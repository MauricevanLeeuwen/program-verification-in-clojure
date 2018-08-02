(ns traffic.core
  (:require (traffic [z3 :as z3]))
  (:require (traffic [env :as env]))
  (:gen-class))

(require '[clojure.core.match :refer [match]])
(require '[clojure.edn :as edn])


(declare eval-expr) ;; Declare it here since eval-sequence and eval-program need it.

(defn eval-empty [program env] ['() env] )
(defn eval-noop "No-op transformation that also prints debug information." [program env]
  (println (apply str "(eval-noop\t" program "\t" env "\t)"))
  [program env])

(defn eval-operands [[res env] expr]
  "To be used as a reducer. Evaluate an expression, append its result to res, and return the new environment."
  (let [[r env] (eval-expr expr env)]
    [(concat res [r]) env] ;; or remove [] from here, so return () from :seq in eval-expr -- the issue is: it is used on things that are not seq like that
    ))

(defn eval-sequence [[res env] expr]
  "To be used as a reducer. Evaluate an expression, append its result to res, and return the new environment."
  (println expr)
  (let [[r env] (eval-expr expr env)]
    [(concat res r) env] ;; or remove [] from here, so return () from :seq in eval-expr -- the issue is: it is used on things that are not seq like that
    ))

(defn eval-program
  ([program] "Programs consist of a list of sequential expressions."
   (eval-program program (env/empty)))

  ([program env]
   (reduce eval-sequence ['() env] program);; TODO 
   ))


(defn eval-expr
  ([program env]
   (match [program]
          ;; When a symbol is encountered, its value is retreived from the environment.
          ;; Consider the following lambda function where x in the environment is bound
          ;; to "anything":
          ;; > ((lambda [x] x) "anything")
          ;; >> "anything"
          ;;
          ;; In program verification no value needs to be retrieved. A variable is declared,
          ;; its value is asserted, and it can be referred to by name.
          ;; The name of the symbol, which is valid within the current scope,
          ;; is maintained in the environment.

          [(x :guard symbol?)] [(z3/symbol (env x)) env]

          ;; Integers evaluate directly to integers:
          [(x :guard integer?)] [x env]
          
          ;; Set! mutates environments.*
          ;; Successive expressions (in a sequence) operate in this mutated environment.
          ;; Example:
          ;; > ((lambda [x] (set! x "mutated") x) "default")
          ;; >> "mutated"
          ;;
          ;; For program verification the following steps are performed:
          ;; 1. A new variable x' is declared. E.g. in SMT: (declare-fun x2 () Int)
          ;;    
          ;; 2. It is asserted that x' is equal to the result of the value expression.
          ;;    
          ;; 3. Subsequent references to x must now refer to x'.
          ;;    This is solved by mutating the environment.
          ;;
          ;; * Since any expression may now mutate the environment,
          ;; all operations therefore return an environment.
          [(['set! (symbol :guard symbol?) value] :seq)]
          (let [[val env] (eval-expr value env)
                env' (env/declare env symbol)
                sym  (env/lookup env symbol)
                sym' (env/lookup env' symbol)
                c (z3/symbol (env/path-condition env'))
                result (list (z3/declare sym')
                             (z3/assert-equals sym' (z3/ite c val (z3/symbol sym))))]
            [result env'])


          [(['fn (arguments :guard vector?) (assertions :guard map?) & body] :seq)]
          (let [;arguments (map vector (take-nth arguments 2) (take-nth (rest arguments) 2))
                arguments (map vector (take-nth 2 arguments ) (take-nth 2 (rest arguments)))
                [c_enter env] (env/branch env) ;; enter the function introduces a path condition
                env (reduce (fn [env [s t]] (env/declare env s t)) env arguments)
                syms (map (fn [[s t]] (z3/declare (env/lookup env s))) arguments)

                [requires env] (eval-expr (:requires assertions) env)
                [body1 env] (eval-program body env)
                c_before_return (env/path-condition env)
                [c_return env] (env/branch env) ;; and when we also return from the function
                [ensures env] (eval-expr (:ensures assertions) env)
                
                result (concat [(z3/declare c_enter) (z3/declare c_return)]
                               syms
                                      (if (contains? assertions :requires)
                                        [(z3/comment "To enter this FN we require:") (z3/assert (z3/eq (z3/symbol c_enter) requires))]
                                        [(z3/comment "We enter this FN unconditionally:") (z3/assert (z3/eq (z3/symbol c_enter) z3/True))])
                                      [(z3/comment "fn body") ]
                                      body1
                                      [(z3/comment "A function returns")(z3/assert (z3/eq (z3/symbol c_before_return) (z3/symbol c_return)))] ;; if we entered, then we also return
                                      (if (contains? assertions :ensures)
                                        [(z3/comment "fn ensures") (z3/assert (z3/and (z3/symbol c_return) ensures))]
                                        [])
                                      )]
            ;; TODO check-sat that the function indeed returns
            [result env])
          
          
          [(['while (condition :guard list?) (assertions :guard map?) & body] :seq)]
          (let [
                ;{:keys [invariant decreases]} r
                c_enter (env/path-condition env)
                [not_inv env1] (eval-expr (:invariant assertions) env)
                [inv1 env1] (eval-expr (:invariant assertions) env1)
                [condition1 env2] (eval-expr condition env1)
                [c_loop env2] (env/branch env2)
                [body1 env2] (eval-program body env2 )
                c_loop_end (env/path-condition env2)
                [not_inv2 env3] (eval-expr (:invariant assertions) env2)


                env4 (reduce (fn [e s] (env/declare e s)) env3 (env/dirty-check env1 env3))
                fresh_syms (map (fn [s] (z3/declare (env/lookup env4 s))) (env/dirty-check env1 env3))
                [c_continues env4] (env/branch env4)
                
                [not_condition2 env4] (eval-expr (list 'not condition) env4)                
                [inv2 env4] (eval-expr (:invariant assertions) env4)


                result (concat [(z3/declare c_loop) (z3/declare c_continues)]
                               (z3/case (z3/comment "Check if the invariant holds before the loop body") (z3/assert (z3/not (z3/implies (z3/symbol c_enter) not_inv))))
                               [(z3/assert inv1)(z3/comment "We enter the loop") (z3/assert (z3/eq (z3/symbol c_loop) condition1))]
                               body1
                               
                               (z3/case (z3/comment "Check if the invariant holds after the loop body")
                                 (z3/assert (z3/not (z3/implies (z3/symbol c_loop_end) not_inv2))))

                               (if (contains? assertions :decreases)
                                 (z3/case (z3/comment "Check the decreases after the loop body")
                                   (z3/assert (z3/not (z3/implies (z3/symbol c_loop_end) (z3/and (z3/operator 'lt (first (eval-expr (:decreases assertions) env2)) (first (eval-expr (:decreases assertions) env1))) (z3/gte (first (eval-expr (:decreases assertions) env2)) 0))))))
                                 [] )
                               [(z3/comment "Reestablish path condition") (z3/assert (z3/implies (z3/symbol c_enter) (z3/symbol c_continues)))]
                               
                               fresh_syms
                               [(z3/comment "loop invariant still holds")
                                (z3/assert (z3/implies (z3/symbol c_continues) inv2))
                                (z3/comment "we're not in the loop anymore, so loop condition must be negated")
                                (z3/assert (z3/implies (z3/symbol c_continues) not_condition2))])]

            [result env4]
            )

          [(['ite condition then else] :seq)]
          (let [c_0 (env/path-condition env)
                [res1 env0] (eval-expr condition env)
                [c_1 env_l] (env/branch env)
                [res2 env_l] (eval-expr then env_l)
                [c_2 env_r] (env/branch env_l)
                [res3 env] (eval-expr else env_r)
                [c_3 env] (env/branch env)
                result (concat[(z3/declare c_1)
                               (z3/declare c_2)
                               (z3/declare c_3)
                               (z3/comment "If we satisfy the condition then take this branch")
                               (z3/assert (z3/eq (z3/symbol c_1) (z3/and res1 (z3/symbol c_0))))
                               (z3/comment "Else we take this branch")
                               (z3/assert (z3/eq (z3/not (z3/symbol c_1)) (z3/symbol c_2))) ;
                               ]
                                res2
                                res3
                                [(z3/comment "Assert that one branch is taken")
                                 (z3/assert (z3/eq (z3/symbol c_3) (z3/or (z3/symbol c_1)(z3/symbol c_2) )))
                                 ]
                               )]
            [result env]
            )

          
          [(['assert (expr :guard seq?)] :seq)]
          (let [[res1 env] (eval-expr expr env)
                result (z3/case
                           (z3/comment "Checking assertion")
                           (z3/assert (z3/not (z3/implies (z3/symbol (env/path-condition env)) res1))))]
            [result env]
            )
          
          
          ;; Applying operators: (operator &operands)
          ;; Because of how we defined set!, evaluating the operator or operands may mutate state.
          ;; Expressions are evaluated left-to-right, starting at the operator and ending at the last operand.
          ;; Environment is then passed between these evaluations.
          ;; Effectively this means that operands can not be evaluated independend of each other, such as:
          ;; > (map #(eval-expr % env) operands)
          ;; Rather a reducer over operands must be used, that appends to a list of results and passes the mutated environment.
          ;; Currently only operands can be used for which an explicit mapping to SMT2 exists in z3/operator.
          [([operator & operands] :seq)]
          (let [[operands env] (reduce eval-operands ['() env] operands)
                res (apply z3/operator operator operands)] ;; TODO: look at this. Should operator be in z3 or core? Should it return environment - it may mutate env like in set! Should operator be evaluated?
            [res env])
          
          ;; default case, for debug purposes.
          :else
          (eval-empty (eval-noop program env) env)
          )))


(defn -main
  "Read a program file and output a file for model checking."
  [& args]
  (let [pipe? (nil? (System/console ))
        ]
    (binding [*out* (if pipe? *err* *out*)]
      (println "Transform all of your problems into SMT2 problems\nUse: java -jar traffic.jar input.clj output.smt2\n")
      (def input_filename (first args))
      (def output_filename (first (rest args)))
      (def data '())
      
      (println "Debug:")
      (def program (clojure.edn/read-string (apply str "(" (slurp input_filename) ")")))
      (def model (first (eval-program program)))
      (if (not pipe?) (println "Output:"))
      )

    (let [output (clojure.string/join "\n" (map str model))] ; stdout
      (println output)
      (spit output_filename output)
      )
  )
)
