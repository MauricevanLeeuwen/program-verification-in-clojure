(ns traffic.z3
  )

(require '[clojure.core.match :refer [match]])

(defn symbol [x]
  "Express a symbol as stored in the environment to a nice SMT2 variable name."
  (clojure.core/symbol (str (:name x) "_" (:n x)))
  )

(defn declare [x]
  "Declare a variable using SMT2 (declare-fun). Depends on the :type of input symbol."
  (match [(:type x)]
         [':boolean] (list 'declare-fun (symbol x) '() 'Bool)
         [':integer] (list 'declare-fun (symbol x) '() 'Int)
         :else (println "I don't know this type!")
         ))

(defn assert [x]
  (list 'assert x)
  )
(defn assert-equals [l r]
  (assert (list '= (symbol l) r))
  )
(defn operator [operator & operands]
  "Translate to SMT2 operator"
  (match [operator]
         ;; comparison
         ['gte] (concat '( >= ) operands)
         ['gt] (concat '( > ) operands)
         ['lte] (concat '( <= ) operands)
         ['lt] (concat '( < ) operands)
         ['eq] (concat '( = ) operands)
         ;; logic
         ['not] (concat '( not ) operands)
         ['and] (concat '( and ) operands)
         ['or] (concat '( or ) operands)
         ['implies] (concat '( => ) operands)
         ;; arithmetic
         ['add] (concat '( + ) operands)
         ['sub] (concat '( - ) operands)
         ['div] (concat '( / ) operands)
         ['mul] (concat '( * ) operands)
         ['inc] (concat '( + 1) operands)
         ['dec] (concat '( + -1) operands)
         )
  )

(def True 'true)

(defn not [& r]
  (apply operator 'not r) 
  )
(defn and [& r]
  (apply operator 'and r) 
  )
(defn gt [& r]
  (apply operator 'gt r) 
  )

(defn gte [& r]
  (apply operator 'gte r) 
  )
(defn eq [& r]
  (apply operator 'eq r) 
  )

(defn implies [& r]
  (apply operator 'implies r)
  )
(defn ite [c l r]
  (list 'ite c l r))
(defn or [& r]
  (apply operator 'or r) 
  )
(defn comment [& r]
  (clojure.core/symbol (apply str "; " r))
  )

(defn path-requires [cur prev]
;  (assert (eq 
           )
(defn path-alternative []
)
(defmacro z3 [form]
  `(list ~@form)
  )

(def push (list 'push))
(def pop (list 'pop))
(def check-sat (list 'check-sat))
(def get-model (list 'get-model))
(defn case [& r]
  (concat [push]
          r
          [check-sat get-model pop])

  )
  

