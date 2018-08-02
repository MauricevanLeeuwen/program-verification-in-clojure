(ns traffic.env
  )

;(require '[clojure.core.match :as match])
(require '[clojure.core.match :refer [match]])

(defrecord Symbol [])
(defn lookup [env symbol]
  (env symbol)
  )

(defn declare
  ([env symbolname] (update env symbolname #(update % :n inc)))
  ([env symbolname type] (update env symbolname #(if (= % nil) {:name symbolname :type type :n 0} (update % :n inc))))
  ([env key symbolname type] (update env key #(if (= % nil) {:name symbolname :type type :n 0} (update % :n inc))))
  )


(defn path-condition [env]
  (lookup env :path-condition)
  )
  ;(lookup env :path-condition))

(defn dirty-check [env_l env_r]
  "Check if there are symbols in env_r that are changed since env_l"
  (map (fn [[k v]] k) (filter (fn [[k v]] (> (:n v) (:n (lookup env_l k)) )) env_r))
  )
(defn branch [env]
  (let [env (declare env :path-condition "branch" :boolean)]
    [(path-condition env) env])
  )

(defn empty []
  "Returns an empty environment"
  {}
  )

  
