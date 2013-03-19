(ns meta
  (:use [live] :reload)
  (:use [supp] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

(defn solve-for* [clause]
  (letfn [(solve [goals]
            (conde
              [(== goals ())]
              [(fresh [c g gs b]
                 (conso g gs goals)
                 (clause c g b)
                 (solve b)
                 (solve gs))]))]
    solve))
(defn solve-for [clause]
  (let [solver* (solve-for* clause)]
    (fn [goal] (solver* [goal]))))

(defn solve-proof-for [clause]
  (letfn [(solve0 [goal tree]
            (solve [goal] tree))
          (solve [goals tree]
            (conde
              [(== goals ())
               (== tree ())]
              [(fresh [c g gs ts b tb]
                 (conso g gs goals)
                 (clause c g b)
                 (conso [g '<-- c tb] ts tree)
                 (solve b tb)
                 (solve gs ts))]))]
    solve0))

(defn debug-proof-for [clause]
  (letfn [(solve0 [goal tree ok]
            (all
              (solve [goal] tree ok)
              (conda
                [(== ok true)]
                [(== ok false)])))
          (solve [goals tree ok]
            (conde
              [(== goals ())
               (== tree ())]
              [(fresh [c g gs ts b tb ehead etail]
                 (conso g gs goals)
                 (conda
                   [(clause c g b)
                    (conso [g '<-- c tb] ts tree)
                    (solve b tb ok)]
                   [(conso [g 'error] ts tree)
                    (== ok false)])
                 (solve gs ts ok))]))]
    solve0))
