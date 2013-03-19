(ns theory
  (:use [supp] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom]))

(def max-tries 4000)

(defn bounded-search [r max-tries]
  (let [n (atom 0)]
    (fn [a]
      (if (= @n max-tries)
        ((== r ['reached max-tries]) a)
        (do
          (swap! n inc)
          (fail a))))))

(defn check-preservation [typingo redo]
  (fn [r max-tries]
    (let [ok (bounded-search r max-tries)]
      (fresh [ta tb tya tyb]
        (typingo empty-env ta tya)
        (redo ta tb)
        (conda
          [(typingo empty-env tb tyb)
            (conda
              [(== tya tyb) ok]
              [(!= tya tyb) (== r ['counterexample ta tb tya tyb])])]
          [(== r ['counterexample ta tb tya])])))))

(defn check-progress [typingo redo valo]
  (fn [r max-tries]
    (let [ok (bounded-search r max-tries)]
      (fresh [ta tya]
        (typingo empty-env ta tya)
        (conda
          [(valo ta) ok]
          [(fresh [tb]
             (redo ta tb))
            ok]
          [(== r ['counterexample ta tya])])))))
