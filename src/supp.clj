(ns supp
  (:use [live] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

;;; prettier reification for single-variable constraints
(defn reifier-for [tag x]
  (fn [c v r a]
    (let [x (walk* r (walk* a x))]
      (when (symbol? x)
        `(~tag ~x)))))

;;; type constraints
(defn nomo [x] (predc x nom? (reifier-for 'nom x)))

(about "nomo"
  (eg
    (run* [q] (nomo q))
    ==> '((_0 :- (nom _0))))
)

(defn symbolo [x] (predc x symbol? (reifier-for 'sym x)))

(about "symbolo"
  (eg
    (run* [q] (symbolo q))
    ==> '((_0 :- (sym _0))))
)

;;; lambda calculus

(defn lam [x e] `(~'fn ~(nom/tie x e)))
(defn app [e1 e2] `(~e1 ~e2))
(defn lamo [x e out] (== out (lam x e)))
(defn appo [e1 e2 out] (all (== out (app e1 e2)) (!= e1 'fn)))
