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
(defn ife [c a b] `(~'if ~c ~a ~b))
(defn lamo [x e out] (== out (lam x e)))
(defn appo [e1 e2 out] (all (== out (app e1 e2)) (!= e1 'fn)))
(defn ifo [c a b out] (== out (ife c a b)))

;;; typed lambda calculus

(defn arr [t1 t2] [t1 '-> t2])
(defn arro [t1 t2 out] (== out (arr t1 t2)))

;;; environments
(defn env [names bindings] ['env names bindings])
(defn envo [names bindings out] (== out (env names bindings)))
(def empty-env (env '() '()))
(defn env-pluso [x v ein eout]
  (fresh [names-in bindings-in names-out bindings-out]
    (envo names-in bindings-in ein)
    (envo names-out bindings-out eout)
    (nom/hash x names-in)
    (conso x names-in names-out)
    (conso [x v] bindings-in bindings-out)))
(defn env-ino [x v e]
  (fresh [names bindings]
    (envo names bindings e)
    (membero [x v] bindings)))
