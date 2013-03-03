(ns talk
  (:use [live] :reload)
  (:use [supp] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

;;; language intro: fresh, hash, tie

(about "fresh"
  (eg
    (run* [q]
      (nom/fresh [a]
        (== a a)))
    ==> '(_0))
  (eg
    (run* [q]
      (nom/fresh [a]
        (== a 5)))
    ==> ())
  (eg
    (run* [q]
      (nom/fresh [a b]
        (== a b)))
    ==> ())
  (eg
    (run* [q]
      (nom/fresh [b]
        (== q b)))
    ==> '(a_0))
)

(about "tie"
  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (nom/tie a `(~'foo ~a 3 ~b)) q)))
    ==> `(~(nom/tie 'a_0 '(foo a_0 3 a_1))))
  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (nom/tie a a) (nom/tie b b))))
    ==> '(_0))
  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (nom/tie a b) (nom/tie b a))))
    ==> '())
)

(about "hash"
  (eg
    (run* [q]
      (nom/fresh [a]
        (== `(3 ~a ~true) q)
        (nom/hash a q)))
    ==> '())
  (eg
    (run* [q]
      (nom/fresh [a]
        (nom/hash a q)
        (== `(3 ~a ~true) q)))
    ==> '())
  (eg
    (run* [q]
      (nom/fresh [a b]
        (nom/hash a (nom/tie b a))))
    ==> '())
  (eg
    (run* [q]
      (nom/fresh [a b]
        (nom/hash a (nom/tie a a))))
    ==> '(_0))
  (eg
    (run* [q]
      (fresh [x]
        (nom/fresh [a]
          (nom/hash a x)
          (== [x a] q))))
    ==> '(([_0 a_1] :- a_1#_0)))
  (eg
    (run* [q]
      (fresh [x y z]
        (nom/fresh [a]
          (nom/hash a x)
          (== [y z] x)
          (== [x a] q))))
    ==> '(([[_0 _1] a_2] :- a_2#_1 a_2#_0)))
)

;;; example: type inferencer for simply-typed lambda calculus

;; x : τ ∈ Γ
;; ---------- Var
;; Γ ⊢ x : τ

;; Γ ⊢ e1 : τ2 → τ
;; Γ ⊢ e2 : τ2
;; ----------------- App
;; Γ ⊢ e1 e2 : τ

;; {x : τx} ∪ Γ ⊢ e0 : τ0
;; ----------------------- Abs
;; Γ ⊢ λx.e1 : τx → τ0

(defn s-tio [g e t] ;; wrong!
  (conde
    ;; Var
    [(fresh [x]
       (symbolo e) (== e x)
       (membero [x t] g))]
    ;; Abs
    [(fresh [x e0 tx t0 g0]
       (symbolo x)
       (== e `(~'fn [~x] ~e0))
       (== t [tx '-> t0])
       (conso [x tx] g g0)
       (s-tio g0 e0 t0))]
    ;; App
    [(fresh [e1 e2 t1 t2]
       (== e `(~e1 ~e2))
       (== t1 [t2 '-> t])
       (s-tio g e1 t1)
       (s-tio g e2 t2))]))

(about "s-tio"
  (eg
    (run* [q]
      (s-tio '() '(fn [x] x) q))
    ==> '([_0 -> _0]))
  (eg
    (run* [q]
      (s-tio '() '(fn [x] (fn [y] y)) q))
    ==> '([_0 -> [_1 -> _1]]))
  (eg
    (run* [q]
      (s-tio '() '(fn [x] (fn [x] x)) q))
    ==> '(
           [_0 -> [_1 -> _1]]
           [_0 -> [_1 -> _0]] ;; wrong!
         ))
  (eg
    (run* [q]
      (s-tio '() '(fn [x] (fn [y] (y y))) q))
    ==> '())
  (eg
    (run* [q]
      (s-tio '() '(fn [x] (fn [x] (x x))) q))
    ==> '(
           [_0 -> [[_0 -> _1] -> _1]] ;; wrong!
           [[_0 -> _1] -> [_0 -> _1]] ;; wrong!
         ))
)

(defn n-tio [g e t]
  (conde
    ;; Var
    [(fresh [x]
       (nomo x) (== e x)
       (membero [x t] g))]
    ;; Abs
    [(fresh [e0 tx t0 g0]
       (nom/fresh [x]
         (nom/hash x g)
         (== e `(~'fn ~(nom/tie x e0)))
         (== t [tx '-> t0])
         (conso [x tx] g g0)
         (n-tio g0 e0 t0)))]
    ;; App
    [(fresh [e1 e2 t1 t2]
       (== e `(~e1 ~e2)) (!= e1 'fn)
       (== t1 [t2 '-> t])
       (n-tio g e1 t1)
       (n-tio g e2 t2))]))

(about "n-tio"
  (eg
    (run* [q]
      (nom/fresh [x]
        (n-tio '() `(~'fn ~(nom/tie x x)) q)))
    ==> '([_0 -> _0]))
  (eg
    (run* [q]
      (nom/fresh [x y]
        (n-tio '() `(~'fn ~(nom/tie x `(~'fn ~(nom/tie y y)))) q)))
    ==> '([_0 -> [_1 -> _1]]))
  (eg
    (run* [q]
      (nom/fresh [x]
        (n-tio '() `(~'fn ~(nom/tie x `(~'fn ~(nom/tie x x)))) q)))
    ==> '([_0 -> [_1 -> _1]]))
  (eg
    (run* [q]
      (nom/fresh [x y]
        (n-tio '() `(~'fn ~(nom/tie x `(~'fn ~(nom/tie y `(~y ~y))))) q)))
    ==> '())
  (eg
    (run* [q]
      (nom/fresh [x]
        (n-tio '() `(~'fn ~(nom/tie x `(~'fn ~(nom/tie x `(~x ~x))))) q)))
    ==> '())
)
