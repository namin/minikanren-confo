(ns talk
  (:use [live] :reload)
  (:use [supp] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

;;; reasoning about scope

(about "alpha-equivalence"
  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (lam a a) (lam b b))))
    ==> '(_0))

  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (lam a (lam b a)) (lam b (lam a b)))))
    ==> '(_0))

  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (lam a (lam b a)) (lam a (lam b b)))))
    ==> '())

  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (lam a b) (lam b a))))
    ==> '())

  (eg
    (run* [q]
      (nom/fresh [a b c]
        (== (lam a c) (lam b c))))
    ==> '(_0)))

(about "freshness-constraints"
  (eg
    (run* [q]
      (nom/fresh [a]
        (nom/hash a (lam a a))))
    ==> '(_0))

  (eg
    (run* [q]
      (nom/fresh [a b]
        (nom/hash a (lam b a))))
    ==> '()))

;;; example: capture-avoiding substitution

(defn substo [e new a out] ;; out == [new/a]e
  (conde
    [(nomo e) (== e a) (== new out)]
    [(nomo e) (!= e a) (== e out)]
    [(fresh [e1 e2 o1 o2]
       (appo e1 e2 e)
       (appo o1 o2 out)
       (substo e1 new a o1)
       (substo e2 new a o2))]
    [(fresh [e0 o0]
       (nom/fresh [c]
         (lamo c e0 e)
         (lamo c o0 out)
         (nom/hash c a) ;; [new/c]λc.e ≡α λc.e
         (nom/hash c new) ;; [c/a]λc.a ≡α λa.c ≢α λc.c
         (substo e0 new a o0)))]))

(about "substo"

  (eg
    (run* [q]
      (fresh [s]
        (nom/fresh [a b c]
          (substo
            (lam a (app a b)) b a s)
          (== s (lam c (app c b))))))
    ==> '(_0))

  (eg
    (run* [q]
      (fresh [s]
        (nom/fresh [a b c]
          (substo
            (lam a (app a b)) b a s)
          (== s (lam b (app b b))))))
    ==> '())

  (eg
    (run* [q]
      (fresh [s]
        (nom/fresh [a b c]
          (substo
            (lam a b) a b s)
          (== s (lam c a)))))
    ==> '(_0))

  (eg
    (run* [q]
      (fresh [s]
        (nom/fresh [a b c]
          (substo
            (lam a b) a b s)
          (== s (lam a a)))))
    ==> '()))

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
    ==> '(a_0)))

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
    ==> '()))

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
    ==> '(([[_0 _1] a_2] :- a_2#_1 a_2#_0))))

;;; example: small-step operational semantics

(defn valo [e]
  (fresh [e0]
    (nom/fresh [x]
      (lamo x e0 e))))

;;    e1 ⟶ e1'
;; ----------------
;; e1 e2 ⟶ e1' e2

;;    e2 ⟶ e2'
;; ----------------
;; v1 e2 ⟶ v1 e2'

;; (λx.e0) v2 ⟶ [v2/x]e0

(defn stepo [e o]
  (conde
    [(fresh [e1 e2 o1]
       (appo e1 e2 e)
       (appo o1 e2 o)
       (stepo e1 o1))]
    [(fresh [e1 e2 o2]
       (appo e1 e2 e)
       (appo e1 o2 o)
       (valo e1)
       (stepo e2 o2))]
    [(fresh [e1 e2 e0]
       (nom/fresh [x]
         (appo e1 e2 e)
         (valo e1)
         (valo e2)
         (lamo x e0 e1)
         (nom/hash x e2)
         (substo e0 e2 x o)))]))

(defn stepo* [e o]
  (conde
    [(valo e) (== e o)]
    [(fresh [i]
       (stepo e i)
       (stepo* i o))]))

(about "operational-semantics"
  (eg
    (to-clj
      (run* [q]
        (nom/fresh [a]
          (stepo (app (lam a a) (lam a a)) q))))
    ==> '((fn [a_0] a_0)))

  (eg
    (to-clj
      (run 3 [q]
        (nom/fresh [a b]
          (stepo* q (lam a a)))))
    ==>
    '(
       (fn [a_0] a_0)
       ((fn [a_0] a_0) (fn [a_1] a_1))
       (((fn [a_0] a_0) (fn [a_1] a_1)) (fn [a_2] a_2)))))

;;; example: type inferencer

;; x : τ ∈ Γ
;; ---------- Var
;; Γ ⊢ x : τ

;; Γ ⊢ e1 : τ2 → τ
;; Γ ⊢ e2 : τ2
;; ----------------- App
;; Γ ⊢ e1 e2 : τ

;; {x : τx} ∪ Γ ⊢ e0 : τ0
;; ----------------------- Abs
;; Γ ⊢ λx.e0 : τx → τ0

(defn tio [g e t]
  (conde
    ;; Var
    [(fresh [x]
       (nomo x) (== e x)
       (env-ino x t g))]
    ;; Abs
    [(fresh [e0 tx t0 g0]
       (nom/fresh [x]
         (lamo x e0 e)
         (== t [tx '-> t0])
         (env-pluso x tx g g0)
         (tio g0 e0 t0)))]
    ;; App
    [(fresh [e1 e2 t1 t2]
       (appo e1 e2 e)
       (== t1 [t2 '-> t])
       (tio g e1 t1)
       (tio g e2 t2))]))

(about "type-inferencer"
  (eg
    (run* [q]
      (nom/fresh [x]
        (tio empty-env (lam x x) q)))
    ==> '([_0 -> _0]))

  (eg
    (run* [q]
      (nom/fresh [x y]
        (tio empty-env (lam x (lam y y)) q)))
    ==> '([_0 -> [_1 -> _1]]))

  (eg
    (run* [q]
      (nom/fresh [x]
        (tio empty-env (lam x (lam x x)) q)))
    ==> '([_0 -> [_1 -> _1]]))

  (eg
    (run* [q]
      (nom/fresh [x y]
        (tio empty-env (lam x (lam y (app y y))) q)))
    ==> '())

  (eg
    (run* [q]
      (nom/fresh [x]
        (tio empty-env (lam x (lam x (app x x))) q)))
    ==> '())

  (eg
    (to-clj
      (run 10 [q]
        (tio empty-env q '[A -> A])))
    ==>
    '(
       (fn [a_0] a_0)
       (fn [a_0] ((fn [a_1] a_1) a_0))
       ((fn [a_0] a_0) (fn [a_1] a_1))
       (fn [a_0] ((fn [a_1] a_0) a_0))
       (fn [a_0] ((fn [a_1] a_1) ((fn [a_2] a_2) a_0)))
       (fn [a_0] ((fn [a_1] a_0) (fn [a_2] a_2)))
       ((fn [a_0] (fn [a_1] a_1)) (fn [a_2] a_2))
       (fn [a_0] ((fn [a_1] a_0) (fn [a_2] a_0)))
       (fn [a_0] ((fn [a_1] a_1) ((fn [a_2] a_0) a_0)))
       ((fn [a_0] a_0) (fn [a_1] ((fn [a_2] a_2) a_1)))))

  (eg
    (to-clj
      (run 10 [q]
        (fresh [e t]
          (tio empty-env e t)
          (== q [e '==> t]))))
    ==>
    '(
       [(fn [a_0] a_0)                     ==> [_1 -> _1]]
       [(fn [a_0] (fn [a_1] a_1))           ==> [_2 -> [_3 -> _3]]]
       [(fn [a_0] (fn [a_1] a_0))           ==> [_2 -> [_3 -> _2]]]
       [(fn [a_0] (fn [a_1] (fn [a_2] a_2))) ==> [_3 -> [_4 -> [_5 -> _5]]]]
       [((fn [a_0] a_0) (fn [a_1] a_1))     ==> [_2 -> _2]]
       [(fn [a_0] (fn [a_1] (fn [a_2] a_1))) ==> [_3 -> [_4 -> [_5 -> _4]]]]
       [(fn [a_0] (fn [a_1] (fn [a_2] a_0))) ==> [_3 -> [_4 -> [_5 -> _3]]]]
       [(fn [a_0] (a_0 (fn [a_1] a_1)))     ==> [[[_2 -> _2] -> _3] -> _3]]
       [((fn [a_0] a_0) (fn [a_1] (fn [a_2] a_2))) ==> [_3 -> [_4 -> _4]]]
       [(fn [a_0] (fn [a_1] (a_1 a_0)))     ==> [_2 -> [[_2 -> _3] -> _3]]]))

  (eg
    (to-clj
      (run 3 [q]
        (fresh [env e t]
          (tio env e t)
          (== q [env '|| e '==> t]))))
    ==>
    '(
       ([[env _0 ([_1 _2] . _3)]       || _1 ==> _2] :- (nom _1))
       ([[env _0 (_1 [_2 _3] . _4)]    || _2 ==> _3] :- (nom _2))
       ([[env _0 (_1 _2 [_3 _4] . _5)] || _3 ==> _4] :- (nom _3)))))
