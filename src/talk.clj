(ns talk
  (:use [live] :reload)
  (:use [supp] :reload)
  (:use [meta] :reload)
  (:use [theory] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

;;; core.logic.nominal

(about "alpha-equivalence"

  ;;; (lam x e): λx.e or (fn [x] e)
  ;;; (== (lam x1 e1) (lam x2 e2))

  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (lam a a)
            (lam b b))))
    ==> '(_0))

  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (lam a (lam b a))
            (lam b (lam a b)))))
    ==> '(_0))

  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (lam a (lam b a))
            (lam a (lam b b)))))
    ==> '())

  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (lam a b)
            (lam b b))))
    ==> '())

  (eg
    (run* [q]
      (nom/fresh [a b c]
        (== (lam a c)
            (lam b c))))
    ==> '(_0))

  (eg
    (run* [q]
      (nom/fresh [a b]
        (== (lam a b)
            (lam b a))))
    ==> '()))

;;; formally,
;;; `λa.e ≡α λb.(swap b a)e` where
;;; `b` does not occur free in `e`

(about "freshness-constraints"

  ;;; (nom/hash x e): x#e

  (eg
    (run* [q]
      (nom/fresh [a]
        (nom/hash a a)))
    ==> '())

  (eg
    (run* [q]
      (nom/fresh [a b]
        (nom/hash a b)))
    ==> '(_0))

  (eg
    (run* [q]
      (nom/fresh [a b]
        (nom/hash a (lam b a))))
    ==> '())

  (eg
    (run* [q]
      (nom/fresh [a]
        (nom/hash a (lam a a))))
    ==> '(_0)))

;;; example: capture-avoiding substitution
;;; [e'/a]e
;;; [c/b]λa.b ≡ λa.c ≡ λb.c ≢ λc.c
;;; [a/b]λa.b ≡ [a/b]λc.b ≡ λc.a ≢ λa.a

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
            (lam a (app a b)) b a s)  ;; [b/a]λa.(a b)
          (== s (lam c (app c b)))))) ;;   == λc.(c b)
    ==> '(_0))

  (eg
    (run* [q]
      (fresh [s]
        (nom/fresh [a b c]
          (substo
            (lam a (app a b)) b a s)  ;; [b/a]λa.(a b)
          (== s (lam b (app b b)))))) ;;   != λb.(b b)
    ==> '())

  (eg
    (run* [q]
      (fresh [s]
        (nom/fresh [a b c]
          (substo
            (lam a b) a b s)  ;; [a/b]λa.b
          (== s (lam c a))))) ;;   == λc.a
    ==> '(_0))

  (eg
    (run* [q]
      (fresh [s]
        (nom/fresh [a b c]
          (substo
            (lam a b) a b s)  ;; [a/b]λa.b
          (== s (lam a a))))) ;;   != λa.a
    ==> '()))

(about "substo-why-freshness-constraints"

  (eg
    (run* [q]
      (fresh [e new]
        (nom/fresh [a b c]
          (substo (lam a e) new b (lam c c))
          (!= (lam a e) (lam a a)))))
    ==> '())
    ;;; without ...#new, we would get success!

  (eg
    (run* [q]
      (fresh [e new x]
        (nom/fresh [a c]
          (substo (lam a a) new x (lam c a)))))
    ==> '())
    ;;; without ...#a, we would get success!
)

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
         (arro tx t0 t)
         (env-pluso x tx g g0)
         (tio g0 e0 t0)))]
    ;; App
    [(fresh [e1 e2 t1 t2]
       (appo e1 e2 e)
       (arro t2 t t1)
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
        (tio empty-env q (arr 'A 'A))))
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

;;; Demo Interlude: Run you Research!

;;; Explaining and Debugging Type Derivations

(about "type-deriv-motiv"
  (eg
    (run* [q]
      (nom/fresh [x]
        (tio empty-env (lam x x) q)))
    ==> '([_0 -> _0]))

  (eg
    (run* [q]
      (nom/fresh [x]
        (tio empty-env (lam x (app x x)) q)))
    ==> '())
)

;;; Finding Counterexamples to Meta-Theoretic Properties

(defn gsubsto [e new a out] ;; out == [new/a]e
  (conde
    [(nomo e) (== e a) (== new out)]
    [(nomo e) (!= e a) (== e out)]
    [(symbolo e) (== e out)]
    [(== true e) (== e out)]
    [(== false e) (== e out)]
    [(== e ()) (== e out)]
    [(fresh [e0 es o0 os]
       (conso e0 es e)
       (conso o0 os out)
       (gsubsto e0 new a o0)
       (gsubsto es new a os))]
    [(fresh [e0 o0]
       (nom/fresh [c]
         (== (nom/tie c e0) e)
         (== (nom/tie c o0) out)
         (nom/hash c a)
         (nom/hash c new)
         (gsubsto e0 new a o0)))]))

(defn bvalo [e]
  (conde
    [(fresh [e0]
       (nom/fresh [x]
         (lamo x e0 e)))]
    [(== e true)]
    [(== e false)]))

(defn bstepo [e o]
  (conde
    [(fresh [e1 e2 o1]
       (appo e1 e2 e)
       (appo o1 e2 o)
       (bstepo e1 o1))]
    [(fresh [e1 e2 o2]
       (appo e1 e2 e)
       (appo e1 o2 o)
       (bvalo e1)
       (bstepo e2 o2))]
    [(fresh [e1 e2 e0]
       (nom/fresh [x]
         (appo e1 e2 e)
         (bvalo e1)
         (bvalo e2)
         (lamo x e0 e1)
         (nom/hash x e2)
         (gsubsto e0 e2 x o)))]
    [(fresh [c a b co]
       (ifo c a b e)
       (ifo co a b o)
       (bstepo c co))]
    [(fresh [c a b]
       (ifo c a b e)
       (bvalo c)
       (conde
         [(== true c) (== o a)]
         [(== false c) (== o b)]))]))

(defn btio [g e t]
  (conde
    ;; Var
    [(fresh [x]
       (nomo x) (== e x)
       (env-ino x t g))]
    ;; Abs
    [(fresh [e0 tx t0 g0]
       (nom/fresh [x]
         (lamo x e0 e)
         (arro tx t0 t)
         (env-pluso x tx g g0)
         (btio g0 e0 t0)))]
    ;; App
    [(fresh [e1 e2 t1 t2]
       (appo e1 e2 e)
       (arro t2 t t1)
       (btio g e1 t1)
       (btio g e2 t2))]
    ;; True
    [(== e true) (== t 'bool)]
    ;; False
    [(== e false) (== t 'bool)]
    ;; If
    [(fresh [c a b]
       (ifo c a b e)
       (btio g c 'bool)
       (btio g a t)
       (btio g b t))]))

(defn btio-bad1 [g e t]
  (conde
    ;; Var
    [(fresh [x]
       (nomo x) (== e x)
       (env-ino x t g))]
    ;; Abs
    [(fresh [e0 tx t0 g0]
       (nom/fresh [x]
         (lamo x e0 e)
         (arro tx t0 t)
         (env-pluso x tx g g0)
         (btio-bad1 g0 e0 t0)))]
    ;; App
    [(fresh [e1 e2 t1 t2]
       (appo e1 e2 e)
       (arro t2 t t1)
       (btio-bad1 g e1 t1)
       (btio-bad1 g e2 t2))]
    ;; True
    [(== e true) (== t 'bool)]
    ;; False
    [(== e false) (== t 'bool)]
    ;; If
    [(fresh [c a b]
       (ifo c a b e)
       (btio-bad1 g c 'bool)
       (btio-bad1 g a t)
       ;; missing else branch: (btio g b t)
     )]))

(defn btio-bad2 [g e t]
  (conde
    ;; Var
    [(fresh [x]
       (nomo x) (== e x)
       (env-ino x t g))]
    ;; Abs
    [(fresh [e0 tx t0 g0]
       (nom/fresh [x]
         (lamo x e0 e)
         (arro tx t0 t)
         (env-pluso x tx g g0)
         (btio-bad2 g0 e0 t0)))]
    ;; App
    [(fresh [e1 e2 t1 t2]
       (appo e1 e2 e)
       (arro t2 t t1)
       (btio-bad2 g e1 t1)
       (btio-bad2 g e2 t2))]
    ;; True
    [(== e true) (== t 'bool)]
    ;; False
    [(== e false) (== t 'bool)]
    ;; If
    [(fresh [c a b tyc]
       (ifo c a b e)
       (btio-bad2 g c tyc) ;; tyc should be 'bool
       (btio-bad2 g a t)
       (btio-bad2 g b t))]))

(about "counterexample-generation"
  (eg (run 1 [q] ((check-preservation tio stepo) q max-tries))
    ==> `((~'reached ~max-tries)))
  (eg (run 1 [q] ((check-preservation btio bstepo) q max-tries))
    ==> `((~'reached ~max-tries)))
  (eg (run 1 [q] ((check-progress btio bstepo bvalo) q max-tries))
    ==> `((~'reached ~max-tries)))
  (eg (to-clj (run 1 [q] ((check-preservation btio-bad1 bstepo) q max-tries)))
    ==> '([counterexample (if false true (fn [a_0] true)) (fn [a_0] true) bool [_1 -> bool]]))
  (eg (to-clj (run 1 [q] ((check-progress btio-bad2 bstepo bvalo) q max-tries)))
    ==> '([counterexample (if (fn [a_0] true) true true) bool])))

;;; Understanding and Debugging via Meta-Interpreters

(defn tio-clause [c a b]
  (fresh [g e t]
    (== ['tio g e t] a)
    (conde
      [(== c 'T-Var)
       (fresh [x]
         (nomo x) (== e x)
         (env-ino x t g)
         (== b ()))]
      [(== c 'T-Abs)
       (fresh [e0 tx t0 g0]
         (nom/fresh [x]
           (lamo x e0 e)
           (arro tx t0 t)
           (env-pluso x tx g g0)
           (== b [['tio g0 e0 t0]])))]
      [(== c 'T-App)
       (fresh [e1 e2 t1 t2]
         (appo e1 e2 e)
         (arro t2 t t1)
         (== b [['tio g e1 t1]
                ['tio g e2 t2]]))])))

(def tio-deriv (solve-proof-for tio-clause))

(about "type-derivations"
  (eg
    (to-clj
      (run* [q]
        (fresh [ty tree]
          (nom/fresh [x]
            (tio-deriv ['tio empty-env (lam x x) ty] tree)
            (== q [ty tree])))))
    ==>
    '([[_0 -> _0]
        ([[tio [env () ()] (fn [a_1] a_1) [_0 -> _0]] <-- T-Abs
           ([[tio [env (a_2) ([a_2 _0])] a_2 _0] <-- T-Var ()])])]))
  (eg
    (run* [q]
      (fresh [ty tree]
        (nom/fresh [x]
          (tio-deriv ['tio empty-env (lam x `(~x ~x)) ty] tree)
          (== q [ty tree]))))
    ==> '()))

(defn tio-debug-clause [c a b]
  (conde
    [(fresh [x y]
       (== a ['== x y])
       (== x y)
       (== b ()))]
    [(fresh [x t g]
       (== a ['env-ino x t g])
       (env-ino x t g)
       (== b ()))]
    [(fresh [g e t]
       (== ['tio g e t] a)
       (conde
         [(== c 'T-Var)
          (fresh [x]
            (nomo x) (== e x)
            (== b [['env-ino x t g]]))]
         [(== c 'T-Abs)
          (fresh [e0 tx t0 g0]
            (nom/fresh [x]
              (lamo x e0 e)
              (env-pluso x tx g g0)
              (== b [['tio g0 e0 t0]
                     ['== t (arr tx t0)]])))]
         [(== c 'T-App)
           (fresh [e1 e2 t1 t2 t11 t12]
             (appo e1 e2 e)
             (== b [['tio g e1 t1]
                    ['tio g e2 t2]
                    ['== t1 (arr t11 t12)]
                    ['== t2 t11]
                    ['== t t12]]))]))]))

(def tio-debug (debug-proof-for tio-clause))

(about "type-debugger"
  (eg
    (to-clj
      (run* [q]
        (fresh [ty tree ok]
          (nom/fresh [x]
            (tio-debug ['tio empty-env (lam x `(~x ~x)) ty] tree ok)
            (== q [ty tree ok])))))
    ==>
    '([[[_0 -> _1] -> _1]
        ([[tio [env () ()] (fn [a_2] (a_2 a_2)) [[_0 -> _1] -> _1]] <-- T-Abs
           ([[tio [env (a_3) ([a_3 [_0 -> _1]])] (a_3 a_3) _1] <-- T-App
              ([[tio [env (a_3) ([a_3 [_0 -> _1]])] a_3 [_0 -> _1]] <-- T-Var ()]
               [[tio [env (a_3) ([a_3 [_0 -> _1]])] a_3 _0] error])])])
        false])))

;;; Under the hood: swapping

(about "nominal-logic"
  (eg
    (run* [q]
      (fresh [x y]
        (nom/fresh [a b]
          (== (nom/tie a x) (nom/tie b y))
          (== [a b x y] q))))
    ==> '(([a_0 a_1 _2 _3] :- a_1#_2 (swap [a_0 a_1] _3 _2))))
        ;;  a   b   x  y      b#x    (y is x with a & b swapped)
  (eg
    (run* [q]
      (fresh [x y]
        (nom/fresh [a b]
          (== (nom/tie a x) (nom/tie b y))
          (== [a b x y] q)
          (== x y))))
    ==> '(([a_0 a_1 _2 _2] :- a_1#_2 a_0#_2)))
        ;;  a   b   x==y      b#x    a#x
  )
