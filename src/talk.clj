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
    ==> '(_0))
)

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
    ==> '())
)

;;; example: capture-avoiding substitution

(defn substo [e new a out]
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
         (nom/hash c a)
         (nom/hash c new)
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

