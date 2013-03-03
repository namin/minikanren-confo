(ns talk
  (:use [live] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

;; language intro: fresh, hash, tie

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
