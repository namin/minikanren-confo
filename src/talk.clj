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

