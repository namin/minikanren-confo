(ns background
  (:use [live] :reload)
  (:use [supp] :reload)
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

(about "minikanren"
  (eg (run* [q] (== 1 1)) ==> '(_0))
  (eg (run* [q] (== 1 2)) ==> '())
  (eg (run* [q] (== q 1)) ==> '(1))
  (eg (run* [q] (fresh [x y] (== q [x y]))) ==> '([_0 _1]))
  (eg (run* [q] (symbolo q)) ==> '((_0 :- (sym _0))))
  (eg (run* [q] (symbolo q) (== q 'a)) ==> '(a))
  (eg (run* [q] (symbolo q) (== q 1)) ==> '())

  (eg (run* [q] (conde [(== q 1)] [(== q 2)])) ==> '(1 2))
  (eg (run* [q] (fresh [x y] (conde [(== x 1)] [(== y 2)]) (== q [x y])))
    ==> '([1 _0] [_0 2])))
