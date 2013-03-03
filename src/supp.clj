(ns supp
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

;; type tests

(defn nomo [x] (predc x nom? `nom?))
(defn symbolo [x] (predc x symbol? `symbol?))
