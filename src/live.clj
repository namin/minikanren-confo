(ns live
  (:refer-clojure :exclude [==])
  (:use [clojure.core.logic :exclude [is] :as l]
        [clojure.core.logic.nominal :exclude [fresh hash] :as nom])
  (:use [clojure.test]))

(def ==> '==>)

(defmacro eg [a _ b]
  `(is (= ~a ~b)))

(defmacro about
  [name & args]
  `(deftest ~(symbol (str 'tests-about- name))
     (println "..." ~name)
     ~@args))
