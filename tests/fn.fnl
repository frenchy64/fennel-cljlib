(require-macros :tests.test)
(require-macros :cljlib-macros)

(deftest defn
  (testing "defn meta"
    (defn f
      "docstring"
      [x] x)
    (assert-eq (meta f) (when-meta {:fnl/docstring "docstring"
                                    :fnl/arglist ["x"]}))

    (defn f
      "docstring"
      ([x] x))
    (assert-eq (meta f) (when-meta {:fnl/docstring "docstring"
                                    :fnl/arglist ["x"]}))

    (defn f
      "docstring"
      ([x] x)
      ([x y] (+ x y)))
    (assert-eq (meta f) (when-meta {:fnl/docstring "docstring"
                                    :fnl/arglist ["\n  [x]"
                                                  "\n  [x y]"]}))

    (defn f
      "docstring"
      ([x] x)
      ([x y] (+ x y))
      ([x y & z] (+ x y)))
    (assert-eq (meta f) (when-meta {:fnl/docstring "docstring"
                                    :fnl/arglist ["\n  [x]"
                                                  "\n  [x y]"
                                                  "\n  [x y & z]"]}))))

(deftest fn+
  (testing "fn+ meta"
    (fn+ f "docstring" [x] x)
    (assert-eq (meta f) (when-meta {:fnl/docstring "docstring"
                                    :fnl/arglist ["x"]}))

    (fn+ f "docstring" [...] [...])
    (assert-eq (meta f) (when-meta {:fnl/docstring "docstring"
                                    :fnl/arglist ["..."]}))))