(local t (require :fennel-test.fennel-test))

(local test-modules
  [:tests.core
   :tests.fn
   :tests.macros])

(t.run-tests test-modules)
