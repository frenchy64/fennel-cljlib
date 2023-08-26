(fn spit-lib [path to]
  (with-open [lib (io.open path)]
    (each [line (lib:lines)]
      ;; patching compile-time variable used to store macro module
      ;; namr because when loafing the combined file it will always
      ;; equal the the main module and will break macros in vendored
      ;; libraries.
      (case (line:match "%(local lib%-name %(or %.%.%. (.*)")
        name (to:write (.. "(local lib-name (or " name "\n"))
        _ (to:write line "\n")))))

(with-open [cljlib (io.open "./cljlib.fnl" :w)]
  (let [main (io.open "src/cljlib.fnl")]
    (each [line (main:lines)]
      (case (line:match ";;;###include (.*)")
        (path) (spit-lib path cljlib)
        _ (cljlib:write line "\n")))))
