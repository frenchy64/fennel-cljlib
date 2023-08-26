# Fennel Cljlib

Experimental library for the [Fennel](https://fennel-lang.org/) language, that adds many functions from [Clojure](https://clojure.org/)'s standard library.
This is not a one-to-one port of Clojure `core`, because many Clojure features require certain facilities from the runtime.
This library implements lazy sequences, transducers, immutable tables, sets and vectors, transients, and a lot of functions from the `core` namespace.
Some semantics like dynamic scope and parallelism are not supported by Lua runtime at all.
Therefore, certain functions were altered to better suit the domain or omitted entirely.

## Installation

Grab the [cljlb.fnl][1] file, and copy it somewhere into your project.
Now you can require `:cljlib` from Fennel:

``` fennel
(local clj (require :cljlib))
```

To use macros provided by the library, due to the implementation of how macros are stored an additional `require` step in the `import-macros` call is required:

```fennel
(import-macros cljm (doto :cljlib require))
```

Alternatively, the library can be precompiled so it will load slightly faster:

    $ fennel -c cljlib.fnl > cljlib.lua

However, this way the macros provided by this library will not be available.

## Documentation

Documentation is auto-generated with [Fenneldoc](https://gitlab.com/andreyorst/fenneldoc) and can be found [here](https://gitlab.com/andreyorst/fennel-cljlib/-/tree/master/doc).

# Contributing

Please make sure you've read [contribution guidelines][2].

In order to work on the library, edit the `src/cljlib.fnl` file, then run the `build.fnl` script to produce a self-contained version of the library.

Tests can be ran with

    for test in tests/*.fnl; do fennel --metadata $test; done

[1]: https://gitlab.com/andreyorst/fennel-cljlib/-/raw/master/cljlib.fnl
[2]: https://gitlab.com/andreyorst/fennel-cljlib/-/tree/master/CONTRIBUTING.md

<!--  LocalWords:  Lua submodule precompile cljlib docstring config
      LocalWords:  namespace destructure runtime Clojure precompiled
 -->
