# Cljlib (v1.1.1)
Fennel-cljlib - functions from Clojure's core.clj implemented on top of Fennel.

This library contains a set of functions providing functions that behave similarly to Clojure's equivalents.
The library itself apart from macros has nothing Fennel-specific, so it should work on Lua, e.g.:

``` lua
Lua 5.3.5  Copyright (C) 1994-2018 Lua.org, PUC-Rio
> clj = require"cljlib"
> table.concat(clj.mapv(function (x) return x * x end, {1, 2, 3}), " ")
-- 1 4 9
```

This example is mapping an anonymous `function` over a table, producing a new table, and concatenating it with `" "`.

However, this library also provides a Fennel-specific set of [macros](./macros.md), which provides additional facilities like [`defn`](#defn) or [`defmulti`](#defmulti) which extends the language allowing writing code that looks and works mostly like Clojure.

Each function in this library is created with [`defn`](#defn), which is a special macro for creating multi-arity functions.
So when you see a function signature like `(foo [x])`, this means that this is function `foo`, which accepts exactly one argument `x`.
On the contrary, functions created with `fn` will produce a `(foo x)` signature (`x` is not inside brackets).

Functions, which signatures look like `(foo ([x]) ([x y]) ([x y & zs]))`, it is a multi-arity function, which accepts either one, two, or three or more arguments.
Each `([...])` represents a different body of a function which is chosen by checking the amount of arguments passed to the function.
See [Clojure's doc section on multi-arity functions](https://clojure.org/guides/learn/functions#_multi_arity_functions).

## Compatibility

This library is mainly developed with Lua 5.4 and tested against Lua 5.2, 5.3, 5.4, and LuaJIT 2.1.0-beta3.
Note, that in Lua 5.2 and LuaJIT equality semantics are a bit different from Lua 5.3 and Lua 5.4.
The main difference is that when comparing two tables, they must have exactly the same `__eq` metamethods, so comparing hash sets with hash sets will work, but comparing sets with other tables works only in Lua5.3+.
Another difference is that Lua 5.2 and LuaJIT don't have an inbuilt UTF-8 library, therefore [`seq`](#seq) function will not work for non-ASCII strings.

**Table of contents**

- [`ns`](#ns)
- [`in-ns`](#in-ns)
- [`def`](#def)
- [`fn*`](#fn)
- [`defn`](#defn)
- [`defn-`](#defn-)
- [`time`](#time)
- [`if-let`](#if-let)
- [`when-let`](#when-let)
- [`if-some`](#if-some)
- [`when-some`](#when-some)
- [`defmulti`](#defmulti)
- [`defmethod`](#defmethod)
- [`cond`](#cond)
- [`loop`](#loop)
- [`try`](#try)
- [`lazy-seq`](#lazy-seq)
- [`lazy-cat`](#lazy-cat)
- [`apply`](#apply)
- [`add`](#add)
- [`sub`](#sub)
- [`mul`](#mul)
- [`div`](#div)
- [`le`](#le)
- [`lt`](#lt)
- [`ge`](#ge)
- [`gt`](#gt)
- [`inc`](#inc)
- [`dec`](#dec)
- [`eq`](#eq)
- [`map?`](#map)
- [`vector?`](#vector)
- [`multifn?`](#multifn)
- [`set?`](#set)
- [`nil?`](#nil)
- [`zero?`](#zero)
- [`pos?`](#pos)
- [`neg?`](#neg)
- [`even?`](#even)
- [`odd?`](#odd)
- [`string?`](#string)
- [`boolean?`](#boolean)
- [`true?`](#true)
- [`false?`](#false)
- [`int?`](#int)
- [`pos-int?`](#pos-int)
- [`neg-int?`](#neg-int)
- [`double?`](#double)
- [`empty?`](#empty)
- [`not-empty`](#not-empty)
- [`vector`](#vector-1)
- [`seq`](#seq)
- [`first`](#first)
- [`rest`](#rest)
- [`last`](#last)
- [`butlast`](#butlast)
- [`conj`](#conj)
- [`disj`](#disj)
- [`cons`](#cons)
- [`concat`](#concat)
- [`reduce`](#reduce)
- [`reduced`](#reduced)
- [`reduce-kv`](#reduce-kv)
- [`mapv`](#mapv)
- [`filter`](#filter)
- [`every?`](#every)
- [`some`](#some)
- [`not-any?`](#not-any)
- [`range`](#range)
- [`reverse`](#reverse)
- [`take`](#take)
- [`nthrest`](#nthrest)
- [`partition`](#partition)
- [`identity`](#identity)
- [`comp`](#comp)
- [`complement`](#complement)
- [`constantly`](#constantly)
- [`memoize`](#memoize)
- [`assoc`](#assoc)
- [`hash-map`](#hash-map)
- [`get`](#get)
- [`get-in`](#get-in)
- [`keys`](#keys)
- [`vals`](#vals)
- [`find`](#find)
- [`dissoc`](#dissoc)
- [`remove-method`](#remove-method)
- [`remove-all-methods`](#remove-all-methods)
- [`methods`](#methods)
- [`get-method`](#get-method)
- [`hash-set`](#hash-set)
- [`assoc!`](#assoc-1)
- [`assoc-in`](#assoc-in)
- [`cat`](#cat)
- [`class`](#class)
- [`completing`](#completing)
- [`conj!`](#conj-1)
- [`contains?`](#contains)
- [`count`](#count)
- [`cycle`](#cycle)
- [`dedupe`](#dedupe)
- [`deref`](#deref)
- [`disj!`](#disj-1)
- [`dissoc!`](#dissoc-1)
- [`distinct`](#distinct)
- [`doall`](#doall)
- [`dorun`](#dorun)
- [`drop`](#drop)
- [`drop-last`](#drop-last)
- [`drop-while`](#drop-while)
- [`empty`](#empty-1)
- [`ensure-reduced`](#ensure-reduced)
- [`filterv`](#filterv)
- [`frequencies`](#frequencies)
- [`group-by`](#group-by)
- [`halt-when`](#halt-when)
- [`interleave`](#interleave)
- [`interpose`](#interpose)
- [`into`](#into)
- [`iterate`](#iterate)
- [`keep`](#keep)
- [`keep-indexed`](#keep-indexed)
- [`line-seq`](#line-seq)
- [`list`](#list)
- [`list*`](#list-1)
- [`map`](#map-1)
- [`map-indexed`](#map-indexed)
- [`mapcat`](#mapcat)
- [`merge`](#merge)
- [`next`](#next)
- [`nth`](#nth)
- [`nthnext`](#nthnext)
- [`partition-all`](#partition-all)
- [`partition-by`](#partition-by)
- [`persistent!`](#persistent)
- [`pop`](#pop)
- [`pop!`](#pop-1)
- [`random-sample`](#random-sample)
- [`realized?`](#realized)
- [`reduced?`](#reduced-1)
- [`reductions`](#reductions)
- [`remove`](#remove)
- [`repeat`](#repeat)
- [`repeatedly`](#repeatedly)
- [`replace`](#replace)
- [`rseq`](#rseq)
- [`seq?`](#seq-1)
- [`sequence`](#sequence)
- [`some?`](#some-1)
- [`sort`](#sort)
- [`split-at`](#split-at)
- [`split-with`](#split-with)
- [`take-last`](#take-last)
- [`take-nth`](#take-nth)
- [`take-while`](#take-while)
- [`transduce`](#transduce)
- [`transient`](#transient)
- [`tree-seq`](#tree-seq)
- [`unreduced`](#unreduced)
- [`update`](#update)
- [`update-in`](#update-in)
- [`vec`](#vec)
- [`zipmap`](#zipmap)

## `ns`
Function signature:

```
(ns name commentary requirements)
```

Namespace declaration macro.
Accepts the `name` of the generated namespace, and creates a local
variable with this name holding a table. Optionally accepts
`commentary` describing what namespace is about and a `requirements`
spec, specifying what libraries should be required.

The `requirements` spec is a list that consists of vectors, specifying
library name and a possible alias or a vector of names to refer to
without a prefix:

``` fennel
(ns some-namespace
  "Description of the some-namespace."
  (:require [some.lib]
            [some.other.lib :as lib2]
            [another.lib :refer [foo bar baz]]))

(defn inc [x] (+ x 1))
```

Which is equivalent to:

``` fennel
(local some-namespace {})
(local lib (require :some.lib))
(local lib2 (require :some.other.lib))
(local {:bar bar :baz baz :foo foo} (require :another.lib))
(comment "Description of the some-namespace.")
```

Note that when no `:as` alias is given, the library will be named
after the innermost part of the require path, i.e. `some.lib` is
transformed to `lib`.

See `in-ns` on how to switch namespaces.

## `in-ns`
Function signature:

```
(in-ns name)
```

Sets the compile-time variable `cljlib-namespaces` to the given `name`.
Affects such macros as `def`, `defn`, which will bind names to the
specified namespace.

### Examples
Creating several namespaces in the file, and defining functions in each:

``` fennel
(ns a)
(defn f [] "f from a")
(ns b)
(defn f [] "f from b")
(in-ns a)
(defn g [] "g from a")
(in-ns b)
(defn g [] "g from b")

(assert-eq (a.f) "f from a")
(assert-eq (b.f) "f from b")
(assert-eq (a.g) "g from a")
(assert-eq (b.g) "g from b")
```

Note, switching namespaces in the REPL doesn't affect non-namespaced
local bindings.  In other words, when defining a local with `def`, a
bot a local binding and a namespaced binding are created, and
switching current namespace won't change the local binding:

``` fennel
>> (ns foo)
nil
>> (def x 42)
nil
>> (ns bar)
nil
>> (def x 1337)
nil
>> (in-ns foo)
#<namespace: foo>
>> x ; user might have expected to see 42 here
1337
>> foo.x
42
>> bar.x
1337
```

Sadly, Fennel itself has no support for namespace switching in REPL,
so this feature can be only partially emulated by the cljlib library.


## `def`
Function signature:

```
(def ([name initializer]) ([meta name initializer]))
```

Name binding macro similar to `local` but acts in terms of current
namespace set with the `ns` macro, unless `:private` was passed before
the binding name. Accepts the `name` to be bound and the `initializer`
expression. `meta` can be either an associative table where keys are
strings, or a string representing a key from the table. If a sole
string is given, its value is set to `true` in the meta table.

## `fn*`
Function signature:

```
(fn* ([name doc-string? [params*] pre-post? body]) ([name doc-string? ([params*] pre-post? body) +]))
```

Clojure-inspired `fn` macro for defining functions.
Accepts an optional `name` and `docstring?`, followed by the binding
list containing function's `params*`. The `body` is wrapped in an
implicit `do`.  The `doc-string?` argument specifies an optional
documentation for the function.  Supports multi-arity dispatching via
the following syntax:

(fn* optional-name
  optional-docstring
  ([arity1] body1)
  ([other arity2] body2))

Accepts `pre-post?` conditions in a form of a table after argument
list:

(fn* optional-name
  optional-docstring
  [arg1 arg2]
  {:pre  [(check1 arg1 arg2) (check2 arg1)]
   :post [(check1 $) ... (checkN $)]}
  body)

The same syntax applies to multi-arity version.

(pre- and post-checks are not yet implemented)

## `defn`
Function signature:

```
(defn ([name doc-string? [params*] pre-post? body]) ([name doc-string? ([params*] pre-post? body) +]))
```

Same as `(def name (fn* name docstring? [params*] pre-post? exprs*))`
or `(def name (fn* name docstring? ([params*] pre-post? exprs*)+))`
with any doc-string or attrs added to the function metadata.  Accepts
`name` which will be used to refer to a function in the current
namespace, and optional `doc-string?`, a vector of function's
`params*`, `pre-post?` conditions, and the `body` of the function.
The body is wrapped in an implicit do.  See `fn*` for more info.

## `defn-`
Function signature:

```
(defn- ([name doc-string? [params*] pre-post? body]) ([name doc-string? ([params*] pre-post? body) +]))
```

Same as `(def :private name (fn* name docstring? [params*] pre-post?
exprs*))` or `(def :private name (fn* name docstring? ([params*]
pre-post?  exprs*)+))` with any doc-string or attrs added to the
function metadata. Accepts `name` which will be used to refer to a
function, and optional `doc-string?`, a vector of function's
`params*`, `pre-post?` conditions, and the `body` of the function.
The body is wrapped in an implicit do. See `fn*` for more info.

## `time`
Function signature:

```
(time expr)
```

Measure the CPU time spent executing `expr`.

## `if-let`
Function signature:

```
(if-let [name test] if-branch else-branch)
```

When `test` is logical `true`, evaluates the `if-branch` with `name`
bound to the value of `test`. Otherwise, evaluates the `else-branch`

## `when-let`
Function signature:

```
(when-let [name test] & body)
```

When `test` is logical `true`, evaluates the `body` with `name` bound
to the value of `test`.

## `if-some`
Function signature:

```
(if-some [name test] if-branch else-branch)
```

When `test` is not `nil`, evaluates the `if-branch` with `name`
bound to the value of `test`. Otherwise, evaluates the `else-branch`

## `when-some`
Function signature:

```
(when-some [name test] & body)
```

When `test` is not `nil`, evaluates the `body` with `name` bound to
the value of `test`.

## `defmulti`
Function signature:

```
(defmulti name docstring? dispatch-fn options*)
```

Create multifunction `name` with runtime dispatching based on results
from `dispatch-fn`.  Returns a proxy table with `__call` metamethod,
that calls `dispatch-fn` on its arguments.  Amount of arguments
passed, should be the same as accepted by `dispatch-fn`.  Looks for
multimethod based on result from `dispatch-fn`.

Accepts optional `docstring?`, and `options*` arguments, where
`options*` is a sequence of key value pairs representing additional
attributes.  Supported options:

`:default` - the default dispatch value, defaults to `:default`.

By default, multifunction has no multimethods, see
[`defmethod`](#defmethod) on how to add one.

## `defmethod`
Function signature:

```
(defmethod multi-fn dispatch-value fnspec)
```

Attach new method to multi-function dispatch value. Accepts the
`multi-fn` as its first argument, the `dispatch-value` as second, and
`fnspec` - a function tail starting from argument list, followed by
function body as in [`fn*`](#fn).

### Examples
Here are some examples how multimethods can be used.

#### Factorial example
Key idea here is that multimethods can call itself with different
values, and will dispatch correctly.  Here, `fac` recursively calls
itself with less and less number until it reaches `0` and dispatches
to another multimethod:

``` fennel
(ns test)

(defmulti fac (fn [x] x))

(defmethod fac 0 [_] 1)
(defmethod fac :default [x] (* x (fac (- x 1))))

(assert-eq (fac 4) 24)
```

`:default` is a special method which gets called when no other methods
were found for given dispatch value.

#### Multi-arity dispatching
Multi-arity function tails are also supported:

``` fennel
(ns test)

(defmulti foo (fn* ([x] [x]) ([x y] [x y])))

(defmethod foo [10] [_] (print "I knew I'll get 10"))
(defmethod foo [10 20] [_ _] (print "I knew I'll get both 10 and 20"))
(defmethod foo :default ([x] (print (.. "Umm, got" x)))
                        ([x y] (print (.. "Umm, got both " x " and " y))))
```

Calling `(foo 10)` will print `"I knew I'll get 10"`, and calling
`(foo 10 20)` will print `"I knew I'll get both 10 and 20"`.
However, calling `foo` with any other numbers will default either to
`"Umm, got x"` message, when called with single value, and `"Umm, got
both x and y"` when calling with two values.

#### Dispatching on object's type
We can dispatch based on types the same way we dispatch on values.
For example, here's a naive conversion from Fennel's notation for
tables to Lua's one:

``` fennel
(ns test)

(defmulti to-lua-str (fn [x] (type x)))

(defmethod to-lua-str :number [x] (tostring x))
(defmethod to-lua-str :table [x]
  (let [res []]
    (each [k v (pairs x)]
      (table.insert res (.. "[" (to-lua-str k) "] = " (to-lua-str v))))
    (.. "{" (table.concat res ", ") "}")))
(defmethod to-lua-str :string [x] (.. "\"" x "\""))
(defmethod to-lua-str :default [x] (tostring x))

(assert-eq (to-lua-str {:a {:b 10}}) "{[\"a\"] = {[\"b\"] = 10}}")

(assert-eq (to-lua-str [:a :b :c [:d {:e :f}]])
           "{[1] = \"a\", [2] = \"b\", [3] = \"c\", [4] = {[1] = \"d\", [2] = {[\"e\"] = \"f\"}}}")
```

And if we call it on some table, we'll get a valid Lua table, which we
can then reformat as we want and use in Lua.

All of this can be done with functions, and single entry point
function, that uses if statement and branches on the type, however one
of the additional features of multimethods, is that separate libraries
can extend such multimethod by adding additional claues to it without
needing to patch the source of the function.  For example later on
support for userdata or coroutines can be added to `to-lua-str`
function as a separate multimethods for respective types.

## `cond`
Function signature:

```
(cond ...)
```

Takes a set of test expression pairs. It evaluates each test one at a
time.  If a test returns logical true, `cond` evaluates and returns
the value of the corresponding expression and doesn't evaluate any of
the other tests or exprs. `(cond)` returns nil.

## `loop`
Function signature:

```
(loop binding-vec body*)
```

Recursive loop macro.

Similar to `let`, but binds a special `recur` call that will reassign
the values of the `binding-vec` and restart the loop `body*`.  Unlike
`let`, doesn't support multiple-value destructuring.

The first argument is a binding table with alternating symbols (or destructure
forms), and the values to bind to them.

For example:

``` fennel
(loop [[first & rest] [1 2 3 4 5]
       i 0]
  (if (= nil first)
      i
      (recur rest (+ 1 i))))
```

This would destructure the first table argument, with the first value inside it
being assigned to `first` and the remainder of the table being assigned to
`rest`. `i` simply gets bound to 0.

The body of the form executes for every item in the table, calling `recur` each
time with the table lacking its head element (thus consuming one element per
iteration), and with `i` being called with one value greater than the previous.

When the loop terminates (When the user doesn't call `recur`) it will return the
number of elements in the passed in table. (In this case, 5)

### Limitations

In order to only evaluate expressions once and support sequential
bindings, the binding table has to be transformed like this:

``` fennel
(loop [[x & xs] (foo)
       y (+ x 1)]
  ...)

(let [_1_ (foo)
      [x & xs] _1_
      _2_ (+ x 1)
      y _2_]
  ((fn recur [[x & xs] y] ...) _1_ _2_)
```

This ensures that `foo` is called only once, its result is cached in a
`sym1#` binding, and that `y` can use the destructured value, obtained
from that binding.  The value of this binding is later passed to the
function to begin the first iteration.

This has two unfortunate consequences.  One is that the initial
destructuring happens twice - first, to make sure that later bindings
can be properly initialized, and second, when the first looping
function call happens.  Another one is that as a result, `loop` macro
can't work with multiple-value destructuring, because these can't be
cached as described above.  E.g. this will not work:

``` fennel
(loop [(x y) (foo)] ...)
```

Because it would be transformed to:

``` fennel
(let [_1_ (foo)
      (x y) _1_]
  ((fn recur [(x y)] ...) _1_)
```

`x` is correctly set, but `y` is completely lost.  Therefore, this
macro checks for lists in bindings.

## `try`
Function signature:

```
(try body* catch-clause* finally-clause?)
```

General purpose try/catch/finally macro.
Wraps its body in `pcall` and checks the return value with `match`
macro.

Catch clause is written either as `(catch symbol body*)`, thus acting
as catch-all, or `(catch value body*)` for catching specific errors.
It is possible to have several `catch` clauses.  If no `catch` clauses
specified, an implicit catch-all clause is created.  `body*`, and
inner expressions of `catch-clause*`, and `finally-clause?` are
wrapped in implicit `do`.

The `finally` clause is optional, and written as (finally body*).  If
present, it must be the last clause in the [`try`](#try) form, and the only
`finally` clause.  Note that `finally` clause is for side effects
only, and runs either after succesful run of [`try`](#try) body, or after any
`catch` clause body, before returning the result.  If no `catch`
clause is provided `finally` runs in implicit catch-all clause, and
trows error to upper scope using `error` function.

To throw error from [`try`](#try) to catch it with `catch` clause use `error`
or `assert` functions.

### Examples
Catch all errors, ignore those and return fallback value:

``` fennel
(fn add [x y]
  (try
    (+ x y)
    (catch _ 0)))

(assert-eq (add nil 1) 0)
```

Catch error and do cleanup:

``` fennel
(local tbl [])

(try
  (table.insert tbl "a")
  (table.insert tbl "b" "c")
  (catch _
    (each [k _ (pairs tbl)]
      (tset tbl k nil))))

(assert-eq (length tbl) 0)

```

Always run some side effect action:

``` fennel
(local t [])
(local res (try 10 (finally (table.insert t :finally))))
(assert-eq (. t 1) :finally)
(assert-eq res 10)

(local res (try (error 10) (catch 10 nil) (finally (table.insert t :again))))
(assert-eq (. t 2) :again)
(assert-eq res nil)
```

## `lazy-seq`
Function signature:

```
(lazy-seq & body)
```

Takes a `body` of expressions that returns a sequence, table or nil,
and yields a lazy sequence that will invoke the body only the first
time `seq` is called, and will cache the result and return it on all
subsequent `seq` calls. See also - `realized?`

## `lazy-cat`
Function signature:

```
(lazy-cat & colls)
```

Expands to code which yields a lazy sequence of the concatenation of
`colls` - expressions returning collections.  Each expression is not
evaluated until it is needed.

## `apply`
Function signature:

```
(apply ([f args]) ([f a args]) ([f a b args]) ([f a b c args]) ([f a b c d & args]))
```

Apply `f` to the argument list formed by prepending intervening
arguments to `args`, and `f` must support variadic amount of
arguments.

### Examples
Applying `add` to different amount of arguments:

``` fennel
(assert-eq (apply add [1 2 3 4]) 10)
(assert-eq (apply add 1 [2 3 4]) 10)
(assert-eq (apply add 1 2 3 4 5 6 [7 8 9]) 45)
```

## `add`
Function signature:

```
(add ([]) ([a]) ([a b]) ([a b c]) ([a b c d]) ([a b c d & rest]))
```

Sum arbitrary amount of numbers.

## `sub`
Function signature:

```
(sub ([]) ([a]) ([a b]) ([a b c]) ([a b c d]) ([a b c d & rest]))
```

Subtract arbitrary amount of numbers.

## `mul`
Function signature:

```
(mul ([]) ([a]) ([a b]) ([a b c]) ([a b c d]) ([a b c d & rest]))
```

Multiply arbitrary amount of numbers.

## `div`
Function signature:

```
(div ([a]) ([a b]) ([a b c]) ([a b c d]) ([a b c d & rest]))
```

Divide arbitrary amount of numbers.

## `le`
Function signature:

```
(le ([a]) ([a b]) ([a b & [c d & more]]))
```

Returns true if nums are in monotonically non-decreasing order

## `lt`
Function signature:

```
(lt ([a]) ([a b]) ([a b & [c d & more]]))
```

Returns true if nums are in monotonically decreasing order

## `ge`
Function signature:

```
(ge ([a]) ([a b]) ([a b & [c d & more]]))
```

Returns true if nums are in monotonically non-increasing order

## `gt`
Function signature:

```
(gt ([a]) ([a b]) ([a b & [c d & more]]))
```

Returns true if nums are in monotonically increasing order

## `inc`
Function signature:

```
(inc [x])
```

Increase number `x` by one

## `dec`
Function signature:

```
(dec [x])
```

Decrease number `x` by one

## `eq`
Function signature:

```
(eq ([]) ([_]) ([a b]) ([a b & cs]))
```

Comparison function.

Accepts arbitrary amount of values, and does the deep comparison.  If
values implement `__eq` metamethod, tries to use it, by checking if
first value is equal to second value, and the second value is equal to
the first value.  If values are not equal and are tables does the deep
comparison.  Tables as keys are supported.

## `map?`
Function signature:

```
(map? [x])
```

Check whether `x` is an associative table.

Non-empty tables are tested by calling `next`. If the length of the
table is greater than zero, the last integer key is passed to the
`next`, and if `next` returns a key, the table is considered
associative. If the length is zero, `next` is called with what `paris`
returns for the table, and if the key is returned, table is considered
associative.

Empty tables can't be analyzed with this method, and `map?` will
always return `false`.  If you need this test pass for empty table,
see `hash-map` for creating tables that have additional metadata
attached for this test to work.

### Examples
Non-empty map:

``` fennel
(assert-is (map? {:a 1 :b 2}))
```

Empty tables don't pass the test:

``` fennel
(assert-not (map? {}))
```

Empty tables created with `hash-map` will pass the test:

``` fennel
(assert-is (map? (hash-map)))
```

## `vector?`
Function signature:

```
(vector? [x])
```

Check whether `tbl` is a sequential table.

Non-empty sequential tables are tested for two things:
- `next` returns the key-value pair,
- key, that is returned by the `next` is equal to `1`.

Empty tables can't be analyzed with this method, and `vector?` will
always return `false`.  If you need this test pass for empty table,
see `vector` for creating tables that have additional
metadata attached for this test to work.

### Examples
Non-empty vector:

``` fennel
(assert-is (vector? [1 2 3 4]))
```

Empty tables don't pass the test:

``` fennel
(assert-not (vector? []))
```

Empty tables created with `vector` will pass the test:

``` fennel
(assert-is (vector? (vector)))
```

## `multifn?`
Function signature:

```
(multifn? [mf])
```

Test if `mf` is an instance of `multifn`.

`multifn` is a special kind of table, created with [`defmulti`](#defmulti) macros
from `macros.fnl`.

## `set?`
Function signature:

```
(set? [x])
```

Check if object is a set.

## `nil?`
Function signature:

```
(nil? ([]) ([x]))
```

Test if `x` is nil.

## `zero?`
Function signature:

```
(zero? [x])
```

Test if `x` is equal to zero.

## `pos?`
Function signature:

```
(pos? [x])
```

Test if `x` is greater than zero.

## `neg?`
Function signature:

```
(neg? [x])
```

Test if `x` is less than zero.

## `even?`
Function signature:

```
(even? [x])
```

Test if `x` is even.

## `odd?`
Function signature:

```
(odd? [x])
```

Test if `x` is odd.

## `string?`
Function signature:

```
(string? [x])
```

Test if `x` is a string.

## `boolean?`
Function signature:

```
(boolean? [x])
```

Test if `x` is a Boolean

## `true?`
Function signature:

```
(true? [x])
```

Test if `x` is `true`

## `false?`
Function signature:

```
(false? [x])
```

Test if `x` is `false`

## `int?`
Function signature:

```
(int? [x])
```

Test if `x` is a number without floating point data.

Number is rounded with `math.floor` and compared with original number.

## `pos-int?`
Function signature:

```
(pos-int? [x])
```

Test if `x` is a positive integer.

## `neg-int?`
Function signature:

```
(neg-int? [x])
```

Test if `x` is a negative integer.

## `double?`
Function signature:

```
(double? [x])
```

Test if `x` is a number with floating point data.

## `empty?`
Function signature:

```
(empty? [x])
```

Check if collection is empty.

## `not-empty`
Function signature:

```
(not-empty [x])
```

If `x` is empty, returns `nil`, otherwise `x`.

## `vector`
Function signature:

```
(vector [& args])
```

Constructs sequential table out of its arguments.

Sets additional metadata for function `vector?` to work.

### Examples

``` fennel
(def :private v (vector 1 2 3 4))
(assert-eq v [1 2 3 4])
```

## `seq`
Function signature:

```
(seq [coll])
```

Construct a sequence from the given collection `coll`.  If `coll` is
an associative table, returns sequence of vectors with key and value.
If `col` is sequential table, returns its shallow copy.  If `col` is
string, return sequential table of its codepoints.

### Examples
Sequential tables are transformed to sequences:

``` fennel
(seq [1 2 3 4]) ;; @seq(1 2 3 4)
```

Associative tables are transformed to format like this `[[key1 value1]
... [keyN valueN]]` and order is non-deterministic:

``` fennel
(seq {:a 1 :b 2 :c 3}) ;; @seq([:b 2] [:a 1] [:c 3])
```

## `first`
Function signature:

```
(first [coll])
```

Return first element of a `coll`. Calls `seq` on its argument.

## `rest`
Function signature:

```
(rest [coll])
```

Returns a sequence of all elements of a `coll` but the first one.
Calls `seq` on its argument.

## `last`
Function signature:

```
(last [coll])
```

Returns the last element of a `coll`. Calls `seq` on its argument.

## `butlast`
Function signature:

```
(butlast [coll])
```

Returns everything but the last element of the `coll` as a new
  sequence.  Calls `seq` on its argument.

## `conj`
Function signature:

```
(conj ([]) ([s]) ([s x]) ([s x & xs]))
```

Insert `x` as a last element of a table `tbl`.

If `tbl` is a sequential table or empty table, inserts `x` and
optional `xs` as final element in the table.

If `tbl` is an associative table, that satisfies `map?` test,
insert `[key value]` pair into the table.

Mutates `tbl`.

### Examples
Adding to sequential tables:

``` fennel
(conj [] 1 2 3 4)
;; => [1 2 3 4]
(conj [1 2 3] 4 5)
;; => [1 2 3 4 5]
```

Adding to associative tables:

``` fennel
(conj {:a 1} [:b 2] [:c 3])
;; => {:a 1 :b 2 :c 3}
```

Note, that passing literal empty associative table `{}` will not work:

``` fennel
(conj {} [:a 1] [:b 2])
;; => [[:a 1] [:b 2]]
(conj (hash-map) [:a 1] [:b 2])
;; => {:a 1 :b 2}
```

See `hash-map` for creating empty associative tables.

## `disj`
Function signature:

```
(disj ([Set]) ([Set key]) ([Set key & keys]))
```

Returns a new set type, that does not contain the
specified `key` or `keys`.

## `cons`
Function signature:

```
(cons [head tail])
```

Construct a cons cell.
Prepends new `head` to a `tail`, which must be either a table,
sequence, or nil.

### Examples

``` fennel
(assert-eq [0 1] (cons 0 [1]))
(assert-eq (list 0 1 2 3) (cons 0 (cons 1 (list 2 3))))
```

## `concat`
Function signature:

```
(concat [& colls])
```

Return a lazy sequence of concatenated `colls`.

## `reduce`
Function signature:

```
(reduce ([f coll]) ([f val coll]))
```

`f` should be a function of 2 arguments. If `val` is not supplied,
returns the result of applying `f` to the first 2 items in `coll`,
then applying `f` to that result and the 3rd item, etc. If `coll`
contains no items, f must accept no arguments as well, and reduce
returns the result of calling `f` with no arguments.  If `coll` has
only 1 item, it is returned and `f` is not called.  If `val` is
supplied, returns the result of applying `f` to `val` and the first
item in `coll`, then applying `f` to that result and the 2nd item,
etc. If `coll` contains no items, returns `val` and `f` is not
called. Early termination is supported via `reduced`.

### Examples

``` fennel
(defn- add
  ([] 0)
  ([a] a)
  ([a b] (+ a b))
  ([a b & cs] (apply add (+ a b) cs)))
;; no initial value
(assert-eq 10 (reduce add [1 2 3 4]))
;; initial value
(assert-eq 10 (reduce add 1 [2 3 4]))
;; empty collection - function is called with 0 args
(assert-eq 0 (reduce add []))
(assert-eq 10.3 (reduce math.floor 10.3 []))
;; collection with a single element doesn't call a function unless the
;; initial value is supplied
(assert-eq 10.3 (reduce math.floor [10.3]))
(assert-eq 7 (reduce add 3 [4]))
```

## `reduced`
Function signature:

```
(reduced [value])
```

Terminates the `reduce` early with a given `value`.

### Examples

``` fennel
(assert-eq :NaN
           (reduce (fn [acc x]
                     (if (not= :number (type x))
                         (reduced :NaN)
                         (+ acc x)))
                   [1 2 :3 4 5]))
```

## `reduce-kv`
Function signature:

```
(reduce-kv [f val s])
```

Reduces an associative table using function `f` and initial value `val`.

`f` should be a function of 3 arguments.  Returns the result of
applying `f` to `val`, the first key and the first value in `tbl`,
then applying `f` to that result and the 2nd key and value, etc.  If
`tbl` contains no entries, returns `val` and `f` is not called.  Note
that `reduce-kv` is supported on sequential tables and strings, where
the keys will be the ordinals.

Early termination is possible with the use of `reduced`
function.

### Examples
Reduce associative table by adding values from all keys:

``` fennel
(local t {:a1 1
          :b1 2
          :a2 2
          :b2 3})

(reduce-kv #(+ $1 $3) 0 t)
;; => 8
```

Reduce table by adding values from keys that start with letter `a`:

``` fennel
(local t {:a1 1
          :b1 2
          :a2 2
          :b2 3})

(reduce-kv (fn [res k v] (if (= (string.sub k 1 1) :a) (+ res v) res))
           0 t)
;; => 3
```

## `mapv`
Function signature:

```
(mapv ([f coll]) ([f coll & colls]))
```

Returns a vector consisting of the result of applying `f` to the
set of first items of each `coll`, followed by applying `f` to the set
of second items in each coll, until any one of the `colls` is
exhausted.  Any remaining items in other collections are ignored.
Function `f` should accept number-of-colls arguments.

## `filter`
Function signature:

```
(filter ([pred]) ([pred coll]))
```

Returns a lazy sequence of the items in `coll` for which
`pred` returns logical true. Returns a transducer when no collection
is provided.

## `every?`
Function signature:

```
(every? [pred coll])
```

Test if every item in `coll` satisfies the `pred`.

## `some`
Function signature:

```
(some [pred coll])
```

Test if any item in `coll` satisfies the `pred`.

## `not-any?`
Function signature:

```
(not-any? [pred coll])
```

Test if no item in `coll` satisfy the `pred`.

## `range`
Function signature:

```
(range ([]) ([upper]) ([lower upper]) ([lower upper step]))
```

Returns lazy sequence of numbers from `lower` to `upper` with optional
`step`.

## `reverse`
Function signature:

```
(reverse [coll])
```

Returns a lazy sequence with same items as in `coll` but in reverse order.

## `take`
Function signature:

```
(take ([n]) ([n coll]))
```

Returns a lazy sequence of the first `n` items in `coll`, or all items if
there are fewer than `n`.

## `nthrest`
Function signature:

```
(nthrest [coll n])
```

Returns the nth rest of `coll`, `coll` when `n` is 0.

### Examples

``` fennel
(assert-eq (nthrest [1 2 3 4] 3) [4])
(assert-eq (nthrest [1 2 3 4] 2) [3 4])
(assert-eq (nthrest [1 2 3 4] 1) [2 3 4])
(assert-eq (nthrest [1 2 3 4] 0) [1 2 3 4])
```


## `partition`
Function signature:

```
(partition ([n coll]) ([n step coll]) ([n step pad coll]))
```

Given a collection `coll`, returns a lazy sequence of lists of `n`
items each, at offsets `step` apart. If `step` is not supplied,
defaults to `n`, i.e. the partitions do not overlap. If a `pad`
collection is supplied, use its elements as necessary to complete last
partition up to `n` items. In case there are not enough padding
elements, return a partition with less than `n` items.

## `identity`
Function signature:

```
(identity [x])
```

Returns its argument.

## `comp`
Function signature:

```
(comp ([]) ([f]) ([f g]) ([f g & fs]))
```

Compose functions.

## `complement`
Function signature:

```
(complement [f])
```

Takes a function `f` and returns the function that takes the same
amount of arguments as `f`, has the same effect, and returns the
opposite truth value.

## `constantly`
Function signature:

```
(constantly [x])
```

Returns a function that takes any number of arguments and returns `x`.

## `memoize`
Function signature:

```
(memoize [f])
```

Returns a memoized version of a referentially transparent function.
The memoized version of the function keeps a cache of the mapping from
arguments to results and, when calls with the same arguments are
repeated often, has higher performance at the expense of higher memory
use.

## `assoc`
Function signature:

```
(assoc ([tbl]) ([tbl k v]) ([tbl k v & kvs]))
```

Associate `val` under a `key`.
Accepts extra keys and values.

### Examples

``` fennel
(assert-eq {:a 1 :b 2} (assoc {:a 1} :b 2))
(assert-eq {:a 1 :b 2} (assoc {:a 1 :b 1} :b 2))
(assert-eq {:a 1 :b 2 :c 3} (assoc {:a 1 :b 1} :b 2 :c 3))
```

## `hash-map`
Function signature:

```
(hash-map [& kvs])
```

Create associative table from `kvs` represented as sequence of keys
and values

## `get`
Function signature:

```
(get ([tbl key]) ([tbl key not-found]))
```

Get value from the table by accessing it with a `key`.
Accepts additional `not-found` as a marker to return if value wasn't
found in the table.

## `get-in`
Function signature:

```
(get-in ([tbl keys]) ([tbl keys not-found]))
```

Get value from nested set of tables by providing key sequence.
Accepts additional `not-found` as a marker to return if value wasn't
found in the table.

## `keys`
Function signature:

```
(keys [coll])
```

Returns a sequence of the map's keys, in the same order as `seq`.

## `vals`
Function signature:

```
(vals [coll])
```

Returns a sequence of the table's values, in the same order as `seq`.

## `find`
Function signature:

```
(find [coll key])
```

Returns the map entry for `key`, or `nil` if key is not present in
`coll`.

## `dissoc`
Function signature:

```
(dissoc ([tbl]) ([tbl key]) ([tbl key & keys]))
```

Remove `key` from table `tbl`.  Optionally takes more `keys`.

## `remove-method`
Function signature:

```
(remove-method [multimethod dispatch-value])
```

Remove method from `multimethod` for given `dispatch-value`.

## `remove-all-methods`
Function signature:

```
(remove-all-methods [multimethod])
```

Removes all methods of `multimethod`

## `methods`
Function signature:

```
(methods [multimethod])
```

Given a `multimethod`, returns a map of dispatch values -> dispatch fns

## `get-method`
Function signature:

```
(get-method [multimethod dispatch-value])
```

Given a `multimethod` and a `dispatch-value`, returns the dispatch
`fn` that would apply to that value, or `nil` if none apply and no
default.

## `hash-set`
Function signature:

```
(hash-set [& xs])
```

Create hash set.

Set is a collection of unique elements, which sore purpose is only to
tell you if something is in the set or not.

## `assoc!`
Function signature:

```
(assoc! [map k & ks])
```

Remove `k`from transient map, and return `map`.

## `assoc-in`
Function signature:

```
(assoc-in [tbl key-seq val])
```

Associate `val` into set of immutable nested tables `t`, via given `key-seq`.
Returns a new immutable table.  Returns a new immutable table.

### Examples

Replace value under nested keys:

``` fennel
(assert-eq
 {:a {:b {:c 1}}}
 (assoc-in {:a {:b {:c 0}}} [:a :b :c] 1))
```

Create new entries as you go:

``` fennel
(assert-eq
 {:a {:b {:c 1}} :e 2}
 (assoc-in {:e 2} [:a :b :c] 1))
```

## `cat`
Function signature:

```
(cat [rf])
```

A transducer which concatenates the contents of each input, which must be a
  collection, into the reduction. Accepts the reducing function `rf`.

## `class`
Function signature:

```
(class [x])
```

Return cljlib type of the `x`, or lua type.

## `completing`
Function signature:

```
(completing ([f]) ([f cf]))
```

Takes a reducing function `f` of 2 args and returns a function
suitable for transduce by adding an arity-1 signature that calls
`cf` (default - `identity`) on the result argument.

## `conj!`
Function signature:

```
(conj! ([]) ([coll]) ([coll x]))
```

Adds `x` to the transient collection, and return `coll`.

## `contains?`
Function signature:

```
(contains? [coll elt])
```

Test if `elt` is in the `coll`.  It may be a linear search depending
on the type of the collection.

## `count`
Function signature:

```
(count [s])
```

Count amount of elements in the sequence.

## `cycle`
Function signature:

```
(cycle [coll])
```

Create a lazy infinite sequence of repetitions of the items in the
`coll`.

## `dedupe`
Function signature:

```
(dedupe ([]) ([coll]))
```

Returns a lazy sequence removing consecutive duplicates in coll.
Returns a transducer when no collection is provided.

## `deref`
Function signature:

```
(deref [x])
```

Dereference an object.

## `disj!`
Function signature:

```
(disj! ([Set]) ([Set key & ks]))
```

disj[oin]. Returns a transient set of the same type, that does not
contain `key`.

## `dissoc!`
Function signature:

```
(dissoc! [map k & ks])
```

Remove `k`from transient map, and return `map`.

## `distinct`
Function signature:

```
(distinct ([]) ([coll]))
```

Returns a lazy sequence of the elements of the `coll` without
duplicates.  Comparison is done by equality. Returns a transducer when
no collection is provided.

## `doall`
Function signature:

```
(doall [seq])
```

Realize whole lazy sequence `seq`.

Walks whole sequence, realizing each cell.  Use at your own risk on
infinite sequences.

## `dorun`
Function signature:

```
(dorun [seq])
```

Realize whole sequence `seq` for side effects.

Walks whole sequence, realizing each cell.  Use at your own risk on
infinite sequences.

## `drop`
Function signature:

```
(drop ([n]) ([n coll]))
```

Drop `n` elements from collection `coll`, returning a lazy sequence
of remaining elements. Returns a transducer when no collection is
provided.

## `drop-last`
Function signature:

```
(drop-last ([]) ([coll]) ([n coll]))
```

Return a lazy sequence from `coll` without last `n` elements.

## `drop-while`
Function signature:

```
(drop-while ([pred]) ([pred coll]))
```

Drop the elements from the collection `coll` until `pred` returns logical
false for any of the elemnts.  Returns a lazy sequence. Returns a
transducer when no collection is provided.

## `empty`
Function signature:

```
(empty [x])
```

Get an empty variant of a given collection.

## `ensure-reduced`
Function signature:

```
(ensure-reduced [x])
```

If x is already reduced?, returns it, else returns (reduced x)

## `filterv`
Function signature:

```
(filterv [pred coll])
```

Returns a vector of the items in `coll` for which
`pred` returns logical true.

## `frequencies`
Function signature:

```
(frequencies [t])
```

Return a table of unique entries from table `t` associated to amount
of their appearances.

### Examples

Count each entry of a random letter:

``` fennel
(let [fruits [:banana :banana :apple :strawberry :apple :banana]]
  (assert-eq (frequencies fruits)
             {:banana 3
              :apple 2
              :strawberry 1}))
```

## `group-by`
Function signature:

```
(group-by [f t])
```

Group table items in an associative table under the keys that are
results of calling `f` on each element of sequential table `t`.
Elements that the function call resulted in `nil` returned in a
separate table.

### Examples

Group rows by their date:

``` fennel
(local rows
  [{:date "2007-03-03" :product "pineapple"}
   {:date "2007-03-04" :product "pizza"}
   {:date "2007-03-04" :product "pineapple pizza"}
   {:date "2007-03-05" :product "bananas"}])

(assert-eq (group-by #(. $ :date) rows)
           {"2007-03-03"
            [{:date "2007-03-03" :product "pineapple"}]
            "2007-03-04"
            [{:date "2007-03-04" :product "pizza"}
             {:date "2007-03-04" :product "pineapple pizza"}]
            "2007-03-05"
            [{:date "2007-03-05" :product "bananas"}]})
```

## `halt-when`
Function signature:

```
(halt-when ([pred]) ([pred retf]))
```

Returns a transducer that ends transduction when `pred` returns `true`
for an input. When `retf` is supplied it must be a `fn` of 2 arguments
- it will be passed the (completed) result so far and the input that
triggered the predicate, and its return value (if it does not throw an
exception) will be the return value of the transducer. If `retf` is
not supplied, the input that triggered the predicate will be
returned. If the predicate never returns `true` the transduction is
unaffected.

## `interleave`
Function signature:

```
(interleave ([]) ([s]) ([s1 s2]) ([s1 s2 & ss]))
```

Returns a lazy sequence of the first item in each sequence, then the
second one, until any sequence exhausts.

## `interpose`
Function signature:

```
(interpose ([sep]) ([separator coll]))
```

Returns a lazy sequence of the elements of `coll` separated by
`separator`. Returns a transducer when no collection is provided.

## `into`
Function signature:

```
(into ([]) ([to]) ([to from]) ([to xform from]))
```

Returns a new coll consisting of `to` with all of the items of `from`
conjoined. A transducer `xform` may be supplied.

### Examples

Insert items of one collection into another collection:

```fennel
(assert-eq [1 2 3 :a :b :c] (into [1 2 3] "abc"))
(assert-eq {:a 2 :b 3} (into {:a 1} {:a 2 :b 3}))
```

Transform a hash-map into a sequence of key-value pairs:

``` fennel
(assert-eq [[:a 1]] (into (vector) {:a 1}))
```

You can also construct a hash-map from a sequence of key-value pairs:

``` fennel
(assert-eq {:a 1 :b 2 :c 3}
           (into (hash-map) [[:a 1] [:b 2] [:c 3]]))
```

## `iterate`
Function signature:

```
(iterate [f x])
```

Returns an infinete lazy sequence of x, (f x), (f (f x)) etc.

## `keep`
Function signature:

```
(keep ([f]) ([f coll]))
```

Returns a lazy sequence of the non-nil results of calling `f` on the
items of the `coll`. Returns a transducer when no collection is
provided.

## `keep-indexed`
Function signature:

```
(keep-indexed ([f]) ([f coll]))
```

Returns a lazy sequence of the non-nil results of (f index item) in
the `coll`.  Note, this means false return values will be included.
`f` must be free of side effects. Returns a transducer when no
collection is provided.

## `line-seq`
Function signature:

```
(line-seq [file])
```

Accepts a `file` handle, and creates a lazy sequence of lines using
`lines` metamethod.

### Examples

Lazy sequence of file lines may seem similar to an iterator over a
file, but the main difference is that sequence can be shared onve
realized, and iterator can't.  Lazy sequence can be consumed in
iterator style with the `doseq` macro.

Bear in mind, that since the sequence is lazy it should be realized or
truncated before the file is closed:

``` fennel
(let [lines (with-open [f (io.open "cljlib.fnl" :r)]
              (line-seq f))]
  ;; this will error because only first line was realized, but the
  ;; file was closed before the rest of lines were cached
  (assert-not (pcall next lines)))
```

Sequence is realized with `doall` before file was closed and can be shared:

``` fennel
(let [lines (with-open [f (io.open "cljlib.fnl" :r)]
              (doall (line-seq f)))]
  (assert-is (pcall next lines)))
```

Infinite files can't be fully realized, but can be partially realized
with `take`:

``` fennel
(let [lines (with-open [f (io.open "/dev/urandom" :r)]
              (doall (take 3 (line-seq f))))]
  (assert-is (pcall next lines)))
```

## `list`
Function signature:

```
(list ...)
```

Create eager sequence of provided values.

### Examples

``` fennel
(local l (list 1 2 3 4 5))
(assert-eq [1 2 3 4 5] l)
```

## `list*`
Function signature:

```
(list* [& args])
```

Creates a new sequence containing the items prepended to the rest,
the last of which will be treated as a sequence.

### Examples

``` fennel
(local l (list* 1 2 3 [4 5]))
(assert-eq [1 2 3 4 5] l)
```

## `map`
Function signature:

```
(map ([f]) ([f coll]) ([f coll & colls]))
```

Returns a lazy sequence consisting of the result of applying `f` to
the set of first items of each `coll`, followed by applying `f` to the
set of second items in each `coll`, until any one of the `colls` is
exhausted.  Any remaining items in other `colls` are ignored. Function
`f` should accept number-of-colls arguments. Returns a transducer when
no collection is provided.

### Examples

``` fennel
(map #(+ $ 1) [1 2 3]) ;; => @seq(2 3 4)
(map #(+ $1 $2) [1 2 3] [4 5 6]) ;; => @seq(5 7 9)
(def :private res (map #(+ $ 1) [:a :b :c])) ;; will raise an error only when realized
```

## `map-indexed`
Function signature:

```
(map-indexed ([f]) ([f coll]))
```

Returns a lazy sequence consisting of the result of applying `f` to 1
and the first item of `coll`, followed by applying `f` to 2 and the
second item in `coll`, etc., until `coll` is exhausted.  Returns a
transducer when no collection is provided.

## `mapcat`
Function signature:

```
(mapcat ([f]) ([f & colls]))
```

Apply `concat` to the result of calling `map` with `f` and
collections `colls`. Returns a transducer when no collection is
provided.

## `merge`
Function signature:

```
(merge [& maps])
```

Merge `maps` rght to left into a single hash-map.

## `next`
Function signature:

```
(next [s])
```

Return the tail of a sequence.

If the sequence is empty, returns nil.

## `nth`
Function signature:

```
(nth ([coll i]) ([coll i not-found]))
```

Returns the value at the `index`. `get` returns `nil` if `index` out
of bounds, `nth` raises an error unless `not-found` is supplied.
`nth` also works for strings and sequences.

## `nthnext`
Function signature:

```
(nthnext [coll n])
```

Returns the nth next of `coll`, (seq coll) when `n` is 0.

## `partition-all`
Function signature:

```
(partition-all ([n]) ([n coll]) ([n step coll]))
```

Given a collection `coll`, returns a lazy sequence of lists like
`partition`, but may include partitions with fewer than n items at the
end. Accepts addiitonal `step` argument, similarly to `partition`.
Returns a transducer, if collection is not supplied.

## `partition-by`
Function signature:

```
(partition-by ([f]) ([f coll]))
```

Applies `f` to each value in `coll`, splitting it each time `f`
returns a new value.  Returns a lazy seq of partitions.  Returns a
transducer, if collection is not supplied.

## `persistent!`
Function signature:

```
(persistent! [coll])
```

Returns a new, persistent version of the transient collection. The
transient collection cannot be used after this call, any such use will
raise an error.

## `pop`
Function signature:

```
(pop [coll])
```

If `coll` is a list returns a new list without the first
item. If `coll` is a vector, returns a new vector without the last
item. If the collection is empty, raises an error. Not the same as
`next` or `butlast`.

## `pop!`
Function signature:

```
(pop! [coll])
```

Removes the last item from a transient vector. If the collection is
empty, raises an error Returns coll

## `random-sample`
Function signature:

```
(random-sample ([prob]) ([prob coll]))
```

Returns items from `coll` with random probability of `prob` (0.0 -
1.0).  Returns a transducer when no collection is provided.

## `realized?`
Function signature:

```
(realized? [s])
```

Check if sequence's first element is realized.

## `reduced?`
Function signature:

```
(reduced? [x])
```

Returns true if `x` is the result of a call to reduced

## `reductions`
Function signature:

```
(reductions ([f coll]) ([f init coll]))
```

Returns a lazy seq of the intermediate values of the reduction (as
per reduce) of `coll` by `f`, starting with `init`.

## `remove`
Function signature:

```
(remove ([pred]) ([pred coll]))
```

Returns a lazy sequence of the items in the `coll` without elements
for wich `pred` returns logical true. Returns a transducer when no
collection is provided.

## `repeat`
Function signature:

```
(repeat [x])
```

Takes a value `x` and returns an infinite lazy sequence of this value.

### Examples

``` fennel
(assert-eq 20 (reduce add (take 10 (repeat 2))))
```

## `repeatedly`
Function signature:

```
(repeatedly [f & args])
```

Takes a function `f` and returns an infinite lazy sequence of
function applications.  Rest arguments are passed to the function.

## `replace`
Function signature:

```
(replace ([smap]) ([smap coll]))
```

Given a map of replacement pairs and a vector/collection `coll`,
returns a vector/seq with any elements `=` a key in `smap` replaced
with the corresponding `val` in `smap`.  Returns a transducer when no
collection is provided.

## `rseq`
Function signature:

```
(rseq [rev])
```

Returns, in possibly-constant time, a seq of the items in `rev` in reverse order.
Input must be traversable with `ipairs`.  Doesn't work in constant
time if `rev` implements a linear-time `__len` metamethod, or invoking
Lua `#` operator on `rev` takes linar time.  If `t` is empty returns
`nil`.

### Examples

``` fennel
(def :private v [1 2 3])
(def :private r (rseq v))

(assert-eq (reverse v) r)
```

## `seq?`
Function signature:

```
(seq? [x])
```

Check if object is a sequence.

## `sequence`
Function signature:

```
(sequence ([coll]) ([xform coll]) ([xform coll & colls]))
```

Coerces coll to a (possibly empty) sequence, if it is not already
one. Will not force a lazy seq. `(sequence nil)` yields an empty list,
When a transducer `xform` is supplied, returns a lazy sequence of
applications of the transform to the items in `coll`, i.e. to the set
of first items of each `coll`, followed by the set of second items in
each `coll`, until any one of the `colls` is exhausted.  Any remaining
items in other `colls` are ignored. The transform should accept
number-of-colls arguments

## `some?`
Function signature:

```
(some? [x])
```

Returns true if x is not nil, false otherwise.

## `sort`
Function signature:

```
(sort ([coll]) ([comparator coll]))
```

Returns a sorted sequence of the items in `coll`. If no `comparator`
is supplied, uses `<`.

## `split-at`
Function signature:

```
(split-at [n coll])
```

Return a table with sequence `coll` being split at `n`

## `split-with`
Function signature:

```
(split-with [pred coll])
```

Return a table with sequence `coll` being split with `pred`

## `take-last`
Function signature:

```
(take-last [n coll])
```

Return a sequence of last `n` elements of the `coll`.

## `take-nth`
Function signature:

```
(take-nth ([n]) ([n coll]))
```

Return a lazy sequence of every `n` item in `coll`. Returns a
transducer when no collection is provided.

## `take-while`
Function signature:

```
(take-while ([pred]) ([pred coll]))
```

Take the elements from the collection `coll` until `pred` returns logical
false for any of the elemnts.  Returns a lazy sequence. Returns a
transducer when no collection is provided.

## `transduce`
Function signature:

```
(transduce ([xform f coll]) ([xform f init coll]))
```

`reduce` with a transformation of `f` (`xform`). If `init` is not
supplied, `f` will be called to produce it. `f` should be a reducing
step function that accepts both 1 and 2 arguments, if it accepts only
2 you can add the arity-1 with `completing`. Returns the result of
applying (the transformed) `xform` to `init` and the first item in
`coll`, then applying `xform` to that result and the 2nd item, etc. If
`coll` contains no items, returns `init` and `f` is not called. Note
that certain transforms may inject or skip items.

## `transient`
Function signature:

```
(transient [coll])
```

Returns a new, transient version of the collection.

## `tree-seq`
Function signature:

```
(tree-seq [branch? children root])
```

Returns a lazy sequence of the nodes in a tree, via a depth-first walk.

`branch?` must be a function of one arg that returns true if passed a
node that can have children (but may not).  `children` must be a
function of one arg that returns a sequence of the children.  Will
only be called on nodes for which `branch?` returns true.  `root` is
the root node of the tree.

### Examples

For the given tree `["A" ["B" ["D"] ["E"]] ["C" ["F"]]]`:

        A
       / \
      B   C
     / \   \
    D   E   F

Calling `tree-seq` with `next` as the `branch?` and `rest` as the
`children` returns a flat representation of a tree:

``` fennel
(assert-eq (map first (tree-seq next rest ["A" ["B" ["D"] ["E"]] ["C" ["F"]]]))
           ["A" "B" "D" "E" "C" "F"])
```

## `unreduced`
Function signature:

```
(unreduced [x])
```

If `x` is `reduced?`, returns `(deref x)`, else returns `x`.

## `update`
Function signature:

```
(update [tbl key f])
```

Update table value stored under `key` by calling a function `f` on
that value. `f` must take one argument, which will be a value stored
under the key in the table.

### Examples

Same as `assoc` but accepts function to produce new value based on key value.

``` fennel
(assert-eq
 {:data "THIS SHOULD BE UPPERCASE"}
 (update {:data "this should be uppercase"} :data string.upper))
```

## `update-in`
Function signature:

```
(update-in [tbl key-seq f])
```

Update table value stored under set of immutable nested tables, via
given `key-seq` by calling a function `f` on the value stored under the
last key.  `f` must take one argument, which will be a value stored
under the key in the table.  Returns a new immutable table.

### Examples

Same as `assoc-in` but accepts function to produce new value based on key value.

``` fennel
(fn capitalize-words [s]
  (pick-values 1
    (s:gsub "(%a)([%w_`]*)" #(.. ($1:upper) ($2:lower)))))

(assert-eq
 {:user {:name "John Doe"}}
 (update-in {:user {:name "john doe"}} [:user :name] capitalize-words))
```

## `vec`
Function signature:

```
(vec [coll])
```

Coerce collection `coll` to a vector.

## `zipmap`
Function signature:

```
(zipmap [keys vals])
```

Return an associative table with the `keys` mapped to the
corresponding `vals`.


---

Copyright (C) 2020-2021 Andrey Listopadov

License: [MIT](https://gitlab.com/andreyorst/fennel-cljlib/-/raw/master/LICENSE)


<!-- Generated with Fenneldoc v1.0.1
     https://gitlab.com/andreyorst/fenneldoc -->
