- omg downsample ???? need modulo or something.
- **ok**
  even the most complex problems are already solved [1] after **only** two iterations! however.
  this is also pretty quick. constant propagation however takes a long time, because we have assoc & comm rules.

  [1]: solved := there are no mvars in any substitution.

  so it might be a good idea to
  1. iterate twice
  2. if not solved, goto 1
  3. extract solutions and do constprop on them separately (either with a different ruleset or a different method)

- we need to simplify at least top-level types (with sympy i guess)
- add constant propagation to analysis
- locallaplacian: do we need / and /^ ?
- how do we want to deal with side conditions generated from usage? e.g. the statement "n must divide 4". should we error with a message saying that this assumption needs to be added? then we need syntax for those assumptions.
- maligemm kepler_best in sgemm.scala
- reorderwithstride; nat2nat; reorder;

---

- we should actually disallow should existence of mvars after type-checking............
- fragment, matrixLayout kinds
- [ ] add shiftbvars for rdata!
      obsolete - [ ] natcontraints! (getting ite in gemv)
  - mhhhhhhhhhhhhhhhhhhhhhhhh

  ```
    problem:
    ?m * ?n = b

    is this substitution okay? does this even still work with substutitutions?

    ?m = b/?n
    ?n = b/?m

    i think no, because if we eliminate ?n, we get

    ?m = b/(b/?m)

    and that fails the occurs check...
  ```

  Instead, maybe we want to collect all "unification attempts" of natural numbers, so all `X=Y`, and at the top level then discharge (and prove) all equalities.

---

- type ascription: (x : f32)... anywhere
- [ ] could try eqsat, probably need different substitution data structure. how to substitute there anyways?
- [ ] foreign func
- [ ] natType?
- [ ] type-level functions (TODO: we wanted to rethink those)
  - [ ] dependent pair/array ops
- [x] `+-*/^` for nats in expressions, not just types
- [x] syntax for add/mult (+/\*) in expressions.
- [x] syntax for .1 .2 (fst/snd)
- [ ] makeArray 🤯
- request: option to type-annotate rexprs which we then check against in the end
- [x] it seems that we need to collect nat equalities until we reach top level so that we have all the necessary assumptions
- [x] maybe we want a let..in ?
