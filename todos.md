- weird shenanigans in gemvBlastT
- [ ] add shiftbvars for rdata!
- [ ] natcontraints! (getting ite in gemv)
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
