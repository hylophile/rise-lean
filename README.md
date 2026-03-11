# Rise in Lean

This repository reimplements [RISE](https://rise-lang.org/) in [Lean 4](https://lean-lang.org/).

## Prerequisites

- [Lean](https://lean-lang.org/install/)
- [uv](https://docs.astral.sh/uv/getting-started/installation/) to perform nat-unification with [SymPy](https://www.sympy.org/en/index.html)
- [Rust](https://rust-lang.org/tools/install/) to perform unification with [egg](https://egraphs-good.github.io/)
- (optional) [just](https://github.com/casey/just) to run `just build` which clears build caches

## Execution

Either open any file in [`Rise/Apps/`](./Rise/Apps) and observe the Lean InfoView output which shows inferred types, or run e.g.

```sh
lake build Rise/Apps/MM.lean
```

As seen in that file, prepend `set_option egg.debug_enable true in` to a definition to enable running `egg` and show debug output such as a comparison with SymPy.

Use the command `#pp <defname>` to pretty-print the RISE expression that is defined by `<defname>`.

Optionally, increase the number of iterations that `egg` performs for simplification of natural numbers (default: 3) by changing `simp_iters` in `Rise/Unification/Egg/Bridge/Rust/src/lang.rs:421`. Note that `lake` may cache previously built Rust code, so either use `just build` instead or perform the same steps seen in the `Justfile`.

## Example Output

This is example output from `gemvBlastN` in `Rise/Apps/Gemv.lean`.

`λ` represents term-level abstraction, `Λ` represents type-level abstraction. `m@0` represents a bound variable named `m` with the De Bruijn Index `0`.

```
expr:
  (Λ n : nat =>
   (Λ m : nat =>
    (λ mat : m@0·n@1·f32 =>
     (λ xs : n@1·f32 =>
      (λ ys : m@0·f32 =>
       (λ alpha : f32 =>
        (λ beta : f32 =>
         (λ x : ((m@0/64)*64)·(((n@1/64)*64)·f32 × f32) =>
          (λ x : (m@0/64)·64·(((n@1/64)*64)·f32 × f32) =>
           join (map (λ matChunk : 64·(((n@1/64)*64)·f32 × f32) =>
             (λ x : (n@1/64)·(64·64·f32 × 64·f32) =>
              (λ y : 64·f32 =>
               map (λ x : (f32 × f32) =>
                add (mul (fst x@0) alpha@7) (mul (snd x@0) beta@6))
                (zip y@0 (map snd matChunk@2)))
               (reduceSeq (λ acc : 64·f32 =>
                (λ next : (64·64·f32 × 64·f32) =>
                 map (λ x : (f32 × 64·f32) =>
                  reduceSeq (λ acc2 : f32 =>
                   (λ next2 : (f32 × f32) =>
                    add acc2@1 (mul (fst next2@0) (snd next2@0)))
                   )
                   (fst x@0) (zip (snd x@0) (map id (snd next@1))))
                  (zip acc@1 (fst next@0)))
                )
                (map id (generate (λ dummy : idx[64] =>
                  (scientific "0.0"))
                 )) x@0))
              (zip ((λ x : 64·(((n@1/64)*64)·f32 × f32) =>
                transpose (map (λ x : (((n@1/64)*64)·f32 × f32) =>
                  split 64 (fst x@0))
                  x@0))
                matChunk@0) (split 64 xs@6)))
             x@0))
           (split 64 x@0))
          (zip mat@4 ys@2))
        )
       )
      )
     )
    )
   )
type:
  {n : nat} → {m : nat} → m@0·n@1·f32 → n@1·f32 → m@0·f32 → f32 → f32 → ((m@0/64)*64)·f32
```
