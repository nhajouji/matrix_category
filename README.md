# matrix_category

Lean 4 / Mathlib formalization of the **matrix-category layer** of a paper on
elliptic curves over finite fields: the category 𝓜(α) of 2×2 integer matrices
commuting with a fixed α, binary quadratic forms, and the kernel/gcd lemmas
that drive the isogeny bookkeeping. The bridge to elliptic curves themselves
(Deuring lifting, CM theory) stays on paper — this repo formalizes the
self-contained integer-matrix core.

## Contents

- `MatrixCategory/Content.lean` — the content (gcd of entries) of an integer
  matrix; `M ≡ 0 (mod m)` over `ZMod m` iff `m ∣ content M`
  (the primitive-isogeny characterization lemma); primitivity via reductions
  mod primes.

## Building

Requires [elan](https://github.com/leanprover/elan). Then:

```
lake exe cache get   # prebuilt Mathlib
lake build
```
