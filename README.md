# matrix_category

A Lean 4 / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of the **matrix-category layer** of work in progress on
elliptic curves over finite fields (the theory behind the interactive
explorer at [elliptic-curves.info](https://elliptic-curves.info)).

The idea: the isogeny-theoretic results reduce to a self-contained core
about 2×2 integer matrices, binary quadratic forms, and kernel/gcd
bookkeeping — objects Mathlib handles well. That core is what is
formalized here; the bridge to elliptic curves themselves (Deuring
lifting, CM theory) stays on paper, since Mathlib currently has no
isogeny theory. A side effect worth advertising: the matrix category is
the *formalization-friendly* core of the theory.

**Status: work in progress. Everything below is proven — the repository
contains no `sorry`.**

## Main results

- **Kernel structure theorem** (`KernelStructure.lean`, `ker_structure`):
  for a 2×2 integer matrix `M` and `n ≠ 0`, the kernel of `M` acting on
  `(ℤ/nℤ)²` is isomorphic as an additive group to
  `ℤ/gcd(d₂,n) × ℤ/gcd(d₁,n)`, where `d₁ = content M` (gcd of entries)
  and `d₂ = |det M| / d₁` are the Smith invariants. No hypothesis on
  `det M` is needed.
- **Smith diagonalization with explicit invariants** (`Smith.lean`,
  `exists_smith_diagonalization`): every 2×2 integer matrix `M` satisfies
  `U * M * V = diag(d₁, d₂)` with `U, V` unimodular. The proof avoids the
  classical iterative SNF algorithm entirely (content factoring, a CRT
  primitive-representation argument, and identification of the invariants
  by content-invariance + determinants instead of uniqueness theory).
- **Content lemmas** (`Content.lean`): `M ≡ 0 (mod m)` over `ZMod m` iff
  `m` divides the content of `M` (the primitive-isogeny characterization
  at the matrix layer); primitivity via reductions mod primes.
- **The matrix category 𝓜(α)** (`Cat.lean`): for a quadratic integer `α`
  of trace `t` and norm `d`, the category whose objects are 2×2 integer
  matrices with that trace and determinant and whose morphisms are
  intertwining integer matrices, as a literal `CategoryTheory.Category`;
  includes the companion-matrix object and 2×2 Cayley–Hamilton.
- **The bijection 𝒬(α) ↔ 𝓜(α)** (`QF.lean`, `qfEquiv`): binary quadratic
  forms of discriminant `t² - 4d` (defined by hand — Mathlib has no
  classical form theory) correspond exactly to objects of `𝓜(α)`, via
  `q(x,y) = -det[A·(x,y)ᵀ | (x,y)ᵀ]`; integrality of the inverse map is
  forced by the discriminant condition.
- **Equivariance** (`QF.lean`, `toBQF_smul_eval`): `GL₂(ℤ)` acts on `𝓜(α)`
  by conjugation (a `MulAction`), and the bijection intertwines this with
  the classical change-of-variables action on forms, twisted by `det P` —
  strictly for `P ∈ SL₂(ℤ)`. Hence conjugacy classes in `𝓜(α)` correspond
  to proper equivalence classes of forms.
- **The commutant index formula and 2-torsion criterion**
  (`Commutant.lean`): for non-scalar `A`, the quotient of the commutant
  `End(A) = {M : MA = AM}` by `ℤ[A] = ℤ·1 + ℤ·A` is *cyclic* of order
  `gcd(A₀₁, A₁₀, A₁₁ - A₀₀)` — the index is the content of the non-scalar
  part (`commutant_quotient_equiv`, `index_adjoinInt_commutant`).
  Consequently, for `det A` odd, `2 ∣ [End(A) : ℤ[A]]` iff `A ≡ 1 (mod 2)`
  (`two_dvd_index_iff`) — the matrix layer of "all of `E[2]` is rational
  iff the endomorphism-ring index `[𝒪_E : ℤ[π]]` is even".

The statements are additionally validated by compiled-in `#guard`
numerical sanity checks (brute-forced kernels over small `ℤ/nℤ`,
including torsion counts), which re-run on every build.

## Building

Requires [elan](https://github.com/leanprover/elan). Then:

```
lake exe cache get   # prebuilt Mathlib
lake build
```
