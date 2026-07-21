import Mathlib
import MatrixCategory.Content

/-!
# Structure of the kernel of `M mod n` (statement)

Paper reference: the kernel-group lemma — for a 2×2 integer matrix `M`, the
kernel of `M` acting on `(ℤ/nℤ)²` is `ℤ/cm × ℤ/m`.

## Phase-1 decisions (statement design)

* **The kernel** is `LinearMap.ker` of the `ZMod n`-linear map induced by the
  reduction `M.map (Int.cast : ℤ → ZMod n)`, acting on `Fin 2 → ZMod n` via
  `Matrix.mulVecLin`. We view it as an additive group.
* **The isomorphism** is an additive-group isomorphism `≃+`, wrapped in
  `Nonempty` since it is an existence statement (the iso is not canonical —
  it depends on a choice of Smith basis).
* **The invariants are explicit.** For 2×2 matrices the Smith normal form
  invariants are `d₁ = gcd of entries = content M` and `d₂ = |det M| / d₁`.
  The kernel is `ZMod (gcd d₂ n) × ZMod (gcd d₁ n)`; in the paper's `ℤ/cm × ℤ/m`
  packaging, `m = gcd d₁ n` and `cm = gcd d₂ n` (big factor first).
* **Hypotheses.** `M.det ≠ 0` (in the isogeny context `det = degree > 0`;
  moreover for `det = 0` the second invariant degenerates) and `NeZero n`
  (for `n = 0` the statement is *false*: over `ZMod 0 = ℤ` an injective `M`
  has trivial kernel while the right-hand side is finite nontrivial).

The `#guard`s at the bottom are compiled-in numerical sanity checks of the
statement: they brute-force the kernel over small `ZMod n` and compare both
the cardinality and the `m`-torsion count against the predicted group. They
re-run on every build.
-/

namespace MatrixCategory

open Matrix

/-- First Smith invariant of a 2×2 integer matrix: the gcd of the entries. -/
def smithOne (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  (content M).natAbs

/-- Second Smith invariant of a 2×2 integer matrix: `|det M| / smithOne M`.
This is exact division — see `content_sq_dvd_det`. -/
def smithTwo (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  (M.det).natAbs / smithOne M

/-- The square of the content divides the determinant (2×2 case): the content
divides every entry, and `det` is a sum of products of two entries. This is
what makes `smithTwo` an exact division. -/
theorem content_sq_dvd_det (M : Matrix (Fin 2) (Fin 2) ℤ) :
    content M ^ 2 ∣ M.det := by
  have h := (dvd_content_iff M (content M)).mp dvd_rfl
  rw [Matrix.det_fin_two, sq]
  exact dvd_sub (mul_dvd_mul (h 0 0) (h 1 1)) (mul_dvd_mul (h 0 1) (h 1 0))

theorem smithOne_sq_dvd (M : Matrix (Fin 2) (Fin 2) ℤ) :
    smithOne M ^ 2 ∣ (M.det).natAbs := by
  have := content_sq_dvd_det M
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_pow] at this
  exact this

/-- The Smith invariants form a divisibility chain: `d₁ ∣ d₂`. -/
theorem smithOne_dvd_smithTwo (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0) :
    smithOne M ∣ smithTwo M := by
  have hsq := smithOne_sq_dvd M
  have h1 : smithOne M ∣ (M.det).natAbs := dvd_trans (dvd_pow_self _ two_ne_zero) hsq
  have h0 : smithOne M ≠ 0 := by
    intro h
    apply hM
    have hc : content M = 0 := by
      simpa [smithOne, Int.natAbs_eq_zero] using h
    have hz : ∀ i j, M i j = 0 := by
      intro i j
      have hd := (dvd_content_iff M (content M)).mp dvd_rfl i j
      rwa [hc, zero_dvd_iff] at hd
    rw [Matrix.det_fin_two, hz 0 0, hz 0 1]
    ring
  rw [smithTwo, Nat.dvd_div_iff_mul_dvd h1, ← sq]
  exact hsq

/-- **Kernel structure theorem** (statement; proof is the phase 2–4 work).

For `M` a 2×2 integer matrix with `det M ≠ 0` and `n ≠ 0`, the kernel of
`M mod n` acting on `(ℤ/nℤ)²` is isomorphic as an additive group to
`ℤ/(cm) × ℤ/m` where `m = gcd(d₁, n)`, `cm = gcd(d₂, n)`, and `d₁ ∣ d₂` are
the Smith invariants of `M`. -/
theorem ker_structure (M : Matrix (Fin 2) (Fin 2) ℤ) (hM : M.det ≠ 0)
    (n : ℕ) [NeZero n] :
    Nonempty
      (LinearMap.ker ((M.map (Int.cast : ℤ → ZMod n)).mulVecLin) ≃+
        ZMod (Nat.gcd (smithTwo M) n) × ZMod (Nat.gcd (smithOne M) n)) := by
  sorry

/-! ## Numerical sanity checks of the statement

`kerCard M n` brute-forces `#ker(M mod n)`; the predicted value is
`gcd(d₂,n) * gcd(d₁,n)`. Cardinality alone cannot distinguish e.g.
`ℤ/4` from `ℤ/2 × ℤ/2`, so `kerTorsionCard M n m` additionally counts the
`m`-torsion: in `ℤ/a × ℤ/b` with `b ∣ a`, the number of elements killed by
`b` is `b²` (not `b`), which pins down the two-generator structure. -/

/-- Brute-force cardinality of `ker(M mod n)`. -/
def kerCard (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) [NeZero n] : ℕ :=
  (Finset.univ.filter fun v : Fin 2 → ZMod n =>
    (M.map (Int.cast : ℤ → ZMod n)).mulVec v = 0).card

/-- Brute-force count of the `m`-torsion elements of `ker(M mod n)`. -/
def kerTorsionCard (M : Matrix (Fin 2) (Fin 2) ℤ) (n m : ℕ) [NeZero n] : ℕ :=
  (Finset.univ.filter fun v : Fin 2 → ZMod n =>
    (M.map (Int.cast : ℤ → ZMod n)).mulVec v = 0 ∧ m • v = 0).card

/-- Predicted cardinality from the statement of `ker_structure`. -/
def predictedCard (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) : ℕ :=
  Nat.gcd (smithTwo M) n * Nat.gcd (smithOne M) n

-- Identity: trivial kernel for every n.
#guard kerCard !![1, 0; 0, 1] 12 == predictedCard !![1, 0; 0, 1] 12
-- det 7, content 1: kernel is ℤ/7 mod 7 and mod 14.
#guard kerCard !![2, 1; 3, 5] 7 == predictedCard !![2, 1; 3, 5] 7
#guard kerCard !![2, 1; 3, 5] 14 == predictedCard !![2, 1; 3, 5] 14
-- diag(2,4) mod 8: kernel ℤ/4 × ℤ/2, order 8.
#guard kerCard !![2, 0; 0, 4] 8 == predictedCard !![2, 0; 0, 4] 8
-- 2·I mod 8: kernel ℤ/2 × ℤ/2 (NOT ℤ/4): order 4, and all 4 elements 2-torsion.
#guard kerCard !![2, 0; 0, 2] 8 == predictedCard !![2, 0; 0, 2] 8
#guard kerTorsionCard !![2, 0; 0, 2] 8 2 == 4
-- diag(2,4) mod 8 again: 2-torsion of ℤ/4 × ℤ/2 has order 2·2 = 4.
#guard kerTorsionCard !![2, 0; 0, 4] 8 2 == 4
-- content 2, det 60, invariants (2,30), mod 15: gcd(2,15)=1, gcd(30,15)=15.
#guard kerCard !![6, 0; 0, 10] 15 == predictedCard !![6, 0; 0, 10] 15
-- a non-diagonal composite example: content 2, det 20, invariants (2,10), mod 12.
#guard kerCard !![4, 6; 2, 8] 12 == predictedCard !![4, 6; 2, 8] 12
#guard kerTorsionCard !![4, 6; 2, 8] 12 (Nat.gcd (smithOne !![4, 6; 2, 8]) 12) ==
  Nat.gcd (smithOne !![4, 6; 2, 8]) 12 ^ 2

end MatrixCategory
