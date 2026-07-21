import Mathlib
import MatrixCategory.Content

/-!
# Smith diagonalization of 2×2 integer matrices with explicit invariants

The crux of the kernel structure theorem: every 2×2 integer matrix `M`
satisfies `U * M * V = diagonal ![d₁, d₂]` for unimodular `U, V`, where
`d₁ = content M` and `d₂ = |det M| / d₁` (`exists_smith_diagonalization`).

## Proof strategy (no iteration)

The classical SNF algorithm iterates a reduction step with a termination
measure. We avoid the loop entirely:

* **Existence** (`exists_chained_diagonalization`): produce *some*
  diagonalization `diag(x, y)` with `0 ≤ x`, `0 ≤ y`, `x ∣ y`.
  - `det M = 0`: one Bézout column-clear collapses the last row
    (`g₁ · d' = det = 0`), then one Bézout row-clear finishes. No iteration.
  - `det M ≠ 0`: factor `M = g • M'` with `content M' = 1`; find `t` such
    that `M' · (1, t)ᵀ` is primitive (CRT over primes dividing `det M'` —
    each such prime forbids at most one class of `t`, and primes not
    dividing `det M'` are never bad since `(1, t)` has first coordinate 1);
    one Bézout matrix and two triangular units then give `diag(1, δ)`,
    and scaling back gives `diag(g, gδ)` with the chain for free.
* **Identification** (`eq_smith_of_diagonalization`): *any* chained
  nonnegative diagonalization has `x = content M` (content is invariant
  under unimodular multiplication, and the content of `diag(x,y)` with
  `x ∣ y` is `x`) and `y = |det M| / x` (determinants). No uniqueness
  theory of invariant factors is needed.
-/

namespace MatrixCategory

open Matrix

/-- First Smith invariant of a 2×2 integer matrix: the gcd of the entries. -/
def smithOne (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  (content M).natAbs

/-- Second Smith invariant of a 2×2 integer matrix: `|det M| / smithOne M`.
For `det M ≠ 0` this is exact division (see `content_sq_dvd_det`); for
`det M = 0` it is `0`, which is the correct second invariant of a matrix of
rank ≤ 1. -/
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

theorem smithOne_dvd_natAbs_det (M : Matrix (Fin 2) (Fin 2) ℤ) :
    smithOne M ∣ (M.det).natAbs :=
  dvd_trans (dvd_pow_self _ two_ne_zero) (smithOne_sq_dvd M)

/-- The Smith invariants form a divisibility chain: `d₁ ∣ d₂`. -/
theorem smithOne_dvd_smithTwo (M : Matrix (Fin 2) (Fin 2) ℤ) :
    smithOne M ∣ smithTwo M := by
  rcases eq_or_ne M.det 0 with hdet | hdet
  · simp [smithTwo, hdet]
  · rw [smithTwo, Nat.dvd_div_iff_mul_dvd (smithOne_dvd_natAbs_det M), ← sq]
    exact smithOne_sq_dvd M

/-! ## Content: nonnegativity, vanishing, unimodular invariance -/

theorem content_nonneg {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℤ) :
    0 ≤ content M := by
  have h := Finset.normalize_gcd
    (s := (Finset.univ : Finset (Fin n × Fin k))) (f := fun p => M p.1 p.2)
  unfold content
  rw [← h, ← Int.abs_eq_normalize]
  exact abs_nonneg _

theorem content_eq_zero_iff {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℤ) :
    content M = 0 ↔ M = 0 := by
  constructor
  · intro h
    ext i j
    have := (dvd_content_iff M (content M)).mp dvd_rfl i j
    rw [h, zero_dvd_iff] at this
    simpa using this
  · intro h
    subst h
    have h0 : (0 : ℤ) ∣ content (0 : Matrix (Fin n) (Fin k) ℤ) :=
      (dvd_content_iff _ _).mpr fun i j => by simp
    simpa using h0

theorem content_dvd_mul_left {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) :
    content A ∣ content (B * A) := by
  rw [dvd_content_iff]
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ =>
    dvd_trans ((dvd_content_iff A _).mp dvd_rfl k j) (dvd_mul_left _ _)

theorem content_dvd_mul_right {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) :
    content A ∣ content (A * B) := by
  rw [dvd_content_iff]
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun k _ =>
    dvd_trans ((dvd_content_iff A _).mp dvd_rfl i k) (dvd_mul_right _ _)

/-- The content is invariant under multiplication by units on both sides. -/
theorem content_unit_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (U V : (Matrix (Fin n) (Fin n) ℤ)ˣ) :
    content ((U : Matrix (Fin n) (Fin n) ℤ) * A * (V : Matrix (Fin n) (Fin n) ℤ)) =
      content A := by
  apply Int.dvd_antisymm (content_nonneg _) (content_nonneg _)
  · -- content (U*A*V) ∣ content A: recover A by multiplying with the inverses
    have h1 := content_dvd_mul_left
      ((U : Matrix (Fin n) (Fin n) ℤ) * A * (V : Matrix (Fin n) (Fin n) ℤ))
      (↑U⁻¹ : Matrix (Fin n) (Fin n) ℤ)
    have h2 := content_dvd_mul_right
      ((↑U⁻¹ : Matrix (Fin n) (Fin n) ℤ) *
        ((U : Matrix (Fin n) (Fin n) ℤ) * A * (V : Matrix (Fin n) (Fin n) ℤ)))
      (↑V⁻¹ : Matrix (Fin n) (Fin n) ℤ)
    have hrw : (↑U⁻¹ : Matrix (Fin n) (Fin n) ℤ) *
        ((U : Matrix (Fin n) (Fin n) ℤ) * A * (V : Matrix (Fin n) (Fin n) ℤ)) *
        (↑V⁻¹ : Matrix (Fin n) (Fin n) ℤ) = A := by
      simp [mul_assoc]
    rw [hrw] at h2
    exact dvd_trans h1 h2
  · -- content A ∣ content (U*A*V)
    have h1 := content_dvd_mul_right A (V : Matrix (Fin n) (Fin n) ℤ)
    have h2 := content_dvd_mul_left (A * (V : Matrix (Fin n) (Fin n) ℤ))
      (U : Matrix (Fin n) (Fin n) ℤ)
    rw [← mul_assoc] at h2
    exact dvd_trans h1 h2

/-- The content scales: `content (c • M) = c * content M` for `c ≥ 0`. -/
theorem content_smul {n k : ℕ} (c : ℤ) (M : Matrix (Fin n) (Fin k) ℤ)
    (hc : 0 ≤ c) : content (c • M) = c * content M := by
  unfold content
  rw [show (fun p : Fin n × Fin k => (c • M) p.1 p.2) =
    fun p : Fin n × Fin k => c * M p.1 p.2 from rfl]
  rw [Finset.gcd_mul_left]
  congr 1
  rw [← Int.abs_eq_normalize, abs_of_nonneg hc]

/-- The content of `diag(x, y)` with `0 ≤ x` and `x ∣ y` is `x`. -/
theorem content_diagonal {x y : ℤ} (hx : 0 ≤ x) (hxy : x ∣ y) :
    content (Matrix.diagonal ![x, y]) = x := by
  apply Int.dvd_antisymm (content_nonneg _) hx
  · exact (dvd_content_iff _ _).mp dvd_rfl 0 0
  · rw [dvd_content_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hxy]

/-! ## Identification: any chained diagonalization has the Smith invariants -/

/-- **Identification.** If `U * M * V = diag(x, y)` with `U, V` unimodular,
`x, y ≥ 0` and `x ∣ y`, then `x` and `y` are the explicit Smith invariants.
This replaces the uniqueness theory of invariant factors. -/
theorem eq_smith_of_diagonalization {M : Matrix (Fin 2) (Fin 2) ℤ} {x y : ℤ}
    (U V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ)
    (h : (U : Matrix (Fin 2) (Fin 2) ℤ) * M * (V : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.diagonal ![x, y])
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ∣ y) :
    x = (smithOne M : ℤ) ∧ y = (smithTwo M : ℤ) := by
  -- `x = content M` via invariance
  have hcx : x = content M := by
    rw [← content_unit_mul M U V, h, content_diagonal hx hxy]
  have hx1 : x = (smithOne M : ℤ) := by
    rw [hcx, smithOne, Int.natAbs_of_nonneg (content_nonneg M)]
  refine ⟨hx1, ?_⟩
  -- `x * y = ± det M`, hence `x * y = |det M|` by nonnegativity
  have hdet : ((U : Matrix (Fin 2) (Fin 2) ℤ).det * M.det) *
      (V : Matrix (Fin 2) (Fin 2) ℤ).det = x * y := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, h, Matrix.det_diagonal,
      Fin.prod_univ_two]
    rfl
  have hUdet : ((U : Matrix (Fin 2) (Fin 2) ℤ).det).natAbs = 1 :=
    Int.isUnit_iff_natAbs_eq.mp ((Matrix.isUnit_iff_isUnit_det _).mp U.isUnit)
  have hVdet : ((V : Matrix (Fin 2) (Fin 2) ℤ).det).natAbs = 1 :=
    Int.isUnit_iff_natAbs_eq.mp ((Matrix.isUnit_iff_isUnit_det _).mp V.isUnit)
  have habs : (x * y).natAbs = (M.det).natAbs := by
    rw [← hdet, Int.natAbs_mul, Int.natAbs_mul, hUdet, hVdet, one_mul, mul_one]
  have hxy_eq : x * y = ((M.det).natAbs : ℤ) := by
    rw [← habs, Int.natAbs_of_nonneg (mul_nonneg hx hy)]
  rcases eq_or_ne x 0 with hx0 | hx0
  · -- degenerate: `x = 0` forces `M = 0`, both invariants vanish
    have hM0 : M = 0 := (content_eq_zero_iff M).mp (by rw [← hcx, hx0])
    have hy0 : y = 0 := by simpa [hx0] using hxy
    simp [hy0, smithTwo, smithOne, hM0]
  · -- `y = |det M| / x` matches `smithTwo`
    have hs1 : (smithOne M : ℤ) ≠ 0 := by rwa [← hx1]
    have hcast : ((smithTwo M : ℕ) : ℤ) = ((M.det).natAbs : ℤ) / (smithOne M : ℤ) := by
      rw [smithTwo]
      exact Int.natCast_div _ _
    rw [hcast, ← hxy_eq, hx1, Int.mul_ediv_cancel_left _ hs1]

/-! ## Existence of a chained diagonalization -/

/-- **Bézout column-clear.** For any column `(a, c)ᵀ` there is a unimodular
`U` with `U · (a, c)ᵀ = (gcd(a,c), 0)ᵀ`. -/
theorem exists_unit_mulVec_gcd (a c : ℤ) :
    ∃ U : (Matrix (Fin 2) (Fin 2) ℤ)ˣ,
      (U : Matrix (Fin 2) (Fin 2) ℤ).mulVec ![a, c] = ![(Int.gcd a c : ℤ), 0] := by
  rcases eq_or_ne (Int.gcd a c) 0 with hg | hg
  · obtain ⟨ha, hc⟩ := Int.gcd_eq_zero_iff.mp hg
    subst ha
    subst hc
    refine ⟨1, ?_⟩
    rw [Units.val_one, Matrix.one_mulVec]
    funext i
    fin_cases i <;> simp
  · have hg0 : ((Int.gcd a c : ℤ)) ≠ 0 := by exact_mod_cast hg
    obtain ⟨a', ha'⟩ : ((Int.gcd a c : ℤ)) ∣ a := Int.gcd_dvd_left a c
    obtain ⟨c', hc'⟩ : ((Int.gcd a c : ℤ)) ∣ c := Int.gcd_dvd_right a c
    have hbez : ((Int.gcd a c : ℤ)) = a * Int.gcdA a c + c * Int.gcdB a c :=
      Int.gcd_eq_gcd_ab a c
    have hbez' : a' * Int.gcdA a c + c' * Int.gcdB a c = 1 := by
      apply mul_left_cancel₀ hg0
      rw [mul_one]
      calc (Int.gcd a c : ℤ) * (a' * Int.gcdA a c + c' * Int.gcdB a c)
          = ((Int.gcd a c : ℤ) * a') * Int.gcdA a c
            + ((Int.gcd a c : ℤ) * c') * Int.gcdB a c := by ring
        _ = a * Int.gcdA a c + c * Int.gcdB a c := by rw [← ha', ← hc']
        _ = (Int.gcd a c : ℤ) := hbez.symm
    have hdet : (!![Int.gcdA a c, Int.gcdB a c; -c', a']).det = 1 := by
      rw [Matrix.det_fin_two_of]
      linear_combination hbez'
    have hunit : IsUnit !![Int.gcdA a c, Int.gcdB a c; -c', a'] :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hdet]; exact isUnit_one)
    refine ⟨hunit.unit, ?_⟩
    rw [hunit.unit_spec]
    funext i
    fin_cases i
    · show Matrix.mulVec _ _ 0 = (Int.gcd a c : ℤ)
      simp [Matrix.mulVec]
      linear_combination -hbez
    · show Matrix.mulVec _ _ 1 = 0
      simp [Matrix.mulVec]
      linear_combination (-c') * ha' + a' * hc'

/-- **Bézout row-clear**, transposed version: for any row `(a, b)` there is a
unimodular `V` with `(a, b) · V = (gcd(a,b), 0)`. -/
theorem exists_unit_vecMul_gcd (a b : ℤ) :
    ∃ V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ,
      Matrix.vecMul ![a, b] (V : Matrix (Fin 2) (Fin 2) ℤ) = ![(Int.gcd a b : ℤ), 0] := by
  obtain ⟨U, hU⟩ := exists_unit_mulVec_gcd a b
  have hunit : IsUnit ((U : Matrix (Fin 2) (Fin 2) ℤ)ᵀ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (by rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).mp U.isUnit)
  refine ⟨hunit.unit, ?_⟩
  rw [hunit.unit_spec, Matrix.vecMul_transpose, hU]

/-- Existence of some nonneg chained diagonalization when the first column is
nonzero and the determinant vanishes: one column-clear collapses the second
row (`g₁ · d' = det = 0`), then one row-clear finishes. -/
private theorem det_eq_zero_aux (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 0)
    (hcol : ¬(M 0 0 = 0 ∧ M 1 0 = 0)) :
    ∃ (U V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (x y : ℤ),
      (U : Matrix (Fin 2) (Fin 2) ℤ) * M * (V : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.diagonal ![x, y] ∧ 0 ≤ x ∧ 0 ≤ y ∧ x ∣ y := by
  obtain ⟨U, hU⟩ := exists_unit_mulVec_gcd (M 0 0) (M 1 0)
  set N : Matrix (Fin 2) (Fin 2) ℤ := (U : Matrix (Fin 2) (Fin 2) ℤ) * M with hN
  have hcolN : ∀ i, N i 0 = (U : Matrix (Fin 2) (Fin 2) ℤ).mulVec ![M 0 0, M 1 0] i := by
    intro i
    rw [hN, Matrix.mul_apply, Matrix.mulVec]
    congr 1
    funext k
    fin_cases k <;> rfl
  have hN00 : N 0 0 = (Int.gcd (M 0 0) (M 1 0) : ℤ) := by rw [hcolN 0, hU]; rfl
  have hN10 : N 1 0 = 0 := by rw [hcolN 1, hU]; rfl
  have hg1 : (Int.gcd (M 0 0) (M 1 0) : ℤ) ≠ 0 := by
    intro h
    exact hcol (Int.gcd_eq_zero_iff.mp (by exact_mod_cast h))
  have hdetN : N.det = 0 := by rw [hN, Matrix.det_mul, hdet, mul_zero]
  have hN11 : N 1 1 = 0 := by
    rw [Matrix.det_fin_two, hN10, hN00] at hdetN
    simp at hdetN
    rcases hdetN with h | h
    · exact absurd h hcol
    · exact h
  -- clear the top row with a Bézout row operation
  obtain ⟨V, hV⟩ := exists_unit_vecMul_gcd (N 0 0) (N 0 1)
  have hrow : ∀ i j, ((U : Matrix (Fin 2) (Fin 2) ℤ) * M *
      (V : Matrix (Fin 2) (Fin 2) ℤ)) i j =
      Matrix.vecMul ![N i 0, N i 1] (V : Matrix (Fin 2) (Fin 2) ℤ) j := by
    intro i j
    rw [← hN, Matrix.mul_apply, Matrix.vecMul, dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    fin_cases k <;> rfl
  refine ⟨U, V, (Int.gcd (N 0 0) (N 0 1) : ℤ), 0, ?_, Int.natCast_nonneg _, le_rfl,
    dvd_zero _⟩
  ext i j
  rw [hrow i j]
  fin_cases i <;> fin_cases j
  · simpa using congrFun hV 0
  · simpa using congrFun hV 1
  · simp [hN10, hN11, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  · simp [hN10, hN11, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Existence of some nonneg chained diagonalization, degenerate case. -/
theorem exists_chained_diagonalization_of_det_eq_zero
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 0) :
    ∃ (U V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (x y : ℤ),
      (U : Matrix (Fin 2) (Fin 2) ℤ) * M * (V : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.diagonal ![x, y] ∧ 0 ≤ x ∧ 0 ≤ y ∧ x ∣ y := by
  by_cases hM0 : M = 0
  · refine ⟨1, 1, 0, 0, ?_, le_rfl, le_rfl, dvd_zero _⟩
    subst hM0
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · by_cases hcol : M 0 0 = 0 ∧ M 1 0 = 0
    · -- first column zero: swap the columns first
      have hS : IsUnit !![(0 : ℤ), 1; 1, 0] :=
        (Matrix.isUnit_iff_isUnit_det _).mpr
          (by rw [Matrix.det_fin_two_of]; norm_num)
      set S := hS.unit with hSdef
      have hScoe : (S : Matrix (Fin 2) (Fin 2) ℤ) = !![(0 : ℤ), 1; 1, 0] := hS.unit_spec
      have hdet' : (M * (S : Matrix (Fin 2) (Fin 2) ℤ)).det = 0 := by
        rw [Matrix.det_mul, hdet, zero_mul]
      have hMS : ∀ i, (M * (S : Matrix (Fin 2) (Fin 2) ℤ)) i 0 = M i 1 := by
        intro i
        rw [hScoe, Matrix.mul_apply, Fin.sum_univ_two]
        simp
      have hcol' : ¬((M * (S : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = 0 ∧
          (M * (S : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 = 0) := by
        rintro ⟨h00, h10⟩
        rw [hMS 0] at h00
        rw [hMS 1] at h10
        apply hM0
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [hcol.1, hcol.2, h00, h10]
      obtain ⟨U, V, x, y, hUV, hx, hy, hxy⟩ :=
        det_eq_zero_aux (M * (S : Matrix (Fin 2) (Fin 2) ℤ)) hdet' hcol'
      refine ⟨U, S * V, x, y, ?_, hx, hy, hxy⟩
      rw [Units.val_mul, ← mul_assoc,
        mul_assoc (U : Matrix (Fin 2) (Fin 2) ℤ) M (S : Matrix (Fin 2) (Fin 2) ℤ)]
      exact hUV
    · exact det_eq_zero_aux M hdet hcol

/-- **The number-theoretic core.** A content-1 matrix with nonzero
determinant maps some vector `(1, t)ᵀ` to a *primitive* vector. Proof plan
(CRT over the primes dividing the determinant): a prime `q` for which every
`t` fails would divide all four entries (evaluate at `t = 0, 1`),
contradicting content 1; so each `q ∣ det` forbids at most one residue class
of `t`, and any prime `q ∤ det` never divides both coordinates since
`(1, t)` is nonzero mod `q` and `M` is invertible mod `q`. -/
theorem exists_good_t (M : Matrix (Fin 2) (Fin 2) ℤ) (hcont : content M = 1)
    (hdet : M.det ≠ 0) :
    ∃ t : ℤ, Int.gcd (M 0 0 + t * M 0 1) (M 1 0 + t * M 1 1) = 1 := by
  classical
  set D : ℕ := (M.det).natAbs with hD
  have hD0 : D ≠ 0 := by simpa [hD, Int.natAbs_eq_zero] using hdet
  set s : Finset ℕ := D.primeFactors with hs
  -- For every prime `q`, some residue `τ` avoids killing both coordinates:
  -- otherwise `τ = 0` and `τ = 1` force all four entries to vanish mod `q`,
  -- contradicting `content M = 1`.
  have hex : ∀ q : ℕ, q.Prime → ∃ τ : ZMod q,
      ¬((M 0 0 : ZMod q) + τ * (M 0 1 : ZMod q) = 0 ∧
        (M 1 0 : ZMod q) + τ * (M 1 1 : ZMod q) = 0) := by
    intro q hq
    haveI : Fact q.Prime := ⟨hq⟩
    by_contra hall
    push_neg at hall
    obtain ⟨h00, h10⟩ := hall 0
    obtain ⟨h01, h11⟩ := hall 1
    rw [zero_mul, add_zero] at h00 h10
    rw [one_mul] at h01 h11
    rw [h00, zero_add] at h01
    rw [h10, zero_add] at h11
    have hdvd : (q : ℤ) ∣ content M := by
      rw [dvd_content_iff]
      intro i j
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      fin_cases i <;> fin_cases j
      · exact h00
      · exact h01
      · exact h10
      · exact h11
    rw [hcont] at hdvd
    have hq1 : q ∣ 1 := by exact_mod_cast hdvd
    exact hq.one_lt.ne' (Nat.dvd_one.mp hq1)
  -- Choose a good residue for each prime factor of the determinant.
  have hex' : ∀ i : {x // x ∈ s}, ∃ τ : ZMod (i : ℕ),
      ¬((M 0 0 : ZMod (i : ℕ)) + τ * (M 0 1 : ZMod (i : ℕ)) = 0 ∧
        (M 1 0 : ZMod (i : ℕ)) + τ * (M 1 1 : ZMod (i : ℕ)) = 0) :=
    fun i => hex i (Nat.prime_of_mem_primeFactors i.2)
  choose τ hτ using hex'
  -- Chinese remainder: a single `t` matching every `τ` simultaneously.
  have hcop : Pairwise (Function.onFun Nat.Coprime fun i : {x // x ∈ s} => (i : ℕ)) := by
    intro i j hij
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors i.2)
      (Nat.prime_of_mem_primeFactors j.2)).mpr fun h => hij (Subtype.ext h)
  set P : ℕ := ∏ i : {x // x ∈ s}, (i : ℕ) with hP
  haveI : NeZero P := ⟨Finset.prod_ne_zero_iff.mpr
    fun i _ => (Nat.prime_of_mem_primeFactors i.2).ne_zero⟩
  set e := ZMod.prodEquivPi (fun i : {x // x ∈ s} => (i : ℕ)) hcop with he
  obtain ⟨t, ht⟩ : ∃ t : ℤ, (t : ZMod P) = e.symm τ :=
    ⟨((e.symm τ).val : ℤ), by push_cast; exact ZMod.natCast_rightInverse _⟩
  have hcomp : ∀ i : {x // x ∈ s}, ((t : ℤ) : ZMod (i : ℕ)) = τ i := by
    intro i
    have h1 : e (t : ZMod P) i = τ i := by rw [ht, RingEquiv.apply_symm_apply]
    rwa [he, ZMod.prodEquivPi_apply, map_intCast] at h1
  -- `t` works: any prime dividing the gcd yields a contradiction.
  refine ⟨t, ?_⟩
  by_contra hgcd
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
  haveI : Fact p.Prime := ⟨hp⟩
  have hw0 : (p : ℤ) ∣ M 0 0 + t * M 0 1 :=
    (Int.natCast_dvd_natCast.mpr hpdvd).trans (Int.gcd_dvd_left _ _)
  have hw1 : (p : ℤ) ∣ M 1 0 + t * M 1 1 :=
    (Int.natCast_dvd_natCast.mpr hpdvd).trans (Int.gcd_dvd_right _ _)
  have hz0 : (M 0 0 : ZMod p) + (t : ZMod p) * (M 0 1 : ZMod p) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hw0
    push_cast at h
    linear_combination h
  have hz1 : (M 1 0 : ZMod p) + (t : ZMod p) * (M 1 1 : ZMod p) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hw1
    push_cast at h
    linear_combination h
  by_cases hps : p ∈ s
  · -- `p ∣ det`: contradicts the choice of `τ` at `p`
    rw [hcomp ⟨p, hps⟩] at hz0 hz1
    exact hτ ⟨p, hps⟩ ⟨hz0, hz1⟩
  · -- `p ∤ det`: `M` is invertible mod `p`, but kills `(1, t) ≠ 0`
    have hpD : ¬p ∣ D := fun h => hps (Nat.mem_primeFactors.mpr ⟨hp, h, hD0⟩)
    have hdetp : ((M.det : ℤ) : ZMod p) ≠ 0 := by
      intro hcon
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.dvd_natAbs] at hcon
      exact hpD (Int.natCast_dvd_natCast.mp hcon)
    set Mb : Matrix (Fin 2) (Fin 2) (ZMod p) :=
      M.map (Int.cast : ℤ → ZMod p) with hMb
    have hdetb : Mb.det ≠ 0 := by
      intro hcon
      apply hdetp
      have hmap := RingHom.map_det (Int.castRingHom (ZMod p)) M
      rw [RingHom.mapMatrix_apply] at hmap
      rw [hMb, show M.map (Int.cast : ℤ → ZMod p) =
        M.map ⇑(Int.castRingHom (ZMod p)) from rfl, ← hmap] at hcon
      exact hcon
    have hMbunit : IsUnit Mb :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdetb)
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hMbunit
    have hker : Mb.mulVec ![1, (t : ZMod p)] = 0 := by
      funext i
      fin_cases i
      · simp [hMb, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]
        linear_combination hz0
      · simp [hMb, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]
        linear_combination hz1
    have hv0 : ![(1 : ZMod p), (t : ZMod p)] = 0 := by
      apply hinj
      rw [hker, Matrix.mulVec_zero]
    exact one_ne_zero (congrFun hv0 0)

/-- Diagonalization of a content-1 matrix with nonzero determinant: the good
`t` plus one Bézout step give `diag(1, δ)` — the corner 1 makes the
row-clearing unconditional, so no iteration is needed. -/
private theorem det_ne_zero_content_one (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hcont : content M = 1) (hdet : M.det ≠ 0) :
    ∃ (U V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (δ : ℤ),
      (U : Matrix (Fin 2) (Fin 2) ℤ) * M * (V : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.diagonal ![1, δ] := by
  obtain ⟨t, ht⟩ := exists_good_t M hcont hdet
  obtain ⟨A, hA⟩ := exists_unit_mulVec_gcd (M 0 0 + t * M 0 1) (M 1 0 + t * M 1 1)
  rw [ht] at hA
  push_cast at hA
  have hBunit : IsUnit !![(1 : ℤ), 0; t, 1] :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [Matrix.det_fin_two_of]; simp)
  set N : Matrix (Fin 2) (Fin 2) ℤ :=
    (A : Matrix (Fin 2) (Fin 2) ℤ) * M * !![(1 : ℤ), 0; t, 1] with hN
  have hw : M.mulVec ![1, t] = ![M 0 0 + t * M 0 1, M 1 0 + t * M 1 1] := by
    funext i
    fin_cases i <;>
      (simp [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]; ring)
  have hNcol : ∀ i, N i 0 =
      ((A : Matrix (Fin 2) (Fin 2) ℤ) * M).mulVec ![(1 : ℤ), t] i := by
    intro i
    rw [hN, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _
    fin_cases k <;> simp
  have hN00 : N 0 0 = 1 := by
    rw [hNcol 0, ← Matrix.mulVec_mulVec, hw, hA]
    rfl
  have hN10 : N 1 0 = 0 := by
    rw [hNcol 1, ← Matrix.mulVec_mulVec, hw, hA]
    rfl
  have hCunit : IsUnit !![(1 : ℤ), -(N 0 1); 0, 1] :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [Matrix.det_fin_two_of]; simp)
  refine ⟨A, hBunit.unit * hCunit.unit, N 1 1, ?_⟩
  rw [Units.val_mul, hBunit.unit_spec, hCunit.unit_spec, ← mul_assoc, ← hN]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hN00, hN10]

/-- Existence of some nonneg chained diagonalization, nondegenerate case:
factor out the content, diagonalize the content-1 part to `diag(1, δ)`,
scale back (the chain `g ∣ gδ` is automatic), and fix the sign. -/
theorem exists_chained_diagonalization_of_det_ne_zero
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det ≠ 0) :
    ∃ (U V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (x y : ℤ),
      (U : Matrix (Fin 2) (Fin 2) ℤ) * M * (V : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.diagonal ![x, y] ∧ 0 ≤ x ∧ 0 ≤ y ∧ x ∣ y := by
  have hM0 : M ≠ 0 := by
    intro h
    exact hdet (by rw [h]; simp)
  have hg0 : content M ≠ 0 := fun h => hM0 ((content_eq_zero_iff M).mp h)
  have hgpos : 0 < content M := lt_of_le_of_ne (content_nonneg M) (Ne.symm hg0)
  set M₁ : Matrix (Fin 2) (Fin 2) ℤ :=
    Matrix.of fun i j => M i j / content M with hM₁
  have hsmul : M = content M • M₁ := by
    ext i j
    rw [hM₁]
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' ((dvd_content_iff M (content M)).mp dvd_rfl i j)).symm
  have hcont₁ : content M₁ = 1 := by
    apply mul_left_cancel₀ hg0
    rw [mul_one, ← content_smul (content M) M₁ (content_nonneg M), ← hsmul]
  have hdet₁ : M₁.det ≠ 0 := by
    intro h
    apply hdet
    rw [hsmul, Matrix.det_smul, h, mul_zero]
  obtain ⟨U, V, δ, hUV⟩ := det_ne_zero_content_one M₁ hcont₁ hdet₁
  have hdiag : (U : Matrix (Fin 2) (Fin 2) ℤ) * M * (V : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.diagonal ![content M, content M * δ] := by
    conv_lhs => rw [hsmul, Matrix.mul_smul, Matrix.smul_mul, hUV]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rcases le_or_gt 0 δ with hδ | hδ
  · exact ⟨U, V, content M, content M * δ, hdiag, hgpos.le,
      mul_nonneg hgpos.le hδ, dvd_mul_right _ _⟩
  · have hDunit : IsUnit !![(1 : ℤ), 0; 0, -1] :=
      (Matrix.isUnit_iff_isUnit_det _).mpr
        (by rw [Matrix.det_fin_two_of]; norm_num)
    refine ⟨U, V * hDunit.unit, content M, -(content M * δ), ?_, hgpos.le,
      neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hgpos.le hδ.le),
      dvd_neg.mpr (dvd_mul_right _ _)⟩
    rw [Units.val_mul, hDunit.unit_spec, ← mul_assoc, hdiag]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

theorem exists_chained_diagonalization (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ (U V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (x y : ℤ),
      (U : Matrix (Fin 2) (Fin 2) ℤ) * M * (V : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.diagonal ![x, y] ∧ 0 ≤ x ∧ 0 ≤ y ∧ x ∣ y := by
  rcases eq_or_ne M.det 0 with hdet | hdet
  · exact exists_chained_diagonalization_of_det_eq_zero M hdet
  · exact exists_chained_diagonalization_of_det_ne_zero M hdet

/-! ## The main theorem -/

/-- **L1: Smith diagonalization with explicit invariants.** Every 2×2 integer
matrix is diagonalizable by unimodular matrices with `d₁ = content M` and
`d₂ = |det M| / d₁` on the diagonal. -/
theorem exists_smith_diagonalization (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ U V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ,
      (U : Matrix (Fin 2) (Fin 2) ℤ) * M * (V : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.diagonal ![(smithOne M : ℤ), (smithTwo M : ℤ)] := by
  obtain ⟨U, V, x, y, h, hx, hy, hxy⟩ := exists_chained_diagonalization M
  obtain ⟨h1, h2⟩ := eq_smith_of_diagonalization U V h hx hy hxy
  exact ⟨U, V, by rw [h, h1, h2]⟩

end MatrixCategory
