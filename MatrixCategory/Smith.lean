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

/-- Existence of some nonneg chained diagonalization, nondegenerate case.
Route: factor out the content, represent a primitive vector via CRT over the
primes dividing the determinant, then a single Bézout step. -/
theorem exists_chained_diagonalization_of_det_ne_zero
    (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det ≠ 0) :
    ∃ (U V : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (x y : ℤ),
      (U : Matrix (Fin 2) (Fin 2) ℤ) * M * (V : Matrix (Fin 2) (Fin 2) ℤ) =
        Matrix.diagonal ![x, y] ∧ 0 ≤ x ∧ 0 ≤ y ∧ x ∣ y := by
  sorry

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
