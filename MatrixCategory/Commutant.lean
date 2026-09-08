import Mathlib
import MatrixCategory.Cat

/-!
# The commutant, the index formula, and the 2-torsion criterion

Paper reference: `lem:2tor` — for `E/𝔽_p` (`p` an odd prime) with Frobenius
trace `a`, endomorphism ring `𝒪_E` and `𝒪 = ℤ[x]/(x² - ax + p)`:
`E[2] ⊆ E(𝔽_p)` iff `[𝒪_E : 𝒪]` is even.

## Matrix-layer avatars

* `𝒪_E` becomes the **commutant** `End(A) = {M : MA = AM}` of the Frobenius
  matrix `A` (this is `Hom A A` of `Cat.lean` in additive-subgroup clothing);
* `𝒪 = ℤ[π]` becomes `ℤ[A] = ℤ·1 + ℤ·A` (`adjoinInt`);
* `E[2] ⊆ E(𝔽_p)` becomes `A ≡ 1 (mod 2)` (the bridge stays on paper).

## The redesign (house rule)

Rather than order/conductor theory, we prove the **closed form of the
index**: writing `A = [[α, β], [γ, δ]]`, the commutant relations say that
`(M₀₁, M₁₀, M₁₁ - M₀₀)` is proportional to `(β, γ, δ - α)`, whence for
non-scalar `A`

  `End(A) / ℤ[A] ≃+ ZMod (gcd β γ (δ-α))`    (`commutant_quotient_equiv`)

— the index is the content of the non-scalar part of `A`
(`index_adjoinInt_commutant`). `lem:2tor` is then parity bookkeeping
(`two_dvd_index_iff`, `MObj.two_dvd_index_iff`): only `det A` odd is
needed, and primality of `p` merely supplies non-scalarity.

The quotient map is the coefficient extraction
`M ↦ c₁M₀₁ + c₂M₁₀ + c₃(M₁₁ - M₀₀)` with `cᵢ` three-term Bézout
coefficients of the gcd — linear in `M`, hence an additive hom with no
case splits.
-/

namespace MatrixCategory

open Matrix

/-! ## Scalar matrices, entrywise -/

private theorem intCast_matrix_apply (x : ℤ) (i j : Fin 2) :
    ((x : ℤ) : Matrix (Fin 2) (Fin 2) ℤ) i j = if i = j then x else 0 := by
  rw [← zsmul_one x, Matrix.smul_apply, Matrix.one_apply]
  split <;> simp

private theorem intCast_mul_apply (y : ℤ) (A : Matrix (Fin 2) (Fin 2) ℤ)
    (i j : Fin 2) :
    (((y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * A) i j = y * A i j := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, intCast_matrix_apply, intCast_matrix_apply]
  fin_cases i <;> simp

/-! ## The two subgroups -/

/-- The commutant of `A`: matrices commuting with `A`, as an additive
subgroup of `M₂(ℤ)`. The avatar of `𝒪_E = End(E)`. -/
def commutant (A : Matrix (Fin 2) (Fin 2) ℤ) :
    AddSubgroup (Matrix (Fin 2) (Fin 2) ℤ) where
  carrier := {M | M * A = A * M}
  zero_mem' := by simp
  add_mem' := fun {M N} hM hN => by
    simp only [Set.mem_setOf_eq] at *
    rw [add_mul, mul_add, hM, hN]
  neg_mem' := fun {M} hM => by
    simp only [Set.mem_setOf_eq] at *
    rw [neg_mul, mul_neg, hM]

theorem mem_commutant {A M : Matrix (Fin 2) (Fin 2) ℤ} :
    M ∈ commutant A ↔ M * A = A * M := Iff.rfl

/-- `ℤ[A] = ℤ·1 + ℤ·A`, the avatar of `𝒪 = ℤ[π]`. Scalars are written as
integer-cast (scalar) matrices. -/
def adjoinInt (A : Matrix (Fin 2) (Fin 2) ℤ) :
    AddSubgroup (Matrix (Fin 2) (Fin 2) ℤ) where
  carrier := {M | ∃ x y : ℤ,
    M = (x : Matrix (Fin 2) (Fin 2) ℤ) + (y : Matrix (Fin 2) (Fin 2) ℤ) * A}
  zero_mem' := ⟨0, 0, by push_cast; simp⟩
  add_mem' := fun {M N} ⟨x₁, y₁, h₁⟩ ⟨x₂, y₂, h₂⟩ =>
    ⟨x₁ + x₂, y₁ + y₂, by rw [h₁, h₂]; push_cast; noncomm_ring⟩
  neg_mem' := fun {M} ⟨x, y, h⟩ => ⟨-x, -y, by rw [h]; push_cast; noncomm_ring⟩

theorem mem_adjoinInt {A M : Matrix (Fin 2) (Fin 2) ℤ} :
    M ∈ adjoinInt A ↔ ∃ x y : ℤ,
      M = (x : Matrix (Fin 2) (Fin 2) ℤ) + (y : Matrix (Fin 2) (Fin 2) ℤ) * A :=
  Iff.rfl

/-- `ℤ[A] ⊆ End(A)`. -/
theorem adjoinInt_le_commutant (A : Matrix (Fin 2) (Fin 2) ℤ) :
    adjoinInt A ≤ commutant A := by
  rintro M ⟨x, y, rfl⟩
  rw [mem_commutant, add_mul, mul_add, (Int.cast_commute x A).eq, ← mul_assoc,
    ← (Int.cast_commute y A).eq]

/-! ## The scalar gap -/

/-- The content of the non-scalar part of `A`:
`gcd(A₀₁, A₁₀, A₁₁ - A₀₀)`. This is the index `[End(A) : ℤ[A]]`. -/
def scalarGap (A : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  Int.gcd (A 0 1) ((Int.gcd (A 1 0) (A 1 1 - A 0 0) : ℕ) : ℤ)

theorem scalarGap_dvd₁ (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ((scalarGap A : ℕ) : ℤ) ∣ A 0 1 := Int.gcd_dvd_left _ _

theorem scalarGap_dvd₂ (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ((scalarGap A : ℕ) : ℤ) ∣ A 1 0 :=
  dvd_trans (Int.gcd_dvd_right _ _) (by exact_mod_cast Int.gcd_dvd_left _ _)

theorem scalarGap_dvd₃ (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ((scalarGap A : ℕ) : ℤ) ∣ A 1 1 - A 0 0 :=
  dvd_trans (Int.gcd_dvd_right _ _) (by exact_mod_cast Int.gcd_dvd_right _ _)

/-- Three-term Bézout for the scalar gap. -/
theorem exists_bezout (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ c₁ c₂ c₃ : ℤ,
      c₁ * A 0 1 + c₂ * A 1 0 + c₃ * (A 1 1 - A 0 0) = ((scalarGap A : ℕ) : ℤ) := by
  have h₁ : ((Int.gcd (A 1 0) (A 1 1 - A 0 0) : ℕ) : ℤ) =
      A 1 0 * Int.gcdA (A 1 0) (A 1 1 - A 0 0) +
      (A 1 1 - A 0 0) * Int.gcdB (A 1 0) (A 1 1 - A 0 0) :=
    Int.gcd_eq_gcd_ab _ _
  have h₂ : ((scalarGap A : ℕ) : ℤ) =
      A 0 1 * Int.gcdA (A 0 1) ((Int.gcd (A 1 0) (A 1 1 - A 0 0) : ℕ) : ℤ) +
      ((Int.gcd (A 1 0) (A 1 1 - A 0 0) : ℕ) : ℤ) *
        Int.gcdB (A 0 1) ((Int.gcd (A 1 0) (A 1 1 - A 0 0) : ℕ) : ℤ) :=
    Int.gcd_eq_gcd_ab _ _
  exact ⟨Int.gcdA (A 0 1) ((Int.gcd (A 1 0) (A 1 1 - A 0 0) : ℕ) : ℤ),
    Int.gcdA (A 1 0) (A 1 1 - A 0 0) *
      Int.gcdB (A 0 1) ((Int.gcd (A 1 0) (A 1 1 - A 0 0) : ℕ) : ℤ),
    Int.gcdB (A 1 0) (A 1 1 - A 0 0) *
      Int.gcdB (A 0 1) ((Int.gcd (A 1 0) (A 1 1 - A 0 0) : ℕ) : ℤ),
    by rw [h₂, h₁]; ring⟩

/-- A matrix with vanishing scalar gap is scalar. -/
theorem scalarGap_ne_zero {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : ∀ c : ℤ, A ≠ (c : Matrix (Fin 2) (Fin 2) ℤ)) : scalarGap A ≠ 0 := by
  intro h
  apply hA (A 0 0)
  have h₁ : A 0 1 = 0 := (Int.gcd_eq_zero_iff.mp h).1
  have h₂' : Int.gcd (A 1 0) (A 1 1 - A 0 0) = 0 := by
    have := (Int.gcd_eq_zero_iff.mp h).2
    exact_mod_cast this
  have h₃ : A 1 0 = 0 := (Int.gcd_eq_zero_iff.mp h₂').1
  have h₄ : A 1 1 - A 0 0 = 0 := (Int.gcd_eq_zero_iff.mp h₂').2
  ext i j
  rw [intCast_matrix_apply]
  fin_cases i <;> fin_cases j
  · simp
  · simpa using h₁
  · simpa using h₃
  · simpa using (by omega : A 1 1 = A 0 0)

/-! ## The commutant relations and saturation -/

/-- The commutant relations, entrywise: `M` commutes with `A` iff the three
2×2 "cross products" of `(M₀₁, M₁₀, M₁₁-M₀₀)` against `(A₀₁, A₁₀, A₁₁-A₀₀)`
vanish, i.e. the two triples are proportional. -/
theorem mem_commutant_iff {A M : Matrix (Fin 2) (Fin 2) ℤ} :
    M ∈ commutant A ↔
      M 0 1 * A 1 0 = A 0 1 * M 1 0 ∧
      M 0 1 * (A 1 1 - A 0 0) = A 0 1 * (M 1 1 - M 0 0) ∧
      M 1 0 * (A 1 1 - A 0 0) = A 1 0 * (M 1 1 - M 0 0) := by
  rw [mem_commutant]
  constructor
  · intro h
    have h' : ∀ i j, (M * A) i j = (A * M) i j := fun i j => by rw [h]
    have h00 := h' 0 0
    have h01 := h' 0 1
    have h10 := h' 1 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
    exact ⟨by linear_combination h00, by linear_combination h01,
      by linear_combination -h10⟩
  · rintro ⟨e1, e2, e3⟩
    ext i j
    fin_cases i <;> fin_cases j
    · show (M * A) 0 0 = (A * M) 0 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination e1
    · show (M * A) 0 1 = (A * M) 0 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination e2
    · show (M * A) 1 0 = (A * M) 1 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -e3
    · show (M * A) 1 1 = (A * M) 1 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination -e1

/-- Saturation: for `M` in the commutant with extracted coefficient
`λ = c₁M₀₁ + c₂M₁₀ + c₃(M₁₁-M₀₀)`, we have `g·(triple of M) = λ·(triple of
A)`. -/
theorem gcd_mul_entries {A M : Matrix (Fin 2) (Fin 2) ℤ} (hM : M ∈ commutant A)
    {c₁ c₂ c₃ : ℤ}
    (hbez : c₁ * A 0 1 + c₂ * A 1 0 + c₃ * (A 1 1 - A 0 0) =
      ((scalarGap A : ℕ) : ℤ)) :
    ((scalarGap A : ℕ) : ℤ) * M 0 1 =
        (c₁ * M 0 1 + c₂ * M 1 0 + c₃ * (M 1 1 - M 0 0)) * A 0 1 ∧
      ((scalarGap A : ℕ) : ℤ) * M 1 0 =
        (c₁ * M 0 1 + c₂ * M 1 0 + c₃ * (M 1 1 - M 0 0)) * A 1 0 ∧
      ((scalarGap A : ℕ) : ℤ) * (M 1 1 - M 0 0) =
        (c₁ * M 0 1 + c₂ * M 1 0 + c₃ * (M 1 1 - M 0 0)) * (A 1 1 - A 0 0) := by
  obtain ⟨e1, e2, e3⟩ := mem_commutant_iff.mp hM
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(M 0 1)) * hbez + c₂ * e1 + c₃ * e2
  · linear_combination (-(M 1 0)) * hbez - c₁ * e1 + c₃ * e3
  · linear_combination (-(M 1 1 - M 0 0)) * hbez - c₁ * e2 - c₂ * e3

/-! ## The main structure theorem -/

/-- **The quotient `End(A) / ℤ[A]` is cyclic of order the scalar gap**, for
non-scalar `A`. The isomorphism is induced by Bézout coefficient
extraction. -/
theorem commutant_quotient_equiv (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ∀ c : ℤ, A ≠ (c : Matrix (Fin 2) (Fin 2) ℤ)) :
    Nonempty
      ((↥(commutant A) ⧸ (adjoinInt A).addSubgroupOf (commutant A)) ≃+
        ZMod (scalarGap A)) := by
  have hg0 : scalarGap A ≠ 0 := scalarGap_ne_zero hA
  haveI : NeZero (scalarGap A) := ⟨hg0⟩
  have hgz : ((scalarGap A : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg0
  obtain ⟨c₁, c₂, c₃, hbez⟩ := exists_bezout A
  -- the coefficient-extraction additive hom
  set φ : ↥(commutant A) →+ ZMod (scalarGap A) :=
    { toFun := fun M => ((c₁ * (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
        c₂ * (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 +
        c₃ * ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
          (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0) : ℤ) : ZMod (scalarGap A))
      map_zero' := by simp
      map_add' := fun M N => by
        push_cast [Matrix.add_apply]
        ring } with hφ
  -- the generator: B₀ = (non-scalar part of A) / g
  obtain ⟨b₁, hb₁⟩ := scalarGap_dvd₁ A
  obtain ⟨b₂, hb₂⟩ := scalarGap_dvd₂ A
  obtain ⟨b₃, hb₃⟩ := scalarGap_dvd₃ A
  have hB₀mem : !![0, b₁; b₂, b₃] ∈ commutant A := by
    rw [mem_commutant_iff]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply]
    · apply mul_left_cancel₀ hgz
      linear_combination (-(A 1 0)) * hb₁ + (A 0 1) * hb₂
    · apply mul_left_cancel₀ hgz
      linear_combination (-(A 1 1 - A 0 0)) * hb₁ + (A 0 1) * hb₃
    · apply mul_left_cancel₀ hgz
      linear_combination (-(A 1 1 - A 0 0)) * hb₂ + (A 1 0) * hb₃
  -- Bézout on the divided triple: c₁b₁ + c₂b₂ + c₃b₃ = 1
  have hbez' : c₁ * b₁ + c₂ * b₂ + c₃ * b₃ = 1 := by
    apply mul_left_cancel₀ hgz
    rw [mul_one]
    linear_combination hbez - c₁ * hb₁ - c₂ * hb₂ - c₃ * hb₃
  have hφB₀ : φ ⟨!![0, b₁; b₂, b₃], hB₀mem⟩ = 1 := by
    rw [hφ]
    show ((c₁ * (!![0, b₁; b₂, b₃] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
      c₂ * (!![0, b₁; b₂, b₃] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 +
      c₃ * ((!![0, b₁; b₂, b₃] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (!![0, b₁; b₂, b₃] : Matrix (Fin 2) (Fin 2) ℤ) 0 0) : ℤ) :
      ZMod (scalarGap A)) = 1
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.of_apply]
    rw [show c₁ * b₁ + c₂ * b₂ + c₃ * (b₃ - 0) = 1 by linear_combination hbez']
    exact Int.cast_one
  -- surjectivity via the generator
  have hsurj : Function.Surjective φ := by
    intro ζ
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective ζ
    refine ⟨n • ⟨!![0, b₁; b₂, b₃], hB₀mem⟩, ?_⟩
    rw [map_zsmul, hφB₀, zsmul_one]
  -- the kernel is exactly ℤ[A]
  have hker : φ.ker = (adjoinInt A).addSubgroupOf (commutant A) := by
    ext M
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h0
      have hdvd : ((scalarGap A : ℕ) : ℤ) ∣
          (c₁ * (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
           c₂ * (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 +
           c₃ * ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
             (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0)) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact h0
      obtain ⟨y, hy⟩ := hdvd
      obtain ⟨hp₁, hp₂, hp₃⟩ := gcd_mul_entries M.2 hbez
      rw [hy] at hp₁ hp₂ hp₃
      have hM01 : (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = y * A 0 1 :=
        mul_left_cancel₀ hgz (by linear_combination hp₁)
      have hM10 : (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = y * A 1 0 :=
        mul_left_cancel₀ hgz (by linear_combination hp₂)
      have hMd : (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
          (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = y * (A 1 1 - A 0 0) :=
        mul_left_cancel₀ hgz (by linear_combination hp₃)
      refine ⟨(M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - y * A 0 0, y, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · show (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
          ((((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - y * A 0 0 : ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ) +
            ((y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * A) 0 0
        rw [Matrix.add_apply, intCast_matrix_apply, intCast_mul_apply]
        simp
      · show (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 =
          ((((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - y * A 0 0 : ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ) +
            ((y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * A) 0 1
        rw [Matrix.add_apply, intCast_matrix_apply, intCast_mul_apply]
        simpa using hM01
      · show (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
          ((((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - y * A 0 0 : ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ) +
            ((y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 0
        rw [Matrix.add_apply, intCast_matrix_apply, intCast_mul_apply]
        simpa using hM10
      · show (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
          ((((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 - y * A 0 0 : ℤ) :
              Matrix (Fin 2) (Fin 2) ℤ) +
            ((y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * A) 1 1
        rw [Matrix.add_apply, intCast_matrix_apply, intCast_mul_apply]
        simp
        linear_combination hMd
    · rintro ⟨x, y, hxy⟩
      have h01 : (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = y * A 0 1 := by
        rw [hxy, Matrix.add_apply, intCast_matrix_apply, intCast_mul_apply]
        simp
      have h10 : (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = y * A 1 0 := by
        rw [hxy, Matrix.add_apply, intCast_matrix_apply, intCast_mul_apply]
        simp
      have h00 : (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = x + y * A 0 0 := by
        rw [hxy, Matrix.add_apply, intCast_matrix_apply, intCast_mul_apply]
        simp
      have h11 : (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = x + y * A 1 1 := by
        rw [hxy, Matrix.add_apply, intCast_matrix_apply, intCast_mul_apply]
        simp
      rw [hφ]
      show ((c₁ * (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
        c₂ * (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 +
        c₃ * ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
          (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0) : ℤ) : ZMod (scalarGap A)) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      refine ⟨y, ?_⟩
      rw [h01, h10, h11, h00]
      linear_combination y * hbez
  exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hker.symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj)⟩

/-- **The index formula**: `[End(A) : ℤ[A]] = gcd(A₀₁, A₁₀, A₁₁ - A₀₀)`. -/
theorem index_adjoinInt_commutant (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ∀ c : ℤ, A ≠ (c : Matrix (Fin 2) (Fin 2) ℤ)) :
    ((adjoinInt A).addSubgroupOf (commutant A)).index = scalarGap A := by
  obtain ⟨e⟩ := commutant_quotient_equiv A hA
  rw [AddSubgroup.index, Nat.card_congr e.toEquiv, Nat.card_zmod]

/-! ## The 2-torsion criterion (`lem:2tor`) -/

/-- Parity form: `2 ∣ scalarGap A` iff `A ≡ 1 (mod 2)`, for `det A` odd. -/
theorem two_dvd_scalarGap_iff {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hodd : ¬(2 : ℤ) ∣ A.det) :
    2 ∣ scalarGap A ↔ A.map (Int.cast : ℤ → ZMod 2) = 1 := by
  rw [Matrix.det_fin_two] at hodd
  constructor
  · intro h
    have h2 : ((2 : ℕ) : ℤ) ∣ ((scalarGap A : ℕ) : ℤ) := by exact_mod_cast h
    have hβ : (2 : ℤ) ∣ A 0 1 := by
      have := dvd_trans h2 (scalarGap_dvd₁ A); exact_mod_cast this
    have hγ : (2 : ℤ) ∣ A 1 0 := by
      have := dvd_trans h2 (scalarGap_dvd₂ A); exact_mod_cast this
    have hτ : (2 : ℤ) ∣ A 1 1 - A 0 0 := by
      have := dvd_trans h2 (scalarGap_dvd₃ A); exact_mod_cast this
    -- `det` odd forces the diagonal to be odd
    have hα : ¬(2 : ℤ) ∣ A 0 0 := by
      intro hd
      apply hodd
      obtain ⟨b, hb⟩ := hβ
      obtain ⟨c, hc⟩ := hγ
      obtain ⟨a, ha⟩ := hd
      exact ⟨a * A 1 1 - 2 * b * c,
        by linear_combination (A 1 1) * ha - (A 1 0) * hb - 2 * b * hc⟩
    have hα1 : ((A 0 0 : ℤ) : ZMod 2) = 1 := by
      have hd : (2 : ℤ) ∣ A 0 0 - 1 := by omega
      have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (A 0 0 - 1) 2).mpr
        (by exact_mod_cast hd)
      push_cast at h0
      linear_combination h0
    ext i j
    rw [Matrix.map_apply, Matrix.one_apply]
    fin_cases i <;> fin_cases j
    · simpa using hα1
    · simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (A 0 1) 2).mpr
        (by exact_mod_cast hβ)
    · simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (A 1 0) 2).mpr
        (by exact_mod_cast hγ)
    · have hτ0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (A 1 1 - A 0 0) 2).mpr
        (by exact_mod_cast hτ)
      push_cast at hτ0
      simpa using (by linear_combination hτ0 + hα1 :
        ((A 1 1 : ℤ) : ZMod 2) = 1)
  · intro h
    have hent : ∀ i j, ((A i j : ℤ) : ZMod 2) = if i = j then 1 else 0 := by
      intro i j
      have := congrFun (congrFun h i) j
      rw [Matrix.map_apply, Matrix.one_apply] at this
      exact this
    have hβ : (2 : ℤ) ∣ A 0 1 := by
      have := hent 0 1
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (A 0 1) 2).mp (by simpa using this)
    have hγ : (2 : ℤ) ∣ A 1 0 := by
      have := hent 1 0
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd (A 1 0) 2).mp (by simpa using this)
    have hτ : (2 : ℤ) ∣ A 1 1 - A 0 0 := by
      have hzero : ((A 1 1 - A 0 0 : ℤ) : ZMod 2) = 0 := by
        push_cast
        rw [show ((A 1 1 : ℤ) : ZMod 2) = 1 from by simpa using hent 1 1,
          show ((A 0 0 : ℤ) : ZMod 2) = 1 from by simpa using hent 0 0]
        ring
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hzero
    show 2 ∣ Int.gcd (A 0 1) ((Int.gcd (A 1 0) (A 1 1 - A 0 0) : ℕ) : ℤ)
    refine Int.dvd_gcd (by exact_mod_cast hβ) ?_
    have h2 : 2 ∣ Int.gcd (A 1 0) (A 1 1 - A 0 0) :=
      Int.dvd_gcd (by exact_mod_cast hγ) (by exact_mod_cast hτ)
    exact_mod_cast h2

/-- **`lem:2tor`, matrix layer**: for `A` non-scalar with odd determinant,
`2 ∣ [End(A) : ℤ[A]]` iff `A ≡ 1 (mod 2)`. -/
theorem two_dvd_index_iff (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hodd : ¬(2 : ℤ) ∣ A.det)
    (hA : ∀ c : ℤ, A ≠ (c : Matrix (Fin 2) (Fin 2) ℤ)) :
    2 ∣ ((adjoinInt A).addSubgroupOf (commutant A)).index ↔
      A.map (Int.cast : ℤ → ZMod 2) = 1 := by
  rw [index_adjoinInt_commutant A hA, two_dvd_scalarGap_iff hodd]

/-- **`lem:2tor`, paper form**: for `A ∈ 𝓜(a, p)` with `p` an odd prime,
`2 ∣ [End(A) : ℤ[A]]` iff `A ≡ 1 (mod 2)`. Primality supplies
non-scalarity (a scalar matrix has square determinant); the bridge
`E[2] ⊆ E(𝔽_p) ⟺ Frobenius ≡ 1 (mod 2)` stays on paper. -/
theorem MObj.two_dvd_index_iff {a p : ℤ} (hp : Prime p) (hodd : Odd p)
    (A : MObj a p) :
    2 ∣ ((adjoinInt A.mat).addSubgroupOf (commutant A.mat)).index ↔
      A.mat.map (Int.cast : ℤ → ZMod 2) = 1 := by
  apply _root_.MatrixCategory.two_dvd_index_iff
  · rw [A.det_eq]
    obtain ⟨m, hm⟩ := hodd
    rintro ⟨k, hk⟩
    omega
  · intro c hc
    apply hp.not_unit
    have hdet : p = c * c := by
      rw [← A.det_eq, hc, Matrix.det_fin_two,
        intCast_matrix_apply, intCast_matrix_apply,
        intCast_matrix_apply, intCast_matrix_apply]
      norm_num
    have hpc : p ∣ c := (hp.dvd_mul.mp (hdet ▸ dvd_rfl)).elim id id
    obtain ⟨e, he⟩ := hpc
    have h1 : 1 = p * (e * e) :=
      mul_left_cancel₀ hp.ne_zero (by linear_combination hdet + (c + p * e) * he)
    exact IsUnit.of_mul_eq_one (e * e) h1.symm

end MatrixCategory
