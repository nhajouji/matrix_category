import Mathlib
import MatrixCategory.Cat

/-!
# Binary quadratic forms and the bijection with 𝓜(α)

Paper reference: `prop:qf_matrix_bijection` — the bijection 𝒬(α) ↔ 𝓜(α).

Mathlib has no classical binary quadratic forms (the form class group with
Dirichlet composition is absent), so we define the type by hand: `BQF D` is
a triple `(a, b, c)` with `b² - 4ac = D`.

The bijection with `MObj t d` (matrices of trace `t`, determinant `d`,
where `D = t² - 4d`) is completely explicit:

* `A = [[r, s], [u, v]] ↦ (u, v - r, -s)` — the form
  `q(x, y) = -det[A·(x,y)ᵀ | (x,y)ᵀ]`, measuring the failure of `(x, y)`
  to be an eigenvector of `A`;
* `(a, b, c) ↦ [[(t-b)/2, -c], [a, (t+b)/2]]` — integrality of `(t ± b)/2`
  is *forced* by the discriminant condition, since `b² - t² = 4(ac - d)`
  makes `b` and `t` have the same parity (`BQF.two_dvd_sub`).
-/

namespace MatrixCategory

open Matrix

/-- A binary quadratic form `a·x² + b·xy + c·y²` of discriminant `D`. -/
@[ext]
structure BQF (D : ℤ) where
  a : ℤ
  b : ℤ
  c : ℤ
  disc_eq : b ^ 2 - 4 * (a * c) = D

namespace BQF

/-- The value of the form at `(x, y)`. -/
def eval {D : ℤ} (q : BQF D) (x y : ℤ) : ℤ :=
  q.a * x ^ 2 + q.b * (x * y) + q.c * y ^ 2

/-- The parity obstruction vanishes: for a form of discriminant `t² - 4d`,
the middle coefficient has the parity of `t`, because
`b² - t² = 4(ac - d)`. -/
theorem two_dvd_sub {t d : ℤ} (q : BQF (t ^ 2 - 4 * d)) : 2 ∣ t - q.b := by
  have h4 : (4 : ℤ) ∣ q.b ^ 2 - t ^ 2 :=
    ⟨q.a * q.c - d, by linear_combination q.disc_eq⟩
  rcases Int.even_or_odd q.b with hb | hb <;> rcases Int.even_or_odd t with ht | ht
  · obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := ht
    exact ⟨y - x, by omega⟩
  · exfalso
    obtain ⟨k, hk⟩ := h4
    obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := ht
    rw [hx, hy] at hk
    have h1 : (4 : ℤ) * (x ^ 2 - y ^ 2 - y - k) = 1 := by linear_combination hk
    have h2 : (4 : ℤ) ∣ 1 := ⟨_, h1.symm⟩
    norm_num at h2
  · exfalso
    obtain ⟨k, hk⟩ := h4
    obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := ht
    rw [hx, hy] at hk
    have h1 : (4 : ℤ) * (x ^ 2 + x - y ^ 2 - k) = -1 := by linear_combination hk
    have h2 : (4 : ℤ) ∣ 1 := ⟨-(x ^ 2 + x - y ^ 2 - k), by omega⟩
    norm_num at h2
  · obtain ⟨x, hx⟩ := hb
    obtain ⟨y, hy⟩ := ht
    exact ⟨y - x, by omega⟩

end BQF

namespace MObj

variable {t d : ℤ}

/-- The form attached to an object of `𝓜(α)`:
`q(x,y) = -det[A·(x,y)ᵀ | (x,y)ᵀ]`. -/
def toBQF (A : MObj t d) : BQF (t ^ 2 - 4 * d) where
  a := A.mat 1 0
  b := A.mat 1 1 - A.mat 0 0
  c := -(A.mat 0 1)
  disc_eq := by
    have ht := A.trace_eq
    have hd := A.det_eq
    rw [Matrix.trace_fin_two] at ht
    rw [Matrix.det_fin_two] at hd
    linear_combination (A.mat 0 0 + A.mat 1 1 + t) * ht - 4 * hd

/-- The object of `𝓜(α)` attached to a form of discriminant `t² - 4d`. -/
def ofBQF (t d : ℤ) (q : BQF (t ^ 2 - 4 * d)) : MObj t d where
  mat := !![(t - q.b) / 2, -q.c; q.a, (t + q.b) / 2]
  trace_eq := by
    rw [Matrix.trace_fin_two_of]
    obtain ⟨k, hk⟩ := q.two_dvd_sub
    omega
  det_eq := by
    rw [Matrix.det_fin_two_of]
    obtain ⟨k, hk⟩ := q.two_dvd_sub
    have h1 : (t - q.b) / 2 = k := by omega
    have h2 : (t + q.b) / 2 = k + q.b := by omega
    rw [h1, h2]
    have hd := q.disc_eq
    have ht : t = 2 * k + q.b := by omega
    have h4 : (4 : ℤ) * (k * (k + q.b) - -q.c * q.a) = 4 * d := by
      linear_combination -hd - (t + 2 * k + q.b) * ht
    exact Int.eq_of_mul_eq_mul_left (by norm_num) h4

/-- **The bijection 𝒬(α) ↔ 𝓜(α)** (`prop:qf_matrix_bijection`): objects of
the matrix category of trace `t` and norm `d` correspond exactly to binary
quadratic forms of discriminant `t² - 4d`. -/
def qfEquiv (t d : ℤ) : MObj t d ≃ BQF (t ^ 2 - 4 * d) where
  toFun := toBQF
  invFun := ofBQF t d
  left_inv A := by
    have ht := A.trace_eq
    rw [Matrix.trace_fin_two] at ht
    ext i j
    fin_cases i <;> fin_cases j
    · simp [ofBQF, toBQF]
      omega
    · simp [ofBQF, toBQF]
    · simp [ofBQF, toBQF]
    · simp [ofBQF, toBQF]
      omega
  right_inv q := by
    obtain ⟨k, hk⟩ := q.two_dvd_sub
    ext
    · simp [ofBQF, toBQF]
    · simp [ofBQF, toBQF]
      omega
    · simp [ofBQF, toBQF]

/-! ### Equivariance

Conjugating an object corresponds to the classical linear change of
variables on its form, twisted by `det P`. The key trick: for a unimodular
`P` the inverse is `det P • adjugate P` (since `det P = ±1` is its own
inverse), which makes the whole identity one polynomial computation modulo
the single relation `(det P)² = 1`. -/

/-- For a unimodular matrix, the inverse is `det P • adjugate P`. -/
theorem unit_inv_eq_det_smul_adjugate (P : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) :
    (↑P⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) =
      (P : Matrix (Fin 2) (Fin 2) ℤ).det • (P : Matrix (Fin 2) (Fin 2) ℤ).adjugate := by
  have hsq : (P : Matrix (Fin 2) (Fin 2) ℤ).det * (P : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rcases Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit) with h | h <;>
      rw [h] <;> norm_num
  have key : (P : Matrix (Fin 2) (Fin 2) ℤ) *
      ((P : Matrix (Fin 2) (Fin 2) ℤ).det • (P : Matrix (Fin 2) (Fin 2) ℤ).adjugate) = 1 := by
    rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hsq, one_smul]
  calc (↑P⁻¹ : Matrix (Fin 2) (Fin 2) ℤ)
      = ↑P⁻¹ * ((P : Matrix (Fin 2) (Fin 2) ℤ) *
          ((P : Matrix (Fin 2) (Fin 2) ℤ).det • (P : Matrix (Fin 2) (Fin 2) ℤ).adjugate)) := by
        rw [key, mul_one]
    _ = (↑P⁻¹ * (P : Matrix (Fin 2) (Fin 2) ℤ)) *
          ((P : Matrix (Fin 2) (Fin 2) ℤ).det • (P : Matrix (Fin 2) (Fin 2) ℤ).adjugate) := by
        rw [mul_assoc]
    _ = (P : Matrix (Fin 2) (Fin 2) ℤ).det • (P : Matrix (Fin 2) (Fin 2) ℤ).adjugate := by
        rw [Units.inv_mul, one_mul]

/-- **Equivariance of the bijection** (`prop:qf_matrix_bijection`, action
layer): conjugating an object of `𝓜(α)` by a unimodular `P` corresponds to
the linear change of variables by `P` on the attached form, twisted by
`det P`. For `P ∈ SL₂(ℤ)` this is exactly proper equivalence of forms
(`toBQF_smul_eval_of_det_eq_one`), so the bijection descends to
`SL₂(ℤ)`-orbits: conjugacy classes in `𝓜(α)` ↔ proper form classes. -/
theorem toBQF_smul_eval (P : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (A : MObj t d) (x y : ℤ) :
    (P • A).toBQF.eval
      ((P : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * x + (P : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * y)
      ((P : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * x + (P : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * y) =
      (P : Matrix (Fin 2) (Fin 2) ℤ).det * A.toBQF.eval x y := by
  have hsq : (P : Matrix (Fin 2) (Fin 2) ℤ).det * (P : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rcases Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det _).mp P.isUnit) with h | h <;>
      rw [h] <;> norm_num
  have hinv := unit_inv_eq_det_smul_adjugate P
  rw [Matrix.det_fin_two] at hsq
  simp only [toBQF, BQF.eval, smul_mat, hinv, Matrix.adjugate_fin_two,
    Matrix.det_fin_two, Matrix.mul_apply, Matrix.smul_apply, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.of_apply, smul_eq_mul]
  linear_combination
    (((P : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (P : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (P : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (P : Matrix (Fin 2) (Fin 2) ℤ) 1 0) *
     (A.mat 1 0 * x ^ 2 + (A.mat 1 1 - A.mat 0 0) * (x * y) - A.mat 0 1 * y ^ 2)) * hsq

/-- Proper equivalence: for `P ∈ SL₂(ℤ)` the bijection is strictly
equivariant. -/
theorem toBQF_smul_eval_of_det_eq_one {P : (Matrix (Fin 2) (Fin 2) ℤ)ˣ}
    (hP : (P : Matrix (Fin 2) (Fin 2) ℤ).det = 1) (A : MObj t d) (x y : ℤ) :
    (P • A).toBQF.eval
      ((P : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * x + (P : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * y)
      ((P : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * x + (P : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * y) =
      A.toBQF.eval x y := by
  have h := toBQF_smul_eval P A x y
  rwa [hP, one_mul] at h

end MObj

end MatrixCategory
