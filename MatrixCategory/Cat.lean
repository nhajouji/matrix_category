import Mathlib
import MatrixCategory.Content

/-!
# The matrix category 𝓜(α)

Fix a quadratic integer `α` with trace `t` and norm `d`, i.e. a root of
`X² - tX + d`. The matrix category `𝓜(α)` has:

* **objects**: 2×2 integer matrices `A` with `trace A = t` and `det A = d` —
  the possible matrices of "multiplication by `α`" on a rank-2 lattice with
  a chosen basis;
* **morphisms** `A ⟶ B`: integer matrices `M` with `M * A = B * M` — lattice
  maps intertwining the two `α`-actions;
* composition: matrix multiplication.

This file makes `𝓜(α)` a literal `CategoryTheory.Category`. The bridge to
elliptic curves (objects ↔ curves with CM by `α`, morphisms ↔ isogenies)
stays on paper.

`MObj.sq_eq` verifies the design: every object genuinely satisfies the same
quadratic `A² = tA - d` as `α` (2×2 Cayley–Hamilton, proved by hand from
the trace and determinant equations).
-/

namespace MatrixCategory

open Matrix CategoryTheory

/-- An object of the matrix category `𝓜(α)` for `α` of trace `t` and norm
`d`: a 2×2 integer matrix with that trace and determinant. -/
@[ext]
structure MObj (t d : ℤ) where
  mat : Matrix (Fin 2) (Fin 2) ℤ
  trace_eq : mat.trace = t
  det_eq : mat.det = d

namespace MObj

variable {t d : ℤ}

/-- Morphisms of `𝓜(α)`: integer matrices intertwining the `α`-actions. -/
@[ext]
structure Hom (A B : MObj t d) where
  mat : Matrix (Fin 2) (Fin 2) ℤ
  comm : mat * A.mat = B.mat * mat

/-- `𝓜(α)` is a category under matrix multiplication. -/
instance : Category (MObj t d) where
  Hom := Hom
  id A := ⟨1, by rw [one_mul, mul_one]⟩
  comp f g := ⟨g.mat * f.mat, by
    rw [mul_assoc, f.comm, ← mul_assoc, g.comm, mul_assoc]⟩
  id_comp f := by
    apply Hom.ext
    exact mul_one f.mat
  comp_id f := by
    apply Hom.ext
    exact one_mul f.mat
  assoc f g h := by
    apply Hom.ext
    exact (mul_assoc h.mat g.mat f.mat).symm

@[simp]
theorem id_mat (A : MObj t d) : Hom.mat (𝟙 A) = 1 := rfl

@[simp]
theorem comp_mat {A B C : MObj t d} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).mat = g.mat * f.mat := rfl

/-- The principal object: the companion matrix of `X² - tX + d`, i.e.
multiplication by `α` on `ℤ[α]` in the basis `(1, α)`. -/
def companion (t d : ℤ) : MObj t d where
  mat := !![0, -d; 1, t]
  trace_eq := by rw [Matrix.trace_fin_two_of]; ring
  det_eq := by rw [Matrix.det_fin_two_of]; ring

/-- `α` itself is an endomorphism of every object. -/
def alphaEnd (A : MObj t d) : A ⟶ A := ⟨A.mat, rfl⟩

/-! ### The conjugation action

Units of `M₂(ℤ)` act on `𝓜(α)` by conjugation — base change of the
underlying lattice. Orbits are the isomorphism classes of objects. -/

/-- Conjugation of objects by units of `M₂(ℤ)`. -/
def conj (P : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (A : MObj t d) : MObj t d where
  mat := (P : Matrix (Fin 2) (Fin 2) ℤ) * A.mat * (↑P⁻¹ : Matrix (Fin 2) (Fin 2) ℤ)
  trace_eq := by
    rw [Matrix.trace_mul_cycle, Units.inv_mul, one_mul]
    exact A.trace_eq
  det_eq := by
    rw [Matrix.det_mul, Matrix.det_mul,
      mul_comm ((P : Matrix (Fin 2) (Fin 2) ℤ).det) A.mat.det, mul_assoc,
      ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, mul_one]
    exact A.det_eq

theorem conj_one (A : MObj t d) : conj 1 A = A := by
  ext i j
  simp [conj]

theorem conj_mul (P Q : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (A : MObj t d) :
    conj (P * Q) A = conj P (conj Q A) := by
  ext i j
  simp [conj, Units.val_mul, _root_.mul_inv_rev, mul_assoc]

instance : MulAction (Matrix (Fin 2) (Fin 2) ℤ)ˣ (MObj t d) where
  smul := conj
  one_smul := conj_one
  mul_smul := conj_mul

@[simp]
theorem smul_mat (P : (Matrix (Fin 2) (Fin 2) ℤ)ˣ) (A : MObj t d) :
    (P • A).mat =
      (P : Matrix (Fin 2) (Fin 2) ℤ) * A.mat * (↑P⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) := rfl

/-- Sanity check of the design: every object satisfies the same quadratic
`A² = t·A - d` as `α` (Cayley–Hamilton for 2×2, from the trace and
determinant equations), stated entrywise. -/
theorem sq_eq (A : MObj t d) (i j : Fin 2) :
    (A.mat * A.mat) i j = t * A.mat i j - d * (1 : Matrix (Fin 2) (Fin 2) ℤ) i j := by
  have ht := A.trace_eq
  have hd := A.det_eq
  rw [Matrix.trace_fin_two] at ht
  rw [Matrix.det_fin_two] at hd
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    linear_combination A.mat 0 0 * ht - hd
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    linear_combination A.mat 0 1 * ht
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    linear_combination A.mat 1 0 * ht
  · simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
    linear_combination A.mat 1 1 * ht - hd

end MObj

end MatrixCategory
