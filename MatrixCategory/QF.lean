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

end MObj

end MatrixCategory
