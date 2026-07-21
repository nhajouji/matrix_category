import Mathlib

/-!
# The primitive-isogeny characterization lemma (matrix layer)

Paper reference: `lem:primitive_isogeny_characterization`.

For an integer matrix `M` and an integer `d`, the following are equivalent:
* `d` divides the content of `M` (the gcd of its entries);
* `d` divides every entry of `M`;
* (for `d = m` a natural number) the reduction of `M` mod `m` is the zero
  matrix over `ZMod m`, i.e. `M ≡ 0 (mod m)`.

The bridge to elliptic curves (where `M` is the matrix of an isogeny on a
torsion basis and "content = 1" characterizes primitive isogenies) stays on
paper; this file is the pure matrix statement.
-/

namespace MatrixCategory

open Matrix

/-- The content of an integer matrix: the gcd of all of its entries. -/
def content {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℤ) : ℤ :=
  Finset.univ.gcd fun p : Fin n × Fin k => M p.1 p.2

/-- An integer divides the content of `M` iff it divides every entry. -/
theorem dvd_content_iff {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℤ) (d : ℤ) :
    d ∣ content M ↔ ∀ i j, d ∣ M i j := by
  unfold content
  rw [Finset.dvd_gcd_iff]
  constructor
  · intro h i j
    exact h (i, j) (Finset.mem_univ _)
  · intro h p _
    exact h p.1 p.2

/-- `M ≡ 0 (mod m)` — reduction of `M` mod `m` is the zero matrix — iff `m`
divides the content of `M`. This is `lem:primitive_isogeny_characterization`
in matrix form. -/
theorem map_zmod_eq_zero_iff_dvd_content {n k : ℕ} (m : ℕ)
    (M : Matrix (Fin n) (Fin k) ℤ) :
    M.map (Int.cast : ℤ → ZMod m) = 0 ↔ (m : ℤ) ∣ content M := by
  rw [dvd_content_iff]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using this
  · intro h
    ext i j
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h i j

/-- A matrix is primitive iff its content is a unit (i.e. gcd of entries is 1). -/
def IsPrimitive {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℤ) : Prop :=
  IsUnit (content M)

/-- `M` is primitive iff for every prime `p`, `M` does not reduce to `0` mod `p`. -/
theorem isPrimitive_iff_forall_prime {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℤ) :
    IsPrimitive M ↔ ∀ p : ℕ, p.Prime → M.map (Int.cast : ℤ → ZMod p) ≠ 0 := by
  unfold IsPrimitive
  constructor
  · intro h p hp hmap
    rw [map_zmod_eq_zero_iff_dvd_content] at hmap
    have hu : IsUnit ((p : ℕ) : ℤ) := isUnit_of_dvd_unit hmap h
    have h1 : p = 1 := by simpa using Int.isUnit_iff_natAbs_eq.mp hu
    exact hp.one_lt.ne' h1
  · intro h
    by_contra hc
    have hna : (content M).natAbs ≠ 1 := fun h1 => hc (Int.isUnit_iff_natAbs_eq.mpr h1)
    obtain ⟨p, hp, hdvd⟩ := Int.exists_prime_and_dvd hna
    have hpn : p.natAbs.Prime := Int.prime_iff_natAbs_prime.mp hp
    apply h p.natAbs hpn
    rw [map_zmod_eq_zero_iff_dvd_content]
    exact Int.natAbs_dvd.mpr hdvd

end MatrixCategory
