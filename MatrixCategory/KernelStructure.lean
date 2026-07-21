import Mathlib
import MatrixCategory.Content
import MatrixCategory.Smith

/-!
# Structure of the kernel of `M mod n`

Paper reference: the kernel-group lemma — for a 2×2 integer matrix `M`, the
kernel of `M` acting on `(ℤ/nℤ)²` is `ℤ/cm × ℤ/m`.

## Statement design (phase 1)

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
* **Hypotheses.** `NeZero n` is genuinely needed (for `n = 0` the statement
  is *false*: over `ZMod 0 = ℤ` an injective `M` has trivial kernel while the
  right-hand side is finite nontrivial). The paper's `det M ≠ 0` turned out
  to be unnecessary: for `det M = 0` we get `smithTwo M = 0` by ℕ-division
  convention, `Nat.gcd 0 n = n`, and the statement remains true — covering
  rank-1 matrices (SNF `diag(content, 0)`) and `M = 0`.

## Proof plan (phase 3): the lemma DAG

The Mathlib archaeology (phase 2) verdict: Mathlib has Smith normal form only
in module form (`Submodule.smithNormalForm`, `quotientEquivPiZMod`) with
*opaque* coefficients — nothing identifies them with `content` and
`|det|/content`, and no divisibility chain is provided. So we work at the
matrix level and concentrate all the number theory in one leaf:

* `exists_smith_diagonalization` (**L1, the crux**): `U * M * V = diag(d₁, d₂)`
  with `U V` units of `Matrix (Fin 2) (Fin 2) ℤ` and the *explicit* invariants.
* `ker_mulVecLin_of_unit_mul` (**L2**): multiplying by units on either side
  does not change the kernel, up to `≃+` (over any commutative ring).
* `ker_mulVecLin_diagonal` (**L3**): the kernel of a diagonal matrix splits as
  a product of kernels of scalar multiplications.
* `ker_lsmul_zmod` (**L4**): the kernel of multiplication by `d` on `ZMod n`
  is `ZMod (gcd d n)`.

`ker_structure` composes L1–L4; the composition is fully written, so the
remaining `sorry`s are exactly the unproven leaves.
-/

namespace MatrixCategory

open Matrix

/-! ## The lemma DAG

The Smith invariants (`smithOne`, `smithTwo`) and L1
(`exists_smith_diagonalization`) live in `MatrixCategory.Smith`;
the remaining leaves L2–L4 are below. -/

/-- **L2.** Multiplying by units on either side does not change the kernel of
`mulVecLin`, up to additive isomorphism: the equivalence is `v ↦ Q.mulVec v`. -/
theorem ker_mulVecLin_of_unit_mul {R : Type*} [CommRing R]
    {A B P Q : Matrix (Fin 2) (Fin 2) R} (hP : IsUnit P) (hQ : IsUnit Q)
    (h : A = P * B * Q) :
    Nonempty (LinearMap.ker A.mulVecLin ≃+ LinearMap.ker B.mulVecLin) := by
  lift P to (Matrix (Fin 2) (Fin 2) R)ˣ using hP with Pu
  lift Q to (Matrix (Fin 2) (Fin 2) R)ˣ using hQ with Qu
  -- `mulVec` by a unit is injective (kill a vector, hit it with the inverse).
  have hPinj : ∀ x : Fin 2 → R, (Pu : Matrix (Fin 2) (Fin 2) R).mulVec x = 0 → x = 0 := by
    intro x hx
    have h' := congrArg (fun y => (↑Pu⁻¹ : Matrix (Fin 2) (Fin 2) R).mulVec y) hx
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h'
    exact h'
  have hmem : ∀ v : Fin 2 → R, v ∈ LinearMap.ker A.mulVecLin ↔
      (B * (Qu : Matrix (Fin 2) (Fin 2) R)).mulVec v = 0 := by
    intro v
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, h]
    constructor
    · intro hv
      apply hPinj
      rwa [Matrix.mulVec_mulVec, ← mul_assoc]
    · intro hv
      rw [mul_assoc, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  exact ⟨{
    toFun := fun v => ⟨(Qu : Matrix (Fin 2) (Fin 2) R).mulVec v.1, by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      exact (hmem v.1).mp v.2⟩
    invFun := fun w => ⟨(↑Qu⁻¹ : Matrix (Fin 2) (Fin 2) R).mulVec w.1, by
      rw [hmem, Matrix.mulVec_mulVec, mul_assoc, Units.mul_inv, mul_one]
      exact w.2⟩
    left_inv := fun v => Subtype.ext (by
      simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec])
    right_inv := fun w => Subtype.ext (by
      simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec])
    map_add' := fun v w => Subtype.ext (by
      show (↑Qu : Matrix (Fin 2) (Fin 2) R).mulVec (↑v + ↑w) = _
      rw [Matrix.mulVec_add]
      rfl) }⟩

/-- **L3.** The kernel of a diagonal matrix splits as the product of the
kernels of the scalar multiplications by its diagonal entries. -/
theorem ker_mulVecLin_diagonal {R : Type*} [CommRing R] (w : Fin 2 → R) :
    Nonempty (LinearMap.ker (Matrix.diagonal w).mulVecLin ≃+
      (LinearMap.ker (LinearMap.lsmul R R (w 0)) ×
        LinearMap.ker (LinearMap.lsmul R R (w 1)))) := by
  have hmem : ∀ v : Fin 2 → R,
      v ∈ LinearMap.ker (Matrix.diagonal w).mulVecLin ↔ ∀ i, w i * v i = 0 := by
    intro v
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff]
    simp [Matrix.mulVec_diagonal]
  have hmem' : ∀ a x : R, x ∈ LinearMap.ker (LinearMap.lsmul R R a) ↔ a * x = 0 := by
    intro a x
    simp [LinearMap.mem_ker]
  exact ⟨{
    toFun := fun v =>
      (⟨v.1 0, (hmem' _ _).mpr ((hmem v.1).mp v.2 0)⟩,
       ⟨v.1 1, (hmem' _ _).mpr ((hmem v.1).mp v.2 1)⟩)
    invFun := fun p => ⟨![p.1.1, p.2.1], (hmem _).mpr (by
      intro i
      fin_cases i
      · simpa using (hmem' _ _).mp p.1.2
      · simpa using (hmem' _ _).mp p.2.2)⟩
    left_inv := fun v => Subtype.ext (by
      funext i
      fin_cases i <;> rfl)
    right_inv := fun p => by
      ext <;> rfl
    map_add' := fun v u => by
      ext <;> rfl }⟩

/-- **L4.** The kernel of multiplication by `d` on `ZMod n` is cyclic of order
`gcd d n`, generated by `n / gcd d n`. -/
theorem ker_lsmul_zmod (n d : ℕ) [NeZero n] :
    Nonempty (LinearMap.ker (LinearMap.lsmul (ZMod n) (ZMod n) ((d : ℕ) : ZMod n)) ≃+
      ZMod (Nat.gcd d n)) := by
  set g := Nat.gcd d n with hg
  set e := n / g with he
  have hgn : g ∣ n := Nat.gcd_dvd_right d n
  have hgd : g ∣ d := Nat.gcd_dvd_left d n
  have hn0 : n ≠ 0 := NeZero.ne n
  have hg0 : g ≠ 0 := fun h => hn0 (Nat.eq_zero_of_gcd_eq_zero_right h)
  have hge : g * e = n := Nat.mul_div_cancel' hgn
  have he0 : e ≠ 0 := by
    intro h
    rw [h, mul_zero] at hge
    exact hn0 hge.symm
  have hmem : ∀ x : ZMod n,
      x ∈ LinearMap.ker (LinearMap.lsmul (ZMod n) (ZMod n) ((d : ℕ) : ZMod n)) ↔
        (d : ZMod n) * x = 0 := by
    intro x
    simp [LinearMap.mem_ker]
  -- The homomorphism `ℤ/g → ℤ/n`, `1 ↦ e = n/g`, via the universal property.
  have hφg : (zmultiplesHom (ZMod n) ((e : ℕ) : ZMod n)) (g : ℤ) = 0 := by
    simp only [zmultiplesHom_apply, natCast_zsmul, nsmul_eq_mul, ← Nat.cast_mul, hge,
      ZMod.natCast_self]
  set φ : ZMod g →+ ZMod n :=
    ZMod.lift g ⟨zmultiplesHom (ZMod n) ((e : ℕ) : ZMod n), hφg⟩ with hφ
  have hφ_int : ∀ a : ℤ, φ ((a : ℤ) : ZMod g) = ((a * e : ℤ) : ZMod n) := by
    intro a
    rw [hφ, ZMod.lift_coe]
    push_cast [zmultiplesHom_apply, zsmul_eq_mul]
    ring
  -- The image lies in the kernel: `d * (a·e) = (d/g)·n·a ≡ 0`.
  have hneN : n ∣ d * e := by
    refine ⟨d / g, ?_⟩
    conv_lhs => rw [← Nat.mul_div_cancel' hgd]
    rw [← hge]
    ring
  have hne : (n : ℤ) ∣ (d : ℤ) * e := by exact_mod_cast hneN
  have hrange : ∀ k : ZMod g,
      φ k ∈ LinearMap.ker (LinearMap.lsmul (ZMod n) (ZMod n) ((d : ℕ) : ZMod n)) := by
    intro k
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective k
    rw [hmem, hφ_int]
    rw [show ((d : ℕ) : ZMod n) = ((d : ℤ) : ZMod n) by push_cast; rfl,
      ← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]
    calc (n : ℤ) ∣ d * e := hne
      _ ∣ d * (a * e) := by rw [mul_left_comm]; exact dvd_mul_left _ _
  -- Corestrict to the kernel and prove bijectivity.
  set ψ : ZMod g →+ LinearMap.ker (LinearMap.lsmul (ZMod n) (ZMod n) ((d : ℕ) : ZMod n)) :=
    { toFun := fun k => ⟨φ k, hrange k⟩
      map_zero' := Subtype.ext (map_zero φ)
      map_add' := fun a b => Subtype.ext (map_add φ a b) } with hψ
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    obtain ⟨a, rfl⟩ := ZMod.intCast_surjective k
    have h0 : φ ((a : ℤ) : ZMod g) = 0 := by
      simpa [hψ, Subtype.ext_iff] using hk
    rw [hφ_int, ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : (g : ℤ) * e ∣ a * e := by
      rw [show ((g : ℤ) * e = (n : ℤ)) by exact_mod_cast hge]
      exact h0
    exact (mul_dvd_mul_iff_right (by exact_mod_cast he0)).mp this
  have hsurj : Function.Surjective ψ := by
    rintro ⟨x, hx⟩
    rw [hmem] at hx
    -- lift `x` to `ℕ`; from `n ∣ d·a` and coprimality of `d/g, n/g` get `e ∣ a`.
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, (a : ZMod n) = x := ⟨x.val, ZMod.natCast_rightInverse x⟩
    have hda : n ∣ d * a := by
      have hcast : ((d * a : ℕ) : ZMod n) = 0 := by push_cast; exact hx
      exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
    have hd' : e ∣ (d / g) * a := by
      have h1 : g * e ∣ g * ((d / g) * a) := by
        rw [hge, ← mul_assoc, Nat.mul_div_cancel' hgd]
        exact hda
      exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hg0)).mp h1
    have hea : e ∣ a :=
      Nat.Coprime.dvd_of_dvd_mul_left
        (Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero hg0)).symm hd'
    refine ⟨((a / e : ℕ) : ZMod g), Subtype.ext ?_⟩
    show φ _ = _
    have hc : (((a / e : ℕ) : ℤ) : ZMod g) = ((a / e : ℕ) : ZMod g) := Int.cast_natCast _
    rw [← hc, hφ_int]
    have hae : ((a / e : ℕ) : ℤ) * e = ((a : ℕ) : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel hea
    rw [hae]
    push_cast
    rfl
  exact ⟨(AddEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm⟩

/-! ## The main theorem -/

/-- **Kernel structure theorem.**

For `M` a 2×2 integer matrix and `n ≠ 0`, the kernel of `M mod n` acting on
`(ℤ/nℤ)²` is isomorphic as an additive group to `ℤ/(cm) × ℤ/m` where
`m = gcd(d₁, n)`, `cm = gcd(d₂, n)`, and `d₁ ∣ d₂` are the Smith invariants
of `M`. No hypothesis on `det M` is needed. -/
theorem ker_structure (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) [NeZero n] :
    Nonempty
      (LinearMap.ker ((M.map (Int.cast : ℤ → ZMod n)).mulVecLin) ≃+
        ZMod (Nat.gcd (smithTwo M) n) × ZMod (Nat.gcd (smithOne M) n)) := by
  obtain ⟨U, V, hUV⟩ := exists_smith_diagonalization M
  set D : Matrix (Fin 2) (Fin 2) ℤ :=
    Matrix.diagonal ![(smithOne M : ℤ), (smithTwo M : ℤ)] with hD
  -- Solve `U * M * V = D` for `M`.
  have hM' : M = (↑U⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) * D * (↑V⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← hUV]
    simp [mul_assoc]
  -- Reduce mod n through the ring hom `Int.castRingHom (ZMod n)`, matrix-wise.
  set f : Matrix (Fin 2) (Fin 2) ℤ →+* Matrix (Fin 2) (Fin 2) (ZMod n) :=
    (Int.castRingHom (ZMod n)).mapMatrix with hf
  have hmap : M.map (Int.cast : ℤ → ZMod n) = f ↑U⁻¹ * f D * f ↑V⁻¹ := by
    have := congrArg f hM'
    simpa [hf, RingHom.mapMatrix_apply, map_mul] using this
  obtain ⟨e₁⟩ :=
    ker_mulVecLin_of_unit_mul (U⁻¹.isUnit.map f) (V⁻¹.isUnit.map f) hmap
  -- The reduced matrix is diagonal with entries the reduced invariants.
  have hDmap : f D =
      Matrix.diagonal ![((smithOne M : ℕ) : ZMod n), ((smithTwo M : ℕ) : ZMod n)] := by
    rw [hf, RingHom.mapMatrix_apply, hD, Matrix.diagonal_map (by simp)]
    congr 1
    ext i
    fin_cases i <;> simp
  rw [hDmap] at e₁
  obtain ⟨e₂⟩ := ker_mulVecLin_diagonal
    ![((smithOne M : ℕ) : ZMod n), ((smithTwo M : ℕ) : ZMod n)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e₂
  obtain ⟨e₃⟩ := ker_lsmul_zmod n (smithOne M)
  obtain ⟨e₄⟩ := ker_lsmul_zmod n (smithTwo M)
  exact ⟨e₁.trans <| e₂.trans <| (AddEquiv.prodCongr e₃ e₄).trans AddEquiv.prodComm⟩

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
-- det = 0 cases (the dropped hypothesis): rank 1, invariants (1,0), and M = 0.
#guard kerCard !![2, 4; 1, 2] 6 == predictedCard !![2, 4; 1, 2] 6
#guard kerCard !![3, 6; 6, 12] 9 == predictedCard !![3, 6; 6, 12] 9
#guard kerCard (0 : Matrix (Fin 2) (Fin 2) ℤ) 5 == predictedCard 0 5

end MatrixCategory
