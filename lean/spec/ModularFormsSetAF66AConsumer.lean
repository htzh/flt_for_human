/-
  Cross-module wire test for SET-AF66A (the conjugate form, the Fricke action, the coset sums).

  A `spec/` probe, not a library module. One zone per headline of
  `ModularForms/PrimitiveFormSlash.lean`, each *consuming* the headline rather than restating it:
  the rows are fired on concrete data and the conclusion is read in the shape the downstream cone
  will read it. No primitive form is constructed anywhere in the corpus, so wherever an
  `IsPrimitiveForm` hypothesis is needed it is carried, not discharged.

  * **Zone A, row `CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj` at `k = 0`.**
    Weight zero is the degenerate weight, so the conjugate form is read at the single index `n = 0`:
    the row is fired at level `2` on the zero form, and its coefficient identity is *used* (not
    restated) to transport the vanishing of `qCoeff 0 0` to `qCoeff g' 0`.

  * **Zone B, row `CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one` at `d = 1`
    and `d = -1`.** The Fricke involution satisfies `d ^ 2 = 1`, so it is fired in both
    orientations at level `1`: forward with `τ' = W₁ • τ` (the `d = 1` reading
    `g (W₁ τ) = τ ^ k * h τ`), and backward with the reversed relation
    `τ * (1 * W₁ • τ) = -1` (the `d = -1` reading `g τ = (-τ⁻¹) ^ k * h (W₁ τ)`), since
    `W₁ • τ = -1 / τ`. The two are one involution read in its two directions.

  * **Zone C, row `CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj` at `k = 0`.** The row's
    `q`-coefficient hypothesis is *produced* by zone A's row, so the composition
    `A → C` at weight zero returns the conjugate form together with its primitivity for `ε⁻¹`.

  * **Zone D, row `CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm` at level `2`.**
    The pseudo-eigenvalue `c ≠ 0` is produced for the Fricke involution `W₂` and read at
    `τ' = W₂ • τ`, where `(W₂ • τ) * (2 * τ) = -1` --- the shape the coset sums consume.

  * **Zone E, row `IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd` at the
    divisor pair `q = M = 2`.** The row is fired at `q ∣ M`, and its `z = 0` term
    (`S · T ^ 0 · S⁻¹ = 1`) is split off the `range 2` sum: the zeroth summand is exactly `g τ`.

  * **Zone F, row `…_comp_heckeDiagMatrix_apply_eq_of_not_dvd` at the non-divisor pair `q = 3`,
    `M = 2`.** The row is fired at `q ∤ M`, and again its `z = 0` term is split off: the zeroth
    summand of the `heckeDiagMatrix`-twisted sum is `g (heckeDiagMatrix 3 • τ)`.

  The file contains no `#check`s, no `sorry`s and no placeholder proofs.
-/
import FLTForHuman.ModularForms.PrimitiveFormSlash

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularFormClass
open scoped MatrixGroups ModularForm ComplexConjugate

namespace SetAF66AConsumer

/-- The `q`-coefficients of the zero cusp form vanish --- quoted from the port so that zone A
spends the row's coefficient identity rather than `simp`-ing it away. -/
theorem qCoeff_zero (N : ℕ) (k : ℤ) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma1 N) k)) n = 0 := by
  rw [FunLike.coe_zero, PrimitiveCosetSum.qCoeff_zero_fun]

/-- The Fricke matrix `W_M` sends `τ` to `-1 / (M * τ)`, so `(W_M • τ) * (M * τ) = -1`: the
relation the rows of zones B and D are stated against, read off `FrickeGamma1.coe_frickeGL_smul`. -/
theorem frickeGL_relation (M : ℕ) [NeZero M] (τ : UpperHalfPlane) :
    ((FrickeGamma1.frickeGL M • τ : ℍ) : ℂ) * ((M : ℂ) * (τ : ℂ)) = -1 := by
  rw [FrickeGamma1.coe_frickeGL_smul]
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp

/-- The same relation with its two arguments interchanged --- the hypothesis of the `d = -1`
orientation, where the row is applied to `(W_M • τ, τ)` rather than to `(τ, W_M • τ)`. -/
theorem frickeGL_relation_symm (M : ℕ) [NeZero M] (τ : UpperHalfPlane) :
    (τ : ℂ) * ((M : ℂ) * ((FrickeGamma1.frickeGL M • τ : ℍ) : ℂ)) = -1 := by
  have h := frickeGL_relation M τ
  linear_combination h

/-! ## Zone A: the conjugate form at weight zero -/

/-- **Zone A.** The conjugate form at `k = 0` and level `2`, fired on the zero form. The row's
pointwise identity is carried as its hypothesis-shaped conclusion, and its coefficient identity is
*used* at `n = 0`: at weight zero the conjugate of the zero form has vanishing zeroth coefficient,
which is the whole of what weight zero has to say. -/
theorem zoneA_weightZero :
    ∃ g' : CuspForm (CongruenceSubgroup.Gamma1 2) 0,
      (∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = -(starRingEnd ℂ (τ : ℂ)) →
        g' τ = starRingEnd ℂ ((0 : CuspForm (CongruenceSubgroup.Gamma1 2) 0) τ')) ∧
      ModularFormClass.qCoeff g' 0 = 0 := by
  obtain ⟨g', hpt, hcoef⟩ :=
    CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj 2 0 0
  refine ⟨g', hpt, ?_⟩
  rw [hcoef 0, qCoeff_zero, map_zero]

/-! ## Zone B: the Fricke involution in both orientations -/

/-- **Zone B, `d = 1`.** Level `1`, the Fricke involution `W₁ = [[0, -1], [1, 0]]` in its forward
orientation: the row fired at `τ' = W₁ • τ`, where `(W₁ • τ) * (1 * τ) = -1`, produces the form `h`
with `g (W₁ • τ) = τ ^ k * h τ`. -/
theorem zoneB_d_one (k : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma1 1) k) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma1 1) k, ∀ τ : UpperHalfPlane,
      g (FrickeGamma1.frickeGL 1 • τ) = (τ : ℂ) ^ k * h τ := by
  obtain ⟨h, hh⟩ := CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one 1 k g
  exact ⟨h, fun τ => hh τ (FrickeGamma1.frickeGL 1 • τ) (frickeGL_relation 1 τ)⟩

/-- **Zone B, `d = -1`.** The same involution in its inverse orientation: the row fired on the
*reversed* relation `τ * (1 * W₁ • τ) = -1` produces a form `h` with
`g τ = (-τ⁻¹) ^ k * h (W₁ • τ)`, since `W₁ • τ = -1 / τ`. This is the `d = -1` half of `d ^ 2 = 1`;
composing it with the `d = 1` half is the involution identity. -/
theorem zoneB_d_neg_one (k : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma1 1) k) :
    ∃ h : CuspForm (CongruenceSubgroup.Gamma1 1) k, ∀ τ : UpperHalfPlane,
      g τ = (-(τ : ℂ)⁻¹) ^ k * h (FrickeGamma1.frickeGL 1 • τ) := by
  obtain ⟨h, hh⟩ := CuspForm.exists_gamma1_apply_eq_zpow_mul_apply_of_mul_eq_neg_one 1 k g
  refine ⟨h, fun τ => ?_⟩
  have hW : ((FrickeGamma1.frickeGL 1 • τ : ℍ) : ℂ) = -(τ : ℂ)⁻¹ := by
    rw [FrickeGamma1.coe_frickeGL_smul]
    have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
    field_simp
    norm_num
  rw [hh (FrickeGamma1.frickeGL 1 • τ) τ (frickeGL_relation_symm 1 τ), hW]

/-! ## Zone C: the inverse of a primitive form, at weight zero -/

/-- **Zone C.** The conjugate-inverse row at `k = 0` and level `2`, with its `q`-coefficient
hypothesis *produced* by zone A's row: the composition `A → C` returns the conjugate form together
with its primitivity for `ε⁻¹`. Nothing about the conjugate form is assumed. -/
theorem zoneC_weightZero (ε : DirichletCharacter ℂ 2) (g : CuspForm (CongruenceSubgroup.Gamma1 2) 0)
    (hg : CuspForm.IsPrimitiveForm ε g) :
    ∃ g' : CuspForm (CongruenceSubgroup.Gamma1 2) 0,
      CuspForm.IsPrimitiveForm ε⁻¹ g' ∧
        ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n) := by
  obtain ⟨g', -, hcoef⟩ := CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj 2 0 g
  exact ⟨g', CuspForm.isPrimitiveForm_inv_of_qCoeff_eq_conj 2 0 ε g hg g' hcoef, hcoef⟩

/-! ## Zone D: the Fricke pseudo-eigenvalue -/

/-- **Zone D.** The pseudo-eigenvalue at level `2`: the row produces `c ≠ 0` with
`g (W₂ • τ) = c * τ ^ k * g' τ` for the Fricke transform `W₂` of a primitive form, read at
`W₂ • τ`, where `(W₂ • τ) * (2 * τ) = -1`. -/
theorem zoneD_fricke (k : ℤ) (ε : DirichletCharacter ℂ 2)
    (g g' : CuspForm (CongruenceSubgroup.Gamma1 2) k)
    (hg : CuspForm.IsPrimitiveForm ε g)
    (hg' : ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ τ : UpperHalfPlane,
      g (FrickeGamma1.frickeGL 2 • τ) = c * (τ : ℂ) ^ k * g' τ := by
  obtain ⟨c, hc0, hc⟩ :=
    CuspForm.exists_apply_eq_mul_zpow_mul_apply_of_isPrimitiveForm 2 k ε g hg g' hg'
  exact ⟨c, hc0, fun τ => hc τ (FrickeGamma1.frickeGL 2 • τ) (frickeGL_relation 2 τ)⟩

/-! ## Zone E: the coset sum at a divisor, and its `z = 0` term -/

/-- The `j`-th summand of zone E's coset sum at level `2`, `q = 2`: the twist `S · T ^ z · S⁻¹`
with `z = j * (M / q) = j`. -/
def cosetTermE (k : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma1 2) k) (j : ℕ) :
    UpperHalfPlane → ℂ :=
  (⇑g : UpperHalfPlane → ℂ) ∣[k]
    (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (2 / 2 : ℕ)) * ModularGroup.S⁻¹ : SL(2, ℤ))

/-- **Zone E, at the divisor pair `q = M = 2`.** The row, whose coset sum is `q`-coefficient
readable because `2 ∣ 2`. -/
theorem zoneE_divisor (k : ℤ) (ε : DirichletCharacter ℂ 2)
    (g : CuspForm (CongruenceSubgroup.Gamma1 2) k) (hg : CuspForm.IsPrimitiveForm ε g)
    (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range 2, cosetTermE k g j τ
      = (2 : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g 2) *
          g (ModularForm.heckeMatrix 2 0 • τ) :=
  CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd 2 k ε g hg
    Nat.prime_two (dvd_refl 2) τ

/-- **Zone E, the `z = 0` term.** At `z = 0` the twist `S · T ^ 0 · S⁻¹` is the identity, so the
zeroth summand of the coset sum is `g τ` itself: the sum is a deformation of `g`. -/
theorem zoneE_zero_term (k : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma1 2) k)
    (τ : UpperHalfPlane) :
    cosetTermE k g 0 τ = g τ := by
  simp [cosetTermE]

/-- **Zone E, the row with its `z = 0` term split off.** The row's `range 2` sum is `g τ` plus the
one remaining `j = 1` summand --- the shape in which the downstream cone reads the block. -/
theorem zoneE_split (k : ℤ) (ε : DirichletCharacter ℂ 2)
    (g : CuspForm (CongruenceSubgroup.Gamma1 2) k) (hg : CuspForm.IsPrimitiveForm ε g)
    (τ : UpperHalfPlane) :
    g τ + ∑ j ∈ Finset.range 1, cosetTermE k g (j + 1) τ
      = (2 : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g 2) *
          g (ModularForm.heckeMatrix 2 0 • τ) := by
  have h := zoneE_divisor k ε g hg τ
  rw [Finset.sum_range_succ'] at h
  rw [add_comm] at h
  rw [← zoneE_zero_term k g τ]
  exact h

/-! ## Zone F: the coset sum at a non-divisor, and its `z = 0` term -/

/-- The `j`-th summand of zone F's `heckeDiagMatrix`-twisted coset sum at `M = 2`, `q = 3`: the
twist `S · T ^ z · S⁻¹` with `z = j * M = 2j`, applied to `g (heckeDiagMatrix 3 • ·)`. -/
def cosetTermF (k : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma1 2) k) (j : ℕ) :
    UpperHalfPlane → ℂ :=
  (fun σ : UpperHalfPlane => g (ModularForm.heckeDiagMatrix 3 • σ)) ∣[k]
    (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * 2) * ModularGroup.S⁻¹ : SL(2, ℤ))

/-- **Zone F, at the non-divisor pair `q = 3`, `M = 2`.** The row: the coset sum collapses because
`3 ∤ 2`, and the collapse carries the nebentypus conjugate `conj (ε 3)` --- the `q ∤ M` half of the
pin's block. -/
theorem zoneF_not_dvd (k : ℤ) (ε : DirichletCharacter ℂ 2)
    (g : CuspForm (CongruenceSubgroup.Gamma1 2) k) (hg : CuspForm.IsPrimitiveForm ε g)
    (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range 3, cosetTermF k g j τ
      = (3 : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g 3) * g τ
          - starRingEnd ℂ (ε (3 : ZMod 2)) * (3 : ℂ) ^ (-k) *
              g (ModularForm.heckeMatrix 3 0 • τ) :=
  CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_comp_heckeDiagMatrix_apply_eq_of_not_dvd
    2 k ε g hg Nat.prime_three (by norm_num) τ

/-- **Zone F, the `z = 0` term.** At `z = 0` the twist is the identity, so the zeroth summand of the
twisted coset sum is `g (heckeDiagMatrix 3 • τ)`: the collapse of the row is a statement about that
summand plus the remaining `range 2` tail. -/
theorem zoneF_zero_term (k : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma1 2) k)
    (τ : UpperHalfPlane) :
    cosetTermF k g 0 τ = g (ModularForm.heckeDiagMatrix 3 • τ) := by
  simp [cosetTermF]

/-- **Zone F, the row with its `z = 0` term split off.** -/
theorem zoneF_split (k : ℤ) (ε : DirichletCharacter ℂ 2)
    (g : CuspForm (CongruenceSubgroup.Gamma1 2) k) (hg : CuspForm.IsPrimitiveForm ε g)
    (τ : UpperHalfPlane) :
    g (ModularForm.heckeDiagMatrix 3 • τ) + ∑ j ∈ Finset.range 2, cosetTermF k g (j + 1) τ
      = (3 : ℂ) ^ (1 - k) * starRingEnd ℂ (ModularFormClass.qCoeff g 3) * g τ
          - starRingEnd ℂ (ε (3 : ZMod 2)) * (3 : ℂ) ^ (-k) *
              g (ModularForm.heckeMatrix 3 0 • τ) := by
  have h := zoneF_not_dvd k ε g hg τ
  rw [Finset.sum_range_succ'] at h
  rw [add_comm] at h
  rw [← zoneF_zero_term k g τ]
  exact h

end SetAF66AConsumer
