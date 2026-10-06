/-
  The `PeriodPair` lattice, scale and discriminant prelude — the single home.

  This module carries the mathematical content that was shipped three times: once
  publicly in `Elliptic/PeriodPair/Discriminant.lean` (the `scale`/`G_scale`/
  lattice-equality API), once publicly at the root namespace in
  `ModularForms/WeightOne/Defs/PeriodPair.lean` (`periodPairOfTau`,
  `smulPeriodPair`, the lattice equivalence and the `℘` homogeneity), and once as
  a `private` block in `ModularForms/WeightOne/FrickeFunction.lean` (the
  `smul`-spelled scale law, `latticeDisc` and the lattice-equality lemmas).  The
  dictionary itself stays in `Basic.lean`; the discriminant-specific development
  (Eisenstein comparison, `discriminant_ne_zero`) stays in `Discriminant.lean`.

  One proof per fact.  The scale law is proved for `L.scale α` (`α : ℂˣ`, the
  pin's `Definitions/Def_PeriodPair_Uniformization.lean` binder shape);
  `smulPeriodPair a ha L` is *defined* as `L.scale (Units.mk0 a ha)`, so every
  `smul`-spelled law follows by unfolding that definition and rewriting with the
  scale law.  The two lattice-equality spellings are likewise one proof:
  `G_eq_of_lattice_eq` (`{L L'}` section variables) is proved once and
  `G_of_lattice_eq` (the pin's `WLight` explicit-binder name) is its one-line
  restatement, and the same for `g₂`/`g₃`.

  Names are the pin's; the port's root-level `WeightOne` names are thin aliases in
  `ModularForms/WeightOne/Defs/PeriodPair.lean`, and `FrickeFunction.lean`'s
  private copies are deleted.  The import direction is `WeightOne → Elliptic`;
  this module imports nothing under `ModularForms/WeightOne/`.

  Pin sources, at `anthropics/fermats-last-theorem@aa2d8b3`:

    `P2M/Sol/S_PeriodPair_discriminant_ne_zero.lean`      `scale_lattice`,
      `scaleLatticeEquiv`, `scaleLatticeEquiv_apply`, `G_scale`, `g₂_scale`,
      `g₃_scale`, `discriminant_scale`, `G_eq_of_lattice_eq`,
      `g₂_eq_of_lattice_eq`, `g₃_eq_of_lattice_eq`;
    `P2M/Sol/S_WLight_frickeFunction_modularity_package.lean`  the `B1_homogeneity`
      block (`smulPeriodPair`, `smulPeriodPair_ω₁/_ω₂`,
      `mem_smulPeriodPair_lattice`, `smulLatticeEquiv`, `smulLatticeEquiv_coe`,
      `weierstrassP_smulPeriodPair`), `periodPairOfTau`/`periodPairOfTau_ω₁/_ω₂`,
      and the `B3_fricke` block (`latticeEquivOfEq`, `latticeEquivOfEq_coe`,
      `weierstrassP_of_lattice_eq`, `G_of_lattice_eq`, `G_smulPeriodPair`,
      `g₂_smulPeriodPair`, `g₃_smulPeriodPair`, `latticeDisc`,
      `latticeDisc_smulPeriodPair`, `g₂_of_lattice_eq`, `g₃_of_lattice_eq`,
      `latticeDisc_of_lattice_eq`);
    `P2M/Sol/S_ModularForm_weierstrassP_torsion_qExpansion_package.lean` and
      `P2M/Sol/S_WLight_levelN_structure_package.lean`  `periodPair_eq_of_ω`.

  `latticeDisc` keeps the pin's inline `g₂ ^ 3 - 27 * g₃ ^ 2` body (the checker
  diff is textual); its equality with the dictionary's `weierstrassCurve_Δ` is
  recorded once, privately, as `latticeDisc_eq_weierstrassCurve_Δ`.

  `weierstrassP_of_lattice_eq` has no `Scale`-spelled counterpart, so it is
  promoted here (public) and `FrickeFunction.lean`'s private copy is deleted.
-/
import FLTForHuman.Elliptic.PeriodPair.Basic

noncomputable section

open scoped PeriodPair UpperHalfPlane

namespace PeriodPair

section Scale

variable (L : PeriodPair)
variable (α : ℂˣ)

private def mulLeftR (a : ℂ) : ℂ →ₗ[ℝ] ℂ := Algebra.lmul ℝ ℂ a

@[scoped simp] private theorem mulLeftR_apply (a z : ℂ) : mulLeftR a z = a * z := rfl

private theorem mulLeftR_injective {a : ℂ} (ha : a ≠ 0) :
    Function.Injective (mulLeftR a) := fun _ _ h => by
  simpa using mul_left_cancel₀ ha h

private def mulLeftZ (a : ℂ) : ℂ →ₗ[ℤ] ℂ := (mulLeftR a).restrictScalars ℤ

@[scoped simp] private theorem mulLeftZ_apply (a z : ℂ) : mulLeftZ a z = a * z := rfl

/-- The lattice of `L.scale α` is the image of `L.lattice` under multiplication by `α`. -/
theorem scale_lattice : (L.scale α).lattice = Submodule.map (mulLeftZ (α : ℂ)) L.lattice := by
  unfold lattice scale
  rw [Submodule.map_span]
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, mulLeftZ_apply]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨L.ω₁, Or.inl rfl, rfl⟩
    · exact ⟨L.ω₂, Or.inr rfl, rfl⟩
  · rintro ⟨w, hw | hw, rfl⟩ <;> simp [hw]

/-- Rescaling identifies the two period lattices, linearly over `ℤ`. -/
noncomputable def scaleLatticeEquiv : L.lattice ≃ₗ[ℤ] (L.scale α).lattice :=
  (Submodule.equivMapOfInjective (mulLeftZ (α : ℂ))
    (fun _ _ h => mul_left_cancel₀ α.ne_zero (by simpa using h)) L.lattice).trans
    (LinearEquiv.ofEq _ _ (scale_lattice L α).symm)

@[scoped simp] private theorem scaleLatticeEquiv_apply (l : L.lattice) :
    ((L.scaleLatticeEquiv α l : (L.scale α).lattice) : ℂ) = (α : ℂ) * (l : ℂ) := rfl

/-- The Eisenstein sums are homogeneous of degree `-n` under rescaling. -/
theorem G_scale (n : ℕ) : (L.scale α).G n = ((α : ℂ) ^ n)⁻¹ * L.G n := by
  unfold G
  rw [← (L.scaleLatticeEquiv α).toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, scaleLatticeEquiv_apply, mul_pow, mul_inv]
  exact tsum_mul_left

theorem g₂_scale : (L.scale α).g₂ = ((α : ℂ) ^ 4)⁻¹ * L.g₂ := by
  unfold g₂; rw [G_scale]; ring

theorem g₃_scale : (L.scale α).g₃ = ((α : ℂ) ^ 6)⁻¹ * L.g₃ := by
  unfold g₃; rw [G_scale]; ring

/-- The discriminant `g₂³ - 27 g₃²` is homogeneous of degree `-12`. -/
theorem discriminant_scale :
    (L.scale α).g₂ ^ 3 - 27 * (L.scale α).g₃ ^ 2
      = ((α : ℂ) ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [g₂_scale, g₃_scale]; ring

end Scale

section Smul

/-- Rescale a period pair by a nonzero complex number.  This is the pin's
`smulPeriodPair` binder shape; it is definitionally `L.scale (Units.mk0 a ha)`. -/
def smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) : PeriodPair :=
  L.scale (Units.mk0 a ha)

@[simp] lemma smulPeriodPair_ω₁ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₁ = a * L.ω₁ := rfl

@[simp] lemma smulPeriodPair_ω₂ (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).ω₂ = a * L.ω₂ := rfl

lemma mem_smulPeriodPair_lattice {a : ℂ} (ha : a ≠ 0) (L : PeriodPair) {x : ℂ} :
    x ∈ (smulPeriodPair a ha L).lattice ↔ ∃ y ∈ L.lattice, x = a * y := by
  simp only [mem_lattice, smulPeriodPair_ω₁, smulPeriodPair_ω₂]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨(m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂, ⟨m, n, rfl⟩, by rw [← h]; ring⟩
  · rintro ⟨y, ⟨m, n, h⟩, rfl⟩
    exact ⟨m, n, by rw [← h]; ring⟩

/-- Rescaling identifies the two period lattices.  Derived from
`scaleLatticeEquiv` (`smulPeriodPair a ha L` is `L.scale (Units.mk0 a ha)`). -/
noncomputable def smulLatticeEquiv (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    L.lattice ≃ (smulPeriodPair a ha L).lattice :=
  (L.scaleLatticeEquiv (Units.mk0 a ha)).toEquiv

@[simp] lemma smulLatticeEquiv_coe (a : ℂ) (ha : a ≠ 0) (L : PeriodPair)
    (l : L.lattice) : ((smulLatticeEquiv a ha L) l : ℂ) = a * l := rfl

/-- `weierstrassP` is homogeneous of degree `-2` under a rescaling of the pair. -/
theorem weierstrassP_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (z : ℂ) :
    weierstrassP (smulPeriodPair a ha L) (a * z) = a⁻¹ ^ 2 * weierstrassP L z := by
  have key : ∀ u : ℂ, 1 / (a * u) ^ 2 = a⁻¹ ^ 2 * (1 / u ^ 2) := fun u => by
    simp [one_div, mul_pow, inv_pow, mul_comm]
  simp only [weierstrassP]
  rw [← (smulLatticeEquiv a ha L).tsum_eq, ← tsum_mul_left]
  congr with l
  simp only [smulLatticeEquiv_coe]
  rw [show a * z - a * (l : ℂ) = a * (z - l) by ring, key, key, mul_sub]

/-- The `smul`-spelled scale law, derived from `G_scale`. -/
theorem G_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) (n : ℕ) :
    (smulPeriodPair a ha L).G n = a⁻¹ ^ n * L.G n := by
  simpa only [smulPeriodPair, Units.val_mk0, inv_pow] using G_scale L (Units.mk0 a ha) n

theorem g₂_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).g₂ = a⁻¹ ^ 4 * L.g₂ := by
  simp only [g₂, G_smulPeriodPair]; ring

theorem g₃_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    (smulPeriodPair a ha L).g₃ = a⁻¹ ^ 6 * L.g₃ := by
  simp only [g₃, G_smulPeriodPair]; ring

/-- `g₂ ^ 3 - 27 * g₃ ^ 2`, the dictionary's `weierstrassCurve.Δ`. -/
def latticeDisc (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

private theorem latticeDisc_eq_weierstrassCurve_Δ (L : PeriodPair) :
    latticeDisc L = L.weierstrassCurve.Δ := by
  rw [latticeDisc, weierstrassCurve_Δ]

/-- The `smul`-spelled `discriminant_scale`, derived from it. -/
theorem latticeDisc_smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) :
    latticeDisc (smulPeriodPair a ha L) = a⁻¹ ^ 12 * latticeDisc L := by
  simpa only [latticeDisc, smulPeriodPair, Units.val_mk0, inv_pow]
    using discriminant_scale L (Units.mk0 a ha)

end Smul

section LatticeDependence

variable {L L' : PeriodPair}

private def latticeEquivOfEq (h : L.lattice = L'.lattice) : L.lattice ≃ L'.lattice where
  toFun l := ⟨(l : ℂ), h ▸ l.2⟩
  invFun l := ⟨(l : ℂ), h.symm ▸ l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem latticeEquivOfEq_coe (h : L.lattice = L'.lattice) (l : L.lattice) :
    ((latticeEquivOfEq h l : L'.lattice) : ℂ) = (l : ℂ) := rfl

/-- Period pairs with the same lattice have the same Eisenstein sums. -/
theorem G_eq_of_lattice_eq (h : L.lattice = L'.lattice) (n : ℕ) : L.G n = L'.G n :=
  (latticeEquivOfEq h).tsum_eq fun l => ((l : ℂ) ^ n)⁻¹

theorem g₂_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.g₂ = L'.g₂ := by
  unfold g₂; rw [G_eq_of_lattice_eq h]

theorem g₃_eq_of_lattice_eq (h : L.lattice = L'.lattice) : L.g₃ = L'.g₃ := by
  unfold g₃; rw [G_eq_of_lattice_eq h]

end LatticeDependence

section LatticeDependenceAliases

/-- `℘` depends only on the lattice. -/
theorem weierstrassP_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) (z : ℂ) :
    weierstrassP L z = weierstrassP L' z := by
  simp only [weierstrassP]
  rw [← (latticeEquivOfEq h).tsum_eq]
  rfl

theorem G_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) (n : ℕ) :
    L.G n = L'.G n :=
  G_eq_of_lattice_eq h n

theorem g₂_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.g₂ = L'.g₂ :=
  g₂_eq_of_lattice_eq h

theorem g₃_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) : L.g₃ = L'.g₃ :=
  g₃_eq_of_lattice_eq h

theorem latticeDisc_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    latticeDisc L = latticeDisc L' := by
  simp [latticeDisc, g₂_of_lattice_eq h, g₃_of_lattice_eq h]

end LatticeDependenceAliases

section OfTau

/-- The standard period pair `(τ, 1)` on the upper half plane. -/
def periodPairOfTau (τ : ℍ) : PeriodPair := ofTau τ

@[simp] lemma periodPairOfTau_ω₁ (τ : ℍ) : (periodPairOfTau τ).ω₁ = (τ : ℂ) := rfl

@[simp] lemma periodPairOfTau_ω₂ (τ : ℍ) : (periodPairOfTau τ).ω₂ = 1 := rfl

end OfTau

/-- Two period pairs with the same `ω₁` and `ω₂` are equal. -/
lemma periodPair_eq_of_ω (P P' : PeriodPair) (h1 : P.ω₁ = P'.ω₁) (h2 : P.ω₂ = P'.ω₂) :
    P = P' := by
  rcases P with ⟨_, _, _⟩; rcases P' with ⟨_, _, _⟩
  simp only [PeriodPair.mk.injEq]; exact ⟨h1, h2⟩

end PeriodPair

end
