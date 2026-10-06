/-
  The discriminant of `L.weierstrassCurve` is nonzero.

  Route (the pin's).  Write `E₄³ - E₆²` as a weight-12 cusp form: it is a multiple
  of the modular discriminant `Δ`, whose non-vanishing gives `E₄ τ ^ 3 ≠ E₆ τ ^ 2`.
  The port already proves the identity `Δ = (1/1728) • eCubeSubESq`
  (`FLTForHuman/ModularForms/DiscPow.lean`), so the whole pin modular-forms block
  (`kw_E4cube`, `kw_E6sq`, the `q`-expansion coefficient lemmas and
  `kw_exists_smul_discriminant_eq_E4cube_sub_E6sq`) is not re-proved.  Then compute
  `g₂`/`g₃` of `ofTau τ` from the Eisenstein comparison `G_ofTau_eq`, giving
  `discriminantNeZero_ofTau`; and finally rescale an arbitrary pair to `(τ, 1)` or
  `(-τ, 1)` using the homogeneity `g₂_scale`/`g₃_scale`.

  This module is the discriminant-specific tail: the shared lattice/scale prelude
  (`scale_lattice`, `scaleLatticeEquiv`, `G_scale`, `g₂_scale`, `g₃_scale`,
  `discriminant_scale`, the lattice-equality lemmas) lives once in
  `FLTForHuman/Elliptic/PeriodPair/Lattice.lean` and is imported here.

  Statements are the pin's, verbatim.  Helpers another theory could need are
  **promoted public at the prefix-stripped pin name** (work order §4); a stripped-name
  promotion (`kw_…` → `…`) is verified through the checker's `§2.1` fallback.  Pin
  names (`anthropics/fermats-last-theorem@aa2d8b3`,
  `P2M/Sol/S_PeriodPair_discriminant_ne_zero.lean`):

    pin `kw_G_ofTau_eq`                → `G_ofTau_eq`             (public, stripped)
    pin `kw_riemannZeta_six`           → `riemannZeta_six`        (public, stripped)
    pin `kw_g₂_ofTau` / `kw_g₃_ofTau`  → `g₂_ofTau` / `g₃_ofTau`  (public, stripped)
    pin `kw_ofTau_latticeEquivProd_symm_apply` → `ofTau_latticeEquivProd_symm_apply`
    pin `discriminantNeZero_scale_iff`                            (`private`, stays here)
    pin `kw_discriminant_ofTau_eq`     → `ofTau_discriminant_eq`  (`private`)
    pin `kw_discriminantNeZero_ofTau`  → `ofTau_discriminantNeZero` (`private`)
    pin `kw_discriminantNeZero_of_lattice_eq` → `discriminantNeZero_of_lattice_eq`
                                                                  (`private`)
    pin `kw_im_div_ne_zero`            → `im_div_ne_zero`         (`private`)
    pin `kw_span_neg_fst`              → `span_neg_fst`           (`private`)
    pin `kw_discriminantNeZero`        → `discriminantNeZero`     (`private`)
    pin `kw_E4cube`/`kw_E6sq`/`kw_E4cube_sub_E6sq`/`kw_qExpansion_*`/
        `kw_E4cube_ne_E6sq`/`kw_exists_smul_discriminant_eq_E4cube_sub_E6sq`
                                                 → dropped; the port's
                                                   `UpperHalfPlaneAux.discriminant_eq_smul_eCubeSubESq`
                                                   and `ModularForm.discriminant_ne_zero` replace them
    pin `solution`                             → `PeriodPair.discriminant_ne_zero`

  The headline's statement is taken verbatim from the wrapper
  `Theorems/Thm_PeriodPair_discriminant_ne_zero.lean`
  (https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_PeriodPair_discriminant_ne_zero.lean),
  not from the `S_` file's `solution` binder spelling.

  Assumes `FLTForHuman.Elliptic.PeriodPair.Lattice` (the dictionary plus the
  shared scale/lattice prelude) and the ported modular-forms discriminant identity.
-/
import FLTForHuman.Elliptic.PeriodPair.Lattice
import FLTForHuman.ModularForms.DiscPow
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

noncomputable section

open scoped PeriodPair UpperHalfPlane Real
open ModularForm

namespace PeriodPair

variable (L : PeriodPair)

section OfTau

open Complex UpperHalfPlane

private theorem ofTau_latticeEquivProd_symm_apply (τ : ℍ) (p : ℤ × ℤ) :
    ((ofTau τ).latticeEquivProd.symm p : ℂ) = p.1 * (τ : ℂ) + p.2 := by
  rw [latticeEquiv_symm_apply]; simp

theorem G_ofTau_eq {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    (ofTau τ).G k = 2 * riemannZeta k * E hk τ := by

  rw [G, ← (ofTau τ).latticeEquivProd.symm.toEquiv.tsum_eq]

  simp only [LinearEquiv.coe_toEquiv, ofTau_latticeEquivProd_symm_apply]

  have hstep : ∀ p : ℤ × ℤ,
      ((↑p.1 * (τ : ℂ) + ↑p.2) ^ k)⁻¹ = EisensteinSeries.eisSummand k
        ((finTwoArrowEquiv ℤ).symm p) τ := by
    intro p
    simp only [EisensteinSeries.eisSummand, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, _root_.zpow_neg, zpow_natCast]
  simp only [hstep]
  rw [(finTwoArrowEquiv ℤ).symm.tsum_eq (f := fun v => EisensteinSeries.eisSummand (k : ℤ) v τ),
    tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ]

  have hE : (ModularForm.E hk : ℍ → ℂ) τ =
      (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [hE]; ring

theorem riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by

  have hb5 : bernoulli' 5 = 0 := by
    have : Nat.choose 5 2 = 10 := by decide
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, this]
  have hb6 : bernoulli' 6 = 1 / 42 := by
    have h62 : Nat.choose 6 2 = 15 := by decide
    have h64 : Nat.choose 6 4 = 15 := by decide
    rw [bernoulli'_def]
    norm_num [Finset.sum_range_succ, hb5, h62, h64]
  have hb : bernoulli 6 = 1 / 42 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), hb6]

  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  simp only [show 2 * 3 = 6 from rfl, Nat.cast_ofNat, hb,
    show (6 : ℕ).factorial = 720 from by decide] at h
  rw [show (2 * (3 : ℂ) : ℂ) = (6 : ℂ) by ring] at h
  push_cast at h
  rw [h]; ring

theorem g₂_ofTau (τ : ℍ) :
    (ofTau τ).g₂ = (4 * (π : ℂ) ^ 4 / 3) * E₄ τ := by
  rw [g₂, G_ofTau_eq (by norm_num : (3:ℕ) ≤ 4) τ,
    show ((4 : ℕ) : ℂ) = (4 : ℂ) by push_cast; ring, riemannZeta_four]
  ring

theorem g₃_ofTau (τ : ℍ) :
    (ofTau τ).g₃ = (8 * (π : ℂ) ^ 6 / 27) * E₆ τ := by
  rw [g₃, G_ofTau_eq (by norm_num : (3:ℕ) ≤ 6) τ,
    show ((6 : ℕ) : ℂ) = (6 : ℂ) by push_cast; ring, riemannZeta_six]
  ring

end OfTau

section ModularFormsDedup

open UpperHalfPlane

/-- `eCubeSubESq` is `E₄³ - E₆²` pointwise: the port's public spelling of the pin's
`kw_E4cube_sub_E6sq`. -/
private theorem eCubeSubESq_apply (τ : ℍ) :
    UpperHalfPlaneAux.eCubeSubESq τ = ModularForm.E₄ τ ^ 3 - ModularForm.E₆ τ ^ 2 := by
  simp only [UpperHalfPlaneAux.eCubeSubESq, FunLike.coe_sub, Pi.sub_apply,
    ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply]

/-- `E₄ τ ^ 3 ≠ E₆ τ ^ 2`, from `Δ = (1/1728) • eCubeSubESq` and `Δ τ ≠ 0`.
This replaces the pin's `kw_E4cube_ne_E6sq` and its whole `q`-expansion block. -/
private theorem E4cube_ne_E6sq (τ : ℍ) : ModularForm.E₄ τ ^ 3 ≠ ModularForm.E₆ τ ^ 2 := by
  intro h
  have h0 : UpperHalfPlaneAux.eCubeSubESq τ = 0 := by rw [eCubeSubESq_apply, h, sub_self]
  have hdisc : ModularForm.discriminant τ = 0 := by
    have hfun := congrFun UpperHalfPlaneAux.discriminant_eq_smul_eCubeSubESq τ
    simpa [Pi.smul_apply, smul_eq_mul, h0] using hfun
  exact ModularForm.discriminant_ne_zero τ hdisc

end ModularFormsDedup

section Homogeneity

variable (α : ℂˣ)

private theorem discriminantNeZero_scale_iff :
    (L.scale α).DiscriminantNeZero ↔ L.DiscriminantNeZero := by
  unfold DiscriminantNeZero
  rw [discriminant_scale]
  simp only [mul_ne_zero_iff, and_iff_right (inv_ne_zero (pow_ne_zero 12 α.ne_zero))]

end Homogeneity

section Headline

open UpperHalfPlane

private theorem ofTau_discriminant_eq (τ : ℍ) :
    (ofTau τ).g₂ ^ 3 - 27 * (ofTau τ).g₃ ^ 2
      = (64 * (π : ℂ) ^ 12 / 27) * (ModularForm.E₄ τ ^ 3 - ModularForm.E₆ τ ^ 2) := by
  rw [g₂_ofTau, g₃_ofTau]; ring

private theorem ofTau_discriminantNeZero (τ : ℍ) : (ofTau τ).DiscriminantNeZero := by
  unfold DiscriminantNeZero
  rw [ofTau_discriminant_eq]
  refine mul_ne_zero ?_ (sub_ne_zero.mpr (E4cube_ne_E6sq τ))
  refine div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 12 ?_)) (by norm_num)
  exact_mod_cast Real.pi_ne_zero

private theorem discriminantNeZero_of_lattice_eq {L L' : PeriodPair}
    (h : L.lattice = L'.lattice) : L.DiscriminantNeZero ↔ L'.DiscriminantNeZero := by
  unfold DiscriminantNeZero
  rw [g₂_eq_of_lattice_eq h, g₃_eq_of_lattice_eq h]

private theorem im_div_ne_zero (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  have hω₂ : L.ω₂ ≠ 0 := by
    have := L.indep.ne_zero 1; simpa using this
  intro him

  have hdiv : (L.ω₁ / L.ω₂ : ℂ) = ((L.ω₁ / L.ω₂).re : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  have hreal : L.ω₁ = ((L.ω₁ / L.ω₂).re : ℂ) * L.ω₂ := by
    rw [← hdiv, div_mul_cancel₀ _ hω₂]
  have key : (1 : ℝ) • L.ω₁ + (-(L.ω₁ / L.ω₂).re) • L.ω₂ = 0 := by
    rw [one_smul, _root_.neg_smul, Complex.real_smul, ← hreal, add_neg_cancel]
  exact one_ne_zero (LinearIndependent.pair_iff.mp L.indep 1 (-(L.ω₁ / L.ω₂).re) key).1

private theorem span_neg_fst (a b : ℂ) :
    Submodule.span ℤ ({-a, b} : Set ℂ) = Submodule.span ℤ ({a, b} : Set ℂ) := by
  have hna : (-a : ℂ) ∈ Submodule.span ℤ ({a, b} : Set ℂ) :=
    neg_mem (Submodule.subset_span (Set.mem_insert _ _))
  have ha : (a : ℂ) ∈ Submodule.span ℤ ({-a, b} : Set ℂ) := by
    have hneg : (-(-a) : ℂ) ∈ Submodule.span ℤ ({-a, b} : Set ℂ) :=
      neg_mem (Submodule.subset_span (Set.mem_insert _ _))
    simpa using hneg
  apply le_antisymm <;> rw [Submodule.span_le, Set.insert_subset_iff] <;>
    exact ⟨by assumption,
      Set.singleton_subset_iff.mpr (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))⟩

private theorem discriminantNeZero (L : PeriodPair) : L.DiscriminantNeZero := by
  have hω₂ : L.ω₂ ≠ 0 := by have := L.indep.ne_zero 1; simpa using this
  set α : ℂˣ := (Units.mk0 L.ω₂ hω₂)⁻¹
  have hα : (α : ℂ) = (L.ω₂)⁻¹ := by
    simp only [α, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hω : (α : ℂ) * L.ω₁ = L.ω₁ / L.ω₂ ∧ (α : ℂ) * L.ω₂ = 1 := by
    refine ⟨?_, ?_⟩ <;> rw [hα] <;> field_simp

  have hlat : (L.scale α).lattice = Submodule.span ℤ {L.ω₁ / L.ω₂, 1} := by
    simp only [lattice, scale_ω₁, scale_ω₂, hω.1, hω.2]

  rcases lt_or_gt_of_ne (im_div_ne_zero L) with hneg | hpos
  ·
    set τ : ℍ := ⟨-(L.ω₁ / L.ω₂), by simp only [Complex.neg_im]; linarith⟩
    have heq : (L.scale α).lattice = (ofTau τ).lattice := by
      rw [hlat, ofTau_lattice]; exact (span_neg_fst _ _).symm
    exact (discriminantNeZero_scale_iff L α).mp
      ((discriminantNeZero_of_lattice_eq heq).mpr (ofTau_discriminantNeZero τ))
  ·
    set τ : ℍ := ⟨L.ω₁ / L.ω₂, hpos⟩
    have heq : (L.scale α).lattice = (ofTau τ).lattice := by rw [hlat, ofTau_lattice]
    exact (discriminantNeZero_scale_iff L α).mp
      ((discriminantNeZero_of_lattice_eq heq).mpr (ofTau_discriminantNeZero τ))

/-- The discriminant of `L.weierstrassCurve` is nonzero.  Statement verbatim from
`Theorems/Thm_PeriodPair_discriminant_ne_zero.lean`. -/
theorem discriminant_ne_zero (L : PeriodPair) : L.DiscriminantNeZero :=
  discriminantNeZero L

end Headline

end PeriodPair

end
