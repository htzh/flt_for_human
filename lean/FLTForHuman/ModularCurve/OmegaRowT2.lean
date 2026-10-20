/-
  The `omegaRow_T2` identity: `θ(jq) · Δ = -(E₄² · E₆)` in `q`-expansions.

  With `θ = q d/dq` the normalized derivation on `LaurentSeries`, `Δ` the
  discriminant and `E₄`/`E₆` the level-one Eisenstein series, the
  `q`-expansion identity

      `coeffMap (algebraMap ℚ ℂ) (thetaL ℚ jq) * Δ = -(E₄ ^ 2 * E₆)`

  is the `omegaRow_T2` pin node: the `q`-expansion row of the `T_2`-omega
  differential.  The proof develops, in the pin's `ANb` namespace, the
  subalgebra `𝒩` of `ℍ → ℂ` of periodic, holomorphic, bounded-at-`i∞`
  functions, its `q`-expansion homomorphism `ψ` into `LaurentSeries ℂ`, and then
  differentiates the three identities `J · D = A³`, `A³ - B² = 1728 D` and the
  Rankin–Cohen identity `4 A θB - 6 θA B = -3456 D` that the `ModularForm` leaves
  of this pair provide.

  Two nodes in one module (subject split): the `θ`/`coeffMap` commutation

  * `ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative` (39 pin
    lines) — `θ` commutes with `coeffMap` up to the `single 1 1` factor, the
    `ModularCurve` `θ` fact the omega row consumes;

  and the omega row itself:

  * `omegaRow_T2` (447 pin lines), whose statement is its `Theorems/` wrapper's
    verbatim (the pin files are named after the node).

  Faithfulness and drift.  Statements are the wrappers' verbatim, proofs the `S_`
  files' bodies; the pin's `p2m_export`/`p2m_open`/`p2m_open_scoped`/
  `p2m_reactivate` scaffolding is dropped (it exports definitions the port already
  has: `coeffMap`, `thetaL`, `qCoeff`, …), `solution` is not ported, and the
  pin's inner namespaces are kept verbatim (`ANb`, `ModularCurve`).  The pin's
  `attribute [-instance]`/`attribute [-simp]` blocks on the wrappers are not
  transcribed (they prune the pin's global instance/simp sets, hundreds of hub
  declarations, none of them part of a statement; the port's targeted imports
  reproduce the pin's elaboration without them.  That includes the
  `omegaRow_T2` wrapper's one `attribute [-simp] ModularCurve.jqNModC_one`: the
  proof elaborates without it in the port's targeted environment, and keeping it
  would mutate the global simp set for every importer of this module.  The pin's
  `import Mathlib` becomes the named modules below; the
  `Definitions/` imports are the port's `Defs`/`Period` modules, among them this
  group's `Def_ModularCurve_OmegaOf` home.

  **The one declaration the port lacked.**  The pin's `S_omegaRow_T2.lean` imports
  `Theorems.Thm_ModularCurve_theta_mul`, and its `theta_mul'` step is
  `ModularCurve.theta_mul` (the Leibniz rule for `θ`).  That pin leaf was not
  homed anywhere in the port; it is homed now, in
  `ModularCurve/Period/ThetaMul.lean` (its own module, its own `spec-pin:`
  header, no existing module edited), and imported here — nothing is re-proved in
  this file.

  **Drift (v4.34), this group's modules.**  In this file: (i)
  `local notation "𝒩" => niceSubalgebra` is moved below `def niceSubalgebra` —
  the pin states the notation first and v4.34's `quotPrecheck` rejects the forward
  reference; (ii) two `haveI : …` binders → `have` (`nice_of_modularForm`'s
  `Fact (IsCusp …)` and `rankinCohen_E4_E6`'s `FiniteIndex`), the
  `linter.style.haveILetI` suggestion, sound for `Prop`/subsingleton classes;
  (iii) `ENat.coe_le_coe` → `ENat.natCast_le_natCast`; (iv) two `if_neg` →
  `ite_eq_right`; (v) two `first | …` blocks whose later branches v4.34's tactic
  linter reports as dead are collapsed to the branch that fires (`rfl`,
  respectively `exact this`).  In `Defs/OmegaOf.lean`: `dif_pos`/`dif_neg` →
  `dite_eq_left`/`dite_eq_right`.  In `HeckeCharacter/Equality.lean`:
  `haveI := Fintype.ofFinite ι` → `have`, `zero_le'` → `zero_le`, five
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, and `dif_pos` → `dite_eq_left`
  (`Associates.count`).

  **Deferred gate.**  The pin's `Thm_omegaRow_T2` also imports
  `Definitions/Def_ModularCurve_EigenformIdeal.lean`, the third definition gate of
  this group.  It is **not** homed: its three declarations (`IsEigenformIdeal`,
  `EigenformSupportAt`, `EichlerShimuraDataAt`) are defined in terms of
  `eigenIdeal`, `EigenformSupport` and `EichlerShimuraDataReduced` from
  `Definitions/Def_HeckeGalois_EichlerShimura.lean`, which the port records as
  blocked (see `ModularForms/HeckeFiniteAlgebra.lean` §T10 and
  `CARRY-FORWARD.md`).  The `omegaRow_T2` statement and proof reference none of
  them (the wrapper carries the import only), so the node lands without the gate,
  as the manager directed; the manager records the deferral.

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_omegaRow_T2.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean>

  spec-pin: Theorems/Thm_omegaRow_T2.lean
  spec-pin: P2M/Sol/S_omegaRow_T2.lean
  spec-pin: Theorems/Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean
  spec-pin: P2M/Sol/S_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative.lean
-/

import FLTForHuman.ModularForms.QCoeffLevelOne
import FLTForHuman.ModularCurve.Defs.OmegaOf
import FLTForHuman.ModularCurve.Period.ThetaMul
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularForms.JqAnalyticModel
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularCurve AlgebraicCurve
open scoped MatrixGroups ModularForm Manifold


/-! ### `θ` commutes with `coeffMap` -/

namespace ModularCurve

section

variable {R K : Type*} [CommRing R] [Field K]

private theorem coeffMap_single_one (φ : R →+* K) :
    coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R)) = HahnSeries.single (1 : ℤ) (1 : K) := by
  ext n
  rw [coeffMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single]
  split_ifs <;> simp

private theorem derivative_coeffMap (φ : R →+* K) (w : LaurentSeries R) :
    LaurentSeries.derivative K (coeffMap φ w) = coeffMap φ (LaurentSeries.derivative R w) := by
  ext n
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, coeffMap_coeff,
    coeffMap_coeff, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, map_zsmul]

private theorem thetaL_coeffMap_impl (φ : R →+* K) (w : LaurentSeries R) :
    thetaL K (coeffMap φ w) =
      coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) := by
  rw [thetaL_apply, derivative_coeffMap, map_mul, coeffMap_single_one]

end

theorem thetaL_coeffMap_eq_coeffMap_single_mul_derivative {R : Type*} [CommRing R]
    {K : Type*} [Field K] (φ : R →+* K) (w : LaurentSeries R) :
    thetaL K (coeffMap φ w) =
      coeffMap φ (HahnSeries.single (1 : ℤ) (1 : R) * LaurentSeries.derivative R w) :=
  thetaL_coeffMap_impl φ w

end ModularCurve

/-! ### The omega row -/

namespace ANb

def Nice (f : ℍ → ℂ) : Prop :=
  Function.Periodic (f ∘ ofComplex) 1 ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ IsBoundedAtImInfty f

theorem Nice.mul {f g : ℍ → ℂ} (hf : Nice f) (hg : Nice g) : Nice (f * g) :=
  ⟨by simpa [Function.comp_def] using hf.1.mul hg.1, hf.2.1.mul hg.2.1, hf.2.2.mul hg.2.2⟩

theorem Nice.add {f g : ℍ → ℂ} (hf : Nice f) (hg : Nice g) : Nice (f + g) :=
  ⟨by simpa [Function.comp_def] using hf.1.add hg.1, hf.2.1.add hg.2.1, hf.2.2.add hg.2.2⟩

theorem Nice.const (c : ℂ) : Nice (fun _ => c) :=
  ⟨fun _ => rfl, mdifferentiable_const, Filter.const_boundedAtFilter _ _⟩

def niceSubalgebra : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | Nice f}
  mul_mem' hf hg := hf.mul hg
  add_mem' hf hg := hf.add hg
  algebraMap_mem' c := Nice.const c

local notation "𝒩" => niceSubalgebra

theorem an (f : 𝒩) : AnalyticAt ℂ (cuspFunction 1 (f : ℍ → ℂ)) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero one_pos f.2.1 f.2.2.1 f.2.2.2

def qexpHom : 𝒩 →ₐ[ℂ] PowerSeries ℂ where
  toFun f := qExpansion 1 (f : ℍ → ℂ)
  map_one' := UpperHalfPlane.qExpansion_one 1
  map_mul' f g := UpperHalfPlane.qExpansion_mul (an f) (an g)
  map_zero' := UpperHalfPlane.qExpansion_zero 1
  map_add' f g := UpperHalfPlane.qExpansion_add (an f) (an g)
  commutes' c := by
    have h1 : ((algebraMap ℂ (ℍ → ℂ) c : ℍ → ℂ)) = c • (1 : ℍ → ℂ) := by
      funext z; simp
    have a1 : AnalyticAt ℂ (cuspFunction 1 (1 : ℍ → ℂ)) 0 := an (1 : 𝒩)
    change qExpansion 1 (algebraMap ℂ (ℍ → ℂ) c) = _
    rw [h1, UpperHalfPlane.qExpansion_smul a1 c, UpperHalfPlane.qExpansion_one,
      Algebra.algebraMap_eq_smul_one]

theorem qexpHom_apply (f : 𝒩) : qexpHom f = qExpansion 1 (f : ℍ → ℂ) := rfl

def ψ : 𝒩 →ₐ[ℂ] LaurentSeries ℂ :=
  { (HahnSeries.ofPowerSeries ℤ ℂ).comp qexpHom.toRingHom with
    commutes' := fun c => by
      change HahnSeries.ofPowerSeries ℤ ℂ (qexpHom (algebraMap ℂ 𝒩 c)) = _
      rw [qexpHom.commutes, HahnSeries.algebraMap_apply'] }

theorem ψ_apply (f : 𝒩) : ψ f = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (f : ℍ → ℂ)) := rfl

theorem ψ_injective : Function.Injective ψ := by
  intro f g hfg
  rw [ψ_apply, ψ_apply] at hfg
  have h := HahnSeries.ofPowerSeries_injective hfg
  have h' : qExpansion 1 ((f : ℍ → ℂ) - (g : ℍ → ℂ)) = 0 := by
    rw [UpperHalfPlane.qExpansion_sub (an f) (an g), h, sub_self]
  have hn : Nice ((f : ℍ → ℂ) - (g : ℍ → ℂ)) := (f - g).2
  have h0 := (UpperHalfPlane.qExpansion_eq_zero_iff one_pos hn.1 hn.2.1 hn.2.2).mp h'
  exact Subtype.ext (sub_eq_zero.mp h0)

theorem ψ_eq_zero_iff (f : 𝒩) : ψ f = 0 ↔ f = 0 :=
  ⟨fun h => ψ_injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

def toC : 𝒩 →ₐ[ℂ] (ℂ → ℂ) where
  toFun f := (f : ℍ → ℂ) ∘ ofComplex
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem toC_apply (f : 𝒩) : toC f = (f : ℍ → ℂ) ∘ ofComplex := rfl

theorem analyticAt_toC (f : 𝒩) (τ : ℍ) : AnalyticAt ℂ (toC f) (τ : ℂ) := by
  have hd : DifferentiableOn ℂ ((f : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.2.2.1
  exact hd.analyticAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos)

theorem nice_of_modularForm {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) : Nice (f : ℍ → ℂ) := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  refine ⟨?_, ModularFormClass.holo f, ModularFormClass.bdd_at_infty f⟩
  simpa using SlashInvariantFormClass.periodic_comp_ofComplex (h := 1) f h1

def ofMF {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) : 𝒩 :=
  ⟨f, nice_of_modularForm f h1⟩

@[scoped simp] theorem coe_ofMF {F : Type*} {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (h1 : (1 : ℝ) ∈ Γ.strictPeriods) :
    ((ofMF f h1 : 𝒩) : ℍ → ℂ) = f := rfl

theorem one_mem_strictPeriods_gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 N)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

def 𝔞 : 𝒩 := ofMF ModularForm.E₄ one_mem_strictPeriods_SL

def 𝔟 : 𝒩 := ofMF ModularForm.E₆ one_mem_strictPeriods_SL

def 𝔡 : 𝒩 := ofMF CuspForm.discriminant one_mem_strictPeriods_SL

theorem ψ𝔞 : ψ 𝔞 = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) := rfl
theorem ψ𝔟 : ψ 𝔟 = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (ModularForm.E₆ : ℍ → ℂ)) := rfl
theorem ψ𝔡 : ψ 𝔡 = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ModularForm.discriminant) := rfl
theorem toC𝔡_apply (τ : ℍ) : toC 𝔡 (τ : ℂ) = ModularForm.discriminant τ := by
  change ModularForm.discriminant (ofComplex (τ : ℂ)) = _
  rw [ofComplex_apply]

theorem coeff_one_mul (φ χ : PowerSeries ℂ) :
    PowerSeries.coeff 1 (φ * χ) = PowerSeries.coeff 0 φ * PowerSeries.coeff 1 χ +
      PowerSeries.coeff 1 φ * PowerSeries.coeff 0 χ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_zero_mul' (φ χ : PowerSeries ℂ) :
    PowerSeries.coeff 0 (φ * χ) = PowerSeries.coeff 0 φ * PowerSeries.coeff 0 χ := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]

theorem qA0 : PowerSeries.coeff 0 (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩
theorem qB0 : PowerSeries.coeff 0 (qExpansion 1 (ModularForm.E₆ : ℍ → ℂ)) = 1 :=
  EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨3, rfl⟩
theorem qA1 : PowerSeries.coeff 1 (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) = 240 := by
  have h := ModularForm.levelOne_weight_four_qCoeff_one ModularForm.E₄
  simp only [ModularFormClass.qCoeff] at h
  rw [h, qA0, mul_one]
theorem qB1 : PowerSeries.coeff 1 (qExpansion 1 (ModularForm.E₆ : ℍ → ℂ)) = -504 := by
  have h := ModularForm.levelOne_weight_six_qCoeff_one ModularForm.E₆
  simp only [ModularFormClass.qCoeff] at h
  rw [h, qB0, mul_one]
theorem qD1 : PowerSeries.coeff 1 (qExpansion 1 ModularForm.discriminant) = 1 := by
  rw [ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, PowerSeries.coeff_map,
    PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ModularCurve.constantCoeff_dedekindEtaUnit, map_one]

theorem A_cube_sub_B_sq : ψ 𝔞 ^ 3 - ψ 𝔟 ^ 2 = 1728 * ψ 𝔡 := by
  let T : ModularForm 𝒮ℒ 12 := ModularForm.E₄.mul (ModularForm.E₄.mul ModularForm.E₄)
  let U : ModularForm 𝒮ℒ 12 := ModularForm.E₆.mul ModularForm.E₆
  let Z : ModularForm 𝒮ℒ 12 := T - U
  have hZ : (Z : ℍ → ℂ) = ((𝔞 * (𝔞 * 𝔞) - 𝔟 * 𝔟 : 𝒩) : ℍ → ℂ) := by
    funext z
    show (T : ℍ → ℂ) z - (U : ℍ → ℂ) z = _
    rfl
  have hZq : qExpansion 1 (Z : ℍ → ℂ) =
      qExpansion 1 ⇑ModularForm.E₄ * (qExpansion 1 ⇑ModularForm.E₄ * qExpansion 1 ⇑ModularForm.E₄) -
        qExpansion 1 ⇑ModularForm.E₆ * qExpansion 1 ⇑ModularForm.E₆ := by
    rw [hZ, ← qexpHom_apply, map_sub, map_mul, map_mul, map_mul]
    rfl
  have h0 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 0 = 0 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_zero_mul', qA0, qB0]
    norm_num
  have h1 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 1 = 1728 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_one_mul, coeff_zero_mul', qA0, qA1, qB0, qB1]
    norm_num
  have hW := ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant Z h0
  have hZΔ : qExpansion 1 (Z : ℍ → ℂ) = PowerSeries.C 1728 * qExpansion 1 ModularForm.discriminant := by
    ext n
    rw [PowerSeries.coeff_C_mul]
    have := hW n
    have h1' := h1
    simp only [ModularFormClass.qCoeff] at this h1'
    rw [this, h1']
  have hL : ψ (𝔞 * (𝔞 * 𝔞) - 𝔟 * 𝔟) = 1728 * ψ 𝔡 := by
    rw [ψ_apply, ← hZ, hZΔ, map_mul, HahnSeries.ofPowerSeries_C, map_ofNat, ψ𝔡]
  rw [map_sub, map_mul, map_mul, map_mul] at hL
  rw [← hL]
  ring

theorem ψ𝔡_ne_zero : ψ 𝔡 ≠ 0 := by
  intro h
  have h0 : (𝔡 : 𝒩) = 0 := (ψ_eq_zero_iff _).mp h
  have : ModularForm.discriminant UpperHalfPlane.I = 0 := by
    have := congrArg (fun f : 𝒩 => (f : ℍ → ℂ) UpperHalfPlane.I) h0
    exact this
  exact ModularForm.discriminant_ne_zero _ this

theorem coeffEmb_jq : coeffEmb ℂ jq = jqModC ℂ := by
  change (jqModC ℚ).map (algebraMap ℚ ℂ) = jqModC ℂ
  exact map_jqModC _

theorem J_mul_D : coeffEmb ℂ jq * ψ 𝔡 = ψ 𝔞 ^ 3 := by
  rw [coeffEmb_jq, ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, ← ψ𝔞, ← ψ𝔡,
    div_mul_cancel₀ _ ψ𝔡_ne_zero]

theorem J_sub_mul_D : (coeffEmb ℂ jq - algebraMap ℂ (LaurentSeries ℂ) 1728) * ψ 𝔡 = ψ 𝔟 ^ 2 := by
  rw [map_ofNat, sub_mul, J_mul_D]
  have := A_cube_sub_B_sq
  linear_combination this

theorem le_analyticOrderAt_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z : ℂ) (b : ℕ∞)
    (h : ∀ i ∈ s, b ≤ analyticOrderAt (F i) z) : b ≤ analyticOrderAt (∑ i ∈ s, F i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, analyticOrderAt_eq_top.mpr (by simp)]
    exact le_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans ?_ le_analyticOrderAt_add
    exact le_min (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem order_le_of_identity {p q d : ℂ → ℂ} {n m : ℕ} {C : ℕ → ℂ → ℂ} {z : ℂ}
    (hp : AnalyticAt ℂ p z) (hq : AnalyticAt ℂ q z) (hd : AnalyticAt ℂ d z)
    (hC : ∀ i ∈ Finset.range n, AnalyticAt ℂ (C i) z) (hd0 : d z ≠ 0)
    (hid : p ^ (6 * n) * d ^ m + ∑ i ∈ Finset.range n, C i * (p ^ (6 * i) * (q ^ 6 * d) ^ (n - i)) = 0) :
    analyticOrderAt q z ≤ analyticOrderAt p z := by
  by_contra hlt'
  have hlt := not_le.mp hlt'
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℕ∞) = analyticOrderAt p z :=
    ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hd_ord : analyticOrderAt d z = 0 := hd.analyticOrderAt_eq_zero.mpr hd0

  have hL : analyticOrderAt (p ^ (6 * n) * d ^ m) z = ((6 * n * k : ℕ) : ℕ∞) := by
    rw [analyticOrderAt_mul (hp.pow _) (hd.pow _), analyticOrderAt_pow hp, analyticOrderAt_pow hd,
      ← hk, hd_ord]
    simp only [nsmul_eq_mul, smul_zero, add_zero]
    push_cast
    ring

  have hq_ord : ((k + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt q z := by
    rw [← hk] at hlt
    have := Order.add_one_le_of_lt hlt
    exact_mod_cast this

  have hR : ∀ i ∈ Finset.range n, ((6 * n * k + 6 : ℕ) : ℕ∞) ≤
      analyticOrderAt (C i * (p ^ (6 * i) * (q ^ 6 * d) ^ (n - i))) z := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    have hqd : AnalyticAt ℂ (q ^ 6 * d) z := (hq.pow _).mul hd
    rw [analyticOrderAt_mul (hC i hi) ((hp.pow _).mul (hqd.pow _)),
      analyticOrderAt_mul (hp.pow _) (hqd.pow _), analyticOrderAt_pow hp, analyticOrderAt_pow hqd,
      analyticOrderAt_mul (hq.pow _) hd, analyticOrderAt_pow hq, hd_ord, ← hk, add_zero]
    have h1 : ((6 * (n - i) * (k + 1) : ℕ) : ℕ∞) ≤ (n - i) • (6 • analyticOrderAt q z) := by
      have : (n - i) • (6 • (((k + 1 : ℕ)) : ℕ∞)) ≤ (n - i) • (6 • analyticOrderAt q z) :=
        nsmul_le_nsmul_right (nsmul_le_nsmul_right hq_ord 6) (n - i)
      refine le_trans (le_of_eq ?_) this
      simp only [nsmul_eq_mul]
      push_cast
      ring
    have h2 : ((6 * n * k + 6 : ℕ) : ℕ∞) ≤ ((6 * i) • (k : ℕ∞)) + ((6 * (n - i) * (k + 1) : ℕ) : ℕ∞) := by
      have e : ((6 * i) • (k : ℕ∞)) + ((6 * (n - i) * (k + 1) : ℕ) : ℕ∞) =
          ((6 * i * k + 6 * (n - i) * (k + 1) : ℕ) : ℕ∞) := by
        simp only [nsmul_eq_mul]
        push_cast
        ring
      rw [e]
      exact_mod_cast (show 6 * n * k + 6 ≤ 6 * i * k + 6 * (n - i) * (k + 1) by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hin
        rw [show i + j + 1 - i = j + 1 by omega]
        nlinarith)
    calc ((6 * n * k + 6 : ℕ) : ℕ∞)
        ≤ (6 * i) • (k : ℕ∞) + ((6 * (n - i) * (k + 1) : ℕ) : ℕ∞) := h2
      _ ≤ (6 * i) • (k : ℕ∞) + (n - i) • (6 • analyticOrderAt q z) := add_le_add le_rfl h1
      _ ≤ analyticOrderAt (C i) z + ((6 * i) • (k : ℕ∞) + (n - i) • (6 • analyticOrderAt q z)) :=
          self_le_add_left _ _
  have hsum := le_analyticOrderAt_sum (Finset.range n) _ z _ hR
  have heq : p ^ (6 * n) * d ^ m = -(∑ i ∈ Finset.range n, C i * (p ^ (6 * i) * (q ^ 6 * d) ^ (n - i))) :=
    eq_neg_of_add_eq_zero_left hid
  have : ((6 * n * k + 6 : ℕ) : ℕ∞) ≤ ((6 * n * k : ℕ) : ℕ∞) := by
    rw [← hL, heq, analyticOrderAt_neg]
    exact hsum
  have := ENat.natCast_le_natCast.mp this
  omega

end ANb

namespace ANb

local notation "𝒩" => niceSubalgebra
local notation "𝐉" => ModularCurve.coeffEmb ℂ ModularCurve.jq
local notation "θ" => ModularCurve.thetaL ℂ

theorem theta_mul' (x y : LaurentSeries ℂ) : θ (x * y) = x * θ y + y * θ x := by
  rw [ModularCurve.thetaL_apply, ModularCurve.thetaL_apply, ModularCurve.thetaL_apply]
  exact ModularCurve.theta_mul x y

theorem theta_one : θ (1 : LaurentSeries ℂ) = 0 := by
  have e := theta_mul' 1 1
  rw [mul_one, one_mul] at e
  have e' : θ 1 + θ 1 = θ 1 + 0 := by rw [add_zero]; exact e.symm
  exact add_left_cancel e'

theorem theta_natCast (n : ℕ) : θ (n : LaurentSeries ℂ) = 0 := by
  rw [← nsmul_one, map_nsmul, theta_one, nsmul_zero]

theorem theta_1728 : θ (1728 : LaurentSeries ℂ) = 0 := by
  rw [show (1728 : LaurentSeries ℂ) = ((1728 : ℕ) : LaurentSeries ℂ) from (Nat.cast_ofNat).symm]
  exact theta_natCast 1728

theorem ofPowerSeries_mk_mul (p : PowerSeries ℂ) :
    HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk fun n => (n : ℂ) * PowerSeries.coeff n p) =
      θ (HahnSeries.ofPowerSeries ℤ ℂ p) := by
  ext k
  rw [ModularCurve.thetaL_apply, ModularCurve.theta_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk,
      zsmul_eq_mul, Int.cast_natCast]
  · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ hk, ModularCurve.ofPowerSeries_coeff_of_neg _ hk, smul_zero]

theorem Gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  refine (Subgroup.eq_top_iff' _).mpr fun γ => ?_
  rw [CongruenceSubgroup.Gamma0_mem]
  exact Subsingleton.elim _ _

theorem rankinCohen_E4_E6 :
    4 * ψ 𝔞 * θ (ψ 𝔟) - 6 * θ (ψ 𝔞) * ψ 𝔟 = -3456 * ψ 𝔡 := by
  have : (CongruenceSubgroup.Gamma0 1).FiniteIndex := by rw [Gamma0_one_eq_top]; infer_instance
  obtain ⟨g4, hg4⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne 1 ModularForm.E₄
  obtain ⟨g6, hg6⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne 1 ModularForm.E₆
  obtain ⟨RC, -, hRCq⟩ := ModularForm.exists_rankinCohen_one_qExpansion_eq
    (Γ := CongruenceSubgroup.Gamma0 1) (one_mem_strictPeriods_gamma0 1) g4 g6
  rw [hg4, hg6] at hRCq

  have hΓ : (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)) =
      Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma0 1) := by
    rw [Gamma0_one_eq_top, ← MonoidHom.range_eq_map]
  let Z : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by norm_num) RC hΓ
  have hZcoe : (Z : ℍ → ℂ) = (RC : ℍ → ℂ) := rfl
  have hZq : qExpansion 1 (Z : ℍ → ℂ) =
      PowerSeries.C (4 : ℂ) * qExpansion 1 ⇑ModularForm.E₄ *
          PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 ⇑ModularForm.E₆).coeff n)
        - PowerSeries.C (6 : ℂ) *
          PowerSeries.mk (fun n : ℕ => (n : ℂ) * (qExpansion 1 ⇑ModularForm.E₄).coeff n) *
            qExpansion 1 ⇑ModularForm.E₆ := by
    rw [hZcoe]; exact_mod_cast hRCq
  have hmk0 : ∀ p : PowerSeries ℂ, PowerSeries.coeff 0 (PowerSeries.mk fun n : ℕ => (n : ℂ) * PowerSeries.coeff n p) = 0 := by
    intro p; rw [PowerSeries.coeff_mk]; simp
  have hmk1 : ∀ p : PowerSeries ℂ, PowerSeries.coeff 1 (PowerSeries.mk fun n : ℕ => (n : ℂ) * PowerSeries.coeff n p) =
      PowerSeries.coeff 1 p := by
    intro p; rw [PowerSeries.coeff_mk]; simp
  have h0 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 0 = 0 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_zero_mul', hmk0, PowerSeries.coeff_zero_C]
    ring
  have h1 : ModularFormClass.qCoeff (Z : ℍ → ℂ) 1 = -3456 := by
    simp only [ModularFormClass.qCoeff, hZq, map_sub, coeff_one_mul, coeff_zero_mul', hmk0, hmk1,
      PowerSeries.coeff_zero_C, qA0, qA1, qB0, qB1]
    have hC4 : PowerSeries.coeff 1 (PowerSeries.C (4 : ℂ)) = 0 := by
      rw [PowerSeries.coeff_C, ite_eq_right one_ne_zero]
    have hC6 : PowerSeries.coeff 1 (PowerSeries.C (6 : ℂ)) = 0 := by
      rw [PowerSeries.coeff_C, ite_eq_right one_ne_zero]
    rw [hC4, hC6]
    norm_num
  have hW := ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant Z h0
  have hZΔ : qExpansion 1 (Z : ℍ → ℂ) = PowerSeries.C (-3456) * qExpansion 1 ModularForm.discriminant := by
    ext n
    rw [PowerSeries.coeff_C_mul]
    have := hW n
    have h1' := h1
    simp only [ModularFormClass.qCoeff] at this h1'
    rw [this, h1']

  have hL := congrArg (HahnSeries.ofPowerSeries ℤ ℂ) hZΔ
  rw [hZq] at hL
  simp only [map_sub, map_mul, HahnSeries.ofPowerSeries_C, ofPowerSeries_mk_mul] at hL
  rw [← ψ𝔞, ← ψ𝔟, ← ψ𝔡] at hL
  have e4 : (HahnSeries.C (4 : ℂ) : LaurentSeries ℂ) = 4 := map_ofNat _ 4
  have e6 : (HahnSeries.C (6 : ℂ) : LaurentSeries ℂ) = 6 := map_ofNat _ 6
  have e3456 : (HahnSeries.C (-3456 : ℂ) : LaurentSeries ℂ) = -3456 := by
    rw [map_neg, map_ofNat]
  rw [e4, e6, e3456] at hL
  linear_combination hL

theorem thetaL_coeffEmb_jq :
    θ (𝐉) = coeffMap (algebraMap ℚ ℂ) (ModularCurve.thetaL ℚ jq) := by
  rw [coeffEmb, ModularCurve.thetaL_coeffMap_eq_coeffMap_single_mul_derivative]
  rfl

theorem thetaJ_mul_D : θ (𝐉) * ψ 𝔡 = -(ψ 𝔞 ^ 2 * ψ 𝔟) := by
  have H3 : 𝐉 * ψ 𝔡 = ψ 𝔞 * ψ 𝔞 * ψ 𝔞 := by rw [J_mul_D]; ring
  have H2' : ψ 𝔞 * ψ 𝔞 * ψ 𝔞 - ψ 𝔟 * ψ 𝔟 = 1728 * ψ 𝔡 := by
    rw [← A_cube_sub_B_sq]; ring
  have H1 := rankinCohen_E4_E6

  have H5 : ψ 𝔡 * θ (𝐉) + 𝐉 * θ (ψ 𝔡) = 3 * (ψ 𝔞) ^ 2 * θ (ψ 𝔞) := by
    have e := congrArg (ModularCurve.thetaL ℂ) H3
    simp only [theta_mul'] at e
    linear_combination e
  have H6 : 3 * (ψ 𝔞) ^ 2 * θ (ψ 𝔞) - 2 * ψ 𝔟 * θ (ψ 𝔟) = 1728 * θ (ψ 𝔡) := by
    have e := congrArg (ModularCurve.thetaL ℂ) H2'
    simp only [map_sub, theta_mul', theta_1728] at e
    linear_combination e
  have hD := ψ𝔡_ne_zero
  have h1728 : (1728 : LaurentSeries ℂ) ≠ 0 := by
    rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) 1728]
    exact HahnSeries.C_ne_zero (by norm_num)
  have h2 : (2 : LaurentSeries ℂ) ≠ 0 := by
    rw [← map_ofNat (HahnSeries.C (Γ := ℤ) (R := ℂ)) 2]
    exact HahnSeries.C_ne_zero (by norm_num)

  have key : (2 * 1728 * ψ 𝔡) * (ψ 𝔡 * θ (𝐉) + ψ 𝔞 ^ 2 * ψ 𝔟) = 0 := by
    linear_combination (2 * 1728 * ψ 𝔡) * H5 - (2 * 1728 * θ (ψ 𝔡)) * H3
      + (2 * (ψ 𝔞 * ψ 𝔞 * ψ 𝔞)) * H6 - (6 * ψ 𝔞 ^ 2 * θ (ψ 𝔞)) * H2' + (ψ 𝔞 ^ 2 * ψ 𝔟) * H1
  have : ψ 𝔡 * θ (𝐉) + ψ 𝔞 ^ 2 * ψ 𝔟 = 0 :=
    (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero h2 h1728) hD)
  linear_combination this

end ANb

open ANb in
theorem omegaRow_T2 :
    coeffMap (algebraMap ℚ ℂ) (thetaL ℚ jq) *
        ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
      = -(((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 2 *
          ((qExpansion 1 (ModularForm.E₆ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) := by
  rw [← ANb.thetaL_coeffEmb_jq]
  exact ANb.thetaJ_mul_D

end
