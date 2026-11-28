/-
Summability of the Whittaker coefficients of a Bruhat–Eisenstein series.

For `Re s > 1`, a unitary pair `μ, ν`, an induced section `φ` of `InducedSection` that is
archimedean-`K`-finite, `Kf`-smooth and continuous, and a global additive character `ψ`, the Whittaker
coefficients of the Bruhat–Eisenstein series
`E g = φ g + ∑' ξ, φ (w * u(ξ) * g)` are summable along `F`.

The proof is the pin's unfolding engine — `bruhatSeries`, `jacquetIntegrand`, the coefficient identity
`whittakerCoefficient_bruhatSeries_eq`, and the lattice bound `latticeBound_bruhatSeries` — closed by
SET-AF111A's polynomial decay of the Weyl-unipotent integral (`PolyDecay.lean`) and the level splitting
`exists_level_smul_integral_subset` (`NumberTheory/AdelicFourier/Faithful.lean`).

Assumes, from earlier modules: `InducedSection`, `EtaFamily`, `WeylIntertwining`, `ArchKFinite`,
`WhittakerCoefficient`, `ProductionPins`, `NumberTheory/AdelicHaar`, the polynomial-decay row of
`PolyDecay`, and the trace-dual/character premises `TraceDual`, `NonzeroTrace`,
`NumberTheory/NumberField/GlobalAddChar/Circle`. The pin declares its engine `private`; the names the
pin shares with `EisensteinGeneral/Unfolding.lean` are promoted to public there and imported, not
re-proved, so this module adds only the pin's own new declarations.

Transcribed from the pin below (pinned `aa2d8b3`, 1,038 `S_` lines).

## Port deltas

* The pin's `WhittakerSummability.{Support,Decay,Assembly,LatticeSum}` become
  `AutomorphicForm.BruhatSummability.{Support,Unfold,Vanishing,Decay,Assembly,LatticeSum}`; every
  helper stays `private` as in the pin, so the module's public surface is the headline alone.
* `jacquetIntegrand` is declared twice in the pin, under `Unfold` (`:329`) and `Decay` (`:713`),
  with the same body and different stage namespaces. The `Unfold` copy is the promoted public
  `EisensteinGeneral.Unfolding.jacquetIntegrand`; the `Decay` copy is this module's
  `BruhatSummability.Decay.jacquetIntegrand`. This is the pin's namespace split, not a rename, and
  both copies stay: `dedup.py` reports 0 clusters / 0 removable lines on this module.
* `whittakerCoefficient_bruhatSeries_eq_of_isInducedSection` (`:385`): the port's public copy in
  `EisensteinGeneral.Unfolding` states the same coefficient with the series written out; this
  module's private `BruhatSummability.Unfold.…` is the pin's `bruhatSeries` spelling of that row.
* `FiniteAdeleRing` is `IsDedekindDomain.FiniteAdeleRing`, `RightTranslationFn` is
  `FLT.SmoothVectors.RightTranslationFn`, `mixedSpace` is `mixedEmbedding.mixedSpace`,
  `(𝓞 F)⁰` needs `scoped nonZeroDivisors`; the module opens `IsDedekindDomain`,
  `FLT.SmoothVectors` and `NumberField.AdelicBox` for these.
* `glArch_unipotentGL2` and `continuous_unipotentGL2` are `private` outside this module's import
  closure (`AutomorphicForm/Adelic/KfSmoothTensor.lean`, `…/WhittakerSystem.lean`) and are
  transcribed here, `private`, at the pin's names and statements.
* `set_option linter.style.haveILetI false` at module head: the pin's
  `haveI := isAddHaarMeasure_adelicAddHaar …` registers a measure instance that the style linter
  reads as a `have`; the port's own `AutomorphicForm/Adelic/SmoothAutomorphicFn.lean` carries the
  same switch for the same reason. No `maxHeartbeats` option is set anywhere in this module.

## The rows

* `AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary` — 1,038 pin `S_` lines.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.lean>

spec-pin: Theorems/Thm_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.lean
spec-pin: P2M/Sol/S_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.PolyDecay
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.Assembly
import FLTForHuman.EisensteinGeneral.Unfolding
import FLTForHuman.NumberTheory.AdelicFourier.Faithful
import FLTForHuman.NumberTheory.AdelicFourier.TraceDual
import FLTForHuman.NumberTheory.AdelicFourier.NonzeroTrace
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls feed instance search in the proofs below (the port's own
-- `SmoothAutomorphicFn.lean` carries the same switch for the same reason); the style linter reads
-- the Prop-valued `IsAddHaarMeasure` instance as a `have`.
set_option linter.style.haveILetI false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm IsDedekindDomain FLT.SmoothVectors NumberField.AdelicBox
open scoped NNReal nonZeroDivisors

namespace AutomorphicForm

noncomputable section

/-! ## The support of the Jacquet integral at a level

The pin's `WhittakerSummability.Support` (`:418`–`:571`): the finite/infinite adèle inclusions,
the conjugation `t ↦ g⁻¹ u(t) g` of a unipotent into the level subgroup `finiteAdelicGL2Subgroup`,
and the `1 - c` argument that kills the Fourier integral of a function fixed by a level. -/

namespace BruhatSummability

namespace Support

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "𝔸i" => InfiniteAdeleRing F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private def finAdele (t : 𝔸f) : 𝔸 := ((0 : 𝔸i), t)

private def infAdele (x : 𝔸i) : 𝔸 := (x, (0 : 𝔸f))

@[scoped simp] private theorem finAdele_fst (t : 𝔸f) : (finAdele F t).1 = 0 := rfl
@[scoped simp] private theorem finAdele_snd (t : 𝔸f) : (finAdele F t).2 = t := rfl

private theorem finAdele_zero : finAdele F 0 = 0 := rfl

private theorem continuous_finAdele : Continuous (finAdele F) :=
  (continuous_const.prodMk continuous_id : Continuous fun t : 𝔸f => ((0 : 𝔸i), t))

private theorem algebraMap_mul_finAdele (ξ : F) (t : 𝔸f) :
    algebraMap F 𝔸 ξ * finAdele F t = finAdele F (algebraMap F 𝔸f ξ * t) := by
  refine Prod.ext ?_ ?_
  · show (algebraMap F 𝔸 ξ).1 * 0 = 0
    exact mul_zero _
  · rfl

private theorem algebraMap_mul_infAdele (a : F) (x : 𝔸i) :
    algebraMap F 𝔸 a * infAdele F x = infAdele F (algebraMap F 𝔸i a * x) := by
  refine Prod.ext ?_ ?_
  · rfl
  · show (algebraMap F 𝔸 a).2 * 0 = 0
    exact mul_zero _

private theorem continuous_unipotentGL2 :
    Continuous (fun u : 𝔸 => (unipotentGL2 u : AdelicGL2 (𝓞 F) F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have h1 : (Units.val ∘ fun u : 𝔸 => (unipotentGL2 u : AdelicGL2 (𝓞 F) F))
        = fun u => !![(1 : 𝔸), u; 0, 1] := funext fun u => unipotentGL2_coe u
    rw [h1]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have h1 : (fun u : 𝔸 =>
          (((unipotentGL2 u : AdelicGL2 (𝓞 F) F)⁻¹ : AdelicGL2 (𝓞 F) F) :
            Matrix (Fin 2) (Fin 2) 𝔸)) = fun u => !![(1 : 𝔸), -u; 0, 1] :=
      funext fun u => rfl
    rw [h1]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem glArch_unipotentGL2 (u : 𝔸) :
    NumberField.AdelicLevel.glArch (𝓞 F) F (unipotentGL2 u) = unipotentGL2 u.1 := by
  apply Units.ext
  ext i j
  rw [NumberField.AdelicLevel.glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem conj_unipotentGL2_mem (g : AdelicGL2 (𝓞 F) F) (t : 𝔸f) :
    g⁻¹ * unipotentGL2 (finAdele F t) * g ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_unipotentGL2,
    finAdele_fst, unipotentGL2_zero, mul_one, inv_mul_cancel]

private def conjUnip (g : AdelicGL2 (𝓞 F) F) (t : 𝔸f) : finiteAdelicGL2Subgroup F :=
  ⟨g⁻¹ * unipotentGL2 (finAdele F t) * g, conj_unipotentGL2_mem F g t⟩

private theorem continuous_conjUnip (g : AdelicGL2 (𝓞 F) F) : Continuous (conjUnip F g) := by
  have h2 : Continuous (fun t : 𝔸f => (unipotentGL2 (finAdele F t) : AdelicGL2 (𝓞 F) F)) :=
    (continuous_unipotentGL2 F).comp (continuous_finAdele F)
  have h3 : Continuous (fun t : 𝔸f => g⁻¹ * unipotentGL2 (finAdele F t) * g) :=
    (h2.const_mul g⁻¹).mul_const g
  exact h3.subtype_mk fun t => conj_unipotentGL2_mem F g t

private theorem conjUnip_zero (g : AdelicGL2 (𝓞 F) F) : conjUnip F g 0 = 1 := by
  refine Subtype.ext ?_
  show g⁻¹ * unipotentGL2 (finAdele F 0) * g = 1
  rw [finAdele_zero, unipotentGL2_zero, mul_one, inv_mul_cancel]

private theorem apply_mul_eq_of_mem_stabilizer {φ : AdelicGL2 (𝓞 F) F → ℂ}
    {u : finiteAdelicGL2Subgroup F}
    (hu : u ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F)
        (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ))
    (X : AdelicGL2 (𝓞 F) F) : φ (X * u) = φ X := by
  have h := MulAction.mem_stabilizer_iff.mp hu
  have hX := congrArg (fun f => RightTranslationFn.toFun f X) h
  simpa [Subgroup.smul_def] using hX

private theorem integral_eq_zero_of_period {ψ : AddChar 𝔸 ℂ} (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) (ξ : F) (t : 𝔸)
    (hfix : ∀ y : 𝔸, Φ (unipotentGL2 (t + y) * g) = Φ (unipotentGL2 y * g))
    (hψt : ψ (algebraMap F 𝔸 ξ * t) ≠ 1) :
    ∫ y, Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y)) ∂(adelicAddHaar (𝓞 F) F) = 0 := by
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hshift : ∀ y : 𝔸, Φ (unipotentGL2 (t + y) * g) * ψ (-(algebraMap F 𝔸 ξ * (t + y)))
      = ψ (-(algebraMap F 𝔸 ξ * t)) * (Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y))) := by
    intro y
    rw [hfix y, mul_add, neg_add, AddChar.map_add_eq_mul]
    ring
  have key : ∫ y, Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y)) ∂(adelicAddHaar (𝓞 F) F)
      = ∫ y, Φ (unipotentGL2 (t + y) * g) * ψ (-(algebraMap F 𝔸 ξ * (t + y)))
          ∂(adelicAddHaar (𝓞 F) F) :=
    (integral_add_left_eq_self (μ := adelicAddHaar (𝓞 F) F)
      (fun y => Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y))) t).symm
  simp_rw [hshift] at key
  rw [integral_const_mul] at key
  have hc1 : ψ (-(algebraMap F 𝔸 ξ * t)) ≠ 1 := by
    intro h1
    apply hψt
    have hmul : ψ (-(algebraMap F 𝔸 ξ * t)) * ψ (algebraMap F 𝔸 ξ * t) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    rwa [h1, one_mul] at hmul
  have h0 : (1 - ψ (-(algebraMap F 𝔸 ξ * t)))
      * ∫ y, Φ (unipotentGL2 y * g) * ψ (-(algebraMap F 𝔸 ξ * y)) ∂(adelicAddHaar (𝓞 F) F) = 0 := by
    rw [sub_mul, one_mul, sub_eq_zero]; exact key
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr (Ne.symm hc1))

private theorem lattice_of_level {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) {N : 𝓞 F}
    (hN : N ≠ 0) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ ∀ ξ : F,
      (∀ z ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F,
          ψ (finAdele F (algebraMap F 𝔸f (ξ * algebraMap (𝓞 F) F N) * z)) = 1) →
      ∃ a : 𝓞 F, algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F D * ξ := by
  classical
  obtain ⟨a, ha0, ha⟩ :=
    NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  have hψa : IsGlobalAddChar F (ψ.mulShift (algebraMap F 𝔸 a)) :=
    { principalInvariant := fun q => by
        rw [AddChar.mulShift_apply, ← map_mul]
        exact hψ.principalInvariant (a * q)
      continuous := by
        change Continuous fun x : 𝔸 => ψ (algebraMap F 𝔸 a * x)
        exact hψ.continuous.comp (continuous_const_mul (algebraMap F 𝔸 a))
      nontrivial := by
        intro h
        apply hψ.nontrivial
        refine DFunLike.ext _ _ fun x => ?_
        have hx := DFunLike.congr_fun h (algebraMap F 𝔸 a⁻¹ * x)
        rw [AddChar.one_apply, AddChar.mulShift_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0,
          map_one, one_mul] at hx
        rw [AddChar.one_apply]
        exact hx }
  have hinf : ∀ x : 𝔸i, ψ.mulShift (algebraMap F 𝔸 a) (x, 0)
      = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by
    intro x
    change ψ (algebraMap F 𝔸 a * infAdele F x) = _
    rw [algebraMap_mul_infAdele]
    exact ha x

  obtain ⟨m, hmS, hm⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).isFractional
  obtain ⟨q, hq⟩ := IsLocalization.exists_integer_multiple (𝓞 F)⁰ a
  obtain ⟨p, hp⟩ := hq
  refine ⟨m * N * q, mul_ne_zero (mul_ne_zero (nonZeroDivisors.ne_zero hmS) hN)
    (nonZeroDivisors.coe_ne_zero q), fun ξ hξ => ?_⟩
  have hmem : a⁻¹ * (ξ * algebraMap (𝓞 F) F N)
      ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) := by
    refine (NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual F hψa
      hinf _).mp fun z hz => ?_
    change ψ (algebraMap F 𝔸 a
      * finAdele F (algebraMap F 𝔸f (a⁻¹ * (ξ * algebraMap (𝓞 F) F N)) * z)) = 1
    rw [algebraMap_mul_finAdele, ← mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    exact hξ z hz

  obtain ⟨r, hr⟩ := hm _ hmem
  refine ⟨r * p, ?_⟩
  simp only [map_mul, hr, hp, Algebra.smul_def]
  have h1 : algebraMap (𝓞 F) F m * (a⁻¹ * (ξ * algebraMap (𝓞 F) F N)) * (algebraMap (𝓞 F) F q * a)
      = algebraMap (𝓞 F) F m * algebraMap (𝓞 F) F N * algebraMap (𝓞 F) F q * ξ * (a⁻¹ * a) := by
    ring
  rw [h1, inv_mul_cancel₀ ha0, mul_one]

private theorem integral_weyl_unipotent_eq_zero_of_forall_ne
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφf : IsKfSmooth F φ)
    (g : AdelicGL2 (𝓞 F) F) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) →
      ∫ y, φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y)) ∂(adelicAddHaar (𝓞 F) F) = 0 := by
  classical

  have hSo : IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := hφf
  have hLo := hSo.preimage (continuous_conjUnip F g)
  have h0L : (0 : 𝔸f) ∈ conjUnip F g ⁻¹' ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := by
    rw [Set.mem_preimage, conjUnip_zero]
    exact Subgroup.one_mem _
  obtain ⟨N, hN0, hN⟩ :=
    NumberField.AdelicFourier.Level.exists_level_smul_integral_subset (hLo.mem_nhds h0L)

  obtain ⟨D, hD0, hD⟩ := lattice_of_level F hψ hN0
  refine ⟨D, hD0, fun ξ hξ => ?_⟩
  by_cases hall : ∀ z ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F,
      ψ (finAdele F (algebraMap F 𝔸f (ξ * algebraMap (𝓞 F) F N) * z)) = 1
  · obtain ⟨a, ha⟩ := hD ξ hall
    exact absurd ha (hξ a)
  push Not at hall
  obtain ⟨z, hz, hz1⟩ := hall

  have htL := hN z hz
  rw [Set.mem_preimage] at htL
  have key := integral_eq_zero_of_period F (ψ := ψ) (fun x => φ (adelicWeyl (𝓞 F) F * x)) g ξ
    (finAdele F (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z)) (fun y => ?_) ?_
  · simpa only [mul_assoc] using key
  · show φ (adelicWeyl (𝓞 F) F
        * (unipotentGL2 (finAdele F (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z) + y) * g))
      = φ (adelicWeyl (𝓞 F) F * (unipotentGL2 y * g))
    have hgrp : adelicWeyl (𝓞 F) F
          * (unipotentGL2 (finAdele F (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z) + y) * g)
        = adelicWeyl (𝓞 F) F * (unipotentGL2 y * g)
          * (conjUnip F g (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z) : AdelicGL2 (𝓞 F) F) := by
      rw [add_comm, unipotentGL2_add]
      show _ = _ * (g⁻¹ * unipotentGL2 (finAdele F (algebraMap F 𝔸f (algebraMap (𝓞 F) F N) * z)) * g)
      group
    rw [hgrp]
    exact apply_mul_eq_of_mem_stabilizer F htL _
  · rw [algebraMap_mul_finAdele, ← mul_assoc, ← map_mul]
    exact hz1

end Support

/-! The pin's `Unfold` tail (`:385`–`:391`). The port's public
`EisensteinGeneral.Unfolding.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection` states the
same coefficient with the series written out; this is the pin's `bruhatSeries` spelling. -/

namespace Unfold

variable {F : Type} [Field F] [NumberField F]

private theorem whittakerCoefficient_bruhatSeries_eq_of_isInducedSection
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    (hψ : IsGlobalAddChar F ψ) {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) {ξ : F} (hξ : ξ ≠ 0) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g))
      (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ (EisensteinGeneral.Unfolding.bruhatSeries φ) ξ g
      = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal •
          ∫ y, EisensteinGeneral.Unfolding.jacquetIntegrand ψ φ ξ g y ∂(adelicAddHaar (𝓞 F) F) :=
  EisensteinGeneral.Unfolding.whittakerCoefficient_bruhatSeries_eq hψ
    (fun x g' => isInducedSection_unipotent_mul hφ x g') hξ g hint

end Unfold

namespace Vanishing

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem whittakerCoefficient_bruhatSeries_eq_zero_of_forall_ne (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (hφf : IsKfSmooth F φ) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g))
      (adelicAddHaar (𝓞 F) F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) →
      whittakerCoefficient F (productionPins F) ψ
        (EisensteinGeneral.Unfolding.bruhatSeries φ) ξ g = 0 := by
  obtain ⟨d, hd, hsup⟩ := Support.integral_weyl_unipotent_eq_zero_of_forall_ne F hψ hφf g
  refine ⟨d, hd, fun ξ hξ => ?_⟩
  by_cases hξ0 : ξ = 0
  · exfalso
    refine hξ 0 ?_
    rw [hξ0, mul_zero]
    exact map_zero _
  · rw [Unfold.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection hψ hφ hξ0 g hint]
    have h0 : ∫ y, EisensteinGeneral.Unfolding.jacquetIntegrand ψ φ ξ g y
        ∂(adelicAddHaar (𝓞 F) F) = 0 := hsup ξ hξ
    rw [h0, smul_zero]

end Vanishing

/-! ## The decay of the Jacquet integral

The pin's second `jacquetIntegrand` (`:713`, the `Decay` stage's own copy — a namespace split, not
a rename: the port's `EisensteinGeneral.Unfolding.jacquetIntegrand` is the `Unfold` copy) and the
polynomial decay that feeds it, from SET-AF111A's `PolyDecay` row. -/

namespace Decay

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel

private def jacquetIntegrand (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (ξ : F) (g : AdelicGL2 (𝓞 F) F) (y : AdeleRing (𝓞 F) F) : ℂ :=
  φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y))

open scoped Classical in
private theorem norm_integral_jacquetIntegrand_le_polyDecay
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (_hint : ∀ g' : AdelicGL2 (𝓞 F) F,
        Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g'))
          (adelicAddHaar (𝓞 F) F))
      (g : AdelicGL2 (𝓞 F) F) (N : ℕ),
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : F,
      ‖∫ y, jacquetIntegrand F ψ φ ξ g y ∂(adelicAddHaar (𝓞 F) F)‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ)) := by
  intro α hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK _hφf hφc _hint g N
  exact AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary F hα χ₁ χ₂
    hχ₁ hχ₂ ψ hψ s (lt_trans one_half_lt_one hs) φ hφ hφK hφc g N

end Decay

/-! ## The assembly: the lattice bound at `Re s > 1` -/

namespace Assembly

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

private theorem integrable_weyl_unipotent_mul_of_one_lt
    (hα : ∀ x, 0 < ((WeylUnipotentIntegrable.haarModulus F x : ℝˣ) : ℝ))
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ₁ : IsUnitaryChar (𝓞 F) F χ₁) (hχ₂ : IsUnitaryChar (𝓞 F) F χ₂)
    (s : ℂ) (hs : 1 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst χ₁ (WeylUnipotentIntegrable.haarModulus F) hα s)
      (etaSnd χ₂ (WeylUnipotentIntegrable.haarModulus F) hα s) φ)
    (hφc : Continuous φ) (g' : AdelicGL2 (𝓞 F) F) :
    Integrable (fun y : AdeleRing (𝓞 F) F => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g'))
      (adelicAddHaar (𝓞 F) F) :=
  WeylUnipotentIntegrable.integrable_weyl_unipotent_mul F hα χ₁ χ₂ hχ₁ hχ₂ s
    (lt_trans (by norm_num) hs) φ hφ hφc g'

private theorem rpow_neg_le_mul_rpow_neg {X Y c : ℝ} (hX : 0 < X) (hY : 0 < Y) (hc : 0 < c)
    (hYX : Y ≤ c * X) (N : ℕ) :
    X ^ (-(N : ℝ)) ≤ c ^ N * Y ^ (-(N : ℝ)) := by
  rw [Real.rpow_neg hX.le, Real.rpow_neg hY.le, Real.rpow_natCast, Real.rpow_natCast]
  have h1 : Y ^ N ≤ c ^ N * X ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hY.le hYX N
  have h2 : (c ^ N * X ^ N)⁻¹ ≤ (Y ^ N)⁻¹ := inv_anti₀ (pow_pos hY N) h1
  calc (X ^ N)⁻¹ = c ^ N * (c ^ N * X ^ N)⁻¹ := by
        rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_pos hc N).ne', one_mul]
    _ ≤ c ^ N * (Y ^ N)⁻¹ := mul_le_mul_of_nonneg_left h2 (pow_pos hc N).le

open scoped Classical in

private theorem one_add_norm_mixedEmbedding_le (a : F) {d : F} (hd : d ≠ 0) :
    1 + ‖NumberField.mixedEmbedding F a‖ ≤
      max 1 ‖NumberField.mixedEmbedding F d‖ * (1 + ‖NumberField.mixedEmbedding F (a / d)‖) := by
  have hmul : NumberField.mixedEmbedding F a
      = NumberField.mixedEmbedding F (a / d) * NumberField.mixedEmbedding F d := by
    rw [← map_mul, div_mul_cancel₀ a hd]
  have h1 : ‖NumberField.mixedEmbedding F a‖
      ≤ ‖NumberField.mixedEmbedding F (a / d)‖ * max 1 ‖NumberField.mixedEmbedding F d‖ := by
    rw [hmul]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))
  have hc1 : (1 : ℝ) ≤ max 1 ‖NumberField.mixedEmbedding F d‖ := le_max_left _ _
  have h0 : 0 ≤ ‖NumberField.mixedEmbedding F (a / d)‖ := norm_nonneg _
  linarith [h1, hc1, h0]

open scoped Classical in
private theorem norm_whittakerCoefficient_bruhatSeries_le
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsInducedSection (𝓞 F) F χ₁ χ₂ φ) (g : AdelicGL2 (𝓞 F) F)
    (hint : Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g))
      (adelicAddHaar (𝓞 F) F))
    {d : 𝓞 F} (hd : d ≠ 0) {C : ℝ} (hC : 0 < C) (N : ℕ)
    (hB : ∀ ξ : F, ‖∫ y, Decay.jacquetIntegrand F ψ φ ξ g y ∂(adelicAddHaar (𝓞 F) F)‖ ≤
      C * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ))) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ a : 𝓞 F,
      ‖whittakerCoefficient F (productionPins F) ψ
          (EisensteinGeneral.Unfolding.bruhatSeries φ) ((a : F) / d) g‖ ≤
        C' * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ)) := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hm : 0 < ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr (adelicAddHaar_adelicBox_lt_top F).ne)
      (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')
  have hc : 0 < max 1 ‖NumberField.mixedEmbedding F (d : F)‖ := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal * C
      * (max 1 ‖NumberField.mixedEmbedding F (d : F)‖) ^ N
      + ‖whittakerCoefficient F (productionPins F) ψ
          (EisensteinGeneral.Unfolding.bruhatSeries φ) 0 g‖,
    add_pos_of_pos_of_nonneg (mul_pos (mul_pos hm hC) (pow_pos hc N)) (norm_nonneg _), fun a => ?_⟩
  by_cases ha : a = 0
  ·
    subst ha
    have h0 : ((0 : 𝓞 F) : F) = 0 := map_zero (algebraMap (𝓞 F) F)
    rw [h0, zero_div, map_zero, norm_zero, add_zero, Real.one_rpow, mul_one]
    exact le_add_of_nonneg_left (mul_nonneg (mul_nonneg hm.le hC.le) (pow_pos hc N).le)
  ·
    have ha' : (a : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
    have hξ : (a : F) / d ≠ 0 := div_ne_zero ha' hd'
    have hBξ : ‖∫ y, EisensteinGeneral.Unfolding.jacquetIntegrand ψ φ ((a : F) / d) g y
        ∂(adelicAddHaar (𝓞 F) F)‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F ((a : F) / d)‖) ^ (-(N : ℝ)) := hB ((a : F) / d)
    have hX : 0 < 1 + ‖NumberField.mixedEmbedding F ((a : F) / d)‖ := by positivity
    have hY : 0 < 1 + ‖NumberField.mixedEmbedding F (a : F)‖ := by positivity
    have hpow := rpow_neg_le_mul_rpow_neg hX hY hc (one_add_norm_mixedEmbedding_le F (a : F) hd') N
    rw [Unfold.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection hψ hφ hξ g hint, norm_smul,
      Real.norm_of_nonneg hm.le]
    calc ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal
          * ‖∫ y, EisensteinGeneral.Unfolding.jacquetIntegrand ψ φ ((a : F) / d) g y
              ∂(adelicAddHaar (𝓞 F) F)‖
        ≤ ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal
          * (C * ((max 1 ‖NumberField.mixedEmbedding F (d : F)‖) ^ N
            * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hBξ.trans (mul_le_mul_of_nonneg_left hpow hC.le)) hm.le
      _ = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal * C
            * (max 1 ‖NumberField.mixedEmbedding F (d : F)‖) ^ N
          * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (norm_nonneg _))
          (Real.rpow_nonneg hY.le _)

open scoped Classical in
private theorem latticeBound_bruhatSeries
    (hα : ∀ x, 0 < ((WeylUnipotentIntegrable.haarModulus F x : ℝˣ) : ℝ))
    (χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ₁ : IsUnitaryChar (𝓞 F) F χ₁) (hχ₂ : IsUnitaryChar (𝓞 F) F χ₂)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ) (s : ℂ) (hs : 1 < s.re)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst χ₁ (WeylUnipotentIntegrable.haarModulus F) hα s)
      (etaSnd χ₂ (WeylUnipotentIntegrable.haarModulus F) hα s) φ)
    (hφK : IsArchKFinite F φ) (hφf : IsKfSmooth F φ) (hφc : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ (d : 𝓞 F) (C : ℝ) (N : ℕ), d ≠ 0 ∧ 0 < C ∧ Module.finrank ℚ F < N ∧
      (∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) →
        whittakerCoefficient F (productionPins F) ψ
          (EisensteinGeneral.Unfolding.bruhatSeries φ) ξ g = 0) ∧
      (∀ a : 𝓞 F, ‖whittakerCoefficient F (productionPins F) ψ
          (EisensteinGeneral.Unfolding.bruhatSeries φ) ((a : F) / d) g‖
        ≤ C * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ))) := by
  have hint : ∀ g' : AdelicGL2 (𝓞 F) F,
      Integrable (fun y => φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g')) (adelicAddHaar (𝓞 F) F) :=
    fun g' => integrable_weyl_unipotent_mul_of_one_lt F hα χ₁ χ₂ hχ₁ hχ₂ s hs φ hφ hφc g'
  obtain ⟨d, hd, hS⟩ :=
    Vanishing.whittakerCoefficient_bruhatSeries_eq_zero_of_forall_ne F hψ hφ hφf g (hint g)
  obtain ⟨C, hC, hB⟩ := Decay.norm_integral_jacquetIntegrand_le_polyDecay F hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs
    φ hφ hφK hφf hφc hint g (Module.finrank ℚ F + 1)
  obtain ⟨C', hC', hB'⟩ := norm_whittakerCoefficient_bruhatSeries_le F hψ hφ g (hint g) hd hC
    (Module.finrank ℚ F + 1) hB
  exact ⟨d, C', Module.finrank ℚ F + 1, hd, hC', Nat.lt_succ_self _, hS, hB'⟩

end Assembly

/-! ## From a lattice bound to summability -/

namespace LatticeSum

open scoped Classical in
private theorem latticeBound
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    ∃ (d : 𝓞 F) (C : ℝ) (N : ℕ), d ≠ 0 ∧ 0 < C ∧ Module.finrank ℚ F < N ∧
      (∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) →
        whittakerCoefficient F (productionPins F) ψ E ξ g = 0) ∧
      (∀ a : 𝓞 F, ‖whittakerCoefficient F (productionPins F) ψ E ((a : F) / d) g‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F (a : F)‖) ^ (-(N : ℝ))) := by
  intro α hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK hφf hφc g E
  exact Assembly.latticeBound_bruhatSeries F hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK hφf hφc g

open scoped Classical in

private theorem summable_integers_rpow (F : Type*) [Field F] [NumberField F]
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hN : Module.finrank ℚ F < N) :
    Summable (fun a : 𝓞 F => C * (1 + ‖mixedEmbedding F (a : F)‖) ^ (-(N : ℝ))) := by
  classical
  set L : Submodule ℤ (mixedEmbedding.mixedSpace F) := mixedEmbedding.integerLattice F with hL
  have hrank : Module.finrank ℤ L < N := by
    rw [hL, ZLattice.rank ℝ (mixedEmbedding.integerLattice F), mixedEmbedding.finrank]
    exact hN
  have hLsum : Summable (fun z : L => C * (1 + ‖z‖) ^ (-(N : ℝ))) := by
    refine Summable.of_norm_bounded_eventually
      ((ZLattice.summable_norm_pow_inv L N hrank).mul_left C) ?_
    filter_upwards [Filter.eventually_cofinite_ne (0 : L)] with z hz
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hnn : 0 ≤ C * (1 + ‖z‖) ^ (-(N : ℝ)) := by positivity
    rw [Real.norm_of_nonneg hnn]
    have key : (1 + ‖z‖) ^ (-(N : ℝ)) ≤ ‖z‖⁻¹ ^ N := by
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖z‖), Real.rpow_natCast, inv_pow]
      exact inv_anti₀ (pow_pos hzpos N) (pow_le_pow_left₀ hzpos.le (by linarith) N)
    exact mul_le_mul_of_nonneg_left key hC

  let e : 𝓞 F → L := fun a => ⟨mixedEmbedding F (a : F), LinearMap.mem_range.mpr ⟨a, rfl⟩⟩
  have he : Function.Injective e := by
    intro a b h
    have h' : mixedEmbedding F (a : F) = mixedEmbedding F (b : F) := congrArg Subtype.val h
    exact RingOfIntegers.coe_injective (NumberField.mixedEmbedding_injective F h')
  have hrange : ∀ z ∉ Set.range e,
      (fun z : L => C * (1 + ‖z‖) ^ (-(N : ℝ))) z = 0 := by
    intro z hz
    exfalso
    apply hz
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp z.2
    exact ⟨a, Subtype.ext ha⟩
  exact (he.summable_iff hrange).mpr hLsum

open scoped Classical in
private theorem summable_of_lattice_bound {F : Type*} [Field F] [NumberField F] {W : F → ℂ}
    {d : 𝓞 F} (hd : d ≠ 0) {C : ℝ} (hC : 0 < C) {N : ℕ} (hN : Module.finrank ℚ F < N)
    (hsupp : ∀ ξ : F, (∀ a : 𝓞 F, (a : F) ≠ (d : F) * ξ) → W ξ = 0)
    (hbd : ∀ a : 𝓞 F, ‖W ((a : F) / d)‖ ≤ C * (1 + ‖mixedEmbedding F (a : F)‖) ^ (-(N : ℝ))) :
    Summable W := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  let ι : 𝓞 F → F := fun a => (a : F) / d
  have hι : Function.Injective ι := fun a b h =>
    RingOfIntegers.coe_injective ((div_left_inj' hd').mp h)
  have hoff : ∀ ξ ∉ Set.range ι, W ξ = 0 := by
    intro ξ hξ
    apply hsupp ξ
    intro a ha
    exact hξ ⟨a, by simp only [ι, ha, mul_div_cancel_left₀ _ hd']⟩
  refine (hι.summable_iff hoff).mp ?_
  exact Summable.of_norm_bounded (summable_integers_rpow F C hC.le N hN) (fun a => hbd a)

private theorem summable_of_latticeBound
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    Summable (fun ξ : F => whittakerCoefficient F (productionPins F) ψ E ξ g) := by
  intro α hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK hφf hφc g E
  obtain ⟨d, C, N, hd, hC, hN, hsupp, hbd⟩ :=
    latticeBound F hα χ₁ χ₂ hχ₁ hχ₂ ψ hψ s hs φ hφ hφK hφf hφc g
  exact summable_of_lattice_bound hd hC hN hsupp hbd

end LatticeSum

end BruhatSummability

theorem summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    Summable (fun ξ : F => whittakerCoefficient F (productionPins F) ψ E ξ g) :=
  BruhatSummability.LatticeSum.summable_of_latticeBound F

end

end AutomorphicForm
