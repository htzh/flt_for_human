/-
The Whittaker coefficient is bounded by the derivative of the section at the unipotent.

`AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le`
(645 pin `S_` lines): if the section's right translates along the unipotent subgroup are bounded by
`C` and its derivative at the identity of `unipotentGL2` is bounded by `D`, then the Whittaker
coefficient at every `α ≠ 0` is bounded by `C * D` times the inverse norm of `α` — the norm estimate
the entire-Euler-product identity of SET-AF109A feeds into.

The story is the set's only AutomorphicForm row, and it is the *consumer* of AF109A: the
factorisation datum's `hfac` is what makes the derivative bound uniform in the place. Its three
premise modules are the box Fourier factorisation (`EisensteinGeneral/Factorization/BoxFourier.lean`),
the fundamental-domain integration (`Analysis/Fourier/FundamentalDomainIntegration.lean`) and the
archimedean trace character (`NumberTheory/NumberField/StandardAddCharTrace.lean`), and no existing
module is above all three, so the home is new.

## The rows

* `AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le` — 645 pin `S_` lines.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le.lean>

spec-pin: Theorems/Thm_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le.lean
spec-pin: P2M/Sol/S_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le.lean

## What the engine is

The pin's 60 declarations are one flat engine, generated under the label `WhitIBP` and public
throughout (no `private` helper). This module is a **verbatim transcription** of that engine into
`AutomorphicForm` (the headline's namespace), so the pin-vs-module declaration diff is by hash on
every row it declares. Three rows are *not* declared here, each for a measured reason:

* `continuous_eA_symm` (pin `:249`) — **imported**, statement-identical:
  `AutomorphicForm.LocalIntertwining.UnipDeriv.continuous_eA_symm`
  (`AutomorphicForm/Adelic/RightConvDerivatives.lean:133`, its own `spec-pin` wire). The order measures
  this as the pin's one substitution. The pin's proof of it uses only `eA_symm_apply_of_isReal` and
  `eA_symm_apply_of_isComplex`, and both of *those* rows are transcribed here (they are pin rows of
  this engine, `:229`/`:239`), so nothing of the engine is lost.
* `continuous_unipotentGL2` (pin `:275`) — **reused**: the port's public
  `AutomorphicForm.continuous_unipotentGL2` (`AutomorphicForm/Adelic/ConstantTerm.lean:81`) already
  states the general form `{R} [CommRing R] [TopologicalSpace R] [ContinuousNeg R] →
  Continuous fun x : R => unipotentGL2 x`, of which the pin's row is the instance at
  `R := AdeleRing (𝓞 K) K`. Declaring the pin's specialised statement here would declare the full name
  `AutomorphicForm.continuous_unipotentGL2` twice (FR-0274). The two call sites of the pin's proof
  (`:360`, `:604`) are spelled with `(R := …)` instead of the pin's explicit `K`.
* `μA` (pin `:68`) — **imported**: `AutomorphicForm.μA`
  (`AutomorphicForm/Adelic/HeightWeylMass.lean:427`) is
  `noncomputable abbrev μA : Measure (AdeleRing (𝓞 F) F) := adelicAddHaar (𝓞 F) F`, i.e. the pin's
  `abbrev` under a renamed section variable (the pin's has `K`). Declaring it here would declare the
  full name `AutomorphicForm.μA` twice (FR-0274). Nothing in this module can tell the two apart:
  both unfold to `adelicAddHaar (𝓞 K) K` in the *same* measurable space.

Every row that `check_port` diffs against the wire is therefore either declared here at the pin's
statement, or (for the three rows above) is already a public declaration of the port at that
statement.

## Frictions hit (measured)

* `attribute [-instance] instCountableOfNumberField_definitions` (pin `:16`) is **dropped**: the pin
  instance has no port counterpart (`LanglandsTunnell/WeightOneLiftCentralDet.lean:58` records the
  same), so there is nothing to un-register.
* `set_option linter.unusedSectionVars false` (pin `:24`, module-wide) is **not** carried module-wide
  (house policy: linters are declaration-scoped). Two declarations need it and carry it
  declaration-scoped — `eA_symm_apply_of_isReal` and `eA_symm_apply_of_isComplex`, which genuinely do
  not use `[NumberField K]` (`eA K` needs only `[Field K]`), so the lint is a true report there.
* the pin's file-level `open … NumberField.AdelicLevel` is **dropped**: with both
  `NumberField.AdelicLevel` and `NumberField.AdelicBox` open, `integralFiniteAdeles` and the four
  `is*_integralFiniteAdeles` rows are **ambiguous** in the port (there is a `@[reducible]` alias
  `NumberField.AdelicBox.integralFiniteAdeles` in `NumberTheory/AdelicHaar/PlaceMeasure.lean:48` beside
  `NumberField.AdelicLevel.integralFiniteAdeles`). The pin's own open list has no `AdelicLevel`, so the
  drop restores the pin's spelling; the one `AdelicLevel` name the pin uses inside a proof is qualified
  (`NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers`).
* `AddChar.compAddMonoidHom_apply` (pin `:141`, `:146`) is dropped at the two sites of `μ'_prod_real`:
  the lemma is a `rfl`-unfolding of `AddChar.compAddMonoidHom`, and under the port's `AdeleRing`
  spelling (`AdeleRing` is a `def` whose `CommRing` instance is not the product's) the `simp only` hits
  an `implicit`-transparency type mismatch. Each is replaced by a pointwise `have hpt : ∀ v, (…) = 1`
  discharged at default transparency; the rest of both proofs is the pin's. The same friction is
  recorded in `EisensteinGeneral/PiecePartialEulerProduct.lean:106`.
* one step of `hasDerivAt_inner` (pin `:408–417`): `rw [← unipotentGL2_add]` cannot match when the first
  operand is the pair literal `((eA K).symm ((s + -t) • v), 0)`, whose inferred type is the product, so
  the `+` the pin gets at `AdeleRing` is not the one `rw` sees. The step is rewritten with two `set`s
  typed `AdeleRing (𝓞 K) K` (so the addition really is the adele addition) and the pin's three
  rewrites; the mathematics is unchanged.

## Measurements (all measured on this module; the probe is recorded, never installed)

* `spec/check_port.py --force` — **52 ok, 0 mismatch, 0 missing, 0 own, 0 kw**.
* pin-vs-module declaration diff by statement hash — **56/60 by name *and* hash**; the pin's `solution`
  matches the headline by hash (the headline carries the wrapper's row name); the other 3 are the
  substitutions above.
* edit loop `-DautoImplicit=false -DmaxHeartbeats=200000` — **silent**, 11.2 s.
* heartbeat probe, module: **40 000 ✓ / 20 000 ✗** (the 20 k failure is a `whnf` timeout inside the
  headline's proof). Type floor (all 38 theorem proofs `sorry`): **5 000 ✓ / 1 000 ✗** — the cost is in
  the proofs, not in the statements. No `set_option maxHeartbeats` is installed.
* `dedup.py --within` — 0 duplicate clusters; `move_dead.py --dry-run` — 0 declarations, 0 lines.
-/
import FLTForHuman.Analysis.Fourier.FundamentalDomainIntegration
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.EisensteinGeneral.Factorization.BoxFourier
import FLTForHuman.NumberTheory.NumberField.StandardAddCharTrace
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
-- `continuous_eA_symm` is imported, not restated (see the header).
import FLTForHuman.AutomorphicForm.Adelic.RightConvDerivatives
-- `AutomorphicForm.μA` is imported, not restated (FR-0274; see the header).
import FLTForHuman.AutomorphicForm.Adelic.HeightWeylMass
import Mathlib.Tactic

set_option autoImplicit false

open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open MeasureTheory NumberField NumberField.AdelicBox NumberField.TateGlobal

namespace AutomorphicForm

noncomputable section

open scoped Classical
open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm Set Filter Topology

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K : Type) [Field K] [NumberField K]

scoped instance finBorel : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) := borel _
scoped instance finBorelSpace : BorelSpace (FiniteAdeleRing (𝓞 K) K) := ⟨rfl⟩

def νf : Measure (FiniteAdeleRing (𝓞 K) K) := Measure.addHaar

scoped instance : (νf K).IsAddHaarMeasure := by unfold νf; infer_instance

abbrev MS := mixedEmbedding.mixedSpace K

def Φ : AdeleRing (𝓞 K) K → MS K × FiniteAdeleRing (𝓞 K) K :=
  fun u => (InfiniteAdeleRing.ringEquiv_mixedSpace K u.1, u.2)

theorem continuous_Φ : Continuous (Φ K) :=
  ((continuous_ringEquiv_mixedSpace K).comp continuous_fst).prodMk continuous_snd

theorem Φ_apply (u : AdeleRing (𝓞 K) K) : Φ K u = (InfiniteAdeleRing.ringEquiv_mixedSpace K u.1, u.2) := rfl

theorem measurable_Φ : Measurable (Φ K) := (continuous_Φ K).measurable

abbrev FD : Set (MS K) := ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis K)
abbrev O : Set (FiniteAdeleRing (𝓞 K) K) := integralFiniteAdeles (𝓞 K) K

theorem adelicBox_eq_preimage : adelicBox K = Φ K ⁻¹' (FD K ×ˢ O K) := by
  ext u; rfl

theorem measurableSet_FD : MeasurableSet (FD K) := ZSpan.fundamentalDomain_measurableSet _
theorem measurableSet_O : MeasurableSet (O K) := (isClosed_integralFiniteAdeles K).measurableSet

theorem volume_FD_lt_top : volume (FD K) < ⊤ :=
  (ZSpan.fundamentalDomain_isBounded (mixedEmbedding.latticeBasis K)).measure_lt_top
theorem νf_O_lt_top : νf K (O K) < ⊤ := (isCompact_integralFiniteAdeles K).measure_lt_top
theorem νf_O_pos : 0 < νf K (O K) :=
  (isOpen_integralFiniteAdeles K).measure_pos _ ⟨0, fun _ => zero_mem _⟩

theorem μA_box_lt_top : μA K (adelicBox K) < ⊤ := adelicAddHaar_adelicBox_lt_top K
theorem μA_box_pos : 0 < μA K (adelicBox K) := adelicAddHaar_adelicBox_pos K

def μ' : Measure (MS K × FiniteAdeleRing (𝓞 K) K) := ((μA K).restrict (adelicBox K)).map (Φ K)

scoped instance : IsFiniteMeasure (μ' K) := by
  unfold μ'
  have : IsFiniteMeasure ((μA K).restrict (adelicBox K)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact μA_box_lt_top K⟩
  exact Measure.isFiniteMeasure_map _ _

theorem μ'_prod (s : Set (MS K)) (t : Set (FiniteAdeleRing (𝓞 K) K)) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ' K (s ×ˢ t) = μA K (Φ K ⁻¹' ((s ∩ FD K) ×ˢ (t ∩ O K))) := by
  rw [μ', Measure.map_apply (measurable_Φ K) (hs.prod ht), Measure.restrict_apply ((hs.prod ht).preimage (measurable_Φ K)),
    adelicBox_eq_preimage, ← Set.preimage_inter, Set.prod_inter_prod]

def κ : ℝ := (2 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces K / Real.sqrt |(discr K : ℝ)|

theorem κ_pos : 0 < κ K := by
  unfold κ
  refine div_pos (pow_pos two_pos _) (Real.sqrt_pos.mpr (abs_pos.mpr ?_))
  exact_mod_cast discr_ne_zero K

theorem integral_indicator_one_complex {X : Type*} [MeasurableSpace X] (μ : Measure X) {s : Set X}
    (hs : MeasurableSet s) : ∫ x, s.indicator (1 : X → ℂ) x ∂μ = ((μ s).toReal : ℂ) := by
  rw [integral_indicator hs]
  simp only [Pi.one_apply]
  rw [setIntegral_const, Complex.real_smul, mul_one]
  rfl

theorem μ'_prod_real (s : Set (MS K)) (t : Set (FiniteAdeleRing (𝓞 K) K)) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ' K (s ×ˢ t)).toReal =
      (μA K (adelicBox K)).toReal * κ K * (νf K (O K)).toReal⁻¹ * (volume (s ∩ FD K)).toReal * (νf K (t ∩ O K)).toReal := by
  have : Measure.IsAddHaarMeasure (μA K) := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have key := EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq K (μA K) (νf K)
    (1 : AddChar (AdeleRing (𝓞 K) K) ℂ) ((s ∩ FD K).indicator 1) ((t ∩ O K).indicator 1) 0

  have hP : MeasurableSet (Φ K ⁻¹' ((s ∩ FD K) ×ˢ (t ∩ O K))) :=
    ((hs.inter (measurableSet_FD K)).prod (ht.inter (measurableSet_O K))).preimage (measurable_Φ K)
  have h1 : NumberField.AdelicFourier.fourierIntegral (1 : AddChar (AdeleRing (𝓞 K) K) ℂ) (μA K)
      (fun x => (s ∩ FD K).indicator 1 (InfiniteAdeleRing.ringEquiv_mixedSpace K x.1) * (t ∩ O K).indicator 1 x.2) 0 =
      ((μA K (Φ K ⁻¹' ((s ∩ FD K) ×ˢ (t ∩ O K)))).toReal : ℂ) := by
    rw [NumberField.AdelicFourier.fourierIntegral_def]
    have hfun : (fun v : AdeleRing (𝓞 K) K => (1 : AddChar (AdeleRing (𝓞 K) K) ℂ) (-(v * 0)) *
        ((s ∩ FD K).indicator (1 : MS K → ℂ) (InfiniteAdeleRing.ringEquiv_mixedSpace K v.1) *
          (t ∩ O K).indicator (1 : FiniteAdeleRing (𝓞 K) K → ℂ) v.2)) =
        (Φ K ⁻¹' ((s ∩ FD K) ×ˢ (t ∩ O K))).indicator 1 := by
      funext v
      rw [AddChar.one_apply, one_mul]
      by_cases h₁ : InfiniteAdeleRing.ringEquiv_mixedSpace K v.1 ∈ s ∩ FD K
      · by_cases h₂ : v.2 ∈ t ∩ O K
        · rw [Set.indicator_of_mem h₁, Set.indicator_of_mem h₂,
            Set.indicator_of_mem (Set.mem_preimage.mpr (Set.mk_mem_prod h₁ h₂) : v ∈ Φ K ⁻¹' ((s ∩ FD K) ×ˢ (t ∩ O K)))]
          simp
        · rw [Set.indicator_of_notMem h₂, Set.indicator_of_notMem (show v ∉ Φ K ⁻¹' ((s ∩ FD K) ×ˢ (t ∩ O K)) from
            fun h => h₂ h.2)]
          simp
      · rw [Set.indicator_of_notMem h₁, Set.indicator_of_notMem (show v ∉ Φ K ⁻¹' ((s ∩ FD K) ×ˢ (t ∩ O K)) from
            fun h => h₁ h.1)]
        simp
    rw [hfun, integral_indicator_one_complex _ hP]
  have h2 : NumberField.AdelicFourier.fourierIntegral
      ((1 : AddChar (AdeleRing (𝓞 K) K) ℂ).compAddMonoidHom ((AddMonoidHom.inl _ _).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toAddMonoidHom)) volume ((s ∩ FD K).indicator 1)
      (InfiniteAdeleRing.ringEquiv_mixedSpace K (0 : AdeleRing (𝓞 K) K).1) = ((volume (s ∩ FD K)).toReal : ℂ) := by
    have hpt : ∀ v : MS K,
        ((1 : AddChar (AdeleRing (𝓞 K) K) ℂ).compAddMonoidHom ((AddMonoidHom.inl _ _).comp
          (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toAddMonoidHom))
          (-(v * InfiniteAdeleRing.ringEquiv_mixedSpace K (0 : AdeleRing (𝓞 K) K).1)) = 1 := by
      intro v
      show (1 : AddChar (AdeleRing (𝓞 K) K) ℂ) (((AddMonoidHom.inl _ _).comp
          (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toAddMonoidHom)
            (-(v * InfiniteAdeleRing.ringEquiv_mixedSpace K (0 : AdeleRing (𝓞 K) K).1))) = 1
      rfl
    rw [NumberField.AdelicFourier.fourierIntegral_def]
    simp only [hpt, one_mul]
    exact integral_indicator_one_complex _ (hs.inter (measurableSet_FD K))
  have h3 : NumberField.AdelicFourier.fourierIntegral ((1 : AddChar (AdeleRing (𝓞 K) K) ℂ).compAddMonoidHom (AddMonoidHom.inr _ _))
      (νf K) ((t ∩ O K).indicator 1) (0 : AdeleRing (𝓞 K) K).2 = ((νf K (t ∩ O K)).toReal : ℂ) := by
    have hpt : ∀ v : FiniteAdeleRing (𝓞 K) K,
        ((1 : AddChar (AdeleRing (𝓞 K) K) ℂ).compAddMonoidHom (AddMonoidHom.inr _ _))
          (-(v * (0 : AdeleRing (𝓞 K) K).2)) = 1 := by
      intro v
      show (1 : AddChar (AdeleRing (𝓞 K) K) ℂ) ((AddMonoidHom.inr _ _)
        (-(v * (0 : AdeleRing (𝓞 K) K).2))) = 1
      rfl
    rw [NumberField.AdelicFourier.fourierIntegral_def]
    simp only [hpt, one_mul]
    exact integral_indicator_one_complex _ (ht.inter (measurableSet_O K))
  rw [h1, h2, h3] at key
  rw [μ'_prod K s t hs ht]

  have hB : ((μA K (adelicBox K)).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos (μA_box_pos K).ne' (μA_box_lt_top K).ne).ne'
  have key' := congrArg (fun z : ℂ => ((μA K (adelicBox K)).toReal : ℂ) * z) key
  simp only [← mul_assoc, mul_inv_cancel₀ hB, one_mul] at key'
  apply Complex.ofReal_injective
  rw [key']
  unfold κ
  push_cast
  ring

def Cst : ℝ := (μA K (adelicBox K)).toReal * κ K * (νf K (O K)).toReal⁻¹

theorem Cst_pos : 0 < Cst K := by
  unfold Cst
  refine mul_pos (mul_pos (ENNReal.toReal_pos (μA_box_pos K).ne' (μA_box_lt_top K).ne) (κ_pos K))
    (inv_pos.mpr (ENNReal.toReal_pos (νf_O_pos K).ne' (νf_O_lt_top K).ne))

def P : Measure (MS K × FiniteAdeleRing (𝓞 K) K) := (volume.restrict (FD K)).prod ((νf K).restrict (O K))

scoped instance : IsFiniteMeasure ((volume : Measure (MS K)).restrict (FD K)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact volume_FD_lt_top K⟩
scoped instance : IsFiniteMeasure ((νf K).restrict (O K)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact νf_O_lt_top K⟩
scoped instance : IsFiniteMeasure (P K) := by unfold P; infer_instance

theorem μ'_eq : μ' K = ENNReal.ofReal (Cst K) • P K := by
  have hC : ENNReal.ofReal (Cst K) ≠ 0 := by simpa using Cst_pos K
  have hprod : P K = (ENNReal.ofReal (Cst K))⁻¹ • μ' K := by
    unfold P
    refine Measure.prod_eq fun s t hs ht => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs, Measure.restrict_apply ht]
    have hfinμ : μ' K (s ×ˢ t) ≠ ⊤ := measure_ne_top _ _
    have hfins : volume (s ∩ FD K) ≠ ⊤ := (measure_mono Set.inter_subset_right).trans_lt (volume_FD_lt_top K) |>.ne
    have hfint : νf K (t ∩ O K) ≠ ⊤ := (measure_mono Set.inter_subset_right).trans_lt (νf_O_lt_top K) |>.ne
    rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hC) hfinμ)
      (ENNReal.mul_ne_top hfins hfint), ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (Cst_pos K).le, μ'_prod_real K s t hs ht]
    unfold Cst
    have h1 : (μA K (adelicBox K)).toReal ≠ 0 := (ENNReal.toReal_pos (μA_box_pos K).ne' (μA_box_lt_top K).ne).ne'
    have h2 : κ K ≠ 0 := (κ_pos K).ne'
    have h3 : (νf K (O K)).toReal ≠ 0 := (ENNReal.toReal_pos (νf_O_pos K).ne' (νf_O_lt_top K).ne).ne'
    field_simp
  rw [hprod, smul_smul, ENNReal.mul_inv_cancel hC ENNReal.ofReal_ne_top, one_smul]

theorem setIntegral_box_eq (G : MS K × FiniteAdeleRing (𝓞 K) K → ℂ) (hG : Continuous G) :
    ∫ u in adelicBox K, G (Φ K u) ∂(μA K) =
      Cst K * ∫ z in FD K, ∫ uf in O K, G (z, uf) ∂(νf K) ∂volume := by

  have h1 : ∫ u in adelicBox K, G (Φ K u) ∂(μA K) = ∫ p, G p ∂(μ' K) := by
    rw [μ', integral_map (measurable_Φ K).aemeasurable hG.aestronglyMeasurable]

  have hint : Integrable G (P K) := by
    have hcpt : IsCompact (closure (FD K) ×ˢ O K) :=
      (ZSpan.fundamentalDomain_isBounded _).isCompact_closure.prod (isCompact_integralFiniteAdeles K)
    obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn hG.continuousOn
    have hz1 : (volume.restrict (FD K)) ((closure (FD K))ᶜ) = 0 := by
      rw [Measure.restrict_apply isClosed_closure.measurableSet.compl]
      have : (closure (FD K))ᶜ ∩ FD K = ∅ := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_and]
        exact fun h hp => h (subset_closure hp)
      rw [this, measure_empty]
    have hz2 : ((νf K).restrict (O K)) ((O K)ᶜ) = 0 := by
      rw [Measure.restrict_apply (measurableSet_O K).compl, Set.compl_inter_self, measure_empty]
    have h0 : P K ((closure (FD K) ×ˢ O K)ᶜ) = 0 := by
      refine le_antisymm ?_ bot_le
      calc P K ((closure (FD K) ×ˢ O K)ᶜ)
          ≤ P K ((closure (FD K))ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (O K)ᶜ) := by
            refine measure_mono fun p hp => ?_
            simp only [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hp
            rcases hp with h | h
            · exact Or.inl ⟨h, Set.mem_univ _⟩
            · exact Or.inr ⟨Set.mem_univ _, h⟩
        _ ≤ P K ((closure (FD K))ᶜ ×ˢ Set.univ) + P K (Set.univ ×ˢ (O K)ᶜ) := measure_union_le _ _
        _ = 0 := by rw [P, Measure.prod_prod, Measure.prod_prod, hz1, hz2, zero_mul, mul_zero, add_zero]
    have hae : ∀ᵐ p ∂(P K), p ∈ closure (FD K) ×ˢ O K := by
      have := (measure_eq_zero_iff_ae_notMem.mp h0)
      exact this.mono fun p hp => not_not.mp hp
    exact (integrable_const M).mono' hG.aestronglyMeasurable (hae.mono fun p hp => hM p hp)
  rw [h1, μ'_eq, integral_smul_measure, ENNReal.toReal_ofReal (Cst_pos K).le, P, integral_prod _ hint]
  rfl

abbrev eA := InfiniteAdeleRing.ringEquiv_mixedSpace K

set_option linter.unusedSectionVars false in
theorem eA_symm_apply_of_isReal (z : MS K) {w : InfinitePlace K} (hw : w.IsReal) :
    (eA K).symm z w = (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm (z.1 ⟨w, hw⟩) := by
  have hy : eA K ((eA K).symm z) = z := RingEquiv.apply_symm_apply _ _
  have h1 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((eA K).symm z w) = z.1 ⟨w, hw⟩ :=
    congrArg (fun p : MS K => p.1 ⟨w, hw⟩) hy
  apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).injective
  rw [IsometryEquiv.apply_symm_apply]
  exact h1

set_option linter.unusedSectionVars false in
theorem eA_symm_apply_of_isComplex (z : MS K) {w : InfinitePlace K} (hw : w.IsComplex) :
    (eA K).symm z w = (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm (z.2 ⟨w, hw⟩) := by
  have hy : eA K ((eA K).symm z) = z := RingEquiv.apply_symm_apply _ _
  have h1 : InfinitePlace.Completion.extensionEmbedding w ((eA K).symm z w) = z.2 ⟨w, hw⟩ :=
    congrArg (fun p : MS K => p.2 ⟨w, hw⟩) hy
  apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).injective
  rw [IsometryEquiv.apply_symm_apply]
  exact h1

def pr (p : MS K × FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K := ((eA K).symm p.1, p.2)

theorem continuous_pr : Continuous (pr K) :=
  ((AutomorphicForm.LocalIntertwining.UnipDeriv.continuous_eA_symm K).comp continuous_fst).prodMk continuous_snd

theorem pr_Φ (u : AdeleRing (𝓞 K) K) : pr K (Φ K u) = u := by
  simp only [pr, Φ_apply, RingEquiv.symm_apply_apply]
  rfl

abbrev ψ : AddChar (AdeleRing (𝓞 K) K) ℂ := NumberField.StandardAddChar.stdAddChar K

theorem continuous_ψ : Continuous (ψ K) := (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK

theorem ψ_algebraMap (β : K) : ψ K (algebraMap K (AdeleRing (𝓞 K) K) β) = 1 :=
  (NumberField.StandardAddChar.adelicTraceData K).psiK_algebraMap β

theorem pair_eq_add (a : InfiniteAdeleRing K) (b : FiniteAdeleRing (𝓞 K) K) :
    ((a, b) : AdeleRing (𝓞 K) K) = ((a, (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K) +
      (((0 : InfiniteAdeleRing K), b) : AdeleRing (𝓞 K) K) := by
  refine Prod.ext ?_ ?_
  · show a = a + 0; rw [add_zero]
  · show b = 0 + b; rw [zero_add]

theorem ψ_neg_pair (a : InfiniteAdeleRing K) (b : FiniteAdeleRing (𝓞 K) K) :
    ψ K (-((a, b) : AdeleRing (𝓞 K) K)) =
      ψ K (-((a, (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)) *
        ψ K (-(((0 : InfiniteAdeleRing K), b) : AdeleRing (𝓞 K) K)) := by
  rw [pair_eq_add K a b, neg_add]
  exact AddChar.map_add_eq_mul _ _ _

def ℓ : MS K →L[ℝ] ℝ := -LinearMap.toContinuousLinearMap (Algebra.trace ℝ (MS K))

theorem ℓ_apply (z : MS K) : ℓ K z = -Algebra.trace ℝ (MS K) z := rfl

theorem ψ_neg_arch (z : MS K) :
    ψ K (-(((eA K).symm z, (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)) =
      Complex.exp (2 * Real.pi * Complex.I * ℓ K z) := by
  have hneg : (-(((eA K).symm z, (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)) =
      (((eA K).symm (-z), (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K) := by
    refine Prod.ext ?_ ?_
    · show -((eA K).symm z) = (eA K).symm (-z); rw [map_neg]
    · show -(0 : FiniteAdeleRing (𝓞 K) K) = 0; rw [neg_zero]
  rw [hneg]
  have h := NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace K ((eA K).symm (-z))
  rw [RingEquiv.apply_symm_apply] at h
  rw [show ψ K = NumberField.StandardAddChar.stdAddChar K from rfl, h, Real.fourierChar_apply, ℓ_apply, map_neg]
  congr 1
  push_cast
  ring

theorem ℓ_ne_zero_of {v : MS K}
    (hv : ∃ t : ℝ, ψ K (((eA K).symm (t • v), (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K) ≠ 1) :
    ℓ K v ≠ 0 := by
  obtain ⟨t, ht⟩ := hv
  intro h0
  apply ht
  have h1 := ψ_neg_arch K (-(t • v))
  have hneg : (-(((eA K).symm (-(t • v)), (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)) =
      (((eA K).symm (t • v), (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K) := by
    refine Prod.ext ?_ ?_
    · show -((eA K).symm (-(t • v))) = (eA K).symm (t • v); rw [map_neg, neg_neg]
    · show -(0 : FiniteAdeleRing (𝓞 K) K) = 0; rw [neg_zero]
  rw [hneg] at h1
  rw [h1, map_neg, map_smul, smul_eq_mul, h0, mul_zero, neg_zero]
  simp

section Inner

variable (xs : ℕ → AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K)

def inner (j : ℕ) (z : MS K) : ℂ :=
  ∫ uf in O K, xs j (unipotentGL2 (pr K (z, uf)) * g) *
    ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K)) ∂νf K

variable {xs}

theorem continuous_integrand2 (hxs : ∀ j, Continuous (xs j)) (j : ℕ) :
    Continuous fun p : MS K × FiniteAdeleRing (𝓞 K) K =>
      xs j (unipotentGL2 (pr K p) * g) * ψ K (-(((0 : InfiniteAdeleRing K), p.2) : AdeleRing (𝓞 K) K)) := by
  have h1 : Continuous fun p : MS K × FiniteAdeleRing (𝓞 K) K => xs j (unipotentGL2 (pr K p) * g) :=
    (hxs j).comp (((continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)).comp (continuous_pr K)).mul continuous_const)
  have h2 : Continuous fun p : MS K × FiniteAdeleRing (𝓞 K) K =>
      ψ K (-(((0 : InfiniteAdeleRing K), p.2) : AdeleRing (𝓞 K) K)) := by
    have hc : Continuous fun p : MS K × FiniteAdeleRing (𝓞 K) K => ((((0 : InfiniteAdeleRing K), p.2)) : AdeleRing (𝓞 K) K) :=
      (continuous_const.prodMk continuous_snd : Continuous fun p : MS K × FiniteAdeleRing (𝓞 K) K =>
        ((0 : InfiniteAdeleRing K), p.2))
    exact (continuous_ψ K).comp hc.neg
  exact h1.mul h2

theorem continuous_inner (hxs : ∀ j, Continuous (xs j)) (j : ℕ) : Continuous (inner K xs g j) := by
  have := continuous_parametric_integral_of_continuous (μ := νf K)
    (f := fun (z : MS K) (uf : FiniteAdeleRing (𝓞 K) K) =>
      xs j (unipotentGL2 (pr K (z, uf)) * g) * ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K)))
    (continuous_integrand2 K g hxs j) (isCompact_integralFiniteAdeles K)
  exact this

theorem norm_inner_le (hxs : ∀ j, Continuous (xs j)) (j : ℕ) {A : ℝ}
    (hA : ∀ u : AdeleRing (𝓞 K) K, ‖xs j (unipotentGL2 u * g)‖ ≤ A) (z : MS K) :
    ‖inner K xs g j z‖ ≤ A * ∫ uf in O K, ‖ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K))‖ ∂νf K := by
  unfold inner
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine setIntegral_mono_on ?_ ?_ (measurableSet_O K) fun uf _ => ?_
  · exact ((continuous_integrand2 K g hxs j).comp (Continuous.prodMk_right z)).norm.continuousOn.integrableOn_compact
      (isCompact_integralFiniteAdeles K)
  · refine Integrable.const_mul ?_ A
    have hc : Continuous fun uf : FiniteAdeleRing (𝓞 K) K => ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K)) :=
      (continuous_ψ K).comp ((continuous_const.prodMk continuous_id : Continuous fun uf : FiniteAdeleRing (𝓞 K) K =>
        ((0 : InfiniteAdeleRing K), uf))).neg
    exact hc.norm.continuousOn.integrableOn_compact (isCompact_integralFiniteAdeles K)
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA _) (norm_nonneg _)

theorem hasDerivAt_inner (hxs : ∀ j, Continuous (xs j)) (v : MS K)
    (horb : ∀ (j : ℕ) (u : AdeleRing (𝓞 K) K),
      HasDerivAt (fun t : ℝ => xs j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) * (unipotentGL2 u * g)))
        (xs (j + 1) (unipotentGL2 u * g)) 0)
    (j : ℕ) (z : MS K) :
    HasDerivAt (fun t : ℝ => inner K xs g j (z + t • v)) (inner K xs g (j + 1) z) 0 := by

  set F : ℝ → FiniteAdeleRing (𝓞 K) K → ℂ := fun t uf =>
    xs j (unipotentGL2 (pr K (z + t • v, uf)) * g) * ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K)) with hF
  set F' : ℝ → FiniteAdeleRing (𝓞 K) K → ℂ := fun t uf =>
    xs (j + 1) (unipotentGL2 (pr K (z + t • v, uf)) * g) * ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K)) with hF'

  have hderiv : ∀ (uf : FiniteAdeleRing (𝓞 K) K) (t : ℝ), HasDerivAt (fun s => F s uf) (F' t uf) t := by
    intro uf t
    have key : ∀ s : ℝ, unipotentGL2 (pr K (z + s • v, uf)) =
        unipotentGL2 (R := AdeleRing (𝓞 K) K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm ((s + -t) • v), 0) *
          unipotentGL2 (pr K (z + t • v, uf)) := by
      intro s
      set hp1 : AdeleRing (𝓞 K) K := ((eA K).symm ((s + -t) • v), (0 : FiniteAdeleRing (𝓞 K) K)) with hph1
      set hp2 : AdeleRing (𝓞 K) K := ((eA K).symm (z + t • v), uf) with hph2
      have harg : pr K (z + s • v, uf) = hp1 + hp2 := by
        rw [hph1, hph2]
        refine Prod.ext ?_ ?_
        · show (eA K).symm (z + s • v) = (eA K).symm ((s + -t) • v) + (eA K).symm (z + t • v)
          rw [← map_add]; congr 1; rw [add_smul, neg_smul]; abel
        · show uf = (0 : FiniteAdeleRing (𝓞 K) K) + uf; rw [zero_add]
      rw [harg, unipotentGL2_add]
      rw [hph1, hph2]
      rfl
    have h0 : HasDerivAt (fun t' : ℝ => xs j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t' • v), 0) * (unipotentGL2 (pr K (z + t • v, uf)) * g)))
        (xs (j + 1) (unipotentGL2 (pr K (z + t • v, uf)) * g)) (t + -t) := by
      rw [add_neg_cancel]; exact horb j (pr K (z + t • v, uf))
    have h1' := h0.comp_add_const t (-t)
    have h2 : HasDerivAt (fun s : ℝ => xs j (unipotentGL2 (pr K (z + s • v, uf)) * g))
        (xs (j + 1) (unipotentGL2 (pr K (z + t • v, uf)) * g)) t := by
      refine h1'.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
      show xs j (unipotentGL2 (pr K (z + s • v, uf)) * g) = _
      rw [key s, mul_assoc]
    exact h2.mul_const _

  have hF'cont : Continuous fun p : ℝ × FiniteAdeleRing (𝓞 K) K => F' p.1 p.2 :=
    (continuous_integrand2 K g hxs (j + 1)).comp
      ((continuous_const.add (continuous_fst.smul continuous_const)).prodMk continuous_snd)
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : ℝ) 1).prod (isCompact_integralFiniteAdeles K)).exists_bound_of_continuousOn
    hF'cont.continuousOn
  have hFt : ∀ t : ℝ, Continuous (F t) := fun t =>
    (continuous_integrand2 K g hxs j).comp (continuous_const.prodMk continuous_id)
  have hF't : ∀ t : ℝ, Continuous (F' t) := fun t =>
    (continuous_integrand2 K g hxs (j + 1)).comp (continuous_const.prodMk continuous_id)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (νf K).restrict (O K)) (x₀ := (0 : ℝ))
    (F := F) (F' := F') (bound := fun _ => B) (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds 0 zero_lt_one)
    (Eventually.of_forall fun t => (hFt t).aestronglyMeasurable)
    ((hFt 0).continuousOn.integrableOn_compact (isCompact_integralFiniteAdeles K))
    (hF't 0).aestronglyMeasurable
    ((ae_restrict_mem (measurableSet_O K)).mono fun uf huf t ht => hB (t, uf) ⟨Metric.ball_subset_closedBall ht, huf⟩)
    (integrableOn_const (νf_O_lt_top K).ne)
    (Eventually.of_forall fun uf t _ => hderiv uf t)
  have e2 : (∫ uf in O K, F' 0 uf ∂νf K) = inner K xs g (j + 1) z := by
    simp only [hF', zero_smul, add_zero]
    rfl
  rw [← e2]
  exact key.2

end Inner

section Periodic

variable {xs : ℕ → AdelicGL2 (𝓞 K) K → ℂ} (g : AdelicGL2 (𝓞 K) K)

theorem O_add_mem_iff {β : FiniteAdeleRing (𝓞 K) K} (hβ : β ∈ O K) (x : FiniteAdeleRing (𝓞 K) K) :
    β + x ∈ O K ↔ x ∈ O K := by
  constructor
  · intro h v
    have := sub_mem (h v) (hβ v)
    rwa [show (β + x) v - β v = x v from by rw [NumberField.AdelicLevel.coe_add_apply]; ring] at this
  · intro h v
    rw [NumberField.AdelicLevel.coe_add_apply]
    exact add_mem (hβ v) (h v)

theorem algebraMap_integer_mem_O (b : 𝓞 K) : algebraMap K (FiniteAdeleRing (𝓞 K) K) (b : K) ∈ O K := fun v =>
  NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers v b

theorem inner_sub_integer (j : ℕ) (z : MS K) (b : 𝓞 K) :
    ∫ uf in O K, xs j (unipotentGL2 (pr K (z, uf - algebraMap K (FiniteAdeleRing (𝓞 K) K) (b : K))) * g) *
        ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K)) ∂νf K =
      ψ K (-(((0 : InfiniteAdeleRing K), algebraMap K (FiniteAdeleRing (𝓞 K) K) (b : K)) : AdeleRing (𝓞 K) K)) *
        inner K xs g j z := by
  set βf := algebraMap K (FiniteAdeleRing (𝓞 K) K) (b : K) with hβf
  have hβO : βf ∈ O K := algebraMap_integer_mem_O K b
  have hT : MeasurePreserving (fun x : FiniteAdeleRing (𝓞 K) K => βf + x) (νf K) (νf K) := measurePreserving_add_left (νf K) βf
  have hTe : MeasurableEmbedding (fun x : FiniteAdeleRing (𝓞 K) K => βf + x) := measurableEmbedding_addLeft βf
  have hpre : (fun x : FiniteAdeleRing (𝓞 K) K => βf + x) ⁻¹' O K = O K := by
    ext x; exact O_add_mem_iff K hβO x
  have key := hT.setIntegral_preimage_emb hTe
    (fun y => xs j (unipotentGL2 (pr K (z, y - βf)) * g) * ψ K (-(((0 : InfiniteAdeleRing K), y) : AdeleRing (𝓞 K) K))) (O K)
  rw [hpre] at key
  rw [← key]
  simp only [add_sub_cancel_left]
  rw [inner, ← integral_const_mul]
  refine setIntegral_congr_fun (measurableSet_O K) fun x _ => ?_
  have hsplit : ((((0 : InfiniteAdeleRing K), βf + x)) : AdeleRing (𝓞 K) K) =
      (((0 : InfiniteAdeleRing K), βf) : AdeleRing (𝓞 K) K) + (((0 : InfiniteAdeleRing K), x) : AdeleRing (𝓞 K) K) := by
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing K) = 0 + 0; rw [add_zero]
    · rfl
  have hmul : ψ K (-((((0 : InfiniteAdeleRing K), βf + x)) : AdeleRing (𝓞 K) K)) =
      ψ K (-(((0 : InfiniteAdeleRing K), βf) : AdeleRing (𝓞 K) K)) * ψ K (-(((0 : InfiniteAdeleRing K), x) : AdeleRing (𝓞 K) K)) := by
    rw [hsplit, neg_add]
    exact AddChar.map_add_eq_mul _ _ _
  rw [hmul]
  ring

theorem periodic
    (hinv : ∀ (j : ℕ) (β : K) (h : AdelicGL2 (𝓞 K) K),
      xs j (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = xs j h)
    (j : ℕ) (z : MS K) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 K)) :
    Complex.exp (2 * Real.pi * Complex.I * ℓ K (z + mixedEmbedding.latticeBasis K i)) * inner K xs g j (z + mixedEmbedding.latticeBasis K i) =
      Complex.exp (2 * Real.pi * Complex.I * ℓ K z) * inner K xs g j z := by
  set b : 𝓞 K := RingOfIntegers.basis K i with hb
  have hβ : integralBasis K i = (b : K) := by rw [integralBasis_apply]
  set βa := algebraMap K (InfiniteAdeleRing K) (b : K) with hβa
  set βf := algebraMap K (FiniteAdeleRing (𝓞 K) K) (b : K) with hβf
  have hbi : (eA K).symm (mixedEmbedding.latticeBasis K i) = βa := by
    rw [mixedEmbedding.latticeBasis_apply, hβ, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      RingEquiv.symm_apply_apply]

  have hchr : Complex.exp (2 * Real.pi * Complex.I * ℓ K (z + mixedEmbedding.latticeBasis K i)) =
      Complex.exp (2 * Real.pi * Complex.I * ℓ K z) *
        ψ K (-((βa, (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)) := by
    rw [← hbi, ψ_neg_arch, ← Complex.exp_add, map_add]
    push_cast
    ring_nf

  have hinner : inner K xs g j (z + mixedEmbedding.latticeBasis K i) =
      ψ K (-(((0 : InfiniteAdeleRing K), βf) : AdeleRing (𝓞 K) K)) * inner K xs g j z := by
    rw [← inner_sub_integer K g j z b, inner]
    refine setIntegral_congr_fun (measurableSet_O K) fun uf _ => ?_
    have hsplit : pr K (z + mixedEmbedding.latticeBasis K i, uf) =
        algebraMap K (AdeleRing (𝓞 K) K) (b : K) + pr K (z, uf - βf) := by
      refine Prod.ext ?_ ?_
      · show (eA K).symm (z + mixedEmbedding.latticeBasis K i) = βa + (eA K).symm z
        rw [map_add, hbi, add_comm]
      · show uf = βf + (uf - βf)
        rw [add_sub_cancel]
    rw [hsplit, unipotentGL2_add, mul_assoc, hinv]
  rw [hchr, hinner]
  have hprod : ψ K (-((βa, (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)) *
      ψ K (-(((0 : InfiniteAdeleRing K), βf) : AdeleRing (𝓞 K) K)) = 1 := by
    rw [← ψ_neg_pair]
    have : ((βa, βf) : AdeleRing (𝓞 K) K) = algebraMap K (AdeleRing (𝓞 K) K) (b : K) := rfl
    rw [this]
    exact (congrArg (ψ K) (map_neg (algebraMap K (AdeleRing (𝓞 K) K)) (b : K)).symm).trans (ψ_algebraMap K _)
  linear_combination (Complex.exp (2 * Real.pi * Complex.I * ℓ K z) * inner K xs g j z) * hprod

end Periodic

end

theorem exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (M : ℕ) (v : mixedEmbedding.mixedSpace K)
    (hv : ∃ t : ℝ, NumberField.StandardAddChar.stdAddChar K
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) ≠ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (xs : ℕ → AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (A : ℝ),
        (∀ j : ℕ, Continuous (xs j)) →
        (∀ (j : ℕ) (β : K) (h : AdelicGL2 (𝓞 K) K),
          xs j (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = xs j h) →
        (∀ (j : ℕ) (u : AdeleRing (𝓞 K) K),
          HasDerivAt (fun t : ℝ => xs j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
              ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0) * (unipotentGL2 u * g)))
            (xs (j + 1) (unipotentGL2 u * g)) 0) →
        (∀ u : AdeleRing (𝓞 K) K, ‖xs M (unipotentGL2 u * g)‖ ≤ A) →
        ‖whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (xs 0) 1 g‖ ≤ c * A := by
  classical
  let : MeasurableSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.adeleBorel (𝓞 K) K
  have : BorelSpace (AdeleRing (𝓞 K) K) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  have : Measure.IsAddHaarMeasure (μA K) := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hℓ : ℓ K v ≠ 0 := ℓ_ne_zero_of K hv

  set cψ : ℝ := ∫ uf in O K, ‖ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K))‖ ∂νf K with hcψ
  have hcψ0 : 0 ≤ cψ := integral_nonneg fun _ => norm_nonneg _
  set cK : ℝ := (μA K (adelicBox K)).toReal⁻¹ * Cst K * ((2 * Real.pi * |ℓ K v|)⁻¹) ^ M *
    ((volume (FD K)).toReal * cψ) with hcK
  have hcK0 : 0 ≤ cK := by
    have h1 : 0 ≤ (μA K (adelicBox K)).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    have h2 : 0 ≤ ((2 * Real.pi * |ℓ K v|)⁻¹) ^ M := pow_nonneg (inv_nonneg.mpr (by positivity)) M
    have h3 : 0 ≤ (volume (FD K)).toReal * cψ := mul_nonneg ENNReal.toReal_nonneg hcψ0
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 (Cst_pos K).le) h2) h3
  refine ⟨cK + 1, by linarith, fun xs g A hxs hinv horb hA => ?_⟩
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)

  have hW : whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (xs 0) 1 g =
      ((μA K (adelicBox K))⁻¹).toReal • ∫ u in adelicBox K, xs 0 (unipotentGL2 u * g) * ψ K (-u) ∂(μA K) := by
    show (∫ u, xs 0 (unipotentGL2 u * g) * ψ K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * u))
      ∂(ProbabilityTheory.cond (μA K) (adelicBox K))) = _
    rw [ProbabilityTheory.cond, integral_smul_measure]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show xs 0 (unipotentGL2 u * g) * ψ K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * u)) = xs 0 (unipotentGL2 u * g) * ψ K (-u)
    rw [map_one, one_mul]

  have hG : Continuous fun p : MS K × FiniteAdeleRing (𝓞 K) K => xs 0 (unipotentGL2 (pr K p) * g) * ψ K (-(pr K p)) :=
    ((hxs 0).comp (((continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)).comp (continuous_pr K)).mul continuous_const)).mul
      ((continuous_ψ K).comp (continuous_pr K).neg)
  have hbox : ∫ u in adelicBox K, xs 0 (unipotentGL2 u * g) * ψ K (-u) ∂(μA K) =
      Cst K * ∫ z in FD K, Complex.exp (2 * Real.pi * Complex.I * ℓ K z) * inner K xs g 0 z ∂volume := by
    have h := setIntegral_box_eq K (fun p => xs 0 (unipotentGL2 (pr K p) * g) * ψ K (-(pr K p))) hG
    simp only [pr_Φ] at h
    rw [h]
    congr 1
    refine setIntegral_congr_fun (measurableSet_FD K) fun z _ => ?_
    have hz : ∀ uf : FiniteAdeleRing (𝓞 K) K, ψ K (-(pr K (z, uf))) =
        Complex.exp (2 * Real.pi * Complex.I * ℓ K z) * ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K)) := by
      intro uf
      have e1 : ψ K (-(pr K (z, uf))) = ψ K (-(((eA K).symm z, (0 : FiniteAdeleRing (𝓞 K) K)) : AdeleRing (𝓞 K) K)) *
          ψ K (-(((0 : InfiniteAdeleRing K), uf) : AdeleRing (𝓞 K) K)) := ψ_neg_pair K _ _
      exact e1.trans (congrArg (· * _) (ψ_neg_arch K z))
    simp_rw [hz]
    rw [inner, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_O K) fun uf _ => ?_
    ring

  have hC4 := ZSpan.norm_setIntegral_fundamentalDomain_cexp_mul_le_inv_pow_mul_setIntegral_norm_of_hasDerivAt
    (mixedEmbedding.latticeBasis K) volume (ℓ K) v hℓ (fun j => inner K xs g j) (fun j => continuous_inner K g hxs j)
    (fun j z => hasDerivAt_inner K g hxs v horb j z) (fun j z i => periodic K g hinv j z i) M

  have hIM : ∫ z in FD K, ‖inner K xs g M z‖ ∂volume ≤ A * cψ * (volume (FD K)).toReal := by
    have hle : ∀ z, ‖inner K xs g M z‖ ≤ A * cψ := fun z => norm_inner_le K g hxs M hA z
    calc ∫ z in FD K, ‖inner K xs g M z‖ ∂volume ≤ ∫ z in FD K, A * cψ ∂volume := by
          refine setIntegral_mono_on ?_ (integrableOn_const (volume_FD_lt_top K).ne) (measurableSet_FD K) fun z _ => hle z
          exact ((continuous_inner K g hxs M).norm.continuousOn.integrableOn_compact
            (ZSpan.fundamentalDomain_isBounded _).isCompact_closure).mono_set subset_closure
      _ = A * cψ * (volume (FD K)).toReal := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]

  rw [hW, hbox, norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.toReal_inv, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Cst_pos K)]
  calc (μA K (adelicBox K)).toReal⁻¹ * (Cst K * ‖∫ z in FD K, Complex.exp (2 * Real.pi * Complex.I * ℓ K z) * inner K xs g 0 z ∂volume‖)
      ≤ (μA K (adelicBox K)).toReal⁻¹ * (Cst K * (((2 * Real.pi * |ℓ K v|)⁻¹) ^ M * (A * cψ * (volume (FD K)).toReal))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Cst_pos K).le)
          (inv_nonneg.mpr ENNReal.toReal_nonneg)
        exact hC4.trans (mul_le_mul_of_nonneg_left hIM (pow_nonneg (inv_nonneg.mpr (by positivity)) M))
    _ = cK * A := by rw [hcK]; ring
    _ ≤ (cK + 1) * A := by nlinarith

end AutomorphicForm
