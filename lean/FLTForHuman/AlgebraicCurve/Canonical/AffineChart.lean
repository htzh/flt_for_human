/-
Affine charts of a place, the two-chart cover, and the separating transcendental.

A subalgebra `A ≤ F` is an *affine chart* at `v` when it is a Dedekind domain with
fraction field `F` whose localisation at `v` is `𝒪ᵥ` (`IsAffineChart`). Two charts
suffice to run the Dedekind model at every place: `ValSubringTwoAffineCharts` says there
is `t` such that both `K⟮t⟯` and `K⟮t⁻¹⟯` are charts, and that supplies
`ValSubringDedekindFractionModel` for every `v` — the hypothesis the Kähler model chain
(`Canonical/ValSubringKaehler.lean`) turns into "`D π` spans `Ω[𝒪ᵥ⁄K]`".

The construction of the charts is where the transcendental enters: for transcendental
`t`, `K⟮t⟯` is a Dedekind domain (`isDedekindDomain_adjoin`) whose integral closure is
again a chart (`isAffineChart_transcendentalChart`), and a chart is contained in `𝒪ᵥ` or
its reciprocal is (`transcendentalChart_subset_or_inv_subset`) — which is why the whole
development transports along `t ↦ t⁻¹` (`IntermediateField.adjoin_simple_inv` and the
finiteness/separability transfers below it).

`HasSeparatingTranscendental` is the datum the curve side supplies: a transcendental `t`
with `F/K(t)` finite and separable and both charts. After FLT's
`P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean` (1,723 ln, middle),
pinned at `aa2d8b3`: <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean>.

Assumes `Canonical/ValSubringKaehler.lean` (the model predicates it bridges to).

spec-pin: P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean
-/
import FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain Polynomial IsLocalRing KaehlerDifferential IntermediateField
open scoped TensorProduct IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.Place

open IsLocalRing

namespace AlgebraicCurve

namespace Place

section IntegrallyClosed

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem isIntegrallyClosed_toValuationSubring :
    IsIntegrallyClosed v.toValuationSubring := inferInstance

theorem mem_valuationSubring_of_isIntegral {x : F}
    (hx : IsIntegral v.toValuationSubring x) :
    x ∈ v.toValuationSubring := by
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff F).mp (v.isIntegrallyClosed_toValuationSubring) hx
  exact hy ▸ y.2

variable (B : Subalgebra K F) (hB : (B : Set F) ⊆ (v.toValuationSubring : Set F))

include hB in
theorem modelAlgebra_isScalarTower_top :
    letI := v.modelAlgebra B hB
    IsScalarTower B v.toValuationSubring F := by
  letI := v.modelAlgebra B hB
  refine IsScalarTower.of_algebraMap_eq fun b => ?_
  rfl

include hB in
theorem mem_valuationSubring_of_isIntegral_subalgebra {x : F}
    (hx : IsIntegral B x) :
    x ∈ v.toValuationSubring := by
  letI := v.modelAlgebra B hB
  haveI := v.modelAlgebra_isScalarTower_top B hB
  exact v.mem_valuationSubring_of_isIntegral (hx.tower_top (A := v.toValuationSubring))

include hB in
theorem integralClosure_subset_valuationSubring :
    ((integralClosure B F : Subalgebra B F) : Set F)
      ⊆ (v.toValuationSubring : Set F) := fun _ hx =>
  v.mem_valuationSubring_of_isIntegral_subalgebra B hB hx

end IntegrallyClosed

end Place

section TwoCharts

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def IsAffineChart (A : Subalgebra K F) : Prop :=
  Algebra.FiniteType K A ∧ IsDedekindDomain A ∧ IsFractionRing A F

def ValSubringTwoAffineCharts : Prop :=
  ∃ A₀ A₁ : Subalgebra K F, IsAffineChart K F A₀ ∧ IsAffineChart K F A₁
    ∧ ∀ v : Place K F, (A₀ : Set F) ⊆ (v.toValuationSubring : Set F)
        ∨ (A₁ : Set F) ⊆ (v.toValuationSubring : Set F)

variable {K F}

theorem valSubringDedekindFractionModel_of_twoAffineCharts
    (h : ValSubringTwoAffineCharts K F) :
    ValSubringDedekindFractionModel K F := fun v => by
  obtain ⟨A₀, A₁, ⟨hft₀, hded₀, hfrac₀⟩, ⟨hft₁, hded₁, hfrac₁⟩, hcover⟩ := h
  rcases hcover v with h₀ | h₁
  · exact ⟨A₀, h₀, hft₀, hded₀, hfrac₀⟩
  · exact ⟨A₁, h₁, hft₁, hded₁, hfrac₁⟩

theorem valSubringDedekindModel_of_twoAffineCharts
    (h : ValSubringTwoAffineCharts K F) :
    ValSubringDedekindModel K F :=
  valSubringDedekindModel_of_dedekindFractionModel
    (valSubringDedekindFractionModel_of_twoAffineCharts h)

end TwoCharts

end AlgebraicCurve

namespace AlgebraicCurve

section Gates

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

open scoped AlgebraicCurve.Place in
@[reducible] private noncomputable def toKSubalgebra (v : Place K F) : Subalgebra K F where
  __ := v.toValuationSubring.toSubring
  algebraMap_mem' c := v.algebraMap_mem' c

end Place

namespace Place

open scoped AlgebraicCurve.Place in
private theorem coe_toKSubalgebra (v : Place K F) :
    (v.toKSubalgebra : Set F) = (v.toValuationSubring : Set F) := rfl

end Place

theorem gate_adjoin_subset_valuationSubring_of_mem (v : Place K F) {t : F}
    (ht : t ∈ v.toValuationSubring) :
    ((Algebra.adjoin K {t} : Subalgebra K F) : Set F)
      ⊆ (v.toValuationSubring : Set F) := by
  rw [← v.coe_toKSubalgebra]
  exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr ht)

end Gates

end AlgebraicCurve

open scoped IntermediateField.algebraAdjoinAdjoin

namespace AlgebraicCurve

section AdjoinRingProperties

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- For transcendental `t`, the simple adjoin `K⟮t⟯` is a principal ideal ring: it is
a quotient-free image of `K[X]` along `Polynomial.algEquivOfTranscendental`. -/
theorem isPrincipalIdealRing_adjoin {t : F} (ht : Transcendental K t) :
    IsPrincipalIdealRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  IsPrincipalIdealRing.of_surjective
    (Polynomial.algEquivOfTranscendental K t ht).toRingHom
    (Polynomial.algEquivOfTranscendental K t ht).surjective

/-- For transcendental `t`, `K⟮t⟯` is a Dedekind domain (principal ideal ring and
integrally closed: it is `K[X]`'s localisation-free model). -/
theorem isDedekindDomain_adjoin {t : F} (ht : Transcendental K t) :
    IsDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := isPrincipalIdealRing_adjoin ht
  inferInstance

/-- For transcendental `t`, `K⟮t⟯` is integrally closed. -/
theorem isIntegrallyClosed_adjoin {t : F} (ht : Transcendental K t) :
    IsIntegrallyClosed ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := isDedekindDomain_adjoin ht
  inferInstance

/-- For transcendental `t`, `K⟮t⟯` is Noetherian. -/
theorem isNoetherianRing_adjoin {t : F} (ht : Transcendental K t) :
    IsNoetherianRing ↥(Algebra.adjoin K ({t} : Set F)) :=
  haveI := isPrincipalIdealRing_adjoin ht
  inferInstance

/-- The simple adjoin of one element is a finite-type `K`-algebra. -/
theorem finiteType_adjoin_singleton (t : F) :
    Algebra.FiniteType K ↥(Algebra.adjoin K ({t} : Set F)) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton t)

/-- If `t` is transcendental then so is `t⁻¹`. -/
theorem transcendental_inv {t : F} (ht : Transcendental K t) :
    Transcendental K t⁻¹ := by
  rw [Transcendental, IsAlgebraic.inv_iff]; exact ht

end AdjoinRingProperties

section TranscendentalChart

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F]

@[reducible] noncomputable def transcendentalChart (t : F) : Subalgebra K F :=
  (integralClosure (Algebra.adjoin K ({t} : Set F)) F).restrictScalars K

theorem coe_transcendentalChart (t : F) :
    (transcendentalChart K t : Set F)
      = ((integralClosure (Algebra.adjoin K ({t} : Set F)) F : Subalgebra _ F) : Set F) :=
  rfl

variable {K}

theorem transcendentalChart_subset_valuationSubring_of_mem (v : Place K F)
    {t : F} (ht : t ∈ v.toValuationSubring) :
    (transcendentalChart K t : Set F) ⊆ (v.toValuationSubring : Set F) := by
  rw [coe_transcendentalChart]
  exact v.integralClosure_subset_valuationSubring _
    (gate_adjoin_subset_valuationSubring_of_mem v ht)

theorem transcendentalChart_subset_or_inv_subset (v : Place K F) (t : F) :
    (transcendentalChart K t : Set F) ⊆ (v.toValuationSubring : Set F)
      ∨ (transcendentalChart K t⁻¹ : Set F) ⊆ (v.toValuationSubring : Set F) :=
  (v.toValuationSubring.mem_or_inv_mem t).imp
    (transcendentalChart_subset_valuationSubring_of_mem v)
    (transcendentalChart_subset_valuationSubring_of_mem v)

end TranscendentalChart

section IsAffineChartEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section

variable (B : Subalgebra K F)

theorem isScalarTower_integralClosure_subalgebra :
    IsScalarTower K B ↥(integralClosure B F) := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  exact Subtype.ext rfl

theorem finiteType_integralClosure_of_moduleFinite (hft : Algebra.FiniteType K B)
    (hfin : Module.Finite B ↥(integralClosure B F)) :
    Algebra.FiniteType K ↥(integralClosure B F) :=
  haveI := isScalarTower_integralClosure_subalgebra B
  haveI := hfin
  Algebra.FiniteType.trans (S := B) hft inferInstance

end

theorem isDedekindDomain_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    IsDedekindDomain ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) := by
  haveI := isDedekindDomain_adjoin ht
  exact integralClosure.isDedekindDomain ↥(Algebra.adjoin K ({t} : Set F)) ↥(K⟮t⟯) F

theorem isFractionRing_integralClosure_adjoin (t : F) [FiniteDimensional K⟮t⟯ F] :
    IsFractionRing ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) F :=
  integralClosure.isFractionRing_of_finite_extension
    (A := ↥(Algebra.adjoin K ({t} : Set F))) ↥(K⟮t⟯) F

theorem moduleFinite_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    Module.Finite ↥(Algebra.adjoin K ({t} : Set F))
      ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) := by
  haveI := isIntegrallyClosed_adjoin ht
  haveI := isNoetherianRing_adjoin ht
  exact IsIntegralClosure.finite (A := ↥(Algebra.adjoin K ({t} : Set F)))
    (K := ↥(K⟮t⟯)) (L := F) (integralClosure ↥(Algebra.adjoin K ({t} : Set F)) F)

theorem finiteType_integralClosure_adjoin {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.FiniteType K ↥(integralClosure (Algebra.adjoin K ({t} : Set F)) F) :=
  finiteType_integralClosure_of_moduleFinite (Algebra.adjoin K {t})
    (finiteType_adjoin_singleton t) (moduleFinite_integralClosure_adjoin ht)

theorem isAffineChart_restrictScalars_integralClosure (B : Subalgebra K F)
    (hft : Algebra.FiniteType K ↥(integralClosure B F))
    (hded : IsDedekindDomain ↥(integralClosure B F))
    (hfrac : IsFractionRing ↥(integralClosure B F) F) :
    IsAffineChart K F ((integralClosure B F).restrictScalars K) :=
  ⟨hft, hded, hfrac⟩

theorem isAffineChart_transcendentalChart {t : F} (ht : Transcendental K t)
    [FiniteDimensional K⟮t⟯ F] [Algebra.IsSeparable K⟮t⟯ F] :
    IsAffineChart K F (transcendentalChart K t) :=
  isAffineChart_restrictScalars_integralClosure (Algebra.adjoin K {t})
    (finiteType_integralClosure_adjoin ht)
    (isDedekindDomain_integralClosure_adjoin ht)
    (isFractionRing_integralClosure_adjoin t)

end IsAffineChartEngine

section SeparatingTranscendental

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def HasSeparatingTranscendental : Prop :=
  ∃ t : F, Transcendental K t
    ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F
    ∧ FiniteDimensional K⟮t⁻¹⟯ F ∧ Algebra.IsSeparable K⟮t⁻¹⟯ F

variable {K F}

theorem valSubringTwoAffineCharts_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringTwoAffineCharts K F := by
  obtain ⟨t, ht, hfin, hsep, hfin', hsep'⟩ := h
  exact ⟨transcendentalChart K t, transcendentalChart K t⁻¹,
    isAffineChart_transcendentalChart ht,
    isAffineChart_transcendentalChart (transcendental_inv ht),
    fun v => transcendentalChart_subset_or_inv_subset v t⟩

theorem valSubringDedekindModel_of_hasSeparatingTranscendental
    (h : HasSeparatingTranscendental K F) :
    ValSubringDedekindModel K F :=
  valSubringDedekindModel_of_twoAffineCharts
    (valSubringTwoAffineCharts_of_hasSeparatingTranscendental h)

end SeparatingTranscendental

end AlgebraicCurve

namespace IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem adjoin_simple_inv (t : F) : K⟮t⁻¹⟯ = K⟮t⟯ := by
  refine le_antisymm (adjoin_simple_le_iff.mpr ?_) (adjoin_simple_le_iff.mpr ?_)
  · exact inv_mem (mem_adjoin_simple_self K t)
  · have h : (t⁻¹)⁻¹ ∈ (K⟮t⁻¹⟯ : IntermediateField K F) :=
      inv_mem (mem_adjoin_simple_self K t⁻¹)
    rwa [inv_inv] at h

theorem algebraMap_comp_equivOfEq {S T : IntermediateField K F} (h : S = T) :
    (algebraMap T F).comp ((IntermediateField.equivOfEq h).toRingEquiv : S →+* T)
      = ((RingEquiv.refl F : F ≃+* F) : F →+* F).comp (algebraMap S F) := by
  ext x; rfl

theorem finiteDimensional_of_eq {S T : IntermediateField K F} (h : S = T)
    [FiniteDimensional ↥S F] : FiniteDimensional ↥T F :=
  Module.Finite.of_equiv_equiv (IntermediateField.equivOfEq h).toRingEquiv (RingEquiv.refl F)
    (algebraMap_comp_equivOfEq h)

theorem isSeparable_of_eq {S T : IntermediateField K F} (h : S = T)
    [Algebra.IsSeparable ↥S F] : Algebra.IsSeparable ↥T F :=
  Algebra.IsSeparable.of_equiv_equiv (IntermediateField.equivOfEq h).toRingEquiv
    (RingEquiv.refl F) (algebraMap_comp_equivOfEq h)

theorem finiteDimensional_adjoin_inv (t : F) [FiniteDimensional K⟮t⟯ F] :
    FiniteDimensional K⟮t⁻¹⟯ F :=
  finiteDimensional_of_eq (adjoin_simple_inv t).symm

theorem isSeparable_adjoin_inv (t : F) [Algebra.IsSeparable K⟮t⟯ F] :
    Algebra.IsSeparable K⟮t⁻¹⟯ F :=
  isSeparable_of_eq (adjoin_simple_inv t).symm

end IntermediateField

end
