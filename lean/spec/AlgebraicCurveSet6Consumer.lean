/-
  Consumer specification for SET 6 of the `AlgebraicCurve` layer.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the set's headlines, composed with the place/differential API across
  modules, expressed in Lean so that each is either bound or not. It is a deliverable measure,
  not a proof obligation. It is **not part of any library** (`lake build` does not see `spec/`);
  run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/AlgebraicCurveSet6Consumer.lean 2>&1 | grep -c error

  The error count is the metric; deleting any one module must make it fail.

  ZONES
  -----
    [weil]    ZONE A — `RationalFunctionField.weilReciprocity` (WR, `P1/Dictionary.lean`) is the
               ℙ¹ instance of the reciprocity hypothesis `hrec` of
               `WeilDatum.pairing_eq_of_isPrincipal_sub` (WR, `Pic0/WeilPairing.lean`): the two
               modules are the two halves of the same story, written a wave apart, and the
               capstone is what makes the pairing theorem *apply* at `RatFunc K`.
               `pairing_ne_zero` and `addLeft_pairing` (`Defs/WeilDatum.lean`) then keep the
               pairing of an `addLeft` nonzero.
    [trace]   ZONE B — `Differential.sum_ord_smul_pullbackAlong_eq_zero` (TS,
               `ResidueTheorem/TraceSum.lean`) needs a *regular* differential; the regular
               differentials of the form `Differential.correspondence φ ψ η` are supplied by
               SET 5's `Differential.correspondence_mem_regularDifferentials`
               (`Differential/CorrespondenceRegular.lean`). The trace sum then vanishes at a
               correspondence, which is the composition no single module states.
    [cfe]     ZONE C — `Differential.map_correspondence_regularDifferentials_of_constantFieldExtension`
               (CFE, `Differential/CorrespondenceRegularCFE.lean`) is four conjuncts; its
               naturality conjunct composed with the same SET 5 regularity theorem says the
               *lifted* correspondence of a regular differential is regular in the `E`-world.
    [laurent] ZONE D — `Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` (TL,
               `Place/LaurentSeriesModel.lean`) realises a Laurent-series embedding as a place;
               the resulting order relation, read against `Place.mem_of_ord_nonneg`
               (`Defs/PushPull.lean`), puts the elements of positive `ι`-order in the place's
               valuation ring. Engine and conclusion are in different modules.
-/

import FLTForHuman.AlgebraicCurve.P1.Dictionary
import FLTForHuman.AlgebraicCurve.Pic0.WeilPairing
import FLTForHuman.AlgebraicCurve.Defs.WeilDatum
import FLTForHuman.AlgebraicCurve.ResidueTheorem.TraceSum
import FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegular
import FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegularCFE
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Place.LaurentSeriesModel

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve
open scoped Pointwise

universe u v w

/-! ## Zone A — `[weil]` the ℙ¹ capstone is the pairing theorem's reciprocity hypothesis -/

theorem set6_weil_capstone_feeds_pairing {K : Type*} [Field K] [IsAlgClosed K]
    {n : ℕ} [NeZero n] (d d' : WeilDatum K (RatFunc K) n)
    (hconst : ∀ u : RatFunc K, u ≠ 0 →
      (∀ v : Place K (RatFunc K), v.ord u = 0) → ∃ c : K, u = algebraMap K (RatFunc K) c)
    (hmove : ∀ (x : Pic0.torsion K (RatFunc K) n) (S : Finset (Place K (RatFunc K))),
      ∃ D : Divisor.degZero (K := K) (F := RatFunc K),
        Pic0.mk D = (x : Pic0 K (RatFunc K)) ∧
        (∀ v ∈ (D : Divisor K (RatFunc K)).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K (RatFunc K)).support, v ∉ S))
    (hL : Divisor.IsPrincipal (d'.D₁ - d.D₁)) (hR : Divisor.IsPrincipal (d'.D₂ - d.D₂)) :
    d'.pairing = d.pairing := by
  haveI := RationalFunctionField.hasPrincipalDivisors K
  exact WeilDatum.pairing_eq_of_isPrincipal_sub (RationalFunctionField.weilReciprocity K)
    hconst hmove d d' hL hR

/-- The two small laws compose: `addLeft` multiplies the pairing, and the pairing never
vanishes, so an `addLeft` pairing is nonzero. -/
theorem set6_weil_addLeft_pairing_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).pairing ≠ 0 := by
  rw [WeilDatum.addLeft_pairing]
  exact mul_ne_zero (WeilDatum.pairing_ne_zero d) (WeilDatum.pairing_ne_zero d')

/-! ## Zone B — `[trace]` the trace sum vanishes at a correspondence -/

theorem set6_trace_of_correspondence (K F E FE : Type*) [Field K] [Field F] [Field E]
    [Field FE] [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (g : FE) (hg : g ≠ 0)
    (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E))
    (hS : ∀ P ∈ S, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1)
    (hrat : ∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
      ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψfin : FiniteAlong K ψ)
    (η : Ω[F⁄K]) (hη : η ∈ regularDifferentials K F) :
    ∑ P ∈ S, (P.ord g) • Differential.pullbackAlong (y P)
      (Differential.correspondence φ ψ η) = 0 :=
  Differential.sum_ord_smul_pullbackAlong_eq_zero K F E FE hfg hfgE hgen g hg S y hS hrat _
    (Differential.correspondence_mem_regularDifferentials K F F' hfg φ ψ hφ hψ hψfin hη)

/-! ## Zone C — `[cfe]` the lifted correspondence of a regular differential is regular -/

theorem set6_cfe_lifted_correspondence_regular (K F E FE : Type*) [Field K] [Field F] [Field E]
    [Field FE] [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [SMulCommClass E F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψfin : FiniteAlong K ψ)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE ψE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (ω : Ω[F⁄K]) (hω : ω ∈ regularDifferentials K F) :
    Differential.correspondence φE ψE
        (KaehlerDifferential.map K E F FE ω) ∈ regularDifferentials E FE := by
  obtain ⟨hint, -, hreg, -⟩ :=
    Differential.map_correspondence_regularDifferentials_of_constantFieldExtension K F
      hfg F' hfg' φ ψ hφ hψ E FE hfgE hgen F'E hfgE' hgen' φE ψE hφcomm hψcomm hφE hψE
  rw [← hint ω]
  exact hreg _ (Differential.correspondence_mem_regularDifferentials K F F' hfg φ ψ hφ hψ
    hψfin hω)

/-! ## Zone D — `[laurent]` a Laurent-series embedding puts positive-order elements in a
valuation ring

`Algebra K (HahnSeries Γ K)` has two mathlib instances (`HahnSeries.instAlgebra` and
`HahnSeries.powerSeriesAlgebra`); which one an `F →ₐ[K] LaurentSeries K` is elaborated with
depends on the import order, and `Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` is
stored with `instAlgebra`. The same local pin the module uses (it does not leak: this file is
not a library) makes the two meet — FR-0045. -/

attribute [local instance 2000] HahnSeries.instAlgebra

theorem set6_laurent_embedding_yields_integral {K F : Type*} [Field K] [Field F] [Algebra K F]
    (ι : F →ₐ[K] LaurentSeries K) (h : ∃ x : F, (ι x).order ≠ 0)
    {x : F} (hx : 0 < (ι x).order) :
    ∃ w : Place K F, x ∈ w.toValuationSubring := by
  obtain ⟨w, γ, hγ, hw⟩ := Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K ι h
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp only [map_zero, HahnSeries.order_zero] at hx
    exact lt_irrefl (0 : ℤ) hx
  have hγz : (0 : ℤ) < (γ : ℤ) := by exact_mod_cast hγ
  have hpos : 0 < w.ord x := by nlinarith [hw x]
  exact ⟨w, Place.mem_of_ord_nonneg w hx0 hpos.le⟩
