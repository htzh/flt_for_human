/-
The genus of `X₁`, its `j`-ramification over the algebraic closure, and its regular differentials.

Three rows on the function field `F = laurentBaseChange (AlgebraicClosure ℚ)
(qExpFunctionFieldC ℚ Γ)` of the modular curve `X₁` (`Γ ⊇ Γ₁(M)`, `y` the class of
`jqModC` there):

* `ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure`
  — the **ramification of `jq` over `ℚ̄`**: at every place `P` of `F`,
  `P.ord y ≤ 3`, `P.ord (y - 1728) ≤ 2`, and `P.ord (y - a) ≤ 1` for every
  `a ∈ ℚ̄ \ {0, 1728}`.  Over the algebraic closure the constant field extension turns the
  `ℂ`-statement of `X1/JqRamification.lean` into the geometric one, and the three bounds are
  the ramification indices of the map `X₁ → P¹` over `∞`, `1728` and the other points;
* `two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le` — the
  **Riemann–Hurwitz count**: with `y` transcendental (the `j`-line),
  `2 * genusFF + #{P | P.ord y < 0} + #{P | 0 < P.ord y} + #{P | 0 < P.ord (y - 1728)}
   ≤ [F : ℚ̄(y)] + 2`, the Riemann–Hurwitz inequality for `X₁ → X(1)` with the fibre counts
  over `0`, `∞` and `1728` supplied by the ramification bounds;
* `mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion` — a
  **regular differential from its `q`-expansion**: a weight-2 cusp form `f` for `Γ₁(M)`
  whose `q`-expansion agrees, through `coeffMap ι₀ ∘ diffQExp`, with `ω ∈ Ω[F⁄ℚ̄]` forces
  `ω` to be a regular differential on the `X₁` function field, i.e. the differentials with
  nonnegative order at every place, which is the dualizing half of the genus count.

The engine is the place/differential calculus of `AlgebraicCurve`
(`Place/{OrdCalculus,OrbitCardinality}`, `Differential/{Coefficient,Different,RegularDiffs}`,
`Canonical/{HasCanonicalDivisor,DCoordGenerates}`), the Riemann–Roch and canonical-degree
assemblies (`ResidueTheorem/RRAssembly`, `RiemannRoch/Assembly`), the genus computations
over a constant field extension (`Genus/ConstantFieldExtension*`), the `X₁` function-field
and `LevelN` covers (`X1/{Structure,FunctionFieldBaseChange,FunctionFieldConstExt,CoeffMap}`,
`LevelN/{QExpBridge,FieldGalois,SpecialRamification}`), the `jq`-integrality engine
(`Analytic/JqInverseIntegral`, `JqIntegralRatios`) and SET-AF103's ramification bound
(`X1/JqRamification.lean`).

The three `S_` engines are transcribed in three subject namespaces:

* `ModularCurve.ConstantFieldLift` — the pin's `UBAux` block: the `coeffMap` lift of
  `laurentBaseChange ℚ F₀` along a `ℚ`-algebra map, its range, `LevelN.ring`'s domain
  property, and the `ℚ̄`-form of the `ℂ` ramification bound;
* `ModularCurve.RiemannHurwitzCount` — the pin's `RiemannHurwitzCount` block: the
  `RiemannRoch`/`Stichtenoth` package, the place/different bridge, the zero/pole counting
  engine and the `ℚ̄`-descent (`iota`, `psi`), then the headline count;
* `ModularCurve.RegularDifferential` — the pin's `SolB8bd4cf51` block: the `thetaL`
  calculus, `jq ∈ x1FunctionField M`, and the regular-differential criterion.

Substitutions (imported, **not** restated — `port_advise` lists them as already in the port
and they are; `rg`-verified at the port's own statement):

| pin row | port declaration |
|---|---|
| 346, 163 `coeffMap_coeffEmb'` | `ModularCurve.UnramifiedGamma.coeffMap_coeffEmb'` (`X1/JqRamification.lean`) |
| 346 `coeffMap_algebraMap'` | `ModularCurve.QExpAutBaseChange.coeffMap_algebraMap'` (`X1/CoeffMap.lean`) |
| 812 `T_mem_Gamma1` | `ModularCurve.UnramifiedGamma.T_mem_Gamma1` (`X1/JqRamification.lean`) |
| 812 `mem_of_ord_nonneg` | `AlgebraicCurve.W7XH.mem_of_ord_nonneg` (`IsCurveOver/ConstantFieldExtensionSpan.lean`) — the pin's no-`f ≠ 0` form |
| 812 `ord_pos_of_mem_maximalIdeal` | `AlgebraicCurve.Place.ord_pos_of_mem_maximalIdeal` (`Place/OrdCalculus.lean`) |
| 812 `degree_eq_sum_support` | `AlgebraicCurve.Divisor.degree_eq_sum_support` (`Genus/Index.lean`) |
| 163 `thetaL_coeff'` | `ModularCurve.UnramifiedGamma.thetaL_coeff'` (`X1/JqRamification.lean`) |
| 163 `coeffMap_thetaL` | `ModularCurve.UnramifiedGamma.coeffMap_thetaL` (`X1/JqRamification.lean`) |
| 163 `qEuler_eq_thetaL` | `ModularCurve.Period.qEuler_eq_thetaL` (`Period/QExpansionDiff.lean`) — binder `f` for the pin's `x` |
| 163 `one_mem_strictPeriods_Gamma1` | `Depletion.one_mem_strictPeriods_Gamma1` (`ModularForms/AtkinLehnerLowering.lean`) |
| 163 `Gamma_le_Gamma1` | `AtkinLehnerMain.Gamma_le_Gamma1` (`ModularForms/AtkinLehnerLowering.lean`) |

The `_pkg` rows of 812 (`isCurveOver_pkg`, `essFiniteType_pkg`,
`riemannRoch_and_constantsAreBase_pkg`, `degree_canonical_pkg`, `genus_eq_genusFF_pkg`) are
**not** substitutions despite `port_advise` matching them to
`DegreeOnePrimes.finiteDimensional_fractionRing`: they are `haveI`-prefixed `Prop` packages
whose statement view collapses the `haveI` prefix, so any port theorem of the shape
`haveI _; (…)` matches.  They are transcribed below (FR-0266).

`with_ratFunc` and `ord_nonneg_of_ord_sub_algebraMap_pos` are transcribed although
`AlgebraicCurve/Genus/HurwitzBound.lean` carries both proofs: there they are `private`, so they
are not importable (the checker confirms both as `ok` against their pin rows).

## Heartbeat probe (gate 7) — recorded, never installed

No `set_option maxHeartbeats` and no `set_option synthInstance.maxHeartbeats` is carried: the
project's edit loop is `-DmaxHeartbeats=200000` and `lean/lakefile.lean:7-12` ships
`(maxHeartbeats, 4000000)` for the build.  The pins carry the bound this set's two biggest rows
would otherwise inherit:

| declaration | pin's option | low-cap reading (200 000) |
|---|---|---|
| `ConstantFieldLift.ord_sub_algebraMap_le_one_algebraicClosure` | `maxHeartbeats 6400000`, `synthInstance 1600000` (S_346:130-131) | silent |
| `RiemannHurwitzCount.riemannRoch_and_constantsAreBase_pkg` | `maxHeartbeats 3200000`, `synthInstance 1600000` (S_812:48-49) | silent |
| `RiemannHurwitzCount.main` | idem | silent |
| `RiemannHurwitzCount.psi` / `exists_place_complex_ord_eq` | idem | silent |
| `mem_regularDifferentials_…` (163) | none | silent |
| `ord_le_three_and_…_algebraicClosure` | `maxHeartbeats 6400000`, `synthInstance 1600000` (S_346:179-180) | **fails** (see below) |

The 346 headline is the one residual.  The pin's two local `have`-blocks are carved into the four
`private` helpers `natCard_fibre_le`, `ord_le_of_ord_pos`, `finiteDimensional_adjoin_singleton`,
`isIntegral_of_algHom_apply_eq`, each charged to its own command; the headline then still does not
finish at 200 000 and is silent at the lakefile's 4 000 000.  The measured ladder and the
attribution are in `lean/tmp/af104/AF104E-REPORT.md`; nothing is installed.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion.lean>

spec-pin: Theorems/Thm_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure.lean
spec-pin: Theorems/Thm_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.lean
spec-pin: Theorems/Thm_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion.lean
spec-pin: P2M/Sol/S_ModularCurve_ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure.lean
spec-pin: P2M/Sol/S_ModularCurve_two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le.lean
spec-pin: P2M/Sol/S_ModularCurve_mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion.lean
-/
import FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.Canonical.PolarDifferentials
import FLTForHuman.AlgebraicCurve.Defs.IntegralAdjoin
import FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegular
import FLTForHuman.AlgebraicCurve.Differential.Different
import FLTForHuman.AlgebraicCurve.Differential.RegularDiffs
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences
import FLTForHuman.AlgebraicCurve.Genus.RatFunc
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.OrbitCardinality
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import FLTForHuman.ModularCurve.Analytic.JqInverseIntegral
import FLTForHuman.ModularCurve.Degree.PhiDegree
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.LevelN.FieldGalois
import FLTForHuman.ModularCurve.LevelN.QExpBridge
import FLTForHuman.ModularCurve.LevelN.SpecialRamification
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.ModularCurve.X1.FunctionFieldConstExt
import FLTForHuman.ModularCurve.X1.JqRamification
import FLTForHuman.ModularCurve.X1.Structure
import FLTForHuman.ModularForms.AtkinLehnerLowering
import FLTForHuman.ModularForms.WeightOne.LevelN

noncomputable section

set_option autoImplicit false

open AlgebraicCurve ModularCurve KaehlerDifferential
open scoped MatrixGroups TensorProduct IntermediateField

-- The `haveI`/`letI` instance walls of the pin's place/differential sections are load-bearing:
-- they register the constant-field-extension instances the following terms elaborate against,
-- so the style linter's `have`/`let` suggestion does not apply (cf. `Genus/HurwitzBound.lean`).
set_option linter.style.haveILetI false

namespace ModularCurve

/-! ## The constant-field lift of the `q`-expansion function field (pin `UBAux`) -/

namespace ConstantFieldLift

section CoeffLift

variable {L : Type*} [Field L] {Ω : Type*} [Field Ω] [Algebra ℚ L] [Algebra ℚ Ω]
  (τ : L →ₐ[ℚ] Ω) (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem coeffMap_mem_laurentBaseChange' {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    coeffMap τ.toRingHom x ∈ laurentBaseChange Ω F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [QExpAutBaseChange.coeffMap_algebraMap']
        exact (laurentBaseChange Ω F₀).algebraMap_mem _
      · rw [UnramifiedGamma.coeffMap_coeffEmb']
        exact coeffEmb_mem_laurentBaseChange Ω hz
  | one => simp
  | add _ _ _ _ hx hy => simpa using add_mem hx hy
  | neg _ _ hx => simpa using neg_mem hx
  | inv _ _ hx => simpa using inv_mem hx
  | mul _ _ _ _ hx hy => simpa using mul_mem hx hy

@[reducible] def algebraOfLift : Algebra L ↥(laurentBaseChange Ω F₀) :=
  ((algebraMap Ω ↥(laurentBaseChange Ω F₀)).comp τ.toRingHom).toAlgebra

def liftRingHom : ↥(laurentBaseChange L F₀) →+* ↥(laurentBaseChange Ω F₀) :=
  ((coeffMap τ.toRingHom).comp (laurentBaseChange L F₀).toSubring.subtype).codRestrict
    (laurentBaseChange Ω F₀).toSubring (fun x => coeffMap_mem_laurentBaseChange' τ F₀ x.2)

theorem coe_liftRingHom (x : ↥(laurentBaseChange L F₀)) :
    ((liftRingHom τ F₀ x : ↥(laurentBaseChange Ω F₀)) : LaurentSeries Ω) =
      coeffMap τ.toRingHom x :=
  rfl

def liftHom :
    letI := algebraOfLift τ F₀; ↥(laurentBaseChange L F₀) →ₐ[L] ↥(laurentBaseChange Ω F₀) :=
  letI := algebraOfLift τ F₀
  { liftRingHom τ F₀ with
    commutes' := fun c => Subtype.ext (by
      change coeffMap τ.toRingHom (algebraMap L (LaurentSeries L) c) =
        algebraMap Ω (LaurentSeries Ω) (τ c)
      exact QExpAutBaseChange.coeffMap_algebraMap' τ.toRingHom c) }

theorem coe_liftHom (x : ↥(laurentBaseChange L F₀)) :
    letI := algebraOfLift τ F₀;
    ((liftHom τ F₀ x : ↥(laurentBaseChange Ω F₀)) : LaurentSeries Ω) =
      coeffMap τ.toRingHom x :=
  rfl

theorem liftHom_toRingHom :
    letI := algebraOfLift τ F₀; (liftHom τ F₀).toRingHom = liftRingHom τ F₀ := rfl

theorem adjoin_range_liftRingHom_eq_top :
    IntermediateField.adjoin Ω (Set.range (liftRingHom τ F₀)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  let T : IntermediateField Ω ↥(laurentBaseChange Ω F₀) :=
    IntermediateField.adjoin Ω (Set.range (liftRingHom τ F₀))
  let T' : Subfield (LaurentSeries Ω) := T.toSubfield.map (laurentBaseChange Ω F₀).val.toRingHom
  have hgens : Set.range (algebraMap Ω (LaurentSeries Ω)) ∪
      (⇑(coeffEmb Ω) '' (F₀ : Set (LaurentSeries ℚ))) ⊆ T' := by
    rintro w (⟨a, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨algebraMap Ω ↥(laurentBaseChange Ω F₀) a, T.algebraMap_mem a, rfl⟩
    · refine ⟨liftRingHom τ F₀ ⟨coeffEmb L x, coeffEmb_mem_laurentBaseChange L hx⟩,
        IntermediateField.subset_adjoin Ω _ ⟨_, rfl⟩, ?_⟩
      change coeffMap τ.toRingHom (coeffEmb L x) = coeffEmb Ω x
      exact UnramifiedGamma.coeffMap_coeffEmb' τ.toRingHom x
  have hle : Subfield.closure (Set.range (algebraMap Ω (LaurentSeries Ω)) ∪
      (⇑(coeffEmb Ω) '' (F₀ : Set (LaurentSeries ℚ)))) ≤ T' := Subfield.closure_le.mpr hgens
  obtain ⟨w, hw, hwz⟩ := hle (mem_laurentBaseChange_iff.mp z.2)
  have : w = z := Subtype.ext hwz
  rw [← this]
  exact hw

end CoeffLift

theorem isDomain_levelN_ring (N : ℕ) [NeZero N] : IsDomain ↥(ModularCurve.LevelN.ring N) := by
  have h := WLight.levelN_structure_package N (fun τ => PeriodPair.ofTau τ) (fun τ => ⟨rfl, rfl⟩)
    (ModularCurve.LevelN.wp N) (fun v τ => rfl) (ModularCurve.LevelN.fricke N) (fun v τ => rfl)
    ModularCurve.LevelN.jAnalytic (fun τ => rfl)
  obtain ⟨-, -, -, -, -, hdom⟩ := h
  haveI : NoZeroDivisors ↥(ModularCurve.LevelN.ring N) := ⟨fun {a b} hab => by
    have := hdom a b a.2 b.2 (by rw [← Subalgebra.coe_mul, hab]; rfl)
    rcases this with h0 | h0
    · left; exact Subtype.ext h0
    · right; exact Subtype.ext h0⟩
  haveI : Nontrivial ↥(ModularCurve.LevelN.ring N) := inferInstance
  exact NoZeroDivisors.to_isDomain _

section Generic

theorem ord_sub_algebraMap_le_one_algebraicClosure (M : ℕ) [NeZero M]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (ιa : AlgebraicClosure ℚ →ₐ[ℚ] ℂ)
    (y : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : Place (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (a : AlgebraicClosure ℚ) (ha0 : a ≠ 0) (ha1728 : a ≠ 1728) :
    P.ord (y - algebraMap (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) ≤ 1 := by
  classical
  let ι : AlgebraicClosure ℚ →+* ℂ := ιa.toRingHom
  letI algQC : Algebra (AlgebraicClosure ℚ) ℂ := ι.toAlgebra
  letI algQFC : Algebra (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
    algebraOfLift ιa (ModularCurve.qExpFunctionFieldC ℚ Γ)
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ
      ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let Ψ : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ)) →+*
      ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
    liftRingHom ιa (ModularCurve.qExpFunctionFieldC ℚ Γ)
  letI algFF : Algebra ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ))
      ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) := Ψ.toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
      ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((liftHom ιa (ModularCurve.qExpFunctionFieldC ℚ Γ)).commutes c).symm
  obtain ⟨x₀, hx₀tr, hx₀fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ)
      Γ hT
  haveI : IsCurveOver (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
    isCurveOver_of_transcendental_of_perfectField hx₀tr hx₀fd
  obtain ⟨x₁, hx₁tr, hx₁fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℂ Γ hT
  have hgenC : IntermediateField.adjoin ℂ (Set.range (algebraMap
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
      ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)))) = ⊤ :=
    adjoin_range_liftRingHom_eq_top ιa (ModularCurve.qExpFunctionFieldC ℚ Γ)
  obtain ⟨P'', -, hP''ord, -⟩ := Place.exists_comap_algebraMap_eq_of_constantFieldExtension
    (AlgebraicClosure ℚ)
    ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ))
    ⟨x₀, hx₀tr, hx₀fd⟩ ⟨x₁, hx₁tr, hx₁fd⟩ hgenC P

  have hyC : ((Ψ y : ↥(ModularCurve.laurentBaseChange ℂ
      (ModularCurve.qExpFunctionFieldC ℚ Γ))) : LaurentSeries ℂ) = ModularCurve.jqModC ℂ := by
    rw [coe_liftRingHom, hy]
    exact map_jqModC ι
  have hιa0 : ι a ≠ 0 := fun h => ha0 (ι.injective (by rw [h, map_zero]))
  have hιa1728 : ι a ≠ 1728 := fun h => ha1728 (ι.injective (by rw [h, map_ofNat]))
  have hle1 := ModularCurve.ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728
    M Γ hΓ (Ψ y) hyC (ι a) hιa0 hιa1728 P''
  have htrans : P''.ord (Ψ y - algebraMap ℂ
        ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) (ι a)) =
      P.ord (y - algebraMap (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) := by
    rw [← hP''ord, map_sub, ← IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) a,
      IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ℂ
        ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) a]
    rfl
  rw [htrans] at hle1
  exact hle1

end Generic

end ConstantFieldLift


/-! ### Two `private` helpers of the 346 headline

The pin keeps its `hint` and `keyUB` as local `have`s of the 200-line `solution`; hoisted
here as `private` lemmas so each elaboration step is charged to its own command (the pin's
single command needed `maxHeartbeats 6400000`, this project's cap is 200 000).  They are the
pin's statements, generalised over the function field / model field pair, and are `private`
so `check_port` does not see them (it skips private declarations). -/

/-! ## Row 346 — the `jq`-ramification over `ℚ̄` -/

/-! ### The 346 headline's four `private` helpers

The pin keeps these as local `have`s of its 200-line `solution`, whose single command carries
`set_option maxHeartbeats 6400000` / `synthInstance.maxHeartbeats 1600000`
(`P2M/Sol/S_ModularCurve_ord_le_three_…_algebraicClosure.lean:179-180`).  Neither option is
transcribable, so the pin's `have`-blocks are cut into `private` lemmas — each charged to its
own command, with the budgets summing to less than the removed one (workorder §"The gates",
gate 7 / the manager's carve recipe).  They are `private`, so `check_port` skips them. -/

private theorem natCard_fibre_le {K : Type*} [Field K] [Algebra ℂ K] {F : Type*}
    [Field F] [Algebra ℂ F] (x : F) (t : K)
    (hfin : FiniteDimensional (IntermediateField.adjoin ℂ ({t} : Set K)) K)
    (hint : ∀ ψ : F →ₐ[ℂ] K, ψ x = t → ψ.toRingHom.IsIntegral)
    (W₀ : Place ℂ K)
    (h4 : ∀ (ψ ψ' : F →ₐ[ℂ] K) (hψ : ψ x = t) (hψ' : ψ' x = t),
        W₀.restrictAlong ψ (hint ψ hψ) = W₀.restrictAlong ψ' (hint ψ' hψ') ↔
          ∃ σ : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K,
            SemilinearAut.ofAlgAut (σ.restrictScalars ℂ) • W₀ = W₀ ∧
              ψ' = ((σ : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K).restrictScalars ℂ).comp ψ)
    (ψ : F →ₐ[ℂ] K) (hψ : ψ x = t) :
    Nat.card {ψ' : {ψ' : F →ₐ[ℂ] K // ψ' x = t} //
        W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)} ≤
      Nat.card {σ : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K //
        SemilinearAut.ofAlgAut (σ.restrictScalars ℂ) • W₀ = W₀} := by
  haveI := hfin
  haveI : Finite {σ : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K //
      SemilinearAut.ofAlgAut (σ.restrictScalars ℂ) • W₀ = W₀} := Subtype.finite
  have htmem : t ∈ IntermediateField.adjoin ℂ ({t} : Set K) :=
    IntermediateField.mem_adjoin_simple_self ℂ t
  have hσt : ∀ σ : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K, σ t = t := fun σ =>
    σ.commutes (⟨t, htmem⟩ : ↥(IntermediateField.adjoin ℂ ({t} : Set K)))
  let g : {σ : K ≃ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K //
        SemilinearAut.ofAlgAut (σ.restrictScalars ℂ) • W₀ = W₀} →
      {ψ' : {ψ' : F →ₐ[ℂ] K // ψ' x = t} //
        W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)} := fun σ =>
    have hψσ : (((σ.1 : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K).restrictScalars ℂ).comp ψ)
        x = t := by
      rw [AlgHom.comp_apply, AlgHom.restrictScalars_apply, hψ]; exact hσt σ.1
    ⟨⟨((σ.1 : K →ₐ[↥(IntermediateField.adjoin ℂ ({t} : Set K))] K).restrictScalars ℂ).comp ψ, hψσ⟩,
      ((h4 ψ _ hψ hψσ).mpr ⟨σ.1, σ.2, rfl⟩).symm⟩
  have hg : Function.Surjective g := by
    rintro ⟨⟨ψ', hψ'⟩, heq⟩
    obtain ⟨σ, hσ, rfl⟩ := (h4 ψ ψ' hψ hψ').mp heq.symm
    exact ⟨⟨σ, hσ⟩, rfl⟩
  exact_mod_cast Nat.card_le_card_of_surjective g hg

private theorem ord_le_of_ord_pos {K : Type} [Field K] [Algebra ℂ K] {F : Type}
    [Field F] [Algebra ℂ F] (x : F) (t : K)
    (hfin : FiniteDimensional (IntermediateField.adjoin ℂ ({t} : Set K)) K)
    (hgal : IsGalois (IntermediateField.adjoin ℂ ({t} : Set K)) K)
    (hint : ∀ ψ : F →ₐ[ℂ] K, ψ x = t → ψ.toRingHom.IsIntegral)
    (φ : F →ₐ[ℂ] K) (hφ : φ x = t)
    (j₀ : ℂ) (W₀ : Place ℂ K) (hW₀ : 0 < W₀.ord (t - algebraMap ℂ K j₀))
    (w : Place ℂ F) (hw : 0 < w.ord (x - algebraMap ℂ F j₀)) :
    w.ord (x - algebraMap ℂ F j₀) ≤ W₀.ord (t - algebraMap ℂ K j₀) := by
  obtain ⟨h1, -, h3, h4, h5⟩ :=
    Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois (K := ℂ) x t j₀ φ hφ
      hfin hgal hint W₀ hW₀
  obtain ⟨ψ, hψ, rfl⟩ := h3 w hw
  rw [h5 ψ hψ, h1]
  exact_mod_cast natCard_fibre_le x t hfin hint W₀ h4 ψ hψ

private theorem finiteDimensional_adjoin_singleton {K : Type*} [Field K] [Algebra ℂ K]
    (E : IntermediateField ℂ K) (t : K) (e : ↥E) (het : (e : K) = t)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({t} : Set K)) K] :
    FiniteDimensional (IntermediateField.adjoin ℂ ({e} : Set ↥E)) ↥E := by
  have hlift : IntermediateField.lift (IntermediateField.adjoin ℂ ({e} : Set ↥E)) =
      IntermediateField.adjoin ℂ ({t} : Set K) := by
    rw [IntermediateField.lift_adjoin_simple, het]
  have hle' : IntermediateField.adjoin ℂ ({t} : Set K) ≤ E := by
    rw [← hlift]; exact IntermediateField.lift_le _
  let E₂ : IntermediateField ↥(IntermediateField.adjoin ℂ ({t} : Set K)) K :=
    IntermediateField.extendScalars hle'
  have hE₂ : FiniteDimensional ↥(IntermediateField.adjoin ℂ ({t} : Set K)) ↥E₂ :=
    IntermediateField.finiteDimensional_left E₂
  let e₁ : ↥(IntermediateField.adjoin ℂ ({e} : Set ↥E)) ≃ₐ[ℂ]
      ↥(IntermediateField.adjoin ℂ ({t} : Set K)) :=
    (IntermediateField.liftAlgEquiv _).trans (IntermediateField.equivOfEq hlift)
  let e₂ : ↥E₂ ≃+* ↥E := RingEquiv.refl _
  exact Module.Finite.of_equiv_equiv e₁.symm.toRingEquiv e₂ (by
    refine RingHom.ext fun w => Subtype.ext ?_
    have h1 : ∀ v : ↥(IntermediateField.adjoin ℂ ({e} : Set ↥E)),
        ((e₁ v : ↥(IntermediateField.adjoin ℂ ({t} : Set K))) : K) = ((v : ↥E) : K) :=
      fun v => rfl
    have h2 := congrArg (fun u : ↥(IntermediateField.adjoin ℂ ({t} : Set K)) => (u : K))
      (e₁.apply_symm_apply w)
    simp only [h1] at h2
    exact h2)

private theorem isIntegral_of_algHom_apply_eq {K : Type*} [Field K] [Algebra ℂ K] {E : Type*}
    [Field E] [Algebra ℂ E] (x : E) (t : K)
    [FiniteDimensional (IntermediateField.adjoin ℂ ({t} : Set K)) K]
    (ψ : E →ₐ[ℂ] K) (hψ : ψ x = t) : ψ.toRingHom.IsIntegral := by
  let S : Subalgebra ℂ K := ψ.range
  have hleS : (IntermediateField.adjoin ℂ ({t} : Set K)).toSubalgebra ≤ S := by
    have h : IntermediateField.adjoin ℂ ({t} : Set K) ≤ ψ.fieldRange :=
      IntermediateField.adjoin_simple_le_iff.mpr ⟨x, hψ⟩
    intro w hw
    exact (AlgHom.mem_fieldRange.mp (h hw))
  letI algRS : Algebra ↥(IntermediateField.adjoin ℂ ({t} : Set K)) ↥S :=
    (Subalgebra.inclusion hleS).toRingHom.toAlgebra
  haveI : IsScalarTower ↥(IntermediateField.adjoin ℂ ({t} : Set K)) ↥S K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite ↥S K := Module.Finite.of_restrictScalars_finite
    ↥(IntermediateField.adjoin ℂ ({t} : Set K)) _ _
  haveI : Algebra.IsIntegral ↥S K := Algebra.IsIntegral.of_finite _ _
  have hS : (algebraMap ↥S K).IsIntegral := fun y => Algebra.IsIntegral.isIntegral (R := ↥S) y
  let e : E ≃ₐ[ℂ] ↥S := AlgEquiv.ofInjective ψ ψ.toRingHom.injective
  have he : ψ.toRingHom = (algebraMap ↥S K).comp e.toAlgHom.toRingHom := by
    refine RingHom.ext fun y => ?_
    change ψ y = ((e y : ↥S) : K)
    rw [AlgEquiv.ofInjective_apply]
  rw [he]
  exact RingHom.IsIntegral.trans _ _ (RingHom.isIntegral_of_surjective e.toAlgHom.toRingHom
    e.surjective) hS

open ConstantFieldLift in
theorem ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
      (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
    P.ord y ≤ 3 ∧
    P.ord (y - 1728) ≤ 2 ∧
    (∀ a : AlgebraicClosure ℚ, a ≠ 0 → a ≠ 1728 →
      P.ord (y - algebraMap (AlgebraicClosure ℚ)
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) a) ≤ 1) := by
  classical

  haveI : IsDomain ↥(ModularCurve.LevelN.ring M) := isDomain_levelN_ring M
  let K : Type := FractionRing ↥(ModularCurve.LevelN.ring M)
  letI algCK : Algebra ℂ K := inferInstance
  haveI : IsScalarTower ℂ ↥(ModularCurve.LevelN.ring M) K := inferInstance

  let ιa : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let ι : AlgebraicClosure ℚ →+* ℂ := ιa.toRingHom

  have hΓM : CongruenceSubgroup.Gamma M ≤ Γ := by
    refine le_trans (fun γ hγ => ?_) hΓ
    rw [CongruenceSubgroup.Gamma_mem] at hγ
    rw [CongruenceSubgroup.Gamma1_mem]
    exact ⟨hγ.1, hγ.2.2.2, hγ.2.2.1⟩
  have hT : ModularGroup.T ∈ Γ :=
    hΓ (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])

  obtain ⟨Φ, hΦc, hΦy, -⟩ :=
    ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN M Γ hΓM hT ι K

  obtain ⟨hst, σ, hσ, hker, hfix, htr, hfd, hdeg, hgal⟩ :=
    ModularCurve.LevelN.exists_monoidHom_algEquiv_fixedField_eq_adjoin M K

  obtain ⟨⟨W1728, hW1728pos, hW1728⟩, ⟨W0, hW0pos, hW0⟩, -⟩ :=
    ModularCurve.LevelN.exists_place_ord_jGen_le_two_three_level M K

  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  let t : K := algebraMap ↥(ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)
  have hΦy' : Φ y = t := hΦy y hy
  let E : IntermediateField ℂ K := IntermediateField.adjoin ℂ (Set.range Φ)
  have hΦmem : ∀ f, Φ f ∈ E := fun f => IntermediateField.subset_adjoin ℂ _ ⟨f, rfl⟩
  let ΦE : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.qExpFunctionFieldC ℚ Γ)) →+* ↥E := Φ.codRestrict E hΦmem
  have hΦE : ∀ f, ((ΦE f : ↥E) : K) = Φ f := fun f => RingHom.codRestrict_apply Φ E hΦmem f
  have hcoeC : ∀ z : ℂ, ((algebraMap ℂ ↥E z : ↥E) : K) = algebraMap ℂ K z := fun _ => rfl
  letI algFE : Algebra ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥E := ΦE.toAlgebra
  letI algQC : Algebra (AlgebraicClosure ℚ) ℂ := ι.toAlgebra
  letI algQE : Algebra (AlgebraicClosure ℚ) ↥E := ((algebraMap ℂ ↥E).comp ι).toAlgebra
  haveI : IsScalarTower (AlgebraicClosure ℚ) ℂ ↥E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
      ↥E := IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (by
      change ((algebraMap ℂ ↥E (ι c) : ↥E) : K) =
        ((ΦE (algebraMap (AlgebraicClosure ℚ)
          ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.qExpFunctionFieldC ℚ Γ)) c) : ↥E) : K)
      rw [hcoeC, hΦE, hΦc])
  obtain ⟨x₀, hx₀tr, hx₀fd⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
      (AlgebraicClosure ℚ) Γ hT
  haveI : IsCurveOver (AlgebraicClosure ℚ)
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
    isCurveOver_of_transcendental_of_perfectField hx₀tr hx₀fd

  have htr' : Transcendental ℂ (ΦE y) := fun h => htr (by
    have h' := IntermediateField.isAlgebraic_iff.mp h
    rwa [hΦE, hΦy'] at h')
  haveI := hfd
  have hEfd : FiniteDimensional ↥(IntermediateField.adjoin ℂ ({ΦE y} : Set ↥E)) ↥E :=
    finiteDimensional_adjoin_singleton E t (ΦE y) ((hΦE y).trans hΦy')
  have hgen : IntermediateField.adjoin ℂ (Set.range (algebraMap
      ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥E)) = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    have : Subtype.val '' Set.range (algebraMap
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ)) ↥E) = Set.range Φ := by
      ext w
      constructor
      · rintro ⟨_, ⟨f, rfl⟩, rfl⟩; exact ⟨f, (hΦE f).symm⟩
      · rintro ⟨f, rfl⟩; exact ⟨ΦE f, ⟨f, rfl⟩, hΦE f⟩
    rw [this]
  obtain ⟨P', -, hP'ord, -⟩ := Place.exists_comap_algebraMap_eq_of_constantFieldExtension
    (AlgebraicClosure ℚ)
    ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    ℂ ↥E ⟨x₀, hx₀tr, hx₀fd⟩ ⟨ΦE y, htr', hEfd⟩ hgen P

  have hvaly : E.val (ΦE y) = t := by rw [IntermediateField.coe_val]; exact (hΦE y).trans hΦy'
  have hint : ∀ ψ : ↥E →ₐ[ℂ] K, ψ (ΦE y) = t → ψ.toRingHom.IsIntegral :=
    fun ψ hψ => isIntegral_of_algHom_apply_eq (ΦE y) t ψ hψ
  have keyUB : ∀ (j₀ : ℂ) (W₀ : Place ℂ K), 0 < W₀.ord (t - algebraMap ℂ K j₀) →
      ∀ w : Place ℂ ↥E, 0 < w.ord (ΦE y - algebraMap ℂ ↥E j₀) →
        w.ord (ΦE y - algebraMap ℂ ↥E j₀) ≤ W₀.ord (t - algebraMap ℂ K j₀) :=
    fun j₀ W₀ hW₀ w hw =>
      ord_le_of_ord_pos (ΦE y) t hfd hgal hint E.val hvaly j₀ W₀ hW₀ w hw

  have h0E : P'.ord (ΦE y) = P.ord y := by rw [← hP'ord y]; rfl
  have h1728E : P'.ord (ΦE y - 1728) = P.ord (y - 1728) := by
    rw [← hP'ord (y - 1728), map_sub, map_ofNat]; rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    by_cases hpos : 0 < P.ord y
    · have hk := keyUB 0 W0 (by rw [map_zero, sub_zero]; exact hW0pos) P'
      simp only [map_zero, sub_zero] at hk
      rw [h0E] at hk
      exact (hk hpos).trans hW0
    · linarith
  ·
    by_cases hpos : 0 < P.ord (y - 1728)
    · have hk := keyUB 1728 W1728 (by rw [map_ofNat]; exact hW1728pos) P'
      simp only [map_ofNat] at hk
      rw [h1728E] at hk
      exact (hk hpos).trans hW1728
    · linarith
  ·
    intro a ha0 ha1728
    exact ord_sub_algebraMap_le_one_algebraicClosure M Γ hΓ hT ιa y hy P a ha0 ha1728

/-! ## The Riemann–Hurwitz count (pin `RiemannHurwitzCount`) -/

namespace RiemannHurwitzCount

universe u v

set_option linter.unusedSectionVars false

section Package

variable (k : Type u) [Field k] {F : Type v} [Field F] [Algebra k F]
  (x : F) (hx : Transcendental k x) (hfin : FiniteDimensional k⟮x⟯ F)
  (hsep : Algebra.IsSeparable k⟮x⟯ F)

include hx hfin hsep

theorem isCurveOver_pkg : IsCurveOver k F :=
  AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable k F x hx hfin hsep

omit hsep in
theorem essFiniteType_pkg : Algebra.EssFiniteType k F :=
  AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfin

theorem with_ratFunc {P : Prop}
    (h : ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F],
      algebraMap (RatFunc k) F RatFunc.X = x →
      Module.finrank (RatFunc k) F = Module.finrank k⟮x⟯ F → P) : P := by
  haveI := hfin
  haveI := hsep
  let e : RatFunc k ≃ₐ[k] k⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  letI : Algebra (RatFunc k) F := ((algebraMap k⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc k) F) (e.symm.toRingEquiv : k⟮x⟯ →+* RatFunc k)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap k⟮x⟯ F) := by
    ext y
    show algebraMap k⟮x⟯ F (e (e.symm y)) = algebraMap k⟮x⟯ F y
    rw [e.apply_symm_apply]
  haveI : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap k F a = algebraMap k⟮x⟯ F (e (algebraMap k (RatFunc k) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI hfd : FiniteDimensional (RatFunc k) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc k) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have hX : algebraMap (RatFunc k) F RatFunc.X = x := by
    show algebraMap k⟮x⟯ F (e RatFunc.X) = x
    have h := RatFunc.algEquivOfTranscendental_X x hx
    exact h
  have hn : Module.finrank (RatFunc k) F = Module.finrank k⟮x⟯ F :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl F) (by ext y; rfl)
  exact h hX hn

variable [IsAlgClosed k]

theorem hasCanonicalDivisor_pkg : HasCanonicalDivisor (K := k) (F := F) := by
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := essFiniteType_pkg k x hx hfin
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

theorem dCoordGenerates_pkg : ∀ v : Place k F, v.DCoordGenerates := by
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := essFiniteType_pkg k x hx hfin
  exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

theorem riemannRoch_and_constantsAreBase_pkg :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    FunctionFieldRiemannRoch k F ∧ ConstantsAreBase k F := by
  classical
  haveI := hfin
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
  haveI := dCoordGenerates_pkg k x hx hfin hsep
  haveI : IsCurveOver k (RatFunc k) := AlgebraicCurve.isCurveOver_ratFunc k
  haveI : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial k))
  haveI : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  haveI : ∀ v : Place k (RatFunc k), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  refine with_ratFunc k x hx hfin hsep ?_
  intro _ _ _ _ _ _
  haveI : Algebra.IsIntegral (RatFunc k) F := Algebra.IsIntegral.of_finite _ _
  exact ⟨AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver,
    AlgebraicCurve.constantsAreBase_of_isAlgClosed k F⟩

theorem genus_eq_genusFF_pkg :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    genus k F = genusFF k F := by
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
  haveI := dCoordGenerates_pkg k x hx hfin hsep
  haveI := essFiniteType_pkg k x hx hfin
  have rr := riemannRoch_and_constantsAreBase_pkg k x hx hfin hsep
  have hSG : StichtenothGenusExists k F :=
    AlgebraicCurve.stichtenothGenusExists_of_isCurveOver rr.2
  have wda : WeilDualityAdelic k F :=
    AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists rr.1 hSG
  exact AlgebraicCurve.genus_eq_genusFF rr.1 wda rr.2

theorem degree_canonical_pkg :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    ∀ {ω : Ω[F⁄k]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genusFF k F : ℤ) - 2 := by
  intro ω hω
  haveI := isCurveOver_pkg k x hx hfin hsep
  haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
  haveI := dCoordGenerates_pkg k x hx hfin hsep
  have rr := riemannRoch_and_constantsAreBase_pkg k x hx hfin hsep
  rw [← genus_eq_genusFF_pkg k x hx hfin hsep]
  exact AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch rr.1 rr.2 hω

end Package

section Bridge

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [PerfectField K]
  (x : F) [FiniteDimensional K⟮x⟯ F]

omit [PerfectField K] [FiniteDimensional K⟮x⟯ F] in
theorem exists_dCoord_eq_D (v : Place K F) : ∃ t : F, v.ord t = 1 ∧ v.dCoord = D K F t :=
  ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F),
    v.ord_coe_irreducible
      (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec, rfl⟩

omit [PerfectField K] [FiniteDimensional K⟮x⟯ F] in
theorem coeff_unique {η : Ω[F⁄K]} (hη : η ≠ 0) {a b : F} (h : a • η = b • η) : a = b := by
  have h0 : (a - b) • η = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hη

include x in

theorem ordDiff_eq_ordDifferential (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (ω : Ω[F⁄K]) : v.ordDiff ω = v.ordDifferential ω := by
  obtain ⟨t₂, ht₂, hdc⟩ := exists_dCoord_eq_D v
  have ht₁ : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  have hc_smul : Place.diffCoeff v.uniformizer_alt (D K F t₂) • D K F v.uniformizer_alt = D K F t₂ :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht₁ _
  have hc'_smul : Place.diffCoeff t₂ (D K F v.uniformizer_alt) • D K F t₂ = D K F v.uniformizer_alt :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht₂ _
  have hD₁ : D K F v.uniformizer_alt ≠ 0 := by
    intro h0
    obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
    have h := Place.diffCoeff_smul_D_of_ord_eq_one x v ht₁ ω
    rw [h0, smul_zero] at h
    exact hω h.symm
  have hcc' : Place.diffCoeff t₂ (D K F v.uniformizer_alt) *
      Place.diffCoeff v.uniformizer_alt (D K F t₂) = 1 := by
    refine coeff_unique hD₁ ?_
    rw [mul_smul, hc_smul, hc'_smul, one_smul]
  have hc0 : Place.diffCoeff v.uniformizer_alt (D K F t₂) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcc'
    exact zero_ne_one hcc'
  have hc'0 : Place.diffCoeff t₂ (D K F v.uniformizer_alt) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcc'
    exact zero_ne_one hcc'
  have hordc : v.ord (Place.diffCoeff v.uniformizer_alt (D K F t₂)) = 0 := by
    have h1 : 0 ≤ v.ord (Place.diffCoeff v.uniformizer_alt (D K F t₂)) :=
      Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht₁ (by rw [ht₂]; exact zero_le_one)
    have h2 : 0 ≤ v.ord (Place.diffCoeff t₂ (D K F v.uniformizer_alt)) :=
      Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht₂ (by rw [ht₁]; exact zero_le_one)
    have h3 := v.ord_mul hc'0 hc0
    rw [hcc', v.ord_one] at h3
    omega
  have ha : Place.diffCoeff v.uniformizer_alt ω • D K F v.uniformizer_alt = ω :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht₁ ω
  have hb : v.differentialCoeff ω • v.dCoord = ω := v.differentialCoeff_smul_dCoord ω
  have hab : Place.diffCoeff v.uniformizer_alt ω =
      v.differentialCoeff ω * Place.diffCoeff v.uniformizer_alt (D K F t₂) := by
    refine coeff_unique hD₁ ?_
    rw [ha, mul_smul, hc_smul, ← hdc, hb]
  rw [Place.ordDiff_def, Place.ordDifferential, hab]
  rcases eq_or_ne (v.differentialCoeff ω) 0 with hb0 | hb0
  · rw [hb0, zero_mul]
  · rw [v.ord_mul hb0 hc0, hordc, add_zero]

end Bridge

section Identity

variable (k : Type u) [Field k] [IsAlgClosed k] {F : Type v} [Field F] [Algebra k F]

theorem exists_sum_ordDiff_D_eq (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F) :
    ∃ S : Finset (Place k F), (∀ P, P ∉ S → P.ordDiff (KaehlerDifferential.D k F x) = 0) ∧
      ∑ P ∈ S, P.ordDiff (KaehlerDifferential.D k F x) = 2 * (genusFF k F : ℤ) - 2 := by
  classical
  haveI hC : IsCurveOver k F := isCurveOver_pkg k x hx hfin hsep
  haveI hK : HasCanonicalDivisor (K := k) (F := F) := hasCanonicalDivisor_pkg k x hx hfin hsep
  haveI hG : ∀ v : Place k F, v.DCoordGenerates := dCoordGenerates_pkg k x hx hfin hsep
  haveI := hfin
  have hω : KaehlerDifferential.D k F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental k x hx
  have hWapp : ∀ P : Place k F, canonicalDivisorOf hω P = P.ordDiff (D k F x) := fun P => by
    rw [canonicalDivisorOf_apply, ordDiff_eq_ordDifferential x P]
  have hWdeg : (canonicalDivisorOf hω).degree = 2 * (genusFF k F : ℤ) - 2 :=
    degree_canonical_pkg k x hx hfin hsep hω
  have hdeg1 : ∀ P : Place k F, P.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  refine ⟨(canonicalDivisorOf hω).support, fun P hP => ?_, ?_⟩
  · rw [← hWapp]; exact Finsupp.notMem_support_iff.mp hP
  · rw [← hWdeg, Divisor.degree_eq_sum_support]
    exact (Finset.sum_congr rfl fun P _ => by rw [hWapp, hdeg1, Nat.cast_one, mul_one]).symm

end Identity

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_sub_algebraMap_of_ord_neg (v : Place K F) {x : F} (c : K) (hx : v.ord x < 0) :
    v.ord (x - algebraMap K F c) = v.ord x := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hc0 : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have hxc : x - algebraMap K F c ≠ 0 := by
    intro h
    have : v.ord x = 0 := by
      rw [sub_eq_zero.mp h]; exact v.ord_algebraMap c
    omega
  have h1 := v.min_ord_le_ord_add (f := x) (g := -algebraMap K F c)
    (by rwa [← sub_eq_add_neg])
  rw [← sub_eq_add_neg, ← map_neg, v.ord_algebraMap] at h1
  have h2 := v.min_ord_le_ord_add (f := x - algebraMap K F c) (g := algebraMap K F c)
    (by rw [sub_add_cancel]; exact hx0)
  rw [sub_add_cancel, v.ord_algebraMap] at h2
  omega

theorem ord_neg_of_ord_sub_algebraMap_neg (v : Place K F) {x : F} (c : K)
    (hx : v.ord (x - algebraMap K F c) < 0) : v.ord x < 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using hx
  have hc0 : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have hxc : x - algebraMap K F c ≠ 0 := by rintro h; rw [h] at hx; simp at hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_sub, ← map_neg, v.ord_algebraMap] at hx
    exact lt_irrefl _ hx
  have h2 := v.min_ord_le_ord_add (f := x - algebraMap K F c) (g := algebraMap K F c)
    (by rw [sub_add_cancel]; exact hx0)
  rw [sub_add_cancel, v.ord_algebraMap] at h2
  by_contra h
  have h1 := v.min_ord_le_ord_add (f := x) (g := -algebraMap K F c)
    (by rwa [← sub_eq_add_neg])
  rw [← sub_eq_add_neg, ← map_neg, v.ord_algebraMap] at h1
  omega

theorem ord_nonneg_of_ord_sub_algebraMap_pos (v : Place K F) {x : F} (c : K)
    (h : 0 < v.ord (x - algebraMap K F c)) : 0 ≤ v.ord x := by
  by_contra hneg
  have := ord_sub_algebraMap_of_ord_neg v c (not_le.mp hneg)
  omega

theorem not_ord_sub_pos_of_ord_sub_pos (v : Place K F) {x : F} {c c' : K} (hcc' : c ≠ c')
    (h : 0 < v.ord (x - algebraMap K F c)) : ¬ 0 < v.ord (x - algebraMap K F c') := by
  intro h'
  have hne : x - algebraMap K F c ≠ 0 := by rintro hh; rw [hh] at h; simp at h
  have hne' : x - algebraMap K F c' ≠ 0 := by rintro hh; rw [hh] at h'; simp at h'
  have hd : algebraMap K F (c' - c) ≠ 0 := (map_ne_zero _).mpr (sub_ne_zero.mpr hcc'.symm)
  have hsum : (x - algebraMap K F c) + -(x - algebraMap K F c') = algebraMap K F (c' - c) := by
    rw [map_sub]; ring
  have key := v.min_ord_le_ord_add (f := x - algebraMap K F c) (g := -(x - algebraMap K F c'))
    (by rw [hsum]; exact hd)
  rw [hsum, v.ord_algebraMap] at key
  have : v.ord (-(x - algebraMap K F c')) = v.ord (x - algebraMap K F c') := by
    rw [show -(x - algebraMap K F c') = (x - algebraMap K F c') * (-1) by ring,
      v.ord_mul hne' (by norm_num), show (-1 : F) = algebraMap K F (-1) by simp,
      v.ord_algebraMap, add_zero]
  rw [this] at key
  have hmin : 0 < min (v.ord (x - algebraMap K F c)) (v.ord (x - algebraMap K F c')) := lt_min h h'
  omega

theorem exists_finset_zeros [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    ∃ T : Finset (Place K F), ∀ v, v ∈ T ↔ 0 < v.ord f := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine ⟨D.support.filter fun v => 0 < D v, fun v => ?_⟩
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hD v]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem exists_finset_poles [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) :
    ∃ T : Finset (Place K F), ∀ v, v ∈ T ↔ v.ord f < 0 := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  refine ⟨D.support.filter fun v => D v < 0, fun v => ?_⟩
  rw [Finset.mem_filter, Finsupp.mem_support_iff, hD v]
  exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩

theorem natCard_subtype_eq_card {γ : Type*} (T : Finset γ) (p : γ → Prop)
    (hT : ∀ v, v ∈ T ↔ p v) : Nat.card {v // p v} = T.card := by
  classical
  have e : {v // p v} ≃ {v // v ∈ T} := Equiv.subtypeEquivRight fun v => (hT v).symm
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

variable [IsAlgClosed K] [IsCurveOver K F]

theorem exists_ord_sub_algebraMap_pos (v : Place K F) {x : F} (hx : Transcendental K x)
    (h : 0 ≤ v.ord x) : ∃ c : K, 0 < v.ord (x - algebraMap K F c) := by
  have hxmem : x ∈ v.toValuationSubring := W7XH.mem_of_ord_nonneg v h
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨c, hc⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring ⟨x, hxmem⟩)
  refine ⟨c, ?_⟩
  have hsub_mem : x - algebraMap K F c ∈ v.toValuationSubring :=
    v.toValuationSubring.sub_mem hxmem (v.algebraMap_mem' c)
  have hne : x - algebraMap K F c ≠ 0 := by
    intro h0
    apply hx
    rw [sub_eq_zero] at h0
    rw [h0]; exact isAlgebraic_algebraMap c
  refine Place.ord_pos_of_mem_maximalIdeal v hne hsub_mem ?_
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hres : IsLocalRing.residue v.toValuationSubring ⟨x - algebraMap K F c, hsub_mem⟩ =
      IsLocalRing.residue v.toValuationSubring ⟨x, hxmem⟩ -
        IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring c) := by
    rw [← map_sub]
    congr 1
  rw [hres, ← hc]
  change algebraMap K v.ResidueField c -
    (IsLocalRing.residue v.toValuationSubring) (algebraMap K v.toValuationSubring c) = 0
  rw [sub_eq_zero]
  rfl

theorem degree_eq_sum_support' (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v := by
  rw [Divisor.degree_eq_sum_support]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed v]; simp

theorem sum_ord_sub_algebraMap_eq_finrank {x : F} (hx : Transcendental K x)
    [FiniteDimensional K⟮x⟯ F] (c : K)
    (T : Finset (Place K F)) (hT : ∀ v, v ∈ T ↔ 0 < v.ord (x - algebraMap K F c)) :
    ∑ v ∈ T, v.ord (x - algebraMap K F c) = (Module.finrank K⟮x⟯ F : ℤ) := by
  classical
  set f := x - algebraMap K F c with hf
  have hf0 : f ≠ 0 := by
    intro h
    apply hx
    rw [hf, sub_eq_zero] at h
    rw [h]; exact isAlgebraic_algebraMap c
  obtain ⟨D, hD, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  set Dinf : Divisor K F := -(D.filter fun v => D v < 0) with hDinf
  have hDinf_apply : ∀ v, Dinf v = max 0 (-v.ord x) := by
    intro v
    rw [hDinf, Finsupp.neg_apply, Finsupp.filter_apply]
    split_ifs with h
    · rw [hD v] at h
      have hx' := ord_neg_of_ord_sub_algebraMap_neg v c h
      rw [hD v, ord_sub_algebraMap_of_ord_neg v c hx', max_eq_right (by omega)]
    · rw [hD v] at h
      have : 0 ≤ v.ord x := by
        by_contra hneg
        exact h (by rw [ord_sub_algebraMap_of_ord_neg v c (by omega)]; omega)
      rw [neg_zero, max_eq_left (by omega)]
  have hdegInf := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx Dinf
    hDinf_apply
  have hsplit : (D.filter fun v => 0 < D v) + (D.filter fun v => D v < 0) = D := by
    ext v
    rw [Finsupp.add_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    split_ifs with h1 h2 <;> omega
  have hdegpos : Divisor.degree (D.filter fun v => 0 < D v) = (Module.finrank K⟮x⟯ F : ℤ) := by
    have h := congrArg Divisor.degree hsplit
    rw [map_add, hdeg] at h
    have h2 : Divisor.degree (D.filter fun v => D v < 0) = -Divisor.degree Dinf := by
      rw [hDinf, map_neg, neg_neg]
    rw [h2, hdegInf] at h
    linarith
  rw [degree_eq_sum_support', Finsupp.support_filter] at hdegpos
  have hTeq : T = D.support.filter fun v => 0 < D v := by
    ext v
    rw [hT, Finset.mem_filter, Finsupp.mem_support_iff, hD v]
    constructor
    · intro h; exact ⟨by omega, h⟩
    · intro h; exact h.2
  rw [hTeq, ← hdegpos]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finsupp.filter_apply, ite_eq_left (Finset.mem_filter.mp hv).2, hD v]

theorem sum_neg_ord_eq_finrank {x : F} (hx : Transcendental K x)
    [FiniteDimensional K⟮x⟯ F]
    (T : Finset (Place K F)) (hT : ∀ v, v ∈ T ↔ v.ord x < 0) :
    ∑ v ∈ T, (-v.ord x) = (Module.finrank K⟮x⟯ F : ℤ) := by
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl; exact hx isAlgebraic_zero
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) x hx0
  set Dinf : Divisor K F := -(D.filter fun v => D v < 0) with hDinf
  have hDinf_apply : ∀ v, Dinf v = max 0 (-v.ord x) := by
    intro v
    rw [hDinf, Finsupp.neg_apply, Finsupp.filter_apply, hD v]
    split_ifs with h
    · rw [max_eq_right (by omega)]
    · rw [neg_zero, max_eq_left (by omega)]
  have hdegInf := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx Dinf
    hDinf_apply
  rw [degree_eq_sum_support'] at hdegInf
  have hTeq : T = Dinf.support := by
    ext v
    rw [hT, Finsupp.mem_support_iff, hDinf_apply]
    constructor
    · intro h; exact (lt_max_of_lt_right (by omega)).ne'
    · intro h
      by_contra h'
      exact h (max_eq_left (by omega))
  rw [hTeq, ← hdegInf]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [hDinf_apply]
  rw [Finsupp.mem_support_iff, hDinf_apply] at hv
  rcases le_or_gt 0 (v.ord x) with h | h
  · exact absurd (max_eq_left (by omega : -v.ord x ≤ 0)) hv
  · rw [max_eq_right (by omega)]

end Generic

section Descent

local instance isAlgebraicQbar_rh : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

def iota : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift

local notation "ℚbar" => AlgebraicClosure ℚ

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

theorem coeffMap_iota_coeffEmb (y : LaurentSeries ℚ) :
    coeffMap (iota : ℚbar →+* ℂ) (coeffEmb ℚbar y) = coeffEmb ℂ y := by
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  refine coeffMap_congr ?_ y
  ext c
  simp

theorem coeffMap_iota_algebraMap (c : ℚbar) :
    coeffMap (iota : ℚbar →+* ℂ) (algebraMap ℚbar (LaurentSeries ℚbar) c) =
      algebraMap ℂ (LaurentSeries ℂ) (iota c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]
  rfl

theorem coeffMap_iota_mem {x : LaurentSeries ℚbar} (hx : x ∈ laurentBaseChange ℚbar F₀) :
    coeffMap (iota : ℚbar →+* ℂ) x ∈ laurentBaseChange ℂ F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  refine Subfield.closure_induction (p := fun x _ => coeffMap (iota : ℚbar →+* ℂ) x ∈
      laurentBaseChange ℂ F₀) ?_ (by simp) ?_ ?_ ?_ ?_ hx
  · rintro x (⟨c, rfl⟩ | ⟨y, hy, rfl⟩)
    · rw [coeffMap_iota_algebraMap]
      exact (laurentBaseChange ℂ F₀).algebraMap_mem _
    · rw [coeffMap_iota_coeffEmb]
      exact coeffEmb_mem_laurentBaseChange ℂ hy
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro x _ hx; rw [map_neg]; exact neg_mem hx
  · intro x _ hx; rw [map_inv₀]; exact inv_mem hx
  · intro x y _ _ hx hy; rw [map_mul]; exact mul_mem hx hy

def psi : laurentBaseChange ℚbar F₀ →+* laurentBaseChange ℂ F₀ where
  toFun x := ⟨coeffMap (iota : ℚbar →+* ℂ) x, coeffMap_iota_mem F₀ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[scoped simp] theorem coe_psi (x : laurentBaseChange ℚbar F₀) :
    (psi F₀ x : LaurentSeries ℂ) = coeffMap (iota : ℚbar →+* ℂ) x := rfl

theorem psi_algebraMap (c : ℚbar) :
    psi F₀ (algebraMap ℚbar (laurentBaseChange ℚbar F₀) c) =
      algebraMap ℂ (laurentBaseChange ℂ F₀) (iota c) :=
  Subtype.ext (coeffMap_iota_algebraMap c)

theorem psi_coeffEmb (y : LaurentSeries ℚ) (hy : y ∈ F₀) :
    psi F₀ ⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩ =
      ⟨coeffEmb ℂ y, coeffEmb_mem_laurentBaseChange ℂ hy⟩ :=
  Subtype.ext (coeffMap_iota_coeffEmb y)

theorem exists_place_complex_ord_eq (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (v : Place ℚbar (laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))) :
    ∃ v' : Place ℂ (laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)),
      ∀ f, v'.ord (psi (qExpFunctionFieldC ℚ Γ) f) = v.ord f := by
  let F₀ := qExpFunctionFieldC ℚ Γ
  letI : Algebra (laurentBaseChange ℚbar F₀) (laurentBaseChange ℂ F₀) := (psi F₀).toAlgebra
  letI : Algebra ℚbar ℂ := (iota : ℚbar →+* ℂ).toAlgebra
  letI : Algebra ℚbar (laurentBaseChange ℂ F₀) :=
    ((algebraMap ℂ (laurentBaseChange ℂ F₀)).comp (iota : ℚbar →+* ℂ)).toAlgebra
  haveI : IsScalarTower ℚbar ℂ (laurentBaseChange ℂ F₀) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℚbar (laurentBaseChange ℚbar F₀) (laurentBaseChange ℂ F₀) := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    change algebraMap ℂ (laurentBaseChange ℂ F₀) (iota c) = psi F₀ (algebraMap ℚbar _ c)
    rw [psi_algebraMap]
  have hfg : ∃ x : laurentBaseChange ℚbar F₀, Transcendental ℚbar x ∧
      FiniteDimensional (IntermediateField.adjoin ℚbar ({x} : Set _)) (laurentBaseChange ℚbar F₀) :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℚbar Γ hT
  have hfg' : ∃ x : laurentBaseChange ℂ F₀, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set _)) (laurentBaseChange ℂ F₀) :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℂ Γ hT
  haveI : IsCurveOver ℚbar (laurentBaseChange ℚbar F₀) := by
    obtain ⟨x, hx, hfin⟩ := hfg
    exact isCurveOver_of_transcendental_of_perfectField hx hfin
  have hgen : IntermediateField.adjoin ℂ
      (Set.range (algebraMap (laurentBaseChange ℚbar F₀) (laurentBaseChange ℂ F₀))) = ⊤ := by
    apply le_antisymm le_top
    have h1 : laurentBaseChange ℂ F₀ ≤ (IntermediateField.adjoin ℂ
        (Set.range (algebraMap (laurentBaseChange ℚbar F₀) (laurentBaseChange ℂ F₀)))).map
          (laurentBaseChange ℂ F₀).val := by
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨⟨coeffEmb ℂ y, coeffEmb_mem_laurentBaseChange ℂ hy⟩, ?_, rfl⟩
      apply IntermediateField.subset_adjoin
      exact ⟨⟨coeffEmb ℚbar y, coeffEmb_mem_laurentBaseChange ℚbar hy⟩, psi_coeffEmb F₀ y hy⟩
    intro x _
    obtain ⟨y, hy, hyx⟩ := h1 x.2
    have : y = x := Subtype.ext hyx
    rwa [← this]
  obtain ⟨v', -, hord, -⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension ℚbar (laurentBaseChange ℚbar F₀) ℂ
      (laurentBaseChange ℂ F₀) hfg hfg' hgen v
  exact ⟨v', hord⟩

end Descent

section Unramified

local notation "ℚbar" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)

include hΓ in

theorem ord_sub_algebraMap_le_one
    (y : laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries ℚbar) = jqModC ℚbar) (a : ℚbar) (ha₀ : a ≠ 0) (ha₁ : a ≠ 1728)
    (P : Place ℚbar (laurentBaseChange ℚbar (qExpFunctionFieldC ℚ Γ))) :
    P.ord (y - algebraMap ℚbar _ a) ≤ 1 := by
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hT : ModularGroup.T ∈ Γ := hΓ (UnramifiedGamma.T_mem_Gamma1 M)
  obtain ⟨P', hP'⟩ := exists_place_complex_ord_eq Γ hT P
  rw [← hP', map_sub, psi_algebraMap]
  have hy' : ((psi (qExpFunctionFieldC ℚ Γ) y : laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)) :
      LaurentSeries ℂ) = jqModC ℂ := by
    rw [coe_psi, hy]
    exact map_jqModC _
  have hinj : Function.Injective (iota : ℚbar →+* ℂ) := (iota : ℚbar →+* ℂ).injective
  have h₀ : (iota : ℚbar →+* ℂ) a ≠ 0 := by
    intro h; exact ha₀ (hinj (by rw [h, map_zero]))
  have h₁ : (iota : ℚbar →+* ℂ) a ≠ 1728 := by
    intro h; exact ha₁ (hinj (by rw [h, map_ofNat]))
  exact ModularCurve.ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728
    M Γ hΓ (psi (qExpFunctionFieldC ℚ Γ) y) hy' _ h₀ h₁ P'

end Unramified

section Main

local notation "ℚbar" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ)) (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)

local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)

theorem sum_eq_sum_of_vanish {ι : Type*} [DecidableEq ι] (f : ι → ℤ) (S U : Finset ι)
    (hS : ∀ P, P ∉ S → f P = 0) (hU : ∀ P, P ∉ U → f P = 0) :
    ∑ P ∈ S, f P = ∑ P ∈ U, f P := by
  have h1 : ∑ P ∈ S, f P = ∑ P ∈ S ∪ U, f P :=
    Finset.sum_subset Finset.subset_union_left fun P _ hPS => hS P hPS
  have h2 : ∑ P ∈ U, f P = ∑ P ∈ S ∪ U, f P :=
    Finset.sum_subset Finset.subset_union_right fun P _ hPU => hU P hPU
  rw [h1, h2]

include hΓ in

theorem main (y : FF) (hy : (y : LaurentSeries ℚbar) = jqModC ℚbar) :
    2 * genusFF ℚbar FF + Nat.card {P : Place ℚbar FF // P.ord y < 0} +
        Nat.card {P : Place ℚbar FF // 0 < P.ord y} +
        Nat.card {P : Place ℚbar FF // 0 < P.ord (y - 1728)} ≤
      Module.finrank ℚbar⟮y⟯ FF + 2 := by
  classical
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  have hT : ModularGroup.T ∈ Γ := hΓ (UnramifiedGamma.T_mem_Gamma1 M)

  have hytr : Transcendental ℚbar y := by
    have h := transcendental_jqModC ℚbar
    rw [← hy] at h
    exact (transcendental_algebraMap_iff (R := ℚbar) (A := LaurentSeries ℚbar) (S := ↥FF)
      Subtype.val_injective).mp h
  obtain ⟨x₀, hx₀, hx₀fin⟩ := JOneES.exists_transcendental_finiteDimensional_laurentBaseChange ℚbar Γ hT
  haveI := hx₀fin
  haveI hfin : FiniteDimensional ℚbar⟮y⟯ FF :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x₀ hytr
  haveI hAlg : Algebra.IsAlgebraic ℚbar⟮y⟯ FF := Algebra.IsAlgebraic.of_finite ℚbar⟮y⟯ FF
  haveI hsep : Algebra.IsSeparable ℚbar⟮y⟯ FF := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hC : IsCurveOver ℚbar FF := isCurveOver_of_transcendental_of_perfectField hytr hfin

  obtain ⟨S, hS0, hSsum⟩ := exists_sum_ordDiff_D_eq ℚbar y hytr hfin hsep

  have hy0 : (y : FF) ≠ 0 := fun h => hytr (h ▸ isAlgebraic_zero)
  have h1728F : (1728 : FF) = algebraMap ℚbar FF 1728 := (map_ofNat _ 1728).symm
  have hy1728 : y - algebraMap ℚbar FF 1728 ≠ 0 := by
    intro h
    apply hytr
    rw [sub_eq_zero] at h
    rw [h]; exact isAlgebraic_algebraMap _
  obtain ⟨Z₀, hZ₀⟩ := exists_finset_zeros (K := ℚbar) hy0
  obtain ⟨Z₁, hZ₁⟩ := exists_finset_zeros (K := ℚbar) hy1728
  obtain ⟨Pinf, hPinf⟩ := exists_finset_poles (K := ℚbar) hy0

  have hsum₀ : ∑ v ∈ Z₀, v.ord y = (Module.finrank ℚbar⟮y⟯ FF : ℤ) := by
    have h := sum_ord_sub_algebraMap_eq_finrank (K := ℚbar) hytr 0 Z₀
      (fun v => by rw [map_zero, sub_zero]; exact hZ₀ v)
    simpa using h
  have hsum₁ : ∑ v ∈ Z₁, v.ord (y - algebraMap ℚbar FF 1728) = (Module.finrank ℚbar⟮y⟯ FF : ℤ) :=
    sum_ord_sub_algebraMap_eq_finrank (K := ℚbar) hytr 1728 Z₁ hZ₁
  have hsuminf : ∑ v ∈ Pinf, (-v.ord y) = (Module.finrank ℚbar⟮y⟯ FF : ℤ) :=
    sum_neg_ord_eq_finrank (K := ℚbar) hytr Pinf hPinf

  set f : Place ℚbar FF → ℤ := fun v => v.ordDiff (KaehlerDifferential.D ℚbar FF y) with hf
  have hD1728 : KaehlerDifferential.D ℚbar FF (y - algebraMap ℚbar FF 1728) =
      KaehlerDifferential.D ℚbar FF y := by
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  have hf_pole : ∀ v ∈ Pinf, f v = v.ord y - 1 := fun v hv => by
    have h : v.ord y ≠ 0 := by have := (hPinf v).mp hv; omega
    exact Place.ordDiff_D_eq_ord_sub_one y v h
  have hf_zero : ∀ v ∈ Z₀, f v = v.ord y - 1 := fun v hv => by
    have h : v.ord y ≠ 0 := by have := (hZ₀ v).mp hv; omega
    exact Place.ordDiff_D_eq_ord_sub_one y v h
  have hf_one : ∀ v ∈ Z₁, f v = v.ord (y - algebraMap ℚbar FF 1728) - 1 := fun v hv => by
    have h : v.ord (y - algebraMap ℚbar FF 1728) ≠ 0 := by have := (hZ₁ v).mp hv; omega
    change v.ordDiff (KaehlerDifferential.D ℚbar FF y) = _
    rw [← hD1728]
    exact Place.ordDiff_D_eq_ord_sub_one y v h

  set U : Finset (Place ℚbar FF) := Z₀ ∪ Z₁ ∪ Pinf with hU
  have hf_off : ∀ v, v ∉ U → f v = 0 := by
    intro v hv
    have hv₀ : v ∉ Z₀ := fun h => hv (by rw [hU]; exact Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hv₁ : v ∉ Z₁ := fun h => hv (by rw [hU]; exact Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hvinf : v ∉ Pinf := fun h => hv (by rw [hU]; exact Finset.mem_union_right _ h)
    have hreg : 0 ≤ v.ord y := by
      by_contra h; exact hvinf ((hPinf v).mpr (not_le.mp h))
    obtain ⟨c, hc⟩ := exists_ord_sub_algebraMap_pos (K := ℚbar) v hytr hreg
    have hc₀ : c ≠ 0 := by
      rintro rfl
      rw [map_zero, sub_zero] at hc
      exact hv₀ ((hZ₀ v).mpr hc)
    have hc₁ : c ≠ 1728 := by
      rintro rfl
      exact hv₁ ((hZ₁ v).mpr hc)
    have hle := ord_sub_algebraMap_le_one M Γ hΓ y hy c hc₀ hc₁ v
    have heq : v.ord (y - algebraMap ℚbar FF c) = 1 := le_antisymm hle hc
    have hDc : KaehlerDifferential.D ℚbar FF (y - algebraMap ℚbar FF c) =
        KaehlerDifferential.D ℚbar FF y := by
      rw [map_sub, Derivation.map_algebraMap, sub_zero]
    change v.ordDiff (KaehlerDifferential.D ℚbar FF y) = 0
    rw [← hDc, Place.ordDiff_D_eq_ord_sub_one y v (by rw [heq]; exact one_ne_zero), heq]
    ring

  have hUsum : ∑ v ∈ U, f v = 2 * (genusFF ℚbar FF : ℤ) - 2 := by
    rw [← hSsum]
    exact (sum_eq_sum_of_vanish f S U hS0 hf_off).symm

  have h1728ne : (1728 : ℚbar) ≠ 0 := by norm_num
  have hd01 : Disjoint Z₀ Z₁ := by
    rw [Finset.disjoint_left]
    intro v hv₀ hv₁
    have h₀ : 0 < v.ord (y - algebraMap ℚbar FF 0) := by rw [map_zero, sub_zero]; exact (hZ₀ v).mp hv₀
    exact not_ord_sub_pos_of_ord_sub_pos v h1728ne.symm h₀ ((hZ₁ v).mp hv₁)
  have hd0inf : Disjoint Z₀ Pinf := by
    rw [Finset.disjoint_left]
    intro v hv₀ hvinf
    have := (hZ₀ v).mp hv₀; have := (hPinf v).mp hvinf; omega
  have hd1inf : Disjoint Z₁ Pinf := by
    rw [Finset.disjoint_left]
    intro v hv₁ hvinf
    have h := ord_nonneg_of_ord_sub_algebraMap_pos v (1728 : ℚbar) ((hZ₁ v).mp hv₁)
    have := (hPinf v).mp hvinf; omega
  have hd01inf : Disjoint (Z₀ ∪ Z₁) Pinf := Finset.disjoint_union_left.mpr ⟨hd0inf, hd1inf⟩
  have hsplit : ∑ v ∈ U, f v = ∑ v ∈ Z₀, f v + ∑ v ∈ Z₁, f v + ∑ v ∈ Pinf, f v := by
    rw [hU, Finset.sum_union hd01inf, Finset.sum_union hd01]

  have hs₀ : ∑ v ∈ Z₀, f v = (Module.finrank ℚbar⟮y⟯ FF : ℤ) - Z₀.card := by
    rw [Finset.sum_congr rfl hf_zero, Finset.sum_sub_distrib, hsum₀]
    simp
  have hs₁ : ∑ v ∈ Z₁, f v = (Module.finrank ℚbar⟮y⟯ FF : ℤ) - Z₁.card := by
    rw [Finset.sum_congr rfl hf_one, Finset.sum_sub_distrib, hsum₁]
    simp
  have hsinf : ∑ v ∈ Pinf, f v = -(Module.finrank ℚbar⟮y⟯ FF : ℤ) - Pinf.card := by
    rw [Finset.sum_congr rfl hf_pole, Finset.sum_sub_distrib, ← hsuminf, Finset.sum_neg_distrib]
    simp

  have hc₀ : Nat.card {P : Place ℚbar FF // 0 < P.ord y} = Z₀.card :=
    natCard_subtype_eq_card Z₀ _ hZ₀
  have hc₁ : Nat.card {P : Place ℚbar FF // 0 < P.ord (y - 1728)} = Z₁.card := by
    rw [h1728F]; exact natCard_subtype_eq_card Z₁ _ hZ₁
  have hcinf : Nat.card {P : Place ℚbar FF // P.ord y < 0} = Pinf.card :=
    natCard_subtype_eq_card Pinf _ hPinf
  rw [hc₀, hc₁, hcinf]
  have key : 2 * (genusFF ℚbar FF : ℤ) - 2 =
      (Module.finrank ℚbar⟮y⟯ FF : ℤ) - Z₀.card - Z₁.card - Pinf.card := by
    rw [← hUsum, hsplit, hs₀, hs₁, hsinf]; ring
  omega

end Main

end RiemannHurwitzCount

/-! ## Row 812 — the Riemann–Hurwitz count -/

open RiemannHurwitzCount in
theorem two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    2 * AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            P.ord y < 0} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord y} +
        Nat.card {P : AlgebraicCurve.Place (AlgebraicClosure ℚ)
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) //
            0 < P.ord (y - 1728)} ≤
      Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) +
        2 :=
  RiemannHurwitzCount.main M Γ hΓ y hy

end ModularCurve

/-! ## Row 163 — a regular differential from its `q`-expansion (pin `SolB8bd4cf51`) -/

namespace ModularCurve

namespace RegularDifferential

theorem jq_mem_x1FunctionField (M : ℕ) [NeZero M] : jq ∈ x1FunctionField M := by
  rw [← jqModC_rat]
  exact intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ (CongruenceSubgroup.Gamma1 M))

theorem coeffEmb_jq_eq_jqModC (K : Type*) [Field K] [Algebra ℚ K] :
    coeffEmb K jq = jqModC K := by
  rw [jqModC_eq_map_intCast (K := K), ← jqModC_rat, jqModC_eq_map_intCast (K := ℚ)]
  ext n
  simp only [coeffEmb_coeff, HahnSeries.map_coeff, eq_intCast, map_intCast]

end RegularDifferential

/-! ## Row 163 headline -/

open RegularDifferential in
theorem mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion
    (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ])
    (hω : ModularCurve.coeffMap ι₀ (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω) =
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f)) :
    ω ∈ AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) := by

  set K := AlgebraicClosure ℚ with hK
  let F : IntermediateField K (LaurentSeries K) := x1FunctionFieldBar M
  let jb : F := ⟨coeffEmb K jq, coeffEmb_mem_laurentBaseChange K (jq_mem_x1FunctionField M)⟩
  have hjb : (jb : LaurentSeries K) = jqModC K := coeffEmb_jq_eq_jqModC K

  haveI := essFiniteType_x1FunctionFieldBar M
  haveI := isCurveOver_x1FunctionFieldBar M
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T]
  obtain ⟨hjT, hjfd⟩ :=
    transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
      K (CongruenceSubgroup.Gamma1 M) hT jb hjb
  haveI : FiniteDimensional (IntermediateField.adjoin K ({jb} : Set F)) F := hjfd
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({jb} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({jb} : Set F)) F :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField

  obtain ⟨y, hyω, -⟩ :=
    @KaehlerDifferential.exists_unique_smul_D_of_transcendental K _ F _ _ jb hjT hsep ω
  by_cases hy0 : y = 0
  · rw [hyω, hy0]
    show (0 : ↥F) • KaehlerDifferential.D K ↥F jb ∈ AlgebraicCurve.regularDifferentials K ↥F
    rw [zero_smul]
    exact Submodule.zero_mem _

  have hθ : coeffMap ι₀ ((y : LaurentSeries K) * thetaL K (coeffEmb K jq)) =
      ((UpperHalfPlane.qExpansion 1 ⇑f : PowerSeries ℂ) : LaurentSeries ℂ) := by
    rw [← qEuler_eq_thetaL, ← hω, hyω]
    show _ = coeffMap ι₀ (diffQExp F (y • KaehlerDifferential.D K F jb))
    rw [diffQExp_smul_D]

  show ω ∈ regularDifferentials K F
  rw [← regularDiffs_eq_regularDifferentials]
  refine mem_regularDiffs_of_isRegularDiff fun v => ?_
  rw [hyω]
  by_cases hv : v.ord jb < 0
  ·
    have hle := ModularCurve.one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion_of_gamma_le F jb rfl M
      (CongruenceSubgroup.Gamma1 M) (X1DiamondRational.Gamma_le_Gamma1 M)
      (Depletion.one_mem_strictPeriods_Gamma1 M) ι₀ f y hy0 hθ v hv
    have hD0 : KaehlerDifferential.D K F jb ≠ 0 := Place.D_ne_zero_of_ord_ne_zero jb v hv.ne
    have h1 : v.ordDiff (y • KaehlerDifferential.D K F jb) =
        v.ord y + v.ordDiff (KaehlerDifferential.D K F jb) :=
      Place.ordDiff_smul jb v hy0 hD0
    have h2 : v.ordDiff (KaehlerDifferential.D K F jb) = v.ord jb - 1 :=
      Place.ordDiff_D_eq_ord_sub_one jb v hv.ne
    have h3 : v.ordDiff (y • KaehlerDifferential.D K F jb) = v.ord y + (v.ord jb - 1) := by
      rw [h1, h2]
    have h4 : (0 : ℤ) ≤ v.ord y + (v.ord jb - 1) := by omega
    exact le_of_le_of_eq h4 h3.symm
  ·
    push Not at hv
    haveI : PerfectField K := PerfectField.ofCharZero
    have h1728 : (1728 : K) ≠ 0 := by norm_num
    refine Place.ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg
      v jb y jb h1728 (Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg v ?_ hv)

    set u : F := y ^ 6 * jb ^ 4 * (jb - algebraMap K F 1728) ^ 3 with hu
    have hI := ModularCurve.isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_eq_qExpansion_of_finiteIndex
      (CongruenceSubgroup.Gamma1 M) (Depletion.one_mem_strictPeriods_Gamma1 M) f
      (coeffMap ι₀ (y : LaurentSeries K)) (by
      rw [← UnramifiedGamma.coeffMap_coeffEmb' ι₀, ← UnramifiedGamma.coeffMap_thetaL, ← map_mul, hθ])
    have hD : IsIntegral (Algebra.adjoin K ({(jb : LaurentSeries K)} : Set (LaurentSeries K)))
        (u : LaurentSeries K) := by
      refine isIntegral_adjoin_of_isIntegral_adjoin_coeffMap ι₀ _ _ ?_
      have hcoe : ((u : F) : LaurentSeries K) =
          (y : LaurentSeries K) ^ 6 * coeffEmb K jq ^ 4 * (coeffEmb K jq - 1728) ^ 3 := by
        show F.val u = _
        simp only [hu, map_mul, map_pow, map_sub, map_ofNat]
        rfl
      have hj : ((jb : F) : LaurentSeries K) = coeffEmb K jq := rfl
      rw [hcoe, hj, map_mul, map_mul, map_pow, map_pow, map_pow, map_sub,
        UnramifiedGamma.coeffMap_coeffEmb', map_ofNat]
      exact hI
    simpa using isIntegral_adjoin_intermediateField_mk F jb.2 u.2 hD

end ModularCurve
