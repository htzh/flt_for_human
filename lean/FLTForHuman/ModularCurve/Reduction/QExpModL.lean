/-
The reduction inputs of the `q`-expansion modulo `ℓ`.

For the modular curve `X₁` over a number field, the reduction of a modular form modulo a prime `ℓ`
is read off its `q`-expansion: `qExpModL` sends a `q`-expansion to its reduction mod `ℓ`, and a
modular form reduces well when the `q`-expansion of its pullback agrees with the reduction of its
own.  This module supplies the **inputs** of that comparison:

  if the relative finrank of the `X₁` function field over the `j`-line is bounded by
  `genusFF`-data (`_hfr`), then the reduction inputs — the integrality of the `q`-expansion
  coefficients, the identification of the reduced function field with the reduction of the
  `q`-expansion ring, and the compatibility of the `q`-expansion with the reduction map — hold,

which is the hypothesis package the modular-representation arguments (`ρ` mod `ℓ`, its
semisimplicity from the Frobenius trace/det data of `GaloisRep/SemisimpleCriterion.lean`) consume.

The engine is the reduction dictionary (`ModularCurve/Defs/QExpReductionModL.lean` for the ring map,
`ModularCurve/ConstantReductionQExp.lean` for its compatibility with `q`-expansions), the degree glue
(`Degree/PhiDegree.lean`), the `jq`-integrality (`JqIntegralRatios.lean`,
`Analytic/JqInverseIntegral.lean`), the function field's residue dictionary
(`X1/FunctionField{BaseChange,Residue}.lean`) and AF105C's regular-prolongation retraction
(`AlgebraicCurve/RegularProlongationRetraction.lean`).

## Substitute-first: what this module imports and what it writes

The pin's `S_` file is a 96-declaration, 1,236-line engine under one generated namespace label
(`QExpDeuringRed`).  The substitution pass is what most of the order's saving is spent on: the port
already has the whole `Coeff` / `Scaling` / `Generators` / `Residue` / `PolyJ` layer of the pin,
publicly, in `ModularCurve.QExpDeuring` (`X1/FunctionFieldResidue.lean`) and the whole assembly half
in `ModularCurve.QExpDeuring` (`X1/GaussResidue.lean`) — `ι`, `ϖ`, `IsInt` and its algebra,
`intSeriesA`, `coeffMap_intSeries`, `exists_coeffMap_subtype_eq`, `valuation_le_of_mem_span`,
`exists_primitive_{scaling,form,poly}`, `exists_frac_form`, `algebraMap_laurentSeries_A`,
`ι_aeval`, `ϖ_aeval`, `aeval_jqModC_ne_zero`, `jqModC_mem_{rat,FF}`, `jbar`,
`transcendental_{jF,jbar}`, `intSeriesC_ne_zero_rat`, `exists_inv_mem_maximalIdeal`,
`exists_resHom_eq`, `exists_adjoin_coe_eq_resHom`, `resHom_mem` — plus
`ModularCurve.JOneES.JOneESNorm.one_mem_strictPeriods` (`X1/FunctionField.lean`),
`ModularCurve.{delta,isIntegralQExp_delta}` (`JqIntegralRatios.lean`),
`ModularCurve.coeffEmb_intSeriesC` and `AlgebraicCurve.PolarFinrank.ord_algebraMap_eq_zero`.
None of those is restated or re-proved here.

**The one signature shift.** The pin threads `hT : ModularGroup.T ∈ Γ` as a section variable
through the *definitions* `gaussRing`, `resHom`, `wit`, `resL`, `resF`; the port dropped it, because
the definition does not use it, and passes `hT` only where a proof needs it — the decision
`X1/GaussResidue.lean`'s header records.  The pin's statement *text* therefore spells
`gaussRing A Γ hT` where the port spells `gaussRing A Γ`, so the advise's shape tier pairs only the
names whose texts are identical.  This module closes that gap by declaring the pin's surface at the
pin's own statement text over two `abbrev` aliases (`gaussRing`, `resHom`) that forget the unused
`hT`; the bodies are then one-liners into the port's copies, so nothing is proved twice and the
module's `check_port` reads green on the pin's text.

**What is genuinely new here** (the port had none of it):
* the integral Laurent layer — `intLaurentC` and its `coeffMap` lemmas, `intSeriesC_pow`,
  `intSeriesC_deltaPow_ne_zero`, `deltaPow_mul_inv`, `exists_intLaurent_of_mem_intFormRatiosC`
  (the 70-line lemma that turns an `intFormRatiosC` element into a ratio of *integral Laurent*
  series, clearing the denominator with `Δ^w` and a `q⁻ʷ` twist);
* the generator set `gensF` over that layer with `coeffEmb_intLaurentC`, `gensF_subset`,
  `adjoin_gensF_le`, `laurentBaseChange_le_adjoin_gensF`, `exists_fg_coeff_mem`,
  `algebra_adjoin_gensF_le`;
* the placement assembly `exists_placeMap` and the integrality clause `ClauseB`
  (`exists_mem_integralPrincipalDivisors_of_mem_adjoin`, `laurentPrincipalGeneratedByIntegral_of`).

**One suspect substitution (FR-0266).** `gensF` is matched by `port_advise` to
`QExpDeuring.gensZ` on its *type* alone (`Set (LaurentSeries L)`); the bodies differ and are not
interchangeable — `gensF` is the integral-**Laurent** set, `gensZ` the integral-`q`-expansion set,
and `exists_intLaurent_of_mem_intFormRatiosC` genuinely produces series with negative exponents
(`HahnSeries.single (-(w : ℤ))`).  The pin's set, its `exists_fg_coeff_mem` and
`laurentBaseChange_le_adjoin_gensF` are therefore transcribed here, not substituted.

Pin `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` lines are **not** transcribed
(project build hygiene; the pin's `solution` carries `3200000` and `1600000`).  The pin's private
`Forms` chain is not needed: `exists_frac_form` here is the port's, not the pin's
fourth-conjunct variant, because `resHom_mem` is the port's too.

## The measured gates of this module (order AF106A)

| figure | value |
|---|---:|
| pin `S_` file | 1,236 lines, 96 declarations (all public) |
| pin `Theorems/` wrapper | 35 lines, 1 declaration |
| this module | 736 lines, 54 declarations (all public) |
| **imported from the port (the substitution pass)** | **42 declarations, 447 pin lines** |
| declared here at the pin's text | 54 — **20 new**, 26 transcribed from the pin, 8 one-line aliases into the port |
| `spec/check_port.py --force` | **54 ok / 0 mismatch / 0 missing / 0 own / 0 kw** |
| the pin-vs-module declaration diff | wire 97, module 54: **54 by hash, 0 by name, 0 unaccounted** |
| `#print axioms`, every public declaration | 54/54 ⊆ {propext, Classical.choice, Quot.sound}; no `sorryAx` |
| the edit loop (`-DmaxHeartbeats=200000`) | silent |
| `dedup.py --within --module '*ModularCurve/Reduction/QExpModL*'` | 0 duplicate clusters |
| `move_dead.py --dry-run` | 0 declarations, 0 lines |
| the set-level collision probe | silent |

### The heartbeat probe pair (recorded, **not** installed)

*`maxHeartbeats`, downward ladder on this module* — **silent at 150 000, one failure at 100 000**:
`exists_placeMap` (`QExpDeuringRed.exists_placeMap:528:10`) dies with a deterministic `isDefEq`
timeout, and at 50 000 the peak spreads to six sites, three of which are **statement-only**
(`resHom_mem` and `exists_placeMap`'s `hle` binder, i.e. the `Module.finrank (adjoin kk {jbar}) Fb`
type, plus `exists_mem_integralPrincipalDivisors_of_mem_adjoin`).  So part of the cost is in the
*types*: the pin carries `set_option maxHeartbeats 3200000` on `solution` and `6400000` on
`resHom_mem` / `exists_adjoin_coe_eq_resHom` precisely for them.  Nothing is installed; the module
sits at the edit loop's 200 000 with ~2× headroom, and the peak declaration is named above for the
manager.

*`synthInstance.maxHeartbeats` — the one instance-inference site.*  The headline needs
`Module.Finite K0 FF` for `K0 = adjoin (AlgebraicClosure ℚ) {jF}`, and the only route from
`0 < finrank K0 FF` is `Module.finite_of_finrank_pos`, which needs `[Module.Free K0 FF]`.  The bare
instance search for that **exceeds the default 20 000**: red at 20 000, green at 40 000 (probe
`lean/tmp/af106/probe-QExpModL-synth.lean`).  The module **supplies the instance by hand**
(`Module.Free.of_divisionRing K0 _`) rather than raising the cap, which is why it needs no
`synthInstance.maxHeartbeats` option at all — the pin's `1600000` on `solution` is that same site.
This is the instance-inference defect the playbook asks to be named, not a budget to raise.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq.lean>

spec-pin: Theorems/Thm_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq.lean
spec-pin: P2M/Sol/S_ModularCurve_reductionInputsQExpModL_of_finrank_le_of_genusFF_eq.lean
-/
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueIntegralClosure
import FLTForHuman.AlgebraicCurve.RegularProlongationRetraction
import FLTForHuman.FieldTheory.ValuationSubringResidueField
import FLTForHuman.ModularCurve.ConstantReductionQExp
import FLTForHuman.ModularCurve.Defs.QExpReductionModL
import FLTForHuman.ModularCurve.Degree.PhiDegree
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.X1.FunctionField
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.ModularCurve.X1.FunctionFieldResidue
import FLTForHuman.ModularCurve.X1.GaussResidue
import FLTForHuman.ModularForms.JqAnalyticModel

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option autoImplicit false

noncomputable section

open scoped Classical
open scoped MatrixGroups ModularForm

open IntermediateField AlgebraicCurve ModularCurve Polynomial UpperHalfPlane

namespace ModularCurve

namespace QExpDeuringRed

open QExpDeuring

/-! ## The integral Laurent layer

The pin's `intLaurentC` is `intSeriesC` without the `PowerSeries` hypothesis: it carries an
*arbitrary* integral Laurent series.  The pin's generator set `gensF` is built from it, and
`exists_intLaurent_of_mem_intFormRatiosC` is where the extra generality is earned (the pin clears
the denominator by hand, with `Δ^w` and a `q⁻ʷ` twist, because `intFormRatiosC` only supplies
integral `q`-expansions). -/

section IntLaurent

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

abbrev intLaurentC (K : Type*) [CommRing K] : LaurentSeries ℤ →+* LaurentSeries K :=
  coeffMap (Int.castRingHom K)

theorem coeffMap_intLaurentC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : LaurentSeries ℤ) :
    coeffMap f (intLaurentC R P) = intLaurentC S P := by
  rw [coeffMap_coeffMap, RingHom.ext_int (f.comp _) (Int.castRingHom S)]

theorem intLaurentC_ofPowerSeries (K : Type*) [CommRing K] (p : PowerSeries ℤ) :
    intLaurentC K (HahnSeries.ofPowerSeries ℤ ℤ p) = HahnSeries.ofPowerSeries ℤ K (p.map (Int.castRingHom K)) :=
  coeffMap_ofPowerSeries _ p

theorem intLaurentC_ofPowerSeries' (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intLaurentC K (HahnSeries.ofPowerSeries ℤ ℤ p) = intSeriesC K p :=
  coeffMap_ofPowerSeries _ p

theorem intLaurentC_single (K : Type*) [CommRing K] (n : ℤ) (a : ℤ) :
    intLaurentC K (HahnSeries.single n a) = HahnSeries.single n (a : K) := by
  rw [coeffMap_single, eq_intCast]

theorem intSeriesC_pow (K : Type*) [Field K] (p : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (p ^ n) = intSeriesC K p ^ n := by
  rw [intSeriesC, intSeriesC, map_pow (PowerSeries.map (Int.castRingHom K)), map_pow]

theorem intSeriesC_deltaPow_ne_zero (K : Type*) [Field K] (w : ℕ) :
    intSeriesC K ((PowerSeries.X * dedekindEtaUnit) ^ w) ≠ 0 := by
  rw [intSeriesC_pow]
  refine pow_ne_zero _ fun h => ?_
  have h1 := congrArg (fun z : LaurentSeries K => z.coeff 1) h
  have h2 : (HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom K))).coeff ((1 : ℕ) : ℤ) = 1 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit, map_one]
  simp only [intSeriesC, HahnSeries.coeff_zero] at h1
  rw [show ((1 : ℕ) : ℤ) = 1 from rfl] at h2
  rw [h2] at h1
  exact one_ne_zero h1

theorem deltaPow_mul_inv (w : ℕ) :
    intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) *
      (intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ)) = 1 := by
  have hUV : intSeriesC ℚ (dedekindEtaUnit ^ w) * intSeriesC ℚ (dedekindEtaUnitInv ^ w) = 1 := by
    rw [← intSeriesC_mul, ← mul_pow, dedekindEtaUnit_mul_inv, one_pow, intSeriesC_one]
  have hX : intSeriesC ℚ (PowerSeries.X ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ) = 1 := by
    rw [intSeriesC_pow, intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X, HahnSeries.single_pow,
      HahnSeries.single_mul_single]
    simp
  calc intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) *
        (intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ))
      = (intSeriesC ℚ (PowerSeries.X ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ)) *
          (intSeriesC ℚ (dedekindEtaUnit ^ w) * intSeriesC ℚ (dedekindEtaUnitInv ^ w)) := by
        rw [mul_pow, intSeriesC_mul]; ring
    _ = 1 := by rw [hX, hUV, one_mul]

end IntLaurent

section IntFormRatios

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

theorem exists_intLaurent_of_mem_intFormRatiosC [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    {x : LaurentSeries ℚ} (hx : x ∈ intFormRatiosC ℚ Γ) :
    ∃ P Q : LaurentSeries ℤ, intLaurentC ℚ P ∈ qExpFunctionFieldC ℚ Γ ∧
      intLaurentC ℚ Q ∈ qExpFunctionFieldC ℚ Γ ∧ intLaurentC ℚ Q ≠ 0 ∧
      x = intLaurentC ℚ P / intLaurentC ℚ Q := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx

  have hk : 0 ≤ k := by
    by_contra hk
    push Not at hk
    have hg' : g = 0 := ModularForm.isZero_of_neg_weight hk g
    apply hg0
    have hpg : pg = 0 := by
      have h := hg
      rw [hg', IsIntegralQExp, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero] at h
      ext n
      have := congrArg (PowerSeries.coeff n) h
      simpa using this
    rw [hpg, intSeriesC_zero]
  obtain ⟨w, rfl⟩ : ∃ w : ℕ, k = w := ⟨k.toNat, (Int.toNat_of_nonneg hk).symm⟩

  have hper := JOneES.JOneESNorm.one_mem_strictPeriods hT
  have hG : IsIntegralQExp ((g.pow 12 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (w : ℤ))) : ℍ → ℂ)
      (pg ^ 12) := by
    rw [IsIntegralQExp, map_pow, hg, ModularForm.qExpansion_pow one_pos hper]
  have hD : IsIntegralQExp ((((delta Γ).pow w).mcast (by ring) :
      ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (12 * (w : ℤ))) : ℍ → ℂ)
      ((PowerSeries.X * dedekindEtaUnit) ^ w) := by
    rw [IsIntegralQExp, ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos hper, map_pow,
      isIntegralQExp_delta]
  have hbmem : intSeriesC ℚ (pg ^ 12) / intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) ∈
      qExpFunctionFieldC ℚ Γ :=
    div_mem_qExpFunctionFieldC _ _ hG hD (intSeriesC_deltaPow_ne_zero ℚ w)
  obtain ⟨Q, hQ⟩ : ∃ Q : LaurentSeries ℤ, Q =
      HahnSeries.ofPowerSeries ℤ ℤ (pg ^ 12 * dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) 1 :=
    ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : LaurentSeries ℤ, P =
      HahnSeries.ofPowerSeries ℤ ℤ (pf * pg ^ 11 * dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) 1 :=
    ⟨_, rfl⟩
  have hQeq : intLaurentC ℚ Q = intSeriesC ℚ (pg ^ 12) / intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) := by
    rw [eq_div_iff (intSeriesC_deltaPow_ne_zero ℚ w), hQ, map_mul (intLaurentC ℚ), intLaurentC_ofPowerSeries',
      intLaurentC_single, Int.cast_one, intSeriesC_mul]
    calc intSeriesC ℚ (pg ^ 12) * intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ) *
          intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w)
        = intSeriesC ℚ (pg ^ 12) * (intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) *
            (intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ))) := by ring
      _ = intSeriesC ℚ (pg ^ 12) := by rw [deltaPow_mul_inv, mul_one]
  have hPeq : intLaurentC ℚ P = intSeriesC ℚ pf / intSeriesC ℚ pg * intLaurentC ℚ Q := by
    rw [hQeq, hP, map_mul (intLaurentC ℚ), intLaurentC_ofPowerSeries', intLaurentC_single, Int.cast_one,
      div_mul_div_comm, eq_div_iff (mul_ne_zero hg0 (intSeriesC_deltaPow_ne_zero ℚ w)), intSeriesC_mul,
      intSeriesC_mul]
    calc intSeriesC ℚ pf * intSeriesC ℚ (pg ^ 11) * intSeriesC ℚ (dedekindEtaUnitInv ^ w) *
          HahnSeries.single (-(w : ℤ)) (1 : ℚ) *
          (intSeriesC ℚ pg * intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w))
        = intSeriesC ℚ pf * (intSeriesC ℚ (pg ^ 11) * intSeriesC ℚ pg) *
            (intSeriesC ℚ ((PowerSeries.X * dedekindEtaUnit) ^ w) *
              (intSeriesC ℚ (dedekindEtaUnitInv ^ w) * HahnSeries.single (-(w : ℤ)) (1 : ℚ))) := by ring
      _ = intSeriesC ℚ pf * intSeriesC ℚ (pg ^ 12) := by
          rw [deltaPow_mul_inv, mul_one, ← intSeriesC_mul, ← pow_succ]
  have hQ0 : intLaurentC ℚ Q ≠ 0 := by
    rw [hQeq]
    exact div_ne_zero (by rw [intSeriesC_pow]; exact pow_ne_zero _ hg0) (intSeriesC_deltaPow_ne_zero ℚ w)
  refine ⟨P, Q, ?_, hQeq ▸ hbmem, hQ0, ?_⟩
  · rw [hPeq]
    exact mul_mem (div_mem_qExpFunctionFieldC f g hf hg hg0) (hQeq ▸ hbmem)
  · rw [hPeq, mul_div_assoc, div_self hQ0, mul_one]

end IntFormRatios

section IntGenerators

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (L : Type*) [Field L] [Algebra ℚ L]

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

def gensF : Set (LaurentSeries L) :=
  {u | ∃ P : LaurentSeries ℤ, intLaurentC ℚ P ∈ qExpFunctionFieldC ℚ Γ ∧ u = intLaurentC L P}

theorem coeffEmb_intLaurentC (P : LaurentSeries ℤ) : coeffEmb L (intLaurentC ℚ P) = intLaurentC L P :=
  coeffMap_intLaurentC _ P

theorem gensF_subset : gensF Γ L ⊆ (FF : Set (LaurentSeries L)) := by
  rintro _ ⟨P, hP, rfl⟩
  rw [← coeffEmb_intLaurentC]
  exact coeffEmb_mem_laurentBaseChange L hP

theorem adjoin_gensF_le : adjoin L (gensF Γ L) ≤ FF :=
  adjoin_le_iff.mpr (gensF_subset Γ L)

theorem laurentBaseChange_le_adjoin_gensF [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    FF ≤ adjoin L (gensF Γ L) := by
  change adjoin L _ ≤ adjoin L (gensF Γ L)
  rw [adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ) :=
    hx
  have hmap : coeffEmb L x ∈ (Subfield.closure
      (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ intFormRatiosC ℚ Γ)).map (coeffEmb L) :=
    ⟨x, hx', rfl⟩
  rw [RingHom.map_field_closure] at hmap
  refine (Subfield.closure_le.mpr ?_) hmap
  rintro _ ⟨z, hz | hz, rfl⟩
  · obtain ⟨c, rfl⟩ := hz
    rw [algebraMap_apply_eq_single]
    change coeffMap (algebraMap ℚ L) (HahnSeries.single 0 c) ∈ adjoin L (gensF Γ L)
    rw [coeffMap_single, ← algebraMap_laurentSeries_eq_single]
    exact (adjoin L (gensF Γ L)).algebraMap_mem _
  · obtain ⟨P, Q, hP, hQ, -, rfl⟩ := exists_intLaurent_of_mem_intFormRatiosC Γ hT hz
    change coeffEmb L (intLaurentC ℚ P / intLaurentC ℚ Q) ∈ adjoin L (gensF Γ L)
    rw [map_div₀, coeffEmb_intLaurentC, coeffEmb_intLaurentC]
    exact div_mem (IntermediateField.subset_adjoin L _ ⟨P, hP, rfl⟩)
      (IntermediateField.subset_adjoin L _ ⟨Q, hQ, rfl⟩)

theorem exists_fg_coeff_mem {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (gensF Γ L)) :
    ∃ M : Submodule ℤ L, M.FG ∧ ∀ n, x.coeff n ∈ M := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨P, -, rfl⟩ := hx
      refine ⟨Submodule.span ℤ {(1 : L)}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      rw [intLaurentC, coeffMap_coeff, eq_intCast, ← zsmul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  | algebraMap a =>
      refine ⟨Submodule.span ℤ {a}, Submodule.fg_span (Set.finite_singleton _), fun n => ?_⟩
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single]
      split_ifs
      · exact Submodule.subset_span rfl
      · exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ ⊔ M₂, hM₁.sup hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (h₁ n)) (Submodule.mem_sup_right (h₂ n))
  | mul x y _ _ hx hy =>
      obtain ⟨M₁, hM₁, h₁⟩ := hx
      obtain ⟨M₂, hM₂, h₂⟩ := hy
      refine ⟨M₁ * M₂, hM₁.mul hM₂, fun n => ?_⟩
      rw [HahnSeries.coeff_mul]
      exact Submodule.sum_mem _ fun ij _ => Submodule.mul_mem_mul (h₁ _) (h₂ _)

theorem algebra_adjoin_gensF_le {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (gensF Γ L)) : x ∈ FF :=
  adjoin_gensF_le Γ L (algebra_adjoin_le_adjoin L _ hx)

end IntGenerators

/-! ## The residue dictionary at the pin's `hT`-threaded signature

Every declaration below has its mathematics in `ModularCurve.QExpDeuring`
(`X1/FunctionFieldResidue.lean`, `X1/GaussResidue.lean`) without the section variable `hT`; the
`abbrev`s `gaussRing` / `resHom` forget the unused `hT`, so these are the pin's statement texts. -/

section Gauss

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A

/-- The pin's `gaussRing` takes the (unused) `hT`; the port's does not.  Keeping the pin's arity is
what lets the rest of the surface be stated at the pin's text; `hT` is consumed by a beta-redex so
that the section variable still becomes a parameter (definitionally it is the port's
`gaussRing A Γ`). -/
abbrev gaussRing : ValuationSubring FF :=
  (fun _ : ModularGroup.T ∈ Γ => ModularCurve.QExpDeuring.gaussRing A Γ) hT

/-- As `gaussRing`: the pin threads `hT` in the type, the port does not. -/
abbrev resHom : gaussRing A Γ hT →+* LaurentSeries kk := ModularCurve.QExpDeuring.resHom A Γ

theorem mem_gaussRing_iff (f : FF) : f ∈ gaussRing A Γ hT ↔ IsInt A (f : LaurentSeries L) := Iff.rfl

theorem exists_witness (f : gaussRing A Γ hT) :
    ∃ p : LaurentSeries A × LaurentSeries A,
      ϖ A p.2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A p.2 = ι A p.1 := by
  obtain ⟨x, y, hy, h⟩ := f.2
  exact ⟨(x, y), hy, h⟩

def wit (f : gaussRing A Γ hT) : LaurentSeries A × LaurentSeries A :=
  Classical.choose (exists_witness A Γ hT f)

theorem wit_spec (f : gaussRing A Γ hT) :
    ϖ A (wit A Γ hT f).2 ≠ 0 ∧ ((f : FF) : LaurentSeries L) * ι A (wit A Γ hT f).2 = ι A (wit A Γ hT f).1 :=
  Classical.choose_spec (exists_witness A Γ hT f)

def resL (f : gaussRing A Γ hT) : LaurentSeries kk :=
  ϖ A (wit A Γ hT f).1 / ϖ A (wit A Γ hT f).2

theorem resL_eq {f : gaussRing A Γ hT} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resL A Γ hT f = ϖ A x / ϖ A y := by
  obtain ⟨hy', h'⟩ := wit_spec A Γ hT f
  have hc := IsInt.cross (A := A) h' h
  rw [resL, div_eq_div_iff hy' hy, ← map_mul, ← map_mul, hc]

theorem resHom_eq {f : gaussRing A Γ hT} {x y : LaurentSeries A} (hy : ϖ A y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * ι A y = ι A x) : resHom A Γ hT f = ϖ A x / ϖ A y :=
  resL_eq A Γ hT hy h

theorem resHom_eq_zero_iff (f : gaussRing A Γ hT) :
    resHom A Γ hT f = 0 ↔ f ∈ IsLocalRing.maximalIdeal (gaussRing A Γ hT) :=
  ModularCurve.QExpDeuring.resHom_eq_zero_iff (A := A) (Γ := Γ) f

theorem coe_algebraMap (c : L) :
    ((algebraMap L FF c : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c := rfl

theorem algebraMap_mem_gaussRing_iff (c : L) : algebraMap L FF c ∈ gaussRing A Γ hT ↔ c ∈ A :=
  ModularCurve.QExpDeuring.algebraMap_mem_gaussRing_iff (A := A) (Γ := Γ) c

theorem resHom_algebraMap (a : A) (h : algebraMap L FF a ∈ gaussRing A Γ hT) :
    resHom A Γ hT ⟨algebraMap L FF a, h⟩ = algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a) :=
  ModularCurve.QExpDeuring.resHom_algebraMap (A := A) (Γ := Γ) a h

end Gauss

section PolyJ

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

def jF : FF := ⟨jqModC L, jqModC_mem_FF Γ⟩

theorem coe_jF : ((jF Γ : FF) : LaurentSeries L) = jqModC L := rfl

theorem coe_jF' : ((jF Γ : FF) : LaurentSeries L) = ι A (jqModC A) := by
  rw [coe_jF, coeffMap_jqModC]

theorem coe_jbar (K : Type*) [Field K] : ((jbar Γ K : qExpFunctionFieldC K Γ) : LaurentSeries K) = jqModC K :=
  rfl

theorem jF_mem_gaussRing : (jF Γ : FF) ∈ gaussRing A Γ hT :=
  (mem_gaussRing_iff A Γ hT _).mpr ⟨jqModC A, 1, by rw [map_one]; exact one_ne_zero,
    by rw [map_one, mul_one, coe_jF']⟩

theorem resHom_jF : resHom A Γ hT ⟨jF Γ, jF_mem_gaussRing A Γ hT⟩ = jqModC kk := by
  rw [resHom_eq A Γ hT (f := ⟨jF Γ, jF_mem_gaussRing A Γ hT⟩) (x := jqModC A) (y := 1)
    (by rw [map_one]; exact one_ne_zero) (by rw [map_one, mul_one]; exact coe_jF' A Γ),
    map_one, div_one, coeffMap_jqModC]

theorem exists_resHom_eq {z : LaurentSeries kk} (hz : z ∈ qExpFunctionFieldC kk Γ) :
    ∃ f : gaussRing A Γ hT, resHom A Γ hT f = z :=
  ModularCurve.QExpDeuring.exists_resHom_eq (A := A) (Γ := Γ) hz

theorem exists_adjoin_coe_eq_resHom {g : FF} (hgK : g ∈ IntermediateField.adjoin L {(jF Γ : FF)})
    (hgO : g ∈ gaussRing A Γ hT) :
    ∃ t : IntermediateField.adjoin kk {(jbar Γ kk : Fb)},
      (((t : Fb) : LaurentSeries kk)) = resHom A Γ hT ⟨g, hgO⟩ :=
  ModularCurve.QExpDeuring.exists_adjoin_coe_eq_resHom (A := A) (Γ := Γ) hgK hgO

end PolyJ

section Image

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

theorem resHom_mem
    [Module.Finite (IntermediateField.adjoin L {(jF Γ : FF)}) FF]
    [FiniteDimensional (IntermediateField.adjoin kk {(jbar Γ kk : Fb)}) Fb]
    (hle : Module.finrank (IntermediateField.adjoin L {(jF Γ : FF)}) FF ≤
      Module.finrank (IntermediateField.adjoin kk {(jbar Γ kk : Fb)}) Fb)
    (f : gaussRing A Γ hT) : resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ :=
  ModularCurve.QExpDeuring.resHom_mem (A := A) (Γ := Γ) hT f

end Image

section Assembly

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

theorem coe_smul' (c : L) (f : FF) :
    ((c • f : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c * (f : LaurentSeries L) := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]

theorem exists_smul_mem_gaussRing (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A Γ hT, resHom A Γ hT ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h⟩ := exists_frac_form (A := A) (Γ := Γ) f hf
  have key : ((c⁻¹ • f : FF) : LaurentSeries L) * ι A y₀ = ι A x₀ := by
    rw [coe_smul', mul_assoc, h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  have hmem : c⁻¹ • f ∈ gaussRing A Γ hT := (mem_gaussRing_iff A Γ hT _).mpr ⟨x₀, y₀, hy₀, key⟩
  refine ⟨c⁻¹, hmem, ?_⟩
  rw [Ne, resHom_eq A Γ hT (f := ⟨_, hmem⟩) hy₀ key]
  exact div_ne_zero hx₀ hy₀

theorem ι_mem_gaussRing {y : LaurentSeries A} (hyF : ι A y ∈ FF) : (⟨ι A y, hyF⟩ : FF) ∈ gaussRing A Γ hT :=
  ⟨y, 1, by simp, by simp⟩

theorem resHom_ι {y : LaurentSeries A} (hyF : ι A y ∈ FF) :
    resHom A Γ hT ⟨⟨ι A y, hyF⟩, ι_mem_gaussRing A Γ hT hyF⟩ = ϖ A y := by
  rw [resHom_eq A Γ hT (x := y) (y := 1) (by simp) (by simp)]; simp

def resF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) :
    gaussRing A Γ hT →+* Fb :=
  (resHom A Γ hT).codRestrict (qExpFunctionFieldC kk Γ) hmem

theorem coe_resF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) (f : gaussRing A Γ hT) : ((resF A Γ hT hmem f : Fb) : LaurentSeries kk) = resHom A Γ hT f := rfl

theorem resF_ne_zero_iff (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) (f : gaussRing A Γ hT) : resF A Γ hT hmem f ≠ 0 ↔ resHom A Γ hT f ≠ 0 := by
  rw [Ne, Ne, ← coe_resF A Γ hT hmem f, ZeroMemClass.coe_eq_zero]

theorem resF_surjective (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) : Function.Surjective (resF A Γ hT hmem) := fun z => by
  obtain ⟨f, hf⟩ := exists_resHom_eq A Γ hT z.2
  exact ⟨f, Subtype.ext hf⟩

theorem ker_resF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) : RingHom.ker (resF A Γ hT hmem) = IsLocalRing.maximalIdeal (gaussRing A Γ hT) := by
  ext f
  rw [RingHom.mem_ker, ← resHom_eq_zero_iff, ← coe_resF A Γ hT hmem f, ZeroMemClass.coe_eq_zero]

theorem resF_algebraMap (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) (a : A) (h : algebraMap L FF a ∈ gaussRing A Γ hT) :
    resF A Γ hT hmem ⟨algebraMap L FF a, h⟩ = algebraMap kk Fb (IsLocalRing.residue A a) :=
  Subtype.ext (resHom_algebraMap A Γ hT a h)

theorem exists_smul_mem_resF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ gaussRing A Γ hT, resF A Γ hT hmem ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, h, hne⟩ := exists_smul_mem_gaussRing A Γ hT f hf
  exact ⟨c, h, (resF_ne_zero_iff A Γ hT hmem _).mpr hne⟩

theorem resF_jF (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) : resF A Γ hT hmem ⟨jF Γ, jF_mem_gaussRing A Γ hT⟩ = jbar Γ kk :=
  Subtype.ext (resHom_jF A Γ hT)

theorem exists_placeMap (hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC kk Γ) [IsAlgClosed L] [IsCurveOver L FF] [IsCurveOver kk Fb]
    (hfin : Module.finrank (IntermediateField.adjoin L {(jF Γ : FF)}) FF =
      Module.finrank (IntermediateField.adjoin kk {(jbar Γ kk : Fb)}) Fb)
    (hpos : 0 < Module.finrank (IntermediateField.adjoin kk {(jbar Γ kk : Fb)}) Fb)
    (hgood : genusFF kk Fb = genusFF L FF) :
    ∃ r : Place L FF → Place kk Fb,
      ∀ f : gaussRing A Γ hT, resF A Γ hT hmem f ≠ 0 → ∀ D : Divisor L FF, (∀ P, D P = P.ord (f : FF)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (resF A Γ hT hmem f : Fb) :=
  AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction A
    (gaussRing A Γ hT) (resF A Γ hT hmem) (algebraMap_mem_gaussRing_iff A Γ hT) (resF_surjective A Γ hT hmem)
    (ker_resF A Γ hT hmem) (fun a => resF_algebraMap A Γ hT hmem a _) (exists_smul_mem_resF A Γ hT hmem)
    ⟨⟨jF Γ, jF_mem_gaussRing A Γ hT⟩, by
      rw [resF_jF]
      exact ⟨transcendental_jbar Γ kk, hpos, hfin⟩⟩
    hgood

end Assembly

section ClauseB

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

theorem exists_mem_integralPrincipalDivisors_of_mem_adjoin [HasPrincipalDivisors L FF]
    (hq : ∀ y : LaurentSeries A, ι A y ∈ FF → ϖ A y ∈ Fb)
    {x : LaurentSeries L} (hx : x ∈ Algebra.adjoin L (gensF Γ L)) (hx0 : x ≠ 0) :
    ∃ D₀ ∈ laurentIntegralPrincipalDivisors A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ) Fb,
      ∀ v : Place L FF, D₀ v = v.ord (⟨x, algebra_adjoin_gensF_le Γ L hx⟩ : FF) := by
  obtain ⟨M, hM, hxM⟩ := exists_fg_coeff_mem (Γ := Γ) (L := L) hx
  obtain ⟨c, hc0, hcA, n₀, hn₀⟩ := exists_primitive_scaling A hx0 M hM hxM
  have hxF : x ∈ FF := algebra_adjoin_gensF_le Γ L hx
  have hx'F : algebraMap L (LaurentSeries L) c⁻¹ * x ∈ FF :=
    mul_mem ((laurentBaseChange L (qExpFunctionFieldC ℚ Γ)).algebraMap_mem _) hxF
  have hcoeff : ∀ n, (algebraMap L (LaurentSeries L) c⁻¹ * x).coeff n = c⁻¹ * x.coeff n := fun n => by
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]
  obtain ⟨y, hy⟩ := exists_coeffMap_subtype_eq A (algebraMap L (LaurentSeries L) c⁻¹ * x) fun n => by
    rw [hcoeff]; exact hcA n
  have hyF : ι A y ∈ FF := hy ▸ hx'F
  have hyk : ϖ A y ∈ Fb := hq y hyF
  have hy0 : ϖ A y ≠ 0 := by
    intro h
    have h1 := congrArg (fun s : LaurentSeries kk => s.coeff n₀) h
    simp only [coeffMap_coeff, HahnSeries.coeff_zero] at h1
    have h2 : (y.coeff n₀ : L) = 1 := by
      have := congrArg (fun s : LaurentSeries L => s.coeff n₀) hy
      simp only [coeffMap_coeff, hcoeff] at this
      rw [← hn₀]; exact this
    have h3 : y.coeff n₀ = 1 := Subtype.ext (by simpa using h2)
    rw [h3, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨D₀, hD₀, -⟩ :=
    HasPrincipalDivisors.exists_divisor (K := L) (⟨ι A y, hyF⟩ : FF) (by
      intro h
      apply hy0
      have h' : ι A y = 0 := congrArg Subtype.val h
      rw [(ι_eq_zero_iff A y).mp h', map_zero])
  refine ⟨D₀, ⟨y, hyF, hyk, hy0, hD₀⟩, fun v => ?_⟩
  rw [hD₀ v]
  have heq : (⟨ι A y, hyF⟩ : FF) = algebraMap L FF c⁻¹ * ⟨x, hxF⟩ := by
    apply Subtype.ext
    change ι A y = algebraMap L (LaurentSeries L) c⁻¹ * x
    rw [hy]
  have hxne : (⟨x, hxF⟩ : FF) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hcne : algebraMap L FF c⁻¹ ≠ 0 := (_root_.map_ne_zero _).mpr (inv_ne_zero hc0)
  have hc0' : v.ord (algebraMap L FF c⁻¹) = 0 := by
    have h := v.ord_coe_unit
      (Units.map (algebraMap L v.toValuationSubring).toMonoidHom (Units.mk0 c⁻¹ (inv_ne_zero hc0)))
    simpa using h
  rw [heq, v.ord_mul hcne hxne, hc0', zero_add]

include hT in
theorem laurentPrincipalGeneratedByIntegral_of [HasPrincipalDivisors L FF]
    (hq : ∀ y : LaurentSeries A, ι A y ∈ FF → ϖ A y ∈ Fb) :
    LaurentPrincipalGeneratedByIntegral A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ) Fb := by
  intro D hD
  obtain ⟨f, hf0, hDf⟩ := Divisor.mem_principal.mp hD
  have hfF : (f : LaurentSeries L) ∈ adjoin L (gensF Γ L) := laurentBaseChange_le_adjoin_gensF Γ L hT f.2
  obtain ⟨r, hr, s, hs, hrs⟩ := (mem_adjoin_iff_div (F := L)).mp hfF
  have hf0' : (f : LaurentSeries L) ≠ 0 := fun h => hf0 (Subtype.ext h)
  have hr0 : r ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, zero_div])
  have hs0 : s ≠ 0 := by rintro rfl; exact hf0' (by rw [hrs, div_zero])
  obtain ⟨Dr, hDr, hDr'⟩ := exists_mem_integralPrincipalDivisors_of_mem_adjoin A Γ hq hr hr0
  obtain ⟨Ds, hDs, hDs'⟩ := exists_mem_integralPrincipalDivisors_of_mem_adjoin A Γ hq hs hs0
  have hrF : r ∈ FF := algebra_adjoin_gensF_le Γ L hr
  have hsF : s ∈ FF := algebra_adjoin_gensF_le Γ L hs
  have hfeq : f = (⟨r, hrF⟩ : FF) * (⟨s, hsF⟩ : FF)⁻¹ := by
    apply Subtype.ext
    rw [hrs, div_eq_mul_inv]
    rfl
  have hrne : (⟨r, hrF⟩ : FF) ≠ 0 := fun h => hr0 (congrArg Subtype.val h)
  have hsne : (⟨s, hsF⟩ : FF)⁻¹ ≠ 0 := inv_ne_zero fun h => hs0 (congrArg Subtype.val h)
  have hDeq : D = Dr - Ds := by
    ext v
    rw [Finsupp.sub_apply, hDf v, hDr' v, hDs' v, hfeq, v.ord_mul hrne hsne, v.ord_inv]
    ring
  rw [hDeq]
  exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure hDr) (AddSubgroup.subset_closure hDs)

end ClauseB

end QExpDeuringRed

/-! ## The headline -/

open QExpDeuringRed in
theorem reductionInputsQExpModL_of_finrank_le_of_genusFF_eq
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hdeg : ∀ (x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)
      (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)),
      (x : LaurentSeries (IsLocalRing.ResidueField A)) =
          ModularCurve.jqModC (IsLocalRing.ResidueField A) →
      (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
      Module.finrank
          (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ)) ≤
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)))
          (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ))
    (hgen : AlgebraicCurve.genusFF (IsLocalRing.ResidueField A)
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) =
      AlgebraicCurve.genusFF (AlgebraicClosure ℚ)
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
    ModularCurve.ReductionInputsQExpModL A Γ := by
  obtain ⟨x, hx, htr, hfinb, hleP⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
      (AlgebraicClosure ℚ) A Γ hT
  obtain rfl : x = QExpDeuring.jbar Γ (IsLocalRing.ResidueField A) := Subtype.ext hx
  haveI := hfinb
  have hpos : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) {(QExpDeuring.jbar Γ (IsLocalRing.ResidueField A) :
        qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)})
      (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) := Module.finrank_pos
  have h1 := hleP (jF Γ) (coe_jF Γ)
  set K0 : IntermediateField (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
    IntermediateField.adjoin (AlgebraicClosure ℚ)
      {(jF Γ : laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ))} with hK0
  have hposK : 0 < Module.finrank K0
      (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
    lt_of_lt_of_le hpos h1
  haveI : Module.Free K0 (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
    Module.Free.of_divisionRing K0 _
  haveI : Module.Finite K0 (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) :=
    Module.finite_of_finrank_pos hposK
  have h2 := hdeg (QExpDeuring.jbar Γ (IsLocalRing.ResidueField A)) (jF Γ) rfl (coe_jF Γ)
  have hfin := le_antisymm h2 h1
  have hmem : ∀ f : gaussRing A Γ hT, resHom A Γ hT f ∈ qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ :=
    resHom_mem A Γ hT h2

  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (IsLocalRing.ResidueField A) := IsAlgClosed.perfectField _
  haveI : IsCurveOver (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) := by
    obtain ⟨z, hz, hzfin⟩ :=
      ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange (AlgebraicClosure ℚ) Γ hT
    exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hz hzfin
  haveI : IsCurveOver (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfinb

  obtain ⟨r, hr⟩ := exists_placeMap A Γ hT hmem hfin hpos hgen
  refine ⟨r, ⟨fun P => ?_, fun y hy hyk hy0 D hD Q => ?_⟩,
    laurentPrincipalGeneratedByIntegral_of A Γ hT fun y hyF => ?_⟩
  · rw [IsCurveOver.deg_eq_one_of_isAlgClosed (K := IsLocalRing.ResidueField A) (r P),
      IsCurveOver.deg_eq_one_of_isAlgClosed (K := AlgebraicClosure ℚ) P]
  · have hres : resF A Γ hT hmem ⟨⟨QExpDeuring.ι A y, hy⟩, ι_mem_gaussRing A Γ hT hy⟩ =
        ⟨QExpDeuring.ϖ A y, hyk⟩ := Subtype.ext (resHom_ι A Γ hT hy)
    have hne : resF A Γ hT hmem ⟨⟨QExpDeuring.ι A y, hy⟩, ι_mem_gaussRing A Γ hT hy⟩ ≠ 0 := by
      rw [hres]; exact fun h => hy0 (congrArg Subtype.val h)
    have := hr ⟨⟨QExpDeuring.ι A y, hy⟩, ι_mem_gaussRing A Γ hT hy⟩ hne D hD Q
    rwa [hres] at this
  · have h := hmem ⟨⟨QExpDeuring.ι A y, hyF⟩, ι_mem_gaussRing A Γ hT hyF⟩
    rwa [resHom_ι A Γ hT hyF] at h

end ModularCurve

end
