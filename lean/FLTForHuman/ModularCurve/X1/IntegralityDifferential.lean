/-
Integrality on `X₁` from a regular differential.

The `q`-expansion of a weight-two object is the bridge between the analytic and the algebraic
side of `X₁`: `diffQExp` maps a Kähler differential on the `X₁` function field to a power series,
and a **regular** differential is one whose order at every place is nonnegative.  This module
proves the criterion

  if `ω` is a differential on the `X₁` function field over the algebraic closure whose
  `q`-expansion is the `q`-expansion of a weight-2 cusp form for `Γ₁(M)`, then `ω` is regular
  (and the element it is built from is integral),

i.e. the inverse of "a cusp form gives a regular differential": the `q`-expansion alone forces
regularity.  The proof is the order calculus at the places of `X₁`: the integrality of the
`jq`-coefficients (`Analytic/JqInverseIntegral.lean`, `JqIntegralRatios.lean`) bounds
`ord (y^{6} (y - 1728)^{4})`, `Place.ordDiff_smul_D_nonneg_of_ord_pow_six_mul_pow_four_mul_sub_1728_pow_three_nonneg`
converts that bound into a nonnegativity of the divisor of the differential, and
`regularDiffs_eq_regularDifferentials` identifies the algebraic regularity with the
order-theoretic one.

The engine is the differential/place calculus of `AlgebraicCurve`
(`Differential/{Coefficient,ConstantFieldExtension,RegularDiffs}.lean`,
`Place/OrdCalculus.lean`, `Defs/{KaehlerTranscendental,PushPull,WeilOfKaehler}.lean`), the
constant-field-extension genus computations (`Genus/ConstantFieldExtension*`), the
regular-prolongation residue identities (`RegularProlongation{OrdResidueEquality,ReducedPlace,SumOrdResidue}.lean`),
the `X₁` function field's curve structure (`X1/FunctionFieldIsAlgClosed.lean`,
`X1/CoeffMap.lean`) and SET-AF104E's `X1/GenusBound.lean`.

Port notes (order AF105E).

* **Transcription.** The pin's `S_` file is a flat all-public engine (8 declarations, 340 lines)
  and it is transcribed in full, so the module carries the pin's 5 remaining rows at the pin's
  names and statements; the pin's generated namespace label (`P2MW.S_…`) comes off, its `IntH`
  helper namespace is kept (it is the pin's own, not a generated label), and the pin's `solution`
  row is the module's headline at the wrapper's published name. `P2M/Util.lean`'s macros and the
  pin's two `attribute [-instance]` / `attribute [-simp]` walls are not transcribed.
* **Substitutions.** Three of the eight pin rows are imported, not re-proved: `ord_pow'`,
  `ord_algebraMap`, `ord_neg` (details below). `ord_pos_of_mem_maximalIdeal` and `exists_value`
  are **not** the port's `Place.ord_pos_of_mem_maximalIdeal` /
  `DeuringMultiplicity.exists_sub_algebraMap_mem_nonunits` — the first takes its element already
  in the valuation subring, the second concludes `∈ nonunits` rather than the pin's
  `= 0 ∨ 0 < ord` — so both are transcribed (the first as a one-line wrapper of the port's own
  lemma). This is the FR-0266 check on the three rows `port_advise` proposed.
* **The two instance sites (the pin's `synthInstance.maxHeartbeats 1600000`).** They are the
  only places where the pin's options were load-bearing, and both are instance-inference defects,
  not spread cost: `hSEP : Algebra.IsSeparable ↥ℚ̄⟮x₀⟯ F := inferInstance` and the
  `Module.IsTorsionFree ↥ℚ̄⟮x₀⟯ F` search behind `Module.finrank_pos` (the pin's `hψpos`). Both
  are supplied by **direct terms** here — `Algebra.IsAlgebraic.isSeparable_of_perfectField` and
  `DivisionSemiring.to_moduleIsTorsionFree` — which is what makes the declaration fit at the
  edit loop's cap. See the probe pair below.
* **Visibility.** Nothing is `private` in this module (the pin has no private row), so the surface
  gate is vacuous: all 5 declarations are public and read `ok`.
* **Axioms.** `#print axioms` on all 5 public declarations: each is a subset of
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **Dedup / move_dead.** `dedup.py --within --module '*X1/IntegralityDifferential*'`: 5
  declarations, **0 duplicate clusters**, 0 removable lines. `move_dead.py --dry-run`:
  **0 declarations, 0 lines**.
* **Heartbeat probe pair** (FR-0225 — measured, never installed). The pin carries
  `set_option synthInstance.maxHeartbeats 1600000` (`S_…:33`, again on `solution` at `:142`) and
  `set_option maxHeartbeats 6400000` (`:34`); this file carries neither. Readings, at the
  project's low cap (`-DmaxHeartbeats=200000`, `synthInstance` default 20000):
  the file as written is **silent**. With the pin's own text restored at the two sites
  (`tmp/af105/probe-E-hb-intdiff.lean`, probes A/B/I) both **time out at 20000** and succeed at
  **40000** (probes C/D) and at the pin's 1 600 000 (E/F), i.e. the minimal `synthInstance` cap is
  in `(20000, 40000]`; with the port's two direct terms (G/H) the same sites are silent at the
  default cap. The 6 400 000 `maxHeartbeats` is unnecessary: nothing here exceeds 200 000.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC.lean>

spec-pin: Theorems/Thm_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC.lean
spec-pin: P2M/Sol/S_ModularCurve_isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler
import FLTForHuman.AlgebraicCurve.DeuringMultiplicity
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Differential.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Differential.RegularDiffs
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionSpan
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.RegularProlongationOrdResidueEquality
import FLTForHuman.AlgebraicCurve.RegularProlongationReducedPlace
import FLTForHuman.AlgebraicCurve.RegularProlongationSumOrdResidue
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.X1.FunctionFieldIsAlgClosed
import FLTForHuman.ModularCurve.X1.GenusBound

noncomputable section

set_option autoImplicit false

-- The pin's `haveI` walls are kept verbatim (they are the instance-inference sites the
-- heartbeat probe reads); the linter is silenced locally, as in
-- `AlgebraicCurve/Differential/Coefficient.lean`.
set_option linter.style.haveILetI false

open scoped MatrixGroups
open ModularCurve AlgebraicCurve HahnSeries KaehlerDifferential

/-! ## The order calculus at the places of `X₁`

Three of the pin's eight declarations are **substituted**, not re-proved (the pin's `IntH`
prelude, `P2M/Sol/S_…_qExpFunctionFieldC.lean:47–66`):

* `ord_pow'` — `AlgebraicCurve.RegularProlongation.DeuringMultiplicity.ord_pow`
  (`DeuringMultiplicity.lean`, binder spelling only);
* `ord_algebraMap` — `AlgebraicCurve.PolarFinrank.ord_algebraMap_eq_zero`
  (`Canonical/PolarDifferentials.lean`, byte-identical);
* `ord_neg` — `ModularCurve.GF24a9RRDx.gf24a9r_ord_neg` (`ResidueTheorem/KCotrace.lean`,
  binder spelling only).

The pin's `ord_pos_of_mem_maximalIdeal` (`:68`) and `exists_value` (`:82`) are **not** the
port's `Place.ord_pos_of_mem_maximalIdeal` / `DeuringMultiplicity.exists_sub_algebraMap_mem_nonunits`:
the first takes its element already in the valuation subring, the second concludes membership in
`nonunits` rather than the pin's `= 0 ∨ 0 < ord` disjunction.  Both statements differ, so both
are transcribed (the first as a four-line wrapper of the port's own lemma). -/

namespace IntH

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- (pin `IntH.ord_pos_of_mem_maximalIdeal`, `S_…:68`) The pin's `toValuationSubring`-element
shape of the port's public `Place.ord_pos_of_mem_maximalIdeal`
(`Place/OrdCalculus.lean`), which takes the element and its membership unpacked. -/
theorem ord_pos_of_mem_maximalIdeal (v : Place K F) {a : v.toValuationSubring}
    (ha : a ∈ IsLocalRing.maximalIdeal v.toValuationSubring) (ha0 : (a : F) ≠ 0) :
    0 < v.ord (a : F) :=
  Place.ord_pos_of_mem_maximalIdeal v ha0 a.2 ha

/-- (pin `IntH.exists_value`, `S_…:82`) At a place of a curve over an algebraically closed
field, an integral element is a constant to first order at some constant. -/
theorem exists_value [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    ∃ c : K, f - algebraMap K F c = 0 ∨ 0 < v.ord (f - algebraMap K F c) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨c, hc⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩)
  refine ⟨c, ?_⟩
  have hmem : (⟨f, hf⟩ - algebraMap K v.toValuationSubring c : v.toValuationSubring) ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← hc]
    rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField]
    exact sub_self _
  have hcoe : ((⟨f, hf⟩ - algebraMap K v.toValuationSubring c : v.toValuationSubring) : F) =
      f - algebraMap K F c := by
    push_cast
    rw [v.coe_algebraMap]
  by_cases h0 : f - algebraMap K F c = 0
  · exact Or.inl h0
  · right
    have := ord_pos_of_mem_maximalIdeal v hmem (by rw [hcoe]; exact h0)
    rwa [hcoe] at this

end Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- (pin `IntH.ord_bound`, `S_…:110`) The `q`-expansion bounds the order of `x` from below:
if `x • D J` is regular, then at a place where `g` has nonzero order and `D g = D J`,
`1 - ord g ≤ ord x`.  This is the inequality the two `isIntegral` conclusions consume. -/
theorem ord_bound [PerfectField K] [CharZero K] (J : F) (hDJ : D K F J ≠ 0)
    [FiniteDimensional ↥(IntermediateField.adjoin K ({J} : Set F)) F]
    (x : F) (hx0 : x ≠ 0) (hreg : ∀ v : Place K F, 0 ≤ v.ordDiff (x • D K F J))
    (v : Place K F) {g : F} (hg : v.ord g ≠ 0) (hDg : D K F g = D K F J) :
    1 - v.ord g ≤ v.ord x := by
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin K ({J} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  have h := hreg v
  rw [← hDg] at h
  rw [Place.ordDiff_smul_of_perfectField J v hx0 (by rw [hDg]; exact hDJ),
    Place.ordDiff_D_eq_ord_sub_one J v hg] at h
  omega

/-- (pin `IntH.ram_profile`, `S_…:121`) The ramification profile of the `j`-line over
`X₁`: `j` has order at most `3`, `j - 1728` at most `2`, and `j - a` at most `1` for every
other nonzero `a`.  SET-AF104E's `X1/GenusBound.lean` proves the same statement for
`laurentBaseChange`; the pin's `key` transports it along
`laurentBaseChange_qExpFunctionFieldC_eq`. -/
theorem ram_profile (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ)
    (jbar : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))
    (hjbar : (jbar : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) :
    v.ord jbar ≤ 3 ∧
      v.ord (jbar -
        algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ≤ 2 ∧
      (∀ a : AlgebraicClosure ℚ, a ≠ 0 → a ≠ 1728 →
        v.ord (jbar -
          algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) a) ≤ 1) := by
  have key : ∀ (E : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))),
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) = E →
      ∀ (y : ↥E), (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
        ∀ P : Place (AlgebraicClosure ℚ) ↥E,
        P.ord y ≤ 3 ∧
          P.ord (y - algebraMap (AlgebraicClosure ℚ) ↥E 1728) ≤ 2 ∧
          (∀ a : AlgebraicClosure ℚ, a ≠ 0 → a ≠ 1728 →
            P.ord (y - algebraMap (AlgebraicClosure ℚ) ↥E a) ≤ 1) := by
    rintro E rfl y hy P
    have h :=
      ModularCurve.ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure
        M Γ hΓ₁ y hy P
    refine ⟨h.1, ?_, h.2.2⟩
    rw [map_ofNat]
    exact h.2.1
  exact key _ (ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq (AlgebraicClosure ℚ) Γ) jbar hjbar v

end IntH

open IntH in
/-- (pin `solution`, `S_…:143`; statement from the `Theorems/` wrapper) **Integrality on `X₁`
from a regular differential.**  If the `q`-expansion of `x` is that of a weight-2 cusp form for
`Γ₁(M)` and `x • D j` is regular, then `x ^ 6 j ^ 4 (j - 1728) ^ 3` is integral over `ℚ[j]`
and `x ^ (2ψ) j ^ (ψ+1) (j - 1728) ^ ψ` is integral over `ℚ[j⁻¹]`, `ψ` the degree of the
`X₁ → j`-line cover.

The proof is the pin's, declaration for declaration: `x = 0` is trivial; otherwise the pole set
of `j` sums to `ψ` (`exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed`), `ord_bound` turns
regularity of `x • D j` into a lower bound for `ord x` at every place, `ram_profile` supplies
the upper bounds for `ord j`, `ord (j - 1728)` and `ord (j - a)`, and
`isIntegral_adjoin_of_forall_ord_nonneg` closes. -/
theorem ModularCurve.isIntegral_and_isIntegral_of_smul_D_mem_regularDifferentials_qExpFunctionFieldC
    (M : ℕ) [NeZero M] (Γ : Subgroup SL(2, ℤ))
    (hΓ₁ : CongruenceSubgroup.Gamma1 M ≤ Γ) (_hΓ₀ : Γ ≤ CongruenceSubgroup.Gamma0 M)
    (jbar : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))
    (hjbar : (jbar : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (x : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))
    (hx : x • KaehlerDifferential.D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) jbar ∈
      regularDifferentials (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) :
    IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)))
        (x ^ 6 * jbar ^ 4 * (jbar - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ^ 3) ∧
      IsIntegral ↥(Algebra.adjoin (AlgebraicClosure ℚ) ({jbar⁻¹} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)))
        (x ^ (2 * Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) *
          jbar ^ (Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) + 1) *
          (jbar - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ^
            Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({jbar} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) := by
  classical
  haveI : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ₁
  have hT : ModularGroup.T ∈ Γ := hΓ₁ (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  obtain ⟨x₀, hx₀, htr, hFD⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
      (AlgebraicClosure ℚ) Γ hT
  have hxj : x₀ = jbar := Subtype.ext (hx₀.trans hjbar.symm)
  subst hxj
  haveI := hFD
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hFD
  haveI hEFT : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hFD
  haveI hALG : Algebra.IsAlgebraic ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x₀} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI hSEP : Algebra.IsSeparable ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x₀} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := IsCurveOver.hasPrincipalDivisors
  have hDJ : D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) x₀ ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental (AlgebraicClosure ℚ) x₀ htr
  set ψ : ℕ := Module.finrank ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x₀} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) with hψdef
  set J : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := x₀ with hJdef
  haveI hTF : Module.IsTorsionFree
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x₀} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)))
      ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) :=
    DivisionSemiring.to_moduleIsTorsionFree
  have hψpos : 0 < ψ := Module.finrank_pos
  have hJ0 : J ≠ 0 := by
    intro h
    apply hDJ
    rw [h, map_zero]
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨?_, ?_⟩
    · rw [zero_pow (by norm_num), zero_mul, zero_mul]; exact isIntegral_zero
    · rw [zero_pow (by omega), zero_mul, zero_mul]; exact isIntegral_zero
  have hreg : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), 0 ≤ v.ordDiff (x • D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) J) := by
    have h1 : x • D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) J ∈ regularDiffs (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := by
      rw [AlgebraicCurve.regularDiffs_eq_regularDifferentials]; exact hx
    exact (AlgebraicCurve.mem_regularDiffs_iff (J : ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) _).mp h1
  obtain ⟨S, hS, hsum⟩ := AlgebraicCurve.exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed (AlgebraicClosure ℚ) J htr hFD
  have hwidth : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), v.ord J < 0 → -v.ord J ≤ (ψ : ℤ) := by
    intro v hv
    rw [hψdef, ← hsum]
    exact Finset.single_le_sum (f := fun w => -w.ord J)
      (fun w hw => by have := (hS w).mp hw; show (0 : ℤ) ≤ -w.ord J; omega) ((hS v).mpr hv)
  have hpole : ∃ v₀ : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), v₀.ord J < 0 := by
    by_contra hno
    push Not at hno
    have hSe : S = ∅ := by
      ext v
      simp only [Finset.notMem_empty, iff_false]
      intro hv
      exact absurd ((hS v).mp hv) (not_lt.mpr (hno v))
    rw [hSe, Finset.sum_empty] at hsum
    have h' : (ψ : ℤ) = 0 := by rw [hψdef]; exact hsum.symm
    omega
  obtain ⟨v₀, hv₀⟩ := hpole
  have hram := fun v => IntH.ram_profile M Γ hΓ₁ J hjbar v
  have hJne1728 : J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have := PolarFinrank.ord_algebraMap_eq_zero v₀ (c := (1728 : (AlgebraicClosure ℚ))) (by norm_num)
    rw [← h] at this
    omega
  have h1728_0 : v₀.ord (algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = 0 := PolarFinrank.ord_algebraMap_eq_zero v₀ (by norm_num)
  have hordJsub_of_pos : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), 0 < v.ord J → v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = 0 := by
    intro v hv
    have hc : v.ord (-(algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728)) = 0 := by rw [GF24a9RRDx.gf24a9r_ord_neg]; exact PolarFinrank.ord_algebraMap_eq_zero v (by norm_num)
    have := v.ord_add_eq_of_lt (f := -(algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728)) (g := J)
      (neg_ne_zero.mpr (by rw [Ne, map_eq_zero]; norm_num)) hJ0 (by rw [hc]; exact hv)
    rw [hc] at this
    rwa [sub_eq_add_neg, add_comm]
  have hordJsub_of_neg : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), v.ord J < 0 → v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = v.ord J := by
    intro v hv
    have hc : v.ord (-(algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728)) = 0 := by rw [GF24a9RRDx.gf24a9r_ord_neg]; exact PolarFinrank.ord_algebraMap_eq_zero v (by norm_num)
    have := v.ord_add_eq_of_lt (f := J) (g := -(algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728)) hJ0
      (neg_ne_zero.mpr (by rw [Ne, map_eq_zero]; norm_num)) (by rw [hc]; exact hv)
    rwa [← sub_eq_add_neg] at this
  have hordJ_of_sub_pos : ∀ (v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) (c : (AlgebraicClosure ℚ)), c ≠ 0 → 0 < v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) →
      v.ord J = 0 := by
    intro v c hc hv
    have h1 : v.ord (algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) = 0 := PolarFinrank.ord_algebraMap_eq_zero v hc
    have hne : J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c ≠ 0 := by
      intro h; rw [h, v.ord_zero] at hv; exact lt_irrefl _ hv
    have := v.ord_add_eq_of_lt (f := algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) (g := J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c)
      (by rw [Ne, map_eq_zero]; exact hc) hne (by rw [h1]; exact hv)
    rw [h1, add_sub_cancel] at this
    exact this
  have hDsub : ∀ c : (AlgebraicClosure ℚ), D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) = D (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) J := by
    intro c
    rw [map_sub, Derivation.map_algebraMap, sub_zero]
  have hfinite : ∀ v : Place (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ), v.ord J = 0 →
      (0 ≤ v.ord x ∧ v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = 0) ∨
      (∃ a : ℤ, 0 < a ∧ a ≤ 2 ∧ v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) = a ∧ 1 - a ≤ v.ord x) := by
    intro v hvJ
    have hJmem : J ∈ v.toValuationSubring := by rw [v.mem_iff_ord_nonneg hJ0, hvJ]
    obtain ⟨c, hc⟩ := exists_value v hJmem
    have hcpos : 0 < v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) := by
      rcases hc with hc | hc
      · exfalso
        rw [sub_eq_zero] at hc
        have := PolarFinrank.ord_algebraMap_eq_zero v₀ (c := c) (by rintro rfl; rw [map_zero] at hc; exact hJ0 hc)
        rw [← hc] at this
        omega
      · exact hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, sub_zero] at hcpos
      omega
    by_cases hc1728 : c = 1728
    · subst hc1728
      right
      refine ⟨v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728), hcpos, ?_, rfl, ?_⟩
      · exact (hram v).2.1
      · exact IntH.ord_bound J hDJ x hx0 hreg v hcpos.ne' (hDsub 1728)
    · left
      have h1 : v.ord (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) = 1 := by
        have hle := (hram v).2.2 c hc0 hc1728
        omega
      have hb := IntH.ord_bound J hDJ x hx0 hreg v (g := J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c) (by rw [h1]; norm_num) (hDsub c)
      rw [h1] at hb
      refine ⟨by omega, ?_⟩
      have hcc : v.ord (algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) (c - 1728)) = 0 := PolarFinrank.ord_algebraMap_eq_zero v (sub_ne_zero.mpr hc1728)
      have := v.ord_add_eq_of_lt (f := algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) (c - 1728)) (g := J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) c)
        (by rw [Ne, map_eq_zero]; exact sub_ne_zero.mpr hc1728)
        (by intro h; rw [h, v.ord_zero] at hcpos; exact lt_irrefl _ hcpos) (by rw [hcc]; exact hcpos)
      rw [hcc] at this
      rw [← this, map_sub]
      congr 1
      ring
  refine ⟨?_, ?_⟩
  ·
    refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := (AlgebraicClosure ℚ)) (F := ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) J htr _ ?_
    intro v hvJ
    have hne : x ^ 6 * J ^ 4 * (J - algebraMap (AlgebraicClosure ℚ) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) 1728) ^ 3 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728)
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), RegularProlongation.DeuringMultiplicity.ord_pow, RegularProlongation.DeuringMultiplicity.ord_pow, RegularProlongation.DeuringMultiplicity.ord_pow]
    rcases hvJ.lt_or_eq with hpos | hzero
    ·
      have ha3 : v.ord J ≤ 3 := (hram v).1
      have hb := IntH.ord_bound J hDJ x hx0 hreg v hpos.ne' rfl
      rw [hordJsub_of_pos v hpos]
      push_cast
      nlinarith
    · rcases hfinite v hzero.symm with ⟨hx', h1728'⟩ | ⟨a, ha0, ha2, h1728', hb⟩
      · rw [← hzero, h1728']; push_cast; nlinarith
      · rw [← hzero, h1728']; push_cast; nlinarith
  ·
    have htr' : Transcendental (AlgebraicClosure ℚ) J⁻¹ := by
      intro halg
      exact htr (by simpa using halg.inv)
    have hadj : IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) = IntermediateField.adjoin (AlgebraicClosure ℚ) ({J} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) J)
      · rw [IntermediateField.adjoin_simple_le_iff]
        have h1 := IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) (J⁻¹)
        have h2 : (J⁻¹)⁻¹ ∈ IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) := inv_mem h1
        rwa [inv_inv] at h2
    haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({J⁻¹} : Set ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ))) ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ) := by
      rw [hadj]; exact hFD
    refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg (K := (AlgebraicClosure ℚ)) (F := ↥(qExpFunctionFieldC (AlgebraicClosure ℚ) Γ)) J⁻¹ htr' _ ?_
    intro v hvJinv
    rw [v.ord_inv] at hvJinv
    have hvJ : v.ord J ≤ 0 := by omega
    rw [v.ord_mul (mul_ne_zero (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0)) (pow_ne_zero _ hJne1728),
      v.ord_mul (pow_ne_zero _ hx0) (pow_ne_zero _ hJ0), RegularProlongation.DeuringMultiplicity.ord_pow, RegularProlongation.DeuringMultiplicity.ord_pow, RegularProlongation.DeuringMultiplicity.ord_pow]
    rcases hvJ.lt_or_eq with hneg | hzero
    ·
      have hw := hwidth v hneg
      have hb := IntH.ord_bound J hDJ x hx0 hreg v hneg.ne rfl
      rw [hordJsub_of_neg v hneg]
      push_cast
      nlinarith
    · rcases hfinite v hzero with ⟨hx', h1728'⟩ | ⟨a, ha0, ha2, h1728', hb⟩
      · rw [hzero, h1728']; push_cast; nlinarith
      · rw [hzero, h1728']; push_cast; nlinarith
