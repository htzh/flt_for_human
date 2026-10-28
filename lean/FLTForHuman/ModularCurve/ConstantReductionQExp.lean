/-
  The constant reduction of the `q`-expansion function field at the Gauss place `q = 0` —
  `ModularCurve.exists_constantReduction_pic0Map_eq_reductionQExpModL`.

  For `A : ValuationSubring (AlgebraicClosure ℚ)` and a reduction input
  `h : ReductionInputsQExpModL A Γ`, the theorem produces a `ConstantReduction` of
  `FF = laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)` into
  `Fb = qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ` whose integers are the Gauss
  ring `gaussRing A Γ = {f | IsInt A f}` (`∃ x y, ϖ y ≠ 0 ∧ f * ι y = ι x`), whose residue
  is the codomain restriction `resF A hT`, whose place map is `placeReductionQExpModL h`
  and whose `Pic0` map is `reductionQExpModL A Γ`, and which reproduces
  `coeffMap (IsLocalRing.residue A)` on the integral series. The hard steps are
  `resF_surjective` (the residue image *is* `Fb`) and `mapDomain_placeMap` (the place map
  extends to divisors, through the closure of the integral principal divisors and the
  "order-0 element is an `A`-constant" step: `JOneES.exists_transcendental_…` plus
  `Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed`).

  Proof transcribed from FLT's
  `P2M/Sol/S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.lean`
  (pin `aa2d8b3`) — its `PlaceMap` section, `S_:788–930`; the headline statement is
  verbatim from
  `Theorems/Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.lean`.
  The pin's `Forms` … `end Gauss` engine block (lines 131–786, byte-identical to the
  regular-prolongation row's block) is not repeated here: see below.

  **The residue dictionary is the shared home `X1/GaussResidue.lean`.** The Gauss ring
  `gaussRing A Γ`, its residue map `resHom A Γ`, the codomain restriction `resF A hT` with
  `coe_resF`, `resF_ne_zero_iff`, `ker_resF`, `resF_surjective`, `resF_algebraMap`,
  `exists_smul_mem_resF`, and `ι_mem_gaussRing`, `resHom_ι`,
  `inv_mem_gaussRing_of_resHom_ne_zero`, `coe_smul'`, `exists_smul_mem_gaussRing`,
  `resHom_mem` are public there (`ModularCurve.QExpDeuring`), written once for this row and
  the three regular-prolongation rows; this module imports it and adds only the pin's
  `PlaceMap` section and the headline.

  **Why the assembly carries the fractional-form chain.** `resHom_mem` — hence `resF`, the
  whole codomain restriction — needs the pin's *fourth* conjunct of `exists_frac_form`:
  that the reduced ratio `ϖ u₀ / ϖ w₀` lies in the residue function field
  `qExpFunctionFieldC kk Γ`. The engine's public `QExpDeuring.exists_frac_form` has only
  the first three conjuncts (it is the version stated in the pin's
  `…qExpFunctionFieldC_residueField` sibling), and `exists_resHom_eq` proves the *opposite*
  containment `qExpFunctionFieldC kk Γ ≤ range (resHom A Γ)` — which is exactly what
  `resF_surjective` uses. So there is no cheaper route to `resF`, and the proof of the
  fourth conjunct (the `Lam`/`homSpan`/`IsFrac` chain, `exists_frac_form_mem` and
  `div_mem_qExpFunctionFieldC_of_mem_span`) is carried `private` in `X1/GaussResidue.lean`:
  engine internals, not surface.

  **Statements.** The pin's `hT : ModularGroup.T ∈ Γ` is an unused explicit parameter of
  its `gaussRing`/`resHom` definitions, while the port's engine is `Γ`-shaped. The four
  declarations whose pin statement names `gaussRing A hT` / `resHom A hT` state the weaker
  `gaussRing A Γ` / `resHom A Γ` form and carry an in-source `own:` marker with that
  reason; `gaussReduction`, `pic0Map_gaussReduction`, `residue_gaussReduction` and `main`
  go through the `FF`/`Fb` notations and are the pin's statements verbatim.

  Not ported: `resRange`, `div_intSeriesC_mem`, `qExpFunctionFieldC_le_resRange` — the
  pin's alternative route to `resF_surjective` (the port proves it from
  `QExpDeuring.exists_resHom_eq`). No `set_option maxHeartbeats`: the pin's
  `mapDomain_placeMap` carries `set_option maxHeartbeats 1600000 in`, which is not
  transcribed — the project cap is 4,000,000 and the module closes at the edit loop's
  200,000.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.lean

  spec-pin: Theorems/Thm_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_constantReduction_pic0Map_eq_reductionQExpModL.lean

-/
import FLTForHuman.ModularCurve.Defs.QExpReductionModL
import FLTForHuman.ModularCurve.X1.GaussResidue
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.AlgebraicCurve.ConstantReduction
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension

set_option autoImplicit false

noncomputable section

open scoped Classical MatrixGroups
open IntermediateField HahnSeries PowerSeries AlgebraicCurve

namespace ModularCurve

namespace ConstantReductionQExp

open QExpDeuring

/-! ## The pin's `PlaceMap` block — the `ConstantReduction` itself -/

section PlaceMap

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
variable (A : ValuationSubring (AlgebraicClosure ℚ)) (h : ReductionInputsQExpModL A Γ)

local notation "Qb" => AlgebraicClosure ℚ
local notation "FF" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ

/-- The `Algebra (IsLocalRing.ResidueField A) Fb` structure that `Place`/`ConstantReduction`
ask for: given explicitly once, because the generic search for it wanders through the
`IntermediateField`'s adjoin-shaped `Algebra` candidates and exceeds the default
`synthInstance` budget (the pin carries a global `synthInstance.maxHeartbeats` bump for
the same reason; no option is set in this module). -/
private instance instAlgebraFb : Algebra kk Fb := SubalgebraClass.toAlgebra (qExpFunctionFieldC kk Γ)

omit [Γ.FiniteIndex] in
-- own: the pin's `hT : ModularGroup.T ∈ Γ` is unused in the port's engine; the port states the weaker `gaussRing A Γ`/`resHom A Γ` form
theorem coe_ne_zero_of_resHom_ne_zero (u : gaussRing A Γ) (hu : resHom A Γ u ≠ 0) : (u : FF) ≠ 0 := by
  intro h0
  apply hu
  have : u = 0 := Subtype.ext h0
  rw [this, map_zero]

omit [Γ.FiniteIndex] in
-- own: the pin's `hT : ModularGroup.T ∈ Γ` is unused in the port's engine; the port states the weaker `gaussRing A Γ`/`resHom A Γ` form
theorem resF_inv (u : gaussRing A Γ) (hu : resHom A Γ u ≠ 0) :
    resF A hT ⟨(u : FF)⁻¹, inv_mem_gaussRing_of_resHom_ne_zero A u hu⟩ = (resF A hT u)⁻¹ := by
  have hu0 := coe_ne_zero_of_resHom_ne_zero A u hu
  have hprod : resF A hT ⟨(u : FF)⁻¹, inv_mem_gaussRing_of_resHom_ne_zero A u hu⟩ * resF A hT u = 1 := by
    rw [← map_mul, ← map_one (resF A hT)]
    congr 1
    exact Subtype.ext (inv_mul_cancel₀ hu0)
  exact eq_inv_of_mul_eq_one_left hprod

omit [Γ.FiniteIndex] in
-- own: the pin's `hT : ModularGroup.T ∈ Γ` is unused in the port's engine; the port states the weaker `gaussRing A Γ`/`resHom A Γ`/`resF A hT` form
theorem exists_unit_of_mem_closure {D : Divisor Qb FF}
    (hD : D ∈ AddSubgroup.closure
      (laurentIntegralPrincipalDivisors A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ) Fb)) :
    ∃ u : gaussRing A Γ, resHom A Γ u ≠ 0 ∧ (∀ P, D P = P.ord ((u : FF) : FF)) ∧
      ∀ Q : Place kk Fb, Finsupp.mapDomain (placeReductionQExpModL h) D Q = Q.ord (resF A hT u : Fb) := by
  have hr := isPlaceReductionQExpModL_placeReductionQExpModL h
  induction hD using AddSubgroup.closure_induction with
  | mem D hD =>
    obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
    refine ⟨⟨⟨_, hy⟩, ι_mem_gaussRing A hy⟩, ?_, hDy, fun Q => ?_⟩
    · rw [resHom_ι A hy]; exact hne
    · rw [hr.2 y hy hyk hne D hDy Q]
      congr 1
      exact Subtype.ext (by rw [coe_resF A hT, resHom_ι A hy])
  | zero =>
    exact ⟨1, by rw [map_one]; exact one_ne_zero, fun P => by simp, fun Q => by simp⟩
  | add D E _ _ hD hE =>
    obtain ⟨u, hu, hDu, hru⟩ := hD
    obtain ⟨v, hv, hEv, hrv⟩ := hE
    have hu0 := coe_ne_zero_of_resHom_ne_zero A u hu
    have hv0 := coe_ne_zero_of_resHom_ne_zero A v hv
    have hru0 : (resF A hT u : Fb) ≠ 0 := (resF_ne_zero_iff A hT u).mpr hu
    have hrv0 : (resF A hT v : Fb) ≠ 0 := (resF_ne_zero_iff A hT v).mpr hv
    refine ⟨u * v, by rw [map_mul]; exact mul_ne_zero hu hv, fun P => ?_, fun Q => ?_⟩
    · rw [Finsupp.add_apply, hDu, hEv]
      exact (P.ord_mul hu0 hv0).symm
    · rw [Finsupp.mapDomain_add, Finsupp.add_apply, hru, hrv, map_mul]
      exact (Q.ord_mul hru0 hrv0).symm
  | neg D _ hD =>
    obtain ⟨u, hu, hDu, hru⟩ := hD
    have hru0 : (resF A hT u : Fb) ≠ 0 := (resF_ne_zero_iff A hT u).mpr hu
    refine ⟨⟨(u : FF)⁻¹, inv_mem_gaussRing_of_resHom_ne_zero A u hu⟩, ?_, fun P => ?_, fun Q => ?_⟩
    · have h : resF A hT ⟨(u : FF)⁻¹, inv_mem_gaussRing_of_resHom_ne_zero A u hu⟩ ≠ 0 := by
        rw [resF_inv hT A u hu]; exact inv_ne_zero hru0
      rwa [resF_ne_zero_iff A hT ⟨(u : FF)⁻¹, inv_mem_gaussRing_of_resHom_ne_zero A u hu⟩] at h
    · rw [Finsupp.neg_apply, hDu, ← Place.ord_inv]
    · rw [← Finsupp.mapDomain.addMonoidHom_apply, map_neg, Finsupp.mapDomain.addMonoidHom_apply,
        Finsupp.neg_apply, hru, resF_inv hT A u hu, ← Place.ord_inv]

-- own: the pin's `hT : ModularGroup.T ∈ Γ` is unused in the port's engine; the port states the weaker `gaussRing A Γ`/`resHom A Γ` form
theorem mapDomain_placeMap (f : gaussRing A Γ) (hf : resF A hT f ≠ 0) (D : Divisor Qb FF)
    (hD : ∀ P, D P = P.ord ((f : FF) : FF)) (Q : Place kk Fb) :
    Finsupp.mapDomain (placeReductionQExpModL h) D Q = Q.ord (resF A hT f : Fb) := by
  have hf' : resHom A Γ f ≠ 0 := (resF_ne_zero_iff A hT f).mp hf
  have hf0 : (f : FF) ≠ 0 := coe_ne_zero_of_resHom_ne_zero A f hf'

  have hDprin : D ∈ Divisor.principal (K := Qb) (F := FF) := ⟨(f : FF), hf0, hD⟩
  have hgen : LaurentPrincipalGeneratedByIntegral A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ) Fb :=
    h.choose_spec.2
  obtain ⟨u, hu, hDu, hru⟩ := exists_unit_of_mem_closure hT A h (hgen hDprin)
  have hu0 : (u : FF) ≠ 0 := coe_ne_zero_of_resHom_ne_zero A u hu

  have hgO : (f : FF) * (u : FF)⁻¹ ∈ gaussRing A Γ :=
    mul_mem f.2 (inv_mem_gaussRing_of_resHom_ne_zero A u hu)
  have hg_ord : ∀ P : Place Qb FF, P.ord ((f : FF) * (u : FF)⁻¹) = 0 := fun P => by
    rw [P.ord_mul hf0 (inv_ne_zero hu0), P.ord_inv, ← hD P, ← hDu P]; ring

  obtain ⟨x, hxtr, hfd⟩ :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange Qb Γ hT
  have := hfd
  obtain ⟨c, hc⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hxtr hg_ord
  have hcA : c ∈ A := (algebraMap_mem_gaussRing_iff A Γ c).mp (by rw [hc]; exact hgO)

  have hfgu : f = ⟨_, hgO⟩ * u :=
    Subtype.ext (by change (f : FF) = (f : FF) * (u : FF)⁻¹ * (u : FF); rw [inv_mul_cancel_right₀ hu0])
  have hgc : (⟨_, hgO⟩ : gaussRing A Γ) =
      ⟨algebraMap Qb FF ((⟨c, hcA⟩ : A) : Qb), (algebraMap_mem_gaussRing_iff A Γ _).mpr hcA⟩ :=
    Subtype.ext hc.symm
  have hresg : resF A hT ⟨_, hgO⟩ = algebraMap kk Fb (IsLocalRing.residue A ⟨c, hcA⟩) := by
    rw [hgc, resF_algebraMap]
  have hru0 : (resF A hT u : Fb) ≠ 0 := (resF_ne_zero_iff A hT u).mpr hu
  have hres_f : resF A hT f = algebraMap kk Fb (IsLocalRing.residue A ⟨c, hcA⟩) * resF A hT u := by
    rw [hfgu, map_mul, hresg]
  have hcbar : IsLocalRing.residue A ⟨c, hcA⟩ ≠ 0 := by
    intro h0
    apply hf
    rw [hres_f, h0, map_zero, zero_mul]
  rw [hres_f, Q.ord_mul ((_root_.map_ne_zero _).mpr hcbar) hru0,
    ConstantReduction.ord_algebraMap Q hcbar, zero_add, hru Q]

def gaussReduction : ConstantReduction A FF Fb where
  integers := gaussRing A Γ
  residue := resF A hT
  placeMap := placeReductionQExpModL h
  algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A Γ
  residue_surjective := resF_surjective A hT
  ker_residue := ker_resF A hT
  residue_algebraMap a := resF_algebraMap A hT a _
  exists_smul_mem := exists_smul_mem_resF A hT
  deg_placeMap := (isPlaceReductionQExpModL_placeReductionQExpModL h).1
  mapDomain_placeMap f hf D hD Q := mapDomain_placeMap hT A h f hf D hD Q

theorem pic0Map_gaussReduction : (gaussReduction hT A h).pic0Map = reductionQExpModL A Γ := by
  refine AddMonoidHom.ext fun z => ?_
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective z
  rw [ConstantReduction.pic0Map_mk, reductionQExpModL_mk h]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem residue_gaussReduction (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF)
    (hyk : coeffMap (IsLocalRing.residue A) y ∈ Fb) :
    ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ (gaussReduction hT A h).integers,
      (gaussReduction hT A h).residue ⟨_, hO⟩ = ⟨coeffMap (IsLocalRing.residue A) y, hyk⟩ :=
  ⟨ι_mem_gaussRing A hy, Subtype.ext (resHom_ι A hy)⟩

include hT in
theorem main :
    ∃ R : ConstantReduction A FF Fb,
      R.placeMap = placeReductionQExpModL h ∧
      R.pic0Map = reductionQExpModL A Γ ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF)
        (hyk : coeffMap (IsLocalRing.residue A) y ∈ Fb),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ R.integers,
          R.residue ⟨_, hO⟩ = ⟨coeffMap (IsLocalRing.residue A) y, hyk⟩ :=
  ⟨gaussReduction hT A h, rfl, pic0Map_gaussReduction hT A h, residue_gaussReduction hT A h⟩

end PlaceMap

end ConstantReductionQExp

/-! ## The headline — the `Theorems/` wrapper's statement, verbatim -/

open ConstantReductionQExp in
theorem exists_constantReduction_pic0Map_eq_reductionQExpModL
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (h : ModularCurve.ReductionInputsQExpModL A Γ) :
    ∃ R : ConstantReduction A
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      R.placeMap = ModularCurve.placeReductionQExpModL h ∧
      R.pic0Map = ModularCurve.reductionQExpModL A Γ ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (hyk : ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
          ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ))
              ∈ R.integers,
          R.residue ⟨_, hO⟩ = ⟨ModularCurve.coeffMap (IsLocalRing.residue A) y, hyk⟩ :=
  main hT A h

end ModularCurve

end
