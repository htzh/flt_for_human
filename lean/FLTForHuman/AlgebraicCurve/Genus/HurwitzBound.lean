/-
The two Hurwitz line bounds for the different, after FLT's
`P2M/Sol/S_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean` (418 ln)
and `P2M/Sol/S_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean`
(76 ln).

* the sum of `ordDiff` over the regular places of an `x`, plus the ramification
  correction `-ord x - 1` over its poles, is at most `2g - 2 + 2[F : k(x)]`; the counting
  lemma `sum_bound` is the pin's, and the pole count runs through the `RatFunc`
  transcendence tower, whose two facts (`poleDivisor_apply`,
  `degree_poleDivisor_eq_finrank`) are re-derived locally because the shared home keeps
  them `private`;
* replacing the `ordDiff` summands of that bound by `ord (x - a) - 1` costs nothing, since
  the different is effective at every place and a translation of `x` does not change its
  differential.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean

spec-pin: Theorems/Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.Canonical.PolarDifferentials
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegular
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.Differential.Different
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly

set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero IsLocalRing Polynomial
open scoped IntermediateField

-- The `letI`/`haveI` instance walls in the place sections are load-bearing — they
-- register the `algebraAlong`/`isScalarTower_along` instances the following tactic needs —
-- so the style linter's `let`/`have` suggestion does not apply; cf. `Genus/Index.lean`.
set_option linter.style.haveILetI false

namespace AlgebraicCurve

/-! ## The Hurwitz line bound for the different

The pin's `sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable` (418 ln,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean>):
the sum of `ordDiff` over the regular places of an `x`, plus the ramification
correction `-ord x - 1` over its poles, is at most `2g - 2 + 2[F : k(x)]`.  The
counting lemma `sum_bound` is the pin's; the pole count runs through the port's
`RationalFunctionField.transcendenceTower`, whose two facts the pin proves
(`poleDivisor_apply`, `degree_poleDivisor_eq_finrank`) are re-derived locally because
`Genus/Stichtenoth.lean` keeps them `private`.  The pin's `with_ratFunc` transports the
`RatFunc` tower to `k⟮x⟯`, and its `riemannRoch_and_constantsAreBase_pkg` /
`genus_eq_genusFF_pkg` / `degree_canonical_pkg` are the port's
`riemannRoch_and_constantsAreBase`, `genus_eq_genusFF` and
`degree_canonicalDivisor_eq_of_riemannRoch`, applied in place. -/

section HurwitzLineBound

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]

/-- The `RatFunc` transport: every instance the `RatFunc`-tower formulation needs can be
transported along `RatFunc k ≃ₐ[k] k⟮x⟯`. -/
private theorem with_ratFunc (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional k⟮x⟯ F) (hsep : Algebra.IsSeparable k⟮x⟯ F) {P : Prop}
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
    exact RatFunc.algEquivOfTranscendental_X x hx
  have hn : Module.finrank (RatFunc k) F = Module.finrank k⟮x⟯ F :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl F) (by ext y; rfl)
  exact h hX hn

section Poles

variable [DecidableEq (RatFunc k)]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
  [HasPrincipalDivisors k F]

omit [DecidableEq (RatFunc k)] [FiniteDimensional (RatFunc k) F] in

private theorem poleDivisor_apply
    (T : TranscendenceTower k (RatFunc k) F) (w : Place k F) :
    T.poleDivisor w = (w.ramificationIndex (RatFunc k) : ℤ) *
      (Finsupp.single T.v 1) (w.restrict (RatFunc k)) :=
  Divisor.pullback_apply (Finsupp.single T.v 1) w

omit [DecidableEq (RatFunc k)] in
private theorem degree_poleDivisor_eq_finrank
    (T : TranscendenceTower k (RatFunc k) F) :
    Divisor.degree T.poleDivisor = (Module.finrank (RatFunc k) F : ℤ) := by
  rw [TranscendenceTower.poleDivisor, Divisor.degree_pullback, Divisor.degree_single, T.hvdeg]
  push_cast
  ring

omit [FiniteDimensional (RatFunc k) F] in

private theorem towerX_poleDivisor_apply (w : Place k F) :
    (RationalFunctionField.transcendenceTower k F).poleDivisor w =
      if w.ord (algebraMap (RatFunc k) F RatFunc.X) < 0 then
        -w.ord (algebraMap (RatFunc k) F RatFunc.X) else 0 := by
  have happ := poleDivisor_apply (RationalFunctionField.transcendenceTower k F) w
  have hres := w.ord_restrict (F := RatFunc k) (RatFunc.X : RatFunc k)
  have hv : (RationalFunctionField.transcendenceTower k F).v = RationalFunctionField.placeInfty k := rfl
  rw [hv] at happ
  by_cases hw : w.restrict (RatFunc k) = RationalFunctionField.placeInfty k
  · rw [hw, RationalFunctionField.ord_placeInfty_X, mul_neg, mul_one] at hres
    have hepos : 0 < Place.ramificationIndex (F := RatFunc k) w := w.ramificationIndex_pos
    rw [happ, hw, Finsupp.single_eq_same, mul_one, hres, neg_neg, ite_eq_left]
    rw [neg_lt_zero]
    exact_mod_cast hepos
  · have hnn := RationalFunctionField.ord_X_nonneg_of_ne_placeInfty k hw
    have h0 : 0 ≤ w.ord (algebraMap (RatFunc k) F RatFunc.X) := by
      rw [hres]; positivity
    rw [happ, Finsupp.single_eq_of_ne hw, mul_zero, ite_eq_right (not_lt.mpr h0)]

private theorem sum_poles_eq_finrank (hdeg1 : ∀ w : Place k F, w.deg = 1) :
    ∃ P : Finset (Place k F),
      (∀ w, w ∈ P ↔ w.ord (algebraMap (RatFunc k) F RatFunc.X) < 0) ∧
      ∑ w ∈ P, (-w.ord (algebraMap (RatFunc k) F RatFunc.X)) =
        (Module.finrank (RatFunc k) F : ℤ) := by
  have hD := towerX_poleDivisor_apply (k := k) (F := F)
  refine ⟨(RationalFunctionField.transcendenceTower k F).poleDivisor.support, fun w => ?_, ?_⟩
  · rw [Finsupp.mem_support_iff, hD]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => by omega⟩
    · exact ⟨fun h0 => absurd rfl h0, fun h' => absurd h' h⟩
  · rw [← degree_poleDivisor_eq_finrank (RationalFunctionField.transcendenceTower k F), Divisor.degree_eq_sum_support]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hdeg1, Nat.cast_one, mul_one, hD]
    rw [Finsupp.mem_support_iff, hD] at hw
    split_ifs at hw ⊢ with h
    · rfl
    · exact absurd rfl hw

end Poles

private theorem sum_bound {ι : Type*} [DecidableEq ι] (f m : ι → ℤ)
    (S : Finset ι) (hS : ∀ P, P ∉ S → f P = 0) (C : ℤ) (hC : ∑ P ∈ S, f P = C)
    (Poles : Finset ι) (hPoles : ∀ P, P ∈ Poles ↔ m P < 0) (n : ℤ)
    (hn : ∑ P ∈ Poles, (-m P) = n)
    (hreg : ∀ P, 0 ≤ m P → 0 ≤ f P) (hpole : ∀ P, m P - 1 ≤ f P)
    (T : Finset ι) (hT : ∀ P ∈ T, 0 ≤ m P) (Tinf : Finset ι) (hTinf : ∀ P ∈ Tinf, m P < 0) :
    ∑ P ∈ T, f P + ∑ P ∈ Tinf, (-m P - 1) ≤ C + 2 * n := by
  set U : Finset ι := S ∪ T ∪ Poles with hU
  have hSU : S ⊆ U := Finset.subset_union_left.trans Finset.subset_union_left
  have hTU : T ⊆ U := Finset.subset_union_right.trans Finset.subset_union_left
  have hPU : Poles ⊆ U \ T := by
    intro P hP
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_union_right _ hP, fun hPT => ?_⟩
    have h1 := (hPoles P).mp hP
    have h2 := hT P hPT
    omega

  have hUsum : ∑ P ∈ U, f P = C := by
    rw [← hC]; exact (Finset.sum_subset hSU fun P _ hPS => hS P hPS).symm

  have hsplit : ∑ P ∈ U \ T, f P + ∑ P ∈ T, f P = ∑ P ∈ U, f P := Finset.sum_sdiff hTU

  let g : ι → ℤ := fun P => if m P < 0 then m P - 1 else 0
  have hfg : ∀ P, g P ≤ f P := fun P => by
    show (if m P < 0 then m P - 1 else 0) ≤ f P
    split_ifs with h
    · exact hpole P
    · exact hreg P (not_lt.mp h)
  have hg1 : ∑ P ∈ U \ T, g P ≤ ∑ P ∈ U \ T, f P := Finset.sum_le_sum fun P _ => hfg P
  have hg2 : ∑ P ∈ Poles, g P = ∑ P ∈ U \ T, g P := by
    refine Finset.sum_subset hPU fun P _ hP => ?_
    show (if m P < 0 then m P - 1 else 0) = 0
    rw [ite_eq_right (fun h => hP ((hPoles P).mpr h))]
  have hg3 : ∑ P ∈ Poles, g P = ∑ P ∈ Poles, (m P - 1) :=
    Finset.sum_congr rfl fun P hP => ite_eq_left ((hPoles P).mp hP)

  have hcard : ∑ P ∈ Poles, (1 : ℤ) = Poles.card := by simp
  have hsum1 : ∑ P ∈ Poles, (m P - 1) = -n - Poles.card := by
    rw [Finset.sum_sub_distrib, hcard, ← hn, Finset.sum_neg_distrib, neg_neg]
  have hsum2 : ∑ P ∈ Poles, (-m P - 1) = n - Poles.card := by
    rw [Finset.sum_sub_distrib, hcard, hn]

  have hTP : Tinf ⊆ Poles := fun P hP => (hPoles P).mpr (hTinf P hP)
  have hinf : ∑ P ∈ Tinf, (-m P - 1) ≤ ∑ P ∈ Poles, (-m P - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hTP fun P hP _ => by
      have := (hPoles P).mp hP
      omega

  have hTle : ∑ P ∈ T, f P ≤ C + n + Poles.card := by
    have := hg1; rw [← hg2, hg3, hsum1] at this
    linarith
  linarith

/-- **The Hurwitz line bound**: the different contributes at most `2g - 2 + 2[F : k(x)]`.
Statement from
`Theorems/Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean`. -/
theorem sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (hT : ∀ P ∈ T, 0 ≤ P.ord x)
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  classical
  haveI hC : IsCurveOver k F :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable k F x hx hfin hsep
  haveI hEss : Algebra.EssFiniteType k F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hfin
  haveI hK : HasCanonicalDivisor (K := k) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI hG : ∀ v : Place k F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI hsepI : Algebra.IsSeparable k⟮x⟯ F := hsep

  have hω : KaehlerDifferential.D k F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental k x hx
  have hrr := riemannRoch_and_constantsAreBase (K := k) (F := F)
  have hSG : StichtenothGenusExists k F :=
    stichtenothGenusExists_of_isCurveOver (K := k) (F := F) hrr.2
  have wda : WeilDualityAdelic k F :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hrr.1 hSG
  have hgenus : genus k F = genusFF k F := genus_eq_genusFF hrr.1 wda hrr.2
  have hWapp : ∀ P : Place k F, canonicalDivisorOf hω P = P.ordDiff ((KaehlerDifferential.D k F x)) := fun P => by
    rw [canonicalDivisorOf_apply]
    rfl
  have hWdeg : (canonicalDivisorOf hω).degree = 2 * (genusFF k F : ℤ) - 2 := by
    rw [← hgenus]
    exact degree_canonicalDivisor_eq_of_riemannRoch hrr.1 hrr.2 hω
  have hdeg1 : ∀ P : Place k F, P.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have hS : ∀ P, P ∉ (canonicalDivisorOf hω).support → P.ordDiff ((KaehlerDifferential.D k F x)) = 0 := fun P hP => by
    rw [← hWapp]; exact Finsupp.notMem_support_iff.mp hP
  have hsumW : ∑ P ∈ (canonicalDivisorOf hω).support, P.ordDiff ((KaehlerDifferential.D k F x)) =
      2 * (genusFF k F : ℤ) - 2 := by
    rw [← hWdeg, Divisor.degree_eq_sum_support]
    exact (Finset.sum_congr rfl fun P _ => by rw [hWapp, hdeg1, Nat.cast_one, mul_one]).symm

  obtain ⟨Poles, hPoles, hn⟩ : ∃ Poles : Finset (Place k F), (∀ w, w ∈ Poles ↔ w.ord x < 0) ∧
      ∑ w ∈ Poles, (-w.ord x) = (Module.finrank k⟮x⟯ F : ℤ) := by
    refine with_ratFunc x hx hfin hsep ?_
    intro _ _ _ _ hX hnn
    have h := sum_poles_eq_finrank hdeg1
    rw [hX, hnn] at h
    exact h

  have hreg : ∀ P : Place k F, 0 ≤ P.ord x → 0 ≤ P.ordDiff ((KaehlerDifferential.D k F x)) := fun P hP => by
    rw [Place.ordDiff_def]
    exact Place.ord_diffCoeff_D_nonneg_of_perfectField x P
      (P.ord_uniformizer_alt P.exists_ord_eq_one) hP
  have hpole : ∀ P : Place k F, P.ord x - 1 ≤ P.ordDiff ((KaehlerDifferential.D k F x)) := fun P =>
    Place.ord_sub_one_le_ordDiff_D_of_perfectField x P hω
  exact sum_bound (fun P : Place k F => P.ordDiff (KaehlerDifferential.D k F x)) (fun P => P.ord x)
    (canonicalDivisorOf hω).support hS _ hsumW Poles hPoles _ hn hreg hpole T hT Tinf hTinf

end HurwitzLineBound

/-! ## The logarithmic Hurwitz line bound

The pin's `sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable` (76 ln,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean>):
replacing the `ordDiff` summands of the bound above by `ord (x - a) - 1` costs nothing, since
`Place.ord_sub_one_le_ordDiff_D_of_perfectField` bounds each summand from above and a
translation of `x` does not change its differential.  The two helpers are the pin's
`HurwitzRamificationOverLine` lemmas; the summed bound
`sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable` and the local bound are this module's own
public declarations, applied in place. -/

section HurwitzLogBound

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]

/-- A place at which `x - a` has positive order is a place where `x` is integral. -/
private theorem ord_nonneg_of_ord_sub_algebraMap_pos (P : Place k F) (x : F) (a : k)
    (h : 0 < P.ord (x - algebraMap k F a)) : 0 ≤ P.ord x := by
  have h1 : P.adicValuation (x - algebraMap k F a) ≤ 1 :=
    P.adicValuation_le_one_iff.mpr (Or.inr h.le)
  have h2 : P.adicValuation (algebraMap k F a) ≤ 1 := P.adicValuation_algebraMap_le_one a
  have h3 : P.adicValuation x ≤ 1 := by
    have hx : x = (x - algebraMap k F a) + algebraMap k F a := by ring
    rw [hx]
    exact Valuation.map_add_le _ h1 h2
  rcases P.adicValuation_le_one_iff.mp h3 with hx0 | hx0
  · simp [hx0]
  · exact hx0

/-- Translating `x` does not change its differential. -/
private theorem D_sub_algebraMap (x : F) (a : k) :
    KaehlerDifferential.D k F (x - algebraMap k F a) = KaehlerDifferential.D k F x := by
  rw [map_sub, Derivation.map_algebraMap, sub_zero]

/-- **The logarithmic Hurwitz line bound**: the sum of `ord (x - a) - 1` over the places
where `x - a` has positive order, plus the pole correction `-ord x - 1`, is at most
`2g - 2 + 2[F : k(x)]`.  Statement from
`Theorems/Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean`. -/
theorem sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (a : Place k F → k)
    (hT : ∀ P ∈ T, 0 < P.ord (x - algebraMap k F (a P)))
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, (P.ord (x - algebraMap k F (a P)) - 1) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  haveI := hfin
  haveI := hsep
  have hmain :=
    sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable k x hx hfin hsep T
      (fun P hP => ord_nonneg_of_ord_sub_algebraMap_pos P x (a P) (hT P hP)) Tinf hTinf
  have hDx : KaehlerDifferential.D k F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental k x hx
  have hloc : ∀ P ∈ T,
      P.ord (x - algebraMap k F (a P)) - 1 ≤ P.ordDiff (KaehlerDifferential.D k F x) := by
    intro P hP
    have hD : KaehlerDifferential.D k F (x - algebraMap k F (a P)) ≠ 0 := by
      rwa [D_sub_algebraMap]
    have h := Place.ord_sub_one_le_ordDiff_D_of_perfectField x P hD
    rwa [D_sub_algebraMap] at h
  have hsum :
      ∑ P ∈ T, (P.ord (x - algebraMap k F (a P)) - 1) ≤
        ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) :=
    Finset.sum_le_sum hloc
  linarith

end HurwitzLogBound

end AlgebraicCurve
