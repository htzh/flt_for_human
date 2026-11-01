/-
**Weil reciprocity for a function field over an algebraically closed field.**  After FLT's
`S_AlgebraicCurve_weilReciprocity.lean` (100 ln) and its wrapper
`Theorems/Thm_AlgebraicCurve_weilReciprocity.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_weilReciprocity.lean>).

`WeilReciprocity K F` (`Defs/PlaceEvaluation.lean`) is the divisor-theoretic reciprocity
`evalFun f Dg = evalFun g Df` for two functions with disjoint-support divisors.  The ℙ¹ case is
`RationalFunctionField.weilReciprocity` (`P1/Dictionary.lean`); this module states the law for
**every** `F` that is finite over `RatFunc K` with principal divisors, at the pin wrapper's binders
(`[IsAlgClosed K] [CharZero K]`, the `RatFunc K`-algebra tower, `[HasPrincipalDivisors K F]`).

Two steps, the pin's:

* `g` is a constant: then `Dg = 0`, and the right-hand side collapses to `c ^ ∑ Df`; the exponent
  is `degree Df = 0` because every place of `Df`'s support is rational (`Place.isRational_of_isAlgClosed`,
  `Place/DegreeOne.lean`);
* otherwise a `K`-algebra map `RatFunc K →ₐ[K] F` with `X ↦ g` exists
  (`FunctionField.exists_ratFuncAlgHom_apply_X_eq`), `F` is finite and separable over `RatFunc K`
  under it, and `weilReciprocity_algebraMap` (`Place/EvalAtNorm.lean`) transports the ℙ¹ capstone
  along that extension.

The two anchors the proof needs (`finsupp_prod_zpow_const`, `degree_eq_sum_of_rational`) are the
pin's `WeilReciprocityAnchor` block; they are private here, at the pin's statements.

spec-pin: Theorems/Thm_AlgebraicCurve_weilReciprocity.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_weilReciprocity.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Place.DegreeOne
import FLTForHuman.AlgebraicCurve.Place.EvalAtNorm
import FLTForHuman.AlgebraicCurve.FunctionField

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

namespace AlgebraicCurve

namespace WeilReciprocityAnchor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem finsupp_prod_zpow_const {c : K} (hc : c ≠ 0) (D : Divisor K F) :
    (D.prod fun _ n => c ^ n) = c ^ (D.sum fun _ n => n) := by
  classical
  unfold Finsupp.prod Finsupp.sum
  induction D.support using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

private theorem degree_eq_sum_of_rational (D : Divisor K F)
    (hrat : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v hv => ?_
  rw [AddMonoidHom.mulRight_apply, (Place.isRational_iff_deg_eq_one v).1 (hrat v hv),
    Nat.cast_one, mul_one]

end WeilReciprocityAnchor

open WeilReciprocityAnchor in
/-- **Weil reciprocity**, general form: statement from
`Theorems/Thm_AlgebraicCurve_weilReciprocity.lean`, proof from the pin's `solution` — the
constant case reads `∑ Df = degree Df = 0` off the rationality of `Df`'s support, and the general
case descends from `RationalFunctionField.weilReciprocity` through
`weilReciprocity_algebraMap`, with `F` re-read as a finite separable `RatFunc K`-extension under
the map `X ↦ g`. -/
theorem weilReciprocity (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [HasPrincipalDivisors K F] :
    WeilReciprocity K F := by
  classical
  intro f g Df Dg hf hg hDf hDg hdisj hratf hratg
  by_cases hconst : g ∈ Set.range (algebraMap K F)
  ·
    obtain ⟨c, rfl⟩ := hconst
    have hc : c ≠ 0 := fun h => hg (by rw [h, map_zero])
    have hDg0 : Dg = 0 := by
      ext v
      rw [hDg v, Place.ord_algebraMap, Finsupp.coe_zero, Pi.zero_apply]

    obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
    have hDfD' : Df = D' := by
      ext v; rw [hDf v, hD' v]
    have hsum : (Df.sum fun _ n => n) = 0 := by
      rw [← degree_eq_sum_of_rational Df hratf, hDfD', hdeg]
    rw [hDg0, Divisor.evalFun_zero, Divisor.evalFun_def]
    rw [show (∏ v ∈ Df.support, Place.evalAt v (algebraMap K F c) ^ Df v)
        = Df.prod fun _ n => c ^ n from
      Finset.prod_congr rfl fun v _ => by rw [Place.evalAt_algebraMap]]
    rw [finsupp_prod_zpow_const hc, hsum, zpow_zero]
  ·
    obtain ⟨φ, hφ⟩ := FunctionField.exists_ratFuncAlgHom_apply_X_eq hconst

    have finφ : @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule :=
      FunctionField.finite_of_ratFuncAlgHom φ

    let algφ : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
    have stφ : @IsScalarTower K (RatFunc K) F _ algφ.toSMul _ :=
      @IsScalarTower.of_algebraMap_eq K (RatFunc K) F _ _ _ _ algφ _ fun x => (φ.commutes x).symm
    haveI : CharZero (RatFunc K) :=
      charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
    have algc : @Algebra.IsAlgebraic (RatFunc K) F _ _ algφ :=
      @Algebra.IsAlgebraic.of_finite (RatFunc K) F _ _ _ algφ finφ
    have sepφ : @Algebra.IsSeparable (RatFunc K) F _ _ algφ :=
      @Algebra.IsAlgebraic.isSeparable_of_perfectField (RatFunc K) F _ _ algφ algc _
    haveI : HasPrincipalDivisors K (RatFunc K) :=
      RationalFunctionField.hasPrincipalDivisors K
    have hXg : @algebraMap (RatFunc K) F _ _ algφ RatFunc.X = g := hφ
    have hratF : ∀ v : Place K (RatFunc K), v.IsRational := fun v =>
      (Place.isRational_iff_deg_eq_one v).2 (RationalFunctionField.deg_eq_one_of_isAlgClosed K v)
    have hratAll : ∀ w : Place K F, w.IsRational := fun w =>
      @Place.isRational_of_isAlgClosed K F _ _ _ _ algφ stφ finφ w
    have key := @weilReciprocity_algebraMap K (RatFunc K) F _ _ _ _ _ algφ stφ finφ sepφ
      _ _ _ (RationalFunctionField.weilReciprocity K) f RatFunc.X hf RatFunc.X_ne_zero
      Df Dg hDf (fun w => by rw [hDg w, ← hXg]) (fun w => by rw [← hXg] at hdisj; exact hdisj w)
      hratf hratF (fun v _ w _ => hratAll w)
    rw [hXg] at key
    exact key

end AlgebraicCurve

end
