/-
  Consumer specification for SET 3 of the `AlgebraicCurve` layer.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the set's headlines, composed with the divisor/place API across
  modules, expressed in Lean so that each is either bound or not. It is a deliverable
  measure, not a proof obligation. It is **not part of any library** (`lake build` does not
  see `spec/`); run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/AlgebraicCurveSet3Consumer.lean 2>&1 | grep -c error

  The error count is the metric; deleting any one module must make it fail.

  ZONES
  -----
    [order]    ZONE A — `Place.exists_forall_ord_eq_finset` prescribes orders at finitely
               many places, and `Place.mem_iff_ord_nonneg` turns a prescribed positive
               order into membership in each of the valuation subrings. A two-module
               composition with no hypotheses beyond the module's own.
    [norm]     ZONE B — `Place.ord_norm_eq_zero_of_forall_fiber` says a norm whose values
               are units above `v` has order zero at `v`; `Place.mem_iff_ord_nonneg` then
               puts the norm in `v`'s valuation subring.
    [dictionary] ZONE D — `Divisor.pushforward_div` composed with `exists_divisor`, and the
               integral-closure membership form of `Place.exists_integralClosureAt_of_ord_fiber_nonneg`.
    [descent]  ZONE C — `AlgebraicCurve.exists_constantFieldDescent` unpacked: the countable,
               algebraically closed field of constants `K₀` and the curve `F₀` over it with
               the transported transcendence data and the generation statement.
-/

import FLTForHuman.AlgebraicCurve.Place.OrderArithmetic
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldDescent
import FLTForHuman.AlgebraicCurve.Place.IntegralClosureAtFiber
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.PoleDivisor
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtensionRamification
import FLTForHuman.AlgebraicCurve.Defs.PushPull

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve

universe u v w x

/-! ## Zone A — `[order]` a function with prescribed orders is integral at those places -/

example {K F : Type*} [Field K] [Field F] [Algebra K F] (S : Finset (Place K F))
    (n : Place K F → ℤ) (hn : ∀ v ∈ S, 0 ≤ n v) :
    ∃ g : F, g ≠ 0 ∧ ∀ v ∈ S, v.ord g = n v ∧ g ∈ v.toValuationSubring := by
  obtain ⟨g, hg0, hg⟩ := Place.exists_forall_ord_eq_finset S n
  refine ⟨g, hg0, fun v hv => ⟨hg v hv, ?_⟩⟩
  rw [Place.mem_iff_ord_nonneg v hg0, hg v hv]
  exact hn v hv

/-! ## Zone B — `[norm]` a norm that is a unit above `v` is integral at `v` -/

example {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    [CharZero F] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) (v : Place K F)
    (h : ∀ w ∈ v.fiber F', w.ord f = 0) (hn : Algebra.norm F f ≠ 0) :
    Algebra.norm F f ∈ v.toValuationSubring := by
  rw [Place.mem_iff_ord_nonneg v hn, Place.ord_norm_eq_zero_of_forall_fiber hf v h]


/-! ## Zone C — `[descent]` the countable algebraically closed field of constants -/

example (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] :
    ∃ (K₀ : Type u) (F₀ : Type v) (_ : Field K₀) (_ : Field F₀) (_ : Algebra K₀ F₀)
      (_ : Algebra K₀ K) (_ : Algebra F₀ F) (_ : Algebra K₀ F) (_ : IsScalarTower K₀ K F)
      (_ : IsScalarTower K₀ F₀ F) (_ : IsAlgClosed K₀) (_ : Countable K₀),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ := by
  obtain ⟨K₀, F₀, iK₀, iF₀, iAlg, iKK, iFF, iKF, iT1, iT2, iC, iAlgC, iCount, iCurve, iCanon,
    htr, hgen⟩ := exists_constantFieldDescent K F hfg
  exact ⟨K₀, F₀, iK₀, iF₀, iAlg, iKK, iFF, iKF, iT1, iT2, iAlgC, iCount, htr, hgen⟩

/-! ## Zone D — `[dictionary]` the pointwise dictionary composed across modules -/

-- `Divisor.pushforward_div` composed with `HasPrincipalDivisors.exists_divisor`: the
-- pushforward of the principal divisor of `f` is the principal divisor of the norm.
example {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] [CharZero F] [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    {f : F'} (hf : f ≠ 0) (hN : Algebra.norm F f ≠ 0) :
    ∃ D : Divisor K F', (∀ w, D w = w.ord f) ∧
      ∃ E : Divisor K F, (∀ v, E v = v.ord (Algebra.norm F f)) ∧
        Divisor.pushforward F D = E := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F') f hf
  obtain ⟨E, hE, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F)
    (Algebra.norm F f) hN
  exact ⟨D, hD, E, hE, Divisor.pushforward_div hf hD hE⟩

-- `Place.exists_integralClosureAt_of_ord_fiber_nonneg` puts `f` in the integral closure as a
-- subring, not only in its subtype.
example {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] {v : Place K F} [HasPrincipalDivisors K F'] {f : F'}
    (hf : f ≠ 0) (hord : ∀ w ∈ v.fiber F', 0 ≤ w.ord f) :
    f ∈ integralClosure v.toValuationSubring F' := by
  obtain ⟨c, hc⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg hf hord
  have hc' : (c : F') = f := hc
  exact hc' ▸ c.2
