/-
  Mathlib supplement: `Valued.WithZeroMulInt`, the valuation of the completed
  integer ring at a discrete valuation.

  Backported from the pin's `Definitions/Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean`
  (pinned `aa2d8b3`), which mirrors the mathlib path
  `Mathlib/Topology/Algebra/Valued/WithZeroMulInt.lean`; it therefore lives at that
  path under `FLTForHuman/`. These are the local compactness inputs for the adic
  completion of a number field: an irreducible element has valuation `< 1`, the
  maximal ideal's powers are bounded by its valuation, the quotient by `𝓂 ^ n` is
  finite when the residue field is, and the integer ring is compact and totally
  bounded.

  `v4.34.0` carries `finite_quotient_maximalIdeal_pow_of_finite_residueField` only as
  the deprecated `Valued.integer` alias
  `IsLocalRing.instFiniteQuotientIdealHPowNatMaximalIdealOfIsNoetherianRingOfResidueField`,
  so the pin's name is kept and its body delegated.
-/
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import FLTForHuman.RingTheory.Ideal.Quotient.Basic

set_option autoImplicit false

-- The pin's `letI` installs the `NeZero`-style hypothesis consumed by `le_ofAdd_iff`.
set_option linter.style.haveILetI false

section

open Multiplicative WithZero

open scoped Topology

namespace Valued.WithZeroMulInt

variable {K : Type*} [Field K] [hv : Valued K ℤᵐ⁰]

-- pin: irreducible_valuation_lt_one (Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean:14)
theorem irreducible_valuation_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : v ϖ.1 < 1 := by
  have := mt (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 h.not_isUnit
  exact lt_of_le_of_ne (Valuation.mem_integer_iff _ _ |>.1 ϖ.2) this

-- pin: irreducible_valuation_le_ofAdd_neg_one (Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean:18)
theorem irreducible_valuation_le_ofAdd_neg_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v ϖ.1 ≤ ofAdd (-1 : ℤ) := by
  letI := (lt_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])).1 (irreducible_valuation_lt_one h)
  rw [le_ofAdd_iff (show v ϖ.1 ≠ 0 by simp [h.ne_zero])]
  omega

-- pin: mem_maximalIdeal_pow_valuation (Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean:24)
theorem mem_maximalIdeal_pow_valuation [IsDiscreteValuationRing 𝒪[K]]
    {x : 𝒪[K]} {n : ℕ} (hx : x ∈ 𝓂[K] ^ n) {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    v x.val ≤ v ϖ.1 ^ n := by
  by_cases hx₀ : x = 0
  · simp [hx₀]
  · simp_rw [h.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    let ⟨y, hy⟩ := hx
    simp only [hy, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow, ge_iff_le]
    exact le_trans (mul_le_of_le_one_right' <| (Valuation.mem_integer_iff _ _).1 y.2) le_rfl

-- pin: finite_quotient_maximalIdeal_pow_of_finite_residueField (Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean:34)
lemma finite_quotient_maximalIdeal_pow_of_finite_residueField {K Γ₀ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsDiscreteValuationRing 𝒪[K]]
    (h : Finite 𝓀[K]) (n : ℕ) :
    Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (↥𝒪[K] ⧸ ⊤)
  | succ n ih =>
    have : 𝓂[K] ^ (n + 1) ≤ 𝓂[K] ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE this).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))) (𝓂[K] ^ n)) from
      Finite.of_ideal_quotient
        (I := Ideal.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

-- pin: finite_cover_of_uniformity_basis (Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean:53)
theorem finite_cover_of_uniformity_basis [IsDiscreteValuationRing 𝒪[K]] (γ : ℤᵐ⁰ˣ)
    (h : Finite 𝓀[K]) :
    ∃ t : Set K, Set.Finite t ∧
      (𝒪[K]).carrier ⊆ ⋃ y ∈ t, { x | (x, y) ∈ { p | v (p.2 - p.1) < γ.val } } := by
  classical
  let ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let ⟨m, hm⟩ := exists_pow_lt_of_le_exp_neg_one (irreducible_valuation_le_ofAdd_neg_one hϖ) γ
  letI := finite_quotient_maximalIdeal_pow_of_finite_residueField h m
  have h := Fintype.ofFinite (𝒪[K] ⧸ 𝓂[K] ^ m)
  let T := Subtype.val '' (h.elems.image Quotient.out : Set 𝒪[K])
  refine ⟨T, (Set.Finite.image _ (Finset.finite_toSet _)), fun x hx => ?_⟩
  simp only [Set.mem_iUnion]
  let y := (Ideal.Quotient.mk (𝓂[K] ^ m) ⟨x, hx⟩).out
  refine ⟨y, Set.mem_image_of_mem _ <| Finset.mem_image_of_mem Quotient.out (h.complete _),
    lt_of_le_of_lt (mem_maximalIdeal_pow_valuation (Ideal.Quotient.out_sub _ _) hϖ) hm⟩

variable (K)

open Valuation.IsRankOneDiscrete in

-- pin: integer_compactSpace (Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean:73)
theorem integer_compactSpace [CompleteSpace K] [IsDiscreteValuationRing 𝒪[K]]
    [hv.v.IsRankOneDiscrete] (h : Finite 𝓀[K]) (hsurj : Function.Surjective hv.v) :
    CompactSpace 𝒪[K] where
  isCompact_univ := by
    refine isCompact_iff_isCompact_univ.1 <| isCompact_iff_totallyBounded_isComplete.2
      ⟨(hasBasis_uniformity _ _).totallyBounded_iff.2 fun γ _ ↦ ?_, (isClosed_integer K).isComplete⟩
    obtain ⟨t, htf, ht⟩ := finite_cover_of_uniformity_basis
      (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt v).toMulEquiv γ) h
    refine ⟨t, htf, ht.trans fun x hx ↦ ?_⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hit, hi⟩ := hx
    use i, hit
    rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
      valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj]
    simpa using hi

end Valued.WithZeroMulInt

end
