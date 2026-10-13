/-
  The `InlineSpecific` dense/valuation slice at a discrete place.

  This is the second slice of the pin's single
  `Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean` (pinned
  `aa2d8b3`): lines 26–344 and 359–429, 555–560. The uniformizer slice (pin 104,
  299–551) is the port's `AlgebraicCurve/Place/Completion.lean`, which this file
  imports; the two slices stay together in `AlgebraicCurve/Place/` because the pin
  is one node and the port's existing home for it is there (playbook §2.3, §3.1).

  Contents: the `intValuation`/`emultiplicity` comparison, the approximation lemma
  `exists_adicValued_sub_lt_of_adicValued_le_one` for `WithVal`, the density of
  `A` in the completed integers and in the completion, the residue-field
  identification `ResidueFieldEquivCompletionResidueField`, and the integral
  cofactor lemmas `eq_mul_nonZeroDivisor_inv_adicCompletionIntegers` /
  `eq_mul_pi_adicCompletionIntegers`.

  Adaptations, all in proofs, none in statements:
  * the pin's `private intValuation_eq_coe_neg_multiplicity` is mathlib `v4.34.0`'s
    `intValuation_eq_exp_neg_multiplicity`, and the pin's private
    `IsLocalRing.maximalIdeal_le` is mathlib's; neither is re-derived;
  * the pin's `Set.mem_setOf_eq`/deprecated names are updated per §7.
-/
import FLTForHuman.AlgebraicCurve.Place.Completion
import FLTForHuman.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Valuation.Discrete.RankOne

set_option autoImplicit false

-- The pin's `letI`s install the localization/valuation instances consumed by the
-- statements below; `have`/`let` do not feed instance search.
set_option linter.style.haveILetI false

noncomputable section

open IsLocalRing IsDedekindDomain.HeightOneSpectrum
open WithZero Multiplicative

namespace IsDedekindDomain.HeightOneSpectrum

section Multiplicative

open scoped WithZero

-- pin: exists_ofAdd_natCast_of_le_one (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:95)
lemma exists_ofAdd_natCast_of_le_one {x : ℤᵐ⁰} (hx : x ≠ 0) (hx' : x ≤ 1) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) = x := by
  lift x to Multiplicative ℤ using hx
  rw [← WithZero.coe_one, WithZero.coe_le_coe] at hx'
  have hle : Multiplicative.toAdd x ≤ 0 := by
    rwa [← Multiplicative.toAdd_le, toAdd_one] at hx'
  refine ⟨(-Multiplicative.toAdd x).toNat, ?_⟩
  rw [WithZero.coe_inj]
  have hk : ((-Multiplicative.toAdd x).toNat : ℤ) = -Multiplicative.toAdd x :=
    Int.toNat_of_nonneg (by omega)
  rw [hk, neg_neg, ofAdd_toAdd]

end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

-- pin: ne_zero_of_some_le_intValuation (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:118)
lemma ne_zero_of_some_le_intValuation {a : A} {m : Multiplicative ℤ} (h : m ≤ v.intValuation a)
    : a ≠ 0 := by
  rintro rfl
  simp at h

-- pin: emultiplicity_eq_of_valuation_eq_ofAdd (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:123)
lemma emultiplicity_eq_of_valuation_eq_ofAdd {a : A} {k : ℕ}
    (hv : v.intValuation a = (Multiplicative.ofAdd (-(k : ℤ)))) :
    emultiplicity v.asIdeal (Ideal.span {a}) = k := by
  classical
  have hnz : a ≠ 0 := ne_zero_of_some_le_intValuation _ (le_of_eq hv.symm)
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  simp only [intValuation_if_neg _ hnz, WithZero.exp, ofAdd_neg, WithZero.coe_inv, inv_inj,
    WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq, Nat.cast_inj] at hv
  rw [← hv, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb,
    Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot, normalize_eq]

-- pin: exists_adicValued_mul_sub_le (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:135)
lemma exists_adicValued_mul_sub_le {a b : A} {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0)
    (hle : γ ≤ v.intValuation a)
    (hle' : v.intValuation b ≤ v.intValuation a) :
    ∃ y, v.intValuation (y * a - b) ≤ γ := by
  have hγ' : γ ≤ 1 := by
    apply hle.trans
    apply intValuation_le_one
  obtain ⟨n, hn⟩ := exists_ofAdd_natCast_of_le_one hγ hγ'
  rw [← hn, ← WithZero.exp] at hle ⊢
  have hnz : a ≠ 0 := ne_zero_of_some_le_intValuation _ hle
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]

  rw [intValuation_eq_exp_neg_multiplicity _ hnz, WithZero.exp_le_exp, neg_le_neg_iff,
    Int.ofNat_le] at hle
  have hm : emultiplicity v.asIdeal (Ideal.span {a}) ≤ n :=
    le_of_eq_of_le
      (emultiplicity_eq_of_valuation_eq_ofAdd v <| intValuation_eq_exp_neg_multiplicity v hnz)
      (ENat.natCast_le_natCast.mpr hle)
  have hb : b ∈ v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) := by
    rwa [← intValuation_le_pow_iff_mem, ← intValuation_eq_exp_neg_multiplicity _ hnz]

  rw [← Ideal.irreducible_pow_sup_of_ge hnb (irreducible v) n hm] at hb

  obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.mp hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
  use y

  rwa [hy, ← hxz, sub_add_cancel_right, intValuation_le_pow_iff_mem, neg_mem_iff]

open MonoidWithZeroHom in

-- pin: exists_adicValued_sub_lt_of_adicValued_le_one (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:167)
lemma exists_adicValued_sub_lt_of_adicValued_le_one {x : (WithVal (v.valuation K))}
    (γ : ((WithZero (Multiplicative ℤ)))ˣ) (hx : Valued.v x ≤ 1) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  obtain ⟨⟨n, d, hd⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors A) x
  dsimp only at hnd

  have hnd' := congr_arg Valued.v hnd
  simp only [map_mul] at hnd'
  have hge : Valued.v ((algebraMap A (WithVal (v.valuation K))) d) ≥
      Valued.v ((algebraMap A (WithVal (v.valuation K))) n) :=
    calc Valued.v ((algebraMap A (WithVal (v.valuation K))) d)
          ≥ (valuation K v) x.ofVal *
            (valuation K v) ((algebraMap A (WithVal (v.valuation K))) d).ofVal :=
                mul_le_of_le_one_left' hx
        _ = Valued.v ((algebraMap A (WithVal (v.valuation K))) n) := hnd'
  simp only [ge_iff_le, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hge
  simp only [valuation_of_algebraMap] at hge
  have hdz : (algebraMap A (WithVal (v.valuation K)) d) ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ (fun _ ↦ id) hd

  have hv : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hdz
  let hu : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) * γ.val ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact ⟨hv, γ.ne_zero⟩
  obtain ⟨γ', hγ, hγu, hγv⟩ := WithZero.exists_ne_zero_and_lt_and_lt hu hv
  simp only [WithVal.algebraMap_right_apply, WithVal.valued_toVal, valuation_of_algebraMap] at hγv

  obtain ⟨a, hval⟩ := exists_adicValued_mul_sub_le v hγ hγv.le hge
  use a
  rw [← eq_div_iff_mul_eq hdz] at hnd
  rw [adicCompletion.valuedAdicCompletion_def, ← adicCompletion.equiv_apply, map_sub,
    adicCompletion.equiv_apply, adicCompletion.equiv_apply,
    adicCompletion.toCompletion_ofCompletion, adicCompletion.toCompletion_ofCompletion,
    ← UniformSpace.Completion.coe_sub, Valued.extensionValuation_apply_coe, hnd, sub_div' hdz,
    map_div₀]
  rw [← Valuation.pos_iff Valued.v, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hdz
  simp only [WithVal.algebraMap_right_apply,
    ← WithVal.toVal_mul, ← WithVal.toVal_sub, WithVal.valued_toVal, ← map_mul, ← map_sub] at hγu ⊢
  rw [div_lt_iff₀' hdz, valuation_of_algebraMap]
  exact lt_of_le_of_lt hval hγu

open scoped WithZero

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

-- pin: instIsRankOneDiscreteAdicCompletion (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:215)
instance : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

open Valuation.IsRankOneDiscrete in

-- pin: closureAlgebraMapIntegers_eq_integers (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:223)
theorem closureAlgebraMapIntegers_eq_integers :
    closure (algebraMap A (v.adicCompletion K)).range =
    SetLike.coe (v.adicCompletionIntegers K) := by
  apply subset_antisymm

  · apply closure_minimal _ (Valued.isClosed_valuationSubring _)
    rintro b ⟨a, rfl⟩
    exact coe_mem_adicCompletionIntegers v a

  · let f := fun (k : WithVal (v.valuation K)) => (k : v.adicCompletion K)
    suffices h : closure (f '' (f ⁻¹' (adicCompletionIntegers K v))) ⊆
        closure (algebraMap A (adicCompletion K v)).range by
      apply Set.Subset.trans _ h
      exact DenseRange.subset_closure_image_preimage_of_isOpen
        ((adicCompletion.ofCompletion_surjective K v).denseRange.comp
          UniformSpace.Completion.denseRange_coe (adicCompletion.continuous_ofCompletion K v))
        (Valued.isOpen_valuationSubring _)

    apply closure_minimal _ isClosed_closure
    rintro k ⟨x, hx, rfl⟩
    unfold f at hx
    rw [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers,
        adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply] at hx
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Valued.mem_nhds] at hU
    obtain ⟨γ, hγ⟩ := hU
    let γ' := Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt _).toMulEquiv γ
    obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicValued_le_one K v γ' hx
    use algebraMap A K a
    constructor
    · use a
      rfl
    · apply hγ
      simp only [sub_zero, Set.mem_ofPred_eq]
      rwa [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
        valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (valuedAdicCompletion_surjective K v)]

open Valuation.IsRankOneDiscrete in

-- pin: denseRange_of_integerAlgebraMap (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:262)
theorem denseRange_of_integerAlgebraMap :
    DenseRange (algebraMap A (v.adicCompletionIntegers K)) := by
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  intro x
  rw [closure_subtype]
  suffices h : Subtype.val ''
      Set.range ((algebraMap A ↥(adicCompletionIntegers K v))) =
      (algebraMap A (v.adicCompletion K)).range by
    rw [h, closureAlgebraMapIntegers_eq_integers K v]
    exact Subtype.coe_prop x
  simp only [RingHom.coe_range, ← Set.range_comp']
  rfl

open Valuation.IsRankOneDiscrete in

-- pin: exists_adicValued_sub_lt_of_adicCompletionInteger (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:277)
theorem exists_adicValued_sub_lt_of_adicCompletionInteger
    (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  have h := closureAlgebraMapIntegers_eq_integers K v
  rw [Set.ext_iff] at h
  specialize h x
  simp_rw [RingHom.coe_range, Subtype.coe_prop, iff_true, mem_closure_iff_nhds] at h
  specialize h { y | Valued.v (y  - (x : v.adicCompletion K)) < γ.val }
  have hn : {y | Valued.v (y - (x : v.adicCompletion K)) < γ.val} ∈ nhds x.val := by
    rw [Valued.mem_nhds]
    use (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv).symm γ
    have hsurj := (valuedAdicCompletion_surjective K v)
    intro y hy
    have hy' := (valueGroup₀_equiv_withZeroMulInt_strictMono vK) hy
    rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj] at hy'
    refine lt_of_lt_of_eq hy' ?_
    exact MulEquiv.apply_symm_apply (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv _
  obtain ⟨z, ⟨hz, a, ha⟩⟩ := h hn
  use a
  rw [algebraMap_adicCompletion, Function.comp_apply] at ha
  rwa [ha]

open IsLocalRing in

-- pin: algebraMap_completionIntegers (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:306)
lemma algebraMap_completionIntegers (x : A) :
    (algebraMap A (v.adicCompletionIntegers K) x) = (algebraMap A (v.adicCompletion K) x) :=
  rfl

-- pin: instLiesOverCompletionIdeal (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:310)
instance : (v.completionIdeal K).LiesOver v.asIdeal := ⟨by
    rw [Ideal.under_def]
    ext x
    simp only [Ideal.mem_comap, mem_completionIdeal_iff, algebraMap_completionIntegers,
      valuedAdicCompletion_eq_valuation, valuation_lt_one_iff_mem]⟩

open IsLocalRing in

-- pin: ResidueFieldToCompletionResidueField (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:318)
noncomputable def ResidueFieldToCompletionResidueField :
    A ⧸ v.asIdeal →+* ResidueField (v.adicCompletionIntegers K) :=
  Ideal.quotientMap _ (algebraMap _ _) <| le_of_eq Ideal.LiesOver.over

set_option backward.isDefEq.respectTransparency false in
open IsLocalRing in

-- pin: ResidueFieldEquivCompletionResidueField (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:325)
noncomputable def ResidueFieldEquivCompletionResidueField :
    A ⧸ v.asIdeal ≃+* ResidueField (v.adicCompletionIntegers K) := by
  apply RingEquiv.ofBijective (ResidueFieldToCompletionResidueField K v)
    ⟨Ideal.quotientMap_injective' <| ge_of_eq Ideal.LiesOver.over, ?_⟩
  intro z
  obtain ⟨x, hx⟩ :=
    Submodule.Quotient.mk_surjective (p := maximalIdeal ↥(adicCompletionIntegers K v)) z
  rw [← hx, Ideal.Quotient.mk_eq_mk]
  suffices ∃ a : A, (ResidueFieldToCompletionResidueField K v) a = Ideal.Quotient.mk _ x by
    obtain ⟨a, ha⟩ := this
    refine ⟨a, ha⟩
  change ∃ a, Ideal.Quotient.mk (maximalIdeal (v.adicCompletionIntegers K)) _ = _
  simp_rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_maximalIdeal, mem_nonunits_iff]

  conv =>
    pattern ¬(IsUnit _)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact exists_adicValued_sub_lt_of_adicCompletionInteger K v x 1

attribute [local instance 9999] Algebra.toModule in

-- pin: inertiaDeg_asIdeal_completionIdeal (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:345)
-- Adapted: `Ideal.inertiaDeg'` is `v4.34.0`'s `Ideal.inertiaDeg` (with the same
-- argument order reversed), and the pin's `Ideal.inertiaDeg'_algebraMap` is the
-- definition unfolded below.
theorem inertiaDeg_asIdeal_completionIdeal :
    Ideal.inertiaDeg (v.completionIdeal K) A = 1 := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (p := v.asIdeal) (q := v.completionIdeal K)]
  have f : (A ⧸ v.asIdeal) ≃ₐ[A ⧸ v.asIdeal]
      ((adicCompletionIntegers K v) ⧸ completionIdeal K v) :=
    { ResidueFieldEquivCompletionResidueField K v with
      commutes' := by intro x; rfl }
  rw [← f.toLinearEquiv.finrank_eq]
  exact Module.finrank_self _

-- pin: exists_forall_adicValued_sub_lt (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:359)
theorem exists_forall_adicValued_sub_lt {ι : Type*} (s : Finset ι)
    (e : ι → (WithZero (Multiplicative ℤ))ˣ) (valuation : ι → HeightOneSpectrum A)
    (injective : Function.Injective valuation)
    (x : (i : ι) → (valuation i).adicCompletionIntegers K) :
    ∃ a, ∀ i ∈ s, Valued.v ((algebraMap A K a) - (x i).val) < (e i).val := by
  choose f hf using fun (i : s) =>
    exists_adicValued_sub_lt_of_adicCompletionInteger K (valuation i) (x i) (e i)

  have hexists_e' : ∀ (i : ι), ∃ (e' : ℕ), (Multiplicative.ofAdd (-(e' : ℤ))) < (e i).val := by
    intro i
    apply exists_ofAdd_natCast_lt (e i).ne_zero
  choose e' he' using hexists_e'
  have hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (fun i ↦ (valuation i).asIdeal) i ≠ (fun i ↦ (valuation i).asIdeal) j := by
    intro _ _ _ _
    exact mt <| fun hij ↦ injective (HeightOneSpectrum.ext hij)

  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun i => (valuation i).asIdeal) e' (fun i hi => (valuation i).prime) hinj f
  use a
  intro i hi
  specialize ha i hi
  specialize hf ⟨i, hi⟩
  rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := K),
    ← valuedAdicCompletion_eq_valuation, algebraMap.coe_sub] at ha
  refine lt_of_le_of_lt ?_ (Valuation.map_add_lt _ (ha.trans_lt (he' i)) hf)
  apply le_of_eq
  congr
  rw [add_sub, sub_eq_sub_iff_add_eq_add, add_right_cancel_iff,
    add_comm_sub, add_sub, eq_sub_iff_add_eq]
  rfl

-- pin: adicCompletion.eq_mul_nonZeroDivisor_inv_adicCompletionIntegers (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:392)
lemma adicCompletion.eq_mul_nonZeroDivisor_inv_adicCompletionIntegers (v : HeightOneSpectrum A)
    (x : v.adicCompletion K) :
    ∃a ∈ nonZeroDivisors A, ∃b ∈ v.adicCompletionIntegers K, x = (algebraMap A K a)⁻¹ • b := by
  obtain ⟨a, hz, ha⟩ :=
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  use a, hz, (algebraMap A K a) • x
  constructor
  · rwa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_comm]
  · rw [smul_smul, inv_mul_cancel₀, one_smul]
    exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K (fun _ ↦ id) hz

-- pin: adicCompletion.eq_mul_pi_adicCompletionIntegers (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:403)
lemma adicCompletion.eq_mul_pi_adicCompletionIntegers {ι : Type*} [Finite ι]
    (valuation : ι → HeightOneSpectrum A) (x : (i : ι) → (valuation i).adicCompletion K) :
      ∃k : K, ∃y ∈ Set.pi Set.univ (fun (i : ι) ↦ ((valuation i).adicCompletionIntegers K).carrier),
      x = k • y := by
  classical
  let := Fintype.ofFinite ι
  choose f hf using fun (i : ι) =>
    eq_mul_nonZeroDivisor_inv_adicCompletionIntegers K (valuation i) (x i)
  use (algebraMap A K (∏ i : ι, f i))⁻¹, (algebraMap A K (∏ i : ι, f i)) • x
  have hz : ∀ (i : ι), (algebraMap A K) (f i) ≠ 0 := fun i =>
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K (fun _ ↦ id) (hf i).left
  constructor
  · rintro i -
    obtain ⟨b, hb, hx⟩ := (hf i).right
    beta_reduce
    rw [Pi.smul_apply, algebraMap_smul, Subsemiring.coe_carrier_toSubmonoid,
        Subring.coe_toSubsemiring, SetLike.mem_coe, ValuationSubring.mem_toSubring, hx,
        ← Finset.prod_erase_mul _ f (Finset.mem_univ i), mul_smul,
        ← IsScalarTower.smul_assoc (f i), Algebra.smul_def (f i), mul_inv_cancel₀ (hz i), one_smul,
        Algebra.smul_def]
    apply mul_mem (coe_mem_adicCompletionIntegers _ _) hb
  · rw [smul_smul, inv_mul_cancel₀, one_smul]
    simp [Finset.prod_ne_zero_iff, hz]

-- pin: mem_completionIdeal_iff' (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:555)
lemma mem_completionIdeal_iff' (x : v.adicCompletionIntegers K) :
    x ∈ v.completionIdeal K ↔ Valued.v x.val ≤ ↑(Multiplicative.ofAdd (-(1 : ℤ))) := by
  rw [← Submodule.pow_one (v.completionIdeal K), adicCompletion.mem_completionIdeal_pow,
    Int.natCast_one]

-- pin: completionIdeal_ne_bot (Def_DedekindDomain_AdicValuation_InlineSpecific.lean:560)
lemma completionIdeal_ne_bot : completionIdeal K v ≠ ⊥ := IsDiscreteValuationRing.not_a_field _

end IsDedekindDomain.HeightOneSpectrum

end
