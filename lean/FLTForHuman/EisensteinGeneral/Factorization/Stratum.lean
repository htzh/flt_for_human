/-
  The stratum `Stratum F T` of the finite adèles: the restricted product in which the
  coordinates outside the finite set `T` are integral, together with its homeomorphism
  onto the product `GT F T × YT F T` (the coordinates in `T`, arbitrary, times the
  integral coordinates outside `T`).

  This is the pin's `section Places` taken whole.  The mathematics: the spectrum of the
  ring of integers is countable (`countable_heightOneSpectrum`, registered as a `local
  instance` because the restricted-product and `Finset` machinery needs it), the
  integrality ball `v.adicCompletionIntegers F` is open, `incl F T` embeds the stratum
  as the open set `stratumSet F T` of the finite adèles (`isOpenEmbedding_incl`,
  `range_incl`), and `split F T` is a **homeomorphism** `Stratum F T ≃ₜ GT F T × YT F T`
  (`split`, with inverse `splitInv` built from `glue`).  Additivity of `incl` on the
  stratum and the translation identity `split_add_symm` are what make the stratum
  measure of the next module translation invariant.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`,
  `P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:95-283`
  (`section Places`), mathlib `v4.34.0`.  The pin's `private` becomes public: this is the
  engine the rest of the set imports, and the checker diffs every declaration of it
  (work order §1).  Declarations keep the pin's `variable {F} in` / `omit [...] in` /
  `open scoped Classical in` prefixes and its `@[scoped simp]` attributes; the proofs are
  transcribed unchanged.
-/
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import FLTForHuman.Topology.Algebra.RestrictedProduct.TopologicalSpace

set_option autoImplicit false

-- The pin's `haveI` declarations are load-bearing: they feed instance search.
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField

namespace EisensteinGeneral

namespace FiniteAdelicFactorization

section Places

open IsDedekindDomain.HeightOneSpectrum Filter Topology

open scoped RestrictedProduct ENNReal NNReal

variable (F : Type) [Field F] [NumberField F]

-- pin: countable_heightOneSpectrum (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:99)
theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable F := by
    have e := (Module.finBasis ℚ F).equivFun.toEquiv
    exact (Equiv.countable_iff e).mpr inferInstance
  haveI : Countable (𝓞 F) :=
    Function.Injective.countable (f := ((↑) : 𝓞 F → F)) NumberField.RingOfIntegers.coe_injective
  haveI : Countable (List (𝓞 F)) := inferInstance
  have hsurj : Function.Surjective (fun l : List (𝓞 F) => Ideal.span {x | x ∈ l}) := by
    intro I
    obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨s.toList, ?_⟩
    have hset : {x : 𝓞 F | x ∈ s.toList} = (s : Set (𝓞 F)) := Set.ext fun x => Finset.mem_toList
    show Ideal.span {x | x ∈ s.toList} = I
    rw [hset]
    exact hs
  haveI : Countable (Ideal (𝓞 F)) := hsurj.countable
  exact Function.Injective.countable (f := fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    fun v w h => HeightOneSpectrum.ext h

attribute [local instance] countable_heightOneSpectrum

-- pin: isOpen_adicCompletionIntegers (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:120)
theorem isOpen_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Valued.isOpen_valuationSubring _

-- pin: Stratum (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:124)
abbrev Stratum (T : Finset (HeightOneSpectrum (𝓞 F))) : Type :=
  Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[𝓟 ((↑T : Set _)ᶜ)]

omit [NumberField F] in
-- pin: cofinite_le (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:128)
theorem cofinite_le (T : Finset (HeightOneSpectrum (𝓞 F))) :
    cofinite ≤ 𝓟 ((↑T : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
  le_principal_iff.mpr T.finite_toSet.compl_mem_cofinite

-- pin: incl (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:132)
def incl (T : Finset (HeightOneSpectrum (𝓞 F))) : Stratum F T → FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion _ _ (cofinite_le F T)

variable {F} in
-- pin: incl_apply (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:136)
@[scoped simp] theorem incl_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T)
    (v : HeightOneSpectrum (𝓞 F)) : incl F T x v = x v := rfl

-- pin: isOpenEmbedding_incl (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:139)
theorem isOpenEmbedding_incl (T : Finset (HeightOneSpectrum (𝓞 F))) : IsOpenEmbedding (incl F T) :=
  RestrictedProduct.isOpenEmbedding_inclusion_principal (isOpen_adicCompletionIntegers F) (cofinite_le F T)

-- pin: stratumSet (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:142)
def stratumSet (T : Finset (HeightOneSpectrum (𝓞 F))) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v, v ∉ T → x v ∈ v.adicCompletionIntegers F}

-- pin: GT (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:145)
abbrev GT (T : Finset (HeightOneSpectrum (𝓞 F))) : Type := ∀ i : ↥T, (i.1).adicCompletion F

-- pin: YT (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:147)
abbrev YT (T : Finset (HeightOneSpectrum (𝓞 F))) : Type :=
  ∀ i : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}, (i.1).adicCompletionIntegers F

variable {F} in
-- pin: mem_of_not_mem (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:151)
theorem mem_of_not_mem {T : Finset (HeightOneSpectrum (𝓞 F))} (x : Stratum F T)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T) : x v ∈ v.adicCompletionIntegers F :=
  (Filter.eventually_principal.mp x.2) v (by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hv)

-- pin: range_incl (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:155)
theorem range_incl (T : Finset (HeightOneSpectrum (𝓞 F))) : Set.range (incl F T) = stratumSet F T := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ v hv
    exact mem_of_not_mem y hv
  · intro hx
    refine ⟨⟨fun v => x v, Filter.eventually_principal.mpr fun v hv => hx v ?_⟩,
      RestrictedProduct.ext _ _ fun v => rfl⟩
    simpa only [Set.mem_compl_iff, Finset.mem_coe] using hv

-- pin: isOpen_stratumSet (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:165)
theorem isOpen_stratumSet (T : Finset (HeightOneSpectrum (𝓞 F))) : IsOpen (stratumSet F T) := by
  rw [← range_incl]
  exact (isOpenEmbedding_incl F T).isOpen_range

open scoped Classical in

-- pin: glue (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:171)
def glue (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletion F :=
  if h : v ∈ T then p.1 ⟨v, h⟩ else ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F)

variable {F} in
-- pin: glue_of_mem (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:176)
theorem glue_of_mem (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T)
    {v : HeightOneSpectrum (𝓞 F)} (h : v ∈ T) : glue F T p v = p.1 ⟨v, h⟩ := by
  simp only [glue, dite_eq_left h]

variable {F} in
-- pin: glue_of_not_mem (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:181)
theorem glue_of_not_mem (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T)
    {v : HeightOneSpectrum (𝓞 F)} (h : v ∉ T) :
    glue F T p v = ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
  simp only [glue, dite_eq_right h]

-- pin: splitFun (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:186)
def splitFun (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) : GT F T × YT F T :=
  (fun i => x i.1, fun i => ⟨x i.1, mem_of_not_mem x i.2⟩)

-- pin: splitInv (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:189)
def splitInv (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) : Stratum F T :=
  ⟨glue F T p, Filter.eventually_principal.mpr fun v hv => by
    have hv' : v ∉ T := by simpa only [Set.mem_compl_iff, Finset.mem_coe] using hv
    rw [glue_of_not_mem T p hv']
    exact Subtype.coe_prop _⟩

variable {F} in
-- pin: splitInv_apply (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:195)
@[scoped simp] theorem splitInv_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T)
    (v : HeightOneSpectrum (𝓞 F)) : splitInv F T p v = glue F T p v := rfl

variable {F} in
-- pin: splitFun_fst (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:199)
@[scoped simp] theorem splitFun_fst (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) (i : ↥T) :
    (splitFun F T x).1 i = x i.1 := rfl

variable {F} in
-- pin: coe_splitFun_snd (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:203)
@[scoped simp] theorem coe_splitFun_snd (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T)
    (i : {v : HeightOneSpectrum (𝓞 F) // v ∉ T}) :
    ((splitFun F T x).2 i : (i.1).adicCompletion F) = x i.1 := rfl

variable {F} in
-- pin: splitInv_splitFun (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:209)
theorem splitInv_splitFun (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) :
    splitInv F T (splitFun F T x) = x := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  rw [splitInv_apply]
  by_cases h : v ∈ T
  · rw [glue_of_mem T _ h, splitFun_fst]
  · rw [glue_of_not_mem T _ h, coe_splitFun_snd]

variable {F} in
-- pin: splitFun_splitInv (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:218)
theorem splitFun_splitInv (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) :
    splitFun F T (splitInv F T p) = p := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => Subtype.ext ?_)
  · rw [splitFun_fst, splitInv_apply, glue_of_mem T p i.2]
  · rw [coe_splitFun_snd, splitInv_apply, glue_of_not_mem T p i.2]

-- pin: continuous_splitFun (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:224)
theorem continuous_splitFun (T : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (splitFun F T) :=
  continuous_prodMk.mpr
    ⟨continuous_pi fun i => RestrictedProduct.continuous_eval i.1,
      continuous_pi fun i => (RestrictedProduct.continuous_eval i.1).subtype_mk _⟩

-- pin: continuous_glue (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:229)
theorem continuous_glue (T : Finset (HeightOneSpectrum (𝓞 F))) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun p : GT F T × YT F T => glue F T p v := by
  by_cases h : v ∈ T
  · simp only [glue, dite_eq_left h]
    exact (continuous_apply _).comp continuous_fst
  · simp only [glue, dite_eq_right h]
    exact continuous_subtype_val.comp
      ((continuous_apply (⟨v, h⟩ : {w : HeightOneSpectrum (𝓞 F) // w ∉ T})).comp continuous_snd)

-- pin: continuous_splitInv (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:238)
theorem continuous_splitInv (T : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (splitInv F T) :=
  RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi fun v => continuous_glue F T v)

-- pin: split (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:241)
def split (T : Finset (HeightOneSpectrum (𝓞 F))) : Stratum F T ≃ₜ GT F T × YT F T where
  toFun := splitFun F T
  invFun := splitInv F T
  left_inv := splitInv_splitFun T
  right_inv := splitFun_splitInv T
  continuous_toFun := continuous_splitFun F T
  continuous_invFun := continuous_splitInv F T

variable {F} in
-- pin: split_apply (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:249)
@[scoped simp] theorem split_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (x : Stratum F T) :
    split F T x = splitFun F T x := rfl

variable {F} in
-- pin: split_symm_apply (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:253)
@[scoped simp] theorem split_symm_apply (T : Finset (HeightOneSpectrum (𝓞 F))) (p : GT F T × YT F T) :
    (split F T).symm p = splitInv F T p := rfl

variable {F} in
-- pin: incl_add (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:258)
theorem incl_add (T : Finset (HeightOneSpectrum (𝓞 F))) (x y : Stratum F T) :
    incl F T (x + y) = incl F T x + incl F T y :=
  RestrictedProduct.ext _ _ fun _ => rfl

variable {F} in
-- pin: incl_sub (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:263)
theorem incl_sub (T : Finset (HeightOneSpectrum (𝓞 F))) (x y : Stratum F T) :
    incl F T (x - y) = incl F T x - incl F T y :=
  RestrictedProduct.ext _ _ fun _ => rfl

-- pin: split_add_symm (S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean:267)
theorem split_add_symm (T : Finset (HeightOneSpectrum (𝓞 F))) (a : GT F T) (p : GT F T × YT F T) :
    split F T ((split F T).symm (a, 0) + (split F T).symm p) = (a + p.1, p.2) := by
  simp only [split_apply, split_symm_apply]
  refine Prod.ext (funext fun i => ?_) (funext fun i => Subtype.ext ?_)
  · show (splitInv F T (a, 0) + splitInv F T p) i.1 = a i + p.1 i
    rw [RestrictedProduct.add_apply, splitInv_apply, splitInv_apply, glue_of_mem T _ i.2, glue_of_mem T _ i.2]
  · show (splitInv F T (a, 0) + splitInv F T p) i.1 = (p.2 i : (i.1).adicCompletion F)
    rw [RestrictedProduct.add_apply, splitInv_apply, splitInv_apply, glue_of_not_mem T _ i.2,
      glue_of_not_mem T _ i.2]
    show ((0 : (i.1).adicCompletionIntegers F) : (i.1).adicCompletion F) + (p.2 i : (i.1).adicCompletion F)
      = (p.2 i : (i.1).adicCompletion F)
    rw [ZeroMemClass.coe_zero, zero_add]

scoped instance (T : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSpace (Stratum F T) := borel _
scoped instance (T : Finset (HeightOneSpectrum (𝓞 F))) : BorelSpace (Stratum F T) := ⟨rfl⟩

end Places

end FiniteAdelicFactorization

end EisensteinGeneral
