/-
  The level-`N` lattice in the finite adèles.

  `idealBound N v` is the exponent of the prime `v` in `N` (and `1` off `N`); the
  local sublevel sets `{x : v(x - t) ≤ idealBound N v}` are clopen, and their product
  is the *level-`N` ball* `idealBall N` inside the integral finite adèles
  `integralFiniteAdeles`. That ball is clopen, and `integralFiniteAdeles` is compact —
  the compactness the level subgroups of `GL₂(𝔸_K)` inherit.

  Transcribed verbatim from `Definitions/Def_NumberField_AdelicLevel.lean:10–134` and
  `:225–304` (the pin's `idealBound`/`IdealBound`/`Local`/`FiniteAdelic` sections,
  pinned `aa2d8b3`), one of the four role modules the pin node is split into
  (playbook §3.1). The pin's `Projections` section between them is the port's
  `Projections.lean`, which this module imports.
-/
import FLTForHuman.NumberTheory.AdelicHaar.Adele
import FLTForHuman.NumberTheory.AdelicLevel.Projections

set_option autoImplicit false

-- The pin's `haveI` at `isCompact_integralFiniteAdeles` feeds instance search.
set_option linter.style.haveILetI false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField RestrictedProduct
open scoped RestrictedProduct Topology

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

open scoped Classical in

def idealBound (N : Ideal R) (v : HeightOneSpectrum R) : WithZero (Multiplicative ℤ) :=
  if N = ⊥ then 0
  else WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ))

section IdealBound

variable {R}

theorem idealBound_bot (v : HeightOneSpectrum R) : idealBound R ⊥ v = 0 := ite_eq_left rfl

theorem idealBound_of_ne_bot {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N v
      = WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk N).factors : ℤ)) := by
  classical
  exact ite_eq_right hN

theorem idealBound_ne_zero {N : Ideal R} (hN : N ≠ ⊥) (v : HeightOneSpectrum R) :
    idealBound R N v ≠ 0 := by
  rw [idealBound_of_ne_bot hN]; exact WithZero.exp_ne_zero

theorem idealBound_le_one (N : Ideal R) (v : HeightOneSpectrum R) : idealBound R N v ≤ 1 := by
  by_cases hN : N = ⊥
  · rw [hN, idealBound_bot]; exact zero_le
  · rw [idealBound_of_ne_bot hN, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega

theorem idealBound_eq_one_of_not_dvd {N : Ideal R} (hN : N ≠ ⊥) {v : HeightOneSpectrum R}
    (hv : ¬ v.asIdeal ∣ N) : idealBound R N v = 1 := by
  classical
  rw [idealBound_of_ne_bot hN]
  have h0 : (Associates.mk v.asIdeal).count (Associates.mk N).factors = 0 := by
    by_contra h
    exact hv ((Associates.count_ne_zero_iff_dvd (show N ≠ 0 from hN) v.irreducible).mp h)
  rw [h0]; simp

theorem idealBound_top (v : HeightOneSpectrum R) : idealBound R (⊤ : Ideal R) v = 1 :=
  idealBound_eq_one_of_not_dvd top_ne_bot fun h =>
    v.isPrime.ne_top ((Ideal.dvd_iff_le.mp h).antisymm le_top |>.symm ▸ rfl)

theorem finite_setOf_idealBound_ne_one {N : Ideal R} (hN : N ≠ ⊥) :
    {v : HeightOneSpectrum R | idealBound R N v ≠ 1}.Finite :=
  (Ideal.finite_factors hN).subset fun _ hv => by
    by_contra h
    exact hv (idealBound_eq_one_of_not_dvd hN h)

end IdealBound

section Local

variable {R K} (v : HeightOneSpectrum R)

theorem algebraMap_mem_adicCompletionIntegers (r : R) :
    algebraMap K (v.adicCompletion K) (algebraMap R K r) ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact v.valuation_le_one r

theorem valued_algebraMap (r : R) :
    Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.intValuation r := by
  rw [show algebraMap K (v.adicCompletion K) (algebraMap R K r) =
      ((algebraMap R K r : K) : v.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

theorem setOf_valued_le_eq_preimage (t : v.adicCompletion K) (ht : t ≠ 0) :
    {y : v.adicCompletion K | Valued.v y ≤ Valued.v t}
      = (fun y => y * t⁻¹) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
  rw [mul_inv_le_iff₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr ht)), one_mul]

theorem isOpen_setOf_valued_le (t : v.adicCompletion K) (ht : t ≠ 0) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ Valued.v t} := by
  rw [setOf_valued_le_eq_preimage v t ht]
  exact (continuous_id.mul continuous_const).isOpen_preimage _ (Valued.isOpen_valuationSubring _)

theorem isClosed_adicCompletionIntegers :
    IsClosed (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  Valued.isClosed_valuationSubring _

theorem isClosed_setOf_valued_le (t : v.adicCompletion K) (ht : t ≠ 0) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ Valued.v t} := by
  rw [setOf_valued_le_eq_preimage v t ht]
  exact (isClosed_adicCompletionIntegers v).preimage (continuous_id.mul continuous_const)

theorem exists_valued_eq_exp_neg (n : ℕ) :
    ∃ t : v.adicCompletion K, t ≠ 0 ∧ Valued.v t = WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := v.intValuation_exists_uniformizer
  refine ⟨(algebraMap K (v.adicCompletion K) (algebraMap R K π)) ^ n, ?_, ?_⟩
  · refine pow_ne_zero _ fun h => ?_
    have := valued_algebraMap (K := K) v π
    rw [h, map_zero, hπ] at this
    exact WithZero.exp_ne_zero this.symm
  · rw [map_pow, valued_algebraMap, hπ]
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

theorem isOpen_setOf_valued_le_idealBound {N : Ideal R} (hN : N ≠ ⊥) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} := by
  obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := K) v
    ((Associates.mk v.asIdeal).count (Associates.mk N).factors)
  rw [idealBound_of_ne_bot hN, ← hvt]
  exact isOpen_setOf_valued_le v t ht

theorem isClosed_setOf_valued_le_idealBound (N : Ideal R) :
    IsClosed {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} := by
  by_cases hN : N = ⊥
  · have : {y : v.adicCompletion K | Valued.v y ≤ idealBound R N v} = {0} := by
      ext y; simp [hN, idealBound_bot]
    rw [this]; exact isClosed_singleton
  · obtain ⟨t, ht, hvt⟩ := exists_valued_eq_exp_neg (K := K) v
      ((Associates.mk v.asIdeal).count (Associates.mk N).factors)
    rw [idealBound_of_ne_bot hN, ← hvt]
    exact isClosed_setOf_valued_le v t ht

end Local


section FiniteAdelic

def integralFiniteAdeles : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, x v ∈ v.adicCompletionIntegers K}

def idealBall (N : Ideal R) : Set (FiniteAdeleRing R K) :=
  {x | ∀ v : HeightOneSpectrum R, Valued.v (x v) ≤ idealBound R N v}

variable {R K}

section Coe
variable (x y : FiniteAdeleRing R K) (v : HeightOneSpectrum R)
theorem coe_zero_apply : (0 : FiniteAdeleRing R K) v = 0 := rfl
theorem coe_one_apply : (1 : FiniteAdeleRing R K) v = 1 := rfl
theorem coe_add_apply : (x + y) v = x v + y v := rfl
theorem coe_mul_apply : (x * y) v = x v * y v := rfl
theorem coe_sub_apply : (x - y) v = x v - y v := rfl
theorem coe_neg_apply : (-x) v = -x v := rfl
end Coe

theorem idealBall_subset_integralFiniteAdeles (N : Ideal R) :
    idealBall R K N ⊆ integralFiniteAdeles R K := fun _ hx v =>
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ((hx v).trans (idealBound_le_one N v))

theorem zero_mem_idealBall (N : Ideal R) : (0 : FiniteAdeleRing R K) ∈ idealBall R K N :=
  fun v => by rw [coe_zero_apply, map_zero]; exact zero_le

variable (R K)

theorem isOpen_integralFiniteAdeles : IsOpen (integralFiniteAdeles R K) :=
  RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out

theorem isClosed_integralFiniteAdeles : IsClosed (integralFiniteAdeles R K) := by
  have : integralFiniteAdeles R K = ⋂ v : HeightOneSpectrum R,
      (fun x : FiniteAdeleRing R K => x v) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    ext x; simp [integralFiniteAdeles]
  rw [this]
  exact isClosed_iInter fun v => (isClosed_adicCompletionIntegers v).preimage (continuous_finAdeleEval R K v)

theorem isClosed_idealBall (N : Ideal R) : IsClosed (idealBall R K N) := by
  have : idealBall R K N = ⋂ v : HeightOneSpectrum R,
      (fun x : FiniteAdeleRing R K => x v) ⁻¹' {y | Valued.v y ≤ idealBound R N v} := by
    ext x; simp [idealBall]
  rw [this]
  exact isClosed_iInter fun v =>
    (isClosed_setOf_valued_le_idealBound v N).preimage (continuous_finAdeleEval R K v)

theorem isOpen_idealBall {N : Ideal R} (hN : N ≠ ⊥) : IsOpen (idealBall R K N) := by
  have hfin := finite_setOf_idealBound_ne_one hN
  have : idealBall R K N = integralFiniteAdeles R K ∩
      ⋂ v ∈ {v : HeightOneSpectrum R | idealBound R N v ≠ 1},
        (fun x : FiniteAdeleRing R K => x v) ⁻¹' {y | Valued.v y ≤ idealBound R N v} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    refine ⟨fun hx => ⟨idealBall_subset_integralFiniteAdeles N hx, fun v _ => hx v⟩,
      fun ⟨hint, hT⟩ v => ?_⟩
    by_cases hv : idealBound R N v = 1
    · rw [hv]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hint v)
    · exact hT v hv
  rw [this]
  exact (isOpen_integralFiniteAdeles R K).inter (hfin.isOpen_biInter fun v _ =>
    (isOpen_setOf_valued_le_idealBound v hN).preimage (continuous_finAdeleEval R K v))

variable [Module.Free ℤ R] [Module.Finite ℤ R]

theorem isCompact_integralFiniteAdeles : IsCompact (integralFiniteAdeles R K) := by
  haveI : ∀ v : HeightOneSpectrum R,
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

end FiniteAdelic

end NumberField.AdelicLevel

end
