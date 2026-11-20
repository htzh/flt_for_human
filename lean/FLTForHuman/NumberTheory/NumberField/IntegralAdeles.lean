/-
The integral and compact structure of the adele ring.

Four rows: the adic completeness of the local integer ring, a global denominator for a
compact set of finite adèles, the compactness of `𝔸_F ⧸ F`, and the discreteness of the
principal idèles (an open set meeting them only at `1`).

  spec-pin: P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers.lean
  spec-pin: P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact.lean
  spec-pin: P2M/Sol/S_NumberField_AdeleRing_compactSpace_quotient_principalSubgroup.lean
  spec-pin: P2M/Sol/S_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton.lean

  ## Port deltas

  None: the scaffold's four imports carry every premise. The pins' search-stage
  namespaces are renamed to the module's subject namespaces (`M4aP3B.Rows.CompactDenominator`
  → `IsDedekindDomain.FiniteAdeleRing`, `NumberField.FujisakiVocab` → `NumberField.AdeleRing`);
  every declaration keeps the pin's last name, statement and visibility.

  ## Heartbeat probe

  Probe pair (`lake env lean -DautoImplicit=false -DmaxHeartbeats=<n>` on this module):
  **silent at 20 000, fails at 10 000** — at 10 000 the first abort is
  `(deterministic) timeout at whnf` in C1's `isAdicComplete_adicCompletionIntegers`
  (lines 143–146, the `Valuation.map_add_eq_of_lt_left` step), so the natural cost lies
  between 10 k and 20 k. The module is silent at the playbook cap 200 000 (a 10× margin).
  No in-file `set_option maxHeartbeats` is installed.
-/
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.NumberField.IdeleClass.Vocab
import FLTForHuman.NumberTheory.AdelicHaar.Adele

set_option autoImplicit false

noncomputable section

universe u v

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ENNReal BigOperators

namespace IsDedekindDomain.HeightOneSpectrum

theorem isAdicComplete_adicCompletionIntegers
    {R : Type u} [CommRing R] [IsDedekindDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K)
  := by
  classical
  have hv : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers
      (v.adicCompletionIntegers K) := Valuation.valuationSubring.integers _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hball : ∀ n : ℕ, ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
      Ideal (v.adicCompletionIntegers K)) :
      Set (v.adicCompletionIntegers K)) =
      {y : v.adicCompletionIntegers K |
        Valued.v (y : v.adicCompletion K) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n} :=
    fun n => hv.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow hϖ n
  have hmem : ∀ (n : ℕ) (y : v.adicCompletionIntegers K),
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (y : v.adicCompletion K) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n := fun n y => by
    rw [← SetLike.mem_coe, hball n]; rfl
  have hsmod : ∀ (n : ℕ) (x y : v.adicCompletionIntegers K),
      x ≡ y [SMOD (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n •
        ⊤ : Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K))] ↔
        Valued.v ((x : v.adicCompletion K) - y) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem]
    rfl
  have hvϖ0 : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro h; apply hϖ.ne_zero; exact Subtype.ext h
  have hvϖ1 : Valued.v (ϖ : v.adicCompletion K) < 1 := hv.valuation_irreducible_lt_one hϖ

  have hsmall : ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 →
      ∃ n : ℕ, Valued.v (ϖ : v.adicCompletion K) ^ n < γ := by
    intro γ hγ
    set t := Valued.v (ϖ : v.adicCompletion K) with ht
    have hlt : WithZero.log t < 0 := by
      rw [← WithZero.exp_lt_exp (G := ℤ) (a := WithZero.log t), WithZero.exp_log hvϖ0,
        WithZero.exp_zero]
      exact hvϖ1
    refine ⟨(WithZero.log γ).natAbs + 1, ?_⟩
    rw [← WithZero.exp_log hvϖ0, ← WithZero.exp_nsmul]
    conv_rhs => rw [← WithZero.exp_log hγ]
    rw [WithZero.exp_lt_exp]
    have hle := Int.le_natAbs (a := -WithZero.log γ)
    rw [Int.natAbs_neg] at hle
    rw [nsmul_eq_mul]
    have h1 : (((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) * WithZero.log t ≤
        (((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) * (-1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by positivity)
    push_cast at h1 hle ⊢
    linarith
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  · apply Subtype.ext
    show (x : v.adicCompletion K) = 0
    rw [← (Valued.v : Valuation (v.adicCompletion K)
      (WithZero (Multiplicative ℤ))).zero_iff]
    by_contra h0
    obtain ⟨n, hn⟩ := hsmall _ h0
    have := (hsmod n x 0).1 (hx n)
    rw [ZeroMemClass.coe_zero, sub_zero] at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)
  · let g : ℕ → v.adicCompletion K := fun n => (f n : v.adicCompletion K)
    have hfg : ∀ {m n : ℕ}, m ≤ n →
        Valued.v (g m - g n) ≤ Valued.v (ϖ : v.adicCompletion K) ^ m :=
      fun {m n} hmn => (hsmod m (f m) (f n)).1 (hf hmn)
    have hcauchy : CauchySeq g := by
      rw [(Valued.hasBasis_uniformity (v.adicCompletion K)
        (WithZero (Multiplicative ℤ))).cauchySeq_iff]
      intro γ _
      obtain ⟨N, hN⟩ := hsmall (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by
        intro h0
        exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
          (h0.trans (map_zero _).symm)))
      refine ⟨N, fun m hm n hn => ?_⟩
      show Valued.v.restrict (g n - g m) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding, Valuation.map_sub_swap]
      calc Valued.v (g m - g n) = Valued.v (g m - g N + (g N - g n)) := by
            rw [sub_add_sub_cancel]
        _ ≤ max (Valued.v (g m - g N)) (Valued.v (g N - g n)) := Valuation.map_add _ _ _
        _ ≤ Valued.v (ϖ : v.adicCompletion K) ^ N := by
            refine max_le ?_ (hfg hn)
            rw [Valuation.map_sub_swap]; exact hfg hm
        _ < _ := hN
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy

    have hclosed : ∀ (c : WithZero (Multiplicative ℤ)) (a : v.adicCompletion K),
        IsClosed {y : v.adicCompletion K | Valued.v (a - y) ≤ c} := by
      intro c a
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hy
      rw [Valued.mem_nhds]
      have hy0 : Valued.v (a - y) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hy)
      refine ⟨Units.mk0 (Valued.v.restrict (a - y))
        (fun h => hy0 ((Valuation.restrict_eq_zero_iff Valued.v).1 h)), fun z hz => ?_⟩
      simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
      have : Valued.v (a - z) = Valued.v (a - y) := by
        have h := Valuation.map_add_eq_of_lt_left Valued.v (x := a - y) (y := -(z - y))
          (by rwa [Valuation.map_neg])
        rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at h
      rwa [this]
    have hLmem : ∀ n : ℕ, Valued.v (g n - L) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n := by
      intro n
      have hev : ∀ᶠ m in Filter.atTop,
          g m ∈ {y : v.adicCompletion K |
            Valued.v (g n - y) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n} :=
        Filter.eventually_atTop.2 ⟨n, fun m hm => hfg hm⟩
      exact (hclosed _ (g n)).mem_of_tendsto hL hev
    have hL1 : Valued.v L ≤ 1 := by
      have h0 := hLmem 0
      rw [pow_zero] at h0
      calc Valued.v L = Valued.v (g 0 - (g 0 - L)) := by rw [sub_sub_cancel]
        _ ≤ max (Valued.v (g 0)) (Valued.v (g 0 - L)) := Valuation.map_sub _ _ _
        _ ≤ 1 := max_le (f 0).2 h0
    refine ⟨⟨L, hL1⟩, fun n => ?_⟩
    rw [hsmod]
    exact hLmem n

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.FiniteAdeleRing

section CompactDenominator

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact_impl
    {C : Set (FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ s : R, s ≠ 0 ∧ ∀ y ∈ C, ∀ v : HeightOneSpectrum R,
      (algebraMap R (FiniteAdeleRing R K) s * y) v ∈ v.adicCompletionIntegers K := by
  classical
  let U : R → Set (FiniteAdeleRing R K) := fun s =>
    {y | algebraMap R (FiniteAdeleRing R K) s * y ∈ integralFiniteAdeles R K}
  have hopen : ∀ s ∈ {s : R | s ≠ 0}, IsOpen (U s) := fun s _ =>
    (AdelicLevel.isOpen_integralFiniteAdeles R K).preimage (continuous_const_mul _)
  have hcover : C ⊆ ⋃ s ∈ {s : R | s ≠ 0}, U s := fun y _ => by
    obtain ⟨s, hs0, hs⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles R K y
    exact Set.mem_biUnion hs0 hs
  obtain ⟨T, hTsub, hTfin, hCT⟩ := hC.elim_finite_subcover_image hopen hcover
  refine ⟨∏ s ∈ hTfin.toFinset, s,
    Finset.prod_ne_zero_iff.mpr fun s hs => hTsub (hTfin.mem_toFinset.mp hs), fun y hy v => ?_⟩
  obtain ⟨s, hsT, hys⟩ := Set.mem_iUnion₂.mp (hCT hy)
  rw [← Finset.prod_erase_mul _ _ (hTfin.mem_toFinset.mpr hsT), map_mul, mul_assoc,
    NumberField.AdelicBox.algebraMap_mul_apply]
  exact mul_mem (AdelicLevel.algebraMap_mem_adicCompletionIntegers v _) (hys v)

theorem gate_empty : ∃ s : R, s ≠ 0 ∧ ∀ y ∈ (∅ : Set (FiniteAdeleRing R K)), ∀ v : HeightOneSpectrum R,
      (algebraMap R (FiniteAdeleRing R K) s * y) v ∈ v.adicCompletionIntegers K :=
  ⟨1, one_ne_zero, fun _ h => h.elim⟩

end CompactDenominator

theorem exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Set (IsDedekindDomain.FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ s : R, s ≠ 0 ∧ ∀ y ∈ C, ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      (algebraMap R (IsDedekindDomain.FiniteAdeleRing R K) s * y) v
        ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v
  := by
  exact exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact_impl R K hC

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

theorem compactSpace_quotient_principalSubgroup
    (F : Type) [Field F] [NumberField F] :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F)
  := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  rw [← isCompact_univ_iff]

  have hcont : Continuous
      (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) :=
    continuous_quot_mk
  have hsurj : (QuotientAddGroup.mk (s := AdeleRing.principalSubgroup (𝓞 F) F)) '' C
      = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y

    obtain ⟨x, rfl⟩ := Quot.exists_rep y
    obtain ⟨k, hk, -⟩ := existsUnique_algebraMap_add_mem_adelicBox F x
    refine ⟨algebraMap F (AdeleRing (𝓞 F) F) k + x, hsub hk, ?_⟩

    refine (QuotientAddGroup.eq (s := AdeleRing.principalSubgroup (𝓞 F) F)).mpr ?_
    refine ⟨-k, ?_⟩
    simp only [map_neg]
    abel
  rw [← hsurj]
  exact hC.image hcont

end NumberField.AdeleRing

namespace NumberField.AdeleRing

section PrincipalIdelesDiscrete

variable (F : Type) [Field F] [NumberField F]

theorem continuous_infiniteAdeleNorm :
    Continuous (fun y : InfiniteAdeleRing F => ‖y‖) := by
  simp only [InfiniteAdeleRing.norm_def]
  exact continuous_finsetProd _ fun w _ =>
    (continuous_apply w).norm.pow _

theorem isOpen_finiteIntegralAdeles :
    IsOpen {b : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F} :=
  AdelicLevel.isOpen_integralFiniteAdeles (𝓞 F) F

def adelicZeroNbhd : Set (AdeleRing (𝓞 F) F) :=
  {a | ‖a.1‖ < 1} ∩
    Prod.snd ⁻¹' {b : FiniteAdeleRing (𝓞 F) F |
      ∀ v : HeightOneSpectrum (𝓞 F), b v ∈ v.adicCompletionIntegers F}

theorem isOpen_adelicZeroNbhd : IsOpen (adelicZeroNbhd F) := by
  refine IsOpen.inter ?_ ?_
  · exact isOpen_lt ((continuous_infiniteAdeleNorm F).comp continuous_fst) continuous_const
  · exact IsOpen.preimage continuous_snd (isOpen_finiteIntegralAdeles F)

theorem zero_mem_adelicZeroNbhd : (0 : AdeleRing (𝓞 F) F) ∈ adelicZeroNbhd F := by
  refine ⟨?_, fun v => ?_⟩
  · show ‖(0 : InfiniteAdeleRing F)‖ < 1
    rw [InfiniteAdeleRing.norm_eq_zero_of_not_isUnit not_isUnit_zero]
    exact zero_lt_one
  · show (0 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
    exact zero_mem _

theorem adelicZeroNbhd_inter_principal :
    adelicZeroNbhd F ∩ (algebraMap F (AdeleRing (𝓞 F) F)).range = {0} := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨harch, hfin⟩, x, rfl⟩
    simp only [Set.mem_ofPred_eq] at harch hfin
    have hxint : x ∈ (algebraMap (𝓞 F) F).range := by
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_
      have hv := hfin v
      rw [AdeleRing.algebraMap_snd_apply] at hv
      rwa [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x,
        ← HeightOneSpectrum.mem_adicCompletionIntegers]
    obtain ⟨r, rfl⟩ := hxint
    have harch' : ‖algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F r)‖ < 1 := harch
    rw [InfiniteAdeleRing.coe_norm_eq_abs_norm, ← Algebra.coe_norm_int] at harch'
    have hN : |Algebra.norm ℤ r| < 1 := by exact_mod_cast harch'
    simp [Algebra.norm_eq_zero_iff.mp (Int.abs_lt_one_iff.mp hN)]
  · rintro rfl
    exact ⟨zero_mem_adelicZeroNbhd F, 0, map_zero _⟩

end PrincipalIdelesDiscrete

theorem exists_isOpen_inter_principalIdeles_eq_singleton
    (F : Type) [Field F] [NumberField F] :
    ∃ V : Set (AdeleRing (𝓞 F) F)ˣ, IsOpen V ∧
      V ∩ (M4aHerbrand.principalIdeles (𝓞 F) F : Set (AdeleRing (𝓞 F) F)ˣ) = {1}
  := by
  set W : Set (AdeleRing (𝓞 F) F) := (· - 1) ⁻¹' adelicZeroNbhd F with hWdef
  have hWopen : IsOpen W :=
    IsOpen.preimage (continuous_sub_right 1) (isOpen_adelicZeroNbhd F)
  set V : Set (AdeleRing (𝓞 F) F)ˣ :=
    (Units.val : (AdeleRing (𝓞 F) F)ˣ → AdeleRing (𝓞 F) F) ⁻¹' W with hVdef
  have hVopen : IsOpen V := IsOpen.preimage Units.continuous_val hWopen
  have hV1 : (1 : (AdeleRing (𝓞 F) F)ˣ) ∈ V := by
    show ((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) - 1 ∈ adelicZeroNbhd F
    rw [Units.val_one, sub_self]
    exact zero_mem_adelicZeroNbhd F
  have hVP : ∀ p ∈ M4aHerbrand.principalIdeles (𝓞 F) F, p ∈ V → p = 1 := by
    intro p hp hpV
    obtain ⟨a, ha⟩ := hp
    have hav : ((p : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) =
        algebraMap F (AdeleRing (𝓞 F) F) (a : F) := by
      rw [← ha]; rfl
    have hm : algebraMap F (AdeleRing (𝓞 F) F) ((a : F) - 1) ∈
        adelicZeroNbhd F ∩ (algebraMap F (AdeleRing (𝓞 F) F)).range := by
      refine ⟨?_, (a : F) - 1, rfl⟩
      have hpW : ((p : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) - 1 ∈
          adelicZeroNbhd F := hpV
      rw [hav] at hpW
      simpa only [map_sub, map_one] using hpW
    rw [adelicZeroNbhd_inter_principal, Set.mem_singleton_iff,
      map_eq_zero_iff _ (AdeleRing.algebraMap_injective (𝓞 F) F), sub_eq_zero] at hm
    apply Units.ext
    rw [hav, hm, map_one, Units.val_one]
  refine ⟨V, hVopen, ?_⟩
  ext p
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hpV, hp⟩
    exact hVP p hp hpV
  · rintro rfl
    exact ⟨hV1, one_mem _⟩

end NumberField.AdeleRing

end
