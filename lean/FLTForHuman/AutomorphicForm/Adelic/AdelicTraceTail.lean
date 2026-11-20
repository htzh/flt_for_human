/-
The local standard character equals the trace character, and the idèle norm slice has finite Haar measure.

Two measure/trace facts: the local additive character of the standard global character at a place is
the local trace character, and the idèles whose norm lies in a positive interval have finite Haar
measure.

  spec-pin: P2M/Sol/S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace.lean
  spec-pin: P2M/Sol/S_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top.lean

## Port deltas

* added `import FLTForHuman.NumberTheory.AdelicLevel.LatticeCounting` — the pin's
  `NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace` (pin 1 `:38`) is declared there and is
  not reachable from the scaffold's import closure.

## Namespaces

The pins' search-stage labels are renamed to subject names and nothing else moves:
`P2MW.S_NumberField_StandardAddChar_psiLocal_eq_psiLocal_trace.NumberField.StandardAddChar.LocalTraceCompat`
keeps the pin's own sub-namespace `LocalTraceCompat` (unchanged), and
`P2MW.S_NumberField_Idele_idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top.Vol17` becomes
`NumberField.Idele.IdeleNormSlice`. Declaration last names, visibility and order are the pins'.

## Heartbeat probe (recorded, never installed — FR-0225)

`lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/AutomorphicForm/Adelic/AdelicTraceTail.lean`
is **silent at N = 6 250** and **fails at N = 3 125** (= 6 250 / 2), at
`(deterministic) timeout at isDefEq` on `private instance finiteDimensional_QK` (the
`inferInstanceAs (FiniteDimensional ℚp ((vp K v).1.adicCompletion K))` step). No
`set_option maxHeartbeats` is in this module.

## Dedup

`dedup.py` in within-module mode on `AdelicTraceTail` reports 2 intra-module clusters, and both
are the pins' own `main` / `solution` pairs, which FR-0221 requires the port to keep as *two*
declarations:

* `LocalTraceCompat.main` (private) vs `psiLocal_eq_psiLocal_trace` (public) — pin 1 `:130`
  vs `:147`;
* `IdeleNormSlice.main` (private) vs
  `idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top` (public) — pin 2 `:103` vs `:142`.

In both pins the `solution` is a statement-identical specialization of the engine, so the pair is
the wire's shape, not a port duplication; `check_port` in fact matches each row *through* its
`main` (`[pin name …LocalTraceCompat.main]`). No other cluster exists.
-/
import FLTForHuman.NumberTheory.NumberField.AdelicTraceFin
import FLTForHuman.RingTheory.DedekindDomain.CompletionBaseChange
import FLTForHuman.LanglandsTunnell.StandardLocalConstantsAt
import FLTForHuman.NumberTheory.NumberField.IdeleProductMeasure
import FLTForHuman.NumberTheory.NumberField.IdeleClass.Vocab
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobal.FundamentalDomain
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import FLTForHuman.NumberTheory.AdelicLevel.LatticeCounting

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain NumberField.TateGlobal
open NumberField.StandardAddChar NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open scoped ENNReal NNReal BigOperators

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace NumberField.StandardAddChar

namespace LocalTraceCompat

section oneField

variable (L : Type) [Field L] [NumberField L]

private theorem psiLocal_eq_psiFin (u : HeightOneSpectrum (𝓞 L)) (x : u.adicCompletion L) :
    psiLocal L u x = psiFin (traceFinHom L (finAdeleSingleAt L u x)) := by
  /- `AdeleRing` is a `def` of a product in v4.34 (FR-0238): the two pairs are named at their
     own types and every step goes through the named values. -/
  set y : AdeleRing (𝓞 L) L := ((0 : InfiniteAdeleRing L), finAdeleSingleAt L u x) with hy
  have hy1 : y.1 = (0 : InfiniteAdeleRing L) := by rw [hy]
  have hy2 : y.2 = finAdeleSingleAt L u x := by rw [hy]
  have hpsi : psiLocal L u x = psiQ ((adelicTraceData L).adelicTrace y) := by
    rw [psiLocal_apply]
    exact congrArg psiQ (congrArg (adelicTraceData L).adelicTrace hy.symm)
  set z : AdeleRing (𝓞 ℚ) ℚ
    := ((adelicTraceData L).traceInf y.1, (adelicTraceData L).traceFin y.2) with hz
  have hz1 : z.1 = (adelicTraceData L).traceInf y.1 := by rw [hz]
  have hz2 : z.2 = (adelicTraceData L).traceFin y.2 := by rw [hz]
  have htrace : (adelicTraceData L).adelicTrace y = z := by
    rw [hz, AdelicTraceData.adelicTrace_apply]
  have hq : psiQ ((adelicTraceData L).adelicTrace y)
      = psiArch ((adelicTraceData L).traceInf y.1)
        * psiFin ((adelicTraceData L).traceFin y.2) := by
    rw [htrace, psiQ_apply, hz1, hz2]
  rw [hpsi, hq, hy1, hy2, map_zero, AddChar.map_zero_eq_one, one_mul]
  rfl

private theorem psiLocal_eq_psiV_trace (p : HeightOneSpectrum (𝓞 ℚ)) (u : p.Extension (𝓞 L))
    (x : u.1.adicCompletion L) :
    psiLocal L u.1 x = psiV p (Algebra.trace (p.adicCompletion ℚ) (u.1.adicCompletion L) x) := by
  rw [psiLocal_eq_psiFin, psiFin_apply]
  rw [finprod_eq_single _ p (fun q hq => ?_)]
  · congr 1
    rw [NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace L (finAdeleSingleAt L u.1 x) p]
    let := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ L (𝓞 L) p
    rw [Finset.sum_eq_single u]
    · rw [finAdeleSingleAt_apply_self]
    · intro w _ hw
      rw [finAdeleSingleAt_apply_of_ne L u.1 _ (fun h => hw (Subtype.ext h)), map_zero]
    · intro h
      exact absurd (Finset.mem_univ u) h
  · rw [NumberField.AdelicTrace.traceFinHom_apply_eq_sum_trace L (finAdeleSingleAt L u.1 x) q]
    let := HeightOneSpectrum.Extension.fintype (𝓞 ℚ) ℚ L (𝓞 L) q
    rw [Finset.sum_eq_zero (fun w _ => ?_), AddChar.map_zero_eq_one]
    have hne : w.1 ≠ u.1 := fun h => hq (by rw [← w.2, ← u.2, h])
    rw [finAdeleSingleAt_apply_of_ne L u.1 _ hne, map_zero]

end oneField

section tower

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

private theorem ringHom_ratInt_ext {R : Type*} [Ring R] (f g : 𝓞 ℚ →+* R) : f = g := by
  refine RingHom.ext fun x => ?_
  have hx : x = ((Rat.ringOfIntegersEquiv x : ℤ) : 𝓞 ℚ) := by
    have h := (eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom (Rat.ringOfIntegersEquiv x)).symm
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.symm_apply_apply] at h
    exact h.symm
  rw [hx, map_intCast, map_intCast]

private theorem under_rat_eq : w.1.under (𝓞 ℚ) = v.under (𝓞 ℚ) := by
  apply HeightOneSpectrum.ext
  have hv : v.asIdeal = Ideal.under (𝓞 K) w.1.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal]
    exact (congrArg HeightOneSpectrum.asIdeal w.2).symm
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, hv,
    Ideal.under_def, Ideal.under_def, Ideal.under_def, Ideal.comap_comap,
    ringHom_ratInt_ext ((algebraMap (𝓞 K) (𝓞 L)).comp (algebraMap (𝓞 ℚ) (𝓞 K)))
      (algebraMap (𝓞 ℚ) (𝓞 L))]

private def pQ : HeightOneSpectrum (𝓞 ℚ) := v.under (𝓞 ℚ)

private def vp : (pQ K v).Extension (𝓞 K) := ⟨v, rfl⟩

private def wp : (pQ K v).Extension (𝓞 L) := ⟨w.1, under_rat_eq K L v w⟩

local notation "ℚp" => HeightOneSpectrum.adicCompletion ℚ (pQ K v)
local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

/- These four are consumed only by instance search, so they are declared `instance` (the pin's
   `def` plus `attribute [local instance]` pair); `move_dead`'s liveness is syntactic and treats
   an `instance` as always live, which is exactly what they are. -/
@[reducible] private instance algQK : Algebra ℚp Kv := inferInstanceAs (Algebra ℚp ((vp K v).1.adicCompletion K))
@[reducible] private instance algQL : Algebra ℚp Lw := inferInstanceAs (Algebra ℚp ((wp K L v w).1.adicCompletion L))

private instance finiteDimensional_QK : FiniteDimensional ℚp Kv :=
  inferInstanceAs (FiniteDimensional ℚp ((vp K v).1.adicCompletion K))
private instance finiteDimensional_QL : FiniteDimensional ℚp Lw :=
  inferInstanceAs (FiniteDimensional ℚp ((wp K L v w).1.adicCompletion L))

private theorem tower_apply (y : ℚp) :
    algebraMap Kv Lw (algebraMap ℚp Kv y) = algebraMap ℚp Lw y := by
  have hKL : Continuous (algebraMap Kv Lw) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous K L w
  have hQK : Continuous (algebraMap ℚp Kv) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous ℚ K (vp K v)
  have hQL : Continuous (algebraMap ℚp Lw) :=
    HeightOneSpectrum.Extension.adicCompletionSemialgHom_continuous ℚ L (wp K L v w)
  refine DenseRange.induction_on (HeightOneSpectrum.denseRange_algebraMap ℚ (pQ K v)) y
    (isClosed_eq (hKL.comp hQK) hQL) (fun q => ?_)
  change (w.adicCompletionSemialgHom K L) (((vp K v).adicCompletionSemialgHom ℚ K) (algebraMap ℚ ℚp q))
    = ((wp K L v w).adicCompletionSemialgHom ℚ L) (algebraMap ℚ ℚp q)
  have h1 : ((vp K v).adicCompletionSemialgHom ℚ K) (algebraMap ℚ ℚp q)
      = algebraMap K Kv (algebraMap ℚ K q) :=
    SemialgHom.commutes _ _
  have h2 : (w.adicCompletionSemialgHom K L) (algebraMap K Kv (algebraMap ℚ K q))
      = algebraMap L Lw (algebraMap K L (algebraMap ℚ K q)) :=
    SemialgHom.commutes _ _
  have h3 : ((wp K L v w).adicCompletionSemialgHom ℚ L) (algebraMap ℚ ℚp q)
      = algebraMap L Lw (algebraMap ℚ L q) :=
    SemialgHom.commutes _ _
  rw [h1, h2, h3, eq_ratCast (algebraMap ℚ K) q, eq_ratCast (algebraMap ℚ L) q, map_ratCast]

private instance isScalarTower_QKL : IsScalarTower ℚp Kv Lw :=
  IsScalarTower.of_algebraMap_eq fun y =>
    (tower_apply K L v w y).symm

private theorem trace_tower (x : Lw) :
    Algebra.trace ℚp Kv (Algebra.trace Kv Lw x) = Algebra.trace ℚp Lw x :=
  Algebra.trace_trace x

end tower

private theorem main (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L)) (x : w.1.adicCompletion L) :
    psiLocal L w.1 x
      = psiLocal K v (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x) := by
  have hL := psiLocal_eq_psiV_trace L (pQ K v) (wp K L v w) x
  have hK := psiLocal_eq_psiV_trace K (pQ K v) (vp K v)
    (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x)
  have ht := trace_tower K L v w x
  change psiLocal L w.1 x = _ at hL
  change psiLocal K v _ = _ at hK
  rw [hL, hK]
  exact congrArg (psiV (pQ K v)) ht.symm

end LocalTraceCompat

theorem psiLocal_eq_psiLocal_trace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : v.Extension (𝓞 L))
    (x : w.1.adicCompletion L) :
    psiLocal L w.1 x
      = psiLocal K v (Algebra.trace (v.adicCompletion K) (w.1.adicCompletion L) x)
  :=
  LocalTraceCompat.main K L v w x

end NumberField.StandardAddChar

namespace NumberField.Idele

namespace IdeleNormSlice

open scoped Pointwise

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.Idele.isHaarMeasure_idelicHaar

private scoped instance countableK : Countable K := (Module.finBasis ℚ K).equivFun.toEquiv.injective.countable

private scoped instance countableKunits : Countable Kˣ := Function.Injective.countable fun _ _ h => Units.ext h

private scoped instance countablePrincipalIdeles : Countable ↥(M4aHerbrand.principalIdeles (𝓞 K) K) := by
  unfold M4aHerbrand.principalIdeles
  exact Function.Surjective.countable (MonoidHom.rangeRestrict_surjective _)

private theorem ideleNorm_eq_one_of_mem {γ : (AdeleRing (𝓞 K) K)ˣ}
    (hγ : γ ∈ M4aHerbrand.principalIdeles (𝓞 K) K) :
    ideleNorm K γ = 1 := by
  obtain ⟨u, rfl⟩ := hγ
  unfold ideleNorm
  rw [NNReal.coe_eq_one]
  convert @NumberField.AdeleRing.distribHaarChar_algebraMap K _ _ (NumberField.AdelicHaar.adeleBorel (𝓞 K) K)
    (NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K) u using 2
  all_goals first | with_reducible_and_instances rfl | rfl

private theorem smul_slab_eq (S : Set ℝ) (γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K)) :
    γ • {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K z ∈ S} = {z | ideleNorm K z ∈ S} := by
  ext z
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have h1 : ideleNorm K ((γ : (AdeleRing (𝓞 K) K)ˣ)⁻¹) = 1 := by
    rw [← Subgroup.coe_inv]; exact ideleNorm_eq_one_of_mem K (γ⁻¹).2
  simp only [Set.mem_ofPred_eq, Subgroup.smul_def, smul_eq_mul, ideleNorm_mul, Subgroup.coe_inv, h1, one_mul]

private theorem preimage_slab_eq (S : Set ℝ) (γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K)) :
    (fun z : (AdeleRing (𝓞 K) K)ˣ => γ • z) ⁻¹' {z | ideleNorm K z ∈ S} = {z | ideleNorm K z ∈ S} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Subgroup.smul_def, smul_eq_mul, ideleNorm_mul,
    ideleNorm_eq_one_of_mem K γ.2, one_mul]

private theorem measurableSet_slab {S : Set ℝ} (hS : MeasurableSet S) :
    MeasurableSet {z : (AdeleRing (𝓞 K) K)ˣ | ideleNorm K z ∈ S} :=
  (NumberField.TateGlobal.continuous_ideleNorm K).measurable hS

private theorem finite_on_tate (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ D₀ : Set (AdeleRing (𝓞 K) K)ˣ, MeasurableSet D₀ ∧
      IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D₀ (NumberField.Idele.idelicHaar K) ∧
      (NumberField.Idele.idelicHaar K) (D₀ ∩ {z | ideleNorm K z ∈ Set.Icc a b}) < ⊤ := by
  obtain ⟨D₀, hD₀m, hD₀F, hint⟩ :=
    NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow K
      (NumberField.Idele.idelicHaar K)
  obtain ⟨k, hk⟩ := hint 0
  refine ⟨D₀, hD₀m, hD₀F, ?_⟩
  set A : Set (AdeleRing (𝓞 K) K)ˣ := {z | ideleNorm K z ∈ Set.Icc a b} with hA
  set c : ℝ := min a b⁻¹ with hc
  have hcpos : 0 < c := lt_min ha (inv_pos.mpr (ha.trans hab))
  have hb : 0 < b := ha.trans hab

  have hlow : ∀ z ∈ D₀ ∩ A, ENNReal.ofReal (c ^ k) ≤
      ‖min (ideleNorm K z) (ideleNorm K z)⁻¹ ^ k * ideleNorm K z ^ (0 : ℝ)‖ₑ := by
    rintro z ⟨-, hz1, hz2⟩
    rw [Real.rpow_zero, mul_one,
      Real.enorm_eq_ofReal (pow_nonneg (le_min (ideleNorm_pos z).le (inv_nonneg.mpr (ideleNorm_pos z).le)) _)]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hcpos.le (le_min ?_ ?_) _)
    · exact (min_le_left _ _).trans hz1
    · exact (min_le_right _ _).trans ((inv_le_inv₀ hb (ideleNorm_pos z)).mpr hz2)
  have hmeas : MeasurableSet (D₀ ∩ A) := hD₀m.inter (measurableSet_slab K measurableSet_Icc)
  have h1 : ENNReal.ofReal (c ^ k) * (NumberField.Idele.idelicHaar K) (D₀ ∩ A) ≤
      ∫⁻ z in D₀, ‖min (ideleNorm K z) (ideleNorm K z)⁻¹ ^ k * ideleNorm K z ^ (0 : ℝ)‖ₑ
        ∂(NumberField.Idele.idelicHaar K) := by
    calc ENNReal.ofReal (c ^ k) * (NumberField.Idele.idelicHaar K) (D₀ ∩ A)
        = ∫⁻ z in D₀ ∩ A, ENNReal.ofReal (c ^ k) ∂(NumberField.Idele.idelicHaar K) :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ z in D₀ ∩ A, ‖min (ideleNorm K z) (ideleNorm K z)⁻¹ ^ k * ideleNorm K z ^ (0 : ℝ)‖ₑ
            ∂(NumberField.Idele.idelicHaar K) :=
          setLIntegral_mono' hmeas hlow
      _ ≤ ∫⁻ z in D₀, ‖min (ideleNorm K z) (ideleNorm K z)⁻¹ ^ k * ideleNorm K z ^ (0 : ℝ)‖ₑ
            ∂(NumberField.Idele.idelicHaar K) :=
          lintegral_mono_set Set.inter_subset_left
  have h2 := hk.2
  rw [HasFiniteIntegral] at h2
  have hck : ENNReal.ofReal (c ^ k) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hcpos k)).ne'
  exact (ENNReal.le_div_iff_mul_le (Or.inl hck) (Or.inl ENNReal.ofReal_ne_top)).mpr (by rwa [mul_comm]) |>.trans_lt
    (ENNReal.div_lt_top h2.ne hck)

private theorem main (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) ∧
      (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) < ⊤ := by
  /- the pin's proof never spends `hD` (its fundamental domain carries the measurability it
     needs); the binder is part of the wire, so it is spent once rather than renamed (FR-0236). -/
  have hDmeas : MeasurableSet D := hD
  set μ := NumberField.Idele.idelicHaar K with hμ
  set A : Set (AdeleRing (𝓞 K) K)ˣ := {z | ideleNorm K z ∈ Set.Icc a b} with hA
  have hAm : MeasurableSet A := measurableSet_slab K measurableSet_Icc
  have hAinv : ∀ γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K), (fun z => γ • z) ⁻¹' A = A :=
    fun γ => preimage_slab_eq K _ γ
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨z₀, -, hz₀⟩ := NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one K ((a + b) / 2) (by linarith)
    set U : Set (AdeleRing (𝓞 K) K)ˣ := {z | ideleNorm K z ∈ Set.Ioo a b} with hU
    have hUopen : IsOpen U := isOpen_Ioo.preimage (NumberField.TateGlobal.continuous_ideleNorm K)
    have hUne : U.Nonempty := ⟨z₀, by rw [hU, Set.mem_ofPred_eq, hz₀]; constructor <;> linarith⟩
    have hUpos : 0 < μ U := hUopen.measure_pos μ hUne
    have hUA : U ⊆ A := fun z hz => Set.Ioo_subset_Icc_self hz
    have hApos : 0 < μ A := hUpos.trans_le (measure_mono hUA)
    rw [pos_iff_ne_zero]
    intro h0
    have hsum := hDF.measure_eq_tsum A
    have hterm : ∀ γ : ↥(M4aHerbrand.principalIdeles (𝓞 K) K), μ (γ • A ∩ D) = 0 := by
      intro γ
      rw [smul_slab_eq K _ γ, Set.inter_comm]
      exact h0
    simp only [hterm, tsum_zero] at hsum
    exact hApos.ne' hsum
  ·
    obtain ⟨D₀, hD₀m, hD₀F, hfin⟩ := finite_on_tate K a b ha hab
    have heq : μ (A ∩ D₀) = μ (A ∩ D) := hD₀F.measure_set_eq hDF hAm hAinv
    rw [Set.inter_comm, ← heq, Set.inter_comm]
    exact hfin

end IdeleNormSlice

theorem idelicHaar_inter_setOf_ideleNorm_mem_Icc_pos_and_lt_top
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdeleRing (𝓞 K) K)ˣ) (hD : MeasurableSet D)
    (hDF : IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 K) K) D (NumberField.Idele.idelicHaar K))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) ∧
      (NumberField.Idele.idelicHaar K) (D ∩ {z | ideleNorm K z ∈ Set.Icc a b}) < ⊤
  :=
  IdeleNormSlice.main K D hD hDF a b ha hab

end NumberField.Idele

end
