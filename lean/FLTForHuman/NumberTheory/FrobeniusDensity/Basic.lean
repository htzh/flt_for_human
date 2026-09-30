/-
  The shared Frobenius-density prelude (phase H1).

  This module holds once the analytic and group-theoretic helpers that the pin
  repeats privately across the `S_FrobeniusDensity_*` solution files:

  * the Dedekind-zeta / `idealSum` comparison chain
    (`zetaTerm_nonneg` … `idealSum_eq_tsum_zetaTerm`);
  * the Möbius / `zpowers` group-theory block
    (`mem_zpowers_pow_div_iff` … `ncard_eq_sum_indicator`) and the polynomial
    degree bound `card_le_of_forall_pow_eq`;
  * the first comparison and the `toReal` transfer lemma
    (`primeSum_le_idealSum`, `toReal_term`).

  Transcribed from the pinned FLT solution files (`aa2d8b3`, `P2M/Sol/`).
  Two blocks are *not* ported because their pin proofs consume phase-T
  headlines the port does not carry (see the module report):
  `sum_moebius_mem_zpowers` needs `ArithmeticFunction.sum_moebius_filter_dvd`
  and `degOneSum_ne_top` needs `FrobeniusDensity.idealSum_ne_top`.
-/
import FLTForHuman.NumberTheory.FrobeniusDensity.PrimeSums
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Group
import Mathlib.Tactic.Positivity

set_option autoImplicit false

open Ideal NumberField Filter Topology Asymptotics IsDedekindDomain
open scoped ENNReal Topology

namespace FrobeniusDensity

section Zeta

variable (K : Type*) [Field K] [NumberField K]

lemma zetaTerm_nonneg (s : ℝ) (n : ℕ) : 0 ≤ zetaTerm K s n := by
  unfold zetaTerm
  split
  · exact le_refl 0
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  simp only [idealCount]
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 0} by
      simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

lemma isBigO_sum_of_tendsto_div :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ))
      =O[atTop] (fun n => (n : ℝ) ^ (1:ℝ)) := by
  simp only [Real.rpow_one]
  rw [isBigO_iff]

  have hbdd : BddAbove (Set.range (fun n : ℕ =>
      (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n)) :=
    (tendsto_sum_idealCount_div K).bddAbove_range
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨max C 0, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.norm_of_nonneg hn'.le,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)]
  calc ∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)
      = ((∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) * n := by field_simp
    _ ≤ C * n := mul_le_mul_of_nonneg_right (hC ⟨n, rfl⟩) hn'.le
    _ ≤ max C 0 * n := mul_le_mul_of_nonneg_right (le_max_left _ _) hn'.le

lemma LSeriesSummable_idealCount {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n => (idealCount K n : ℂ)) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (idealCount K n : ℝ))
    ?_ (fun n => Nat.cast_nonneg _) zero_le_one (by simpa using hs)
  exact isBigO_sum_of_tendsto_div K

lemma term_eq_ofReal_zetaTerm (s : ℝ) (n : ℕ) :
    LSeries.term (fun n => (idealCount K n : ℂ)) s n = (zetaTerm K s n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [zetaTerm, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, zetaTerm, ite_eq_right hn]
    have hpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_cpow hpos.le,
      Complex.ofReal_neg, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

lemma summable_zetaTerm {s : ℝ} (hs : 1 < s) : Summable (zetaTerm K s) := by
  have h : Summable fun n => ((zetaTerm K s n : ℝ) : ℂ) := by
    refine (LSeriesSummable_idealCount K hs).congr fun n => ?_
    exact term_eq_ofReal_zetaTerm K s n
  exact Complex.summable_ofReal.mp h

def NormFiber (n : ℕ) : Type _ :=
  {I : {I : Ideal (𝓞 K) // I ≠ ⊥} // Ideal.absNorm I.1 = n}

noncomputable def normFiberEquiv :
    (Σ n : ℕ, NormFiber K n) ≃ {I : Ideal (𝓞 K) // I ≠ ⊥} where
  toFun p := p.2.1
  invFun I := ⟨Ideal.absNorm I.1, I, rfl⟩
  left_inv p := by rcases p with ⟨n, I, rfl⟩; rfl
  right_inv I := rfl

lemma tsum_normFiber (s : ℝ) (n : ℕ) :
    ∑' I : NormFiber K n, normRpow K s I.1.1 = ENNReal.ofReal (zetaTerm K s n) := by
  have hconst : ∀ I : NormFiber K n, normRpow K s I.1.1 = (n : ℝ≥0∞) ^ (-s) := fun I => by
    rw [normRpow, I.2]
  rw [tsum_congr hconst, ENNReal.tsum_const]
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsEmpty (NormFiber K 0) := ⟨fun I => I.1.2 (Ideal.absNorm_eq_zero_iff.mp I.2)⟩
    simp [zetaTerm, ENat.card_eq_coe_natCard]
  · have hpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hequiv : NormFiber K n ≃ {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      { toFun := fun I => ⟨I.1.1, I.2⟩
        invFun := fun I => ⟨⟨I.1, fun h => hn (by rw [← I.2, h, Ideal.absNorm_bot])⟩, I.2⟩
        left_inv := fun I => rfl
        right_inv := fun I => rfl }
    have hfin : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).to_subtype
    have hfin' : Finite (NormFiber K n) := Finite.of_equiv _ hequiv.symm
    rw [zetaTerm, ite_eq_right hn, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_pos hpos, ENat.card_eq_coe_natCard, Nat.card_congr hequiv]
    simp only [ENNReal.ofReal_natCast, idealCount]
    norm_cast

lemma tsum_equiv' {α β : Type*} (e : α ≃ β) (f : β → ℝ≥0∞) :
    ∑' a, f (e a) = ∑' b, f b := by
  refine le_antisymm (ENNReal.tsum_comp_le_tsum_of_injective e.injective f) ?_
  simpa using ENNReal.tsum_comp_le_tsum_of_injective e.symm.injective fun a => f (e a)

lemma idealSum_eq_tsum_zetaTerm (s : ℝ) :
    idealSum K s = ∑' n : ℕ, ENNReal.ofReal (zetaTerm K s n) := by
  rw [idealSum, ← tsum_equiv' (normFiberEquiv K) (fun I => normRpow K s I.1),
    ENNReal.tsum_sigma']
  exact tsum_congr fun n => tsum_normFiber K s n

end Zeta

section Weight

variable {G : Type*} [Group G] [Finite G]

theorem mem_zpowers_pow_div_iff (σ y : G) {f : ℕ} (hf : f ∣ orderOf σ) (hf0 : f ≠ 0) :
    y ∈ Subgroup.zpowers (σ ^ (orderOf σ / f))
      ↔ y ∈ Subgroup.zpowers σ ∧ orderOf y ∣ f := by
  have hn0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  constructor
  · intro hy
    obtain ⟨i, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
    refine ⟨?_, ?_⟩
    · rw [← pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers σ) _
    · rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, ← pow_mul]
      have h : orderOf σ / f * (i * f) = orderOf σ * i := by
        rw [show i * f = f * i from mul_comm i f, ← mul_assoc, Nat.div_mul_cancel hf]
      rw [h, pow_mul, pow_orderOf_eq_one, one_pow]
  · rintro ⟨hy, hyf⟩
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hy)
    have h1 : σ ^ (j * f) = 1 := by
      rw [pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp hyf
    have h2 : orderOf σ ∣ j * f := orderOf_dvd_iff_pow_eq_one.mpr h1
    have h3 : orderOf σ / f ∣ j := by
      obtain ⟨c, hc⟩ := h2
      have hfpos : 0 < f := Nat.pos_of_ne_zero hf0
      refine ⟨c, Nat.eq_of_mul_eq_mul_right hfpos ?_⟩
      rw [mul_comm (orderOf σ / f) c, mul_assoc, Nat.div_mul_cancel hf, hc]
      ring
    obtain ⟨c, hc⟩ := h3
    rw [hc, pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem exists_pow_coprime_eq_of_orderOf_eq {σ y : G} (hmem : y ∈ Subgroup.zpowers σ)
    (hord : orderOf y = orderOf σ) :
    ∃ k : ℕ, k.Coprime (orderOf σ) ∧ σ ^ k = y := by
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h1 : orderOf σ = 1 := by simpa using hord.symm
    exact ⟨1, Nat.coprime_one_left _, by simp [orderOf_eq_one_iff.mp h1]⟩
  · refine ⟨k, ?_, rfl⟩
    have h1 : orderOf (σ ^ k) = orderOf σ / Nat.gcd (orderOf σ) k := orderOf_pow' σ hk.ne'
    rw [hord] at h1
    have hgcd : Nat.gcd (orderOf σ) k = 1 := by
      by_contra hne
      have hpos : 0 < Nat.gcd (orderOf σ) k :=
        Nat.pos_of_ne_zero fun h0 => (orderOf_pos σ).ne'
          (Nat.eq_zero_of_gcd_eq_zero_left h0)
      have h4 : 1 < Nat.gcd (orderOf σ) k := lt_of_le_of_ne hpos (Ne.symm hne)
      exact absurd h1.symm (Nat.div_lt_self (orderOf_pos σ) h4).ne
    exact Nat.coprime_comm.mp hgcd

theorem orderOf_pow_orderOf_div (σ : G) {f : ℕ} (hf : f ∣ orderOf σ) (hf0 : f ≠ 0) :
    orderOf (σ ^ (orderOf σ / f)) = f := by
  have hn0 : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  have hd0 : orderOf σ / f ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hf0, Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hf⟩
  rw [orderOf_pow' σ hd0, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hf), Nat.div_div_self hf hn0]

omit [Finite G] in
theorem ncard_conj_mem_eq_card_mul_ncard (H : Subgroup G) (τ : G) :
    {g : G | g⁻¹ * τ * g ∈ H}.ncard
      = Nat.card H * {x : G ⧸ H | τ • x = x}.ncard := by
  have hpre : {g : G | g⁻¹ * τ * g ∈ H}
      = (QuotientGroup.mk : G → G ⧸ H) ⁻¹' {x : G ⧸ H | τ • x = x} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    have hsmul : τ • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk (τ * g) :=
      MulAction.Quotient.smul_coe H τ g
    rw [hsmul, QuotientGroup.eq, show (τ * g)⁻¹ * g = (g⁻¹ * τ * g)⁻¹ by group]
    exact (inv_mem_iff).symm
  rw [← Nat.card_coe_set_eq, hpre,
    Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet H _), Nat.card_prod,
    Nat.card_coe_set_eq]

open scoped Classical in
theorem ncard_eq_sum_indicator {α : Type*} [Fintype α] (p : α → Prop) :
    ({a : α | p a}.ncard : ℤ) = ∑ a : α, (if p a then 1 else 0) := by
  rw [Finset.sum_boole]
  norm_cast
  rw [← Set.ncard_coe_finset (Finset.univ.filter p)]
  congr 1
  ext a
  simp

end Weight

open Polynomial in
theorem card_le_of_forall_pow_eq {K : Type*} [CommRing K] [IsDomain K] [Finite K]
    {n : ℕ} (hn : 1 < n) (h : ∀ x : K, x ^ n = x) : Nat.card K ≤ n := by
  cases nonempty_fintype K
  have hdeg : (X ^ n - X : K[X]).natDegree = n := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; exact hn),
      natDegree_X_pow]
  have hne : (X ^ n - X : K[X]) ≠ 0 := ne_zero_of_natDegree_gt (n := 0) (by omega)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ← hdeg]
  refine card_le_degree_of_subset_roots fun x _ ↦ ?_
  rw [mem_roots hne]
  simp [Polynomial.IsRoot, h x]

section PrimeSums

variable (K : Type*) [Field K] [NumberField K]

lemma primeSum_le_idealSum (s : ℝ) : primeSum K s ≤ idealSum K s := by
  have hinj : Function.Injective
      (fun v : HeightOneSpectrum (𝓞 K) =>
        (⟨v.asIdeal, v.ne_bot⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})) :=
    fun v w h => HeightOneSpectrum.ext (by simpa using congrArg Subtype.val h)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1

omit [NumberField K] in
theorem toReal_term (S₀ : Finset ℕ) (s : ℝ) (ℓ : ℕ) :
    ((if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s)).toReal
      = (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) := by
  rw [ENNReal.toReal_mul, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ENNReal.toReal_natCast, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

end PrimeSums

end FrobeniusDensity
