/-
  The monic-relation leaves (SET-8 order 1).

  Statements verbatim from the pinned wrappers
  `Theorems/Thm_WLight_exists_{analyticOnNhd,mdifferentiable}_div_of_monicRel.lean`,
  `Theorems/Thm_WLight_exists_twist_of_flat.lean` and
  `Theorems/Thm_WLight_span_inter_rational_of_twist_stable.lean`; proofs
  transcribed from the matching `P2M/Sol/S_WLight_*` files and adapted to
  mathlib `v4.34.0`. Every pin helper is `private` here, so the four headlines
  are the module's only public surface.

  The pin splits these four leaves over four `S_` files that repeat the same
  valuation engine (`le_meromorphicOrderAt_sum`,
  `meromorphicOrderAt_le_of_monicRel`,
  `meromorphicOrderAt_div_nonneg_of_monicRel`) in the first two, and repeat the
  closure-1 `exists_twist_of_flat` proof in the third and fourth. The port writes
  each block once: the evaluation engine feeds `exists_analyticOnNhd_div_of_monicRel`,
  which in turn feeds `exists_mdifferentiable_div_of_monicRel`, and
  `span_inter_rational_of_twist_stable` consumes the single
  `exists_twist_of_flat`. The pin's `S_WLight_exists_mdifferentiable_div_of_monicRel`
  also carries an unused `mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero`,
  which is mathlib's `UpperHalfPlane.mul_eq_zero_iff` and is not transcribed.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_exists_analyticOnNhd_div_of_monicRel.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_exists_mdifferentiable_div_of_monicRel.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_exists_twist_of_flat.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WLight_span_inter_rational_of_twist_stable.lean

  v4.34 drifts hit here: `if_true`/`if_false` → `ite_true`/`ite_false` and
  `dif_pos` → `dite_eq_left` in the flat-descent proof; the pin's local
  `set_option maxHeartbeats 1600000` in `exists_twist_of_flat` is **not**
  transcribed (the project's global cap is `4000000`, above it).
-/

import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

set_option autoImplicit false

noncomputable section

open Complex Real UpperHalfPlane Function
open scoped Topology Manifold UpperHalfPlane

namespace WLight

/-! ### The valuation engine

The meromorphic order at a point of a monic-relation quotient is nonnegative. -/

private theorem le_meromorphicOrderAt_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} (s : Finset ι) {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) (m : WithTop ℤ)
    (hm : ∀ i ∈ s, m ≤ meromorphicOrderAt (f i) x) :
    m ≤ meromorphicOrderAt (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc m ≤ min (meromorphicOrderAt (f a) x) (meromorphicOrderAt (∑ i ∈ s, f i) x) := by
            refine le_min (hm a (Finset.mem_insert_self a s)) ?_
            exact ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
              (fun i hi ↦ hm i (Finset.mem_insert_of_mem hi))
      _ ≤ meromorphicOrderAt (f a + ∑ i ∈ s, f i) x := by
            apply meromorphicOrderAt_add (hf a (Finset.mem_insert_self a s))
            exact MeromorphicAt.sum (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

private theorem meromorphicOrderAt_le_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    meromorphicOrderAt G τ ≤ meromorphicOrderAt F τ := by
  by_contra hlt
  rw [not_le] at hlt
  lift meromorphicOrderAt G τ to ℤ using hGord with m hm
  have hFord : meromorphicOrderAt F τ ≠ ⊤ := hlt.ne_top
  lift meromorphicOrderAt F τ to ℤ using hFord with r hr
  have hrm : r < m := WithTop.coe_lt_coe.mp hlt
  set S := ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k with hS
  have hMerS : ∀ k ∈ Finset.range n, MeromorphicAt (c k * G ^ (n - k) * F ^ k) τ := by
    intro k hk
    exact (((hc k (Finset.mem_range.mp hk)).mul ((hG.pow _))).mul (hF.pow _)).meromorphicAt
  have hsum_ord : (↑(n * r) + 1 : WithTop ℤ) ≤ meromorphicOrderAt S τ := by
    refine le_meromorphicOrderAt_sum _ hMerS _ ?_
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hterm : meromorphicOrderAt (c k * G ^ (n - k) * F ^ k) τ
        = meromorphicOrderAt (c k) τ + ((n - k : ℕ) * meromorphicOrderAt G τ
            + k * meromorphicOrderAt F τ) := by
      rw [meromorphicOrderAt_mul (((hc k hk').mul (hG.pow (n - k))).meromorphicAt)
            ((hF.pow k).meromorphicAt),
          meromorphicOrderAt_mul (hc k hk').meromorphicAt ((hG.pow (n - k)).meromorphicAt),
          meromorphicOrderAt_pow hG.meromorphicAt (n := n - k),
          meromorphicOrderAt_pow hF.meromorphicAt (n := k), add_assoc]
    rw [hterm, ← hm, ← hr]
    have hc_ord : (0 : WithTop ℤ) ≤ meromorphicOrderAt (c k) τ :=
      (hc k hk').meromorphicOrderAt_nonneg
    have hnk : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by omega
    have key : (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := by
      rw [show ((n - k : ℕ) : WithTop ℤ) = (((n - k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          show ((k : ℕ) : WithTop ℤ) = (((k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          ← WithTop.coe_mul, ← WithTop.coe_mul, ← WithTop.coe_add,
          ← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe, hnk]
      have h1 : (1 : ℤ) ≤ (n : ℤ) - k := by omega
      nlinarith [h1, hrm]
    calc (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := key
      _ = 0 + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := (zero_add _).symm
      _ ≤ meromorphicOrderAt (c k) τ + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := by
          gcongr
  have hFn_ord : meromorphicOrderAt (F ^ n) τ = (↑(n * r) : WithTop ℤ) := by
    rw [meromorphicOrderAt_pow hF.meromorphicAt, ← hr]; push_cast; ring_nf
  have hlt2 : meromorphicOrderAt (F ^ n) τ < meromorphicOrderAt S τ := by
    rw [hFn_ord]
    refine lt_of_lt_of_le ?_ hsum_ord
    exact_mod_cast lt_add_one (n * r)
  have heq : meromorphicOrderAt (F ^ n + S) τ = meromorphicOrderAt (F ^ n) τ :=
    meromorphicOrderAt_add_eq_left_of_lt
      (MeromorphicAt.sum (fun i hi ↦ hMerS i hi)) hlt2
  have hzero : (F ^ n + S) =ᶠ[𝓝[≠] τ] 0 :=
    hrel.filter_mono nhdsWithin_le_nhds
  have htop : meromorphicOrderAt (F ^ n + S) τ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]; exact hzero
  rw [heq, hFn_ord] at htop
  exact WithTop.coe_ne_top htop

private theorem meromorphicOrderAt_div_nonneg_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    0 ≤ meromorphicOrderAt (F / G) τ := by
  have hle := meromorphicOrderAt_le_of_monicRel hF hG hGord hc hrel
  rw [meromorphicOrderAt_div hF.meromorphicAt hG.meromorphicAt,
      ← LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top hGord]
  exact (LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top hGord).mpr hle

/-! ### The half-plane bridge -/

private lemma analyticOnNhd_comp_ofComplex {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet

private lemma mdifferentiable_of_analyticOnNhd {f : ℍ → ℂ}
    (hf : AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  UpperHalfPlane.mdifferentiable_iff.mpr hf.differentiableOn

/-! ### Order 1, leaf 1: analytic division from a monic relation -/

theorem exists_analyticOnNhd_div_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {U : Set 𝕜} (hU : IsOpen U) (hUc : IsPreconnected U)
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ}
    (hF : AnalyticOnNhd 𝕜 F U) (hG : AnalyticOnNhd 𝕜 G U) (hG0 : ∃ z ∈ U, G z ≠ 0)
    (hc : ∀ k < n, AnalyticOnNhd 𝕜 (c k) U)
    (hrel : Set.EqOn (F ^ n + ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) 0 U) :
    ∃ H : 𝕜 → 𝕜, AnalyticOnNhd 𝕜 H U ∧ Set.EqOn F (G * H) U := by
  obtain ⟨τ₀, hτ₀U, hGτ₀⟩ := hG0
  have hGord0 : meromorphicOrderAt G τ₀ ≠ ⊤ := by
    have h0 := (hG τ₀ hτ₀U).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hGτ₀
    simp [h0]
  have hGord : ∀ τ ∈ U, meromorphicOrderAt G τ ≠ ⊤ := fun τ hτ ↦
    hG.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hUc hτ₀U hτ hGord0
  have hdiv_ord : ∀ τ ∈ U, 0 ≤ meromorphicOrderAt (F / G) τ := by
    intro τ hτ
    refine meromorphicOrderAt_div_nonneg_of_monicRel (hF τ hτ) (hG τ hτ) (hGord τ hτ)
      (fun k hk ↦ hc k hk τ hτ) ?_
    filter_upwards [hU.mem_nhds hτ] with z hz using hrel hz
  have hmer : MeromorphicOn (F / G) U :=
    fun τ hτ ↦ (hF τ hτ).meromorphicAt.div (hG τ hτ).meromorphicAt
  set H := toMeromorphicNFOn (F / G) U with hH
  have hHnf : MeromorphicNFOn H U := meromorphicNFOn_toMeromorphicNFOn (F / G) U
  have hHan : AnalyticOnNhd 𝕜 H U := by
    rw [← hHnf.divisor_nonneg_iff_analyticOnNhd]
    intro z
    by_cases hz : z ∈ U
    · simp only [MeromorphicOn.divisor_apply hHnf.meromorphicOn hz,
        Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
      rw [hH, meromorphicOrderAt_toMeromorphicNFOn hmer hz]
      exact WithTop.untop₀_nonneg.mpr (hdiv_ord z hz)
    · simp [hz]
  refine ⟨H, hHan, ?_⟩
  have hGHan : AnalyticOnNhd 𝕜 (G * H) U := hG.mul hHan
  have heq_near : F =ᶠ[𝓝 τ₀] G * H := by
    have hGopen : {z | G z ≠ 0} ∈ 𝓝 τ₀ :=
      (hG τ₀ hτ₀U).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hGτ₀)
    filter_upwards [hGopen, hU.mem_nhds hτ₀U] with z hGz hzU
    have hanalz : AnalyticAt 𝕜 (F / G) z := (hF z hzU).div (hG z hzU) hGz
    have : H z = (F / G) z := by
      rw [hH, toMeromorphicNFOn_eq_toMeromorphicNFAt hmer hzU,
          toMeromorphicNFAt_eq_self.mpr hanalz.meromorphicNFAt]
    simp only [Pi.mul_apply, this, Pi.div_apply]
    field_simp
  have hfreq : ∃ᶠ z in 𝓝[≠] τ₀, F z = (G * H) z := by
    refine (heq_near.filter_mono nhdsWithin_le_nhds).frequently
  exact fun τ hτ ↦ hF.eqOn_of_preconnected_of_frequently_eq hGHan hUc hτ₀U hfreq hτ

/-! ### Order 1, leaf 2: manifold differentiability from a monic relation -/

theorem exists_mdifferentiable_div_of_monicRel {a b : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}
    (hahol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a) (hbhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b)
    (hb0 : b ≠ 0) (hc : ∀ k < d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c k))
    (hrel : a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0) :
    ∃ F : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ F * b = a := by
  obtain ⟨τ₀, hτ₀⟩ := Function.ne_iff.mp hb0
  have hrelH : ∀ τ : ℍ, a τ ^ d
      + ∑ k ∈ Finset.range d, c k τ * b τ ^ (d - k) * a τ ^ k = 0 := by
    intro τ
    simpa only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply,
      Pi.zero_apply] using congrFun hrel τ
  let a' := a ∘ ofComplex
  let b' := b ∘ ofComplex
  let c' := fun k ↦ (c k) ∘ ofComplex
  have hrel' : Set.EqOn (a' ^ d + ∑ k ∈ Finset.range d, c' k * b' ^ (d - k) * a' ^ k) 0
      upperHalfPlaneSet := by
    intro z hz
    simp only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply, Pi.zero_apply,
      a', b', c', comp_ofComplex_of_im_pos _ z hz]
    exact hrelH ⟨z, hz⟩
  obtain ⟨H', hH'an, hH'eq⟩ := exists_analyticOnNhd_div_of_monicRel isOpen_upperHalfPlaneSet
    (convex_halfSpace_im_gt 0).isPreconnected (analyticOnNhd_comp_ofComplex hahol)
    (analyticOnNhd_comp_ofComplex hbhol)
    ⟨(τ₀ : ℂ), τ₀.im_pos, by
      simpa [b', comp_ofComplex_of_im_pos b _ τ₀.im_pos] using hτ₀⟩
    (fun k hk ↦ analyticOnNhd_comp_ofComplex (hc k hk)) hrel'
  have hHmem : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ H' ↑τ) := by
    apply mdifferentiable_of_analyticOnNhd
    refine AnalyticOnNhd.congr isOpen_upperHalfPlaneSet hH'an (fun z hz ↦ ?_)
    exact (comp_ofComplex_of_im_pos (fun τ : ℍ ↦ H' ↑τ) z hz).symm
  refine ⟨fun τ ↦ H' ↑τ, hHmem, ?_⟩
  funext τ
  have heq := hH'eq τ.im_pos
  simp only [Pi.mul_apply, Function.comp_apply, ofComplex_apply] at heq
  show H' ↑τ * b τ = a τ
  rw [mul_comm]
  exact heq.symm

/-! ### Order 1, leaf 3: the flat twist -/

theorem exists_twist_of_flat (K : IntermediateField ℚ ℂ) (M : Submodule ↥K (ℍ → ℂ))
    (hflat : ∀ s : Finset (ℍ → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) →
      LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) →
      LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)))
    (σ : ℂ ≃ₐ[↥K] ℂ) :
    ∃ T : (ℍ → ℂ) → (ℍ → ℂ), ∀ (ι : Type) [Fintype ι] (c : ι → ℂ) (e : ι → ℍ → ℂ),
      (∀ i, e i ∈ M) → T (∑ i, c i • e i) = ∑ i, σ (c i) • e i := by
  classical
  set bM := Module.Basis.ofVectorSpace ↥K ↥M with hbM_def
  set e : Module.Basis.ofVectorSpaceIndex ↥K ↥M → ℍ → ℂ := fun i => ((bM i : ↥M) : ℍ → ℂ)
    with he_def
  have he_mem : ∀ i, e i ∈ M := fun i => (bM i : ↥M).2
  have he_inj : Function.Injective e := Subtype.val_injective.comp bM.injective
  have halg : ∀ (a : ↥K) (f : ℍ → ℂ), a • f = (a : ℂ) • f := fun a f => rfl

  have heK : LinearIndependent ↥K e :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)

  have heC : LinearIndependent ℂ e := by
    rw [← linearIndepOn_id_range_iff he_inj]
    refine linearIndepOn_of_finite _ fun t htsub htfin => ?_
    have hcoe : (↑htfin.toFinset : Set (ℍ → ℂ)) = t := htfin.coe_toFinset
    have hsM : (↑htfin.toFinset : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) := by
      rw [hcoe]
      intro w hw
      obtain ⟨j, rfl⟩ := htsub hw
      exact he_mem j
    have hsK : LinearIndependent ↥K
        (fun w : ↥(↑htfin.toFinset : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) := by
      have h2 : LinearIndepOn ↥K id t := heK.linearIndepOn_id.mono htsub
      show LinearIndepOn ↥K id (↑htfin.toFinset : Set (ℍ → ℂ))
      rwa [hcoe]
    have h3 := hflat htfin.toFinset hsM hsK
    show LinearIndepOn ℂ id t
    rw [← hcoe]
    exact h3

  have hM_rep : ∀ (m : ℍ → ℂ) (hm : m ∈ M)
      (S : Finset (Module.Basis.ofVectorSpaceIndex ↥K ↥M)), (bM.repr ⟨m, hm⟩).support ⊆ S →
      m = ∑ i ∈ S, ((bM.repr ⟨m, hm⟩ i : ℂ)) • e i := by
    intro m hm S hS
    have h1 := bM.linearCombination_repr ⟨m, hm⟩
    have h2 := congrArg (fun z : ↥M => (z : ℍ → ℂ)) h1
    simp only [Finsupp.linearCombination_apply] at h2
    rw [Finsupp.sum_of_support_subset (bM.repr ⟨m, hm⟩) hS (fun i a => a • bM i)
      (fun i _ => by simp)] at h2
    conv_lhs => rw [← h2]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, halg]

  have hext : ∀ (S' S : Finset (Module.Basis.ofVectorSpaceIndex ↥K ↥M)) (_ : S' ⊆ S)
      (a : Module.Basis.ofVectorSpaceIndex ↥K ↥M → ℂ),
      (∑ i ∈ S', a i • e i) = ∑ i ∈ S, (if i ∈ S' then a i else 0) • e i := by
    intro S' S hsub a
    rw [← Finset.sum_subset hsub (fun i _ hi => by rw [ite_eq_right hi, zero_smul])]
    exact Finset.sum_congr rfl fun i hi => by rw [ite_eq_left hi]

  have hwellDefE : ∀ (S₁ S₂ : Finset ↥(Module.Basis.ofVectorSpaceIndex ↥K ↥M))
      (a₁ a₂ : ↥(Module.Basis.ofVectorSpaceIndex ↥K ↥M) → ℂ),
      (∑ i ∈ S₁, a₁ i • e i) = (∑ i ∈ S₂, a₂ i • e i) →
      (∑ i ∈ S₁, σ (a₁ i) • e i) = (∑ i ∈ S₂, σ (a₂ i) • e i) := by
    intro S₁ S₂ a₁ a₂ hEq
    set S := S₁ ∪ S₂ with hS_def
    rw [hext S₁ S Finset.subset_union_left a₁,
      hext S₂ S Finset.subset_union_right a₂] at hEq
    have hdiff : (∑ i ∈ S, ((if i ∈ S₁ then a₁ i else 0) - (if i ∈ S₂ then a₂ i else 0)) • e i)
        = 0 := by
      have h1 : ∀ i ∈ S, ((if i ∈ S₁ then a₁ i else 0) - (if i ∈ S₂ then a₂ i else 0)) • e i =
          (if i ∈ S₁ then a₁ i else 0) • e i - (if i ∈ S₂ then a₂ i else 0) • e i :=
        fun i _ => sub_smul _ _ _
      rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hEq, sub_self]
    have hcoords := linearIndependent_iff'.mp heC S
      (fun i => (if i ∈ S₁ then a₁ i else 0) - (if i ∈ S₂ then a₂ i else 0)) hdiff
    rw [hext S₁ S Finset.subset_union_left (fun i => σ (a₁ i)),
      hext S₂ S Finset.subset_union_right (fun i => σ (a₂ i))]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hbi := sub_eq_zero.mp (hcoords i hi)
    by_cases h1 : i ∈ S₁ <;> by_cases h2 : i ∈ S₂ <;>
      simp only [h1, h2, ite_true, ite_false] at hbi ⊢
    · rw [hbi]
    · rw [hbi, map_zero, zero_smul]
    · rw [← hbi, map_zero, zero_smul]

  have hfam_rep : ∀ (ι' : Type) (_ : Fintype ι') (c : ι' → ℂ)
      (f : ι' → ℍ → ℂ) (hf : ∀ j, f j ∈ M),
      ∃ (S : Finset ↥(Module.Basis.ofVectorSpaceIndex ↥K ↥M))
        (A : ↥(Module.Basis.ofVectorSpaceIndex ↥K ↥M) → ℂ),
        (∑ j, c j • f j) = (∑ i ∈ S, A i • e i) ∧
        (∑ j, σ (c j) • f j) = (∑ i ∈ S, σ (A i) • e i) := by
    intro ι' _ c f hf
    set L : ι' → Module.Basis.ofVectorSpaceIndex ↥K ↥M →₀ ↥K := fun j => bM.repr ⟨f j, hf j⟩
      with hL_def
    set S := Finset.univ.biUnion fun j : ι' => (L j).support with hS_def
    have hfj : ∀ j, f j = ∑ i ∈ S, ((L j i : ℂ)) • e i := fun j =>
      hM_rep (f j) (hf j) S
        (Finset.subset_biUnion_of_mem (fun j' : ι' => (L j').support) (Finset.mem_univ j))
    have hassemble : ∀ (g : ι' → ℂ),
        (∑ j, g j • f j) = ∑ i ∈ S, (∑ j, g j * (L j i : ℂ)) • e i := by
      intro g
      calc ∑ j, g j • f j = ∑ j, ∑ i ∈ S, (g j * (L j i : ℂ)) • e i := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hfj j, Finset.smul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]
        _ = ∑ i ∈ S, (∑ j, g j * (L j i : ℂ)) • e i := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_smul]
    refine ⟨S, fun i => ∑ j, c j * (L j i : ℂ), hassemble c, ?_⟩
    rw [hassemble (fun j => σ (c j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    congr 1
    exact (σ.commutes ((L j) i)).symm

  have hwellDefFam : ∀ (ι₁ : Type) (_ : Fintype ι₁) (c₁ : ι₁ → ℂ)
      (f₁ : ι₁ → ℍ → ℂ) (hf₁ : ∀ j, f₁ j ∈ M) (ι₂ : Type) (_ : Fintype ι₂) (c₂ : ι₂ → ℂ)
      (f₂ : ι₂ → ℍ → ℂ) (hf₂ : ∀ j, f₂ j ∈ M),
      (∑ j, c₁ j • f₁ j) = (∑ j, c₂ j • f₂ j) →
      (∑ j, σ (c₁ j) • f₁ j) = (∑ j, σ (c₂ j) • f₂ j) := by
    intro ι₁ h₁ c₁ f₁ hf₁ ι₂ h₂ c₂ f₂ hf₂ hEq
    obtain ⟨S₁, A₁, hA₁, hA₁'⟩ := hfam_rep ι₁ h₁ c₁ f₁ hf₁
    obtain ⟨S₂, A₂, hA₂, hA₂'⟩ := hfam_rep ι₂ h₂ c₂ f₂ hf₂
    rw [hA₁', hA₂']
    exact hwellDefE S₁ S₂ A₁ A₂ (by rw [← hA₁, ← hA₂, hEq])

  have hrep_span : ∀ v : ℍ → ℂ, v ∈ Submodule.span ℂ (M : Set (ℍ → ℂ)) →
      ∃ (s : Finset (ℍ → ℂ)) (c : (ℍ → ℂ) → ℂ),
        (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) ∧ v = ∑ w ∈ s, c w • w := by
    intro v₀ hvs
    obtain ⟨T₀, hT₀M, hvT₀⟩ := Submodule.mem_span_finite_of_mem_span hvs
    obtain ⟨cf, hcf⟩ := Submodule.mem_span_finset.mp hvT₀
    exact ⟨T₀, cf, hT₀M, hcf.2.symm⟩

  set T : (ℍ → ℂ) → (ℍ → ℂ) := fun w =>
    if h : w ∈ Submodule.span ℂ (M : Set (ℍ → ℂ)) then
      ∑ u ∈ (hrep_span w h).choose, σ ((hrep_span w h).choose_spec.choose u) • u
    else 0 with hT_def

  have hattach : ∀ (s : Finset (ℍ → ℂ)) (g : (ℍ → ℂ) → ℂ),
      (∑ w ∈ s, g w • w) = ∑ j : ↥s, g (j : ℍ → ℂ) • (j : ℍ → ℂ) := by
    intro s g
    rw [Finset.sum_coe_sort s (fun w => g w • w)]
  have hchosen_twist : ∀ (w : ℍ → ℂ)
      (h : w ∈ Submodule.span ℂ (M : Set (ℍ → ℂ)))
      (ι' : Type) (_ : Fintype ι') (c : ι' → ℂ) (f : ι' → ℍ → ℂ) (hf : ∀ j, f j ∈ M),
      w = (∑ j, c j • f j) → T w = ∑ j, σ (c j) • f j := by
    intro w h ι' hfin c f hf hw
    obtain ⟨hsM', hseq'⟩ := (hrep_span w h).choose_spec.choose_spec
    simp only [hT_def, dite_eq_left h]
    rw [hattach _ (fun u => σ ((hrep_span w h).choose_spec.choose u))]
    refine hwellDefFam _ _ _ _ (fun j => hsM' j.2) ι' hfin c f hf ?_
    rw [← hattach _ ((hrep_span w h).choose_spec.choose), ← hseq', ← hw]

  refine ⟨T, fun ι' hfin c f hf => ?_⟩
  have hmem : (∑ j, c j • f j) ∈ Submodule.span ℂ (M : Set (ℍ → ℂ)) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hf j))
  exact hchosen_twist _ hmem ι' hfin c f hf rfl

/-! ### Order 1, leaf 4: the abstract descent -/

private theorem descent_core {k K E : Type*} [Field k] [Field K] [Algebra k K] [AddCommGroup E]
    [Module K E] {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → E)
    (V : Submodule K E) (P : ι → Prop) [DecidablePred P] (hP : ∀ i, P i → e i ∈ V)
    (key : ∀ a : ι → k, (∑ i, algebraMap k K (a i) • e i) ∈ V → ∀ i, ¬ P i → a i = 0)
    (T : (K ≃ₐ[k] K) → E → E)
    (hT : ∀ (σ : K ≃ₐ[k] K) (c : ι → K), T σ (∑ i, c i • e i) = ∑ i, σ (c i) • e i)
    (hTV : ∀ σ, ∀ v ∈ V, T σ v ∈ V)
    (G1 : ∀ c : K, (∀ σ : K ≃ₐ[k] K, σ c = c) → ∃ a : k, algebraMap k K a = c)
    (c : ι → K) (hc : (∑ i, c i • e i) ∈ V) : ∀ i, ¬ P i → c i = 0 := by
  classical
  suffices h : ∀ (n : ℕ) (c : ι → K),
      (Finset.univ.filter fun i ↦ ¬ P i ∧ c i ≠ 0).card ≤ n → (∑ i, c i • e i) ∈ V →
        ∀ i, ¬ P i → c i = 0 from h _ c le_rfl hc
  intro n
  induction n with
  | zero =>
    intro c hn hc i hi
    by_contra h
    have : i ∈ Finset.univ.filter fun i ↦ ¬ P i ∧ c i ≠ 0 := by simp [hi, h]
    rw [Nat.le_zero, Finset.card_eq_zero] at hn
    simp [hn] at this
  | succ n ih =>
    intro c hn hc
    by_contra hex
    push Not at hex
    obtain ⟨i₀, hi₀, hci₀⟩ := hex
    set c' : ι → K := fun i ↦ (c i₀)⁻¹ * c i with hc'def
    have hc' : (∑ i, c' i • e i) ∈ V := by
      have : (∑ i, c' i • e i) = (c i₀)⁻¹ • ∑ i, c i • e i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul]
      rw [this]; exact V.smul_mem _ hc
    have hc'i₀ : c' i₀ = 1 := inv_mul_cancel₀ hci₀
    have hc'supp : ∀ i, c' i ≠ 0 → c i ≠ 0 := fun i h h0 ↦ h (by simp [hc'def, h0])
    have hfix : ∀ (σ : K ≃ₐ[k] K) (i : ι), ¬ P i → σ (c' i) = c' i := by
      intro σ
      set d : ι → K := fun i ↦ σ (c' i) - c' i with hddef
      have hd : (∑ i, d i • e i) ∈ V := by
        have : (∑ i, d i • e i) = T σ (∑ i, c' i • e i) - ∑ i, c' i • e i := by
          rw [hT, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [sub_smul]
        rw [this]; exact V.sub_mem (hTV σ _ hc') hc'
      have hsub : (Finset.univ.filter fun i ↦ ¬ P i ∧ d i ≠ 0) ⊆
          (Finset.univ.filter fun i ↦ ¬ P i ∧ c i ≠ 0).erase i₀ := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [Finset.mem_erase, Finset.mem_filter]
        refine ⟨?_, Finset.mem_univ _, hi.1, hc'supp i fun h0 ↦ hi.2 (by simp [hddef, h0])⟩
        rintro rfl
        exact hi.2 (by simp [hddef, hc'i₀])
      have hcard : (Finset.univ.filter fun i ↦ ¬ P i ∧ d i ≠ 0).card ≤ n := by
        have h1 := Finset.card_le_card hsub
        have h2 : i₀ ∈ Finset.univ.filter fun i ↦ ¬ P i ∧ c i ≠ 0 := by simp [hi₀, hci₀]
        rw [Finset.card_erase_of_mem h2] at h1
        omega
      intro i hi
      exact sub_eq_zero.mp (ih d hcard hd i hi)
    have hk : ∀ i, ¬ P i → ∃ a : k, algebraMap k K a = c' i := fun i hi ↦
      G1 (c' i) fun σ ↦ hfix σ i hi
    choose a ha using hk
    let a' : ι → k := fun i ↦ if h : ¬ P i then a i h else 0
    have ha' : ∀ i, algebraMap k K (a' i) = if P i then 0 else c' i := by
      intro i
      by_cases h : P i
      · simp [a', h]
      · simp [a', h, ha i h]
    have hm : (∑ i, algebraMap k K (a' i) • e i) ∈ V := by
      have : (∑ i, algebraMap k K (a' i) • e i) =
          (∑ i, c' i • e i) - ∑ i, (if P i then c' i else 0) • e i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [ha', ← sub_smul]
        by_cases h : P i <;> simp [h]
      rw [this]
      refine V.sub_mem hc' (V.sum_mem fun i _ ↦ ?_)
      by_cases h : P i
      · simp only [h, ite_true]; exact V.smul_mem _ (hP i h)
      · simp [h]
    have := key a' hm i₀ hi₀
    have h1 : algebraMap k K (a' i₀) = 1 := by rw [ha', ite_eq_right hi₀, hc'i₀]
    rw [this, map_zero] at h1
    exact zero_ne_one h1

private theorem descent_generic {k K E : Type*} [Field k] [Field K] [Algebra k K] [AddCommGroup E]
    [Module K E] [Module k E] [IsScalarTower k K E] (M : Submodule k E) (V : Submodule K E)
    (hVle : V ≤ Submodule.span K (M : Set E))
    (T : (K ≃ₐ[k] K) → E → E)
    (hT : ∀ (σ : K ≃ₐ[k] K) (ι : Type) [Fintype ι] (c : ι → K) (e : ι → E), (∀ i, e i ∈ M) →
      T σ (∑ i, c i • e i) = ∑ i, σ (c i) • e i)
    (hTV : ∀ σ, ∀ v ∈ V, T σ v ∈ V)
    (G1 : ∀ c : K, (∀ σ : K ≃ₐ[k] K, σ c = c) → ∃ a : k, algebraMap k K a = c)
    {v : E} (hv : v ∈ V) : v ∈ Submodule.span K {y : E | y ∈ V ∧ y ∈ M} := by
  classical
  obtain ⟨T₀, hTM, hvT⟩ := Submodule.mem_span_finite_of_mem_span (hVle hv)
  set X : Submodule k E := Submodule.span k (T₀ : Set E)
  have hXM : X ≤ M := Submodule.span_le.mpr fun t ht ↦ hTM ht
  have : FiniteDimensional k ↥X := FiniteDimensional.span_of_finite _ T₀.finite_toSet
  let U : Submodule k ↥X := (V.restrictScalars k).comap X.subtype
  obtain ⟨W, hUW⟩ := U.exists_isCompl
  let bU := Module.finBasis k ↥U
  let bW := Module.finBasis k ↥W
  let ι := Fin (Module.finrank k ↥U) ⊕ Fin (Module.finrank k ↥W)
  let eX : ι → ↥X := Sum.elim (fun i ↦ (bU i : ↥X)) (fun j ↦ (bW j : ↥X))
  let e : ι → E := fun i ↦ (eX i : E)
  let P : ι → Prop := fun i ↦ Sum.isLeft i
  have heM : ∀ i, e i ∈ M := fun i ↦ hXM (eX i).2
  have hP : ∀ i, P i → e i ∈ V := by
    rintro (i | j) h
    · exact (bU i).2
    · simp [P] at h
  have key : ∀ a : ι → k, (∑ i, algebraMap k K (a i) • e i) ∈ V → ∀ i, ¬ P i → a i = 0 := by
    intro a ha
    have hsum : (∑ i, algebraMap k K (a i) • e i) = ((∑ i, a i • eX i : ↥X) : E) := by
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Submodule.coe_smul, algebraMap_smul]
    have hxU : (∑ i, a i • eX i : ↥X) ∈ U := by
      change ((∑ i, a i • eX i : ↥X) : E) ∈ V
      rw [← hsum]; exact ha
    rw [Fintype.sum_sum_type] at hxU
    have hu : (∑ i, a (Sum.inl i) • eX (Sum.inl i) : ↥X) ∈ U :=
      U.sum_mem fun i _ ↦ U.smul_mem _ (bU i).2
    have hw : (∑ j, a (Sum.inr j) • eX (Sum.inr j) : ↥X) ∈ W :=
      W.sum_mem fun j _ ↦ W.smul_mem _ (bW j).2
    have hwU : (∑ j, a (Sum.inr j) • eX (Sum.inr j) : ↥X) ∈ U := by
      have := U.sub_mem hxU hu
      rwa [add_sub_cancel_left] at this
    have hw0 : (∑ j, a (Sum.inr j) • eX (Sum.inr j) : ↥X) = 0 :=
      Submodule.disjoint_def.mp hUW.disjoint _ hwU hw
    have hw0' : (∑ j, a (Sum.inr j) • (bW j : ↥W)) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero, ← hw0]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Submodule.coe_smul]; rfl
    have hlin := Fintype.linearIndependent_iff.mp bW.linearIndependent (fun j ↦ a (Sum.inr j))
      hw0'
    rintro (i | j) h
    · simp [P] at h
    · exact hlin j
  have hT' : ∀ (σ : K ≃ₐ[k] K) (c : ι → K), T σ (∑ i, c i • e i) = ∑ i, σ (c i) • e i :=
    fun σ c ↦ hT σ ι c e heM
  have hTe : ∀ t ∈ T₀, t ∈ Submodule.span K (Set.range e) := by
    intro t ht
    have htX : t ∈ X := Submodule.subset_span ht
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp
      (hUW.sup_eq_top ▸ Submodule.mem_top (x := (⟨t, htX⟩ : ↥X)))
    have ht' : t = ((u : ↥X) : E) + ((w : ↥X) : E) := by
      rw [← Submodule.coe_add, huw]
    rw [ht']
    refine Submodule.add_mem _ ?_ ?_
    · have hrepr := bU.sum_repr ⟨u, hu⟩
      have : (u : E) = ∑ i, algebraMap k K (bU.repr ⟨u, hu⟩ i) • e (Sum.inl i) := by
        have := congrArg (fun z : ↥U ↦ ((z : ↥X) : E)) hrepr
        simp only at this
        rw [← this, Submodule.coe_sum, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Submodule.coe_smul, Submodule.coe_smul, algebraMap_smul]
        rfl
      rw [this]
      exact Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    · have hrepr := bW.sum_repr ⟨w, hw⟩
      have : (w : E) = ∑ j, algebraMap k K (bW.repr ⟨w, hw⟩ j) • e (Sum.inr j) := by
        have := congrArg (fun z : ↥W ↦ ((z : ↥X) : E)) hrepr
        simp only at this
        rw [← this, Submodule.coe_sum, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Submodule.coe_smul, Submodule.coe_smul, algebraMap_smul]
        rfl
      rw [this]
      exact Submodule.sum_mem _ fun j _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  have hve : v ∈ Submodule.span K (Set.range e) := (Submodule.span_le.mpr hTe) hvT
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hve
  have hzero := descent_core e V P hP key T hT' hTV G1 c hv
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rcases i with i | j
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hP _ rfl, heM _⟩)
  · rw [hzero (Sum.inr j) (by simp [P]), zero_smul]; exact Submodule.zero_mem _

/-! ### Order 1, leaf 4 continued: the twist-stable span -/

theorem span_inter_rational_of_twist_stable (K : IntermediateField ℚ ℂ)
    (M : Submodule ↥K (ℍ → ℂ))
    (hflat : ∀ s : Finset (ℍ → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) →
      LinearIndependent ↥K (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)) →
      LinearIndependent ℂ (fun w : ↥(↑s : Set (ℍ → ℂ)) => (w : ℍ → ℂ)))
    (V : Submodule ℂ (ℍ → ℂ))
    (hVle : V ≤ Submodule.span ℂ (M : Set (ℍ → ℂ)))
    (hstab : ∀ (σ : ℂ ≃ₐ[↥K] ℂ) (v : ℍ → ℂ), v ∈ V →
      ∃ (s : Finset (ℍ → ℂ)) (c : (ℍ → ℂ) → ℂ), (↑s : Set (ℍ → ℂ)) ⊆ (M : Set (ℍ → ℂ)) ∧
        v = ∑ w ∈ s, c w • w ∧ (∑ w ∈ s, σ (c w) • w) ∈ V)
    (G1 : ∀ c : ℂ, (∀ σ : ℂ ≃ₐ[↥K] ℂ, σ c = c) → ∃ a : ↥K, algebraMap ↥K ℂ a = c)
    {v : ℍ → ℂ} (hv : v ∈ V) :
    v ∈ Submodule.span ℂ {y : ℍ → ℂ | y ∈ V ∧ y ∈ M} := by
  classical
  choose T hT using fun σ => exists_twist_of_flat K M hflat σ
  have hattach : ∀ (s : Finset (ℍ → ℂ)) (g : (ℍ → ℂ) → ℂ),
      (∑ w ∈ s, g w • w) = ∑ j : ↥s, g (j : ℍ → ℂ) • (j : ℍ → ℂ) := by
    intro s g
    rw [Finset.sum_coe_sort s (fun w => g w • w)]
  have hTV : ∀ σ, ∀ w ∈ V, T σ w ∈ V := by
    intro σ w hw
    obtain ⟨s, c, hsM', hweq, htw⟩ := hstab σ w hw
    have h1 : T σ w = ∑ j : ↥s, σ (c (j : ℍ → ℂ)) • (j : ℍ → ℂ) := by
      rw [show w = ∑ j : ↥s, c (j : ℍ → ℂ) • (j : ℍ → ℂ) by rw [hweq, hattach s c]]
      exact hT σ ↥s (fun j => c (j : ℍ → ℂ)) (fun j => (j : ℍ → ℂ))
        (fun j => hsM' j.2)
    rw [h1, ← hattach s (fun u => σ (c u))]
    exact htw
  exact descent_generic M V hVle T (fun σ ι _ c f hf => hT σ ι c f hf) hTV G1 hv

end WLight
