/-
  Haar averaging over an open subgroup, the scaling decomposition, and the uniqueness of an
  invariant measure.

  Four leaves of the analytic floor of the D–S shelf, all of them statements about a measure on
  a group and the averaging it performs:

  * `exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup` — on a compact group with a Haar
    probability measure, an open subgroup `H` has finite index `n`, the `n` cosets are picked by
    representatives `r : Fin n → K`, and a function invariant under right multiplication by `H`
    integrates to `n⁻¹ * ∑ i, h (r i)`: the integral is the average over the quotient;
  * `lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul` — if a measurable
    equivalence `T` scales `ν` by `κ` and raises a level function `m` by one, an invariant `h`
    splits the `lintegral` of `h * Φ ∘ m` into the geometric series `∑ n, κ ^ n * Φ n` times the
    `lintegral` of `h` over the level `m = 0`;
  * `measure_biUnion_finset_image_mul_right_lt_top` — a finite union of right translates of a
    finite-measure set by `IsMulRightInvariant μ` is again of finite measure;
  * `Measure.exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer` — a
    pretransitive continuous action of a locally compact, second countable group on a locally
    compact space, with compact stabilizer at `x₀` and a finite-on-compacts measure `σ` invariant
    under the action, is a scalar multiple of the pushforward of the Haar measure along
    `g ↦ g • x₀`. The engine is the fibre average over the stabilizer.

  Transcribed from the D–S shelf's `MeasureTheory` leaves (pinned `aa2d8b34`), rows 4–7 of the
  order, from
  `S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup.lean`,
  `S_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul.lean`,
  `S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top.lean` and
  `S_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer.lean`.
  Generic measure theory on a topological group, so its home is `MeasureTheory/` (playbook §3.1);
  the pin's generation namespaces are dropped and the statements stay the pin's, the last one in
  the pin's own `MeasureTheory.Measure` namespace.

  spec-pin: P2M/Sol/S_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup.lean
  spec-pin: P2M/Sol/S_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul.lean
  spec-pin: P2M/Sol/S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top.lean
  spec-pin: P2M/Sol/S_MeasureTheory_Measure_exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer.lean
-/
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal BigOperators

namespace MeasureTheory

theorem exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (H : Subgroup K) (hH : IsOpen (H : Set K)) :
    ∃ (n : ℕ) (r : Fin n → K), H.index = n ∧ 0 < n ∧
      (∀ v : K, ∃ i, (r i)⁻¹ * v ∈ H) ∧
      (∀ i j, (r i)⁻¹ * r j ∈ H → i = j) ∧
      ∀ h : K → ℂ, (∀ v : K, ∀ w ∈ H, h (v * w) = h v) →
        ∫ v, h v ∂μ = (n : ℂ)⁻¹ * ∑ i, h (r i) := by
  classical
  have : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  have : Fintype (K ⧸ H) := Fintype.ofFinite _
  have : DiscreteTopology (K ⧸ H) := QuotientGroup.discreteTopology hH
  set n := Fintype.card (K ⧸ H) with hn
  let e : Fin n ≃ K ⧸ H := (Fintype.equivFin _).symm
  let r : Fin n → K := fun i => (e i).out
  have hr : ∀ i, (QuotientGroup.mk (r i) : K ⧸ H) = e i := fun i => QuotientGroup.out_eq' (e i)

  let σ : K → Fin n := fun v => e.symm (QuotientGroup.mk v)
  have hσ : ∀ v, (r (σ v))⁻¹ * v ∈ H := fun v => by
    rw [← QuotientGroup.eq, hr, Equiv.apply_symm_apply]
  have hn0 : 0 < n := Fintype.card_pos
  have hidx : H.index = n := by
    rw [Subgroup.index, Nat.card_eq_fintype_card]
  refine ⟨n, r, hidx, hn0, fun v => ⟨σ v, hσ v⟩, ?_, ?_⟩
  · intro i j hij
    apply e.injective
    rw [← hr, ← hr]
    exact QuotientGroup.eq.mpr hij

  let A : Fin n → Set K := fun i => σ ⁻¹' {i}
  have hσc : Continuous σ :=
    continuous_of_discreteTopology.comp (QuotientGroup.continuous_mk (N := H))
  have hAm : ∀ i, MeasurableSet (A i) := fun i =>
    ((isOpen_discrete ({i} : Set (Fin n))).preimage hσc).measurableSet

  have hA : ∀ i, A i = (fun v => (r i)⁻¹ * v) ⁻¹' (H : Set K) := fun i => by
    ext v
    simp only [A, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · rintro rfl; exact hσ v
    · intro hv
      apply e.injective
      rw [Equiv.apply_symm_apply, ← hr]
      exact (QuotientGroup.eq.mpr hv).symm
  have hμA : ∀ i, μ (A i) = μ H := fun i => by
    rw [hA]; exact measure_preimage_mul μ (r i)⁻¹ _

  have hsum : ∑ i, μ (A i) = 1 := by
    have hdisj : Pairwise (Function.onFun Disjoint A) := fun i j hij =>
      Set.disjoint_iff.mpr fun v ⟨hi, hj⟩ => hij (hi.symm.trans hj)
    have h1 : μ (⋃ i, A i) = ∑' i, μ (A i) := measure_iUnion hdisj hAm
    rw [tsum_fintype] at h1
    rw [← h1, ← measure_univ (μ := μ)]
    congr 1; ext v; simp [A]
  have hμH : μ (H : Set K) = 1 / (n : ENNReal) := by
    simp only [hμA, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    exact (ENNReal.eq_div_iff (by exact_mod_cast hn0.ne') (ENNReal.natCast_ne_top n)).mpr hsum
  have hμrA : ∀ i, μ.real (A i) = (n : ℝ)⁻¹ := fun i => by
    rw [measureReal_def, hμA, hμH, one_div, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  intro h hh

  have hconst : ∀ v, h v = ∑ i, (A i).indicator (fun _ => h (r i)) v := fun v => by
    rw [Finset.sum_eq_single (σ v)]
    · rw [Set.indicator_of_mem (by simp [A])]
      conv_lhs => rw [show v = r (σ v) * ((r (σ v))⁻¹ * v) by group]
      exact hh _ _ (hσ v)
    · intro i _ hi
      exact Set.indicator_of_notMem (by simpa [A] using fun h' => hi h'.symm) _
    · simp
  calc ∫ v, h v ∂μ = ∫ v, ∑ i, (A i).indicator (fun _ => h (r i)) v ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hconst)
    _ = ∑ i, ∫ v, (A i).indicator (fun _ => h (r i)) v ∂μ :=
        integral_finsetSum _ fun i _ => (integrable_const _).indicator (hAm i)
    _ = ∑ i, (μ.real (A i)) • h (r i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact integral_indicator_const _ (hAm i)
    _ = (n : ℂ)⁻¹ * ∑ i, h (r i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hμrA, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul
    {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) (T : Q ≃ᵐ Q)
    (κ : ℝ≥0∞) (hκ₀ : κ ≠ 0) (hκ : κ ≠ ∞)
    (hT : ∀ s : Set Q, MeasurableSet s → ν (T '' s) = κ * ν s)
    (m : Q → ℤ) (hm : Measurable m) (hmT : ∀ q, m (T q) = m q + 1)
    (h : Q → ℝ≥0∞) (hh : Measurable h) (hhT : ∀ q, h (T q) = h q)
    (Φ : ℤ → ℝ≥0∞) :
    ∫⁻ q, h q * Φ (m q) ∂ν = (∑' n : ℤ, κ ^ n * Φ n) * ∫⁻ q in {q | m q = 0}, h q ∂ν := by
  set A : ℤ → Set Q := fun n => {q | m q = n} with hA_def
  have hA : ∀ n, MeasurableSet (A n) := fun n => hm (measurableSet_singleton n)
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun q hqi hqj => hij ?_
    rw [hA_def] at hqi hqj
    exact hqi.symm.trans hqj
  have hunion : (⋃ n, A n) = Set.univ := by
    ext q; simp [hA_def]

  have hmap : ν.map T.symm = κ • ν := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply T.symm.measurable hs, Measure.smul_apply, smul_eq_mul, ← hT s hs,
      MeasurableEquiv.image_eq_preimage_symm]

  have hAsucc : ∀ n, A (n + 1) = T.symm ⁻¹' (A n) := by
    intro n; ext q
    simp only [hA_def, Set.mem_ofPred_eq, Set.mem_preimage]
    have := hmT (T.symm q)
    rw [MeasurableEquiv.apply_symm_apply] at this
    rw [this]; exact add_left_inj 1

  have hhS : ∀ q, h (T.symm q) = h q := fun q => by
    conv_rhs => rw [← MeasurableEquiv.apply_symm_apply T q]
    exact (hhT _).symm

  set I : ℤ → ℝ≥0∞ := fun n => ∫⁻ q in A n, h q ∂ν with hI_def
  have hstep : ∀ n, I (n + 1) = κ * I n := by
    intro n
    simp only [hI_def]
    rw [hAsucc]
    calc ∫⁻ q in T.symm ⁻¹' A n, h q ∂ν
        = ∫⁻ q in T.symm ⁻¹' A n, h (T.symm q) ∂ν := by simp_rw [hhS]
      _ = ∫⁻ q in A n, h q ∂(ν.map T.symm) :=
          (setLIntegral_map (hA n) hh T.symm.measurable).symm
      _ = κ * ∫⁻ q in A n, h q ∂ν := by
          rw [hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]

  have hI : ∀ n : ℤ, I n = κ ^ n * I 0 := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
        rw [hstep, ih, ← mul_assoc, ENNReal.zpow_add hκ₀ hκ, zpow_one, mul_comm κ]
    | pred k ih =>
        have h1 : I (-(k : ℤ)) = κ * I (-(k : ℤ) - 1) := by
          rw [← hstep]; congr 1; ring
        have h2 : I (-(k : ℤ) - 1) = κ⁻¹ * I (-(k : ℤ)) := by
          rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hκ₀ hκ, one_mul]
        rw [h2, ih, ← mul_assoc, sub_eq_add_neg, ENNReal.zpow_add hκ₀ hκ, zpow_neg_one,
          mul_comm κ⁻¹]

  have hlevel : ∀ n, ∫⁻ q in A n, h q * Φ (m q) ∂ν = I n * Φ n := by
    intro n
    simp only [hI_def]
    rw [← lintegral_mul_const _ hh]
    refine setLIntegral_congr_fun (hA n) fun q hq => ?_
    rw [show m q = n from hq]
  have hsplit : ∫⁻ q, h q * Φ (m q) ∂ν = ∑' n, I n * Φ n := by
    rw [← setLIntegral_univ, ← hunion, lintegral_iUnion hA hdisj]
    exact tsum_congr hlevel
  rw [hsplit, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [hI n]
  simp only [hI_def, hA_def]
  ring

theorem measure_biUnion_finset_image_mul_right_lt_top
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant]
    (s : Set G) (hs : μ s < ⊤) (T : Finset G) :
    μ (⋃ x ∈ T, (· * x) '' s) < ⊤ := by
  refine lt_of_le_of_lt (measure_biUnion_finset_le T _) ?_
  refine ENNReal.sum_lt_top.mpr fun x _ => ?_
  have : (· * x) '' s = (· * x⁻¹) ⁻¹' s := by
    ext g; simp [Set.mem_preimage]
  rw [this, measure_preimage_mul_right]
  exact hs

namespace FibreAverage

open Set Filter Topology MulAction Measure

variable {L : Type*} [Group L] [MeasurableSpace L]

/-- The fibre average of a measure `μS` on a subgroup `S ≤ L` along the orbit of `l`: the mass,
under `μS`, of the fibre over `A` of the map `t ↦ l * t`. -/
noncomputable def fib {S : Subgroup L} (μS : Measure S) (A : Set L) (l : L) : ℝ≥0∞ :=
  μS ((fun t : S => l * (t : L)) ⁻¹' A)

lemma fib_def {S : Subgroup L} (μS : Measure S) (A : Set L) (l : L) :
    fib μS A l = μS ((fun t : S => l * (t : L)) ⁻¹' A) := rfl

lemma measurable_coe_mul [TopologicalSpace L] [IsTopologicalGroup L] [BorelSpace L]
    (S : Subgroup L) (l : L) : Measurable (fun t : S => l * (t : L)) :=
  (continuous_const.mul continuous_subtype_val).measurable

lemma measurable_fib [TopologicalSpace L] [IsTopologicalGroup L] [BorelSpace L]
    [SecondCountableTopology L] {S : Subgroup L} (μS : Measure S) [SFinite μS]
    {A : Set L} (hA : MeasurableSet A) : Measurable (fib μS A) := by
  have hm : MeasurableSet ((fun p : L × S => p.1 * (p.2 : L)) ⁻¹' A) :=
    (measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)) hA
  exact measurable_measure_prodMk_left hm

lemma fib_mul_coe [TopologicalSpace L] [IsTopologicalGroup L] [BorelSpace L] {S : Subgroup L} (μS : Measure S) [μS.IsMulLeftInvariant] (A : Set L)
    (l : L) (s : S) : fib μS A (l * (s : L)) = fib μS A l := by
  unfold fib
  have : (fun t : S => l * (s : L) * (t : L)) ⁻¹' A =
      (fun t : S => s * t) ⁻¹' ((fun t : S => l * (t : L)) ⁻¹' A) := by
    ext t
    simp [mul_assoc]
  rw [this, measure_preimage_mul]

lemma lowerSemicontinuous_fib [TopologicalSpace L] [IsTopologicalGroup L] {S : Subgroup L} (μS : Measure S) [μS.Regular] {U : Set L}
    (hU : IsOpen U) : LowerSemicontinuous (fib μS U) := by
  intro l₀ c hc
  have hV : IsOpen ((fun t : S => l₀ * (t : L)) ⁻¹' U) :=
    hU.preimage (continuous_const.mul continuous_subtype_val)
  obtain ⟨K, hKV, hK, hcK⟩ := hV.exists_lt_isCompact hc
  have hK' : IsCompact ((fun t : S => l₀ * (t : L)) '' K) :=
    hK.image (continuous_const.mul continuous_subtype_val)
  have hsub : (fun t : S => l₀ * (t : L)) '' K ⊆ U := image_subset_iff.mpr hKV
  obtain ⟨V, hV1, hVU⟩ := compact_open_separated_mul_left hK' hU hsub
  have hev : ∀ᶠ l in 𝓝 l₀, K ⊆ (fun t : S => l * (t : L)) ⁻¹' U := by
    rw [← map_mul_right_nhds_one l₀, eventually_map]
    filter_upwards [hV1] with v hv
    intro t ht
    show v * l₀ * (t : L) ∈ U
    rw [mul_assoc]
    exact hVU (Set.mul_mem_mul hv (mem_image_of_mem _ ht))
  filter_upwards [hev] with l hl
  exact hcK.trans_le (measure_mono hl)

end FibreAverage

namespace Measure

open FibreAverage Set Filter Topology MulAction in
theorem exists_eq_smul_map_smul_of_forall_map_smul_eq_of_isCompact_stabilizer
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L] [LocallyCompactSpace L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (μL : Measure L) [μL.IsHaarMeasure]
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MulAction L X] [ContinuousSMul L X] [MulAction.IsPretransitive L X]
    (x₀ : X) (hx₀ : IsCompact (MulAction.stabilizer L x₀ : Set L))
    (σ : Measure X) [IsFiniteMeasureOnCompacts σ]
    (hσ : ∀ g : L, σ.map (fun x : X => g • x) = σ) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ σ = c • μL.map (fun g : L => g • x₀) := by
  obtain ⟨S, hS⟩ : ∃ S : Subgroup L, S = MulAction.stabilizer L x₀ := ⟨_, rfl⟩
  have hmemS : ∀ {l : L}, l ∈ S ↔ l • x₀ = x₀ := by
    intro l; rw [hS, MulAction.mem_stabilizer_iff]
  have hScpt : IsCompact (S : Set L) := hS ▸ hx₀
  have : CompactSpace S := isCompact_iff_compactSpace.mp hScpt
  have hπc : Continuous (fun g : L => g • x₀) := by fun_prop
  have hπm : Measurable (fun g : L => g • x₀) := hπc.measurable
  have hSclosed : IsClosed (S : Set L) := by
    have : (S : Set L) = (fun g : L => g • x₀) ⁻¹' {x₀} := by
      ext l; simp [hmemS]
    rw [this]
    exact isClosed_singleton.preimage hπc
  have : LocallyCompactSpace S := hSclosed.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology (S : Set L)

  let K₀ : TopologicalSpace.PositiveCompacts S :=
    { carrier := univ, isCompact' := isCompact_univ, interior_nonempty' := by simp }
  let μS : Measure S := Measure.haarMeasure K₀
  have : IsProbabilityMeasure μS := ⟨by
    have h := Measure.haarMeasure_self (K₀ := K₀)
    exact h⟩

  have hπo : IsOpenMap (fun g : L => g • x₀) := isOpenMap_smul_of_sigmaCompact x₀
  choose sec hsec using fun x : X => MulAction.exists_smul_eq L x₀ x

  have hfib : ∀ (x : X) (t : S), (sec x * (t : L)) • x₀ = x := by
    intro x t
    rw [mul_smul, hmemS.mp t.2, hsec]

  have hF_eq : ∀ (A : Set L) (l l' : L), l • x₀ = l' • x₀ → fib μS A l = fib μS A l' := by
    intro A l l' h
    have hs : l⁻¹ * l' ∈ S := by
      rw [hmemS, mul_smul, ← h, inv_smul_smul]
    have : l' = l * ((⟨l⁻¹ * l', hs⟩ : S) : L) := by simp
    rw [this, fib_mul_coe]
  have hF_sec : ∀ (A : Set L) (l : L), fib μS A (sec (l • x₀)) = fib μS A l :=
    fun A l => hF_eq A _ _ (hsec _)

  have hG_open : ∀ U : Set L, IsOpen U → Measurable (fun x => fib μS U (sec x)) := by
    intro U hU
    apply LowerSemicontinuous.measurable
    rw [lowerSemicontinuous_iff_isOpen_preimage]
    intro c
    have hlsc := (lowerSemicontinuous_iff_isOpen_preimage.mp (lowerSemicontinuous_fib μS hU)) c
    have : (fun x => fib μS U (sec x)) ⁻¹' Ioi c = (fun g : L => g • x₀) '' (fib μS U ⁻¹' Ioi c) := by
      ext x
      constructor
      · intro hx
        exact ⟨sec x, hx, hsec x⟩
      · rintro ⟨l, hl, rfl⟩
        simp only [mem_preimage, mem_Ioi] at hl ⊢
        rwa [hF_sec]
    rw [this]
    exact hπo _ hlsc
  have hG : ∀ A : Set L, MeasurableSet A → Measurable (fun x => fib μS A (sec x)) := by
    intro A hA
    induction A, hA using MeasurableSpace.induction_on_inter
      (BorelSpace.measurable_eq (α := L)) isPiSystem_isOpen with
    | empty => simp [fib_def]
    | basic U hU => exact hG_open U hU
    | compl A hA ih =>
      have : (fun x => fib μS Aᶜ (sec x)) = fun x => 1 - fib μS A (sec x) := by
        funext x
        rw [fib_def, fib_def, preimage_compl, prob_compl_eq_one_sub ((measurable_coe_mul S _) hA)]
      rw [this]
      exact measurable_const.sub ih
    | iUnion f hdisj hfm ih =>
      have : (fun x => fib μS (⋃ i, f i) (sec x)) = fun x => ∑' i, fib μS (f i) (sec x) := by
        funext x
        rw [fib_def, preimage_iUnion, measure_iUnion]
        · rfl
        · exact fun i j hij => (hdisj hij).preimage _
        · exact fun i => (measurable_coe_mul S _) (hfm i)
      rw [this]
      exact Measurable.tsum ih

  let k : X → Measure L := fun x => μS.map (fun t : S => sec x * (t : L))
  have hk_apply : ∀ (x : X) (A : Set L), MeasurableSet A → k x A = fib μS A (sec x) :=
    fun x A hA => Measure.map_apply (measurable_coe_mul S _) hA
  have hk : Measurable k := by
    refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
    have : (fun x => k x A) = fun x => fib μS A (sec x) := funext fun x => hk_apply x A hA
    rw [this]
    exact hG A hA
  let ν : Measure L := σ.bind k
  have hν : ∀ A : Set L, MeasurableSet A → ν A = ∫⁻ x, fib μS A (sec x) ∂σ := by
    intro A hA
    rw [Measure.bind_apply hA hk.aemeasurable]
    exact lintegral_congr (fun x => hk_apply x A hA)

  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    have hK' : IsCompact (closure K) := hK.closure
    have hπK : IsCompact ((fun g : L => g • x₀) '' closure K) := hK'.image hπc
    refine (measure_mono subset_closure).trans_lt ?_
    rw [hν _ isClosed_closure.measurableSet]
    refine lt_of_le_of_lt ?_ (hπK.measure_lt_top (μ := σ))
    refine (lintegral_mono (fun x => ?_)).trans (lintegral_indicator_one_le _)
    by_cases hx : x ∈ (fun g : L => g • x₀) '' closure K
    · rw [indicator_of_mem hx, Pi.one_apply]
      exact prob_le_one
    · have : (fun t : S => sec x * (t : L)) ⁻¹' closure K = ∅ := by
        ext t
        simp only [mem_preimage, mem_empty_iff_false, iff_false]
        intro ht
        exact hx ⟨_, ht, hfib x t⟩
      rw [fib_def, this, measure_empty]
      exact zero_le⟩

  have : ν.IsMulLeftInvariant := ⟨fun g => by
    ext A hA
    have hgA : MeasurableSet ((fun h : L => g * h) ⁻¹' A) := (continuous_const_mul g).measurable hA
    rw [Measure.map_apply (continuous_const_mul g).measurable hA, hν _ hgA, hν A hA]
    have h1 : ∀ x, fib μS ((fun h : L => g * h) ⁻¹' A) (sec x) = fib μS A (sec (g • x)) := by
      intro x
      rw [show g • x = (g * sec x) • x₀ by rw [mul_smul, hsec], hF_sec]
      simp only [fib_def, preimage_preimage, mul_assoc]
    simp_rw [h1]
    calc ∫⁻ x, fib μS A (sec (g • x)) ∂σ
        = ∫⁻ x, fib μS A (sec x) ∂(σ.map (fun x : X => g • x)) :=
          (lintegral_map (hG A hA) (continuous_const_smul g).measurable).symm
      _ = ∫⁻ x, fib μS A (sec x) ∂σ := by rw [hσ g]⟩

  have hmap : ν.map (fun g : L => g • x₀) = σ := by
    ext B hB
    rw [Measure.map_apply hπm hB, hν _ (hπm hB)]
    have h1 : ∀ x, fib μS ((fun g : L => g • x₀) ⁻¹' B) (sec x) = B.indicator 1 x := by
      intro x
      by_cases hx : x ∈ B
      · have : (fun t : S => sec x * (t : L)) ⁻¹' ((fun g : L => g • x₀) ⁻¹' B) = univ := by
          ext t; simp [hfib x t, hx]
        rw [fib_def, this, measure_univ, indicator_of_mem hx, Pi.one_apply]
      · have : (fun t : S => sec x * (t : L)) ⁻¹' ((fun g : L => g • x₀) ⁻¹' B) = ∅ := by
          ext t; simp [hfib x t, hx]
        rw [fib_def, this, measure_empty, indicator_of_notMem hx]
    simp_rw [h1]
    exact lintegral_indicator_one hB

  obtain ⟨c, hc⟩ : ∃ c : NNReal, ν = c • μL :=
    ⟨Measure.haarScalarFactor ν μL, Measure.isMulLeftInvariant_eq_smul ν μL⟩
  refine ⟨(c : ℝ≥0∞), ENNReal.coe_ne_top, ?_⟩
  rw [← hmap, hc, Measure.map_smul]
  · ext s hs
    simp
  · exact hπm.aemeasurable

end Measure

end MeasureTheory
