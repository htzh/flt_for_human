/-
  A continuity-and-density criterion for Hecke characters.

  A continuous idèle-class character of a number field that takes the value `1`
  on the local uniformizer units outside a finite set `S` is trivial
  (`HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq`).  The proof
  approximates an arbitrary idèle by global units using two density statements:
  the diagonal image of `K` is dense in the product of finitely many finite
  completions with all archimedean ones, and a finite family of pairwise
  inequivalent nontrivial absolute values can be simultaneously approximated.

  Three leaves, transcribed from their pinned `Theorems/` wrappers with the
  bodies of their `P2M/Sol/` files, whole (`aa2d8b3`):

  * `AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv` (91 pin lines) —
    simultaneous approximation for pairwise inequivalent nontrivial absolute
    values;
  * `NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi`
    (140) — the diagonal `K → ∏_{v ∈ S} K_v × ∏_{w | ∞} K_w` has dense range
    (its helper namespace `P2mS26B6b` is kept verbatim);
  * `HeckeCharacter.eq_of_forall_apply_localUnit_uniformizerUnit_eq` (459) — the
    criterion itself, whose private helpers stay `private` in
    `namespace HeckeCharacter`.

  The gate `HeckeCharacter/FiniteOrder.lean` (this group's home of
  `Def_HeckeCharacter_FiniteOrder`) supplies `AdmitsModulus`/`idealMultiplicity`/
  `IsFiniteOrderHeckeChar`; `Def_NumberField_AdelicLevel` is the port's
  `NumberTheory/AdelicLevel/` split (`finIncl`, `localUnit`, `uniformizerUnit`,
  `isOpen_setOf_valued_le`, `adeleArch`/`adeleFin`, `archEval`) and is imported,
  never re-proved.

  Faithfulness and drift.  Statements are the wrappers' verbatim; proofs are the
  `S_` files' bodies; `solution` is not ported, the pin's `p2m_*` lines are
  dropped, and the pin's inner namespaces are kept verbatim (`P2mS26B6b`,
  `HeckeCharacter`).  The pin's `import Mathlib` becomes the named modules below.

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq.lean>

  spec-pin: Theorems/Thm_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.lean
  spec-pin: P2M/Sol/S_AbsoluteValue_exists_forall_sub_lt_of_pairwise_not_isEquiv.lean
  spec-pin: Theorems/Thm_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi.lean
  spec-pin: P2M/Sol/S_NumberField_denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi.lean
  spec-pin: Theorems/Thm_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq.lean
  spec-pin: P2M/Sol/S_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq.lean
-/

import FLTForHuman.HeckeCharacter.FiniteOrder
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Topology.Algebra.Valued.ValuedField

set_option autoImplicit false

noncomputable section

/-! ### Simultaneous approximation -/

namespace AbsoluteValue

theorem exists_forall_sub_lt_of_pairwise_not_isEquiv {K : Type*} [Field K] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue K ℝ} (hv : ∀ i, (v i).IsNontrivial)
    (hne : Pairwise fun i j => ¬(v i).IsEquiv (v j))
    (a : ι → K) {ε : ℝ} (hε : 0 < ε) : ∃ x : K, ∀ i, v i (x - a i) < ε := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun i => isEmptyElim i⟩
  have := Fintype.ofFinite ι

  choose b hb using fun i => AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv hv hne i
  have hb0 : ∀ i, b i ≠ 0 := by
    intro i h0
    have h1 := (hb i).1
    rw [h0, map_zero] at h1
    exact absurd h1 (by norm_num)

  set θ : ι → ℕ → K := fun i n => 1 / (1 + (b i)⁻¹ ^ n) with hθ
  have hθ0 : ∀ i j, j ≠ i → Filter.Tendsto (fun n => v j (θ i n)) Filter.atTop (nhds 0) := by
    intro i j hji
    have h1 : 1 < v j (b i)⁻¹ := by
      rw [map_inv₀, one_lt_inv₀ ((v j).pos (hb0 i))]
      exact (hb i).2 j hji
    exact AbsoluteValue.tendsto_div_one_add_pow_nhds_zero h1
  have hθ1 : ∀ i, Filter.Tendsto (fun n => v i (θ i n - 1)) Filter.atTop (nhds 0) := by
    intro i
    have h1 : 1 < v i (b i) := (hb i).1
    have hvinv : v i (b i)⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ h1
    have hlim : Filter.Tendsto (fun n => v i (1 / (1 + b i ^ n))) Filter.atTop (nhds 0) :=
      AbsoluteValue.tendsto_div_one_add_pow_nhds_zero h1
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn

    have hden : 1 + b i ^ n ≠ 0 := by
      intro h0
      have h2 : v i (b i ^ n) = 1 := by rw [eq_neg_of_add_eq_zero_right h0, (v i).map_neg, (v i).map_one]
      rw [map_pow] at h2
      have h3 : 1 < v i (b i) ^ n := one_lt_pow₀ h1 (by omega)
      linarith
    have hden' : 1 + (b i)⁻¹ ^ n ≠ 0 := by
      intro h0
      have h2 : v i ((b i)⁻¹ ^ n) = 1 := by rw [eq_neg_of_add_eq_zero_right h0, (v i).map_neg, (v i).map_one]
      rw [map_pow] at h2
      have h3 : v i (b i)⁻¹ ^ n < 1 := pow_lt_one₀ (apply_nonneg _ _) hvinv (by omega)
      linarith
    have hid : θ i n - 1 = -(1 / (1 + b i ^ n)) := by
      have h3 : b i ^ n + 1 ≠ 0 := by rwa [add_comm]
      have hcn : b i ^ n ≠ 0 := pow_ne_zero _ (hb0 i)
      have hden'' : 1 + (b i ^ n)⁻¹ ≠ 0 := by rwa [← inv_pow]
      have h4 : (b i ^ n)⁻¹ + 1 ≠ 0 := by rwa [add_comm]
      simp only [hθ]
      rw [inv_pow]
      field_simp
      ring
    rw [hid, (v i).map_neg]

  let xs : ℕ → K := fun n => ∑ i, θ i n * a i
  have hest : ∀ j n, v j (xs n - a j)
      ≤ v j (θ j n - 1) * v j (a j) + ∑ i ∈ Finset.univ.erase j, v j (θ i n) * v j (a i) := by
    intro j n
    have hsplit : xs n - a j = (θ j n - 1) * a j + ∑ i ∈ Finset.univ.erase j, θ i n * a i := by
      simp only [xs]
      rw [← Finset.add_sum_erase Finset.univ (fun i => θ i n * a i) (Finset.mem_univ j)]
      ring
    rw [hsplit]
    refine ((v j).add_le _ _).trans ?_
    rw [map_mul]
    refine add_le_add le_rfl ?_
    refine ((v j).sum_le _ _).trans ?_
    simp only [map_mul]
    exact le_rfl
  have hlim : ∀ j, Filter.Tendsto (fun n => v j (xs n - a j)) Filter.atTop (nhds 0) := by
    intro j
    have hR : Filter.Tendsto (fun n => v j (θ j n - 1) * v j (a j)
        + ∑ i ∈ Finset.univ.erase j, v j (θ i n) * v j (a i)) Filter.atTop (nhds 0) := by
      have h1 := (hθ1 j).mul_const (v j (a j))
      have h2 : Filter.Tendsto (fun n => ∑ i ∈ Finset.univ.erase j, v j (θ i n) * v j (a i))
          Filter.atTop (nhds (∑ i ∈ Finset.univ.erase j, 0 * v j (a i))) :=
        tendsto_finsetSum _ fun i hi => (hθ0 i j (Finset.ne_of_mem_erase hi).symm).mul_const _
      simpa using h1.add h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hR
      (fun n => apply_nonneg _ _) (fun n => hest j n)
  have hev : ∀ᶠ n in Filter.atTop, ∀ j, v j (xs n - a j) < ε :=
    Filter.eventually_all.2 fun j => (hlim j).eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨xs n, hn⟩

end AbsoluteValue

/-! ### Density of the diagonal in the finite completions times the infinite ones -/

namespace P2mS26B6b

open NumberField IsDedekindDomain

theorem norm_algebraMap_completion {K : Type*} [Field K] (w : InfinitePlace K) (x : K) :
    ‖algebraMap K w.Completion x‖ = w x := by
  rw [show algebraMap K w.Completion x = (((WithAbs.equiv w.1).symm x : WithAbs w.1) : w.Completion) from rfl,
    NumberField.InfinitePlace.Completion.norm_coe]
  simp

theorem denseRange_algebraMap_completion {K : Type*} [Field K] (w : InfinitePlace K) :
    DenseRange (algebraMap K w.Completion) := by
  have h := UniformSpace.Completion.denseRange_coe (α := WithAbs w.1)
  exact (NumberField.InfinitePlace.Completion.ofCompletion_surjective w).denseRange.comp
    (h.comp (WithAbs.equiv w.1).symm.surjective.denseRange (UniformSpace.Completion.continuous_coe _))
    (NumberField.InfinitePlace.Completion.continuous_ofCompletion w)

theorem denseRange_algebraMap_adicCompletion {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : DenseRange (algebraMap K (v.adicCompletion K)) := by
  exact IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v)

theorem isNontrivial_and_pairwise_not_isEquiv {K : Type*} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∀ i, (Sum.elim (fun v : S => NumberField.place (algebraMap K (v.1.adicCompletion K)))
        (fun w : InfinitePlace K => w.1) i).IsNontrivial) ∧
    Pairwise (fun i j => ¬ (Sum.elim (fun v : S => NumberField.place (algebraMap K (v.1.adicCompletion K)))
        (fun w : InfinitePlace K => w.1) i).IsEquiv
      (Sum.elim (fun v : S => NumberField.place (algebraMap K (v.1.adicCompletion K)))
        (fun w : InfinitePlace K => w.1) j)) := by
  set V := Sum.elim (fun v : S => NumberField.place (algebraMap K (v.1.adicCompletion K)))
        (fun w : InfinitePlace K => w.1) with hV
  have hVl : ∀ (v : S) (x : K), V (Sum.inl v) x = ‖algebraMap K (v.1.adicCompletion K) x‖ := fun v x =>
    NumberField.place_apply _ _
  have hemb : ∀ v : S, NumberField.FinitePlace.embedding v.1 = algebraMap K (v.1.adicCompletion K) := fun v => rfl

  have hlt : ∀ (v : S) (x : 𝓞 K), V (Sum.inl v) (algebraMap (𝓞 K) K x) < 1 ↔ x ∈ v.1.asIdeal := by
    intro v x
    rw [hVl, ← hemb]
    exact NumberField.FinitePlace.norm_lt_one_iff_mem K v.1 x
  have h2v : ∀ v : S, V (Sum.inl v) (2 : K) ≤ 1 := by
    intro v
    have h := NumberField.FinitePlace.norm_le_one K v.1 (2 : 𝓞 K)
    rw [map_ofNat, hemb] at h
    rw [hVl]; exact h
  have h2w : ∀ w : InfinitePlace K, V (Sum.inr w) (2 : K) = 2 := by
    intro w
    show w (2 : K) = 2
    rw [← NumberField.InfinitePlace.norm_embedding_eq, map_ofNat]
    exact Complex.norm_two

  have hfin2 : ∀ v : S, ¬ V (Sum.inl v) (2⁻¹ : K) < 1 := by
    intro v h
    rw [map_inv₀] at h
    have hpos : 0 < V (Sum.inl v) (2 : K) := (V (Sum.inl v)).pos two_ne_zero
    have : 1 < V (Sum.inl v) (2 : K) := by
      rcases (inv_lt_one_iff₀.1 h) with h' | h'
      · exact absurd h' (not_le.2 hpos)
      · exact h'
    exact absurd (h2v v) (not_le.2 this)
  have hinf2 : ∀ w : InfinitePlace K, V (Sum.inr w) (2⁻¹ : K) < 1 := by
    intro w
    rw [map_inv₀, h2w]; norm_num
  refine ⟨?_, ?_⟩
  · rintro (v | w)
    · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.1.ne_bot
      refine ⟨algebraMap (𝓞 K) K x, ?_, ?_⟩
      · exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hx0
      · exact ne_of_lt ((hlt v x).2 hx)
    · exact w.isNontrivial
  · rintro (v | w) (v' | w') hij heq
    · have hvv : v.1 ≠ v'.1 := fun h => hij (by rw [Subtype.ext h])
      have hnle : ¬ (v.1.asIdeal ≤ v'.1.asIdeal) := fun hle =>
        hvv (HeightOneSpectrum.ext (v.1.isMaximal.eq_of_le v'.1.isPrime.ne_top hle))
      obtain ⟨x, hxv, hxv'⟩ := Set.not_subset.1 hnle
      rw [AbsoluteValue.isEquiv_iff_lt_one_iff] at heq
      exact hxv' ((hlt v' x).1 ((heq _).1 ((hlt v x).2 hxv)))
    · rw [AbsoluteValue.isEquiv_iff_lt_one_iff] at heq
      exact hfin2 v ((heq _).2 (hinf2 w'))
    · rw [AbsoluteValue.isEquiv_iff_lt_one_iff] at heq
      exact hfin2 v' ((heq _).1 (hinf2 w))
    · have hww : w ≠ w' := fun h => hij (by rw [h])
      exact hww (NumberField.InfinitePlace.eq_iff_isEquiv.2 heq)

end P2mS26B6b

namespace NumberField

theorem denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi {K : Type*} [Field K]
    [NumberField K]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    DenseRange (fun x : K =>
      ((fun v : S => algebraMap K (v.1.adicCompletion K) x),
       (fun w : NumberField.InfinitePlace K => algebraMap K w.Completion x))) := by
  classical
  obtain ⟨hV, hne⟩ := P2mS26B6b.isNontrivial_and_pairwise_not_isEquiv S
  intro z
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := mem_nhds_prod_iff.1 ht
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.1 ht₁
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 ht₂

  have hd₁ : ∀ v : S, ∃ k : K, dist (algebraMap K (v.1.adicCompletion K) k) (z.1 v) < ε₁ / 2 := by
    intro v
    obtain ⟨k, hk⟩ := (P2mS26B6b.denseRange_algebraMap_adicCompletion v.1).exists_dist_lt (z.1 v) (half_pos hε₁)
    exact ⟨k, by rw [dist_comm]; exact hk⟩
  have hd₂ : ∀ w : NumberField.InfinitePlace K, ∃ k : K, dist (algebraMap K w.Completion k) (z.2 w) < ε₂ / 2 := by
    intro w
    obtain ⟨k, hk⟩ := (P2mS26B6b.denseRange_algebraMap_completion w).exists_dist_lt (z.2 w) (half_pos hε₂)
    exact ⟨k, by rw [dist_comm]; exact hk⟩
  choose k₁ hk₁ using hd₁
  choose k₂ hk₂ using hd₂

  obtain ⟨x, hx⟩ := AbsoluteValue.exists_forall_sub_lt_of_pairwise_not_isEquiv hV hne (Sum.elim k₁ k₂)
    (lt_min (half_pos hε₁) (half_pos hε₂))
  refine ⟨_, hsub ⟨hb₁ ?_, hb₂ ?_⟩, Set.mem_range_self x⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε₁]
    intro v
    have h1 : dist (algebraMap K (v.1.adicCompletion K) x) (algebraMap K (v.1.adicCompletion K) (k₁ v)) < ε₁ / 2 := by
      rw [dist_eq_norm, ← map_sub, ← NumberField.place_apply]
      exact (hx (Sum.inl v)).trans_le (min_le_left _ _)
    calc dist (algebraMap K (v.1.adicCompletion K) x) (z.1 v)
        ≤ dist (algebraMap K (v.1.adicCompletion K) x) (algebraMap K (v.1.adicCompletion K) (k₁ v))
          + dist (algebraMap K (v.1.adicCompletion K) (k₁ v)) (z.1 v) := dist_triangle _ _ _
      _ < ε₁ / 2 + ε₁ / 2 := add_lt_add h1 (hk₁ v)
      _ = ε₁ := add_halves ε₁
  · rw [Metric.mem_ball, dist_pi_lt_iff hε₂]
    intro w
    have h1 : dist (algebraMap K w.Completion x) (algebraMap K w.Completion (k₂ w)) < ε₂ / 2 := by
      rw [dist_eq_norm, ← map_sub, P2mS26B6b.norm_algebraMap_completion]
      exact (hx (Sum.inr w)).trans_le (min_le_right _ _)
    calc dist (algebraMap K w.Completion x) (z.2 w)
        ≤ dist (algebraMap K w.Completion x) (algebraMap K w.Completion (k₂ w))
          + dist (algebraMap K w.Completion (k₂ w)) (z.2 w) := dist_triangle _ _ _
      _ < ε₂ / 2 + ε₂ / 2 := add_lt_add h1 (hk₂ w)
      _ = ε₂ := add_halves ε₂

end NumberField

/-! ### The criterion for Hecke characters -/

namespace HeckeCharacter

open NumberField IsDedekindDomain

noncomputable section

open IsDedekindDomain.HeightOneSpectrum NumberField.AdelicLevel AutomorphicForm
open scoped Topology

section IdeleCharacter

variable (F : Type*) [Field F] [NumberField F]

private noncomputable def ideleChar_archIncl : InfiniteAdeleRing F →* AdeleRing (𝓞 F) F where
  toFun z := (z, (1 : FiniteAdeleRing (𝓞 F) F))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

private theorem ideleChar_continuous_archIncl : Continuous (ideleChar_archIncl F) :=
  (continuous_id.prodMk continuous_const :
    Continuous fun z : InfiniteAdeleRing F =>
      ((z, (1 : FiniteAdeleRing (𝓞 F) F)) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

private noncomputable def ideleChar_component (v : HeightOneSpectrum (𝓞 F)) :
    (FiniteAdeleRing (𝓞 F) F)ˣ →* (v.adicCompletion F)ˣ :=
  Units.map (finAdeleEval (𝓞 F) F v)

private noncomputable def ideleChar_archInv : InfiniteAdeleRing F → InfiniteAdeleRing F :=
  fun z w => (z w)⁻¹

private noncomputable def ideleChar_ball (v : HeightOneSpectrum (𝓞 F)) (a : v.adicCompletion F) (n : ℕ) :
    Set (v.adicCompletion F) :=
  {b | Valued.v (b - a) ≤ Valued.v ((uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a)}

variable {F}

private theorem ideleChar_fin_apply_ne_zero (u : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (u : AdeleRing (𝓞 F) F).2 v ≠ 0 :=
  left_ne_zero_of_mul_eq_one (congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) u.mul_inv)

private theorem ideleChar_idele_decomp (u : (AdeleRing (𝓞 F) F)ˣ) :
    u = Units.map (ideleChar_archIncl F) (Units.map (adeleArch (𝓞 F) F) u) *
        Units.map (finIncl (𝓞 F) F) (Units.map (adeleFin (𝓞 F) F) u) :=
  Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)

private theorem ideleChar_component_apply (v : HeightOneSpectrum (𝓞 F)) (y : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (ideleChar_component F v y : v.adicCompletion F) = (y : FiniteAdeleRing (𝓞 F) F) v := rfl

private theorem ideleChar_component_localUnit_self (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ideleChar_component F v (localUnit (𝓞 F) F v t) = t :=
  Units.ext (localUnit_apply_self (𝓞 F) F v t)

private theorem ideleChar_component_localUnit_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : v ≠ w)
    (t : (w.adicCompletion F)ˣ) : ideleChar_component F v (localUnit (𝓞 F) F w t) = 1 :=
  Units.ext (localUnit_apply_of_ne (𝓞 F) F w t h)

omit [NumberField F] in
private theorem ideleChar_arch_apply_ne_zero (z : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    (z : InfiniteAdeleRing F) w ≠ 0 :=
  left_ne_zero_of_mul_eq_one
    (congrFun (congrArg (fun a : InfiniteAdeleRing F => (a : (w' : InfinitePlace F) → w'.Completion))
      z.mul_inv) w)

omit [NumberField F] in
private theorem ideleChar_arch_val_inv (z : (InfiniteAdeleRing F)ˣ) :
    ((z⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = ideleChar_archInv F (z : InfiniteAdeleRing F) :=
  funext fun w => eq_inv_of_mul_eq_one_right
    (congrFun (congrArg (fun a : InfiniteAdeleRing F => (a : (w' : InfinitePlace F) → w'.Completion))
      z.mul_inv) w)

omit [NumberField F] in
private theorem ideleChar_continuousAt_archInv (p : InfiniteAdeleRing F) (hp : ∀ w, p w ≠ 0) :
    ContinuousAt (ideleChar_archInv F) p :=
  continuousAt_pi.mpr fun w => (continuousAt_inv₀ (hp w)).comp (continuousAt_apply w p)

private theorem ideleChar_valued_ne_zero {v : HeightOneSpectrum (𝓞 F)} {a : v.adicCompletion F} (ha : a ≠ 0) :
    Valued.v a ≠ 0 :=
  (map_ne_zero (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr ha

private theorem ideleChar_finite_supp {𝔣 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) :
    {v : HeightOneSpectrum (𝓞 F) | HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0}.Finite :=
  (Ideal.finite_factors (show 𝔣 ≠ 0 from h𝔣)).subset fun v hv =>
    (Associates.count_ne_zero_iff_dvd (show 𝔣 ≠ 0 from h𝔣) v.irreducible).mp hv

private theorem ideleChar_ball_mem_nhds (v : HeightOneSpectrum (𝓞 F)) {a : v.adicCompletion F} (ha : a ≠ 0)
    (n : ℕ) : ideleChar_ball F v a n ∈ nhds a := by
  have ht : (uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (uniformizerUnit F v).ne_zero) ha
  have hopen : IsOpen (ideleChar_ball F v a n) :=
    (isOpen_setOf_valued_le v _ ht).preimage (continuous_id.sub continuous_const)
  refine hopen.mem_nhds ?_
  show Valued.v (a - a) ≤ _
  rw [sub_self, map_zero]
  exact zero_le

private theorem ideleChar_congruence {v : HeightOneSpectrum (𝓞 F)} {a b : v.adicCompletion F} (ha : a ≠ 0)
    (n : ℕ) (hb : b ∈ ideleChar_ball F v a n) :
    Valued.v (a * b⁻¹) = 1 ∧ Valued.v (a * b⁻¹ - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  change Valued.v (b - a) ≤ Valued.v ((uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a) at hb
  have ha0 : Valued.v a ≠ 0 := ideleChar_valued_ne_zero ha
  obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = Valued.v a := ⟨_, WithZero.exp_log ha0⟩
  have ht : Valued.v ((uniformizerUnit F v : v.adicCompletion F) ^ (n + 1) * a)
      = WithZero.exp (m - (n + 1 : ℤ)) := by
    rw [map_mul, map_pow, valued_uniformizerUnit, ← hm, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1
    rw [nsmul_eq_mul]
    push_cast
    ring
  rw [ht] at hb
  have hlt : Valued.v (b - a) < Valued.v a := by
    rw [← hm]
    exact hb.trans_lt (WithZero.exp_lt_exp.mpr (by omega))
  have hba : Valued.v b = Valued.v a := Valuation.map_eq_of_sub_lt _ hlt
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hba
    exact ha0 hba.symm
  refine ⟨?_, ?_⟩
  · rw [map_mul, map_inv₀, hba, mul_inv_cancel₀ ha0]
  · have h2 : a * b⁻¹ - 1 = (a - b) * b⁻¹ := by
      rw [sub_mul, mul_inv_cancel₀ hb0]
    rw [h2, map_mul, map_inv₀, hba, Valuation.map_sub_swap, ← hm]
    calc Valued.v (b - a) * (WithZero.exp m)⁻¹
        ≤ WithZero.exp (m - (n + 1 : ℤ)) * (WithZero.exp m)⁻¹ := mul_le_mul_left hb _
      _ = WithZero.exp (-(n + 1 : ℤ)) := by
          rw [← WithZero.exp_neg, ← WithZero.exp_add]
          congr 1
          ring
      _ ≤ WithZero.exp (-(n : ℤ)) := WithZero.exp_le_exp.mpr (by omega)

private theorem ideleChar_finIncl_eq_one (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {𝔣 : Ideal (𝓞 F)}
    (hmod : HeckeCharacter.AdmitsModulus F θ 𝔣) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hS : ∀ v ∉ S, θ (Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (uniformizerUnit F v))) = 1)
    (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ∨ HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0 →
      Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 ∧
        Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v - 1)
          ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ))) :
    θ (Units.map (finIncl (𝓞 F) F) y) = 1 := by
  obtain ⟨hne, hcof⟩ := IsDedekindDomain.FiniteAdeleRing.isUnit_iff.mp y.isUnit
  have hZ : {v : HeightOneSpectrum (𝓞 F) | Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) ≠ 1}.Finite :=
    Filter.eventually_cofinite.mp hcof
  have hv0 : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 :=
    fun v => ideleChar_valued_ne_zero (hne v)
  obtain ⟨k, hk⟩ : ∃ k : HeightOneSpectrum (𝓞 F) → ℤ,
      ∀ v, WithZero.exp (k v) = Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) :=
    ⟨fun v => WithZero.log _, fun v => WithZero.exp_log (hv0 v)⟩
  have hZS : ∀ v ∈ hZ.toFinset, v ∉ S := by
    intro v hv hvS
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
    exact hv (hy v (Or.inl hvS)).1
  have hnotZ : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 →
      v ∉ hZ.toFinset := by
    intro v h1 hv
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
    exact hv h1

  obtain ⟨c, hc⟩ : ∃ c : (FiniteAdeleRing (𝓞 F) F)ˣ,
      c = ∏ v ∈ hZ.toFinset, localUnit (𝓞 F) F v (uniformizerUnit F v ^ (-(k v))) := ⟨_, rfl⟩
  have hθc : θ (Units.map (finIncl (𝓞 F) F) c) = 1 := by
    rw [hc, map_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => ?_
    rw [map_zpow, map_zpow, map_zpow, hS v (hZS v hv), _root_.one_zpow]
  have hevc_in : ∀ v ∈ hZ.toFinset, ideleChar_component F v c = uniformizerUnit F v ^ (-(k v)) := by
    intro v hv
    rw [hc, map_prod, Finset.prod_eq_single v]
    · exact ideleChar_component_localUnit_self v _
    · intro w _ hwv
      exact ideleChar_component_localUnit_of_ne (Ne.symm hwv) _
    · intro h
      exact absurd hv h
  have hevc_out : ∀ v, v ∉ hZ.toFinset → ideleChar_component F v c = 1 := by
    intro v hv
    rw [hc, map_prod]
    refine Finset.prod_eq_one fun w hw => ?_
    refine ideleChar_component_localUnit_of_ne (fun hvw => hv ?_) _
    rw [hvw]
    exact hw

  obtain ⟨u, hu⟩ : ∃ u : (FiniteAdeleRing (𝓞 F) F)ˣ, u = y * c⁻¹ := ⟨_, rfl⟩
  have hyu : y = u * c := by
    rw [hu]
    simp
  have hu_out : ∀ v, v ∉ hZ.toFinset →
      (u : FiniteAdeleRing (𝓞 F) F) v = (y : FiniteAdeleRing (𝓞 F) F) v := by
    intro v hv
    change (ideleChar_component F v u : v.adicCompletion F) = ideleChar_component F v y
    rw [hu, map_mul, map_inv, hevc_out v hv, inv_one, mul_one]
  have hu_val : ∀ v, Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    intro v
    by_cases hv : v ∈ hZ.toFinset
    · change Valued.v (ideleChar_component F v u : v.adicCompletion F) = 1
      rw [hu, map_mul, map_inv, hevc_in v hv, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, valued_uniformizerUnit, ideleChar_component_apply,
        ← hk v, ← WithZero.exp_zsmul]
      have h1 : (-(k v)) • (-1 : ℤ) = k v := by simp
      rw [h1]
      exact mul_inv_cancel₀ WithZero.exp_ne_zero
    · rw [hu_out v hv]
      by_contra h
      exact hv (by rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; exact h)
  have hu_cong : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v ((u : FiniteAdeleRing (𝓞 F) F) v - 1)
        ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ)) := by
    intro v
    by_cases hn : HeckeCharacter.idealMultiplicity F v 𝔣 = 0
    · rw [hn, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact (Valuation.map_sub Valued.v _ _).trans (max_le (hu_val v).le (map_one Valued.v).le)
    · have hvZ : v ∉ hZ.toFinset := hnotZ v (hy v (Or.inr hn)).1
      rw [hu_out v hvZ]
      exact (hy v (Or.inr hn)).2
  have hθu : θ (Units.map (finIncl (𝓞 F) F) u) = 1 :=
    hmod (Units.map (finIncl (𝓞 F) F) u) rfl fun v => ⟨hu_val v, hu_cong v⟩
  rw [hyu, map_mul, map_mul, hθu, hθc, one_mul]

private theorem ideleChar_eq_one_of_denseRange (F : Type*) [Field F] [NumberField F]
    (hwa : ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
      DenseRange (fun x : F =>
        ((fun v : S => algebraMap F (v.1.adicCompletion F) x),
         (fun w : NumberField.InfinitePlace F => algebraMap F w.Completion x))))
    (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hcont : Continuous θ)
    (hclass : AutomorphicForm.IsIdeleClassChar (𝓞 F) F θ)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F θ 𝔣)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, θ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
        (NumberField.AdelicLevel.localUnit (𝓞 F) F v (NumberField.AdelicLevel.uniformizerUnit F v))) = 1) :
    θ = 1 := by
  classical
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.one_apply]

  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), T = S ∪ (ideleChar_finite_supp h𝔣).toFinset :=
    ⟨_, rfl⟩
  have hmemT : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ∨ HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0 →
      v ∈ T := by
    intro v hv
    rw [hT, Finset.mem_union]
    rcases hv with h | h
    · exact Or.inl h
    · right
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact h

  have hx2 : ∀ v : HeightOneSpectrum (𝓞 F), (x : AdeleRing (𝓞 F) F).2 v ≠ 0 :=
    ideleChar_fin_apply_ne_zero x
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : (InfiniteAdeleRing F)ˣ, x₁ = Units.map (adeleArch (𝓞 F) F) x := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (InfiniteAdeleRing F)ˣ → ℂˣ,
      ∀ z, ψ z = θ (Units.map (ideleChar_archIncl F) (x₁ * z⁻¹)) :=
    ⟨fun z => θ (Units.map (ideleChar_archIncl F) (x₁ * z⁻¹)), fun _ => rfl⟩
  have hψ_cont : Continuous ψ := by
    have hψ' : ψ = fun z => θ (Units.map (ideleChar_archIncl F) (x₁ * z⁻¹)) := funext hψ
    rw [hψ']
    exact (hcont.comp (Continuous.units_map _ (ideleChar_continuous_archIncl F))).comp
      (continuous_const.mul continuous_inv)
  have hψ_one : ψ x₁ = 1 := by
    rw [hψ]
    simp

  have hstepA : ∀ N ∈ nhds (x₁ : InfiniteAdeleRing F),
      ∃ z : (InfiniteAdeleRing F)ˣ, (z : InfiniteAdeleRing F) ∈ N ∧ θ x = ψ z := by
    intro N hN
    obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
    obtain ⟨E, hE⟩ : ∃ E : Set (InfiniteAdeleRing F), E = archEval F w₀ ⁻¹' {c | c ≠ 0} := ⟨_, rfl⟩
    have hEN : E ∈ nhds (x₁ : InfiniteAdeleRing F) := by
      rw [hE]
      exact ((isOpen_ne (x := (0 : w₀.Completion))).preimage (continuous_archEval F w₀)).mem_nhds
        (ideleChar_arch_apply_ne_zero x₁ w₀)
    have hN' : N ∩ E ∈ nhds (x₁ : InfiniteAdeleRing F) := Filter.inter_mem hN hEN
    have hpi : Set.univ.pi (fun v : T => ideleChar_ball F v.1 ((x : AdeleRing (𝓞 F) F).2 v.1)
          (HeckeCharacter.idealMultiplicity F v.1 𝔣))
        ∈ nhds (fun v : T => (x : AdeleRing (𝓞 F) F).2 v.1) :=
      set_pi_mem_nhds Set.finite_univ fun v _ => ideleChar_ball_mem_nhds v.1 (hx2 v.1) _
    obtain ⟨pt, hpt_def⟩ : ∃ pt : ((v : T) → v.1.adicCompletion F) × InfiniteAdeleRing F,
        pt = ((fun v : T => (x : AdeleRing (𝓞 F) F).2 v.1), (x₁ : InfiniteAdeleRing F)) := ⟨_, rfl⟩
    have hU : (Set.univ.pi (fun v : T => ideleChar_ball F v.1 ((x : AdeleRing (𝓞 F) F).2 v.1)
          (HeckeCharacter.idealMultiplicity F v.1 𝔣))) ×ˢ (N ∩ E) ∈ nhds pt := by
      rw [hpt_def, nhds_prod_eq]
      exact Filter.prod_mem_prod hpi hN'
    have hpt := hwa T pt
    obtain ⟨q, hqU, α, hαq⟩ := mem_closure_iff_nhds.mp hpt _ hU
    subst hαq
    have hfin : ∀ v : T, algebraMap F (v.1.adicCompletion F) α ∈ ideleChar_ball F v.1
        ((x : AdeleRing (𝓞 F) F).2 v.1) (HeckeCharacter.idealMultiplicity F v.1 𝔣) :=
      fun v => (Set.mem_univ_pi.mp hqU.1) v
    have harch : (algebraMap F (AdeleRing (𝓞 F) F) α).1 ∈ N ∩ E := hqU.2
    have hα0 : α ≠ 0 := by
      intro h
      have h2 := harch.2
      rw [hE, Set.mem_preimage, Set.mem_ofPred_eq, archEval_apply] at h2
      subst h
      exact h2 (map_zero (algebraMap F w₀.Completion))

    obtain ⟨P, hP⟩ : ∃ P : (AdeleRing (𝓞 F) F)ˣ,
        P = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) (Units.mk0 α hα0) := ⟨_, rfl⟩
    have hθP : θ P = 1 := by
      rw [hP]
      exact hclass _
    have hcomp : ∀ v : HeightOneSpectrum (𝓞 F),
        ((Units.map (adeleFin (𝓞 F) F) (x * P⁻¹) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
          = (x : AdeleRing (𝓞 F) F).2 v * (algebraMap F (v.adicCompletion F) α)⁻¹ := by
      intro v
      rw [hP, ← map_inv₀]
      rfl
    have hyf : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ S ∨ HeckeCharacter.idealMultiplicity F v 𝔣 ≠ 0 →
        Valued.v (((Units.map (adeleFin (𝓞 F) F) (x * P⁻¹) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
            FiniteAdeleRing (𝓞 F) F) v) = 1 ∧
          Valued.v (((Units.map (adeleFin (𝓞 F) F) (x * P⁻¹) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
            FiniteAdeleRing (𝓞 F) F) v - 1)
            ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity F v 𝔣 : ℤ)) := by
      intro v hv
      have hb : algebraMap F (v.adicCompletion F) α ∈ ideleChar_ball F v ((x : AdeleRing (𝓞 F) F).2 v)
          (HeckeCharacter.idealMultiplicity F v 𝔣) := hfin ⟨v, hmemT v hv⟩
      rw [hcomp v]
      exact ideleChar_congruence (hx2 v) _ hb
    have hθfin : θ (Units.map (finIncl (𝓞 F) F) (Units.map (adeleFin (𝓞 F) F) (x * P⁻¹))) = 1 :=
      ideleChar_finIncl_eq_one θ hmod hS _ hyf

    refine ⟨Units.map (adeleArch (𝓞 F) F) P, ?_, ?_⟩
    · rw [hP]
      exact harch.1
    · have h1 : θ x = θ (x * P⁻¹) := by
        rw [map_mul, map_inv, hθP, inv_one, mul_one]
      have h3 : Units.map (adeleArch (𝓞 F) F) (x * P⁻¹) = x₁ * (Units.map (adeleArch (𝓞 F) F) P)⁻¹ := by
        rw [map_mul, map_inv, hx₁]
      rw [h1, ideleChar_idele_decomp (x * P⁻¹), map_mul, hθfin, mul_one, hψ, h3]

  refine Specializes.eq ?_
  rw [specializes_iff_forall_open]
  intro V hV h1V
  have hVψ : ψ ⁻¹' V ∈ nhds x₁ :=
    hψ_cont.continuousAt.preimage_mem_nhds (by rw [hψ_one]; exact hV.mem_nhds h1V)
  rw [(Units.isEmbedding_embedProduct (M := InfiniteAdeleRing F)).toIsInducing.nhds_eq_comap x₁,
    Filter.mem_comap] at hVψ
  obtain ⟨Q, hQ, hQsub⟩ := hVψ
  change Q ∈ nhds ((x₁ : InfiniteAdeleRing F),
    MulOpposite.op ((x₁⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)) at hQ
  rw [mem_nhds_prod_iff] at hQ
  obtain ⟨A, hA, B', hB', hAB⟩ := hQ
  have hB : MulOpposite.op ⁻¹' B' ∈ nhds ((x₁⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB'
  rw [ideleChar_arch_val_inv x₁] at hB
  have hB2 : ideleChar_archInv F ⁻¹' (MulOpposite.op ⁻¹' B') ∈ nhds (x₁ : InfiniteAdeleRing F) :=
    (ideleChar_continuousAt_archInv (x₁ : InfiniteAdeleRing F) (ideleChar_arch_apply_ne_zero x₁)).preimage_mem_nhds hB
  obtain ⟨z, hz, hθz⟩ := hstepA (A ∩ ideleChar_archInv F ⁻¹' (MulOpposite.op ⁻¹' B')) (Filter.inter_mem hA hB2)
  have hz2 : MulOpposite.op ((z⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) ∈ B' := by
    rw [ideleChar_arch_val_inv z]
    exact hz.2
  have hzQ : z ∈ Units.embedProduct (InfiniteAdeleRing F) ⁻¹' Q := by
    change ((z : InfiniteAdeleRing F),
      MulOpposite.op ((z⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)) ∈ Q
    exact hAB (Set.mk_mem_prod hz.1 hz2)
  rw [hθz]
  exact hQsub hzQ

private theorem ideleChar_eq_one (F : Type*) [Field F] [NumberField F]
    (θ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hcont : Continuous θ)
    (hclass : AutomorphicForm.IsIdeleClassChar (𝓞 F) F θ)
    (𝔣 : Ideal (𝓞 F)) (h𝔣 : 𝔣 ≠ ⊥) (hmod : HeckeCharacter.AdmitsModulus F θ 𝔣)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, θ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
        (NumberField.AdelicLevel.localUnit (𝓞 F) F v (NumberField.AdelicLevel.uniformizerUnit F v))) = 1) :
    θ = 1 :=
  ideleChar_eq_one_of_denseRange F NumberField.denseRange_algebraMap_adicCompletion_pi_prod_infinitePlace_pi
    θ hcont hclass 𝔣 h𝔣 hmod S hS

end IdeleCharacter

section Reduction

variable {K : Type*} [Field K] [NumberField K]

private theorem idealMultiplicity_le_of_dvd {𝔞 𝔟 : Ideal (𝓞 K)} (h𝔟 : 𝔟 ≠ ⊥) (h : 𝔞 ∣ 𝔟)
    (v : HeightOneSpectrum (𝓞 K)) :
    HeckeCharacter.idealMultiplicity K v 𝔞 ≤ HeckeCharacter.idealMultiplicity K v 𝔟 := by
  unfold HeckeCharacter.idealMultiplicity
  refine Associates.count_le_count_of_le ?_ v.associates_irreducible (Associates.mk_le_mk_of_dvd h)
  rw [Ne, Associates.mk_eq_zero, Ideal.zero_eq_bot]
  exact h𝔟

private theorem admitsModulus_of_forall_le {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {𝔞 𝔟 : Ideal (𝓞 K)}
    (hχ : HeckeCharacter.AdmitsModulus K χ 𝔞)
    (hle : ∀ v : HeightOneSpectrum (𝓞 K),
      HeckeCharacter.idealMultiplicity K v 𝔞 ≤ HeckeCharacter.idealMultiplicity K v 𝔟) :
    HeckeCharacter.AdmitsModulus K χ 𝔟 := by
  intro u h1 h2
  refine hχ u h1 (fun v => ⟨(h2 v).1, le_trans (h2 v).2 ?_⟩)
  rw [WithZero.exp_le_exp]
  exact neg_le_neg (by exact_mod_cast hle v)

private theorem idealMultiplicity_bot (v : HeightOneSpectrum (𝓞 K)) :
    HeckeCharacter.idealMultiplicity K v (⊥ : Ideal (𝓞 K)) = 0 := by
  unfold HeckeCharacter.idealMultiplicity
  rw [← Ideal.zero_eq_bot, Associates.mk_zero, Associates.factors_zero]
  by_cases hp : Irreducible (Associates.mk v.asIdeal)
  · simp only [Associates.count, dite_eq_left hp]
    rfl
  · exact congrFun (Associates.count_reducible hp) _

private theorem exists_ne_bot_admitsModulus {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 K)}
    (hχ : HeckeCharacter.AdmitsModulus K χ 𝔣) :
    ∃ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus K χ 𝔪 := by
  by_cases h𝔣 : 𝔣 = ⊥
  · subst h𝔣
    refine ⟨⊤, ?_, admitsModulus_of_forall_le hχ (fun v => ?_)⟩
    · exact fun h => bot_ne_top h.symm
    · rw [idealMultiplicity_bot]
      exact Nat.zero_le _
  · exact ⟨𝔣, h𝔣, hχ⟩

private theorem exists_common_modulus {χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {𝔣₁ 𝔣₂ : Ideal (𝓞 K)}
    (h₁ : HeckeCharacter.AdmitsModulus K χ₁ 𝔣₁) (h₂ : HeckeCharacter.AdmitsModulus K χ₂ 𝔣₂) :
    ∃ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ ∧ HeckeCharacter.AdmitsModulus K χ₁ 𝔪 ∧ HeckeCharacter.AdmitsModulus K χ₂ 𝔪 := by
  obtain ⟨𝔪₁, hm₁, hχ₁⟩ := exists_ne_bot_admitsModulus h₁
  obtain ⟨𝔪₂, hm₂, hχ₂⟩ := exists_ne_bot_admitsModulus h₂
  have hmul : 𝔪₁ * 𝔪₂ ≠ ⊥ := fun h => by
    rcases Ideal.mul_eq_bot.mp h with h | h
    · exact hm₁ h
    · exact hm₂ h
  refine ⟨𝔪₁ * 𝔪₂, hmul, ?_, ?_⟩
  · exact admitsModulus_of_forall_le hχ₁ (idealMultiplicity_le_of_dvd hmul (dvd_mul_right 𝔪₁ 𝔪₂))
  · exact admitsModulus_of_forall_le hχ₂ (idealMultiplicity_le_of_dvd hmul (dvd_mul_left 𝔪₂ 𝔪₁))

end Reduction

theorem eq_of_forall_apply_localUnit_uniformizerUnit_eq
    (K : Type*) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ₁ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₁)
    (hχ₂ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K χ₂)
    (hc₁ : Continuous χ₁)
    (hc₂ : Continuous χ₂)
    (𝔣₁ 𝔣₂ : Ideal (𝓞 K))
    (hmod₁ : HeckeCharacter.AdmitsModulus K χ₁ 𝔣₁)
    (hmod₂ : HeckeCharacter.AdmitsModulus K χ₂ 𝔣₂)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v ∉ S,
      χ₁ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))
        = χ₂ (Units.map (NumberField.AdelicLevel.finIncl (𝓞 K) K)
          (NumberField.AdelicLevel.localUnit (𝓞 K) K v (NumberField.AdelicLevel.uniformizerUnit K v)))) :
    χ₁ = χ₂ := by
  obtain ⟨𝔪, hm, hmod₁', hmod₂'⟩ := exists_common_modulus hmod₁ hmod₂
  have hθ : χ₁ * χ₂⁻¹ = 1 := by
    refine ideleChar_eq_one K (χ₁ * χ₂⁻¹) (hc₁.mul hc₂.inv) ?_ 𝔪 hm ?_ S ?_
    · intro u
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχ₁ u, hχ₂ u, inv_one, mul_one]
    · intro u h1 h2
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hmod₁' u h1 h2, hmod₂' u h1 h2, inv_one, mul_one]
    · intro v hv
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hS v hv, mul_inv_cancel]
  exact mul_inv_eq_one.mp hθ

end

end HeckeCharacter

end
