/-
  Two finite-dimensionality supplements coming from compactness:

  * `Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq` — a
    closed subspace of a normed space on which a compact operator `T` acts as the
    identity is finite-dimensional;
  * `LinearMap.exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional` — for
    a finite-dimensional `Y ≤ X → ℂ` and linear maps `T n : Y → (X → ℂ)` converging
    pointwise to the inclusion of `Y`, one `T n` is injective.

  The ports of the pin leaves of the same names (38 and 77 pin lines), together
  with the statements of their `Theorems/` wrappers. They share the module
  because they share their area — a finite-dimensionality conclusion obtained
  from a limiting/compactness argument — and because both are sub-80-line
  entries (order §5).

  The mathematics of the first is the `T = id` case of the closed-ball criterion
  `FiniteDimensional.of_isCompact_closedBall₀`: `T` fixes the closed unit ball of
  `ker (T - 1)`, and `T`'s image of a ball is relatively compact.

  The mathematics of the second separates points of `Y` by a finite `s ⊆ X`
  (`finrank` induction: each nonvanishing `y` has an `x` with `y x ≠ 0`, and
  `W (insert x s) < W s`), then evaluates the convergence at a basis of that
  finite-dimensional space.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has neither statement — `rg -n
  "finiteDimensional_of_isCompactOperator"` and `rg -n
  "exists_forall_eq_zero_of_tendsto_apply"` over `Mathlib/` find nothing; the
  ingredients it does have (`FiniteDimensional.of_isCompact_closedBall₀`,
  `IsCompactOperator.isCompact_closure_image_ball`,
  `Topology.IsClosedEmbedding.isCompact_iff`,
  `Submodule.finrank_lt_finrank_of_lt`) are imported, not restated.

  Drift: the pin's bare `import Mathlib` became the four modules named below.

  spec-pin: Theorems/Thm_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq.lean
  spec-pin: P2M/Sol/S_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq.lean
  spec-pin: Theorems/Thm_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional.lean
  spec-pin: P2M/Sol/S_LinearMap_exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional.lean
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Basic.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Constructions

set_option autoImplicit false

open Topology

theorem Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {T : E →L[𝕜] E} (hT : IsCompactOperator T) (V : Submodule 𝕜 E) (hV : ∀ v ∈ V, T v = v) :
    FiniteDimensional 𝕜 ↥V := by

  let W : Submodule 𝕜 E := LinearMap.ker ((T : E →ₗ[𝕜] E) - LinearMap.id)
  have hWmem : ∀ v : E, v ∈ W ↔ T v = v := by
    intro v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hVW : V ≤ W := fun v hv => (hWmem v).mpr (hV v hv)
  have hWclosed : IsClosed (W : Set E) := by
    have : (W : Set E) = {v | T v = v} := Set.ext fun v => hWmem v
    rw [this]
    exact isClosed_eq T.continuous continuous_id

  have : FiniteDimensional 𝕜 ↥W := by
    refine FiniteDimensional.of_isCompact_closedBall₀ 𝕜 zero_lt_one ?_
    have hK : IsCompact (closure ((T : E → E) '' Metric.closedBall 0 1)) := by
      have h := hT.isCompact_closure_image_ball (f := (T : E →ₗ[𝕜] E)) 2
      exact h.of_isClosed_subset isClosed_closure
        (closure_mono (Set.image_mono (Metric.closedBall_subset_ball (by norm_num))))
    have hemb : Topology.IsClosedEmbedding (Subtype.val : ↥W → E) :=
      hWclosed.isClosedEmbedding_subtypeVal
    rw [hemb.isCompact_iff]
    refine hK.of_isClosed_subset (hemb.isClosedMap _ Metric.isClosed_closedBall) ?_
    rintro _ ⟨w, hw, rfl⟩
    refine subset_closure ⟨(w : E), ?_, ((hWmem w).mp w.2)⟩
    simpa using hw
  exact Submodule.finiteDimensional_of_le hVW

namespace LinearMap

theorem exists_forall_eq_zero_of_tendsto_apply_of_finiteDimensional
    {X : Type*} (Y : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥Y]
    (T : ℕ → (↥Y →ₗ[ℂ] (X → ℂ)))
    (hT : ∀ (y : ↥Y) (x : X), Filter.Tendsto (fun n => T n y x) Filter.atTop (nhds ((y : X → ℂ) x))) :
    ∃ n, ∀ y : ↥Y, T n y = 0 → y = 0 := by
  classical
  let ev : X → (↥Y →ₗ[ℂ] ℂ) := fun x =>
    { toFun := fun y => (y : X → ℂ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W : Finset X → Submodule ℂ ↥Y := fun s => ⨅ x ∈ s, LinearMap.ker (ev x)
  have hW_anti : ∀ s t : Finset X, s ⊆ t → W t ≤ W s := fun s t hst =>
    biInf_mono hst
  have hsep : ∃ s : Finset X, W s = ⊥ := by
    suffices h : ∀ (d : ℕ) (s : Finset X), Module.finrank ℂ ↥(W s) ≤ d → ∃ t : Finset X, W t = ⊥ from
      h _ ∅ le_rfl
    intro d
    induction d with
    | zero =>
      intro s hs
      exact ⟨s, Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hs)⟩
    | succ d ih =>
      intro s hs
      by_cases hbot : W s = ⊥
      · exact ⟨s, hbot⟩
      · obtain ⟨y, hyW, hy0⟩ := (Submodule.ne_bot_iff (W s)).mp hbot
        have hyfun : (y : X → ℂ) ≠ 0 := fun h => hy0 (Subtype.ext h)
        obtain ⟨x, hx⟩ : ∃ x, (y : X → ℂ) x ≠ 0 := Function.ne_iff.mp hyfun
        refine ih (insert x s) (Nat.le_of_lt_succ (lt_of_lt_of_le ?_ hs))
        apply Submodule.finrank_lt_finrank_of_lt
        refine lt_of_le_of_ne (hW_anti s _ (Finset.subset_insert x s)) fun heq => hx ?_
        have hy' : y ∈ W (insert x s) := heq ▸ hyW
        have h1 := (Submodule.mem_iInf _).mp hy' x
        have h2 := (Submodule.mem_iInf _).mp h1 (Finset.mem_insert_self x s)
        simpa [ev] using h2
  obtain ⟨s, hs⟩ := hsep
  let Φ : (X → ℂ) →ₗ[ℂ] (↥s → ℂ) :=
    { toFun := fun f i => f i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦinj : ∀ y : ↥Y, Φ (y : X → ℂ) = 0 → y = 0 := by
    intro y hy
    have hyW : y ∈ W s := by
      refine (Submodule.mem_iInf _).mpr fun x => (Submodule.mem_iInf _).mpr fun hx => ?_
      show (y : X → ℂ) x = 0
      exact congr_fun hy ⟨x, hx⟩
    rw [hs] at hyW
    exact (Submodule.mem_bot ℂ).mp hyW
  let b := Module.finBasis ℂ ↥Y
  let v : Fin (Module.finrank ℂ ↥Y) → (↥s → ℂ) := fun j => Φ (b j : X → ℂ)
  have hv : LinearIndependent ℂ v := by
    refine LinearIndependent.map' b.linearIndependent (Φ ∘ₗ Y.subtype) ?_
    rw [LinearMap.ker_eq_bot']
    intro y hy
    exact hΦinj y hy
  have htend : Filter.Tendsto (fun n => fun j => Φ (T n (b j))) Filter.atTop (nhds v) := by
    rw [tendsto_pi_nhds]
    intro j
    rw [tendsto_pi_nhds]
    intro i
    exact hT (b j) i
  obtain ⟨n, hn⟩ := (htend.eventually hv.eventually).exists
  refine ⟨n, fun y hy => ?_⟩
  have h0 : ∑ j, (b.repr y j) • Φ (T n (b j)) = 0 := by
    have hΦ0 : Φ (T n y) = 0 := by rw [hy, map_zero]
    have hy' : y = ∑ j, (b.repr y j) • b j := (b.sum_repr y).symm
    rw [hy', map_sum, map_sum] at hΦ0
    simpa only [map_smul] using hΦ0
  have hc := Fintype.linearIndependent_iff.mp hn (fun j => b.repr y j) h0
  rw [← b.sum_repr y]
  exact Finset.sum_eq_zero fun j _ => by rw [show b.repr y j = 0 from hc j, zero_smul]

end LinearMap
