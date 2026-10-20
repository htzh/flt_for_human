/-
  Orbit transversals in connected graphs: a connected graph carrying a
  vertex-transitive-by-edges action of a group `Γ` has a connected transversal
  of the `Γ`-orbits.

  The node is `SimpleGraph.exists_walkConnected_transversal_of_preconnected`
  (pin lines 1-156).  Its proof is a Zorn-style maximality argument over the set
  of subsets that are walk-connected and meet every orbit at most once; the
  statement it delivers is a quadruple: a set `D ∋ v₀` whose induced subgraph is
  walk-connected, on which `Γ` acts freely, and which meets every orbit.

  FLT provenance, pinned `aa2d8b3` (Lean `v4.33.1`; the port is at mathlib
  `v4.34.0`), `S_` 156 lines:

  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_SimpleGraph_exists_walkConnected_transversal_of_preconnected.lean

  The statement authority is `Theorems/Thm_SimpleGraph_exists_walkConnected_transversal_of_preconnected.lean`.

  What this module assumes: nothing (the pin's `S_` file imports `Mathlib` and
  `P2M.Util` only; `P2M.Util` is metaprogramming and its `p2m_open` is spelled
  `open` here).  It is the home of the shared `GroupTheory.GraphTransversal`
  prelude: `WalkConnected`, `IsConnectedTransversal`, `walkConnected_singleton`,
  `WalkConnected.insert_of_adj`, `walkConnected_sUnion`,
  `eq_of_mem_orbit_sUnion`, `eq_of_mem_orbit_insert`, `exists_adj_of_walk`,
  `exists_isConnectedTransversal`.  The pin re-proves this prelude inside
  `S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean`; the port keeps
  this one copy and `FLTForHuman/GroupTheory/FreeGroup/KuroshRank.lean` imports it.

  Mathlib-first negative (checked against `v4.34.0`): `SimpleGraph.Connected` /
  `Preconnected` and the walk API exist, but nothing combines an action with a
  connected orbit transversal; `Mathlib/Combinatorics/SimpleGraph/Connectivity/`
  has no `orbit` lemma at all.

  spec-pin: P2M/Sol/S_SimpleGraph_exists_walkConnected_transversal_of_preconnected.lean
  spec-pin: Theorems/Thm_SimpleGraph_exists_walkConnected_transversal_of_preconnected.lean
  spec-pin: P2M/Sol/S_Monoid_CoprodI_nonempty_freeGroupBasis_fin_kuroshRank.lean
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

open Subgroup MulAction SimpleGraph Monoid

namespace SimpleGraph

namespace GraphTransversal

def WalkConnected {V : Type*} (T : SimpleGraph V) (s : Set V) : Prop :=
  ∀ v ∈ s, ∀ w ∈ s, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ s

structure IsConnectedTransversal {V : Type*} (T : SimpleGraph V) (Γ : Type*) [Group Γ]
    [MulAction Γ V] (D : Set V) : Prop where

  walkConnected : WalkConnected T D

  eq_of_mem_orbit : ∀ v ∈ D, ∀ w ∈ D, v ∈ orbit Γ w → v = w

  exists_mem_orbit : ∀ u : V, ∃ v ∈ D, v ∈ orbit Γ u

variable {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]

theorem walkConnected_singleton (T : SimpleGraph V) (v₀ : V) : WalkConnected T {v₀} := by
  intro v hv w hw
  rw [Set.mem_singleton_iff] at hv hw
  subst hv; subst hw
  exact ⟨Walk.nil, by simp⟩

theorem WalkConnected.insert_of_adj {s : Set V} (hs : WalkConnected T s) {v w : V}
    (hv : v ∈ s) (hadj : T.Adj v w) : WalkConnected T (insert w s) := by

  have key : ∀ x ∈ insert w s, ∃ p : T.Walk v x, ∀ y ∈ p.support, y ∈ insert w s := by
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · refine ⟨Walk.cons hadj Walk.nil, fun y hy => ?_⟩
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact Set.mem_insert_of_mem _ hv
      · exact Set.mem_insert _ _
    · obtain ⟨p, hp⟩ := hs v hv x hx
      exact ⟨p, fun y hy => Set.mem_insert_of_mem _ (hp y hy)⟩
  intro a ha b hb
  obtain ⟨p, hp⟩ := key a ha
  obtain ⟨q, hq⟩ := key b hb
  refine ⟨p.reverse.append q, fun y hy => ?_⟩
  rw [Walk.support_append, List.mem_append] at hy
  rcases hy with hy | hy
  · rw [Walk.support_reverse, List.mem_reverse] at hy
    exact hp y hy
  · exact hq y (List.mem_of_mem_tail hy)

theorem walkConnected_sUnion {c : Set (Set V)} (hchain : IsChain (· ⊆ ·) c)
    (hwc : ∀ s ∈ c, WalkConnected T s) : WalkConnected T (⋃₀ c) := by
  rintro v ⟨s, hs, hvs⟩ w ⟨t, ht, hwt⟩
  rcases hchain.total hs ht with hst | hts
  · obtain ⟨p, hp⟩ := hwc t ht v (hst hvs) w hwt
    exact ⟨p, fun x hx => Set.mem_sUnion.mpr ⟨t, ht, hp x hx⟩⟩
  · obtain ⟨p, hp⟩ := hwc s hs v hvs w (hts hwt)
    exact ⟨p, fun x hx => Set.mem_sUnion.mpr ⟨s, hs, hp x hx⟩⟩

private theorem mem_orbit_symm' {a b : V} (h : a ∈ orbit Γ b) : b ∈ orbit Γ a := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨γ⁻¹, inv_smul_smul γ b⟩

theorem eq_of_mem_orbit_sUnion {c : Set (Set V)} (hchain : IsChain (· ⊆ ·) c)
    (hinj : ∀ s ∈ c, ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w) :
    ∀ v ∈ ⋃₀ c, ∀ w ∈ ⋃₀ c, v ∈ orbit Γ w → v = w := by
  rintro v ⟨s, hs, hvs⟩ w ⟨t, ht, hwt⟩ hvw
  rcases hchain.total hs ht with hst | hts
  · exact hinj t ht v (hst hvs) w hwt hvw
  · exact hinj s hs v hvs w (hts hwt) hvw

theorem eq_of_mem_orbit_insert {s : Set V}
    (hs : ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w) {w : V}
    (hw : ¬∃ v ∈ s, v ∈ orbit Γ w) :
    ∀ v ∈ insert w s, ∀ v' ∈ insert w s, v ∈ orbit Γ v' → v = v' := by
  intro v hv v' hv' hvv'
  rcases Set.mem_insert_iff.mp hv with rfl | hvs <;>
    rcases Set.mem_insert_iff.mp hv' with rfl | hv's
  · rfl
  · exact absurd ⟨v', hv's, mem_orbit_symm' hvv'⟩ hw
  · exact absurd ⟨v, hvs, hvv'⟩ hw
  · exact hs v hvs v' hv's hvv'

theorem exists_adj_of_walk (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    {s : Set V} {a b : V} (p : T.Walk a b) :
    (∃ v ∈ s, v ∈ orbit Γ a) → (¬∃ v ∈ s, v ∈ orbit Γ b) →
      ∃ v ∈ s, ∃ w, T.Adj v w ∧ ¬∃ v' ∈ s, v' ∈ orbit Γ w := by
  induction p with
  | nil => exact fun ha hb => absurd ha hb
  | @cons a c b hac p ih =>
    intro ha hb
    by_cases hc : ∃ v ∈ s, v ∈ orbit Γ c
    · exact ih hc hb
    · obtain ⟨v, hvs, γ, hγ⟩ := ha
      refine ⟨v, hvs, γ • c, ?_, ?_⟩
      · rw [← hγ]
        exact hsmul γ hac
      · rintro ⟨v', hv's, hv'⟩
        rw [MulAction.orbit_smul] at hv'
        exact hc ⟨v', hv's, hv'⟩

theorem exists_isConnectedTransversal
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧ IsConnectedTransversal T Γ D := by
  classical

  obtain ⟨D, hsub, hDmem, hDmax⟩ := zorn_subset_nonempty
    {s : Set V | v₀ ∈ s ∧ WalkConnected T s ∧ ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w}
    (fun c hc hchain hcne => by
      obtain ⟨s₀, hs₀⟩ := hcne
      exact ⟨⋃₀ c, ⟨Set.mem_sUnion.mpr ⟨s₀, hs₀, (hc hs₀).1⟩,
        walkConnected_sUnion hchain fun s hs => (hc hs).2.1,
        eq_of_mem_orbit_sUnion hchain fun s hs => (hc hs).2.2⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩)
    {v₀}
    ⟨Set.mem_singleton v₀, walkConnected_singleton T v₀, by
      intro v hv w hw _
      rw [Set.mem_singleton_iff] at hv hw
      rw [hv, hw]⟩
  have hv₀D : v₀ ∈ D := hsub (Set.mem_singleton v₀)

  refine ⟨D, hv₀D, hDmem.2.1, hDmem.2.2, fun u => ?_⟩
  by_contra hu

  obtain ⟨p⟩ := hpre v₀ u
  obtain ⟨v, hvD, w, hadj, hw⟩ :=
    exists_adj_of_walk hsmul p ⟨v₀, hv₀D, MulAction.mem_orbit_self v₀⟩ hu

  have hwD : w ∉ D := fun hwD => hw ⟨w, hwD, MulAction.mem_orbit_self w⟩
  have hins : insert w D ∈
      {s : Set V | v₀ ∈ s ∧ WalkConnected T s ∧ ∀ v ∈ s, ∀ w ∈ s, v ∈ orbit Γ w → v = w} :=
    ⟨Set.mem_insert_of_mem _ hv₀D, hDmem.2.1.insert_of_adj hvD hadj,
      eq_of_mem_orbit_insert hDmem.2.2 hw⟩

  exact hwD (hDmax hins (Set.subset_insert w D) (Set.mem_insert w D))


variable {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]

variable {D : Set V}

noncomputable def orbitRepr (hD : IsConnectedTransversal T Γ D) (v : V) : V :=
  (hD.exists_mem_orbit v).choose

theorem orbitRepr_mem (hD : IsConnectedTransversal T Γ D) (v : V) : orbitRepr hD v ∈ D :=
  (hD.exists_mem_orbit v).choose_spec.1

theorem orbitRepr_mem_orbit (hD : IsConnectedTransversal T Γ D) (v : V) :
    orbitRepr hD v ∈ orbit Γ v :=
  (hD.exists_mem_orbit v).choose_spec.2

noncomputable def transl (hD : IsConnectedTransversal T Γ D) (v : V) : Γ :=
  (orbitRepr_mem_orbit hD v).choose⁻¹

theorem transl_smul_orbitRepr (hD : IsConnectedTransversal T Γ D) (v : V) :
    transl hD v • orbitRepr hD v = v :=
  inv_smul_eq_iff.mpr (orbitRepr_mem_orbit hD v).choose_spec.symm

theorem orbitRepr_eq_self (hD : IsConnectedTransversal T Γ D) {v : V} (hv : v ∈ D) :
    orbitRepr hD v = v :=
  hD.eq_of_mem_orbit _ (orbitRepr_mem hD v) _ hv (orbitRepr_mem_orbit hD v)

theorem orbitRepr_smul (hD : IsConnectedTransversal T Γ D) (γ : Γ) (v : V) :
    orbitRepr hD (γ • v) = orbitRepr hD v := by
  refine hD.eq_of_mem_orbit _ (orbitRepr_mem hD _) _ (orbitRepr_mem hD _) ?_
  rw [MulAction.orbit_eq_iff.mpr (orbitRepr_mem_orbit hD v), ← MulAction.orbit_smul γ v]
  exact orbitRepr_mem_orbit hD (γ • v)

theorem eq_of_smul_eq_smul_of_free (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1)
    {γ γ' : Γ} {v : V} (h : γ • v = γ' • v) : γ = γ' := by
  have h1 : (γ'⁻¹ * γ) • v = v := by rw [mul_smul, h, inv_smul_smul]
  have h2 := hfree _ _ h1
  rwa [inv_mul_eq_one, eq_comm] at h2

theorem transl_eq_one (hD : IsConnectedTransversal T Γ D)
    (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) {v : V} (hv : v ∈ D) :
    transl hD v = 1 := by
  apply hfree _ v
  have h := transl_smul_orbitRepr hD v
  rwa [orbitRepr_eq_self hD hv] at h

theorem mem_of_transl_eq_one (hD : IsConnectedTransversal T Γ D) {v : V}
    (h : transl hD v = 1) : v ∈ D := by
  have h1 := transl_smul_orbitRepr hD v
  rw [h, one_smul] at h1
  rw [← h1]
  exact orbitRepr_mem hD v

theorem transl_smul (hD : IsConnectedTransversal T Γ D)
    (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1) (γ : Γ) (v : V) :
    transl hD (γ • v) = γ * transl hD v := by
  refine eq_of_smul_eq_smul_of_free hfree (v := orbitRepr hD v) ?_
  rw [mul_smul, transl_smul_orbitRepr, ← orbitRepr_smul hD γ v, transl_smul_orbitRepr]


end GraphTransversal

end SimpleGraph


theorem SimpleGraph.exists_walkConnected_transversal_of_preconnected {V : Type*} {T : SimpleGraph V} {Γ : Type*} [Group Γ] [MulAction Γ V]
    (hsmul : ∀ (γ : Γ) {v w : V}, T.Adj v w → T.Adj (γ • v) (γ • w))
    (hpre : T.Preconnected) (v₀ : V) :
    ∃ D : Set V, v₀ ∈ D ∧
      (∀ v ∈ D, ∀ w ∈ D, ∃ p : T.Walk v w, ∀ x ∈ p.support, x ∈ D) ∧
      (∀ v ∈ D, ∀ w ∈ D, v ∈ MulAction.orbit Γ w → v = w) ∧
      (∀ u : V, ∃ v ∈ D, v ∈ MulAction.orbit Γ u) := by
  obtain ⟨D, h0, hD⟩ := SimpleGraph.GraphTransversal.exists_isConnectedTransversal hsmul hpre v₀
  exact ⟨D, h0, hD.walkConnected, hD.eq_of_mem_orbit, hD.exists_mem_orbit⟩


