/-
  The generic group-theoretic engine of the `AlgebraicCurve` bifibre count.

  Two statements mathlib does not have, each stated exactly as FLT states it (the
  binders are the `Theorems/Thm_MulAction_*` / `Theorems/Thm_Subgroup_*` wrappers
  of `anthropics/fermats-last-theorem@aa2d8b3`, transcribed verbatim):

  * `MulAction.ncard_orbit_inter_orbit_mul_card` — for a finite pretransitive
    `G`-set `X` and subgroups `H₁ H₂ ≤ G` whose product is all of `G`, the
    intersection of an `H₁`-orbit with an `H₂`-orbit satisfies
    `#(H₁x₁ ∩ H₂x₂) · #X = #(H₁x₁) · #(H₂x₂)`. This is read against
    [math/009](../../../math/009-hecke-jacobian-commute.md): the place-theoretic
    instance in `WeilExchange/Bifibre.lean` is the double-fibration count that
    turns the two `restrict`-fibres into the bifibre weight
    `(e₁f₁)(e₂f₂)`.
  * `Subgroup.exists_eq_mul_of_index_inf_eq` — if
    `[G : H₁ ⊓ H₂] = [G : H₁] · [G : H₂]` then `G = H₁ · H₂` elementwise. It is
    the hypothesis the count above consumes; the index equality comes from the
    Hecke roof's `hLD` degree identity.

  Neither is in mathlib (a name search over `Mathlib/` returns nothing); the
  proofs are the pin's, transcribed. The pin keeps both proof bodies plus seven
  helpers in two files, `P2M/Sol/S_MulAction_ncard_orbit_inter_orbit_mul_card.lean`
  and `P2M/Sol/S_Subgroup_exists_eq_mul_of_index_inf_eq.lean`, which repeat the
  helpers; the port writes each helper once, `private`. The route was scouted
  before porting (`logs/ac-port.md` §5.0): all seven helpers transcribe unchanged
  against mathlib `v4.34.0`, in 3.2 s.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_MulAction_ncard_orbit_inter_orbit_mul_card.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Subgroup_exists_eq_mul_of_index_inf_eq.lean
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

set_option autoImplicit false

-- The pin's `haveI : Finite …` instance walls are kept literal (SET-1 §3).
set_option linter.style.haveILetI false

noncomputable section

open MulAction

/-! ## The orbit-intersection count -/

private theorem card_eq_mul_of_card_fiber {α β : Type*} [Finite α] [Finite β] (f : α → β) (c : ℕ)
    (hc : ∀ b, Nat.card {a // f a = b} = c) : Nat.card α = Nat.card β * c := by
  classical
  haveI := Fintype.ofFinite β
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma, Finset.sum_congr rfl
    (fun b _ => hc b), Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

private theorem card_preimage_eq_mul_of_card_fiber {α β : Type*} [Finite α] [Finite β] (f : α → β)
    (c : ℕ) (hc : ∀ b, Nat.card {a // f a = b} = c) (t : Set β) :
    Nat.card {a // f a ∈ t} = Nat.card t * c := by
  refine card_eq_mul_of_card_fiber (fun a : {a // f a ∈ t} => (⟨f a.1, a.2⟩ : t)) c ?_
  rintro ⟨b, hb⟩
  rw [← hc b]
  exact Nat.card_congr
    { toFun := fun a => ⟨a.1.1, congrArg Subtype.val a.2⟩
      invFun := fun a => ⟨⟨a.1, show f a.1 ∈ t by rw [a.2]; exact hb⟩, Subtype.ext a.2⟩
      left_inv := fun a => by ext; rfl
      right_inv := fun a => by ext; rfl }

section OrbitCount

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

private theorem card_fiber_smul_eq (x : X) (g₀ : G) :
    Nat.card {g : G // g • x = g₀ • x} = Nat.card (stabilizer G x) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨g₀⁻¹ * g.1, by rw [mem_stabilizer_iff, mul_smul, g.2, inv_smul_smul]⟩
      invFun := fun s => ⟨g₀ * s.1, by rw [mul_smul, s.2]⟩
      left_inv := fun g => by ext; simp
      right_inv := fun s => by ext; simp }

private theorem card_smul_mem_eq [Finite G] (H : Subgroup G) (x : X) (B : Set X) :
    Nat.card {h : H // (h : G) • x ∈ B} = (orbit H x ∩ B).ncard * Nat.card (stabilizer H x) := by
  haveI : Finite (orbit H x) := Set.finite_range _ |>.to_subtype

  have hfib : ∀ o : orbit H x, Nat.card {h : H // (⟨h • x, mem_orbit x h⟩ : orbit H x) = o} =
      Nat.card (stabilizer H x) := by
    rintro ⟨_, ⟨h₀, rfl⟩⟩
    rw [← card_fiber_smul_eq x h₀]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun h => by simp [Subtype.ext_iff])
  have := card_preimage_eq_mul_of_card_fiber (fun h : H => (⟨h • x, mem_orbit x h⟩ : orbit H x))
    (Nat.card (stabilizer H x)) hfib {o | (o : X) ∈ B}
  rw [← Nat.card_coe_set_eq]
  convert this using 2
  · rfl
  exact Nat.card_congr
    { toFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      invFun := fun o => ⟨o.1.1, o.1.2, o.2⟩
      left_inv := fun y => rfl
      right_inv := fun o => rfl }

private theorem card_fiber_psi_eq (H₁ H₂ : Subgroup G)
    (hprod : ∀ g : G, ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂) (g : G) :
    Nat.card {p : H₁ × H₂ // (p.2 : G)⁻¹ * p.1 = g} = Nat.card (H₁ ⊓ H₂ : Subgroup G) := by

  obtain ⟨a₁, ha₁, a₂, ha₂, hg⟩ := hprod g⁻¹
  have hg' : (a₂ : G)⁻¹ * a₁⁻¹ = g := by rw [← mul_inv_rev, ← hg, inv_inv]
  refine Nat.card_congr
    { toFun := fun p => ⟨(p.1.1 : G) * a₁, ?_⟩
      invFun := fun k => ⟨(⟨k.1 * a₁⁻¹, ?_⟩, ⟨k.1 * a₂, ?_⟩), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  ·
    obtain ⟨⟨p₁, p₂⟩, hp⟩ := p
    have hp₁ : (p₁ : G) = p₂ * g := by rw [← hp, mul_inv_cancel_left]
    refine Subgroup.mem_inf.mpr ⟨H₁.mul_mem p₁.2 ha₁, ?_⟩
    rw [hp₁, ← hg', show (p₂ : G) * ((a₂ : G)⁻¹ * a₁⁻¹) * a₁ = p₂ * a₂⁻¹ by group]
    exact H₂.mul_mem p₂.2 (H₂.inv_mem ha₂)
  · exact H₁.mul_mem (Subgroup.mem_inf.mp k.2).1 (H₁.inv_mem ha₁)
  · exact H₂.mul_mem (Subgroup.mem_inf.mp k.2).2 ha₂
  · show ((k : G) * a₂)⁻¹ * (k * a₁⁻¹) = g
    rw [← hg']; group
  · rintro ⟨⟨p₁, p₂⟩, hp⟩
    have hp₁ : (p₁ : G) = p₂ * g := by rw [← hp, mul_inv_cancel_left]
    ext
    · simp
    · simp only
      rw [hp₁, ← hg']; group
  · intro k; ext; simp

private theorem ncard_orbit_inter_orbit_mul_card_eq [Finite G] [IsPretransitive G X]
    (H₁ H₂ : Subgroup G)
    (hprod : ∀ g : G, ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂) (x₁ x₂ : X) :
    (orbit H₁ x₁ ∩ orbit H₂ x₂).ncard * Nat.card X = (orbit H₁ x₁).ncard * (orbit H₂ x₂).ncard := by
  haveI : Finite X := Finite.of_surjective (fun g : G => g • x₁) (surjective_smul G x₁)
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq G x₁ x₂

  let A := {p : H₁ × H₂ // (p.1 : G) • x₁ = (p.2 : G) • x₂}

  have hA₁ : Nat.card A = Nat.card (stabilizer G x₁) * Nat.card (H₁ ⊓ H₂ : Subgroup G) := by
    have h := card_preimage_eq_mul_of_card_fiber (fun p : H₁ × H₂ => (p.2 : G)⁻¹ * p.1)
      (Nat.card (H₁ ⊓ H₂ : Subgroup G)) (card_fiber_psi_eq H₁ H₂ hprod) {g | g • x₁ = x₂}
    rw [show Nat.card {g | g • x₁ = x₂} = Nat.card (stabilizer G x₁) from by
      rw [← hg₀]; exact card_fiber_smul_eq x₁ g₀] at h
    rw [← h]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by
      simp only [Set.mem_ofPred_eq, mul_smul, inv_smul_eq_iff])

  have hA₂ : Nat.card A = (orbit H₁ x₁ ∩ orbit H₂ x₂).ncard * Nat.card (stabilizer H₂ x₂)
      * Nat.card (stabilizer H₁ x₁) := by
    let M := {h₂ : H₂ // (h₂ : G) • x₂ ∈ orbit H₁ x₁}
    have hM : Nat.card M = (orbit H₁ x₁ ∩ orbit H₂ x₂).ncard * Nat.card (stabilizer H₂ x₂) := by
      rw [Set.inter_comm]; exact card_smul_mem_eq H₂ x₂ (orbit H₁ x₁)
    rw [← hM]
    refine card_eq_mul_of_card_fiber (fun a : A => (⟨a.1.2, ⟨a.1.1, a.2⟩⟩ : M)) _ ?_
    rintro ⟨h₂, ⟨h₁, hh⟩⟩

    have hh' : (h₁ : G) • x₁ = (h₂ : G) • x₂ := hh
    rw [← card_fiber_smul_eq x₁ (h₁ : H₁)]
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1.1.1, ?_⟩
        invFun := fun h => ⟨⟨(h.1, h₂), ?_⟩, rfl⟩
        left_inv := ?_
        right_inv := ?_ }
    ·
      have e2 : a.1.1.2 = h₂ := congrArg (fun m : M => (m : H₂)) a.2
      show ((a.1.1.1 : H₁) : G) • x₁ = ((h₁ : H₁) : G) • x₁
      rw [hh']; exact a.1.2.trans (by rw [e2])
    · show ((h.1 : H₁) : G) • x₁ = (h₂ : G) • x₂
      rw [← hh']; exact h.2
    · rintro ⟨⟨⟨a₁, a₂⟩, ha⟩, ha'⟩
      have e2 : a₂ = h₂ := congrArg (fun m : M => (m : H₂)) ha'
      subst e2; rfl
    · intro h; rfl

  have hO₁ : (orbit H₁ x₁).ncard * Nat.card (stabilizer H₁ x₁) = Nat.card H₁ := by
    rw [← index_stabilizer H₁ x₁, mul_comm, Subgroup.card_mul_index]
  have hO₂ : (orbit H₂ x₂).ncard * Nat.card (stabilizer H₂ x₂) = Nat.card H₂ := by
    rw [← index_stabilizer H₂ x₂, mul_comm, Subgroup.card_mul_index]
  have hX : Nat.card X * Nat.card (stabilizer G x₁) = Nat.card G := by
    rw [← index_stabilizer_of_transitive G x₁, mul_comm, Subgroup.card_mul_index]

  have hGK : Nat.card H₁ * Nat.card H₂ = Nat.card G * Nat.card (H₁ ⊓ H₂ : Subgroup G) := by
    rw [← Nat.card_prod]
    exact card_eq_mul_of_card_fiber (fun p : H₁ × H₂ => (p.2 : G)⁻¹ * p.1) _
      (card_fiber_psi_eq H₁ H₂ hprod)

  have hpos : 0 < Nat.card (stabilizer H₂ x₂) * Nat.card (stabilizer H₁ x₁)
      * Nat.card (stabilizer G x₁) :=
    Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (orbit H₁ x₁ ∩ orbit H₂ x₂).ncard * Nat.card X
        * (Nat.card (stabilizer H₂ x₂) * Nat.card (stabilizer H₁ x₁)
          * Nat.card (stabilizer G x₁))
      = ((orbit H₁ x₁ ∩ orbit H₂ x₂).ncard * Nat.card (stabilizer H₂ x₂)
          * Nat.card (stabilizer H₁ x₁))
          * (Nat.card X * Nat.card (stabilizer G x₁)) := by ring
    _ = Nat.card A * Nat.card G := by rw [hA₂, hX]
    _ = Nat.card (stabilizer G x₁) * (Nat.card G * Nat.card (H₁ ⊓ H₂ : Subgroup G)) := by
          rw [hA₁]; ring
    _ = Nat.card (stabilizer G x₁) * (Nat.card H₁ * Nat.card H₂) := by rw [hGK]
    _ = (orbit H₁ x₁).ncard * (orbit H₂ x₂).ncard
        * (Nat.card (stabilizer H₂ x₂) * Nat.card (stabilizer H₁ x₁)
          * Nat.card (stabilizer G x₁)) := by
          rw [← hO₁, ← hO₂]; ring

end OrbitCount

/-- **The orbit-intersection count.** For a finite pretransitive `G`-set `X`, two
subgroups `H₁ H₂ ≤ G` whose product is all of `G`, and `x₁ x₂ : X`, the `H₁`-orbit
of `x₁` and the `H₂`-orbit of `x₂` intersect in a set of `ncard` equal to
`#(H₁x₁) · #(H₂x₂) / #X`. Read against
[math/009](../../../math/009-hecke-jacobian-commute.md): its double-fibration
proof (`Nat.card A` computed one way over `H₁ × H₂` and another over the second
orbit) is exactly the place-theoretic count that
`Place.sum_ramificationIndex_mul_inertiaDeg_bifiber` runs at
`X = MulAction.orbit (M ≃ₐ[F] M) P₁`. -/
theorem MulAction.ncard_orbit_inter_orbit_mul_card {G : Type*} [Group G] {X : Type*}
    [MulAction G X] [Finite G] [MulAction.IsPretransitive G X] (H₁ H₂ : Subgroup G)
    (hprod : ∀ g : G, ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂) (x₁ x₂ : X) :
    (MulAction.orbit H₁ x₁ ∩ MulAction.orbit H₂ x₂).ncard * Nat.card X =
      (MulAction.orbit H₁ x₁).ncard * (MulAction.orbit H₂ x₂).ncard :=
  ncard_orbit_inter_orbit_mul_card_eq H₁ H₂ hprod x₁ x₂

/-! ## The index condition implies the product is everything -/

private theorem stabilizer_mk_one_eq {G : Type*} [Group G] (H₁ H₂ : Subgroup G) :
    stabilizer H₂ ((1 : G) : G ⧸ H₁) = H₁.subgroupOf H₂ := by
  ext h
  have key : h • ((1 : G) : G ⧸ H₁) = (((h : G) * 1 : G) : G ⧸ H₁) := rfl
  rw [mem_stabilizer_iff, Subgroup.mem_subgroupOf, key, mul_one, QuotientGroup.eq, mul_one,
    inv_mem_iff]

private theorem exists_eq_mul_of_index_inf_eq' {G : Type*} [Group G] [Finite G]
    (H₁ H₂ : Subgroup G) (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) :
    ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ := by

  have hrel : H₁.relIndex H₂ = H₁.index := by
    have h1 : H₁.relIndex H₂ * H₂.index = (H₁ ⊓ H₂).index := by
      rw [← Subgroup.inf_relIndex_right, Subgroup.relIndex_mul_index inf_le_right]
    rw [h] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
  have hcard : (orbit H₂ ((1 : G) : G ⧸ H₁)).ncard = (Set.univ : Set (G ⧸ H₁)).ncard := by
    rw [← index_stabilizer, stabilizer_mk_one_eq, Set.ncard_univ, ← Subgroup.index_eq_card]
    exact hrel
  have huniv : orbit H₂ ((1 : G) : G ⧸ H₁) = Set.univ :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hcard.ge Set.finite_univ
  have hmem : ((g⁻¹ : G) : G ⧸ H₁) ∈ orbit H₂ ((1 : G) : G ⧸ H₁) := huniv ▸ Set.mem_univ _
  obtain ⟨h₂, hh₂⟩ := mem_orbit_iff.mp hmem
  have key : h₂ • ((1 : G) : G ⧸ H₁) = (((h₂ : G) * 1 : G) : G ⧸ H₁) := rfl
  rw [key, mul_one, QuotientGroup.eq] at hh₂

  refine ⟨g * h₂, ?_, (h₂ : G)⁻¹, H₂.inv_mem h₂.2, by group⟩
  have := H₁.inv_mem hh₂
  rwa [mul_inv_rev, inv_inv, inv_inv] at this

/-- **The index equality gives the product decomposition.** This is the `hprod`
hypothesis of the count above: it is supplied in the bifibre assembly by the
Hecke roof's degree identity `Module.finrank F E = Module.finrank F F₁ *
Module.finrank F F₂`, read through `index_range_resHom` and
`Subgroup.index_dvd_of_le`. -/
theorem Subgroup.exists_eq_mul_of_index_inf_eq {G : Type*} [Group G] [Finite G]
    (H₁ H₂ : Subgroup G) (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) :
    ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂ :=
  exists_eq_mul_of_index_inf_eq' H₁ H₂ h g
