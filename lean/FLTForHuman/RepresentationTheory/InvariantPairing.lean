/-
  An invariant pairing against an irreducible representation vanishes, given that it
  vanishes on some nonzero vector of the second factor.

  For representations `ρ : Representation k K S` and `ρ' : Representation k K S'` over a
  commutative semiring `k`, a `k`-bilinear `β : S →ₗ[k] S' →ₗ[k] X` invariant under `K`
  (`β (ρ g s) (ρ' g s') = β s s'`) is zero as soon as `β · s' = 0` for one `s' ≠ 0`,
  provided `Subrepresentation ρ'` is a simple order — i.e. `ρ'` is irreducible. The
  proof is the pin's: the vanishing vectors `{s' | ∀ s, β s s' = 0}` form a
  subrepresentation of `ρ'` (`hβ` gives stability), it is nonzero by hypothesis, and
  simplicity forces it to be everything.

  Transcribed verbatim from the pin's node
  `Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` —
  `Theorems/Thm_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero.lean`
  (the statement authority) and
  `P2M/Sol/S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero.lean`
  (36 pin lines, pinned `aa2d8b3`). The pin's public target is its `solution` tail; the
  port keeps the wrapper's statement verbatim and the pin's `P2MW.S_…` namespace, and
  drops `import Mathlib`/`P2M.Util` in favour of the specific imports below.

  Mathlib-first audit (one line per declaration; the pin's helper-free proof has no
  helper declarations to audit):

  * `Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` —
    searched mathlib for an invariant bilinear pairing on an irreducible
    `Subrepresentation` (`rg -n --multiline 'invariant.*pairing|pairing.*invariant'
    Mathlib`, the `Subrepresentation`/`IsSimpleOrder` surface of
    `RepresentationTheory/Subrepresentation.lean` and `RepresentationTheory/Irreducible.lean`,
    and `Schur` over all of `Mathlib`): nothing. Mathlib states only the vocabulary the
    proof consumes — `Subrepresentation` (`RepresentationTheory/Subrepresentation.lean:31`),
    `IsSimpleOrder (Subrepresentation ρ)` as the definition of `IsIrreducible`
    (`RepresentationTheory/Irreducible.lean:31`), and the case split
    `IsSimpleOrder.eq_bot_or_eq_top` (`Order/Atoms.lean:738`) — and its Schur lemmas are
    about `IntertwiningMap`s, not bilinear pairings.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  spec-pin: Theorems/Thm_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero.lean
  spec-pin: P2M/Sol/S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero.lean
-/

import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Order.Atoms
import Mathlib.RepresentationTheory.Subrepresentation

set_option autoImplicit false

namespace P2MW.S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero

theorem Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
    {k : Type*} [CommSemiring k] {K : Type*} [Group K]
    {S : Type*} [AddCommMonoid S] [Module k S] {S' : Type*} [AddCommMonoid S'] [Module k S']
    {X : Type*} [AddCommMonoid X] [Module k X]
    (ρ : Representation k K S) (ρ' : Representation k K S') [IsSimpleOrder (Subrepresentation ρ')]
    (β : S →ₗ[k] S' →ₗ[k] X) (hβ : ∀ (g : K) (s : S) (s' : S'), β (ρ g s) (ρ' g s') = β s s')
    (h0 : ∃ s' : S', s' ≠ 0 ∧ ∀ s : S, β s s' = 0) :
    β = 0 := by
  let N : Subrepresentation ρ' :=
    { toSubmodule :=
        { carrier := {s' | ∀ s : S, β s s' = 0}
          zero_mem' := fun s => by simp
          add_mem' := fun {a b} ha hb s => by simp [ha s, hb s]
          smul_mem' := fun c {a} ha s => by simp [ha s] }
      apply_mem_toSubmodule := fun g {s'} hs' s => by
        have := hβ g (ρ g⁻¹ s) s'
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        show β s (ρ' g s') = 0
        rw [this]; exact hs' _ }
  have hmem : ∀ s' : S', s' ∈ N ↔ ∀ s : S, β s s' = 0 := fun s' => Iff.rfl
  have hN : N ≠ ⊥ := by
    obtain ⟨s', hs'0, hs'⟩ := h0
    intro h
    have hs'N : s' ∈ N := (hmem s').mpr hs'
    rw [h] at hs'N
    exact hs'0 ((Submodule.mem_bot k).mp hs'N)
  have hT : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN
  ext s s'
  have : s' ∈ N := by rw [hT]; trivial
  exact (hmem s').mp this s

end P2MW.S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
