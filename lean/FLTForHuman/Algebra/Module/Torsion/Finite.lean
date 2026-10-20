/-
  The `a ^ k`-torsion of a module is finite when the `a`-torsion is:

      `Finite (Submodule.torsionBy R M a) → Finite (Submodule.torsionBy R M (a ^ k))`.

  The port of the pin leaf `Submodule.finite_torsionBy_pow_of_finite_torsionBy` (45 pin
  lines), statement from its `Theorems/` wrapper and proof from the matching
  `P2M/Sol/S_…` file (pinned `aa2d8b3`). Split out of the former `Algebra/TorsionFinite`
  module (2026-10-20): its other half — the valuation-ring annihilator — is a different
  subject and lives in `RingTheory/Valuation/FiniteModule.lean`, where the object
  (`ValuationRing`) is.

  The mathematics is a fibre decomposition: the `a ^ (k+1)`-torsion maps onto the
  `a ^ k`-torsion (finite, by induction) with fibres `{x | a ^ k • x = y}` that are
  translates of the `a ^ k`-torsion, so the total is finite.

  Assumes: mathlib `v4.34.0` only. Mathlib has no such statement (`rg -n
  "finite_torsionBy_pow|torsionBy_pow" Mathlib/` is empty, 2026-10-20).

  spec-pin: Theorems/Thm_Submodule_finite_torsionBy_pow_of_finite_torsionBy.lean
  spec-pin: P2M/Sol/S_Submodule_finite_torsionBy_pow_of_finite_torsionBy.lean
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem Submodule.finite_torsionBy_pow_of_finite_torsionBy
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : R)
    (h : Finite (Submodule.torsionBy R M a)) (k : ℕ) :
    Finite (Submodule.torsionBy R M (a ^ k)) := by
  have hS : {x : M | a • x = 0}.Finite := by
    have : {x : M | a • x = 0} = (Submodule.torsionBy R M a : Set M) := by
      ext x; simp
    rw [this]
    exact Set.toFinite _
  suffices H : ∀ k : ℕ, {x : M | a ^ k • x = 0}.Finite by
    have hk := H k
    have : {x : M | a ^ k • x = 0} = (Submodule.torsionBy R M (a ^ k) : Set M) := by
      ext x; simp
    rw [this] at hk
    exact hk.to_subtype
  intro k
  induction k with
  | zero =>
      refine (Set.finite_singleton (0 : M)).subset ?_
      intro x hx
      simpa using hx
  | succ k ih =>

      have hfib : ∀ y : M, {x : M | a ^ k • x = y}.Finite := by
        intro y
        rcases Set.eq_empty_or_nonempty {x : M | a ^ k • x = y} with he | ⟨x₀, hx₀⟩
        · rw [he]; exact Set.finite_empty
        · refine (ih.image fun s => x₀ + s).subset ?_
          intro x hx
          simp only [Set.mem_ofPred_eq] at hx hx₀
          refine ⟨x - x₀, ?_, by abel_nf⟩
          simp only [Set.mem_ofPred_eq, smul_sub, hx, hx₀, sub_self]

      refine (hS.biUnion fun y _ => hfib y).subset ?_
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      refine Set.mem_biUnion (x := a ^ k • x) ?_ rfl
      simp only [Set.mem_ofPred_eq, smul_smul, ← pow_succ', hx]
