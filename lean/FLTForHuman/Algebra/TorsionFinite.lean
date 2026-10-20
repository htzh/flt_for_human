/-
  Two torsion supplements:

  * `Submodule.finite_torsionBy_pow_of_finite_torsionBy` — if the `a`-torsion of
    `M` is finite then so is the `a ^ k`-torsion;
  * `ValuationRing.exists_ne_zero_forall_smul_eq_zero_of_module_finite` — a finite
    module over a valuation ring has a single nonzero annihilator of its whole
    torsion submodule.

  The ports of the pin leaves `Submodule.finite_torsionBy_pow_of_finite_torsionBy`
  (45 pin lines) and `ValuationRing.exists_ne_zero_forall_smul_eq_zero_of_module_finite`
  (52 pin lines), together with the statements of their `Theorems/` wrappers.
  The two share their area (torsion submodules) and nothing else; they are grouped
  in one module under the order's §5 licence for the sub-80-line entries.

  The mathematics of the first is a fibre decomposition: the `a ^ (k+1)`-torsion
  maps onto the `a ^ k`-torsion (finite, by induction) with fibres `{x | a ^ k • x = y}`
  that are translates of the `a ^ k`-torsion; so the total is finite.

  The mathematics of the second is that over a valuation ring the quotient by the
  torsion submodule `T` is torsion-free, hence flat (`IsBezout`), hence free, hence
  projective; a splitting of `M ⧸ T → M` then exhibits `T` as the range of
  `1 - s ∘ mkQ`, so `T` is finite, and `annihilator_top_inter_nonZeroDivisors`
  produces one nonzero `a` killing it.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has neither statement — `rg -n
  "finite_torsionBy_pow|torsionBy_pow"` and `rg -n "forall_smul_eq_zero_of_module_finite"`
  over `Mathlib/` find nothing. Both proofs are assembled from mathlib lemmas that
  *are* imported rather than restated: `Submodule.QuotientTorsion.torsion_eq_bot`,
  `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`,
  `Module.free_of_flat_of_isLocalRing`, `Module.projective_lifting_property`,
  `Submodule.annihilator_top_inter_nonZeroDivisors`.

  Drift: the pin's file-level `set_option maxHeartbeats 1600000` on the torsionBy
  node is dropped (the port elaborates inside the 200,000 edit-loop budget).
  Imports: the pin's bare `import Mathlib` became the five modules the two proofs
  name.

  spec-pin: Theorems/Thm_Submodule_finite_torsionBy_pow_of_finite_torsionBy.lean
  spec-pin: P2M/Sol/S_Submodule_finite_torsionBy_pow_of_finite_torsionBy.lean
  spec-pin: Theorems/Thm_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite.lean
  spec-pin: P2M/Sol/S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite.lean
-/
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Module

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

namespace ValuationRing

open Submodule

theorem exists_ne_zero_forall_smul_eq_zero_of_module_finite
    {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ a : R, a ≠ 0 ∧ ∀ m : M, (∃ c : R, c ≠ 0 ∧ c • m = 0) → a • m = 0 := by
  classical

  set T : Submodule R M := torsion R M with hT
  have : Module.Finite R (M ⧸ T) := inferInstance
  have : Module.Flat R (M ⧸ T) :=
    (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr (Submodule.QuotientTorsion.torsion_eq_bot)
  have : Module.Free R (M ⧸ T) := Module.free_of_flat_of_isLocalRing
  have : Module.Projective R (M ⧸ T) := Module.Projective.of_free

  obtain ⟨s, hs⟩ := Module.projective_lifting_property T.mkQ (LinearMap.id : M ⧸ T →ₗ[R] M ⧸ T)
    (Submodule.mkQ_surjective T)

  set φ : M →ₗ[R] M := LinearMap.id - s ∘ₗ T.mkQ with hφ
  have hrange : LinearMap.range φ = T := by
    apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      have : T.mkQ (φ m) = 0 := by
        have h1 : T.mkQ (s (T.mkQ m)) = T.mkQ m := by
          have := LinearMap.congr_fun hs (T.mkQ m)
          simpa using this
        simp only [Submodule.mkQ_apply] at h1
        simp only [hφ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
          Submodule.mkQ_apply, Submodule.Quotient.mk_sub, h1, sub_self]
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using this
    · intro t ht
      refine ⟨t, ?_⟩
      have : T.mkQ t = 0 := by simpa [Submodule.Quotient.mk_eq_zero] using ht
      simp [hφ, this]
  have hTfin : Module.Finite R T := by
    rw [← hrange]
    exact Module.Finite.range φ

  have hTtors : Module.IsTorsion R T := by
    intro t
    obtain ⟨c, hc⟩ := (mem_torsion_iff (t : M)).mp t.2
    exact ⟨c, Subtype.ext (by simpa using hc)⟩
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hTtors
  refine ⟨a, nonZeroDivisors.ne_zero ha0, fun m hm => ?_⟩
  obtain ⟨c, hc0, hcm⟩ := hm
  have hmT : m ∈ T := (mem_torsion_iff m).mpr ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc0⟩, hcm⟩
  have := Submodule.mem_annihilator.mp ha ⟨m, hmT⟩ Submodule.mem_top
  simpa using congrArg Subtype.val this

end ValuationRing
