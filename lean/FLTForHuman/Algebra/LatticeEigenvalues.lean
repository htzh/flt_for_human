/-
  Rational coordinates of lattice eigenvectors.

  Two generic algebra facts the coefficient ring of a weight-one newform is
  built from:

  * `Module.Basis.repr_mem_range_ratCast_of_forall_dual` — a vector of a `ℂ`-vector
    space all of whose pairings against a separating dual family are rational has
    rational coordinates in any basis whose basis vectors pair rationally.
  * `Submodule.moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top` — if a
    family of `ℂ`-linear maps preserves a finitely generated `ℤ`-lattice spanning
    the space and has `v` as a joint eigenvector, then the `ℤ`-subalgebra generated
    by the eigenvalues is finite as a `ℤ`-module.

  Both statements are the pin's `Theorems/` wrappers verbatim; the proofs are
  transcribed from the `P2M/Sol/S_*` files, pinned `aa2d8b3`:

  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Module_Basis_repr_mem_range_ratCast_of_forall_dual.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top.lean

  The pin's blanket `import Mathlib` and the `P2M.Util` shims are replaced by the
  specific mathlib modules actually used. The pin-internal `RatCoords`/
  `LatticeEigenInt` helpers are `private` here, so the module's public surface is
  exactly the two target statements.
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Noetherian.Basic
import FLTForHuman.Algebra.IntegralExtensionCharacters

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing; keep them literal (port convention).
set_option linter.style.haveILetI false

noncomputable section

open scoped BigOperators

namespace RatCoords

private theorem exists_sum_smul_eq_of_algebraMap {K : Type*} [Field K] [Algebra K ℂ]
    {ι E : Type*} [Fintype ι] [Fintype E]
    (col : ι → E → K) (β : E → K) (c : ι → ℂ)
    (hc : ∑ i, c i • ((algebraMap K ℂ) ∘ col i) = (algebraMap K ℂ) ∘ β) :
    ∃ x : ι → K, ∑ i, x i • col i = β := by
  classical
  haveI : FaithfulSMul K ℂ :=
    (faithfulSMul_iff_algebraMap_injective K ℂ).mpr (algebraMap K ℂ).injective
  rw [← Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range col)
  rw [← hs_span]
  by_contra hβ

  let fam : Option s → E → K := fun o => Option.casesOn o β (fun m => (m : E → K))
  have hfam : LinearIndependent K fam := by
    rw [linearIndependent_option]
    refine ⟨?_, ?_⟩
    · exact hs_li
    · show β ∉ Submodule.span K (Set.range (fun m : s => (m : E → K)))
      rwa [Subtype.range_coe_subtype, Set.ofPred_mem_eq]

  have hfamC : LinearIndependent ℂ (fun o => (algebraMap K ℂ) ∘ fam o) :=
    (linearIndependent_algebraMap_comp_iff (v := fam)).mpr hfam
  rw [linearIndependent_option] at hfamC
  apply hfamC.2

  show (algebraMap K ℂ) ∘ β ∈
    Submodule.span ℂ (Set.range (fun m : s => (algebraMap K ℂ) ∘ (m : E → K)))
  rw [← hc]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_

  have hcol : col i ∈ Submodule.span K s := by
    rw [hs_span]; exact Submodule.subset_span (Set.mem_range_self i)
  let Φ : (E → K) →ₗ[K] (E → ℂ) :=
    { toFun := fun y => (algebraMap K ℂ) ∘ y
      map_add' := fun y z => by ext e; simp
      map_smul' := fun r y => by ext e; simp [Algebra.smul_def] }
  have h1 : Φ (col i) ∈ Submodule.span K (Φ '' s) := by
    rw [← Submodule.map_span]; exact Submodule.mem_map_of_mem hcol
  have h2 : Submodule.span K (Φ '' s) ≤
      (Submodule.span ℂ (Φ '' s)).restrictScalars K := Submodule.span_le_restrictScalars K ℂ _
  have h3 := h2 h1
  rw [Submodule.restrictScalars_mem] at h3
  have h4 : Φ '' s = Set.range (fun m : s => (algebraMap K ℂ) ∘ (m : E → K)) := by
    ext y
    simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_prop]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  rw [h4] at h3
  exact h3

private theorem exists_finset_separating {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [Module.Free ℂ V]
    {A : Type*} (φ : A → V →ₗ[ℂ] ℂ) (hinj : ∀ x : V, (∀ a : A, φ a x = 0) → x = 0) :
    ∃ s : Set (V →ₗ[ℂ] ℂ), s.Finite ∧ s ⊆ Set.range φ ∧
      ∀ x : V, (∀ ψ ∈ s, ψ x = 0) → x = 0 := by
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℂ (Set.range φ)
  refine ⟨s, hs_li.setFinite, hs_sub, fun x hx => hinj x fun a => ?_⟩
  have ha : φ a ∈ Submodule.span ℂ s := by
    rw [hs_span]; exact Submodule.subset_span (Set.mem_range_self a)
  refine Submodule.span_induction (p := fun ψ _ => ψ x = 0) ?_ ?_ ?_ ?_ ha
  · exact fun ψ hψ => hx ψ hψ
  · simp
  · intro ψ χ _ _ hψ hχ; simp [hψ, hχ]
  · intro r ψ _ hψ; simp [hψ]

end RatCoords

namespace Module.Basis

/-- **Rational coordinates of a vector with rational dual pairings.** Stated
verbatim from `Theorems/Thm_Module_Basis_repr_mem_range_ratCast_of_forall_dual.lean`. -/
theorem repr_mem_range_ratCast_of_forall_dual
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {A : Type*} (φ : A → V →ₗ[ℂ] ℂ)
    (hinj : ∀ x : V, (∀ a : A, φ a x = 0) → x = 0)
    (hφb : ∀ (a : A) (i : ι), φ a (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (h : V) (hh : ∀ a : A, φ a h ∈ Set.range ((↑) : ℚ → ℂ)) (i : ι) :
    b.repr h i ∈ Set.range ((↑) : ℚ → ℂ) := by
  classical
  haveI : Module.Finite ℂ V := Module.Finite.of_basis b
  haveI : Module.Free ℂ V := Module.Free.of_basis b
  obtain ⟨s, hs_fin, hs_sub, hs_sep⟩ := RatCoords.exists_finset_separating φ hinj
  haveI : Fintype s := hs_fin.fintype

  choose aOf haOf using hs_sub

  choose q hq using hφb
  choose r hr using hh

  let col : ι → s → ℚ := fun i e => q (aOf e.2) i
  let β : s → ℚ := fun e => r (aOf e.2)

  let c : ι → ℂ := b.equivFun h
  have hsum : h = ∑ i, c i • b i := (b.sum_equivFun h).symm
  have hc : ∑ i, c i • ((algebraMap ℚ ℂ) ∘ col i) = (algebraMap ℚ ℂ) ∘ β := by
    funext e
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      eq_ratCast, col, β, hq, hr]
    rw [haOf e.2]
    conv_rhs => rw [hsum]
    simp [map_sum, map_smul, smul_eq_mul]
  obtain ⟨x, hx⟩ := RatCoords.exists_sum_smul_eq_of_algebraMap col β c hc

  let h' : V := ∑ i, ((x i : ℚ) : ℂ) • b i
  have hval : ∀ e : s, (e : V →ₗ[ℂ] ℂ) h' = (e : V →ₗ[ℂ] ℂ) h := by
    intro e
    have hxe := congrFun hx e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, β] at hxe

    have hxeC : ∑ i, ((x i : ℚ) : ℂ) * (q (aOf e.2) i : ℂ) = (r (aOf e.2) : ℂ) := by
      have := congrArg (fun t : ℚ => (t : ℂ)) hxe
      push_cast at this
      exact this
    simp only [hq, hr] at hxeC
    rw [← haOf e.2]
    simp only [h', map_sum, map_smul, smul_eq_mul]
    exact hxeC
  have heq : h' = h := by
    have h0 : h' - h = 0 := hs_sep _ fun ψ hψ => by
      have := hval ⟨ψ, hψ⟩
      simp [this]
    exact sub_eq_zero.mp h0
  have hcoord : b.repr h i = ((x i : ℚ) : ℂ) := by
    rw [← heq]
    simp [h', map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply]
  exact ⟨x i, hcoord.symm⟩

end Module.Basis

namespace LatticeEigenInt

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem isAddTorsionFree_submodule (Λ : Submodule ℤ V) : IsAddTorsionFree Λ := by
  refine ⟨fun n hn a b hab => ?_⟩
  apply Subtype.ext
  have h : (n : ℂ) • ((a : V) - b) = 0 := by
    have hab' : n • (a : V) = n • (b : V) := by
      have := congrArg (fun x : Λ => (x : V)) hab
      simpa using this
    rw [smul_sub, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hab', sub_self]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have := (smul_eq_zero.mp h).resolve_left hn'
  exact sub_eq_zero.mp this

private theorem moduleFinite_end (Λ : Submodule ℤ V) (hΛfg : Λ.FG) :
    Module.Finite ℤ (Λ →ₗ[ℤ] Λ) := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛfg
  haveI : IsAddTorsionFree Λ := isAddTorsionFree_submodule Λ
  haveI : Module.IsTorsionFree ℤ Λ := inferInstance
  haveI : Module.Free ℤ Λ := inferInstance
  exact Module.Finite.linearMap ℤ ℤ Λ Λ

private def opAlg {J : Type*} (S : J → V →ₗ[ℂ] V) : Subalgebra ℤ (V →ₗ[ℂ] V) :=
  Algebra.adjoin ℤ (Set.range S)

private theorem opAlg_preserves (Λ : Submodule ℤ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) :
    ∀ T ∈ opAlg S, ∀ x ∈ Λ, T x ∈ Λ := by
  intro T hT
  refine Algebra.adjoin_induction (p := fun T _ => ∀ x ∈ Λ, T x ∈ Λ) ?_ ?_ ?_ ?_ hT
  · rintro _ ⟨j, rfl⟩ x hx; exact hS j x hx
  · intro n x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact Λ.smul_mem n hx
  · intro T₁ T₂ _ _ h₁ h₂ x hx
    rw [LinearMap.add_apply]; exact Λ.add_mem (h₁ x hx) (h₂ x hx)
  · intro T₁ T₂ _ _ h₁ h₂ x hx
    rw [Module.End.mul_apply]; exact h₁ _ (h₂ x hx)

private noncomputable def res (Λ : Submodule ℤ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) : opAlg S →ₗ[ℤ] (Λ →ₗ[ℤ] Λ) where
  toFun T := (T.1.restrictScalars ℤ).restrict (fun x hx => opAlg_preserves Λ S hS T.1 T.2 x hx)
  map_add' T₁ T₂ := by ext x; rfl
  map_smul' n T := by ext x; rfl

private theorem res_apply (Λ : Submodule ℤ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) (T : opAlg S) (x : Λ) :
    ((res Λ S hS T x : Λ) : V) = T.1 x := rfl

private theorem res_injective (Λ : Submodule ℤ V) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) :
    Function.Injective (res Λ S hS) := by
  intro T₁ T₂ h
  apply Subtype.ext
  apply LinearMap.ext_on hΛspan
  intro x hx
  have := congrArg (fun F : Λ →ₗ[ℤ] Λ => ((F ⟨x, hx⟩ : Λ) : V)) h
  simpa [res_apply] using this

private theorem moduleFinite_opAlg [FiniteDimensional ℂ V] (Λ : Submodule ℤ V) (hΛfg : Λ.FG)
    (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) :
    Module.Finite ℤ (opAlg S) := by
  haveI := moduleFinite_end Λ hΛfg
  exact Module.Finite.of_injective (res Λ S hS) (res_injective Λ hΛspan S hS)

private def eigAlg (v : V) : Subalgebra ℤ (V →ₗ[ℂ] V) where
  carrier := {T | ∃ μ : ℂ, T v = μ • v}
  mul_mem' := by
    rintro T₁ T₂ ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩
    refine ⟨μ₂ * μ₁, ?_⟩
    rw [Module.End.mul_apply, h₂, map_smul, h₁, smul_smul]
  add_mem' := by
    rintro T₁ T₂ ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩
    exact ⟨μ₁ + μ₂, by rw [LinearMap.add_apply, h₁, h₂, add_smul]⟩
  algebraMap_mem' n := ⟨n, by
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
      Int.cast_smul_eq_zsmul]⟩

private theorem mem_eigAlg {v : V} {T : V →ₗ[ℂ] V} : T ∈ eigAlg v ↔ ∃ μ : ℂ, T v = μ • v :=
  Iff.rfl

private noncomputable def ev (v : V) (T : eigAlg v) : ℂ := (mem_eigAlg.mp T.2).choose

private theorem ev_spec (v : V) (T : eigAlg v) : T.1 v = ev v T • v :=
  (mem_eigAlg.mp T.2).choose_spec

private theorem ev_unique {v : V} (hv0 : v ≠ 0) (T : eigAlg v) {μ : ℂ} (h : T.1 v = μ • v) :
    ev v T = μ := by
  have h1 := ev_spec v T
  rw [h] at h1
  exact (smul_left_injective ℂ hv0 h1).symm

private noncomputable def evHom {v : V} (hv0 : v ≠ 0) : eigAlg v →+* ℂ where
  toFun := ev v
  map_one' := ev_unique hv0 _ (by simp)
  map_mul' T₁ T₂ := ev_unique hv0 _ (by
    show T₁.1 (T₂.1 v) = _
    rw [ev_spec v T₂, map_smul, ev_spec v T₁, smul_smul, mul_comm])
  map_zero' := ev_unique hv0 _ (by simp)
  map_add' T₁ T₂ := ev_unique hv0 _ (by
    show T₁.1 v + T₂.1 v = _
    rw [ev_spec v T₁, ev_spec v T₂, add_smul])

end LatticeEigenInt

namespace Submodule

/-- **Finiteness of the eigenvalue algebra of a lattice eigenvector.** Stated
verbatim from
`Theorems/Thm_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top.lean`. -/
theorem moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
    {J : Type*} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ)
    (lam : J → ℂ) (v : V) (hv0 : v ≠ 0) (hv : ∀ j : J, S j v = lam j • v) :
    Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam)) := by
  haveI := LatticeEigenInt.moduleFinite_opAlg Λ hΛfg hΛspan S hS

  have hle : LatticeEigenInt.opAlg S ≤ LatticeEigenInt.eigAlg v := by
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    exact ⟨lam j, hv j⟩

  let χ : LatticeEigenInt.opAlg S →+* ℂ :=
    (LatticeEigenInt.evHom hv0).comp (Subalgebra.inclusion hle).toRingHom

  let χl : LatticeEigenInt.opAlg S →ₗ[ℤ] ℂ := χ.toIntAlgHom.toLinearMap

  have hfin : Module.Finite ℤ (LinearMap.range χl) := Module.Finite.range χl
  have hsub : (Subalgebra.toSubmodule (Algebra.adjoin ℤ (Set.range lam))) ≤
      LinearMap.range χl := by

    have hr : LinearMap.range χl =
        Subalgebra.toSubmodule (χ.toIntAlgHom.range) := by
      ext z
      simp only [LinearMap.mem_range, Subalgebra.mem_toSubmodule, AlgHom.mem_range]
      rfl
    rw [hr]
    apply Subalgebra.toSubmodule.monotone
    apply Algebra.adjoin_le
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨S j, Algebra.subset_adjoin ⟨j, rfl⟩⟩, ?_⟩
    show LatticeEigenInt.ev v ⟨S j, _⟩ = lam j
    exact LatticeEigenInt.ev_unique hv0 _ (hv j)

  haveI : IsNoetherian ℤ (LinearMap.range χl) :=
    isNoetherian_of_isNoetherianRing_of_finite ℤ _
  let f : Algebra.adjoin ℤ (Set.range lam) →ₗ[ℤ] LinearMap.range χl :=
    { toFun := fun x => ⟨x.1, hsub x.2⟩
      map_add' := fun x y => rfl
      map_smul' := fun n x => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun z : LinearMap.range χl => (z : ℂ)) hxy
    exact this
  exact Module.Finite.of_injective f hf

end Submodule

/-! ## Rational eigenconjugation

The pin's `S_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast.lean`
(131 lines): over the rational coordinate hypothesis of node 1, a Galois
automorphism of `ℂ` fixing the coefficient algebra `R` carries a joint
eigenvector to a joint eigenvector with the conjugated eigenvalues. The three
pin-internal helpers are `private`; the public surface is the target statement. -/

namespace RationalEigenConj

private theorem exists_ringEquiv_apply_eq (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R]
    (τ : R →+* ℂ) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x : R, σ (x : ℂ) = τ x := by

  have hRle : R ≤ integralClosure ℤ ℂ := fun x hx => by
    have h : IsIntegral ℤ (⟨x, hx⟩ : R) := Algebra.IsIntegral.isIntegral _
    have h__af := h.map R.val
    simp at h__af
    exact h__af
  let ι : R →ₐ[ℤ] integralClosure ℤ ℂ := Subalgebra.inclusion hRle
  have hιval : ∀ x : R, ((ι x : integralClosure ℤ ℂ) : ℂ) = (x : ℂ) := fun _ => rfl
  letI : Algebra R (integralClosure ℤ ℂ) := ι.toRingHom.toAlgebra
  have halg : ∀ x : R, algebraMap R (integralClosure ℤ ℂ) x = ι x := fun _ => rfl
  haveI : IsScalarTower ℤ R (integralClosure ℤ ℂ) :=
    IsScalarTower.of_algebraMap_eq (fun n => by rw [halg]; simp)

  haveI : Algebra.IsIntegral R (integralClosure ℤ ℂ) :=
    ⟨fun x => (integralClosure.isIntegral x).tower_top⟩
  have hker : RingHom.ker (algebraMap R (integralClosure ℤ ℂ)) ≤ RingHom.ker τ := by
    intro x hx
    rw [RingHom.mem_ker, halg] at hx
    have hx0 : x = 0 := by
      apply Subtype.ext
      have := congrArg (fun y : integralClosure ℤ ℂ => (y : ℂ)) hx
      rw [hιval] at this
      simpa using this
    simp [hx0]
  obtain ⟨ψ, hψ⟩ := RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed τ hker
  have hψx : ∀ x : R, ψ (ι x) = τ x := fun x => by
    have := congrArg (fun f : R →+* ℂ => f x) hψ
    simpa [halg] using this

  obtain ⟨σ, hσ⟩ := integralClosure.exists_complex_ringEquiv_apply_eq ℂ ψ
    (integralClosure ℤ ℂ).val.toRingHom
  refine ⟨σ, fun x => ?_⟩
  have hyint : IsIntegral ℤ (σ ((ι x : integralClosure ℤ ℂ) : ℂ)) :=
    ((ι x).2).map (σ.toRingHom.toIntAlgHom)
  have key := hσ (ι x) ⟨σ ((ι x : integralClosure ℤ ℂ) : ℂ), hyint⟩ rfl

  rw [hψx] at key
  rw [key]
  rfl

private theorem ringEquiv_ratCast (σ : ℂ ≃+* ℂ) (q : ℚ) : σ (q : ℂ) = q :=
  map_ratCast σ q

private theorem ringEquiv_of_mem_range (σ : ℂ ≃+* ℂ) {z : ℂ}
    (hz : z ∈ Set.range ((↑) : ℚ → ℂ)) : σ z = z := by
  obtain ⟨q, rfl⟩ := hz
  exact ringEquiv_ratCast σ q

end RationalEigenConj

namespace Module.Basis

/-- **Eigenconjugation over the rational coordinate hypothesis.** Stated verbatim
from
`Theorems/Thm_Module_Basis_exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast.lean`. -/
theorem exists_forall_apply_eq_ringHom_smul_of_repr_mem_range_ratCast
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {J : Type*} (S : J → V →ₗ[ℂ] V)
    (hS : ∀ (j : J) (i i' : ι), b.repr (S j (b i)) i' ∈ Set.range ((↑) : ℚ → ℂ))
    (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ i : ι, ℓ (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (lam : J → ℂ) (v : V) (hv : ∀ j : J, S j v = lam j • v) (hℓv : ℓ v ≠ 0)
    (R : Subalgebra ℤ ℂ) [Module.Finite ℤ R] (hR : ∀ j : J, lam j ∈ R) (τ : R →+* ℂ) :
    ∃ w : V, ℓ w ≠ 0 ∧ ∀ j : J, S j w = τ ⟨lam j, hR j⟩ • w := by
  classical
  obtain ⟨σ, hσ⟩ := RationalEigenConj.exists_ringEquiv_apply_eq R τ

  let c : ι → ℂ := b.equivFun v
  have hv_sum : v = ∑ i, c i • b i := (b.sum_equivFun v).symm

  let w : V := ∑ i, σ (c i) • b i
  have hw_coord : ∀ i, b.equivFun w i = σ (c i) := by
    intro i
    simp [w, map_sum, map_smul, Module.Basis.equivFun_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  refine ⟨w, ?_, ?_⟩
  ·
    have hℓv' : ℓ v = ∑ i, c i * ℓ (b i) := by
      conv_lhs => rw [hv_sum]
      simp [map_sum, map_smul, smul_eq_mul]
    have hℓw : ℓ w = ∑ i, σ (c i) * ℓ (b i) := by
      simp [w, map_sum, map_smul, smul_eq_mul]
    have hℓw' : ℓ w = σ (ℓ v) := by
      rw [hℓw, hℓv', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, RationalEigenConj.ringEquiv_of_mem_range σ (hℓ i)]
    rw [hℓw']
    exact fun h => hℓv (by simpa using congrArg σ.symm h)
  · intro j

    apply b.equivFun.injective
    funext i'

    have hcoordS : ∀ x : V, b.equivFun (S j x) i' =
        ∑ i, b.repr (S j (b i)) i' * b.equivFun x i := by
      intro x
      have h := LinearMap.toMatrix_mulVec_repr b b (S j) x
      have h' := congrFun h i'
      rw [Matrix.mulVec, dotProduct] at h'
      rw [Module.Basis.equivFun_apply, ← h']
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.toMatrix_apply, Module.Basis.equivFun_apply]

    have hcv : ∑ i, b.repr (S j (b i)) i' * c i = lam j * c i' := by
      rw [← hcoordS v, hv j, map_smul]
      simp [c, Module.Basis.equivFun_apply]
    rw [hcoordS w, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, hw_coord]

    have := congrArg σ hcv
    rw [map_sum, map_mul, hσ ⟨lam j, hR j⟩] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, RationalEigenConj.ringEquiv_of_mem_range σ (hS j i i')]

end Module.Basis
