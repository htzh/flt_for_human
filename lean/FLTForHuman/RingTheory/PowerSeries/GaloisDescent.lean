/-
  Galois descent for power series: a series with coefficients in a finite-dimensional
  `K ⊆ ℚ̄` that is carried into an `E`-subspace `V` by every `ℚ`-conjugate map is a
  `K`-linear combination of `ℚ`-rational series whose images lie in `V`.

      `PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem`.

  The mathematics.  `N` is the normal closure of `K` in `ℚ̄`, so `N / ℚ` is Galois and
  finite, and the trace form `Algebra.traceForm ℚ N` is nondegenerate.  The dual basis
  `bd` of a `ℚ`-basis `b` of `N` with respect to that form satisfies
  `∑ i, bd i * τ (b i) = if τ = 1 then 1 else 0` (`sum_dualBasis_mul_apply`), which —
  together with the linear independence of the `ℚ`-algebra automorphisms of a field
  (`linearIndependent_monoidHom`) — gives the reconstruction formula
  `x = ∑ τ, (∑ i, bd i * τ (b i)) * τ x` (`eq_sum_dualBasis_mul`).  Applying it
  coefficientwise to `A` expresses `A` in the conjugates `τ • A`, and each conjugate
  lies in `V` by hypothesis.

  FLT provenance, pinned `aa2d8b3`: the whole of
  `P2M/Sol/S_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem.lean`
  (186 lines).  The pin's inner label was `A2GaloisDescentPS` (a phase label); it is
  folded into the descriptive `PowerSeries.GaloisDescent`, so the pin's declarations
  keep their last names at `PowerSeries.GaloisDescent.{comp_algebraMap_rat,
  apply_algebraMap_rat, eq_sum_dualBasis_mul, sum_dualBasis_mul_apply, descent}`.
  `descent` is the pin's proof-bearing public and stays public.  The pin's top-level
  `solution` is not ported as a second declaration: its statement is
  `Theorems/Thm_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem.lean`
  verbatim, and it becomes the headline at `PowerSeries`, proved by
  `GaloisDescent.descent`.  The pin's two trailing `p2m_reactivate` lines are dropped;
  they were `P2M.Util` bookkeeping with no mathematical content and no later use in
  the file.

  Home.  The statement names mathlib's `PowerSeries`, so the headline stays in
  `PowerSeries`, beside the mathlib mirror `RingTheory/PowerSeries/`.  The Galois
  content is a library dependency, not a different area: nothing here is a result
  about `FieldTheory/Galois/` that belongs there.  Mathlib `v4.34.0` has
  descent-for-submodules nowhere (`Mathlib/FieldTheory/Galois/` has no such result),
  and no name of this file occurs in `Mathlib/`.

  Drift.  The pin's bare `import Mathlib` became the modules the proof names.
  Deprecations: `if_neg` -> `ite_eq_right` (two sites); the two `haveI` binders of
  `FiniteDimensional ℚ N` and `IsGalois ℚ N` became `have` on the
  `linter.style.haveILetI` suggestion (the instances are already global).

  spec-pin: Theorems/Thm_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem.lean
  spec-pin: P2M/Sol/S_PowerSeries_exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem.lean
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.LinearIndependent.Basic

set_option autoImplicit false

noncomputable section

namespace PowerSeries

namespace GaloisDescent

local notation "Qb" => AlgebraicClosure ℚ

scoped instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ

scoped instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩

scoped instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

open PowerSeries

variable {E : Type*} [Field E] [CharZero E]

theorem comp_algebraMap_rat (ι : Qb →+* E) : ι.comp (algebraMap ℚ Qb) = algebraMap ℚ E :=
  Subsingleton.elim _ _

theorem apply_algebraMap_rat (ι : Qb →+* E) (q : ℚ) : ι (algebraMap ℚ Qb q) = algebraMap ℚ E q :=
  RingHom.congr_fun (comp_algebraMap_rat ι) q

section Dedekind

variable (N : Type*) [Field N] [Algebra ℚ N] [FiniteDimensional ℚ N] [IsGalois ℚ N]

theorem eq_sum_dualBasis_mul {r : Type*} [Fintype r] [DecidableEq r] (b : Module.Basis r ℚ N)
    (x : N) :
    x = ∑ τ : N ≃ₐ[ℚ] N,
      (∑ i, ((Algebra.traceForm ℚ N).dualBasis (traceForm_nondegenerate ℚ N) b i) * τ (b i)) * τ x := by
  set bd := (Algebra.traceForm ℚ N).dualBasis (traceForm_nondegenerate ℚ N) b with hbd
  have h1 := bd.sum_repr x
  have h2 : ∀ i, (bd.repr x i) • bd i = (∑ τ : N ≃ₐ[ℚ] N, τ x * τ (b i)) * bd i := by
    intro i
    rw [hbd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Algebra.smul_def,
      trace_eq_sum_automorphisms, ← hbd]
    congr 1
    exact Finset.sum_congr rfl fun τ _ => map_mul τ x (b i)
  have h3 : x = ∑ i, (∑ τ : N ≃ₐ[ℚ] N, τ x * τ (b i)) * bd i := by
    conv_lhs => rw [← h1]
    exact Finset.sum_congr rfl fun i _ => h2 i
  have h4 : ∀ τ : N ≃ₐ[ℚ] N, (∑ i, bd i * τ (b i)) * τ x = ∑ i, τ x * τ (b i) * bd i := by
    intro τ
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc x = ∑ i, (∑ τ : N ≃ₐ[ℚ] N, τ x * τ (b i)) * bd i := h3
    _ = ∑ i, ∑ τ : N ≃ₐ[ℚ] N, τ x * τ (b i) * bd i :=
        Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    _ = ∑ τ : N ≃ₐ[ℚ] N, ∑ i, τ x * τ (b i) * bd i := Finset.sum_comm
    _ = ∑ τ : N ≃ₐ[ℚ] N, (∑ i, bd i * τ (b i)) * τ x :=
        Finset.sum_congr rfl fun τ _ => (h4 τ).symm

open Classical in

theorem sum_dualBasis_mul_apply {r : Type*} [Fintype r] [DecidableEq r] (b : Module.Basis r ℚ N)
    (τ : N ≃ₐ[ℚ] N) :
    ∑ i, ((Algebra.traceForm ℚ N).dualBasis (traceForm_nondegenerate ℚ N) b i) * τ (b i) =
      if τ = 1 then 1 else 0 := by
  set bd := (Algebra.traceForm ℚ N).dualBasis (traceForm_nondegenerate ℚ N) b with hbd

  have hind : LinearIndependent N (fun τ : N ≃ₐ[ℚ] N => ((τ : N →* N) : N → N)) := by
    have h := linearIndependent_monoidHom N N
    have hinj : Function.Injective (fun τ : N ≃ₐ[ℚ] N => (τ : N →* N)) := by
      intro τ₁ τ₂ h12
      apply AlgEquiv.ext
      intro x
      exact DFunLike.congr_fun h12 x
    exact h.comp _ hinj

  set g : (N ≃ₐ[ℚ] N) → N := fun τ => (∑ i, bd i * τ (b i)) - if τ = 1 then 1 else 0 with hg
  have hsum : ∑ τ ∈ (Finset.univ : Finset (N ≃ₐ[ℚ] N)), g τ • ((τ : N →* N) : N → N) = 0 := by
    funext x
    rw [Finset.sum_apply, Pi.zero_apply]
    have e0 : ∀ τ : N ≃ₐ[ℚ] N, (g τ • ((τ : N →* N) : N → N)) x =
        (∑ i, bd i * τ (b i)) * τ x - (if τ = 1 then 1 else 0) * τ x := fun τ => by
      rw [hg]; exact sub_mul _ _ _
    simp only [e0, Finset.sum_sub_distrib]
    rw [sub_eq_zero, ← eq_sum_dualBasis_mul N b x, Finset.sum_eq_single (1 : N ≃ₐ[ℚ] N)]
    · simp
    · intro τ _ hτ; rw [ite_eq_right hτ, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hzero := (linearIndependent_iff'.mp hind) Finset.univ g hsum τ (Finset.mem_univ τ)
  rw [hg] at hzero
  exact sub_eq_zero.mp hzero

end Dedekind

theorem descent (ι : Qb →+* E) (V : Submodule E (PowerSeries E))
    (K : IntermediateField ℚ Qb) [FiniteDimensional ℚ K]
    (A : PowerSeries Qb) (hA : ∀ n : ℕ, PowerSeries.coeff n A ∈ K)
    (hV : ∀ σ : Qb ≃ₐ[ℚ] Qb, A.map (ι.comp (σ : Qb →+* Qb)) ∈ V) :
    ∃ (n : ℕ) (c : Fin n → Qb) (r : Fin n → PowerSeries ℚ),
      (∀ i, (r i).map (algebraMap ℚ E) ∈ V) ∧
        A.map ι = ∑ i, ι (c i) • (r i).map (algebraMap ℚ E) := by
  classical

  set N : IntermediateField ℚ Qb := IntermediateField.normalClosure ℚ K Qb with hN
  have : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ K Qb
  have : IsGalois ℚ N := IsGalois.normalClosure ℚ K Qb
  have hAN : ∀ n, PowerSeries.coeff n A ∈ N := fun n => IntermediateField.le_normalClosure K (hA n)

  set a : ℕ → N := fun n => ⟨PowerSeries.coeff n A, hAN n⟩ with ha
  have hcoeff : ∀ n, PowerSeries.coeff n A = ((a n : N) : Qb) := fun n => rfl

  set b : Module.Basis (Fin (Module.finrank ℚ N)) ℚ N := Module.finBasis ℚ N with hb
  set bd := (Algebra.traceForm ℚ N).dualBasis (traceForm_nondegenerate ℚ N) b with hbd

  set lift : (N ≃ₐ[ℚ] N) → (Qb ≃ₐ[ℚ] Qb) := fun τ => τ.liftNormal Qb with hlift
  have hlift_apply : ∀ (τ : N ≃ₐ[ℚ] N) (x : N), lift τ (x : Qb) = ((τ x : N) : Qb) := fun τ x =>
    AlgEquiv.liftNormal_commutes τ Qb x

  have hconj : ∀ (τ : N ≃ₐ[ℚ] N) (n : ℕ),
      PowerSeries.coeff n (A.map (ι.comp (lift τ : Qb →+* Qb))) = ι ((τ (a n) : N) : Qb) := by
    intro τ n
    rw [PowerSeries.coeff_map, RingHom.comp_apply, hcoeff n, RingHom.coe_coe, hlift_apply]

  set r : Fin (Module.finrank ℚ N) → PowerSeries ℚ := fun i =>
    PowerSeries.mk fun n => Algebra.trace ℚ N (b i * a n) with hr
  set R : Fin (Module.finrank ℚ N) → PowerSeries E := fun i =>
    ∑ τ : N ≃ₐ[ℚ] N, ι ((τ (b i) : N) : Qb) • A.map (ι.comp (lift τ : Qb →+* Qb)) with hR
  have hRV : ∀ i, R i ∈ V := fun i =>
    V.sum_mem fun τ _ => V.smul_mem _ (hV (lift τ))
  have hRcoeff : ∀ i n, PowerSeries.coeff n (R i) =
      ι ((∑ τ : N ≃ₐ[ℚ] N, τ (b i) * τ (a n) : N) : Qb) := by
    intro i n
    rw [hR]
    simp only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, IntermediateField.coe_sum,
      IntermediateField.coe_mul]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [hconj, ← map_mul]
  have hRr : ∀ i, (r i).map (algebraMap ℚ E) = R i := by
    intro i
    ext n
    rw [PowerSeries.coeff_map, hr, PowerSeries.coeff_mk, ← apply_algebraMap_rat ι,
      IsScalarTower.algebraMap_apply ℚ N Qb, IntermediateField.algebraMap_apply,
      trace_eq_sum_automorphisms, hRcoeff]
    congr 2
    exact Finset.sum_congr rfl fun τ _ => map_mul τ _ _
  refine ⟨Module.finrank ℚ N, fun i => ((bd i : N) : Qb), r, fun i => (hRr i).symm ▸ hRV i, ?_⟩

  ext n
  simp only [map_sum, PowerSeries.coeff_smul, smul_eq_mul, hRr, hRcoeff, PowerSeries.coeff_map,
    hcoeff]
  simp_rw [← map_mul, ← IntermediateField.coe_mul]
  rw [← map_sum, ← IntermediateField.coe_sum]
  congr 2

  symm
  calc ∑ i, bd i * ∑ τ : N ≃ₐ[ℚ] N, τ (b i * a n)
      = ∑ τ : N ≃ₐ[ℚ] N, (∑ i, bd i * τ (b i)) * τ (a n) := by
        simp_rw [map_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ τ : N ≃ₐ[ℚ] N, (if τ = 1 then 1 else 0) * τ (a n) := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [hbd, sum_dualBasis_mul_apply N b τ]
    _ = a n := by
        rw [Finset.sum_eq_single (1 : N ≃ₐ[ℚ] N)]
        · simp
        · intro τ _ hτ; rw [ite_eq_right hτ, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h

end GaloisDescent

theorem exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem
    {E : Type*} [Field E] [CharZero E] (ι : AlgebraicClosure ℚ →+* E)
    (V : Submodule E (PowerSeries E))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (A : PowerSeries (AlgebraicClosure ℚ)) (hA : ∀ n : ℕ, PowerSeries.coeff n A ∈ K)
    (hV : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      A.map (ι.comp (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ∈ V) :
    ∃ (n : ℕ) (c : Fin n → AlgebraicClosure ℚ) (r : Fin n → PowerSeries ℚ),
      (∀ i, (r i).map (algebraMap ℚ E) ∈ V) ∧
        A.map ι = ∑ i, ι (c i) • (r i).map (algebraMap ℚ E) :=
  GaloisDescent.descent ι V K A hA hV

end PowerSeries
