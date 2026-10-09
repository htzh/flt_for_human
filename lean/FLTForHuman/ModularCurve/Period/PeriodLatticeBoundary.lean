/-
  The boundary of a `ℤ`-chain of periods: a vanishing boundary sum lies in the
  period lattice.

  A finitely supported integer combination `Z` of pairs `(τ₀, τ₁) ∈ ℍ × ℍ` is a
  `ℤ`-chain; its boundary at a point `τ` is the coefficient sum of the
  `Γ`-orbit of the second endpoint minus that of the first. When every boundary
  vanishes, the period combination `∑ m • periodAlongOf Γ τ₀ τ₁` is a
  `ℤ`-combination of the periods `periodOf Γ γ` of group elements, i.e. it lies
  in `periodLatticeOf Γ`.

  The proof writes each period as a difference `P τ₁ - P τ₀` of the base-point
  functionals `P τ = periodAlongOf Γ I τ`, chooses one orbit representative
  `rep Γ τ` per `Γ`-orbit, and rewrites the combination as the boundary sum plus
  a sum of differences `P τ - P (rep Γ τ)`; the boundary hypothesis kills the
  middle term, and each difference is `±` a `periodOf` because `rep Γ τ = γ • τ`
  for some `γ ∈ Γ`.

  Transcribed from
  `P2M/Sol/S_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero.lean`
  (pinned `aa2d8b3`, 237 lines); the statement is the `Theorems/` wrapper's. The
  shared prelude `hasDerivAt_affine`/`segmentPoint_eq_of_mem`/`periodAlongOf_eq_sub`
  is imported from `PeriodLatticeSpan.lean` (order 1 of this set), not re-proved.
  All other machinery is `private` here, so the checker diffs only the headline.

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero.lean>
-/
import FLTForHuman.ModularCurve.Period.PeriodLatticeSpan

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

open UpperHalfPlane

namespace ModularCurve

namespace ClosedChainLatticeOf

variable {Γ : Subgroup SL(2, ℤ)}

private noncomputable def P (Γ : Subgroup SL(2, ℤ)) (τ : ℍ) : Module.Dual ℂ (CuspForm Γ 2) :=
  ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ

private theorem periodAlong_eq_P_sub [Γ.FiniteIndex] (a b : ℍ) :
    ModularCurve.periodAlongOf Γ a b = P Γ b - P Γ a := by
  apply LinearMap.ext
  intro f
  obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ f
  rw [LinearMap.sub_apply, P, P, periodAlongOf_eq_sub Γ f hF.1, periodAlongOf_eq_sub Γ f hF.1,
    periodAlongOf_eq_sub Γ f hF.1]
  ring

private theorem P_smul_sub_P_mem [Γ.FiniteIndex] (γ : Γ) (τ : ℍ) :
    P Γ ((γ : SL(2, ℤ)) • τ) - P Γ τ ∈ ModularCurve.periodLatticeOf Γ := by
  have h : P Γ ((γ : SL(2, ℤ)) • τ) - P Γ τ = ModularCurve.periodOf Γ γ := by
    apply LinearMap.ext
    intro f
    obtain ⟨F, hF⟩ := ModularCurve.exists_hasEquivariantPrimitiveOf Γ f
    have hequiv : ModularCurve.Period.IsEquivariantPrimitive Γ F := hF.2.2.1
    rw [LinearMap.sub_apply, P, P, ModularCurve.periodOf, periodAlongOf_eq_sub Γ f hF.1,
      periodAlongOf_eq_sub Γ f hF.1, periodAlongOf_eq_sub Γ f hF.1]
    rw [show F ((γ : SL(2, ℤ)) • τ) - F UpperHalfPlane.I - (F τ - F UpperHalfPlane.I) =
        F ((γ : SL(2, ℤ)) • τ) - F τ by ring]
    rw [hequiv.sub_eq_period γ τ, ← hequiv.sub_eq_period γ UpperHalfPlane.I]
  rw [h]
  exact ModularCurve.periodOf_mem_periodLatticeOf Γ γ

section Reps

open Classical

private def orbInd (Γ : Subgroup SL(2, ℤ)) (τ x : ℍ) : ℤ :=
  if ∃ γ : Γ, (γ : SL(2, ℤ)) • x = τ then 1 else 0

private theorem ite_eq_mul_orbInd (τ x : ℍ) (m : ℤ) :
    (if ∃ γ : Γ, (γ : SL(2, ℤ)) • x = τ then m else 0) = m * orbInd Γ τ x := by
  unfold orbInd; split_ifs <;> simp

private def qo (Γ : Subgroup SL(2, ℤ)) (x : ℍ) : Quotient (MulAction.orbitRel Γ ℍ) :=
  Quotient.mk (MulAction.orbitRel Γ ℍ) x

private theorem orbInd_eq_one_iff (τ x : ℍ) : orbInd Γ τ x = 1 ↔ qo Γ τ = qo Γ x := by
  unfold orbInd qo
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · intro h
    by_contra hne
    rw [ite_eq_right] at h
    · exact zero_ne_one h
    · rintro ⟨γ, hγ⟩
      exact hne ⟨γ, hγ⟩
  · rintro ⟨γ, hγ⟩
    rw [ite_eq_left ⟨γ, hγ⟩]

private theorem orbInd_eq_ite (τ x : ℍ) : orbInd Γ τ x = if qo Γ τ = qo Γ x then 1 else 0 := by
  by_cases h : qo Γ τ = qo Γ x
  · rw [ite_eq_left h]; exact (orbInd_eq_one_iff τ x).2 h
  · rw [ite_eq_right h]
    unfold orbInd
    split_ifs with h'
    · exact absurd ((orbInd_eq_one_iff (Γ := Γ) τ x).1 (by unfold orbInd; rw [ite_eq_left h'])) h
    · rfl

private def rep (Γ : Subgroup SL(2, ℤ)) (x : ℍ) : ℍ := (qo Γ x).out

private theorem qo_rep (x : ℍ) : qo Γ (rep Γ x) = qo Γ x := Quotient.out_eq _

private theorem P_sub_P_rep_mem [Γ.FiniteIndex] (x : ℍ) :
    P Γ x - P Γ (rep Γ x) ∈ ModularCurve.periodLatticeOf Γ := by
  have h : qo Γ (rep Γ x) = qo Γ x := qo_rep x
  unfold qo at h
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨γ, hγ⟩ := h

  rw [← hγ, show P Γ x - P Γ ((γ : Γ) • x) = -(P Γ ((γ : SL(2, ℤ)) • x) - P Γ x) by
    rw [neg_sub]; rfl]
  exact Submodule.neg_mem _ (P_smul_sub_P_mem γ x)

private def reps (Γ : Subgroup SL(2, ℤ)) (S : Finset ℍ) : Finset ℍ := (S.image (qo Γ)).image Quotient.out

private theorem sum_reps_orbInd_smul {S : Finset ℍ} {x : ℍ} (hx : x ∈ S) :
    ∑ r ∈ reps Γ S, orbInd Γ r x • P Γ r = P Γ (rep Γ x) := by
  unfold reps
  rw [Finset.sum_image]
  · simp_rw [orbInd_eq_ite]
    have : ∀ s : Quotient (MulAction.orbitRel Γ ℍ),
        ((if qo Γ s.out = qo Γ x then (1 : ℤ) else 0) • P Γ s.out) =
          if s = qo Γ x then P Γ (rep Γ x) else 0 := by
      intro s
      rw [show qo Γ s.out = s from Quotient.out_eq s]
      by_cases hs : s = qo Γ x
      · rw [ite_eq_left hs, ite_eq_left hs, one_smul, hs]; rfl
      · rw [ite_eq_right hs, ite_eq_right hs, zero_smul]
    simp_rw [this]
    rw [Finset.sum_ite_eq' (S.image (qo Γ)) (qo Γ x), ite_eq_left (Finset.mem_image_of_mem _ hx)]
  · intro a _ b _ hab
    rw [← Quotient.out_eq a, ← Quotient.out_eq b]
    exact congrArg (Quotient.mk _) hab |>.trans (by rfl)

end Reps

end ClosedChainLatticeOf

open ClosedChainLatticeOf in
open Classical in
/-- **The boundary of a chain of periods.** An integer combination of periods
whose `Γ`-orbit boundary sum vanishes lies in the period lattice. The pin's
`ModularCurve.sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero`, with
the statement of the `Theorems/` wrapper. -/
theorem sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (Z : (ℍ × ℍ) →₀ ℤ)
    (hZ : ∀ τ : ℍ,
      Z.sum (fun e m =>
        (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
        (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.1 = τ then m else 0)) = 0) :
    (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) ∈
      ModularCurve.periodLatticeOf Γ := by
  have hb : ∀ τ : ℍ, (Z.sum fun e m => m * orbInd Γ τ e.2 - m * orbInd Γ τ e.1) = 0 := by
    intro τ
    rw [← hZ τ]
    exact Finsupp.sum_congr fun e _ => by rw [ite_eq_mul_orbInd, ite_eq_mul_orbInd]
  set S : Finset ℍ := Z.support.image Prod.fst ∪ Z.support.image Prod.snd with hS
  have h1 : ∀ e ∈ Z.support, e.1 ∈ S := fun e he =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)
  have h2 : ∀ e ∈ Z.support, e.2 ∈ S := fun e he =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)

  have hrep : (Z.sum fun e m => m • (P Γ (rep Γ e.2) - P Γ (rep Γ e.1))) = 0 := by
    simp only [Finsupp.sum]
    calc ∑ e ∈ Z.support, Z e • (P Γ (rep Γ e.2) - P Γ (rep Γ e.1))
        = ∑ e ∈ Z.support, ∑ r ∈ reps Γ S,
            (Z e * orbInd Γ r e.2 - Z e * orbInd Γ r e.1) • P Γ r := by
          refine Finset.sum_congr rfl fun e he => ?_
          rw [← sum_reps_orbInd_smul (h2 e he), ← sum_reps_orbInd_smul (h1 e he),
            ← Finset.sum_sub_distrib, Finset.smul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [sub_smul, mul_smul, mul_smul, smul_sub]
      _ = ∑ r ∈ reps Γ S, (∑ e ∈ Z.support,
            (Z e * orbInd Γ r e.2 - Z e * orbInd Γ r e.1)) • P Γ r := by
          rw [Finset.sum_comm]
          simp_rw [Finset.sum_smul]
      _ = 0 := Finset.sum_eq_zero fun r _ => by
          have := hb r
          simp only [Finsupp.sum] at this
          rw [this, zero_smul]
  have hdiff : (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) =
      (Z.sum fun e m => m • ((P Γ e.2 - P Γ (rep Γ e.2)) - (P Γ e.1 - P Γ (rep Γ e.1)))) +
        Z.sum fun e m => m • (P Γ (rep Γ e.2) - P Γ (rep Γ e.1)) := by
    simp only [Finsupp.sum, ← Finset.sum_add_distrib, ← smul_add]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [periodAlong_eq_P_sub]
    congr 1
    abel
  rw [hdiff, hrep, add_zero]
  refine Submodule.sum_mem _ fun e _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · exact P_sub_P_rep_mem e.2
  · exact P_sub_P_rep_mem e.1

end ModularCurve

end
