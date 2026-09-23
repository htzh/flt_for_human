/-
The bifibre count: the sum of ramification index times inertia degree over a
fibre equals the degree, plus the `≤` form and `inertiaDeg_pos`, after FLT's
`P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_{fiberOver,le_finrank}.lean`
and `P2M/Sol/S_AlgebraicCurve_Place_inertiaDeg_pos.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean>).

The pin ships the 45-line Assembly twice (byte-identical); the port writes it
once, here, as the proof of the public `_fiberOver` node. The two v4.34 bridges
against the new `Ideal.sum_ramification_inertia_eq_finrank` are
`IsDedekindDomain.coe_primesOverFinset` + `Finset.sum_coe_sort` and
`IsFractionRing.finrank_eq` (`TOPIC-t2-fibre-dictionary.md` §3, SET-1 §3.1).
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceDictionary
import Mathlib.LinearAlgebra.Dimension.Localization

set_option autoImplicit false

-- The statements keep the pin's primed `Ideal.inertiaDeg'` text; the proofs use
-- v4.34's names, which are deprecated but exact transcriptions.
set_option linter.deprecated false

set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace Place

theorem sum_ramificationIndex_mul_inertiaDeg_fiberOver {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F) :
    ∑ w ∈ v.fiberOver F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) =
      (Module.finrank F F' : ℤ) := by
  classical
  haveI hfin : Fintype ↥((IsLocalRing.maximalIdeal v.toValuationSubring).primesOver
      (integralClosureAt F' v)) :=
    (IsDedekindDomain.coe_primesOverFinset (maximalIdeal_ne_bot v) (integralClosureAt F' v)) ▸
      (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
        (integralClosureAt F' v)).finite_toSet.fintype
  have hkey := Ideal.sum_ramification_inertia_eq_finrank
    (p := IsLocalRing.maximalIdeal v.toValuationSubring) (integralClosureAt F' v)
  rw [← IsFractionRing.finrank_eq v.toValuationSubring F (integralClosureAt F' v) F'] at hkey
  -- Bridge 1: the new theorem sums over the subtype `p.primesOver S`; the pin sums
  -- over the `Finset` `primesOverFinset p S`. `Finset.sum_subtype` identifies them
  -- through `mem_primesOverFinset_iff`.
  have hconv : (∑ q : ↥((IsLocalRing.maximalIdeal v.toValuationSubring).primesOver
        (integralClosureAt F' v)),
        q.1.ramificationIdx v.toValuationSubring * q.1.inertiaDeg v.toValuationSubring)
      = ∑ P ∈ IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
          (integralClosureAt F' v),
          P.ramificationIdx v.toValuationSubring * P.inertiaDeg v.toValuationSubring :=
    (Finset.sum_subtype
      (IsDedekindDomain.primesOverFinset (IsLocalRing.maximalIdeal v.toValuationSubring)
        (integralClosureAt F' v))
      (fun P => IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v) (P := P))
      (fun P => P.ramificationIdx v.toValuationSubring * P.inertiaDeg v.toValuationSubring)).symm
  rw [← hkey]
  rw [hconv]
  push_cast
  refine Finset.sum_bij
    (fun w hw => (fiberCenter F' v ((mem_fiberOver v).mp hw)).asIdeal) ?_ ?_ ?_ ?_
  ·
    intro w hw
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)]
    exact ⟨(fiberCenter F' v ((mem_fiberOver v).mp hw)).isPrime,
      fiberCenter_liesOver ((mem_fiberOver v).mp hw)⟩
  ·
    intro w hw w' hw' h
    exact eq_of_fiberCenter_eq ((mem_fiberOver v).mp hw) ((mem_fiberOver v).mp hw')
      (HeightOneSpectrum.ext h)
  ·
    intro P hP
    rw [IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)] at hP
    obtain ⟨hP1, hP2⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro h
      apply maximalIdeal_ne_bot v
      have h2 := hP2.over
      rw [h, Ideal.under_def, Ideal.comap_bot_of_injective _
        (algebraMap_integralClosureAt_injective v)] at h2
      exact h2
    refine ⟨placeOfPrime ⟨P, hP1, hPne⟩,
      (mem_fiberOver v).mpr (restrict_placeOfPrime ⟨P, hP1, hPne⟩), ?_⟩
    exact congrArg HeightOneSpectrum.asIdeal
      (fiberCenter_placeOfPrime (⟨P, hP1, hPne⟩ :
        HeightOneSpectrum (integralClosureAt F' v)))
  ·
    intro w hw
    have hwr := (mem_fiberOver v).mp hw
    haveI : (fiberCenter F' v hwr).asIdeal.LiesOver
        (IsLocalRing.maximalIdeal v.toValuationSubring) := fiberCenter_liesOver hwr
    rw [ramificationIndex_eq_ramificationIdx_fiberCenter hwr,
      inertiaDeg_eq_inertiaDeg_fiberCenter hwr,
      Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal v.toValuationSubring)
        (fiberCenter F' v hwr).asIdeal (maximalIdeal_ne_bot v),
      Ideal.inertiaDeg'_eq_inertiaDeg _ _]

theorem sum_ramificationIndex_mul_inertiaDeg_le_finrank {K F F' : Type*} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (v : Place K F)
    (S : Finset (Place K F')) (hS : ∀ w ∈ S, w.restrict F = v) :
    ∑ w ∈ S, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) ≤ (Module.finrank F F' : ℤ) :=
  le_of_le_of_eq
    (Finset.sum_le_sum_of_subset_of_nonneg (subset_fiberOver_of_forall_restrict_eq v hS)
      (fun _ _ _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)))
    (sum_ramificationIndex_mul_inertiaDeg_fiberOver v)

theorem inertiaDeg_pos {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F'] (w : Place K F') : 0 < w.inertiaDeg F := by
  haveI := fiberCenter_liesOver (F' := F') (v := w.restrict F) (w := w) rfl
  rw [inertiaDeg_eq_inertiaDeg_fiberCenter (F' := F') (v := w.restrict F) (w := w) rfl,
    Ideal.inertiaDeg'_eq_inertiaDeg]
  exact Ideal.inertiaDeg_pos _ _

end Place

end AlgebraicCurve
