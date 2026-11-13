/-
  The residue field of a valuation subring of an algebraically closed field.

  Two statements:

  * a monic polynomial of nonzero degree over a valuation subring `A` of an
    algebraically closed field `K` has a root in `A` itself — the integral closure
    of `A` in `K` is `A` (a valuation subring is integrally closed), so the root that
    `K` provides lies in `A`;
  * consequently the residue field of `A` is algebraically closed: a monic
    polynomial over `ResidueField A` lifts to a monic polynomial over `A` of the
    same degree (the residue map is surjective), and the residue of its root is a
    root of the lifted one.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_ValuationSubring_exists_root_mem_of_monic.lean` (23 lines) and
  `P2M/Sol/S_ValuationSubring_isAlgClosed_residueField.lean` (30), with the
  statements from their wrappers `Theorems/Thm_ValuationSubring_*.lean`.

  Imports mathlib only; nothing is assumed from earlier port modules.

  spec-pin: Theorems/Thm_ValuationSubring_exists_root_mem_of_monic.lean
  spec-pin: P2M/Sol/S_ValuationSubring_exists_root_mem_of_monic.lean
  spec-pin: Theorems/Thm_ValuationSubring_isAlgClosed_residueField.lean
  spec-pin: P2M/Sol/S_ValuationSubring_isAlgClosed_residueField.lean
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace ValuationSubring


theorem exists_root_mem_of_monic {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) (f : Polynomial A) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    ∃ x : A, Polynomial.aeval (x : K) f = 0 := by
  have hdeg : (f.map (algebraMap A K)).degree ≠ 0 := by
    rw [hf.degree_map]
    intro h
    exact hd (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap A K)) hdeg
  have hint : IsIntegral A x := by
    refine ⟨f, hf, ?_⟩
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  have hyx : (y : K) = x := hy
  rw [Polynomial.aeval_def, hyx]
  rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx

theorem isAlgClosed_residueField {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hmonic hirr
  have hlift : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => IsLocalRing.residue_surjective _
  obtain ⟨f, hmap, hdeg, hf⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmonic
  have hd : f.natDegree ≠ 0 := by
    rw [Polynomial.natDegree_eq_of_degree_eq hdeg]
    exact hirr.natDegree_pos.ne'
  obtain ⟨x, hx⟩ := ValuationSubring.exists_root_mem_of_monic A f hf hd
  refine ⟨IsLocalRing.residue A x, ?_⟩
  have hx0 : f.eval x = 0 := by
    have h1 : (algebraMap A K) (f.eval x) = 0 := by
      rw [← hx, Polynomial.aeval_def]
      exact (Polynomial.eval₂_at_apply (algebraMap A K) x).symm
    exact Subtype.coe_injective (by simpa using h1)
  rw [← hmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, hx0, map_zero]

end ValuationSubring
