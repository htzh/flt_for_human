/-
  The characteristic polynomial of a rank-two endomorphism from a quadratic
  relation plus its determinant: if `f * f - t • f + d = 0` and `det f = d`, then
  `charpoly f = X ^ 2 - C t * X + C d`.

  This is the conversion that every Eichler–Shimura Frobenius-charpoly statement
  needs — "quadratic relation + determinant ⟹ characteristic polynomial" — and
  the pin carries it as a `private` helper `charpoly_eq_of_quadratic_of_det`,
  re-proved in eight `S_` files. This module promotes it once, at the
  `LinearMap` level, so a ported consumer imports it instead of transcribing a
  seventh copy. The mathematics is studies/frobenius-charpoly-scout.md §4.

  Statement and proof are transcribed verbatim from
  `P2M/Sol/S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar.lean`
  lines 565–626 (pinned `aa2d8b3`); the only changes are the `LinearMap`
  namespace and the `haveI` → `have` linter fix in the companion (playbook §6).
  The pin's other seven copies of the pair are statement-identical:

    S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar.lean:578
    S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar_tateModule_quotient.lean:578
    S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeDiamondChar_tateModule_quotient.lean:698
    S_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_and_inertia_mul_eq_zero_….lean:600
    S_CuspForm_IsNormalizedEigenform_exists_residualGaloisRep_isAttachedTo.lean:35
    S_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_charpoly_frobenius_eq_and_isRoot_charpoly_one_….lean:249
    S_CuspForm_IsPrimitiveForm_exists_galoisRepAdic_linearIndependent_inertia_apply_eq_smul_….lean:253

  The companion `eq_zero_of_smul_id_eq_zero` is kept `private` here: it is the
  one step needing the positive-rank basis argument and has no other consumer.
  This module assumes nothing from earlier port modules (Mathlib only).
-/
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Nontriviality
import Mathlib.Tactic.Ring

open Polynomial

namespace LinearMap

variable {O : Type*} [CommRing O]
variable {V : Type*} [AddCommGroup V] [Module O V]
variable [Module.Free O V] [Module.Finite O V]

/-- A scalar acting as zero on the identity of a positive-rank endomorphism ring
is zero. Transcribed from the pin's private `eq_zero_of_smul_id_eq_zero`. -/
private theorem eq_zero_of_smul_id_eq_zero (hV : 0 < Module.finrank O V) (c : O)
    (hc : c • (LinearMap.id : Module.End O V) = 0) : c = 0 := by
  classical
  nontriviality O
  let b := Module.Free.chooseBasis O V
  have hne : Nonempty (Module.Free.ChooseBasisIndex O V) := by
    rw [Module.finrank_eq_card_chooseBasisIndex] at hV
    exact Fintype.card_pos_iff.mp hV
  obtain ⟨i⟩ := hne
  have h1 : c • b i = 0 := by
    have := LinearMap.congr_fun hc (b i)
    simpa using this
  have h2 := congrArg (fun v => b.repr v i) h1
  simpa using h2

/-- **The rank-two charpoly from a quadratic relation and the determinant.**
If `f` is a unit of `Module.End O V` over a free finite `O`-module of rank two
satisfying `f * f - t • f + d = 0` with `det f = d`, then
`f.charpoly = X ^ 2 - C t * X + C d`. This is the "quadratic relation +
determinant ⟹ characteristic polynomial" conversion; the pin carries it as a
per-consumer helper (public inside the generated `E1G1ES` namespace) and
re-proves it eight times. -/
theorem charpoly_eq_of_quadratic_of_det (hV : Module.finrank O V = 2)
    (f : Module.End O V) (hf : IsUnit f) (t d : O)
    (hq : f * f - t • f + algebraMap O (Module.End O V) d = 0) (hdet : LinearMap.det f = d) :
    f.charpoly = X ^ 2 - C t * X + C d := by
  nontriviality O
  have hdeg : f.charpoly.natDegree = 2 := by rw [LinearMap.charpoly_natDegree, hV]
  have hmonic := f.charpoly_monic
  have hc0 : f.charpoly.coeff 0 = d := by
    have h := LinearMap.det_eq_sign_charpoly_coeff f
    rw [hV] at h
    rw [← hdet, h]
    ring
  set c₁ := f.charpoly.coeff 1 with hc₁
  have hshape : f.charpoly = X ^ 2 + C c₁ * X + C d := by
    apply Polynomial.ext
    intro n
    rcases n with _ | _ | _ | n
    · simp [hc0]
    · simp [hc₁]
    · have : f.charpoly.coeff 2 = 1 := by
        have := hmonic.leadingCoeff
        rwa [Polynomial.leadingCoeff, hdeg] at this
      simp [this]
    · have hlt : f.charpoly.natDegree < n + 3 := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
      simp
  have hCH : f * f + c₁ • f + algebraMap O (Module.End O V) d = 0 := by
    have h := LinearMap.aeval_self_charpoly f
    rw [hshape] at h
    simpa [sq, Algebra.smul_def] using h
  have hdiff : (t + c₁) • f = 0 := by
    have := sub_eq_zero.mpr (hCH.trans hq.symm)
    have e : f * f + c₁ • f + algebraMap O (Module.End O V) d
        - (f * f - t • f + algebraMap O (Module.End O V) d) = (t + c₁) • f := by
      rw [add_smul]; abel
    rw [e] at this
    exact this
  obtain ⟨u, rfl⟩ := hf
  have hid : (t + c₁) • (LinearMap.id : Module.End O V) = 0 := by
    have : ((t + c₁) • (u : Module.End O V)) * (↑u⁻¹ : Module.End O V) = 0 := by
      rw [hdiff, zero_mul]
    rwa [smul_mul_assoc, Units.mul_inv] at this
  have hpos : 0 < Module.finrank O V := by rw [hV]; exact two_pos
  have htc : t + c₁ = 0 := eq_zero_of_smul_id_eq_zero hpos _ hid
  have : c₁ = -t := by linear_combination htc
  rw [hshape, this, C_neg]
  ring

end LinearMap
