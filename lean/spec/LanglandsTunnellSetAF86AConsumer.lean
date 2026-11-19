/-
  SET-AF86A consumer: the converse, read as "all but finitely many places" and as one packaged bound.

  **The row.** `FLTForHuman/LanglandsTunnell/Converse.lean` carries
  `LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable`:
  for an arithmetic genuine cuspidal eigensystem over `ℚ` there is a finite set `S` outside which the Hecke
  ratio is `a² = t·b` with `t ≥ 0` real and the Ramanujan-type bound `‖a‖² < ‖b‖ (N + 2 + 1/N)` holds.

  **The readings.**

  * Zone 1 — **almost all places**: the row's `∃ S, ∀ p ∉ S, …` read as the *finiteness* it states, i.e.
    the set of places where the square-ratio fails is finite. That is the form a counting or
    Chebotarev-style consumer wants;
  * Zone 2 — **one conjunction per place**: the two conclusions at a single place, packaged as one
    hypothesis about that place (what a downstream statement about "a good place" would take).

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF86AConsumer.lean` and never enters the build.
-/
import FLTForHuman.LanglandsTunnell.Converse

set_option autoImplicit false

noncomputable section

open IsDedekindDomain AutomorphicForm
open scoped Classical

namespace LanglandsTunnellSetAF86AConsumer

/-- **Zone 1.** The places where the square-ratio fails are finite: the row's `∃ S, ∀ p ∉ S, …` read as the
finiteness statement it is. -/
theorem finite_setOf_not_sq_ratio (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ (AutomorphicForm.productionPinsGeneral ℚ) Φ) :
    {p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) |
      ¬ ∃ t : ℝ, 0 ≤ t ∧ Φ.a p ^ 2 = (t : ℂ) * Φ.b p}.Finite := by
  obtain ⟨S, hS⟩ :=
    LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable Φ hΦ
  refine S.finite_toSet.subset ?_
  intro p hp
  by_contra hpS
  exact hp (hS p hpS).1

/-- **Zone 2.** At a place outside the exceptional set both conclusions hold at once: a real `t ≥ 0` with
`a² = t·b`, and the Ramanujan-type bound. -/
theorem exists_sq_ratio_and_ramanujan_bound (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ (AutomorphicForm.productionPinsGeneral ℚ) Φ) :
    ∃ S : Finset (HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      ∀ p : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ S →
        ∃ t : ℝ, 0 ≤ t ∧ Φ.a p ^ 2 = (t : ℂ) * Φ.b p ∧
          ‖Φ.a p‖ ^ 2 <
            ‖Φ.b p‖ * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) + 2 +
              ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹) := by
  obtain ⟨S, hS⟩ :=
    LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable Φ hΦ
  exact ⟨S, fun p hp => by
    obtain ⟨⟨t, ht, heq⟩, hlt⟩ := hS p hp
    exact ⟨t, ht, heq, hlt⟩⟩

end LanglandsTunnellSetAF86AConsumer
