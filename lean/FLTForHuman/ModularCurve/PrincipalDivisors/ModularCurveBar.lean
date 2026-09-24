/-
  m11 — `HasPrincipalDivisors` for the modular function fields (M11).

  This is the coverage report's "nearly a corollary" prediction: the layer form
  writes `laurentBaseChange L (modularFunctionFieldFull N)` as
  `adjoin L (insert (jqModC L) {jqNModC L d | d ∣ N})` (m7's
  `laurentBaseChange_modularFunctionFieldFull`), then AC's
  `hasPrincipalDivisors_adjoin_of_transcendental` needs only
  `Transcendental L (jqModC L)` (m6) and the integrality of each generator over
  `L⟮jqModC L⟯` (m6's `isIntegral_jqNModC_all_of_modularPolynomialFamily`, which
  consumes the datum family `hΦ`). The `bar` form is the layer form at
  `L = AlgebraicClosure ℚ`, where `modularFunctionFieldBar` is definitionally
  `laurentBaseChange`.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.lean
-/
import FLTForHuman.ModularCurve.Defs.ArithmeticGalois
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Degree.LaurentGlue
import FLTForHuman.ModularCurve.Degree.PhiData
import FLTForHuman.ModularCurve.Degree.PhiDegree
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

/-- The finite generating set `{jqNModC L d | d ∣ N}` of
`laurentBaseChange L (modularFunctionFieldFull N)` over `L⟮jqModC L⟯`. -/
private def gens (L : Type*) [Field L] (N : ℕ) : Finset (LaurentSeries L) := by
  classical
  exact Finset.univ.image fun d : {d // d ∈ N.divisors} =>
    @jqNModC L _ d.1 ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors d.2)⟩

private theorem mem_gens_iff (L : Type*) [Field L] (N : ℕ) [NeZero N] (x : LaurentSeries L) :
    x ∈ gens L N ↔ ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC L d := by
  classical
  unfold gens
  constructor
  · intro hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨d.1, ⟨Nat.ne_of_gt (Nat.pos_of_mem_divisors d.2)⟩, Nat.dvd_of_mem_divisors d.2, rfl⟩
  · rintro ⟨d, hd, hdN, rfl⟩
    exact Finset.mem_image.mpr ⟨⟨d, Nat.mem_divisors.mpr ⟨hdN, NeZero.ne N⟩⟩, Finset.mem_univ _, rfl⟩

private theorem insert_gens (L : Type*) [Field L] (N : ℕ) [NeZero N] :
    insert (jqModC L) (gens L N : Set (LaurentSeries L)) =
      {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = jqNModC L d} := by
  ext x
  simp only [Set.mem_insert_iff, Finset.mem_coe, mem_gens_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | h)
    · exact ⟨1, inferInstance, one_dvd N, (jqNModC_one L).symm⟩
    · exact h
  · exact Or.inr

theorem hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull (L : Type*) [Field L]
    [Algebra ℚ L] (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N)) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  rw [laurentBaseChange_modularFunctionFieldFull, ← insert_gens]
  refine AlgebraicCurve.hasPrincipalDivisors_adjoin_of_transcendental L (jqModC L)
    (transcendental_jqModC L) (gens L N) ?_
  intro t ht
  obtain ⟨d, hd, -, rfl⟩ := (mem_gens_iff L N t).mp ht
  exact isIntegral_jqNModC_all_of_modularPolynomialFamily L hΦ d

theorem hasPrincipalDivisors_modularFunctionFieldBar (hΦ : ModularPolynomialFamily) (N : ℕ)
    [NeZero N] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) hΦ N

end ModularCurve

end
