/-
  The star action on the `j`-series: `StarBank.press`.

  The diamond/star action of the `p`-th cyclotomic twist on `j(q)`: if a
  polynomial `R` over a field `K` satisfies `aeval (jqModC K) R = jqNModC K p`,
  then `R` is monic of degree `p` and, after extending scalars to the Laurent
  series,

    `R.map (algebraMap K (LaurentSeries K)) - C (jqNModC K p)`
      `= ∏ b ∈ range p, (X - C (qTwist (ζ ^ b) (jqModC K)))`.

  The proof compares the two sides at the `p` distinct values
  `qTwist (ζ ^ b) (jqModC K)` and invokes mathlib's
  `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_StarBank_press.lean` (209 lines). The public statement is
  the `Theorems/` wrapper verbatim. **Recorded deviation:** the pin's two
  anonymous `example` probes (its lines 191–197) are regression checks of
  *imported* lemmas — `IsPrimitiveRoot.pow_inj` and `qTwist_one_apply` — not of
  this node's mathematics; they carry no consumer, and transcribing them would
  pull in `Mathlib.Tactic.Omega` for seven lines of non-mathematics, so they are
  dropped (playbook §2.3 residue, §3.1 "no self-consumed lemmas"). They elaborate
  unchanged in the port under this module's imports, so nothing is lost by it.

  ## Reuse

  `press` reads only `Degree/JqCyclotomicConjugates.lean`, the one home for the
  conjugates' structure: `monic_of_aeval_eq`, `natDegree_eq_of_aeval_eq`,
  `qTwist_pow_jqModC_injective` and `aeval_qTwist_jqModC_eq_of_aeval_eq` are
  public there at the pin's names and binders, together with the whole
  `coeff_jqNModC_*` / `qTwist_*` forcing block the pin re-derives `private` in
  every solution file that uses it. The fourteen `private` copies that used to
  live in this module are gone; `qTwist_qExpand_of_pow_eq_one` is public in
  `Defs/KatzLevelPCusps.lean`, which that module imports. The pin-imported
  `coeff_jqModC_*` trio is three pin headlines and lives, public, in
  `Defs/JqCoeff.lean` (the pole at the cusp), also reached through it.

  ## Assumptions

  `Defs/Jq`'s `jNum`/`constantCoeff_jNum`/`ofPowerSeries_coeff_of_neg`;
  `Defs/JqCoeff`'s `jqModC`/`jqNModC`/`jqModC_pow`/`coeff_jqModC_pow_self`/
  `coeff_jqModC_pow_of_lt`/`coeff_jqModC_neg_one`; `Defs/Laurent`'s `qExpand`/
  `qExpand_coeff_mul`/`qExpand_coeff_of_not_dvd`/`algebraMap_laurentSeries_eq_single`;
  `Defs/Twist`'s `qTwist`/`qTwist_coeff`/`qTwist_single`/`qTwist_one_apply`/
  `qTwist_qExpand`; mathlib's `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`.

  spec-pin: P2M/Sol/S_ModularCurve_StarBank_press.lean
  spec-pin: Theorems/Thm_ModularCurve_StarBank_press.lean
-/
import FLTForHuman.ModularCurve.Degree.JqCyclotomicConjugates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries Finset

namespace ModularCurve

namespace StarBank

/-- The star action: `R` is the minimal-degree annihilator of `jqModC K` at
`jqNModC K p`, so it is monic of degree `p` and the scalar-extended
`R - C (jqNModC K p)` factors over the `p` distinct twists of `jqModC K`.
Verbatim from the pin wrapper `Theorems/Thm_ModularCurve_StarBank_press.lean`. -/
theorem press {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) {R : Polynomial K}
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p) :
    R.Monic ∧ R.natDegree = p ∧
      R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by
  have hp : Fact p.Prime := inferInstance
  refine ⟨monic_of_aeval_eq hR, natDegree_eq_of_aeval_eq hR, ?_⟩

  set A : Polynomial (LaurentSeries K) := R.map (algebraMap K (LaurentSeries K)) with hA
  set B : Polynomial (LaurentSeries K) :=
    ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) (jqModC K))) with hB
  have hAmonic : A.Monic := (monic_of_aeval_eq hR).map _
  have hAdeg : A.natDegree = p := by
    rw [hA, (monic_of_aeval_eq hR).natDegree_map, natDegree_eq_of_aeval_eq hR]
  have hBmonic : B.Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hBdeg : B.natDegree = p := by
    rw [hB, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  have key : A - B = Polynomial.C (jqNModC K p) := by
    refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _
      (qTwist_pow_jqModC_injective hζ) (fun b => ?_) ?_
    · have hAev : A.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = jqNModC K p := by
        rw [hA, Polynomial.eval_map_algebraMap]
        exact aeval_qTwist_jqModC_eq_of_aeval_eq hζ hR b
      have hBev : B.eval (qTwist (ζ ^ (b : ℕ)) (jqModC K)) = 0 := by
        rw [hB, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp)
      simp only [Polynomial.eval_sub, Polynomial.eval_C, hAev, hBev, sub_zero]
    · rw [Fintype.card_fin]
      refine max_lt ?_ (by rw [Polynomial.natDegree_C]; exact hp.out.pos)
      by_cases hAB : A = B
      · rw [hAB, sub_self, Polynomial.natDegree_zero]; exact hp.out.pos
      · refine lt_of_lt_of_eq (Polynomial.natDegree_lt_natDegree (sub_ne_zero.mpr hAB) ?_) hAdeg
        exact Polynomial.degree_sub_lt_left
          (by rw [Polynomial.degree_eq_natDegree hAmonic.ne_zero,
            Polynomial.degree_eq_natDegree hBmonic.ne_zero, hAdeg, hBdeg])
          hAmonic.ne_zero (by rw [hAmonic.leadingCoeff, hBmonic.leadingCoeff])

  have hconcl : A - Polynomial.C (jqNModC K p) = B := by
    rw [← key]; ring
  rw [hconcl, hB, Finset.prod_range]

end StarBank

end ModularCurve

end

#print axioms ModularCurve.StarBank.press
