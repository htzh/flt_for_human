/-
The degree-one place theorem for the bar field: every place of
`modularFunctionFieldBar M` over `AlgebraicClosure ℚ` has degree one.

`modularFunctionFieldBar M` is `laurentBaseChange (AlgebraicClosure ℚ)
(modularFunctionFieldFull M)`, and the pin's proof shows it is finite-dimensional —
hence algebraic — over `AlgebraicClosure ℚ⟮j(q)⟯` by the relative-degree identity
`relfinrank_laurentBaseChange_modularFunctionFieldFull` and
`relfinrank_full_eq_dedekindPsi` (`ψ(M) > 0`), then applies the generic
`Place.deg_eq_one_of_isAlgebraic_adjoin` from
`FLTForHuman/AlgebraicCurve/Place/DegreeOne.lean`.

The pin names the element `j(q)` in the bar field with a local `set j`; the port
gives it a `private abbrev jBar` so the `adjoin (AlgebraicClosure ℚ) {jBar M}` term
in `finiteDimensional_adjoin_jBar`'s type and in the headline's instance argument
is syntactically the same — otherwise instance search compares the two `coeffEmb`
subtype terms and times out at the default budget. The `Algebra.IsAlgebraic`
instance is then supplied explicitly (`Algebra.IsAlgebraic.of_finite`) rather than
left to search, the playbook's §6 remedy for instance-search timeouts. The pin's
`B2Deg.finiteDimensional_adjoin_jBar` is `private` in its `S_` file, so the port
transcribes it `private` too; only the headline is public. Verbatim from
`Theorems/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean`, whose proof
body is `P2M/Sol/S_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean`.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean
-/
import FLTForHuman.ModularCurve.Degree.Relfinrank
import FLTForHuman.AlgebraicCurve.Place.DegreeOne
import FLTForHuman.ModularCurve.Defs.ArithmeticGalois
import FLTForHuman.ModularCurve.Defs.QAdicPlace

set_option autoImplicit false

-- The pin's `haveI`/`letI` walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve IntermediateField

namespace ModularCurve

/-- `j(q)` as an element of the bar field `modularFunctionFieldBar M`. -/
private abbrev jBar (M : ℕ) [NeZero M] : modularFunctionFieldBar M :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full M)⟩

/-- `modularFunctionFieldBar M` is finite-dimensional over `AlgebraicClosure ℚ⟮j(q)⟯`:
the relative degree is `ψ(M) > 0`. This is the pin's `B2Deg.finiteDimensional_adjoin_jBar`,
read as `relfinrank = ψ(M)` through `finrank_comap` and the tower
`modularFunctionFieldFull M ≤ modularFunctionFieldBar M`. -/
private theorem finiteDimensional_adjoin_jBar (M : ℕ) [NeZero M] :
    FiniteDimensional
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar M} : Set (modularFunctionFieldBar M)))
      (modularFunctionFieldBar M) := by
  have hcm : IntermediateField.comap (modularFunctionFieldBar M).val
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({(jBar M : LaurentSeries (AlgebraicClosure ℚ))} :
            Set (LaurentSeries (AlgebraicClosure ℚ))))
      = IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({jBar M} : Set (modularFunctionFieldBar M)) := by
    rw [← IntermediateField.lift_adjoin_simple]
    exact IntermediateField.comap_map (modularFunctionFieldBar M).val _
  have h1 := IntermediateField.finrank_comap
    (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(jBar M : LaurentSeries (AlgebraicClosure ℚ))} :
        Set (LaurentSeries (AlgebraicClosure ℚ))))
    (modularFunctionFieldBar M).val
  rw [hcm, IntermediateField.fieldRange_val] at h1
  have h2 : IntermediateField.relfinrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar M : LaurentSeries (AlgebraicClosure ℚ))} :
          Set (LaurentSeries (AlgebraicClosure ℚ))))
      (modularFunctionFieldBar M) = dedekindPsi M := by
    rw [← ModularCurve.relfinrank_full_eq_dedekindPsi M,
      ← ModularCurve.relfinrank_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) M]
  have hpos : 0 < IntermediateField.relfinrank
      (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(jBar M : LaurentSeries (AlgebraicClosure ℚ))} :
          Set (LaurentSeries (AlgebraicClosure ℚ))))
      (modularFunctionFieldBar M) := by
    rw [h2]
    exact ModularCurve.dedekindPsi_pos M (NeZero.ne M)
  rw [← h1] at hpos
  exact Module.finite_of_finrank_pos hpos

/-- **Every place of `modularFunctionFieldBar M` has degree one.** Verbatim from
`Theorems/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean`. -/
theorem deg_eq_one_modularFunctionFieldBar (M : ℕ) [NeZero M]
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar M)) : w.deg = 1 := by
  haveI := finiteDimensional_adjoin_jBar M
  haveI : Algebra.IsAlgebraic
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jBar M} : Set (modularFunctionFieldBar M)))
      (modularFunctionFieldBar M) :=
    Algebra.IsAlgebraic.of_finite _ _
  exact Place.deg_eq_one_of_isAlgebraic_adjoin (jBar M) w

end ModularCurve

end
