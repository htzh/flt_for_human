/-
  Cross-module wire test for **D-2**, the countable function-field descent
  (`FLTForHuman/WeierstrassCurve/Isogeny/IntermediateField.lean`).

  A `spec/` probe, not a library module. It exists so that D-2 has a wire test that
  executes the headline on a concrete datum and composes its output with the ported
  `finrankAlong` API; deleting `IntermediateField.lean` makes every zone fail.

  Executed zones (each a real composition, no `#check`, no `sorry`):

  * zone 1 — the headline at the identity endomorphism of a curve over
    `AlgebraicClosure ℚ`: the descent returns a **countable** `K₀`, a descended curve
    `E₀` with `E₀.map (algebraMap K₀ _) = W`, and a descended endomorphism `ι₀` whose
    `finrankAlong` is the original one; the ported `finrankAlong_id`
    (`AlgebraicCurve/Defs/Correspondence.lean`) collapses that to `1`;
  * zone 2 — the descended curve's discriminant: the headline's `E₀.map … = W` output
    composed with the ported `WeierstrassCurve.map_Δ`;
  * zone 3 — the countability output is consumed by `Cardinal.mk_le_aleph0`, i.e. the
    descent lands in a countable field in the sense the `Cardinal` API asks for.

  The D-1 prelude (`BaseChange.lean`) supplies `TreeIsogenyEndDatum`; the headline's
  own module supplies the descent. Both are on the import path, so a break in either
  breaks this probe.
-/
import FLTForHuman.WeierstrassCurve.Isogeny.IntermediateField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open Polynomial
open scoped Polynomial.Bivariate WeierstrassCurve TensorProduct
open WeierstrassCurve WeierstrassCurve.Affine ModularCurve AlgebraicCurve

/-- The descent at the identity endomorphism: a countable `K₀`, a descended curve and a
descended endomorphism of `finrankAlong` `1`. This *runs* the whole D-2 chain
(`iCa_K₀`, the pinned point, `iPFA_finiteAlong`, `iPFE_finrankEq`, `iE2E_*`). -/
example (W : WeierstrassCurve (AlgebraicClosure ℚ)) [W.IsElliptic] :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)), Countable K₀ ∧
      ∃ (E₀ : WeierstrassCurve K₀), E₀.IsElliptic ∧
        E₀.map (algebraMap K₀ (AlgebraicClosure ℚ)) = W ∧
        ∃ (ι₀ : (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
            (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField),
          ι₀.toRingHom.IsIntegral ∧
          ∃ (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
            finrankAlong (AlgebraicClosure K₀) ι₀ = 1 := by
  obtain ⟨K₀, hK₀, E₀, hE₀, hmap, ι₀, hι₀, hfin₀, hdeg⟩ :=
    WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq W
      (AlgHom.id (AlgebraicClosure ℚ) W.toAffine.FunctionField)
      (by
        show (RingHom.id W.toAffine.FunctionField).IsIntegral
        exact RingHom.Finite.to_isIntegral (RingHom.Finite.id _))
      (by show Module.Finite _ _; exact Module.Finite.self _)
  exact ⟨K₀, hK₀, E₀, hE₀, hmap, ι₀, hι₀, hfin₀, hdeg.trans finrankAlong_id⟩

/-- The descended curve has the same discriminant, through the headline's
`E₀.map (algebraMap K₀ _) = W` and the ported `WeierstrassCurve.map_Δ`. -/
example (W : WeierstrassCurve (AlgebraicClosure ℚ)) [W.IsElliptic] :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (E₀ : WeierstrassCurve K₀),
      E₀.IsElliptic ∧ E₀.map (algebraMap K₀ (AlgebraicClosure ℚ)) = W ∧
      algebraMap K₀ (AlgebraicClosure ℚ) E₀.Δ = W.Δ := by
  obtain ⟨K₀, -, E₀, hE₀, hmap, -, -, -, -⟩ :=
    WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq W
      (AlgHom.id (AlgebraicClosure ℚ) W.toAffine.FunctionField)
      (by
        show (RingHom.id W.toAffine.FunctionField).IsIntegral
        exact RingHom.Finite.to_isIntegral (RingHom.Finite.id _))
      (by show Module.Finite _ _; exact Module.Finite.self _)
  exact ⟨K₀, E₀, hE₀, hmap, by rw [← hmap, WeierstrassCurve.map_Δ]⟩

/-- The countability the headline produces is the `Cardinal` notion: the descended
field has at most countably many elements. -/
example (W : WeierstrassCurve (AlgebraicClosure ℚ)) [W.IsElliptic] :
    ∃ (K₀ : IntermediateField ℚ (AlgebraicClosure ℚ)),
      (Cardinal.mk K₀ : Cardinal) ≤ Cardinal.aleph0 := by
  obtain ⟨K₀, hK₀, -, -, -, -, -, -, -⟩ :=
    WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq W
      (AlgHom.id (AlgebraicClosure ℚ) W.toAffine.FunctionField)
      (by
        show (RingHom.id W.toAffine.FunctionField).IsIntegral
        exact RingHom.Finite.to_isIntegral (RingHom.Finite.id _))
      (by show Module.Finite _ _; exact Module.Finite.self _)
  exact ⟨K₀, Cardinal.mk_le_aleph0⟩
