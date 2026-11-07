/-
  The `ℚ` spelling of the level-degree package, and its conversion to the general one.

  `Tight`, `Gen` and `Hall` are the `ℚ` vocabulary of the package: `Tight d` is the `finrank` `ψ(d)`,
  `Gen d` is the level-`d` field's generation, and `Hall N` is both at every `d ∣ N`. They are the
  same predicate as `PkgAt jq N`; the two lemmas below say so, clause by clause, and `hall_pkgAt`
  composes them into the form the theory consumes.

  Keeping the `ℚ` spelling is not duplication: it is the vocabulary the capstone's strong induction
  and every `ℚ` consumer speak, and it names the two invariants separately (`Tight` is what the
  tower law multiplies, `Gen` is what the descent produces). The single package predicate used by
  the theory is `PkgAt`, whose clauses are `degreeAt` and `generatedAt`.

  Only one of the two clauses needs a bridge. `Tight d` and `degreeAt jq d` are the same term, so
  there is nothing to prove; `Gen d` is stated over the named fields `modularFunctionField` /
  `modularFunctionFieldFull` while `generatedAt jq d` is a relative adjoin, and that conversion is
  real (`extendScalars_adjoin` twice) and is `gen_iff_levelField`.

  Both proofs are term-level rewrites around the definitions: the `Tight` half needs no bridge at all
  (definitional), and the `Gen` half is `extendScalars_adjoin` twice.
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.LevelPackage
import FLTForHuman.ModularCurve.Defs.Fields

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-- **`Gen` is the generation clause** at the `ℚ` base field, and `Tight` needs no bridge at all: it
*is* `degreeAt jq d`, definitionally, so a caller projects `PkgAt`'s first conjunct straight into it.

The two sides here differ only in how the adjoined sets are written — `{jq, jqN d}` against
`{jq} ∪ {jqN d}`, and the bare divisor set against `{jq} ∪ divisorExpansions d`, which absorbs `jq`
because `1 ∣ d`. No base change is needed, which is the point of stating `generatedAt` absolutely. -/
theorem gen_iff_levelField (d : ℕ) [NeZero d] :
    Gen d ↔ generatedAt jq d := by
  have hpair : ({jq, qExpand ℚ d jq} : Set (LaurentSeries ℚ)) = {jq} ∪ {qExpand ℚ d jq} := by
    ext x
    simp [or_comm]
  have hS : ({x : LaurentSeries ℚ | ∃ (d' : ℕ) (_ : NeZero d'),
      d' ∣ d ∧ x = levelSeries jq d'} : Set (LaurentSeries ℚ)) = divisorExpansions d := rfl
  have hfull : ({jq} ∪ divisorExpansions d : Set (LaurentSeries ℚ)) = divisorExpansions d :=
    Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr
      ⟨1, inferInstance, one_dvd d, by rw [qExpand_one_apply]⟩)
  unfold Gen generatedAt
  rw [modularFunctionField, modularFunctionFieldFull, hS, hpair, hfull]
  exact Iff.rfl

/-- **`Hall` is `PkgAt`**: the `ℚ` package is the general package at `jg = jq`. The `Tight` half is
`degreeAt jq d` by definition, so the projection needs no bridge; the `Gen` half is
`gen_iff_levelField`. -/
theorem hall_pkgAt (N : ℕ) : Hall N → PkgAt jq N :=
  fun h d hd _ => ⟨(h d hd).1, (gen_iff_levelField d).mp (h d hd).2⟩

end ModularCurve
