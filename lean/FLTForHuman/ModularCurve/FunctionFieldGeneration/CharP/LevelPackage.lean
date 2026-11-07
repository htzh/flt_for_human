/-
  The level-degree package at a general field, as the pin's `C` layer states it.

  This is the instance layer of `Generic/LevelPackage.lean` at `κ = K`, `jg = jqModC K`: the base
  field is `K⟮jqModC K⟯`, the level-`d` series is `jqNModC K d`, and the package is the pin's `Pkg
  K M` — the inline `finrank ∧ modularFunctionFieldC d = adjoin (divisors)` conjunction, which is
  `PkgAt (jqModC K) M` clause by clause.

  The degree clause needs no bridge at all: `baseField (jqModC K)` is `adjoin K {jqModC K}`,
  `levelSeries (jqModC K) d` is `jqNModC K d`, and the two `dedekindPsi` spellings in scope are the
  same constant (`ModularCurve.dedekindPsi` is a `def` alias of `_root_.dedekindPsi`). The
  generation clause does: `modularFunctionFieldC` names the field by the two generators `{jq(j),
  j(q ^ d)}`, while `generatedAt` is stated over the coefficient field as
  `{jq(j)} ∪ {level series at the divisors}`, and the two differ by the set identity
  `{a, b} = {a} ∪ {b}` plus the absorption of `jqModC K` by the divisor set (`1 ∣ d`,
  `jqNModC K 1 = jqModC K`). No base change is involved — which is why `generatedAt` is stated
  absolutely.

  Both bridges are the `ℚ` layer's `gen_iff_levelField` / `hall_pkgAt` with `jq` replaced by
  `jqModC K`; the transcriptions of the slot-product objects (`pushedMinpoly`, `slotPolynomial`)
  belong to the headline module, as at `ℚ`.
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.LevelPackage
import FLTForHuman.ModularCurve.Defs.JqCoeff

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

variable {K : Type*} [Field K]

/-- **The generation clause at the `C` base field**: the pin's named level field is the adjoin the
generic clause speaks. The two sides differ only in how the adjoined sets are written —
`{jqModC K, jqNModC K d}` against `{jqModC K} ∪ {level series at the divisors of d}` — and in the
absorption of `jqModC K` by the divisor set, because `jqModC K = jqNModC K 1` and `1 ∣ d`. -/
theorem modularFunctionFieldC_iff_generatedAt (d : ℕ) [NeZero d] :
    modularFunctionFieldC K d = IntermediateField.adjoin K
        {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}
      ↔ generatedAt (jqModC K) d := by
  have hpair : ({jqModC K, jqNModC K d} : Set (LaurentSeries K))
      = {jqModC K} ∪ {jqNModC K d} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
  have hS : ({x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'),
        d' ∣ d ∧ x = levelSeries (jqModC K) d'})
      = {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'),
          d' ∣ d ∧ x = jqNModC K d'} := rfl
  have hfull : ({jqModC K} ∪ {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'),
        d' ∣ d ∧ x = jqNModC K d'})
      = {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'),
          d' ∣ d ∧ x = jqNModC K d'} := by
    rw [Set.union_eq_right]
    refine Set.singleton_subset_iff.mpr ⟨1, inferInstance, one_dvd d, ?_⟩
    exact (jqNModC_one K).symm
  unfold modularFunctionFieldC generatedAt
  rw [hpair, hS, hfull]
  exact Iff.rfl

/-- **`Pkg` is `PkgAt`**: the pin's inline package at the `C` base field is the general package at
`jg = jqModC K`. The degree half is `degreeAt (jqModC K) d` by definition, so it needs no bridge;
the generation half is `modularFunctionFieldC_iff_generatedAt`. -/
theorem pkg_pkgAt (N : ℕ) : Pkg K N → PkgAt (jqModC K) N :=
  fun h d hd _ => ⟨(h d hd).1, (modularFunctionFieldC_iff_generatedAt d).mp (h d hd).2⟩

end ModularCurve
