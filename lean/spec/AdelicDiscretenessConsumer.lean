/-
  Consumer zone for `FLTForHuman/NumberTheory/AdelicDiscreteness.lean`.

  The row under test is `NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact`: a
  compact `C ⊆ 𝔸_K` contains the diagonal image of finitely many `ξ : K`.  This file uses it
  once, on a compact set that is *named* — the compact superset of the adèlic box produced by
  `NumberField.AdelicBox.exists_isCompact_adelicBox_subset` — and then checks the two gate
  cases the row's proof carries: `C = ∅` (finite, re-derived from the row) and `C = univ`
  (the compactness hypothesis is not removable).

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AdelicDiscretenessConsumer.lean` and never enters the build.
-/
import FLTForHuman.NumberTheory.AdelicDiscreteness

open NumberField IsDedekindDomain NumberField.AdelicBox

noncomputable section

namespace AdelicDiscretenessConsumer

variable (F : Type) [Field F] [NumberField F]

/-- The adèlic box lies inside a compact set (`exists_isCompact_adelicBox_subset`), so the row
makes the set of `ξ : K` whose adèlic image is in the box finite. -/
theorem finite_points_in_adelicBox :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ adelicBox F}.Finite := by
  obtain ⟨C, hC, hbox⟩ := exists_isCompact_adelicBox_subset F
  exact (NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact F hC).subset
    fun ξ hξ => hbox hξ

/-- The finiteness in the form enumeration wants: a finite list of `K`-points that covers every
`ξ` with `algebraMap K 𝔸_K ξ` in the box. -/
theorem exists_finset_points_in_adelicBox :
    ∃ s : Finset F, ∀ ξ : F, algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ adelicBox F → ξ ∈ s := by
  have hfin := finite_points_in_adelicBox F
  exact ⟨hfin.toFinset, fun ξ hξ => hfin.mem_toFinset.mpr hξ⟩

/-- The integral finite adèles crossed with `0` in the infinite component are compact
(`isCompact_integralFiniteAdeles`), so the row applies there too. -/
theorem finite_points_in_integral_slice :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈
      {x : AdeleRing (𝓞 F) F | x.1 = 0 ∧
        x.2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F}}.Finite :=
  NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact F
    (isCompact_singleton.prod (isCompact_integralFiniteAdeles F))

/-- The `gate_empty` case, read off the general row at `C = ∅`: `∅` is compact, so the row
applies, and its conclusion set is empty by definition. -/
theorem gate_empty_from_row :
    {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ (∅ : Set (AdeleRing (𝓞 F) F))} = ∅ := by
  have hfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact F isCompact_empty
  exact Set.eq_empty_iff_forall_notMem.mpr fun ξ hξ => hξ

/-- The compactness hypothesis is load bearing: at `C = Set.univ` the row's conclusion is false,
which is the module's `gate_univ_infinite` read back as a refutation of the general statement
without `IsCompact C`. -/
theorem not_finite_univ_of_not_compact :
    ¬ {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ (Set.univ : Set (AdeleRing (𝓞 F) F))}.Finite :=
  NumberField.AdeleRing.gate_univ_infinite F

end AdelicDiscretenessConsumer

end
