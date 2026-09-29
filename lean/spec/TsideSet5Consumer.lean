/-
  Consumer specification for T12 SET 5, the power-series patching algebra.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the SET-5 modules, imported from **two** new modules:

  * `FLTForHuman/Algebra/MvPowerSeriesRegular.lean` —
    `MvPowerSeries.residue_comp_C_surjective` and
    `MvPowerSeries.isAdicComplete_maximalIdeal` (extended by SET 5);
  * `FLTForHuman/Algebra/AdicCompleteMap.lean` — the generic
    `IsAdicComplete.map_of_surjective`.

  Zone `[fact]` instantiates `isAdicComplete_maximalIdeal` at a discrete
  valuation ring (with the `𝔪`-adic completeness hypothesis a DVR need not have —
  `ℤ_(p)` is the standard counterexample; `ℤ_p` is complete). Zone `[residue]`
  reads off `residue_comp_C_surjective`. Zone `[compose]` is the real
  cross-module composition (playbook §7.2, the `Universal.lean` lesson): the
  completeness instance produced by `isAdicComplete_maximalIdeal` is handed to
  `IsAdicComplete.map_of_surjective` applied to the residue map, whose
  surjectivity is *derived* from `residue_comp_C_surjective` via
  `Function.Surjective.of_comp` (`residue ∘ C` surjective ⇒ `residue`
  surjective). Deleting either new module fails this file.

  It is deliberately **not part of any library** (nothing globs `spec/`), so it can
  never break a verified build. Run it by hand:

      cd lean
      lake env lean spec/TsideSet5Consumer.lean 2>&1 | grep -c error
-/
import FLTForHuman.Algebra.MvPowerSeriesRegular
import FLTForHuman.Algebra.AdicCompleteMap

set_option autoImplicit false

noncomputable section

universe u v

namespace TsideSet5

/-! ## Zone `[fact]` — the power-series completeness fact at a DVR -/

example {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] {σ : Type v} [Finite σ] :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ 𝒪)) (MvPowerSeries σ 𝒪) :=
  MvPowerSeries.isAdicComplete_maximalIdeal

/-! ## Zone `[residue]` — the residue of `𝒪[[X]]` is reached through `C` -/

example {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {σ : Type v} [Finite σ] :
    Function.Surjective (⇑(IsLocalRing.residue (MvPowerSeries σ 𝒪)) ∘
      ⇑(MvPowerSeries.C (σ := σ) (R := 𝒪))) :=
  MvPowerSeries.residue_comp_C_surjective

/-! ## Zone `[compose]` — the completeness instance feeds `IsAdicComplete.map_of_surjective` -/

example {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] {σ : Type v} [Finite σ] :
    IsAdicComplete ((IsLocalRing.maximalIdeal (MvPowerSeries σ 𝒪)).map
      (IsLocalRing.residue (MvPowerSeries σ 𝒪)))
      (IsLocalRing.ResidueField (MvPowerSeries σ 𝒪)) := by
  have hcomp : IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ 𝒪))
      (MvPowerSeries σ 𝒪) :=
    MvPowerSeries.isAdicComplete_maximalIdeal
  have hsurj : Function.Surjective (IsLocalRing.residue (MvPowerSeries σ 𝒪)) :=
    MvPowerSeries.residue_comp_C_surjective.of_comp
  exact IsAdicComplete.map_of_surjective _ (IsLocalRing.residue _) hsurj

end TsideSet5

end
