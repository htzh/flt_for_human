/-
  The Fujisaki compactness façade: the norm-one ideles and their class group.

  This is the tier-1 wire for the twin pair of
  `topics/numberTheory/tateGlobal/TOPIC-compactness-twins.md`. It declares the two consumed
  headlines, each stated from its pin `Theorems/` wrapper and proved by the corresponding
  public kernel of the tier-3 engine
  `FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiCompact.lean`:

  * `NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul`
    — compact representatives for the norm-one ideles
    (`M4aLocalCFT.FujisakiR1.exists_isCompact_impl`);
  * `NumberField.TateGlobal.compactSpace_normOneIdeleClass` — Fujisaki's theorem that
    $\mathbb{A}_F^1 / F^\times$ is compact
    (`M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl`).

  Both statements are the wrapper text verbatim — the checker diffs that text, so this module
  mirrors the wrappers' spelling (`NumberField.TateGlobal.normOneIdeles`, the bare
  `principalIdeles` under `open M4aHerbrand`) rather than the port's idiom.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`; the wrappers are
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass.lean
  and the proof silo is the first of those files' `P2M/Sol/S_` pair.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.FujisakiCompact
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs

set_option autoImplicit false

open NumberField M4aHerbrand

noncomputable section

namespace NumberField

namespace TateGlobal

-- pin: exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul (S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean:3676)
theorem exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
    (F : Type) [Field F] [NumberField F] :
    ∃ K : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact K ∧ K ⊆ (NumberField.TateGlobal.normOneIdeles F : Set _) ∧
      ∀ x ∈ NumberField.TateGlobal.normOneIdeles F, ∃ (η : Fˣ) (κ : (AdeleRing (𝓞 F) F)ˣ), κ ∈ K ∧
        x = Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom η * κ :=
  M4aLocalCFT.FujisakiR1.exists_isCompact_impl F

-- pin: compactSpace_normOneIdeleClass (S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.lean:3610)
theorem compactSpace_normOneIdeleClass (F : Type) [Field F] [NumberField F] :
    CompactSpace (↥(NumberField.TateGlobal.normOneIdeles F) ⧸
      (principalIdeles (𝓞 F) F).subgroupOf (NumberField.TateGlobal.normOneIdeles F)) :=
  M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl F

end TateGlobal

end NumberField
