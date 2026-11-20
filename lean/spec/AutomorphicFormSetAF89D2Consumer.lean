/-
  SET-AF89D2 consumer: the compact cusp notion and the production-pins coset system.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/CompactCuspNotion.lean` carries the
  `ℤ[√-2]`-character cuspidality notion and `isArithCuspRealizableVia_of_viaCompactCuspNotion`
  (its cusp forms are arithmetically realizable along `iotaZsqrtdNegTwo`); the same module's
  `viaCompactCuspNotion_isCusp_iff` is the explicit reading of the notion.
  `FLTForHuman/LanglandsTunnell/HeckeCosetSystem.lean` carries
  `exists_heckeCosetSystem_productionPinsCompact_of_not_dvd`: at a place not dividing the level,
  the production-pins double coset has a finite coset system.

  **The readings.** Zone 1 is the compact-cusp notion turned into arithmetic realizability at `ℚ`
  — the form in which the weight-one comparison consumes it. Zone 2 is the global coset row read
  through the `IsHeckeCosetSystem` structure: its representatives lie in the production-pins double
  coset, which is what the Hecke operator's matrix coefficients need.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF89D2Consumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.CompactCuspNotion
import FLTForHuman.LanglandsTunnell.HeckeCosetSystem

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField EisensteinWeightOne CongruenceSubgroup
open AutomorphicForm AutomorphicForm.WindowedSiegel AdelicDock LocalGL2 HeckeIntegralSeam
open NumberField.AdelicLevel
open scoped Manifold

namespace AutomorphicFormSetAF89D2Consumer

/-- **Zone 1.** A cusp form of the compact-cusp notion at `ℚ` is arithmetically realizable along
the `ℤ[√-2]` character. -/
theorem isArithCuspRealizableVia_of_viaCompactCuspNotion
    (Φ : HeckeEigensystem ℚ (ℤ√(-2))) (h : viaCompactCuspNotion.IsCusp ℚ Φ) :
    IsArithCuspRealizableVia ℚ (productionPinsCompact ℚ) iotaZsqrtdNegTwo Φ :=
  AutomorphicForm.isArithCuspRealizableVia_of_viaCompactCuspNotion Φ h

/-- **Zone 2.** Away from the divisor of the level, the production-pins double coset's coset system
has its representatives inside that double coset — the reading a matrix-coefficient computation
needs. -/
theorem exists_rep_mem_doubleCoset_productionPinsCompact
    (N : Ideal (𝓞 ℚ)) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 ℚ) ℚ,
      ∀ i, reps i ∈ HeckePair.doubleCoset ((productionPinsCompact ℚ).U N) ((productionPinsCompact ℚ).gen v) := by
  obtain ⟨reps, hsys⟩ := LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd N v hv
  exact ⟨reps, fun i => hsys.mem_doubleCoset i⟩

end AutomorphicFormSetAF89D2Consumer
