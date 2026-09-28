/-
  Consumer specification for the congruence-subgroup / level vocabulary
  (`PORTING-Level.md`, SET-1).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the L1 module
  `FLTForHuman/ModularForms/Defs/GammaH.lean`: each statement is either bound or
  not, and the error count is the deliverable measure. It is deliberately **not
  part of any library** — nothing globs `spec/` — so it can never break a
  verified build. Run it by hand:

      cd lean
      lake env lean spec/LevelConsumer.lean 2>&1 | grep -c error

  The `[level]` zone is a cross-module composition: `CohCarrier.GammaH` and its
  lemmas from the port, `CongruenceSubgroup.Gamma/Gamma0/Gamma1` and their
  inclusion/conjugation lemmas from mathlib. A `#check` alone would not catch an
  unused-import mistake, so every item below is a proof term.
-/
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.Level.Diamond
import FLTForHuman.ModularCurve.Defs.ProjectiveLine
import FLTForHuman.ModularCurve.Defs.PrimCosetReps
import FLTForHuman.ModularCurve.Gamma0Index
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

open CohCarrier CongruenceSubgroup

open scoped MatrixGroups ModularForm

/-! ## Zone `[level]` — the Γ_H vocabulary (L1) -/

-- Top and bottom specialisations: the two ends of the family.
example : CohCarrier.GammaH 2 ⊤ = CongruenceSubgroup.Gamma0 2 :=
  CohCarrier.GammaH_top

example : CohCarrier.GammaH 2 ⊥ = CongruenceSubgroup.Gamma1 2 :=
  CohCarrier.GammaH_bot 2

-- The lift of a unit to `Γ₀`, and its defining property.
example (d : (ZMod 2)ˣ) : CohCarrier.gamma0Units 2 (CohCarrier.gammaLift 2 d) = d :=
  CohCarrier.gamma0Units_gammaLift d

-- The concrete unit, exercising the `ZMod.val` witness of `gamma0Units_surjective`.
example : CohCarrier.gamma0Units 2 (CohCarrier.gammaLift 2 1) = 1 :=
  CohCarrier.gamma0Units_gammaLift 1

-- Monotonicity in `H`.
example {H H' : Subgroup (ZMod 2)ˣ} (h : H ≤ H') :
    CohCarrier.GammaH 2 H ≤ CohCarrier.GammaH 2 H' :=
  CohCarrier.GammaH_mono h

-- `Γ(2) ⊆ Γ_H ⊆ Γ₀(2)`, through L1 and mathlib's group inclusion.
example (H : Subgroup (ZMod 2)ˣ) :
    CongruenceSubgroup.Gamma 2 ≤ CohCarrier.GammaH 2 H :=
  CohCarrier.Gamma_le_GammaH 2 H

example (H : Subgroup (ZMod 2)ˣ) : CohCarrier.GammaH 2 H ≤ CongruenceSubgroup.Gamma0 2 :=
  CohCarrier.GammaH_le_Gamma0 H

example : CohCarrier.GammaH 2 ⊥ ≤ CongruenceSubgroup.Gamma0 2 := by
  rw [CohCarrier.GammaH_bot]
  exact CongruenceSubgroup.Gamma1_in_Gamma0 2

-- The translation is in every `Γ_H`, and the index is finite.
example (H : Subgroup (ZMod 2)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH 2 H :=
  CohCarrier.translation_mem_GammaH 2 H

example (H : Subgroup (ZMod 2)ˣ) : (CohCarrier.GammaH 2 H).FiniteIndex := inferInstance

-- The conjugation action: normality and the raw diamond.
example (σ : CongruenceSubgroup.Gamma0 2) (γ : ↥(CohCarrier.GammaH 2 ⊤)) :
    (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH 2 ⊤ :=
  CohCarrier.conj_mem_GammaH 2 ⊤ σ γ

example (σ : CongruenceSubgroup.Gamma0 2) :
    CohCarrier.H1 2 ⊤ ℤ →+ CohCarrier.H1 2 ⊤ ℤ :=
  CohCarrier.diamondRaw 2 ⊤ ℤ σ

/-! ## Zone `[diamond]` — the Γ₁ / diamond vocabulary (L2)

The L2 module `FLTForHuman/ModularForms/Level/Diamond.lean`: the diamond lift
`IsDiamondLift`, its existence for coprime `d`, and the diamond operator
`diamondLinOne` well defined on `Γ₁`-forms. -/

namespace LevelDiamond

local notation "Γ₁ℝ" M =>
  ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

-- A lift of `⟨1⟩` exists at `M = 2` (coprimality is discharged concretely).
example : ∃ γ : SL(2, ℤ), ModularForm.Level.IsDiamondLift 2 1 γ :=
  ModularForm.Level.exists_isDiamondLift_of_coprime (by decide)

-- The trivial diamond is the identity linear map.
example : ModularForm.Level.diamondLinOne 2 0 1 =
    (LinearMap.id : CuspForm (Γ₁ℝ 2) 0 →ₗ[ℂ] CuspForm (Γ₁ℝ 2) 0) :=
  ModularForm.Level.diamondLinOne_one

-- Two *distinct* lifts of `⟨1⟩` at `M = 2` (`1` and `-1`) slash a `Γ₁`-form the
-- same way: the well-definedness content of `slash_eq_slash_of_isDiamondLift`.
example (f : CuspForm (Γ₁ℝ 2) 0) :
    ⇑f ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ))) =
      ⇑f ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (1 : SL(2, ℤ))) :=
  ModularForm.Level.slash_eq_slash_of_isDiamondLift (M := 2) (k := 0) (d := 1)
    ⟨CongruenceSubgroup.Gamma0_mem.mpr (by simp), by decide⟩
    ⟨Subgroup.one_mem _, by simp⟩ f

end LevelDiamond

/-! ## Zone `[coset]` — the projective line and the index `ψ(N)` (L3)

The SET-3 modules `FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean`,
`Defs/PrimCosetReps.lean` and `Gamma0Index.lean`: the coset bijection
`Γ₀(N)\SL₂(ℤ) ≃ ℙ¹(ℤ/N)`, the count `[SL₂(ℤ) : Γ₀(N)] = ψ(N)`, and the
independent count `#primCosetReps N = ψ(N)`. Every item is a proof term. -/

namespace LevelCoset

open ModularCurve

-- The three `ℤ/2`-points of the projective line: the headline at `N = 2`.
example : Nat.card (ModularCurve.ProjectiveLine (ZMod 2)) = 3 := by
  rw [ModularCurve.card_projectiveLine_zmod 2 (by decide),
    ModularCurve.dedekindPsi_prime Nat.prime_two]

-- The primitive coset representatives at `N = 2` (the `q`-expansion index set),
-- through the *independent* `divisorsAntidiagonal` count.
example : (ModularCurve.primCosetReps 2).card = 3 := by
  rw [ModularCurve.card_primCosetReps_eq_dedekindPsi 2 (by decide),
    ModularCurve.dedekindPsi_prime Nat.prime_two]

-- ...and the `Finset` really evaluates at `N = 2` (prints `3`).
#eval (ModularCurve.primCosetReps 2).card

-- `[SL₂(ℤ) : Γ₀(2)] = ψ(2) = 3`, through the coset bijection (its proof uses
-- mathlib's index and the promoted `sl2_surj` lifting).
example : (CongruenceSubgroup.Gamma0 2).index = 3 := by
  rw [ModularCurve.Gamma0_index 2, ModularCurve.dedekindPsi_prime Nat.prime_two]

-- Cross-module: `Γ₀_index` and `card_projectiveLine_zmod` are two routes to the
-- same number, so the index *is* the projective-line cardinality.
example : (CongruenceSubgroup.Gamma0 2).index =
    Nat.card (ModularCurve.ProjectiveLine (ZMod 2)) := by
  rw [ModularCurve.Gamma0_index 2,
    ← ModularCurve.card_projectiveLine_zmod 2 (by decide)]

-- The `borel` vocabulary the bijection is stated over.
example (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    A ∈ ModularCurve.borel (ZMod 2) ↔ A.1 1 0 = 0 :=
  ModularCurve.mem_borel_iff

-- A row is a `ℤ/2`-point, and `ProjectiveLine.map` transports it along `ℤ → ℤ/2`.
example : ModularCurve.ProjectiveLine.map (Int.castRingHom (ZMod 2))
    (⟦⟨((1 : ℤ), 0), ModularCurve.isUnimodularRow_one_left 0⟩⟧) =
    (⟦⟨((1 : ZMod 2), 0), ModularCurve.isUnimodularRow_one_left 0⟩⟧ : ModularCurve.ProjectiveLine (ZMod 2)) :=
  ModularCurve.ProjectiveLine.map_mk _ _

end LevelCoset

