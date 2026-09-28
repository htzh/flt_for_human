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
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

open CohCarrier CongruenceSubgroup

open scoped MatrixGroups

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
