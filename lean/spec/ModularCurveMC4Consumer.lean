/-
  Consumer specification for **SET MC-4** (M6 + M5): the period lattice's Hecke-diamond
  stability and the Galois action on the Hecke operators.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the set's six headlines, composed across modules, expressed in Lean so
  that each is either bound or not.  It is a deliverable measure, not a proof obligation.  It is
  **not part of any library** (`lake build` does not see `spec/`); run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveMC4Consumer.lean 2>&1 | grep -c error

  The error count is the metric.  The rows are
  `ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable` (MC-4a),
  `…exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf…` (MC-4b),
  `JOne.galois_smul_heckeAlgOne_smul` (MC-4c), `galois_smul_genOpH_comm` and
  `heckeOperatorHAlong_diamondHBar_comm` (MC-4d), `heckeOperatorOneBar_comm_diamondOneBar`
  (MC-4e); see `topics/modularCurve/SET-MC4.md`.

  ZONES
  -----
    [stable]  ZONE A — the period lattice is stable under the three Hecke-diamond duals, and the
              statement composes with `Submodule.add_mem` through `LinearMap.dualMap`'s additivity.
    [dual]    ZONE B — the period lattice is the `ℤ`-dual of the parabolic homs: the equivalence
              applied at `⟨periodOf Γ δ, _⟩` returns `ψ (ofMul δ)`, and it is a `LinearEquiv`.
    [module]  ZONE C — the Galois action commutes with the `HeckeAlgOne`-module structure,
              specialised to the two algebra generators (`heckeGenOne ℓ`, `diamondGen d`).
    [genop]   ZONE D — `genOpH` at a diamond generator is `diamondHBar`, and the Galois action
              commutes with `genOpH` — the two statements composed at `g = .dia d`.
    [comm]    ZONE E — the two commutation rows, applied: the `X_H` Hecke operator commutes with
              `diamondHBar`, and the `X₁` one with `diamondOneBar`.
-/

import FLTForHuman.ModularCurve.Period.HeckeStability
import FLTForHuman.ModularCurve.Period.PeriodLatticeBasis
import FLTForHuman.ModularCurve.X1.HeckeModule
import FLTForHuman.ModularCurve.XH.Operators
import FLTForHuman.ModularCurve.XH.DiamondLift
import FLTForHuman.ModularCurve.X1.DiamondLift

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open scoped MatrixGroups ModularForm

namespace MC4Consumer

/-! ## Zone A — `[stable]` the period lattice under the Hecke-diamond duals -/

theorem mem_periodLatticeOf_dualMap_heckeTLinH {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {v : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2)}
    (hv : v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    (CuspForm.heckeTLinH 2 hℓ hℓM).dualMap v ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) :=
  (ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable M H).1 ℓ hℓ hℓM v hv

theorem mem_periodLatticeOf_dualMap_diamondLinH {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}
    (d : (ZMod M)ˣ)
    {v w : Module.Dual ℂ (CuspForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2)}
    (hv : v ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H))
    (hw : w ∈ ModularCurve.periodLatticeOf (CohCarrier.GammaH M H)) :
    (CuspForm.diamondLinH 2 d).dualMap (v + w) ∈
      ModularCurve.periodLatticeOf (CohCarrier.GammaH M H) := by
  rw [map_add]
  exact Submodule.add_mem _ ((ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable M H).2.2 d v hv)
    ((ModularCurve.periodLatticeOf_gammaH_heckeDiamondStable M H).2.2 d w hw)

/-! ## Zone B — `[dual]` the period lattice is the `ℤ`-dual of the parabolic homs -/

theorem parabolicHoms_dual_apply_periodOf (Γ : Subgroup SL(2, ℤ))
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ)
    (ψ : ModularCurve.Period.parabolicHoms ℤ Γ ℤ) (δ : Γ) :
    (ModularCurve.exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
        Γ hΓ).choose ψ ⟨ModularCurve.periodOf Γ δ,
          ModularCurve.periodOf_mem_periodLatticeOf Γ δ⟩ =
      (ψ : Additive Γ →+ ℤ) (Additive.ofMul δ) :=
  (ModularCurve.exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup
    Γ hΓ).choose_spec ψ δ

/-! ## Zone C — `[module]` the Galois action on the two `HeckeAlgOne` generators -/

theorem galois_smul_heckeGenOne {M : ℕ} [NeZero M]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ℓ : Nat.Primes) (x : ModularCurve.JOne M) :
    (letI := ModularCurve.heckeModuleOneBar M;
      σ • (ModularCurve.heckeGenOne ℓ • x) = ModularCurve.heckeGenOne ℓ • (σ • x)) :=
  ModularCurve.JOne.galois_smul_heckeAlgOne_smul M σ (ModularCurve.heckeGenOne ℓ) x

theorem galois_smul_diamondGen {M : ℕ} [NeZero M]
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (d : ℕ) (x : ModularCurve.JOne M) :
    (letI := ModularCurve.heckeModuleOneBar M;
      σ • (ModularCurve.diamondGen d • x) = ModularCurve.diamondGen d • (σ • x)) :=
  ModularCurve.JOne.galois_smul_heckeAlgOne_smul M σ (ModularCurve.diamondGen d) x

/-! ## Zone D — `[genop]` `genOpH` at a diamond generator, under the Galois action -/

theorem galois_smul_genOpH_dia {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (d : (ZMod M)ˣ)
    (P : ModularCurve.JH M H) :
    σ • (ModularCurve.genOpH M H S (.dia d) P) =
      ModularCurve.diamondHBar M H d (σ • P) := by
  rw [ModularCurve.genOpH_dia]
  exact ModularCurve.galois_smul_genOpH_comm M H S σ (.dia d) P

/-! ## Zone E — `[comm]` the two commutation rows, applied -/

theorem heckeOperatorHAlong_diamondHBar_apply {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ : ℕ) [Fact ℓ.Prime] (d : (ZMod M)ˣ) (P : ModularCurve.JH M H) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ
        (ModularCurve.diamondHBar M H d P) =
      ModularCurve.diamondHBar M H d
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ P) :=
  ModularCurve.heckeOperatorHAlong_diamondHBar_comm M H ℓ d P

theorem heckeOperatorOneBar_comm_diamondOneBar_apply {M : ℕ} [NeZero M] (ℓ : Nat.Primes) (d : ℕ)
    (x : ModularCurve.JOne M) :
    (ModularCurve.heckeOperatorOneBar M ℓ * ModularCurve.diamondOneBar M d) x =
      (ModularCurve.diamondOneBar M d * ModularCurve.heckeOperatorOneBar M ℓ) x :=
  congrFun (congrArg DFunLike.coe
    (ModularCurve.heckeOperatorOneBar_comm_diamondOneBar M ℓ d)) x

end MC4Consumer
