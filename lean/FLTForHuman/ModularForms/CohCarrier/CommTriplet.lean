/-
  The three commuting-operator leaves of the `CohCarrier` layer, tier 1:
  `heckeT` commutes with the diamond action, `heckeT` at a prime commutes with
  `heckeT` at a coprime level, and two diamond actions commute.

  Tier-3 source (unlisted): `FLTForHuman/ModularForms/CohCarrier/Engine/CommTriplet.lean`,
  the port of the pin's whole deduped development `P2M/Sol/S_CohCarrier_heckeT_diamondRaw_comm.lean`
  (pinned `aa2d8b3`, 90 declarations); that module carries all three kernels
  `IharaSolComm.heckeDiamond_impl`, `IharaSolComm.commPrime_impl`,
  `IharaSolComm.twoDiamonds_impl`, of which each of the pin's three sibling `S_`
  files picks one for its `solution`. Each headline below is the one-line
  application of its kernel, exactly as the pin's `solution` forwards.

  Statements are those of the pin's `Theorems/Thm_CohCarrier_*.lean` wrappers (the
  checker's comparable copies, line 9 of each); the wrappers' `attribute
  [-instance] CohCarrier.GammaHLower_finiteIndex` / `attribute [-simp] …uMat_apply_*`
  prelude is deliberately not reproduced — the port keeps those global.
-/
import FLTForHuman.ModularForms.CohCarrier.Engine.CommTriplet

set_option autoImplicit false

namespace CohCarrier

-- pin: `CohCarrier.heckeT_diamondRaw_comm` (Theorems/Thm_CohCarrier_heckeT_diamondRaw_comm.lean:9)
theorem heckeT_diamondRaw_comm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (σ : CongruenceSubgroup.Gamma0 M)
    (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (diamondRaw M H V σ F) = diamondRaw M H V σ (heckeT M H ℓ V F) :=
  IharaSolComm.heckeDiamond_impl M H ℓ σ hσ V F

-- pin: `CohCarrier.heckeT_comm_of_prime` (Theorems/Thm_CohCarrier_heckeT_comm_of_prime.lean:9)
theorem heckeT_comm_of_prime (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (hℓ : ℓ.Prime) (hcop : Nat.Coprime ℓ ℓ') {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (heckeT M H ℓ' V F) = heckeT M H ℓ' V (heckeT M H ℓ V F) :=
  IharaSolComm.commPrime_impl M H ℓ ℓ' hℓ hcop V F

-- pin: `CohCarrier.diamondRaw_comm` (Theorems/Thm_CohCarrier_diamondRaw_comm.lean:9)
theorem diamondRaw_comm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (σ σ' : CongruenceSubgroup.Gamma0 M)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    diamondRaw M H V σ (diamondRaw M H V σ' F) = diamondRaw M H V σ' (diamondRaw M H V σ F) :=
  IharaSolComm.twoDiamonds_impl M H σ σ' V F

end CohCarrier
