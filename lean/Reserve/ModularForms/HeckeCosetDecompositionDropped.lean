/-
  The `Γ_H`-coset pin, dropped as a module: the mathematics now lives in
  `FLTForHuman/ModularForms/HeckeCosetGammaH.lean`.

  The pin source below used to verify `FLTForHuman/ModularForms/HeckeCosetDecomposition.lean`,
  whose only content was the `Γ_H`-over-`Γ_HUpper` coset decomposition (the representatives
  `beta`, the level-pair identity, and the two coset sums that read `U_q` and
  `U_ℓ + (·) ∣ (ρ · diag ℓ)` off it). That module is gone: the level pair, the two
  transversals (`heckeUTransversal` over `ZMod q`, `heckeTTTransversal` over the projective line
  `ℙ¹(ℤ/ℓ)`) and the sums are stated once, in `HeckeCosetGammaH`, against
  `HeckeCoset.Transversal` / `Transversal.sum_eq_sum` / `Transversal.sum_eq_doubleCosetOperator`.
  Its consumers (`ModularForms/HeckeInvariance.lean`,
  `ModularCurve/Period/PeriodMapHecke.lean`) import the new module; their statements are unchanged
  and still diffed against their own pins.

  This file declares nothing and imports nothing: it only keeps the pin marked *ported* for
  `frontier.py`, so the dropped module is not proposed for porting again.

    spec-pin: P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean
-/
