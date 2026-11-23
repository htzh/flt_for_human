/-
  Pin sources whose statements the port owns rather than diffs.

  This module declares nothing and imports nothing. It carries the `spec-pin:` lines
  that were removed from a port module when that module's interface deliberately
  departed from the pin's shape; `spec/check_port.py` reads them here (no declarations,
  so nothing to diff) and `frontier.py` reads them from this file as well, which keeps
  the pin marked *ported* and stops it being proposed for porting again.

  The changes themselves are registered in `topics/TOPIC-interface-changes.md`, with the
  pin shape, the port shape and the bridges between them. Add a `spec-pin:` line here
  only together with an entry there.

  ModularForms/QCoeff — the `q`-coefficient floor. Its interface is the port's
  presentation `HasQCoeffWith` and its diagonal `HasQCoeff`, rather than the pin's three
  regularity conditions, and the q-expansion analysis behind it is public here
  (topics/TOPIC-interface-changes.md Entry 1):

    spec-pin: Definitions/Def_FLTPrelim_Modularity.lean
    spec-pin: Theorems/Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean
    spec-pin: P2M/Sol/S_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean
    spec-pin: P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean

  ModularForms/QCoeffClass — the bundled `hasSum_qCoeff` producer (pin: a `variable`
  section, so the checker's stored text omits the section binders) and the bundled
  equality principle, which is the instance-level facade on `QCoeff`:

    spec-pin: Theorems/Thm_ModularFormClass_eq_of_forall_qCoeff_eq.lean
    spec-pin: P2M/Sol/S_UpperHalfPlane_qCoeff_heckeU.lean

  ModularForms/HeckeQCoeff — the Hecke action on `q`-coefficients. The function-level
  coefficient identities take the certificate instead of the three regularity
  conditions, so the module is unpinned; the rest of its declarations sit on the same
  wire and are listed here with it:

    spec-pin: Theorems/Thm_UpperHalfPlane_qCoeff_heckeU.lean
    spec-pin: Theorems/Thm_UpperHalfPlane_qCoeff_heckeT.lean
    spec-pin: Theorems/Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul.lean
    spec-pin: Theorems/Thm_ModularFormClass_qCoeff_heckeU.lean
    spec-pin: Theorems/Thm_ModularFormClass_qCoeff_heckeT.lean
    spec-pin: Theorems/Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.lean
    spec-pin: Theorems/Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU.lean
    spec-pin: Theorems/Thm_ModularFormClass_qExpansion_heckeT_eq_heckeT.lean
    spec-pin: Theorems/Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeU_comm.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeU_int.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeT_comm.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeT_int.lean
    spec-pin: P2M/Sol/S_UpperHalfPlane_qCoeff_heckeU.lean

  ModularForms/Level + Defs/HeckeRepresentatives — the Hecke representatives on `ℙ¹(𝔽_p)` and the
  `Γ₁`/diamond vocabulary. The pin's public home for that block is not a wire for any single port
  module: it is split across `Level/Diamond`, `Defs/HeckeRepresentatives` and
  `Defs/Gamma1HeckeOperators`, and three of its statements are repackaged — `isUnit_wt` carries the
  primality as a `[Fact p.Prime]` instance instead of an explicit `hp : p.Prime`;
  `heckeMatrix_mul_of_dvd` is the level-raising packaging (`(M : ℕ)`, `p ∣ M`, conclusion
  `g' ∈ Γ₀(p * M)`) rather than the pin's `(p : ℤ) ∣ g 1 0` plus the `1 0`-entry conjunct; and
  `heckeMatrix_mul_of_eq` is stated over labels (`j j' : ZMod p`) instead of `ℕ` lifts, which drops
  the pin's quotient `e` because `p` vanishes in `ZMod p`
  (topics/TOPIC-interface-changes.md Entry 6). The two `Γ₀` `S_` copies of that block are already
  wired by `ModularForms/HeckeInvariance.lean` and stay there.

    spec-pin: Definitions/Def_CuspForm_Gamma1HeckeOperators.lean

  ModularForms/Analytic/PeterssonCoset — the pin's coset-integral layer. `unfold_sum` is stated for
  an arbitrary group and the canonical fiber `Γ ⧸ Λ.subgroupOf Γ` instead of the pin's `SL(2, ℤ)`
  transversal (Entry 9); the other 26 public declarations keep the pin's statements.

    spec-pin: Definitions/Def_CuspForm_PeterssonCoset.lean

  ModularForms/Analytic/PeterssonHecke — the Hecke adjointness engine. The subgroup `Λ` it
  pairs over is `Γ₁(N) ⊓ Γ⁰(p)` (`Level.Gamma0Upper`'s group) instead of a carrier with its own
  `mul_mem'`/`inv_mem'`; the Bézout datum is `Level.BezoutPair` (one normalization, `u * p +
  v * N = 1`) with no sign-translating `bez`; the two statements that name their divisibility
  witness do so through `dvd_01_of_mem_Lam`; and two one-use entry computations are inlined
  (topics/TOPIC-interface-changes.md Entry 7). The pin was written twice in the pin's own
  tree (`S_CuspForm_norm_sq_…` carries a second copy of its group layer) and none of its 117
  declarations is `private`, so unpinning hands the whole public surface to the port:

    spec-pin: P2M/Sol/S_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean

  The pin's group-and-pairing layer (`Nice`, `dens`, `unfold_sum`, the `integral_cosum_*`
  triple, the coset-integral block) has its wire with `ModularForms/Analytic/PeterssonCoset`
  above, whose module carries it; this module keeps no copy of it.

  ModularForms/NebentypusEigenbasis — the `ε`-eigenspace. The invariance statement is proved for
  the diamond-twisted `T_p` instead of for the pin's `U_p + ε(p) • (· ∣[k] heckeDiagMatrix p)`:
  `SSbasis.heckeTOne_slash` says `T_p f ∣[k] γ = ε(dd γ) • T_p f` for `f` of nebentypus `ε`, and
  the pin's shape is recovered through `coe_heckeTOne_nebentypus` (on a nebentypus form the
  diamond `⟨p⟩` acts by `ε(p)`, which is `heckeT` in the shared `CuspForm.heckeFun`). The
  `Γ₀(N)`-equivariance that this rests on is `HeckeTLinOneQCoeff.heckeTLinOne_slashOfMemGamma0`,
  not a local coset computation (topics/TOPIC-interface-changes.md Entry 8). The module's other two
  wires — the eigenbasis theorem and its `S_` file — stay in its own header.

    spec-pin: Theorems/Thm_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0.lean
    spec-pin: P2M/Sol/S_ModularForm_heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0.lean

  Re-wiring a parked module needs `own:` rows back for the declarations whose pin has no
  comparable statement: `ModularFormClass.qCoeff_add'`, `…qCoeff_sub'` and
  `…qCoeff_const_smul'` are the general spellings of the pin's concrete per-file copies.
-/
