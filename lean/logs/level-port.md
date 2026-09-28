# `lean/logs/level-port.md` — the congruence-subgroup / level vocabulary port, measured

The running record of the effort opened by
[../topics/PORTING-Level.md](../topics/PORTING-Level.md): the `Γ_H` / `Γ₁` /
diamond / coset layer that the Hecke effort scoped as its **Stage D** and left
deferred. One section per set/topic, with the measured costs and the friction.
FLT is pinned at `anthropics/fermats-last-theorem@aa2d8b3`; mathlib at `v4.34.0`.

## §0 Baseline (2026-09-27, before SET-1)

| check | result |
|---|---|
| `lake build` | green (4,334 jobs, 0 warnings, no `sorry`) |
| `spec/check_flt_statements.py` | **1,330 identical, 0 mismatched, 0 missing** (deduced: the L1 module contributes 25 checked declarations to the 1,355 after) |
| ported level vocabulary | `redMatrix`/`heckeRep`/`heckeRep_mul` (weakened) only; `GammaH`, `gamma0Units`, `IsDiamondLift`, `diamondLinOne`, `ProjectiveLine`, `borel`, `primCosetReps`, `Gamma0_index` all absent |
| Hecke Stage D | Tier 2 (Γ₁, 785 pin lines) and Tier 3 (Γ_H, 970) deferred; Γ_H "gated on porting `CohCarrier.GammaH`" ([../topics/PORTING-Hecke.md](../topics/PORTING-Hecke.md) §3.1) |

## §1 SET-1 — the `Γ_H` vocabulary (l1)

**Deliverable.** `FLTForHuman/ModularForms/Defs/GammaH.lean`, 25 public
declarations, namespace `CohCarrier`.

| check | result |
|---|---|
| `timeout 120 lake build FLTForHuman.ModularForms.Defs.GammaH` | green, **0 warnings, no `sorry`** (~4–9 s) |
| `timeout 300 lake build` | green, 4,334 jobs |
| `spec/check_flt_statements.py` | **1,355 identical (70 promoted), 0 mismatched, 0 missing, 15 own-proof** (1,370 checked) |
| `spec/LevelConsumer.lean` | **0 errors** |
| `#print axioms` on `GammaH_bot`, `GammaH_top`, `gamma0Units_surjective`, `GammaH_normal_in_Gamma0`, `slash_mapGL_eq_of_gamma0Units_eq`, `diamondRaw` | `[propext, Classical.choice, Quot.sound]` |

### 1.1 What was transcribed

25 declarations from four pin `Definitions/` files, all verbatim statements
(proofs adapted to `v4.34.0` only):

| group | declarations | pin |
|---|---|---|
| the character | `Gamma0_d_mul_a`, `gamma0Units`, `val_gamma0Units` | `Def_CohCarrier_Level` 111–131 |
| the subgroup | `GammaH`, `mem_GammaH_iff`, `GammaH_le_Gamma0`, `GammaH_top`, `GammaH_mono` | 133–154, `Def_ModularCurve_XH` 64 |
| the ends | `translation_mem_GammaH`, `Gamma1_le_GammaH`, `GammaH_bot` | `Def_ModularCurve_XH` 20–60 |
| inclusions | `Gamma_le_GammaH`, `GammaH_finiteIndex` | `Def_CuspForm_HeckeOperatorFormsGammaH` 18–34 |
| the lift | `gamma0Units_surjective`, `gammaLift`, `gamma0Units_gammaLift`, `unitOfPrimeNotDvd`, `gammaLift_apply_11` | `Def_CohCarrier_Inst` 39–53, `FormsGammaH` 36–49 |
| unit equality | `mul_inv_mem_GammaH_of_gamma0Units_eq`, `slash_mapGL_eq_of_gamma0Units_eq` | `FormsGammaH` 51–70 |
| conjugation | `H1`, `GammaH_normal_in_Gamma0`, `conj_mem_GammaH`, `conjHom`, `diamondRaw` | `Def_CohCarrier_Level` 162, 261–294 |

### 1.2 What was left out, with `grep -c`

| pin declaration | count | reason |
|---|---|---|
| `Gamma0Upper`, `mem_Gamma0Upper`, `Gamma0Upper_isCongruenceSubgroup`, `Gamma0Upper_finiteIndex` | 8, 4, 3, 2 | the Hecke-compatible subgroup; needs the transfer layer (L3) |
| `conjUpperMat` + 3, `GammaHUpper`, `dvd_of_mem_GammaHUpper`, `conjUpperMat_mem`, `conjL`, `heckeT` | 6–12 | the cohomological level-raising operator; `Def_CohCarrier_Level` 168–259 |
| `coresAdd` + transfer helpers, `LevelLE`, `iotaDeg`, `jDeg`, `pushChar` | 10–25 | the level-map theory (`Def_CohCarrier_Level` 15–84, 300–506) |
| `diamondL`, `opFamily`, `hdata`, `heckeTL`, `Gen` | 1–4 | Hecke-data machinery (`Def_CohCarrier_Inst` 23–113) |

### 1.3 Friction

- **The checker is textual.** The first draft wrote
  `theorem gamma0Units_surjective (M : ℕ) [NeZero M] : …`, which elaborates but
  does not *spell* the pin's `variable (M : ℕ); theorem … [NeZero M] : …`. The
  fix is to mirror the pin's section-variable structure so the raw statement
  text matches. This is playbook §7.4's rule, and it cost one build round.
- **`linter.unusedSectionVars`.** The pin's `[NeZero M]` section variable is
  unused in `mul_inv_mem_GammaH_of_gamma0Units_eq` and
  `slash_mapGL_eq_of_gamma0Units_eq`; the port needs `omit [NeZero M] in` on
  both to stay at 0 warnings. The `omit` line is before the declaration, so the
  checker's statement chunk is unchanged.
- **No route risk.** `gamma0Units_surjective` is the only non-trivial proof
  (Bezout + `ZMod.intCast_zmod_eq_-zero_iff_dvd`); it transcribed and built on
  the first attempt. Nothing here is a mathlib-gap re-derivation: mathlib has
  `Gamma0`, `Gamma0Map`, `Gamma1`, `Gamma`, `det_coe`, `ZMod` but none of the
  `Γ_H` layer.

### 1.4 The dedup this opens

The port now has a public home for the `Γ`-membership vocabulary. The private
duplicates measured in `PORTING-Level.md` §3 are `Γ₁`-specific
(`Gamma_le_Gamma1` ×4, `conj_mem_Gamma1` ×3, `neg_one_mem_Gamma1` ×2,
`conj_mem_Gamma` ×2, `T_mem_Gamma1`/`T_pow_mem_Gamma1` ×2, each), so their
promotion is SET-2's job: L2 adds the `Γ₁` conjugation home and the consumers
(`WeightOne/Gamma1IntegralBasis.lean`, `WeightOne/Gamma1Basis.lean`,
`WeightOne/Gamma0Rationality.lean`) import it instead of re-proving. The
blueprint's estimate is ≈230 lines removed.

## §2 SET-2 — the `Γ₁` / diamond vocabulary (l2)

Not started. Work order: [../topics/level/TOPIC-l2-gamma1-diamond.md](../topics/level/TOPIC-l2-gamma1-diamond.md).

## §3 SET-3 — cosets and the index (l3)

Not started. Work order: [../topics/level/TOPIC-l3-coset-index.md](../topics/level/TOPIC-l3-coset-index.md).
