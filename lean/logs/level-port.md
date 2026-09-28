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

**Deliverable.** `FLTForHuman/ModularForms/Level/Diamond.lean`, 31 public
declarations (303 lines), namespace `ModularForm.Level`; plus the Tier-2
strengthening of `HeckeRepresentatives.heckeRep_mul` and the two consumer
updates (`HeckeRepresentatives.heckeT_slash_mapGL`, `PhiGenDescends`).

| check | result |
|---|---|
| `timeout 90 lake env lean …/Level/Diamond.lean` | green, **0 warnings, no `sorry`** (~4.5 s) |
| `timeout 90 lake build FLTForHuman.ModularForms.Defs.HeckeRepresentatives` | green (~6.5 s; builds `Level.Diamond` in ~4.6 s) |
| `timeout 90 lake build FLTForHuman.ModularForms.HeckeInvariance` | green (~3.1 s after deps) |
| `timeout 90 lake build FLTForHuman.ModularForms.PhiGenDescends` | green (~9–12 s) |
| `timeout 180 lake build` | green, 4,335 jobs, **0 warnings**, 2m44s (re-run after the header edits: 2m55s) — the widely-imported `HeckeRepresentatives` forces the downstream replay |
| `spec/check_flt_statements.py` | **1,386 identical (71 promoted), 0 mismatched, 0 missing, 15 own-proof** (1,401 checked) |
| `spec/LevelConsumer.lean` | **0 errors** (the new `[diamond]` zone) |
| `#print axioms` on `exists_isDiamondLift_of_coprime`, `IsDiamondLift.coprime`, `conj_mem_Gamma1`, `toConjAct_inv_smul_coe_Gamma1`, `slash_eq_slash_of_isDiamondLift`, `diamondLinOne`, `diamondLinOne_one`, `heckeRep_mul` | `[propext, Classical.choice, Quot.sound]` |

### 2.1 What was transcribed

31 declarations from `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean`,
statements verbatim:

| group | declarations | pin |
|---|---|---|
| the character/point layer | `wt`, `wt_infty`, `wt_coe`, `isUnit_wt`, `lift`, `lift_infty`, `lift_coe`, `lift_mem`, `lift_apply_one_one`, `d_mul`, `det_mod`, `mem_Gamma1_of_d_eq_one`, `isUnit_d` | 193–246, 371 |
| the diamond lift | `IsDiamondLift`, `exists_isDiamondLift_of_coprime`, `IsDiamondLift.coprime`, `conj_mem_Gamma1`, `mem_coe_Gamma1_iff`, `toConjAct_inv_smul_coe_Gamma1` | 469–527 |
| the diamond operator | `slashOfMemGamma0`, `coe_slashOfMemGamma0`, `slashLinOfMemGamma0`, `coe_slashLinOfMemGamma0_apply`, `slash_eq_slash_of_isDiamondLift`, `diamondLinOne`, `coe_diamondLinOne_apply`, `coe_diamondLinOne_apply'`, `diamondLinOne_apply_apply`, `diamondLinOne_of_not`, `diamondLinOne_of_not_coprime`, `diamondLinOne_one` | 535–628 |

**Tier 2.** `HeckeRepresentatives.heckeRep_mul` is now the pin's public
`CuspForm.Gamma1Hecke` statement (`:281–285`): the hypothesis is
`hg : g ∈ Γ₀(N)` (was `(N : ℤ) ∣ g 1 0`) and the result carries the `g' 1 1`
entry and the `wt`-equation. The four `_mul_of_eq` lemmas deliberately keep the
Γ₀ `S_` copy's two-conjunct statements; four `private` `_11` refinements
(verbatim copies of the pin's public four) supply the strengthened proof, so no
other public statement moved.

### 2.2 Friction

- **The checker's `heckeRep_mul` shadow.** `Def_CuspForm_Gamma1HeckeOperators`
  provides *two* divergent `heckeRep_mul`s: the Γ₀ `S_` copy
  (`S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0`, two conjuncts, pinned
  namespace `HeckeSlashInvariance`) and the pin's public block (three conjuncts,
  namespace `CuspForm.Gamma1Hecke`). `SOURCES` already listed the former, and the
  checker's bare-name lookup is first-come-first-served, so the strengthened
  declaration is written under the pin's `Gamma1Hecke` namespace segment: the
  checker's **dotted-name fallback** (the mechanism SET-3 T6 already uses for
  `ModularForm.heckeTLin` vs `CuspForm.heckeTLin`) then verifies it against the
  public block. The four `_mul_of_eq` are untouched, so the module's own
  two-conjunct surface stays the Γ₀ copy's. `SOURCES` gained
  `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean` (appended, so it cannot
  flip an earlier last-name match) and `PORT_FILES` gained `Level/Diamond.lean`.
- **v4.34 proof drifts (proof-only).** `rw [Gamma0_mem]` / `simp [Gamma0_mem]`
  on a matrix literal fails under `implicit` transparency (`SL(2,ℤ)` vs
  `{A // A.det = 1}`); the fix is `Gamma0_mem.mpr`, plus
  `set_option backward.isDefEq.respectTransparency.types false` on the
  Γ₁-entry computation (the same device `WeightOne/Gamma0Integral.lean:1595`
  needed). The `SL2_inv_expl` reduction additionally needs `Matrix.of_apply` and
  `Fin.isValue` in the `simp only` set, and `simp [Gamma0_mem]` "made no
  progress" on the Bezout witness. `dif_pos`/`dif_neg` →
  `dite_eq_left`/`dite_eq_right`; `CuspForm.coe_add` → `FunLike.coe_add`.
- **`set_option … in` + doc comment.** `set_option X in` may not follow a `/-- -/`
  doc comment (the parser then expects a declaration keyword), so the private
  `_11` helpers carry `--` line comments.
- **Build cost.** No blow-up: every module ≤ 12 s wall. The 2m44s full build is
  the downstream replay of the widely-imported `HeckeRepresentatives`, not a
  heartbeat blow-up (high parallelism, no single step over ~71 s).

### 2.3 The dedup this opens

`ModularForm.Level.conj_mem_Gamma1` is exactly the statement the `WeightOne/`
private copies re-prove; the replacement map is §2.4. The public `wt` is what
the Tier-2 `heckeRep_mul` consumes. `Level/Diamond.lean` imports mathlib only;
`Defs/HeckeRepresentatives.lean` imports it (for `wt`), so the Tier-2
strengthening lives beside the Γ₀ copy it refines.

### 2.4 The `WeightOne/` replacement map (for the parent's dedup reorg)

SET-2 was authorised **not** to edit `WeightOne/`. Checked against the new
public statements (counts from `grep -rnw` over `FLTForHuman/`; all 18
declaration lines are `private`):

| private copy | file:line | verdict against the new public statement |
|---|---|---|
| `conj_mem_Gamma1` (×4) | `Gamma1IntegralBasis.lean:939`, `Gamma0Rationality.lean:1664`, `IntegralStructure.lean:87`, `Gamma0Integral.lean:1519` | **exact match** with `ModularForm.Level.conj_mem_Gamma1 {γ x} (hγ : γ ∈ Gamma0 M) (hx : x ∈ Gamma1 M)` modulo binder names (`x`/`A`/`g`, `M`/`N`). Replace: `private theorem conj_mem_Gamma1 := ModularForm.Level.conj_mem_Gamma1` (after importing `Level.Diamond`). `Gamma0Rationality.lean:1664`/`Gamma0Integral.lean:1519` use explicit `N`/`M` from a `variable`, which the implicit-`M` public lemma still accepts application-side |
| `Gamma_le_Gamma1` (×4) | `Gamma1IntegralBasis.lean:148`, `Gamma1Basis.lean:3345`, `Gamma0Rationality.lean:1684`, `Gamma0Integral.lean:2127` | **no public counterpart in SET-2.** The TOPIC's "one-liner from `mem`" was not ported. Recoverable from L1 only under `[NeZero N]` (`(CohCarrier.Gamma_le_GammaH N ⊥).trans (le_of_eq (CohCarrier.GammaH_bot N))`); the copies carry no `NeZero`, so promote a standalone 3-line public lemma instead |
| `neg_one_mem_Gamma1` (×2) | `Gamma1IntegralBasis.lean:604`, `Gamma1Basis.lean:4171` | **no public counterpart**, and the copy's extra hypothesis `(hN : N ∣ 2)` means it needs its own name anyway. The TOPIC's table anticipated a public `neg_one_mem_Gamma1`; SET-2's declaration list does not include it |
| `conj_mem_Gamma` (×3) | `Gamma1Basis.lean:3341`, `Gamma0Rationality.lean:1680`, `Gamma0Rationality.lean:2743` | **no public counterpart.** The statement is `α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N` (the principal congruence subgroup `Γ(N)`, a different group from `Γ₁`); `conj_mem_Gamma1` does not cover it |
| `T_mem_Gamma1` (×3) / `T_pow_mem_Gamma1` (×2) | `Gamma1Basis.lean:1228`, `Gamma0Rationality.lean:1657`, `Gamma0Rationality.lean:1661`, `Gamma0Integral.lean:1512`, `Gamma0Integral.lean:2120` | **no public counterpart.** `ModularGroup.T`/`T^t` membership is independent of the diamond layer |

**Net:** only `conj_mem_Gamma1` (4 copies) is a drop-in replacement this set;
`Gamma_le_Gamma1` (4) is recoverable from L1 under `[NeZero]`; the remaining 10
declarations (`neg_one_mem_Gamma1` ×2, `conj_mem_Gamma` ×3,
`T_mem_Gamma1`/`T_pow_mem_Gamma1` ×5) still need promotion.

### 2.5 The `WeightOne/` dedup — done (parent, 2026-09-27)

The parent replaced the four `conj_mem_Gamma1` copies and the two Γ₁ companions
by the shared proofs, keeping each local `private` name as a one-line alias so no
use site moved:

| file | declarations whose proof is now the shared lemma |
|---|---|
| `Gamma1IntegralBasis.lean` | `conj_mem_Gamma1`, `mem_coe_Gamma1_iff`, `toConjAct_inv_smul_coe_Gamma1` |
| `Gamma0Rationality.lean` | `conj_mem_Gamma1` |
| `Gamma0Integral.lean` | `conj_mem_Gamma1` |
| `IntegralStructure.lean` | `conj_mem_Gamma1` |

Each file gained `import FLTForHuman.ModularForms.Level.Diamond` and lost its
private proof body; the statement and name are unchanged, so nothing downstream
moved. `git diff --numstat` over the four files: **+12 / −67 lines** (net ≈ −55),
zero warnings, all four modules green; `spec/check_flt_statements.py` unchanged at
**1,386 identical, 0 mismatched, 0 missing**, `spec/LevelConsumer.lean` 0 errors,
full `lake build` green (replay 1.9 s).

The remaining copies in the §2.4 table are deliberately **not** promoted. Per
playbook §9 the test is mathematical content, not line count: `Gamma_le_Gamma1`
(4), `conj_mem_Gamma` (3), `T_mem_Gamma1`/`T_pow_mem_Gamma1` (5) and
`neg_one_mem_Gamma1` (2) are one-line glue (an entrywise inclusion, a
`Subgroup.Normal.conj_mem` application, `simp`), so promoting them would add
public API plus `OWN_PROOFS` entries for no mathematical gain. §9's escape hatch
still applies if a later theory wants them: promote in the theory they are
*about*.

## §3 SET-3 — cosets and the index (l3)

**Status: complete (2026-09-27).** Three modules landed under namespace
`ModularCurve`. Work order:
[../topics/level/TOPIC-l3-coset-index.md](../topics/level/TOPIC-l3-coset-index.md).

**Target retargeted to `ModularCurve` (2026-09-27).** The code goes to namespace
`ModularCurve` and the `FLTForHuman/ModularCurve/` directory —
`Defs/ProjectiveLine.lean` (the `ℙ¹`/`borel` vocabulary),
`Defs/PrimCosetReps.lean` (`primCosetReps`, beside `Defs/PhiGen.lean`'s
`cosetSubst`) and `Gamma0Index.lean` (the coset bijection, `Gamma0_index`,
`card_projectiveLine_zmod`, `card_primCosetReps_eq_dedekindPsi`). All five pin
files are `Def_ModularCurve_*`/`S_ModularCurve_*`/`Thm_ModularCurve_*`, the three
headlines are `ModularCurve.*`, `dedekindPsi` already lives in
`ModularCurve/Defs/Jq.lean`, and the checker's `norm` strips the `ModularCurve.`
qualifier; the effort is still managed here (see `PORTING-Level.md` §4). The
`Γ_H`/diamond code (l1/l2) stays in `ModularForms/` — it is automorphic — while
the coset/index theory is curve/group mathematics.

**Re-priced 2026-09-27 (read-only reconnaissance).** The five pin files are
**747 content lines** (739 excluding the 8 `p2m_export`/`p2m_open` macros), not
the 180–240 the work order estimated — low by ~3.1–4.2×. The three `S_` files
alone are 658 content lines (193 + 219 + 246); the two `Definitions/` files add
89 (59 + 30). There are zero comment lines in all five files, so
`content = raw − blank − scaffolding` exactly. The work order's item (b) lists
only 6 of the 12 private `Gamma0_index` declarations; the omitted helpers
(`natCast_dvd_int`, `primeSel`, `dvd_primeSel`, `not_dvd_primeSel`,
`exists_coprime_lift`) are load-bearing and cannot be skipped. The work order's
estimate is updated in place.

### 3.1 Deliverables and the measured record

| module | lines | public surface |
|---|---|---|
| `FLTForHuman/ModularCurve/Defs/ProjectiveLine.lean` | 121 | 12 (`IsUnimodularRow`, `isUnimodularRow_one_left`/`_one_right`, `IsUnimodularRow.map`, `UnimodularRow`, `unimodularRowSetoid`, `ProjectiveLine`, `instFiniteProjectiveLine`, `ProjectiveLine.map`, `ProjectiveLine.map_mk`, `borel`, `mem_borel_iff`) |
| `FLTForHuman/ModularCurve/Defs/PrimCosetReps.lean` | 75 | 5 (`primCosetReps`, `mem_primCosetReps`, `cosetConj`, `cosetConj_eq`, `cosetTwoVarPoly`) |
| `FLTForHuman/ModularCurve/Gamma0Index.lean` | 802 | 5 (`exists_sl2_int_lift`, `sl2_surj`, `Gamma0_index`, `card_projectiveLine_zmod`, `card_primCosetReps_eq_dedekindPsi`) |

| check | result |
|---|---|
| `timeout 120 lake env lean …/Defs/ProjectiveLine.lean` | green, **0 warnings, no `sorry`** (~3 s after deps) |
| `timeout 120 lake env lean …/Defs/PrimCosetReps.lean` | green, 0 warnings (~7 s wall / 1.9 s CPU) |
| `timeout 120 lake env lean …/Gamma0Index.lean` | green, 0 warnings (~5 s) |
| `timeout 120 lake build FLTForHuman.ModularCurve.Gamma0Index` | green, 4.4 s (3,147 jobs) |
| `timeout 180 lake build` | green, 4,338 jobs, **0 warnings**, ~7 s (the new modules are leaves — nothing downstream imports them yet, so no replay) |
| `spec/check_flt_statements.py` | **1,408 identical (74 promoted), 0 mismatched, 0 missing, 15 own-proof** (1,423 checked) |
| `spec/LevelConsumer.lean` | **0 errors** (the new `[coset]` zone; `#eval (primCosetReps 2).card` prints `3`) |
| `#print axioms` on `Gamma0_index`, `card_projectiveLine_zmod`, `card_primCosetReps_eq_dedekindPsi`, `sl2_surj`, `exists_sl2_int_lift` | `[propext, Classical.choice, Quot.sound]` |

The checker grew from **1,386 → 1,408 identical** (the 22 public declarations of
the three modules), with **3 promoted**: `sl2_surj` and `exists_sl2_int_lift`
(the two promoted pin-`private` lifting statements) and `ProjectiveLine.map`
(whose bare last name `map` is shadowed in the pin by `IsUnimodularRow.map`, so
the dotted fallback reads the pin's own definition). No new `OWN_PROOFS`
entries: every public declaration is a transcription or a promotion.

### 3.2 What was ported where

- **`ProjectiveLine.lean`** is the verbatim definitions port of
  `Definitions/Def_ModularCurve_ProjectiveLine.lean:14–89` (all 12 public
  declarations). The pin's two `simp only [Set.mem_setOf_eq]` became
  `Set.mem_ofPred_eq` (v4.34), and the deprecated `Mathlib.Data.Finite.Prod`
  import became `Mathlib.Basic.Finite.Prod`.
- **`PrimCosetReps.lean`** ports all five declarations of
  `Definitions/Def_ModularCurve_PrimCosetReps.lean:8–45`; `cosetSubst`
  (`Defs/PhiGen.lean`) is imported. The required pre-port `grep -c` over
  `FLTForHuman/` (before SET-3) found **`primCosetReps`: 0 files, 0 lines;
  `cosetConj`: 0, 0; `cosetTwoVarPoly`: 0, 0**; `cosetSubst` was already in one
  module. So the whole file was missing and was ported whole — nothing was left
  out here. v4.34: `dif_neg` → `dite_eq_right`.
- **`Gamma0Index.lean`** merges the three `S_` files. Public: the three wrapper
  statements verbatim and the two lifting statements (base/018 §4.3). Private:
  the arithmetic block `natCast_dvd_int`/`primeSel`/`dvd_primeSel`/
  `not_dvd_primeSel`/`exists_coprime_lift`; the Borel-quotient block
  `isUnimodularRow_firstCol`/`firstColumnClass`/`firstColumnClass_eq_iff`/
  `card_quotient_borel`; `Gamma0_eq_comap_borel`; the prime-power count
  `isUnit_zmod_prime_pow_iff`/`IsUnimodularRow.isUnit_or_isUnit`/
  `isUnitSubtypeEquivUnits`/`card_not_isUnit_zmod_prime_pow`/
  `card_projectiveLine_prime_pow`; the CRT count `crtFst`/`crtSnd`/`crtFst_apply`/
  `crtSnd_apply`/`card_projectiveLine_mul`; and the 23-declaration
  `PrimCosetCount` block (`h`, `card_filter_coprime_range_mul`, `card_fibre`,
  `gcd_rotate`, `card_primCosetReps_eq_sum`,
  `sum_divisorsAntidiagonal_mul_of_coprime`, `h_mul`, `G`/`G_apply`/
  `isMultiplicative_G`, `h_prime_pow`/`h_one_left`/`h_one_right`/
  `sum_h_prime_pow_partial`/`G_prime_pow`, `sqf`/`sqf_apply`/
  `isMultiplicative_sqf`, `Psi`/`isMultiplicative_Psi`/`Psi_apply`/
  `Psi_prime_pow`, `G_eq_Psi`). As the TOPIC requires, the two counts are
  **independent** in the port too: `card_projectiveLine_zmod` goes through
  `ℙ¹` and `dedekindPsi_*`, `card_primCosetReps_eq_dedekindPsi` through
  `divisorsAntidiagonal` and the multiplicative function `G = Psi`.

### 3.3 Left out, with count and reason

| pin item | `grep -c` in pin | reason |
|---|---|---|
| topic (e) `index_GammaHUpper_of_prime`, `index_GammaHUpper_of_dvd` | 48, 15 | the optional Hecke-coset tail; needs `GammaHUpper`/`Gamma0Upper` (1680/2801 occl.) and the explicit `uElt`/`gElt` representatives, which are the Hecke coset count, not the group vocabulary — the topic defers them |
| the `PrimCosetCount` block's 23 declarations | — | ported, but kept `private` (the pin publishes them); making `h`/`G`/`Psi`/`sqf` public would only invite last-name collisions in the checker, and the TOPIC scopes the public surface to the three headlines |
| the pin's local `set_option maxHeartbeats 3200000` in `S_…card_primCosetReps…` | 1 | not transcribed: the project's global cap is 4,000,000 and the proof builds in ~5 s |
| the pin's `p2m_export`/`p2m_open`/`attribute [-instance]`/`[-simp]` walls | 8 + walls | never carried by the port |

### 3.4 Friction

- **`if_pos`/`if_neg`/`dif_neg`/`Set.mem_setOf_eq` are gone in v4.34.** The
  whole `dvd_primeSel`/`not_dvd_primeSel`/`exists_coprime_lift`/`Psi_prime_pow`
  block rewrote `if_pos`→`ite_eq_left`, `if_neg`→`ite_eq_right`, and the
  `cosetConj_eq` proof used `dite_eq_right`; `borel` used `Set.mem_ofPred_eq`.
- **`Subgroup.index_comap_of_surjective`.** Despite the docstring signature,
  the call form is the pin's: the subgroup is explicit, so
  `Subgroup.index_comap_of_surjective _ (sl2_surj N)`, not the `H`-implicit
  `(sl2_surj N)`. One build round.
- **`isMultiplicative_id`.** It lives in `ArithmeticFunction` (declared in a
  `section Id`, not a namespace), so the port spells it
  `ArithmeticFunction.isMultiplicative_id`; the pin's `p2m_open "ArithmeticFunction"`
  had made it bare.
- **`Mathlib.Tactic.Omega` is not a v4.34 module** (the file lives elsewhere and
  has no olean); `omega` arrives with `import Mathlib.Tactic`. One build round.
- **`linter.style.haveILetI`.** The pin's ~8 `haveI : NeZero …`/`Fact …` walls
  trip the style linter (the instance's type is a `Prop`); disabled file-locally,
  exactly as `ModularForms/Level/Diamond.lean` does.
- **No blow-up, no heartbeat bump.** The largest single build was
  `Gamma0Index.lean` at ~5 s; the pin's 3.2M-heartbeat local cap was not needed.

## §4 Post-SET-3 dedup (2026-09-27)

SET-3 exposed one substantial redundancy: the port already had a **public**
surjectivity theorem, and SET-3's `Gamma0Index.lean` promoted the pin's
`S_ModularCurve_Gamma0_index` copy of the *same* statement plus its 135-line
private lifting block.

| duplicate | where | decision |
|---|---|---|
| `sl2_surj` (public, promoted by SET-3) | `Gamma0Index.lean:169` | made **`private`** — the pin keeps it private; the public statement is the wrapper below |
| `natCast_dvd_int`, `primeSel`, `dvd_primeSel`, `not_dvd_primeSel`, `exists_coprime_lift`, `exists_sl2_int_lift` (all private, ~135 lines) | `WeightOne/LevelOneHauptmodul.lean:81–213` | **deleted**; `LevelOneHauptmodul` imports `Gamma0Index` and proves its public theorem from the shared `ModularCurve.exists_sl2_int_lift` |

Which side stays: the **pin-public** `ModularCurve.surjective_specialLinearGroup_map_zmod`
(`Theorems/Thm_ModularCurve_surjective_specialLinearGroup_map_zmod.lean`, already
in the checker's `SOURCES` and consumed by `Gamma1Basis.lean:1276`) is the single
public surjectivity theorem; the *lifting mathematics* `exists_sl2_int_lift` keeps
one public home in `Gamma0Index.lean`, and `sl2_surj` is the pin-private name it
had in the pin. `LevelOneHauptmodul.lean`: **+1 / −135** lines.

Verification after the trim: checker **1,407 identical (73 promoted), 0
mismatched, 0 missing** (was 1,408 — the now-private `sl2_surj` drops out);
`lake build` 4,339 jobs green, 0 warnings; `spec/LevelConsumer.lean` 0 errors.

**Remaining smaller duplicates** (each has a "which side stays" call and a
rebuild cost; the first was subsequently trimmed — see §5):

- `card_filter_coprime_range_mul`, `slotH` (pin's `h`), `card_fibre`:
  byte-identical private copies in `FunctionFieldGeneration/SlotProduct.lean`
  (T19's re-derived closed form) and `Gamma0Index.PrimCosetCount` (SET-3's
  transcription). Decision: neither theory owns a generic `Nat.totient`/fibre
  count — promote once to `ModularCurve/Defs/`, both import; costs a module plus
  `OWN_PROOFS` exemptions for the port-authored `slotH` name, ≈40 lines saved.
- `det_eq` (`Analytic/Gamma0Cosets.lean:171`) duplicates the public
  `HeckeRepresentatives.det_eq`; `conjSL`/`mapGL_conjSL`/`heckeDiagMatrix_mul_mapGL`
  duplicate `HeckeRepresentatives.heckeDiagMatrix_mul_of_eq'(_11)`. Decision:
  `HeckeRepresentatives` (the public `Defs/` Hecke vocabulary) keeps them and
  `Gamma0Cosets` imports; trimming the second needs the private `_11` refinement
  promoted for the denominator conjunct.

## §5 The counting core, shared (2026-09-27)

The second overlap after SET-3: `card_filter_coprime_range_mul`, the fibre value
and `card_fibre` were byte-identical private copies in
`FunctionFieldGeneration/SlotProduct.lean` (T19's re-derived closed form) and
`Gamma0Index.PrimCosetCount` (SET-3's transcription of the pin's private block).
Both now import them from

- `FLTForHuman/NumberTheory/DedekindPsiCount.lean` — `card_filter_coprime_range_mul`
  (public; mathlib has only its three ingredients, not the block statement),
  `dedekindPsiFibre` and `card_fibre`.

Which side stays: **neither theory**. A generic `Nat.totient`/fibre count is not
`ModularCurve` or `ModularForms` mathematics, so it gets its own `NumberTheory/`
module — exactly the rule `TsumDivisorsAntidiagonal.lean` records for the `tsum`
rearrangement. The pin's value-function names `h` (in
`S_ModularCurve_card_primCosetReps_eq_dedekindPsi`) and `slotH` (T19's re-derived
form) are renamed `dedekindPsiFibre`, because `slotH` is already taken publicly by
`ModularCurve.QExpN.slotH` (the Hecke slot function, a different object).
`Gamma0Index` keeps a two-line local alias `h := dedekindPsiFibre` so its
twenty-odd `h`-lemmas are untouched; `SlotProduct`'s `slotH` uses are renamed.
The two pin-private names go on `OWN_PROOFS` (the block count is a promotion; the
renamed value/fibre are the pin's modulo the rename).

Verification: checker **1,408 identical (73 promoted), 0 mismatched, 0 missing,
17 own-proof**; `lake build` 4,340 jobs green, 0 warnings; `spec/LevelConsumer.lean`
0 errors. `SlotProduct.lean` **+7 / −42**; the new module is 71 lines (25 of
docstring). The line saving is small — the point is the single public API.

**Still open** (from §4): the `det_eq` and `conjSL`/`heckeDiagMatrix_mul_mapGL`
duplicates in `Analytic/Gamma0Cosets.lean`; decision recorded there —
`HeckeRepresentatives` keeps them.
