# Blueprint: the congruence-subgroup / level vocabulary for `FLTForHuman`

**Status (2026-09-27): SET-1 (l1) and SET-2 (l2) complete; SET-3 (l3) has a
work order and is not started.** This is the
fifth Lean port, and
the first that is *vocabulary repair* rather than a new proof cone: it ports the
`Γ_H` / `Γ₁` / diamond / coset layer the Hecke effort already scoped as its
**Stage D** and left deferred, and it consolidates the `Γ`-membership lemmas the
port has so far re-proved `private` two to four times.

SET-1 landed `FLTForHuman/ModularForms/Defs/GammaH.lean` (25 declarations): the
checker reads **1,355 identical, 0 mismatched, 0 missing**, `lake build` is
green with 0 warnings and no `sorry`, `spec/LevelConsumer.lean` is at
**0 errors**, and `#print axioms` on the headlines is
`[propext, Classical.choice, Quot.sound]`. The measured record is
[../logs/level-port.md](../logs/level-port.md) §1. SET-2 landed
`FLTForHuman/ModularForms/Level/Diamond.lean` (31 declarations) and the Tier-2
strengthening of `HeckeRepresentatives.heckeRep_mul`: the checker reads
**1,386 identical, 0 mismatched, 0 missing**, `lake build` is green with 0
warnings, and the new `[diamond]` consumer zone is at 0 errors; the record is
§2. SET-3 (l3) has a work order and is not started (its cost is re-priced to
≈747 content lines in §5 and the topic).

## 0. Scope

Targets, in the Hecke effort's own words
([PORTING-Hecke.md](PORTING-Hecke.md) §3.1, [hecke/TOPIC-slash-invariance.md](hecke/TOPIC-slash-invariance.md) §1):

| tier | declarations | prerequisite (pin) | pin lines | verdict there |
|---|---|---|---|---|
| 2 | `Γ₁`, Nebentypus | mathlib `Gamma1`, `DirichletCharacter` | 785 | scoped, not attempted |
| 3 | `Γ_H` ×2 | `Def_CohCarrier_Level` (Γ_H) + `GroupTheory.Transfer` | 970 | blocked on a foreign def module |
| 4 | Atkin–Lehner ×8 | `Def_ModularForm_AtkinLehnerDatum`, `alSlash`, `diamondLinH`, `traceLin` | 8,620 | blocked on a foreign def tree |

The recommended order there is **Atkin–Lehner → Γ_H → Γ₁ → `HeckeULower`**, with
Γ_H "gated on porting `CohCarrier.GammaH` (`Def_CohCarrier_Level:133` +
`Def_CohCarrier_Inst`)". This blueprint opens exactly that gate, at the
*vocabulary* level first, so the proof tiers can follow.

**What this port is not.**

| slice | status |
|---|---|
| the Γ_H *proof* tiers (`heckeU_slash_eq_self_of_mem_GammaH`, …) | follow-up sets; this port supplies the vocabulary they were blocked on |
| Atkin–Lehner (`Def_ModularForm_AtkinLehnerDatum`, `alSlash`, `alSlash_*`) | out of scope; a separate theory with its own def tree |
| the cohomological Hecke operator (`coresAdd`, `conjUpperMat`, `conjL`, `heckeT` in `Def_CohCarrier_Level:15–84, 168–259`) | deferred to L3; it is transfer/level-raising, not group vocabulary |
| the modular-curve side (`ModularCurve.XH`, `XHDiamondModL`, `LevelLE`/`iotaDeg`/`jDeg`) | out of scope; the `ModularCurve` theory consumes `GammaH` but is its own cone |

**What it buys.** A single public home for the congruence-subgroup vocabulary
every later level argument needs, and the removal of the port's duplicated
`Gamma_le_Gamma1` / `conj_mem_Gamma1` / `neg_one_mem_Gamma1` / `T_mem_Gamma1`
families (§3).

FLT line numbers and paths are against `anthropics/fermats-last-theorem@aa2d8b3`
(local clone `~/proj/fermats-last-theorem`); mathlib is the project's pinned
**v4.34.0**. The port is `lean/FLTForHuman/` with namespace `CohCarrier` for the
L1 vocabulary (matching the pin, so the checker's name map stays mechanical).

## 1. Organization for math clarity

The rules of [porting-playbook.md](porting-playbook.md) §7.1 and §8 govern.

- **A module is a mathematical role.** The pin's `Def_CohCarrier_Level` (506) is
  four subjects: the `Γ_H` group vocabulary, the transfer/`coresAdd` block, the
  Hecke transfer `conjUpperMat`/`conjL`/`heckeT`, and the level maps
  `LevelLE`/`iotaDeg`/`jDeg`. Only the first is L1; the last is its own topic.
- **Adopt mathlib's interface.** `CongruenceSubgroup.Gamma0`,
  `.Gamma0Map`, `.Gamma1`, `.Gamma`, `Matrix.SpecialLinearGroup.det_coe`,
  `ZMod.intCast_zmod_eq_zero_iff_dvd`, `Subgroup.finiteIndex_of_le` are
  mathlib's; `GammaH` / `gamma0Units` / `IsDiamondLift` are FLT's and keep their
  names.
- **One public home for the duplicated `Γ`-membership lemmas.** The port has
  grown private copies in `WeightOne/` (§3); L2 promotes the shared ones and the
  consumers import instead of re-proving.
- **Statements verbatim from the pin.** L1's declarations have no `Theorems/`
  wrappers (they are `Definitions/`), so the checker verifies them by name
  against the pin's `Definitions/` files — the same arrangement the FFG layer
  used for definition declarations.
- **Count before dropping.** Every pin declaration left out of L1 gets a
  `grep -c` and a reason in the topic order.

## 2. The measured cone

### 2.1 The modules

| pin module | lines | role | in L1? |
|---|---|---|---|
| `Definitions/Def_CohCarrier_Level.lean` | 506 | `gamma0Units`, `GammaH`, conjugation, transfer, `LevelLE`/`iotaDeg`/`jDeg` | 90–154, 261–294 |
| `Definitions/Def_CohCarrier_Inst.lean` | 118 | `gamma0Units_surjective`, `diamondL`, `Gen`, `hdata` | 39–53 |
| `Definitions/Def_ModularCurve_XH.lean` | 179 | `GammaH_bot`, `Gamma1_le_GammaH`, `GammaH_mono`, `translation_mem_GammaH` | 20–68 |
| `Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean` | 262 | `Gamma_le_GammaH`, `gammaLift`, `diamondLinH` | 18–70 (L1), 72–262 (L2) |
| `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean` | 680 | `redMatrix`, `IsDiamondLift`, `diamondLinOne` | 182–247, 462–628 (L2) |
| `Definitions/Def_ModularCurve_ProjectiveLine.lean` | 93 | `ProjectiveLine`, `borel` | L3 |
| `Definitions/Def_ModularCurve_PrimCosetReps.lean` | 49 | `primCosetReps` | L3 |

### 2.2 The declarations, by topic

**L1 — the `Γ_H` vocabulary** (≈210 pin lines):

`Gamma0_d_mul_a`, `gamma0Units`, `val_gamma0Units`, `GammaH`, `mem_GammaH_iff`,
`GammaH_le_Gamma0`, `GammaH_top`, `translation_mem_GammaH`, `Gamma1_le_GammaH`,
`GammaH_bot`, `GammaH_mono`, `Gamma_le_GammaH`, `GammaH_finiteIndex`,
`gamma0Units_surjective`, `gammaLift`, `gamma0Units_gammaLift`,
`unitOfPrimeNotDvd`, `gammaLift_apply_11`, `mul_inv_mem_GammaH_of_gamma0Units_eq`,
`slash_mapGL_eq_of_gamma0Units_eq`, `H1`, `GammaH_normal_in_Gamma0`,
`conj_mem_GammaH`, `conjHom`, `diamondRaw`.

**L2 — the `Γ₁` / diamond vocabulary** (≈250 pin lines):

`wt`, `lift`, `lift_mem`, `lift_apply_one_one`, `d_mul`, `det_mod`,
`mem_Gamma1_of_d_eq_one`, `isUnit_d`, `isUnit_wt`, `IsDiamondLift`,
`exists_isDiamondLift_of_coprime`, `IsDiamondLift.coprime`, `conj_mem_Gamma1`,
`mem_coe_Gamma1_iff`, `toConjAct_inv_smul_coe_Gamma1`, `slashOfMemGamma0`,
`slashLinOfMemGamma0`, `slash_eq_slash_of_isDiamondLift`, `diamondLinOne`;
plus the **Tier-2 strengthening** of the ported `HeckeRepresentatives.heckeRep_mul`
(the pin's `g' 1 1` and `wt` conjuncts; the port deliberately dropped them).

**L3 — cosets and index** (≈747 content lines, re-priced 2026-09-27 by the
SET-2 reconnaissance; see `level/TOPIC-l3-coset-index.md`):

`IsUnimodularRow`, `UnimodularRow`, `ProjectiveLine`, `ProjectiveLine.map`,
`borel`, `mem_borel_iff`, `sl2_surj`, `exists_sl2_int_lift`,
`Gamma0_eq_comap_borel`, `firstColumnClass`, `firstColumnClass_eq_iff`,
`card_quotient_borel`, `Gamma0_index`, `card_projectiveLine_zmod`,
`primCosetReps`, `mem_primCosetReps`, `card_primCosetReps_eq_dedekindPsi`.

The two `GammaHUpper` index facts (`index_GammaHUpper_of_prime` = ℓ+1,
`_of_dvd` = ℓ) sit at the L1/L3 seam: they need `GammaH` (L1) and the coset
counting (L3). Deferred to a follow-up once both are green.

### 2.3 The outbound interface tier

`Def_CuspForm_HeckeOperatorFormsGammaH` has 80 consumers (36 in statements),
`Def_CuspForm_Gamma1HeckeOperators` 24 (10), and `Def_CohCarrier_Level` is
imported by the whole Eichler–Shimura / mod-`p` tower. The vocabulary is
therefore the highest-reuse surface in the automorphic area, which is why it is
ported *first* and as definitions plus short lemmas, not as a proof cone.

## 3. Deduplication already visible

The port has re-proved the `Γ`-membership family privately:

| declaration | private copies | files |
|---|---|---|
| `Gamma_le_Gamma1` | 4 | `WeightOne/Gamma1IntegralBasis.lean:148`, `WeightOne/Gamma1Basis.lean:3345`, `WeightOne/LevelFraction.lean`, `WeightOne/…` |
| `conj_mem_Gamma1` | 3 | `WeightOne/Gamma1IntegralBasis.lean:939`, `WeightOne/Gamma0Rationality.lean:1664`, `WeightOne/…` |
| `neg_one_mem_Gamma1` | 2 (+2 GL forms) | `WeightOne/Gamma1IntegralBasis.lean:604`, `WeightOne/Gamma1Basis.lean:4171` |
| `T_mem_Gamma1` / `T_pow_mem_Gamma1` | 2 | `WeightOne/Gamma1Basis.lean:1228`, `WeightOne/Gamma0Rationality.lean:1657` |
| `conj_mem_Gamma` | 2 | `WeightOne/Gamma1Basis.lean:3341`, `WeightOne/Gamma0Rationality.lean:1680` |
| `one_mem_strictPeriods_Gamma1` | 2 | `WeightOne/Gamma0Rationality.lean:1015`, `WeightOne/…` |

(Counts from `grep -c` over `FLTForHuman/`, 2026-09-27.) L2 gives the shared
`conj_mem_Gamma1`/`mem_coe_Gamma1_iff`/`toConjAct_inv_smul_coe_Gamma1` a public
home; the reorg then replaces the private copies by imports. Two of the copies
(`Gamma_le_Gamma1`) are one-liners that belong beside the groups they relate.

**Measured saving:** the Γ₁-conjugation block is ~60 lines per copy; the shared
home is ~90 lines. Four copies + the shared home is ≈330 lines today; one home
plus six one-line imports is ≈96. Net ≈230 lines removed, before the copies in
the not-yet-counted files.

## 4. Module layout

```text
lean/FLTForHuman/ModularForms/
  Defs/
    GammaH.lean        -- L1: gamma0Units, GammaH, membership, top/bot/mono,
                       --     surjectivity, gammaLift, normal/conjugation, H1/diamondRaw
    HeckeRepresentatives.lean  -- existing; L2 strengthens heckeRep_mul in place
  Level/
    Diamond.lean       -- L2: IsDiamondLift, diamondLinOne, the Γ₁ conjugation home
    Coset.lean         -- L3: ProjectiveLine, borel, sl2_surj, Gamma0_index
```

The reorg decision (§8 of the playbook): `Γ_H` is shared vocabulary, so it goes
in `Defs/`; the diamond and index developments are the theories, so they get
`Level/`. The existing `HeckeRepresentatives.lean` stays where it is (its
subject is the Hecke representatives); L2 only strengthens one lemma in it.

## 5. Topics and sets

| topic | object | pin lines | ≈ port | prereq |
|---|---|---|---|---|
| **l1** | the `Γ_H` vocabulary | ≈210 | 220–280 | mathlib only |
| **l2** | the Γ₁ / diamond vocabulary | ≈250 | 260–330 | l1, `HeckeRepresentatives` |
| **l3** | cosets and the index `ψ(N)` | ≈747 | 740–750 | l1 |

Planned sets:

- **SET-1 = l1** — the vocabulary the Hecke Stage D is gated on.
- **SET-2 = l2** — the diamond vocabulary and the `HeckeRepresentatives`
  strengthening; the `WeightOne` dedup reorg lands here.
- **SET-3 = l3** — the projective line, the Borel quotient and the index.

## 6. Risks, in the order they will bite

1. **`gamma0Units_surjective`'s witness.** The pin builds an explicit integer
   lift `!![u⁻¹.val, k; M, u.val]` from a Bezout relation; the only risk is the
   `ZMod.val`/`Int.cast` coercion dance. It is a transcription, not a route.
2. **`CohCarrier` namespace.** The port has no `CohCarrier` namespace yet. L1
   introduces it deliberately (matching the pin); the checker keys by last name,
   so this is free, but an accidental clash with a future `CohCarrier` module
   should be avoided by keeping L1 the only home.
3. **The `WeightOne` reorg touches large files.** The private copies are inside
   4,000-line modules. Replace them one file at a time, building after each, and
   only where the statement matches the promoted lemma (some copies have extra
   hypotheses, e.g. `neg_one_mem_Gamma1`'s `N ∣ 2`).
4. **The Tier-2 `heckeRep_mul` strengthening.** Restoring the pin's `g' 1 1` and
   `wt` conjuncts changes an existing public statement's type; the two Γ₀
   consumers (`HeckeInvariance.lean`) do not use those conjuncts, so they are
   unaffected, but the change must be made by *adding* conjuncts to the tuple,
   which changes pattern-matching use sites. Check with the consumer zone.

## 7. Verification

- **Statement checker.** L1 has no `Theorems/` wrappers; its declarations are
  verified by name against `Definitions/Def_CohCarrier_Level.lean`,
  `Def_CohCarrier_Inst.lean`, `Def_ModularCurve_XH.lean` and
  `Def_CuspForm_HeckeOperatorFormsGammaH.lean`, all appended to `SOURCES`.
  `PORT_FILES` gains `FLTForHuman/ModularForms/Defs/GammaH.lean`.
- **Consumer.** The existing `spec/` consumers must stay green; add a zone to
  `spec/ModularCurveConsumer.lean` (or a new `LevelConsumer.lean`) that
  instantiates `GammaH` at `M = 2`, checks `GammaH ⊥ = Gamma1`, and uses
  `gamma0Units_gammaLift` — a cross-module composition, not a `#check`.
- **Axioms.** `#print axioms` on the L1 headlines returns only
  `[propext, Classical.choice, Quot.sound]`.
- **Build discipline** (playbook §3.11): every build under `timeout 60 lake env
  lean <file>` / `timeout 90 lake build <module>`; expect ≤ 30 s; never raise
  `maxHeartbeats`.

Definition of done per topic: module green with 0 warnings and no `sorry`;
checker 0 mismatched / 0 missing; dedup demonstrated with `grep -c`;
`logs/level-port.md` section; `README.md` row.

## 8. Reproduction recipes

Count the private duplicates:

```bash
cd lean && for n in "theorem Gamma_le_Gamma1" conj_mem_Gamma1 neg_one_mem_Gamma1 \
  T_mem_Gamma1 conj_mem_Gamma; do
  printf '%-28s %s\n' "$n" "$(grep -rh "$n" FLTForHuman --include='*.lean' | wc -l)"
done
```

Locate the pin declarations already ported:

```bash
cd lean/FLTForHuman && for id in GammaH gamma0Units IsDiamondLift diamondLin \
  ProjectiveLine primCosetReps redMatrix heckeRep; do
  printf '%-16s %s\n' "$id" "$(grep -rl "$id" --include='*.lean' . | wc -l)"
done
```

## 9. Links

- [PORTING-Hecke.md](PORTING-Hecke.md) §3.1 — the Stage-D measurement this blueprint consumes.
- [hecke/TOPIC-slash-invariance.md](hecke/TOPIC-slash-invariance.md) §1 — the tiering and the deferred verdicts.
- [porting-playbook.md](porting-playbook.md) — the method, especially §7.1, §8, §9.
- [`Definitions/Def_CohCarrier_Level.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CohCarrier_Level.lean#L133) — the pin's `GammaH`.
- [`Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean#L18) — `Gamma_le_GammaH`, `gammaLift`.
- [`Definitions/Def_CuspForm_Gamma1HeckeOperators.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_Gamma1HeckeOperators.lean#L469) — `IsDiamondLift`, `diamondLinOne`.
- [base/018](../../base/018-congruence-subgroups-and-invariance.md) — the mathematics this vocabulary encodes.
