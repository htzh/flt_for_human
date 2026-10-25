# The any-field `Φ_p` splitting and its at-slot roots — WORKORDER-GS1 landing

Landing record for the two remaining char-`p` splitting nodes of the `Φ_p` cone, 2026-10-25.
Order: [modularCurve/WORKORDER-GS1-phigen-splits-any-field.md](../topics/modularCurve/WORKORDER-GS1-phigen-splits-any-field.md).
Ground: [ts-general-field.md](ts-general-field.md) — the `TS` field generality, landed the same
day as this set's preparation.

## 1. The nodes

| node | citers | frontier before | after |
|---|---:|---|---|
| `ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot` | 9 | needed 1 | ported |
| `ModularCurve.PhiGen.splits_prime_of_isPrimitiveRoot` | 2 | needed 1 | ported |

The D-S `--ds` demand reads **1,194 → 1,192 nodes / 454,892 → 453,678 raw `S_` lines** (−1,214 =
607 × 2: the pin writes one 607-line development in two byte-identical files, so the pair is priced
and ported once).

## 2. The module

`FLTForHuman/ModularCurve/PhiGenSplitsAnyField.lean` — **489 lines** (134 header with the two
`spec-pin:` lines, 355 body), 19 declarations: 9 public + 10 private.

- public: `PhiGen.splits_prime_of_isPrimitiveRoot`, `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot`
  (the two wrappers verbatim); `PhiGen.phiAtSeed_qExpand_prime_eq`, `PhiGen.phiAtSeed_slot_prime_eq`
  (pin-public engine theorems, pin 426/462); `ModularCurve.roots_prime_at_slot_of_isPrimitiveRoot`
  (518), `roots_prime_at_slot_nodup_of_isPrimitiveRoot` (535),
  `roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot` (558),
  `isRoot_prime_at_slot_iff_of_isPrimitiveRoot` (565), `roots_phiAtSeed_TS` (584) — the pin's
  statements verbatim (see §4 for the four names).
- private engine (pin 267–486, transcribed): `comp_evalAtJ`, `iota`, `iota_root`,
  `iota_units_zeta`, `iota_injective`, `integral` (the 47-line pullback core), `zetaLift`,
  `zetaLift_root`, `zetaLift_units_zeta`, `prod_form_ne_zero` (pin 511, the pin's `private` kept).

The mathematics: apply the ported char-0 `splits_of_prime` at `CyclotomicField p ℚ`, rewrite its
`X`-slot as `phiAtSeed` (`comp_evalAtJ`) and its `jq` as `jqModC` (`coeffEmb_jq`), **pull back** to
the integral cyclotomic order `cyclRing ℤ p` along the injective `iota` (injective because
`cyclotomic p ℚ` is the minpoly of `cycUnit p`, so `map_dvd_map` reflects divisibility), then
**push forward** to an arbitrary field along `AdjoinRoot.lift (Int.castRingHom K) ζ`. The at-slot
form pushes the level-`p` identity through `(qExpand K e).comp (qTwist u)`, and the second headline
is its `e = u = 1` case — the same relation the port already homes for the char-0 pair.

## 3. Reuse — what the ground bought

Of the pin's 607 lines, **no prelude was transcribed**: `TS` and its API (including
`TS_injective` at `[Field K]`, which `roots_prime_at_slot_nodup` needs), the four
`jqModC`/`jqNModC`→`TS` bridges, `phiAtSeed` and its API, `conj`/`conj_zero`/`conj_succ`/`phiProd`,
`cycUnit`/`cycUnit_spec`/`isPrimitiveRoot_pow_div`, `cyclRing`/`cyclZeta`/`cyclRing_root_pow`/
`val_cyclZeta`, `coeffMap_qExpand`/`coeffEmb_qExpand`/`coeffMap_injective`, `coeffEmb_jq`,
`coeffMap_qTwist`, `coeff_jqModC_of_lt`, `units_pow_eq_one_of_isPrimitiveRoot` are all imports.
The pin's `ksplit_exists_isPrimitiveRoot`/`ksplitCycUnit`/`ksplitCycUnit_spec` (14 lines) and
`ksplit_root_pow`/`ksplitZeta` (23) are instances of `Defs/Cyclotomic`'s and
`Defs/KatzLevelPCusps`'s.

Measured against the pre-landing price: `port_advise` + `port_plan` said **397 net new** for the
pair; the landed public+private *new* content is the engine, and the module is 489 lines including a
134-line header — so the price was an upper bound by the whole prelude share, as predicted in the
ground record.

## 4. The one structural decision — four names

The pin states the at-slot roots API twice (this file at level `p` with `jqModC`; `PhiSlotRoots` at
general `N` with `coeffEmb K jq`), each in its own per-file namespace, so both keep the plain names.
A single `ModularCurve` namespace cannot: Lean **refuses the import** of two modules that both
declare `ModularCurve.isRoot_prime_at_slot_iff` (`environment already contains '…'`), which would
make any module wanting both unbuildable. Verified by a two-import probe before deciding. The char-0
copy landed first and is what five modules call, so the char-`p` four take the pin's own
disambiguator for the any-field variants, `_of_isPrimitiveRoot` (the suffix of the two headlines and
of the pin's file names):

| port declaration | pin name, same statement | pin line |
|---|---|---:|
| `roots_prime_at_slot_of_isPrimitiveRoot` | `roots_prime_at_slot` | 518 |
| `roots_prime_at_slot_nodup_of_isPrimitiveRoot` | `roots_prime_at_slot_nodup` | 535 |
| `roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot` | `roots_prime_at_slot_roots_nodup` | 558 |
| `isRoot_prime_at_slot_iff_of_isPrimitiveRoot` | `isRoot_prime_at_slot_iff` | 565 |

Each has a `pin:` row in [spec/decl_markers.tsv](../spec/decl_markers.tsv), so the checker still
diffs it against the char-`p` source by explicit name (verdict `ok`, `how: marker`). `prod_form_ne_zero`
stays `private` as in the pin — its public promoted home is `PhiSlotRoots`' more general copy — and
`roots_phiAtSeed_TS` keeps the pin's name (the char-0 module has no such declaration).

**For the C layer:** [functionFieldGeneration/TOPIC-qexp-function-field-c.md](../topics/functionFieldGeneration/TOPIC-qexp-function-field-c.md)
Set A item 3 is now satisfied by importing `PhiGenSplitsAnyField`, and its call sites use the four
renamed names above.

## 5. Verification

- `lake build FLTForHuman.ModularCurve.PhiGenSplitsAnyField` (under `flock`/`timeout 170`): green,
  module 6.9 s, 4,019 jobs with deps, **0 warnings**, no `sorry`, no `set_option maxHeartbeats`.
- `spec/check_port.py --force --strict-markers`: **9 ok / 0 mismatch / 0 missing / 0 own** on the
  new module (2 headlines + 2 engine theorems + 4 renamed roots + `roots_phiAtSeed_TS`) and
  **19 ok / 0 own** on `Defs/TS.lean` (the four bridges added at pin 105/108/111/114).
- `#print axioms` on both headlines: exactly `[propext, Classical.choice, Quot.sound]`.
- `dedup.py --tier name,shape`: 19 declarations, **0 clusters**.
- Two-import probe of `PhiSlotRoots` + `PhiGenSplitsAnyField`: builds, and the plain names resolve to
  the char-0 copies — the collision is gone.

## 6. Dropped, and why

| dropped | pin | reason |
|---|---|---|
| `PhiGen.roots_nodup_prime_at_slot_of_isPrimitiveRoot` | 596–598 | `private`, a one-line alias of `roots_prime_at_slot_roots_nodup`, no consumer in the pin |
| `qTwistEquiv_apply`, `coeff_qTwistEquiv` | 163–167 | dead in the pin (`coeff_qTwistEquiv` has no consumer anywhere); the one live member `qTwistEquiv` is `Defs/Twist.lean`'s |
| the `TS`/`coeffMap`/`phiAtSeed` prelude | 33–192, 269–281, 296–317, 355–364 | imported (§3) |

## 7. Residue

- `Defs/TS.lean` now carries the four `jqModC`/`jqNModC`→`TS` bridges, which
  `Degree/JqCyclotomicConjugates.lean`'s header had *claimed* were there since before they were:
  the claim is now true. Its `coeff_jqNModC_self`-family notes were reworded (the `TS` route is
  available but the landed proofs stay).
- `coeffMap_qTwist` is the port's general 6-argument spelling (pin: a 3-argument `Units.map`
  special case), so both engine call sites spell `v`/`huv` explicitly — recorded, not changed.
- The char-`p` roots API is a *different statement* from `PhiSlotRoots`' (level `p` vs general `N`,
  `jqModC` vs `coeffEmb`), so this is not a dedup failure: `dedup.py` reports no cluster, and the
  four renames make the two copyable side by side in one import graph.
