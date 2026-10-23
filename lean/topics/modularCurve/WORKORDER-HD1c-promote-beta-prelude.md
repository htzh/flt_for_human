# WORKORDER-HD1c — promote the β-tower prelude into the engine

**Status: landed (2026-10-22)** — see §4. One dispatch, one narrow pass; the residue is closed. Closes the residue recorded in
[WORKORDER-HD1b](WORKORDER-HD1b-beta-row-degree.md) §7: after HD1b the two β proofs carry **6 private
duplicate clusters / 34 lines**, the shared vocabulary of the β tower. They are genuinely
side-independent (their statements never mention `FF`/`FF'`/`BB`, the only per-side fields), so this is
the same promotion pass HD1 made for the α prelude — no new module, no statement moves.

## 1. What is promoted, and where

Home: the **engine namespace** `ModularCurve.HeckeDegree` in
`FLTForHuman/ModularCurve/XH/HeckeDegree.lean` — the module that already owns HD1's public α prelude
(`relfinrank_adjoin_eq_finrank`, `relfinrank_adjoin_ne_zero`,
`isAlgebraic_of_subsingleton_ratAlgebra`, `finiteDimensional_adjoin_of_subsingleton_ratAlgebra`,
`KL`, `EL`, `relfinrank_KL_EL`, …). Both β proofs already import it.

**Public, verbatim from the pin's text** (the private copies in the two modules are the transcription;
move them, do not rewrite them):

| declaration | kind | note |
|---|---|---|
| `F0`, `F0'`, `B0`, `dd` | abbrev | side-independent: `modularFunctionFieldFull M`, `… (M*ℓ)`, `… .map (qExpandₐ ℓ)`, `if ℓ ∣ M then ℓ else ℓ + 1` — **identical in both pin files** |
| `jq_mem_F0`, `jqN_mem_B0`, `adjoin_jq_le_F0` | theorem | `F0`-membership of `jq`/`jqN` |
| `relfinrank_F0_F0'` | theorem | `[F0' : F0] = dd` (full-level `dedekindPsi` computation) |
| `relfinrank_ne_zero_of_tower` | theorem | generic tower non-vanishing |
| `laurentBaseChange_map_qExpand` | theorem | base change commutes with the `q ↦ q^ℓ` map |

**Not promoted** (side-specific, keep them `private` where they are): `FF`, `FF'`, `BB` (X₁ vs X_H
fields — the engine's own `FF` is the Γ_H one, which is why the β blocks live in their own
sub-namespaces), `relfinrank_B0_BB` (mentions `BB`), and everything else in the two β towers.

## 2. Edits

1. `XH/HeckeDegree.lean`: add the ten declarations to `namespace HeckeDegree` (one commented block,
   headed "the β-row prelude — the shared half of the two β proofs"). They are public; the engine's
   existing public surface is unchanged.
2. `XH/HeckeDegree.lean`, `X1/HeckeDegree.lean`: delete the ten from the `DBetaH` / `BetaOne` blocks,
   and make the remaining β code see the engine's copies — the sub-namespaces already have access;
   add `open HeckeDegree` (or qualify `HeckeDegree.F0`) inside the two β namespaces, whichever
   reads better. The call sites of the six theorems do not change.
3. `XH/HeckeDegree.lean` header: one `spec-pin:` line for
   `P2M/Sol/S_ModularCurve_finrankAlong_heckeBetaHBar.lean`, so the promoted declarations are in the
   module's wire (they are pin-private there, matched by direct name). If a promoted declaration
   mismatches, add a `pin:` row to `lean/spec/decl_markers.tsv` naming its exact pin copy in
   `S_…_heckeBetaHBar.lean` **or** `S_…_heckeBetaOneBar.lean` (the two texts agree; take the one that
   matches). Do not edit any statement to make it fit.

## 3. Verification

* `cd lean && flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.ModularCurve.X1.HeckeDegree FLTForHuman.ModularCurve.XH.HeckeDegree` — green, **0 warnings**, no heartbeat bump.
* `python3 lean/spec/check_port.py --force` on both: `0 mismatch, 0 missing`; `X1/HeckeDegree` stays **2 ok**, `XH/HeckeDegree` goes 33 → **43 ok** (ten promoted declarations).
* `python3 tools/deps/dedup.py 'ModularCurve/X1/HeckeDegree' 'ModularCurve/XH/HeckeDegree' --tier name` must read **0 clusters** (this is the deliverable).
* `#print axioms` on the three β/`_of_dvd` headlines unchanged (`[propext, Classical.choice, Quot.sound]`); `grep -c "sorry\|admit"` 0; `frontier.py --ds --ready --nexus --fanin-min 10 --top 3` unchanged (the shelf head stays the commutativity pair).
* `git status --short`.

Stop and report (do not work around) if a promoted declaration's statement does not match either pin
copy, or if opening the engine inside the β namespaces captures a name the β code shadows (`FF`,
`FF'`, `BB`, or a local `dd`).

## 4. The record

| module | lines | public | `check_port --force` |
|---|---:|---:|---|
| `ModularCurve/X1/HeckeDegree.lean` | 451 → **414** | 2 | **2 ok, 0 mm, 0 missing, 0 own** |
| `ModularCurve/XH/HeckeDegree.lean` | 790 → **828** | 33 → **42 + 1 own** | **42 ok, 0 mm, 0 missing, 1 own** |

`python3 tools/deps/dedup.py 'ModularCurve/X1/HeckeDegree' 'ModularCurve/XH/HeckeDegree' --tier name`
now reads **0 clusters** (was 6 clusters / 34 lines) — the deliverable. Build green with 0 warnings,
no heartbeat bump; `frontier.py` head unchanged (`heckeOperatorHAlong_comm`, then
`heckeOperatorOneBar_comm`).

**The one `own:` row, and why it is not an alias.** Nine of the ten promoted declarations are
byte-identical to the pin. The tenth, `laurentBaseChange_map_qExpand`, has the pin's `.map
(qExpandAlg L ℓ)` where the port spells `.map (qExpandAlgHomC L ℓ)`: the pin's `qExpandAlg` is its
private `def` (`DBetaH:213`), and the port gave that map the public home `ModularCurve.qExpandAlgHomC`
(`ModularCurve/Frobenius/Defs.lean:75`). Restoring the pin's spelling through a private alias would
put a private name inside a public statement and make a rectification look like a transcription, so
the delta is recorded instead:

```
FLTForHuman/ModularCurve/XH/HeckeDegree.lean  ModularCurve.HeckeDegree.laurentBaseChange_map_qExpand
  own: restated with the port's qExpandAlgHomC for the pin's private qExpandAlg; the statement is
       the pin's up to that rectified map name
```

`check_port --force --strict-markers` accepts the row (no stale-marker report), and the module reads
`42 ok / 1 own`. This is the port's documented path for a tier-2 restatement; it is the only `own:` in
the degree layer.
