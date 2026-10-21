# The Deligne–Serre Prop. 7.2 pair — the `GL₂` count and its Serre-image premise: port record

**Status: landed 2026-10-20.** One set, **two modules, 53 statement-checked declarations**
(13 + 40), pinned `aa2d8b3`, port at mathlib `v4.34.0`. Execution was split: the manager ported the
definition and statement layer (the eight pin definitions, every statement verbatim, 48 `sorry`
bodies), one coding subagent ported the proof bodies. Order:
[../topics/deligneSerre/WORKORDER-MG4-matrix-gl2-count.md](../topics/deligneSerre/WORKORDER-MG4-matrix-gl2-count.md);
pricing: [../topics/deligneSerre/TOPIC-matrix-family-in-cone.md](../topics/deligneSerre/TOPIC-matrix-family-in-cone.md)
§ "Set MG4".

## 1. Measured table

| module | pin `S_` lines | port lines | declarations (public / private) | wired | `lake build` | checker |
|---|---:|---:|---:|---:|---|---|
| `ModularCurve/SerreImage/ContainsSL2.lean` | 390 | 407 | 13 / 0 | **13** | 4,320 jobs / 5.9–6.3 s | **13 ok**, 0 / 0 / 0 |
| `ModularCurve/SerreImage/SemisimpleOrderBound.lean` | 1,242 | 1,263 | 40 / 3 (`main`s) | **40** | 4,326 jobs / 8.9–10 s | **40 ok**, 0 / 0 / 0 |
| **total** | **1,632** | **1,670** | **53 / 3** | **53** | | **53 ok, 0 mismatch, 0 missing, 0 own, 0 kw** |

The estimate was 1,611 net new math lines; the port is 1,670 raw lines, the difference being the two
headers and the block/section structure. `wired` = the public declarations plus the headline stated
once; the three `private theorem main`s are unwired, and no declaration is registered as tier 3.

`check_port.py --all`: **3,539 ok, 0 mismatch, 0 missing, 11 own, 0 kw over 135 modules** (from
3,486 over 133). Rebuilt from scratch (oleans deleted) by the manager after the subagent's report:
6.1 s and 10 s, no warning from either file. `#print axioms` on both headlines:
`[propext, Classical.choice, Quot.sound]`. `rg` sweep for `sorry`/`admit`/`axiom`/`native_decide`/
`maxHeartbeats`/`import Mathlib`: empty; `git status` shows only the new directory.

## 2. The homing decision

Both modules live in **`ModularCurve/SerreImage/`** — one theory directory: the Serre-image
generation theorem and the order bound that consumes it. The first homing attempt put the count under
`LinearAlgebra/Matrix/GeneralLinearGroup/`, mirroring mathlib; that was reverted because its proof
uses `ModularCurve.SerreImage.contains_SL2` and its statement names
`Deformation.matrixRepresentation`, so it would have made a `LinearAlgebra/Matrix` module import from
`ModularCurve` — the dependency inversion the homing standard forbids, and a first for a
`LinearAlgebra/Matrix` module in this tree. The standard's rule 1 settles the direction: a theory
that depends on a new theory from another area stays with that theory. The **namespace** stays with
the object (`Matrix.GeneralLinearGroup` for the headline, the pin's `KleinFixedPointCount` /
`DicksonPrimeToCharacteristic` / `DeligneSerre72` blocks for the helpers); the **path** names the
subject. Promoting the pair to the library area would mean moving `contains_SL2` (and the
`Deformation` def) first — a separate re-homing, not done here.

## 3. Drift (proof only; no statement or binder touched)

* **One import added** to the count module: `Mathlib.LinearAlgebra.Matrix.CharP` —
  `sub_pow_char_of_commute` needs `CharP (Matrix (Fin 2) (Fin 2) (ZMod ℓ)) ℓ`, which the rest of the
  targeted import set does not deliver (`synthInstanceFailed`). No `import Mathlib`.
* **`haveI`/`letI` → `have`/`let`** in the Prop-goal proofs, at the v4.34 `linter.style.haveILetI`
  sites: the `Finite G`, `Fact ℓ.Prime`, `CharP F ℓ`, `MulAction G (PL F)` and `ComplementedLattice`
  binders in `KleinFixedPointCount` and `DicksonPrimeToCharacteristic`; module 1's
  `exists_natCast_mul_eq` dropped the pin's redundant `haveI : NeZero p` (v4.34 derives it from
  `Fact p.Prime`).
* **v4.34 deprecations**: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `dif_pos` → `dite_eq_left`,
  `Set.Finite.diff` → `Set.Finite.sdiff`, `Set.ncard_diff` → `Set.ncard_sdiff` (all in
  `DeligneSerre72.card_filter_charpoly_le`/`caseB2`).
* No private helper was added, no proof restructured, no `set_option` beyond the pin's
  `autoImplicit false`. The pin's `p2m_*` macros and its `_root_.`-prefixed private mains follow the
  port convention: macros dropped, the mains `private theorem main` in their own namespaces.

## 4. What the set adds

* The **Serre-image generation theorem** (irreducible + nontrivial unipotent ⇒ `SL₂ ⊆ H`) — the D-S
  route's own step — and **Deligne–Serre Prop. 7.2** (few characteristic polynomials ⇒ bounded
  order), with the explicit witness `A = (4M+1)^4 + 240M + ⌈8M²/(1-2η)⌉₊`.
* The **`Matrix.` namespace's D-S demand is now zero**: `frontier.py --ds` no longer lists a
  `Matrix.` row, and `ModularCurve.` drops by one node and 390 raw lines (238 / 109,359 → 237 /
  108,969). The nine priced rows of the family
  ([TOPIC-matrix-family-in-cone.md](../topics/deligneSerre/TOPIC-matrix-family-in-cone.md)) are all
  landed.
* No host edit, no promotion, no marker entry, no new module beyond the two.
