# The different's wild lower bound — one-node cut

**Status (2026-10-27): landed and verified.** The node
`AlgebraicCurve.Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois` (899 `S_` lines, 793 net
new) is in `AlgebraicCurve/Differential/Different.lean` under
[WORKORDER-DS1-different-wild-bound.md](WORKORDER-DS1-different-wild-bound.md); the module is on
the wire at **5 ok / 0 mismatch / 0 missing / 0 own**, the node is off the D-S ready shelf, and
the two `jqModC` demands fell 54 → 53 (§4). Everything else the first scoping of this slice
proposed is out (§2) and stays out.

**Correction — why the first proposal was wrong.** The slice was first reported as five nodes
`≈2,700` lines, chosen by name (`--ds --list`) and size, and the `needed` figure was quoted only
for the node that happened to be on the ready shelf. Reading `needed` per node afterwards:

* `Place.ordDiff_D_eq_ord_sub_one`, called "a cheap 178-line opener", has
  **`needed == 6` / 950 lines** — three 79-line `diffCoeff` lemmas and a 508-line
  `ord_diffCoeff_D_nonneg` sit under it;
* the three modular rows are **138 / 54 / 54 nodes** deep (49,114 / 15,737 / 16,001 lines) — the
  modular `jqModC`/`CharP`/`ord_census` cluster, never one wave with the algebraic-curve part.

Neither error is repeated here: §1.1 is the node actually being ported, §1.2 records the bundled
rows with their true `needed` so nobody re-proposes the five-node "slice" by accident.

**Why this node, once the slice is cut.** It is the one row of the slice that is genuinely
ready: `frontier --ds --include-leaves --ready` lists it with `needed == 1`, and every one of
its fifteen direct premises is in the port. It is also the pin's own module for the wild
refinement of a bound the port already carries (the tame `ord f - 1 ≤ ordDiff (df)` in the same
file), so porting it is port-whole work inside a module the port owns, not a new subject.

## 1. Measurement

Corpus at `aa2d8b3`; instruments `frontier`, `port_advise`, `port_plan`, all re-run 2026-10-27.

### 1.1 The node being ported

| node | `S_` lines | decls | needed | home |
|---|---:|---:|---:|---|
| `Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois` | 899 | 62 | **1** | `Differential/Different.lean` |

Statement: `K` algebraically closed of characteristic `p`, `E ⊆ M` finite Galois, `K⟮x⟯ ⊆ M`
finite; if `P` is a place of `M` with `(P.restrict E).ord x = 1` and
`p ^ a ∣ P.ord (algebraMap E M x)`, then

```
P.ord (algebraMap E M x) - 1 + ((p : ℤ) ^ a - 1) ≤ P.ordDiff (D K M (algebraMap E M x))
```

— the tame bound plus the wild correction `p ^ a - 1`. The pin's proof is the `HilbertWildLB`
engine (899 lines: `OrdGe` order calculus, the `adjoinEquiv`/`der` transport, the `ZK` fixed
subfield, the Vieta count, then `main`); `solution` is `main`.

### 1.2 What the first proposal bundled — recorded, not ported

| row | `S_` lines | needed | why it is out |
|---|---:|---:|---|
| `Place.ordDiff_D_eq_ord_sub_one` | 178 | 6 / 950 | its own prelude is 745 lines; a separate order |
| `Place.ord_diffCoeff_D_nonneg` | 508 | 2 | part of that prelude |
| `Place.diffCoeff_smul_D_eq` / `D_ne_zero_of_ord_ne_zero` / `diffCoeff_smul_D_of_ord_ne_zero` | 3 × 79 | 1 each | part of that prelude |
| `ModularCurve.two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five` | 789 | **138 / 49,114** | modular cluster |
| `ModularCurve.seven_le_ordDiff_D_jqModC_of_ord_eq_six` | 412 | **54 / 15,737** | modular cluster |
| `ModularCurve.fourteen_le_ordDiff_D_jqModC_of_ord_eq_twelve` | 412 | **54 / 16,001** | modular cluster |

The equality chain is a legitimate second order (it completes the `diffCoeff` API: the general
forms of the three `_of_ord_eq_one`/`_of_perfectField` specialisations the port already has), but
it is six nodes and ≈900 lines of its own, and it is not needed by this node. The modular three
are a modular wave: their one algebraic-curve prerequisite is this node.

### 1.3 Readiness, checked rather than read off the graph

* **All fifteen direct premises of the headline resolve in the port by name**
  (`exists_ord_eq_one`, `diffCoeff_smul_D_of_ord_eq_one`, `diffCoeff_smul_D_eq_of_ord_eq_one`,
  `ord_diffCoeff_D_nonneg_of_perfectField`, `min_ord_le_ord_add`, `ord_algebraMap`,
  `mem_iff_ord_nonneg`, `deg_ne_zero_of_finiteDimensional_adjoin`, `isRational_iff_deg_eq_one`,
  `D_ne_zero_of_transcendental`, `isSeparable_adjoin_of_ord_eq_one`, and the four orbit nodes
  `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`,
  `exists_algEquiv_smul_eq_of_restrict_eq`, `restrict_ofAlgAut_smul`,
  `deg_eq_one_of_isAlgClosed`).
* **The statement elaborates**: written as a `Prop` against the current port it typechecks with
  `Place.restrict`, `Place.ord`, `Place.ordDiff`, `KaehlerDifferential.D`, `CharP`, `IsGalois`
  and the `adjoin`-finiteness binder. Nothing but the proof body is missing.
* **The seven-declaration prelude is public.** The pin declares `toSemilinear`, `placeAction`,
  `smul_place_def`, `mem_fiberOver_iff_mem_orbit`, `card_stabilizer_mul_card_fiberOver`,
  `inertiaDeg_eq_one_of_deg_eq_one`, `card_stabilizer_eq` publicly in this very file. The port
  carried them `private` inside the old degree-identity module and made them public on
  2026-10-27 when that module was split (`Place/OrbitCardinality.lean`, 8 ok, whose wire names
  this node's `S_` file for exactly this prelude). `port_advise` lists all seven as importable
  substitutions for the slice, so the proof imports them and never re-proves them.

### 1.4 Price

`port_plan --section budget` on the two files of the node (`S_` 899 + the 21-line wrapper):

| | lines |
|---|---:|
| raw `S_` | 899 |
| declaration lines | 858 |
| duplicate copies in the node | 0 |
| boilerplate (imports/attrs/`p2m`) | 41 |
| already in the port (vetted) | 65 |
| **net new math** | **793** |

The 65 are the nine substitutions of §1.3 plus the two order lemmas (`ord_neg'`, `ord_pow'`).
No headline is among them: all 62 declaration groups are new except those nine.

## 2. Scope

**In.** The one node of §1.1, whole: the public headline at the pin's name and its engine
private in `Differential/Different.lean`, plus the three one-line `place`-action consequences
the pin carries beside it (`ord_smul_apply`, `ord_apply_of_smul_eq`, `apply_algebraMap`) and the
private `HilbertWildLB` block they belong to.

**Out.**

* the equality chain of §1.2 (a separate order; its own six nodes and ≈900 lines);
* the three modular consequences (§1.2) and the modular cluster behind them;
* the two tiny ready `ordDiff` rows beside the slice (`Place.ordDiff_zero_of_perfectField`, 31
  lines; `Place.ordDiff_smul_of_perfectField`, 40) — separate pin nodes, no premise of this one;
* `AbelJacobiCard` and everything else in `Def_AlgebraicCurve_DivisorClassGroup.lean` outside the
  `Pic0` definition block.

## 3. Readiness is not demand

This node is ready, and that is the only sense in which it is "next": its consumers inside the
D-S cone are the modular three of §1.2, whose demand is 138 and 54 nodes. Porting it does not
advance `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` until that cluster lands.
It is taken now as port-whole work: the wild bound is a pin node of the differential layer the
port already owns, every premise is closed, and the body is 793 net lines with no new theory. A
scheduler optimizing only for the D-S target would instead fold this node into the modular run
that consumes it.

## 4. Order and checkpoints

0. **A0 — ground, done 2026-10-27.** `Differential/Different.lean` carries the node's
   `spec-pin` pair (`Thm_…isGalois` and its `S_` copy), imports
   `Place/OrbitCardinality.lean` for the prelude, and stays on the wire at 1 ok / 0 missing.
   The workorder is written.
1. **A1 — the body** ([WORKORDER-DS1](WORKORDER-DS1-different-wild-bound.md)), one implementer:
   the public headline, the engine private in the same file, the prelude imported, the pin's
   local `attribute [local instance] placeAction` re-registered **locally** in each section
   that needs it and never globally.
2. **A2 — close, done.** The headline resolves to its `Thm_` copy and the three prelude lemmas
   to `S_…isGalois.lean:360/363/368` (**5 ok / 0 mismatch / 0 missing / 0 own**); axioms
   `[propext, Classical.choice, Quot.sound]`; `move_dead` 0; `dedup` two cost-0 `shape` pairs (the
   pre-existing perfect-field aux/headline pair and the new engine/headline pair); the consumer's
   zone 4 binds the headline and stays at 0 errors; frontier: the node is off
   `--ds --include-leaves --ready`, and the two `jqModC` demands read **53 nodes / 14,838 lines**
   and **53 / 15,102** (from 54 / 15,737 and 54 / 16,001).

   One thing the close had to fix: the port had re-stated `deg_eq_one_of_isAlgClosed` **privately**
   (the orbit module's copy was private, hence unreachable once the two subjects were split into
   different modules). It is the pin's *public* node
   `Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed`, so the orbit copy was promoted to public
   (`Place/OrbitCardinality.lean` now 9 ok, with that node's `Thm_`/`S_` pair on its wire) and the
   copy in `Different.lean` deleted — no cross-module duplicate is left.

   Proof-level deviations from the pin — statement unchanged and wire-verified — are the
   workorder's list: `ord_neg'`/`ord_pow'`/`transcendental_of_ord_ne_zero` are the port's public
   `Place.ord_neg`/`ord_pow`/`transcendental_of_ord_ne_zero`; `exists_constant` goes through
   `Place.ord_sub_evalAt_pos` with `v.evalAt y`; two `min_ord_le_ord_add` calls drop two
   nonzeroness arguments (the port's version takes only `f + g ≠ 0`); `adjoinEquiv`'s `equivOfEq`
   closes with an extra `rfl`; the module adds `open KaehlerDifferential` (the pin spells the
   differential `D`), `set_option linter.style.haveILetI false` (the `haveI` walls are
   load-bearing) and seven per-declaration `omit … in` — not the pin's blanket
   `unusedSectionVars`/`unusedVariables` options.

## 5. Homing

`AlgebraicCurve/Differential/Different.lean`, beside the tame bound it refines. The module is
212 lines and gains ~800; it stays far below the size at which this port splits (the
degree-identity module was split at 2,048 lines and four subjects). The alternative — a new
`Differential/HilbertWild.lean` — buys nothing and would split the two forms of the same bound.

## 6. Decisions

* **D1.** The statement verbatim at the pin's name, public; the engine private in the same file,
  as the pin's `solution := HilbertWildLB.main`.
* **D2.** Port once: the seven-declaration prelude is `Place/OrbitCardinality.lean`'s public block
  (the pin's own public prelude, made public on 2026-10-27 for this consumer); the proof imports
  it. A `private` copy would recreate the 65-line duplication `port_advise` prices.
* **D3.** The pin's `attribute [-instance]` / `[-simp]` walls and its blanket
  `set_option linter.unusedSectionVars false` / `unusedVariables false` are not copied: the
  port uses `omit … in` / `include … in` or fixes the `variable` line. Its local instance
  registration of `placeAction` *is* load-bearing and is kept, locally.
* **D4.** The pin's `d(u t^m)`-style order bookkeeping is kept as the pin writes it (the
  `OrdGe` calculus); it is the proof's own structure, not a port artefact.

## 7. Budget

**793 net new lines**, 62 declarations, no new imports beyond
`Place/OrbitCardinality.lean` (already added in A0) and what the body pulls from
`Differential/Coefficient.lean`. Risk: the one 900-line body and the `local instance` handling;
nothing else has to land first.

## 8. Verification

* wire: `python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Differential/Different.lean
  --force --strict-markers` → 0 mismatch / 0 missing / 0 own, and
  `AlgebraicCurve.Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois` resolves to
  `Theorems/Thm_…isGalois.lean`;
* `lake build FLTForHuman.AlgebraicCurve.Differential.Different` green and silent, one module at
  a time, `timeout 110` (background job if the body makes it longer), log in `lean/tmp`, no
  warnings, no `sorry` / `axiom` / `native_decide`;
* `#print axioms` on the headline = `[propext, Classical.choice, Quot.sound]`;
* `tools/deps/dedup.py Different.lean --min-cost 0` (the engine-plus-headline pair may show as a
  cost-0 `shape` cluster — the pin's structure) and `tools/deps/move_dead.py … --select dead
  --dry-run` (instance-search uses are invisible to it: check call sites before deleting);
* consumer: extend `spec/DegreeIdentityConsumer.lean`'s zone 4 with the wild headline, run it to
  0 errors;
* frontier re-read: the node leaves `--ds --include-leaves --ready` and the two `jqModC` demands
  drop by the one AC node they still count (54 → 53).

## 9. Execution

The manager did A0 (home, wire, import, workorder, this file). One implementer takes A1 under
[WORKORDER-DS1](WORKORDER-DS1-different-wild-bound.md) with its build discipline and its
first-blocker report. The manager closes A2 and records the numbers there.
