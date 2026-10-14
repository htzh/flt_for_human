# WORKORDER-P2 — split the generic valuation-subring core out of the Place headline

**Status (closed 2026-10-14): landed and reviewed green.** One mechanical split; no
new mathematics. **As landed the partition is two unwired modules, not one** — this
order's §1–§4 describe the original one-core plan; the manager re-cut it by subject
after discovering that only 70 of the 124 declarations actually mention a `Place`.
Final shape: **B** = `FLTForHuman/NumberTheory/ValuationSubring/Domination.lean` (54
`Place`-free declarations, 898 lines, public, tier 3) and **A** =
`FLTForHuman/AlgebraicCurve/Place/ValueDictionary.lean` (70 `AlgebraicCurve.Place.*`
declarations, 989 lines, public, tier 3, imports B), with
`AlgebraicCurve/Place/IsPrimeOverValuationSubring.lean` (104 lines, exactly the one
public headline, tier 1) importing A; `ValuationSubringCore.lean` was deleted.
Measured: checker **unchanged** at 9743 identical (671 promoted, 83 renamed), 0
mismatched, 0 missing, 38 own-proof exempted (9781 checked); all three modules build
clean; `unwired_register.py --check` current; a `#check` over all 124 consumer names
resolves. The two-module rationale (tier is per-module, so public-but-unwired needs
an unlisted module) is in [TOPIC-valuation-subring-core.md](TOPIC-valuation-subring-core.md).

**Audience.** A coding session. Read this whole order, then the reuse note
[TOPIC-valuation-subring-core.md](TOPIC-valuation-subring-core.md) and the method
in [porting-playbook.md](../../porting-playbook.md) §3.5, §4, §5.

**Companion.** The split is the outcome of the cross-silo duplication search: the
124-declaration prelude of the row landed by
[WORKORDER-P1-isPrimeOverValuationSubring.md](WORKORDER-P1-isPrimeOverValuationSubring.md)
is generic valuation-subring theory and is duplicated near-verbatim in the 19-file
`ModularCurve.CharPModel` / `PlaceSpecialization` cluster (120 statement-identical,
111 body-identical; the top copy is
`S_ModularCurve_CharPModel_FibreModel_spPlace_surjective.lean`, 4,118 lines). The
core is homed once here, made public, and left unwired.

## 1. Scope

Split `FLTForHuman/AlgebraicCurve/Place/IsPrimeOverValuationSubring.lean` in two:

* a new **tier-3** module `FLTForHuman/AlgebraicCurve/Place/ValuationSubringCore.lean`
  holding the module's entire `private` prelude — **124 declarations** (110
  `theorem`, 10 `def`, 3 `scoped instance`, 1 `abbrev`) — promoted to **public**,
  each with a `-- pin:` provenance comment;
* the existing **tier-1** module reduced to the one public headline
  `AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring`, importing the core.

The headline statement and proof do not change. No new mathematics is written.

**Not this set:** no other module is edited; the new module is **not** wired (not in
`PORT_FILES`); the `RadialRegion` row is untouched; the 19 ModularCurve files are
not ported here (see the reuse note).

## 2. Why this shape (the directive)

* **Natural home:** the prelude is not `Place`-specific — it is the
  `ValuationSubring`/`Subring`/`RingHom`/`Valuation` domination-and-value theory
  plus the `Place` value dictionary. It gets its own subject-named module instead
  of living inside the headline's file.
* **Public, not `private`:** every moved declaration is made public so a future
  consumer (the ModularCurve cluster) never needs a visibility change, which would
  edit the module and trigger a build wave.
* **Unwired:** the new module stays out of the checker's `PORT_FILES`, so its 124
  public declarations do not enter the checked surface; `unwired_register.py`
  records them as tier 3.
* **A note:** [TOPIC-valuation-subring-core.md](TOPIC-valuation-subring-core.md)
  tells the future porter to import, not re-prove.

## 3. Deliverable 1 — `ValuationSubringCore.lean`

Module `FLTForHuman.AlgebraicCurve.Place.ValuationSubringCore`.

**Contents.** Exactly the 124 declarations listed in the generated mapping
`tools/deps/build/vs_core_split.tsv` (columns: `port_dotted`, `kind`, `pin_line`,
`pin_raw`), in the **same source order** and the **same namespaces** they have today
(`ValuationSubring`, `Subring`, `Valuation`, `RingHom`, `AlgebraicCurve` / `Place`,
`IntermediateField`, and the `HasValueAt` namespace block). The mapping was computed
from the checker's own parser over the current module; it is the checklist — a
declaration in the module that is not in the mapping, or vice versa, is a bug.

**Each declaration:**

* drop the leading `private ` (keep `scoped` on the three instances
  `centre_isPrime`, `centre_isMaximal`, `centreOver_isPrime`);
* immediately above it, add the provenance comment (its own line):

  ```lean
  -- pin: <pinName> (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:<pin_line>)
  ```

  where `<pinName>` is the mapping's `pin_raw` with any leading `_root_.` removed
  (e.g. `ValuationSubring.centreOver`, `polynomialEquivClosure_apply`). The format is
  the one `unwired_register.py` reads (`tools/deps/README.md`, "Checker tiers").

**No declaration in the new module is `private`.**

**Header.** A docstring that (a) names the module as the generic valuation-subring
core of the place-realisation development, (b) states it is public but **tier 3**
(unwired) and why, (c) points at
[TOPIC-valuation-subring-core.md](TOPIC-valuation-subring-core.md), and (d) carries
the pinned provenance links:

* `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean`

**Imports.** `FLTForHuman.AlgebraicCurve.Defs.Place`,
`FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR`, and the same Mathlib imports the
current module carries (pin lines 1–20). No bare `import Mathlib`.

## 4. Deliverable 2 — the reduced `IsPrimeOverValuationSubring.lean`

The module keeps:

* its (updated) docstring — the headline's story, plus a line that the generic
  prelude now lives in `AlgebraicCurve/Place/ValuationSubringCore.lean`;
* `import FLTForHuman.AlgebraicCurve.Place.ValuationSubringCore` and whatever
  Mathlib imports the headline still needs (it is fine to keep the current list);
* `set_option autoImplicit false`, `set_option linter.style.haveILetI false` (keep
  only if the headline still needs it — otherwise drop it), `open Polynomial`;
* the single public headline
  `AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring` **exactly as it is
  now**: same statement text, same 46-line proof body, same `-- pin:` comment.

Nothing else. After the split the module declares exactly one declaration.

## 5. Unwired registration

Do **not** add `ValuationSubringCore.lean` to `PORT_FILES` or `SOURCES`. Register
it as tier 3:

```bash
# from the repo root, NOT from lean/ — the tool lives at tools/deps/
python3 tools/deps/unwired_register.py          # rewrites lean/spec/UNWIRED-PUBLIC.md
python3 tools/deps/unwired_register.py --check  # must exit 0
```

The register's summary line should grow by the new module (roughly +124 public,
+124 transcribed). Confirm the new module appears in the summary table and that its
rows carry the pin file/line from the `-- pin:` comments.

## 6. Build discipline (copy, do not paraphrase)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` —
> the cap is **low on purpose**: a declaration that exceeds it has an
> instance-inference defect, and the low cap is what finds it. Never raise
> `maxHeartbeats`, never add a module `set_option maxHeartbeats`. `lake build
> <module>` per finished file, serialized with `flock` and bounded with `timeout`.
> Per wave, build only the wave's affected targets — **never a bare whole-tree
> `lake build`**. A whole-tree build happens once, at the session's end, only after
> the user agrees to it, and never on the agent's own initiative.

Run from `lean/`:

```bash
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.ValuationSubringCore
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.IsPrimeOverValuationSubring
```

## 7. Verification

* **Checker must be unchanged**: `9743 identical (671 promoted, 83 renamed), 0
  mismatched, 0 missing, 38 own-proof exempted (9781 port declarations checked)`.
  The tier-1 module still contributes exactly its one headline; the core is tier 3
  and invisible to the checker. Any other number is a bug.
* **Tier 0 and tier 1** green on both modules, 0 warnings.
* `unwired_register.py --check` exits 0.
* `#print axioms AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring` =
  `[propext, Classical.choice, Quot.sound]`.
* grep sweep over both modules for `sorry` / `admit` / `axiom` / `native_decide` /
  bare `import Mathlib` / `maxHeartbeats` — all zero.
* `git status` shows only the two modules and `spec/UNWIRED-PUBLIC.md`.

## 8. Hub prohibition

This order edits exactly `AlgebraicCurve/Place/IsPrimeOverValuationSubring.lean`,
creates `AlgebraicCurve/Place/ValuationSubringCore.lean`, and rewrites
`spec/UNWIRED-PUBLIC.md` through the tool. Nothing else — no other `.lean` file, no
checker list, no commit.

## 9. Report shape

Report: (1) the two module paths and their sizes; (2) the declaration counts
(moved / staying) checked against `vs_core_split.tsv`; (3) the checker before/after;
(4) the tier-0/tier-1 build results; (5) `unwired_register.py --check`; (6) the
axioms line and grep sweep; (7) `git status`; (8) any deviation, in particular any
declaration the mapping missed or any name the compiler reports as a duplicate.
