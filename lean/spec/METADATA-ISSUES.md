# Metadata issues

Bookkeeping problems in the port's **metadata** — `spec-pin:` wires, `PORT_FILES` /
`SOURCES` entries, `decl_markers.tsv` rows, module headers — that do not touch a proof
but make a tool read the tree wrongly.  This is the register for them: the declarations
are right, the metadata says otherwise, and the fix is a header/registry edit made on
that module's **next edit** (the playbook rule: batch the prose and the metadata with the
code change, so no separate build is paid for it).

This is not a register of:

* unverified public surface — that is the generated [UNWIRED-PUBLIC.md](UNWIRED-PUBLIC.md);
* declaration-level checker exceptions — those are rows in [decl_markers.tsv](decl_markers.tsv);
* mathematical, Lean or build frictions — those go to the log in
  [../logs/frictions.md](../logs/frictions.md).  An FR entry may point here when the
  cause is metadata, and a metadata entry may cite the FR that found it.

A metadata issue matters because the planning/checking tools read metadata as evidence:
`frontier.py` decides "ported" partly from a module's `spec-pin:` lines and the checker's
`SOURCES`, so a wire that names a pin source the module does not transpose hides a
missing node from the demand and can put a consumer on the ready shelf.  That is a *false
ready* with the same effect as FR-0044, by a different mechanism.  `check_port.py` does
**not** catch it: it checks the module's declarations against the wire, not the wire's
declarations against the module, so the wired-but-absent source reads `0 missing` (see
MD-002 for the measurement).

## Detecting them

`frontier.py --selfcheck` prints `source node not covered by the name scan` for every
node the source tier claims (a `Thm_` source in `SOURCES` or a `spec-pin:` line) that no
port declaration carries by last name.  On 2026-10-27 the inventory was MD-001..003 below;
SET 7 fixed MD-002 and MD-003, so the live inventory is **MD-001 alone**.  It cannot see a node
that a *different* pin node's last name
shadows (the FR-0047 name-shadow artifact; `weilReciprocity` is the known case — that is a
tool limitation, not tree metadata, and is not listed here).  `twin_scan.py --node <qual>`
says whether the missing statement exists in the port under another name (`twin-public` /
`twin-private`), which is how to tell a wire that only needs a rename from a wire that
names mathematics the port does not have.

A module header edit has no Lean elaboration effect; a registry edit
(`old_check_stmts.py`, `decl_markers.tsv`) never runs Lean either.  Only the declaration
added for an `open` entry's fix needs the module's own build gate.

## Format

Each entry: an id `MD-NNN`, the module/registry and the exact metadata, the symptom, the
effect on each tool (with the command that shows it), the correction (the literal edit),
the verification, and a status.  Do not delete a resolved entry; mark it resolved and keep
the check, so the next reader can see what was wrong.  `open` entries are the work list
for the next edit of their module.

## MD-001 — `IntegralityJqNModC.lean` wires a pin source it deliberately does not port

- **module**: `FLTForHuman/ModularCurve/X1/IntegralityJqNModC.lean`
- **metadata**: header lines 64 and 68 name the deferred row's pin files:
  `spec-pin: Theorems/Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1.lean`
  and its `P2M/Sol/S_…_exists_sum_smul_eq_of_isIntegralQExp_gamma1.lean`.  The module's
  own prose (lines 42–47) says **"Not ported here"**: the headline's one non-elementary
  input is the *modular-form* Gamma₁ rational structure, and the pin chain behind it is
  unported.  The checker's `SOURCES` deliberately has no row for it (see the comment
  above the `Theorems/` block in `old_check_stmts.py`), so the header is the only place
  it is claimed.
- **symptom**: `frontier.py --selfcheck` reports
  `FAIL source tier covered by name tier`, naming
  `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`.  `Frontier.wired_sources()`
  reads every `spec-pin:` line in a module header, so the deferred node is added to the
  frontier and treated as **ported**.
- **effect** (the D–S read, 2026-10-27):
  * `needed [F terminal]` is **1,026 / 406,533** instead of **1,027 / 406,569** (+1 node /
    +36 lines: the node's own `S_` file).  The node's own demand reads as itself only
    because its premise `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` is
    itself caught by the name tier through the *`CuspForm` twin's* last name in
    `Gamma1IntegralBasis.lean` (the pin has both a `ModularForm` and a `CuspForm` node
    with that last name; only the twin is ported).  The deeper undercount is that name
    shadow, not this wire — see the name-shadow note in the frontier README;
  * its consumer `ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem` (80 silo) sits
    on the ready shelf as `needed = 1` / `premises_unported = 0`, because its premise is
    read as ported — a false ready, not visible in the `withheld` block (that block
    covers the prune set only).
- **correction (on the next edit of the module)**: delete the two `spec-pin:` lines for
  the deferred row (64 and 68).  Keep the prose block and the pin citation — they are the
  record of the deferral.  Do not add a `SOURCES`/`PORT_FILES` row; do not touch
  `decl_markers.tsv` (the row is not a declaration exception — it is not in the module at
  all).
- **verify**:
  * `python3 frontier.py --selfcheck` → the `evalFun_pullback` and `inertiaDeg_pos`
    entries disappear with MD-002/003; this one goes too;
  * `python3 frontier.py --ds --ready` → the MC ready shelf loses
    `ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem` (`needed` 1 → 2);
  * `python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/IntegralityJqNModC.lean`
    → still **3 ok / 0 / 0** (no declaration changes);
  * `python3 spec/unwired_register.py --check` → unchanged (the deferred declaration is
    not declared in the module at all).
- **status**: **open** — wait for the next edit of `IntegralityJqNModC.lean` (ModularCurve
  side; not in SET 7).  Found 2026-10-27 while auditing the FR-0044 rows.

## MD-002 — `PlaceEvaluationAlgebra.lean` wires `Divisor.evalFun_pullback`, which it does not declare and cannot host

- **module**: `FLTForHuman/AlgebraicCurve/Defs/PlaceEvaluationAlgebra.lean`
- **metadata**: header line 25,
  `spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_evalFun_pullback.lean`.  The module
  declares the other `evalFun_*` wrappers and `evalFun_single_sub_single`, but **not**
  `AlgebraicCurve.Divisor.evalFun_pullback`; the declaration exists nowhere in the port
  (`twin_scan.py --node AlgebraicCurve.Divisor.evalFun_pullback` → `new`).
- **symptom**: `frontier.py --selfcheck` names `AlgebraicCurve.Divisor.evalFun_pullback`
  as a source node not covered by the name scan, and the frontier treats it as ported.
- **effect**:
  * the pin node (33 silo) is absent from the demand; with the wire removed it is a
    **ready** row (its three premises — `Place.evalAt_norm_eq_prod_fiber`,
    `Place.pairwiseDisjoint_fiber`, `Divisor.support_pullback_subset` — are ported);
  * its consumer `AlgebraicCurve.weilReciprocity_algebraMap` (58) is hidden by the FR-0047
    shadow on the instrument's shelf; in the corrected (shadow-aware) read it would read
    `needed = 1` because this lemma is read ported, although its proof uses it.  The row is
    therefore *not* really ready (it is one row behind the pullback);
  * the module **cannot** host the lemma: the proof needs
    `Place.evalAt_norm_eq_prod_fiber` from `Place/EvalAtNorm.lean`, which the Defs module
    does not import (it imports only `Defs.PlaceEvaluation`), and a `Defs/` module must
    not be moved above the Place layer to reach it.  A wire does not move a declaration
    above its premises;
  * `check_port.py --force` on the module still reports **17 ok / 0 mismatch / 0
    missing** (measured), because it checks the module's declarations against the wire,
    not the reverse.  The false wire is invisible to the checker and live to the
    frontier.
- **correction (SET 7's PAIR order, with the manager's wire fix)**: transcribe the row in
  `Place/EvalAtNorm.lean` (its own subject: the value of a norm on a fibre, and the
  `evalFun` pullback is the fibre computation), wiring **there** the wrapper and the
  `S_` copy; delete line 25 from `PlaceEvaluationAlgebra.lean`.  The row's statement and
  the pin's proof are 33 lines, net 28 (measured `port_advise`/`port_plan` on the row).
- **verify**:
  * `python3 frontier.py --selfcheck` → this entry disappears (the other two remain until
    MD-001/003 land);
  * `python3 frontier.py --ds --ready` → the instrument's shelf gains
    `AlgebraicCurve.Divisor.evalFun_pullback` (33);
  * `AlgebraicCurve.weilReciprocity_algebraMap` (58) is hidden by the FR-0047 shadow on the
    instrument's shelf, but the corrected read drops its `needed` from 2 to 1 as soon as the
    33 is ported — that is the row's own order, not this wire fix;
  * `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Place/EvalAtNorm.lean`
    → 28 → **29 ok**, 0 / 0;
  * `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Defs/PlaceEvaluationAlgebra.lean`
    → still **17 ok / 0 / 0**.
- **status**: **resolved (2026-10-27, SET 7)** — the row landed in `Place/EvalAtNorm.lean`
  (checker **29 ok / 0 mismatch / 0 missing**), the false wire was deleted from
  `PlaceEvaluationAlgebra.lean` (still **17 ok / 0 / 0**), and `frontier.py --selfcheck` no
  longer names the node.  The 33 row is ported; the 58 row is one row behind it (the FR-0047
  shadow still hides it), as planned.

## MD-003 — the checker's `SOURCES` claim the weaker `Place.inertiaDeg_pos`, the port has only the strong form

- **registry**: `lean/spec/old_check_stmts.py:376`,
  `"Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_pos.lean"`.  The port declares only
  `Place.inertiaDeg_pos_of_finiteDimensional` (`WeilExchange/FiberOverCount.lean`, with
  `[FiniteDimensional F F']`; its header lines 5–8 say the pin's weaker `inertiaDeg_pos`
  node is "deliberately not reproduced: it is a consequence of the strong form in three
  lines").
- **symptom**: `frontier.py --selfcheck` names `AlgebraicCurve.Place.inertiaDeg_pos` as a
  source node not covered by the name scan; the sources tier treats it as ported.
- **effect**: the node (214 silo) is absent from the demand and from the shelf, although
  the port has no declaration with that last name.  Removing the source claim (or
  fixing it) is what makes the frontier honest; the alias below is the better fix
  because the node is a real pin row with five call sites.
- **correction (SET 7's manager lane)**: add the two-line alias at the pin's name and
  binders (`[FiniteDimensional F F'] [Algebra.IsSeparable F F']`, the separability unused)
  in `WeilExchange/FiberOverCount.lean`, applying `inertiaDeg_pos_of_finiteDimensional`;
  add `spec-pin:` for the weak `Theorems/Thm_…_inertiaDeg_pos.lean` and its `S_` copy to
  that module's wire.  Keep the `SOURCES` row — it then names a ported statement.
- **verify**:
  * `python3 frontier.py --selfcheck` → this entry disappears;
  * in the corrected read (the false source claim removed), the 214 node enters `needed`;
    after the alias it is ported and the figure falls by 214 lines.  On the instrument the
    alias changes no figure — the node was already read ported — but the marker becomes
    true, which is the point;
  * `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/WeilExchange/FiberOverCount.lean`
    → 3 → **4 ok**, 0 / 0 (the alias matched to the weak wrapper).
- **status**: **resolved (2026-10-27, SET 7)** — the two-line alias and its wire landed in
  `WeilExchange/FiberOverCount.lean` (checker **4 ok / 0 mismatch / 0 missing**), and
  `frontier.py --selfcheck` no longer names the node; the `SOURCES` row now names a ported
  statement.  The 214 row left the demand.

## Resolved / not metadata

* **FR-0044** (`--ready` blind to a prune-set premise): fixed in `frontier.py` on
  2026-10-27; the tool now withholds such rows and reports them.  Recorded in
  [../logs/frictions.md](../logs/frictions.md), not here — it was a tool bug, not tree
  metadata.
* **The FR-0047 name shadow** (`AlgebraicCurve.weilReciprocity` read ported because the ℙ¹
  node `RationalFunctionField.weilReciprocity` shares its last name): a frontier tier
  limitation, recorded in the frontier README's "Notes and limits" and in SET 6 §8.  It
  is not fixed by a header edit — the cure is to port the general node.  SET 7 defers the
  consumer and names the chain.
