# WORKORDER-V6 — a degree-N self-isogeny forces Φ_N(j(E), j(E)) = 0

**Status: landed (2026-10-23)** — see §8. Unusual shape: **37 of the pin's 52 declarations already have their
statement in the port** (36 byte-identical, 1 identical up to binder spelling — ≈385 lines not to
re-prove), so this is an *assembly* module plus one promotion pass, not a transcription. One
dispatch: the 15 new declarations are small except the 80-line capstone proof.

## 0. The node

| node | pin `S_` lines | decls | public / private in the pin |
|---|---:|---:|---|
| `WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq` | 647 | 52 | 33 / 19 |

The wrapper `Theorems/Thm_…` is 21 lines: the statement at :18–36 plus a long
`attribute [-instance]`/`[-simp]` block, and a proof that is `p2m_exact_reverting … solution`.

**Readiness, verified (and the recorded gate is stale).** `frontier.py --target …` reports
**needed 1 node / 647 lines** — every premise is in. All **15** direct premises are ported and homed:

| premise | port home |
|---|---|
| `WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq` | `WeierstrassCurve/Isogeny/IntermediateField.lean` |
| `WeierstrassCurve.Affine.exists_algHom_functionField_baseChange_finrankAlong_eq` | `WeierstrassCurve/Isogeny/BaseChangeAlgHom.lean` |
| `WeierstrassCurve.Affine.natCard_ker_pointMapOfPushforward_eq_finrankAlong` | `WeierstrassCurve/IsogenyEndDatum/Vocabulary.lean` |
| `IsAddCyclic.of_squarefree_natCard` | `GroupTheory/SpecificGroups/CyclicSquarefree.lean` |
| `PeriodPair.{jLattice_surjective}` | `Elliptic/PeriodPair/JLine.lean` |
| `PeriodPair.{discriminant_ne_zero, isUniformization_toPoint}` | `Elliptic/PeriodPair/Uniformization.lean` |
| `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq` | `ModularCurve/ModularPolynomialEvalJ.lean` |
| `WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange` | `WeierstrassCurve/Isogeny/VariableChangeAlgEquiv.lean` |
| `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient` | `Elliptic/PeriodPair/LatticeIndex.lean` |
| `ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic` | `ModularCurve/ModularPolynomialEvalJ.lean` |
| `WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem` | `WeierstrassCurve/GenusOnePlaceGateCentred.lean` |
| `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain` | `RingTheory/IntegralClosure/CompleteDVR.lean` |
| `WeierstrassCurve.Affine.hasPrincipalDivisors_functionField` | `Elliptic/PeriodPair/HoloLift.lean` |
| `AlgebraicCurve.normFormulaAlong` | `AlgebraicCurve/WeilExchange/Transport.lean` |

The **recorded block is closed**, twice over:

1. **The co-import collision is fixed.** `IsogenyEndDatum/Vocabulary.lean:14–21` still says this
   node is "blocked on unported `Theorems/` nodes", and `TOPIC-V4` says it is "gated on the
   `PeriodPair` uniformization ladder" — both were true before `IsogenyEndDatum/Engine.lean:96–104`
   made its `instInfinitePlace` **`private`** on 2026-10-06, which is exactly what made
   `Engine.lean` and `GenusOnePlaceGateCentred.lean` importable together. Re-verified: a probe that
   imports `Engine` + `Vocabulary` + `GenusOnePlaceGateCentred` + the whole `PeriodPair` ladder and
   `#check`s the premise statements elaborates clean (`lean/tmp/IW2CollisionProbe.lean`, exit 0).
2. **The `PeriodPair` ladder landed** (`TOPIC-V5` status: U, J and D rows in the port).

**Two stale sentences to correct** (comment-only edits, no declaration changes; say what you did in
the report): `IsogenyEndDatum/Vocabulary.lean` header, the clause "The one H5 vocabulary node still
**not** here is `IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq`, blocked on unported
`Theorems/` nodes outside this cone"; and `TOPIC-V4-isogeny-kernel-rigidity.md`'s "the only Phase D
item left is … still gated on the `PeriodPair` uniformization ladder".

**Demand.** Cited by two: `exists_forall_pointEnd_eq_zsmul_of_transcendental_j` and
`…_of_not_isIntegral_j` — both unported, so this node is again a leaf that closes a Phase-D column
rather than feeding a landed proof.

## 1. Deliverable — one module, mostly imports

`FLTForHuman/WeierstrassCurve/IsogenyEndDatum/DiagonalPhi.lean`.

**Do not re-prove the 37.** `tools/deps/port_advise.py --nodes <node>` prints the mapping (saved at
`lean/tmp/iw2_advise.txt`); it splits them in two:

* **20 importable** (public in the port) — `Elliptic/PeriodPair/Lattice.lean` (9: `G_scale`,
  `g₂_scale`, `g₃_scale`, `g₂_cubed_scale`→, `scale_lattice`, `scaleLatticeEquiv`,
  `discriminant_scale`, `G_eq_of_lattice_eq`, `g₂_eq_of_lattice_eq`/`g₃_eq_of_lattice_eq`),
  `Elliptic/PeriodPair/Uniformization.lean` (4: `discriminantNeZero`, `toPointHom`,
  `ker_toPointHom`, `toPointAddEquiv`), `Elliptic/PeriodPair/LatticeIndex.lean` (`gate_scale_mul`),
  `Elliptic/PeriodPair/PrimCosetReps.lean` (`jLattice_eq_of_lattice_eq`),
  `WeierstrassCurve/Isogeny/KernelCyclicTransfer.lean` (4: `conjSeam`, `conjSeam_isIntegral`,
  `conjSeam_finiteAlong`, `finrankAlong_conj`), and
  `WeierstrassCurve/IsogenyEndDatum/Engine.lean` (`normFormulaAlong_of_elliptic` — note it is
  **already public there**, so this module must import it, never redeclare it: Engine is in the
  import cone, and a second `WeierstrassCurve.Affine.normFormulaAlong_of_elliptic` is a duplicate
  FQN).
* **17 port-private** twins (same statement, `private` in the home module) — see §2; they are the
  reason this order has a promotion pass.

**The 15 declarations that are new** (14 helpers + `solution`), with the pin's sizes and visibility:

| pin line | decl | vis | lines |
|---:|---|---|---:|
| 46 | `kw_d5eu_ratEquivStrip` (def) | priv | 5 |
| 51 | `kw_countable_algebraicClosure` | pub | 6 |
| 57 | `kw_aleph0_lt_mk_transcendenceBasis_complex` | pub | 16 |
| 72 | `kw_nonempty_ringHom_algebraicClosure_complex` | pub | 25 |
| 106 | `instHasPrincipalDivisorsFunctionField_s13` (instance) | pub | 4 |
| 213 | `kw_isUniformization` | priv | 5 |
| 224 | `kw_toPoint_surjective` | pub | 3 |
| 376 | `mulLeftR_apply` | priv | 2 |
| 378 | `mulLeftR_injective` | priv | 6 |
| 384 | `mulLeftZ_apply` | priv | 2 |
| 505 | `kw_toPointHom_apply` | pub | 2 |
| 523 | `kw_toPointAddEquiv_mk` | pub | 17 |
| 547 | `s13_aeval_diag_eq_eval_map` | pub | 17 |
| 564 | `s13_j_weierstrassCurve_eq_jLattice` | pub | 5 |
| 570 | `solution` | pub | 80 → inlined into the headline |

**Headline**, verbatim from the wrapper (the `universe u` line belongs to it):

```lean
universe u
theorem WeierstrassCurve.Affine.IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    {N : ℕ} [NeZero N] (hN : Squarefree N) (data : ModularCurve.ModularPolynomialData N)
    (D : IsogenyEndDatum W.toAffine) (hdeg : finrankAlong K D.ι = N) :
    Polynomial.aeval W.j (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X) = 0
```

  Its proof is the body of the pin's `solution` (570–647): the transcendence/descent/base-change
  ladder ending in the `PeriodPair` uniformization. No `solution` twin is kept.

**Namespaces.** The pin scatters its declarations (`ModularCurve`, `WeierstrassCurve.Affine`,
`PeriodPair`, `WeierstrassCurve.Affine.IsogenyEndDatum`) and the port's homes use the same ones, so
keep each new declaration in its pin namespace: the two `Cardinal`/transcendence lemmas and
`kw_d5eu_ratEquivStrip` in `ModularCurve`, `instHasPrincipalDivisorsFunctionField_s13` in
`WeierstrassCurve.Affine`, the `PeriodPair` ones in `PeriodPair`, the `s13_*` pair and the headline
in `WeierstrassCurve.Affine.IsogenyEndDatum`.

**Imports** — the port homes above, plus narrow `Mathlib.*` (start from `Cardinal`,
`IntermediateField`, `Pow.Complex`, `Haar.DistribChar`, `Valued.ValuationTopology` and whatever the
`PeriodPair` proofs themselves name). Never `import Mathlib`.

**Four pin-isms, decided here:**

* **Drop the heartbeat bumps.** The pin carries `set_option maxHeartbeats 6400000`,
  `synthInstance.maxHeartbeats 1600000` (:34–35) and a per-declaration
  `synthInstance.maxHeartbeats 6400000 in` (:71). None is inherited: the cap is 200,000, and a
  declaration that will not fit at it is an instance-inference defect (§5).
* **Transcribe the pin's `linter.*` suppressions exactly** (`linter.unusedVariables false`,
  `linter.unusedSectionVars false` at the head and the section-level copies at :194–196) — they are
  pin facts, and do not invent new ones. (If a file-level suppression can be replaced by
  `omit … in` with zero warnings, that is fine — report which.)
* **The `attribute` blocks**: pin :26–29 and the wrapper's exist because `import Mathlib` polluted
  the simp set. Keep only those the build actually demands, and report which survived (expect few
  or none — the port's import set is narrow).
* **Drop the staging**: `P2M.Util`, the `P2MW.S_<stem>` namespace, every `p2m_open`/`p2m_export`/
  `p2m_reactivate`, and the wrapper's `p2m_exact_reverting`.

## 2. The 17 port-private twins — promote, with the checker as arbiter

`port_advise` lists them with their homes: `Elliptic/PeriodPair/{Lattice, LatticeIndex,
Uniformization, Discriminant, PrimCosetReps}.lean`. They are real mathematics with a consumer
outside their module (§5's test), so the answer is promotion, one declaration at a time, with
`check_port` deciding each:

1. remove `private` from the declaration in its home module;
2. rebuild that module — `flock .lake/flt_build.lock timeout 120 lake build <HomeModule>` — and run
   `check_port --force <home module>`;
3. if the module's counts stay clean (`ok` may rise, nothing new in mismatch/own/kw), keep it. If the
   declaration turns up `own`/`missing` because its statement is not in that module's own wire, add a
   row to `spec/decl_markers.tsv` naming the pin declaration and **this** order's pin file, e.g.
   `pin: kw_discriminantNeZero (P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_aeval_j_diag_eq_zero_of_finrankAlong_eq.lean:209)`,
   then re-check that module and `--strict-markers`;
4. if it cannot be made clean without changing the statement or a proof, **revert** and restate that
   one declaration in the new module at the pin's statement (public if the pin's is public, `private`
   if it is private). Report every restatement.

Never edit a landed module's proof or statement to make a promotion fit. The 17 are listed by
`port_advise`; the five home modules are 260 / 1,255 / 1,294 / 248 / 510 lines, so each rebuild is
seconds. **Their dependents then go stale in `.lake` — that is expected, and a whole-tree build is
not this dispatch's (the repository owner runs it).**

## 3. Names

* The port's guard **fails a wired module** whose declaration — public *or* private — carries a
  residual `kw*` token, so nothing may keep one. In the new module: `kw_countable_algebraicClosure` →
  `countable_algebraicClosure`, `kw_aleph0_lt_mk_transcendenceBasis_complex` →
  `aleph0_lt_mk_transcendenceBasis`, `kw_nonempty_ringHom_algebraicClosure_complex` →
  `nonempty_ringHom_algebraicClosure`, `kw_toPoint_surjective` → `toPoint_surjective`,
  `kw_toPointHom_apply` → `toPointHom_apply`, `kw_toPointAddEquiv_mk` → `toPointAddEquiv_mk`, and
  for the two private ones a descriptive name that does **not** collide with an imported FQN — note
  `PeriodPair.isUniformization` is already public in `Uniformization.lean`, so `kw_isUniformization`
  must not become `isUniformization` in `PeriodPair`; keep it local and distinct (or in its own
  namespace). `instHasPrincipalDivisorsFunctionField_s13` and the two `s13_*` names carry no `kw`
  token and are fine.
* One `pin:` row per **renamed public** declaration in `spec/decl_markers.tsv` (`# module`,
  `# full name`, `pin: kw_… (P2M/Sol/S_…aeval_j…lean:<line>)`) — an assertion, not a coincidence:
  it is what turns a content-hash match into a checked one. Six such rows for the six renames above
  (`countable_algebraicClosure`, `aleph0_lt_mk_transcendenceBasis`, `nonempty_ringHom_algebraicClosure`,
  `toPoint_surjective`, `toPointHom_apply`, `toPointAddEquiv_mk`).
* Promoted declarations keep their port names (the home modules already use the rectified ones);
  a promotion whose last name cannot match its wire declaration gets the marker row in §2, not a
  rename.

## 4. Build discipline — read before the first compile

From `lean/`, always through the lock:

```bash
flock .lake/flt_build.lock timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/WeierstrassCurve/IsogenyEndDatum/DiagonalPhi.lean
```

A finished file: `flock .lake/flt_build.lock timeout 120 lake build FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DiagonalPhi`.

* **No tree `lake build`, ever** — in particular not after the promotions; the five home modules are
  rebuilt one at a time and the new module's own build closes the gate.
* Every tool call finishes inside two minutes; a loop is not a way around that. Anything that can
  plausibly run a minute is a **background job** with its own `timeout` and a log under `lean/tmp/`.
* **The 200,000 cap is a diagnostic.** The pin's 6.4M/1.6M bumps are dropped, not transplanted; no
  `set_option maxHeartbeats`, no `synthInstance.maxHeartbeats`. If a declaration will not fit, get the
  floor first (a `lean/tmp/` copy with proofs `sorry`), then use the order's levers (an unused
  section variable becomes a `haveI`/term-`letI` in the proof that needs it, `private abbrev` alias,
  one syntactic form for a type) and stop-and-report rather than raise.
* **Where the friction is expected**: `Cardinal`/`TranscendenceBasis` (`aleph0_lt_mk_…`,
  `countable_algebraicClosure`), the `IntermediateField` descent, and the `PeriodPair`/`Uniformization`
  complex-analysis API — that is `Elliptic/PeriodPair/*`'s territory, and the pin is `v4.33.1`
  (`db584cd6`) against the port's `v4.34.0`; check `lean/topics/TOPIC-mathlib-drift.md` before
  hunting a missing name.

## 5. Gates

```bash
cd lean
flock .lake/flt_build.lock timeout 120 python3 spec/check_port.py --force \
  FLTForHuman/WeierstrassCurve/IsogenyEndDatum/DiagonalPhi.lean
# expected: 10 ok, 0 mismatch, 0 missing, 0 own, 0 kw  (9 new public helpers + the headline)
python3 spec/check_port.py --changed --strict-markers      # exit 0, no stale marker
```

plus: `--force` clean on each of the five promoted home modules (report each reading); `lake build`
of the new module green with **0 warnings**; `#print axioms` on the headline
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`native_decide`/`import Mathlib`; only
`set_option autoImplicit false` (plus the pin's two `linter.*` suppressions); `git status` =
the new module + the five home modules + `spec/decl_markers.tsv` + the two docstring corrections.

## 6. Stop and report — do not improvise — if

a home module's **proof or statement** would have to change (a promotion that needs one is reverted
and restated, per §2 — that is not a stop, but a *weakening* is); a heartbeat raise looks necessary;
a promoted declaration reads `MISMATCH` with a correct `pin:` row in place; the proof needs a
statement outside §0's 15 premises; `--strict-markers` rejects a marker row; a name in a pin
namespace collides with an imported declaration and cannot be renamed without losing the pin's name;
or the capstone's proof seems to need a `PeriodPair` API that does not exist (report the missing
statement — that is a real finding for `CARRY-FORWARD.md`).

## 7. Report shape

(i) the module's lines, declarations, public/private split, namespaces; (ii) every checker reading —
the new module and each promoted home module; (iii) warnings, axioms, the 200k edit loop; (iv) **the
promotion ledger**: the 17, each as *promoted cleanly* / *promoted with a `pin:` row* / *restated*;
(v) every proof deviation from the pin with its site, and confirm no statement deviates; (vi) the
names rectified, the marker rows added, the imports dropped, and which `attribute`/`linter` lines
survived; (vii) the two docstring corrections; (viii) open issues only, for `CARRY-FORWARD.md`;
(ix) `git status`, plus the statement that a tree build is owed because five modules were promoted.

Records: [TOPIC-V5-periodpair-uniformization.md](TOPIC-V5-periodpair-uniformization.md) (the ladder
that gated this node), [TOPIC-V4-isogeny-kernel-rigidity.md](TOPIC-V4-isogeny-kernel-rigidity.md)
(Phase D), `WeierstrassCurve/IsogenyEndDatum/Vocabulary.lean` (the H5 tail and its stale sentence),
[../TOPIC-mathlib-drift.md](../TOPIC-mathlib-drift.md), and
[WORKORDER-IW1](../automorphicForm/WORKORDER-IW1-iwasawa-weyl-unipotent.md) for the house shape of a
single-dispatch order.

## 8. Landed (2026-10-23)

**Three corrections to this order's own numbers, from the checker's parser rather than mine.** The
pin's `S_` file has **55** declarations (36 public, 19 private), not 52: it also carries three
`scoped instance`s (`kw_instIsElliptic`, `kw_infinite_quotientLattice`, `kw_infinite_point`) that
`move_dead.blocks()` does not see. `port_advise` also missed four substituted declarations whose
statements are byte-identical in the port (`mulLeftR_apply`, `mulLeftR_injective`, `mulLeftZ_apply`
in `Lattice.lean`, and `toPoint_surjective` in `Uniformization.lean`). So the split is **41 in the
port, 14 genuinely new**, and the module makes **10 public + 1 private** declarations, of which the
checker diffs **7** (the three `scoped instance`s are invisible to `pg.scan_declarations`).

### The upgrade path (chosen over promoting into legacy modules)

`Elliptic/PeriodPair/{Lattice,Uniformization,Discriminant}.lean` were **unwired and in
`PORT_FILES`** (the frozen registry). All three are now on the current standard and out of it:

| module | before | after | wire |
|---|---|---:|---|
| `Lattice.lean` | unwired, 30 public undiffed | **39 ok**, 0/0/0/0 | 4 pin files + the two sublattice/prim-coset files for the moved lemmas |
| `Uniformization.lean` | unwired, 7 public undiffed | **16 ok**, 0/0/0/0 | wrapper + `S_PeriodPair_isUniformization_toPoint` + the D-5 `…toPoint_comp_eq_pointMapOfPushforward…` file |
| `Discriminant.lean` | unwired, 5 public undiffed | **8 ok**, 0/0/0/0 | wrapper + `S_PeriodPair_discriminant_ne_zero` |

Their `PORT_FILES` entries are gone (`Basic.lean` is still frozen), so 3 of the 572 exemptions are
retired and the checker's tree reading rose from 168 to **172 modules / 4325 ok**.

### The promotion ledger (21 promotions, 5 homing moves, 8 dedup deletions)

* **Promoted in place** (private → public, checker-clean, no `pin:` row anywhere):
  `Lattice`: `mulLeftR`, `mulLeftR_apply`, `mulLeftR_injective`, `mulLeftZ`, `mulLeftZ_apply`,
  `scaleLatticeEquiv_apply`, `latticeEquivOfEq`. `Uniformization`: `countable_lattice`,
  `sub_fract_mem_lattice`, `apply_eq_apply_of_differentiable_of_forall_periodic`, `toPoint_add_mem`,
  `toPoint_neg`, `toPoint_eq_zero_iff`, `toPoint_add`, `toPoint_surjective`. `Discriminant`:
  `discriminantNeZero_scale_iff`.
* **Moved to their subject home, then promoted**: `mem_scale_lattice_iff` (LatticeIndex → `Lattice`,
  next to `scale_lattice`), `g₂_cubed_scale` and `exists_smul_mem_and_apply_eq_of_forall_sub_mem`
  (PrimCosetReps / LatticeIndex → `Lattice` / `Uniformization`); `apply_eq_apply_of_continuous_of_mapsTo_lattice`
  moved to `Uniformization` keeping `private` (its pin copy is private).
* **`jLattice_scale` — four copies became one.** Its subject home is `Lattice`, but
  `ModularCurve/ModularPolynomialEvalJ.lean` kept a `private` re-derivation, and a *public*
  `PeriodPair.jLattice_scale` upstream makes a private copy of the same name fail to elaborate
  ("a non-private declaration has already been declared"). So the promoting pass migrated that module
  too (see below): `jLattice_scale` is now **public in `Lattice`** and the three former
  re-derivations — `PrimCosetReps`' (13 lines), `ModularPolynomialEvalJ`'s (13 lines, and it was a
  *different* proof: the port's module re-derived `g₂ ^ 3` inline) and `DiagonalPhi`'s restatement —
  are deleted. Four copies of a 3-line proof became one.
* **Duplicates deleted** (the promotions' real payoff — six modules had shadowed copies):
  `PrimCosetReps` (`mem_scale_lattice_iff`, `span_neg_fst`, `im_div_ne_zero`),
  `LatticeIndex` (`sub_fract_mem_lattice`, `apply_eq_apply_of_differentiable_of_forall_periodic`,
  `toPoint_add_mem`), `HoloLift` (`countable_lattice`), and the last two promoted in `Discriminant`
  for the same reason. `dedup.py --cross` over the five PeriodPair modules now reports **0 clusters**
  (it found 2 before the last pair was merged). The one deletion I **reverted** is
  `ModularPolynomialEvalJ`'s, for the reason above.

### The new module

`FLTForHuman/WeierstrassCurve/IsogenyEndDatum/DiagonalPhi.lean` — 11 declarations (10 public, 1
private `ratEquivStrip`), namespaces `ModularCurve` / `PeriodPair` /
`WeierstrassCurve.Affine.IsogenyEndDatum`, importing the 41 substituted declarations from their
homes. Substitutions not written: `instHasPrincipalDivisorsFunctionField_s13` (already public in
`IsogenyEndDatum/DualEndData.lean` — declaring it again is a duplicate FQN) and
`kw_isUniformization` (its only consumers, `ker_toPointHom` and `toPointAddEquiv`, are imported
already proved; porting it would add dead code — recorded, not ported).

**The one substantive proof deviation, and it is the order's own warning come true.** The pin buys
`set_option synthInstance.maxHeartbeats 6400000 in` for `nonemptyRingHom_algebraicClosure`, where
`IsAlgClosed.lift` needs `Module.IsTorsionFree ↥Qs ℂ`; at 20 000 heartbeats the search times out
(unfolding `φQs.toAlgebra`). The port discharges the instance directly instead —
`have hφinj : Function.Injective φQs` from `RingHom.injective_iff_ker_eq_bot` + `Ideal.eq_bot_or_top`
(ker is `⊥` or `⊤`, and `φQs 1 ≠ 0`), then
`Module.isTorsionFree_iff_algebraMap_injective.mpr hφinj` — and the file closes at **200 000** with
an empty log, no cap raise anywhere. This is the instance-defect pattern the drift topic names: the
pin's bump was carrying a missing-instance search, not a genuinely expensive proof. Four local
`set_option linter.style.haveILetI false in` suppressions carry the pin's load-bearing `haveI`s (its
own `linter.*` lines are transcribed; the style linter postdates the pin), and `s13_aeval_diag_eq_eval_map`
lost two unused `simp` arguments.

| gate | reading |
|---|---|
| `check_port --force` on the new module | **6 ok** after the `jLattice_scale` dedup (it was 7), 0 mismatch, 0 missing, 0 own, 0 kw (3 `scoped instance`s not parsed by the checker — Lean-checked only) |
| the touched modules | `Lattice` **40**, `Uniformization` 16, `Discriminant` 8, `LatticeIndex` 61, `PrimCosetReps` 25, `HoloLift` 20, `ModularPolynomialEvalJ` **14** — all **0 / 0 / 0 / 0** |
| `--changed --strict-markers` | **4339 ok**, 0 mismatch, 0 missing, 12 own (pre-existing), 0 kw — **173 modules**, 0 stale markers, **568 exempt** |
| `lake build` | green, 0 warnings from the new module; 200k edit loop empty |
| `#print axioms` | `[propext, Classical.choice, Quot.sound]` |
| dedup / dead code | `dedup.py --within` new module **0 clusters**; `--cross` over the five PeriodPair modules **0 clusters**; `move_dead.py --select dead` on the new module **0 declarations** |
| `git status` | new module + this order; modified `Elliptic/PeriodPair/{Lattice,Uniformization,Discriminant,LatticeIndex,PrimCosetReps,HoloLift}.lean`, `spec/old_check_stmts.py` |

**Pin ranges consumed.** `S_` 1–24 replaced by the header and imports; 25–45 (`namespace P2MW.…`,
`p2m_export`/`p2m_open`, both `[-ext]` attributes, the three `set_option`s) dropped except the two
`linter.*` lines, which are transcribed; 46–96 written (4 declarations); 98–130 substituted; 133–191
substituted; 194–545 substituted except `jLattice_scale` and the three instances; 547–568 written;
570–647 inlined into the headline. `Theorems/` 18–36 verbatim.

**Open issues.**
1. `kw_isUniformization` is **deferred**: no port consumer, and its pin consumers are imported
   already proved.
2. **Resolved** (follow-up below): `jLattice_scale` is public in `Lattice`, and its three former
   re-derivations — including `ModularPolynomialEvalJ`'s — are gone; that module was migrated to the
   `spec-pin:` protocol on the way.
3. The `conjSeam*` pair is the same kind of case one step further out (`WeierstrassCurve.Affine`
   copies of a `ModularCurve` lemma): 2 clusters / 26 lines, left for `ModularPolynomialEvalJ`'s next
   owner.
4. **Tool gap**: `spec/check_port.py`'s parser skips `scoped instance` lines, so a wired module's
   instances are Lean-checked but never statement-diffed — the same blind spot that made
   `move_dead.blocks()` (and my own inventory) under-count the pin's 52 vs 55.

### Follow-up: `ModularPolynomialEvalJ` migrated, and four `jLattice_scale`s became one

`jLattice_scale` is a 3-line proof (`have hα …; unfold jLattice; rw [discriminant_scale,
g₂_cubed_scale, …]`). The port held **four** copies of it, because a `private` declaration does not
survive a module boundary and each consumer re-derived its own: `PrimCosetReps` (13 lines incl. its
docstring), `ModularCurve/ModularPolynomialEvalJ.lean` (13 lines, and a *different* proof — it
re-derived `g₂ ^ 3` inline rather than importing `g₂_cubed_scale`), and the public restatement this
order had just put in `DiagonalPhi.lean`.

Resolving it meant touching `ModularPolynomialEvalJ`, which was still frozen (in `PORT_FILES`,
unwired), so by the same rule as the three `PeriodPair` modules it was brought to the current
standard first:

* a `spec-pin:` header naming its wrapper and its `S_` file → `check_port --force` reads **14 ok, 0
  mismatch, 0 missing, 0 own, 0 kw** (15 public declarations; the one `scoped instance` is invisible
  to the checker's parser);
* its `PORT_FILES` entry retired (568 exemptions now, from 572 at the start of this order);
* then its private `jLattice_scale` deleted.

`jLattice_scale` is now **public in `Lattice`** (its subject home, next to `scale_lattice` /
`g₂_scale` / `discriminant_scale`) and diffed there (`Lattice` 39 → **40 ok**); `PrimCosetReps`,
`ModularPolynomialEvalJ` and `DiagonalPhi` all use that one. The empty scaffolding left behind
(`PrimCosetReps`' `section Homogeneity`, `ModularPolynomialEvalJ`'s `namespace PeriodPair`) went with
it, and both headers' "re-derived here because a `private` name does not cross a module boundary"
sentences were replaced with the truth.

**One dedup opportunity is left in this corner, recorded rather than taken**:
`dedup.py --cross` over `{ModularPolynomialEvalJ, KernelCyclicTransfer, Lattice}` still finds 2
clusters / 26 lines — `conjSeam_finiteAlong` (16 L) and `conjSeam_isIntegral` (10 L), public in
**both** `ModularCurve/ModularPolynomialEvalJ.lean` (in `namespace WeierstrassCurve.Affine`) and
`WeierstrassCurve/Isogeny/KernelCyclicTransfer.lean` (in `namespace ModularCurve`). The pin's home is
`ModularCurve.conjSeam*`, so the `WeierstrassCurve.Affine` spellings are the wrong home; deleting
them costs a proof edit in `ModularPolynomialEvalJ`'s capstone (its uses would need qualifying or an
`open ModularCurve`) and drops that module's `ok` from 14 to 12. That is a homing decision of the
same kind this order made for the scale laws, and it is left for whoever owns `ModularPolynomialEvalJ`
next.
