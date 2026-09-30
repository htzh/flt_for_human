# The Deligne–Serre weight-one port — status, method and subject plan

**Status: the unconditional 54-node slice is COMPLETE (2026-09-29); the
density-dependent and converse halves are deferred behind two large gates (§6).**
This note was rewritten after the fact: §1 records what actually shipped, §2 the
order and the way it was executed, §3 the build economy that made it cheap, and
§6 what remains. Everything is measured against the pin
`anthropics/fermats-last-theorem@aa2d8b3` with `tools/deps`; the port's mathlib is
`v4.34.0`.

The operative work orders are the nine files
[deligneSerre/WORKORDER-H-homes.md](deligneSerre/WORKORDER-H-homes.md),
`WORKORDER-S1-eisenstein.md`, `-S2-hecke-gamma1.md`, `-S3-relevement-lifting.md`,
`-S4-coefficient-ring.md`, `-S5-semisimple-descent.md`,
`-S7-frobenius-density.md`, `-S6-conjugacy-lifting.md`, `-S8-assembly.md` — each a
self-contained brief (scope, pin file:line, exact target statements, homes and
namespaces, route with negatives, build discipline, stop conditions). The
after-the-fact record is [../logs/deligne-serre-port.md](../logs/deligne-serre-port.md);
the running friction/promotion ledger is
[../logs/deligne-serre-friction.md](../logs/deligne-serre-friction.md).

Companions:

- [../../math/019-deligne-serre-weight-one.md](../../math/019-deligne-serre-weight-one.md)
  — the mathematics: the theorem, the lifting, the assembly from residual data.
- [../../studies/deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md)
  — the effort measurement, the subject clusters, and the two gates (§1, §3.1).
- [porting-playbook.md](../porting-playbook.md) — the rules; §2.4 (dedup before
  coding), §3.1–§3.4 (module-as-role, one topic at a time, sets and review gates),
  §3.5 (the build ladder), §3.7 (porting order inside one effort), §4 (faithfulness).
- The earlier planning sketches
  [deligneSerre/TOPIC-port-order.md](deligneSerre/TOPIC-port-order.md),
  [TOPIC-definitions-and-homes.md](deligneSerre/TOPIC-definitions-and-homes.md),
  [TOPIC-theorem-order.md](deligneSerre/TOPIC-theorem-order.md) and
  [TOPIC-weight-one-lifting-and-assembly.md](deligneSerre/TOPIC-weight-one-lifting-and-assembly.md)
  hold the background mathematics; where they disagree with the work orders, the
  work orders and the port are right.
- Adjacent efforts: [PORTING-Hecke.md](PORTING-Hecke.md), [PORTING-Level.md](PORTING-Level.md).

## 0. What this effort is, and is not

**Is.** The weight-one `DeligneSerre.*` family in the three shapes FLT uses:

* **forward** — a normalized weight-one cuspidal newform produces an odd
  finite-image $`\rho_f : G_{\mathbb{Q}} \to \mathrm{GL}_2(\mathbb{C})`$ with
  $`\mathrm{charpoly}(\rho_f(\mathrm{Frob}_p)) = X^2 - a_p X + \varepsilon(p)`$ at
  good $`p`$;
* **lifting** — the reduction of a weight-one mod-$`\ell`$ eigenform is a weight-two
  mod-$`\ell`$ eigenform (multiply by a weight-one Eisenstein series, then the
  *relèvement*);
* **assembly** — semisimple descent, characteristic-polynomial conjugacy, and the
  complex-trace gluing that turn a compatible family of residual representations
  into the complex one.

**Shipped is the unconditional slice**: everything that does not depend on the two
automorphic gates — the lifting half plus the assembly half, 54 nodes. The slice
takes the residual family as a hypothesis (`hfam` in the S8 capstone), so it lands
without the ray-class input or the automorphic layer.

**Is not shipped** (§6): the two gates and the automorphic/adèlic subject beneath
them, the shared ray-class continuation, the density-dependent pair of lemmas, the
forward capstone above them, and the converse cone (local factors and Artin
conductor).

## 1. What shipped

| phase | subject | nodes / modules | written lines | checker (identical) |
|---|---|---|---:|---:|
| **D** | the 20 pin `Def_*` modules | 15 new + 5 verify-only | 1,922 | 2058 → 2252 |
| **H1** | the four shared prelude homes | 4 new | 624 | 2252 → 2295 |
| **H2** | promotions and the 22 clash reconciliations | edits in 11 files | — | 2295 → 2301 |
| **S1** | weight-one Eisenstein series | 5 / 5 | 2,074 | 2301 → 2444 |
| **S2** | Hecke / Γ₁ vanishing and nebentypus | 9 / 5 | 1,893 | 2444 → 2453 |
| **S3** | relèvement and the lifting | 2 / 2 | ~2,000 | 2453 → 2457 |
| **S4** | coefficient ring and Galois conjugation | 6 / 2 new + 2 extended | 1,381 | 2457 → 2463 |
| **S5** | semisimple descent | 1 / 1 | 727 | 2463 → 2467 |
| **S7** | Frobenius density and Frobenius elements | 27 / 17 | ~2,900 | 2467 → 2548 |
| **S6** | representation conjugacy and lifting | 3 / 3 | 1,174 | 2548 → 2551 |
| **S8** | the complex-trace assembly | 1 / 1 | 493 | 2551 → 2552 |
| | **total** | **54 targets / 55 new modules** | **≈15,200** | **2058 → 2552 (+494)** |

Plus the consumer wire test `spec/DeligneSerreConsumer.lean` (281 lines, one
executed cross-module zone per set). Baseline before the effort: 2058 identical /
0 mismatched / 0 missing / 30 own-proof exempted; final: **2552 / 0 / 0 / 30**,
92 promoted from pin-`private` declarations.

Homes, in brief: definitions under their subject directories
(`GaloisRep/Defs/`, `ModularForms/Eisenstein/`, `ModularCurve/Defs/`, `Algebra/`,
`NumberTheory/FrobeniusDensity/`, `FieldTheory/`); the four new prelude homes in §2;
the theorem sets in `ModularForms/Eisenstein/` (S1), `ModularForms/` +
`ModularCurve/` (S2), `DeligneSerre/` (S3, S4's node 6, S8), `Algebra/` +
`GaloisRep/` (S4, S5), `NumberTheory/FrobeniusDensity/` (S7), `GaloisRep/` (S6).

## 2. The porting order and how it was executed

The order is a **forward-import DAG**, and it is the primary planning object:

```text
D    the pin Def_* modules, in their own four-level import order
 └ H1  the shared preludes into four NEW files          (no cascade)
    └ H2  promotions + clash reconciliations in EXISTING files   (the only cascade)
       └ T   the theorem sets, importees first: S1, S2, S3, S4, S5, S7, S6, S8
```

* **D — definitions first.** Nothing can be *stated* before the 20 `Def_*` modules
  exist; they are leaves, cheap to build, and the whole cone imports them. The
  declarations that already had a port home with a different statement are not
  shadowed — they are handed to H2.
* **H1 — the shared preludes into new files.** `port_advise` gave 78 blocks repeated
  inside the 54 targets (585 removable lines by its greedy count); they get one home
  each in *new* files, which touch nothing and so cannot cascade. The proof-dedup
  list misses repeated **definitions**: a manual scan added the union of `om` (four
  Eisenstein files) and `ser` (two), which would otherwise have been copied three
  and two times.
* **H2 — reconciliation in existing files.** The seven port-`private` promotions and
  the 22 clashes (binder-only, naming-only, dropped-conjunct, specialised-vs-general,
  genuine, unrelated collision). This is the *only* phase that re-elaborates
  existing modules; it is done in one pass, then the touched files freeze.
* **T — the theorem sets, importees first.** The unit is the mathematical set (§1),
  not the pin's file order; each set imports only levels below it.

**One work order and one subagent per set, with a review gate between sets.** The
manager writes a self-contained work order — scope; pin files with `file:line` for
every declaration; exact target statements; home modules and namespaces; route with
recorded negatives; the build-discipline block; stop conditions; the report shape —
and hands the subagent that plus the playbook (method), never the whole plan. The
subagent ports, builds, wires the statement checker, and reports. The manager then
reviews the tree itself (checker at 0 mismatched / 0 missing; a bounded build;
hygiene; git state; statement spot-checks) *before* writing and dispatching the next
order. That review is what made a 54-node, 8-set port tractable without one agent
carrying the whole cone.

**Freezing and the friction log.** A file that is ported and reviewed is *closed*.
A worker that needs something from a closed file resolves it locally — a `private`
restatement — and appends an entry to `lean/logs/deligne-serre-friction.md`; it does
not reopen the file. A dedicated **refactor round** at the end promotes the recorded
shares and deletes the local copies. One real duplication surfaced this way
(S3 transcribed S4's node 5 before S4 landed); the refactor round swapped it for the
public copy and deleted the private one.

**Workers stop at a boundary and report.** Two genuine ordering stops occurred —
S7-I's tail node needed S7-II's `degOneSum_add_log_isBigO`, and H1 could not home
`hasSum_ser` because its pin proof calls S1's own target — and both were resolved by
a focused later dispatch rather than by editing a frozen file. Nothing was
`sorry`-ed or weakened.

## 3. The build economy — why the order pays off

This is the methodological finding worth keeping: **the order let the effort run on
per-module builds and a single whole-tree build.** The discipline:

* edit loop `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`
  (writes no `.olean`, recompiles nothing);
* `lake build <module>` when a file is done (writes the `.olean`, builds
  dependencies, never dependents);
* **no bare whole-tree `lake build` during a phase**; one at the milestone;
* every `lake build` serialized with `flock` and bounded with `timeout`;
* never raise the heartbeat cap (a blow-up is bisected, and the wall bound is the
  protection).

Measured here: phase D wrote 1,922 lines and touched **only its own 11 modules'
`.olean`s** — no existing module was re-elaborated. Each set closed on per-module
builds of 2–20 s. The effort's **single whole-tree build was the milestone gate
(4805 jobs, green)**, and because D and H had landed first and every set imports
downward, almost nothing was stale, so it ran in seconds. The earlier failure mode
this avoids is transcribing pin files in filesystem order: each new file then sits
under a large cone that must be re-elaborated, and the full build is paid
repeatedly.

The manager watched this from outside: after each phase, the `.olean` mtimes and the
process table confirmed that only the phase's own modules were being built and that
no bare whole-tree build was running. The subagent briefs carried the four build
rules verbatim, and the two phases that could cascade (D1's remainder, H2) were
bounded on purpose.

## 4. Reuse and dedup, as it actually happened

* The 78 shared in-target blocks were homed once in H1; the load-bearing ones are
  `card_le_of_forall_pow_eq`, `ncard_conj_mem_eq_card_mul_ncard`, the zeta/`tsum`
  chain, and the cotangent calculus of S1.
* 28 substitutions / 21 importable reuse points were imported, not re-proved; S1's
  multiplier imports `ModularFormClass.qCoeff` from the existing `HeckeQCoeff`.
* Three semisimple engines duplicated verbatim between S5 and the *deferred*
  `DSRt` sibling are homed **publicly** so that half can import them.
* The refactor round found exactly one now-redundant private copy (S3/S4's node 5)
  and deleted it. Deliberately kept: S2's prelude copies whose public homes sit in
  the heavy `WeightOne` cone (sharing would invert the import graph),
  `exists_finset_separating` (no public home), and S7-III's deliberate 7-line
  duplicate.
* Coset geometry: the S7 ideal-coset steps use mathlib's `Ideal` orbit API. The
  PhiGen and Hecke SL(2,ℤ) coset ports, and even `FieldTheory/FiniteGroupAction.lean`
  / `WeilExchange/Bifibre.lean`, are the **wrong geometry** for them — a recorded
  negative, not a reuse.

## 5. Verification

The gate that closed each set, and the milestone gate:

```bash
cd lean
python3 spec/check_flt_statements.py          # 2552 identical / 0 / 0
flock /tmp/flt_for_human.lock timeout 400 lake build          # 4805 jobs, green
flock /tmp/flt_for_human.lock timeout 180 \
  lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
```

plus a generated `#print axioms` probe over **all 54 headlines** (every name
resolves, no `sorryAx`, axioms `[propext, Classical.choice, Quot.sound]`), a
`grep` sweep for `sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/
heartbeat overrides, and the workers' one-token checker mutation tests. The full
per-phase numbers are in [../logs/deligne-serre-port.md](../logs/deligne-serre-port.md).

## 6. What remains, and its two gates

The slice stops where the automorphic input begins. The remaining forward work is
the two density-dependent lemmas and the capstones above them, and both hang on one
subject:

* **Gate 1 — the Rankin-type second-moment bound.**
  `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen`
  (271-line statement, **775 new nodes**). It is what makes
  `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd`
  (18 nodes) available.
* **Gate 2 — coefficient-ring finiteness by upper density.**
  `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen`
  (248-line statement, **783 new nodes**). It is what makes
  `DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le`
  (21 nodes) available.

The two gates have almost the same cone, so they are **one subject**, not two: the
automorphic/adèlic `GL₂` layer (scout: 534 nodes / 242k raw `S_` lines) plus the
number-field/adelic infrastructure (133 / 70k) it rests on. The scout's caveat
matters for budgeting: those nodes are mostly self-contained against mathlib and so
show cost 1 in `frontier.py` — read the `S_`-line column, and port the 242k lines
module by module (Iwasawa, Whittaker/cuspidal constituents, Rankin–Selberg), not as
a closure of 534 nodes.

One more seam is already measured. The two density-dependent lemmas also reach the
shared ray-class node `M4aTorus.completedRayL_fe` (12,126 lines), but by exactly one
route — `NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one` — and they
use only its *continuation* conjunct, discarding the functional equation. That is
the classical Hecke continuation of the nontrivial narrow ray-class `L`-function,
strictly weaker than the pin's theorem: behind that one interface the pair is
21 nodes / 8,265 lines, and behind a second (density) interface 5 / 2,428 (scout
§3.1). The full ray-class file is ported once by the converse cone, which does need
its functional equation.

The **converse cone** (`exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace`,
421 nodes) — local factors, Artin conductor, the Artin-`L` functional equation — is
a separate subject and a separate effort.

Because the 54-node slice takes the residual family as a hypothesis and states the
gates as explicit hypotheses, both remainders attach to a **fixed interface**: they
can be ported later without reworking what shipped.

## 7. Reproduce

```bash
cd tools/deps
# the slice's own advice reading
python3 port_advise.py --nodes "$(paste -sd, build/groupA_nodes.txt)" --json build/groupA_advise.json
# the remaining half's two gates
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --top 40
python3 port_advise.py --target 'P2M/Sol/S_DeligneSerre_*'
```

The per-set declaration inventories (pin `file:line` and span for every block) are
the appendices of the nine work orders and were generated with `port_advise`'s
`factor` reading; the checker wiring convention (append the `Thm_*` wrapper *and* its
`S_` file to `SOURCES`, the target's name lives on the wrapper) is in §2 of every
work order and in the friction log.

## 8. Residuals

* `locKer`/`adjoinRoot'` are public in `DeligneSerre/Lifting.lean` with no consumer
  today (kept per the pin).
* A handful of style-linter notes (`linter.style.haveILetI`, `unusedSectionVars`)
  remain in proof modules; pin-inherited deprecations outside the refactor
  whitelist were left as the pin wrote them.
* The private `det_eq` copies in `Gamma1Vanishing.lean`/`HeckeEigenNebentypus.lean`
  are statement-identical to the public `ModularForm.HeckeRepresentatives.det_eq`
  and are the one un-promoted dedup candidate.
* The deferred half as in §6, by design.
