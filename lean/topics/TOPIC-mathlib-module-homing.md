# The homing of mathlib-shaped modules — how the cut was made, why it was wrong, and the standard

**Status: the pass is done (2026-10-20); the descriptive-namespace residue is recorded, not
scheduled.** This note is the durable record of the homing problem that surfaced in the 2026-10-19/20
leaf-node campaign — porting small families of the D-S cone — and of the refactor that fixed it. The
per-module measurements, the survey of the 93 files added in those two days, and the list of issues
found but not yet fixed live in [../logs/recent-mathlib-homing.md](../logs/recent-mathlib-homing.md);
this note states the *problem*, the *criterion*, the *trade-offs* and the *standard* so the next
order does not repeat it.

**The guiding principle is the user's view: what is the most natural place for a user to *find*
(discovery: import path, module name) and to *use* (namespace, `#check`, `#find`) the library
content?** The rules in §3 are that question made operational; where a rule and the user's first
guess collide, the user's guess wins. The campaign's own records are
[deligneSerre/WORKORDER-MG3-ds-leaf-families.md](deligneSerre/WORKORDER-MG3-ds-leaf-families.md)
(phases 1–2), [deligneSerre/TOPIC-ds-leaf-families.md](deligneSerre/TOPIC-ds-leaf-families.md),
[logs/ds-leaf-families-wave1.md](../logs/ds-leaf-families-wave1.md),
[logs/ds-leaf-families-wave2.md](../logs/ds-leaf-families-wave2.md), and the free-group set's
[logs/qexp-and-freegroup.md](../logs/qexp-and-freegroup.md).

## 1. The symptom

Two modules made it visible:

* `Combinatorics/SimpleGraph/Transversal.lean` declared nine of its ten public names under
  `GroupTheory.GraphTransversal`;
* `LinearAlgebra/Matrix/SpecialLinearGroupFreeProduct.lean` and
  `...FreeGenerators.lean` declared almost everything under `ModularCurve.ModularGroupPingPong`,
  `BassSerreCuspSL2`, `ModularCurve.FreeTransport`, `ModularCurve.FreeModNegOne`.

The paths said one subject, the namespaces another. The general survey found the same class in
smaller doses:

* `LinearAlgebra/Matrix/SubfieldBasis.lean` — a representation-theory result in a matrix directory;
* the four `RepresentationTheory/*` modules and `Analysis/Fourier/PoissonSummationPi` — their
  public names under the pin `S_` file's wrapper namespace `P2MW.S_<stem>`;
* `RepresentationTheory/SubfieldBasis.lean` — its engine under the pin code namespace `P2mWs11Desc`.

These are the two independent axes. A module has a **path** (how you find a theory by import) and a
**namespace** (how you find a theorem by object). The campaign got each axis individually defensible
and the pair wrong.

## 2. How the original cut was made, and why

### 2.1 The order template

The leaf campaign was dispatched as one module per pin node, or per small family, with a rule that
reads naturally: *a mathlib-shaped supplement is homed at the mathlib path of the object in its
headline*. A `SimpleGraph` theorem went under `Combinatorics/SimpleGraph`; an `SL(2, ℤ)` theorem
under `LinearAlgebra/Matrix`; a `SchwartzMap` theorem under `Analysis/Fourier`; a representation
theorem under `RepresentationTheory`. That rule is how mathlib itself is laid out, and it is why the
campaign could be dispatched at all: the home of each node was read off its statement's head symbol.

The same orders said *transcribe the pin `S_` file*, which carries the pin's own file-local
namespace. The port copied that namespace verbatim — mechanically, because renaming adds a class of
error (references, `open`s, scoped instances) to a transcription whose value is exactly that it is
boring. The checker's dotted fallback also resolved the pin's names most directly that way. So the
namespace was chosen by *provenance* while the path was chosen by *object*.

### 2.2 Where the drift entered

The two choices were never compared. The pin's `S_` namespaces are proof-organization namespaces:
`GroupTheory.GraphTransversal` is where the pin parked a lemma for a group-theory proof;
`ModularCurve.ModularGroupPingPong` is where the pin's file happened to live; `P2MW.S_<stem>` is the
`S_` file's own wrapper; `P2mWs11Desc`, `P2MKc…`, `M4a…`, `Ef8d`, `RS40E` are the pin's generated
engine labels. None of them is a mathematical subject namespace, and none of them was reviewed
against the path.

The manager's later re-home of the free-group set (WORKORDER-FG1 §8) fixed the *lumping* — one
3,079-line engine became seven modules — but kept the object-path/pin-namespace split, so the two
symptoms above survived the first correction. That is the precise sense in which "the cut was
wrong": the module boundaries were fixed by subject, but the homes and names were not.

### 2.3 Why it was reasonable at the time

* The leaves had no consumers, so nothing broke; the cheapness of the re-home later is exactly the
  cheapness of having done nothing yet.
* The mathlib-mirroring rule is the right default for a *supplement*: it is how a missing mathlib
  theorem would be filed. The mistake is to read "mathlib-shaped" as "the headline's object is the
  subject".
* A pin namespace keeps the checker's dotted matching exact and makes the transcription mechanical.
  That is a real advantage — it is just an advantage of the *proof* layer, not of the *API*.

## 3. The criterion

Four rules, in order of precedence. They are the standard this note recommends for every
mathlib-shaped port.

1. **Home = the mathematical subject.** A module sits in the area of the mathematics it proves.
   A generic theory that needs no new theory from another area gets its **own** subject home, not
   the citer's. A theory that depends on a *new* theory from another area stays with that theory.
   Depending on a mathlib **library** (`SimpleGraph`, `Matrix`, `SchwartzMap`) is not such a
   dependency.
2. **Namespace = the object's namespace where mathlib has one** (`SimpleGraph`, `ModularGroup`,
   `Matrix.SpecialLinearGroup`, `Monoid.CoprodI`, `Representation`, `SchwartzMap`); otherwise FLT's
   name **if it already names the subject** (`GroupTheory.BassSerre`, `GroupTheory.FreeDoubleCoset`,
   `GroupTheory.Kurosh`). Prefer the aligned FLT name; do not rename merely because the path differs.
3. **A pin `P2MW.S_<stem>` wrapper, or a pin code name (`P2M…`, `M4a…`, `Ef8d`, …), is not a
   namespace** for public API. The wrapper is `S_`-file scaffolding and is removed at the module
   boundary. A pin engine name may stay only while mathlib has no name for the object and the path
   already names the subject; then a descriptive rename is scheduled (the residue in §7).
4. **A module named for its content is a user-facing API module, not a "façade".** The *façade*
   existed only to keep the frozen checker's listed delta small; `spec-pin:` + `check_port` make
   that unnecessary. But the **user's view** survives the checker argument: if a user looking for
   the content would naturally import a module named for it (the `SL₂` free-generation headlines),
   that module is the right home even though it only restates results proved in the engine. Split
   for discovery, not for the checker; merge only when the API has no separate natural name.

### 3.1 The genericity/dependency test, worked

* **`GroupTheory.GraphTransversal`** — seven of the nine prelude declarations mention
  `SimpleGraph`, `T.Adj`, `T.Walk` or `IsChain`; `IsConnectedTransversal` bundles
  `WalkConnected T D` with orbit conditions; only `eq_of_mem_orbit_sUnion` and
  `eq_of_mem_orbit_insert` are pure orbit lemmas, and they are proof-local. This is **graph
  theory**, not generic group theory: home `Combinatorics/SimpleGraph`, namespace
  `SimpleGraph.GraphTransversal`. The eleven `orbitRepr`/`transl` declarations the Kurosh engine
  carried were graph theory too and moved here.
* **Bass–Serre, ping-pong, Kurosh rank, SL₂ free generators** — generic group theory. The graph is a
  construction, not the subject; the dependence on mathlib's `SimpleGraph` is a library dependency.
  Home `GroupTheory/…`; namespaces `GroupTheory.BassSerre`, `GroupTheory.Kurosh`,
  `ModularGroup.PingPong`, `Matrix.SpecialLinearGroup.*` (the object).
* **`SubfieldBasis`** — a basis whose trace and determinant lie in a subfield: representation
  theory. Home `RepresentationTheory/`, namespace `Representation.*`.

## 4. The refactor

| module | before | after | namespace |
|---|---|---|---|
| graph transversal | `Combinatorics/SimpleGraph/Transversal.lean`, `GroupTheory.GraphTransversal` | same path | `SimpleGraph.GraphTransversal` |
| graph declarations in the engine | eleven `GroupTheory.GraphTransversal.*` in `KuroshRank` | moved into the graph module | `SimpleGraph.GraphTransversal` |
| double-coset count | `GroupTheory/FreeDoubleCoset.lean` | unchanged | `GroupTheory.FreeDoubleCoset` |
| coset graph | `GroupTheory/CoprodI/CosetGraph.lean`, `GroupTheory.BassSerre` | `GroupTheory/BassSerre/CosetGraph.lean` | `GroupTheory.BassSerre` |
| edge-chain engine | `GroupTheory/CoprodI/MinimalPeriod.lean`, `BassSerreCusp` | `GroupTheory/BassSerre/MinimalPeriod.lean` | `GroupTheory.BassSerre` (merged) |
| ping-pong | `LinearAlgebra/Matrix/SpecialLinearGroupFreeProduct.lean`, `ModularCurve.ModularGroupPingPong` | `GroupTheory/ModularGroup/FreeProduct.lean` | `ModularGroup.PingPong` |
| four SL₂ headlines | `LinearAlgebra/Matrix/SpecialLinearGroupFreeGenerators.lean`, `BassSerreCuspSL2`/`ModularCurve.*` | `GroupTheory/FreeGroup/SpecialLinearGroupGenerators.lean` (user-facing API over the Kurosh engine) | `Matrix.SpecialLinearGroup.*` |
| subfield basis | `LinearAlgebra/Matrix/SubfieldBasis.lean`, `P2MW.S_…` + `P2mWs11Desc` | `RepresentationTheory/SubfieldBasis.lean` | `Representation.*` + `Representation.SubfieldBasisAux` |
| four representation modules | `P2MW.S_…` wrapper | unchanged | `Representation.*` |
| Poisson summation | `P2MW.S_…` wrapper | unchanged | `PiPoissonSummation.*` + `SchwartzMap.*` |

The Poisson move needed one genuine proof fix: the headline's unqualified `toLp`/`ofLp` only
resolved inside the wrapper's namespace stack, so they are now spelled `WithLp.toLp` / `WithLp.ofLp`
(statements unchanged). The seven `own:` markers for the registered `LocSum` deviation were re-keyed
in `spec/decl_markers.tsv`.

## 5. Rationale: pro and con

**Pro.**

* **Discoverability on both axes** — the import path now names the theory and the namespace names
  the object. A consumer looking for Bass–Serre material imports `GroupTheory/…`; a user looking for
  `SL(2, ℤ)` results finds `Matrix.SpecialLinearGroup.*`.
* **Cohesion** — one theory per directory; a module no longer mixes a citer's engine with another
  area's object.
* **Dependencies go down or stay even** — measured over the tree, baseline `8cd8e96` was 841 modules
  / 1,954 import edges / 439 cross-area edges; after the pass 841 / 1,953 / 436. That was the
  acceptance condition for the refactor, and it held.
* **No verification cost** — the checker matches by last name and normalised statement, so every
  rename kept `0 mismatch / 0 missing`; the checked surface stayed at 3,506 over 129 modules.
* **Cheap now, expensive later** — the leaves had no consumers; doing it after the first consumer
  would mean updating proof scripts and importers across the port.
* **The user's first guess is the test** — after the pass, a group theorist looking for Bass–Serre
  imports `GroupTheory/…`; an `SL₂(ℤ)` user imports `SpecialLinearGroupGenerators`; a graph user
  imports `Combinatorics/SimpleGraph`; a representation user imports `RepresentationTheory/…`. None
  of them has to know the pin's `S_` file layout.

**Con.**

* **Churn** — paths moved, several hundred declarations changed namespace, and the orders, records and notes
  had to be updated in the same pass (the WORKORDER-FG1 §3/§8 tables, the FG1 record, the column and
  leaf-families notes). A rename that lands without its records is worse than no rename.
* **Proof-script risk** — `open`/`open scoped`/`attribute` and scoped-instance activation are keyed
  by namespace. Relative opens inside a renamed namespace survive; absolute ones do not. The
  free-product module's `open ModularCurve.ModularGroupPingPong (mem_center_iff_eq)` had to change;
  the scoped `IrrationalPt` coercion survives because the `open` is relative.
* **Markers and search** — `decl_markers.tsv` is keyed by `(module, full name)`; a rename orphans
  the entries (the Poisson ones needed re-keying). The pin's names are no longer searchable; the
  record must say where a pin name went.
* **One more module, one more import edge** — a user-facing API module over an engine costs a module
  and an edge (the `SL₂` API imports the Kurosh engine). That is the price of the user's natural
  import; it is paid deliberately, and it is why the dependency metric is a *sign* (the re-home is
  even against the baseline, three cross-area edges down) and not the principle.
* **Judgment calls** — the graph transversal could be argued either way; the note fixes the test
  (does the declaration mention the graph, and is the group action generic?) rather than the outcome.

## 6. Verification and acceptance

A re-home is accepted when:

1. **Dependencies do not go up**: measure modules / internal import edges / cross-area edges before
   and after (a one-off script over `import FLTForHuman.*` is enough; `tools/deps/port_graph.py`
   gives the declaration-level view). Down or even is the target.
2. **Every touched module builds** (`flock /tmp/flt.lake.lock timeout 90 lake build …`), 0 warnings.
3. **`check_port --force` is 0 mismatch / 0 missing** for each touched module (expected same `ok`
   count as before — the checker is name-insensitive), and `check_port --all` at the end.
4. **Markers are current** — run with `--strict-markers`, re-key any entry for a renamed
   declaration.
5. **No stale reference remains** — `rg` the old paths, namespaces and module names in
   `FLTForHuman/`, `topics/`, `logs/`.
6. **Records and orders carry the new homes** in the same change.

Measured for this pass: graph 21, FreeDoubleCoset 12, CosetGraph 49, MinimalPeriod 75,
FreeProduct 68, KuroshRank 104, SpecialLinearGroupGenerators 52, QExpansionCoeff 19, SubfieldBasis
17, representations 1 × 4, Poisson 31 + 7 own; global `check_port --all` **3506 ok, 0 mismatch, 0
missing, 11 own, 0 kw over 130 modules**; dependency metric **842 modules / 1,955 edges / 436
cross-area** — the one added module and edge are `ModularForms/HeckeFrickeTrace.lean`, so the
re-home itself is even on edges and three cross-area edges down.

## 7. Residual issues for the two-day leaf campaign

The survey and the not-yet-fixed list are in
[../logs/recent-mathlib-homing.md](../logs/recent-mathlib-homing.md). In summary:

* **Pin code namespaces — 31 files; the two in the modules this pass touched are fixed**
  (`RepresentationTheory/SubfieldBasis.lean`'s `P2mWs11Desc`, and
  `Analysis/Fourier/PoissonSummationPi.lean`'s `P2MW.S_…` wrapper). Of the remaining 29, twenty-two
  are in other 2026-10-19/20 modules (`P2MKcIgusaGroup`, `P2MKcOrbitCensus`,
  `P2MKcMarksA4`, `P2MKcCB`/`P2MKcADAPT`, `M4aP3B.Rows`, `Ws50CH3`, `A2HexPoisson`, `IBPLattice`,
  `AdjoinExt`, `TrDesc`/`TrFrob`/`TrFinal`, `Ef8d`, `RS40E`/`PPSeries43`, `K2Seam3`, `M4aP1R`,
  `ChevalleyHom`, `CardC0`, `SolIntClosDVR`, `EngineCoreSol`/`RankOneNilSol`, `WittLift`); seven are
  older (`M4aS4` in `NumberTheory/AdelicHaar/{AdelicModulus,PlaceMeasure}`, `M4aLocalCFT` in
  `FujisakiCompact`, `M4aHerbrand` in `IdeleClass/{Vocab,ArchSemilocal}`, `P2MKcSerreTate` in
  `InertiaReduction`, `P2MKcCQJvc`/`P2MKcCQJbc` in `CyclicQuotientJ`). The names are the pin
  `S_` files' generated labels; the paths already are their subjects, so this is a **descriptive
  rename campaign**, not a homing defect. It needs a rename map, a per-module `check_port` run and
  the records — a separate, schedulable piece of work.
* **Fixed in this pass and worth knowing**: the `P2MW` wrappers of the four representation modules
  and `SubfieldBasis`; `P2mWs11Desc` → `Representation.SubfieldBasisAux`; the Poisson wrapper
  (with the `WithLp` proof qualification and the seven re-keyed markers).
* **Tooling**: FR-0028 (the corpus's `end A.B` namespace tracker) is fixed by the parser extraction
  in `spec/lean_parser.py` (FR-0035); the corpus was rebuilt and `check_port --all` re-verified.
* **Where the campaign's other classes stand**: "path right, namespace = pin engine name" is the
  residue above; "path and namespace both right" needs nothing; the "path wrong" cases were the
  three fixed here (`SpecialLinearGroupFreeProduct`, `SpecialLinearGroupFreeGenerators`,
  `SubfieldBasis`) — no other path/namespace mismatch was found in the 93 files.

## 8. Process lessons

* **Write the homing decision into the order**, not into the agent's taste: "home by subject;
  namespace by object; never expose the pin wrapper" is one line and prevents the whole class.
* **"Mathlib-shaped" is about the statement's subject, not the object's namespace.** A theorem about
  a matrix group can be group theory; a theorem about a graph can be group theory; a theorem about
  a representation is representation theory.
* **Do the re-home before the first consumer.** Leaves are cheap; after a landing the cost moves to
  proof scripts and importers.
* **Path and namespace are independent axes; both must be right.** Renaming a namespace does not fix
  a wrong home, and moving a file does not fix a wrong namespace.
* **The checker is name-insensitive; the rest of the tree is not.** Renames are safe for
  verification, but they are not free: `open`s, scoped instances, markers and records must move with
  them.
* **Measure the dependency graph** — a cut that increases import edges is a cut to reconsider; a cut
  that lowers them is the one to keep.
* **Ask where the user would look, then check the graph.** The user-view question decides the home
  and the module name; the dependency metric is the sanity check on the answer, not the criterion.
  A user-facing API module can add an edge and still be right — as the `SL₂` API module does.
