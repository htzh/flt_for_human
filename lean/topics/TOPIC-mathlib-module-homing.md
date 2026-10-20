# The homing of mathlib-shaped modules — how the cut was made, why it was wrong, the standard, and the rehoming pass

**Status: both passes are done (2026-10-20).** This note is the durable record of the homing
problem that surfaced in the 2026-10-19/20 leaf-node campaign — porting small families of the D-S
cone — of the refactor that fixed it (§4–§6), and of the rehoming pass that finished the residue
(§8). It states the *problem*, the *criterion*, the *trade-offs* and the *standard* so the next
order does not repeat it. The per-module measurements of the 93 files added in those two days, and
the survey that produced the list rehomed in §8, are in
[../logs/recent-mathlib-homing.md](../logs/recent-mathlib-homing.md).

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
   already names the subject; then a descriptive rename is scheduled (the residue in §7, landed in §8).
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

* **Pin code namespaces — the 2026-10-19/20 supplements are clean (landed in §8).** The two
  modules this first pass touched were fixed here (`RepresentationTheory/SubfieldBasis.lean`'s
  `P2mWs11Desc`, `Analysis/Fourier/PoissonSummationPi.lean`'s `P2MW.S_…` wrapper); the twenty-two
  that remained in the window's other supplements were re-homed in §8 (302 declarations out of
  labels such as `P2MKcIgusaGroup`, `M4aP3B.Rows`, `TrFrob`, `Ef8d`, `IBPLattice`, `AdjoinExt`,
  `CardC0`, `SolIntClosDVR`, `WittLift`). What remains is **out of this line of work**: the
  FLT-domain modules of the window (`HeckeCharacter/Equality`,
  `ModularForms/CohCarrier/TorsionOrbit`, …) and the seven older namespaces (`M4aS4` in
  `NumberTheory/AdelicHaar/{AdelicModulus,PlaceMeasure}`, `M4aLocalCFT` in `FujisakiCompact`,
  `M4aHerbrand` in `IdeleClass/{Vocab,ArchSemilocal}`, `P2MKcSerreTate` in `InertiaReduction`,
  `P2MKcCQJvc`/`P2MKcCQJbc` in `CyclicQuotientJ`). Those are FLT mathematics, not supplements, and
  their rename is a separate campaign.
* **Fixed in this pass and worth knowing**: the `P2MW` wrappers of the four representation modules
  and `SubfieldBasis`; `P2mWs11Desc` → `Representation.SubfieldBasisAux`; the Poisson wrapper
  (with the `WithLp` proof qualification and the seven re-keyed markers).
* **Tooling**: FR-0028 (the corpus's `end A.B` namespace tracker) is fixed by the parser extraction
  in `spec/lean_parser.py` (FR-0035); the corpus was rebuilt and `check_port --all` re-verified.
* **Where the campaign's other classes stand**: "path right, namespace = pin engine name" was the
  residue above, re-homed for the supplements in §8; "path and namespace both right" needed
  nothing; the "path wrong" cases were the three fixed here (`SpecialLinearGroupFreeProduct`,
  `SpecialLinearGroupFreeGenerators`, `SubfieldBasis`) plus the supplements moved in §8 — no other
  path/namespace mismatch was found in the 93 files.

## 8. The rehoming pass (2026-10-20)

This pass was written as a separate plan file, executed in five waves, and merged back into this
note when the waves closed; it is a record, not a live plan (the status table is §8.8). The standard
it applies is §3; the survey that produced it is
[../logs/recent-mathlib-homing.md](../logs/recent-mathlib-homing.md), and the numbers below are the
ones that were measured, not estimates.

### 8.1 Scope, measured

A **supplement** is pin material that is not FLT mathematics: its statement names only mathlib
objects and it would live in mathlib if mathlib had it (supplements note §1). This pass covers
only supplements, and only the ones ported in the two-day window: **45 modules, 15,705 lines, 834
public declarations** (50 private). `Algebra/AddAutCompat` (now `Algebra/AddAut/Compat.lean`) is the one non-supplement kept in
scope: it is a mathlib-version compat shim, but it sits with the supplements and shares their
homing problem (§8.2 E). Within those 45 modules:

* **23 modules / 359 declarations** sit under a pin-inner namespace: **302** in 21 modules
  bear a label that must go (a generated label such as `P2MKc…`, `M4a…`, `Ef8d`, or a pin label that
  names no subject), and **57** in 2 modules bear a pin name that *does* name its subject and has no
  mathlib counterpart (`ChevalleyHom` 25, `A2HexPoisson` 32): those two are compliant and stay;
* **9 modules** have consumers (11 import edges); the other 36 are leaves, so the re-home is cheap
  now and expensive after the first consumer (homing note §5);
* the previous pass already fixed twelve modules and `PoissonSummationPi`; they are the template
  and are not repeated here (homing note §4, log §3).

**The standing rule: any file this pass touches is namespace-rectified in the same change.** A
path move never lands with its old namespace, and a file is not left pin-labelled because its path
happens to be right; every namespace the file declares is audited against the standard (§8.5 step 1)
and the labels are renamed or folded in that edit. The pin namespace each new name came from is
recorded in the module header, so a pin name stays searchable. The one exception is an
out-of-scope module touched only to retarget an import line: its own namespaces belong to the
parallel campaign, and are recorded there, not fixed here.

**Baseline, measured 2026-10-20** (corpus stamp `aa2d8b3`, `check_port --force` on all 46 —
the 45 above plus `PoissonSummationPi`): **872 public declarations, 865 `ok` + 7 `own`, 0
mismatched, 0 missing, 0 kw**; the 7 `own` are `PoissonSummationPi`'s registered `LocSum` deviation.
Every in-scope module is clean today, and its `ok` count equals its public surface, so the pass's
gates were measurable per module (per-wave counts in §8.4).

**Out of scope (25 files).** The FLT-domain ports of the same window are not supplements and keep
their present homes and namespaces: `AlgebraicCurve/*` (3), `Elliptic/PeriodPair/*` (1),
`GaloisRep/Deformation/*` (3), `HeckeCharacter/*` (2), `LanglandsTunnell/*` (1), `ModularCurve/*` (3),
`ModularForms/*` (7), `NumberTheory/{ModularForms,RatAdele,RatIdele}/*` (4),
`RepTheory/LocalLanglands/*` (1). Their own pin-code namespaces (`P2MKcLEVEL`, `P2MKcXHCount`,
`EIS2K1`, `WPGamma1`, `P2mS26B6b`, `ANb`, `PsiSol`, `JTPEngine`, `LocalGL2`, …) are the parallel
descriptive-rename campaign, not a homing defect; do not fold them into this pass. The same goes
for the seven older pin-code namespaces in the record (`M4aS4` in `AdelicHaar/*`, `M4aLocalCFT`,
`M4aHerbrand`, `P2MKcSerreTate`, `P2MKcCQJvc`/`P2MKcCQJbc`): those modules are FLT-domain.

**No statement changes; no mathematics touched.** A supplement's statements are the pin's, and the
checker is name-insensitive (playbook §4): a namespace or file rename keeps `0 mismatched / 0
missing`. The only proof text the pass edits is the `solution`/`gate` scaffolding taken `private`
(§8.3 F, where inlining `exact main` is mechanical) and the lemmas §8.2 D moves to a library home. The
only intended checker delta is that privating, a smaller `ok` count by exactly the number privated.

### 8.2 The issues, measured

* **A. Namespace is a pin artifact.** 302 declarations in 21 modules under the pin `S_` file's own
  namespace. The pin's namespaces are proof-organization labels (`P2MKcIgusaGroup`,
  `M4aP3B.Rows.UniformSeminorm`, `TrFrob`, `BrauerNesbitt`), not subject namespaces; a user cannot
  guess one. Two pin-inner names pass the standard and stay (§8.1): `ChevalleyHom` and
  `A2HexPoisson` each name their subject and mathlib has no object for them.
* **B. Path is a bare area or the wrong area.** 20 modules: nine sit under a bare `Algebra/`
  (five of them with no subject directory at all), five directly under `Analysis/`, four at
  `RingTheory/` without their subject directory, one is filed under `NumberTheory/` though it is
  valuation theory, and one is a directory split (`Fourier/PoissonSummation/`) that is cosmetic.
* **C. Mixed-subject modules.** `Algebra/TorsionFinite` (a `Submodule.torsionBy` fact and a
  `ValuationRing` fact), `Analysis/DecayEstimates` (a seminorm bound and a model integral),
  `Analysis/Complex/LogBranchAndPrimitiveRoot` (a log branch and a primitive-root ring hom),
  `RingTheory/LocalRingNilpotent` (a Krull-dimension divisibility fact and an idempotent lift).
  Each is one module for two subjects, which is not a role (playbook §3.1).
* **D. One dependency inversion.** `GroupTheory/ModularGroup/FreeProduct` imports
  `FLTForHuman.ModularForms.Analytic.PeterssonCoset` for `det_entries` (a five-line
  determinant computation) and the `mapGL` entry lemmas: a general group-theory module depending
  on a modular-forms module. A library supplement may be imported by FLT-domain modules, never the
  reverse (playbook §3.2). The four lemmas are general `SL(2, ℤ)`/`mapGL` facts with no home of
  their own, so the fix is a library module — `LinearAlgebra/Matrix/SpecialLinearGroupMapGL.lean`
  holding `mapGL_apply`, `val_mapGL_eq`, `mapGL_injective` and `det_entries` — which both
  `PeterssonCoset` and `FreeProduct` import; check first whether `det_entries` is mathlib's
  `SpecialLinearGroup.det_coe` with `Matrix.det_fin_two`, in which case it is dropped, not moved.
* **E. A compat shim filed as subject content.** `Algebra/AddAutCompat` restores a mathlib-4.30
  instance that 4.33 removed; it is version glue, not a supplement, and should not occupy an
  `Algebra/` slot as if it were content.
* **F. Pin `solution` scaffolding in the public API.** Nine `*.main` declarations are the pin's
  `solution` wrapper (two are byte-identical to the headline that now states the same theorem),
  and seven `*_impl` / `*_proved` / `gate_*` declarations are the pin's case-split machinery; four
  more are `*_aux`. They are proofs, not statements, and no consumer imports them.
* **G. Name hygiene.** Four declarations carry a redundant `_root_.` escape inside the namespace
  they escape to (`BrauerNesbittRepresentation` ×2, `KuroshRank` ×1, `SimultaneousEigenbasis` ×1).
  The corpus's `parse_file` records these as `Namespace._root_.Namespace.x`, not `Namespace.x`, so
  a marker keyed on the full name cannot be written correctly — fix the parser first (§8.7).

### 8.3 The targets, and what landed

Path rule, following the homing note §3 and the supplements note's "proposed home" convention:
**home is the mathematical subject; where mathlib files that subject, mirror mathlib's directory
(a file for a single addendum, a directory when mathlib has one).** Namespace rule: **the object's
mathlib namespace where mathlib has one; otherwise FLT's name if it already names the subject; a
pin-inner descriptive name may stay, a generated label may not.** Where the object's namespace is
mathlib's, the declaration's *last name* is unchanged unless it is pin scaffolding.

The exact final spelling of every declaration was the executor's, under a collision check (§8.5);
the tables below fix the home and the namespace family, and record the landing (§8.11).

#### Algebra

| module (before) | path after | namespace after | class |
|---|---|---|---|
| `Algebra/AddAutCompat` | `Algebra/AddAut/Compat.lean` | `AddAut` (keep) | E |
| `Algebra/AddAutTransvectionFrame` | `Algebra/AddAut/TransvectionFrame.lean` | `AddAut` + `AddAut.Frame` | A |
| `Algebra/BrauerNesbittRepresentation` | `RepresentationTheory/BrauerNesbitt.lean` | `Module.End` (keep), `Representation` (headline), `BrauerNesbitt` (keep: it names the theorem) | A, B |
| `Algebra/FunctionOrbitCensus` | `GroupTheory/GroupAction/OrbitCensus.lean` | `Function.OrbitCensus` | A, B |
| `Algebra/FunctionSeparation` | keep | `Function` (+ the descriptive `SepFinAux` / `FactorAux`) | — |
| `Algebra/IsAddCyclicSquarefree` | `GroupTheory/SpecificGroups/CyclicSquarefree.lean` | `IsAddCyclic` (keep) | B |
| `Algebra/LaurentSeriesAlgebraic` | `RingTheory/LaurentSeriesAlgebraic.lean` | `LaurentSeries` (`AlgClosedPort` dropped) | A, B |
| `Algebra/MulActionOrbitCounts` | `GroupTheory/GroupAction/OrbitCounts.lean` | `MulAction` (headline) + `GroupTheory.MarksTwelve` | A, B |
| `Algebra/TorsionByCoordinates` | `Algebra/Module/Torsion/Coordinates.lean` | `Submodule.TorsionBy` family | A, B |
| `Algebra/TorsionFinite` | split: `Algebra/Module/Torsion/Finite.lean` + `RingTheory/Valuation/FiniteModule.lean` | `Submodule` / `ValuationRing` (keep) | C |

#### Analysis

| module (before) | path after | namespace after | class |
|---|---|---|---|
| `Analysis/CompactOperatorFiniteDimensional` | `Analysis/Normed/Operator/CompactFiniteDimensional.lean` | `Submodule` / `LinearMap` (keep) | B |
| `Analysis/Complex/LogBranchAndPrimitiveRoot` | keep (not split; §8.11) | `Complex` for both headlines; the two `main`s private | A, C |
| `Analysis/DecayEstimates` | split: `Analysis/SpecialFunctions/Pow/Decay.lean` + `Analysis/Calculus/SeminormBound.lean` | root (matching the two headlines) | A, B, C |
| `Analysis/Fourier/PoissonSummationPi` | done (template) | `PiPoissonSummation` / `SchwartzMap` | — |
| `Analysis/Fourier/PoissonSummationZLattice` | keep (the `PoissonSummation/` split was dropped, §8.11) | `ZLattice` (keep) | — |
| `Analysis/FourierIntegralFlip` | `Analysis/Fourier/VectorIntegralFlip.lean` | `VectorFourier` / `SchwartzMap` / `AddChar`; `PiFourier` folded into `VectorFourier` | A, B |
| `Analysis/FundamentalDomainIntegration` | `Analysis/Fourier/FundamentalDomainIntegration.lean` | `ZSpan` | A, B |
| `Analysis/StarSubalgebraIntegral` | `Topology/ContinuousMap/StarSubalgebraIntegral.lean` | `ContinuousMap` (keep) | B |
| `Analysis/Theta/HexagonalLattice` | keep | `A2HexPoisson` stays (names the subject; no mathlib counterpart) | — |

#### FieldTheory, LinearAlgebra

| module (before) | path after | namespace after | class |
|---|---|---|---|
| `FieldTheory/AdjoinExtension` | keep | `IntermediateField` (headline) + `IntermediateField.AdjoinExtension` (`AdjoinExt` dropped); `SolChiFinField.isIntegral_apply` private | A |
| `FieldTheory/TranscendentalAdjoin` | keep | `Polynomial` / `Subalgebra` (keep) | — |
| `LinearAlgebra/FinrankStableInequality` | keep | `FinrankStable` (root subject namespace; `Ef8d` dropped) | A |
| `LinearAlgebra/Matrix/SimultaneousEigenbasis` | keep | `Matrix` (`TrFrob` / `TrDesc` / `TrFinal` dropped) | A, G |

#### GroupTheory, Combinatorics

| module (before) | path after | namespace after | class |
|---|---|---|---|
| `Combinatorics/SimpleGraph/Transversal` | done | `SimpleGraph.GraphTransversal` | — |
| `GroupTheory/BassSerre/{CosetGraph,MinimalPeriod}` | done | `GroupTheory.BassSerre` | — |
| `GroupTheory/ExactFundamentalDomain` | keep | `Subgroup` (keep; helpers already private) | — |
| `GroupTheory/FreeDoubleCoset` | keep | `GroupTheory.FreeDoubleCoset` (keep) | — |
| `GroupTheory/FreeGroup/KuroshRank` | keep | `GroupTheory.{BassSerre,Kurosh,FreeActionTree}` (keep) | G |
| `GroupTheory/FreeGroup/SpecialLinearGroupGenerators` | keep | `Matrix.SpecialLinearGroup` (keep) | — |
| `GroupTheory/ModularGroup/FreeProduct` | keep | `ModularGroup.PingPong` (keep); the dependency is broken by a private local `det_entries` (§8.11) | D |

`SpecialLinearGroupGenerators` is the deliberate user-facing API module of homing note §3 rule 4:
it is named for its content so a user imports it, and it restates the engine's headlines. Keep it
and keep the reason in its header.

#### NumberTheory, RingTheory, Topology

| module (before) | path after | namespace after | class |
|---|---|---|---|
| `NumberTheory/LSeries/AnalyticContinuation` | keep | `LSeries` (`RS40E` / `PPSeries43` dropped) | A |
| `NumberTheory/SquarefreeValues` | keep | `Nat` / `Int` (headlines) + descriptive aux | A |
| `NumberTheory/UnimodularLift` | keep | `Int` (headline) + `UnimodularLift` (root, the pin's descriptive name) | A |
| `NumberTheory/ValuationSubring/ChevalleyExtension` | `RingTheory/Valuation/ChevalleyExtension.lean` | `ChevalleyHom` / `ChevalleyHom.IsGraph` stay (they name the construction); `ValuationSubring` / `IsAlgClosed` headlines stay | B |
| `NumberTheory/ZModPowerTsum` | keep | `ZMod` (`CardC0` dropped) | A |
| `RingTheory/DedekindDomain/ClassGroupSupport` | `RingTheory/ClassGroup/Support.lean` | `ClassGroup` (keep) | B |
| `RingTheory/IntegralClosureCompleteDVR` | `RingTheory/IntegralClosure/CompleteDVR.lean` | `integralClosure` | A, B |
| `RingTheory/LocalRingNilpotent` | split: `RingTheory/LocalRing/DimensionOne.lean` + `.../IdempotentLift.lean` | `IsLocalRing` | A, B, C |
| `RingTheory/WittVectorLift` | `RingTheory/WittVector/Lift.lean` | `WittVector` | A, B |
| `Topology/Algebra/LocallyConstantCompactSupport` | keep | `IsLocallyConstant` (`M4aP3B.Rows.*` dropped; `_impl` / `gate_*` private) | A |

#### RepresentationTheory

| module (before) | path after | namespace after | class |
|---|---|---|---|
| `RepresentationTheory/{Burnside,CompactGroup,InvariantPairing,SubfieldBasis,SubrepresentationExtension}` | keep | `Representation.*` (including the descriptive `Representation.SubfieldBasisAux`) | — |

The `—` rows need no action. A file on one of them that a wave *does* touch (an import retarget, a
consumer fix) is audited like any other (§8.1, §8.5 step 1); a file nobody touches is left alone.

### 8.4 Waves

One pass per module: path move **and** namespace rename **and** the `main`/`_impl` hygiene in the
same edit, so a module is never touched twice (playbook §3.5 rule 2). Within a wave: leaves first,
modules with consumers last (their importers are updated in the same wave). One wave is one
session-let; it needs no whole-tree build.

| wave | modules | lines | baseline `ok` | structural items |
|---|---:|---:|---:|---|
| W1 Algebra | 10 | 3,763 | 168 | AddAut pair re-home; BrauerNesbitt → RepresentationTheory; Torsion pair split |
| W2 Analysis | 9 | 2,864 | 98 + 7 `own` | DecayEstimates split; `PoissonSummation/` directory; `PiFourier` |
| W3 NumberTheory + RingTheory + Topology | 10 | 2,688 | 97 | valuation/class-group/integral-closure/Witt re-homes |
| W4 FieldTheory + LinearAlgebra + RepresentationTheory | 9 | 2,954 | 120 | `AdjoinExt`, `Ef8d`, `Tr*` |
| W5 GroupTheory + Combinatorics | 8 + 1 new | 4,051 | 382 + 4 moved | dependency inversion (D); `_root_` escapes |
| W6 | — | — | 872 total | global check, records, the status table in §8.8 |

The per-module baseline `ok` counts (2026-10-20), in the order the §8.3 tables list each wave, to
check a wave against: W1 = 17/40/3/25/6/1/3/30/41/2; W2 = 2/4/8/31 (+7 `own`)/2/9/9/1/32;
W3 = 12/9/5/28/7/1/10/8/9/8; W4 = 14/3/19/63 then `RepresentationTheory` 1/1/1/17/1;
W5 = 21/49/75/1/12/104/52/68.

W1–W4 change consumers only through import lines: `FiniteDescent` (out of scope) imports
`BrauerNesbittRepresentation`, `RepresentationTheory/Burnside` (W4, in scope) imports it too, and
`ConstTermCubeIntegral` (out of scope) imports `ZModPowerTsum`; each is a one-line import edit in the
wave that moves the module, and a touched in-scope consumer is namespace-audited (§8.1). W5 is last
because its modules are the ones other modules import.

### 8.5 Per-module protocol

1. **Audit every namespace, then map.** From the module source, list every `namespace` it declares
   with its public and private declaration counts, and classify each against the standard: the
   object's mathlib namespace, an FLT name that names the subject, or a pin label that must go
   (§8.1). Rewrite the labels, including a private-only helper namespace, then write the
   `old FQN -> new FQN` map from `spec/check_port.py --json <module>`; keep the last name except
   for the §8.3 F scaffolding. Record the pin namespace each new name came from in the module header
   (the pin's names must stay searchable).
2. **Collision check, in both trees.** For every target FQN:
   `rg -n '^\s*(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+<last name>\b'`
   over `Mathlib/` and over `FLTForHuman/`. A duplicate is a *silent* merge in Lean, not an error;
   on a hit use a descriptive aux sub-namespace (`MulAction.MarksTwelve`,
   `Representation.BrauerNesbitt`, `Submodule.TorsionByCoords`) rather than reusing the object's
   namespace wholesale.
3. **Move and rename.** `mv` the file (git detects the rename; the lakefile globs, so no build-file
   change), rewrite `namespace`/`end` lines and the `open`/`open scoped` that name the old
   namespace, and update importers. Do not touch `spec-pin:` lines: the pin files did not move.
4. **Hygiene.** `main` → `private` (or inline it and delete it when the headline's proof is
   `exact main`); `_impl` / `_proved` / `gate_*` → `private` unless the declaration is genuinely
   more general than its headline, in which case promote it with a descriptive name and state the
   headline as its corollary. Drop the redundant `_root_.` escapes.
5. **Build.** `flock /tmp/flt.lake.lock timeout 120 lake build <module>`, 0 warnings; importers
   build once, at the end of the wave.
6. **Check.** `python3 spec/check_port.py --force <module>` → `0 mismatch / 0 missing` and the
   expected `ok` count (unchanged, minus privated scaffolding). `--strict-markers` clean. No
   `decl_markers.tsv` entry names a re-homed declaration today, so there is nothing to re-key; if
   one appears, re-key it in the same edit. Measured on 2026-10-20 on throwaway copies: renaming
   `MulActionOrbitCounts`'s `P2MKcMarksA4` to `MarksTwelve` re-checks `30 ok / 0 / 0`, the
   namespace audit's worst case; making `AddAutTransvectionFrame.main` `private` takes 40 → 39
   `ok / 0 / 0`. Both are the expected signals, so a wave's `ok` delta is a check, not a hope.
7. **Sweep and record.** `rg` the old paths, namespaces and module names in `FLTForHuman/`,
   `topics/`, `logs/`; update the module header's "kept verbatim" sentence, the status table in
   §8.8, and [../logs/recent-mathlib-homing.md](../logs/recent-mathlib-homing.md).

### 8.6 Acceptance

A wave is accepted when

1. every touched module and every importer builds with 0 warnings;
2. `check_port --force` is `0 mismatch / 0 missing` per module, and the `ok` delta is exactly the
   number of declarations privated, against the per-wave counts in §8.4;
3. `check_port --all` at the end of the pass matches the two baselines: the 46 modules here at
   **872 verdicts (865 `ok` + 7 `own`), 0 / 0** minus the privated scaffolding, and the whole wired
   tree at the record's `3,506 ok / 0 mismatched / 0 missing / 11 own / 0 kw` over 130 modules
   (corpus stamp `aa2d8b3`; rebuild with `python3 spec/statement_db.py build` if it moves). W5's new
   `MapGL` module makes the wired count 131 and moves four `ok` from `PeterssonCoset` to it, so the
   global `ok` is unchanged;
4. the dependency metric does not go up: modules / internal edges / cross-area edges before and
   after (the graph in the record is the baseline; `tools/deps/port_graph.py` gives the
   declaration-level view), and **no library module imports an FLT-domain module** (`rg` the
   import block of every supplement for `FLTForHuman.{ModularForms,ModularCurve,GaloisRep,Elliptic,…}`);
5. `rg` finds no old path or namespace outside the records that describe the migration, and **no
   pin label survives in a touched file**:
   `rg -n '^(namespace|end)\s+(P2M|M4a|Ws50|Ef8d|RS40E|PPSeries43|K2Seam3|CardC0|SolIntClosDVR|EngineCoreSol|RankOneNilSol|WittLift|IBPLattice|AdjoinExt|TrDesc|TrFrob|TrFinal|PiFourier|SolChiFinField|AlgClosedPort)'`;
6. the records carry the new homes (module headers, the log, the status table in §8.8).

### 8.7 Prerequisite: the `_root_` name in the corpus

`spec/statement_db.parse_file` returns `Namespace._root_.Namespace.x` for a declaration written
`theorem _root_.Namespace.x` inside `namespace Namespace`, whose real name is `Namespace.x`
(reproduced 2026-10-20 on a synthetic file). The last name and the promoted key are right, so
matching is unaffected, but a full-name marker key cannot be written. Fix it where the enclosing
namespace is prefixed (`lean_parser`), with `python3 spec/statement_db.py selftest` as the guard,
before any marker is added on such a declaration. The four current instances are in §8.3 G.

### 8.8 Status

| wave | modules | baseline `ok` | landed `ok` | status |
|---|---:|---:|---:|---|
| W1 Algebra | 10 (11 files after the split) | 168 | 165 | landed 2026-10-20 |
| W2 Analysis | 9 (10 files after the split) | 98 + 7 `own` | 92 + 7 `own` | landed 2026-10-20 |
| W3 NumberTheory + RingTheory + Topology | 10 (11 files after the splits) | 97 | 88 | landed 2026-10-20 |
| W4 FieldTheory + LinearAlgebra + RepresentationTheory | 9 | 120 | 118 | landed 2026-10-20 |
| W5 GroupTheory + Combinatorics | 8 | 382 | 382 | landed 2026-10-20 |
| W6 global check + records | — | 872 | 845 + 7 `own` | landed 2026-10-20 |

The `ok` deltas are exactly the privated scaffolding and the one deduplicated lemma (§8.11).

### 8.9 Cost and risk

The measured content is 15.7k lines / 834 public declarations, but the work is not proportional to
them: the renames are mechanical (namespace lines, `open`s, importers) and the builds are
per-module seconds. The cost is the collision checks (302 renamed FQNs, two trees) and the records.
Estimate: one session-let per wave, W1 and W5 the largest because of the splits and the dependency
inversion.

Risks, in the order they bite:

* **A silent collision.** Lean merges two declarations of one name silently, so a re-home into
  `Matrix.*`, `Submodule.*`, `Int.*`, `ZMod.*`, `Complex.*` or `IsLocalRing.*` can shadow a mathlib
  lemma; the build stays green and the statement diff still passes. Hence step 2 of §8.5 is not
  optional, and a hit is resolved by an aux sub-namespace.
* **A proof script keyed on the old namespace.** Absolute `open`s, `open scoped` and attribute
  targets do not survive a rename; relative `open`s do. Build each module at tier 0 before moving
  on.
* **Records going stale.** Every module header states "the pin's inner namespace `X` is kept
  verbatim"; after the pass that sentence is false. The header must name the pin namespace and the
  new home, or a later reader cannot map a pin name to the port.
* **Partial waves.** A moved file whose importers are not updated leaves the tree red; the wave is
  one change, importers included.
* **Scope creep.** Visibility, dedup against mathlib, and upstreaming are not homing; leave them
  to their own passes (supplements note §2, playbook §2.4).

### 8.10 What this pass does not do

* No statement, proof, or `spec-pin:` change; no mathematics is re-derived.
* No re-home of an FLT-domain module (the 25-file list in §8.1), and no cleanup of their pin-code
  namespaces.
* No dedup against mathlib and no upstreaming; no `Reserve/` moves.
* No whole-tree build except the single end-of-pass verification of §8.6 item 3, which needs the
  user's agreement (playbook §3.5 rule 5).

### 8.11 What landed

All five waves landed in one session-let. **845 `ok` + 7 `own`, 0 mismatch / 0 missing / 0 kw**
across the 49 files that now carry the 45 modules (three modules were split), against the 872
measured before: the 20-verdict delta is exactly the privated scaffolding (19 declarations) and
one deduplicated lemma; no statement, proof route or `spec-pin:` line changed. Whole wired tree:
**3,486 ok / 0 mismatch / 0 missing / 11 own / 0 kw over 133 modules** (was 3,506 over 130; the three
new modules are the splits). Dependency metric: **845 modules / 1,954 internal edges / 434
cross-area** (was 842 / 1,955 / 436) — edges and cross-area edges down, the three added modules
being the splits. No supplement imports an FLT-domain module any more.

**Where the landing differs from the table, and why.**

* **`BrauerNesbitt` keeps its namespace** (root, not `Representation.BrauerNesbitt`): it names the
  theorem, and renaming it would have rewritten `GaloisRep/Deformation/FiniteDescent`, an
  out-of-scope FLT-domain module, for no homing gain.
* **`GroupTheory.MarksTwelve`** (not `MulAction.MarksTwelve`): the twenty-eight declarations are
  Sylow/marks lemmas about a group of order 12, not about an action; `GroupTheory.*` is the port's
  established subject namespace (`GroupTheory.BassSerre`, `.Kurosh`).
* **`UnimodularLift` stays at root** (not `Int.Unimodular`): inside `namespace Int`, mathlib's
  `Int.dvd_mul_of_dvd_right` shadows the generic lemma of the same name and the proof stops
  elaborating; the pin's own name is descriptive anyway.
* **`FinrankStable` is a root subject namespace** (not `LinearEquiv.FinrankStable`): inside
  `namespace LinearEquiv`, `map_sub`/`map_sum` resolve to the `LinearEquiv` lemmas and one rewrite
  in the fitting argument fails. The same shadowing hazard is why `IntermediateField.AdjoinExtension`
  and `Matrix.TransposeMulVec` were kept to *auxiliary* sub-namespaces (their names are unique) and
  why `integralClosure`, `ZSpan`, `ZMod.BernoulliTsum` and `IsLocalRing` needed no such fallback.
* **`SolChiFinField.isIntegral_apply` is `private`**, not a `RingHom` lemma: inside `namespace
  RingHom` the statement's `IsIntegral` resolves to a ring-hom relation and fails; it is a proof
  step of the extension theorem with no consumer.
* **The `PoissonSummation/` directory split was dropped**: it is cosmetic and moving
  `PoissonSummationPi` would re-key its seven `own:` markers for no verification gain.
* **`LogBranchAndPrimitiveRoot` was not split**: the two headlines are different subjects (a
  `Complex` log branch, and a primitive-root ring hom), but the module is the two-ℂ-supplement set
  the reduction-integral-closure proof consumes; its two pin `solution` wrappers are `private` and
  the file keeps both headlines. A split is a module-boundary decision, not a homing one, and would
  add a file for one four-declaration half.
* **The dependency inversion is broken by a private local `det_entries`** in
  `GroupTheory/ModularGroup/FreeProduct`, not by a new shared module: the four `mapGL` entry lemmas
  have five consumers in the modular-forms tree, so a single library home is a separate,
  tree-wide re-home (recorded in `CARRY-FORWARD.md`).
* **One dedup fell out**: `AddAutTransvectionFrame`'s specialised `mul_apply'` was dropped in
  favour of the compat module's general `AddAut.mul_apply'` (a real collision, found by the build).
* **Splits** (all three named in the table): `TorsionFinite` →
  `Algebra/Module/Torsion/Finite` + `RingTheory/Valuation/FiniteModule`; `DecayEstimates` →
  `Analysis/Calculus/SeminormBound` + `Analysis/SpecialFunctions/Pow/Decay`; `LocalRingNilpotent` →
  `RingTheory/LocalRing/{DimensionOne,IdempotentLift}`.

**Per-module verification** was `lake build` (0 warnings) + `check_port --force` (0 mismatch / 0
missing, the expected `ok` count) for every touched file, plus the import sweep (`0 stale
`import FLTForHuman.*``) and `check_port --all` at the end. The tracked records
(`CARRY-FORWARD.md`, `logs/`, the work orders, the homing note) carry the new paths.

## 9. Process lessons

* **Write the homing decision into the order**, not into the agent's taste: "home by subject;
  namespace by object; never expose the pin wrapper" is one line and prevents the whole class.
* **"Mathlib-shaped" is about the statement's subject, not the object's namespace.** A theorem about
  a matrix group can be group theory; a theorem about a graph can be group theory; a theorem about
  a representation is representation theory.
* **Do the re-home before the first consumer.** Leaves are cheap; after a landing the cost moves to
  proof scripts and importers.
* **Path and namespace are independent axes; both must be right.** Renaming a namespace does not fix
  a wrong home, and moving a file does not fix a wrong namespace.
* **The checker is name-insensitive; the rest of the tree is not — and neither is the build.**
  Renames are safe for verification, but they are not free: `open`s, scoped instances, markers and
  records must move with them, and a namespace is a *resolution context*: inside `namespace Int`,
  `LinearEquiv`, `RingHom` or `Matrix`, an unqualified `dvd_mul_of_dvd_right`, `map_sub` or
  `IsIntegral` can resolve to the namespace's own lemma and a green block turns red. Put a renamed
  block under the object's namespace only where the collision check finds no same-last-name lemma;
  otherwise use a subject namespace at root (`FinrankStable`, `UnimodularLift`) or a descriptive aux
  sub-namespace (`IntermediateField.AdjoinExtension`, `Matrix.TransposeMulVec`).
* **Touch ⇒ rectify.** A path move never lands with its old namespace, and a file is not left
  pin-labelled because its path happens to be right: audit every `namespace` the file declares —
  private-only helper namespaces included — and record where each pin name went in the header.
* **A plan is evidence.** Write the plan with measured numbers, per-module targets and acceptance
  gates, and merge it into the standard when it lands: a landed plan is the cheapest evidence the
  next session can read, and a live-looking one is a maintenance liability.
* **Measure the dependency graph** — a cut that increases import edges is a cut to reconsider; a cut
  that lowers them is the one to keep.
* **Ask where the user would look, then check the graph.** The user-view question decides the home
  and the module name; the dependency metric is the sanity check on the answer, not the criterion.
  A user-facing API module can add an edge and still be right — as the `SL₂` API module does.
