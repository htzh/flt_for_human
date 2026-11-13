# Carry-forward register

Status of work that is **not done** — deferred API, open follow-ups, cleanup — with the facts
needed to price it. Grep this file for a node name before pricing that node: an entry means its
`lines`/`needed` does not yet account for something its consumers need. Add an entry when part of a
pin file's surface is deferred; delete it when the work lands. The general scoping cautions are in
[porting-playbook.md](porting-playbook.md) §2.1.

Deferred API that has been ported and verified is in `Reserve/`, not here.

## Deferred API

### The two `exists_digit`s — one general, one pinned, to be fused when `Place/ConstantFieldExtension.lean` is next opened

`Place/ConstantFieldExtension.lean`'s `ConstantFieldPlaceLift.exists_digit` is a **pin
declaration** (pin `S_…Place_exists_comap_algebraMap_eq_of_constantFieldExtension.lean:241`,
checked `ok`): `[IsAlgClosed K] [IsCurveOver K F]` and the conclusion
`∃ a o', o = algebraMap … a + π * o' ∧ (o = 0 → o' = 0)`. SET 3's BC4 needed the same digit
decomposition under weaker hypotheses — only `[Module.Finite K v.ResidueField]` and no
`IsCurveOver`, which its frozen ramification statement does not provide — so it states the
general form publicly at `AlgebraicCurve.Place.exists_digit` in
`Place/ConstantFieldExtensionRamification.lean`, without the `(o = 0 → o' = 0)` conjunct.

The two are the same argument. The clean end-state is **one** public lemma with the stronger
conclusion at the weaker hypotheses, with the pinned statement a three-line wrapper on top —
which is an edit to a hub module in the direction *opposite* to the current import edge
(`ConstantFieldExtensionRamification` already imports the place dictionary, and
`Place/ConstantFieldExtension.lean` must not import it back). So the fusion waits for the next
refactor round of that module, not for a consumer.

Price: ~10 lines moved plus one wrapper, no statement change; the checker is unaffected.

### Four dropped declarations of the ported `Defs/` modules (SET 3 audit, 2026-10-27)

The SET 3 ground audit of the twelve pin `Def_*` modules in the next AlgebraicCurve cluster's
closure found their ported surface complete **for that cluster**, with four recorded drops.
Two of them have live pin consumers and will be wanted by another column's node:

* `Place.fiber_eq_fiberOver` (`Definitions/Def_AlgebraicCurve_PlacesOverDVR.lean`, 2 lines) is
  the `fiber = fiberOver` identification; **five** pin `S_` files use it (`S_…Place_hasValue_norm_along_of_separableAlong`,
  `S_…ModularCurve_JZero_exists_pointHt_le_absLogHeight_jCoord` and three more), while the port
  inlines `ext w; rw [mem_fiber, mem_fiberOver]` at each site (e.g. `WeilExchange/Transport.lean`).
  Home: `Defs/PlacesOverDVR.lean`, wired 36 ok / 0 / 0.
* `Place.finite_setOf_forall_mem_and_ord_pos` (same pin file, ~20 lines) — the finiteness of the
  places centred in a DVR with positive order at `r₀`; four pin `S_` files use it, including the
  `pushforwardNormFormula` pair. Home: the same module.

The other two are pin-dead and should stay dropped: `Divisor.mapRestrict`/`mapRestrict_single`
(used only inside their own pin `Def_` file — `grep -c` over the pin tree gives 1) and
`Divisor.card_fiberOver_eq` (same). `AbelJacobiCard` (`Def_AlgebraicCurve_DivisorClassGroup.lean`)
is the statement of an unported Abel–Jacobi node, not definition surface: it belongs to the
pruned complex-analytic subject.

Price: two declarations, no statement changes, no checker movement on any existing module; take
them when `Defs/PlacesOverDVR.lean` is next opened.

### The DC1 wave's homing debt — `rightConv` laws and `orbitSpan` support in `ArchDualCut`

Landed 2026-10-25 ([automorphicForm/WORKORDER-DC1-arch-dual-cut.md](automorphicForm/WORKORDER-DC1-arch-dual-cut.md)).
Two public results of the dual-cut node are not about the dual cut, and they sit in
`AutomorphicForm/Adelic/ArchDualCut.lean` only because their natural owners were frozen for the
wave:

* `hasCompactSupport_of_mem_orbitSpan` (pin `S_ …archDualCutSubmodule_and_rightConv_eq.lean:788`) —
  a property of the orbit span; its home is `AutomorphicForm/Adelic/ArchCompactOrbit.lean`, beside
  `orbitSpan`'s membership API. The cut-side sibling's pin file carries the same lemma and will
  want it too;
* `rightConv_rightTranslate_rightTranslate'` (:800) — invariance of `rightConv` under simultaneous
  right translation; its home is the `Operators` section of
  `AutomorphicForm/Adelic/IsotypicCuspSpace.lean`, beside `rightConv_add_left`, with it the four
  private `rightConv` laws of `ArchDualCut` (`integrable_mul_rightConv`, `rightConv_add_right`,
  `rightConv_smul_right`, `rightConv_smul_left`), which are the second-argument bilinearity of
  `rightConv` and will be re-proved by any other right-convolution consumer that needs them.

Price: additions to two existing modules (~12 + ~12 lines plus four ~8-line lemmas and their
docstrings), no statement of an existing module changes, so the checker is unaffected; take it
when one of those modules is opened for another reason. Until then the two results are public and
checked where they are.

### SET-AF55's A8 — homed one import above its subject, to be moved into `CutWeightDecomposition` when that module is migrated

Landed 2026-11-13 ([automorphicForm/SET-AF55.md](automorphicForm/SET-AF55.md) §3.3). The row
`AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` (56 silo,
pin `P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot.lean`)
is homed in `AutomorphicForm/Adelic/Cusp/ConstituentCharCut.lean` — a one-headline module — only
because its subject home, `AutomorphicForm/Adelic/Cusp/CutWeightDecomposition.lean` (which holds the
row's single premise), is still wired through the frozen `spec/old_check_stmts.py` `PORT_FILES`, and
appending there would have dragged that module's whole legacy migration (a `spec-pin:` wire over a
906-line pin source, the `PORT_FILES` deletion, a ~76-declaration public-surface diff) into the wave.

**The debt**: when `CutWeightDecomposition` is next opened, move the declaration down into it, delete
`ConstituentCharCut.lean`, and (if it is then the only declaration with that subject) keep the
`spec-pin:` pair with the moved declaration. The statement does not change and the checker's reading
of the declaration moves with it. Price: one file deletion plus a wire line; no mathematics.

### The four generic type-submodule lemmas — transcribed twice, one home still owed

`comp_mem_typeSubmodule_of_map`, `comp_mem_iSup_of_forall`,
`commute_of_glArch_eq_one_of_glFin_eq_one` and `eq_of_glArch_eq_of_glFin_eq` are generic
representation-theory rows (`{H G G' W} [Group …] [AddCommGroup W] [Module ℂ W]`, no automorphic-form
content). The port holds the first three in `AutomorphicForm/Adelic/RightConvIntegral.lean` and the
fourth as `CuspidalSpectrum.eq_of_glArch_eq_of_glFin_eq` in `AutomorphicForm/Adelic/Cusp/SpectrumLift.lean`;
SET-AF55's A3 transcribes all four again in `AutomorphicForm/Adelic/TestFnInvariance.lean`, because
both holding modules sit **above** it and importing is a cycle (FR-0191).

**The debt**: their home is a `RepTheory` module below `RightConvIntegral` and below `TestFnInvariance`
(`RepTheory/TypeSpan.lean` is the natural owner of the type-submodule span induction). Move them
there, then delete the `RightConvIntegral` and `TestFnInvariance` copies and let `SpectrumLift` import
the generic one. Price: four declarations (~47 lines) plus the three call sites' imports; no statement
changes in the consuming modules. Until then both copies are public, checked where they are, and
`dedup.py`'s `shape` clusters between them are the recorded ruling (SET-AF55 §3.4).

### The cuspidal unfolding (`integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn`, 635) — deferred at SET-AF56's scaffold, **homed at SET-AF57**

Read off the D–S shelf and cut at the scaffold, not by preference: the row's **statement** needs the
adele ring's `MeasurableSpace`/`SecondCountableTopology` instances, which the pin derives privately in
the proof file and the port does not carry globally (FR-0194). The three things a definition-layer set
has to settle first: the `attribute [local instance] NumberField.AdelicHaar.adeleBorel` convention (a
per-module pin, not an instance), the v4.34 spelling of the finite-adeles second-countability
(`NumberField.AdelicHaar.ProductMeasure.L1.secondCountableTopology_finiteAdeleRing`, a theorem), and
whether the pin's `private scoped instance` block can be dropped wholesale against the port's
`AdelicHaar/PlaceMeasure` scoped instances. **Resolved the next day.** The three things are FR-0196's three steps (`adeleBorel`/`glBorel` pinned
**inside** the section, and `open scoped ProbabilityTheory` for `μ[|s]`), and with them the 635-line
statement elaborates in one probe — the pin's derived-instance block is simply dropped. The row is now
homed in `AutomorphicForm/Adelic/CuspidalUnfolding.lean` (31 declarations at the pin's names, 30 of them
`private`), scaffolded and checker-green under SET-AF57, with its leaf neighbour
`constantTerm_adelicBox_unipotentGL2_mul` (144, 14 project consumers) in
`AutomorphicForm/Adelic/ConstantTermUnipotent.lean`.

### `Finset.map_noncommProd` inside `rw` — a v4.34 elaboration trap with a written cure (FR-0195)

Not a debt but a recipe to reuse: `rw [Finset.map_noncommProd]` fails at v4.34 with "target expression
is not type-correct under the `implicit` transparency level", because the lemma's right-hand side is
`fun _ hx _ hy _ => (comm.forall₂ hx hy).map g` and `rw` elaborates patterns at *implicit*
transparency. State the step as a closed `have` (default transparency) and `rw` with it. Found and
cured in SET-AF56's row A (`RightConvProduct.iota_mulSingle`); the worked line pair is in
[logs/frictions.md](logs/frictions.md) FR-0195. Any future port of a `noncommProd`/`noncommSum`
argument (the Hecke-coset and `Finset.map` families) should expect it.

### Two dead prelude lemmas of the dual-cut node — dropped, not ported

`orbitSpan_le_Ecf` (pin `S_ …archDualCutSubmodule_and_rightConv_eq.lean:268`) and
`placeOrbitSpan_mono_of_mem` (:460) are declared in that `S_` file and used **nowhere** in it or in
any ported consumer: the only other occurrences in the pin are copies inside sibling `S_` files,
and the landed cut module (`ArchCutProjector`, which carries the same prelude block) does not have
them either. They were therefore dropped as dead prelude rather than transcribed. If a future node
needs them, its own file carries a copy: port them there at the pin's statement. Prices: 2–6 lines
each.

### The pin's proof-search **task labels** still in the port — a naming pass of its own

The pin nests its generated proofs in task-label namespaces (`P6B`, `JE2aFlat`, `JE2aHMod`, `M4aS4`,
`M4aP3B`, `RINHFold`). Those are **not subjects**: the same label carries unrelated mathematics in
different pin files — `P6B.JE2aFlat` is 11 pin `S_` files, from `LocalNewvector_PSCarrier_*` to
`NumberField_dedekindZeta_ne_zero`; `M4aS4` is 6; `M4aP3B` 19. The port's rule is explicit ("no
random tokens in names") and it has a precedent: SET-AF4 dropped `P6B.RFCSol` as "a proof-search
label: keep the names". Five labels survived, either deliberately (the headers of
`Adelic/InducedSectionFlat.lean` and `NumberTheory/AdelicHaar/AdelicModulus.lean` say the pin
namespaces are kept) or by inheritance:

**Resolved 2026-11-02** (the instruction was to fix the label that had reached a module under edit,
and any co-occurring label in the same modules): `P6B.JE2aFlat` → `FlatInducedSection`
(`AutomorphicForm`, `Adelic/InducedSectionFlat.lean`) and → `PlaceModulus` (`NumberField.AdelicHaar`,
`NumberTheory/AdelicHaar/AdelicModulus.lean`); `P6B.JE2aHMod` → `ZhatModulus`; the `RINHFold_*` and
`RHMODFold_*` **section** labels dropped. Four modules edited, all their importers rebuilt and green,
the checker unchanged. **Still open:** `M4aS4` — it is one namespace spread over
`AdelicHaar/PlaceMeasure.lean` (29 declarations) and `AdelicHaar/AdelicModulus.lean` (4, which use
PlaceMeasure's `placeBorel`/`finMeasure` unqualified), so it moves only in a sweep over both, together
with its ~15 references in `WeylIntegrable/*`, `Iwasawa/Complex/*`, `MeasureTheory/FourierDecay`,
`Analysis/Calculus/SeminormBound` and the big-cell module's `attribute [local instance]` lines; and
`M4aP3B`, which is only four docstring references to pin file names.

**Second pass, 2026-11-02 — the AF column's `arch*` and `Iwasawa` modules, and the Iwasawa
migration.** Two families, nine labels on namespaces and four more in the Iwasawa column:

* **arch-Casimir** (`Adelic/ArchCasimir.lean`, `Adelic/ArchCasimirComplex.lean`,
  `Adelic/ArchDerivRightConv.lean`): `CasCore17`→`CasCore`, `CommAway17`→`CommAway`,
  `Elem17LR`→`ElemLR`, `CasLR17`→`CasLR`, `OsAlg17`→`OsAlg`, `OsInf17`→`OsInf`,
  `InvZero22`→`InvZero`, `CommAway40`→`CommAwayC` (the complex twin), `CommConv17`→`CommConv`,
  `CasLeft2`→`CasLeft`; the pin's file wrappers `Ws23`/`M0a`/`Ws26`/`Ws50KDER0` dropped.
  Statements untouched, so the checker's name tier loses and its **content-hash tier** carries:
  measured **135 / 106 / 5 ok, 0 mismatch / 0 missing** before and after, wires unchanged.
* **Iwasawa** (`AutomorphicForm/Iwasawa/{Real,Complex}/*`): `B2bCL1`→`ComplexIwasawa.UniformDecay`,
  `B2bCL2`→`ComplexIwasawa.Decay`, `B2bRUnif`→`RealIwasawa.UniformDecay`, and
  `RealIwasawa.Ws1.HARCHR`→`RealIwasawa.HARCHR` (the `.Ws1` file label dropped; the complex twin
  `HARCHC` never carried one).

**The Iwasawa modules were then migrated to `spec-pin`** (they were tier 3, unwired). Three
findings worth keeping:

1. **A `-- pin:` marker that names a *bare* pin file is `UNKNOWN PIN FILE` to `check_port`.** Every
   one of those modules carried markers of the form `-- pin: kC (S_….lean:33)` — no `P2M/Sol/`
   prefix — so the checker could not resolve them and every marked declaration came out `missing`
   until the markers were stripped and the files moved into the header (`spec-pin: P2M/Sol/S_….lean`).
   The old checker resolved bare names; `spec-pin` does not. **Strip-on-touch is also what unblocks
   a migration.**
2. **The wire is discoverable from the checker**: with one or two files wired, each `missing` line
   prints `identical statement at <file>:<line> (not in this wire)` — that hint *is* the missing wire
   entry. Ten modules needed 2–9 pin files each (the pin's per-file preludes overlap heavily).
3. **One statement genuinely differs by a pipeline label**: `RealIwasawa.RealDecay.radR_eq_rad`
   states its right-hand side with the pin's `M4aP3B.RealIwasawa.rad` label, which has no port
   namespace; it is now an `own:` row in `spec/decl_markers.tsv` with that reason. It is the only
   such row the migration needed.

Result: 282 markers stripped, ten modules wired, `check_port` per module **0 mismatch / 0 missing**
(4, 1, 93, 11, 9, 16 for `Complex/{Basic,Continuation,Core,Decay,Estimates,UniformDecay}`; 1, 113, 52,
4 for `Real/{Continuation,Core,Decay,Estimates}`), one `own:` row, headers rewired (the "(tier 3,
unlisted)" and "every declaration carries a `-- pin:` comment" sentences are gone),
`spec/UNWIRED-PUBLIC.md` **112 → 105 modules / 3,394 → 3,106 public declarations** (the ten
Iwasawa modules are gone from it), all ten modules rebuilt.

**Still open elsewhere — the survey, re-measured 2026-11-02.** 151 digit-carrying namespaces remain
in the port; most are *mathematical* (`Pic0` 12 files, `LocalGL2` 4, `X1DiamondRational`/`X1HeckeCommute`/
`X1x0`, `Gamma1Hecke`, `HeckeGamma1`, `KatzGamma0Form`, `CuspForm.Gamma1Hecke`, `Module.End.Sl2Strings`,
`FLT.Gamma0FundamentalSet`) and must stay. The pipeline families, by the number of namespaces:
`WLightS9/S10/S11` (16 — they are *pin file names* used as namespaces), `Ldgr*` (11), `Mmr*` (7),
`P2MKc*` (6), `W7X*` (5) over 4 files, `MilneAvAg*` (4), `N5ID*` (4), `Mp72a*` (4 over 2 files),
`Es1a1` (4 files), `X1DiamondRational` (3, math), `FujisakiC*` (3), `GL2StrongApproxW8M` (5 files),
plus singletons (`A2*`, `B2`, `K1HBC`, `EIS2K1`, `ES1Sol`, `F10d`, `FF2`, `FrobChareqC2`, `G1Discharge`,
`G2Proof`, `IharaSlashB2a`, `Lg37`, `P1Tower`, `P2mS26B6b`, `S06W2`, `S12R`, `S13Bridge`, `SEXP1`,
`SU2EulerAux`, `RatioE96`, `Velu5Generic`, `Cotpk43T3`, `W1`, `W2`, `W4B*`, `WL12Pen`, `WLightR2`,
`WPGamma1`, `Ws13S7`, `Ws18BDeg`, `Ws18BDist`, `Ws47`, `X1`, `ArchModS44`, `ElevenA1`, `GF24a*` 3,
`Aux4SevenTN*` 2, `DeligneSerre271`/`72`, `M4aHerbrand*` 2, `M4aLocalCFT.*` 4, `M4aS4` 2,
`P2MTwisted*`/`P2mWInert*` 2, `S_*` 16 in `WLightS9/S10/S11`, …). `M4aS4` is still **live in code**
(`attribute [local instance] M4aS4.placeBorel`/`infMS`, `BigCellExpansion.lean` ×3 and
`WeylIntegrable/UniformBound.lean` ×1), so its sweep also repoints four `attribute` lines.

Method for any of them (measured twice now): strip the markers, put **every** file they named into
the header as `spec-pin:` with its full `P2M/Sol/…` path, keep the abbreviation and drop the id, and
let the checker's `identical statement at … (not in this wire)` hints complete the wire. It is free
on the checker side (namespace segments are not compared), the statements do not move, and no wire
that already exists changes — only the modules' own headers, plus one rebuild each.

The table below is the survey as written:

| label | port files | occurrences | what it actually holds there |
|---|---|---:|---|
| `P6B.JE2aFlat` | `Adelic/InducedSectionFlat`, `Adelic/BigCellExpansion` (an `open`), `NumberTheory/AdelicHaar/AdelicModulus` | 12 | the flat induced section (34 decls) **and**, in the NumberTheory module, `placeModulus` + the fin-component norm lemmas (5 decls) — two subjects under one label |
| `P6B.JE2aHMod` | `NumberTheory/AdelicHaar/AdelicModulus` | 19 | the `ẑ`-coset / transversal modulus machinery (46 decls) |
| `M4aS4` | `NumberTheory/AdelicHaar/{PlaceMeasure,AdelicModulus,ArchModulus}`, `Adelic/WeylIntegrable/{Assembly,LatticeEstimates,UniformBound}`, `Iwasawa/Complex/{Core,Decay}`, `Analysis/Calculus/SeminormBound`, `MeasureTheory/FourierDecay` | 30 | place measures (29 decls in `PlaceMeasure`) **and** transversals (4 decls in `AdelicModulus`) |
| `M4aP3B` | `Analysis/Calculus/SeminormBound` (`M4aP3B.Rows.UniformSeminorm`), `MeasureTheory/FourierDecay` and `Iwasawa/Complex/{Core,Decay}` (`M4aP3B.FourierDecay`) | 4 | **a source-file reference in a docstring**, not a namespace — drop or repoint |
| `RINHFold` | `Adelic/InducedSectionFlat` (sections only) | 6 | fold markers, not namespaces |

Proposed map as executed: `P6B.JE2aFlat` (InducedSectionFlat) →
`AutomorphicForm.FlatInducedSection`; `P6B.JE2aFlat` (AdelicModulus) →
`NumberField.AdeleRing.PlaceModulus`; `P6B.JE2aHMod` → `NumberField.AdeleRing.ZhatModulus`;
`M4aS4` (PlaceMeasure) → `NumberField.AdelicHaar.PlaceMeasure`, `M4aS4` (AdelicModulus) →
`NumberField.AdeleRing.HasTransversal`; `M4aP3B`/`RINHFold` → drop (sections and 4 helpers).
Two of these pairs **must move together** (`P6B.JE2aFlat` is declared in two modules and
`InducedSectionFlat` reuses `AdelicModulus`'s copy), so it is all-or-nothing per label —
a naming sweep, not a set: ~11 files, 3 hub modules (2 and 8 importers), mechanical edits, a
`dedup`-free pass with only builds to pay. Not done as of 2026-11-02 (SET-AF7 §5 records where it
was noticed: the new `open AutomorphicForm.P6B.JE2aFlat` in the big-cell module).

### The FTF1 left half's nine pre-cut declarations — in the pin only — **RESOLVED 2026-11-02**

> **Resolved by SET-AF6's manager's layer.** The left halves were promoted out of `Reserve/` into
> `FLTForHuman/AutomorphicForm/Adelic/FactorizableTestFnArchSmooth{,Complex}Left.lean`, public at the
> port's content names, and all nine declarations below were restored from the pin there (the four
> real ones and the five complex ones). `Reserve/AutomorphicForm/Adelic/` is now empty. The record
> below is kept as written.

On 2026-10-23 the FTF1 left halves moved to
`Reserve/AutomorphicForm/Adelic/FactorizableTestFnArchSmooth{,Complex}Dead.lean`, but an earlier
pass had already cut nine declarations of that half from the live modules, so they have no home in
the port at all:

* real, `S_AutomorphicForm_IsFactorizableTestFn_isArchSmoothAt_and_archDerivAt_eq_tensor.lean`:
  `e8l5_archFlowAt_inv` :392, `e8l5_continuous_cD` :427, `e8l5_glFin_archFlowAt` :486,
  `e8l5_isFactorizableTestFn_leftDeriv` :541;
* complex, `S_…_isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor.lean`:
  `e8l5_exists_compact_support` :363, `e8l5_continuous_cD` :429, `e8l5_continuous_LD` :433,
  `e8l5_isFactorizableTestFn_leftDeriv` :543, `e8l5_leftDeriv_tensor` :550.

Nothing in the port needs them — the headline and the pin's own `solution` reach only the right
half — so this is deferred API, not a gap in a proof. It matters only if the left action is taken
up: the shelves then lack these nine (and are ragged against each other, see their headers), and
the fix is to port them from the pin under the rename map the shelf headers carry. Prices: 3–19
lines each, all `private`.

### `Eaux_apply` — a pin-public unfolding lemma with no consumer, deferred from FR1

`Eaux_apply (a b : ℕ) (τ : ℍ) : Eaux a b τ = E₄ τ ^ a * E₆ τ ^ b` is pin-public at
`S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean:605`. It is used
**nowhere** in the pin — a `grep -c` over the whole tree finds the declaration line only — and the
FR1 module does not need it, so [deligneSerre/WORKORDER-FR1-fricke-reciprocity.md](deligneSerre/WORKORDER-FR1-fricke-reciprocity.md)
deferred it rather than open `WeightOne/Gamma0Integral.lean` to append one line. If a consumer ever
appears its home is beside the public `Eaux` in that module (`:1628`), appended at the pin's
signature with a `pin:` row — the treatment `frickeConj` got. Nothing any pin file uses is missing;
the entry is here so that a later reader does not mistake the omission for an oversight.

### `Def_AutomorphicForm_CuspidalSpectrumCarrier` — **closed 2026-11-02 (landed and consumed)**

Landed as `FLTForHuman/AutomorphicForm/Adelic/Cusp/SpectrumCarrier.lean` (289 lines, **41 declarations,
41 `ok`**) with its `Def_AutomorphicForm_CuspidalSpectrumSubrep` sibling (104 lines, 11 `ok`) in
`Cusp/SpectrumSubrep.lean`, and consumed in the same set: the deferred 234-line slab bound
(`CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample`)
landed in `Cusp/SpectrumPairing.lean` (`2 ok`), together with five carrier-API rows, the general
norm-exponent node whose only port copy had been the ℚ statement (FR-0092), and the row the set makes
ready (`exists_hasModulus_of_isCuspConstituent`, 37). Scope and numbers:
[topics/automorphicForm/SET-AF1.md](topics/automorphicForm/SET-AF1.md) §1.4–§1.5; the entry is deleted
because nothing of it is owed.

### `Def_ModularCurve_EigenformIdeal` — the gate of `omegaRow_T2`'s definition layer

Deferred 2026-10-20 while porting the nine small-family pairs (WORKORDER-MG3, group C). The 24-line pin
module defines three declarations **in terms of** declarations of another pin definition module:

- `ModularCurve.IsEigenformIdeal (N) (𝔪 : Ideal HeckeAlg) : Prop` :=
  `∃ f IsNormalizedEigenform …, 𝔪 = eigenIdeal (…)` — uses `eigenIdeal`;
- `ModularCurve.EigenformSupportAt` := `EigenformSupport p J (IsEigenformIdeal N)` — uses `EigenformSupport`;
- `ModularCurve.EichlerShimuraDataAt` := `EichlerShimuraDataReduced … (IsEigenformIdeal N)` — uses
  `EichlerShimuraDataReduced`.

All three of `eigenIdeal`, `EigenformSupport`, `EichlerShimuraDataReduced` live in
`Definitions/Def_HeckeGalois_EichlerShimura.lean`, which this register already records as blocked
(`ModularForms/HeckeFiniteAlgebra.lean`, "Still blocked (not this module)"; §`exists_hasEquivariantPrimitiveOf`
above). Homing the 24-line gate therefore means homing that module and its prerequisites first.

**What is deferred is only the gate.** `ModularCurve.omegaRow_T2` (447 pin lines) and its six
`ModularForm`/`ModularCurve` premises reference none of the three declarations
(`rg -c 'eigenIdeal|EigenformSupport|EichlerShimuraDataReduced' P2M/Sol/S_omegaRow_T2.lean` → 0), so the
pair landed without it. **Trigger:** a consumer that states `IsEigenformIdeal`, `EigenformSupportAt` or
`EichlerShimuraDataAt` — i.e. any `Def_HeckeGalois_EichlerShimura` consumer — must home that module (and
then this 24-line gate) first. Do not port a consumer of the three by stubbing them.

### `Def_Compat_Mathlib430` blocks A–C — not homed, only block D is

Decided 2026-10-20 while porting `AddAut.exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem`
(WORKORDER-MG3 group D). The pin module (`Definitions/Def_Compat_Mathlib430.lean`, 340 lines, imported
by 197 pin `S_`/`Theorems` files) vendors four blocks of mathlib **4.30.0** API that `v4.34.0` renamed or
removed:

- **block D** (lines 124–340): `instance : Group (AddAut A)` plus thirteen primed lemmas
  (`coe_mul'`, `mul_apply'`, `inv_def'`, …). **Homed** as `FLTForHuman/Algebra/AddAut/Compat.lean`,
  because v4.34 gives `AddAut` only an *additive* group and the `AddAut` node's statement
  (`(H : Subgroup (AddAut (ZMod M × ZMod M)))`) cannot elaborate without a `Group` instance. `rg` cannot
  see this need — it is a typeclass instance, not a symbol — so a "the compat import is dead" reading is
  wrong here.
- **blocks A–C** (lines 20–122): the v4.30 `Representation`/`Rep` API (`ofMulActionFinsupp*`,
  `leftRegularHomFinsupp*`, and their `Bridge` lemmas). **Not homed**: no port consumer, and vendoring
  old representation API wholesale invites future landings to use it instead of adapting to `v4.34`.
  Trigger: any ported node whose statement or proof names one of those declarations — then home the
  block that is needed, verbatim, at the pin's suffixed names, and record it here.

### `HeckeEis.coresHom_eq_transfer` — a definition gate still deferred

Deferred 2026-10-20 at the close of WORKORDER-MG3 phase 2, when the column stopped cutting this front.
It is a statement-level gap (nothing in the port can be imported for it) and it asks for a pin
definition module the port has never homed:

| node | pin lines | gate module | gate lines | pin importers |
|---|---:|---|---:|---:|
| `HeckeEis.coresHom_eq_transfer` | 59 | `Def_Gamma0HeckeOperatorHom` (`HeckeEis.coresHom`, `transferAux`, `coe_transferAux`) | 304 | 144 |

`rg` over `FLTForHuman/` still finds no `coresHom`/`transferAux`; that gate remains deferred.
**Trigger**: home `Def_Gamma0HeckeOperatorHom` **whole and verbatim** (playbook §2.3), with its own
`spec-pin:` header, before stating the node.

### The `LocalNewvector` pair of WORKORDER-MG3 — a definition gate bigger than the family

Deferred 2026-10-20 while phase 2 was dispatching. The two nodes — `LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization`
(58 pin lines) and `…exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq` (589) — total
647 pin lines, but **none of the vocabulary they are stated over is homed**. The gate, measured by the group that found it:

| pin module | lines | pin importers | needed for |
|---|---:|---:|---|
| `Def_LocalNewvector_AdelicSpanCarrier` | 179 | **173** | both (`LocalNewvector.AdelicSpan`, `AdelicFnCarrier`, `AdelicSpanSubmodule`) |
| `Def_LocalNewvector_ConductorDatum` | 114 | 56 | both (`fixedSubmodule`, `mem_fixedSubmodule_iff`, `HasNewvectorConductor`, `congruenceK1_le_integralSubgroup`) |
| `Def_RepTheory_GL2CongruenceSubgroup` | 531 | 23 | node 2 (`FLT.SmoothVectors.gl2CongruenceSubgroup` and its API) |
| `Def_LocalLanglands_IntegralSubgroupCompact` | 40 | 17 | node 2 (`FLT.SpectralSide.isCompact_coe_integralSubgroup_padic`) |

≈ **864 pin definition lines for a 647-line family** — it is not a small family, and `AdelicSpanCarrier`
(173 pin importers) and `GL2CongruenceSubgroup` (531 lines) are definition sets with consumers of their
own, so they want an order and a review of their own rather than being a side-charge on a pair.

Two further pin definition modules are touched **only** by the wrappers' `open`/`attribute` lines (so
dropping them leaves no statement effect; record the drift): `Def_LocalNewvector_PrincipalSeriesCarrier`
(255, the `PSCarrier` `attribute [-instance]`/`[-simp]` prelude) and
`Def_AutomorphicForm_DihedralWeightOneLift` (30, an `open … DihedralWeightOne`).

Already homed and *not* owed: `LocalNewvector.padicK1`/`congruenceK0`
(`RepTheory/LocalNewvector/CongruenceSubgroupK1.lean`), `AdelicDock.*`
(`NumberTheory/AdelicDock/LocalEmbedding.lean`), `FLT.SmoothVectors` (`RepTheory/SmoothVectors.lean`),
`AdelicLevel.*`, `LocalGL2.integralSubgroup`, and the `open`-only
`FLT.SpectralSide.isOpen_coe_integralSubgroup_padic`. **Trigger:** the next session that wants these two
nodes homes the four modules **whole and verbatim** (playbook §2.3), `spec-pin:`-header each, before
stating either node.

### The exact-volume / L2 chain — `Def_AutomorphicForm_{Gamma0ExactVolume,FundamentalDomainExactVolume,EisensteinScattering,L2ProductionInstance,L2AutomorphicCarrier,TruncatedDomainPartition}`

Deferred 2026-10-17 while porting `CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus`
(record: [topics/deligneSerre/TOPIC-petersson-hecke-adjointness.md](topics/deligneSerre/TOPIC-petersson-hecke-adjointness.md)). The pin's
`Def_AutomorphicForm_ModularFundamentalDomain.lean` (217 lines) reaches this six-module chain
(1,436 pin lines: 176 + 236 + 278 + 111 + 147 + 488) only for five facts:
`volume_fd_diff_fdo`, `volume_fdo_eq_volume_fd` (from `Gamma0ExactVolume`), `volume_fd_eq`,
`gate_volume_ne_zero` (from `FundamentalDomainExactVolume`) and `measurableSet_smul_fd` (from
`L2ProductionInstance`). The port's
`FLTForHuman/AutomorphicForm/UpperHalfPlane/ModularFundamentalDomain.lean` carries the first two
and the last `private` — short measure-theory proofs over the already-ported
`FundamentalDomainVolume`/`HyperbolicMeasure` — and wires the other 16 public declarations of the
module verbatim.

Deferred:
- the four gate theorems of `ModularFundamentalDomain` (`gate_not_isFundamentalDomain_sl2z`,
  `gate_two_routes`, `gate_factor_two_load_bearing`, `gate_two_routes_ne_zero_ne_top`), the only
  consumers of `volume_fd_eq = ENNReal.ofReal (π / 3)`;
- the whole public surface of the six modules above.

**Not a D-S dependency of its own.** Checked against the 1,396 needed rows of
`frontier.py --ds --include-leaves --list`: no needed node imports any of the six directly; they
enter only through `ModularFundamentalDomain`, which three needed nodes use — this row,
`CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough` and
`CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen`. The latter two additionally need
`Definitions/Def_CuspForm_PeterssonCoset.lean` (744 lines), not ported and not needed here.

### `MeasureAssembly.archBorel` — duplicate of `AutomorphicForm.glBorelOf`

`AutomorphicForm.MeasureAssembly.archBorel`
(`FLTForHuman/AutomorphicForm/Adelic/RightConvComm/MeasureAssembly.lean:61`) is statement-identical
to the pin's `glBorelOf`, which landed at `AutomorphicForm/Adelic/ArchHaar.lean`. The adapter is
used as a `local instance` in `MeasureAssembly.lean` and in `SliceCentrality.lean:55`. Collapsing
the twin edits two modules of the `RightConvComm` cone. Price:
`build_ladder.py --edit FLTForHuman/AutomorphicForm/Adelic/RightConvComm/MeasureAssembly.lean`.

### `CuspForm.exists_degeneracy_gamma1_hasNebentypus` — two unported definition modules

The frontier lists this row ready (218 silo lines); it is not. Its `S_` file imports and uses
`FreyPackage.ModMCarrier.rescaleSlash_isZeroAt`, and neither of the modules supplying it is ported:

- `Definitions/Def_ModularForm_AtkinLehnerDatum.lean` (157 lines, 21 declarations);
- `Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean` (176 lines, 10 declarations).

It is a different subject from the landed Γ₁/Nebentypus pair (nebentypus under the `V_d`
rescaling) and needs its own definition-first order. Reproduce:
`python3 tools/deps/port_advise.py --nodes CuspForm.exists_degeneracy_gamma1_hasNebentypus`.

### `ModularCurve.exists_hasEquivariantPrimitiveOf` — unported pieces of the period API

Landed with its 28-citer `ModularCurve.Period` API in
`FLTForHuman/ModularForms/EichlerShimura/{PeriodPrimitive,PeriodIntegral,PeriodOf}.lean`
(vocabulary and `Γ₀(N)` lattice; `periodOf`/`periodLatticeOf`/`HasEquivariantPrimitiveOf`/
`periodMapOf`). Not ported, because no consumer of this node reaches them:

- `Def_ModularCurve_PeriodTransfer.lean` (150 raw / 104 content): `conjRel`/`conjSubgroup`/
  `conjPrimitive`, `traceRep`/`transferElt`/`traceSum`, `IsEquivariantPrimitive.traceSum`;
- the `Hecke` section of `Def_ModularCurve_PeriodLattice.lean` (≈185 raw):
  `cuspHeckeGen`/`cuspHeckeAeval`/`cuspHeckeRep`/`dualHeckeRep`/`PeriodLatticeHeckeStable`/
  `periodLatticeModule` — the only piece that pulls in `Def_CuspForm_HeckeAlgebra` and
  `Def_HeckeGalois_EichlerShimura`;
- the `CuspForm` Petersson block of `Def_ModularCurve_PeriodOf.lean` (≈30 raw):
  `peterssonIntegrandOf`/`peterssonOf`.

Trigger: the Hecke-stability consumers (`periodLatticeHeckeEnd*`, `PeriodLatticeHeckeStable`) and
the period-transfer consumers (`IsEquivariantPrimitive.traceSum`).
`Def_ModularCurve_PeriodLattice.lean` is in the checker's `SOURCES` for its `Period` section only;
adding the `Hecke` section must not disturb the names already verified from it.

### `JOne.torsionGaloisRep` / `diamondOneBar` — the unported `Pic0` action/torsion block

Five declarations omitted from the X₁ Hecke/diamond inputs because their prerequisite is unported:

- `JOne.torsionGaloisRep`, `JOne.torsionGaloisRep_apply`, `JOne.coe_torsionGaloisRep_apply`
  (pin `Definitions/Def_ModularCurve_X1.lean:189-207`);
- `diamondOneBar`, `diamondOneBar_apply` (pin `Definitions/Def_ModularCurve_X1Diamond.lean:98-103`).

The missing prerequisite:

- `Pic0.torsion` / `mem_torsion` / `instModuleZModTorsion` (pin
  `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`);
- the `SMul`/`DistribMulAction (SemilinearAut K F)` actions on `Divisor` and `Pic0`,
  `degZeroSMulHom`, `smul_mem_torsion`, `instSMulTorsion`/`instDistribMulActionTorsion`,
  `instSMulCommClassZModTorsion`, `SemilinearAut.torsionRep` (pin
  `Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean:206-356`, ≈150 content lines); decided
  home `AlgebraicCurve/Defs/SemilinearAut.lean`, beside the `Pic0.torsion` block in
  `AlgebraicCurve/Defs/Divisor.lean`;
- `ModularCurve.PicAction` (pin `Definitions/Def_ModularCurve_ArithmeticGalois.lean:85-105`),
  decided home `ModularCurve/Defs/ArithmeticGalois.lean`.

Size ≈170 content lines plus the `Pic0.torsion` block; it edits three frozen files, so it is a
definitions-first mini-set with its own review gate. Consumers: the five declarations above and the
successor targets `ModularCurve.heckeDiamondCommuteBar`,
`ModularCurve.rationalRankTwoNebentypus_family`,
`ModularCurve.moduleFinite_padicInt_tateModule_jOne`, `CuspForm.IsEigenformWith.exists_galoisRepAdic_*`.
Not on the `heckeDiamondInputsAll` cone.

Frontier caveat: `ModularCurve/X1/Defs.lean` and `X1/Diamond.lean` are in `PORT_FILES` and their pin
files in `SOURCES`, so a citer that reaches `JOne.torsionGaloisRep` reads one node closer than it
is. Treat those citers as blocked on this entry.

### `Def_EllipticCurve_FunctionFieldPullback` — the remainder behind `placeOf`/`transEquiv`

`FLTForHuman/WeierstrassCurve/Place/PointPlace.lean` ports only what the `weilPairing0` entry point
consumes: `Point.xc`/`yc` (with `xc_some`/`yc_some`, `nonsingular_xc_yc`, `eq_some_xc_yc`),
`placeOf`/`placeOf_asIdeal`, `transEquiv`. `placeOf` is re-derived over the port's
`CoordinateRing.heightOneSpectrumOfEquation` and `transEquiv` over
`WeierstrassCurve.Affine.translationAlgEquivOf` (`Velu/Engine.lean`); the pin's
`transPull`/`pointPull`/`pointHom` route is not transcribed.

Unported (the node's algebraic content — the pullback/translation/multiplication dictionary):
`genericX`/`genericY`, `evalEval_baseChange_polynomial`, `genericPoint`, `pointHom` and its lemmas,
`pointPull`, `FunctionField.algHom_ext`, `exists_eq_baseChange_of_isIntegral_xc`,
`not_isIntegral_xc_of_ne_baseChange`, `genericPoint_*`, `transPull` (with `map_*`/`transPull_*`),
the `transEquiv_*` lemmas beyond the definition, `negPull`/`negEquiv`/`MulGood`/`mulPull`,
`exists_point_xc_eq`/`infinite_point`.

Consumers: the Frey/Galois-representation and `Elliptic/PeriodPair` cones; port the node whole
before pricing those through `PointPlace.lean`. Frontier caveat: the pin file is in `SOURCES` and
`Place/PointPlace.lean` in `PORT_FILES`, so a citer reaching `transPull`, `pointHom`, `genericPoint`
or `negPull` also reads one node closer than it is.

### `NumberField.TateGlobal.integrable_refMeasure_mul` — blocked on the `v4.34.0` product-measure API

Pin file **B**, `S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:5146` (pinned `aa2d8b3`):

```lean
theorem integrable_refMeasure_mul {L} [NormedRing L] {A} {B} {C}
    (hA : Integrable A (archRef μa)) (hB : Integrable B (sRef S μf))
    (hC : Integrable C (deepRef S)) :
    Integrable (fun q => A q.1 * (B q.2.1 * C q.2.2)) (refMeasure S μa μf)
```

The statement carries no measure hypotheses (mathlib `v4.33.0` proved `Integrable.mul_prod`/
`smul_prod`/`op_fst_snd` with `omit [SFinite ν]`). In `v4.34.0` those lemmas carry `[SFinite ν]`,
and the gap is wider than them: `Measure.prod_restrict` needs `[SFinite μ] [SFinite ν]` on the
**unrestricted** factors, and `Measure.prod_eq` needs `SigmaFinite`.

The statement is true and the port already proves the needed s-finiteness — `Integrable f μ` makes
`μ.restrict (Function.support f)` s-finite, which is
`MeasureTheory.sFinite_restrict_support_of_integrable` in
`FLTForHuman/MeasureTheory/Integral/Prod.lean` — but the `v4.34.0` product-measure API cannot
consume it. A general-statement dispatch must first redevelop that API for non-s-finite measures;
it must not change the statement.

The headline `NumberField.TateGlobal.integrable_zetaIntegrand` and the downstream chain are
complete: the declaration's only consumer, `integrableOn_unitsOutside_norm_mul_ideleNorm_rpow`
(B:5190), states the step in a section that carries the Haar hypotheses, and the port inlines the
s-finiteness there. Any other `S_NumberField_TateGlobal_*` file needing the general form is blocked
on the same redevelopment.

### `AlgebraicCurve.linearIndependent_of_constantFieldExtension` — the unported second node

The landed node is
`AlgebraicCurve.linearIndependent_of_constantFieldExtension_of_isAlgClosed` (583 lines, silo rank 1)
in `FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldExtension.lean`. The pin proves the same
development a second time in `S_AlgebraicCurve_linearIndependent_of_constantFieldExtension.lean`
(579 lines, `[CharZero K]` in place of the separating-transcendental route); **17 of its 21
declarations are statement-identical** to the landed ones.

That second node is unported, is demanded by 16 nodes of the same cone, and cites nothing — a graph
leaf, so `frontier.py --ready` drops it by design and it appears only under `--include-leaves`
(`used_by` 16 / 19). Four further declarations (`algebraMap_mem_adjoin`, `exists_ringHom_adjoin`,
`isIntegral_algebraMap`, `transcendental_algebraMap`) are statement-identical in the unported
`S_AlgebraicCurve_genus_eq_of_constantFieldExtension_of_isAlgClosed.lean`
(lines 344/353/358/368) and want one home. Cut the two as one cluster; scope and prices are in
[topics/algebraicCurve/TOPIC-constant-field-extension.md](topics/algebraicCurve/TOPIC-constant-field-extension.md).

### `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` — the unported C2 row

Not a leaf: its one substantive proof step is the premise
`ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, which is unported — only the `CuspForm`
twin is (`FLTForHuman/ModularForms/WeightOne/Gamma1IntegralBasis.lean:871`) — and the twin cannot
substitute, because the headline's `f` is a `ModularForm (Gamma1 N) k` for arbitrary `k : ℤ` and
the cuspidal subspace does not span the Eisenstein part.

Unported closure under `--frontier sources`: **10 nodes / 5,172 raw `S_` lines** (8 `ModularForm` +
1 `WLight` + the row's 36), headed by `ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top` (1,524)
and `ModularForm.exists_gamma1_frickeRational_sigmaTransport` (772), then the
`…_mem_adjoin_exp`/`…_eq_algEquiv_apply`/`…_mem_range_ratCast` steps and
`ModularForm.exists_mul_E4_pow_mul_E6_pow_eq_iff` (424). The default frontier prices the row at
1 node / 36 lines.

Needs its own definition-layer-first `ModularForm`-side work order, not a row on a `ModularCurve`
shelf. Reproduce:
`python3 tools/deps/frontier.py --target ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1 --frontier sources`.
Record: [topics/modularCurve/WORKORDER-C2-x1-function-field.md](topics/modularCurve/WORKORDER-C2-x1-function-field.md)
§2, §9, and the docstring of `FLTForHuman/ModularCurve/X1/IntegralityJqNModC.lean`.

### `WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`

The D row restated in two-curve form; do not transcribe the pin file. `port_advise` finds **107 of
its 183 declarations** already statement-identical in the port (≈2,077 raw lines; 76 trusted + 31
suspect), of which 26 of the 27 `private` hits are D-2's descent core in
`WeierstrassCurve/Isogeny/IntermediateField.lean` (`iA_*`, `iCa_*`, `iPFA_*`, `iPFE_*`, `iCa_K₀`,
`iP_xP`); 9 of the 31 suspect hits are the tool's type-only `def … : Prop` match against
`PeriodPair.DiscriminantNeZero`, where the `KwD5*` class wrappers are new and the match is not.
`port_plan` prices it at **1,975 net-new** lines, not 3,729.

Genuinely new: the two-curve case — `ι : E'.FunctionField →ₐ[K] E.FunctionField` between
*different* curves, `KwD5BetweenCurvesSubfieldDescent` — which occurs only in this file; every
`∃ K₀ …` in the port is one-curve. The new layer is the `hSD_*`/`cfe_*`/`ChiCompChiEqPhi` block plus
the `NoAC` engine (below), ≈1.1k lines by hand.

Work shape: generalise D-2's landed chain to two curves in place (the descent helpers are already
`private` in `IntermediateField.lean`, so it is a promotion plus a second curve), and let the
headline compose with D-5's. Its only consumer is the 415-line capstone
`eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`. Reproduce:
`port_advise.py --nodes WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`,
then `port_plan.py` on its `--json`.

### The uniformization gate's remaining columns

The gate's unported closure is **13 nodes / 11,880 lines**: the S family (seam/index) 6,537 and the
D-descent family 4,764 (the D family has since landed). The j-line is on the `DeligneSerre` capstone
cone — `frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` lists
14 unported `PeriodPair.*` nodes / 9,071 lines, `jLattice_surjective` among them. Measurement:
[topics/velu/TOPIC-V5-periodpair-uniformization.md](topics/velu/TOPIC-V5-periodpair-uniformization.md)
(15,179 lines; the two classical theorems are on the path, not prelude).

Note: the port's `ModularForms/WeightOne/Defs/PeriodPair.lean` is a **different** object — the
weight-one prelude `periodPairOfTau`/`smulPeriodPair` over mathlib's `PeriodPair` struct.

### The rest of the `AutomorphicForm.LocalIntertwining` cluster

Two of the 19 nodes are ported — `integral_unramifiedWeylIntegrand_adicCompletion` and
`integral_smoothWeylIntegrand_adicCompletion`, sets LI-1/LI-2, with their prelude
(`TateGlobal/{WeylPrelude,WeylShell}.lean`); record:
[topics/automorphicForm/TOPIC-local-intertwining-weyl-integrand.md](topics/automorphicForm/TOPIC-local-intertwining-weyl-integrand.md).
The prelude is now in the port, so the rest are their own new files. Remaining, by the cluster's own
import order:

- **layer 0** — `integral_one_add_norm_sq_cpow_neg_eq_pi_div`,
  `integral_one_add_sq_cpow_neg_eq_GammaReal_div`,
  `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg`,
  `exists_bound_norm_integral_mixedSpace_archAtom_prod`,
  `integrable_{complex,real}Atom_and_integrable_moebiusShift`, the two
  `bounded_and_tendsto_integral_{weylShift_sub_integral_smoothAtom_adicCompletion,moebiusShift_sub_integral_*Atom}`,
  the two `tendsto_integral_{normSq_rpow_sub_one_mul_complexAtom,sq_rpow_sub_one_mul_realAtom}_nhdsGT_one_half`
  — 5–25 declarations each, and a 13-declaration shared block between
  `bounded_and_tendsto_integral_weylShift_…` and `integrable_smoothAtom_and_integrable_weylShift_adicCompletion`;
- **layer 1** — the two `moebiusShift` rows,
  `exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion`,
  `exists_one_sub_mul_integral_smoothWeylIntegrand_eq_sum`,
  `integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` (1,291 lines, its own
  5-declaration block), `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg`,
  `integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` (465);
- **layer 2** — `integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`.

### `Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean` — the remainder

Only `higherUnitsAt` is ported (with the smooth headline, in `TateGlobal/WeylSmooth.lean`; the pin
file is in `SOURCES` for that one declaration). The rest of the module — `HasConductorExponentAt`,
`conductorExponentAt`, … — is unported; port the node whole when a consumer needs it.

### `ofReal_pow_cpow` — two `private` re-proofs beside a public port copy

`TateGlobal/WeylShell.lean` and `TateGlobal/WeylSmooth.lean` each re-prove it `private`: the public
port copy at `NumberTheory/NumberField/TateGlobal/EulerFactors.lean:80` is the same identity with the
binders `(x) (m) (s)`, while the LocalIntertwining pin spells them `(a) (s) (k)`, and a `private`
declaration is not importable. Unifying them means generalising the public copy's binders, which
edits a frozen module.

### Orphan phantoms — pin headlines the port states only from behind `private`

`frontier.py`'s `names` tier counts `private` declarations as ported, so a pin headline whose only copy
is `private` leaves the demand while nothing can import it and no checker has diffed it. Scanning every
port module's private declarations against the pin's public `Theorems/` statements
(`tools/deps/phantom_scan.py`, untracked; method in
[logs/phantom-landings.md](logs/phantom-landings.md)) leaves **17 declarations in 12 modules** (scan
re-run 2026-10-25):

```
Algebra/FaithfulLatticeEigenvector.lean:98             Module.exists_ne_zero_forall_smul_eq_smul_of_algHom
AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean:386   AlgebraicCurve.existsUnique_pDigits_of_transcendental
AlgebraicCurve/P1/DivisorAction.lean:21                AlgebraicCurve.Place.ord_add_eq_of_lt
AlgebraicCurve/WeilExchange/Transport.lean:293         AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg
ModularCurve/Analytic/Gamma0InvariantCore.lean:116     ModularCurve.PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq
ModularCurve/Analytic/Gamma0InvariantCore.lean:133     ModularCurve.PhiGen.exists_galoisPerm
ModularCurve/Analytic/Gamma0InvariantCore.lean:153     ModularCurve.PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter
ModularCurve/Degree/Roof.lean:61                       ModularCurve.finrankAlong_heckeBetaBar
ModularCurve/Degree/Roof.lean:140                      ModularCurve.finrankAlong_towerInclBar_of_eq
ModularCurve/Degree/Roof.lean:150                      ModularCurve.finrankAlong_towerSubstBar_roof
ModularCurve/Degree/Roof.lean:220                      ModularCurve.laurentBaseChange_adjoin_pair
ModularCurve/PhiGenIntegrality.lean:232                ModularCurve.PhiGen.intCoeffs_jq_pow
ModularCurve/PhiGenPoleBounds.lean:270                 ModularCurve.PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero
ModularCurve/X1/IntegralityJqNModC.lean:99             ModularCurve.qExpansion_E6_eq_map_mk
ModularForms/Hauptmodul.lean:342                       ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty
ModularForms/JqAnalyticModel.lean:570                  ModularCurve.hasSum_jNum_qParam
WeierstrassCurve/IsogenyEndDatum/DualEndData.lean:63    WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero
```

The fix is per node a one-line `private` → public where the statement is the module's own subject, or
a lift into a subject module where it is not — plus the same `spec-pin:` wiring. Twelve of the
seventeen are the `ModularCurve` q-expansion / `PhiGen` / degree layer, so one order can take them
as a family. **Do not schedule them off `--ready`-style pricing:** the demand does not currently show
them at all (that is the bug). The batched dependent wave for these refactors is owed and recorded in
[logs/build-time-issues.md](logs/build-time-issues.md) §3b.

The **29 `twin`** hits are *not* on this list: a public declaration elsewhere already states the same
theorem under another name (the pin's `solution`/`impl` wiring, e.g. `Saturation.main`). Leave them.

## Open follow-ups

### `lean_parser.ENCLOSE_RE` swallows a bare `end` followed by `end Name` — full names key one frame too deep

**Open.** `spec/lean_parser.ENCLOSE_RE` matches an `end` and then, optionally, `\s+` plus its name; the
`\s+` crosses newlines, so

```lean
end          -- closes a section
end Foo      -- closes a namespace
```

is read as one event whose endname is the word `end`, and the `end Foo` is swallowed. Every
declaration after it is keyed one frame too deep — observed in
`AutomorphicForm/Adelic/FactorizableTestFnArchSmoothComplex.lean`, where the private twin first came
out as `…IsFactorizableTestFn.Complex.AutomorphicForm.IsFactorizableTestFn.solution`, which is why that
module's engine section is *named* (`section E8Engine`). Matching is by last name and content hash, so
no verdict is wrong today; the damage is confined to full-name keys — `spec/decl_markers.tsv` rows, the
corpus's name column, and any tool that resolves a full name. Exposure, measured 2026-10-23:
**82 adjacencies in 62 port files**, 1,662 in 1,211 pin files.

**Fix.** `\s+` → `[ \t]+` in the two name groups of `ENCLOSE_RE` (and `(?P<indent>\s*)` → `[ \t]*`).
Then rebuild the corpus — `python3 spec/statement_db.py build`; the stamp carries the parser digest, so
every cached verdict invalidates — and re-run `check_port --all` plus `--strict-markers`, expecting
0 mismatch / 0 missing / 0 stale. **Workaround until then**: name every `section` (`section Foo` /
`end Foo`), which makes both `end`s explicit.

### The AC3 engine carries the pin's engine tokens — a checker rename map, then one rename pass

**Open.** `AutomorphicForm/Adelic/ArchCompactOrbit.lean` and `ArchCutProjector.lean` (landed
2026-10-22) ship their public surface under the pin's spellings: `Ecf`, `ρc`, `QM`, `Qc`, `CA`, `CB`,
`projCA`, `goodComponents`, `cutc`, `cutM`, `underSub`, `archRep`, `ArchIsometryProd`, `ℂK`. The target
spelling is [WORKORDER-AC3](automorphicForm/WORKORDER-AC3-arch-cut-projector.md) §3; why they were
kept, and the mechanism that unblocks a rename (a `pin:`-driven rename map applied to the pin side of
the comparison before hashing), are in that order's §3 and §9. **Price**: ~20 lines in
`spec/check_port.py` plus a `--selftest` case with a renamed type inside a statement; then the
fourteen names move in one pass (79 statements, no mathematics), the `pin:` rows are re-pointed and
the two module headers updated. **Trigger**: the pass that opens these modules for another reason —
both sibling consumers (`exists_linearMap_archCutProjector`,
`exists_rightConv_eq_of_archCutProjector`) are unstarted, so the churn is at its minimum today and
grows with the first import.

### `typeSubmodule_eq_typeSpan` is one codomain short — a generic bridge at arbitrary `G`

`AutomorphicForm/Adelic/RightConvComm/SliceCentrality.lean:76` states the type-submodule ↔ type-span
dictionary for `e : H →* GL (Fin 2) (InfiniteAdeleRing F)`, but the archimedean cut lives on
`AdelicGL2 (𝓞 F) F`, so it does not apply there. `AutomorphicForm/Adelic/ArchCutProjector.lean`
(landed 2026-10-22, [WORKORDER-AC3](automorphicForm/WORKORDER-AC3-arch-cut-projector.md) §9) carries a
`private` twelve-line adapter, `typeSubmodule_eq_typeSpanOf`, at arbitrary `G` — the same proof with the
codomain generalized. The generic form (`e : H →* G`, both groups arbitrary) belongs beside
`typeSpan`/`rightRep` in `RepTheory/BiIsotypic.lean`, where the port's generic representation theory
lives; the adapter then goes. Price: an edit to an existing module, so a manager's call with
`tools/deps/build_ladder.py --edit` (twelve lines plus its wire) — **no statement of an existing module
changes**, so the checker is unaffected. Take it when a second cut consumer appears, or when
`BiIsotypic` is opened for another reason. Known not to be needed yet: `exists_rightConv_eq_of_archCutProjector`'s
pin file carries no `Qc`/`projCA`/`cutc`, so that sibling imports `ArchCompactOrbit` and not this bridge.

### The `Γ₁` slash/level toolkit has a home; the copies it replaces are still in place

`FLTForHuman/ModularForms/Level/Gamma1Slash.lean` landed 2026-10-20 as the home of the block the
pin carries as `section Level` of
`S_ModularCurve_exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0.lean`: `ΓGL`,
`restrictF`/`coe_restrictF`, `resLevel`/`coe_resLevel`, `resSL`/`coe_resSL`, `le_conj_of_SL`,
`slashForm`/`coe_slashForm`, the four property transfers `periodic_slash`,
`mdifferentiable_slash`, `bdd_slash`, `analyticAt_slash`, and the `Γ₁` facts `T_mem_Gamma1`,
`one_mem_strictPeriods`, `L_mem_strictPeriods_Gamma`, `Gamma_le_Gamma1` (18 declarations, wired to
the pin file, checker 18 ok). It is **not** a consolidation: the copies below were left in place,
because each sits inside a silo that the port transcribed whole and folding them in is a wave of
its own, to be taken when one of those modules is opened for another reason.

- `restrictF` (`restrictForm` elsewhere): **public at its pin home**,
  `ModularCurve/X1/Defs.lean:53` (+ `coe_restrictForm`, `restrictForm_apply`) — the pin's
  `Restrict` block of `Definitions/Def_ModularCurve_X1.lean`, where it belongs; `private restrictForm`
  at `WeightOne/Gamma0Integral.lean:1349`; `private restrictMF` at `Level/Degeneracy.lean:44`.
  Two private copies of a six-line `ModularForm` constructor remain.
- `T_mem_Gamma1`: public at `WeightOne/Defs/GammaRational.lean:262`,
  `Elliptic/PeriodPair/InvariantsTorsion.lean:1119`,
  `ModularCurve/X1/AtkinLehnerExchange.lean:1241`,
  `ModularForms/Eisenstein/WeightOneMultiplier.lean:645`; private at
  `ModularCurve/X1/Inputs.lean:154`, `HeckeEigenNebentypus.lean:120`.
- `one_mem_strictPeriods`: **the fact is mathlib's** — `Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem`
  for `T ∈ Γ`, and `@[simp] CongruenceSubgroup.strictPeriods_Gamma0`/`strictPeriods_Gamma1` for the
  level instances — so no home and no promotion is wanted: it is a `simp` at the call site
  ([logs/qexp-definition-layer-homes.md](logs/qexp-definition-layer-homes.md) §3). 37 copies remain
  (95 proof lines; 34 of them 1–2-line `simp`/`rw` spellings, the one real re-derivation being
  `ModularCurve/X1/FunctionField.lean:361`). A copy never earns a *promotion*; what it may keep is
  its `by simp` body. The working rule, refined: a single site writes `by simp` and no lemma; a
  `private` one-liner used twice or more in one file may stay (one elaboration in the olean instead
  of N `simp` calls, one point of repair, readable call sites) provided the body is `by simp`; a
  public copy stays only where a pin file states it, and a consumer that needs the fact should write
  `by simp` rather than import the module for it.
- `Gamma_le_Gamma1`: public at `Analytic/NormSqPow.lean:121` and `Defs/GammaRational.lean:272`;
  private at `Gamma0Integral.lean:1959` and `Gamma1IntegralBasis.lean:120`.
- `mul_inv_mem_Gamma1`: private at `X1/DiamondAut.lean:122` (the `γ 0 0` variant) and
  `Gamma0Integral.lean:1460` (the `γ 1 1` variant — the one the pin states).
- `slash_of_neg_mem`: private at `Gamma0Integral.lean:1750`.
- `coe_Eaux`: `Gamma0Integral.lean`'s copy is `private`, so `ModularForms/FrickeReciprocity.lean`
  writes its own two-line copy. That is the FR1 set's **single added twin** in the shape index
  (`shapes.py` on the landed module: 59 theorem/lemmas, one port twin, `coe_Eaux`); promote the
  host's copy in the wave that folds this block.
- `frickeConj`: now public at `ModularForms/HeckeFrickeTrace.lean`
  (`ALTraceIdentity.frickeConj`, appended 2026-10-20 at the pin's `[NeZero L]` signature, with a
  `pin:` row in `spec/decl_markers.tsv`). Two private spellings remain —
  `HeckeFricke.lean:274` (`(p) (g) (hg)`) and `HeckeNebentypusFricke.lean:80` (`(γ) (hγ)` under a
  section variable). They are the same conjugation in three spellings; unifying them means
  rewriting `HeckeFricke`'s call sites, which is not worth it for ten lines. Note when folding:
  the pin's `diagGL (t : ℝ) (ht : 0 < t)` is `Defs/HeckeOperator.heckeDiagMatrix` at a real
  parameter — if a second consumer ever needs the real form, generalise that hub rather than
  copy the pin's version again.

The same file also carries **two different `IsRat`s**: public at `Gamma0Integral.lean:1360`
(`∀ n, ∃ r : ℚ, q.coeff n = (r : ℂ)`, the pin's) and private at `:359`
(`∃ p : PowerSeries ℚ, p.map (algebraMap ℚ ℂ) = φ`). They are equivalent but not defeq, and a
consumer that opens the wrong namespace proves against the wrong predicate.

### Two promotion candidates the Gauss-prolongation set left `private`

Both are in `X1/FunctionFieldResidue.lean`'s reach but not in its surface, so the set that needed them
re-derived them `private` ([logs/qexp-regular-prolongation.md](logs/qexp-regular-prolongation.md)):

* `ModularCurve.laurentBaseChange_le` — `laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ≤
  qExpFunctionFieldC L Γ`, the pin's own 17-line lemma (`S_:301–320`), re-derived `private` in
  `X1/QExpRegularProlongation.lean`. Its home is beside `laurentBaseChange_le_adjoin_gensZ`
  (`FunctionFieldResidue.lean:264`), which is only the *`gensZ`* strengthening; the
  `intFormRatiosC`-target inclusion exists nowhere in that closure (`Degree/LaurentGlue.lean:221`
  proves the stronger equality but is not in the closure). Every future consumer of the pin's
  `exists_frac_form` re-derives it until it is promoted.
* The seven Gauss-block helpers the engine dropped and the new module carries `private`:
  `coe_LamSub` (pin:188), `resHom_apply` (:550), `ι_mem_gaussRing` (:556), `resHom_ι` (:559),
  `ker_resHom` (:594), `coe_smul'` (:636), `exists_smul_mem_gaussRing` (:640). Promote into
  `QExpDeuring` in one pass, with the usual price — they are one block, and the wave is the same
  price for one move or seven. Note when promoting: `gaussProlongation` must stay an `abbrev` (a
  plain `def` breaks the sibling assemblies' `change`/`rw` at `implicit` transparency).

### `Defs/TS.lean`'s `TS` is the `ℚ`-model — the pin has two spellings of it

The pin defines `TS` twice, and the two agree by `coeffEmb K jq = jqModC K` but not by binders:

* `S_ModularCurve_functionFieldGeneration.lean:39–101` (the port's source for `Defs/TS.lean`,
  transcribed whole) — `def TS (K) [Field K] [Algebra ℚ K] (e) [NeZero e] (u : Kˣ) :=
  qExpand K e (qTwist u (coeffEmb K jq))`;
* the `p`-torsion blocks of `S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_{charZero,
  forall_aeval_ne}.lean` (pin lines 35–42) and of `S_ModularCurve_StarBank_press.lean` — the same
  name at `[Field K]`, over `jqModC K`.

The port homes the first spelling as `ModularCurve.TS`, so a pin statement that *mentions* `TS` at
`[Field K]` cannot be transcribed at the pin's binders: `Algebra ℚ K` is not synthesizable from
`[Field K]`, and no pin copy of those statements exists over a `ℚ`-algebra. Two declarations are
affected today — `ModularCurve.phiAtSeed_TS_eval` and `phiAtSeed_TS_eval_symm` in
`ModularCurve/Degree/JqCyclotomicConjugates.lean`, both registered as `own:` rows in
`spec/decl_markers.tsv` (so `check_port` reads `21 ok + 2 own` on that module) and both stated one
hypothesis stronger. Every other `TS` fact the column needed is proved around it instead
(`coeff_jqNModC_self`, `coeff_jqNModC_of_lt`, `qTwist_pow_jqModC_injective` go through `qExpand`'s
coefficient API).

**Price and shape of the fix.** Generalise the one home: `def TS (K) [Field K] (e) [NeZero e]
(u : Kˣ) := qExpand K e (qTwist u (jqModC K))` — three `coeffEmb K jq` sites and three
`[Algebra ℚ K]` binders in the module itself — then re-state `TS_coeff_mul` and `TS_coeff_neg` at
the pin's text (`(jqModC K).coeff n` in place of `algebraMap ℚ K (jq.coeff n)`), add the module's
`spec-pin:` lines for its own pin source (`Defs/TS.lean` is in `PORT_FILES` and carries no wire
today), re-run `check_port --force` on it, and delete the two `own:` rows with the two statements
restored at `[Field K]`. The pass must also decide which of the pin's two spellings is the
statement authority and mark the other (`pin:`), because the frozen registry's ten rows were
diffed against the *first* file. **Trigger**: the next set that states a pin `TS` fact at
`[Field K]`, or the sweep that wires `Defs/TS.lean`; the dependent wave is the eight files that
state `TS`-facts over a `ℚ`-algebra (`qTwistEquiv`, `phiAtSeed_TS_eval*`, `qTwist_TS_one_cycle`,
`coeffMap_TS` call sites), priced with `build_ladder.py --edit`.

### The `mapGL` entry lemmas have no library home

`mapGL_apply`, `val_mapGL_eq`, `mapGL_injective` and `det_entries` live with their modular-forms
consumers in `FLTForHuman/ModularForms/Analytic/PeterssonCoset.lean`. The group-theory module
`GroupTheory/ModularGroup/FreeProduct` used to import that module for `det_entries` — a dependency
inversion, broken 2026-10-20 by a private local copy (the pin restates the same five lines) — and a
single library home, `LinearAlgebra/Matrix/SpecialLinearGroupMapGL.lean`, is the proper fix once
the five consumers (`Analytic/NormSqPow`, `HeckePrelude`, `SturmBound`, `Analytic/PeterssonCoset`,
and the private copies in `ModularGroup`/`Gamma1Vanishing`) are updated together. Do not move them
piecemeal: the four are general `SL(2, ℤ)`/`mapGL` facts, but moving them changes every unqualified
reference reached through `open CuspForm.PeterssonCoset`.

### The `JOneES` engine is re-derived in its three siblings

Measured 2026-10-25 with `dedup.py --module '*X1/FunctionField*' --module '*JqIntegralRatios*'`:
239 declarations in 8 modules, **11 clusters / 176 removable lines**, every one of them a copy of
the promoted `JOneES` engine in `X1/FunctionField.lean` (public there) or of a pin spelling that
lives beside it:

| cluster | tier | copies | removable |
|---|---|---|---:|
| `qExpansion_mem_monomialSpan` | name | `X1/FunctionField:281` (88 L, public) vs `X1/FunctionFieldDegree:128` (76 L, public) | 76 |
| `eq_C_of_isAlgebraic` | name | `FunctionField:108` (public) vs `FunctionFieldBaseChange:69` (private) | 33 |
| `valuation_le_one_of_isAlgebraic` | name | `:89` vs `:50` (private) | 19 |
| `transcendental_of_coeff_ne_zero` | name | `:141` (13 L) vs `:102` (21 L, private) | 13 |
| `intSeriesC_neg'` vs `FIdxLevelOne.intSeriesC_neg` | shape | `:742` vs `FunctionFieldDegree:348` | 9 |
| `valuation_algebraMap_le_one` | name | `:82` vs `:43` (private) | 7 |
| `intSeriesC_add'` vs `FIdxLevelOne.intSeriesC_add` | shape | `:737` vs `FunctionFieldDegree:343` | 5 |
| `isIntegralQExp_E4` | name | `JqIntegralRatios:63` vs `FunctionField:647` (`JOneESRat`) | 4 |
| `coeffEmb_intSeriesC` | shape | `JqIntegralRatios:173` vs `QExpDeuring` (`FunctionFieldResidue:107`) | 4 |
| `e4cube` vs `A12` | body | `JqIntegralRatios:67` vs `FunctionField:662` (`JOneESRat`) | 3 |
| `jqModC_mem` vs `jqModC_mem_rat` | shape | `FunctionFieldDegree:524` vs `FunctionFieldResidue:587` | 3 |

**Two cautions on this table.** (i) The `coeffEmb_intSeriesC` row is *not* a deletion candidate:
the two declarations have different statements — `ModularCurve.coeffEmb_intSeriesC` in
`JqIntegralRatios.lean` is the general form, `JOneES.JOneESAlg.JOneESLevelOne.JOneESNorm.JOneESRat.coeffEmb_intSeriesC`
in `X1/FunctionField.lean` is the pin's `S_`:782 `.map` form — and the latter has a qualified
consumer (`X1/QExpansionDiv.lean:461`), so deleting it breaks the build (tried and reverted
2026-10-25). What is shared is the *last component*, which is what makes an unqualified use inside
`namespace ModularCurve` resolve to the general one: qualify such a use, or unfold `intSeriesC`
(`X1/FunctionFieldDegree.lean`). (ii) The `isIntegralQExp_E4` and `e4cube`/`A12` rows are the same
shape of thing — one statement under two pin names in two namespaces — and stay.

**The row worth doing first** is the first one: `X1/FunctionFieldDegree.lean` re-derives the
76-line `monomialSpan` induction that `X1/FunctionField.lean` already carries public (its own
docstring says the promoted `JOneES*` engine is *imported*, not re-transcribed), and it re-declares
the `intSeriesC_add`/`intSeriesC_neg` pair under its own `FIdxLevelOne` names. Deleting those three
and calling the engine's — already imported in that module — removes the `FIdxLevelOne` monomial
block; its `hc`/`hQEi` rewrites then spell the engine's names. The `FunctionFieldBaseChange` rows
are `private` copies, so deleting them is free but every proof there must re-point at the engine.
The last three rows are **not** to be renamed: `JOneES.JOneESRat.*`, `FIdxLevelOne.*` and
`QExpDeuring.*` are each faithful to a different pin `S_` file and each module is diffed against
its own wire, so they are the "one statement, two pin names" case (dedup's cost-0 class).
**Trigger**: the next pass that opens `X1/FunctionFieldDegree` or `X1/FunctionFieldBaseChange`;
price the wave with `build_ladder.py --edit` after the edit.

### `AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional`

Landed at `FLTForHuman/AlgebraicCurve/IsCurveOver/EssFiniteType.lean`. Its consumer test
(`spec/AlgebraicCurveConsumer.lean`, Zone L) is hypothesis-form: the concrete witness
`F = ↥K⟮X⟯` needs the subtype coercion of `RatFunc.X` through `RatFunc.transcendental_X`'s `K⟮X⟯`
notation. The node has no ported consumer — the pin's consumers are the `essFiniteType_*` targets
— so it is a pre-payment, not a link in a chain.

### Patching `class` binder spelling

Four deviations are exempted by dotted name in the checker's `OWN_PROOFS`, all in
`FLTForHuman/Patching/PatchingConstruction.lean`:

- `IsLocalRing.IsAdicTopology` writes `(R)` where the pin
  (`Definitions/Def_Patching_SystemTypes.lean`) writes `(R : Type*)`;
- `Algebra.TopologicallyFG` and `IsPatchingSystem` spell their binders through surrounding
  `variable`s where the pin is explicit;
- `PatchingAlgebra.smulData` has no textual counterpart under that name.

The Patching effort should re-spell the three binders as the pin does and re-home or rename
`smulData`, which removes the exemptions.

### Duplicate `private` norm-formula blocks

Char-free fibre-centre norm formula, two byte-identical `private` copies:
`ord_norm_eq_sum_fiberOver` (29 lines) and `pushforwardNormFormula_of_finiteDimensional` (17
lines), at `AlgebraicCurve/PrincipalDivisors/Transcendence.lean:309`/`:345` and
`WeierstrassCurve/Velu/RestrictAlong.lean:1713`/`:1749`. They cannot be retired by pointing
`Transcendence.lean` at the public home: `Velu/RestrictAlong.lean` already reaches
`Transcendence.lean`, so that would be a cycle. Retiring them means extracting the char-free
formula into a module **below** `Transcendence.lean` and rebuilding that cone once (52-module
cascade, measured); until then both private bodies stay.

`ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal`, statement-identical `private` copies at
`AlgebraicCurve/PrincipalDivisors/Transcendence.lean:138` and
`WeierstrassCurve/Velu/RestrictAlong.lean:1547` (about `v.ord` for a curve's place, unrelated to the
DVR order). Waves are lopsided: `build_ladder.py --edit` prices the `Transcendence` side at
**81 modules / 49,336 lines ≈ 598 s** and the `RestrictAlong` side at 2 modules / 670 lines ≈ 34 s.
Cheap shape: a public home beside `ord` in `AlgebraicCurve/Defs/Place.lean` with both consumers
importing it.

`AlgebraicCurve.Place.isRational_of_deg_eq_one` is public at one FQN in two modules —
`AlgebraicCurve/P1/Dictionary.lean:59` and `WeierstrassCurve/Velu/Discharge.lean:38` — with
byte-identical bodies, so the two modules *are* co-importable (Lean merges identical declarations
silently) but the tree carries two copies. Dedup: keep the lower `P1/` copy, delete or alias the
`Velu/Discharge.lean` one. Same family: `finite_setOf_ord_ne_zero_of_finiteDimensional`
(`P1/EnginePrelude.lean:652` public vs `PrincipalDivisors/Transcendence.lean:387` private).
`Velu/Discharge.lean` is the larger cascade.

### The second-order `XYIdeal` block (`IsogenyEndDatum/DualEndData.lean`)

`DualEndData.lean` carries a generic second-order-at-a-point development:
`derivative_polynomial`, `evalEval_eq_zero_of_mem_span`, `evalEval_derivative_eq_zero_of_mem_span_sq`,
`exists_eq_add_mul_polynomial_of_mem_XYIdeal_sq`, `X_sub_C_dvd_eval_of_mem_span`,
`X_sub_C_sq_dvd_eval_of_mem_span_sq`, `XClass_notMem_XYIdeal_sq`, `ord_placeOfEquation_XClass_self`
and the `ord_ofHeightOneSpectrum_*` family (`:1134`, `:1360`, `:1387`–`:1478`). None is
`IsogenyEndDatum`-specific; the V3 node
`WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add` needs two members of it.

The current cost is `TranslationAlgEquiv.lean`'s import of `DualEndData` (1 m 21 s fixed per
`lake env lean` check, against 23.5 s for the `Engine`-only cone). Trigger for the refactor: when a
third cone needs the block, extract it to a module under `Place/` below `DualEndData` and drop that
import. Price: `build_ladder.py --edit DualEndData.lean` (5 modules / ≈119 s) plus the new home's
dependents.

### The `General`/`NoAC` engine split (`KernelBaseChange.lean`)

`KernelBaseChange.lean:133–420` is landed `General`-only — its section carries `[IsAlgClosed F]
[IsAlgClosed F']` and four `GenusOnePlaceGate`/`IsCentred`/`AbelTheorem` blocks — so it cannot be
instantiated at a subfield. The two-curve descent needs it at `F = K₀`, and therefore transcribes
the pin's `NoAC` engine `private` (≈320 lines). D-1 resolved the same split in the function-field
prelude by making the `NoAC` name the primitive and each `General` name a one-line invocation.

Refactor: restate the engine's section gate-free (`kw_surge_hgf4_bcTensorIota`,
`…bcTensorFracIota`, `…bcTensorFracIotaAlg`, `…bcIota₁`, `…bcTensorFracIotaSeam`,
`…bcIota₁_{finiteAlong,isIntegral,finrankAlong,compat}`), keep the `General` names as one-line
invocations of the gate-free ones, delete the private copies and re-point their file at the
imports. The two D-5 headline statements do not move. `KernelBaseChange.lean` is a leaf, so the
cascade should be small; price with `build_ladder.py --edit`. Do not reopen
`Isogeny/TwoCurveDescent.lean` mid-set.

Related measurement: `gateDescent_of_descent` carries the pin's
`set_option maxHeartbeats 48000000` / `synthInstance.maxHeartbeats 8000000` and ≈120 lines of
`⁄`-spelling instance/`Eq.trans` scaffolding (`S_:2882–2885`); re-measure it if the engine promotion
happens.

### Deprecated-name sweep in frozen modules

The milestone build prints deprecation warnings from frozen port modules:
`WeierstrassCurve/Velu/OrderTwo.lean:224` (`dif_neg` → `dite_eq_right`) and `:452`
(`linter.style.haveILetI` on the pinned `haveI` in `veluQuotient2_j`'s statement), plus `if_neg`/
`if_true`/`TensorProduct.induction_on`/`TensorProduction.inductionOn` in
`WeierstrassCurve/IsogenyEndDatum/DualEndData.lean` and `Isogeny/TwoCurveDescent.lean`. Lake replays
their cached logs, so they do not recompute. New modules of every set are 0-warning; the debt is in
the older ones only. Sweep a maintenance round, one file at a time, priced with
`build_ladder.py --edit`, never mid-set.

### Narrowed linter suppressions are house style

The subject-A modules carry 15 `set_option linter.* false in` suppressions (13
`unusedSectionVars`, 1 `style.haveILetI`, 1 `unusedVariables`), each on a single declaration. They
are forced: Lean auto-includes `[NeZero N]` in a signature when the *value* uses it but the *type*
does not, the linter then reports it unused, and `omit [NeZero N] in` is refused
(`cannot omit referenced section variable`). The pin sets `linter.unusedSectionVars false` /
`linter.unusedVariables false` in 7 of these 8 `S_` files
(`S_ModularCurve_LevelN_isDomain_ring.lean` excepted), and ~190 other port modules set them too. A
work order's "no `set_option linter.*` suppression" line means *no file-wide suppression and no
suppression of a real warning*; each narrowed use is recorded in the set's report.

### Tier-3 theories not in `PORT_FILES`

The completed Dedekind zeta package (`NumberField.exists_completedDedekindZeta_package`, 7,555 pin
lines / 388 public declarations, one consumed headline) is ported as a natural-named theory in
`FLTForHuman/NumberTheory/CompletedDedekindZeta/` plus a thin listed façade carrying the headline.
Its ten pin consumers and the two sibling silos that re-declare the same obligation vocabulary stay
unported by design. Order:
[topics/numberTheory/WORKORDER-Z1-completed-dedekind-zeta.md](topics/numberTheory/WORKORDER-Z1-completed-dedekind-zeta.md).

The cell-dissection / radial-region cluster
([topics/algebraicCurve/TOPIC-cell-dissection.md](topics/algebraicCurve/TOPIC-cell-dissection.md))
is ported the same way. Its pin `S_` files declare the development's lemmas public
(537 across the nine `RadialRegion` nodes, more in the `CellDissection` half); per
playbook §0.5/§4.1 they stay public and stay unwired, in per-node tier-3 engines
`AlgebraicCurve/RadialRegion/Engine/<Node>.lean` (registered with `-- pin:`
provenance), with a thin listed façade `AlgebraicCurve/RadialRegion/<Node>.lean` per
node carrying the wrapper headline. First order:
[topics/algebraicCurve/WORKORDER-R1-radial-rectangle.md](topics/algebraicCurve/WORKORDER-R1-radial-rectangle.md).

## Cleanup families

### Two pin-chapter namespaces still in use

Two modules declare under the pin's transcription-device namespaces, which name a chapter rather
than a theory:

| namespace | declared in | reference sites | consumer modules |
|---|---|---|---|
| `M4aS4` | `AdelicHaar/{AdelicModulus,PlaceMeasure}.lean` | 6 | `AutomorphicForm/Adelic/WeylIntegrable/{Assembly,LatticeEstimates,UniformBound}.lean` + the two declarers |
| `M4aLocalCFT` | `NumberField/TateGlobal/FujisakiCompact.lean` | 59 | most of the T1 `TateGlobal/*` cluster |

**Resolved 2026-11-02 (the `FltWs24` sweep, triggered by SET-AF12).** `FltWs24` →
`NumberField.AdelicHaar` in `NumberTheory/AdelicHaar/ProductFormula.lean`, with the two sub-chapter
namespaces `AdelicModulusOne` and `AdelicModulusOneChar` folded into it and the duplicate
`variable`/`local notation` pair that the merge exposed deleted. The module was **wired** on the way
(its four `S_` files as the header's `spec-pin:` lines, grandfathered `-- pin:` markers stripped,
**9 ok / 0 mismatch / 0 missing**), and its tier-1 façade `NumberTheory/AdelicModulus.lean` was handed
over to the checker (six `Theorems/` wrappers as the wire, markers stripped, **6 ok / 0 / 0**, its
`PORT_FILES` row retired — its `SOURCES` rows stay). The two `haveI` walls in the façade and the nine
in the engine were rewritten as `have` (Lean 4 registers a local instance for `have`/`let`, so no
suppression is needed anywhere) and the engine's file-wide `linter.style.haveILetI false` is gone.
The two modules are `dedup --within` 0 clusters and `move_dead` 0/0. Remaining: `M4aS4` (the
`AdelicModulus` half is 4 declarations, the `PlaceMeasure` half 29) and `M4aLocalCFT`.

Merging one into an existing theory namespace (`NumberField.AdelicHaar`, `NumberField.TateGlobal`)
is the case playbook §3.2 warns about — two chapters can hold the same declaration name with
different statements — so each rename needs a collision check before the wave, and the
`M4aLocalCFT` one is a 59-site job over a frozen cluster. Do them as their own wave when the owning
cluster is next active, keeping every last name so the checker's dotted fallback still matches.

### Tool hazards

- **`frontier.py` credits a `spec-pin:` header before the module is green.** The `sources`
  tier now reads the `spec-pin:` lines of the port tree, so a node counts as ported as soon
  as the header exists — including while the module is still half-written and does not
  compile (the `names` tier behaves the same way: a partial file already declares some
  names). Harmless for the final reading, misleading mid-wave: do not trust the frontier
  between dispatch and review, and use `check_port` as the gate.
- `spec/unwired_register.py --json` rewrites `lean/spec/UNWIRED-PUBLIC.md` unconditionally, even
  with `--json` — a read-only-looking invocation still writes the register (it is git-ignored
  now, so only the working tree is touched). Use `--check` unless the register is meant to be
  regenerated.
- Re-running `port_advise` on a pin file **after** its engine has landed reports the engine's own
  declarations as substitutions (the tool scans the whole port tree, so every transcribed
  declaration matches itself). Use the advise file generated before the module was written, or
  exclude the new module.
- The checker's `DECL_RE` admits only `private`/`noncomputable`, so a `scoped instance` is
  invisible to `raw_declarations`: `unwired_register.py` skips it (the P1 prelude registers 121 of
  its 124 declarations — `A` 68/70, `B` 53/54), and the statement checker would not diff it if its
  module were wired. The three are present, public and pinned. Teaching the tracked checker to see
  `scoped` changes the global checked surface and needs its own pass with `--selftest`; record in
  `logs/ac-port.md` §13.
- **`inductive` is invisible to the statement parser.** `DECL_RE` admits
  `def|theorem|lemma|abbrev|structure|class|instance` only, so a pin `inductive` is in neither the
  corpus nor a port module's parse: `CohCarrier.Gen` (`ModularForms/CohCarrier/Inst.lean`) is
  checked by nothing, although it is the *type* of two rows' `genOpH`/`opFamily`. Same fixing rule
  as the `scoped instance` above (a checker pass with `--selftest`, not a rider); read such a
  declaration by eye against the pin. FR-0057.
- **A `haveI`/`letI` binding in a statement's *type* truncates the diff.** `top_level_cut` looks for
  the first top-level `:=` to find where the proof starts, and an instance binding's value is such a
  `:=`: `CuspForm.coe_heckeTLinH_apply`/`coe_heckeTLinH_eq` (`ModularForms/Defs/GammaH.lean`) are
  therefore only diffed on their binder prefix. Read them by eye; a fix is the same kind of checker
  pass. FR-0056.
- The checker's `strip_comments` removes only block comments (`/- … -/`), not `--` line
  comments, while `top_level_cut` finds no `:=` in an equation-style `def` — so a `-- pin:`
  line above the *next* declaration is absorbed into an equation-style def's statement. Harmless
  today (only unlisted tier-3 engines carry per-declaration `-- pin:` comments, and the register
  does not compare statements), but a wired module with that pairing would report a spurious
  mismatch. Fixing it means stripping `--` comments in the tracked checker and re-running its
  selftest; deliberately not a rider on a set (see `logs/ac-port.md` §13).
- **Measured 2026-11-07 (SET-AF20 order C): the same `--` asymmetry mis-attributes *namespaces*.**
  `lean_parser.strip_line_comments` deletes `--` comments from the text, but the declaration offsets
  it then compares are computed on the *un-stripped* text, so every `--` comment (and every `-- pin:`
  / `-- own:` marker) shifts the `namespace`/`end` scan leftwards relative to the declarations. In a
  module with two helper namespaces of 20+ declarations each, declarations after the first several
  markers were reported under the *wrong* enclosing namespace (`…CentreUnipotent.isHaarMeasure` as
  `…TorusUnipotent.isHaarMeasure`, the last two as a bare `isHaarMeasure`). Matching survives — the
  checker keys on last name and statement hash, and `0 mismatch` was unaffected — but a `-- own:`
  marker can attach to the wrong declaration, and 7 of 8 did. **Rule: do not put `-- own:`/`-- pin:`
  markers in a multi-namespace module; write the row in `spec/decl_markers.tsv` instead** (which is
  where the markers are going anyway). Also note that `decl_markers.py` reads only a single-line
  marker placed *immediately* above the declaration (the walk stops at the first non-attribute line).

### Co-import constraint: the gate producer and `Engine`

`WeierstrassCurve/GenusOnePlaceGateCentred.lean` (the producer
`exists_genusOnePlaceGate_isCentred_and_abelTheorem`) cannot be co-imported with
`WeierstrassCurve/IsogenyEndDatum/Engine.lean` — both reach a declaration of
`WeierstrassCurve.Affine.instInfinitePlace`, and no environment holds the two. A consumer that
*produces* the gate instances and one that uses `Engine` must therefore stay in separate `spec/`
files until one instance is reconciled; the capstone
`ModularCurve/ModularPolynomialEvalJ.lean` holds both because it reaches the producer without
importing `Engine`. Rule for the column:
[topics/velu/WORKORDER-P2-basechange.md](topics/velu/WORKORDER-P2-basechange.md) §3.1.
