# Mathlib-first substitution audit — P3.3a, the Tate residue currency and `tateCommFinite`

**Method:** [`lean/porting-playbook.md`](../porting-playbook.md) §2.2 (audit the route,
mathlib first), after the phase-1/2/3.1/3.2a–3.2f templates
[`AUDIT-mathlib.md`](AUDIT-mathlib.md), [`AUDIT-mathlib-p2.md`](AUDIT-mathlib-p2.md),
[`AUDIT-mathlib-p3-1.md`](AUDIT-mathlib-p3-1.md),
[`AUDIT-mathlib-p3-2a.md`](AUDIT-mathlib-p3-2a.md) … `-p3-2e.md`, and
[`AUDIT-mathlib-p3-2f.md`](AUDIT-mathlib-p3-2f.md). Pin:
`anthropics/fermats-last-theorem@aa2d8b3` (read-only clone at `~/proj/fermats-last-theorem`);
port mathlib `v4.34.0` (`lean/.lake/packages/mathlib`). Work order target:
[`PLAN-P3-3.md`](PLAN-P3-3.md) §1–§2. Pre-port measurement: the whole-row run
[`tools/deps/build/p33_advise.log`](../../../tools/deps/build/p33_advise.log) (17 targets,
755 declarations) and its `.json` (per-declaration matches).

**Sources.** Two pin files, their homes the new
`FLTForHuman/AlgebraicCurve/Defs/TateResidueCurrency.lean` and
`FLTForHuman/AlgebraicCurve/Tate/CommFinite.lean`:

- [`Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean)
  (449 ln, 27 checked declarations) — the Tate commutator/trace vocabulary, the Kähler
  pullback/cotrace, `regularSubmodule`, the two `kwHgfV352_*` atoms, and the six
  `KwF4gRRTate*` / `KwF4R1V391a*` / `FiberKaehler*` `Prop` atoms;
- [`P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean)
  (1,257 ln, 53 checked declarations + 2 `scoped instance`s) — the finiteness discharge
  chain `clearPole → poleWindowFinite → DVRQuotPowKFinite → DVRCotangentKFinite` and the
  headline published as `AlgebraicCurve.tateCommFinite` by
  [`Theorems/Thm_AlgebraicCurve_tateCommFinite.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_tateCommFinite.lean).

**Baseline.** The classification is measured against the `port_advise` corpus as of the
`p33_advise` logs, i.e. the port *before* the two home modules land. A parallel set-3.3a
worker landed `Defs/TateResidueCurrency.lean` and `Tate/CommFinite.lean` at 18:00 while
this audit was written; following the P3.2f convention those in-flight modules are
deliberately **ignored** by the tables below, and Correction 7 plus §10 cross-check their
text against the leads. The audit was therefore written against the pre-set-3.3a port
(checker 3701 identical, per PLAN-P3-3 §1).

**Class convention** (unchanged from phases 1–3.2f). SUBSTITUTE = the port can import or
drop the row: an already-landed port declaration, a port-private declaration to promote,
or a mathlib constant whose *type* is the pin's, or a pin `def`/`abbrev` whose body is
`rfl`-equal to a mathlib/port term. GENERALISE = the port already declares the row under
the same last name at a different binder spelling; import it and do not re-declare.
KEEP/NEW splits into PROOF-INGREDIENT (bespoke statement over pin vocabulary, proof a
short assembly of named mathlib/port lemmas) and BESPOKE (a `def`/`Prop`/instance
introducing vocabulary). Because the file names are new, no row is byte-identical in the
public port; the only reusable rows are the two `Place` helpers (GENERALISE) and the
`private` def to promote.

**Scratch evidence.** A scratch file (`lean/ScratchAuditP33a.lean`, gitignored, deleted
after use) was compiled from `lean/` with

```bash
timeout 1200 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false ScratchAuditP33a.lean
```

**final run clean, exit 0** (no errors, no warnings). The probe ledger:

- **A** — the port rows confirmed present: `AlgebraicCurve.Place.{ord_nonneg_of_mem,
  mem_of_ord_nonneg, mem_iff_ord_nonneg, mem_toValuationSubring_of_ord_nonneg_alt,
  ord_nonneg_of_mem_vs, mem_vs_of_ord_nonneg, kw_ffgc_completionTrace,
  kw_ffgc_completionTraceF', maximalIdeal_eq_span_uniformizer, uniformizerSubring'''}`.
- **M** — the mathlib ledger, all present in `v4.34.0`:
  `Valuation.valuationSubring.integers`, `Valuation.Integers.{one_of_isUnit,
  isUnit_of_one', isUnit_iff_valuation_eq_one}`,
  `ValuationSubring.{valuation_eq_one_iff, valuation_unit}`,
  `Algebra.{lmul, coe_lmul_eq_mul}`, `Ring.lie_def`,
  `LinearMap.{trace, trace_lie, trace_mul_comm, trace_comp_comm',
  trace_restrict_eq_of_forall_mem}`, `Module.End.{mul_eq_comp, mul_apply}`,
  `Ideal.IsMaximal.eq_of_le`, `IsLocalRing.maximalIdeal.isMaximal`,
  `Irreducible.maximalIdeal_eq`, `IsDiscreteValuationRing.{exists_irreducible,
  eq_unit_mul_pow_irreducible}`, `Valued.{isOpen_closedBall, isOpen_valuationSubring}`,
  `Submodule.{restrictScalars, restrictScalars_mem, exists_isCompl, projectionOnto,
  projectionOnto_apply_left, quotientQuotientEquivQuotient, comapSubtypeEquivOfLe}`,
  `LinearMap.{mulLeft, mulLeft_apply, quotKerEquivRange}`, `Module.Finite.of_submodule_quotient`,
  `Ideal.{span_singleton_pow, mem_span_singleton, quotientMap, quotientEquivAlgOfEq}`,
  `RingEquiv.ofBijective`, `KaehlerDifferential.{map, map_D}`.
- **N** (recorded negatives, run in the second pass) — `IsLocalRing.maximalIdeal_le`,
  `IsDedekindDomain.HeightOneSpectrum.completionIdeal`,
  `…adicCompletion.mem_completionIdeal_pow`, `…adicCompletion.maximalIdeal_eq_span_uniformizer`,
  `…adicCompletion.exists_uniformizer` each report `unknown constant`.
- **E** — compile-checked prototypes: `KaehlerDifferential.map K K E F` at the pin's
  `kaehlerCotrace` binders and its application at `kaehlerPullback`'s;
  `(Algebra.lmul K A) fh` for `lmulK`; the bracket equality
  `` pA ∘ φ ∘ pA ∘ ψ - pA ∘ ψ ∘ pA ∘ φ = ⁅pA ∘ φ, pA ∘ ψ⁆ `` by
  `Ring.lie_def` + `Module.End.mul_apply`; `finrankTrace φ = LinearMap.trace K V φ` under
  `[FiniteDimensional K V]` by `LinearMap.trace_restrict_eq_of_forall_mem`; the three
  `ValuationSubring.*` statements discharged by `Valuation.Integers.*`; and
  `IsLocalRing.maximalIdeal_le` by `(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le`.

## 1. Summary — class counts

| file | rows | SUBSTITUTE | GENERALISE | KEEP/NEW | NEW: proof-ingredient | NEW: bespoke |
|---|---:|---:|---:|---:|---:|---:|
| `Defs/TateResidueCurrency.lean` | 27 | 5 | 0 | 22 | 6 | 16 |
| `Tate/CommFinite.lean` | 53 | 3 | 2 | 48 | 36 | 12 |
| **total** | **80** | **8** | **2** | **70** | **42** | **28** |

Plus **2 `scoped instance`s** in the `S_` file that the checker and `port_advise` do not
see (Correction 3): `kwF4R1V410a_subsingletonHeightOneSpectrumDVR` (pin 771) and
`instIsScalarTower_K_toValuationSubring_adicCompletionIntegers` (pin 1191). These must be
landed by hand.

**Headline.** The two files are, as PLAN-P3-3 §2 says, the *shared definition layer plus
one finiteness proof*. Of the 80 rows only 8 are droppable: three mathlib `Integers`
lemmas (probe M), four one-line aliases of mathlib terms (`tateComm`, `kaehlerPullback`,
`kaehlerCotrace`, `lmulK`), and one port-private declaration to promote. Two pin-private
`Place` helpers are the port's public `Defs/PushPull.lean` lemmas. The remaining 70 rows
are genuinely new — but 36 of them in `tateCommFinite` are assemblies of the ported
`Place`/`adicCompletion` dictionary and mathlib's submodule-quotient algebra, and 28 are
bespoke vocabulary atoms (`def`/`Prop`/instance) for the later sets. **The single biggest
lever is the `ValuationSubring` unit triple, which the pin proves but mathlib already
has.**

## 2. Corrections to the work order and the measurement

**Correction 1 — the `def` substitutions in `p33_advise` are false positives.** The
checker's `raw_declarations` returns a `def`'s signature without its body, so every
`def … : Prop` with the same binder block has the same normalised statement and matches
`EisensteinWeightOne.E1Chi3IsModular` (`FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean`).
Ten such rows are reported as substitutes for these two files and **all ten are NEW**:

| file | pin ln | `def` | bogus `port_name` |
|---|---:|---|---|
| `Def_…TateResidueCurrency` | 211 | `KwHgfV352R3MPGKPowBasisLocal` | `EisensteinWeightOne.E1Chi3IsModular` |
| `Def_…TateResidueCurrency` | 237 | `KwHgfV352CompletionTraceSum` | `EisensteinWeightOne.E1Chi3IsModular` |
| `Def_…TateResidueCurrency` | 300 | `KwF4gRRTateCommFinite` | `EisensteinWeightOne.E1Chi3IsModular` |
| `Def_…TateResidueCurrency` | 368 | `KwF4R1V391aResidueTraceCompletionCommute` | `EisensteinWeightOne.E1Chi3IsModular` |
| `Def_…TateResidueCurrency` | 399 | `FiberKaehlerCotraceResidueIdentityK` | `EisensteinWeightOne.E1Chi3IsModular` |
| `Def_…TateResidueCurrency` | 432 | `CotraceResidueIdentityOnFiberLocalizedK` | `EisensteinWeightOne.E1Chi3IsModular` |
| `S_…tateCommFinite` | 560 | `KwF4gRRTateClearPole` | `EisensteinWeightOne.E1Chi3IsModular` |
| `S_…tateCommFinite` | 576 | `KwF4gRRTatePoleWindowFinite` | `EisensteinWeightOne.E1Chi3IsModular` |
| `S_…tateCommFinite` | 971 | `KwF4gRRTateDVRQuotPowKFinite` | `EisensteinWeightOne.E1Chi3IsModular` |
| `S_…tateCommFinite` | 1050 | `KwF4gRRTateDVRCotangentKFinite` | `EisensteinWeightOne.E1Chi3IsModular` |

The three real port matches are `mem_of_ord_nonneg`/`ord_nonneg_of_mem` (port lemmas,
§4) and the port-private `kwHgfV352_localResidueCompletion` (§3.5). The measurement's
"0 already in the port" for both target files (drags section) is the opposite error: it
counts only the public home, and misses the two `Defs/PushPull.lean` imports.

**Correction 2 — the set has an unmeasured dependency on
`Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean`.** The `S_` file's
`kwF4R1V410a_*` block and `span_irreducible_eq_completionIdeal_pow_one` use
`IsDedekindDomain.HeightOneSpectrum.{completionIdeal, adicCompletion.exists_uniformizer,
adicCompletion.maximalIdeal_eq_span_uniformizer, adicCompletion.mem_completionIdeal_pow}`.
None of these is in mathlib `v4.34.0` (probe N) or in the port; they are pin-local,
defined in the InlineSpecific file, which is **not one of the 17 measured targets**
(`p33_advise.log` line 4 lists only the `Def_` file). The worker must either port that
API or transcribe the reached slice. The in-flight module chose the latter as seven
`private` facts plus a `private` DVR instance (`Tate/CommFinite.lean:99–212`;
Correction 7). This is the P3.3a analogue of the "scope a topic from
the pin's import graph, not its file list" caution (playbook §2.2).

**Correction 3 — the two `scoped instance`s are invisible to both tools.** The checker's
declaration list for `S_…tateCommFinite` has 53 entries and no instance; `port_advise`
likewise. `attribute`/`instance` declarations are not checked, but they must elaborate for
the quotient/cotangent block to compile. Land `kwF4R1V410a_subsingletonHeightOneSpectrumDVR`
(pin 771, `Subsingleton (HeightOneSpectrum O)` for a DVR `O`) and
`instIsScalarTower_K_toValuationSubring_adicCompletionIntegers` (pin 1191) explicitly.
This is the same omission pattern as `AUDIT-mathlib-p3-2f.md` Correction 4.

**Correction 4 — the `512`-line `Place.isPrincipalIdealRing_comap` row is not in P3.3a.**
The task brief names it as the archetype of a substituted row; in this set's measurement
it appears only in
[`S_AlgebraicCurve_residueTraceCompletionCommute.lean:391`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTraceCompletionCommute.lean#L391)
(set 3.4) and in the `tateChainRule`/`tateTraceCompat` files (3.3b/3.3d), where it is the
ported public `FLT.AlgebraicCurve.Place.isPrincipalIdealRing_comap`
(`P1/EnginePrelude.lean`). The same is true of the other big substituted row,
`kwHgfV352_localResidueCompletion_algebraMap` (132 pin ln, port `P1/DivPow.lean:704`).
Neither belongs to P3.3a's substitution count; do not fold them into this set.
Inside P3.3a the genuine "port already has it" cases are
`kwHgfV352_localResidueCompletion` (§3.5) and the two `Place` helpers (§4).

**Correction 5 — the `V →ₗ[K] V` trace/commutator block is statement-level.** The pin's
`tateComm*`/`tateRes` rows are five short theorems and four `def`s. There is no proof
cone here: `tateCommTrace` appears only in `tateRes`' *statement*, and `tateRes` only in
the `Prop` atoms. So the mathlib trace API (`LinearMap.trace_lie`, `trace_mul_comm`,
`trace_restrict_eq_of_forall_mem`) is a *statement-simplification* lead, not a
line-count win: with `[FiniteDimensional K V]` the pin's `finrankTrace φ` is
`LinearMap.trace K V φ` (§7.1), but at the pin's binders (finite-dimensionality of the
*range* only) the identity is not available, so `finrankTrace` stays.

**Correction 6 — the `p2m_*` scaffolding is not declarations.** `p2m_export`/`p2m_open`/
`p2m_reactivate` and the empty sections they bracket are pin extraction markers; the port
drops them, as the in-flight module does.

**Correction 7 — the in-flight port transcribes two of the strongest substitutes.**
At 18:00 a parallel worker landed `Defs/TateResidueCurrency.lean` (417 ln) and
`Tate/CommFinite.lean` (866 ln). It took the `Algebra.lmul` body for `lmulK`, kept the
pin's `kaehlerCotrace := KaehlerDifferential.map K K E F`, promoted
`kwHgfV352_localResidueCompletion` to the home public, and imported the two `Place`
helpers. It did **not** take the `ValuationSubring` → `Valuation.Integers` substitution:
`Tate/CommFinite.lean:52–88` re-proves the triple (~35 lines), and its header does not
mention mathlib's `Integers.isUnit_iff_valuation_eq_one`. That is the one review fix this
audit changes (§11).

## 3. SUBSTITUTE rows, with probe evidence

### 3.1 The `ValuationSubring` unit triple → `Valuation.Integers`

`S_…tateCommFinite` pin 318/329/340. Probes M and E:

| pin row | mathlib substitute | note |
|---|---|---|
| `ValuationSubring.valued_eq_one_of_isUnit` | `Valuation.Integers.one_of_isUnit (Valuation.valuationSubring.integers hv.v) hx` | `v := hv.v`, `O := hv.v.valuationSubring`; the `algebraMap` is the subtype coercion |
| `ValuationSubring.isUnit_of_valued_eq_one` | `Valuation.Integers.isUnit_of_one' (Valuation.valuationSubring.integers hv.v) hx` | same instantiation |
| `ValuationSubring.isUnit_iff_valued_eq_one` | `Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.valuationSubring.integers hv.v)` | one application gives the exact iff |

Imports: `Mathlib.RingTheory.Valuation.Integers` (for
`Valuation.Integers.isUnit_iff_valuation_eq_one`, `Mathlib/RingTheory/Valuation/Integers.lean:160`)
and `Mathlib.RingTheory.Valuation.ValuationSubring` (for
`Valuation.valuationSubring.integers`, `…/ValuationSubring.lean:469`). Both are reachable
through the file's existing `Mathlib` import. There is also the `adicCompletionIntegers`
specialisation `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one`
(`Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:1006`), but the pin's statement is
at the general `Valued`/`valuationSubring` binders, so the `Integers` form is the right
one. Drop all three pin lemmas.

### 3.2 `kaehlerCotrace` and `kaehlerPullback` → `KaehlerDifferential.map`

`Def_…TateResidueCurrency` pin 157 and 102. Probe E compiles
`KaehlerDifferential.map K K E F : Ω[E⁄K] →ₗ[E] Ω[F⁄K]` at the pin's binders, and its
application at `kaehlerPullback`'s `ωE : Ω[E⁄K]`. So:

- `kaehlerCotrace (K E F)` — drop the `abbrev`; use `KaehlerDifferential.map K K E F`
  directly (`Mathlib/RingTheory/Kaehler/Basic.lean`; the pin gives the same instance
  wall, `[IsScalarTower K E F]` supplies `SMulCommClass`).
- `kaehlerPullback (ωE)` — keep as a one-line `def`/`abbrev` body
  `KaehlerDifferential.map K K E F ωE`, or eliminate it and write the map application at
  the call sites. Its body carries no proof.

The pin uses both names pervasively in 3.3b–3.4, so keeping the names as `abbrev`s is the
low-churn choice; the point is that no mathematics is transcribed.

### 3.3 `lmulK` → `Algebra.lmul`

`Def_…TateResidueCurrency` pin 286. `Algebra.lmul K u.adicCompletion : u.adicCompletion →ₐ[K] Module.End K u.adicCompletion`
(`Mathlib/Algebra/Algebra/Bilinear.lean:143`), so
`lmulK u fh = (Algebra.lmul K u.adicCompletion) fh` by `rfl` (probe E). The in-flight port
already writes exactly this body.

### 3.4 `tateComm` is mathlib's ring bracket

`Def_…TateResidueCurrency` pin 38. `Ring.lie_def` plus `Module.End.mul_eq_comp` gives
`` pA ∘ φ ∘ pA ∘ ψ - pA ∘ ψ ∘ pA ∘ φ = ⁅pA ∘ φ, pA ∘ ψ⁆ `` (probe E, closed by
`Ring.lie_def`, `Module.End.mul_apply`, `LinearMap.{sub_apply, comp_apply}`). The `def`
can therefore be a one-line bracket alias, and the trace-algebra inputs become mathlib's
`LinearMap.{trace_lie, trace_mul_comm, trace_comp_comm'}`. `tateComm_antisymm` is the
one-line `unfold tateComm; rw [neg_sub]`, or `neg_sub` after the unfold: note that
`lie_skew`/`LieRing.neg_lie` do **not** apply at `Module.End K V`, since
`LieRing.ofAssociativeRing` is only a `[local instance 100]`
(`Mathlib/Algebra/Lie/OfAssociative.lean:66`) — recorded negative §10.3.

### 3.5 `kwHgfV352_localResidueCompletion` — promote the port-private copy

`Def_…TateResidueCurrency` pin 185. The port already has this declaration `private` in
`FLTForHuman/AlgebraicCurve/P1/DivPow.lean:683` (re-landed verbatim for the 3.2f tail,
with `_spec` at `:687` and `_algebraMap` at `:704`), and the advice log flags it
"only as a port-private declaration: promote or move to a home". The home is
`Defs/TateResidueCurrency.lean`, where the in-flight port did land a public copy. The
promotion should also delete the `P1/DivPow.lean` private copy (and point 3.2f's
consumers at the home) so the declaration exists once. `_spec`/`_algebraMap` are not
needed by P3.3a itself but are the same promotion debt for 3.4 — the port's
`_algebraMap` at `P1/DivPow.lean:704` is already the advice-matched twin of the 132-line
row in `S_AlgebraicCurve_residueTraceCompletionCommute.lean:921`.

## 4. GENERALISE rows

Two pin-private section-local lemmas in `S_…tateCommFinite` are the port's public
`AlgebraicCurve.Place` lemmas; import them and do not re-declare (a re-declaration at the
same last name under `AlgebraicCurve.Place` is a hard "already declared" error).

| pin ln | name | port `module:line` | adaptation |
|---:|---|---|---|
| 258 | `Place.ord_nonneg_of_mem` | `Defs/PushPull.lean:43` | the pin's section variables `{K F} [Field K] [Field F] [Algebra K F] (v : Place K F)` are exactly the port's explicit binders; `#check` confirms the same type (probe A) |
| 273 | `Place.mem_of_ord_nonneg` | `Defs/PushPull.lean:60` | same; `Place.mem_toValuationSubring_of_ord_nonneg_alt` (`Defs/PlaceEvaluationAlgebra.lean:34`) is the alt-spelling twin `port_advise` matched |

The in-flight module's header records both imports (§Correction 7) — this part is right.
`Place.mem_iff_ord_nonneg` (`Defs/PushPull.lean:69`) is not needed by P3.3a but is the
same family.

## 5. KEEP/NEW — `Defs/TateResidueCurrency.lean` (27 rows)

Pin line numbers are into
[`Def_AlgebraicCurve_TateResidueCurrency.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean).
`PI` = proof-ingredient, `B` = bespoke.

| pin ln | name | class | disposition / route |
|---:|---|---|---|
| 28 | `ModularCurve.KwF4gRRTate.finrankTrace` | NEW B | `LinearMap.trace K (LinearMap.range φ) (φ.restrict _)`; keep at pin binders (Correction 5); under `[FiniteDimensional K V]` it is `LinearMap.trace K V φ` (probe E) |
| 38 | `tateComm` | SUBSTITUTE | body `⁅pA ∘ₗ φ, pA ∘ₗ ψ⁆` via `Ring.lie_def` (§3.4) |
| 41 | `tateComm_apply` | NEW PI | `rfl` |
| 44 | `tateComm_mem_range` | NEW PI | `sub_mem` + `LinearMap.mem_range_self` |
| 48 | `tateComm_antisymm` | NEW PI | `unfold; rw [neg_sub]`; not `lie_skew` (§3.4, §10.3) |
| 52 | `tateCommRestrict` | NEW B | `(tateComm pA φ ψ).restrict (fun x _ => tateComm_mem_range …)` |
| 56 | `tateCommRestrict_apply` | NEW PI | `rfl` |
| 59 | `tateCommTrace` | NEW B | `finrankTrace (tateCommRestrict pA φ ψ)` |
| 69 | `tateComm_eq_of_commute` | NEW PI | `map_sub` × 4, `abel`; pin-private factoring identity |
| 102 | `kaehlerPullback` | SUBSTITUTE | one-line `KaehlerDifferential.map K K E F ωE` (§3.2) |
| 129 | `Place.regularSubmodule` | NEW B | carrier `{f | f * w.differentialCoeff ωF ∈ w.toValuationSubring}`; `zero_mem`, `add_mem`, `mul_mem` + `w.algebraMap_mem'` |
| 157 | `kaehlerCotrace` | SUBSTITUTE | exactly `KaehlerDifferential.map K K E F` (§3.2) |
| 185 | `kwHgfV352_localResidueCompletion` | SUBSTITUTE (port) | promote `P1/DivPow.lean:683` (§3.5) |
| 197 | `kwHgfV352_completionTraceAt` | NEW PI | `Place.mem_fiber.mp hw' ▸ Place.kw_ffgc_completionTraceF' E w' g` (`Defs/PlaceCompletion.lean:439`) |
| 211 | `KwHgfV352R3MPGKPowBasisLocal` | NEW B | `def : Prop`, the local pow-basis atom of the 3.3d/3.4 chain |
| 237 | `KwHgfV352CompletionTraceSum` | NEW B | `def : Prop`; `Algebra.trace E F` vs the `Finset.sum` over `v.fiber F` |
| 263 | `adicIntegersKSubmod` | NEW B | `Submodule K u.adicCompletion` on `u.adicCompletionIntegers`; no mathlib `Subring → Submodule` coercion exists (§10.4), but the port's `instAlgebraKAdicCompletionIntegers` (`Defs/PlaceCompletion.lean:544`) makes the `smul_mem'` two lines |
| 274 | `tateProj` | NEW B | `Classical.choose (Submodule.exists_isCompl …)` with `Submodule.projectionOnto`; mathlib `Submodule.exists_isCompl` needs `[DivisionRing K]` ✓ |
| 286 | `lmulK` | SUBSTITUTE | `Algebra.lmul K u.adicCompletion` (§3.3) |
| 289 | `tateRes` | NEW B | `tateCommTrace (tateProj u) (lmulK u fh) (lmulK u gh)` |
| 300 | `KwF4gRRTateCommFinite` | NEW B | the headline statement atom; consumed by 3.3b–3.4 |
| 307 | `KwF4gRRTateAgreement` | NEW B | consumes `KwF4gRRTateCommFinite` and `kwHgfV352_localResidueCompletion` |
| 317 | `KwF4gRRTateChainRule` | NEW B | statement atom |
| 331 | `KwF4gRRTateTraceCompat` | NEW B | statement atom |
| 368 | `KwF4R1V391aResidueTraceCompletionCommute` | NEW B | statement atom (3.4) |
| 399 | `FiberKaehlerCotraceResidueIdentityK` | NEW B | statement atom (3.4) |
| 432 | `CotraceResidueIdentityOnFiberLocalizedK` | NEW B | statement atom (3.4), uses `Place.regularSubmodule` |

## 6. KEEP/NEW — `Tate/CommFinite.lean` (53 rows + 2 instances)

Pin line numbers are into
[`S_AlgebraicCurve_tateCommFinite.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean).

| pin ln | name | class | disposition / route |
|---:|---|---|---|
| 102 | `IsLocalRing.maximalIdeal_le` | NEW PI | no mathlib name (probe N); one line `(IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ …` (`Ideal.IsMaximal.eq_of_le`, `Mathlib/RingTheory/Ideal/Maximal.lean:65`); probe E |
| 258 | `Place.ord_nonneg_of_mem` | GENERALISE | import `Defs/PushPull.lean:43` (§4) |
| 273 | `Place.mem_of_ord_nonneg` | GENERALISE | import `Defs/PushPull.lean:60` (§4) |
| 318 | `ValuationSubring.valued_eq_one_of_isUnit` | SUBSTITUTE | `Valuation.Integers.one_of_isUnit` (§3.1) |
| 329 | `ValuationSubring.isUnit_of_valued_eq_one` | SUBSTITUTE | `Valuation.Integers.isUnit_of_one'` (§3.1) |
| 340 | `ValuationSubring.isUnit_iff_valued_eq_one` | SUBSTITUTE | `Valuation.Integers.isUnit_iff_valuation_eq_one` (§3.1) |
| 432 | `mem_adicIntegersKSubmod_iff` | NEW PI | `Iff.rfl` |
| 435 | `tateProj_mem_integers` | NEW PI | `Submodule.coe_mem` + `Submodule.projectionOnto`; `Submodule.projectionOnto_apply_left` |
| 442 | `tateProj_of_mem` | NEW PI | `Submodule.projectionOnto_apply_left` + `Subtype.val` congruence |
| 450 | `range_tateProj` | NEW PI | `le_antisymm` with rows 435/442 |
| 508 | `poleWindowKSubmod` | NEW B | `Submodule K u.adicCompletion`, carrier `(πh)^M * x ∈ u.adicCompletionIntegers` |
| 520 | `mem_poleWindowKSubmod_iff` | NEW PI | `Iff.rfl` |
| 525 | `adicIntegersKSubmod_le_poleWindowKSubmod` | NEW PI | `mul_mem (pow_mem πh.2 M)` |
| 529 | `kwF4gRRTate_clearPole` | NEW PI | `IsFractionRing.div_surjective` + `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` (probe M) |
| 560 | `KwF4gRRTateClearPole` | NEW B | `def : Prop` |
| 565 | `kwF4gRRTate_clearPole_discharged` | NEW PI | one line from row 529 |
| 568 | `lmul_mem_poleWindow` | NEW PI | `mem_poleWindowKSubmod_iff`, `mul_assoc`, `mul_mem` |
| 576 | `KwF4gRRTatePoleWindowFinite` | NEW B | `def : Prop` |
| 583 | `ker_tateProj_inf_integers` | NEW PI | `eq_bot_iff`, `Submodule.mem_inf`, `tateProj_of_mem` |
| 591 | `finiteDimensional_ker_inf_poleWindow` | NEW PI | `FiniteDimensional.of_injective` of `A'.mkQ ∘ inclusion`, `ker_tateProj_inf_integers`; mathlib `Submodule.finiteDimensional_of_le` |
| 616 | `finiteDimensional_principalPart_range` | NEW PI | row 591 + `Submodule.finiteDimensional_of_le`; `IsDiscreteValuationRing.exists_irreducible` |
| 635 | `tateComm_target_le_range` | NEW PI | `sup_le` + `LinearMap.mem_range_self` |
| 641 | `kwF4gRRTate_commFinite_of_clearPole_of_poleWindowFinite` | NEW PI | the main assembly: `Module.Finite.map`, `Submodule.finiteDimensional_sup`, `Submodule.comapSubtypeEquivOfLe`, `range_tateProj`, `tateComm_eq_of_commute` |
| 678 | `kwF4gRRTate_commFinite_of_poleWindowFinite` | NEW PI | one line from rows 565/641 |
| 718 | `adicCompletion.isOpen_setOf_valued_le` | NEW PI | `Valued.isOpen_closedBall` (`Mathlib/Topology/Algebra/Valued/ValuationTopology.lean:255`), `valuedAdicCompletion_surjective`, `Valuation.{restrict_eq_zero_iff, restrict_le_iff}` |
| 787 | `kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff` | NEW PI | needs the InlineSpecific `adicCompletion.mem_completionIdeal_pow` (Correction 2); plus `valuedAdicCompletion_eq_valuation'`, `valuation_of_algebraMap`, `intValuation_le_pow_iff_mem`, `WithZero.exp_eq_coe_ofAdd` |
| 798 | `kwF4R1V410a_exists_sub_mem_completionIdeal_pow` | NEW PI | row 718, `denseRange_algebraMap`, `mem_integers_of_valuation_le_one`, `Valuation.map_add`, `adicCompletion.mem_completionIdeal_pow` |
| 841 | `kwF4R1V410a_quotientEquiv` | NEW B | `RingEquiv.ofBijective (Ideal.quotientMap …)`: `Ideal.quotientMap_injective'`, `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.mk_eq_mk_iff_sub_mem` |
| 857 | `kwF4R1V410a_quotientEquiv_mk` | NEW PI | `rfl` |
| 898 | `coe_smul_K` | NEW PI | `Algebra.smul_def` twice + `rfl` |
| 903 | `poleWindowShift` | NEW B | `LinearMap` into `u.adicCompletionIntegers` |
| 914 | `poleWindowShift_injective` | NEW PI | `LinearMap.ker_eq_bot`, `pow_ne_zero`, `mul_eq_zero` |
| 928 | `poleWindowShift_surjective` | NEW PI | `mul_div_cancel₀`, `pow_ne_zero` |
| 941 | `poleWindowShiftEquiv` | NEW B | `LinearEquiv.ofBijective` |
| 946 | `piPowKSubmod` | NEW B | `Submodule K u.adicCompletionIntegers`, carrier `πh^M * x` |
| 955 | `poleWindowShift_image_integers` | NEW PI | `Submodule.map` extensionality + `Subtype.ext` |
| 971 | `KwF4gRRTateDVRQuotPowKFinite` | NEW B | `def : Prop` |
| 976 | `kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite` | NEW PI | `Submodule.Quotient.equiv` + `FiniteDimensional.of_injective` |
| 990 | `kwF4gRRTate_commFinite_of_DVRQuotPowKFinite` | NEW PI | rows 678/976 |
| 1035 | `piPowKSubmod_eq_restrictScalars` | NEW PI | `Ideal.mem_span_singleton`, `Submodule.restrictScalars_mem` |
| 1042 | `quotPiPowEquivIdealQuot` | NEW B | `Submodule.quotEquivOfEq` + `Submodule.Quotient.restrictScalarsEquiv` |
| 1050 | `KwF4gRRTateDVRCotangentKFinite` | NEW B | `def : Prop` |
| 1055 | `range_mulLeft_eq_restrictScalars_span` | NEW PI | `LinearMap.mulLeft` (`Mathlib/Algebra/Module/LinearMap/Defs.lean:1019`), `Ideal.mem_span_singleton`; no mathlib name for this equality (§10.5) |
| 1065 | `finiteDimensional_restrictScalarsQuot_pow` | NEW PI | induction on `M`; `Ideal.span_singleton_le_span_singleton`, `Submodule.restrictScalars_mono`, `Submodule.quotientQuotientEquivQuotient`, `LinearMap.quotKerEquivRange`, `Module.Finite.of_submodule_quotient`, `LinearMap.{range_comp, ker_comp}` |
| 1131 | `finiteDimensional_idealQuot_pow` | NEW PI | row 1065 + `Submodule.Quotient.restrictScalarsEquiv` |
| 1139 | `kwF4gRRTate_DVRQuotPowKFinite_of_cotangent` | NEW PI | rows 1042/1131 |
| 1146 | `kwF4gRRTate_commFinite_of_cotangent` | NEW PI | rows 990/1139 |
| 1200 | `span_irreducible_eq_completionIdeal_pow_one` | NEW PI | `pow_one` + `Irreducible.maximalIdeal_eq` (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:98`) with `completionIdeal = IsLocalRing.maximalIdeal _` (Correction 2) |
| 1206 | `quotientEquivKAlg` | NEW B | row 841 plus `commutes'`; `Ideal.Quotient.algebraMap_eq`, `IsScalarTower.algebraMap_apply` |
| 1220 | `quotSpanIrreducibleEquivResidueField` | NEW B | row 1200/1206 + `Ideal.quotientEquivAlgOfEq` |
| 1229 | `kwF4gRRTate_DVRCotangentKFinite` | NEW PI | row 1220 + `FiniteResidue.finite` + `Module.Finite.equiv` |
| 1234 | `kwF4gRRTate_commFinite` | NEW PI | row 1146 + row 1229 |
| 1254 | `solution` → `AlgebraicCurve.tateCommFinite` | NEW PI | the wrapper's public name; one application of row 1234 |
| 771 | `kwF4R1V410a_subsingletonHeightOneSpectrumDVR` | NEW B (instance) | checker-invisible (Correction 3); `IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime`, `HeightOneSpectrum.ext` |
| 1191 | `instIsScalarTower_K_toValuationSubring_adicCompletionIntegers` | NEW B (instance) | checker-invisible; `IsScalarTower.of_algebraMap_eq` + `Subtype.ext` |

## 7. Reuse wins and route options

### 7.1 The trace/commutator algebra is mathlib's (Correction 5)

`tateComm` is the ring bracket (§3.4), so `LinearMap.trace_lie`
(`Mathlib/LinearAlgebra/Trace.lean:132`) and `LinearMap.trace_mul_comm` (`:103`) are the
available trace inputs, and `LinearMap.trace_restrict_eq_of_forall_mem`
(`Mathlib/LinearAlgebra/PID.lean:35`) is the only route to collapsing `finrankTrace`:
under `[FiniteDimensional K V]`, `finrankTrace φ = LinearMap.trace K V φ` (probe E). The
pin's `KwF4gRRTateCommFinite` asserts only that the *range* of the restricted commutator
is finite-dimensional, so the port cannot change `finrankTrace`'s binders without also
strengthening the five `Prop` atoms; do not. Record the identity as an available
simplification for any consumer that has `[FiniteDimensional K V]`.

### 7.2 The adic-completion block is the pin's own API, not mathlib's (Correction 2)

Everything from pin 787 to 1234 is the port's `Place`/`adicCompletion` dictionary plus
mathlib's submodule-quotient algebra. No mathlib declaration replaces
`kwF4R1V410a_quotientEquiv`, `quotientEquivKAlg` or
`quotSpanIrreducibleEquivResidueField`; the `completionIdeal`-power API they use is
pin-local. The right home for the seven InlineSpecific facts is a promoted
`Place/Completion.lean` (the in-flight module's stated promotion debt), not a private
block in `Tate/CommFinite.lean`.

### 7.3 The residue-completion vocabulary is already ported

`kwHgfV352_{valued_algebraMap_adicCompletion, algebraMap_mem_adicCompletionIntegers_iff,
exists_sub_mem_adicCompletionIntegers}` (`Defs/PlaceCompletion.lean:467/481/499`),
`Place.kw_ffgc_completionTraceF'` (`:439`) and `instAlgebraKAdicCompletionIntegers`
(`:544`) cover every `kwHgfV352_*`/completion leaf the two files need; do not re-prove
them. `kwF4gRRTate_clearPole` and `kwF4R1V410a_exists_sub_mem_completionIdeal_pow` are
the only two places that rebuild a completion argument.

### 7.4 The Prop-valued `def` atoms are interface, not work

The thirteen `Prop`-valued `def`s (nine in the `Def_` file, four in the `S_` file, and in
the `Def_` file three of them `KwF4gRRTate{Agreement, ChainRule, TraceCompat}` take a
`hfin` argument) are the shared statement surface for 3.3b–3.4; port them verbatim, once,
in the `Defs` home (PLAN-P3-3 §2). The `S_` file must import them rather than re-declare.

### 7.5 Route options

- **R1 — take the eight substitutes; keep the 70 new rows as written.** The only
  non-cosmetic one is the `ValuationSubring` triple (§3.1).
- **R2 — do not attempt to drop `finrankTrace` at the pin's binders.** The range-only
  finiteness hypothesis is deliberate (Correction 5); the ambient-finiteness identity is
  an optional consumer-side simplification.
- **R3 — land the two `scoped instance`s explicitly** (Correction 3); neither tool sees
  them.
- **R4 — do not put the InlineSpecific `completionIdeal` chain in `Tate/CommFinite.lean`.**
  If it is transcribed at all, it belongs in the completion home; the in-flight module
  made it `private` and recorded the debt, which is acceptable for the set but must not
  propagate to 3.3b–3.4.
- **R5 — import, do not re-state, `Place.ord_nonneg_of_mem`/`Place.mem_of_ord_nonneg`.**
  A local re-declaration collides on the global last name.

## 8. API drift (`v4.34.0`) — what the worker must change

| pin call / assumption | `v4.34.0` status | worker action |
|---|---|---|
| `ValuationSubring.{valued_eq_one_of_isUnit, isUnit_of_valued_eq_one, isUnit_iff_valued_eq_one}` (pin 318/329/340) | mathlib has the general `Valuation.Integers.{one_of_isUnit, isUnit_of_one', isUnit_iff_valuation_eq_one}` + `Valuation.valuationSubring.integers` (probe M) | drop the three; apply the `Integers` lemmas at `v := hv.v`, `O := hv.v.valuationSubring` |
| `Valued.v x.val` vs `ValuationSubring.valuation x` | both exist; `A.valuation x = v x.val` for `A = v.valuationSubring` | the `Integers` form avoids the spelling mismatch entirely |
| `IsLocalRing.maximalIdeal_le` (pin 102) | **not in mathlib** (probe N); `Ideal.IsMaximal.eq_of_le` is (`Mathlib/RingTheory/Ideal/Maximal.lean:65`) | keep the one-line new lemma |
| `IsDedekindDomain.HeightOneSpectrum.completionIdeal` (pin 299 of the InlineSpecific file) | **not in mathlib** (probe N); it is the pin's `abbrev … := IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)` | spell the term, or land the abbrev in the completion home |
| `…adicCompletion.mem_completionIdeal_pow`, `…maximalIdeal_eq_span_uniformizer`, `…exists_uniformizer` | **not in mathlib** (probe N) | port the reached slice (Correction 2) |
| `Irreducible.maximalIdeal_eq` (pin 1204) | present (`Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:98`) | no change |
| `IsDiscreteValuationRing.{exists_irreducible, eq_unit_mul_pow_irreducible}` (pin 261/263/535) | present (probe M) | no change |
| `LinearMap.mulLeft`/`mulLeft_apply` (pin 1056/1059) | present (`Mathlib/Algebra/Module/LinearMap/Defs.lean:1019/1024`) | no change; no mathlib lemma for `range (mulLeft …) = span …` |
| `Submodule.{quotEquivOfEq, Quotient.restrictScalarsEquiv, quotientQuotientEquivQuotient, comapSubtypeEquivOfLe, exists_isCompl, projectionOnto, projectionOnto_apply_left}` | all present (probe M) | keep the camelCase names |
| `Valued.isOpen_closedBall` (pin 719/730) | present (`Mathlib/Topology/Algebra/Valued/ValuationTopology.lean:255`); requires `r ≠ 0` | no change; `Valued.isOpen_valuationSubring` is the port's route for `exists_sub_mem` |
| `KaehlerDifferential.map`/`map_D` (pin 103/158) | present (`Mathlib/RingTheory/Kaehler/Basic.lean`) | use directly for `kaehlerCotrace`/`kaehlerPullback` |
| `Ring.lie_def`, `Module.End.mul_eq_comp`, `LinearMap.trace_lie` | present (probe M) | the bracket-alias route for `tateComm` |
| pin `p2m_export`/`p2m_open`/`p2m_reactivate` scaffolding | not declarations | drop |
| pin `scoped instance`s | invisible to `port_advise`/checker (Correction 3) | land explicitly |
| pin `maxHeartbeats 6400000/12800000` raises | project cap 4,000,000 | the two quotient steps are the risk (in-flight module's note); raise locally only if needed |

## 9. Recorded negatives

Confirmed against mathlib `v4.34.0` and the port; phrased so the search is not repeated.

1. **No `tateComm`, `tateProj`, `tateRes`, `finrankTrace`, `adicIntegersKSubmod`,
   `kaehlerPullback`, `kaehlerCotrace`, `regularSubmodule`, `KwHgfV352*`, `KwF4gRRTate*`,
   `poleWindowKSubmod`, `piPowKSubmod`, `kwF4R1V410a_*`, `kwF4gRRTate_*`,
   `quotSpanIrreducibleEquivResidueField` or `quotientEquivKAlg` in the pre-3.3a port.**
   Greps over `FLTForHuman/` return only the comment/namespace mentions in
   `P1/DivPow.lean:16`, `Defs/PlaceCompletion.lean:10/526` and the `Tate/` module landed
   at 18:00. These are the 70 new rows.
2. **No mathlib declaration replaces the new rows.** Every new name is either a
   pin-specific `def`/`Prop` or a statement over `Place`/`adicCompletion` vocabulary; the
   mathlib leaves are proof ingredients only (probe M).
3. **`lie_skew`/`LieRing.neg_lie` are not usable at `Module.End K V`.** The commutator
   `LieRing` instance `LieRing.ofAssociativeRing` is a `[local instance 100]`
   (`Mathlib/Algebra/Lie/OfAssociative.lean:66`), not global, so
   `tateComm_antisymm` stays a one-line `neg_sub`. Do not search for a `LieAlgebra (Module.End K V)`
   instance.
4. **There is no `Subring`/`ValuationSubring` to `Submodule` coercion** (a name search
   finds no `Subring.toSubmodule`; `Mathlib/` has only `Subalgebra.toSubmodule` and
   the bimodule/Lie variants). So `adicIntegersKSubmod` is a genuine `def`, not
   `Submodule.restrictScalars` of the completion integers. The port's
   `instAlgebraKAdicCompletionIntegers` only shortens its `smul_mem'`.
5. **No mathlib lemma gives `LinearMap.range (LinearMap.mulLeft K a) = (Ideal.span {a}).restrictScalars K`**
   (`range_mulLeft_eq_restrictScalars_span`, pin 1055). The proof is
   `LinearMap.mem_range` + `Ideal.mem_span_singleton` + `Submodule.restrictScalars_mem`.
6. **No mathlib `IsOpen {y | Valued.v y ≤ γ}` lemma.** The pin's
   `adicCompletion.isOpen_setOf_valued_le` (pin 718) is a bespoke rewrite to
   `Valued.isOpen_closedBall` + `valuedAdicCompletion_surjective`.
7. **The `completionIdeal`-power API is not mathlib's.** `completionIdeal` is an
   InlineSpecific `abbrev` of `IsLocalRing.maximalIdeal`; `mem_completionIdeal_pow`,
   `maximalIdeal_eq_span_uniformizer` and `exists_uniformizer` at the completion integers
   are pin-local (Correction 2).
8. **The `def : Prop` "substitutions" are all false positives** (Correction 1); the checker
   cannot see `def` bodies and `EisensteinWeightOne.E1Chi3IsModular` is the attractor.
9. **The 512-line `Place.isPrincipalIdealRing_comap` substitute is out of this set**
   (Correction 4); so is `kwHgfV352_localResidueCompletion_algebraMap` (132 ln). Their
   port homes are `P1/EnginePrelude.lean` and `P1/DivPow.lean:704`.

## 10. What this changes for the P3.3a review

**Scope / measurement.**

- Corrected counts: **8 SUBSTITUTE / 2 GENERALISE / 70 KEEP-NEW** over 80 checked
  declarations, plus **2 checker-invisible instances** (Corrections 1, 3). The
  `p33_advise` "10 substitute defs" for these files are false positives.
- The set is larger than its 27 + 53 rows: it depends on the unmeasured
  `Def_DedekindDomain_AdicValuation_InlineSpecific.lean` slice (Correction 2). Budget the
  seven facts (`completionIdeal`, `exists_uniformizer`, `uniformizer_ne_zero`,
  `uniformizer_not_isUnit`, `eq_pow_uniformizer_mul_unit`,
  `maximalIdeal_eq_span_uniformizer`, `mem_completionIdeal_pow`) plus the DVR instance
  `instIsDiscreteValuationRingAdicCompletionIntegers` as part of 3.3a, or promote
  them to a shared completion home once.

**Discharged rows (mark import-discharged; the statements still land in `SOURCES`).**

- `S_…tateCommFinite` 258/273 — `Defs/PushPull.lean:43/60`.
- `S_…tateCommFinite` 318/329/340 — `Valuation.Integers.*` (no new declaration).
- `Def_…TateResidueCurrency` 157/102/286/38 — mathlib terms (`KaehlerDifferential.map`,
  `Algebra.lmul`, the ring bracket); keep the names only as one-line `abbrev`/`def`s if
  the later sets need them.
- `Def_…TateResidueCurrency` 185 — promote `P1/DivPow.lean:683` and delete the private copy.

**Review fix for the in-flight module (Correction 7).**

- Replace `Tate/CommFinite.lean:52–88` (`ValuationSubring.{valued_eq_one_of_isUnit,
  isUnit_of_valued_eq_one, isUnit_iff_valued_eq_one}`) with the three `Valuation.Integers`
  one-liners. This is the single substantive change the audit makes to the landed text.
- Confirm the two `scoped instance`s are present and elaborating (the header should say so).
- Record the `completionIdeal` chain as promotion debt with a named future home, not a
  permanent `private` block in a proof module.

**Checker wiring.** `SOURCES` does not yet list
`Theorems/Thm_AlgebraicCurve_tateCommFinite.lean` or
`P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean`; `PORT_FILES` does not yet list
`Defs/TateResidueCurrency.lean` or `Tate/CommFinite.lean`. Append them as the work order
says (wrappers first, then `S_`/`Def_`; homes appended last). The checker keys by last
name across all source candidates, so the two `Place` imports cannot flip an existing row
to `MISMATCH`.

## 11. Appendix — module map for the named constants

| name | home |
|---|---|
| `Place.ord_nonneg_of_mem`, `Place.mem_of_ord_nonneg`, `Place.mem_iff_ord_nonneg` | `FLTForHuman/AlgebraicCurve/Defs/PushPull.lean:43/60/69` |
| `Place.mem_toValuationSubring_of_ord_nonneg_alt`, `Place.ord_nonneg_of_mem_vs` | `…/Defs/PlaceEvaluationAlgebra.lean:34`, `…/Canonical/WeilDifferential.lean:57` |
| `kwHgfV352_{valued_algebraMap_adicCompletion, algebraMap_mem_adicCompletionIntegers_iff, exists_sub_mem_adicCompletionIntegers}` | `…/Defs/PlaceCompletion.lean:467/481/499` |
| `Place.kw_ffgc_completionTrace{F',}` | `…/Defs/PlaceCompletion.lean:435/439` |
| `instAlgebraKAdicCompletionIntegers`, `algebraMapKIntegers`, `algebraMap_K_mem_adicCompletionIntegers` | `…/Defs/PlaceCompletion.lean:544/537/532` |
| `kwHgfV352_localResidueCompletion{, _spec, _algebraMap}` (pin-private in `P1/DivPow.lean:683/687/704`; public in-flight copy at `…/Defs/TateResidueCurrency.lean:159`) | `…/P1/DivPow.lean`, `…/Defs/TateResidueCurrency.lean` |
| `Place.maximalIdeal_eq_span_uniformizer`, `Place.uniformizerSubring'''` | `…/Canonical/HasCanonicalDivisor.lean:194/186` |
| `Place.FiniteResidue.finite`, `Place.ResidueField`, `Place.localResidue` | `…/Defs/Place.lean:108/103`, `…/LocalResidue/Instance.lean` |
| `Algebra.lmul`, `LinearMap.trace_lie`, `LinearMap.trace_restrict_eq_of_forall_mem`, `Valuation.Integers.isUnit_iff_valuation_eq_one`, `Valuation.valuationSubring.integers`, `KaehlerDifferential.map`, `Irreducible.maximalIdeal_eq` | mathlib `v4.34.0` (probe M) |
