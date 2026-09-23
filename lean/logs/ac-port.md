# The `AlgebraicCurve` effort — the complete record

**Status: the effort is complete.** AC0 and T1–T9 are done and green, and T7
(the divisor-exchange capstone) was written and verified by the human reviewer. This
is the running record for the third port, parallel to
[ffg-port.md](ffg-port.md) and [card-torsion-port.md](card-torsion-port.md): what
*this* effort did, what it cost, and what it decided. Lessons that generalize go
to [porting-playbook.md](../porting-playbook.md); decisions and measurements stay
here.

The run brief is [topics/algebraicCurve/SET-1.md](../topics/algebraicCurve/SET-1.md)
and the per-topic work orders are `topics/algebraicCurve/TOPIC-*.md`. SET 2
(T5, T6, T8, T9) is written only after SET 1 is reviewed; T7 is the human
capstone. The blueprint is [PORTING-AC.md](../topics/PORTING-AC.md).

FLT is pinned at `aa2d8b3`; mathlib at `v4.34.0`.

## 0. Where the effort stands

| layer | scope | status | measure |
|---|---|---|---|
| AC0 | the `AlgebraicCurve/Defs/` vocabulary, 8 modules | **done** | consumer **Zone A at 0 errors**; checker 538 |
| T1 | the `Place` ord/valuation interface, 19 nodes | **done** | consumer **Zone B at 0 errors**, cross-module wire test proved; checker 538 |
| T2 | the promoted fibre dictionary, `fiberOver`, `le_finrank`, `inertiaDeg_pos` | **done** | consumer **Zone C at 0 errors**; checker 557; axioms clean |
| T3 | Galois ramification/inertia, 7 nodes | **done** | consumer **Zone D at 0 errors**; checker 586; axioms clean |
| T4 | along-map transport + `Pic0` descent, 16 nodes + the 6-declaration prelude | **done** | consumer **Zone E at 0 errors**; checker 586; axioms clean |
| T5 | the generic orbit/index engine + the bifibre count, 5 nodes | **done** | consumer **Zone F at 0 errors**; checker 600; scout open in 3.2 s |
| T6 | the local exchange + the normal closure, 1 node | **done** | consumer **Zone G at 0 errors**; checker 603; axioms clean |
| T8 | the `P¹` places and degree, 10 of 11 nodes | **done** | consumer **Zone H at 0 errors**; checker 613; axioms clean |
| T9 | `HasPrincipalDivisors` via transcendence, 2 nodes | **done** | consumer **Zone I at 0 errors**; checker 617; axioms clean |
| T7 | the divisor exchange (capstone, human) | **done** | consumer **Zone J at 0 errors**; checker 618; axioms clean |

Baseline before the first edit (2026-09-23): `lake build` **3,874 jobs green**;
`python3 spec/check_flt_statements.py`
`304 statements identical (16 promoted from pin-private declarations), 0 mismatched, 0 missing, 12 own-proof declarations exempted (316 port declarations checked)`.

Full build after AC0 + T1: **4,012 jobs green, 0 warnings, no `sorry`**; after T2,
**4,015**; after T3, **4,018**; after T4 and the consumer tail, **4,022 jobs green,
0 warnings, no `sorry`**. Final checker line: `586 statements identical (34
promoted from pin-private declarations), 0 mismatched, 0 missing, 14 own-proof
declarations exempted (600 port declarations checked)`.

## 1. AC0 — the vocabulary. What it cost

One goal round (the checkpoint round), no structural restart.

- `timeout 300 lake build`: 4,012 jobs green, 0 warnings.
- `timeout 120 lake env lean spec/AlgebraicCurveConsumer.lean 2>&1 | grep -c error`: **0**.
- `python3 spec/check_flt_statements.py`: **538 identical (18 promoted from
  pin-private declarations), 0 mismatched, 0 missing, 14 own-proof
  declarations exempted (552 port declarations checked)**.
- `#print axioms Place.mem_iff_ord_nonneg` = `[propext, Classical.choice, Quot.sound]`.

### 1.1 Per-module table

Every file is in namespace `AlgebraicCurve` (sub-namespaces `Place`, `Divisor`,
`Pic0`, `RationalFunctionField`, `SemilinearAut`). "decls" counts non-`private`
declarations of kinds `def/theorem/lemma/abbrev/structure/instance/class`.

| module | lines | decls | FLT source |
|---|---|---|---|
| `Defs/Place.lean` | 392 | 39 | `Def_AlgebraicCurve_DivisorClassGroup` 22–179, 456–485 + T1's 11 nodes (wrappers) |
| `Defs/Divisor.lean` | 85 | 14 | `Def_AlgebraicCurve_DivisorClassGroup` 179–247 |
| `Defs/PushPull.lean` | 756 | 63 | `Def_AlgebraicCurve_DivisorPushPull` (whole, minus drops) |
| `Defs/PlacesOverDVR.lean` | 448 | 36 | `Def_AlgebraicCurve_PlacesOverDVR` (whole, minus drops) |
| `Defs/Correspondence.lean` | 362 | 39 | `Def_AlgebraicCurve_Correspondence` (whole) |
| `Defs/SemilinearAut.lean` | 207 | 26 | `Def_AlgebraicCurve_BaseChangeGalois` 15–206 |
| `Defs/RatFuncPlaces.lean` | 272 | 20 | `Def_AlgebraicCurve_RatFuncPlaces` 18–236 + `Def_AlgebraicCurve_RatFuncPlaceInfty` (whole) |
| `Defs/IntegralAdjoin.lean` | 95 | 3 | T1's three `isIntegral_adjoin_*` wrappers |
| `spec/AlgebraicCurveConsumer.lean` | 172 | — | Zones A + B + C |

AC0 + T1 write **2,617 module lines / 240 public declarations** (AC0's seven
modules 2,130 / 218; T1 adds 11 declarations to `Place.lean`, 2 to
`RatFuncPlaces.lean` and the 3-declaration `IntegralAdjoin.lean`).

### 1.2 The measured `Def_` drop list

`grep -c` counts are occurrences in the 65-node corpus (the 63 AC + 2 generic
`S_` files), regenerated with `PORTING-AC.md` §9.1's closure recipe. Every name
below has count **0**, which is the evidence for dropping it. Whole dropped
blocks: 1,270-ish raw lines not written (`PORTING-AC.md` §4.3's estimate).

| module | dropped | corpus `grep -c` |
|---|---|---|
| `DivisorClassGroup` | `Pic`, `torsion`, `mem_torsion`, `AbelJacobiCard` | 0, 0, 0, 0 |
| `DivisorClassGroup` | the Galois `F ≃ₐ[K] F` action block 262–456 | 0 (whole block) |
| `PushPull` | `Place.mapRestrict`, `Divisor.mapRestrict`, `Divisor.mapRestrict_single` | 0, 0, 0 |
| `PlacesOverDVR` | `chartHom`, `coe_chartHom`, `mem_center_iff`, `inv_algebraMap_mem`, `finite_setOf_forall_mem_and_ord_pos` | 0 each |
| `PlacesOverDVR` | `card_fiberOver_eq`, `fiber_eq_fiberOver` | 0, 0 |
| `BaseChangeGalois` | the Divisor/`Pic0` action + torsion block 206–356 | 0 (whole block) |
| `RatFuncPlaces` | `placeOfPoint` 236–274 | 0 |
| `RatFuncPlaces` | the whole `Place.Congr` section 274–398 (`comapSymmRingEquiv`, `coe_comapSymmRingEquiv_apply`, `symm_algebraMap_comm`, `congrRingEquiv`, `congrRingEquiv_toValuationSubring`, `ord_congrRingEquiv`, `congrResidueAlgEquiv`, `deg_congrRingEquiv`, `congrEquiv`, `congrEquiv_apply`, `congrEquiv_symm_apply`) | 0 each |
| `BaseChangeGalois` | `divisor_smul_def`, `smul_single`, `divisor_smul_apply`, `degree_smul`, `torsionRep`, `pic0_smul_mk` | 0 each |

The chart block is *partially* kept: `chartHom`, `inv_algebraMap_mem` and
`mem_center_iff` stay **`private`** because `Place.center` is defined through
`chartHom` and its proofs use the other two; `coe_chartHom` and
`finite_setOf_forall_mem_and_ord_pos` are not written at all. `card_fiberOver_eq`
and `fiber_eq_fiberOver` are not written; T5's `card_fiberOver` may re-add the
first — recorded as a deliberate deferral, not a mistake.

`Place.FiniteResidue` (a 3-line `class`, invisible to the checker) is kept: T8's
`deg_ofHeightOneSpectrum` may want it. Call recorded.

### 1.3 Which of the four `Place` instances needed help

None. The structure's own field carries `IsPrincipalIdealRing` verbatim
(`instance : IsPrincipalIdealRing v.toValuationSubring := v.isPrincipalIdealRing'`),
`IsDiscreteValuationRing` follows from `ValuationSubring.not_isField_of_ne_top`,
`Algebra K v.toValuationSubring` is the `codRestrict` of `algebraMap`, and
`IsScalarTower K v.toValuationSubring F` follows from `coe_algebraMap`. So the
bridge decision SET 2 inherits is AC0's, unchanged from FLT.

### 1.4 The checker's AC ordering

`SOURCES` gains, in this order:

1. T1's nineteen wrappers, then the three promoted-`private` wrappers
   (`exists_ord_pos`, `comap_algebraMap_ne_top`, `mem_comap_iff_ord_nonneg`);
2. the seven AC definition modules, with **`BaseChangeGalois` before
   `DivisorClassGroup`**.

Ordering decisions that actually bit:

- **`smul_def`, `smul_toValuationSubring`, `ord_smul`, `deg_smul`.** The pin's
  `Def_AlgebraicCurve_DivisorClassGroup` carries a *second, dropped* Galois action
  (`F ≃ₐ[K] F` on `Divisor`/`Pic0`) with the same last names as the
  `SemilinearAut` block. Listing `BaseChangeGalois` first made the transcribed
  copies win.
- **`correspondence`.** The one collision no ordering can resolve:
  `Def_AlgebraicCurve_Correspondence` declares `Divisor.correspondence` (line 137)
  and `Pic0.correspondence` (line 183); the checker keys by last name and keeps
  the first. `"correspondence"` is therefore in `OWN_PROOFS` with that reason
  (the only AC exemption), so the exemption covers the pair, both transcribed
  verbatim. The predicted collisions `restrict`, `mk`, `deg`, `degree`, `ord`,
  `ext` did **not** bite.

## 2. T1 — the ord interface. What it cost

The nineteen nodes are mostly exposure of leaves; two of them
(`ord_nonneg_of_mem`, `mem_of_ord_nonneg`) were already written by AC0's
`Defs/PushPull.lean`, and eleven more were already in AC0's `Defs/Place.lean` /
`Defs/RatFuncPlaces.lean` keep sets. The overlap is **13 of 19**: the three
`ord`/`mem`/`mem_iff` leaves in `PushPull.lean`; `mem_iff_adicValuation_le_one`,
`mem_maximalIdeal_iff_adicValuation_lt_one`, `adicValuation_valuationSubring`,
`isEquiv_adicValuation_of_valuationSubring_eq` (moved to `Place.lean` with the
wrappers' binders); `isEquiv_adicValuation_ofHeightOneSpectrum` and
`ord_ofHeightOneSpectrum_ne_zero_iff` (in `RatFuncPlaces.lean`); and the
`adicValuation.IsRankOneDiscrete` / `IsTrivialOn` instances (named theorems added
in `Place.lean`, anonymous instances retained in `RatFuncPlaces.lean`). The
genuinely new work is `ord_algebraMap`, `ord_smul_of_ne_zero`,
`ord_eq_neg_log_of_valuationSubring_eq`,
`mem_toValuationSubring_of_isIntegral_adjoin`,
`ord_eq_zero_of_isIntegral_adjoin` and the three generic `isIntegral_adjoin_*`.

### 2.1 Interface table (declaration → external indegree → port module)

Re-derived from the work order's counts; "ext" is citers outside the hecke
closure.

| declaration | ext | port module |
|---|---|---|
| `Place.mem_iff_ord_nonneg` | 184 | `Defs/PushPull.lean` (AC0) |
| `Place.ord_algebraMap` | 142 | `Defs/Place.lean` (T1) |
| `Place.mem_of_ord_nonneg` | 106 | `Defs/PushPull.lean` (AC0) |
| `Place.ord_nonneg_of_mem` | 104 | `Defs/PushPull.lean` (AC0) |
| `isIntegral_adjoin_intermediateField_mk` | 21 | `Defs/IntegralAdjoin.lean` |
| `Place.ord_smul_of_ne_zero` | 23 | `Defs/Place.lean` |
| `isIntegral_adjoin_map_algHom` | 12 | `Defs/IntegralAdjoin.lean` |
| `Place.ord_eq_neg_log_of_valuationSubring_eq` | 13 | `Defs/Place.lean` |
| `isIntegral_adjoin_of_isScalarTower` | 10 | `Defs/IntegralAdjoin.lean` |
| `Place.ord_eq_zero_of_isIntegral_adjoin` | 11 | `Defs/Place.lean` |
| `Place.mem_iff_adicValuation_le_one` | 11 | `Defs/Place.lean` (moved from `RatFuncPlaces`) |
| `Place.mem_toValuationSubring_of_isIntegral_adjoin` | 45 | `Defs/Place.lean` |
| `Place.ord_ofHeightOneSpectrum_ne_zero_iff` | 3 | `Defs/RatFuncPlaces.lean` |
| `Place.mem_maximalIdeal_iff_adicValuation_lt_one` | 2 | `Defs/Place.lean` |
| `Place.adicValuation_valuationSubring` | 0 | `Defs/Place.lean` |
| `Place.isEquiv_adicValuation_of_valuationSubring_eq` | 0 | `Defs/Place.lean` |
| `Place.isEquiv_adicValuation_ofHeightOneSpectrum` | 0 | `Defs/RatFuncPlaces.lean` |
| `Place.adicValuation_isRankOneDiscrete` | 0 | `Defs/Place.lean` |
| `Place.adicValuation_isTrivialOn` | 0 | `Defs/Place.lean` |

The four high-indegree leaves sum to 536 external citers; three of the four are
AC0's, so T1's own new surface is the 142-citer `ord_algebraMap` plus the
generic `isIntegral_adjoin_*` trio (43 citers).

### 2.2 Was exposure free?

Yes except for two items:

- `mem_toValuationSubring_of_isIntegral_adjoin` is the topic's one real proof
  (the `placeSubalgebra`/`Valuation.Integers` route), transcribed from
  `S_…_mem_toValuationSubring_of_isIntegral_adjoin.lean`.
- `ord_eq_neg_log_of_valuationSubring_eq` needed its private
  `le_exp_neg_one_of_lt_one` helper, transcribed.

`Place.adicValuation_isRankOneDiscrete` is **not** a separate proof in v4.34: it
is exactly `IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F`
(there is no `HeightOneSpectrum.valuation_isRankOneDiscrete`). Recorded.

### 2.3 `Defs/IntegralAdjoin.lean`

The three generic transport lemmas were not needed by AC0's modules (AC0's
`mem_toValuationSubring_of_isIntegral_adjoin` uses only `Algebra.adjoin` over a
field and inlines its own `placeSubalgebra`); they are homed in their own module
for T5 and T9. Deviation from the blueprint's `WeilExchange/OrdInterface.lean`:
**not created**, exactly as `TOPIC-t1-ord-interface.md` §1 settles — the ord
lemmas live beside `Place`, and the interface has no module of its own.

## 2b. T2 — the fibre dictionary. What it cost

One goal round. `Defs/PlaceDictionary.lean` (398 lines, 17 public declarations:
the pin's whole copied block, written once) and
`WeilExchange/FiberOverCount.lean` (122 lines, the three nodes with the single
Assembly). The pin ships the dictionary byte-for-byte in four files and the
45-line Assembly twice; the actual dictionary written is **398 port lines for an
estimated 737 content lines never written** (the estimate counts the pin's four
copies; the port writes one, plus its header).

*The one real shape adaptation.* The pin calls the deprecated
`Ideal.sum_ramification_inertia`, whose statement is `∑ P ∈ primesOverFinset p S,
p.ramificationIdx' P * p.inertiaDeg' P = Module.finrank K L`. v4.34's replacement
`Ideal.sum_ramification_inertia_eq_finrank` (in `Mathlib.RingTheory.RamificationInertia.Basic`)
has the different shape `∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R
= Module.finrank R S`. Two bridges, exactly as the manager's recon predicted:

1. **The sum domain.** `Finset.sum_subtype (primesOverFinset p S) (fun P =>
   IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v) (P := P))
   (fun P => P.ramificationIdx R * P.inertiaDeg R)` identifies the subtype sum with
   the pin's `∑ P ∈ …`; the `Fintype ↥(p.primesOver S)` instance is
   `(IsDedekindDomain.primesOverFinset p S).finite_toSet.fintype` transported along
   `IsDedekindDomain.coe_primesOverFinset` (a `▸`, because the two `_` placeholders
   otherwise elaborate to different metavariables — `set_option`-free).
2. **The finrank.** `IsFractionRing.finrank_eq v.toValuationSubring F
   (integralClosureAt F' v) F' : Module.finrank F F' = Module.finrank
   v.toValuationSubring (integralClosureAt F' v)`, from
   `Mathlib.LinearAlgebra.Dimension.Localization` (the manager's pointer; the file's
   `IsFractionRing.finrank_right_eq`/`finrank_left_eq` are the one-sided variants).
   Rewritten `←` so the new theorem's RHS becomes the pin's.
3. **The primed-vs-unprimed constants in the `sum_bij` value obligation.** The new
   theorem's terms use `q.ramificationIdx`/`q.inertiaDeg` while the dictionary keeps
   the pin's `ramificationIdx'`/`inertiaDeg'`; the two are bridged by
   `Ideal.ramificationIdx'_eq_ramificationIdx p P (maximalIdeal_ne_bot v)` and
   `Ideal.inertiaDeg'_eq_inertiaDeg p P`. (This third bridge is the real adaptation
   cost the work order did not anticipate.)

`Ideal.ramificationIdx'` is **not** deprecated and stays in the statements;
`Ideal.inertiaDeg'` is, so both `PlaceDictionary.lean` and `FiberOverCount.lean`
carry `set_option linter.deprecated false` with a one-line reason (the manager's
instruction, SET-1 §3.1). No statement changed. `inertiaDeg_pos` needs only the
ResidueDictionary; it is homed in `FiberOverCount.lean` per the work order (both
that file and `PlaceDictionary.lean` are consumed by T3/T5 anyway).

`#print axioms` on all three nodes = `[propext, Classical.choice, Quot.sound]`.
Consumer Zone C = 0 errors, with a proved abstract instantiation of the `≤` form
(the place is abstract because `Place K K` is empty).

## 2c. T3 — Galois ramification/inertia. What it cost

One goal round. `WeilExchange/GaloisRamification.lean`, 195 lines, 7 public nodes
(4 private helpers: `ord_smul_eq`, `intertwinesAlong_one_ofAlgAut`,
`restrictSmulValuationSubringEquiv`,
`coe_restrictSmulValuationSubringEquiv_apply`). The only
mathlib-archaeology node is `exists_algEquiv_smul_eq_of_restrict_eq`; the three
API points (`IsIntegralClosure.MulSemiringAction` in
`Mathlib.RingTheory.Invariant.Galois`, `IsGaloisGroup.of_isFractionRing` in
`Mathlib.RingTheory.IsGaloisGroup.Basic`, `Ideal.exists_smul_eq_of_isGaloisGroup`
in `Mathlib.NumberTheory.RamificationInertia.Galois`) all had the v4.34 shape the
pin used — **no restatement was needed**. `Mathlib.NumberTheory.RamificationInertia.Galois`
is not itself deprecated (it imports the new `RingTheory.RamificationInertia.Basic`),
so importing it does not warn.

`Place.restrict_ofAlgAut_smul` is written once and the pin's private duplicate
`restrict_ofAlgAut_restrictScalars_smul` is not written; the two copies are
byte-identical in the pin. Consumer Zone D instantiates
`exists_algEquiv_smul_eq_of_restrict_eq` at a documented abstract Galois
extension.

**One work-order statement divergence.** `TOPIC-t1-ord-interface.md`'s §2 table
(and the T3 §2 statement list) give `SemilinearAut.ramificationIndex_smul` with
`[IsScalarTower K F F'] [Algebra.IsIntegral F F']`; the pin's wrapper has
**neither** (they do not occur in `Place.ramificationIndex`'s type, so the pin's
section variables are not parameters). The pin wins (SET-1 §1) and the port drops
them; the checker confirms the wrapper's text. `inertiaDeg_smul` does keep them,
because `Place.inertiaDeg`'s value mentions `w.restrict F`, so they *are* its
parameters. Recorded.

## 2d. T4 — transport and `Pic0` descent. What it cost

One goal round. `WeilExchange/Transport.lean`, 304 lines, 22 public declarations:
the 16 nodes plus the 6-declaration shared prelude written once. The pin copies
the prelude into `bifiber` (`BifibreDev.*`), `exchange` (`BifibreW2.*`) and
`divisor_exchange` (`BifibreWEX.*`): `inertiaDegAlong_congr`,
`isIntegral_toAlgHom`, `toAlgHom_comp_toAlgHom`, `restrict_restrict`,
`Place.ramificationIndex_eq_mul_ramificationIndex_restrict`,
`Place.inertiaDeg_eq_mul_inertiaDeg_restrict`. The first four are kept in a
`BifibreDev` namespace so T5/T6/T7 can use the pin's own dotted names; the last
two are in `namespace Place`. The checker verifies all six against the pin's
public `S_..._bifiber.lean` copy.

**The `rfl` canary passed.** `Place.restrictAlong_restrictAlong` is
`Place.ext (SetLike.ext fun _ => Iff.rfl)` with no rewriting, so `algebraAlong`
is still an `abbrev`. **No `rfl` bridge needed help.**

One proof-body adaptation (the playbook §3.5 rewrite-search trap):
`inertiaDegAlong_comp`'s `IsScalarTower v.ResidueField w.ResidueField W.ResidueField`
instance in the pin uses `rw [Place.restrictResidueMap_residue, …]`, which fails
in the port because the outer `restrictResidueMap`'s implicit `F` is not pinned
and its `residue` argument's ring is the `restrict`-of-`restrict` (not syntactically
`(W.restrict F)`). Passing the `Place` argument explicitly
(`Place.restrictResidueMap_residue W a`, `… w a`, `… W (Place.restrictInclusion F w a)`)
restores the rewrite. No statement changed; this is the monomorphic-helper rule
in action.

**One work-order statement divergence.** `TOPIC-t4-transport.md` §2 transcribes
`Divisor.pullbackAlong_pullbackAlong` with `[HasPrincipalDivisors K F']
[HasPrincipalDivisors K F'']` in the typeclass block; the pin's wrapper places
them **after** `(χ : F' →ₐ[K] F'')`. The pin wins; the port matches the wrapper.

## 3. Friction log

Kept current while the friction happened.

- **`lake env lean <file>` needs its dependencies' oleans.** On a fresh module the
  first per-module check must be `lake build FLTForHuman.AlgebraicCurve.Defs.X`
  (which builds deps); a bare `lake env lean` on the file fails with "object file
  … does not exist". Used `lake build` per module as the per-module gate, then the
  consumer for the zone.
- **Section variables in the pin are explicit arguments.** FLT's
  `Def_AlgebraicCurve_DivisorPushPull` has `variable (w : Place K F')` then calls
  `isUnit_mk_comap_iff hg0 hmem`. With `autoImplicit false` the ported private
  helper must be called `isUnit_mk_comap_iff w hg0 hmem`; the pin's text is not
  literally reproducible. This is a *proof-body* adaptation only (no statement
  changes); the private helper is invisible to the checker.
- **Wrapper binders vs definition-file binders.** T1's nodes have wrappers with
  explicit binders while the corresponding definitions use section variables. The
  checker compares text, so the port writes the **wrappers'** binders for T1 nodes
  and the **definition files'** style for AC0 definitions, and `SOURCES` lists the
  wrappers first (SET-1 §5). Four AC0 declarations
  (`adicValuation_valuationSubring`, `mem_iff_adicValuation_le_one`,
  `isEquiv_adicValuation_of_valuationSubring_eq`,
  `mem_maximalIdeal_iff_adicValuation_lt_one`) therefore moved out of
  `RatFuncPlaces.lean` into `Place.lean` rewritten at the wrappers' binders.
- **`Mathlib.NumberTheory.RamificationInertia.Basic` is a deprecated module.**
  Importing it warns and the warning cannot be silenced (options cannot precede
  imports), so `PlacesOverDVR.lean` imports `Mathlib.RingTheory.RamificationInertia.Basic`
  instead — the manager's recon, SET-1 §3.1. T2 needs the primed constants from
  `Mathlib.NumberTheory.RamificationInertia.{Inertia,Ramification}` and the new
  sum theorem from `Mathlib.RingTheory.RamificationInertia.Basic`.
- **Deprecated proof lemmas renamed:** `zero_le'` → `zero_le` (Place.lean),
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (PushPull/PlacesOverDVR).
- **`linter.style.haveILetI`** is disabled at module level in `PushPull`,
  `PlacesOverDVR`, `Correspondence` and `IntegralAdjoin`, as the pin's cone-algebra
  files do; the `letI`/`haveI` walls are kept literal (SET-1 §3).
- **`Def_AlgebraicCurve_Correspondence` last-name collision** (`Divisor.` vs
  `Pic0.correspondence`): `correspondence` added to `OWN_PROOFS`; see §1.4.
- **`RationalFunctionField.placeInfty`** needs `[DecidableEq (RatFunc K)]` and
  `open WithZero`; `RatFunc.inftyValuation K` is mathlib's
  `RatFunc.inftyValuation`. The consumer carries the instance explicitly.
- **T2's three bridges** (the new `Ideal.sum_ramification_inertia_eq_finrank`):
  `IsFractionRing.finrank_eq`, `Finset.sum_subtype` +
  `mem_primesOverFinset_iff` (plus the `Fintype` `▸` transport along
  `coe_primesOverFinset`), and the primed/unprimed
  `ramificationIdx'_eq_ramificationIdx` / `inertiaDeg'_eq_inertiaDeg` bridges. See
  §2b; the third was not anticipated by the work order.
- **T3's `ramificationIndex_smul` dropped two instances** the work order listed;
  the pin's wrapper has none. The pin wins.
- **T4's `pullbackAlong_pullbackAlong` instance-binder position** follows the
  wrapper, not the work order's §2 transcription.
- **T4's `inertiaDegAlong_comp` `IsScalarTower` instance**: the pin's
  `rw [Place.restrictResidueMap_residue, …]` does not fire with implicit `F`
  unresolved; pass the `Place` argument explicitly (playbook §3.5).
- **`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`** in `GaloisRamification.lean`; the
  consumer carries `set_option linter.deprecated false` for the pin's primed
  `Ideal.inertiaDeg'` statements.
- **`#print axioms`** on T1's `ord_nonneg_of_mem`/`ord_algebraMap`, T2's
  `sum_ramificationIndex_mul_inertiaDeg_fiberOver`/`inertiaDeg_pos`, T3's
  `exists_algEquiv_smul_eq_of_restrict_eq`/`inertiaDeg_eq_of_restrict_eq` and T4's
  `separableAlong_of_charZero`/`pullbackAlong_pullbackAlong`/`Pic0.zsmul_mk` is
  `[propext, Classical.choice, Quot.sound]`.



## 4. SET 1 closed: the measured picture

| topic | modules | lines | public decls | checker | consumer zone | build |
|---|---|---|---|---|---|---|
| AC0 | 7 `Defs/*` + consumer Zone A | 2,130 | 218 | 538 | A, 0 errors | green |
| T1 | `Defs/IntegralAdjoin` + 13 declarations in `Place`/`RatFuncPlaces` | 95 + 36 | 3 + 13 | 538 | B, 0 errors | green |
| T2 | `Defs/PlaceDictionary` + `WeilExchange/FiberOverCount` | 398 + 122 | 16 + 3 | 557 | C, 0 errors | green |
| T3 | `WeilExchange/GaloisRamification` | 195 | 7 | 564 | D, 0 errors | green |
| T4 | `WeilExchange/Transport` | 304 | 22 (16 nodes + 6 prelude) | 586 | E, 0 errors | green |

SET 1 writes **13 modules / 3,244 lines / 269 public declarations** (the 8 `Defs/`
modules, the 4 `WeilExchange/` modules, and the consumer). Every dropped definition
name has `grep -c` 0 in the 65-node corpus. The one `OWN_PROOFS` AC addition is
`correspondence` (a within-file last-name collision); the only other `SOURCES`
ordering decisions were `BaseChangeGalois` before `DivisorClassGroup` (a dropped
duplicate Galois action) and wrappers before definition files.

### Hand-off for SET 2 (T5, T6, T8, T9)

`Transport.lean` exposes, once: `BifibreDev.{inertiaDegAlong_congr,
isIntegral_toAlgHom, toAlgHom_comp_toAlgHom, restrict_restrict}` and
`Place.{ramificationIndex_eq_mul_ramificationIndex_restrict,
inertiaDeg_eq_mul_inertiaDeg_restrict}`; T5/T6/T7 must import these, not restate
them. `PlaceDictionary.lean` exposes the whole 16-declaration dictionary at the
pinned names under `AlgebraicCurve.Place` (plus the private
`eq_ord_of_addHom_of_nonneg_iff`), with the two centre identifications
(`ramificationIndex_eq_ramificationIdx_fiberCenter`,
`inertiaDeg_eq_inertiaDeg_fiberCenter`) that T5's count and T9's principal-divisors
route consume. `FiberOverCount.lean` exposes
`sum_ramificationIndex_mul_inertiaDeg_fiberOver` and
`sum_ramificationIndex_mul_inertiaDeg_le_finrank`;
`GaloisRamification.lean` exposes the transitivity and invariance lemmas T5/T6 need.
All are `lake build`-green, 0-warning, axiom-clean, and statement-verified.

# The `AlgebraicCurve` effort — record (SET 2)

**Status: SET 2 in progress.** T5 (the generic orbit/index engine + the bifibre
count), T6 (the local exchange), T8 (`P¹` places and degree) and T9
(`HasPrincipalDivisors` via transcendence) are the authorized topics; T7 (the
divisor exchange) is the human capstone and is **not** written here. The run brief
is [topics/algebraicCurve/SET-2.md](../topics/algebraicCurve/SET-2.md).

## 5. T5 — the orbit/index engine and the bifibre count

### 5.0 The route scout (done first, per SET-2's preface)

Prototyped, before writing `FiniteGroupAction.lean`, the pin's whole
`S_MulAction_ncard_orbit_inter_orbit_mul_card.lean` +
`S_Subgroup_exists_eq_mul_of_index_inf_eq.lean` pair in the gitignored
`Scratch.lean` (the seven helpers and the two public statements at the wrappers'
binders).

**Outcome: the route is open — the two generic statements are provable from
mathlib v4.34's orbit–stabiliser API with the pin's proof transcribed unchanged.**
`timeout 60 lake env lean Scratch.lean` returned in **3.2 s** with **0 errors** and
four warnings, all of them the two known v4.34 nits (no mathlib statement moved or
went missing):

- `linter.style.haveILetI` on the three `haveI : Finite …` instance walls
  (`card_eq_mul_of_card_fiber`, `card_smul_mem_eq`,
  `ncard_orbit_inter_orbit_mul_card_eq`). The SET 1 remedy applies: the module
  carries `set_option linter.style.haveILetI false`.
- `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (the rename SET 1 already logged).

Fate of the helpers, all transcribed unchanged and all kept `private` in the port:

| helper | fate | mathlib ingredient |
|---|---|---|
| `card_eq_mul_of_card_fiber` | unchanged | `Equiv.sigmaFiberEquiv`, `Nat.card_sigma`, `Nat.card_eq_fintype_card` |
| `card_preimage_eq_mul_of_card_fiber` | unchanged | same |
| `card_fiber_smul_eq` | unchanged | `Nat.card_congr` |
| `card_smul_mem_eq` | unchanged | `Nat.card_coe_set_eq`, `Equiv.subtypeEquivRight` |
| `card_fiber_psi_eq` | unchanged | `Subgroup.mem_inf`, `mul_inv_cancel_left` |
| `ncard_orbit_inter_orbit_mul_card_eq` | unchanged | `index_stabilizer`, `index_stabilizer_of_transitive`, `Subgroup.card_mul_index`, `Nat.card_prod` |
| `stabilizer_mk_one_eq` (second statement) | unchanged | `QuotientGroup.eq` |

The v4.34 names the work order flagged were the right ones: `MulAction.index_stabilizer`
and `MulAction.index_stabilizer_of_transitive` resolve under the pin's `open
MulAction`; `QuotientGroup.eq` (two rewrite goals) is unchanged. Cost: the scout
spent **one `Scratch.lean` build, 3.2 s**; it confirmed the route before any port
module was written, so no port time was risked.

### 5.1 What it cost

One goal round. Two modules, 625 lines, 14 public declarations:

| module | lines | decls | FLT source |
|---|---|---|---|
| `FLTForHuman/FieldTheory/FiniteGroupAction.lean` | 264 | 2 (7 helpers `private`) | the two `S_MulAction_*` / `S_Subgroup_*` files |
| `FLTForHuman/AlgebraicCurve/WeilExchange/Bifibre.lean` | 361 | 12 | `S_..._card_fiberOver_...`, `S_..._exists_restrict_eq`, `S_..._bifiber` (minus the T4/T2 preludes) |

- `timeout 300 lake build`: **4,024 jobs green, 0 warnings, no `sorry`** (SET 1
  baseline 4,022 + the two new modules).
- `timeout 120 lake env lean spec/AlgebraicCurveConsumer.lean 2>&1 | grep -c error`:
  **0** (Zone F added).
- `python3 spec/check_flt_statements.py`: **600 statements identical (34 promoted
  from pin-private declarations), 0 mismatched, 0 missing, 14 own-proof
  declarations exempted (614 port declarations checked)** — up from SET 1's 586 by
  the 14 new public declarations (2 generic + 12 in `Bifibre.lean`).
- `#print axioms` on both generic statements and all three `Place` nodes =
  `[propext, Classical.choice, Quot.sound]`.

The pin's `bifiber` `S_` file is **875 raw lines** in this one copy (and the pin
ships its prelude again in the `exchange`/`divisor_exchange` copies); the port's
`Bifibre.lean` is 361 lines because the T4 prelude (already in `Transport.lean`)
and the T2 dictionary (already in `PlaceDictionary.lean`) are imported. The two
small `Place` nodes transcribe unchanged; the 269-content-line assembly is the
pin's, with only the two known v4.34 substitutions (`Set.mem_ofPred_eq`; `push Not`
for the deprecated `push_neg`) and the `haveI` lint wall disabled at module level.

### 5.2 The one statement divergence

`Place.sum_ramificationIndex_mul_inertiaDeg_bifiber` has **different binders in the
wrapper and in the pin's `S_` file**: the wrapper (the statement authority, SET-2
§1.2) makes the compositum `M` an explicit binder, placing it before the
typeclass block —

```lean
theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber
    {K F F₁ F₂ E : Type*} (M : Type*) [Field K] … [IsGalois F M] …
```

— while the `S_` file's internal `BifibreDev` copy (line 209) and its `solution`
(line 373) both bind it implicitly inside `{K F F₁ F₂ E M : Type*}`. The port
follows the **wrapper** (`(M : Type*)`). Because the checker keeps the first
same-last-name source in `SOURCES`, the five T5 wrappers are listed **before** the
pin's `bifiber` `S_` file, so the explicit-`M` wrapper wins the lookup; with the
`S_` file first the run reported exactly this mismatch (`1 mismatched`) and nothing
else. T6 calls the theorem as `…_bifiber (M := M) …` either way.

## 6. T6 — the local exchange and the normal closure

One goal round. `WeilExchange/LocalExchange.lean`, 206 lines, 3 public declarations
(`BifibreW2.exchange_of_isGalois`, `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable`,
`Place.sum_ramificationIndex_mul_inertiaDeg_exchange`); the envelope's `Env`,
`algebraEnv` and the four `isScalarTower_env_*` are `private`.

- `timeout 180 lake build FLTForHuman.AlgebraicCurve.WeilExchange.LocalExchange`:
  green, **0 warnings**, first try, 3.1 s.
- `timeout 300 lake build`: green, **0 warnings**, no `sorry`.
- Consumer Zone G: **0 errors**.
- Checker: **603 identical, 0 mismatched, 0 missing, 14 own-proof declarations
  exempted (617 port declarations checked)**.
- `#print axioms` on all three = `[propext, Classical.choice, Quot.sound]`.

**The named shape risk (risk 3) did not materialize.** The four
`isScalarTower_env_*` proofs — the topic's instance block — transcribed literally
from the pin with no help: `IsScalarTower.of_algebraMap_eq` + `Subtype.ext` + the
`← IsScalarTower.algebraMap_apply` rewrite. `algebraEnv` stayed
`@[reducible]`, and `isScalarTower_env_const` needed only the pin's
`omit [Algebra R E] in`. The pin's two `letI` blocks (in the separable stage and in
the public node) are **syntactically identical** in the port, as the pin has them;
they are not factored (no clean way across the two binder lists).

The S_` file's prelude copies (`BifibreW2.{inertiaDegAlong_congr, isIntegral_toAlgHom,
toAlgHom_comp_toAlgHom, restrict_restrict}` and the two `Place.*_restrict` rows) are
**not** reproduced: the port imports T4's `BifibreDev.*`/`Place.*` and the checker
still verifies those last names against the T4 `S_..._bifiber` source. The only
`BifibreW2` declaration written is the Galois-case exchange.

### 6.1 The exact public surface T7 consumes

```lean
-- the capstone's local identity (wrapper binders, verbatim):
AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange
    {K F F₁ F₂ E : Type*} [Field K] … [Algebra.IsSeparable F E]
    (hgen : Algebra.adjoin …) (hLD : …) (v : Place K F) (w₁ : Place K F₁)
    (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ …) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ =
      w₁.inertiaDeg F * w₂.ramificationIndex F

-- the two public stages (pin's dotted names):
AlgebraicCurve.BifibreW2.exchange_of_isGalois
AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable
```

Also public for T7: T4's `BifibreDev.{restrict_restrict, toAlgHom_comp_toAlgHom,
inertiaDegAlong_congr, isIntegral_toAlgHom}` and
`Place.{ramificationIndex_eq_mul_ramificationIndex_restrict,
inertiaDeg_eq_mul_inertiaDeg_restrict}` (imported, not restated); T5's
`Place.{card_fiberOver_mul_ramificationIndex_mul_inertiaDeg, exists_restrict_eq,
sum_ramificationIndex_mul_inertiaDeg_bifiber}`; T3's
`Place.{ramificationIndex_eq_of_restrict_eq, inertiaDeg_eq_of_restrict_eq}` and the
`fiberAlong`/`algebraAlong` API from AC0's `Defs/Correspondence.lean`.

## 7. T8 — the `P¹` places and degree

One goal round. `PrincipalDivisors/RatFuncDegree.lean`, 435 lines, **10 public
declarations** (the eleventh node, `deg_ofHeightOneSpectrum`, is AC0's and is not
rewritten, exactly as the work order allowed). Seven private helpers: the dichotomy
`eq_ofHeightOneSpectrum_or_eq_placeInfty`, `placeInfty_ne_ofHeightOneSpectrum`,
`finite_setOf_valuation_ne_one`, `WFg.exists_sub_algebraMap_intDegree_neg`,
`WFj.{ne_finitePlace_of_forall_ne, single_add_single_apply_eq_ord,
degree_single_add_single}`.

- `timeout 180 lake build …RatFuncDegree`: green, **0 warnings**, 3.2 s.
- `timeout 300 lake build`: green, **0 warnings**, no `sorry`.
- Consumer Zone H: **0 errors**.
- Checker: **613 identical, 0 mismatched, 0 missing, 14 own-proof declarations
  exempted (627 port declarations checked)** — up 10 (the tenth node;
  `deg_ofHeightOneSpectrum` was already counted at AC0).
- `#print axioms` on `finite_setOf_ord_ne_zero`,
  `degree_eq_zero_of_forall_eq_ord_algebraMap`,
  `degree_eq_zero_of_forall_eq_ord`,
  `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` and
  `subsingleton_setOf_forall_ne_ofHeightOneSpectrum` =
  `[propext, Classical.choice, Quot.sound]`.

### 7.1 The real prelude saving, and `deg_ofHeightOneSpectrum`

The work order's blueprint estimate for the three `'`-copy files was ≈214 content
lines never written. The measured saving is **larger**: the pin ships the private
bridge (`adicValuation_valuationSubring'`, `mem_iff_adicValuation_le_one'`,
`adicValuation_isRankOneDiscrete'`, `adicValuation_isTrivialOn'`,
`isEquiv_adicValuation_of_valuationSubring_eq'`,
`ord_eq_zero_iff_adicValuation_eq_one'`,
`isEquiv_adicValuation_ofHeightOneSpectrum'`, `nontrivial_valueGroup_inftyValuation`,
`placeInfty'`, `placeInfty'_ne_ofHeightOneSpectrum`,
`eq_ofHeightOneSpectrum_or_eq_placeInfty'`, `finite_setOf_valuation_ne_one'`) in
each of the first three `S_` files (≈90 raw lines each, all `private`), and AC0
already exposes every one of them publicly except the dichotomy, the
`placeInfty`-ne lemma, `finite_setOf_valuation_ne_one` and the two `WF*` blocks —
which the port writes once, ≈150 lines total. No `'`-copy is written.

**`deg_ofHeightOneSpectrum` was already AC0's** (`Defs/RatFuncPlaces.lean` lines
226–230), proved as a one-liner after `residueFieldEquivOfHeightOneSpectrum`; it is
*not* rewritten. Note its source is the definition file, not the `P2M.Dup` wrapper
(the wrapper spells `K` explicitly, the definition file — and the port — leave it
implicit); the pin's `P2M.Dup` alias is the `TOPIC-t8` §2.3 "duplicate" and is a
non-issue.

### 7.2 The shape risks

- **Ostrowski is exactly as the blueprint described.** `toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum`
  consumes `RatFunc.valuation_isEquiv_infty_or_adic`, whose `or` has the left
  branch `IsEquiv infty` (→ the valuation-subring equality through
  `Valuation.isEquiv_iff_valuationSubring`) and the right branch
  `∃ w, v.IsEquiv w.valuation` (→ `Place.ext` + `hv w`). The `∃!` shape the work
  order mentioned is inside the right branch and is handled by `obtain ⟨w, hw, -⟩`.
  `[DecidableEq (RatFunc K)]` is carried only where the wrapper has it.
- **`DecidableEq (RatFunc K)` did materialize as a v4.34 drift**, but not where the
  work order predicted: in v4.34 `RatFunc.inftyValuation` itself takes
  `[DecidableEq (RatFunc F)]` (checked with `#check @RatFunc.inftyValuation`), so
  the port's private `WFg.exists_sub_algebraMap_intDegree_neg` needs the instance
  binder (the pin's does not) and the public `deg_eq_one…` proof opens `classical`.
  Every statement still matches its wrapper; only a private proof's binders changed.
- **The private `WFg` helper transcribed with one rename**:
  `Polynomial.degree_sub_lt` is deprecated in v4.34 in favour of
  `Polynomial.degree_sub_lt_left` (identical signature).
- The `finite_setOf_ord_ne_zero` union/subset argument transcribed as written; the
  only substitution is the known `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`.

## 8. T9 — `HasPrincipalDivisors` via transcendence

One goal round. `PrincipalDivisors/Transcendence.lean`, 514 lines, **4 public
declarations** (`hasPrincipalDivisors_of_finiteDimensional_ratFunc`,
`hasPrincipalDivisors_of_transcendental`,
`W2.hasPrincipalDivisors_adjoin`, `hasPrincipalDivisors_adjoin_of_transcendental`)
and 11 `private` (the ten norm-block declarations plus the `CharZero
v.toValuationSubring` instance).

- `timeout 180 lake build …Transcendence`: green, **0 warnings**, 7.0 s.
- `timeout 300 lake build`: **4,033 jobs green, 0 warnings, no `sorry`**
  (the final SET-2 build: 4,022 baseline + the five new modules and their re-checks).
- Consumer Zone I: **0 errors** (Zones A–I all clean).
- Checker: **617 identical, 0 mismatched, 0 missing, 14 own-proof declarations
  exempted (631 port declarations checked)** — up 4.
- `#print axioms` on all three headlines and `W2.hasPrincipalDivisors_adjoin` =
  `[propext, Classical.choice, Quot.sound]`.

### 8.1 The `PerfectField` risk fired without help

`Ideal.relNorm_eq_pow_of_isMaximal` requires `[PerfectField (FractionRing R)]` with
`R = v.toValuationSubring`. The pin installs a **private scoped instance**
`CharZero v.toValuationSubring`; the port installs it as a plain `private instance`
(`⟨fun a b hab => Nat.cast_injective (R := F) (… Subtype.val …)⟩`), and from
`[CharZero F]` the chain `CharZero v.toValuationSubring →
IsFractionRing.charZero → PerfectField.ofCharZero` fires with **no further help**.
No statement was weakened and no hypothesis added. The exact instance that fired is
`PerfectField (FractionRing v.toValuationSubring)`, synthesized from
`PerfectField.ofCharZero` on `IsFractionRing.charZero v.toValuationSubring`.

### 8.2 The norm block: what was reducible, and what was not

The measured negative the blueprint asked for: **none of the ten norm-block
declarations is reducible to a mathlib `relNorm` lemma.** mathlib has `relNorm`,
`Ideal.relNorm_eq_pow_of_isMaximal` and `Ideal.relNorm_singleton`, but not
`relNorm (fiberCenter) = maximalIdeal ^ inertiaDeg` (`relNorm_fiberCenter`), nor the
`normalizedFactors` factorisation over the fibre (`relNorm_span_singleton`), nor the
element-norm transfer (`ord_norm_*`). The pin's route — `Ideal.relNorm_singleton` →
`ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal` → the `normalizedFactors`
`map_prod`/`map_pow`/`prod_pow_eq_pow_sum` computation with the fibre-centre
bijection — is transcribed as written; it is the irreducible core.

Three v4.34 shims, all in `private` proof bodies:

1. `prime_of_normalized_factor` → `UniqueFactorizationMonoid.prime_of_normalized_factor`;
2. `finiteDimensional_adjoin` → `IntermediateField.finiteDimensional_adjoin`;
3. `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` in
   `finite_setOf_ord_ne_zero_of_finiteDimensional`.

**One deliberate use of the deprecated API.** `relNorm_fiberCenter` ends by
rewriting `(maximalIdeal).inertiaDeg' P` to `P.inertiaDeg R`. The v4.34 replacement
`Ideal.inertiaDeg_eq_of_isMaximal` has the *different* shape
`q.inertiaDeg R = finrank (R ⧸ p) (S ⧸ q)`, so it cannot perform that rewrite; the
port keeps the deprecated `Ideal.inertiaDeg'_eq_inertiaDeg` (the T2 dictionary's
`inertiaDeg_eq_inertiaDeg_fiberCenter` is itself primed). The module carries
`set_option linter.deprecated false`, as `PlaceDictionary.lean` does. No statement
changed.

### 8.3 Exposure of `hasPrincipalDivisors_of_finiteDimensional_ratFunc`

It is public and the checker verifies it against its wrapper (the pin's
`S_..._of_finiteDimensional_ratFunc` copy exposes the same statement as `solution`;
the pin's `of_transcendental` copy carries it `private` under its own name). The
public `W2.hasPrincipalDivisors_adjoin` is kept public too so the adjoin `S_` file's
public original is verified. **Exposing it caused no consumer or checker issue**:
the checker's port-side count rises by exactly the four new names, and Zone I uses
it directly for `HasPrincipalDivisors K (RatFunc K)`.

## 9. SET 2 closed: the measured picture

| topic | modules | lines | public decls | checker | consumer zone | build |
|---|---|---|---|---|---|---|
| T5 | `FieldTheory/FiniteGroupAction` + `WeilExchange/Bifibre` | 264 + 361 | 2 + 12 | 600 | F, 0 errors | green |
| T6 | `WeilExchange/LocalExchange` | 206 | 3 | 603 | G, 0 errors | green |
| T8 | `PrincipalDivisors/RatFuncDegree` | 435 | 10 | 613 | H, 0 errors | green |
| T9 | `PrincipalDivisors/Transcendence` | 514 | 4 | 617 | I, 0 errors | green |

SET 2 writes **5 modules / 1,780 lines / 31 public declarations**, plus **249 lines
of consumer** (Zones F–I, 175 lines of them from Zone F onward). Final `lake build`
**4,033 jobs green, 0 warnings, no `sorry`**; `spec/check_flt_statements.py`
**617 identical (34 promoted from pin-private declarations), 0 mismatched, 0
missing, 14 own-proof declarations exempted (631 port declarations checked)**;
consumer Zones A–I **0 errors**; `#print axioms` on every SET-2 headline
`[propext, Classical.choice, Quot.sound]`.

### Against `PORTING-AC.md` §4.3's budget

The work orders priced SET 2 at 1,800–2,140 port lines (T5 560–650, T6 230–270,
T8 560–680, T9 450–540). The measured module lines are **1,780** — at the bottom of
the range — and total written lines including the consumer are **2,029**. The two
big savings are exactly the ones the blueprint predicted: T8 writes no `'`-copy
prelude (AC0's ≈214 lines) and T9 restates none of T2's 350-line dictionary. The
whole effort is now at **5,416 AlgebraicCurve + FiniteGroupAction module lines**
against §4.3's ≈4,060 deduplicated structural total and ≈5.1k–5.9k written-line
budget, i.e. at the low end, with T7 still to come.

### The SET-2 hand-off to the human's T7

`Bifibre.lean` exposes, public:
`Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`,
`Place.exists_restrict_eq`, `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber`,
and the `BifibreDev` packaging (`resHom`, `galAction` (`@[reducible]`),
`gal_smul_def`, `mem_range_resHom_iff`, `card_range_resHom`, `index_range_resHom`,
`orbit_range_resHom_eq`, `orbit_gal_eq`, `image_val_orbit`,
`forall_apply_algebraMap_eq_of_adjoin_eq_top`).

`LocalExchange.lean` exposes, public: `Place.sum_ramificationIndex_mul_inertiaDeg_exchange`
(the capstone's local identity, wrapper binders verbatim — quoted in §6.1),
`BifibreW2.exchange_of_isGalois` and
`Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable`.

The T4 prelude T7 imports rather than restates:
`BifibreDev.{restrict_restrict, toAlgHom_comp_toAlgHom, inertiaDegAlong_congr,
isIntegral_toAlgHom}` and
`Place.{ramificationIndex_eq_mul_ramificationIndex_restrict,
inertiaDeg_eq_mul_inertiaDeg_restrict}`. The `fiberAlong` API
(`fiberAlong`, `mem_fiberAlong`, `Place.restrictAlong`, `ramificationIndexAlong`,
`inertiaDegAlong`, `algebraAlong`, `Divisor.pushforwardAlong`) is AC0's in
`Defs/Correspondence.lean`, all public. The `HasPrincipalDivisors` typeclass data
T7's instances need is T9's `hasPrincipalDivisors_of_transcendental` /
`hasPrincipalDivisors_adjoin_of_transcendental` /
`hasPrincipalDivisors_of_finiteDimensional_ratFunc`.

**`WeilExchange/DivisorExchange.lean` is not written.** T7 must state its divisor
exchange and call `Place.sum_ramificationIndex_mul_inertiaDeg_exchange` for the
place `wA` of `A`, exactly as `TOPIC-t7-divisor-exchange.md` §1 describes.

## 10. T7 — the divisor exchange (the human's capstone)

Written by the reviewer, per [TOPIC-t7-divisor-exchange.md](../topics/algebraicCurve/TOPIC-t7-divisor-exchange.md).

One module, `WeilExchange/DivisorExchange.lean`, 143 lines, one public declaration:
`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`,
statement verbatim from its wrapper. This is the declaration
`ModularCurve.heckeOperatorsCommuteBar` calls at
`S_ModularCurve_heckeOperatorsCommuteBar.lean:42`.

The proof is the pin's, transcribed: the six `algebraAlong`/`IsScalarTower`/integral
installations; `hgenF` (the `K`-generation hypothesis restricted to `F`); the four
`rfl` bridges `eA`/`fB`/`fF`/`eF` (the `algebraAlong`-unfolding canary, passed);
`Finsupp.addHom_ext` on `Divisor.pushforwardAlong_single`/`pullbackAlong_single`;
`ext wB` with `Finset.sum_apply'`; the `by_cases` on
`wB.restrictAlong b hb = wA.restrictAlong a ha`, whose diagonal branch calls T6's
`Place.sum_ramificationIndex_mul_inertiaDeg_exchange` and whose off-diagonal branch
vanishes by the T4 prelude's `BifibreDev.restrict_restrict`. The pin's third copy
`BifibreWEX.restrict_restrict` is **not** reproduced — that was T4's whole point.

Two v4.34 nits, both already in the playbook's drift table or SET 1's practice:

- `if_pos`/`if_neg` are deprecated → `ite_eq_left`/`ite_eq_right` (the playbook §4
  table lists this rename; SET 1 had not hit it).
- the `letI`/`haveI` styles lint on the `haveI : FiniteDimensional …` walls → the
  same `set_option linter.style.haveILetI false` SET 1's modules carry.

Verification after T7: `timeout 300 lake build` **4,034 jobs green, 0 warnings, no
`sorry`**; checker **618 identical, 0 mismatched, 0 missing**; consumer **Zone J 0
errors**; `#print axioms` on the capstone and on the local exchange
`[propext, Classical.choice, Quot.sound]`.

### 10.1 Consumer Zone J — the cross-module wire test

Zone J adds, beyond the `#check`s at the pinned statements, a real composition:
`Divisor.correspondence_correspondence` (T4) needs a divisor-level square identity
`hex` that nothing else in the port supplies, and the capstone **is** that identity
at `(a, b, a', b') := (ψ', φ, u', u)`. The consumer's `example` discharges `hex` by
the capstone and concludes the correspondence identity — the two halves of the
effort (route A's transport and route A's exchange) meeting in one term.

## 11. The effort closed: the measured picture

| check | result |
|---|---|
| `lake build` | **4,034 jobs, 0 warnings, no `sorry`** in `FLTForHuman/` |
| `spec/check_flt_statements.py` | **618 identical (34 promoted from pin-`private`), 0 mismatched, 0 missing**, 14 exempted (632 port declarations) |
| `spec/AlgebraicCurveConsumer.lean` | **0 errors**, Zones A–J |
| `#print axioms` on `Divisor.pullbackAlong_pushforwardAlong_eq_…`, `Place.sum_ramificationIndex_mul_inertiaDeg_exchange`, `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver`, `hasPrincipalDivisors_of_transcendental`, the two generic engine lemmas, … | `[propext, Classical.choice, Quot.sound]` |
| commits | none — the working tree is the hand-off |

The ported layer, in dependency order:

| module | role | lines |
|---|---|---|
| `Defs/{Place, Divisor, PushPull, PlacesOverDVR, Correspondence, SemilinearAut, RatFuncPlaces, IntegralAdjoin}` | AC0 + T1 vocabulary and interface | 2,617 |
| `Defs/PlaceDictionary` | T2's promoted fibre dictionary (16 public) | 398 |
| `WeilExchange/FiberOverCount` | T2's three nodes | 122 |
| `WeilExchange/GaloisRamification` | T3 | 195 |
| `WeilExchange/Transport` | T4 + the shared prelude | 304 |
| `FieldTheory/FiniteGroupAction` | T5's two generic engine statements | 264 |
| `WeilExchange/Bifibre` | T5 | 361 |
| `WeilExchange/LocalExchange` | T6 | 206 |
| `PrincipalDivisors/RatFuncDegree` | T8 (10 of 11 nodes; `deg_ofHeightOneSpectrum` is AC0's) | 435 |
| `PrincipalDivisors/Transcendence` | T9 | 514 |
| `WeilExchange/DivisorExchange` | T7, the capstone | 143 |
| **total** | | **5,559** |

Against [PORTING-AC.md](../topics/PORTING-AC.md) §4.3's ≈4,060 deduplicated structural total
and ≈5.1k–5.9k written-line budget, the effort landed at **5,559 module lines** —
inside the budget, at the lower-middle. The two structural savings the plan
predicted are real and measured: the fibre dictionary written once (398 port lines
against a 737-content-line 4-copy estimate), the `P¹` classification prelude never
copied (AC0 publishes all but the dichotomy), and the `BifibreDev` prelude written
once instead of three times.

**The three generic inputs of `math/009`'s exchange reduction are now ported
theorems, not references:** the Weil exchange
(`Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`),
`separableAlong_of_charZero`, and `HasPrincipalDivisors` for the modular function
field (`hasPrincipalDivisors_of_transcendental` + `_adjoin_`). `finiteAlong_comp`
and the `Pic0` descent are in `WeilExchange/Transport.lean`.

### 11.1 Residual and deferred items

Recorded, not judged worthless:

- **The `ModularCurve` Hecke layer** (`DegeneracyTower`, `HeckeOperatorTotal`,
  `HeckeModule`, the roof square) is out of this port's scope
  ([PORTING-AC.md](../topics/PORTING-AC.md) §0's table). The AC side is unconditional; only
  that layer separates the port from `heckeOperatorsCommuteBar` itself.
- **The deprecated-`Ideal` statement migration.** Three statements
  (`PlaceDictionary`'s two centre identifications and T9's `relNorm_fiberCenter`
  proof) keep the pin's primed `Ideal` text under a reasoned
  `set_option linter.deprecated false`, because the v4.34 replacements changed
  argument order or shape. The next pin should migrate the statements and teach the
  checker the rename.
- **Deferred definition-module API**: the Galois `≃ₐ` action on
  `Place`/`Divisor`/`Pic0`, `Pic`/`torsion`/`AbelJacobiCard`,
  `SemilinearAut`'s action on `Pic0`-torsion, `Place.card_fiberOver_eq` /
  `fiber_eq_fiberOver`, `Place.finite_setOf_forall_mem_and_ord_pos`, and
  `placeOfPoint`/`Place.Congr`. Each has a `grep -c` in §1.2 or §2.4; they are
  other consumers' API.
- **T8's `WFg`/`WFj` helper block and T9's norm block** are irreducible by the
  measured audit (§8.2); no cleanup is owed.
- **`Place.FiniteResidue`** is kept though the cone does not exercise it (T8's
  `deg_ofHeightOneSpectrum` is AC0's and does not need it); it is 3 lines and is
  real API.

### 11.2 The one-line friction summary

Every topic's named shape risk **failed to materialize as a blocker** except the
`Ideal` API drift, which the manager's recon caught before the agent hit it; the
two genuinely-new pieces of mathematics (T5's orbit/index engine) transcribed from
the pin unchanged. The cost of the effort was 5,553 lines and two coding-agent runs
(one per set) plus the capstone, against a blueprint that predicted 5.1k–5.9k — so
the plan's *pricing* was accurate and its *risk register* was pessimistic. The one
recurring real cost was not mathematics but v4.34 API drift: `Set.mem_setOf_eq`,
`zero_le'`, `if_pos`/`if_neg`, `RatFunc.inftyValuation`'s new `DecidableEq`,
`Polynomial.degree_sub_lt`, `prime_of_normalized_factor`,
`finiteDimensional_adjoin`, and the deprecated `Ideal` ramification API.
