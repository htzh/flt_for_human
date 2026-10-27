# SET 4 — the silo tails and the now-ready `AlgebraicCurve` rows

**Status (2026-10-27): landed and green.** All four orders are in, the set's final targeted build
over its eleven modules exits 0 with 0 warnings from them, and every module reports
`0 mismatch / 0 missing`. §1.1–§1.3 are the landing records; §0 is the scoping method.

Cut from the D–S shelf **after** SET 3 landed, read canonically
(`python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0`, JSON in
`tools/deps/build/frontier-set4.json`):

| figure | value |
|---|---|
| ready candidates (all namespaces) | 96 |
| `AlgebraicCurve` rows | **14** |
| their silo lines | **4,410** |
| of which in new modules | 2,229 (four modules) |
| of which insertions into existing modules | 2,181 |

SET 3 consumed 17 rows; these 14 are what the wave left, and three of them are new arrivals
(`Place.evalAt_norm_eq_prod_fiber`, `Place.ordDifferential_D_eq_zero_…`, `genusFF_sub_one_…`)
that became ready *because* the wave promoted and wired the norm block.

**The method this brief follows is now written down** in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) — the read,
the story groupings, the pricing, the homing rule and the instrument failures. Read it before
cutting SET 5.

## 0. Homing, checked against the dependency direction first

Every home below was verified with the rule FR-0037 left: **a node's module must be at or above
the port modules its pin proof consumes**. The method, reproducible:

1. for each node, read the `import Theorems.Thm_*` lines of its pin `S_` file — its premise nodes;
2. map each premise's wrapper *statement* to the port module holding a statement-identical
   declaration (the checker's own normaliser over `twin_scan`'s port index);
3. build the port's module import closure (`lean/tmp/mod-above.json`) and keep the modules above
   all of them (a module counts as above *itself*).

| node | silo | prem | home |
|---|---:|---:|---|
| `Divisor.mapDomain_placeReduction_correspondence` | 925 | 6 | **new** `AlgebraicCurve/ConstantReductionCorrespondence.lean` (no existing module is above its four) |
| `Place.evalAt_norm_eq_prod_fiber` | 672 | 8 | **new** `Place/EvalAtNorm.lean` |
| `Pic0.natCard_torsion_eq_of_constantFieldExtension` | 541 | 5 | insert `Genus/ConstantFieldExtension.lean` |
| `Place.ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem` | 517 | 3 | insert `Differential/RegularDiffs.lean` |
| `finrankAlong_eq_and_trace_eq_of_constantFieldExtension` | 407 | 1 | insert `IsCurveOver/ConstantFieldExtensionSpan.lean` |
| `Place.connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex` | 369 | 7 | **new** `Place/ComplexDictionary.lean` |
| `finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin` | 348 | 4 | insert `IsCurveOver/ConstantFieldExtensionSpan.lean` |
| `genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord` | 263 | 15 | **new** `Genus/SplittingFieldGenus.lean` |
| `exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed` | 99 | 7 | insert `Genus/ConstantFieldExtension.lean` |
| `exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed` | 93 | 1 | insert `IsCurveOver/ConstantFieldExtension.lean` (+ migrate it) |
| `Pic0.exists_mk_eq_forall_notMem_support` | 60 | 1 | insert `Place/OrderArithmetic.lean` (re-homed: `Defs/Divisor.lean` is below the approximation layer, so the ordered home was a cycle — the worker caught it) |
| `mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain` | 51 | 1 | **new** `Place/EvalAtNorm.lean` (it must also import `Place/ConstantFieldExtensionRamification.lean`) |
| `Place.ordDiff_eq_ordDifferential` | 44 | 4 | insert `Differential/RegularDiffs.lean` |
| `SemilinearAut.pushforward_smul` | 21 | 2 | insert `WeilExchange/GaloisRamification.lean` |

**The instrument failed the first time, twice** (recorded as FR-0038): the statement-hash
premise mapping misses a premise whose wrapper writes its binders inline while the port
transcribes the pin `S_` copy's section variables, misses a premise the port lacks (it would be
imported by the node's proof, not stated by it), and the port index is cached — a run before a
wave lands maps against a stale tree. Name-based mapping then over-approximates wildly. So the
machine table is a *first cut* and each home was confirmed by hand against the pin proof's uses;
where the two disagree, the proof wins.

**Homing is by mathematics, and a legacy home is not a reason to move.** Where the subject names a
module in the frozen checker, the module is migrated in the same touch; the cost is paid whether or
not this set pays it. The one veto is the import direction (a home below the proof's premises is a
cycle). The separable-adjoin row below is the correction of this wave: it was first put in
`IsCurveOver/Transcendental.lean`, and re-homed to the legacy `IsCurveOver/ConstantFieldExtension.lean`
once the subject was followed rather than the migration avoided.

Every insertion target is **wired and green** before the wave starts (`Genus/ConstantFieldExtension`
4 pins, `Differential/RegularDiffs` 2, `IsCurveOver/ConstantFieldExtensionSpan` 3,
`IsCurveOver/Transcendental` 3, `Defs/Divisor` 2, `WeilExchange/GaloisRamification` 7 — the last one
migrated in this wave's ground prep). (`IsCurveOver/ConstantFieldExtension.lean` was the second and is migrated by §1.2.)

## 1. The cut

| order | work order | object | nodes | silo | homes |
|---|---|---|---:|---:|---|
| 1 | [WORKORDER-BC6-reduction-tail.md](WORKORDER-BC6-reduction-tail.md) | the reduction/reduction-correspondence tail and two cheap leaves | 3 | 1,006 | 1 new + 2 insertions |
| 2 | [WORKORDER-BC7-cfe-invariants.md](WORKORDER-BC7-cfe-invariants.md) | the constant-field-extension invariants: torsion order, index of specialty, degree/trace, place counts, separable adjoin | 5 | 1,488 | 3 insertions |
| 3 | [WORKORDER-BC8-place-differential.md](WORKORDER-BC8-place-differential.md) | the place/differential dictionary: the norm's value at a place, the two orders of a differential, the vanishing along the extension, RR coefficients descending | 4 | 1,284 | 1 new + 1 insertion |
| 4 | [WORKORDER-BC9-genus-complex.md](WORKORDER-BC9-genus-complex.md) | the Kummer splitting-field genus and the complex place dictionary | 2 | 632 | 2 new |

The four orders touch **disjoint files**, so they are safe to run concurrently; the only shared
resource is the build lock, which every order already serializes on.

## 1.1 Order 1 (BC6) — landed 2026-10-27

| item | value |
|---|---|
| new module | `AlgebraicCurve/ConstantReductionCorrespondence.lean`, **619** lines, 12 public declarations, **13 ok** / 0 / 0 |
| insertions | `WeilExchange/GaloisRamification.lean` 7 → **9 ok** (adds `SemilinearAut.restrict_smul`, the pin prerequisite, and `pushforward_smul`); `Place/OrderArithmetic.lean` 8 → **9 ok** (the moving lemma under `namespace Pic0`) |
| build | 5.9 s / 4.3 s / 6.5 s, **0 warnings** from the three |
| axioms | four probes (`mapDomain_placeReduction_correspondence`, `exists_mk_eq_forall_notMem_support`, `pushforward_smul`, `restrict_smul`) all `[propext, Classical.choice, Quot.sound]` |

**The new module is a dedup lesson, not a transcription.** The pin's `S_` file carries the whole
place-centring/valuation/extension/fibre prelude as its own copy; the port already owns every
piece of it, so the module imports and qualifies them — sixteen declarations from
`CentredPlaceRigidity`, `IsCurveOver/BaseChangeCorrespondence`, `Place/ConstantFieldExtension` and
`Place/IntegralClosureAtFiber` — and declares only the 11 in-scope helpers plus the headline
against the pin's 29. That is why 925 silo lines became 619.

**Two re-homes, both the worker's catch.** `Pic0.exists_mk_eq_forall_notMem_support` was ordered
into `Defs/Divisor.lean`, which is below every approximation module, so its proof could not import
`Place.exists_forall_ord_eq_finset` without a cycle; it now lives in `Place/OrderArithmetic.lean`,
the module that proves the approximation theorem (see FR-0038 for why the manager's mapping missed
it). And `SemilinearAut.pushforward_smul` needs the pin node `SemilinearAut.restrict_smul`, which
the port lacked — ported public at the pin's name into the same module, with its own wrapper and
`S_` file on the wire, rather than hidden as private glue.

## 1.2 Order 2 (BC7) — landed 2026-10-27

| module | added | checker | build |
|---|---|---|---|
| `Genus/ConstantFieldExtension.lean` (+603) | `Pic0.natCard_torsion_eq_of_constantFieldExtension` (541-line node, engine private in `W7XL2`), `exists_indexOfSpecialty_mapDomain_eq_zero_…` | 4 → **4 ok** / 0 / 0 | 0 warnings |
| `IsCurveOver/ConstantFieldExtensionSpan.lean` (+760) | `finrankAlong_eq_and_trace_eq_of_constantFieldExtension`, `finrank_le_and_natCard_places_le_…_adjoin` (engines private in `TraceBaseChangeProof`, `ConstantFieldAdjoin`) | **7 ok** / 0 / 0 | 0 warnings |
| `IsCurveOver/Transcendental.lean` (+91, later −101) | `exists_finiteDimensional_isSeparable_adjoin_…` — **re-homed** to the module below (see the note) | 6 → **5 ok** / 0 / 0 | 0 warnings |

Pure insertions (1,454 lines added, 0 deleted); five axioms probes clean; no module-level
`maxHeartbeats`, no `sorry`, no marker row.

**Two reported dependency choices, both accepted.** The `indexOfSpecialty` node's pin helper
`W7XChildE.constantsAreBase` is the statement the module already proves privately as
`TorsionDescentDeriv.constantsAreBase_of_isAlgClosed`; Lean privacy is per-file, so the worker
reached it through a six-line private adapter rather than promoting or restating — nothing written
twice, no existing declaration touched. The 541-line torsion node reuses the public
`ConstantFieldPlaceLift.ord_eq_zero_of_mem_of_inv_mem`, `Place.ord_algebraMap_base` and
`WXH.linearIndependent_pow_of_transcendental` instead of carrying the pin's copies; its
`linearIndependent_adjoin_simple_of_pow_mul` is re-proved by clearing denominators over `K'⟮x⟯`
because v4.34 no longer supplies the `Algebra ↥(Algebra.adjoin K' {x}) ↥(IntermediateField.adjoin K' {x})`
instance the pin's `LinearIndependent.localization` call needs — statement unchanged.

**The re-home (2026-10-27, after review).** The separable-adjoin node first went to
`IsCurveOver/Transcendental.lean` — the wrong reason, a non-legacy module chosen to dodge a
migration. Its subject is the constant field extension, so it now lives in the legacy
`IsCurveOver/ConstantFieldExtension.lean`, which was migrated in the same touch: five `spec-pin:`
sources (both linear-independence wrappers, both `S_` copies, and this node), the `PORT_FILES` row
replaced by a `MIGRATED` note, **26 ok / 0 mismatch / 0 missing**, 12 s build, both headlines
axiom-clean, and the frozen checker still green at 7,356 identical / 0 / 0. `Transcendental.lean`
shrank to 5 ok and keeps its own `isCurveOver_iff_…` node.

**One residual, recorded not raised.** `finrank_le_finrank` (a helper of the 348-line counts node)
needs the pin's own 1.6M heartbeat budget: the pin's `set_option maxHeartbeats` was dropped as the
rule requires, and the module elaborates under the library's 4M, so the gate is met — but the
declaration does **not** fit the 200k edit-loop cap, which is the project's instance-inference
detector. By the playbook's own rule that is a symptom, not a budget: the pin's bump here was *not*
precautionary. It is logged for a build-cost pass
([../notes/lean-build-cost.md](../notes/lean-build-cost.md), `build_ladder.py --profile`), not
exempted and not raised in source.

## 1.3 Orders 3 and 4 (BC8, BC9) — BC9 landed, then its surface corrected

| module | checker | build | state |
|---|---|---|---|
| `Genus/SplittingFieldGenus.lean` (new, 198 lines) | **1 ok** / 0 / 0 | 6.7 s, 0 warnings | landed; the headline fits the 200k cap |
| `Place/ComplexDictionary.lean` (new, 325 lines) | **1 → 10 → 12 ok** / 0 / 0 | 4.7 s / 4.4 s, 0 warnings | landed, surface corrected (§ below) |
| `Place/EvalAtNorm.lean` (new, 726 lines) | **2 → 27 ok** / 0 / 0 | 31 s, 0 warnings | landed; surface promoted at review |
| `Differential/RegularDiffs.lean` (+406, pure addition) | **8 → 13 ok** / 0 / 0 | 11 s, 0 warnings | landed; surface promoted at review |

Both headlines axiom-clean. Two decisions taken at review, both from the same principle:

- **The genus node's twelve `*_pkg` shims are not carried.** They are instantiation plumbing with
  generated names (§3.1: a generated token is rectified, not carried), and `Genus/HurwitzBound.lean`
  already derives the same instances inline and applies the port's generic theorems — the worker
  followed that precedent, so the module is 198 lines against the pin's 263. The two human-named
  helpers (`transcendental_algebraMap`, `finiteDimensional_adjoin_algebraMap`) are pin-public and go
  to BC9b, which promotes them or drops them for a port-public twin.
- **The complex node's engine is not allowed to stay private.** Its pin `S_` file has 19 public
  declarations; ten are statement-identical to existing port declarations (used, not restated) and
  **nine are new pin-public lemmas** which BC9b promotes at the pin's names and makes diff. Hiding
  them was the wrong default: a private engine is mathematics the next theory re-derives, and the
  port's rule is that a pin-public statement is public and checked.

### The surface correction, as landed

`Place/ComplexDictionary.lean` now declares **12** public declarations and the checker diffs all
of them: the headline, the **nine** promoted dictionary lemmas (`finite_setOf_ord_ne_zero`,
`exists_nonconst_mem_of_ne`, `reading_center`, `eventually_mem_chart`, `tendsto_reading`,
`continuousAt_reading`, `analyticAt_reading`, `continuousAt_evalAt`, `false_of_isClopen`, in the
pin's namespace `ConnectedOfCharted`), and the two definitions the promoted statements are spelled
with — `reading` and `OrderHypothesis`.

Three findings from that round, worth carrying:

- **Two of the three "the port already has it" claims were wrong.** `Place.chartRead` *is*
  statement-identical to the pin's `reading`, so `reading` is an `rfl`-level alias of it (public,
  one implementation, two names — `dedup.py` sees no cluster inside the module). But
  `OrderHypothesis` is **not** `PeriodPair.DiscriminantNeZero` (an unrelated lattice-discriminant
  condition) and `functionFieldRiemannRoch` is **not** the port's
  `functionFieldRiemannRoch_of_isAlgClosed` (a different RatFunc-tower instance set); `port_advise`'s
  shape tier can pair a `def … : Prop` with any other `Prop`-valued `def` of the same size, so both
  texts were read before deciding.
- **A pin `def` written `variable (F) in … def foo : Prop` must be transcribed that way.** Spelling
  the binders inline builds but reports `MISMATCH` (the checker extracts the statement without the
  prefix), and the docstring must sit *after* the prefix or the file does not parse. That cost one
  iteration here and is now a drift-table row.
- `Genus/SplittingFieldGenus.lean` ends at **3 ok**: the headline plus the two pin-public helpers
  `KummerGenusReduction.transcendental_algebraMap` and `finiteDimensional_adjoin_algebraMap`; the
  twelve `*_pkg` shims stay out. The port has no statement-identical copy of either helper (the
  four-field `transcendental_algebraMap`s are `private` elsewhere and the adjoin-transport copy is
  `private` with a different instance argument), so promoting them was right.

Both modules: 0 warnings from their own build, axioms clean (headline, `false_of_isClopen`,
`OrderHypothesis`), `dedup.py`/`move_dead.py` clean.

### BC8's surface, promoted at review

The worker kept both nodes' engines `private` (precedent: `Differential/ConstantFieldExtension.lean`)
and flagged it. The pin's two `S_` files have **26 and 29 declarations, none private**, so the same
rule as BC9b applies — and the experiment showed the transcription was pin-faithful, so the
promotion was nearly free:

- `Place/EvalAtNorm.lean`: dropping `private` from all 27 declarations gave **27 ok / 0 mismatch /
  0 missing** on the first run. The whole pin node is now diffed, not two declarations of it.
- `Differential/RegularDiffs.lean`: unprivating gives 13 `ok`, 8 `MISMATCH`, 3 `MISSING`. The 3
  missing are port-side helpers (`irreducible_uniformizerSubring`, `exists_unit_mul_zpow_uniformizer`,
  `D_ne_zero_of_transcendental'`); the 8 mismatches are the **pin's prelude copies** whose statements
  differ from the port's public `Place.*` forms (e.g. a `mem_iff_ord_nonneg` without the `≠ 0`
  hypothesis), so they are local re-spellings, not duplicates: they and the 3 stay `private`, the
  other 13 are public and checked.

Both modules build silently (31 s and 11 s), the four headlines are axiom-clean, `dedup.py` reports
one false positive in `EvalAtNorm` (`conductorIdeal_ne_top` / `conductorIdeal_ne_bot` — two different
statements about one object, which the shape tier pairs), and `move_dead.py` reports nothing.

### The set's final gate

One targeted build of the **eleven** modules SET 4 created or edited — `ConstantReductionCorrespondence`,
`Place/OrderArithmetic`, `WeilExchange/GaloisRamification`, `Genus/ConstantFieldExtension`,
`IsCurveOver/{ConstantFieldExtensionSpan, Transcendental, ConstantFieldExtension}`, `Place/EvalAtNorm`,
`Differential/RegularDiffs`, `Genus/SplittingFieldGenus`, `Place/ComplexDictionary` — exits 0 with
**0 warnings from any of them** (the 30 in the log belong to pre-existing dependency modules).

## 2. Definition of done (unchanged from SET 3)

- **no tree build, ever**: the gate is one targeted build of exactly the modules the order
  creates or edits, `flock`-serialized and `timeout`-bounded; no dependents;
- `check_port.py --force <module>` → **0 mismatch, 0 missing** on each module, the added
  declaration listed `ok` (or `own:` recorded by the manager);
- `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`;
- 0 warnings; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`;
- the order appends the wrapper **and** the `S_` file of every node it adds to its module's
  `spec-pin:` block;
- no worker edits a module outside its order's list, promotes a `private` helper, or adds a
  `spec/decl_markers.tsv` row (the manager owns markers and promotions).
