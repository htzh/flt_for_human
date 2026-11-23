# SET-AF103 — the equivariant torsion reduction, the `j`-ramification on `X₁`, the cuspidal spectrum's approximation, and the valued field

**Status: LANDED (2026-11-23).** The next set of the AF column in the D–S cone, scoped per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. **Five orders, fourteen rows, 5,558 silo**, **five new modules**; it moved
`needed [F terminal]` by exactly its cut (339/181,644 → **325/176,086**) and made **13 new rows ready**
(5,003 silo), **five of them out of the leaves block** — the first time in this column that a set has
done that. One row (A) lands with a recorded edit-loop gap: it builds, but its `main` needs 2 M against
the 200 k detector (§6.1). It takes the
whole of the shelf's post-SET-AF102 `ModularCurve` head — the four rows that SET-AF102 itself made
ready — plus the AF-subject remainder's cuspidal-spectrum block and the `ValuationSubring` leaves.

The subject is three stories, all continuations:

* **the automorphism group as a decomposition group** — the equivariant torsion reduction over the
  `j`-line (`exists_equivariant_torsion_reduction_ofJ`), which is SET-AF101W1's stabilizer count and
  SET-AF102A3's faithful-inertia model read back on the modular curve;
* **the ramification of `j` on `X₁`** — `ord_P (jq - a) ≤ 1` for every place `P` and every
  `a ∉ {0, 1728}`, plus its `thetaL`-ratio companion; the order-theoretic half of the `jq`-integrality
  story SET-AF102M1/M2 proved the integrality half of;
* **the cuspidal spectrum as a closure** — the carrier is approached by translates of one flat
  level-spherical test function, and the cusp lift is a continuous monoid homomorphism; the two
  constituent-spine rows that make the spectrum's constituents irreducible;
* **the valued field** — the `ValuationSubring` toolbox (Krull dimension vs transcendence degree,
  transcendental residues, root counts, primitive factors) that the place calculus under every other
  order rests on; `Mathlib`-only, and the set's cheap order.

| # | order | rows | silo | module |
|---|---|---|---:|---|
| A | the equivariant torsion reduction over `j` | 1 | 1,288 | `ModularCurve/Reduction/EquivariantTorsion.lean` (new) |
| B | the ramification of `j` on `X₁` away from 0 and 1728 | 2 | 1,234 | `ModularCurve/X1/JqRamification.lean` (new) |
| C | the cuspidal spectrum approximated by one flat test function | 4 | 1,342 | `AutomorphicForm/Adelic/Cusp/SpectrumApproximation.lean` (new) |
| D | the constituent spine | 2 | 854 | `AutomorphicForm/Adelic/Cusp/ConstituentSpine.lean` (new) |
| E | the valued field toolbox | 5 | 840 | `FieldTheory/ValuationSubringValuedField.lean` (new) |
| **total** | | **14** | **5,558** | 5 new modules |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af103_read.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **339 / 181,644** |
| ready rows | 25 / 9,519 |
| leaves | 23 / 15,967 |
| withheld (FR-0044 guard) | 4 / 831 |

This is SET-AF102's landing read reproduced exactly (`lean/tmp/af102/REVIEW-CHECKLIST.md`,
`shelf_af102_landed.json`), so nothing has landed since. The corrected read is the same one — the 21
`--selfcheck` false ported markers (MD-005's phi-refactor block and MD-007) were already subtracted in
it, and all five orders below take rows that are on the *corrected* shelf.

**Four of the set's rows are SET-AF102's own payoff.** `exists_equivariant_torsion_reduction_ofJ`
(1,288) became ready when SET-AF102A3's faithful-inertia model landed on top of SET-AF101W1's
stabilizer order; `ord_sub_algebraMap_le_one_…` (1,112) and
`one_sub_ord_le_ord_…` (122) are SET-AF102M1/M2's consumers; `exists_pt_eq_of_mem` is named in §5 and
deferred. That is why this set is cut now rather than from the leaves: the shelf's head is a chain of
consumers of the last two sets.

## 1. The stories

### A — the automorphism group is the decomposition group

`exists_equivariant_torsion_reduction_ofJ`: over an algebraically closed `K` of characteristic `p` and
an elliptic `E₀/K` with `j(E₀) = j₀`, there are `M ⊇ K(t)` (`t` transcendental, `M/K(t)` finite
Galois), a place `W₀` with `W₀.ord (t - j₀) > 0`, a homomorphism `θ` from the `N`-torsion of the
`j`-model over `M` onto `E₀[N]` (injective off `p`), and `ρ` from the decomposition group of `W₀` to
the variable changes of `E₀` which is a monoid hom, commutes with the Galois action through `θ`, hits
**every** variable change up to sign, and is injective. 14 premises, and the single biggest ready row
of the set. Its definition layer is two ported `Definitions` modules
(`BaseChangeGalois`, `VariableChangePointEquiv`) — checked per FR-0298 on the `S_` file, not the
wrapper; its premises are `Automorphism/StabilizerOrder.lean` (SET-AF101W1),
`Reduction/{InertiaReduction,InertiaFaithful}.lean`, `Automorphism/{NormalForm,DeuringForm}.lean` and
`AlgebraicCurve/Place/OrbitCardinality.lean`.

Home: a new `ModularCurve/Reduction/` directory. The subject is the **fibre of the modular curve above
`j₀`** and its decomposition group, so the module sits in `ModularCurve` (the `ofJ` model and the
place `W₀` are modular-curve objects) and above every premise.

### B — the ramification of `j` on `X₁`

Two rows on the function field `F = laurentBaseChange ℂ (qExpFunctionFieldC ℚ Γ)`:

* `ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728` (1,112): for
  `Γ ≥ Γ₁(M)`, `y` the class of `jqModC`, and `a ≠ 0, 1728`, `P.ord (y - a) ≤ 1` at **every** place `P`;
* `one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion_of_gamma_le` (122): if `y · thetaL(jq)`
  maps to the `q`-expansion of a weight-2 cusp form under `σ` and `ord_P j < 0`, then
  `1 - ord_P j ≤ ord_P y`.

The first is the "`j` is unramified away from 0 and 1728" statement the whole `X₁` theory needs; the
second is its `thetaL`-ratio companion and consumes SET-AF102M1's engine. Home
`ModularCurve/X1/`, beside the function field it speaks about.

### C — the carrier as a closure

Four rows: the two carrier approximation rows (`exists_norm_toCarrier_sub_lt` at `U(N)`, and
`exists_isLevelSphericalOfType_flat_norm_toCuspSubcarrier_sub_lt_of_forall_apply_mul_eq` for an
arbitrary compact open `U`), and the two cusp-lift monoid-hom rows (`exists_monoidHom_isCuspLift_…` and
its `isCompact` variant). One subject: *the cuspidal spectrum is the closure of the translates of one
factorizable, flat, level-spherical test function*, which is what makes it a limit of
finite-dimensional `archCut` pieces.

Home: `AutomorphicForm/Adelic/Cusp/`. The four rows' premise modules are the archimedean
approximation/`archCut` family, the carrier's convolution action and the parametric-integral floor;
all ported, all imported by the scaffold.

### D — the constituent spine

The two `iInf_isCuspSubrep_inf_…` rows (level-invariant spelling, and the invariants spelling): the
intersection of the `IsCuspSubrep` submodules of the `levelInvariantSubmodule ∩ archCutSubmodule`
piece is the constituent `V`. Same subject as `Cusp/SpectrumConstituentClosure.lean`, which is one of
its premises.

### E — the valued field

Five `Mathlib`-only rows: `ringKrullDim_le_ringKrullDim_comap_add_trdeg` (269),
`exists_smul_mem_of_transcendental_residue` (262), `natDegree_map_eq_card_roots_of_splits` (174),
`tensorProduct_exists_primitive_factor` (78),
`exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero` (57). This is the `ValuationSubring` leaves
block SET-AF101 §7 named "a set of its own"; it is cut here because it is cheap and because every
other order's place calculus rests on it. Home `FieldTheory/`, in the `ValuationSubring*` family
(`Approximation`, `CompleteSplitting`, `Composite`, `Finrank`, `Polynomial`, `ResidueField`).

## 2. The scaffolds

Each module exists before its order starts, with its header prose, its `spec-pin:` wires (the
`Theorems/` wrapper and the `P2M/Sol/S_` file of every row), a narrow import list and the **headline
declarations only**, at the wrapper's statement and the published name, body `sorry`. All five were
elaborated before any order was written (each silent but for its `sorry`s) and are green:

| order | module | scaffold `check_port` |
|---|---|---:|
| A | `ModularCurve/Reduction/EquivariantTorsion.lean` | **1 ok** |
| B | `ModularCurve/X1/JqRamification.lean` | **2 ok** |
| C | `AutomorphicForm/Adelic/Cusp/SpectrumApproximation.lean` | **4 ok** |
| D | `AutomorphicForm/Adelic/Cusp/ConstituentSpine.lean` | **2 ok** |
| E | `FieldTheory/ValuationSubringValuedField.lean` | **5 ok** |
| **total** | | **14 ok / 0 / 0 / 0** |

Two scaffold findings, both about **mathlib module names in this toolchain** (v4.34, not the pin's):
`Mathlib.FieldTheory.Transcendental.Basic` does not exist — `Transcendental` is in
`Mathlib.FieldTheory.AlgebraicClosure`, with `IntermediateField.Adjoin.Algebra` for the adjoin API —
and `Mathlib.RingTheory.KrullDimension.ValuationSubring` does not exist either (`ringKrullDim`'s
lemmas are in `Mathlib.RingTheory.KrullDimension.Polynomial`). Both fail as `object file … does not
exist`, not as a name error.

One homing decision inside E: the two remaining `ValuationSubring` leaves
(`IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` 83 and `charP_residueField_of_liesOverPrime` 37) are **not**
in the module, because their vocabulary (`A.LiesOverPrime ℓ`, `A.IsFrobeniusAt σ ℓ`) lives in
`GaloisRep/Defs/` and importing it into a `FieldTheory/` module inverts the layering (SET-AF101W4's
lesson). They are deferred to a `GaloisRep`-layer order (§5), 120 silo.

## 3. The pricing

`port_plan` on the fourteen rows:

| figure | value |
|---|---:|
| raw `S_` lines | 5,558 |
| declaration lines | 5,203 |
| duplicate copies | 352 |
| boilerplate | 355 |
| distinct declaration groups | 260 |
| **already in the port (vetted)** | **2,060** (2,050 tier 1 / 10 tier 3) |
| **net new math lines** | **2,791** |
| substitutions | 110 trusted / 6 suspect |

**This set is much cheaper than its silo suggests, and that is the finding of the pricing pass**: 2,060
of its 5,203 declaration lines are already in the port under *other nodes'* names — the pins are
late-stage assembly rows whose engines (`some_congr`, `vcXInv_mul`, `inclArch`, `levelAvg`,
`isFinTestFactor_indicator`, `continuous_adelicArchGLIncl`, `mem_of_ord_nonneg`, …) were ported as
part of SET-AF100/101/102's modules. The per-block `inport` figures are the map: A 120 of 250,
B 75 of 248, C 52 of 190 and 120 of 250, D 83 of 236, E 0 of its 840 (`Mathlib`-only, all new). So
the workers' first task on each order is a **substitution pass**: read `port_advise --nodes <row>`'s
*substitute* and *port once* sections, and import what is there instead of transcribing it.

The six *suspect* substitutions are the parser's type-only `def` matches (`presSubfield → ratioField`,
`GG`/`HH` → `JOneESRat.A12`, `Kprod → BassSerre.Gp`, two `levelAvg → ArchCxGL.conjFn`) — the same
shape of false positive that made SET-AF102M2's `Δ₀ → A12` wrong (FR-0266): read the body before
believing the match. The `check_port` sizes will be measured at landing (§6), not estimated — a
SET-AF102 lesson, where three of five estimates were low.

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6: `check_port` 0 mismatch / 0 missing with every declaration `ok`; the engine gate as the
`statement_db` pin-vs-module declaration diff; `#print axioms` on every headline; the module's own
silent `lake env lean` loop and one locked `lake build`; `dedup.py --within` on a path-suffix pattern;
`move_dead.py --dry-run`; a heartbeat probe pair recorded and not installed. The set-level import probe
is `lean/tmp/af103/collision-probe.lean`. The review harness from SET-AF102 (`lean/tmp/af102/review.py`)
runs all but the build and takes any module path — use it.

## 5. Not cut — named and deferred (FR-0040)

* **`ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem`** (370) — a SET-AF102 payoff row, but
  its subject (the complex place dictionary's point identification) is its own module's story; a set
  that takes it should take the dictionary's remainder.
* **`ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary`** (951),
  `ModularCurve.StarBank.hassePolyDescent` (407), `ModularCurve.card_quotient_gamma0_le_dedekindPsi`
  (318), `GaloisRep.exists_isSemisimpleRepresentation_…` (495),
  `ModularCurve.ModularPolynomialData.eq_all` (75, the MD-005 row),
  `ModularCurve.rep_tateModule_jOne_comm` (24), `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`
  (36, the FR-0299 row), `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction`
  (59), `HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer`
  (261), and the four `TateCurve` rows (158).
* **`AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery` (1,194)** — the
  last AF-subject ready row, and deliberately not cut: its `S_` file imports **13** `Definitions`
  modules (all ported) and its headline is a ~20-binder telescope over the whole Rankin–Selberg
  machinery (`rationalCentreUnipotentQuotientMeasure`, `productionPinsOf`, `whittakerCoefficient`,
  `glArch`/`glFin`/`archComponent`, …). It is a set of its own — one order, one module, and a scaffold
  that must import the Rankin–Selberg family rather than the analyticity module. Registered in §8.
* The two `LiesOverPrime` leaves (120) — §2.
* **Two rows that an earlier draft of this set carried**: `HaarQuotient.integrable_and_integral_mul_
  comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer` (261) was to ride in order D and
  `AutomorphicForm.RankinSelberg.analyticOnNhd_sPartIntegral_and_pos_of_shell_surgery` (1,194) was to
  be order E. The pricing pass moved both: the Haar row is a `MeasureTheory/HaarQuotient*` subject, not
  the constituent spine, and the Rankin–Selberg row is a set of its own (below). The set as cut is
  therefore **5,558 silo over 14 rows**, not the 6,173 of the draft.
* `M4aTorus.completedRayL_fe` (12,126), `NumberField.*` leaves, `MeasureTheory.Lp` (148),
  `WeierstrassCurve.{stepCurve_stepSubgroup_two_eq}` (231) and
  `…exists_map_eq_veluQuotient_and_map_residue_eq_veluQuotient_reduceHom` (194), the Tate-curve
  points-law pair (471, 247, the deferred definition layer).
* Withheld by the FR-0044 guard: the four rows of §AF100 §7 / AF101 §7.

## 6. The landing

Every number below was measured twice — by the order's worker and again by the manager on the landed
files, with `lean/tmp/af103/review.py`. Four of the five orders are closed; **A is the set's one hard
row** and its state is recorded honestly at the end of this section.

| order | module | lines | checker | engine diff | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| B | `ModularCurve/X1/JqRamification.lean` (new) | **1,289** | **118 ok / 0 / 0** | 4 pin sources, 120 pin decls, 119 module decls → **118 by hash, 0 by name**, 1 unaccounted (`mem_center_iff_center`, the private helper) | 118 decls, clean | 1 (the pin's `realize_mul_`/`realize_add_eventuallyEq` pair) | 0 / 0 | 150,000 / 100,000 |
| C | `AutomorphicForm/Adelic/Cusp/SpectrumApproximation.lean` (new) | **1,161** | **8 ok / 0 / 0** | 8 pin sources, **52 wire rows**, 15 module decls → **15 by hash, 0 by name, 0 unaccounted** | 8 decls, clean | **0** | 0 / 0 | 160,000 / 130,000 |
| D | `AutomorphicForm/Adelic/Cusp/ConstituentSpine.lean` (new) | **595** | **10 ok / 0 / 0** | 4 pin sources, 31 pin decls, 18 module decls → **16 by hash**, 2 unaccounted (`prodPins`, `spine_le` — invented `private` helpers) | 10 decls, clean | **0** | 0 / 0 | 200,000 & 20,000 / 15,000 |
| E | `FieldTheory/ValuationSubringValuedField.lean` (new) | **972** | **29 ok / 0 / 0** | 10 pin sources, 34 pin decls, 29 module decls → 28 by hash, 1 by name (`_hker`), **0 unaccounted** | 29 decls, clean | **0** | 0 / 0 | 20,000 / 15,000 |
| A | `ModularCurve/Reduction/EquivariantTorsion.lean` (new) | **1,436** | **65 ok / 0 / 0** | 2 pin sources, 66 pin decls, 70 module decls → **65 by hash, 0 by name**, 5 unaccounted (the `private` carves `torsion_card_eq_sq`, `gK_conj_mul`, `eq_of_forall_nsmul_eq_of_faithful`, `exists_good_model_route`, `stabilizer_card_bound`) | 65 decls, clean | **0** | 0 / 0 | **`main` 2,000,000 / fails 1,500,000 — §6.1** |

**The set's `check_port` sizes are 8 / 10 / 29 / 118 and not the silo.** Three count rules were
measured here, and they are the landing table's real content:

1. a **pair of pins sharing one engine** gives `check_port` = distinct engine rows + headlines
   (**D: 10** against my ≈20 estimate — the second copy would have been a `dedup` cluster);
2. a **mostly-`private` pin** gives `check_port` = its public rows only (**C: 8** against 52 wire
   rows), so the pin-vs-module diff, not the checker, is the completeness evidence (FR-0277);
3. the **diff is the only size figure that means anything** — B's 118/118 and E's 29/29 are exact,
   C's 52→15 is complete with 0 unaccounted, D's 31→18 has exactly its two invented helpers.

**The set's most repeated finding is FR-0266, three times over and always the same shape** — a
type-only `def` match offered by `port_advise` that is not importable:

* `levelAvg → ArchCxGL.conjFn` is *conjugation*, not level averaging (D: the six rows are transcribed);
* `Pres`/`mu` in `ModularCurve/ComplexPlaceDictionaryAction.lean` are `private`, spelled `realizeOf`
  vs `realizeG`, and stated at a fixed `X Γ` (B: the pin's engine is transcribed, and the substitute
  saving is confined to proof bodies — `strictPeriods_eq_zmultiple_of_T_mem`,
  `Place.min_ord_le_ord_add`'s arity, the v4.34 `FunLike.coe_*` spellings);
* and the two `mem_of_ord_nonneg` hits differ by an `hf : f ≠ 0` (B).

So this set is **not** cheaper than its silo in the way `port_plan`'s 2,791 net lines suggested: the
2,060 "already in the port" lines are largely *private* or differently stated, and only C's and D's
substitutions (27 of C's rows from `ArchInfra`, the one-line `commute_of_glArch_*`/`glFin_eq_one_*`
calls in D) actually removed declarations from the port's ledger. The rest was re-transcribed, as the
checker's exact sizes show.

### 6.1 A — the heartbeat wall, and what it means

A's `main` needs **≈2.1 M heartbeats** against the project's 200 k edit loop; the pin bought it with
`set_option maxHeartbeats 16000000` and `synthInstance 1600000`, neither of which a port module may
carry. The worker measured, in this order: the pin's `attribute [-instance]` wall transcribed for the
eleven names that exist in the port's closure (330 s → 167 s wall, no statement moved, so it halves);
`synthInstance.maxHeartbeats` raised to the pin's 1.6 M (187 s vs 167 s, no errors — so **no single
instance search is the defect**, the cost is cumulative); per-region attribution (setup ≈80 s, the
`Nat.card` bullet ≈88 s, the final `γ` bullet ≈236 s, of which the pin's 180-line `have key` block is
essentially all).

The route is the playbook's: **restructure, not exempt** — the low-cap ladder first
(`40000/20000/10000/5000/1000`, one run per value: the earliest cap at which the file still fails
localises the stuck step), then `set_option diagnostics true` on that step to name the comparison, then
the fix (a named instance, an ascribed `have`, a detour — FR-0074's `RingEquiv`, FR-0088's
`Module.Free`, FR-0302's explicit `Algebra.IsIntegral`), and only if the trace shows the cost is
*spread* the carve — the pin's 180-line `have key` block as one `private` lemma first (not eight),
re-measured with the low cap as the acceptance test (a helper silent at 5,000 is healthy) and the
TwoCurveDescent caution (the helpers' budgets must sum below the removed one). Wall-clock comparisons
are not the instrument; the question is only "does it fit inside `timeout N` at cap N".

**The transcribed `attribute [-instance]` wall is a diagnostic, not a shipped artefact.** Transcribing
the eleven names that exist in the port's closure did halve the cost (330 s → 167 s, no statement
moved), which confirms the wall's nature — instance-search pruning — but the project's recorded
position is that the walls are scaffolding the port does not carry (`PORTING-AC`: "disable instances
that the port either does not import or wants. None of it is ported"; `PORTING-MC`: "drop the pin's
scaffolding, not its mathematics"; `TOPIC-abel-jacobi-port-structure` §5/§6.1: "must not add them
back — they are the place the build will misbehave if it does"), and an instance trimmed for the pin's
generated proofs does not compose with the port's different import graph. So the order's acceptance
criterion is a **wall-free `main` at the 200,000 default**, with the cap ladder reported both ways
(wall in / wall out); if the wall-free file does not fit, that is a search the fix did not reach, not a
licence to restore the wall. All 65 pin rows stay public and at the pin's names, so `check_port` must
stay 65 ok. Whatever the outcome, the row's *statements* are landed and green; the open question is
only the proof's elaboration budget.

**The outcome (measured, accepted with a recorded gap).** The low-cap ladder found the one real defect
(the `stabilizer_card_bound` defeq trap, FR-0304, fixed), three carves landed (`torsion_card_eq_sq`
and `exists_good_model_route` silent at 50,000, `stabilizer_card_bound` at 200,000, plus `gK_conj_mul`),
and the def-layer hypothesis was **falsified** (hoisting `gK`/`ρ` to named `private def`s moved no gate
and broke a `rw` match — reverted). The wall was removed (its two ladders are identical in shape, so it
bought only wall-clock time). Two more carves then landed — `gK_conj_mul` (the pin's `hc4`, "the residue-induced variable change is
multiplicative", silent at 50,000) and `eq_of_forall_nsmul_eq_of_faithful` (the pin's `hLfix`, generic in
`F`/`Ω`/`E`, silent at 50,000) — which removed the 400 k and 800 k sites but **did not move the
bracket**: `main` fails 200 k / 500 k / 750 k / 1 M / 1.5 M and is silent at **2,000,000**. The
residual sites are now the pin's own `θ`/`ρ` construction and the `γ` bullet's tail.

**It is accepted, because the package's own build cap settles it**: `lean/lakefile.lean:11` ships
`⟨\`maxHeartbeats, (4000000 : Nat)⟩`, so `lake build` gives the module 4 M — and it builds:
`✔ Built FLTForHuman.ModularCurve.Reduction.EquivariantTorsion (66 s)`, `Build completed successfully
(3474 jobs)`, **0 warning lines from this file**. So the tree is green and the residual is a
**discipline gap in the edit loop** (200 k, the detector), not a build failure — the first such
exception in this column, and recorded as one: the 200 k edit loop reports `main` only, and the two
remaining sites (the `θ`/`ρ` construction and the `γ` tail) are registered in CARRY-FORWARD for a
refactor round. Five `private` carves are in the file and every one fits 200 k except
`stabilizer_card_bound`, which sits exactly at it. Nothing is installed: no
`set_option maxHeartbeats`, no `synthInstance.*`, no `attribute [-instance]`/`[-simp]` wall.

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' <the 21 selfcheck names>) > build/shelf_af103_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` (corrected read) | 339 / 181,644 | **325 / 176,086** |
| ready rows | 25 / 9,519 | **29 / 9,804** |
| leaves | 23 / 15,967 | **18 / 15,127** |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |

The delta is **−14 nodes / −5,558 lines**, which is *exactly* the cut — and the composition of the two
blocks moved in a way no previous set of this column achieved: **9 ready rows left** (A, B's two, C's
four, D's two = 4,720 silo) and **5 leaves left the leaves block** (E's five, 840 silo), while
**13 rows became ready** (5,003 silo):

* `AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector` (**1,219**) — C's consumer,
  the idempotent archimedean projector, which is exactly what C's "one flat level-spherical test
  function" was for;
* `ModularCurve.two_mul_genusFF_add_card_fibres_le_finrank_add_two_of_gamma1_le` (**812**) — B's
  consumer (the genus/fibre-count inequality the `j`-ramification bound feeds);
* `AlgebraicCurve.RationalFunctionField.ord_placeInfty_eq_ord_placeInfty_add_sum_ord_placeOfPoint_of_reduction`
  (**604**), `AlgebraicCurve.exists_regularProlongation_retraction_of_constantField_valuationSubring`
  (**300**), `AlgebraicCurve.RegularProlongation.exists_of_forall_mem_adjoin_iff_of_isAlgebraic`
  (**221**) — three rows that were **leaves** and are now ready, unblocked by E's valuation toolbox;
* `AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero`
  (**483**), `…exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt`
  (**363**), `…exists_idempotent_levelAverage_of_isCompact` (**274**) — C's and D's consumers in the
  spectrum;
* `ModularCurve.ord_le_three_and_ord_sub_le_two_and_ord_sub_le_one_laurentBaseChange_qExpFunctionFieldC_algebraicClosure`
  (**346**), `…mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion` (**163**)
  — B's and M1's continuation of the `jq`-order story;
* `AutomorphicForm.CuspidalConstituent.inf_eq_bot_or_le_of_isCuspConstituent` (**101**) — D's consumer;
* `ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one` (**75**) and
  `…exists_polynomial_map_residue_ne_zero_eval_mul_mem` (**42**) — two rows that were **leaves**,
  unblocked by E.

**Five leaves became ready**, which is the first time in this column that a set has moved rows *out of*
the leaves block rather than only consuming the ready one — and it is E, the cheapest order of the set
(840 silo, `Mathlib`-only), that did it.

## 8. What the set leaves behind

The landing table (§6 of the AF102 pattern), the per-order reports in `lean/tmp/af103/`, a shelf
re-read, the frictions hit — and three things worth carrying: `ModularCurve/Reduction/` as the home
directory for the `j`-fibre/decomposition-group mathematics, the `Cusp/SpectrumApproximation` module as
the statement of "the spectrum is a closure" that the constituent spine consumes, and the two mathlib
module-name facts of §2 that cost a compile each.
