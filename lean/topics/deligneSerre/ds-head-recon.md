# TOPIC — the Deligne–Serre function-field head: the `AlgebraicCurve` differential / ramification tail

**Status: landed 2026-10-07; shelf re-measured 2026-10-08.** The topic itself is
complete — one set, three modules, checker `6306 identical / 0 mismatched /
0 missing` at the landing commit; [§8](#8-outcome-landed-2026-10-07)–[§11](#11-the-genusff-node-landed-2026-10-07)
are that landed record and are kept verbatim (they cite the checker and the job
counts of the landing day, not today's `6520 (312 promoted, 83 renamed), 0
mismatched, 0 missing, 36 own (6556 checked)`). **§1 is re-measured against the
current head**: the `AlgebraicCurve` differential/ramification tail planned here is
ported, and the head of the ready shelf has moved to the `ModularCurve`
q-expansion cluster, whose topic is
[../functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md](../functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md).

## 1. Where it sits (re-measured 2026-10-08)

`frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen
--rank-by silo --ready --top 0` now leaves **89 ready nodes** (it left **97** when
this topic was planned, 2026-10-07):

| namespace | nodes now | silo lines now | nodes then | silo lines then |
|---|---:|---:|---:|---:|
| `ModularCurve` | **38** | **14,819** | 41 | 18,367 |
| `WeierstrassCurve` | 8 | 3,868 | 8 | 3,868 |
| `CuspForm` | 10 | 2,843 | 10 | 2,843 |
| `AlgebraicCurve` | 23 | 2,504 | **27** | **7,550** |
| `AutomorphicForm` | 2 | 681 | 2 | 681 |
| `PeriodPair` | 2 | 601 | 2 | 601 |
| `CohCarrier` | 2 | 552 | 2 | 552 |
| `ModularForm` | 2 | 102 | 2 | 102 |
| `CuspFormClass` | 2 | 98 | 2 | 98 |
| `KaehlerDifferential` | — | — | 1 | 23 |

The `AlgebraicCurve` row is the measurement of what this topic did: **−4 nodes /
−5,046 silo lines**, exactly the four headlines of §1-then plus the three riders of
§9 and the seven `genusFF` nodes of §11 leaving the ready shelf (they are ported,
so they no longer read as demand). Everything else is unchanged except
`ModularCurve`, which grew from 41 / 18,367 to 38 / 14,819 — the four Hecke/diamond
nodes of
[TOPIC-xH-hecke-diamond-inputs.md](../hecke/TOPIC-xH-hecke-diamond-inputs.md), landed
2026-10-08, fell out of the shelf while the remaining 38 stayed.

**The head is now the `ModularCurve` q-expansion cluster.** The ready list is
ranked by silo lines, and its five largest entries are all `ModularCurve.*`
(5,900 of the silo's 14,819 lines, 40%):

| node | silo lines |
|---|---:|
| `ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd` | 1,388 |
| `ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd` | 1,221 |
| `ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion` | 1,196 |
| `ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index` | 1,095 |
| `ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField` | 1,000 |

They are a fan-out **downstream of three layers the port already carries** (the
weight-one rectification `ModularForms/WeightOne/`, JOneES `ModularCurve/X1/FunctionField.lean`,
and the `X_H` layer of SET-H-A): 249 of their 578 public declarations already have
byte-identical statements in the port. Advise on the five as one group:
`tools/deps/build/next5_advise.txt`, `next5_plan.txt`, `next5_nodes.txt`,
`next5.json`; the planning record is
[../functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md](../functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md).

The larger `ModularCurve` silo remains the Deligne–Serre column's business in the
sense of §1-then: the DS theorem sets (phase T of
[WORKORDER-H-homes.md](WORKORDER-H-homes.md)) consume it. That is a separate topic;
the five nodes above are the *ready* head and are cut on their own terms.

## 1a. Where it sat (2026-10-07, verbatim)

`frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --rank-by
silo --ready` leaves **97 ready nodes**. By cluster:

| namespace | nodes | silo lines | character |
|---|---:|---:|---|
| `ModularCurve` | 41 | 18,367 | level-`N`/`Γ₀` q-expansion, diamond-aut, Frobenius, `xH`-function-field relrank |
| `AlgebraicCurve` | 27 | 7,550 | **this topic** — genus / differentials / ramification |
| `CuspForm` | 10 | 2,843 | nebentypus, Fricke, `Γ₁` degeneracy |
| `WeierstrassCurve` | 8 | 3,868 | char-2/3 Velu, inertia, torsion Galois |
| `AutomorphicForm` | 2 | 681 | factorizable test functions |
| `PeriodPair` | 2 | 601 | `℘`-torsion modular form |
| `CohCarrier` | 2 | 552 | bottom-row / double-coset |
| `ModularForm` | 2 | 102 | `E₄³/Δ` q-expansion forms |
| `CuspFormClass` | 2 | 98 | `slash`/`heckeDiagMatrix` zeroes |
| `KaehlerDifferential` | 1 | 23 | `exists_unique_smul_D_of_transcendental` |

The four nodes above are the largest `AlgebraicCurve.*` entries and the only ones that form one
mathematical story: the differential/ramification layer **above** the ported Riemann–Roch core
(`AlgebraicCurve/{P1,Canonical,Genus,Defs}/`). The larger `ModularCurve` cluster belongs to the
Deligne–Serre column (`lean/topics/deligneSerre/`), whose `WORKORDER-H-homes.md` already names
two of its heads; those are a separate topic.

## 2. Measured cone

| metric | `genus…PerfectField` | `exists_mem_D…IsCurveOver` | `map_ne_zero_of_tame` | `two_mul_genus…canonical` |
|---|---:|---:|---:|---:|
| `S_` raw lines | 1,461 | 1,422 | 1,223 | 1,229 |
| `S_` declarations | 57 | 122 | 83 | 83 |
| `Thm_` wrapper | 1 decl | 1 decl | 1 decl | 1 decl |
| substitutions already in port | 35 / ≈989 ln | **118 / ≈1,354 ln** | 10 / ≈118 ln | 10 / ≈118 ln |
| port-`private` among those | 2 | 11 | 0 | 0 |
| same-file drags | 3, **all `[in-port]`** | 61, **all `[in-port]`** | 14 (5 `[in-port]`, 14 shared, 9 new ≈130 ln) | same as `map_ne_zero` |
| net written (estimate) | ≈400 | ≈70–150 | ≈1,100 for the pair, written **once** | — |

**Union (349 declarations across the eight pin files): 173 substitutions ≈2,579 lines already
statement-identical in the port, and 80 names proved in ≥2 target files ≈1,137 once-only
lines.** With the near-duplicate pair written once (below), the projected written volume is
**≈1,600–1,800 lines** in three modules — inside the one-subagent rule.

Substitution homes are the already-landed Riemann–Roch layer:
`AlgebraicCurve/P1/{UnitNormalForm,Dictionary,KaehlerIntegral,EnginePrelude,DivisorAction,
PerfectField}.lean`, `AlgebraicCurve/Canonical/HasCanonicalDivisor.lean`,
`AlgebraicCurve/Genus/Stichtenoth.lean`, `AlgebraicCurve/Defs/LocalResidue.lean`. Representative
landed matches: `ord_differentialCoeff_dX_ofHeightOneSpectrum` (103 ln),
`exists_sub_algebraMap_intDegree_neg` (83), `ord_placeInfty_X` (65),
`exists_unit_D_eq_smul_dCoord_s12` (56), `exists_smul_dX_eq` (55),
`dCoordGenerates_of_valSubringKaehlerSpanTop` (43), `not_dvd_derivative_of_ord_eq_one` (42),
`differentialCoeff_ne_zero` (36).

Regenerate:

```bash
cd tools/deps
python3 port_advise.py --targets build/readyHead_targets.txt --json build/readyHead_advise.json
python3 frontier.py --target AlgebraicCurve.genus_ratFunc_eq_zero_of_perfectField --no-rank
```

## 3. The near-duplicate pair (the set's dedup)

`map_ne_zero_of_tame` and `two_mul_genus_sub_two_eq_of_degree_canonical` **are the same pin
file**: `SequenceMatcher` ratio **0.977**, 693 of 700 substantive lines identical, the same 80
declarations at the same `S_` line numbers (`…:930`, `:755`, `:484`, `:1030`, `:1122`, `:213`,
`:597`, `:441`, `:321`, `:120`, `:1168`, `:838`, …). They differ only in the headline statement
(`map_ne_zero_of_tame` is the `KaehlerDifferential.map … ≠ 0` step; `two_mul_genus…` is the
Hurwitz degree formula). Writing them as two modules would duplicate ≈1,100 lines. **One home,
one engine, two headlines.**

The shared engine is the pin's Prop-class vocabulary and its reductions:
`CanonicalDifferentDegree`, `HurwitzCanonicalDecomposition`, `LocalHurwitzExponent`,
`CanonicalDivisorVariationPrincipal` (all four **absent** from the port), and
`hurwitzCanonicalDecomposition_of_tameLocalDifferent` (50),
`localHurwitzExponent_tameDifferent_of_universal` (50),
`ord_differentialCoeff_D_of_unit_mul_uniformizer_pow` (54),
`tameLocalDifferentExponent_of_localUnitDerivativeRegular_charZero` (37),
`degree_canonicalDivisor_relation_of_hurwitzCanonicalDecomposition` (28), plus the 9 genuinely
new private helpers (≈130 lines) the drags list.

## 4. Route audit (mathlib first)

**Reuse wins.** The ported vocabulary is the base and must be imported, not re-proved:
`AlgebraicCurve.Place.DCoordGenerates`, `differentialCoeff`, `ordDifferential`,
`ramificationIndex`, `Place.sum_ramificationIndex_mul_inertiaDeg` (fundamental identity),
`canonicalDivisorOf`, `HasCanonicalDivisor`, and the `P1` differential/canonical dictionary.
Mathlib supplies `KaehlerDifferential.D` / `KaehlerDifferential.map`
(`RingTheory/Kaehler/Basic.lean`, `…/TensorProduct.lean`), `PerfectField`
(`FieldTheory/Perfect.lean`), `Module.Free`/`finrank`, `IsScalarTower`, `Algebra.IsSeparable`.

**Recorded negatives.** Mathlib has no Hurwitz/ramification formula for function fields, no
abstract-place ramification index (the pin's `Place.ramificationIndex` is its own), no
"`Ω` is generated by `dπ` at a place" statement, and no canonical-different/`LocalHurwitzExponent`
vocabulary. The pin's four Prop classes and the `ℙ¹` genus computation are the new mathematics;
everything beneath them is import.

## 5. The set cut

**One set, `ds-head`, three modules** (see the work order for the exact declaration lists):

| module | contents |
|---|---|
| `AlgebraicCurve/Differential/Hurwitz.lean` | the shared Hurwitz/ramification engine **once**, plus `map_ne_zero_of_tame` and `two_mul_genus_sub_two_eq_of_degree_canonical` |
| `AlgebraicCurve/Differential/Generation.lean` | `exists_mem_D_eq_smul_D_of_isCurveOver` (its 61 drags are already `[in-port]`) |
| `AlgebraicCurve/Genus/RatFunc.lean` | `genus_ratFunc_eq_zero_of_perfectField` (its 3 drags are `[in-port]`) |

**Not this set:** the two downstream variants `AlgebraicCurve.genus_ratFunc_eq_zero` and
`genusFF_ratFunc_eq_zero_of_isAlgClosed` (they cite the head and become ready only after it);
`KaehlerDifferential.exists_unique_smul_D_of_transcendental` (23 ln, a `KaehlerDifferential`
leaf — it can ride along or wait); the `ModularCurve`/`CuspForm`/`WeierstrassCurve` clusters.

## 6. Risks and open questions

1. **The `generalise` rows.** `port_advise` flags 11 same-conclusion/different-binder names
   (take the **wrapper's** binders) and 14 same-name/different-statement names, headed by
   `ordDifferential_dX_of_ne_placeInfty_of_perfectField` and
   `differentialCoeff_placeInfty_D_X_eq`. The work order fixes these before dispatch; each must
   be resolved by reading the two statements, not by trusting the ratio.
2. **The pair's two headlines vs. the pin's `_port` copies.** Both pin files carry a
   `…_port` lemma and the `solution`; the checker wants the wrapper statement, so the module
   declares the headline at the wrapper spelling and keeps the `_port` copy only as the proof's
   local step (or drops it if the wrapper is a one-line call).
3. **The pin's `attribute [-instance]`/`[-simp]` blocks and heartbeat bumps are not
   transcribed** (the port's frozen cap is `4,000,000`); the Hurwitz engine is the heaviest
   candidate in the cluster, so price it with `build_ladder.py --edit` before a wave.

## 7. Reproduce

```bash
cd tools/deps
python3 kb_build.py
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0            # the 97-node shelf (build/ready_after_rowS.txt)
python3 port_advise.py --targets build/readyHead_targets.txt --json build/readyHead_advise.json
python3 explore.py AlgebraicCurve.genus_ratFunc_eq_zero_of_perfectField
```

`build/readyHead_targets.txt` is the four-file list; `build/` is untracked.

## 8. Outcome (landed 2026-10-07)

One set, three modules, all green. Checker **6235 → 6306 identical** (312
promoted / 83 renamed unmoved), 0 mismatched / 0 missing, 36 own-proof,
**6271 → 6342 checked**; the `+71` is the new public surface and nothing else
moved. Wave `lake build` 2861 jobs / 9.96 s; whole-tree 9329 jobs / 7.25 s;
axioms `[propext, Classical.choice, Quot.sound]`; no `sorry`; consumer exit 0.

| module | written | content | decls | public |
|---|---:|---:|---:|---:|
| `AlgebraicCurve/Differential/Hurwitz.lean` | 990 | 697 | 74 | 66 |
| `AlgebraicCurve/Differential/Generation.lean` | 40 | 6 | 1 | 1 |
| `AlgebraicCurve/Genus/RatFunc.lean` | 90 | 33 | 6 | 4 |
| `spec/DsHeadConsumer.lean` | 123 | — | — | — |

**§2 estimate reconciled.** Written 1,120 against the projected 1,600–1,800. The
pair's `≈1,100` collapsed into 697 content lines (it is one file); the two thin
modules came in at 6 and 33 content lines because their pin bodies were entirely
`[in-port]`. The 173 statement-identical declarations (≈2,579 pin lines) were all
imported, not re-proved; the 13 port-`private` rows were not needed.

**§5 set cut stood as written** — the three modules and their contents are exactly
the ones dispatched, and nothing was moved to `Defs/`. `Generation.lean` is a
1-declaration wrapper (`exists_mem_D_eq_smul_D_of_isCurveOver` over the ported
`s12` lemma); the work order's note that its 61 drags are all `[in-port]` was
correct.

**§6 risks, closed:**
1. *The `generalise` rows.* Resolved by statement-reading, not ratio: the four
   headlines take their `Theorems/` wrapper binders; the `P1` `placeInfty`/
   `p1PlaceInfty` rows are not re-declared (the port's copies verify against the
   other pin `S_` file); `canonicalDivisorOf_eq_of_forall` and
   `degree_canonicalDivisorOf_ratFunc_of_perfectField_s17` land at their pin
   statements.
2. *The pair's `_port` copies.* Dropped; the two headlines are declared once each
   at the wrapper spelling, with the engine's `map_ne_zero_of_tame_port` body
   inlined. The `solution` wrappers are not needed (the checker only reads port
   declarations, never pin-absent rows).
3. *Heaviness.* The Hurwitz engine is the heaviest module in the cluster but
   elaborates in ~20 s under the frozen `4,000,000` cap; no `attribute`/heartbeat
   bump was transcribed.

**Newly recorded (not in the §6 list).** The pin pair's two `S_` files are
byte-for-byte one development, so the dedup is a *file-level* collapse, not a
helper-level one. `RatFunc.lean` needed `P1/PerfectField.lean` (absent from the
work order's import list) and a `private` re-derivation of the 4-line
`genus_eq_degree_div` (its public home, `ResidueTheorem/RRAssembly.lean`, is a
forward import a `Genus/` leaf should not take). Both are folded into
[../logs/riemann-roch-friction.md](../../logs/riemann-roch-friction.md).

## 9. Riders (2026-10-07): two of the three deferred nodes folded in

The two genuinely small deferred nodes are folded into their natural existing
modules (no new files):

| node | home | added |
|---|---|---|
| `AlgebraicCurve.genus_ratFunc_eq_zero` (16 ln pin) | `Genus/RatFunc.lean` | 1 declaration; `PerfectField.ofCharZero` + the landed perfect-field headline |
| `KaehlerDifferential.exists_unique_smul_D_of_transcendental` (23 ln pin) | `Defs/KaehlerTranscendental.lean` | 1 declaration; 5-line proof over the ported `span_D_eq_top_of_transcendental` / `D_ne_zero_of_transcendental` |

Checker `6306 → 6308 identical` (312 promoted / 83 renamed unmoved), 0 mismatched
/ 0 missing, 6342 → 6344 checked; axioms `[propext, Classical.choice, Quot.sound]`;
no `sorry`; `spec/DsHeadConsumer.lean` gains its `[riders]` zone (exit 0). Both new
declarations are one-liner/wrapper transcriptions — the mathematics was already in
the port.

**Cost note.** `Defs/KaehlerTranscendental.lean` is a hub: `HasCanonicalDivisor`
imports it, so this one declaration cascades to **54 modules / 38,733 lines
≈ 467 s** (`tools/deps/build_ladder.py --edit`). By contrast the `Genus/RatFunc.lean`
edit is a leaf. The whole-tree build after the riders is therefore minutes, not the
seconds the ds-head leaves cost.

## 10. The third deferred node is *not* a fold (measured 2026-10-07)

`AlgebraicCurve.genusFF_ratFunc_eq_zero_of_isAlgClosed` (pin wrapper
`Theorems/Thm_AlgebraicCurve_genusFF_ratFunc_eq_zero_of_isAlgClosed.lean:14`,
71-line `S_` file) is **7 needed nodes / 790 raw lines** by
`frontier.py --target AlgebraicCurve.genusFF_ratFunc_eq_zero_of_isAlgClosed --list`:

```
AlgebraicCurve.isCurveOver_ratFunc                                  (S_ 571 ln)
AlgebraicCurve.constantsAreBase_of_isAlgClosed                      (S_  27 ln)
AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed              (S_  39 ln)
AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (S_ 39 ln)
AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch         (S_  13 ln)
AlgebraicCurve.genus_eq_genusFF                                     (S_  30 ln)
AlgebraicCurve.genusFF_ratFunc_eq_zero_of_isAlgClosed               (S_  71 ln)
```

The frontier is an upper bound: the port already has two of the seven under other
names. `isCurveOver_ratFunc` is the scoped instance
`instIsCurveOverRatFunc` (`P1/UnitFinite.lean:57`, no hypotheses beyond
`[Field K]`), and `constantsAreBase_of_isAlgClosed` is
`ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed`
(`ResidueTheorem/RRAssembly.lean:394`). The rest are thin:
`functionFieldRiemannRoch_of_isAlgClosed` is `residueTheoremK_of_isAlgClosed` +
the ported `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`;
`ell_canonicalDivisor_eq_genus_of_riemannRoch` is 6 lines over
`ell_zero_eq_one_of_constantsAreBase`; `genus_eq_genusFF` is ~30 lines over the
ported `indexOfSpecialty_eq_finrank_H1`. So the **effective** new content is
≈220 lines across `RiemannRoch/Assembly.lean`, `ResidueTheorem/RRAssembly.lean`
and `Genus/RatFunc.lean`, with two name reconciliations. None of it is new
mathematics, but it is a small set, not a fold — held pending the manager's call.

## 11. The `genusFF` node landed (2026-10-07)

All seven nodes of §10 landed. Five are thin transcriptions/wrappers over already
ported material; the two "already present under another name" rows were landed as
public wrappers at their pin names. **Module-choice deviation from §10's proposal:**
`genus_eq_genusFF` and `ell_canonicalDivisor_eq_genus_of_riemannRoch` went into
`ResidueTheorem/RRAssembly.lean`, not `RiemannRoch/Assembly.lean`. `Assembly` is a
hub — `build_ladder.py --edit` prices a one-token edit at **56 modules / 39,742
lines ≈ 484 s** — while nothing imports `RRAssembly` (0 dependents) and it already
carries the sibling genus identifications (`genus_eq_degree_div`,
`p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax`), so it is at least as natural a
home for them. The same reasoning kept `constantsAreBase_of_isAlgClosed`, the two
`functionFieldRiemannRoch_of_isAlgClosed*` wrappers, and (for the target) an added
`import KFamily` in `RRAssembly`.

| node | landed in | form |
|---|---|---|
| `isCurveOver_ratFunc` | `Genus/RatFunc.lean` | 1 line over the scoped `instIsCurveOverRatFunc` (+ `P1/UnitFinite` import) |
| `ell_canonicalDivisor_eq_genus_of_riemannRoch` | `RRAssembly.lean` | pin proof (6 lines) |
| `genus_eq_genusFF` | `RRAssembly.lean` | pin proof (~20 lines) |
| `constantsAreBase_of_isAlgClosed` | `RRAssembly.lean` | alias over `ModularCurve.p0n20_rr_…` |
| `functionFieldRiemannRoch_of_isAlgClosed` | `RRAssembly.lean` | 1-liner over the ported `…_of_residueTheoremK_…` + `residueTheoremK_of_isAlgClosed` |
| `functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver` | `RRAssembly.lean` | pin proof (instances + the previous wrapper) |
| `genusFF_ratFunc_eq_zero_of_isAlgClosed` | `Genus/RatFunc.lean` | pin proof |

Checker `6308 → 6315 identical` (312 promoted / 83 renamed unmoved), 0 mismatched /
0 missing, 6344 → 6351 checked; axioms all `[propext, Classical.choice, Quot.sound]`;
no `sorry`; `spec/DsHeadConsumer.lean` gains `[genusff]`, including the fully
concrete `genusFF ℂ (RatFunc ℂ) = 0`; whole-tree `lake build` exit 0 (9329 jobs,
~7 s — the two edited modules are leaves).
