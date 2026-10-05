# H2 — the explicit-Vélu engine: scoping, sets, and a revision of the plan

**Status: scoping (2026-10-04).** Work orders for Phase A item 3 of
[TOPIC-port-plan.md](TOPIC-port-plan.md), and a **revision** of that plan's
homes H1–H4. Pin `anthropics/fermats-last-theorem@aa2d8b3`; mathlib `v4.34.0`.
Method: [../../porting-playbook.md](../../porting-playbook.md) §2 (plan), §3.4
(sets), §3.5 (build ladder), §3.7 (order), §4 (faithfulness); measurement from
`tools/deps/port_advise.json` + `port_plan.py`. The mathematics is
[../../../studies/velu-cluster-structure.md](../../../studies/velu-cluster-structure.md)
§2.2 (Spine V).

## 1. What H2 is, measured

The plan's H2 row is the block of declarations the **four explicit-Vélu `S_`
files share** — the two `velu_map_equation_of_oddOrderSummingSet{,_of_isAlgClosed}`
and the two `exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq{,_of_isAlgClosed}`:

| quantity | measured |
|---|---:|
| declarations | 373 (249 `theorem`, 78 `def`, 46 `lemma`) |
| lines (max span over the four copies) | 7,248 (plan: 7,265) |
| **already in the port** | **65** — `eq_algebraMap_of_forall_ord_nonneg` only |
| new | ≈ 7,180 |
| copies per declaration | 4 for 369; 5/6/10 for four (shared out-of-cone) |

Two corrections to how the plan prints this row:

- The 7,265 "once" figure is a **span sum**, and spans in these files include
  the empty `<section>` skeletons between declarations. For H0 that inflated a
  36-line block to 972; here the inflation is smaller but real: the subject
  clusters below sum to ≈7,060 of the 7,248, and one declaration
  (`degree_eq_sum_support`) reads 5 lines in the map copies and 41 in the
  restrictAlong copies.
- The row said "in port 65", and that is right — but the plan's §2 *reuse-first*
  paragraph then assumed the place dictionary was already available. §2 shows
  it is not.

**The block is not one engine.** Clustered by subject (declaration-name rules;
351 of the 373, the remaining 22 assigned by hand; see §7 to regenerate):

| cluster | decls | lines | what it is |
|---|---:|---:|---|
| A place/`evalAt`/`XYIdeal` dictionary | 53 | 820 | the Weierstrass `CoordinateRing` dictionary + general AC additions |
| B rational-point map, `coordsOrZero` | 5 | 93 | `ratPointMap`/`ratPointHom`, `xOrZero`, `coordsOrZero_fst` |
| C Vélu formulas, singleton/orbit-sum | 28 | 657 | `map_veluGx/Gy/U/Quotient`, `veluXCorr`, `veluDeficit`, `veluX/Y_singleton_eq_orbitSum` |
| D deficit expansion algebra | 31 | 493 | `veluDeficitLinearTerm`, `veluDeficitBracket`, `veluDeficitPsiCofactor`, lin/quad/crossQuad |
| E cleared-polynomial degree engine | 96 | 1,597 | `veluKernelDenom`, `*PadPoly`/`*ClearedPoly`/`*DegLtAt`, `veluWeierstrassCubicPoly`, `exists_equation_of_isAlgClosed` |
| F generic point, translation, `algEquiv` | 62 | 988 | `addXFun`/`addYFun`, `genericPoint`, `translationCoordHom`, `translationAlgEquiv*`, `adjoin_addFun_eq_top` |
| G deficit-fun `ord`/`evalAt` discharge | 48 | 1,228 | `veluDeficitFun`, the `VeluDeficitFunOrdNonnegAt*` carrier chain, `evalAt_velu*_placeOfEquation` |
| H odd-order discharge | 28 | 626 | the `kw_*_odd` summing-set combinatorics |
| Z not split by the rules | 22 | 558 | mostly the `VeluDeficitFun*` carrier chain and the `eval_velu*` lemmas; belong to E and G |

(The rules split 351 of the 373; Z is assigned by hand to E/G below.)

The intra-block call graph has 498 edges, but at cluster level it is **not a
clean chain**: E and F interleave in the source (F's `translationAlgEquivOf*`
block sits after most of E), and the apparent E↔F cycle is a span artifact.
Within any one `S_` file Lean's definition-before-use rule makes **line order a
valid topological order**, which is what the module cuts below follow.

## 2. The finding that revises the plan: the dictionary is missing

Cluster A splits into two very different things.

**A1 — the deferred Weierstrass place dictionary.** Nine of the A names are
declared in `P2M/Sol/S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean`
(332 lines): `exists_eq_XYIdeal_of_isMaximal`, `isUnit_coeIdeal_of_forall_isMaximal`,
`isUnit_of_forall_isMaximal`, `isDedekindDomain_of_forall_isMaximal_isUnit`,
`isDedekindDomain_of_Δ_ne_zero`, `deg_eq_one_of_surjective`,
`deg_ofHeightOneSpectrum_eq_one`, `deg_placeOfEquation`. That file is exactly
**Deferred API entry #1 of [CARRY-FORWARD.md](../../CARRY-FORWARD.md)** — the
Weierstrass place/Riemann–Roch/class-group API, ≈941 content lines, 110 public
declarations, whose registered trigger is "the first citer:
`WeierstrassCurve.Affine.IsogenyEndDatum.*`, `WeierstrassCurve.exists_veluFunctionFieldHom_*`,
…". H2, H3, H4, H5 and H6 *are* those citers.

Cross-checked against the port: `placeOfEquation` appears in 1 port file,
`IsFinitePlace` in 1, `XYIdeal` in **0**, `exists_eq_XYIdeal_of_isMaximal` in 0,
`isDedekindDomain_of_Δ_ne_zero` in 0. The port's `placeOfPoint`/`placeOfEquation`
in `AlgebraicCurve/P1/Dictionary.lean` are the **`RatFunc`/`P¹`** dictionary, not
the Weierstrass `CoordinateRing` one. Mathlib has `XYIdeal`, `XYIdeal'` and
`quotientXYIdealEquiv` (`AlgebraicCurve/EllipticCurve/Affine/Point.lean`) but no
`exists_eq_XYIdeal`, and no Vélu at all.

**A2 — general AC additions the port lacks.** The other 44 A names are not
Weierstrass-specific: `evalAt_sum`, `evalAt_pow`, `evalAt_natCast`,
`evalAt_ofNat`, `evalAt_div'`, `evalAt_algebraMap_placeOfEquation_of_mem_XYIdeal`,
`mem_smul_iff_symm_mem`, `isFinitePlace_smul_iff_forall_symm_mem`,
`not_isFinitePlace_smul_of_symm_X_notMem`, `ord_div`, `ord_smul_of_fixed`,
`ord_nonneg_of_ord_smul_nonneg`, `forall_place_ord_nonneg_iff_finite_and_not_finite`.
They are ~490 lines and every Vélu, Isogeny and base-change file needs them.

**A3 — the Vélu vocabulary, which the plan never counted.** The 373-decl block is
only the four `S_` files' *proof-local* helpers. The `S_` files also import the
pin's definition modules, and those are not ported either:
`Def_WeierstrassCurve_Velu` (98 lines / 29 decls: `veluGx`, `veluGy`, `veluT`,
`veluU`, `veluW`, `veluTSum`, `veluWSum`, `veluQuotient`, `IsVeluSet`, …),
`Def_WeierstrassCurve_VeluQuotientMap` (74 / 9: `IsOddVeluSet`, `veluX`,
`veluQuotient_Δ`, …), `Def_WeierstrassCurve_VeluPointMap` (86 / 9: `veluXNum`,
`veluYNum`, `veluY`, `velu_singleton_equation_cleared`, …),
`Def_WeierstrassCurve_OddOrderSummingSet` (34 / 5: `coordsOrZero`,
`oddOrderSummingSet`, `mem_oddOrderSummingSet`). **292 lines / 52 declarations**,
mathlib-only, and they carry real content (`velu_singleton_equation_cleared` is
the study's "one enormous `linear_combination`"). The plan's budget is over
`S_` lines, so this layer — and every other definition module the slice
imports — is unbudgeted (playbook §2.1: "measure the definition modules
separately"). SET-1 gets a fourth module for it.

**Consequence: H2 as written (one home, "import H1 wholesale") is not
buildable.** The correct first move is a new home for A1 + A2 + A3, landed
*before* any Vélu formula. And because H5/H6 need that dictionary but **zero**
Vélu formulas (`veluDeficit`/`veluXCorr` occur 0 times in the `IsogenyEndDatum`
and base-change files; `IsFinitePlace` occurs 713 / 405 / 525 times), H5 and H6
become parallel with H2 rather than downstream of it — though this run keeps
everything sequential by decision.

## 3. Sets: three, sequential

| set | clusters | new modules | raw | written (est.) |
|---|---|---|---|---|
| **SET-1** | A + B + C + D (+ A3 vocabulary) | `AlgebraicCurve/Defs/PlaceCalculus.lean`, `WeierstrassCurve/Place/Dictionary.lean`, `WeierstrassCurve/Velu/Defs.lean`, `WeierstrassCurve/Velu/Formula.lean` | 2,063 in H2 + ≈600 CARRY-FORWARD closure + 292 vocabulary | 2,200–2,700 |
| **SET-2** | E + F | `WeierstrassCurve/Velu/Engine.lean` | 2,585 | 2,000–2,400 |
| **SET-3** | G + H | `WeierstrassCurve/Velu/Discharge.lean`, `WeierstrassCurve/Velu/OddOrder.lean` | 1,854 | 1,400–1,700 |
| capstone (manager) | H3 + H4 | `WeierstrassCurve/Velu/MapEquation.lean`, `WeierstrassCurve/Velu/RestrictAlong.lean` | 766 + 1,322 | 2,000–2,500 |

**E and F are one module, not two.** They interleave in the pin (F's
`translationAlgEquivOf*` family is declared after most of E and uses it), and
two modules with mutual imports are impossible. `Velu/Engine.lean` is the pin's
own name for that section. G and H do separate: every `kw_*_odd` declaration
sits after all of G in a `S_` file.

The four **headline theorems are the manager's capstone**, not a subagent set:
they are the review instrument (playbook §3.4). Measured against the pin, the
map column adds **39 new declarations / 762 lines** over its 173-decl prelude
(1,904 of 2,670 lines already ported; 5 further "in port" matches are
`def : Prop`/`abbrev` false positives to verify by hand), and the restrictAlong
column **66 new / 1,322 lines** — a genuine second engine
(`kwVeluXGenFun`/`kwVeluYGenFun`, `veluXClearedPoly`, `veluXDenomPoly`,
`s2c_*`, `kw_restrictAlong_*_odd`), not glue. Two attribution notes: the map
column's new block is largely *dictionary* material (`wqDiscPoly`,
`weierstrassQuadratic_separable`, the `P¹`-degree and `smul*` lemmas), which
would belong with H1w were that file not frozen — the capstone records where it
lands; and `kw_vgffhso_axiomAnchor` must be checked to be a theorem, not a pin
axiom.

### Module DAG (all new files; no existing file is edited)

```
AlgebraicCurve/Defs/PlaceCalculus.lean        A2, general AC        (leaf)
   └─ WeierstrassCurve/Place/Dictionary.lean  A1, Weierstrass       (SET-1)
        └─ WeierstrassCurve/Velu/Defs.lean    A3 vocabulary         (SET-1)
             └─ WeierstrassCurve/Velu/Formula.lean B+C+D            (SET-1)
                  └─ WeierstrassCurve/Velu/Engine.lean     E+F      (SET-2)
                       └─ WeierstrassCurve/Velu/Discharge.lean   G  (SET-3)
                            └─ WeierstrassCurve/Velu/OddOrder.lean  H (SET-3)
                                 └─ Velu/MapEquation.lean, Velu/RestrictAlong.lean  (capstone)
```
Each file imports the one above it plus H0; nothing else in the repository
imports any of them until the capstone, so every `lake build <module>` in this
effort re-elaborates exactly one file.

## 4. Build discipline (copy this block into every work order)

**The rule that matters: every file these sets write is new.** A new Lean
module has no dependents, so `lake build <module>` re-elaborates the module
(plus already-built dependencies) and triggers **no cascade**. The whole cost
model of the effort is protecting that property.

1. **Do not edit an existing module.** In particular do not append to an
   existing `AlgebraicCurve/Defs/` file. Measured dependent cascades for the
   files A2 would otherwise extend:

   | existing file | dependent cascade |
   |---|---:|
   | `AlgebraicCurve/Defs/PlaceEvaluationAlgebra.lean` | 30 modules / 15,783 lines ≈ 191 s |
   | `AlgebraicCurve/Defs/PushPull.lean` | 79 modules / 38,031 lines ≈ 465 s |

   A2 exists as the **new** `AlgebraicCurve/Defs/PlaceCalculus.lean` precisely
   to keep this cascade at zero. If a set believes it must extend an existing
   file, that is a **stop-and-report** condition: add the declaration to the
   set's new module under the right namespace instead, or send it back for a
   re-scope.
2. **Edit loop** (per declaration, writes no `.olean`, no cascade):
   `timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`.
   The two `-D` options are mandatory: `lake env lean` does not inherit the
   lakefile's `leanOptions`, so without them the cap is the default 200,000 and
   a heavy declaration reports a false timeout.
3. **Module done** (writes the `.olean`; builds dependencies, never dependents):
   `timeout 120 flock <workspace>/.lake/flt_build.lock lake build <module>`.
   One per finished file; never rebuild a file that was not changed.
   **The lock must live in the workspace, not `/tmp`.** Every tool call runs under
   `bwrap … --tmpfs /tmp`, so `/tmp/flt_build.lock` is a *fresh file per call*
   (AGENTS.md: "`/tmp` is `tmpfs`: it does not persist across tool calls") and
   serializes nothing — not across calls, and not between a manager and a
   subagent. The shared resource is the `.lake` build directory; a lock beside it
   is the only one that means anything. Measured 2026-10-04: a manager
   `lake build` issued while a subagent was building ran the full 400 s at
   `user 0m0.004s` (blocked, not compiling) and produced no `.olean`.
4. **Checker at every module close**: `python3 spec/check_flt_statements.py`
   (text-only, needs no build). This is the cheap faithfulness gate and catches
   a mis-stated binder before the build does.
5. **Never run a bare `lake build`** during the effort. The dependent cascade is
   the one unbounded cost; the whole-tree build is a single milestone gate after
   the last set, serialized with `flock` and bounded (`timeout 300`).
6. **Iterate on a hard declaration in a gitignored `Scratch.lean`** with
   `lake env lean`, not by rebuilding the module. SET-2 has a scout gate (§6).
7. **Import specifically** — the one or two modules the file needs; never
   `import Mathlib` (two such files have cost a build 2,086 → 8,936 jobs).
8. **Do not run another set at the same time** (manager's rule, and `lake build`
   is serialized anyway). A later set never edits an earlier set's file; a
   missing prerequisite is a stop-and-report, not a local patch.

## 5. Work orders

### SET-1 — the dictionary and the Vélu formulas  *(A + B + C + D)*

- **Scope.** First the missing foundation, then the vocabulary, then the local
  formulas. A1 is the deferred CARRY-FORWARD #1 dictionary; A2 its general
  additions; A3 the pin's Vélu definition modules; B/C/D the explicit-Vélu
  formulas and deficit expansion. Nothing from E/F/G/H.
- **Source.** `P2M/Sol/S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean`
  (A1, the citers' closure: 50 unwritten declarations / 1,004 lines;
  CARRY-FORWARD entry #1), `Definitions/Def_WeierstrassCurve_Velu{,.QuotientMap,PointMap}.lean`
  + `Def_WeierstrassCurve_OddOrderSummingSet.lean` (A3, 292 lines / 52 decls,
  mathlib-only), the canonical map `_of_isAlgClosed` `S_` file lines 71–138,
  2895–3114, 4964–5360 (B/C/D; A2 at 1797–1875, 7786–7838, 9097–9141), res lines
  651–718, 987–1228, 1502–1804.
- **Deliverable.** `AlgebraicCurve/Defs/PlaceCalculus.lean` (A2, under
  `AlgebraicCurve.Place`), `WeierstrassCurve/Place/Dictionary.lean` (A1, under
  `WeierstrassCurve.Affine`), `Velu/Defs.lean` (A3, pinned names), `Velu/Formula.lean`
  (B/C/D). Private silo helpers stay private (CARRY-FORWARD names them:
  `min_ord_le_ord_add`, `ord_add_eq_min`, `ord_pow`,
  `ord_ringHom_eq_natDegree_mul`, `le_ord_ringHom_of_natDegree_le`).
- **Route.** `CoordinateRing.XYIdeal` and `quotientXYIdealEquiv` are mathlib;
  `exists_eq_XYIdeal` and the Dedekind/class-number-one step are not; the Vélu
  vocabulary is mathlib-only (`DivisionPolynomial.Basic` carries `Ψ₂Sq`/`Ψ₃`).
  Recorded negatives: no mathlib `placeOfEquation`, no `exists_eq_XYIdeal`, no
  mathlib general `evalAt`, no mathlib Vélu.
- **Verification.** Checker `SOURCES` entries: the hasPrincipalDivisors `S_`
  file (deliberately absent today) for A1, the Vélu `Definitions/` files for A3,
  the map `S_` file for A2/B/C/D; `PORT_FILES` entries for the four new modules;
  a new consumer zone in `spec/WeierstrassCurveConsumer.lean` instantiating the
  dictionary and the Vélu vocabulary at a concrete curve; `#print axioms`.

#### Scoping gap found by SET-3 (2026-10-04) — the lists were not the whole slice

The three sets were scoped from the **H2 4-file block** plus the map-only and
res-only blocks. That is not the whole proof surface: the plan's own §2 block
table lists several *small cross-column* blocks that G/H also need, and the work
orders did not carry them. SET-3 hit the gap immediately:

| missing group | plan §2 block | pin |
|---|---|---|
| `mk_mem_XYIdeal_iff`, `ord_X_neg_of_not_isFinitePlace` | "66 / 2 / 7" | map `S_` |
| `centre_placeOfEquation`, `mem_centre_iff_ord_ne_zero`, `ord_placeOfEquation_{pos_iff,ne_zero_iff,nonneg}`, `algebraMap_coordinateRing_ne_zero` | "58 / 6 / 9" | map `S_` |
| `veluGy_ne_zero_of_two_nsmul_ne_zero`, `exists_some_of_ne_zero` | "64 / 2 / 6" | map `S_` |
| `nsmul_ne_zero_of_addOrderOf_eq_of_not_dvd`, `sub_nsmul_eq_neg_of_nsmul_eq_zero`, `y_ne_negY_of_two_nsmul_ne_zero` | `OrderArithmetic`/`IsOddVeluSet` | map `S_` |

Two causes, both worth fixing in the method: (1) "the block shared by all four
files" is the largest factoring unit, not the *union* of units a set consumes —
a set's list must be the union of its cluster **and** every small block the plan
already tabulated; (2) a name can be pin-public but port-`private`
(`exists_some_of_ne_zero` in `Velu/Formula.lean`), which a coverage sweep that
greps public declarations cannot see.

SET-3 transcribed them verbatim and public in its own modules (approved, to
avoid concurrent edits upstream), in a delimited `section Prerequisites`. A
**refactor round after SET-3** relocates them: the A1 dictionary group
(`mk_mem_XYIdeal_iff`, `centre_placeOfEquation`, `ord_placeOfEquation_*`) to
`WeierstrassCurve/Place/Dictionary.lean` — the `IsogenyEndDatum` home will need
it and must not import Vélu — and `exists_some_of_ne_zero` back to a single
public copy in `Velu/Formula.lean` (the `xOrZero` promotion pattern), deleting
the duplicate.

**The same root cause recurred at the capstone.** H3's headline needed
`kw_veluHPDSupplier`, the pin-private
`two_ne_zero_or_a₁_ne_zero_or_a₃_ne_zero_of_Δ_ne_zero`, and three
`kw_no6_hroute_*` — map-only declarations outside the H2 block, and so on no
list. The general rule this establishes: **a set's declaration list must be the
route closure of its deliverable, not the cluster intersection of its files.**
Concretely, before dispatching, walk the headline proof's cited names (the
`port_advise` per-node drags, or a `grep` of the pin's `solution` body) and add
every one that is neither in the port nor already assigned. H3's agent ported
the four off-list names verbatim and reported them; H4 was dispatched with the
instruction to expect the same.

### SET-2 — the cleared-polynomial engine and the generic point  *(E + F)*

- **Scope.** One module. E: `veluKernelDenom`, every `*NumPoly`/`*PadPoly`/
  `*SumPadPoly`/`*ClearedPoly` with its `_natDegree_le`/`_natDegree_lt`, the
  `VeluDeficit*DegLtAt` carriers, the alpha/beta decomposition,
  `veluWeierstrassCubicPoly`, `exists_equation_of_isAlgClosed`. F:
  `addXFun`/`addYFun` and their equation/nonsingularity lemmas,
  `genericPoint`/`mapPoint`, `addFun_neg_*`, `translationCoordHom`,
  `slope_mem_intermediateField`, `adjoin_addFun_eq_top`, `AddXFunTranscendental`,
  `translationHom`, `translationAlgEquiv*`/`translationAlgEquivOf*`,
  `genericPoint_ne_zero`/`notMem_*`, `kw_infinite_of_isAlgClosed`, `kw_hDDTerm`.
- **Source.** Canonical map lines 6582–6955, 7254–11183, 9801–9965, 10186–10385,
  8523–8563; res lines 4436–4779, 3081–7451, 7472–7610, 7663–7810. **Keep the
  pin's line order for the module's declaration order** — it is the topological
  order.
- **Scout gate (do this first).** Prototype one representative
  `*ClearedPoly_natDegree_lt` identity in `Scratch.lean` at the global heartbeat
  cap. If a direct transcription times out, push into normal form and finish with
  `field_simp; ring`; report the scout result before writing the rest.
- **Route.** The identities are `linear_combination` polynomial computations;
  `smul_basis_mul_Y`/`XYIdeal_mul_XYIdeal` are the external input; H0 carries
  everything stated over `RatFunc F`.
- **Verification.** Checker statements from the canonical map `S_` file;
  `#print axioms`; the `_natDegree_lt` declarations checked individually.

### SET-3 — the discharge and the odd-order combinatorics  *(G + H)*

- **Scope.** `Velu/Discharge.lean` (G): `liftSummingSet`, `veluDeficitFun`, the
  `VeluDeficitFunOrdNonnegAt{InftyAt,FiniteAt,KernelAt,OffKernelAt}` carrier
  chain and its recombinations, `VeluDeficitFunEvalAtPlaceAt`,
  `veluDeficitIsConstantAt_of_ordNonneg_of_*`, and the atomic/evalAt discharge
  `evalAt_veluX/Y_liftSummingSet_placeOfEquation`,
  `evalAt_veluDeficitFun_placeOfEquation`, `veluX/Y_summand_mem`,
  `Ψ₂Sq_ne_zero_of_Δ_ne_zero`. `Velu/OddOrder.lean` (H): the `kw_*_odd` family,
  `liftSummingSet_oddOrderSummingSet`, `coordsOrZero_ratPointMap`.
- **Source.** Canonical map lines 6093–6273, 7473–7928, 8218–8500, 8824–9050,
  9097–9590 (G), 11209–11889 (H); res lines 4046–4192, 5088–5356, 5550–5837,
  6156–6384, 8080–8680.
- **Route.** This set consumes SET-1's dictionary most heavily
  (`placeOfEquation`/`IsFinitePlace`/`ord_X_sub_const_placeOfEquation`). The two
  `evalAt_velu*_liftSummingSet_placeOfEquation` statements are what the capstone
  consumes; diff them before the rest.
- **Verification.** Checker statements from the canonical map and res `S_` files;
  axioms clean.

### Capstone (manager) — the four headlines

`Velu/MapEquation.lean` and `Velu/RestrictAlong.lean`: the map-column-only 766
lines and both `velu_map_equation_of_oddOrderSummingSet{,_of_isAlgClosed}`
proofs; the restrictAlong-only 1,322 lines and both
`exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq{,_of_isAlgClosed}`
proofs. Statements from the `Theorems/` wrappers, binders exactly as the
wrapper (playbook §4); port the general member and derive the plain one
(plan §3). Writing this is the wire test: a wrong binder or missing upstream
lemma surfaces as a compile failure in the reviewer's own file.

## 6. Risk register

Ordered by when they bite.

| risk | mitigation | status |
|---|---|---|
| **The dictionary was never scoped** — SET-1 carries new work the plan did not budget | this document; CARRY-FORWARD entry #1 has the measured size | resolved by §2 |
| **E's `linear_combination` degree bounds blow the defeq/heartbeat budget** | the `Scratch.lean` scout gate at the top of SET-2; normal-form + `field_simp; ring` fallback | open — gate |
| **Cluster boundaries are fuzzy** (E↔F interleave) | E+F is one module; declare in the pin's line order | resolved by §3 |
| **A set wants to extend an existing `AlgebraicCurve/Defs/` file** | 191–465 s cascade measured; A2 lives in a new file; otherwise stop and report | planned |
| **The four copies are not identical** (`degree_eq_sum_support` 5 vs 41 lines; `evalAt_inv` already ported) | take the general statement's copy; the checker diffs against every copy | planned |
| **The checker cannot see section variables** — SET-2's `Engine` carried `[IsAlgClosed F] [W.IsElliptic] [W.InfinitePlace]` and `[IsDedekindDomain W.CoordinateRing]` in sections where the pin has `{F} [Field F] {W}`, so the checker reported "identical" while the elaborated statements were strictly stronger | after any change to a section's `variable` line, `#check @<name>` every affected declaration and compare against the pin's section; treat a surviving extra instance as a fidelity bug. Fixed 2026-10-04 in `Engine`/`Dictionary`/`Discharge`/`OddOrder` (all seven checked signatures are now instance-free, verified independently) | **resolved** |
| **API drift** (`Place`/`ValuationSubring`, `Polynomial`, `HeightOneSpectrum`) | playbook §7 checklist; per-declaration `#check @name` probes | usual |
| Predicted non-event | no mathlib Vélu to replace H2 (checked 2026-10-04: no `velu*` in `Mathlib/`) | measured |

## 7. Reproduce

Regenerate the advice first (plan §6), then:

```bash
cd tools/deps
python3 - <<'PY'        # H2: decl count and once/line sum
import json
d=json.load(open('build/port_advise.json')); f=d['factor']
CANON="P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet_of_isAlgClosed.lean"
RES="P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.lean"
H2={CANON,RES,"P2M/Sol/S_WeierstrassCurve_velu_map_equation_of_oddOrderSummingSet.lean",
    "P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq.lean"}
hit=[e for e in f if set(e['target_files'])==H2]
def span(e):
    s=[o['span'] for o in e['occurrences'] if o['module'] in H2]
    return max(s) if s else 0
print(len(hit), sum(span(e) for e in hit))
PY
```

The per-cluster declaration lists are the same `factor` filter plus the §1 name
rules; regenerate them rather than trusting a stored copy. The dependent
cascades in §4 are `python3 build_ladder.py --edit <file>`. Per-declaration
authority remains `port_advise.py`; the plan layer is `port_plan.py`.
