# Work order — P3.2a: the ℙ¹ place/ord dictionary

**Status: ready to dispatch.** Phase 3.2a of the row-2 re-scope:
[PLAN-P3-2.md](PLAN-P3-2.md) §3, the first engine block. Method:
[../porting-playbook.md](../porting-playbook.md) §2–§5; the build economy is
[../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3 (new files, no
cascade; per-module builds; **no whole-tree `lake build` during 3.2**).

Baseline: checker **3212 identical / 0 mismatched / 0 missing / 30 own-proof**
(3242 checked); whole-tree `lake build` green (4853 jobs); phase 3.1 landed and its
carried debt is closed.

## 0. Scope

The ℙ¹ place/ord dictionary: the `RationalFunctionField` place vocabulary
(`placeInfty` order/degree, the finite-place order `ord_placeOfPoint`,
the `principalDivisor` dictionary, `placeOfPoint`/`placeInfty` exhaustion) plus the
generic place-evaluation interface (`Place.IsRational`, `evalAt`, `evalFun`). Two
**new** modules, so the set cannot cascade.

Two groups of pin files:

1. **`Def_AlgebraicCurve_PlaceEvaluation.lean`** (86 ln, 13 decls) — **unported**
   (grep: no `IsRational`/`evalAt`/`evalFun`/`WeilReciprocity` anywhere under
   `FLTForHuman/AlgebraicCurve/`). This is a definitions prerequisite of the whole
   ℙ¹ engine, not just 3.2a.
2. **the 11 dictionary node files** (10 tiny + one 1,263-line file):

| public node | `S_` file | `S_` ln |
|---|---|---:|
| `AlgebraicCurve.Place.evalAt_algebraMap` | `…_Place_evalAt_algebraMap` | 13 |
| `AlgebraicCurve.Place.evalAt_congr` | `…_Place_evalAt_congr` | 35 |
| `AlgebraicCurve.Place.evalAt_inv` | `…_Place_evalAt_inv` | 18 |
| `AlgebraicCurve.Place.evalAt_mul` | `…_Place_evalAt_mul` | 11 |
| `AlgebraicCurve.Place.evalAt_ne_zero` | `…_Place_evalAt_ne_zero` | 27 |
| `AlgebraicCurve.Place.evalAt_zpow` | `…_Place_evalAt_zpow` | 31 |
| `AlgebraicCurve.Place.isRational_iff_deg_eq_one` | `…_Place_isRational_iff_deg_eq_one` | 21 |
| `AlgebraicCurve.RationalFunctionField.deg_placeInfty` | `…_RationalFunctionField_deg_placeInfty` | 14 |
| `AlgebraicCurve.RationalFunctionField.ord_placeInfty` | `…_RationalFunctionField_ord_placeInfty` | 14 |
| `AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap` | `…_RationalFunctionField_ord_placeInfty_algebraMap` | 12 |
| `AlgebraicCurve.RationalFunctionField.ord_placeOfPoint_algebraMap` | `…_RationalFunctionField_ord_placeOfPoint_algebraMap` | 1,263 (67 public + 3 private) |

Node list: `tools/deps/build/p32a_nodes.txt`. Measured (`port_advise`, log
`build/p32a_advise.log`): 22 target files / 91 declarations, raw ≈1,459, **1**
substitution (14 ln), no shared prelude → **≈1,445 written**.

**Measurement gaps (audit-confirmed 2026-09-30; add ~200 ln, still one set).** The
91-declaration measurement is a lower bound (playbook §2.1). Two prerequisite groups
are needed but are outside it, and both go into the new modules (so the set still
cannot cascade):

- **Gap A — the dropped `placeOfPoint` block.** The big node needs pin
  `Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean:236–274` = `placeOfPoint`,
  `placeOfPoint_def`, `placeOfPoint_eq_ofHeightOneSpectrum`, `placeOfPoint_injective`,
  `deg_placeOfPoint` (5 decls ≈39 ln), **deliberately dropped** from the port's
  `Defs/RatFuncPlaces.lean` (see that file's header). Add them to the new
  `Defs/P1Dictionary.lean`; do **not** edit `Defs/RatFuncPlaces.lean` (cascade).
  Ingredients already public: `finitePlace`, `heightOneSpectrumOfIrreducible`,
  `heightOneSpectrumOfIrreducible_asIdeal`, `Place.ofHeightOneSpectrum_injective`,
  `deg_finitePlace` + mathlib `irreducible_X_sub_C`, `natDegree_X_sub_C`,
  `Ideal.span_singleton_eq_span_singleton`, `dvd_iff_isRoot`.
- **Gap B — `PlaceEvaluationAlgebra`.** The big file's
  `reciprocity_mul_*`/`zpow_*`/`linear`/`of_ord_placeInfty_eq_zero` proofs use 6
  unported nodes of `Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean`
  (160 ln): `Divisor.evalFun_add`, `evalFun_mul`, `evalFun_ne_zero`,
  `evalFun_zsmul`, `evalFun_zpow_left`, `evalFun_single_sub_single`. None exists
  under `FLTForHuman/`. New third module `Defs/PlaceEvaluationAlgebra.lean`.

**Explicitly not this set:** the master ℙ¹ file's dictionary content
(`p1PlaceInfty`, `P1Tower`, `placeInfty_eq_p1PlaceInfty`) — that is extracted with
the engine in 3.2b–d, not here; everything from 3.2b on.

## 1. Deliverables

| new module | content | pin |
|---|---|---|
| `FLTForHuman/AlgebraicCurve/Defs/PlaceEvaluation.lean` | `Place.IsRational`, `residueInv`, `evalAt`, `evalFun`, `WeilReciprocity` + their lemmas, pin names | `Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean` |
| `FLTForHuman/AlgebraicCurve/Defs/PlaceEvaluationAlgebra.lean` | the 6 `Divisor.evalFun_*` nodes (gap B) | `Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean` |
| `FLTForHuman/AlgebraicCurve/Defs/P1Dictionary.lean` | the 11 node files' union **plus the 5 `placeOfPoint` rows (gap A)**, pin names/namespaces | the 11 `S_` files + `Def_AlgebraicCurve_RatFuncPlaces.lean:236–274` |

All three are **new** files: nothing existing is edited, so no existing module
re-elaborates. Keep the pin's namespaces (`AlgebraicCurve.Place`,
`AlgebraicCurve.RationalFunctionField`, `AlgebraicCurve`). The pin's
`p2m_*`/`attribute` scaffolding is dropped. **Never change a statement to ease a
proof.** The pin-private `isUnit_algebraMap`, `ofOption`, `ofOption_bijective`, and
`le_exp_neg_one_of_lt_one` stay `private` (see the inventory); everything the
`Theorems/` wrappers publish lands public.

## 2. Statements

Spell every public statement from its **`Theorems/Thm_*` wrapper**, not from the
`S_` file (the wrapper is the interface copy whose binders the port keeps; the `S_`
file calls its copy `solution`). The wrappers are:

```
Theorems/Thm_AlgebraicCurve_Place_evalAt_{algebraMap,congr,inv,mul,ne_zero,zpow}.lean
Theorems/Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one.lean
Theorems/Thm_AlgebraicCurve_RationalFunctionField_{deg_placeInfty,ord_placeInfty,
  ord_placeInfty_algebraMap,ord_placeOfPoint_algebraMap}.lean
```

The `ord_placeOfPoint_algebraMap` `S_` file's 66 other public declarations
(`isRational_of_deg_eq_one`, `deg_eq_one_of_isRational`,
`ord_finitePlace_ne_zero_iff`, `placeInfty_ne_ofHeightOneSpectrum`,
`eq_ofHeightOneSpectrum_or_eq_placeInfty`, `deg_placeInfty`, `ord_placeInfty`,
`principalDivisor` and its order/degree lemmas, `sum_ord_mul_deg_eq_zero`,
`placeOfPoint_ne_placeInfty`, `ord_placeOfPoint_*`, `exists_eq_placeOfPoint`,
`eq_placeOfPoint_or_eq_placeInfty`, …) are transcribed verbatim at the pin names;
`tools/deps/build/p32a_inventory.txt` is the row list with pin `file:line`.

## 3. Reuse to import, not re-prove

The port already lands these — import, do not re-prove:

- `Place.placeInfty` and the ℙ¹ place vocabulary — `Defs/RatFuncPlaces.lean`;
- `Place.eq_ofHeightOneSpectrum_or_eq_placeInfty` and
  `Place.placeInfty_ne_ofHeightOneSpectrum` — `PrincipalDivisors/RatFuncDegree.lean`
  (promoted by the phase-1 R2 round; the pin `S_` file re-proves them, so **drop
  the pin copies** and import);
- `Place.ord_nonneg_of_mem`, `Place.mem_of_ord_nonneg`, `Place.mem_iff_ord_nonneg`
  — `Defs/PushPull.lean` (the pin files import the `Theorems/Thm_*` wrappers for
  these);
- `Place.le_exp_neg_one_of_lt_one` — **name correction (audit):** the pin's public
  declaration is `AlgebraicCurve.le_exp_neg_one_of_lt_one` (the `S_` file line 194
  is *outside* `namespace Place`), while the port's `private` helper is
  `AlgebraicCurve.Place.le_exp_neg_one_of_lt_one` — a promotion would not match the
  checker. Transcribe the 14-line self-contained proof at the pin name.

**Already-ported-but-private (audit; promote or transcribe, report which):**
`RationalFunctionField.exists_sub_algebraMap_intDegree_neg`,
`RationalFunctionField.single_add_single_apply_eq_ord`,
`RationalFunctionField.degree_single_add_single` (`PrincipalDivisors/RatFuncDegree.lean`),
`Place.adicValuation_algebraMap`, `Place.isUnit_algebraMap` (`Defs/Place.lean:238/243`).
The port's `single_add_single_apply_eq_ord`/`degree_single_add_single` are **more
general** than the pin's (`{vinf}` + `hvinf`), so specialize with
`(placeInfty_ne_ofHeightOneSpectrum K)`.

**Three one-liners (audit probe, exit 0) — do not re-prove the pin bodies:**
`deg_placeInfty := RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum
(placeInfty K) (placeInfty_ne_ofHeightOneSpectrum K)`;
`ord_placeInfty := RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
(placeInfty K) (placeInfty_ne_ofHeightOneSpectrum K) hf`;
`ord_placeInfty_algebraMap := by rw [ord_placeInfty…, RatFunc.intDegree_polynomial]`.

`Defs/{RatFuncPlaces,RatFuncPlaceInfty}` are already in `SOURCES`
(`Def_AlgebraicCurve_RatFuncPlaces`, `Def_AlgebraicCurve_RatFuncPlaceInfty`); the
new `PlaceEvaluation` source is not.

**Mathlib audit (`AUDIT-mathlib-p3-2a.md`, landed: 5 SUBSTITUTE / 81
PROOF-INGREDIENT / 8 BESPOKE over 94 in-set rows, plus 11 out-of-set rows).** Per
playbook §2.2, do not re-prove what mathlib has. The audit's load-bearing results:

- `Mathlib.FieldTheory.RatFunc.Valuation` — `RatFunc.inftyValuation` /
  `inftyValuationDef` is the ℙ¹ valuation at infinity. **Confirmed connection:** the
  port's `Defs/RatFuncPlaces.lean` already defines `Place.placeInfty` with
  `toValuationSubring := (RatFunc.inftyValuation K).valuationSubring` (line 253–255),
  `placeInfty_toValuationSubring` is `rfl`, and
  `inftyValuation_isEquiv_adicValuation` is the port's
  `Place.isEquiv_adicValuation_of_valuationSubring_eq (placeInfty K) rfl`.
  **Negative:** there is no mathlib lemma `placeInfty.ord = -log ∘ inftyValuation`;
  the three ℙ¹ nodes are one-liners on the *port's* wrappers
  (`ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum`,
  `deg_eq_one_of_forall_ne_ofHeightOneSpectrum`);
- `principalDivisor` / `degree_principalDivisor` / `sum_ord_mul_deg_eq_zero`
  reduce to the port's public `degree_eq_zero_of_forall_eq_ord` (a UFD induction),
  **not** to `RatFunc.intDegree` — the earlier `intDegree` lead is a recorded
  negative for this block;
- `placeInfty_ne_ofHeightOneSpectrum`, `eq_ofHeightOneSpectrum_or_eq_placeInfty` —
  exact-name/type SUBSTITUTE from `PrincipalDivisors/RatFuncDegree.lean` (import,
  drop the pin copies);
- `isRational_iff_deg_eq_one` via `AlgEquiv.ofBijective` +
  `Subalgebra.bot_eq_top_iff_finrank_eq_one`;
- `ord_placeOfPoint_X_sub_C` via `IsDiscreteValuationRing.exists_irreducible` +
  `Place.ord_coe_irreducible` (`irreducible_iff_uniformizer`/`addVal` are off-path);
- `rootMultiplicity` API in `Mathlib/Algebra/Polynomial/Div.lean`;
  `Polynomial.multiplicity`/`emultiplicity` do not exist;
- `IsDiscreteValuationRing.{irreducible_iff_uniformizer, addVal, addVal_uniformizer}`
  and `Polynomial.{X_sub_C, rootMultiplicity, multiplicity}` /
  `RatFunc.{num, denom}` for the finite-place order lemmas.

Substitute only where the statement is `rfl`- or one-call-equal; keep every pin
statement verbatim; do not bank an unelaborated claim. Report the substituted rows.

**Confirmed on this set's path (audit):** `(placeInfty K).toValuationSubring =
(RatFunc.inftyValuation K).valuationSubring` is `rfl` in the port, and the public
`RationalFunctionField.degree_eq_zero_of_forall_eq_ord` discharges the whole
`principalDivisor` degree block. v4.34.0 drift to apply:
`Polynomial.degree_sub_lt` (big-file line 159, deprecated) →
`Polynomial.degree_sub_lt_left`; `dif_pos` → `dite_eq_left` (pin `evalAt_of_mem`).

**Recorded negatives (audit; do not repeat the search):** no mathlib
`Place.evalAt`/`IsRational`/`residueInv`/`evalFun` analogue; no mathlib
`placeInfty.ord = -log ∘ inftyValuation` bridge; the `principalDivisor` degree block
does not reduce to `RatFunc.intDegree`; `Polynomial.multiplicity`/`emultiplicity` do
not exist; `Algebra.trace_ne_zero` is not a route to the `IsRational` interface; no
mathlib `uniformizer` def (`IsDiscreteValuationRing.exists_irreducible` + the port's
`Place.uniformizer` is the route). **Import note:** do not import
`Mathlib.RingTheory.Polynomial.Roots` (no `.olean` in this checkout); use
`Mathlib.Algebra.Polynomial.{Div,RingDivision}`.

## 4. Build discipline (Deligne–Serre §3 — copy verbatim)

- Edit loop: `timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false
  <file>` — writes no `.olean`, recompiles nothing.
- File-done: `flock /tmp/flt_for_human.lock timeout 240 lake build <module>` —
  builds dependencies, never dependents.
- **No bare whole-tree `lake build`** during 3.2; one at the phase milestone.
- Never raise the heartbeat cap. No `sorry`/`admit`/`axiom`; no `import Mathlib`
  in a library module; specific mathlib imports only.
- Because both modules are new, only their own `.olean`s are written. Iterate in
  `ScratchP32a.lean` (gitignored); do not touch other `Scratch*.lean`.

## 5. Checker wiring, verification

Append **last** to `spec/check_flt_statements.py`:
- `SOURCES` += `Definitions/Def_AlgebraicCurve_PlaceEvaluation.lean`,
  `Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean`, then the 11
  `Theorems/Thm_*` wrappers, then the 11 `P2M/Sol/S_*` files (wrapper-first, as in
  the phase-1 sets). `Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean` is already
  listed, and it carries the gap-A `placeOfPoint` rows.
- `PORT_FILES` += `FLTForHuman/AlgebraicCurve/Defs/PlaceEvaluation.lean`,
  `FLTForHuman/AlgebraicCurve/Defs/PlaceEvaluationAlgebra.lean` and
  `FLTForHuman/AlgebraicCurve/Defs/P1Dictionary.lean`.

```bash
cd lean
python3 spec/check_flt_statements.py                 # 0 mismatched / 0 missing
for m in PlaceEvaluation PlaceEvaluationAlgebra P1Dictionary; do
  flock /tmp/flt_for_human.lock timeout 240 lake build "FLTForHuman.AlgebraicCurve.Defs.$m"
done
# #print axioms over the 11 public nodes
```
Expected checker: identical rises by the new public surface, `0 mismatched / 0
missing`, `30 own-proof` unless a reasoned `OWN_PROOFS` entry is added.

**Do not run any git command.** Append friction under a new `### Set 3.2a` section
in `lean/logs/riemann-roch-friction.md`.

## 6. Stop-early / gaps

- If a proof needs a declaration outside the measured files (the measurement gap),
  resolve it locally `private` with the statement verbatim and report the pin
  `file:line` — do not inline new mathematics, do not edit a frozen module.
- If the port's `Place`/`RatFunc` API drifts from the pin's by more than a rename,
  stop and report the name.
- If `PlaceEvaluation` reaches an unported definition outside its 86 lines, stop
  and report — the manager re-scopes rather than growing the set.

## 7. Report shape

Module paths + written lines; checker before → after; per-module build wall time;
the friction highlights; `#print axioms` on the 11 public nodes; the list of private
helpers kept; the `le_exp_neg_one_of_lt_one` disposition; and every out-of-set
declaration resolved locally with its pin `file:line`.
