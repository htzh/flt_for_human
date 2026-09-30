# Work order — P3.2b: the ℙ¹ residue core, chunk 1 (prelude + engine head)

**Status: ready to dispatch.** Row 2 of [../PORTING-RR.md](../PORTING-RR.md) §3,
block 3.2b per [PLAN-P3-2.md](PLAN-P3-2.md) §3. Loop: [WORKFLOW.md](WORKFLOW.md);
method [../porting-playbook.md](../porting-playbook.md) §2–§5; build economy
[../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3. A parallel audit
(`AUDIT-mathlib-p3-2b.md`) is dispatched with this order.

Baseline: checker **3316 identical / 0 mismatched / 0 missing / 30 own-proof**
(3346 checked); per-module builds green; phase 3.1 and 3.2a landed.

## 0. Scope

**One new module**, `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean`, holding
declarations **#0–#144** of the master ℙ¹ `S_` file
`P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`
(pin lines 295–3387). The inventory is `tools/deps/build/p32_master_inventory.txt`
(rows 0–144); the pin file has 580 declarations, and the later chunks (3.2c–e)
append to this same module, so **do not rename or restructure what you land**.

This chunk is:

- the **power-basis trace prelude** — `coeff_minpolyDiv_dim_sub_one`,
  `traceDual_eq_one_div_of_val_eq`, `trace_pow_div_aeval_derivative_minpoly_{of_lt,self}`,
  `trace_root_pow_div_derivative_{of_lt,self}`;
- `OrdDifferentialWellDefined` and the `lg37_*`/`Lg37CompletionSection` block;
- the **ord / valuation prelude** — `ord_add_eq_min`, `ord_nonneg_of_mem`,
  `mem_of_ord_nonneg`, `mem_iff_ord_nonneg`, `exists_ord_pos`,
  `algebraMap_ne_zero`, `comap_algebraMap_ne_top`, `mem_comap_iff_ord_nonneg`,
  `isUnit_mk_comap_iff`, `exists_ord_algebraMap_pos`, `ramificationIndex_set_nonempty`,
  `isPrincipalIdealRing_comap`, `ord_add_eq_left`, `ord_ofHeightOneSpectrum_eq_neg_log`,
  `ord_ofHeightOneSpectrum_of_span`, …;
- the `valSubring*`/`gate_*`/`OrdDifferentialWellDefined` model-predicate block.

**Much of this is already in the port.** `port_advise` on the four engine files
(log `build/p32_engine_advise.log`, JSON/§1) reports **279 substitutions / 5,477
lines** and **8,251 removable**; the engine's general machinery was already ported
by phase 3.1b-ii into `Defs/CanonicalLocalResidueInstanceV2.lean`:
`ModularCurve.Lg37.Lg37CompletionSection`, `Mp72a102T1.…exists_completion_root_of_residue_root`,
`Mp72a102T3.…sigma_taylor_expansion`, `Mp72a103T2.…taylor_coeff_eq_zero_of_depth`,
`Mp72a102T2.…residueHatAlgHom`, `Place.canonicalLocalResidueDataKOfExtend`,
`gate_uniformizer_inv_mem_simplePoleSubmodule`, the `KwNo6Pin.aCoeff*` block, … —
**import those, do not re-prove them** (see §3).

**Explicitly not this set:** declarations #145+ (chunks 3.2c–e), and the atom/base
files. Do not transcribe past the last line of declaration #144 (line 3387).

## 1. Deliverable

`FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean` — **new** file, so no cascade.
Keep the pin's namespaces (`AlgebraicCurve.Place`, `AlgebraicCurve.RationalFunctionField`,
`AlgebraicCurve`, `ModularCurve.Lg37`, `Mp72a102T1`, …). Module header: name the pin
file + pinned URL, state the chunk (rows 0–144) and that 3.2c–e append.
Drop the pin's `p2m_*`/`attribute` scaffolding; replace `import Mathlib` with
specific imports + the port's `Defs/` modules.

## 2. Statements

Spell each public statement from the pin `S_` file verbatim (there is no
`Theorems/` wrapper for most of these; where the port already has the statement,
import it — §3). **Never change a statement to ease a proof.** Pin-private helpers
stay `private`.

## 3. Reuse — import, do not re-prove

Check every declaration against `build/p32_engine_advise.log` §1 before writing it.
The load-bearing importable substitutes on this chunk's path include (from the port):

- `ModularCurve.Lg37.{lg37_completion, lg37_residueHat, lg37_residueHat_algebraMap,
  Lg37CompletionSection}` and the `Mp72*`/`KwNo6Pin` blocks —
  `Defs/CanonicalLocalResidueInstanceV2.lean` (phase 3.1b-ii);
- `Place.{ord_nonneg_of_mem, mem_of_ord_nonneg, mem_iff_ord_nonneg}` —
  `Defs/PushPull.lean`;
- `Place.mk_mem_maximalIdeal_iff` — `Genus/Index.lean`;
- `Place.{inertiaDeg_eq_inertiaDeg_fiberCenter, surjective_residueOfCenter,
  neg_log_valuation_fiberCenter_eq_ord}` — `Defs/PlaceDictionary.lean`;
- `valSubringKaehler*`, `isLocalization_centerIdeal_of_isDedekindDomain`,
  `gate_adjoin_subset_valuationSubring_of_mem`, `mem_valuationSubring_of_isIntegral*`
  — `Canonical/HasCanonicalDivisor.lean` (phase 2);
- the ℙ¹ dictionary names (`placeInfty`, `ord_placeInfty`, `deg_placeInfty`,
  `ord_placeOfPoint*`, …) — `Defs/{RatFuncPlaces,P1Dictionary}.lean` (phase 1 / 3.2a);
- the `PlaceEvaluation`/`PlaceEvaluationAlgebra` interface — phase 3.2a.

`port_advise`'s "already present" matches on trivial `def … : Prop` declarations
(`OrdDifferentialWellDefined`, `P1PlaceInftySimplePoleResidueEulerValue`, … against
`EisensteinWeightOne.E1Chi3IsModular`) are **false positives** — verify each with the
checker, do not bank them.

The parallel `AUDIT-mathlib-p3-2b.md` will add the mathlib substitutes; its
load-bearing rows are folded into this order when it lands.

**Audit result (`AUDIT-mathlib-p3-2b.md`, landed — 108 SUBSTITUTE / 30
PROOF-INGREDIENT / 7 BESPOKE over the 145 rows).** Mathlib substitutes on this
chunk: `Module.Basis.traceDual_powerBasis_eq` (pin row 1 exactly) and
`Module.Basis.trace_mul_traceDual` (rows 2–3); `minpolyDiv_monic` +
`natDegree_minpolyDiv` + `PowerBasis.natDegree_minpoly` (row 0);
`AdjoinRoot.{powerBasis, minpoly_powerBasis_gen_of_monic, powerBasis_dim}` +
`Module.Finite.of_basis` (rows 4–5); `Valuation.map_add_of_distinct_val` +
`WithZero.{log_le_log, exp_le_exp, exp_injective, exp_log, log_zpow}` (rows 7/23);
`IsDiscreteValuationRing.{exists_irreducible, ofHasUnitMulPowIrreducibleFactorization,
toIsPrincipalIdealRing}` (rows 20–22); `WfDvdMonoid.max_power_factor` +
`normalizedFactors` (rows 83/102). Recorded negatives: no mathlib `Place.ord` /
`-log∘valuation` API, no `ord_add_eq_min`/`ord_add_eq_left`, no
`IsPrincipalIdealRing`-of-comap, no single constant for row 0, no `Polynomial.multiplicity`.
Corrections: the scope is exactly rows #0–#144 (`ord_ofHeightOneSpectrum_of_span` is
row #145, out); the `PlaceDictionary` bridges named in the brief are pin lines
3829/3951/4038 — i.e. 3.2c–e, not this chunk; `PushPull.lean` carries six public ord
rows and five private. Extra drift on this path: `if_neg` → `ite_eq_right`,
`if_pos` → `ite_eq_left`.

## 4. Build discipline (Deligne–Serre §3 — copy verbatim)

- Edit loop `timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false
  <file>`; iterate in a gitignored `lean/ScratchP32b.lean` (do not touch other
  `Scratch*.lean`).
- File-done `flock /tmp/flt_for_human.lock timeout 300 lake build
  FLTForHuman.AlgebraicCurve.Defs.P1ResidueCore` (deps only).
- **No bare whole-tree `lake build`** (new file → no cascade; only its own `.olean`
  moves). No `sorry`/`admit`/`axiom`; no `import Mathlib`; never raise the heartbeat
  cap.

## 5. Checker wiring, verification

Append **last** to `spec/check_flt_statements.py`:
- `SOURCES` += `P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean`
  and its `Theorems/Thm_*` wrapper (wrapper first).
- `PORT_FILES` += `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean`.

```bash
cd lean
python3 spec/check_flt_statements.py                 # 0 mismatched / 0 missing
flock /tmp/flt_for_human.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Defs.P1ResidueCore
# #print axioms over this chunk's public surface
```
Expected: identical rises by the new public surface; `0 mismatched / 0 missing`.

**Do not run any git command.** Append friction under `### Set 3.2b` in
`lean/logs/riemann-roch-friction.md`.

## 6. Stop-early / gaps

- If a proof reaches a declaration outside the measured files, resolve it locally
  `private` with the statement verbatim and report the pin `file:line` as promotion
  debt — do not inline new mathematics, do not edit a frozen module.
- If the pin's order requires a declaration from a **later** chunk (a forward
  reference), stop and report it: the chunk boundary moves, it is not worked around.
- If `port_advise`'s substitute list and the checker disagree, the checker wins;
  report the row.

## 7. Report shape

Module path + written lines; checker before → after; per-module build wall time;
`.olean` mtime evidence that nothing else moved; `#print axioms` on the chunk's
public surface; the substitutions imported (count + the load-bearing names);
friction; private helpers kept; every out-of-set declaration resolved locally with
its pin `file:line`.
