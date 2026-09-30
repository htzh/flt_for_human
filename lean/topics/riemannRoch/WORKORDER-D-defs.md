# Work order — D: the Riemann–Roch definition layer (prerequisite set)

**Status: ready to dispatch.** Method: `lean/porting-playbook.md` §2.2 (route),
§2.4 (dedup), §3.1–§3.5, §4 (faithfulness). Plan: `PLAN.md` §1–§4. Precedent:
`deligneSerre/WORKORDER-H-homes.md`. This is **phase D**, the leaves: no theorem
target of its own, but nothing in S1–S4 can be *stated* before it lands.

## 0. Scope

Transcribe the pinned `Definitions/` modules that the phase-1 `S_` files import and
that the port does **not** yet have. Verified absent under `FLTForHuman/`: no
`LSpace`, `ell`, `repartitions`, `riemannRochSpace`, `adeleBdd`, `adeleSpace`,
`indexOfSpecialty`, `omegaSpace`, `genusFF`, `H1`, `HasCanonicalDivisor`,
`ordDifferential`, `RiemannGenusReachedAt`, `StichtenothGenusExists`.

**Explicitly not this set:** the theorem targets (S1–S4); the differentials /
residue block (`LocalResidue`, `WeilOfKaehler`, `RegularDifferentials`) belongs to
S4; anything beyond RR (Serre duality, the Weil pairing, `genusFF` computations).

## 1. Deliverables

New modules under the existing `AlgebraicCurve/` tree. Every module keeps the
pin's `AlgebraicCurve.*` names; imports are specific (never `import Mathlib` in a
library module). The port's already-ported vocabulary is **imported, not
re-proved**: `FLTForHuman.AlgebraicCurve.Defs.{Place,Divisor,PushPull,RatFuncPlaces}`
(`Place`, `Place.ord`/`adicValuation`/`deg`/`ResidueField`, `Divisor`,
`Divisor.degree`/`degZero`/`IsPrincipal`/`principal`/`HasPrincipalDivisors`/`Pic0`,
`Divisor.pullback`).

| # | new module | pin source | imports |
|---|---|---|---|
| 1 | `FLTForHuman/AlgebraicCurve/Defs/CanonicalDivisor.lean` | `Definitions/Def_ModularCurve_CanonicalDivisor.lean` (97 ln) + `Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean` (42 ln) | `Defs.Place`; `Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing`; `Mathlib.RingTheory.Kaehler.Basic` |
| 2 | `FLTForHuman/AlgebraicCurve/Defs/Repartitions.lean` | `Definitions/Def_AlgebraicCurve_Repartitions.lean` (149 ln) | `Defs.Divisor`; `Defs.Place` |
| 3 | `FLTForHuman/AlgebraicCurve/Defs/AdelicIndex.lean` | `Definitions/Def_AlgebraicCurve_AdelicIndex.lean` (435 ln) | `Defs.Repartitions` |
| 4 | `FLTForHuman/AlgebraicCurve/Defs/IsCurveOver.lean` | `Definitions/Def_AlgebraicCurve_IsCurveOver.lean` (76 ln) | `Defs.AdelicIndex`; `Mathlib.RingTheory.Kaehler.Basic`; `Mathlib.FieldTheory.IsAlgClosed.Basic` |
| 5 | `FLTForHuman/AlgebraicCurve/Defs/RiemannRochRows.lean` | `Definitions/Def_AlgebraicCurve_RiemannRochRows.lean` (66 ln) | `Defs.AdelicIndex`; `Defs.CanonicalDivisor`; `Defs.IsCurveOver` |
| 6 | `FLTForHuman/AlgebraicCurve/Defs/PoleDivisorPackage.lean` | `Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean` (101 ln) | `Defs.PushPull`; `Defs.AdelicIndex` |

Write in that order (it is the pin's own import order). Module 1 merges the
`Def_ModularCurve_CanonicalDivisor` `Place.dCoord` block with the
`Def_AlgebraicCurve_CanonicalDivisor` `HasCanonicalDivisor` block, because in the
port's tree both are `AlgebraicCurve.Place`/`AlgebraicCurve` vocabulary and the pin
split is by artifact kind, not concept (playbook §3.1).

## 2. Statements — verbatim from the pin

There are **no `Theorems/` wrappers** for these modules: the `Definitions/` files
are the authority. Transcribe every declaration's signature *textually* as the pin
writes it. **Do not paraphrase, reorder binders, or drop a hypothesis.** The
statement checker diffs text, not elaborated types.

Two `class` declarations are **omitted by the inventory tool** (see the appendix
generator) and must not be missed:
`Definitions/Def_AlgebraicCurve_IsCurveOver.lean:15 class IsCurveOver` and
`Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean:14 class HasCanonicalDivisor`.

Public declarations to land, per module (147 inventory rows; the full
`decl | kind | line | span | private` table is
`tools/deps/build/rr_defs_inventory.txt`):

- **CanonicalDivisor** — `Place.dCoord`, `Place.dCoord_ne_zero`,
  `Place.differentialCoeff`, `Place.exists_eq_smul_dCoord`,
  `Place.differentialCoeff_smul_dCoord`, `Place.differentialCoeff_unique`,
  `Place.differentialCoeff_dCoord`, `Place.differentialCoeff_zero`,
  `Place.differentialCoeff_smul`, `Place.ordDifferential`,
  `Place.gate_ordDifferential_dCoord`, `Place.ordDifferential_smul`,
  `Place.DCoordGenerates` (**class**, pin line 32);
  `HasCanonicalDivisor` (**class**), `canonicalDivisorOf`,
  `canonicalDivisorOf_apply`, `canonicalClass`, `genus`. The pin's
  `uniformizer`, `ord_uniformizer`, `uniformizer_ne_zero` are `private` — keep
  them `private` in the port (that is what keeps `OWN_PROOFS` short).
- **Repartitions** — `Place.adicValuation_le_one_of_mem`,
  `Place.adicValuation_algebraMap_le_one`,
  `Place.adicValuation_eq_exp_neg_ord`, `Place.adicValuation_le_exp_iff`,
  `Place.adicValuation_le_one_iff`, `Place.not_adicValuation_le_one_iff`,
  `repartitions`, `mem_repartitions_of_finite`,
  `mem_repartitions_of_finite_ord`, `mem_repartitions_of_forall_le_exp`,
  `repartitionsOf`, `mem_repartitionsOf_iff`, `repartitionsOf_mono`,
  `riemannRochSpace`, `mem_riemannRochSpace_iff`, `principalRepartitions`,
  `mem_principalRepartitions_iff`, `H1` (abbrev), `genusFF`.
- **AdelicIndex** — 68 declarations, listed in the appendix above; the load-bearing
  definitions are `LSpace`, `ell`, `ConstantsAreBase`, `adeleBdd`, `diagonalHom`,
  `adeleSpace`, `globalSub`, `indexOfSpecialty`, `adeleBddPrincipal`, `omegaSpace`,
  `weilDifferentialModule`, `mulAdele`, `adeleSpaceMul`, `weilSmul`,
  `residuePairing`, `WeilDifferentialRankOne`, `HasWeilCanonicalDivisor`,
  `RiemannGenusReachedAt` (structure), `RiemannGenusReached`,
  `StichtenothGenusExists`, `RiemannGenusBounded`, `IndexOfSpecialtyFinite`.
- **IsCurveOver** — `IsCurveOver` (**class**, extends `HasPrincipalDivisors`),
  `IsCurveOver.hasPrincipalDivisors`, `IsCurveOver.finite_residueField`,
  `IsCurveOver.instFiniteResidue`, `IsCurveOver.instFreeKaehler`,
  `IsCurveOver.finrank_kaehler`, `IsCurveOver.instNontrivialKaehler`,
  `Place.deg_eq_one_of_isAlgClosed_of_finite`,
  `IsCurveOver.deg_eq_one_of_isAlgClosed`,
  `IsCurveOver.forall_deg_eq_one_of_isAlgClosed` (namespaces as the pin writes).
- **RiemannRochRows** — the six predicates `RiemannInequality`,
  `RiemannIndexFormula`, `WeilDualityAdelic`, `WeilDuality`, `WeilOmegaEllAgrees`,
  `FunctionFieldRiemannRoch` and the two thin assemblies
  `functionFieldRiemannRoch_of_riemann_and_duality`,
  `weilDuality_of_riemannIndex_and_adelic`. **Warning:** `port_advise` reports
  these six `def … : Prop` as "already in the port" by a **false-positive**
  statement match against `EisensteinWeightOne.E1Chi3IsModular`
  (`PLAN.md` §1). They are **not** ported; land them here.
- **PoleDivisorPackage** — `PoleDivisorPackage` (structure),
  `HasPoleDivisorPackage`, `TranscendenceTower`, `TranscendenceTower.xF`,
  `TranscendenceTower.poleDivisor`, `TranscendenceTower.RegularOutside`,
  `IntegralBasisInLSpace`, `HasIntegralBasisInLSpace`,
  `HasIntegralBasisRegularOutside`, `HasRegularFractionSubring`.

Reuse rather than port, when the port already has the statement
(`port_advise` substitution check): `Place.*` from `Defs/Place.lean`, `Divisor.*`
from `Defs/Divisor.lean`, `Divisor.pullback` from `Defs/PushPull.lean`,
`placeInfty` from `Defs/RatFuncPlaces.lean`. Import them; do not copy.

## 3. Route and risk

- **mathlib supplies the primitives.** `ValuationSubring`,
  `IsDiscreteValuationRing.exists_irreducible`, `HeightOneSpectrum.valuation`,
  `KaehlerDifferential.D`, `Submodule.dualAnnihilator`,
  `Submodule.dualQuotEquivDualAnnihilator`, `Subspace.dual_finrank_eq`,
  `Submodule.equivMapOfInjective`, `Submodule.mem_iSup_of_directed`,
  `Module.finrank_quotient_add_finrank`. The pin declares the *statements*; the
  proofs are mostly `exact`/`simp` transcription.
- **Do not weaken.** The pin's `indexOfSpecialty` is the adelic index
  `finrank (adeleSpace ⧸ adeleBddPrincipal)`, **not** `ell (K − D)`; keep it.
  The pin's `genus` is the canonical-divisor genus `(deg K + 2)/2` with a
  `Classical.propDecidable` branch; keep the branch.
- **Stop-early risks** (stop and report, do not inline a fix):
  1. A `Place`/`Divisor` declaration the pin module uses is **not** in the port's
     `Defs/` with the identical statement. Report the pin `file:line` and the port
     delta; do **not** re-prove it into this set.
  2. `KaehlerDifferential` API drift (a name from the pin's imports no longer
     resolving) that needs more than a rename.
  3. A `class`/`structure` whose fields need an instance the port lacks.
- Keep every helper the pin keeps `private` as `private`; keep `simp`
  attributes exactly where the pin puts them (`@[simp]` on `mem_adeleBdd`,
  `diagonalHom_apply`, `differentialCoeff_*`).
- Record a negative for any mathlib search that finds nothing.

## 4. Checker wiring, build discipline, verification

**Checker wiring** (`spec/check_flt_statements.py`), appended **last** so a bare
last-name match cannot flip an earlier entry:
- `SOURCES` += the seven pin `Definitions/Def_*.lean` files of §1, in the §1 order.
  `Def_AlgebraicCurve_CanonicalDivisor` must come **after**
  `Def_ModularCurve_CanonicalDivisor`? No — the pin import order is the reverse
  (`Def_AlgebraicCurve_CanonicalDivisor` imports `Def_ModularCurve_CanonicalDivisor`);
  append `Def_ModularCurve_CanonicalDivisor`, then `Def_AlgebraicCurve_CanonicalDivisor`,
  then `Repartitions`, `AdelicIndex`, `IsCurveOver`, `RiemannRochRows`,
  `PoleDivisorPackage`.
- `PORT_FILES` += the six new modules, same order.
- Run the checker; resolve any `MISSING`/`MISMATCH` by fixing the *port statement*,
  never the pin. If a genuinely-ours declaration is needed, add it to `OWN_PROOFS`
  with a reason.

**Build discipline (copy this in).** Edit loop
`timeout 90 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`
(without the options the check runs at the default cap and lies); file-done
`flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.AlgebraicCurve.Defs.<Module>`;
**one** `lake build` per wave; no bare whole-tree `lake build`; never raise the
cap; no `sorry`/`admit`/`axiom`; no `import Mathlib`; serialize every `lake build`
with `flock`.

**Verification.**
```bash
cd lean
python3 spec/check_flt_statements.py        # expect 0 mismatched / 0 missing; identical count up by ~147
flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
# #print axioms on the six predicates + genus + indexOfSpecialty once they are public
```
Baseline before this set: **2552 identical / 0 mismatched / 0 missing / 30
own-proof exempted**.

**Do not run any git command.** Leave the tree for the manager to review.

## 5. Report shape (what to return)

1. The six module paths and their written line counts.
2. The checker line before → after, and any `OWN_PROOFS` additions with reasons.
3. Per-module `lake build` wall time (bounded), and the exact command used.
4. A friction-log block (append to `lean/logs/riemann-roch-friction.md`, create it
   if absent): every boundary stop, every false `port_advise` substitution you
   checked, every mathlib negative, every statement you had to spell against a
   wrapper rather than the pin.
5. `#print axioms` output for `AlgebraicCurve.genus`, `AlgebraicCurve.indexOfSpecialty`,
   `AlgebraicCurve.LSpace`, `AlgebraicCurve.RiemannRochRows.*`.
6. Explicit list of anything **not** landed, with pin `file:line` and why.

## Appendix — pin declaration inventory

Generated with `port_advise`'s inventory (the statement checker's own parser):
`tools/deps/build/rr_defs_inventory.txt` (`decl | kind | line | span | private`),
147 rows over the seven modules. It **omits `class` declarations**; add
`Place.DCoordGenerates`, `IsCurveOver`, `HasCanonicalDivisor` by hand.
