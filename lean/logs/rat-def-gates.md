# The two `Rat*` definition gates

**Landed 2026-10-20, manager's own set.** The two `Definitions/` modules that blocked the
`RatAdele` and `RatIdele` families of the six-family audit are homed whole, verbatim, each with
its own `spec-pin:` wire. With them, **(3) of the audit is unblocked**: both nodes are
statement-ready (and `RatIdele` already had every theorem premise ported).

## 1. What landed

| module | pin source | declarations | build | checker |
|---|---|---:|---:|---|
| `FLTForHuman/LanglandsTunnell/StandardLocalConstantsAt.lean` | `Definitions/Def_LanglandsTunnell_StandardLocalConstantsAt.lean` (144 lines, 799 pin importers) | 21 | 3.9 s, 0 warnings | **21 ok, 0 mismatch, 0 missing** |
| `FLTForHuman/NumberTheory/RatIdele/Normalizer.lean` | `Definitions/Def_RatIdele_Normalizer.lean` (391 lines) | 63 | 4.0 s, 0 warnings | **63 ok, 0 mismatch, 0 missing** |

Both are tier 1 by their own header, no `decl_markers.tsv` entry, no `PORT_FILES` edit.

Axioms on the key declarations of both modules (and on the definitional rewrites):
`[propext, Classical.choice, Quot.sound]`.

## 2. What they sit on

* `StandardLocalConstantsAt` imports the already-homed `NumberField/AdelicTraceFin.lean`
  (`stdAddChar`, `adelicTraceData`, `continuous_psiK`) and
  `LanglandsTunnell/TateLocalConstantsAt.lean` (`higherUnitsAt`, `conductorExponentAt`,
  `localEpsilonAt`). Of the pin's three `Definitions/` imports, `Def_NumberField_AdelicBox` is
  homed (`NumberTheory/AdelicBox.lean`, finite half in `AdelicLevel/IdealBall.lean`) and
  `Def_Mathlib_…RestrictedProduct…` is inert for the node (0 uses); mathlib v4.34 supplies the
  `RestrictedProduct.single`/`inclusion` API the gate's own proof uses.
* `Normalizer` imports `NumberTheory/AdelicLevel/HeckeGen.lean` (`finIncl`, `localUnit` and
  their `_apply_self`/`_apply_of_ne` lemmas — the port of the pin's `Def_NumberField_AdelicLevel`
  `Gen` section) and mathlib `Mathlib.NumberTheory.Padics.HeightOneSpectrum` (`natGenerator`,
  `primesEquiv`, `intEquiv`), `AdicValuation`, `AdeleRing`, `Completion.InfinitePlace`,
  `InfinitePlace.Basic`, `Units.Basic`, `FinBigOperators`.

## 3. Adaptations (proof only; no statement touched)

1. **`FiniteAdeleRing.ext` is namespaced in v4.34.** The pin's
   `FiniteAdeleRing.ext K fun w => rfl` resolves in the port to a *different* ext lemma (the
   `NumberField.FiniteAdeleRing` one) unless fully qualified. The transcription uses
   `IsDedekindDomain.FiniteAdeleRing.ext K fun w => rfl`, the same call the port already makes in
   `AutomorphicForm/Adelic/ArchKFiniteFamily.lean:459`.
2. **`Set.mem_setOf_eq` is deprecated** in v4.34; the two `simp`/`rw` uses are now
   `Set.mem_ofPred_eq`. No other proof drift; every other name the pin uses exists unchanged.

Both are exactly the kind of drift the work order's risk list expects: they are recorded here
rather than as `own:` deviations because the statements are unchanged.

## 4. State of the two families

`frontier.py --ds` reads both families exactly as before (they are unported nodes, 1 / 309 and
1 / 312), but the audit's blockers are gone:

* `RatAdele.denseRange_algebraMap_add_adeleSingleAt` — statement constants now homed:
  `NumberField.StandardAddChar.adeleSingleAt`, `AdelicBox.adelicBox`,
  `NumberField.AdeleLevel.integralFiniteAdeles`; the pin `S_` file's `RestrictedProduct` import is
  inert.
* `RatIdele.exists_norm_apply_eq_ideleNorm_rpow` — the proof's `ρ`/`ρ_spec`/`ρ_ne_zero`/
  `IsNormalizer`/`archCoord`/`finPart` API is now importable; the statement constants
  (`NumberField.TateGlobal.ideleNorm`, `AutomorphicForm.IsIdeleClassChar`) were already homed.

Neither node was ported here: they are a node-level set of their own (309 + 312 pin lines), now
**ready** under the same audit they failed before.

## 5. Reproduce

```bash
cd lean
python3 spec/check_port.py FLTForHuman/LanglandsTunnell/StandardLocalConstantsAt.lean
python3 spec/check_port.py FLTForHuman/NumberTheory/RatIdele/Normalizer.lean
lake build FLTForHuman.LanglandsTunnell.StandardLocalConstantsAt
lake build FLTForHuman.NumberTheory.RatIdele.Normalizer
```
