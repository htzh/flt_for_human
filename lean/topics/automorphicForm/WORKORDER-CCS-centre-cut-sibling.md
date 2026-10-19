# WORKORDER-CCS — the centre-cut sibling and the shared engine

One set: the sibling headline plus the extraction of the block the two centre-cut leaves share.
Mathematics and landing record: [../../logs/centre-cut-sibling.md](../../logs/centre-cut-sibling.md);
the first leaf is [../../logs/centre-cut-vanishing.md](../../logs/centre-cut-vanishing.md). Column:
[../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3.

**Status: landed 2026-10-18.**

## 1. Scope

| | |
|---|---|
| pin statement authority | `Theorems/Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre.lean` (17 lines) |
| pin proof | `P2M/Sol/S_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre.lean` (892 lines) |
| isolated budget | 892 raw lines, 51 groups; `port_advise` reports 46 declarations / 636 lines already in the port (private), 0 substitutions |
| dedup finding | the two pin `S_` files share the 645-line / 47-declaration block byte-for-byte; the only shared helper missing from the port is `toFun_unipT_mul` |
| deliverable | one 59-line façade + the extracted 964-line engine; **net new mathematics is the sibling headline** |
| expected checker delta | **+1** (the sibling); the first leaf's +1 is unchanged |

**Not this set:** the larger `coversModCentre` silo
(`exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre`, 3,038 lines),
which is behind the unit-factorizable chain; the rest of the centre-cut shelf; any change to the
definition layer.

## 2. The structure decision

Copying the sibling's shared 636 lines would be the second copy of a development the port already
holds. Promoting the 46 declarations in place would make the first leaf's module the shared home
and leave its name a misnomer. The order therefore extracts the shared block:

1. `FLTForHuman/AutomorphicForm/Adelic/Cusp/CentreCutEngine.lean` — 964 lines, 49 public
   declarations under `namespace AutomorphicForm.CentreCutEngine`, each with a
   `-- pin: <pin name> (<S_ file>:<line>)` marker. Unlisted (tier 3), registered by
   `unwired_register.py`.
2. `FLTForHuman/AutomorphicForm/Adelic/Cusp/CentreCutVanishing.lean` — reduced to a 64-line
   façade: the first headline only.
3. `FLTForHuman/AutomorphicForm/Adelic/Cusp/CuspUnrealizable.lean` — 59-line façade: the sibling
   headline only.

The common tail is generalized once: the engine's `no_function_of_ne_zero` takes
`ξ, φ, hauto, hcont, g₀, hg₀`. The sibling's pin-specific `no_realization_of_ne_zero` is not
ported; the headline feeds `R.centralChar`, `R.toFun`, `R.smoothCusp.1.1`, `hR`,
`R.exists_ne_zero` into the general lemma.

## 3. Deliverables

* engine imports only `FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent`; the façade and the
  sibling import the engine;
* the two headlines state the wrappers verbatim; no helper is public in a listed module;
* the engine's public surface is marker-registered, not checker-diffed.

## 4. Known drift

The engine carries the two `v4.34.0` adaptations from the first leaf
(`coe_mapGL_lowerUnip`, `aC_unipAdelic`) and the deprecation renames; see
[../../logs/centre-cut-vanishing.md](../../logs/centre-cut-vanishing.md) §4. The sibling headline
itself needs no drift fix: its proof is the general lemma instantiated at `R`.

## 5. Build discipline

* edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`;
* `flock .lake/flt_build.lock timeout 300 lake build <module>` (the engine first, then the
  façades);
* no whole-tree build; no `sorry`/`admit`; no heartbeat override; no `import Mathlib`.

## 6. Wiring (manager)

* `SOURCES`: add the sibling's `Theorems/` wrapper and `S_` file; the engine is not listed;
* `PORT_FILES`: keep `CentreCutVanishing.lean`, add `CuspUnrealizable.lean`; the engine stays
  unlisted;
* run `python3 ../tools/deps/unwired_register.py` to write the 49 engine rows.

## 7. Results

* edit loop: 0 errors / 0 warnings for all three modules;
* `lake build`: engine 9.7 s (3,622 jobs), sibling 3.0 s (3,623 jobs);
* checker: **10,239 identical**, 0 mismatched / 0 missing, 10,476 checked;
* `#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`;
* register current; 49 engine declarations with pin provenance;
* `git status`: the three modules, the checker wiring, the regenerated register, and the records.
