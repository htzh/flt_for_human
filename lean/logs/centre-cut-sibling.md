# The centre-cut sibling — `AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre`

**Status: landed 2026-10-18.** One façade module,
`FLTForHuman/AutomorphicForm/Adelic/Cusp/CuspUnrealizable.lean` (59 lines, one
public headline), green with 0 errors and 0 warnings; no `sorry`, no axiom
beyond `[propext, Classical.choice, Quot.sound]`. The shared development was
extracted to `Cusp/CentreCutEngine.lean` (964 lines, 49 public declarations,
tier 3). Checker **10,239 identical**, 0 mismatched / 0 missing; the new
module's wire is exactly +1.

| | |
|---|---|
| statement | `AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre` |
| pin proof | `P2M/Sol/S_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre.lean` (892 lines) |
| statement authority | `Theorems/Thm_AutomorphicForm_not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre.lean` |
| scope (isolated) | 892 raw lines, 51 declaration groups; **46 declarations / 636 lines already in the port** (private in the vanishing leaf), 243 net new math if copied blindly |
| final structure | 59-line façade + the shared 49-declaration engine; the leaf's own mathematics is the headline |
| public surface | **one theorem**; the engine is tier 3 and registered in `spec/UNWIRED-PUBLIC.md` |
| build | 3.0 s (3,623 jobs), 0 warnings |
| register | current (`unwired_register.py --check`) |

## 1. What the theorem says

If `c ≤ 0 < d₁ < d₂` and a finite union of right translates of the centre-cut
Siegel set `centreCutSiegelSet K c u d₁ d₂` covers the centre of `GL₂(𝔸_K)`,
then the production pins of that cover admit **no arithmetic genuine cuspidal
realization**:

```
¬ IsArithGenuineCuspRealizable K (productionPinsOf K W …) Φ.
```

Unfolding `IsArithGenuineCuspRealizable`, this says there is no
`SmoothCuspRealizationAt` `R` whose `toFun` is continuous. The `u = 0` branch is
the engine's countable-avoidance lemma; for `u ≠ 0`, a putative realization `R`
has a point `g₀` with `R.toFun g₀ ≠ 0` (`R.exists_ne_zero`), and the engine's
general contradiction `no_function_of_ne_zero` applies with `ξ = R.centralChar`,
`φ = R.toFun`, the automorphy half `R.smoothCusp.1.1`, and `hR : Continuous
R.toFun`.

## 2. The dedup

The two pin `S_` files differ only in their headers and tails. The shared prefix
— `section Generic` through `not_coversModCentre_of_u_eq_zero`, then the general
`no_function_of_ne_zero` — is **645 lines / 47 declarations**, byte-identical.
`port_advise` on the sibling reported **46 declarations already identical in the
port, all private in `CentreCutVanishing.lean`**, and the remaining shared helper
`toFun_unipT_mul` (which the first leaf did not need).

The cut was therefore a **promotion by extraction**: the shared block moved to
`Cusp/CentreCutEngine.lean` as public declarations with `-- pin:` provenance,
and the first leaf's `no_function_of_ne_zero` became the engine's general lemma.
The sibling's pin-specific `no_realization_of_ne_zero` is **not ported**: its
only use is to feed `R` into the general lemma, and the headline does that
directly. The two façades hold one headline each:

| module | lines | public surface | tier |
|---|---:|---|---|
| `Cusp/CentreCutEngine.lean` | 964 | 49 declarations | 3 (unlisted, registered) |
| `Cusp/CentreCutVanishing.lean` | 64 | 1 headline | 1 (listed) |
| `Cusp/CuspUnrealizable.lean` | 59 | 1 headline | 1 (listed) |

The engine is unlisted because no consumer outside the two façades names it
today; the register makes it discoverable. Wiring is the two `PORT_FILES` rows
and the two `Theorems/` + `S_` pairs in `SOURCES`.

## 3. The refactor, in detail

* The engine keeps the pin's names, under `namespace AutomorphicForm.CentreCutEngine`.
  The two drifted proofs (`coe_mapGL_lowerUnip`, `aC_unipAdelic`) and the four
  narrow `linter.style.haveILetI` suppressions moved with it; the drift notes are
  in [centre-cut-vanishing.md](centre-cut-vanishing.md) §4.
* `no_function_of_ne_zero` is the general lemma: it takes `ξ`, `φ`, the
  automorphy hypothesis, continuity, and a point `g₀` with `φ g₀ ≠ 0`. Both
  headlines instantiate it. The first leaf's headline passes its `ξ, φ, hφ,
  hcont, g, hg`; the sibling obtains `R.centralChar`, `R.toFun`,
  `R.smoothCusp.1.1`, `hR`, `g₀`, `hg₀` from the realization.
* No statement changed: the two headlines are still binder-for-binder the pin
  wrappers, and the engine declarations are statement-identical to the shared
  pin block.

## 4. Verification

* edit loop: 0 errors / 0 warnings for the engine and both façades;
* `lake build` engine 9.7 s (3,622 jobs), sibling façade 3.0 s (3,623 jobs);
* checker: **10,239 identical**, 0 mismatched / 0 missing, `10476` port
  declarations checked; the sibling's delta is +1;
* `#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`;
* `unwired_register.py --check`: current; the engine contributes 49 rows;
* `git status`: the three modules, the checker wiring, the regenerated register,
  and the records.

## 5. What it buys

The sibling leaves the D-S `--include-leaves` demand, and the pair now shares
one engine instead of two copies. The larger `coversModCentre` silo
(`exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre`,
3,038 lines) remains behind the unit-factorizable chain recorded in
`CARRY-FORWARD.md`; no other centre-cut row is ready at this cut.
