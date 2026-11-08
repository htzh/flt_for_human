# Reserve

Verified modules kept out of the critical-path port — superseded routes,
deferred API, and the halves of a ported development that nothing reaches. They
may import `FLTForHuman`; `FLTForHuman` must never import them. Built by default
(`lake build`), so they stay green; a module that declares no `spec-pin:` wire is
built but not statement-checked (`spec/check_port.py` walks `Reserve` and diffs
only wired modules).

## What is here

| module | what it is |
|---|---|
| `Reserve/ModularForms/CuspFormNorm.lean` | the norm of a cusp form — the pre-Sturm route to cusp-form vanishing, kept as an alternative |
| `Reserve/ModularForms/LevelTwoCuspVanishing.lean` | the norm route to $`S_2(\Gamma_0(2)) = 0`$ and the level-one analogue |
| `Reserve/ModularCurve/Analytic/LevelTauBridge.lean` | the bridge from the analytic $`\tau`$-model to the torsion/level data |
| `Reserve/ModularCurve/FunctionFieldGeneration/BaseChange.lean` | the base-change degree dictionary for the level fields: `[κ'⟮jq, jq^d⟯ : κ'⟮jq⟯] = [κ⟮jq, jq^d⟯ : κ⟮jq⟯]` (the any-field supplement's (5.2)) with the `LinearDisjoint`/`relfinrank` machinery it needs. Proved and green, and **not needed**: the slot product's hypothesis is the *source* package, so the port never asks the question, and every statement it cites is available without the dictionary. It is what the optional one-field *formulation* (not any current theorem) would consume: [`topics/functionFieldGeneration/TOPIC-ffg-refactor.md`](../topics/functionFieldGeneration/TOPIC-ffg-refactor.md) §6 |
| `Reserve/AutomorphicForm/Adelic/FactorizableTestFnArchSmoothDead.lean` | the real-place factorizable-test-function chart's **left**-derivative half — the FTF1 headline's unreachable 25 declarations plus the 43 private premises they need, copied out so the port's module holds only the proof |
| `Reserve/AutomorphicForm/Adelic/FactorizableTestFnArchSmoothComplexDead.lean` | its complex mirror (24 declarations + 43 premises) |
| `Reserve/AutomorphicForm/Adelic/BigCellExpansionDead.lean` | the 5,176-line big-cell expansion node's unreachable **12 declarations / 150 lines** plus the 118 private premises they need — the real-place Fourier/Poisson route the pin abandoned for the archimedean `K`-finiteness engine the headline uses instead, and the definitional API of four of the node's own objects (AF7) |
| `Reserve/Analysis/Complex/ChartedCurveIntegral.lean` | the honest line integral of a 1-form on a complex charted space, the charted piece (`Path.map'`), and the exact-form value theorem — mathlib's `curveIntegral` adopted, not rebuilt. **Held, not superseded:** whether the port keeps it depends on the open question of whether an honest integral can replace the pin's choice-based `pathIntegral` ([`topics/aj/PLAN-W3-honest-integral.md`](../topics/aj/PLAN-W3-honest-integral.md) §4b–§4c) |
| `Reserve/AlgebraicCurve/ChartIntegral.lean` | its curve-side seam: `placeCurveIntegral` and `pathIntegral_eq_sub_of_isPrimitiveAlong`, which makes the pin's `pathIntegral` computable — any primitive's endpoint difference, with no path regularity used. Worth keeping whichever way the decision goes |
| `Reserve/Example/FactPrimeNeZero.lean` | **an illustration, not a shelf of dead code**: the `have : Fact (Nat.Prime p) := ⟨hp⟩` / `NeZero (M * p ^ a)` instance chain that `hall_all` depends on, in both directions, with three `fail_if_success` guards that fail if a future mathlib makes the port's `have` lines redundant. Why it exists and how to debug the shape: [`topics/functionFieldGeneration/TOPIC-refactor-friction.md`](../topics/functionFieldGeneration/TOPIC-refactor-friction.md) §1 |
| `Reserve/AlgebraicCurve/Place/ApproximationDead.lean` | one unreachable helper of the weak-approximation node — the order at `w` of a unit of `v`'s valuation subring (`Place.ord_coe_unit_eq_zero_of_le`); its only pin consumer is the `S_` file's own separation lemma, which the port carries publicly in `Place/OrdCalculus.lean` with a different proof |

`Reserve/Example/` is the one non-shelf directory: it holds re-runnable illustrations of
Lean behaviour the port keeps tripping over, kept out of the library because nothing
should import them. Each is written so that a wrong claim fails the build rather than
sitting in a comment (`fail_if_success` guards).

The `…Dead.lean` shelves are the first `--copy` outcome of
`tools/deps/move_dead.py`: written in one run from the live modules, they import
only the port's public API and never the module they came from, and their
declarations stay `private` as in the pin. How a module gets here — and what
belongs in the bin instead — is [porting-playbook.md](../porting-playbook.md)
§3.8.

## Candidates (not yet ported)

- **Route B — the weight-2 Eichler–Shimura map.** The pin's standalone
  `P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean` (4,308 lines, graph
  closure 1) is a self-contained worked instance of the period construction: the
  weight-2 period map and its injectivity, plus a finiteness statement that C′'s
  integral structure already implies in every weight. It is not on the critical
  path — the full Eichler–Shimura isomorphism supersedes it for coverage — so it
  belongs here as a pedagogical unit if it is ported at all. Mathematics:
  [`math/015-weight-two-hecke-periods.md`](../../math/015-weight-two-hecke-periods.md);
  decision:
  [`studies/eichler-shimura-scout.md`](../../studies/eichler-shimura-scout.md) §1.3.

## The CL4 island (shelved 2026-11-06)

The `C`-layer twin of the `ℚ` slot product and the socket-route degree formula it feeds
(`package_of_socket`, the pin's prelude of the char-`p` route: `→
modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos → … → mazurStepThree… →
fermat_last_theorem`). Nothing in the current tree reaches it — the port's frontier stops three
nodes above `_of_socket`, and the `ℚ` `hall_all` route supplies the degree facts — so it sat as a
consumerless prelude that duplicated the whole `ℚ` slot product.

**Not a re-port target.** When the char-`p` route resumes, `git mv` these four files back (imports
and `spec-pin:` wires travel) instead of porting the pin's `S_` files a second time: `Reserve` is a
shelf and `FLTForHuman` must never import it. The live half of
`Degree/FinrankAdjoinJqNModC.lean` (the Tate `c₄`/`c₆`/`j` in terms of `jqModC`, cited by
`TateSlots/ToricPointDictionary.lean`) stayed in `FLTForHuman`.

| module | what it is |
|---|---|
| `ModularCurve/FunctionFieldGeneration/SlotProductAnyField.lean` | the `C`-layer slot product and non-membership (the pin's two `S_` files, ported once); keeps its `spec-pin:` wire |
| `ModularCurve/FunctionFieldGeneration/MffCMulPrime.lean` | `j(q^M)` lies in the level-`M * p` modular function field, over an arbitrary field |
| `ModularCurve/FunctionFieldGeneration/PrimePowerStepAnyField.lean` | the socket's `Pkg` package and the relative-degree steps (`package_of_socket`) |
| `ModularCurve/Degree/FinrankAdjoinJqNModCDead.lean` | the dead half of `Degree/FinrankAdjoinJqNModC`: the `Transport`/coefficient-map block and the two degree headlines; unwired, so built but not statement-checked |
