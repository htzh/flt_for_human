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
| `Reserve/AutomorphicForm/Adelic/FactorizableTestFnArchSmoothDead.lean` | the real-place factorizable-test-function chart's **left**-derivative half — the FTF1 headline's unreachable 25 declarations plus the 43 private premises they need, copied out so the port's module holds only the proof |
| `Reserve/AutomorphicForm/Adelic/FactorizableTestFnArchSmoothComplexDead.lean` | its complex mirror (24 declarations + 43 premises) |
| `Reserve/Analysis/Complex/ChartedCurveIntegral.lean` | the honest line integral of a 1-form on a complex charted space, the charted piece (`Path.map'`), and the exact-form value theorem — mathlib's `curveIntegral` adopted, not rebuilt. **Held, not superseded:** whether the port keeps it depends on the open question of whether an honest integral can replace the pin's choice-based `pathIntegral` ([`topics/aj/PLAN-W3-honest-integral.md`](../topics/aj/PLAN-W3-honest-integral.md) §4b–§4c) |
| `Reserve/AlgebraicCurve/ChartIntegral.lean` | its curve-side seam: `placeCurveIntegral` and `pathIntegral_eq_sub_of_isPrimitiveAlong`, which makes the pin's `pathIntegral` computable — any primitive's endpoint difference, with no path regularity used. Worth keeping whichever way the decision goes |
| `Reserve/AlgebraicCurve/Place/ApproximationDead.lean` | one unreachable helper of the weak-approximation node — the order at `w` of a unit of `v`'s valuation subring (`Place.ord_coe_unit_eq_zero_of_le`); its only pin consumer is the `S_` file's own separation lemma, which the port carries publicly in `Place/OrdCalculus.lean` with a different proof |

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
