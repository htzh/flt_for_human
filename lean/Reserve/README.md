# Reserve

Verified modules kept out of the critical-path port — superseded routes and
deferred API. They may import `FLTForHuman`; `FLTForHuman` must never import
them. Built by default (`lake build`), so they stay green and checked.

## What is here

| module | what it is |
|---|---|
| `Reserve/ModularForms/CuspFormNorm.lean` | the norm of a cusp form — the pre-Sturm route to cusp-form vanishing, kept as an alternative |
| `Reserve/ModularForms/LevelTwoCuspVanishing.lean` | the norm route to $`S_2(\Gamma_0(2)) = 0`$ and the level-one analogue |
| `Reserve/ModularCurve/Analytic/LevelTauBridge.lean` | the bridge from the analytic $`\tau`$-model to the torsion/level data |

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
