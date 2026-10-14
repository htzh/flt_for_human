# The Iwasawa analytic core — the two-wave port

Record of the port of the complex and real archimedean Iwasawa analytic cores
([topics/automorphicForm/TOPIC-iwasawa-analytic-core.md](../topics/automorphicForm/TOPIC-iwasawa-analytic-core.md))
from the FLT pin `anthropics/fermats-last-theorem@aa2d8b3` into `FLTForHuman/`, mathlib `v4.34.0`.
The method is [porting-playbook.md](../porting-playbook.md); the work orders are
`topics/automorphicForm/WORKORDER-I{1,2,3}*.md`; friction is in [frictions.md](frictions.md)
(FR-0022 is this effort's).

**Status: IN PROGRESS — definition gate landed; the two engine waves dispatched.**

## 0. What ships

| phase | subject | nodes / modules | checker (identical) |
|---|---|---|---|
| **D** | the definition gate: `Def_AutomorphicForm_ComplexIwasawa` whole | 1 new (`AutomorphicForm/Iwasawa/Complex/Basic.lean`) | 9654 → 9658 |
| **D** | the shared generic Fourier-decay block (`M4aP3B.FourierDecay`) | 1 new (`MeasureTheory/FourierDecay.lean`) | 9658 → 9660 |
| **I1** | wave 1 base: the six complex layer-0 kernels | 2 new tier-3 engines (`Complex/{Core,Decay}.lean`) | — (tier 3) |
| **I2** | wave 1 successors: the three complex successors | 2 new tier-3 engines (`Complex/{UniformDecay,Continuation}.lean`) | — (tier 3) |
| **I3** | wave 2: the four real kernels | 3 new tier-3 engines (`Real/{Core,Decay,Continuation}.lean`) | — (tier 3) |
| **F** | the two subject façades (manager) | 2 new tier-1 modules (`Complex/Estimates.lean`, `Real/Estimates.lean`) | 9660 → 9673 (+13) |

Measured cone: 13 nodes in the Deligne–Serre cone (9 complex, 4 real), 9 of them graph leaves;
`port_plan` **10,378 raw / 4,879 duplicate / 5,256 net new** (complex 3,368, real 1,949), 0 already
in the port. The nine leaves' 8,956 silo lines overstate the cost ~2.2×: three complex files carry
one 1,155-line + 102-line development and three real files one 619 + 512-line development.

## 1. Phase D — the definition gate (landed)

`Def_AutomorphicForm_ComplexIwasawa` (25 lines / 4 declarations: `botP`, `botQ`, `radC`, `kC`) is
homed whole at `FLTForHuman/AutomorphicForm/Iwasawa/Complex/Basic.lean`, tier 1; its two deprecated
pin import paths were moved to their v4.34 spellings (FR-0022). The pin's `M4aP3C.CplxIwasawa`
copies of the same four are byte-identical and are dropped in the engines (playbook §2.4). The one
cross-wave shared block, `M4aP3B.FourierDecay.{pow_mul_norm_fourierIntegral_le_of_coercive,gate_degenerate}`,
is homed once at `FLTForHuman/MeasureTheory/FourierDecay.lean`, tier 1 — generic measure/Fourier
mathematics, not Iwasawa theory (playbook §5).

No promotion is owed. Two non-promotions are recorded in the topic §4d: the real `rot` is not the
port's `RepTheory.AntiInvolutionHaar.rot`, and `weylR` is not the port-`private`
`CuspForm.FrickeHecke.frickeGL`.

| check | result |
|---|---|
| tier-0 on both modules | exit 0, 0 warnings |
| tier-1 builds | `Complex.Basic` 1,598 jobs / 1.6 s; `MeasureTheory.FourierDecay` 3,054 jobs / 3.9 s |
| checker | **9660** identical, 0 mismatched, 0 missing, 38 own (9698) — delta **+6**, exactly the two modules |
| one-token mutation (a hypothesis token on `pow_mul_norm_fourierIntegral_le_of_coercive`) | exactly 1 mismatched, reverted |
| `#print axioms` on both headings | `[propext, Classical.choice, Quot.sound]` |
| consumer `spec/IwasawaConsumer.lean` | exit 0 (zones D and F) |
| `unwired_register.py --check` | current |
| wiring | `Definitions/Def_AutomorphicForm_ComplexIwasawa.lean` + the complex `norm` `S_` file appended last to `SOURCES`; the two modules appended last to `PORT_FILES` |

The definition module's mutation test had to target a *theorem*: the checker ignores a computational
`def`'s body (comparing only its type), so mutating `radC`'s body reports nothing — the documented
degeneracy, not a checker bug.

## 2. Waves 1–2 — the engines

The three orders are `topics/automorphicForm/WORKORDER-I{1,2,3}*.md`; I1 and I3 were dispatched in
parallel (disjoint namespaces, shared `flock` builds), I2 waits on I1's review.

**All three waves and both façades have landed and are reviewed; the effort is complete.**

| | module | lines | public/private | tier-1 | checker |
|---|---|---|---:|---|---|
| I3 | `Real/Core.lean` | 819 | 113 / 0 | 3,055 jobs, 5.1 s | — (tier 3) |
| I3 | `Real/Decay.lean` | 872 | 53 / 0 | 3,062 jobs, 14 s | — |
| I3 | `Real/Continuation.lean` | 414 | 1 / 40 | 3,079 jobs, 4.0 s | — |
| I1 | `Complex/Core.lean` | 2,189 | 93 / 6 | 3,056 jobs, 12 s | — |
| I1 | `Complex/Decay.lean` | 554 | 11 / 5 | 3,106 jobs, 7.4 s | — |
| I2 | `Complex/UniformDecay.lean` | 524 | 16 / 0 | 3,107 jobs, 15.0 s | — |
| I2 | `Complex/Continuation.lean` | 446 | 1 / 40 | 3,108 jobs, 9.1 s | — |
| mgr | `Real/Estimates.lean` | 82 | 4 headlines | 3,080 jobs, 3.1 s | 9660 → **9664** (+4) |
| mgr | `Complex/Estimates.lean` | 119 | 9 headlines | 3,116 jobs, 3.4 s | 9664 → **9673** (+6 base, +3 successors) |

All three workers reported no heartbeat blow-up (the named 139/119/117-line chains, the inline
uniform-in-`g` case split and the `rpow`/`exp` differentiations all clear the 200,000 cap), 0
warnings at tier 0, no promotions, no existing module edited, and every kernel proved by the pin's
own `solution` body. The manager re-verified all thirteen kernels' statements with the checker's
parser (0 diff, apart from one textual `g`-binder deviation on
`ComplexIwasawa.Engine.norm_fourierIntegral_cpow_radC_mul_le_polyDecay`, recorded in WORKORDER-I1
§8), ran `#print axioms` on all thirteen (`[propext, Classical.choice, Quot.sound]`), the
forbidden-token sweep (clean), and a one-token mutation per wired façade (exactly 1 mismatched,
reverted each time). The register is regenerated and current: 91 unlisted modules / 2,341 public /
2,053 with a pin original. The consumer `spec/IwasawaConsumer.lean` has zones D (definition layer),
F (the shared Fourier bound) and E (the headline estimates at the identity matrix), exit 0.

**Naming.** The façades are `Complex/Estimates.lean` and `Real/Estimates.lean`, not
`Headlines.lean`: a module is a mathematical role, not an artifact kind, so the `Complex/` and
`Real/` theory directories stay open to further subjects (the draft-name deviation is recorded in
WORKORDER-I2 §8).

The mathematics of the decomposition and the estimates is
[../../math/028-iwasawa-decomposition-and-archimedean-estimates.md](../../math/028-iwasawa-decomposition-and-archimedean-estimates.md),
written during the wait and linked from the topic.

## 3. Plan vs actual

| | planned (topic) | actual |
|---|---|---|
| net new math | 5,256 lines (complex 3,368 + real 1,949) | 5,256 — the plan's number was the dedup budget and the workers wrote it out over 5,818 engine lines (3,713 complex + 2,105 real), plus 201 lines of façade and 143 of definition layer (total 6,162 new Lean lines) |
| def layer | `Def_AutomorphicForm_ComplexIwasawa` whole + the shared Fourier block | exactly: 2 modules, checker +6 |
| waves | 2 (complex 9 nodes, real 4) | 2 waves / 3 orders (complex split for the ~1,500-line dispatch size) |
| tiers | engines tier 3, façades tier 1 | as planned |
| checker | — | 9654 → **9673** identical, 0 mismatched, 0 missing, 38 own (9711 checked) |
| promotions | none expected | none needed; the two recorded non-promotions (`rot`, `weylR`) confirmed |
| build blow-ups | the named long chains were the risk | none; every declaration cleared 200,000 heartbeats |

Two deviations, both recorded: the façade name (`Headlines` → `Estimates`, this file's Naming note
and WORKORDER-I2 §8), and the one textual `g`-binder spelling on one tier-3 kernel (WORKORDER-I1
§8) — harmless because the façade carries the wrapper spelling.

## 4. Close-out: the frontier re-read

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --rank-scope all --top 0
```

| quantity | before | after |
|---|---:|---:|
| cone `needed` nodes | 1,617 | **1,604** (−13) |
| cone `needed` raw `S_` lines | 652,276 | **641,898** (−10,378) |
| Iwasawa rows still needed | 13 | **0** |
| ported frontier `F` nodes | 925 | **938** (+13) |

The 13 nodes left the demand and entered the frontier exactly as the topic predicted; the remaining
consumers (`AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary`,
`AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn`) and the Deligne–Serre
§7 gates are where the column now stands. The residual is the three out-of-cone complex rows
(`exists_forall_norm_weightFourierIntegral_continuation_…`, `exists_entire_…` ×2) and the two real
ones, which the engine namespaces are shaped to receive.
