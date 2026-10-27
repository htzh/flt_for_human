# WORKORDER BC5b — the two homing-blocked leaves, in modules the manager re-homed

Scope: fill **two `sorry`s** in two new modules the manager created for the nodes BC5 could not
place. Both modules already elaborate, their statements are checker-verified (**1 ok / 0 / 0**
each), and their imports are in place. Nothing else is in scope; do not edit any other file.

## The two modules

| module | declaration | pin proof | why it lives here |
|---|---|---|---|
| `FLTForHuman/AlgebraicCurve/Place/IntegralClosureAtFiber.lean` | `Place.exists_integralClosureAt_of_ord_fiber_nonneg` | `P2M/Sol/S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg.lean` (66) | its proof counts normalised factors (`Place.count_normalizedFactors_span_singleton`) and needs the fibre dictionary, neither available in `Defs/PlacesOverDVR.lean`, which is below them |
| `FLTForHuman/AlgebraicCurve/PrincipalDivisors/PoleDivisor.lean` | `exists_poleDivisor_of_transcendental` | `P2M/Sol/S_AlgebraicCurve_exists_poleDivisor_of_transcendental.lean` (26) | the pin's first line is `isCurveOver_of_isAlgClosed_of_transcendental`, which lives above `Defs/PoleDivisorPackage.lean` |

## What changed on the manager's side for you

- `Place.count_normalizedFactors_span_singleton` is now **public** in
  `PrincipalDivisors/Transcendence.lean` (it is a pin node with its own wrapper; it had been
  transcribed privately). Use it directly — the module you need it from is the one the new
  `Place/IntegralClosureAtFiber.lean` already imports.
- `Divisor.pushforward_div` is already landed (in `PrincipalDivisors/Transcendence.lean`, beside
  `pushforwardNormFormula`), so it is *not* part of this round.
- `RegularProlongation.coeff_mem_of_aeval_mem_integers` is now public at the pin's name.

## Rules

- Statements are frozen (they already diff); fill the proofs, transcribe the pin's.
- No tree build; edit loop `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`
  from `lean/`; finished module `flock .lake/flt_build.lock timeout 110 lake build <module>`. Every
  command under 2 minutes, its own `timeout`, no loops.
- `python3 spec/check_port.py --force <module>` → must stay `1 ok, 0 mismatch, 0 missing` with no
  `sorry` warning left; `#print axioms` on both → `[propext, Classical.choice, Quot.sound]`;
  0 warnings; no `sorry`/`admit`/`axiom`; no `spec/decl_markers.tsv` row; no commit.
- If a proof needs something that is `private` or below these modules, stop and report the goal
  rather than editing a hub module.

## Report (one message)

per module: build + warnings, the checker summary line; then the two axioms lines, any deviation
from the pin beyond a tactic rename, and any blocker.
