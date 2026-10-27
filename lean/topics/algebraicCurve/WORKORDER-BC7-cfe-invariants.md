# WORKORDER BC7 — the constant-field-extension invariants

Scope: **five insertions into three existing, already-wired modules**. No new module, nothing else
edited.

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | home |
|---|---|---:|---|
| `AlgebraicCurve.Pic0.natCard_torsion_eq_of_constantFieldExtension` | `S_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension` | 541 | `Genus/ConstantFieldExtension.lean` |
| `AlgebraicCurve.exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed` | `S_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed` | 99 | `Genus/ConstantFieldExtension.lean` |
| `AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension` | `S_AlgebraicCurve_finrankAlong_eq_and_trace_eq_of_constantFieldExtension` | 407 | `IsCurveOver/ConstantFieldExtensionSpan.lean` |
| `AlgebraicCurve.finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin` | `S_AlgebraicCurve_finrank_le_and_natCard_places_le_of_constantFieldExtension_adjoin` | 348 | `IsCurveOver/ConstantFieldExtensionSpan.lean` |
| `AlgebraicCurve.exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed` | `S_AlgebraicCurve_exists_finiteDimensional_isSeparable_adjoin_of_constantFieldExtension_of_isAlgClosed` | 93 | `IsCurveOver/Transcendental.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`. **Statements from the `Theorems/` wrappers**,
proofs from the `S_` files.

**The mathematics.** What a constant field extension `Kⁿ ⊆ K'` preserves: the order of the torsion
of `Pic⁰` (`natCard_torsion_eq_of_constantFieldExtension` — the `p^{2g}` statement), the vanishing
of the index of specialty of a lifted divisor, `finrankAlong` and the trace, the finrank and the
number of places of an `adjoin`, and the finite-dimensional separable `adjoin` that makes a
constant-field extension of a separably generated function field again a curve.

## Why these homes (do not re-home them)

All three targets are **above every module the five proofs consume** (checked against the port's
import closure): `Genus/ConstantFieldExtension.lean` is itself the torsion-descent module (it
already carries `exists_torsion_descent_of_constantFieldExtension`) and lies above `Place/ConstantFieldExtension`,
`IsCurveOver/ConstantFieldExtension` and `Place/FromValuationSubring`;
`IsCurveOver/ConstantFieldExtensionSpan.lean` is above the same set; `IsCurveOver/Transcendental.lean`
is above `IsCurveOver/PerfectField`. Each target is wired (**4 / 3 / 3** `spec-pin:` lines) and green;
keep it so.

## Rules

- **Insertions only**: append the wrapper **and** the `S_` file to each module's `spec-pin:` block,
  add the declaration at the wrapper's statement (binder spelling character for character), leave
  every existing declaration untouched.
- The two `Genus/ConstantFieldExtension.lean` nodes share a source: the pin repeats the
  `isPrincipal`/torsion machinery across `S_` files, so check for a `port_advise`-visible
  shared block before writing it twice; if a helper is `private` in the port, stop and report.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>`; finished module `flock .lake/flt_build.lock timeout 110 lake build <module>`.
  Commands under 2 minutes, own `timeout`, no loops; logs under `lean/tmp/bc7-*.log`.
- `check_port.py --force` → 0 mismatch / 0 missing per module with the new declarations `ok`;
  axioms clean; 0 warnings; no `sorry`; no markers; no commit.
- The `natCard_torsion` node is the biggest single module of the set (541 lines, 33 declarations):
  it is expected to be most of this order's wall time.

## Report (one message)

per module: build + warnings, the checker summary line; then the five axioms lines, the
deviations beyond a tactic rename, and any blocker.
