# The Hahn-series algebraic-closure supplement — `HahnSeries.isAlgClosed_rat`

**Status: landed 2026-10-17.** One module,
`FLTForHuman/RingTheory/HahnSeries/IsAlgClosed.lean` (1,087 lines, 67 public
declarations + 11 `private`), green with 0 errors and 0 warnings; no `sorry`, no
axiom beyond `[propext, Classical.choice, Quot.sound]`. The module is **tier 3**
(unlisted) and its public surface is registered in `spec/UNWIRED-PUBLIC.md`.

| | |
|---|---|
| statement | `HahnSeries.isAlgClosed_rat {K} [Field K] [IsAlgClosed K] : IsAlgClosed (HahnSeries ℚ K)` |
| pin source | `P2M/Sol/S_HahnSeries_isAlgClosed_rat.lean` (975 lines, namespace `DorgePuiseux`), taken whole except its `solution` |
| statement authority | `Theorems/Thm_HahnSeries_isAlgClosed_rat.lean` |
| public surface | 67 declarations (the pin's 66 development publics + the headline), all with `-- pin:` provenance; 11 pin-private helpers stay `private` |
| FLT premises | **0** — the whole development imports mathlib only |
| consumers | 19 project-wide, **5 in the D-S cone** (2,300 raw `S_` lines) |
| checker | unchanged at **9857 identical**, 0 mismatched / 0 missing (tier 3, unlisted) |
| register | `spec/UNWIRED-PUBLIC.md` gains the module: 67 public declarations, 67 pin originals |
| build | edit loop 8 s; `lake build` 4.5 s (module), 2,000 jobs |

## 1. What it is, and why it is homed as a supplement

This is the generalized Newton–Puiseux / Mac Lane–Kaplansky theorem: the Hahn
field `HahnSeries ℚ K` (Mal'cev–Neumann series with well-ordered support over the
divisible value group `ℚ`) is algebraically closed when `K` is. It is used in the
pin as the "big algebraically closed characteristic-zero valued field" in which
generic-point and specialisation arguments take place.

The statement names only mathlib objects (`HahnSeries`, `ℚ`, `IsAlgClosed`) and
the development imports only mathlib, so this is not FLT mathematics. Mathlib
`v4.34.0` has the Hahn-series `Field` instance
(`Mathlib/RingTheory/HahnSeries/Summable.lean`) but **no algebraic-closedness
result and no Puiseux development at all**. Hence the home mirrors mathlib —
`FLTForHuman/RingTheory/HahnSeries/IsAlgClosed.lean`, beside the existing
`RingTheory/{DedekindDomain,DiscreteValuationRing,…}` — rather than being filed
under the pin's `ModularCurve` consumers. The port is a mathlib supplement.

## 2. The proof, and the port

The pin's four blocks, transcribed in order:

1. **Newton step** — `newtonInitialForm`, `exists_newtonSlope`,
   `exists_newtonFirstApprox`: the Newton polygon's initial form produces a first
   approximation whose value is strictly larger.
2. **Ball chains** — `IsBallChain`, `pseudoLimit`: nested balls have pseudo-limits
   because the support is well-ordered (`IsBallChain.isPWO_support_pseudoLimitCoeff`).
3. **Kaplansky iteration** — `KaplanskySlope`, `KaplanskyLE`, the Taylor-expansion
   value estimates, and `exists_kaplanskyLE_upperBound`: the approximation order is
   chain-complete (a `Subtype` order from the valuation, a limit by coefficients).
4. **Maximality** — `exists_isRoot_hahnSeries` by Zorn, then
   `IsAlgClosed.of_exists_root`.

The transcription is the pin's text with the `p2m_reactivate` bookkeeping dropped.
No pin-public declaration is demoted: the 66 public development declarations stay
public at the pin's names (each with a `-- pin: <name> (<file>:<line>)` comment), the
67th public declaration is the headline re-proof, and only the pin's own 11 `private`
helpers stay `private`. The pin's `scoped instance` `Std.Refl (KaplanskyLE f)` is
kept as a plain public `instance` (the global effect the pin's `p2m_reactivate`
gives it). Because no port consumer names these, the module is left **unlisted**:
nothing is wired into `PORT_FILES`, and the tier-3 register recovers the surface from
the provenance comments — the policy in the playbook (§4: public stays public; a
public declaration with no known consumer may stay unwired). Imports are targeted,
not `Mathlib`:

```lean
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Order.Zorn
```

The only `v4.34.0` adaptation is a family of deprecation renames in the pin's proof
terms, eleven sites, no mathematical change: `if_neg` → `ite_eq_right`, `if_pos` →
`ite_eq_left`, `dif_pos` → `dite_eq_left`, `dif_neg` → `dite_eq_right`. Nothing else
fired: the `HahnSeries`, `Polynomial.taylor`, `AddValuation`, `WithTop` and Zorn API
all behave as in the pin's `v4.33.1`/mathlib `db584cd6`.

## 3. What it buys in the D-S cone

`frontier.py --ds --include-leaves --rank-by silo` prices it at `HahnSeries. 1 / 975`
— a leaf (`cites 0`, `needed 1`), `used_by (cone) 5`, `used_by (project) 19`. The five
cone consumers are

| consumer | `S_` lines |
|---|---:|
| `ModularCurve.toricPoint_add_toricPoint_of_charZero` | 919 |
| `ModularCurve.toricPoint_add_nonToricPoint_of_charZero` | 704 |
| `ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed` | 510 |
| `ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq` | 87 |
| `WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental` | 80 |

all using it as the instance `haveI : IsAlgClosed (HahnSeries ℚ …) := HahnSeries.isAlgClosed_rat`.
The port already carries that `[IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ))]`
hypothesis verbatim in `WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` (the pin's
wrapper has it too), so this theorem is exactly the input that will discharge it when
the specialisation layer is ported.

`port_advise -t HahnSeries.isAlgClosed_rat`: 0 substitutions, 0 near-duplicates, 0
declarations already in the port — nothing to reuse, pure transcription.

## 4. Reproduce

```sh
cd lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/RingTheory/HahnSeries/IsAlgClosed.lean
flock .lake/flt_build.lock timeout 300 lake build \
    FLTForHuman.RingTheory.HahnSeries.IsAlgClosed
python3 spec/check_flt_statements.py          # 9857 identical (tier 3: no delta)
python3 tools/deps/unwired_register.py        # register gains the 67 declarations
```

One register-rendering artifact to know about (tool, not this module): for a pin
declaration whose *name* is dotted (`theorem KaplanskySlope.addVal_eval_le`), the
register's "importable name" column reconstructs `<frame>.<last>`, so it prints
`DorgePuiseux.addVal_eval_le` rather than the importable
`DorgePuiseux.KaplanskySlope.addVal_eval_le`. The "pin original" and "pin file"
columns are correct; the two same-last-name rows (`KaplanskySlope.addVal_eval_le`,
`KaplanskyLE.addVal_eval_le`) are distinguishable there.

Upstreaming note: mathlib would want the general divisible-`Γ` statement; the pin
proves the `ℚ` case, which is what the D-S cone needs. This module is therefore the
right thing to port *here* and a natural seed for a later mathlib PR, but it is not a
drop-in upstream file.
