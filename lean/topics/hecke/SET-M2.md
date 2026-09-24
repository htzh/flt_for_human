# SET-M2 — the Fricke/inclusion core, the Φ datum family, and the cusp dichotomy (m4–m6)

**Status (2026-09-23): finalized against the landed SET-M1 modules; ready to
run.** SET-M1 passed review (checker 1,022 identical/0 mismatched/0 missing,
`lake build` 4,093 jobs green, consumer Zones A/B/G at 0 errors); the review is
`../logs/mc-port.md` §Review. This is the run brief for the **second** coding set
of the `ModularCurve` Hecke-layer effort ([PORTING-MC.md](../PORTING-MC.md)). It
authorizes exactly three topics, in this dependency order:

| order | work order | object | pin | ≈ port | prereq |
|---|---|---|---|---|---|
| 1 | [TOPIC-m4-fricke-inclusion.md](TOPIC-m4-fricke-inclusion.md) | the shared `Γ₀`-invariant core and the three Fricke/inclusion headlines (M8) | 8 nodes, 3,030 raw / 2,307 content | 1,000–1,400 | m3, ported `Hauptmodul.RealL` |
| 2 | [TOPIC-m6-phi-data.md](TOPIC-m6-phi-data.md) | the Φ datum family and its degree tail (M5) | 14 nodes, 1,465 raw / 950 content | 550–800 | m1, ported Φ_p effort |
| 3 | [TOPIC-m5-cusp-fricke-aut.md](TOPIC-m5-cusp-fricke-aut.md) | the `RatFunc` cusp model, the cusp dichotomy, the Fricke automorphisms, the cusp bookkeeping, and the prime degree (M9 + one M5 node) | 18 nodes, 1,347 raw / 850 content (160 shared) | 500–700 | m2, m4, m6 |

The order is a real dependency chain: m5's `eq_cuspInftyBar_or_eq_cuspZeroBar`
and `modularFunctionFieldBar_eq_restrictScalars` consume m6's
`nonempty_modularPolynomialData_of_squarefree`, `finrank_adjoin_jqNModC_le` and
`transcendental_jqModC`; m4 is independent of m6 and goes first because it is the
biggest dedup and supplies the `modularUnitSeries` inclusions m5's
`modularFunctionFieldBar_eq_restrictScalars` cites.

**The set's headline is the m4 dedup.** The three M8 `S_` files share a
**651-content-line prelude**; the first two differ by 12 lines total (all `p2m_*`
plus the final `solution`). The port writes it **once**. The measurement is
PORTING-MC §4.2b and `../logs/mc-port.md` §1.3.

**This file is written ahead of the SET-M1 review; the interface names are
finalized against the modules that actually landed before the set is
dispatched.** If SET-M1 changed a name this set imports, the manager edits the
order rather than letting the agent guess.

## 0. What SET-M1 hands over (to be confirmed at review)

- `Defs/{HeckeOperator,DegeneracyTower,HeckeTotal,HeckeModule,ArithmeticGalois}.lean`
  — the Hecke vocabulary, `JZero`, `modularFunctionFieldBar`.
- `Defs/{GeometricBaseChange,QAdicPlace,CuspidalClass,AtkinLehner,ModularUnit,JqCoeff}.lean`
  — the base-change model, `cuspInftyBar`/`cuspZeroBar`/`frickeInvolutionFull`,
  `modularUnitSeries`, `jqModC`/`jqNModC`.
- `Analytic/{QParamUnique,ModularUnitQExpansion,Gamma0Cosets}.lean` — the four
  `hasSum_*modularUnitSeries*` heads and the `Γ₀` coset lemmas m5 cites.
- Baseline: `lake build` green, checker **802 identical, 0 mismatched, 0 missing**.

## 1. The source of truth, and how to read it

As [SET-M1](SET-M1.md) §1: statements from the `Theorems/` wrappers (theorems) or
`Definitions/` files (definitions), binders included; the `S_` files' `p2m_*` /
`attribute` scaffolding is dropped; the pin is read-only.

## 2. Build discipline

As [SET-M1](SET-M1.md) §2. Bound every build with `timeout`; never add or raise
`maxHeartbeats`; quarantine a non-return in `Scratch*.lean`.

## 3. Shared conventions

As [SET-M1](SET-M1.md) §3, with one addition: **m4's core module is the single
home for the 651-line prelude.** Its declarations are `private` except the ones
the pin's own `S_` files name across the three targets (`mem_modularFunctionField_of_data`,
`isIntegral_of_data`, `iota`, `dHat`, …); the checker verifies them by their pin
dotted names under the `QExpN` namespace. Record the `diff | grep -c` before/after.

**Do not edit** the paused Hecke face's modules, the FFG/Φ modules, or the
existing `Defs/{Laurent,Jq,Fields,PhiGen,TS,Twist,PhiAtSlot,Cyclotomic}.lean`.
`ModularForms/Hauptmodul.lean`'s `RealL` is imported, not modified; if a missing
`RealL` lemma blocks m4, prove it in m4's own module and record it (do not edit
`Hauptmodul.lean`).

## 4. Definition of done (per topic and for the set)

As [SET-M1](SET-M1.md) §4. One consumer zone per set in
`spec/ModularCurveHeckeConsumer.lean` (Zone C `[analytic]` for m4, Zone D
`[degree]` for m6, Zone E `[cusp]` for m5).

## 5. What to report back

1. The per-topic table: modules, port lines, public decls, build, checker
   before/after.
2. **m4's dedup, measured**: the prelude's single copy, the three `diff` counts,
   and which pieces were imported from `Hauptmodul.RealL`.
3. **m6's one-liners, measured**: for each of the seven claimed one-liners over
   the ported Φ_p effort, the port declaration it reduces to and the proof term
   length; and where `nonempty_modularPolynomialData_of_squarefree` actually bit.
4. **m5's `eq_cuspInftyBar_or_eq_cuspZeroBar`**: the `RatFunc` route, the
   `Module.finite`/`finrank_le`/`IsSeparable` obligations, and the place count.
5. Any statement that would not match its wrapper (quoted, not weakened).
6. The SET-M3 hand-off: which m4/m5/m6 declarations m7–m9 import.
