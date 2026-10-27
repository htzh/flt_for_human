# WORKORDER BC9b — the public surface of the two new modules

Scope: bring the two modules BC9 created to the port's standard for a pin-public declaration:
either **public at the pin's name and diffed**, or **dropped in favour of the port's existing
public copy**. No new module, no other file, no statement change.

## Why

`WORKORDER-BC9` scoped one headline per module and left the engines private. That was right for the
proof bodies but wrong for the *surface*: the pin states these declarations **public**, and §5 of
the playbook forbids hiding real mathematics (a private engine is one the next theory re-derives).
The port's own standard is: every pin-public declaration the module transcribes is public, at the
pin's name, and diffed by the checker.

## Module 1 — `Place/ComplexDictionary.lean`

The pin `S_` file has **19** public declarations plus the headline. Ten of them are
statement-identical to declarations the port already has publicly, and must be **used, not
re-declared** (check each before touching it):

| pin name | the port's public copy |
|---|---|
| `mem_of_ord_nonneg` | `Place.mem_of_ord_nonneg` |
| `ord_nonneg_of_mem` | `Place.ord_nonneg_of_mem` |
| `ord_pos_of_mem_maximalIdeal` | `Place.ord_pos_of_mem_maximalIdeal` |
| `isRational_of_isAlgClosed` | `Place.isRational_of_isCurveOver` |
| `evalAt_algebraMap` | `Place.evalAt_algebraMap` |
| `evalAt_sub_algebraMap` | `Place.evalAt_sub_algebraMap` |
| `ord_pos_of_evalAt_eq_zero` | `Place.ord_pos_of_evalAt_eq_zero` |
| `reading` | `Place.chartRead` (verify: `port_advise` reports it statement-identical) |
| `OrderHypothesis` | `PeriodPair.DiscriminantNeZero` (verify the same way) |
| `functionFieldRiemannRoch` | `functionFieldRiemannRoch_of_isAlgClosed` |

The remaining **nine are pin-public and new**; promote each to public at the pin's name, in the
pin's namespace, and make it diff: `finite_setOf_ord_ne_zero`, `exists_nonconst_mem_of_ne`,
`reading_center`, `eventually_mem_chart`, `tendsto_reading`, `continuousAt_reading`,
`analyticAt_reading`, `continuousAt_evalAt`, `false_of_isClopen`. Each needs its statement in the
pin's spelling (the wrapper/`S_` text) to match the checker — that is a *text* change only; the
proof you already have is reused. Append the `S_` file (already on the wire) is enough for these;
if a promoted name also has a `Theorems/` wrapper, append that too.

If a promoted statement turns out to be statement-identical to a port-public declaration under
another name, do **not** declare it — report the pair and use the port's.

## Module 2 — `Genus/SplittingFieldGenus.lean`

The pin file's twelve `*_pkg` declarations are instantiation shims with generated names; §3.1 says
a generated token is rectified, not carried, and `Genus/HurwitzBound.lean` already sets the
precedent of deriving the instances inline — **leave them out**. The two non-`_pkg` helpers are a
different matter: `transcendental_algebraMap` and `finiteDimensional_adjoin_algebraMap` are
pin-public, human-named lemmas. Check whether the port already has them publicly (for instance
`AlgebraicCurve.ConstantFieldExtension.transcendental_algebraMap` in
`Place/ConstantFieldExtension.lean`) — if yes, drop the private copy and call it; if no, promote at
the pin's name and let the checker diff it.

## Rules

- Statements are changed only in *spelling*, never in content; proofs are reused.
- Insertions/promotions only; no existing declaration restructured; no other module edited.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>`; finished module `flock .lake/flt_build.lock timeout 110 lake build <module>`.
  Commands under 2 minutes, own `timeout`, no loops; logs `lean/tmp/bc9b-*.log`.
- `check_port.py --force` → 0 mismatch / 0 missing per module, with the promoted declarations `ok`;
  0 warnings; axioms clean; no `sorry`; no markers row; no commit.
- If a promoted statement cannot be made to diff after two attempts at its spelling, stop and
  report that one declaration with the two texts — do not hide it again.

## Report (one message)

per module: build + warnings, the checker summary line with the new `ok` count; the axioms lines;
which declarations were promoted, which were dropped in favour of a port-public copy (name pair),
and which stayed private and why.
