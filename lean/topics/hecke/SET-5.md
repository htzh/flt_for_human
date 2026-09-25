# SET 5 — route C′ foundations: the toolkit layer and the Eisenstein series

**Status: done and reviewed (2026-09-24).** Both orders landed and passed
independent verification (full build 4130 jobs 0 warnings; checker 1270/70/0/0;
consumer exit 0); the review record is [SET-6.md](SET-6.md) §0, and SET-6
re-cuts the later sets. This is the run brief for the **first** coding set of the
route-C′ effort. It authorized exactly **two** topics (orders 1–2 below). The full
route is
[TOPIC-route-c-prime-integral-structure.md](TOPIC-route-c-prime-integral-structure.md);
the mathematics is
[../../../math/013-integral-structure-gamma1-basis.md](../../../math/013-integral-structure-gamma1-basis.md);
the scout that fixed the plan is
[../../../studies/route-c-prime-scout.md](../../../studies/route-c-prime-scout.md).
Read all three before touching Lean.

| order | module | declarations | pin `S_` lines | prereq |
|---|---|---|---|---|
| 1 | `ModularForms/WeightOne/Basic.lean` | the seven toolbox headlines (table in §5.1) | ≈1,861 | T9 port |
| 2 | `ModularForms/WeightOne/EisensteinSeries.lean` | `eisensteinG` existence + `qExpansion_eisensteinG_coeff` | ≈753 | order 1 |

**Reserved for the manager (do not start).** The capstone topic —
`ModularForms/WeightOne/IntegralStructure.lean`, the trace lemma
`CuspForm.hasIntegralStructure_of_basis_gamma1` plus the two corollaries — is
**not** authorized here. It is the reviewer's capstone and needs order 1–2 and
the later sets. If an order-1/2 proof seems to need it, stop and report.

**Do not start the later sets** (the tables are in §8). If a declaration you need
belongs to a later module, prove a local `private` helper in your module and
record it; do not open a new module.

## 0. What earlier sets handed over (verified)

- `ModularForms/Defs/IntegralStructure.lean` — `CuspForm.intLattice`,
  `CuspForm.HasIntegralStructure` (T9, verified).
- `ModularForms/Defs/EisensteinChiNegThree.lean` — `chiNegThree`, `sigmaChi`,
  `e1Chi3`, `e1Chi3In`, `E1Chi3IsModular` (a `Prop` interface; T10's parked
  definitions — they are the interface of this route, keep them).
- `ModularForms/Defs/IntegralLattice.lean` — weight-2/lattice vocabulary (unused
  by this set).
- The Sturm cone (`SturmBound.lean`, `QExpansionOrder.lean`) supplies five nodes
  that already lie in the C′ cone; import, do not re-port.

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3` at
  `~/proj/fermats-last-theorem`. Read it; never modify it.
- Statement = `Theorems/Thm_<dotted, `.` → `_`>.lean`; proof =
  `P2M/Sol/S_<same>.lean`. **The wrapper is the statement authority**; take the
  binders from it. The `S_` file is the proof source (and for the toolbox nodes it
  may also be the only public copy of internal helpers — those stay `private`).
- The pin's `S_` files were written against mathlib `v4.33`; the port is
  `v4.34.0`. Expect the drifts recorded in
  [porting-playbook.md](../../porting-playbook.md) §4 and the Sturm log
  ([logs/sturm-bound-port.md](../../logs/sturm-bound-port.md) §"drift"): `if_pos`
  → `ite_eq_left`, deprecated `coe_*` aliases, `haveI` linter walls, `rfl`-vs-`simp`
  shape changes. Adapt proofs, never statements.

## 2. Build discipline — read and obey first

Measured in this checkout with mathlib prebuilt: `lake env lean <module>` on a
200–350-line green module ≈ 4 s; `lake build <module>` deps-cached ≈ 2–5 s; a
full `lake build` after one edit is under a minute; a `whnf`/heartbeat stall at
the default cap errors in ~15–20 s (it does not hang).

- **Bound every build, and never relax the bound.**
  `timeout 60 lake env lean <file>`, `timeout 90 lake build <module>`,
  `timeout 240 lake build`. A non-return at the bound is a blow-up, not patience.
  Do not re-run it with a larger timeout; do not raise `maxHeartbeats` or
  `maxRecDepth` (the lakefile cap is `4000000`); do not "let it finish".
- **On a timeout: quarantine.** Comment the declaration out and bisect, or
  reproduce in the gitignored `Scratch*.lean` with `set_option diagnostics true`
  and a low cap. Then report which declaration, and stop if it is load-bearing for
  the order.
- **When in doubt, measure the CPU time.** Run the build under `/usr/bin/time -v`
  (or `time`): high user CPU + timeout is a real Lean blow-up — bisect it. Near-zero
  user CPU with a wall-clock stall is lock contention with another agent's build —
  re-run when idle, do not bisect and do not raise the bound.
- **Likely stall points here.** The `IsIntegral.mem_span_of_adjoin_simple_constants*`
  pair (adjoin/constant-field transfer) and
  `UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem` (linear
  independence over power series) are the candidates; they are stated over concrete
  function types in the pin — keep them that way. The Eisenstein `S_` file's
  `qExpansion_eisensteinG_coeff` (610 lines) is the other one.
- Build serially; never build concurrently with another agent.

## 3. Shared conventions

1. Statements **verbatim** from the wrappers, binders included.
2. Specific imports; no `import Mathlib` in a port module.
3. Public surface: only the headlines. Pin-private helpers that the port needs
   become `private` in the port's module.
4. Checker: append every order's wrappers to `SOURCES` and both modules to
   `PORT_FILES` in `spec/check_flt_statements.py`. Target **0 mismatched,
   0 missing**.
5. **No commits.** The working tree is the hand-off. Do not touch the pin.
6. Do not touch the FFG modules (`ModularCurve/ModularPolynomial*`,
   `FunctionFieldGeneration/*`) or the capstone.
7. `README.md` gains both rows; the set/log files are the manager's.

## 4. Definition of done (per module)

- Module created at the named path; headlines verbatim; specific imports.
- `timeout 90 lake build <module>` green with 0 warnings, no `sorry`/`admit`.
- `#print axioms` on the module's headlines clean
  (`[propext, Classical.choice, Quot.sound]`).
- `spec/check_flt_statements.py`: sources appended, **0 mismatched, 0 missing**.
- `README.md` row added.
- No statement weakened; if one cannot match its wrapper, quote both and stop.

## 5. The orders

### 5.1 — order 1: `FLTForHuman/ModularForms/WeightOne/Basic.lean`

The toolbox layer. Each declaration's wrapper is
`Theorems/Thm_<name>.lean`; port the statement verbatim and the proof from the
matching `S_` file.

| declaration | `S_` file | role |
|---|---|---|
| `PowerSeries.mem_range_map_of_monic_of_mul_mem_range` | `S_PowerSeries_mem_range_map_of_monic_of_mul_mem_range.lean` (68) | monic-relation membership |
| `IsIntegral.mem_span_of_adjoin_simple_constants` | `S_IsIntegral_mem_span_of_adjoin_simple_constants.lean` (437) | adjoin/const transfer |
| `IsIntegral.mem_span_of_adjoin_simple_constants_transcendental` | `…_transcendental.lean` (599) | its transcendental variant |
| `IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range` | `S_IsAlgClosed_exists_algEquiv_apply_ne_of_notMem_range.lean` (151) | separating an element from a subfield |
| `UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem` | `S_UpperHalfPlane_linearIndependent_complex_of_qExpansion_coeff_mem.lean` (550) | q-coefficients are a faithful linear invariant |
| `ModularForm.finiteDimensional_of_isArithmetic` | `…_of_isArithmetic.lean` (42) | finite-dimensionality, arithmetic level |
| `CuspForm.finiteDimensional_of_isArithmetic` | `…_of_isArithmetic.lean` (14) | its cusp-form corollary |

The last two are **not** the port's existing `finiteDimensional_Gamma0` (which is
the Sturm corollary); these are the pin's generic `IsArithmetic` statements and
are separate declarations. Keep both.

### 5.2 — order 2: `FLTForHuman/ModularForms/WeightOne/EisensteinSeries.lean`

The general Eisenstein series and its $`q`$-expansion (the seed of the explicit
integral family; the weight-one $`\chi_{-3}`$ case is a later set).

| declaration | `S_` file | role |
|---|---|---|
| `EisensteinSeries.exists_modularForm_coe_eq_eisensteinG` | `S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean` (143) | the series is a modular form |
| `EisensteinSeries.qExpansion_eisensteinG_coeff` | `S_EisensteinSeries_qExpansion_eisensteinG_coeff.lean` (610) | its divisor-sum coefficients |

Do **not** port the $`\chi_{-3}`$ theorem `EisensteinWeightOne.e1Chi3IsModular`
(3,816 lines) here; it is SET 6.

## 6. Consumer / wire test

Add `spec/WeightOneConsumer.lean` (a `spec/` file, not a library module) that

1. `#check`s all nine headlines of orders 1–2, and
2. contains **at least one executed, cross-module application** — a concrete
   instantiation that uses a declaration from each module and is proved, not
   merely `#check`ed. The natural candidate is a q-expansion linear-independence
   or a monic-relation membership at an explicit series; if no honest
   instantiation is available for a declaration, say so in the report rather than
   faking one.

`lake env lean spec/WeightOneConsumer.lean` must exit 0 with no warnings.

## 7. What to report back

1. The per-order table: module, lines, declarations, build jobs/time, checker
   before/after (`SOURCES`/`PORT_FILES` additions).
2. Any wrapper statement that did not match, quoted rather than weakened.
3. The v4.34 drifts actually hit, per declaration.
4. Any `private` helper that had to be promoted (with the reason), and any
   declaration that needed a local helper belonging to a later module.
5. The wire test of §6: what the concrete instantiation was, or why none exists.
6. Any build that hit its bound: the declaration, the CPU reading, and the
   outcome (quarantined/bisected), **before** moving on.
7. Confirmation that the capstone, the FFG modules and the pin are untouched.

## 8. The later sets (for the manager's view; not authorized here)

| set | orders | pin `S_` lines |
|---|---|---|
| **5 (this)** | `Basic`, `EisensteinSeries` | ≈2,614 |
| 6 | `EisensteinChiNegThree` (χ₋₃ weight one), `LevelOneHauptmodul` | ≈5,002 |
| 7 | `FrickePackage` | ≈7,500 |
| 8 | `Gamma0Rationality` | ≈5,000 |
| 9 | `Gamma1Basis` | ≈4,900 |
| capstone (**manager**) | `IntegralStructure` (trace lemma + corollaries) | new |

The split is a budget, not a measurement: each set is authorized only after the
previous one is reviewed, and a later set may be re-cut if an order lands heavier
or lighter than scouted.
