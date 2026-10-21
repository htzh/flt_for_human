# WORKORDER-PH3C — the `Algebra` norm/integrality family of the D-S cone

**Status (closed 2026-10-20): landed and reviewed green.** One set, **two modules, 498 lines, 13
statement-checked declarations**, zero host edits, zero promotions, zero substitutions, zero
markers. The checker's whole wire went **3,605 → 3,654 ok / 140 → 143 modules** (this set is +13 of
the +49; the other +36 is set D); tier-1 builds 2,194 / 2,026 jobs at 9.45 / 6.19 s, **0 warnings**;
all five headlines' axioms `[propext, Classical.choice, Quot.sound]`. Record:
[../../../logs/phase3-algebra-and-congruence-subgroup.md](../../../logs/phase3-algebra-and-congruence-subgroup.md).
The order's two corrections, recorded there: module 1 is **10 public / 0 private**, not 10 / 1 (no
helper needed privating), and row 2's `set_option maxHeartbeats 9600000` was **precaution** — the
module is green at both 200,000 and 100,000 and fails at 20,000, so the `-D` flag was provably live.
The shadowing hazard the order predicted for `norm_of_subsingleton` fired instead at
`IsIntegral.of_finite` (inside `namespace Algebra` the bare name is the *instance*
`Algebra.IsIntegral.of_finite`; fix `_root_.IsIntegral.of_finite`). Sibling
set of this round: [WORKORDER-PH3D-congruence-subgroup-lattice.md](WORKORDER-PH3D-congruence-subgroup-lattice.md).
The pricing note is [TOPIC-phase3-small-supplements.md](TOPIC-phase3-small-supplements.md), whose
`Algebra` row (5 nodes / 349 lines / 13 publics) this order confirmed by measurement.

The standard is [TOPIC-mathlib-module-homing.md](../TOPIC-mathlib-module-homing.md) §3. All five
statements sit in mathlib's own `Algebra` namespace and name only mathlib objects
(`integralClosure`, `Algebra.adjoin`, `IntermediateField.adjoin`, `ValuationSubring`, `Algebra.norm`,
`Module.finrank`, `IsNilpotent`), so **the headline names are kept verbatim** and only the pin's
inner block label is at issue. The paths split by subject:

| # | node | pin `S_` lines | pin decls | the mathematics |
|---:|---|---:|---:|---|
| 1 | `Algebra.finite_integralClosure_adjoin_singleton_of_isAlgClosed` | 236 | 9 | for `k` algebraically closed, `x` transcendental over `k` and `F/k(x)` finite-dimensional, the integral closure of `k[x]` in `F` is a **finite** `k[x]`-module |
| 2 | `Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem` | 79 | 1 | clearing denominators: for `f` with `F/L(f)` finite and any `z : F` there is a nonzero `q₀ ∈ L[f]` such that `q₀ z` lies in **every** valuation subring of `F` containing `L` and `f` |
| 3 | `Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap` | 18 | 1 | if `a - algebraMap R A μ` is nilpotent then `Algebra.norm R a = μ ^ finrank R A` |
| 4 | `Algebra.norm_prod` | 10 | 1 | the norm on a product algebra is the product of the norms |
| 5 | `Algebra.norm_of_subsingleton` | 6 | 1 | the norm of an element of a subsingleton algebra is `1` |

Rows 1–2 are one subject — **the integral model of a function field** (integrality and
denominators over a simple adjoin) — and rows 3–5 are another — **elementary computations with the
algebra norm** (the three lemmas a mathlib PR would append to `RingTheory/Norm/Basic.lean`).

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the per-module protocol — `spec-pin:` header, `spec/check_port.py`, no in-source
per-declaration marker.

**Not this set:** the `CongruenceSubgroup` rows (set D); any edit to an existing module; any
promotion; the `MeasureTheory`, `ValuationSubring` and `ContinuousLinearMap` families of the
phase-3 note.

## 1. Measurement

`port_advise.py --target` ×5 → `.substitutions` is **empty** (0 trusted / 0 suspect), no residue, no
port-name clash, and **no name is proved in two of the five files**. 18 target declarations; the
`S_` files hold 9 + 1 + 1 + 1 + 1.

## 2. Deliverables — two modules

| rows | module | namespace | public | private |
|---|---|---|---:|---:|
| 1–2 | `FLTForHuman/RingTheory/IntegralClosure/FunctionField.lean` | `Algebra`, helpers in the pin's own `Algebra.FiniteIntegralClosureAdjoinSingleton` | 10 | 1 |
| 3–5 | `FLTForHuman/RingTheory/Norm/Elementary.lean` | `Algebra` | 3 | 0 |

Rules:

* **Headlines keep the pin's full names** (`Algebra.<node>`) and the **wrapper's** statement text
  (the `S_` files' `solution` statements are the same theorem; the wrapper is authoritative).
* **Row 1's inner namespace stays as the pin wrote it**: `FiniteIntegralClosureAdjoinSingleton` is
  descriptive (it names the theorem), not a phase label, so it is kept and the helpers keep their
  last names. Do not "improve" it.
* **`solution` is not ported** (five of them, one per file). Each headline is stated once, at the
  wrapper's name, with the `solution` body. Rows 3–5's `solution` *is* the entire proof.
* **`RingTheory/Norm/Elementary.lean`** is the port's name for the block a mathlib PR would append
  to `RingTheory/Norm/Basic.lean`; the port may not add to mathlib, and this directory is mathlib's
  home for `Algebra.norm`, so a user looking for norm computations finds it there. Say that in the
  header.
* **Header:** a leading `/- … -/` block naming the subject, the pin `S_` file and its line count,
  then, **`Theorems/` wrapper line first**:

  ```lean
  spec-pin: Theorems/Thm_Algebra_<stem>.lean
  spec-pin: P2M/Sol/S_Algebra_<stem>.lean
  ```

  Module 1 carries four `spec-pin:` lines (two wrappers, then the two `S_` files); module 2 carries
  six.

## 3. Route and recorded negatives

* **No definition gate.** All five `S_` files import `Mathlib` (rows 1–2) or
  `Mathlib.RingTheory.Norm.Basic` + two more mathlib modules (rows 3–5), plus `P2M.Util`. No pin
  `Definitions/Def_*.lean`, so nothing to home or promote.
* **Rows 1–2's bare `import Mathlib` must go.** It costs **86 s** to load on this checkout, which
  is more than the edit loop allows. Starting points: `Mathlib.RingTheory.IntegralClosure.…`,
  `Mathlib.RingTheory.Valuation.ValuationSubring`, `Mathlib.FieldTheory.IntermediateField.Adjoin.…`,
  `Mathlib.RingTheory.Noetherian`, `Mathlib.Algebra.Polynomial.…`. Add only what the elaboration
  asks for, and report the final lists — they are the set's reusable output.
* **Rows 3–5 keep their own imports** (`RingTheory.Norm.Basic`, `LinearAlgebra.Eigenspace.Zero`,
  `LinearAlgebra.Charpoly.BaseChange` for row 3).
* **Row 2 carries `set_option maxHeartbeats 9600000` and `set_option autoImplicit false` in the
  pin.** The port's rule (§5) is no module-level heartbeat override: try it at the 200,000 edit-loop
  cap first. If it does not close, bisect the declaration and report what unfolded — **do not**
  inherit the 9.6 M bump without a recorded diagnosis, and never add a bare
  `set_option maxHeartbeats`.
* **Watch the namespace**: inside `namespace Algebra`, mathlib's root-level `norm_of_subsingleton`
  (the normed-group lemma, in `Analysis/Normed/Group/Basic.lean`) is visible, so an unqualified use
  of that name in a proof resolves to the normed one. Qualify or state at `Algebra.norm_of_subsingleton`
  and reference it fully; the collision is a **statement-level** name clash that Lean would merge
  silently if the port re-declared it at root — it must be `Algebra.norm_of_subsingleton`.
* **mathlib-first (recorded negative, 2026-10-20).** No name in the five files occurs in
  `Mathlib/` at `5ed29652` / `v4.34.0`. `Mathlib/RingTheory/Norm/` (`Basic`, `Defs`,
  `Transitivity`) has no `norm_prod` for the product algebra, no `norm_of_subsingleton`, and no
  `IsNilpotent` lemma; the mathlib hits for those two names are the normed-group/normed-space ones
  (different namespace, different statement). No `integralClosure`-finiteness statement of row 1's
  shape either. **Do not strengthen** a statement toward any neighbour (playbook §4).

## 4. Build discipline (verbatim)

```
tier 0  edit loop    timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>
tier 1  module done  flock .lake/flt_build.lock timeout 300 lake build <module>
tier 2  wave         none — no existing module is edited
tier 3  milestone    no whole-tree build without the user's permission
```

Every `lake env lean` and every `lake build` runs under `flock .lake/flt_build.lock`; the sibling
set D of this round may be building at the same time. Report the wall time of each edit loop and
each `lake build` (jobs + seconds).

## 5. Verification (record the numbers on the tree you leave)

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/RingTheory/IntegralClosure/FunctionField.lean
python3 spec/check_port.py --force FLTForHuman/RingTheory/Norm/Elementary.lean
python3 spec/check_port.py --all      # record the before/after totals
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.RingTheory.IntegralClosure.FunctionField
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.RingTheory.Norm.Elementary
```

plus `#print axioms` on the five headlines (`[propext, Classical.choice, Quot.sound]`), an `rg`
sweep of both modules for `sorry` / `admit` / a top-level `axiom` / `native_decide` / a bare
`import Mathlib` / a `maxHeartbeats` override, `git status` showing only the two new files, and
**0 warnings** from both builds.

## 6. Report shape

Per module: path, lines, public/private counts, checker verdict, build jobs/time, axioms. Then the
two module totals vs the expected +13 and the `--all` before/after; every drift site fixed (file,
line, old → new); **the targeted import lists** for rows 1–2; what happened to row 2's 9.6 M
heartbeat bump; anything unexpected.

## 7. Hub prohibition and stop conditions

No subagent edits an existing module, appends to `spec/old_check_stmts.py`, or touches
`spec/decl_markers.tsv`. If a promotion or a marker entry seems required, **stop and report** with
the declaration and the `build_ladder.py --edit` price. Stop and report if a pin statement cannot be
reproduced verbatim, if row 2's proof will not close at the edit-loop cap (report the diagnosis, do
not raise the cap), or if a module exceeds the ~60 s reporting threshold.
