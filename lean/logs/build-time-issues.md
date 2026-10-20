# Build-time issues — the D-S column's register, 2026-10-20

The build-cost state this column leaves behind, so the next session does not rediscover it. Companion
registers: [../instance-friction.md](../instance-friction.md) (instance-search *friction*, with re-runnable
probes), [porting-playbook.md](../porting-playbook.md) §5–§6 (the rules), and
[../../notes/lean-build-cost.md](../../notes/lean-build-cost.md) (the measurement method).

**The policy these entries sit under** (column note §5): the 200,000 edit-loop cap is a **diagnostic**, not
the build budget — the library's own setting is the lakefile's `maxHeartbeats 4000000`. A declaration that
exceeds the diagnostic is either (i) instance synthesis, in which case pin the argument the search is
guessing, or (ii) arithmetic defeq, in which case record the pin's own bump, the bisection and the diagnosis
in the module header and land it. Deferral is reserved for a proof that no longer **closes** at any budget.

## 1. Landed, but over the edit-loop budget — the rework is owed

`EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow`
(`ModularForms/Eisenstein/ResidueSumQExpansion.lean`):

* needs **300,000–400,000** hearts (bisected: 300,000 fails inside `h6`, 400,000 passes); the pin sets
  **4,000,000** on that one declaration;
* the diagnosis is **arithmetic defeq**, not instance synthesis: `Add.add` 304,515 unfoldings,
  `HAdd.hAdd` 266,601, `HMul.hMul` 208,538, `Nat.rec` 193,653, and no class-instance counter of note;
* cost at the library cap: **36.0 s wall / 33.7 s user** for a 277-pin-line module — 6× its siblings;
* landed because the library builds at 4M (tier-1 3,764 jobs / 31 s), with **no `set_option`**, the pin's
  bump and the bisection in the module header;
* **the 40-minute shape rework was never spent** (only a `have hsigma` dedup that moved the file from
  failing at 400k to passing at 400k). Rework: cut the `h6`/`hfin` computation into `private` helpers at the
  seams the pin already has, so no declaration needs the bump. Recorded in
  [ds-leaf-families-wave2.md](ds-leaf-families-wave2.md) §4 as owed.

## 2. Not landed, far over budget — parked with its diagnosis

`SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace` (the `ZLattice` pair's blocker), draft at
`lean/tmp/zlattice/PoissonSummationPi.lean`:

* **429 s** at the library cap, exit 0, 0 errors, 0 `sorry` — so it is slow, not broken;
* **typeclass inference 237 s** of it (elaboration 191 s, tactics 1.79 s, `simp` 0.53 s) — i.e. the
  *instance* class, so it is fixable by shape;
* three declarations at **67.6 / 66.5 / 56 s**, unnamed by `set_option profiler true` (which prints
  anonymous `elaboration took` lines — one reason that profile run was low-yield);
* the pin sets `maxHeartbeats 16000000` on its `PeriodizeLift` section and `3200000` file-wide;
* one hotspot already fixed: pinning `(f := toUnitAddTorus)` on the four `Function.surjInv` and one
  `Function.surjInv_eq` (minimal proof `lean/tmp/zlattice/pi_G.lean`) — the pattern for the rest;
* `HANDOVER.md` in the same directory carries the measurement, the regeneration command, and the
  "cut at section boundaries, never truncate" warning.

## 3. The tree's oleans are incomplete — treat a "missing declaration" as possibly a stale build

Oleans that had to be rebuilt during this session (some were absent with only `.olean.hash`/`.trace`
left): `FLTForHuman/ModularForms/Level/Degeneracy`, `FLTForHuman/ModularForms/Eisenstein/ConstTermCubeIntegral`,
`FLTForHuman/Algebra/TorsionByCoordinates`, `FLTForHuman/ModularForms/CohCarrier/TorsionOrbit`. In
addition, two **mathlib** modules have no olean in this tree — `Mathlib.Tactic.Omega` and
`Mathlib.LinearAlgebra.Quotient` — although neither import turned out to be needed (`omega` ships in the
core toolchain; the `Quotient` API arrives transitively). Symptom: `unknown identifier` or `object file …
does not exist` where the source looks fine. Fix: `flock .lake/flt_build.lock timeout 300 lake build <module>`
on the module that should own the olean.

## 4. One compile at a time — the lock and the box

* A single `lake build` may hold `.lake/flt_build.lock` for **40+ minutes**; a queued build waits silently,
  which looks like a hang. Check with `flock -n .lake/flt_build.lock true` (exit 1 = held) before blaming
  the compiler.
* The box is **memory-tight**: 7.9 GB total with swap in use during parallel compiles. Concurrent
  elaborations thrash and inflate everybody's wall time, so serialise both builds and edit loops.

## 5. Measurement pitfall

`/usr/bin/time -f "%e %U" timeout … lake env lean file.lean` reports the **wrapper's** CPU, not the
grandchild's: a 110 s, 110 %-CPU elaboration showed `user 0.4 s` and looked like a lock wait. To measure
CPU, watch the `lean` process (`ps -o time,pcpu`) or invoke it directly; to measure wall, `time` the shell
job. This cost one wrong diagnosis this session (a "blocked" module that was in fact computing).

## 6. The head of the distribution (not defects, but watch these)

Measured this session at the library cap: `ResidueSumQExpansion` **36 s**, `LogBranchAndPrimitiveRoot`
**20 s**, `HexagonalLattice` **16–18 s**, `PeriodPair/InvariantsTorsion` **14 s**, `MulActionOrbitCounts`
9.5 s build; everything else in the ~60 new modules is **2–13 s**. No module in the wave needed more than
200k hearts except the two in §1–§2.
