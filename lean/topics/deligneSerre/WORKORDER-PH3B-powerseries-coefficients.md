# WORKORDER-PH3B — the `PowerSeries` coefficient family of the D-S cone

**Status (closed 2026-10-20): landed and reviewed green.** Three modules, **855 lines**, **15
statement-checked declarations** (7 + 6 + 2), zero host edits, zero promotions, zero markers, and
**no `import Mathlib`** — the four pin files' bare `import Mathlib` became 4 / 7 / 15 named
imports, cutting the load from 86 s to 5–8 s a module. Checker **+15** (set A of this phase is the
other +51 / 2 modules: whole wire **3,539 → 3,605 ok / 135 → 140 modules**, 0 mismatch / 0
missing / 11 own / 0 kw). Tier-1 builds 1,448 / 2,069 / 2,042 jobs at 4.9 / 8.1 / 14.1 s, **0
warnings**; all four headlines' axioms `[propext, Classical.choice, Quot.sound]`. Record:
[../../../logs/phase3-module-end-and-powerseries.md](../../../logs/phase3-module-end-and-powerseries.md).
The expected +16 is measured as +15 because `Saturation.main` is `private` per §2 and the checker
skips private declarations — no `MISSING`, no marker. Set A of the same phase is
[WORKORDER-PH3A-module-end-eigenspace.md](WORKORDER-PH3A-module-end-eigenspace.md); the pricing
note is [TOPIC-phase3-small-supplements.md](TOPIC-phase3-small-supplements.md), now out of date
by three rows (it priced `PowerSeries` at 3 nodes / 265 lines; the demand reads **4 / 696** —
the row it missed is the 431-line saturated-lattice node, three times the size of the rest of
the family).

The homing standard is [TOPIC-mathlib-module-homing.md](../TOPIC-mathlib-module-homing.md) §3.
All four statements are about `PowerSeries` — mathlib's object — so the **headline namespaces
are kept** (`PowerSeries.*`, exactly as the pin writes them) and only the pin's inner labels
(`SaturationLemma`, `A2GaloisDescentPS`) are folded into descriptive sub-namespaces. The paths
mirror mathlib's `Mathlib/RingTheory/PowerSeries/`, which is where a user looks for power-series
theorems; the *valuation*, *subring* and *Galois* content is a mathlib **library** dependency,
not a theory from another area, so it does not drag the home to `RingTheory/Valuation/` or
`FieldTheory/Galois/` (§3 rule 1, second sentence).

| # | node | pin `S_` lines | the mathematics |
|---:|---|---:|---|
| 1 | `PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated` | 431 | reduction of a saturated lattice of integral power series: for a valuation subring `A` of `L` and a `ℤ`-saturated subgroup `N ⊆ ℤ⟦X⟧`, every non-zero `V` in the `L`-span of `N`'s image is `C c · (u.map A.subtype)` with `c ≠ 0`, `u ∈ A⟦X⟧`, and the residue of `u` non-zero and back in `N`'s image |
| 2 | `PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem` | 186 | Galois descent for power series: if `A ∈ ℚ̄⟦X⟧` has all coefficients in a finite-dimensional `K ⊆ ℚ̄` and every `σ`-conjugate of `A` lands in an `E`-subspace `V`, then `A` is a `K`-combination of `ℚ`-rational series whose images lie in `V` |
| 3 | `PowerSeries.coeff_mem_subring_of_coeff_mul_mem` | 41 | dividing by a unit-led power series keeps coefficients in a subring: if `U`'s coefficients lie in `R ⊆ K`, `U` vanishes below `m₀` and its `m₀`-th coefficient is a unit of `R`, and `P * U`'s coefficients lie in `R` below `L`, then `P`'s coefficients lie in `R` below `L - m₀` |
| 4 | `PowerSeries.exists_sum_smul_eq_of_forall_coeff_mem` | 38 | coefficient descent: if a `K₀`-linear combination of series with coefficients in a subfield `K₀` has all its coefficients in `K₀`, then the same series is a `K₀`-linear combination with coefficients in `K₀` |

Subjects: rows 1 and 3 are "what the coefficients of a product/lattice force the coefficients
of a factor to be"; row 4 is the subfield version of the same question; row 2 is Galois descent,
which uses the normal basis. Three modules: **`Saturation.lean`** (row 1, the big one),
**`CoeffMem.lean`** (rows 3 + 4, the two coefficient-membership statements, 79 lines together),
**`GaloisDescent.lean`** (row 2).

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the per-module protocol — `spec-pin:` header, `spec/check_port.py`, no in-source
per-declaration marker.

**Not this set:** any edit to an existing module; any promotion; the `Module.End` family (set
A); anything under `FLTForHuman/Analysis/PowerSeries/` (that is
`EisensteinAlgSeries`, a different set).

## 1. Measurement

`port_advise.py --target` ×4 → `port_plan.py` (2026-10-20, on the tree as found):

| quantity | value |
|---|---:|
| raw `S_` lines | 696 |
| declaration lines | 645 |
| boilerplate (imports/attrs/`p2m`) | 51 |
| distinct declaration groups | 15 |
| duplicate copies removable | 18 |
| already in the port (vetted) | **0** |
| substitutions | **0 trusted / 0 suspect** |
| **net new math lines** | **627** |

No name is proved in two of the four files. One cross-pool duplicate is recorded and is **not**
a shared home: row 2's `descent` (89 lines) has the same last name as eight other pin files
(`port_advise` ratio far below identity) — do not try to import any of them.

## 2. Deliverables — three modules

| row | module | namespace (pin → port) | public |
|---|---|---|---:|
| 1 | `FLTForHuman/RingTheory/PowerSeries/Saturation.lean` | `PowerSeries.SaturationLemma` → `PowerSeries.Saturation`; headline at `PowerSeries` | 7 |
| 2 | `FLTForHuman/RingTheory/PowerSeries/GaloisDescent.lean` | `A2GaloisDescentPS` → `PowerSeries.GaloisDescent`; headline at `PowerSeries` | 5 |
| 3 | `FLTForHuman/RingTheory/PowerSeries/CoeffMem.lean` | both headlines at `PowerSeries`; no inner namespace needed | 2 |

Rules that apply to all three:

* **The headline keeps the pin's full name, exactly** — `PowerSeries.<node>`. Do not rename a
  headline and do not move it out of `PowerSeries`.
* **The pin's inner labels go.** `SaturationLemma` → `PowerSeries.Saturation` (the pin nests it
  *inside* `namespace PowerSeries`, so its declarations are `PowerSeries.Saturation.*` in the
  port), `A2GaloisDescentPS` → `PowerSeries.GaloisDescent` (`A2` is a phase label). Keep every
  **last name**: `linearIndependent_comp_ringHom`, `cvec`, `cvec_apply`, `coeff_map_intCast`,
  `coeff_sum_smul_map`, `map_sum_smul_map`, `main`, `comp_algebraMap_rat`,
  `apply_algebraMap_rat`, `eq_sum_dualBasis_mul`, `sum_dualBasis_mul_apply`, `descent`.
* **`solution` is not ported.** Each `S_` file ends with a `solution` theorem whose statement is
  the wrapper's. State the headline **once**, at the wrapper's name, with the `solution` body
  (`= Saturation.main …` / `= GaloisDescent.descent …`; rows 3–4's `solution` *is* the whole
  proof, so it becomes the headline's body verbatim).
* **`main` is `private`** at `PowerSeries.Saturation.main` (row 1) — it is the pin's wrapper for
  `solution`, no consumer names it (homing note §8.2 F). Row 2's `descent` is the pin's
  proof-bearing public: keep it public at `PowerSeries.GaloisDescent.descent` — it is part of
  the verified surface.
* **`linearIndependent_comp_ringHom` stays public** at `PowerSeries.Saturation.linearIndependent_comp_ringHom`,
  even though it is generic linear algebra (a field hom carries `𝔽`-linear independence to
  `k`-linear independence) and its only consumer is this development. Visibility and re-homing
  are separate passes (homing note §8.10); record the observation in the module header as a
  future `LinearAlgebra/` candidate. Do **not** make it private and do **not** move it now.
* **`scoped` stays scoped.** Row 2's file declares three `scoped instance`s
  (`isAlgebraicQbar`, `isAlgClosureQbar`, `normalQbar`) and `local notation "Qb"`; keep the
  `scoped` keyword, the `local notation`, the `noncomputable section` and the `open Classical in`
  (dropping a `scoped` creates a spurious checker `MISSING`).
* **Header:** a leading `/- … -/` block naming the subject, the pin `S_` file and its line count,
  the pin's inner namespace and where it went, then, **`Theorems/` wrapper line first**:

  ```lean
  spec-pin: Theorems/Thm_PowerSeries_<stem>.lean
  spec-pin: P2M/Sol/S_PowerSeries_<stem>.lean
  ```

  Module 3 carries **four** `spec-pin:` lines (the two wrappers first, then the two `S_` files).

## 3. Route and recorded negatives

* **No definition gate.** All four `S_` files import `Mathlib` plus `P2M.Util` and nothing else —
  no pin `Definitions/Def_*.lean` module, so nothing to home and nothing to promote.
* **`import Mathlib` must go.** All four say `import Mathlib`; replace it with the modules the
  proof actually names. `import Mathlib` costs **86 s** to load on this checkout, so a module
  that keeps it cannot be edit-looped at all — deriving the targeted list is part of the job.
  Starting points: `Mathlib.RingTheory.PowerSeries.Basic` (the `coeff`/`map`/`C`/`mk` API),
  `Mathlib.RingTheory.Valuation.ValuationSubring` (`ValuationSubring`, `A.subtype`),
  `Mathlib.RingTheory.LocalRing.Basic` / `…Ideal.Maximal` (`IsLocalRing.residue`,
  `ResidueField`), `Mathlib.LinearAlgebra.LinearIndependent.Basic`,
  `Mathlib.FieldTheory.Galois.Basic` + `Mathlib.FieldTheory.NormalClosure` (row 2's
  `normalClosure`, `liftNormal`, `traceForm`, `trace_eq_sum_automorphisms`,
  `IntermediateField.normalClosure`), `Mathlib.LinearAlgebra.Trace` (row 2's dual basis over the
  trace form). Add only what the elaboration asks for.
* **`p2m_export` / `p2m_open` / `p2m_reactivate` are dropped.** Row 1's file has
  `p2m_export "PowerSeries" "coeff_mk mk coeff_smul coe_one coeff_map smul_eq_C_mul ext
  map_eq_zero map C coeff coe_smul"`, which registers unqualified aliases for those
  `PowerSeries` lemmas. Row 2 has two `p2m_reactivate` lines at the file's end. Both are
  `P2M.Util` bookkeeping: drop them, and where the alias was load-bearing for an unqualified
  name in a `rw`/`simp`, write `open PowerSeries` (row 1 already has it) or qualify the name —
  record every such site.
* **No scout yet.** These four were not pre-compiled on `v4.34.0` (set A's row 1 was, and came
  back warning-only). Expect the usual small drift: deprecated `if_pos`/`if_neg`/`dif_pos`/
  `dif_neg` (`ite_eq_left` / `ite_eq_right` / `dite_eq_left` / `dite_eq_right`), `haveI`→`have`
  linter suggestions, and possibly a renamed `Algebra.traceForm` / `IntermediateField.normalClosure`
  lemma in row 2. Fix with the pin's own terms; record every site.
* **mathlib-first check (recorded negative, 2026-10-20).** No name in the four files occurs in
  `Mathlib/` at `5ed29652` / `v4.34.0`. The concept is adjacent but not present:
  `Mathlib/RingTheory/PowerSeries/CoeffMulMem.lean` has `coeff_mul_mem_ideal_*` for **ideals**
  (not the `Subring` division of row 3) and nothing about saturated subgroups or spans;
  `Mathlib/FieldTheory/Galois/` has no descent-for-submodules result. **Do not strengthen** a
  statement toward a more general one (playbook §4).

## 4. Build discipline (verbatim)

```
tier 0  edit loop    timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>
tier 1  module done  flock .lake/flt_build.lock timeout 300 lake build <module>
tier 2  wave         none — no existing module is edited
tier 3  milestone    no whole-tree build without the user's permission
```

Every `lake env lean` and every `lake build` runs under `flock .lake/flt_build.lock`; set A of
this phase may be building at the same time, so the lock — not the schedule — serializes them.
Report the wall time of each edit loop and each `lake build` (jobs + seconds). A module over
~120 s elaboration or ~300 s build is a build-time defect to report, not to work around.

## 5. Verification (record the numbers on the tree you leave)

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/RingTheory/PowerSeries/Saturation.lean        # ≈8 ok
python3 spec/check_port.py --force FLTForHuman/RingTheory/PowerSeries/GaloisDescent.lean      # ≈6 ok
python3 spec/check_port.py --force FLTForHuman/RingTheory/PowerSeries/CoeffMem.lean           # ≈2 ok
python3 spec/check_port.py --all      # record the before/after totals
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.RingTheory.PowerSeries.Saturation
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.RingTheory.PowerSeries.GaloisDescent
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.RingTheory.PowerSeries.CoeffMem
```

plus `#print axioms` on the four headlines (`[propext, Classical.choice, Quot.sound]`), an `rg`
sweep of the three modules for `sorry` / `admit` / a top-level `axiom` / `native_decide` / a bare
`import Mathlib` / a `maxHeartbeats` override, `git status` showing only the three new files, and
**0 warnings** from all three builds.

## 6. Report shape

Per module: path, lines, public/private counts, checker verdict (`ok` / mismatch / missing),
build jobs/time, axioms. Then the three module totals vs the expected +16 and the `--all`
before/after; every drift site fixed (file, line, old → new); **the import list chosen for each
module** (the `import Mathlib` replacement — this is the set's main risk and its main reusable
output); every `p2m_export` alias site and what replaced it; anything unexpected.

## 7. Hub prohibition and stop conditions

No subagent edits an existing module, appends to `spec/old_check_stmts.py`, or touches
`spec/decl_markers.tsv`. If a marker entry seems genuinely required — in particular if the
checker reports a `MISSING` on row 1's `main` or a wrong last-name match on `descent` — **stop
and report** with the declaration and the suggested entry. Stop and report if a pin statement
cannot be reproduced verbatim, if the targeted import list cannot be made to close a module's
proof (do not fall back to `import Mathlib`), or if a proof exceeds the 200,000 heartbeat cap.
