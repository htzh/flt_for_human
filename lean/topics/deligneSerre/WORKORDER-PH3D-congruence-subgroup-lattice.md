# WORKORDER-PH3D — the `CongruenceSubgroup` lattice family of the D-S cone

**Status (closed 2026-10-20): the four nodes landed and were reviewed green; the fifth is deferred
to its priced lift (§8).** One set, **one module, 865 lines, 36 statement-checked declarations**,
zero host edits, zero promotions, zero markers. Checker **+36** (set C is the other +13 of the
round's +49; whole wire **3,605 → 3,654 ok / 140 → 143 modules**, 0 mismatch / 0 missing / 11 own /
0 kw); tier-1 build 3,581 jobs / 6.5 s, **0 warnings**; four headlines' axioms
`[propext, Classical.choice, Quot.sound]`. Record:
[../../../logs/phase3-algebra-and-congruence-subgroup.md](../../../logs/phase3-algebra-and-congruence-subgroup.md).
The order's expected **+43** is the pin `S_` declaration count, not the wired count: 43 − 2 imported
(`det_eq`, `Gamma_le_Gamma1`) − 4 `solution` + **4** headlines − 5 port-private = **36**. The pin's
`set_option maxHeartbeats 3200000` was precaution again (green at 200,000). Sibling set of this round:
[WORKORDER-PH3C-algebra-norm-and-integrality.md](WORKORDER-PH3C-algebra-norm-and-integrality.md).

**The phase-3 note excluded this namespace, and that exclusion is wrong.** Its §3 row reads
"`UpperHalfPlane.qExpansion_*`, `CongruenceSubgroup.*` (~500 lines) | modular forms — FLT-flavoured
subject, test 2", i.e. it rejected the family on the *subject* test without reading the statements.
Read against the statements (the note's own caveat: "read each `Theorems/` statement before
believing the namespace-based subject filter"), all five are **group theory of mathlib's own
congruence-subgroup API**: `Gamma`, `Gamma0`, `Gamma1`, `ModularGroup.S`/`T`, `Subgroup.zclosure`,
`Subgroup.relIndex`, `ZMod` — no Weierstrass, no modular form, no Hecke operator, no adele. mathlib
files exactly this subject at `Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean` and has
none of these five statements. They pass test 2, test 3 (the mathlib-first negative below) and
test 4 (no `Definitions/` gate).

Test 1 (size, ≤ ~250 pin lines a node) is where the family is honest about itself: one node is
**406** lines. It is taken anyway, and the reason is recorded — the family is gate-free, its other
four nodes are 85–242 lines, and the 406-line node is one development, not a gate for anything.

| # | node | pin `S_` lines | pin decls | the mathematics |
|---:|---|---:|---:|---|
| 1 | `CongruenceSubgroup.Gamma_div_le_gamma1_inf_Gamma_sup_zpowers` | 406 | 34 | level lowering with a lower unipotent: `Gamma (N/p) ≤ (Gamma1 N ⊓ Gamma (N/p ^ N.factorization p)) ⊔ zpowers (S * T ^ (N/p) * S⁻¹)` |
| 2 | `CongruenceSubgroup.exists_finset_transversal_adapted_T_S` | 179 | 1 | a finite transversal of `±Γ` in `SL(2, ℤ)`, adapted to `T` and `S`, for `Γ` of finite index whose `T`-period is `h₀` and which misses the whole `S·T^ℤ` line |
| 3 | `CongruenceSubgroup.mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff` | 142 | 2 | first-column criteria: `±β ∈ Γ₁(N)` iff `β₁₀ = 0` and `β₀₀ = ±1` in `ZMod N`; and `∃ j, ±β T^j S⁻¹ ∈ Γ₁(N)` iff `β₁₀ = ±1`; plus the Bézout witness |
| 4 | `CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd` | 85 | 6 | `(Γ₁(M) ⊓ Γ₀(Mq)).relIndex (Γ₁ M) = q` for `q ∣ M` |
| — | `CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three` | 242 | 40 | **deferred (§8)**: `⟨T, U, -1⟩ = Γ₀(3)`. 35 of its 40 declarations are *already in the tree* as the private `Gamma0Three` engine of `ModularForms/WeightOne/EisensteinChiNegThree.lean`; the node is a **lift** plus five new declarations, and the lift's dependent wave is 51 modules / 30,597 lines / ≈413 s. |

**This is the congruence-subgroup lattice**, which is one sentence: how `Γ(N) ⊆ Γ₁(N) ⊆ Γ₀(N)`
sit in `SL(2, ℤ)`, with the membership criterion, the relative index, the coset transversal and the
level-lowering inclusion.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the per-module protocol — `spec-pin:` header, `spec/check_port.py`, no in-source
per-declaration marker.

**Not this set:** the Γ₀(3) node and any edit to `EisensteinChiNegThree.lean` (§8); the `Algebra`
rows (set C); the `MeasureTheory`, `ValuationSubring`, `ContinuousLinearMap` families.

## 1. Measurement

`port_advise.py --target` ×5 → `.substitutions` is **36** entries, of which **35 belong to the
deferred Γ₀(3) node** (all byte-identical private copies in `EisensteinChiNegThree.lean`, namespace
`FLT.FLT.AnalyticCore.Gamma0Three`). For **this** dispatch the substitution list is exactly two, both
binder-spelling (`binder_only: true`), and both must be **imported, not re-proved**:

* `det_eq` — pin `S_…Gamma_div_le…:85` (`(m : SL(2, ℤ)) : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1`) has its
  public copy at `ModularForm.HeckeRepresentatives.det_eq`
  (`FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean`); the port also carries **seven**
  private copies, and this is the port's standing un-promoted dedup candidate
  ([PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §9). Import the public one; do not add an
  eighth copy.
* `Gamma_le_Gamma1` — pin `S_…Gamma_div_le…:101`, public in the port as
  `CuspForm.LiNormSq.Gamma_le_Gamma1` (`FLTForHuman/ModularForms/Analytic/NormSqPow.lean`); the
  `port_advise` residue flags it `needs_review` because one side carries it as a section variable.
  **Read both texts** and import if the statements agree modulo binder spelling; if they do not,
  transcribe the pin's text locally and say so in the report. Do not promote anything.

## 2. Deliverable — one module

| module | namespace (pin → port) | public | private |
|---|---|---|---:|---:|
| `FLTForHuman/NumberTheory/ModularForms/CongruenceSubgroupLattice.lean` | headlines at `CongruenceSubgroup`; `GammaGenSol` → `CongruenceSubgroup.LowerUnipotent`; `GCusp` → `CongruenceSubgroup.FirstColumn`; `IndexDvd` → `CongruenceSubgroup.Index` | ≈39 | ≈4 |

Rules:

* **Headlines keep the pin's full names** — `CongruenceSubgroup.<node>` — and mathlib's
  `CongruenceSubgroup` is the object namespace, so no headline is renamed.
* **The pin's inner labels go**, keeping every last name: `GammaGenSol` (a generated label),
  `GCusp`, `IndexDvd`. The pin's `private` helpers stay `private` (`intCast_val`,
  `dvd_entry`, `cHom`, and whatever the 406-line file marks private).
* **`solution` is not ported** (four of them). Each headline is stated once, at the wrapper's name,
  with the `solution` body.
* **`open scoped MatrixGroups` is load-bearing** in every one of these files (the `!![…]` and
  `SL(2, ℤ)` notation). Keep each file's own `open`/`open scoped` lines as the pin writes them, and
  keep the `set_option autoImplicit false` where the pin has it.
* **Header:** a leading `/- … -/` block naming the subject, the four pin `S_` files and their line
  counts, and the correction of the phase-3 note's exclusion; then, **`Theorems/` wrapper lines
  first**:

  ```lean
  spec-pin: Theorems/Thm_CongruenceSubgroup_<stem>.lean      (×4)
  spec-pin: P2M/Sol/S_CongruenceSubgroup_<stem>.lean         (×4)
  ```

## 3. Route and recorded negatives

* **No definition gate.** All four `S_` files import `Mathlib` plus `P2M.Util` and nothing else.
* **`import Mathlib` must go** (86 s of olean loading on this checkout — more than the edit loop
  allows). Starting points: `Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`
  (`Gamma`, `Gamma0`, `Gamma1`), `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`
  (`ModularGroup.S`, `ModularGroup.T`, the `!![…]` API), `Mathlib.NumberTheory.Modular`
  and/or `Mathlib.NumberTheory.ModularForms.Bounds` (the `ModularGroup` API extensions),
  `Mathlib.GroupTheory.Index` (`Subgroup.relIndex`), `Mathlib.GroupTheory.SpecificGroups.…` as
  needed, `Mathlib.Data.ZMod.Basic` (v4.34: `Mathlib.Algebra.Field.ZMod` subsumes it),
  `Mathlib.Data.Nat.Factorization.Basic`. Add only what the elaboration asks for and **report the
  four lists** — they are the set's reusable output.
* **`p2m_*` lines are dropped** (there are `p2m_reactivate` lines at the end of the 406-line file
  and none elsewhere); they are bookkeeping for the dropped `solution`.
* **No scout yet.** These four were not pre-compiled on `v4.34.0`; set C's sibling round expects the
  usual small drift. Expect deprecated `if_pos`/`if_neg`/`dif_pos`/`dif_neg` and `haveI`→`have`
  linter suggestions; fix with the pin's own terms and record every site. If a `decide +kernel`
  proof (rows 1's Schreier lemmas are in the deferred node, but check) fails, report it rather than
  rewriting the decision procedure.
* **mathlib-first (recorded negative, 2026-10-20).** No name in the four files occurs in
  `Mathlib/` at `5ed29652` / `v4.34.0`; `Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean`
  has the definitions and the `≤`/index lemmas mathlib chose to state, but no level-lowering
  inclusion with a unipotent, no adapted transversal, no first-column criterion and no
  `relIndex` formula for `Γ₁ ⊓ Γ₀`. **Do not strengthen** a statement (playbook §4).

## 4. Build discipline (verbatim)

```
tier 0  edit loop    timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>
tier 1  module done  flock .lake/flt_build.lock timeout 300 lake build <module>
tier 2  wave         none — no existing module is edited
tier 3  milestone    no whole-tree build without the user's permission
```

Every `lake env lean` and every `lake build` runs under `flock .lake/flt_build.lock`; the sibling
set C may be building at the same time. Report the wall time of each edit loop and each build.

## 5. Verification (record the numbers on the tree you leave)

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/NumberTheory/ModularForms/CongruenceSubgroupLattice.lean
python3 spec/check_port.py --all      # record the before/after totals
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupLattice
```

plus `#print axioms` on the four headlines (`[propext, Classical.choice, Quot.sound]`), an `rg`
sweep for `sorry` / `admit` / a top-level `axiom` / `native_decide` / a bare `import Mathlib` / a
`maxHeartbeats` override, `git status` showing only the one new file, and **0 warnings**.

## 6. Report shape

Path, lines, public/private counts, checker verdict, build jobs/time, axioms; the `--all`
before/after and the delta against the expected +43; every drift site fixed (file, line, old →
new); **the four targeted import lists**; what happened with `det_eq` and `Gamma_le_Gamma1`
(imported or transcribed, and why); anything unexpected.

## 7. Hub prohibition and stop conditions

No subagent edits an existing module — **in particular not `EisensteinChiNegThree.lean` and not
`CongruenceSubgroupOrder.lean`** — appends to `spec/old_check_stmts.py`, or touches
`spec/decl_markers.tsv`. If a promotion or a marker entry seems required, **stop and report** with
the declaration and the `build_ladder.py --edit` price. Stop and report if a pin statement cannot be
reproduced verbatim, or if a proof exceeds the 200,000 heartbeat cap.

## 8. The Γ₀(3) node — a lift, and it landed 2026-10-20

**Status: landed.** The four steps below were done by the manager in one change, as
`NumberTheory/ModularForms/Gamma0Three.lean` (40 statement-checked declarations, the engine public with
the pin's `@[scoped simp]` / `scoped instance` restored, plus the headline
`CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three`); the host imports it and its private copy is
gone. The same change lifted the host's other transplanted silo (ν₃) into
`ModularCurve/Numerics/NuThree.lean` and made two of the host's own headlines public; checker
**3,654 → 3,718 ok / 143 → 146 modules**, and the `CongruenceSubgroup.` demand row is empty. Record:
[../../../logs/phantom-landings.md](../../../logs/phantom-landings.md). The dependent wave (51 modules)
is owed and unbuilt — [build-time-issues.md](../../../logs/build-time-issues.md) §3b. The rest of this
section is the diagnosis as it was written.

`CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three` ("`Γ₀(3)` is generated by `T`, `U = !![1,0;
-3,1]` and `-1`") is **not** 242 lines of new mathematics. Its pin file has two blocks:

* `A2Gamma0Three` (5 declarations: `U₃`, `gens`, `gens_subset_gamma0_three`,
  `closure_T_U_neg_one_eq`, `mem_closure_gens`) — new;
* `Gamma0Three` (~35 declarations: the Schreier-generator / transversal engine, ending in
  `closure_schreierGens : Subgroup.closure schreierGens = Gamma0 3`) — **already in the port**,
  byte-identical, as the private `FLT.FLT.AnalyticCore.Gamma0Three` block of
  `FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean` (two blocks, lines 899–1040 and
  1064–1108, ~187 lines).

That private copy *is* the port's home for this engine, and it is in the wrong module: the subject
is congruence-subgroup group theory, the host is an Eisenstein-series module. The landing is
therefore a **lift + dedup**, the manager's own work (homing note §8.1's "touch ⇒ rectify", playbook
§4b–c):

1. move the `Gamma0Three` block out of `EisensteinChiNegThree.lean` into a public congruence-subgroup
   home (the same directory as §2's module, e.g. `…/Gamma0Three.lean`), keeping last names;
2. delete the private copy and import the new module from `EisensteinChiNegThree.lean`;
3. add `A2Gamma0Three` + the headline on top;
4. re-run the checker on both sides and the dependent wave.

**Measured price** (`build_ladder.py --edit FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean`):
dependent cascade **51 modules / 30,597 lines, ≈413 s to re-elaborate**, so tier 2 is a 17-module
`lake build` with a 300 s bound and tier 3 a whole-tree build — i.e. a wave that exceeds the
column's per-call 2-minute rule and needs the user's explicit exception. Do **not** start it inside
this dispatch; the four nodes above do not touch that module. Recorded in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md).
