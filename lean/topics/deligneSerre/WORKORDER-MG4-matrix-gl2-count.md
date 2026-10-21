# WORKORDER-MG4 — the last `Matrix.` row: the Deligne–Serre Prop. 7.2 bound and its Serre-image premise

**Status: landed 2026-10-20.** Split execution: the manager landed the definition and statement
layer (the two skeletons, every statement verbatim, the eight definitions complete, 48 `sorry`s), one
coding subagent the proof bodies. Measured on landing: **407 + 1,263 lines, 53 statement-checked
declarations (13 + 40), 0 mismatch / 0 missing / 0 own / 0 kw**, both modules rebuilt from scratch
(5.9–6.3 s / 8.9–10 s), axioms `[propext, Classical.choice, Quot.sound]`, `check_port --all` **3,539
ok over 135 modules**. Record: [../../logs/matrix-gl2-count.md](../../logs/matrix-gl2-count.md). One set, **two modules, 1,632 raw `S_`
lines → 1,611 net new, 53 wired**, 0 substitutions, no host edits, nothing promoted. The premise is
landed first, the row on top of it. Pricing and the rest of the family:
[TOPIC-matrix-family-in-cone.md](TOPIC-matrix-family-in-cone.md) § "Set MG4" (the same set is called
MG3 in the older rows); this order is the "MG4" of its recommendation, written after a full read of
both pin files. It was deferred once on 2026-10-20 as a full dispatch; the deferral reason (a full
dispatch, two subjects) is why the work is two modules and two review gates rather than one, and
this order is what a later session picks up.

## 1. Scope

| # | node | pin `S_` lines | the mathematics |
|---:|---|---:|---|
| 1 | `ModularCurve.SerreImage.contains_SL2` | 390 | an irreducible subgroup of `GL₂(𝔽_p)` (no stable line) that contains a nontrivial unipotent contains `SL₂(𝔽_p)` — Serre's generation argument |
| 2 | `Matrix.GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le` | 1,242 | Deligne–Serre Prop. 7.2: a semisimple subgroup of `GL₂(𝔽_ℓ)` in which a `1-η` fraction of the elements realises at most `M` characteristic polynomials has order bounded by `A(η, M)`, uniformly in `ℓ` |

Row 2 cites row 1 (its only citation: `explore.py` reads `cites 1`, and the pin `S_` file imports
`Theorems/Thm_ModularCurve_SerreImage_contains_SL2.lean`), and row 1's two premises are already in
the port, so the pair is one story with one definition gate-free premise. Row 2 is a `Matrix.` row —
the last one in the D-S demand — and its proof is the largest single block of the `Matrix.` family:
three developments (`KleinFixedPointCount`, `DicksonPrimeToCharacteristic`, `DeligneSerre72`) plus
an explicit witness `A = (4M+1)^4 + 240M + ⌈8M²/(1-2η)⌉₊`.

**Not this set:** the four `SpecialLinearGroup` free-group rows (landed 2026-10-20 as the
free-group family); anything under `FLTForHuman/Analysis/MatrixGroup/` or `LinearAlgebra/Dual/`
(MG1); the `ModularCurve.SerreImage` *definition* — the pin's `SerreImage` is a namespace, not a
structure, and no more of it is ported than the two declarations here.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§0.2–§5; wire: the per-module protocol — a `spec-pin:` header, `spec/check_port.py`, no in-source
per-declaration marker.

## 2. Measurement

From `port_advise.py --target` → `port_plan.py` (the pricing note's run), cross-checked against the
statement corpus (`tmp/flt-statements/statements.tsv`, the same parser the checker uses):

| quantity | row 1 | row 2 | pair |
|---|---:|---:|---:|
| raw `S_` lines | 390 | 1,242 | 1,632 |
| declarations in the pin `S_` file | 14 | 43 | 57 |
| … of which `private` | 0 | 3 (`main` × 3) | 3 |
| … of which the pin's `solution` (not ported) | 1 | 1 | 2 |
| **silo publics to transcribe** | **12 helpers + the theorem** | **39** | **51** |
| **wired in the port** (the above, plus the headline stated once) | **13** | **40** | **53** |
| already in the port | 0 | 0 | 0 |
| substitutions | 0 | 0 | 0 |
| **net new math lines** | **369** | **1,222** | **1,611** |

The pricing note reads row 2 as "42 declarations, 38 publics"; the corpus reads 43 and 39 — one
declaration more, the pair total (53) unchanged. The difference is recorded here so a later run
does not re-price it.

**No definition gate.** Row 1's only non-mathlib imports are the two already-ported modules below;
row 2's are those two plus `Def_Deformations_MatrixRepresentation`. The two mathlib objects the
statements name — `Matrix.ProjGenLinGroup` and `IsSemisimpleRepresentation` — are mathlib's own
(`Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Projective.lean`,
`Mathlib/RepresentationTheory/Semisimple.lean`); the one port definition is
`Deformation.matrixRepresentation`, homed in `FLTForHuman/GaloisRep/Defs/MatrixRepresentation.lean`
(the pin's 23-line module, verbatim), so nothing is homed, promoted or registered by this set.

**Ported premises** (verify the exact names before writing the imports):

* `ModularCurve.upperElem`, `lowerElem`, `elemSet`, `upperElem_pow`, `lowerElem_pow` —
  `FLTForHuman/ModularCurve/Defs/SL2Elementary.lean` (pin `Def_ModularCurve_SL2Elementary`).
* `ModularCurve.closure_elemSet_eq_top` — `FLTForHuman/ModularCurve/X1/Structure.lean` (pin
  `Thm_ModularCurve_closure_elemSet_eq_top`).
* `Deformation.matrixRepresentation` — `FLTForHuman/GaloisRep/Defs/MatrixRepresentation.lean` (pin
  `Def_Deformations_MatrixRepresentation`).

## 3. Deliverables — two modules, in this order

| # | module | namespace | public (silo) | wired |
|---:|---|---|---:|---:|
| 1 | `FLTForHuman/ModularCurve/SerreImage/ContainsSL2.lean` | `ModularCurve.SerreImage` for the theorem and `conj_unipotent`; the pin's `ModularCurve.` layering for the section helpers | 12 | 13 |
| 2 | `FLTForHuman/ModularCurve/SerreImage/SemisimpleOrderBound.lean` | `Matrix.GeneralLinearGroup` (headline); the pin's `KleinFixedPointCount` / `DicksonPrimeToCharacteristic` / `DeligneSerre72` block namespaces verbatim | 39 | 40 |

`wired` = the silo publics plus the headline stated once; the headline is the wrapper's statement,
not a second copy of the `S_` file's theorem.

**The homing decision, stated.** Both rows live in `ModularCurve/SerreImage/`, as one theory
directory: the D-S route's *Serre image* step (row 1) and the order bound that consumes it (row 2).
The alternative — row 2 in `LinearAlgebra/Matrix/GeneralLinearGroup/`, mirroring mathlib's own
directory — was rejected on two counts. First the dependencies: row 2's proof uses row 1 (the
Serre-image theorem) and its statement names `Deformation.matrixRepresentation`, so a home in the
library area would make a `LinearAlgebra/Matrix` module import a `ModularCurve` one — the dependency
inversion this project's homing standard rules out, and the port's `LinearAlgebra/Matrix/` modules
today import nothing from the port at all. Second the standard's rule 1: "a theory that depends on a
*new* theory from another area stays with that theory", and the Serre-image generation theorem is
that theory. The file name and the **namespace** stay with the object (`Matrix.GeneralLinearGroup`
for the headline, the pin's block namespaces for the helpers): path = subject, namespace = object,
the standard's two independent axes. If the port ever promotes the two general theorems to the
mathlib area (moving `contains_SL2` and the `Deformation` def with them), row 2 follows — that is a
separate re-homing, not this order.

**Imports (targeted, never `import Mathlib`).**

* Row 1: `FLTForHuman.ModularCurve.Defs.SL2Elementary`,
  `FLTForHuman.ModularCurve.X1.Structure` (the `closure_elemSet_eq_top` module; it already imports
  `SL2Elementary`), `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`,
  `Mathlib.FieldTheory.Finite.Basic`, `Mathlib.Tactic.NoncommRing`, `Mathlib.Tactic.Group`.
  Keep the pin's `open Matrix MatrixGroups Subgroup`, `open scoped MatrixGroups`, and
  `set_option autoImplicit false`.
* Row 2: `FLTForHuman.ModularCurve.SerreImage.ContainsSL2`,
  `FLTForHuman.GaloisRep.Defs.MatrixRepresentation`,
  `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective` (for `ProjGenLinGroup`),
  `Mathlib.RepresentationTheory.Semisimple` (for `IsSemisimpleRepresentation`),
  `Mathlib.FieldTheory.Finite.Basic`, `Mathlib.LinearAlgebra.Projectivization.Action` (the
  `PL`/`Projectivization` block), `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`, and the tactic
  modules the proof names (`omega`, `noncomm_ring`, `group`, `push_cast`, `linarith`, `ring`).
  Keep `open Matrix MulAction Polynomial`, `open scoped MatrixGroups`, `set_option autoImplicit
  false`.

Rules that apply to both:

* **Drop only the pin's `namespace P2MW.S_<stem>` bookkeeping prefix**, and keep the pin's inner
  namespaces exactly (`ModularCurve`, `ModularCurve.SerreImage`; `KleinFixedPointCount`,
  `DicksonPrimeToCharacteristic`, `DeligneSerre72`). The blocks' statements mention their siblings
  by short name; the content hash and the statement text stay the pin's only while the layering
  does. Do not "improve" the namespaces — folding the three block namespaces under the object (and
  renaming `DeligneSerre72`, a citation label) is a recorded follow-up, not this order.
* **Header:** a leading `/- … -/` block with the subject, the pin file and its line count, what it
  assumes, and then, **the `Theorems/` wrapper line first**:
  ```lean
  spec-pin: Theorems/Thm_<stem>.lean
  spec-pin: P2M/Sol/S_<stem>.lean
  ```
  (`stem` = the node's name with `.` → `_`). No reference to notes or records in the header: it
  states the mathematics and the pin, nothing else.
* **The headline is the wrapper's statement, verbatim** — its text, not the `S_` file's.
* **`solution` is not ported** (both files have one): state the headline once, at the wrapper's
  name, with the pin's proof body.
* **The three `private theorem _root_.<Block>.main`** in row 2 become `private theorem main` inside
  their own namespace, with the `_root_` dropped (it is redundant there and poisons the corpus's
  full-name key — see the rehoming note §8.7). Nothing else about the three mains changes; they are
  the proof-bearing privates of their blocks.
* **The two `local notation`s** (`𝕄` in row 1's `SerreImage` block) are kept; a `local notation` is
  file-scoped and invisible to the checker.

## 4. Source

Pinned `aa2d8b3` (`anthropics/fermats-last-theorem`, Lean `v4.33.1`; port at mathlib `v4.34.0`).

**Row 1** — wrapper `Theorems/Thm_ModularCurve_SerreImage_contains_SL2.lean`; proof
`P2M/Sol/S_ModularCurve_SerreImage_contains_SL2.lean` (390 lines):

| block | lines | declarations |
|---|---|---|
| `section Generation` (in `namespace ModularCurve`) | 18–89 | `exists_natCast_mul_eq`, `mem_range_toGL_of_det_eq_one`, `range_toGL_le_of_conj_elem` |
| `section Unipotent` | 91–224 | `funext_fin_two`, `mulVec_e0`, `mulVec_e1`, `exists_fixed_vec`, `eq_one_of_fixes_two`, `exists_smul_eq_of_cross_eq_zero`, `eq_upperElem_of_fixes_e0`, `eq_lowerElem_of_fixes_e1` |
| `namespace SerreImage` | 226–379 | `conj_unipotent`, `contains_SL2` |
| `solution` | 384–390 | not ported |

**Row 2** — wrapper `Theorems/Thm_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le.lean`;
proof `P2M/Sol/S_Matrix_GeneralLinearGroup_exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le.lean`
(1,242 lines):

| block | lines | content |
|---|---|---|
| `KleinFixedPointCount` | 12–298 | `Omega`, the arithmetic core (`core2`, `core`, `arith3`), `finite_Omega`, `natCard_fixedBy_Omega`, the pair lemmas, `main` (private, 173) |
| `DicksonPrimeToCharacteristic` | 300–707 | `V`/`PL`, the eigenvector/eigenvalue lemmas, `exists_fixedBy_eq_pair`, the reduction `ι`, the center lemmas, `main` (private, 576) — the `ℓ ∤ |G|` case |
| `DeligneSerre72` | 709–1231 | `LinAlg` helpers, `sq_sub_one_eq_zero_of_orderOf`, `no_stable_line`, the explicit coset cells, `tau`, `card_filter_charpoly_le`, `caseA` (the `ℓ ∣ |G|` case), `caseB1`/`caseB2` (the two Dickson branches), `main` (private, 1208) |
| `solution` | 1233–1242 | not ported |

**Statements (the wrapper's text; do not re-spell).** Row 1:

```lean
theorem ModularCurve.SerreImage.contains_SL2 {p : ℕ} [Fact p.Prime]
    (H : Subgroup (GL (Fin 2) (ZMod p)))
    (hirr : ∀ v : Fin 2 → ZMod p, v ≠ 0 → ∃ g ∈ H, ∀ c : ZMod p,
      ((g : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).mulVec v ≠ c • v)
    (hunip : ∃ u ∈ H, ((u : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) ^ 2 = 0 ∧ u ≠ 1) :
    (Matrix.SpecialLinearGroup.toGL (n := Fin 2) (R := ZMod p)).range ≤ H
```

and row 2's statement is the wrapper's `Matrix.GeneralLinearGroup.exists_natCard_le_…` (the `∃ A :
ℕ` over `ℓ`, `G`, `H`); copy it from the wrapper, not from the `S_` file.

## 5. Route, drift and risk

* **`p2m_*` is dropped.** `p2m_export`/`p2m_open`/`p2m_exact_reverting`/`p2m_reactivate` lines are
  the pin's macros; the wrappers' proofs become the plain `exact`/term. Row 2's
  `attribute [-simp] ModularCurve.upperElem_zero …` is also dropped: the row-2 proof never mentions
  `upperElem`/`lowerElem` (checked: zero occurrences in the 1,242 lines), so the attribute is the
  pin's global simp-set workaround for the wrapper macro, not part of the mathematics.
* **No definition gate, no promotion, no registration.** If a helper turns out to be needed
  elsewhere, stop and report — do not promote it on your own.
* **Drift candidates, in the order they will bite** (pin at `v4.33.1`, port at `v4.34.0`): the
  `Matrix (Fin 2) (Fin 2) F` entry computations (`Matrix.eta_fin_two`, `Matrix.one_fin_two`,
  `Matrix.mulVec`, `dotProduct`), the `GL`/`SL` coercion and `Matrix.SpecialLinearGroup.toGL` API,
  `ZMod` surjectivity and inversion (`ZMod.natCast_zmod_surjective`, `ZMod.inv_mul_of_unit`,
  `ZMod.card`), `Matrix.ProjGenLinGroup` and its `mk` hom, `Projectivization`/`PL`,
  `SubMulAction`, `MulAction.fixedBy` and the orbit-counting equivalences,
  `Matrix.exists_mulVec_eq_zero_iff`, `Polynomial.isRoot`/`charpoly` coefficient API,
  `AlgebraicClosure`/`CharP`/`IsAlgClosed`, the ceiling `⌈⌉₊` notation, and `Nat.card` vs
  `Fintype.card` bridging. Each fix is the pin's own term with the minimal rename, recorded by
  site; no `set_option maxHeartbeats`, no weakened statement.
* **Size risk.** Row 2's `caseA` (250 lines), `caseB2` (105) and `DicksonPrimeToCharacteristic.main`
  (129) are the heavy elaboration sites; the `omega` arithmetic (`core2`, `core`, `arith3`) is
  cheap. The instance-heavy sites are `DicksonPrimeToCharacteristic.main` (the `PL` action and the
  permutation representation of `G`) and `caseB2`; if a module exceeds ~120 s elaboration or a
  per-file build exceeds ~300 s, report it — do not work around it. The edit loop's low cap is the
  detector.
* **Order matters.** Land and check row 1 first (it is the dependency and the smaller module), then
  row 2. Row 1 is also the natural place to settle the `GL`/`SL`/`ZMod` API drift, so row 2 starts
  from a known-green base.

## 6. Build discipline (verbatim)

```
tier 0  edit loop    timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>
tier 1  module done  flock .lake/flt_build.lock timeout 300 lake build <module>
tier 2  wave         none — no existing module is edited
tier 3  milestone    no whole-tree build without the user's permission
```

Report the wall time of each edit loop and each `lake build` (jobs + seconds).

## 7. Verification (record the numbers on the tree you leave)

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/SerreImage/ContainsSL2.lean                 # 13 ok
python3 spec/check_port.py --force FLTForHuman/ModularCurve/SerreImage/SemisimpleOrderBound.lean  # 40 ok
python3 spec/check_port.py --all   # expect 3486 + 53 = 3539 ok, 0 mismatch, 0 missing, 11 own, 0 kw, 135 modules
```

plus `#print axioms` on the two headlines (`[propext, Classical.choice, Quot.sound]`), an `rg` sweep
of both modules for `sorry`, `admit`, a top-level `axiom`, `native_decide`, a bare `import Mathlib`
line, a `maxHeartbeats` override, and any reference to a note or a record in the header;
`git status` showing only the two new files; and **0 warnings** from every build. If a checker count
differs from 13 / 40, report the declaration it names rather than adjusting the number.

## 8. Report shape

Per module: path, lines, public/private counts, checker verdict, build jobs/time, axioms. Then the
pair totals vs the expected +53 and the `--all` before/after; every drift site fixed (block and
line, pin text → port text); the import set chosen for each `import Mathlib` replacement; the
answer to the homing question (was the cross-area import needed as stated, and did the reviewer's
alternative — row 2 under `ModularCurve/SerreImage/` — stay unused); anything unexpected.
Stop-and-report items separately.

## 9. Hub prohibition and stop conditions

No subagent edits an existing module, appends to `spec/old_check_stmts.py`, or touches
`spec/decl_markers.tsv`. The new `ModularCurve.SerreImage` and `Matrix.GeneralLinearGroup` namespaces
are declared in the new modules; nothing is registered.

Stop and report if: a pin statement cannot be reproduced verbatim (a `MISMATCH` you cannot fix by
respelling the binder as the pin wrote it); a proof needs a declaration the port does not have
(a definition gate this order missed, or a helper another theory must state); a proof exceeds the
200,000-heartbeat cap after the §3.5 probe ladder (statement vs proof, then isolate, then shrink);
or a build exceeds the time bounds above.
