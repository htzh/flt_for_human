# WORKORDER-FG1 — the `q`-expansion trio and the free-group family

**Dispatched 2026-10-20, one coding agent, three modules.** The set is the two ready cuts of
the six-family audit (the `UpperHalfPlane` leaf family and the free-group family). It is
**13 nodes / 4,342 pin lines / ≈3,641 net new**, every node `needed`, every gate-free (one
inert import), every subject mathlib-shaped. It closes the four `Matrix.SpecialLinearGroup`
rows and takes the `Matrix.` namespace's demand to zero except set MG3.

## 1. Scope

Port, whole (§2.3), the three `UpperHalfPlane.qExpansion_*` nodes (set A) and the ten nodes of
the free-group family (set B):

**Set A — one module.** `UpperHalfPlane.qExpansion_coeff_eq_zero_of_isBigO_exp_neg` (88 pin
lines), `UpperHalfPlane.qExpansion_coeff_mul_width` (91), `UpperHalfPlane.qExpansion_coeff_sum_vAdd_eq_mul_coeff`
(202). All three `S_` files import `Mathlib` + `P2M.Util` only: **no definition gate**. The
second and third share a `FnWrap` structure (10 lines) — port it once. Subject: coefficient
transformation and decay lemmas for mathlib's own `UpperHalfPlane.qExpansion`; mathlib's
`Mathlib/NumberTheory/ModularForms/QExpansion.lean` has the definitions but none of the three
lemmas (recorded negative: `qExpansion_coeff_mul_width`, `vAdd`, `IsBigO` decay absent).

**Set B — two modules.** The free-group family of
[TOPIC-ds-leaf-families.md](TOPIC-ds-leaf-families.md) §3: the five leaf premises
(`Subgroup.card_orbitRelQuotient_mul_card_eq_index` 121,
`SimpleGraph.exists_walkConnected_transversal_of_preconnected` 156,
`Monoid.CoprodI.isTree_cosetGraph` 391,
`ModularGroup.exists_mulEquiv_freeProduct_quotient_center` 519,
`Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero` 543), the
engine `Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank` (1,545), and the four
`Matrix.SpecialLinearGroup` headlines (180 + 194 + 157 + 155). `needed` for the six non-Matrix
nodes is 1 each; the headlines need 3/6/7 nodes, all inside the family. **No external premise
is missing.**

**Not this topic.** The fourth `UpperHalfPlane` row
(`sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU`) is out on the shape test (FLT's
Hecke/Fricke layer). Nothing of the `Matrix`-namespace remainder (set MG3, the four
`SpecialLinearGroup` free-group rows are **in** here — they are the four headlines). No
existing module is edited.

## 2. Source

Pin `~/proj/fermats-last-theorem` at `aa2d8b3` (Lean `v4.33.1`); port at mathlib `v4.34.0`.
For each node `<qual>`, the `S_` file is `P2M/Sol/S_<qual with dots → underscores>.lean` and
the wrapper is `Theorems/Thm_<same stem>.lean`. **The wrapper's statement is the authority;
the `S_` file's `solution` is the same statement.** The statement corpus is
`tmp/flt-statements/statements.tsv` (repo root; columns `path line end kind flags name nhash
signature`).

Wiring: each module's leading `/- … -/` block carries one `spec-pin:` line per pin file, e.g.

    spec-pin: P2M/Sol/S_UpperHalfPlane_qExpansion_coeff_mul_width.lean
    spec-pin: Theorems/Thm_UpperHalfPlane_qExpansion_coeff_mul_width.lean

No `-- pin:` comments in Lean source. Header prose in `/- … -/` only (a `--` line mis-aligns
the checker's namespace tracker).

## 3. Deliverable

**Revised 2026-10-20 (manager re-home, mid-set):** set B is not one engine module. Each of the
six engine nodes is its own mathlib subject, so each gets the module that owns its subject and
the seven headline homes import their preludes from there. The shipped layout is:

| # | module | pin node(s) | imports |
|---|--------|-------------|---------|
| A | `lean/FLTForHuman/NumberTheory/ModularForms/QExpansionCoeff.lean` | the `UpperHalfPlane.qExpansion_*` trio | mathlib |
| 1 | `lean/FLTForHuman/Combinatorics/SimpleGraph/Transversal.lean` | `SimpleGraph.exists_walkConnected_transversal_of_preconnected` + the `SimpleGraph.GraphTransversal` prelude (including the 11 graph declarations moved from the engine) | mathlib |
| 2 | `lean/FLTForHuman/GroupTheory/FreeDoubleCoset.lean` | `Subgroup.card_orbitRelQuotient_mul_card_eq_index` + `GroupTheory.FreeDoubleCoset` block | mathlib |
| 3 | `lean/FLTForHuman/GroupTheory/BassSerre/CosetGraph.lean` | `Monoid.CoprodI.isTree_cosetGraph` + Bass–Serre prelude | mathlib |
| 4 | `lean/FLTForHuman/GroupTheory/ModularGroup/FreeProduct.lean` | `ModularGroup.exists_mulEquiv_freeProduct_quotient_center` + ping-pong prelude (incl. `mem_center_iff_eq`) | mathlib + `PeterssonCoset` (`det_entries`) |
| 5 | `lean/FLTForHuman/GroupTheory/BassSerre/MinimalPeriod.lean` | `Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero` + prelude | mathlib |
| 6 | `lean/FLTForHuman/GroupTheory/FreeGroup/KuroshRank.lean` | the Kurosh engine | 1 + 2 + 3 |
| 7 | `lean/FLTForHuman/GroupTheory/FreeGroup/SpecialLinearGroupGenerators.lean` | the four `Matrix.SpecialLinearGroup` headlines — the user-facing API module over 6 (kept for discovery, not for the checker) | 2 + 4 + 6 |

Dedup homes: the GraphTransversal prelude in 1, the double-coset block in 2, the Bass–Serre
prelude in 3, `mem_center_iff_eq` in 4, the `Matrix` prelude in 7. Measured: 4,342 pin lines →
~3,730 module-body lines in eight modules (the user-facing API module and the 11-declaration move to the graph module came after the first table; 496 pin lines not carried; `port_advise` estimated 513 removable).

All declarations public except genuinely local helpers; no module `set_option maxHeartbeats`;
`set_option autoImplicit false`; no `import Mathlib` in a library module.

**Dedup is owed.** `python3 ../tools/deps/port_advise.py --nodes '<the ten qual names>' --no-drags`
from `tools/deps` re-reads **37 names proved in ≥2 target files, 513 removable lines**
(`mem_center_iff_eq` ×5/72, `finrank_addMonoidHom` ×2/49, `exists_isConnectedTransversal`
×2/40, `exists_gens` ×2/34, `fromRel_eq_graph`, `insert_of_adj`, `exists_adj_of_walk`,
`isTree_of_isAcyclic`, `isAcyclic_two`, `smul_mk`, `adj_base_iff`, `closure_range_basis`,
`eq_one_of_mem_range_of_mem_range`, `eq_of_mem_orbit_insert`, `IsConnectedTransversal`, …).
Port each once, into the module that owns the subject. Two `generalise` rows share a conclusion
but not binders (`ConjTrivial` vs `Kurosh.ConjTrivial`, `card_orbitRelQuotient_mul_card'`):
take the wrapper's binders, once.

**Substitutions — only two are real.**
- Import `CuspForm.PeterssonCoset.det_entries` (`ModularForms/Analytic/PeterssonCoset.lean`)
  for the pin's `det_entries` (5 lines).
- `mul_entry` is **private** in `ModularForms/ModularGroup.lean`, a legacy `PORT_FILES` module;
  do **not** edit or hand it over — restate the 5-line matrix-entry computation locally and
  record the duplication.
- **Decline** the parser's type-only `def` matches: `IrrationalPt ↔ CuspForm.heckeBaseAlgebra`,
  `Vertex ↔ CohCarrier.H1`, `FreeActionRankFormula ↔ PeriodPair.DiscriminantNeZero`. They are
  different objects over the same product type; importing them would be wrong.

**The one pin `Definitions/` import is inert.** `Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero`
imports `Def_Compat_Mathlib430`; 0 of its 44 declarations occur in the file (the single
`coe_mul` is mathlib's `Subgroup.coe_mul`). If elaboration wants the `AddAut` group instance,
the port has block D at `FLTForHuman/Algebra/AddAut/Compat.lean` — import it explicitly rather
than the pin module. Do not home the pin compat module.

## 4. Route and risk

Mathlib map: `Monoid.CoprodI`, `FreeGroupBasis` (with `FreeGroupBasis.coprodI`),
`SimpleGraph.fromRel`/`IsTree`, `Subgroup.zpowers`/`index`, `MulAction.orbitRel.Quotient`,
`Matrix.SpecialLinearGroup`, `ModularGroup.S`/`T`, `UpperHalfPlane.qExpansion`/`atImInfty`.
The 13 `CoprodI`/`FreeGroupBasis` identifiers the family uses all exist in v4.34.0.

Stop-early risks (raise a **short** blocker message at first belief; keep working on the
independent module):
- `Monoid.CoprodI` API drift between v4.33.1 and v4.34.0 (renamed `Word`/`lift` lemmas);
- `FreeGroupBasis` / `Subgroup.index` instance-shape mismatches in the four headlines;
- `UpperHalfPlane.qExpansion` API drift in the trio (the pin is one mathlib version older);
- an `AddAut` typeclass need (see above);
- a statement that will not elaborate at `-DmaxHeartbeats=200000` — diagnose
  (instance inference), do not raise the cap.

Never weaken a statement, never edit an existing module, never work around a hub defect.

## 5. Build discipline

Edit loop: `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`
(no `.olean`, no cascade; the low cap is the inference detector). Per finished file:
`timeout 90 lake build FLTForHuman.<path>` serialized with `flock` (e.g.
`flock /tmp/flt.lock timeout 90 lake build …`). **Never a bare whole-tree `lake build`.**
Each tool call must finish within 2 minutes; no loop to evade the bound. The module's
`lake build` needs 0 warnings.

## 6. Verification

- `cd lean && python3 spec/check_port.py FLTForHuman/...` per module: **0 mismatch / 0 missing**,
  0 `own`, expected `ok` ≈ 25 (set A) + 330–360 (set B).
- `lake build` per module, 0 warnings; `grep -c sorry` 0.
- `#print axioms` on all 13 headlines (a `tmp/` scratch file): `[propext, Classical.choice,
  Quot.sound]`.
- A short record `lean/logs/qexp-and-freegroup.md`: per-module lines, declarations, build job
  count and wall time, checker delta, axiom sets, the dedup table actually achieved, every
  friction hit (append to `lean/logs/frictions.md` while it happens).
- Do not edit `topics/PORTING-DeligneSerre.md`, `spec/old_check_stmts.py`,
  `spec/decl_markers.tsv` (unless a marker is genuinely needed — report it), or any legacy
  module.
- No `git commit` / `git push`.

## 8. Addendum (2026-10-20) — the free-group set is re-homed into mathlib-shaped modules

The first cut put the six engine nodes of set B into one `GroupTheory/FreeGroup/KuroshRank.lean`
(3,079 lines). That is the wrong home: the set carries six distinct mathlib subjects, and the port
homes mathlib-shaped work where mathlib would. Set A is unaffected — its trio is one subject and
stays one module at `NumberTheory/ModularForms/QExpansionCoeff.lean`.

The revised deliverable (the engine file keeps its path but shrinks to its own node):

| module | node(s) | imports |
|---|---|---|
| `Combinatorics/SimpleGraph/Transversal.lean` | `SimpleGraph.exists_walkConnected_transversal_of_preconnected` + `GraphTransversal` prelude | — |
| `GroupTheory/FreeDoubleCoset.lean` | `Subgroup.card_orbitRelQuotient_mul_card_eq_index` + `GroupTheory.FreeDoubleCoset` block | — |
| `GroupTheory/BassSerre/CosetGraph.lean` | `Monoid.CoprodI.isTree_cosetGraph` + `BassSerre` prelude | — |
| `GroupTheory/ModularGroup/FreeProduct.lean` | `ModularGroup.exists_mulEquiv_freeProduct_quotient_center` + ping-pong prelude | — |
| `GroupTheory/BassSerre/MinimalPeriod.lean` | `Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero` + prelude | — |
| `GroupTheory/FreeGroup/KuroshRank.lean` | `Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank` | the three leaf modules |
| `GroupTheory/FreeGroup/KuroshRank.lean` | the four `Matrix.SpecialLinearGroup` headlines + shared prelude | `FreeDoubleCoset`, `…FreeProduct`, `KuroshRank` |

The dedup moves with the subject: the `GraphTransversal` block lives in module 1, the `BassSerre`
block in module 3, `mem_center_iff_eq` in module 4 (used by 7). Every module keeps its own
`spec-pin:` wire (its `S_` and `Thm`), its own edit loop and its own flock'd build + checker run.
The mathlib-first reading is unchanged: `SimpleGraph`/`CoprodI`/`FreeGroupBasis`/`ModularGroup` are
mathlib vocabulary, and these are supplements in mathlib's own directories.

**Superseded 2026-10-20 by the subject re-homing** (see `logs/qexp-and-freegroup.md` §6): the graph
theorem and the engine's 11 graph declarations live in `Combinatorics/SimpleGraph/Transversal.lean`
(`SimpleGraph.GraphTransversal`); the Bass–Serre pair is under `GroupTheory/BassSerre/`; the
ping-pong equivalence under `GroupTheory/ModularGroup/FreeProduct.lean`; and the four headlines live in the user-facing API module
row 7 (restored after the user-view review: a façade is not needed, a module named for the API is).
