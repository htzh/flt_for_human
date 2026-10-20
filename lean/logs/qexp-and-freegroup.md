# WORKORDER-FG1 — the `q`-expansion trio and the free-group family: port record

Pinned `aa2d8b3` (`~/proj/fermats-last-theorem`, Lean `v4.33.1`), port at mathlib `v4.34.0`.
Set A: `UpperHalfPlane.qExpansion` coefficient trio. Set B: the ten free-group nodes.
Layout was re-homed mid-set by the manager (one module per mathlib subject + the headline
façade); see `topics/deligneSerre/WORKORDER-FG1-qexp-and-freegroup.md` §3.

## 1. Measured table

`lines` = file length (`wc -l`), `body` = lines after the header/import block (the transposed
pin text), `decls` = declarations the checker's parser sees (`named`: non-anonymous),
`lake build` = `flock /tmp/flt.lake.lock lake build FLTForHuman.<path>` (jobs / lake's wall
time), `checker` = `python3 spec/check_port.py <file>` (fresh, `--force`).

| module | pin lines | lines | body | decls (named / priv) | lake build | checker |
|---|---|---|---|---|---|---|
| `NumberTheory/ModularForms/QExpansionCoeff.lean` | 88+91+202 = 381 | 425 | 365 | 20 (19 / 0 + 1 anon) | 3087 jobs / 3.6 s | 19 ok, 0 mismatch, 0 missing, 0 own |
| `Combinatorics/SimpleGraph/Transversal.lean` | 156 + 11 moved | 259 | ~218 | 21 (21 / 1) | 1060 jobs / 1.9 s | **21 ok**, 0/0/0 |
| `GroupTheory/FreeDoubleCoset.lean` | 121 | 162 | 122 | 12 (12 / 0) | 3092 jobs / 4.2 s | 12 ok, 0/0/0 |
| `GroupTheory/BassSerre/CosetGraph.lean` | 391 | 431 | 385 | 51 (49 / 0 + 2 anon) | 3131 jobs / 4.0 s | 49 ok, 0/0/0 |
| `GroupTheory/ModularGroup/FreeProduct.lean` | 519 | 575 | 519 | 71 (69 / 1 + 1 anon) | 3783 jobs / 5.6 s | 68 ok, 0/0/0 |
| `GroupTheory/BassSerre/MinimalPeriod.lean` | 543 | 594 | 543 | 75 (75 / 0) | 3096 jobs / 6.9 s | 75 ok, 0/0/0 |
| `GroupTheory/FreeGroup/KuroshRank.lean` (engine) | 1,545 | 1,241 | ~1,180 | 117 (117 / 2) | 3135 jobs / 9.6 s | **104 ok**, 0/0/0 |
| `GroupTheory/FreeGroup/SpecialLinearGroupGenerators.lean` (user-facing API) | 686 | 548 | 500 | 52 (52 / 0) | 3825 jobs / 6.3 s | **52 ok**, 0/0/0 |
| **total** | **4,342** | **4,152** | **~3,730** | **401** | 8 modules built | **400 ok, 0 mismatch, 0 missing, 0 own, 0 kw** |

Every module: `grep -c sorry` 0, `set_option maxHeartbeats` 0, `import Mathlib` 0,
`set_option autoImplicit false` present, 0 `lake build` warnings (after the deprecation/linter
fixes listed in §4).

## 2. Axioms

`lean/tmp/axioms_fg1.lean` (built with `lake env lean`) prints, for all 13 headlines:

    [propext, Classical.choice, Quot.sound]

The 13: the three `UpperHalfPlane.qExpansion_*`, `Subgroup.card_orbitRelQuotient_mul_card_eq_index`,
`SimpleGraph.exists_walkConnected_transversal_of_preconnected`, `Monoid.CoprodI.isTree_cosetGraph`,
`ModularGroup.exists_mulEquiv_freeProduct_quotient_center`,
`Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero`,
`Monoid.CoprodI.nonempty_freeGroupBasis_fin_kuroshRank`, and the four
`Matrix.SpecialLinearGroup.*` headlines.

## 3. Dedup achieved

`port_advise --nodes '<ten quals>' --no-drags` re-read 37 names proved in ≥2 target files,
513 removable lines. Paid as follows (one copy, in the module that owns the subject; each
consumer imports it):

| prelude | pin copies (lines removed) | home (single copy) |
|---|---|---|
| `GroupTheory.BassSerre.*` — `Vertex`, `Vertex.mk`, `graph`, `mk_eq_mk_iff`, `adj_mk`, `adj_iff_exists`, `adj_one`, `SMul`+`MulAction` instances, `smul_def`, `smul_mk`, `smul_adj`, `smulHom`, `smulHom_apply`, `reachable_smul`, `smul_eq_self_iff`, `mk_of_eq_mk_one`, `reachable_one_one/_of/_`, `connected`, `eq_one_of_mem_range_of_mem_range`, `range_inf_range_eq_bot`, `eq_of_mk_eq_mk`, `adj_base_iff`, `isTree_of_isAcyclic`, `fromRel_eq_graph`, `isTree_two`, `isAcyclic_two` | kurosh `S_:169-388` (231 lines, 37 decls incl. 2 anon) | `GroupTheory/BassSerre/CosetGraph.lean` |
| `GroupTheory.GraphTransversal.*` — `WalkConnected`, `IsConnectedTransversal`, `walkConnected_singleton`, `WalkConnected.insert_of_adj`, `walkConnected_sUnion`, `mem_orbit_symm'`, `eq_of_mem_orbit_sUnion`, `eq_of_mem_orbit_insert`, `exists_adj_of_walk`, `exists_isConnectedTransversal` | kurosh `S_:398-500` (103 lines, 10 decls) | `Combinatorics/SimpleGraph/Transversal.lean` |
| `mem_center_iff_eq` | ×5 / 72 lines (4 façade files + `ModularGroup` file) | `GroupTheory/ModularGroup/FreeProduct.lean`, opened by the façade |
| `finrank_addMonoidHom` ×2/49, `exists_gens` ×2/34, `closure_range_basis` ×2/13, `lift_apply_basis` ×2/5, `toBar` ×2/3, `eq_one_or_eq_neg_of_toBar_eq_one` ×2/10 | 10 façade decls | `GroupTheory/FreeGroup/KuroshRank.lean` |
| `exists_isConnectedTransversal` ×2, `conjTrivial_iff…`, `adj_*`, `smul_*`, … (all included above) | — | — |
| `det_entries` | pin's 5-line copy dropped | substituted by `CuspForm.PeterssonCoset.det_entries` |
| generalise `ConjTrivial` vs `Kurosh.ConjTrivial` | 2 defs → 1 | `GroupTheory/FreeDoubleCoset.lean`; `KuroshRank.lean` keeps a `private abbrev` so the pin's statement text `Kurosh.ConjTrivial` survives |
| generalise `card_orbitRelQuotient_mul_card'` | 2 → 1 | `GroupTheory.FreeDoubleCoset.lean`; `KuroshRank.lean` calls the wrapper's headline (`Subgroup.card_orbitRelQuotient_mul_card_eq_index`, expanded binder) |

Net: 52 declaration copies deleted (49 prelude + 2 generalise + 1 substitution), 4,342 pin lines
→ 3,846 body lines, i.e. **496 pin lines not carried** (the tool's 513 estimate counted the
`det_entries` 5-line substitution and did not know the generalise rows would need a 5-line
alias plus the 3-line matrix-entry restatement).

Declined (parser type-only `def` matches, per the work order): `IrrationalPt ↔ CuspForm.heckeBaseAlgebra`,
`Vertex ↔ CohCarrier.H1`, `FreeActionRankFormula ↔ PeriodPair.DiscriminantNeZero` — different
objects over the same product type; none imported.

## 4. Deviations, decisions, blockers

- **No blocker was raised.** Every pin name matched; the four stop-early risks did not fire.
- **Re-home (manager, mid-set):** the six-node engine became five subject modules plus the
  shrunken `KuroshRank.lean` (see the record's §3 table). This is the shipped layout.
- **`mul_entry`** (private in the legacy `ModularForms/ModularGroup.lean`, a `PORT_FILES`
  module that must not be edited): restated locally in
  `SpecialLinearGroupFreeProduct.lean` at the pin's statement. Recorded duplication, 5 lines.
- **`Def_Compat_Mathlib430`** (the family's only `Definitions/` import, in the
  `MinimalPeriod` node): inert — 0 of its 44 declarations occur in the node — so it is not
  homed and not imported. `FLTForHuman/Algebra/AddAut/Compat.lean` (block D) was **not** needed:
  the node's `AddAut` values use only `AddEquiv`, which `v4.34.0` provides.
- **Scoped instances:** the pin re-activates them with `p2m_reactivate`; the port's equivalents
  are `open IrrationalPt` (which does activate `scoped instance`s — verified) and, for the
  `SMul`/`MulAction` instances on `BassSerre.Vertex`, dropping `scoped` so the consumer module
  sees them.
- **Statement-preserving proof fixes** (v4.34 drift, no statement touched): `beta_reduce` +
  `congrArg Subtype.val` before `Sym2.eq_iff` in `treeRepEquivEdgeSet` (the pin's
  `rw [Subtype.mk.injEq, Sym2.eq_iff]` no longer rewrites a dependent `Subtype`);
  `if_pos`→`ite_eq_left`, `if_neg`→`ite_eq_right`, `Set.mem_diff`→`Set.mem_sdiff`,
  `Set.mem_setOf_eq`→`Set.mem_ofPred_eq`,
  `Set.ncard_diff_add_ncard_of_subset`→`Set.ncard_sdiff_add_ncard_of_subset`; one dead
  `push_cast` dropped. `linter.style.haveILetI false` at module level in the three modules
  where the pin's load-bearing `haveI` fires (same prescription as FR-0025).
- **Set A checker count is 19, not the work order's "≈25"**: the three `S_` files contribute 20
  corpus rows, of which one is an anonymous `scoped instance : FunLike FnWrap ℍ ℂ` (the checker
  skips anonymous rows) — 19 is the complete count. Set B: 381 checker-ok across the seven
  modules vs the "330–360" estimate; the estimate discounted the per-file preludes that the
  homes carry once but the wire still matches.
- **Frictions** (full entries in `logs/frictions.md` FR-0027…FR-0034): the pin's
  `p2m_export`/`p2m_open` scaffolding; the corpus's namespace tracker mis-reading `end A.B`
  (it reports `GroupTheory.GroupTheory.…` and so hides 10 of the 37 duplicates from
  `port_advise`); `statements.tsv end_line` being the *statement* end rather than the
  declaration end (a span-based deletion decapitates `def`s); mathlib module paths that are
  directories now; a partially built mathlib olean tree; and `alias` not accepting a `def`.

## 6. Re-homing (2026-10-20, manager's pass)

The first cut's layout was re-homed by **subject**, with genericity and dependency direction as the
tie-breakers (a theory that is generic and self-contained gets its own subject home; a theory that
depends on a new theory from another area stays with that theory; the pin's namespace is kept when
it already names the subject; a pin `P2MW.S_…` wrapper is scaffolding, not a namespace).

| what | where it is now | namespace |
|---|---|---|
| graph theorem + the 11 graph declarations the engine carried (`orbitRepr`/`transl`/…) | `Combinatorics/SimpleGraph/Transversal.lean` | `SimpleGraph.GraphTransversal` |
| double-coset count | `GroupTheory/FreeDoubleCoset.lean` | `GroupTheory.FreeDoubleCoset` |
| coset graph | `GroupTheory/BassSerre/CosetGraph.lean` | `GroupTheory.BassSerre` |
| edge-chain engine | `GroupTheory/BassSerre/MinimalPeriod.lean` | `GroupTheory.BassSerre` (merged) |
| ping-pong equivalence | `GroupTheory/ModularGroup/FreeProduct.lean` | `ModularGroup.PingPong` |
| Kurosh engine | `GroupTheory/FreeGroup/KuroshRank.lean` | `GroupTheory.Kurosh`, `GroupTheory.BassSerre` |
| the four `Matrix.SpecialLinearGroup` headlines | `GroupTheory/FreeGroup/SpecialLinearGroupGenerators.lean` (user-facing API over the engine) | `Matrix.SpecialLinearGroup.*` |

The four-headline module was first merged into the engine and then **restored as the user-facing API
module**: the *façade* reason (a small listed delta for the frozen checker) is dead — `spec-pin:` +
`check_port` make it unnecessary — but the user's reason survives. A user looking for
`Matrix.SpecialLinearGroup` free-generation results imports a module named for them, not
`KuroshRank`; the module is a discovery decision, and its one same-area import edge is the price. The
engine stays at 104 declarations / 1,241 lines, the API module at 52 / 548.

Verification after the pass: checker on the touched modules — graph 21, FreeDoubleCoset 12,
CosetGraph 49, MinimalPeriod 75, FreeProduct 68, KuroshRank 104, SpecialLinearGroupGenerators 52, QExpansionCoeff 19, plus the
representation set 17 + 1 × 4 — 0 mismatch / 0 missing throughout; `lake build` on each moved
module, 0 warnings.

**Dependency metric** (whole tree, module-level `import FLTForHuman.*` edges): baseline `8cd8e96`
841 modules / 1,954 edges / 439 cross-area; after 842 / **1,955** / **436**. The new
`ModularForms/HeckeFrickeTrace.lean` accounts for the +1 module and +1 edge, so the re-home plus the
API module is **even on edges** and three cross-area edges down. The direction the manager asked
for: dependencies down or even.
