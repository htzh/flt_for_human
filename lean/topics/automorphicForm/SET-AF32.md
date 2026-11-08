# SET-AF32 — the archimedean type lattice and the isotypic cusp submodule

**Status: LANDED 2026-11-07** — one order, one new module, four headlines; §4 is the forecast and
§5 records the landing. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the same
post-AF29 read that cut SET-AF31. It is the **thirty-second** `AutomorphicForm`-serving set.

**4 rows / 1,128 silo / 1,005 net new math lines (`port_plan`) / 68 declaration groups**, of which 34
lines are already in the port. All four rows are on the ready block with **zero unported premises**.

| row | silo | lev | what it says |
|---|---|---:|---|
| `AutomorphicForm.exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates` | 390 | 1/5 | a continuous linear map out of a supremum of type submodules has range the span of its right translates |
| `AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | **2/27** | membership in the isotypic cusp submodule implies the pointwise isotypic predicate |
| `AutomorphicForm.CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 2/4 | the inf-of-sup bound by sup-of-inf for the `τ`-isotypic parts, for continuous data |
| `AutomorphicForm.CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1/1 | conjugating an arch test factor by `c⁻¹` and multiplying by `‖det‖ ^ r` keeps it a test factor |

## 0. The read

The post-AF29 read of SET-AF31 §0 applies verbatim: `needed` **771 / 323,794**, frontier
1,645 / 803,582, ready **64 / 17,622** (36 AF rows / 11,483), leaves 205 / 52,847, `AutomorphicForm`
demand 281 / 123,638.

## 1. Why this cut — leverage, not size

The return column is exhausted at this point (the 136-row gate of SET-AF31 is the last leader), so this
cut is made on the recipe's *other* cheap-leaf signal: **fan-in**. The isotypic-membership row has
**27 project consumers** (leverage 2/27) — the highest in the column's shelf — and its three companions
are the lattice algebra it is stated over (`typeSubmodule`, `archTypeSubmoduleAt`,
`isotypicCuspSubmodule`) plus the character twist the archimedean cut is stable under. That is one
story: *the archimedean type decomposition of the cusp spectrum*, which is what SET-AF23's §4 called
"the machine the `CuspidalConstituent`/isotypic block is written against".

It is **1,005 net** for 1,128 silo, in the recipe's band, with 68 declaration groups — a genuine
transcription set rather than a composition one, and the first such after AF26.

## 2. The price

| figure | value |
|---|---|
| raw `S_` lines | 1,128 |
| declaration lines | 1,039 |
| — duplicate copies | 0 |
| — boilerplate | 89 |
| distinct declaration groups | 68 |
| already in the port (vetted) | 34 |
| **net new math lines** | **1,005** |

2 trusted substitutions, 0 suspect. No definition gate (`gate_scan` over
`Def_AutomorphicForm_IsotypicCuspSpace` and `_FactorizableTestFn`: 0 missing).

## 3. Home

**One new module, `Adelic/IsotypicArchType.lean`**, above `IsotypicCuspSpace` (the predicate and the
`ArchTypeFamily`/`ArchRepAt` vocabulary), `ArchType` (`typeSubmodule`, `archCutSubmodule`),
`ArchDerivCasimirComplex` (the split torus and the circle weights), `FactorizableTestFnArchSmoothLeft`
(`IsArchTestFactor`), `Cusp/Constituent` and `Siegel/Covering`. It is the lattice-algebra role, distinct
from both `IsotypicCuspSpace` (the definitions) and `Cusp/CutWeightDecomposition` (the cut weights).

## 4. Forecast

| figure | before | after |
|---|---|---|
| `needed [F terminal]` | 771 / 323,794 | **767 / 322,789** |
| `needed [literal]` | 783 / 327,259 | **779 / 326,254** |
| frontier F | 1,645 / 803,582 | **1,649 / 804,587** |
| ready block | 64 / 17,622 | **60 / 16,494** (4 rows out; 0 in) |
| leaves block | 205 / 52,847 | **205 / 52,847** |
| `AutomorphicForm` demand | 281 / 123,638 | **277 / 122,633** |
| rows readied | — | see review (the 242 row's 27 consumers each lose a premise) |

## 5. The landing (2026-11-07)

`Adelic/IsotypicArchType.lean` — **1,148 lines / 67 declarations**, one order, one dispatch.

| gate | as dispatched | **after the surface gate** |
|---|---|---|
| `check_port --force` | 4 ok / 0 / 0 | **34 ok / 0 mismatch / 0 missing / 0 own** |
| build (single module, flock) | — | success, 4,077 jobs, 9.5 s |
| axioms (4 headlines) | — | `[propext, Classical.choice, Quot.sound]` each |
| `dedup --within` | — | 67 declarations, 0 clusters / 0 removable |
| `move_dead` | — | 0 declarations / 0 lines |
| consumer `spec/AutomorphicFormSetAF32Consumer.lean` | — | **0 errors / 0 warnings** (166 lines) |

**The surface gate again paid 30 declarations** (4 → 34): the worker had made all 64 helpers `private`,
and this time the pin's visibility is *split* — 20 and 11 public in the 390 and 242 files, 1 public with
7 and 26 private in the 214 and 282 files. The promotion needed no `open` surgery and produced no
`MISMATCH`: the 31 pin-public helpers read `ok` at the pin's names on the first try (the 242 row's
needed a namespace move to `AutomorphicForm.IsotypicSpanForms` and the pin's `abbrev pp` restored).
**33 declarations stay private with a reason each**: 4 in the 214 row and 26 in the 282 row are
pin-private; 2 are port-only extraction helpers (the pin writes those `hLs` blocks inline); and 1 —
`Ws49.K1.finiteDimensional_typeSubmodule_id` — is the pin's `scoped instance`, which the statement corpus
has **no row** for, so keeping it `private instance` is the only way to avoid a permanent `MISSING`
(file-global for TC search, as the pin's `scoped` was).

**The hardest row was 214, and not for the mathematical reason.** The inf/sup exchange is short; the cost
is that the port had already moved compactness of the row-isometry group into a `scoped instance`
(`ArchCompactOrbit.compactSpace_rowIsometrySubgroup₀`), so the pin's
`haveI : CompactSpace … := isCompact_iff_compactSpace.mp …` cannot be transcribed literally (and `open
scoped` would drag in a second scoped instance for free), and the pin's `haveI := hSfd` walls pass
*hypotheses* into instance search — the one thing `have`/`let` differ on at v4.34. Every fix is
proof-local and invisible to the checker, so it had to be got right by hand.

Other carried facts: `ringInverse_of_NZ` (pin 282:49) was **deleted** rather than re-spelled — `move_dead`
proved it dead in the pin too; five new imports, each the port home of a pin import; and the three
continuity helpers of the 214 row are not re-proved because the port has them publicly in
`ArchCompactOrbit`.

## 6. What this set does not do

- **`isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow`** (1,043) — the induced-section/height
  power identity that sits beside this block in the shelf: a different subject (Eisenstein data), and it
  belongs with the Weyl intertwining pair when that unblocks.
- **The Weyl intertwining pair** (1,349 + 1,291) stays blocked on FR-0151's two statement-spelling
  decisions — the largest open subject on the shelf, and the manager pass that would open it.
- **`exists_sum_prod_mul_of_rightTranslatesSpanFinite`** (576, readies 552) is the return column's
  runner-up and remains the cheapest un-cut pair.
- The cusp-constituent cluster (94 nodes / 21,595 silo) and the Siegel/Petersson blocks are unchanged.
