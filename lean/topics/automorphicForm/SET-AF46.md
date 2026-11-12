# SET-AF46 — the residue map's Gauss basis, its rank, and the `L²` comparison (a mechanical set)

**Status: LANDED 2026-11-12** — §0 the cut and the mechanical measurement, §1 the forecast, §2 the orders, §3 the landing record and the re-read. Read off the D–S shelf with
the recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The
forty-sixth set, the direct continuation of AF45, and the column's **second mechanical set** (after AF7):
both modules are *copies of the pin's text*, not scaffolds, so **there is not one `sorry` in the set**.

**4 rows / 2,119 silo / 1,835 net (`port_plan`)**, all four readied by AF45; return **431 silo in two rows**.

| # | row | silo | what it says |
|---|---|---:|---|
| **1** | `RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq` | 1,082 | the residue map has an integral Gauss basis, and every residue has a unique integral representation in it |
| **2** | `RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq` | 848 | under the degree hypothesis the residue span has the same finrank as the `L`-span (the equality form of AF45's inequality) |
| **3** | `RegularProlongation.span_residue_lSpace_le_residueSpan_inf` | 98 | the `L²` span of a residue span sits inside the intersection of the two integral spans |
| **4** | `RegularProlongation.coe_minpoly_adjoin_coeff_mem_integers` | 91 | the `minpoly` of a `pi`-residue has integer coefficients |

## 0. The cut, and why mechanical

AF45 readied all four; they are the shelf's largest ready rows (1,082 and 848), and they are the
constructive culmination of the residue calculus AF44–AF45 built. The pin's files are **1,082 + 848 + 98 +
91 lines in four `S_` files**, and their declarations are heavy — nested label namespaces, `LinearMap`/
`RingHom` structure literals, `letI`-scoped modules, and an 84-instance `attribute [-instance]` shim. A
statement-by-statement scaffold (the AF41–AF45 route) is not the right instrument there: the def bodies
carry the mathematics, and cutting them changes the *implicit binder lists* of the surrounding
declarations (a section variable used only by a body drops out of the signature).

So the manager took the **AF7 route**: copy the pin's text with the tooling translated (`import Mathlib`,
`P2M.Util`, `Definitions/*` and `Theorems/*` lines dropped in favour of the port's modules; `p2m_open`/
`p2m_export`/`attribute [-…]`/`set_option maxHeartbeats`/`noncomputable section` lines dropped; qualified
`end A.B` → bare; the P2MW wrapper replaced by `namespace AlgebraicCurve / namespace RegularProlongation`),
and leave the proofs in place. The measurement:

| module | lines | `sorry` | elaboration errors | `check_port` |
|---|---:|---:|---:|---|
| `AlgebraicCurve/RegularProlongationResidueSpan.lean` | 959 | **0** | **0** | **26 ok / 0 mismatch / 0 missing** |
| `AlgebraicCurve/RegularProlongationGaussBasis.lean` | 1,191 | **0** | **14** | **50 ok / 0 mismatch / 0 missing** |

That is the AF7 finding again, sharper: **the statements are already verified in both modules** (76 `ok`
between them) and one module's proofs already elaborate. What is left is warning cleanup (32 warnings in
the first module: 20 deprecations, 4 `haveILetI`, 5 `unusedSectionVars`, 1 each of `unreachableTactic`,
`unusedSimpArgs`, `unusedTactic`) and **14 drift sites** in the second (a v4.34 rename
`IsLocalRing.map_mkQ_eq_top`, two "unknown constant" premises, four application mismatches, two unsolved
goals, one instance-synthesis failure, and the `end FinGeSol` scoping artefact of FR-0172).

**One pre-existing port defect surfaced and was resolved by the manager** (FR-0175): importing
`FLTForHuman.AlgebraicCurve.GaussProlongation` — needed for
`GaussProlongation.residue_mem_adjoin_residue_of_mem_adjoin_integers` — failed because **both**
`AlgebraicCurve/RegularProlongation.lean` and `AlgebraicCurve/GaussProlongation.lean` declared
`AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers`. The identical statements were one
pin node transcribed twice; the copy in the namespace-owning module was kept, the fully qualified duplicate
in `GaussProlongation.lean` (115 lines with its docstring) deleted with its two redundant `spec-pin:` lines,
and the sibling's own proofs now use the imported copy. Measured: that module elaborates silently, builds
(2,521 jobs), and its checker went **10 → 9 ok / 0 mismatch / 0 missing** — one pin declaration with one
port copy, which is the intended accounting.

## 1. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 716 / 301,921 | **712 / 299,802** |
| frontier F | 1,695 / 822,607 | **1,699 / 824,488** |
| ready rows | 52 / 11,898 | **50 / 10,210** |
| leaves | 187 / 46,259 | 187 / 46,259 |
| `AlgebraicCurve` demand | 46 / 18,888 | **42 / 16,769** |
| rows readied | — | **2 / 431 silo** |

## 2. Orders and gates

`tmp/af46/WORKORDER-AF46A-residue-span.md` (module 1: 0 errors, clear the 32 warnings) and
`tmp/af46/WORKORDER-AF46B-gauss-basis.md` (module 2: fix the 14 drift sites). Both are **drift orders**,
not transcription orders: the statements are frozen and already checker-green, no `sorry` may appear, and
the gate is *silence* + the checker count not moving + the pin's route preserved.

## 3. The landing (2026-11-12)

Two orders, both **drift** orders on complete pin copies; nothing left undone, no `sorry` anywhere.

| order | module | lines | errors → | warnings → | `check_port` | build | axioms |
|---|---|---:|---:|---:|---|---:|---|
| **46A** | `RegularProlongationResidueSpan.lean` | 958 → **966** | 0 → 0 | 32 → **0** | **26 ok / 0 / 0** | 3,409 jobs, 19 s | 2/2 |
| **46B** | `RegularProlongationGaussBasis.lean` | 1,191 → **1,244** | 14 → 0 | 49 → **0** | **50 ok / 0 / 0** | 3,164 jobs, 21 s | 2/2 |
| | | | | | **76 ok, 0 mismatch, 0 missing** | | 4/4 |

**The mechanical measurement is the set's finding.** 2,119 silo of the pin's mathematics landed with
**zero `sorry`** and **zero statement changes**: 28 drift edits in the first module (20 deprecation
renames, 4 `haveILetI`, 5 section-variable consumptions, one unused simp lemma, one no-op `ring`) and 14
in the second (one missing mathlib import, one name-shadowing notation, one scoped-instance open, two
port-home imports, one stray `end`, one `abbrev`→`def` instance-search drift), plus 81 warning cleanups
between them. That is the AF7 strategy confirming itself at a different scale: **the pin's text is closer
to a landing port than a scaffold is**, when the declarations are heavy.

### 3.1 What the drift orders found

1. **A checker blind spot of the first order (FR-0176).** The pin's bare `residue` means
   `IsLocalRing.residue`; in the port's `namespace RegularProlongation` the same token resolves to the
   structure's `residue` field. `check_port` compares statement **text**, so the declaration read `ok`
   while its *meaning* had silently changed — and the "obvious" fix (qualifying the term) turned the
   checker red, because qualification changes the text. The port's answer is a `local notation
   "residue" => IsLocalRing.residue`: the pin's meaning with the pin's text. This is the deepest
   instrument finding of the column: a statement hash cannot see a resolution change.
2. **`abbrev` → `def` instance drift (FR-0177).** In v4.33 `ResidueField` was an `abbrev` and unfolded
   during instance search, so mathlib's `Module (R ⧸ I) (M ⧸ I • ⊤)` fired for it; in v4.34 it is a `def`,
   so it does not. The port opens the file's own scoped instances (`open scoped FinGeSol.Generic`) instead
   of taking up the pin's `attribute [-instance]` shim — a better outcome than the pin's own spelling.
3. **A port duplicate at the import boundary (FR-0175)** — resolved by the manager's dedup before the
   worker touched it: `coeff_mem_of_aeval_mem_integers` existed in two modules, so importing both failed.
   Keeping the namespace-owner's copy and deleting the fully-qualified one took that module's checker from
   10 to 9 `ok` (one pin declaration, one copy).
4. **`omit` is not a silencer** (the manager's ruling): the pin's `omit [Fintype ι] in` at
   `S_…_finrank_…:310` **shapes a signature**, so it stays; only `set_option linter.… false` is forbidden.

### 3.2 The re-read

| figure | before | forecast (§1) | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 716 / 301,921 | 712 / 299,802 | **712 / 299,802** ✓ |
| `needed [literal]` | 732 / 307,340 | — | **728 / 305,221** ✓ |
| frontier F | 1,695 / 822,607 | 1,699 / 824,488 | **1,699 / 824,726** (238-line slip) |
| ready rows | 52 / 11,898 | 50 / 10,210 | **50 / 10,210** ✓ |
| leaves | 187 / 46,259 | unchanged | **187 / 46,259** ✓ |
| `AlgebraicCurve` demand | 46 / 18,888 | 42 / 16,769 | **42 / 16,769** ✓ |
| rows readied | — | 2 / 431 | **2 / 431** (261 + 170) ✓ |

**One wrong cell, again arithmetic**: 822,607 + 2,119 = 824,726, and the brief wrote 824,488. The model
(the per-set subtraction) was right in every cell; the additions in the brief are what slip.

## 4. What this set does not do

- `M4aTorus.completedRayL_fe` (12,126 silo) stays the queued big effort: four unported `Def_` modules
  (1,139 pin lines, 82 declarations) then 742 declarations of mechanical transcription.
- The four rows AF45 moved to one premise (`exists_valuation_mul_eq_one_of_finrank_le_card` 1,062, and the
  three `ord_residue`/`existsUnique_place`/`gaussBasis` successors) are AF47.
