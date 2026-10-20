# Mathlib supplements — the mathlib-first check, and the survey it produced

Two things live here, in this order: the **habit** (before homing a supplement, check that mathlib
`v4.34.0` does not already have it — the playbook §2.2 audit, with the negative recorded), and the
**study** that came out of running the habit across the pin once, in 2026-10-20. The habit is what a
porting session runs every time; the study is a one-off record, kept because it exists.

A **supplement** is pin material that is not FLT mathematics: its statement names only mathlib objects,
and it would live in mathlib if mathlib had it — `RingTheory/HahnSeries/IsAlgClosed.lean` (the
generalized Newton–Puiseux theorem) and `Analysis/MatrixGroup/{Unitary,Orthogonal}RightFinite.lean`
(the `U(2)`/`O(2)` right-finite theorem) are the landed ones.

## 1. The check

```bash
cd lean/.lake/packages/mathlib
rg -n "^\s*(theorem|lemma|def|abbrev|structure|class|instance|inductive)\s+<name>\b" Mathlib/   # name
rg -n "<concept>" Mathlib/<the likely directory>/                                                 # concept
rg -n "<distinctive subterm of the pin's statement>" Mathlib/                                     # statement
```

Three traps the check must survive:

* **A trailing name is not a declaration.** `IsIntegrallyClosed.of_faithfullyFlat` "matches"
  `Ideal.comap_map_eq_self_of_faithfullyFlat`; a `rg` on the last segment alone produces false
  positives. Match the full name, then read the file before believing a hit.
* **Mathlib may have it *more generally*.** `HopfAlgebra.antipode_antipode` exists twice in mathlib
  (`GroupLike.lean:54`, `Primitive.lean:44`) under broader hypotheses, and
  `Measure.isInvInvariant_of_isMulRightInvariant` is `Measure/Haar/Unique.lean:979` — transcribing the
  pin's copy re-proves mathlib. This is the trap that no import check catches.
* **A pin `import Mathlib` hides the whole library**, so "the pin does not import it" is no evidence of
  absence. Only the `rg` over mathlib is.

Record the negative in the module header ("Assumes: mathlib `v4.34.0`; mathlib has no …; checked
`rg <concept> Mathlib/…` on <date>"), so a later reader does not repeat the search.

## 2. The study: what the pin contains

Method (re-runnable, §5): a pin `P2M/Sol/S_*.lean` is **clean** when its whole import block is
`Mathlib`/`Mathlib.*` plus `P2M.Util` (the pin's `p2m_*` tactic macros) — nothing from `Definitions.`,
`Theorems.` or any other `P2M.` module. Dotted module syntax, so the dirty sets are
`rg --pcre2 '^import\s+(Definitions|Theorems)\.'` and `'^import\s+P2M(?!\.Util)'`. A clean import block
forces the statement to be mathlib-worded (a statement naming a pin definition needs a `Definitions.`
import), so the import test is a *necessary* condition; the statement, read by hand, is the sufficient
one (D-S calibration: the classifier reproduces the column's own count of 175 in-cone leaves exactly).

| | files | raw lines | named decls | pin in-edges |
|---|---:|---:|---:|---:|
| all pin `S_` files | 29,511 | — | — | — |
| clean (imports `Mathlib*` + `P2M.Util`) | 3,006 (10.2 %) | — | — | — |
| … in the D-S demand (surveyed in the leaf-families note) | 175 | — | — | — |
| … no `solution` statement | 8 | — | — | — |
| **candidates: clean, unported, outside the D-S cone** | **2,723** | **538,498** | **26,402** | **7,297** |

* All 2,723 are **graph leaves** (`d.cites(i) == []`): a clean `S_` file imports no other node, so
  porting one needs nothing first — cheapness is a pure line count.
* All have ≥ 1 pin consumer (7,297 edges; median 2–3, the head feeds hundreds).
* Size: **798 files ≤ 60 lines, 1,742 ≤ 150, 2,468 ≤ 400**; median 103, mean 197.

Most of the pool is FLT mathematics that merely *uses* mathlib vocabulary, so the study's actionable
layer is the hand-read ranking below, not the pool.

### 2.1 The subject families (how much FLT depends on them)

| family | nodes | raw lines | decls | in-edges | verdict |
|---|---:|---:|---:|---:|---|
| `AlgebraicGeometry` (morphism properties, Proj, closed immersions, formally unramified, descent) | 506 | 63,162 | 2,605 | 1,647 | supplement, huge |
| `Algebra`+`Ideal`+`RingHom`+`Subalgebra`+`AlgHom` | 292 | 42,787 | 1,747 | 629 | supplement, long tail |
| `Module`+`LinearMap`+`Submodule`+`LinearEquiv` | 199 | 35,524 | 1,359 | 345 | supplement, long tail |
| `NumberField` (mixed embeddings, infinite adèles, places, units) | 65 | 29,314 | 1,124 | 136 | supplement, large files |
| `Polynomial`+`MvPolynomial`+`PowerSeries`+`Laurent*` | 150 | 28,935 | 1,695 | 344 | supplement, long tail |
| `HopfAlgebra`+`Bialgebra`+`BialgHom`+`Coalgebra` | 75 | 19,396 | 1,168 | 174 | supplement |
| `ValuationSubring`(+`Valued`,`Valuation`,`ValuationRing`) | 98 | ~18,600 | ~660 | ~680 | supplement |
| `IsLocalRing`+`IsDiscreteValuationRing`+`IsAdicComplete`+`AdicCompletion` | 143 | 18,773 | 635 | 442 | supplement |
| `MeasureTheory` (Haar, fundamental domains, adelic integrals, Fourier) | 80 | 16,568 | 868 | 220 | supplement, FLT-adjacent |
| `Matrix` + GLₙ/SL₂ | 65 | 13,218 | 1,060 | 114 | supplement |
| `WeierstrassCurve`+`WeierstrassProjModel`+`DrinfeldCurve` | 82 | 12,521 | 640 | 231 | supplement (elliptic curves) |
| `groupCohomology` | 57 | 5,712 | 301 | 128 | supplement |
| `WittVector` | 21 | 3,682 | 232 | 71 | supplement |
| `IsRegularLocalRing` | 8 | 1,823 | 85 | 122 | supplement, landmark |
| `IsPrimitiveRoot`+`IsCyclotomicExtension`+`KummerTheory` | 19 | 3,137 | 82 | 47 | supplement |
| `QuaternionAlgebra` | 9 | 1,017 | 32 | 46 | supplement |
| FLT-flavoured (`LanglandsTunnell` 78/30,672, `QuadraticForm` 5/19,705, `Ihara*` 4/13,038, `RegularSingular` 6/13,661, `ModularCurve` 30/7,200, `AutomorphicForm` 18/7,542, `CerednikDrinfeld` 27/4,612, modular-form plumbing ~45/7,600, the statement-shaped rump ~90/30,000, …) | ~350 | ~135,000 | ~8,600 | ~800 | **not supplements** |

### 2.2 The ranked supplements

Each row is a coherent module (or small group) with its proposed mathlib-mirroring home, the gap in
mathlib `v4.34.0` (verified by `rg` for the concept), and its blockers. **ev**: **R** = the exact pin
statement was read; **t** = read truncated; **n** = inferred from the name.

| # | subject | pin files | lines | decls | proposed home | mathlib gap | blockers | ev |
|---|---|---|---:|---:|---|---|---|---|
| 1 | regular local ⇒ domain (81 consumers) | `IsRegularLocalRing` ×8 | 1,823 (head 390) | 85 | `RingTheory/RegularLocalRing/Domain.lean` | that directory has only `Defs`+`Polynomial`; **no `isDomain`** | 390-line Krull-dim/Nakayama chain; `v4.34` renames | R |
| 2 | **alg-closed residue fields** | `ValuationSubring.isAlgClosed_residueField_*`, `henselianLocalRing_*` | **27 + 30** (+125) | 2 (+5) | `RingTheory/Valuation/ValuationSubring/AlgebraicallyClosed.lean` | `rg isAlgClosed_residueField` → **0 hits** | **none** for the 27/30 pair | R |
| 3 | finite-group cohomology (`card G` invertible in `R`) | `groupCohomology` ×57 | 5,712 | 301 | `RepresentationTheory/Homological/GroupCohomology/FiniteGroup.lean` | mathlib stops at H⁰/H¹/H² + Shapiro + H90; no `IsUnit (card G)` vanishing, no H¹/H² `natCard` comparison | builds on mathlib's `inhomogeneousCochains`; `v4.34` renames | R |
| 4 | ghost components ⇒ coefficients | `WittVector` ×21 | 3,682 | 232 | `RingTheory/WittVector/GhostComponent.lean` | `ghostComponent` exists, uniqueness does not | needs `p ∈ R⁰` (already in the statement) | R |
| 5 | **quaternion splitting** | `QuaternionAlgebra` ×9 | 1,017 | 32 | `Algebra/Quaternion/Splitting.lean` | `rg normForm` in mathlib's `Quaternion/` → 0 hits; no `M₂(K)` model | **none** | R |
| 6 | division polynomials / normal forms | `WeierstrassCurve` ×71 | 9,861 | 488 | `AlgebraicGeometry/EllipticCurve/{DivisionPolynomial,NormalForms}.lean` | that directory has only `Basic`+`Degree`; no `Psi2Sq`/`Psi3` | transcription of mathlib's Ψ names | R |
| 7 | GLₙ/SL₂ lemmas | `Matrix` ×65 | 13,218 | 1,060 | `LinearAlgebra/Matrix/SpecialLinearGroup.lean` | `Γ ⊔ ⟨-1⟩` membership etc. absent | heterogeneous; split 3–4 modules | R |
| 8 | `withConv`/convPow + antipode | `HopfAlgebra`+`Bialgebra`+`BialgHom`+`Coalgebra` ×75 | 19,396 | 1,168 | `RingTheory/HopfAlgebra/ConvolutionPower.lean` | **`withConv` absent entirely**; antipode involutive only for group-like/primitive | FLT subject boundary (Raynaud), large | R |
| 9 | **primitivity / Kummer** | `IsPrimitiveRoot` ×9, `KummerTheory` ×2 | 984 + 108 | 31 + 5 | `RingTheory/RootsOfUnity/`, `FieldTheory/KummerExtension/` | `existsUnique_eq_pow_val` 0 hits; `KummerTheory` 0 hits; mathlib's Kummer is single-radicand | none | R |
| 10 | EGA morphism toolbox (1,647 consumers) | `AlgebraicGeometry` ×506 | 63,162 | 2,605 | `AlgebraicGeometry/Morphisms/{Etale,FormallyUnramified,Finite,ClosedImmersion,Descent}.lean` | `IsFinite`/`IsSeparated` descent, `ringKrullDim` of stalks, smooth-rel-dim-0 ⇒ finite | size, not difficulty (median 75 lines/file) | n |

Honourable mentions: `IsLocalRing`+`IsDiscreteValuationRing`+`IsAdicComplete`+`AdicCompletion`
(143 / 18,773, edge-heavy), `MeasureTheory` Haar/adèles (80 / 16,568 — one possible *dedup* against
`IsHaarMeasure.isInvInvariant_of_regular`), `NumberField` (65 / 29,314; only single facts are
extractable).

**Row 2 is the cheapest real win and was verified by hand**: the pin's 27-line
`S_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed.lean`
(`{L} [Field L] [IsAlgClosed L] (A : ValuationSubring L) : IsAlgClosed (IsLocalRing.ResidueField ↥A)`)
and 30-line `…_algebraicClosure_rat` (`(A : ValuationSubring (AlgebraicClosure ℚ)) : IsAlgClosed (ResidueField A)`)
import mathlib only, have **124 and 197 pin consumers**, no blockers, and mathlib has no
`isAlgClosed_residueField` at all.

## 3. Not supplements

* **FLT-flavoured** (~350 files / ~135,000 lines): clean imports, but the *name and motivation* are
  FLT's — `LanglandsTunnell` (78 files: the automorphic gates' own subject), `QuadraticForm`
  (19,705 lines), `Ihara*`, `RegularSingular`, `CerednikDrinfeld`, `ModularCurve` model plumbing, and
  the statement-shaped rump (`flt_regular`, `fermatLastTheoremFive`, `Ribet*`, `TW12*`). The import
  test cannot separate these; they are FLT mathematics that happens to be mathlib-worded.
* **Dedup / glue** (a re-proof of a mathlib fact — import, do not transcribe):
  `AbsoluteValue.Completion.{norm_coe_and_exists_one_lt_norm, isUltrametricDist_of_isNonarchimedean}`
  (37 lines, one-`rw` glue over `UniformSpace.Completion.norm_coe`); `HopfAlgebra.antipode_antipode`
  (mathlib's `GroupLike.lean:54` / `Primitive.lean:44` are more general);
  `MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant` vs `Measure/Haar/Unique.lean:979`; and
  the 15 trailing-name collisions of the name index.

## 4. Caveats

* "Absent from mathlib" is a **name-level negative plus a per-row concept `rg`**, not a proof; read the
  mathlib file before committing a landing.
* Evidence is graded per row (R/t/n); row 10 is **n**, so price it by reading, not by this table.
* No compile check was run: `v4.33`→`v4.34` renames are unverified, as for any transcription.
* The subject families of §2.1 are coarse bucketing of ~2,400 unread files; §2.2 is the actionable
  layer, and §1 is the habit.

## 5. Reproduce

```bash
cd tools/deps
python3 frontier.py --top 0 --json --list --include-leaves > /tmp/fr.json
python3 frontier.py --ds  --top 0 --json --list --include-leaves > /tmp/ds.json
cd /home/haitao/proj/fermats-last-theorem
rg -l --pcre2 '^import\s+(Definitions|Theorems)\.' P2M/Sol/     # dirty set
rg -l --pcre2 '^import\s+P2M(?!\.Util)' P2M/Sol/                # dirty set, P2M
```

then per candidate: `d.stem_index`/`d.cited_by` from `fltdata.FltData()`, its
`Theorems/Thm_<stem>.lean` statement, and a concept `rg` over
`lean/.lake/packages/mathlib/Mathlib/`.

## 6. If a column ever wants one

1. **Row 2** (57 lines, 2 declarations, 321 consumers, no blockers) — the cheapest supplement in the pin
   and a real mathlib gap.
2. **Row 5** (quaternion splitting, 1,017 / 32, no blockers) and **row 9** (primitivity/Kummer,
   1,092 / 36, no blockers).
3. **Row 1** (regular local ⇒ domain) once the 390-line Krull-dim/Nakayama head is priced — the
   landmark of the group.
4. Rows 3, 4, 6, 7, 8 by appetite; row 10 (EGA) is a column of its own, and the FLT-flavoured ~135k
   lines are not supplements at all.
