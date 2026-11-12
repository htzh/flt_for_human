# SET-AF45 — the regular prolongation's residue calculus and the valuation subring's denominators

**Status: LANDED 2026-11-12** — §0–§2 the cut, price and manager's layer, §4 the forecast, §5 the landing record and the re-read. Read off the D–S shelf
with the recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md),
on the read SET-AF44's landing left. Forty-fifth set of the column, and the direct continuation of AF44:
**five of its six rows are the rows AF44 readied**, and the sixth and last is the valuation-side lemma the
next one in the chain needs.

**6 rows / 1,337 silo / 1,214 net (`port_plan`) in 28 declaration groups and ≈1,250 written lines.**
**Return: 2,146 silo in five rows** — the best the column has measured in absolute terms, and it includes
the two rows AF44 §7 named as next (`1,082` + `848`).

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `AlgebraicCurve.RegularProlongation.sum_finrank_adjoin_residue_le` | 427 | **4/22** | the residue map of a regular prolongation does not increase the `finrank` of a span of adjoined elements: `∑ finrank (adjoin (residue x i)) ≤ finrank` |
| **A2** | `AlgebraicCurve.RegularProlongation.exists_forall_residue_eq` | 76 | 1/1 | the residue map of a regular prolongation is surjective on a prescribed finite set, up to an integral element |
| **B1** | `ValuationSubring.exists_sub_mem_nonunits_of_finrank_le_card` | 337 | 1/1 | if a valuation subring has fewer residue classes than the degree of an extension, two elements can be separated by a `z` that stays integral and whose differences are non-units |
| **B2** | `ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin` | 259 | 3/36 | `V ⊓ K[f]` is a principal ideal domain for `f` transcendental — **36 project consumers** |
| **B3** | `ValuationSubring.mem_of_forall_mem_iff_of_subset` | 126 | 1/1 | membership in every valuation subring containing a given one is decided by the family alone |
| **B4** | `ValuationSubring.exists_mul_pow_inv_mem_of_finiteDimensional_adjoin` | 112 | 3/5 | in a finite-dimensional extension a high enough power of `f⁻¹` clears `f`-denominators |

## 0. The read

The read SET-AF44's landing left (corrected: the five `ModularCurve` phi markers unported):

| figure | value |
|---|---|
| `needed [F terminal]` | **722 / 303,258** |
| `needed [literal]` | 738 / 308,677 |
| frontier F | 1,689 / 821,270 |
| ready rows | 50 / 10,592 |
| leaves | 190 / 46,756 |
| `ValuationSubring` demand | 20 / 4,214 |
| `AlgebraicCurve` demand | 48 / 19,391 |
| withheld | 4 rows |

**Premise audit**: empty at the shelf level (`premises = 1` on each row, all ported — A1/A2 cite AF44's
`sum_finrank_adjoin_residue_le` chain, B1–B4 cite nothing). **Definition gate: closed.**
`Def_AlgebraicCurve_RegularProlongation` is ported (its port home is the module A1 is inserted into), the
B rows' imports are mathlib plus `P2M.Util`, and `port_advise --with-defs` reports no missing module.

**The cut is the shelf's return column at work.** AF44's five readied rows are the shelf's head by project
leverage (`427` alone carries 22 project consumers, `259` another 36), and taking them together with the
three leaf rows of the same subject makes one story — the residue/finrank calculus of a regular
prolongation on the `AlgebraicCurve` side and the valuation-subring denominator lemmas it consumes on the
`FieldTheory` side. This is the first set of the column whose subject straddles two of its directories,
and the two orders are exactly that division.

## 1. The price

| figure | value |
|---|---:|
| raw `S_` lines | 1,337 |
| declaration lines | 1,258 |
| — duplicate copies | 6 |
| — boilerplate | 79 |
| distinct declaration groups | 28 |
| once-cost after dedup | 1,252 |
| already in the port | 38 |
| **net new math lines** | **1,214** |
| written (two orders) | ≈1,250 |

`port_advise` finds 11 trusted substitutions (all small `open`-level reuses) and no suspect one. One
port-once block: `exists_lift` (127 lines, one file).

## 2. The manager's layer, landed (do not redo it)

1. **Order A is an insertion, and the home is decided by subject.** A1 and A2 are the residue/finrank
   calculus, which is exactly what `FLTForHuman/AlgebraicCurve/RegularProlongationFinrank.lean` is — the
   port's home for five `RegularProlongation` pin nodes already. The module grew **1,568 → 1,690 lines**
   as a **pure addition** (`git diff --stat`: 122 insertions, 0 deletions): the two pin sources' twelve
   declarations appended inside `namespace RegularProlongation` (the pin's label namespace `W7XK3FI` kept),
   four new `spec-pin:` lines, and **11 `sorry` bodies**. It elaborates, builds (2,525 jobs, silent) and
   reads **62 ok / 0 mismatch / 0 missing**; its one dependent (`Place/ConstantFieldExtension.lean`) still
   builds. The insertion's price is that cascade and nothing else.
2. **Order B is a new module**, because the four B rows are generic valuation-subring mathematics:
   `FLTForHuman/FieldTheory/ValuationSubringFinrank.lean`, 161 lines, header with eight `spec-pin:` lines
   and eight mathlib imports plus `…FieldTheory.ValuationSubringApproximation` (AF44's module, whose
   `exists_forall_mem_and_sub_mem_nonunits` is B1's nearest sibling); the declarations are nested under
   `namespace ValuationSubring` in the pin's label namespaces (`CompleteSplitting`,
   `P2mFunctionFieldPlacesDiscrete`). **16 declarations, 16 `sorry` bodies**, `check_port` **16 ok / 0
   mismatch / 0 missing**, builds silent (3,094 jobs).
3. **One pin spelling must be localised in each order**: the pin closes its label namespace with the
   *fully qualified* `end AlgebraicCurve.RegularProlongation.W7XK3FI` (and
   `end ValuationSubring.CompleteSplitting`), which cannot be used inside the port's nested namespace — the
   port writes `end W7XK3FI` / `end CompleteSplitting`. This is the first *end*-line spelling difference the
   column has met, and it is a pure scoping artefact (FR-0172).
4. **One import had to be added to the hub, by ruling**: order A's two proofs consume
   `ValuationSubring.exists_forall_mem_and_sub_mem_nonunits` (pin
   `S_…_sum_finrank_adjoin_residue_le.lean:164` and `…_exists_forall_residue_eq.lean:59`), which SET-AF44
   landed in `FieldTheory/ValuationSubringApproximation.lean` — outside the hub's seven-module closure, and
   absent from mathlib v4.34 (which has only `Ideal.exists_forall_sub_mem_ideal`). The direction is the
   natural one (`AlgebraicCurve` above `FieldTheory`, and that module imports mathlib only), so the import
   was approved rather than the ~300-line approximation proof being inlined. This is the *fifth* instance of
   FR-0166's class in three waves: a scaffold built from statements is not import-clean for its proofs.
5. **No `own:` row, no marker, no `set_option` beyond `autoImplicit false`**; the `Mathlib` imports of the
   pin files are not carried.

## 3. Orders and gates

`tmp/af45/WORKORDER-AF45A-prolongation-residue.md` (insertion, 12 declarations, 503 silo) and
`tmp/af45/WORKORDER-AF45B-valuation-finrank.md` (new module, 16 declarations, 834 silo). Disjoint files, so
they run in parallel — but note order A edits a **hub**: the worker must not build anything else while it
does, and the manager takes the cascade check. Standard gates: `check_port --force` at **62 ok** (A, the
whole module) and **16 ok** (B), axioms clean on the six headlines, each module's own `lake build` under
`flock`/`timeout` with no tree build, silence and zero warnings, `dedup --within --module <Name>` /
`move_dead`, and one `spec/` consumer zone per order.

## 4. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 722 / 303,258 | **716 / 301,921** |
| `needed [literal]` | 738 / 308,677 | **732 / 307,344** |
| frontier F | 1,689 / 821,270 | **1,695 / 822,607** |
| ready rows | 50 / 10,592 | **52 / 11,898** |
| leaves | 190 / 46,756 | **187 / 46,259** |
| `ValuationSubring` demand | 20 / 4,214 | **16 / 3,380** |
| `AlgebraicCurve` demand | 48 / 19,391 | **46 / 18,888** |

**Rows readied: five / 2,146 silo** — `RegularProlongation.exists_gaussBasis_mem_integralClosure_piResidue_uniqueRepr_of_sum_finrank_eq`
(**1,082**), `…finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq` (**848**),
`…span_residue_lSpace_le_residueSpan_inf` (98), `…coe_minpoly_adjoin_coeff_mem_integers` (91) and
`…finiteDimensional_adjoin_residue_of_sum_finrank_eq` (27). Four further rows come within one premise
(the largest `ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card`, 1,062).

## 5. The landing (2026-11-12)

Two orders, all gates green, no blocker; the manager applied one dedup edit to the hub after review.

| order | module | lines | proofs | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **45A** | `AlgebraicCurve/RegularProlongationFinrank.lean` (insertion) | 1,568 → 1,690 → 2,029 → **2,015** | 11 | **62 ok / 0 / 0** (the whole hub) | 14 s + cascade | 2/2 |
| **45B** | `FieldTheory/ValuationSubringFinrank.lean` (new) | 161 → **861** | 16 | **16 ok / 0 / 0** | 6.8 s | 4/4 |
| | | | 27 | **78 ok, 0 mismatch, 0 missing, 0 own** | | 6/6 |

**What the set consumed**: 6 rows / 1,337 silo in **1,034 written proof lines** (338 + 696) over the
manager's layer (12 + 16 declarations). The hub's dependent `Place/ConstantFieldExtension.lean` still
builds (3,844 jobs), so the insertion's cascade is clean. `move_dead` reports **0 dead** on both.

### 5.1 Deviations and the manager's edits

1. **The hub's one import** (§2.4, approved by ruling): +578 jobs (+22.9 %, 14 s) on a 2,525-job build, and
   the alternative was inlining a ~300-line approximation proof.
2. **The manager merged five intra-module duplicates in the hub** — the pin writes `constHom`,
   `coe_constHom`, `residue_constHom`, `aeval_eq_linearCombination` and `linearIndependent_pow_iff_transcendental`
   in *both* of its files, and the appended block brought the second copies. FR-0165's rule applied: one
   proof, the pin's second name kept as a one-line application to the module's own copy. `dedup`'s
   removable count went **59 → 42 lines** (the residual is the pin's duplicated *statements* in two
   namespaces, which both names' checker rows require), the module went 2,029 → **2,015 lines**, and each
   step was verified (silent elaboration + 62 ok) before the next.
3. **The namespace-shadowing trap is wider than FR-0170 recorded**: besides `add_mem`/`neg_mem`/`mul_mem`
   (where the root lemmas are now `AddMemClass.add_mem` &c, there is no `_root_.neg_mem`), the *unqualified*
   `eq_top_iff` now resolves to `ValuationSubring.eq_top_iff` (`O = ⊤ ↔ ¬ O.valuation.IsNontrivial`), so two
   sites needed `_root_.eq_top_iff`; and `IsLocalHom`'s field is now `map_nonunit` (the pin's `h.1` had to be
   spelled `.map_nonunit`). FR-0174 supersedes FR-0170 with the full list.
4. **v4.34's `linter.style.haveILetI` is on by default and forced 11 `haveI`/`letI` → `have`/`let`
   rewrites** in B2 — a behaviour-preserving rewrite (the linter's own documentation states Lean 4
   `have`/`let` already register local instances, and the module would not elaborate otherwise), not a
   silencing. FR-0173.
5. **The rest is the standard v4.34 proof text**: `zero_le'` → `zero_le`, `if_pos`/`if_neg` →
   `ite_eq_left`/`ite_eq_right`, `dif_pos` → `dite_eq_left`, `haveI hfin` → `have hfin`; four mathlib
   imports added to the new module (`Valuation.LocalSubring`, `Valuation.Discrete.Basic`,
   `Polynomial.ScaleRoots`, `Polynomial.Subring`), none removed or reordered.
6. **One `end`-line spelling artefact** (§2.3): the pin closes its label namespaces with *qualified* names
   (`end AlgebraicCurve.RegularProlongation.W7XK3FI`, `end ValuationSubring.CompleteSplitting`) which cannot
   resolve inside the port's nested namespaces; the port writes the bare name. FR-0172.
7. **The order's heartbeat claim was wrong**: trap 5 of the B order said "no pin file overrides the
   budget"; B3's and B4's pin files each carry `set_option maxHeartbeats 8000000`. The worker reported it,
   carried neither, and measured the module silent at **30,000** — a 20× margin under the gate. The order
   has been corrected in place.

### 5.2 The re-read

| figure | before | forecast | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 722 / 303,258 | 716 / 301,921 | **716 / 301,921** ✓ |
| `needed [literal]` | 738 / 308,677 | 732 / 307,344 | **732 / 307,340** (−4) |
| frontier F | 1,689 / 821,270 | 1,695 / 822,607 | **1,695 / 822,607** ✓ |
| ready rows | 50 / 10,592 | 52 / 11,898 | **52 / 11,898** ✓ |
| leaves | 190 / 46,756 | 187 / 46,259 | **187 / 46,259** ✓ |
| `ValuationSubring` demand | 20 / 4,214 | 16 / 3,380 | **16 / 3,380** ✓ |
| `AlgebraicCurve` demand | 48 / 19,391 | 46 / 18,888 | **46 / 18,888** ✓ |

**One wrong cell, and it is arithmetic, not the model**: 308,677 − 1,337 = 307,340, and the brief wrote
307,344. The other six cells are exact.

**Rows readied: five / 2,146 silo, to the line** — 1,082 + 848 + 98 + 91 + 27, the two largest being the
rows AF44 §7 named as next. Four further rows come within one premise, the largest
`ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card` (1,062).

## 6. What this set does not do

- **`ValuationSubring.exists_valuation_mul_eq_one_of_forall_sup_eq_top`** (870, ready since AF44) is not
  cut: it is the one AF44-readied row that belongs to a different story (the valuation ring's units, not the
  finrank/denominator calculus), and it is the cheapest head of the next valuation set.
- **`ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv`** (138, readied by AF44)
  stays: it is the `f⁻¹`-side companion of AF44's own partial fractions, so it belongs with that family.
- **`RegularProlongation.exists_prolongation_of_card_roots_eq`** (613) and
  `…ord_residue_le_sum_ord_of_isIntegral_adjoin` (1,090) are each **one premise away** after this set and
  are the natural AF46 pair.
- **`M4aTorus.completedRayL_fe`** (12,126 silo, the leaves block's largest node by a factor of three) is
  **not** this set and the reason is measured, not preferred: its statement names
  `completedRayL`, `IsParity`, `gaussSumAt`, `IsGaussDatum` and `Deep.Analytic.*`, **none of which the port
  has** — the definition layer behind it is four unported pin modules (`Def_NumberField_{CompletedRayL,
  RayCharacterData,EuclideanIdealLattice,NarrowRayClassGroup}`, 1,139 pin lines, 82 declarations, the last
  alone 986 lines) and the node itself is 742 declarations. That is a def-layer set plus a mechanical-
  transcription set on the AF7 pattern, priced here so the next pass starts from the number.
