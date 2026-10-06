# V3 — the translation automorphism of the function field, and its action on places

**Status: landed and reviewed 2026-10-06** — one set, one agent turn, with one
mid-flight route amendment (§2.4) that deleted ≈130 duplicated lines; see §9 for
the close-out and the hand-off. The orders below are kept as written, with the
amendment marked in place, so the scoping can be judged against what happened. This
is the Phase D continuation of
the H5 column: [TOPIC-H5-engine.md](TOPIC-H5-engine.md) §7 stopped the two remaining
H5 vocabulary nodes, and [TOPIC-port-plan.md](TOPIC-port-plan.md) §5 Phase D carries
them. V3 takes the prerequisite the first of them needs —
`WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add` and its
characteristic-free sibling — and leaves the consumer node to V4. Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §0.2 (staffing), §2 (plan,
dedup, scout), §3.3–§3.5 (order, sets, build ladder), §3.7 (boundary), §4
(faithfulness). Record: [../../logs/velu-port.md](../../logs/velu-port.md).

## 0. The two nodes and why they are one topic

Both wrappers are the same theorem modulo one instance; both `S_` files are one
development. Delivered as **one new library module** plus **one appended spec zone**.

Pin wrapper 1 (`Theorems/Thm_WeierstrassCurve_Affine_exists_algEquiv_restrictAlong_placeOfPoint_eq_add.lean`):

```lean
theorem WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {W : WeierstrassCurve.Affine F} [W.IsElliptic]
    [GenusOnePlaceGate W] [GenusOnePlaceGate.IsCentred W] [AbelTheorem W]
    (R : W.Point) :
    ∃ (τ : W.FunctionField ≃ₐ[F] W.FunctionField) (hτ : τ.toAlgHom.toRingHom.IsIntegral),
      ∀ Q : W.Point, (placeOfPoint Q).restrictAlong τ.toAlgHom hτ = placeOfPoint (Q + R)
```

Pin wrapper 2 (`Theorems/Thm_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add.lean`)
is **character-for-character the same except that `[CharZero F]` is absent** — a
`diff` of the two wrappers has one substantive hunk, the binder list. The two `S_`
`solution` bodies are likewise identical (both end in the characteristic-free
`kw_restrictAlong_translateFF_some_placeOfPoint_charFree`). So this is a
general/special pair whose names do not follow the `X_of_Y` pattern, which is why
`port_plan.py`'s `siblings` section is empty: **not a tool finding, a reading.**

Consequence, binding: prove the **characteristic-free** headline and derive the
`CharZero` one in one line. Both pin names must exist (the checker diffs each), at
their wrappers' exact binders.

## 1. What is actually new, measured 2026-10-06

The plan's figure for this node was **4,271 pin lines** (the sibling is 4,316). That
is a silo figure: each `S_` file inlines its already-ported prerequisite cone. The
pre-port measure is `tools/deps/port_advise.py` + `port_plan.py` (§8).

### 1.1 The budget

```
raw S_ lines (both files: 4,271 + 4,316)                8,587
  − duplicate copies (the two files share 188 decls)  −4,076
  − boilerplate (imports / attributes / p2m_* / blank)    −87
  = distinct declaration groups (213)                   4,424
  − already in the port (vetted)                       −2,610
  = NET NEW MATH LINES                                  1,814
```

`port_advise` reports **286 declarations with an identical statement already in
the port (≈5,176 lines not to re-prove)**, 280 of them importable. An independent
sweep of the primary `S_` file's 207 top-level declarations gives 140 substituted
(2,566 lines, matching the tool) and 67 not (1,678 lines). `port_plan`'s `blocks`
section confirms the two files share a 188-declaration / 4,821-line block; the
sibling's only extra block (183 lines, the Velu `_cf` helpers) is **already in the
port**.

### 1.2 Where the 67 unsubstituted declarations go

| group | decls | nominal lines | disposition |
|---|---:|---:|---|
| `instFactNatPrime{2,3,7}_s13e2`, `fact_prime_two_etaSweep`, `fact_prime_three_exchangeShowcase`, `S13_instIsDedekindDomainCoordinateRing`, `instHasPrincipalDivisorsFunctionField_s13` | 7 | ≈140 | **drop** — mathlib/the port supply them (V2 §9 finding 4) |
| `InfinitePlace` class fields (`place`, `deg_eq_one`, `not_isFinitePlace`, `eq_of_not_isFinitePlace`, `placeOfPoint_injective`, `placeOfPoint_surjective`) | 6 | ≈30 | **drop** — fields of the class at `Place/Dictionary.lean:674` |
| binder-spelling variants (`mem_iff_ord_nonneg`, `ord_eq_neg_log_of_valuationSubring_eq`, `polyToFunctionField_apply`, `algebraMap_polynomial_eq_mk_C`) | 4 | ≈142 | **drop or reuse** — `port_advise` §generalise lists these |
| `taylorRemainder₂` block (L576–972) | 8 | ≈340 | **transcribe** (private) |
| `ord_ofHeightOneSpectrum_algebraMap_eq_zero`, `ord_placeOfEquation_eq_zero_of_evalEval_ne_zero` | 2 | ≈60 | **transcribe**, after diffing against the ported `ord_placeOfEquation_*` family |
| `kwWdp_Δ_ne_zero_of_isElliptic`, `Point.translateFF`, `Point.translateFF_zero` | 3 | ≈20 (span-inflated; `translateFF_zero` is `rfl`) | **transcribe** |
| the `kw_*_charFree` / `kwTISD*` chain + the headline (L3320–4272) | 45 | ≈940 | **transcribe**, minus the items in §2.2 |

The nominal spans over-count: the tail of each `S_` file is padded with
`p2m_reactivate` lines and empty `section … end` stubs (`Pullback`, `MillerGen`,
`DivisorWeil`, `TorsionWrapper`, `AxiomChecks`, …), which is why `translateFF_zero`
— a one-line `rfl` — shows a 101-line span.

**Budget: ≈1,750 transcribable content lines, ×1.0–1.2 (transcription) =
≈1,500–2,000 written, estimate 1,700.** One set, one subagent (§0.2). If the
reconnaissance in §4.2 finds more reuse than the `es1a6`/`translationAlgEquivOf`
items below, the estimate moves down, not up.

## 2. The route

### 2.1 What the pin's proof does

```
solution R := ⟨Point.translateFF R, kw_translateFF_toAlgHom_isIntegral_charFree R, fun Q => _⟩
  R = 0        → IsogenyEndDatum.restrictAlong_algHomId
  R = some a b → kw_restrictAlong_translateFF_some_placeOfPoint_charFree
```

`Point.translateFF` is a 5-line `def` by cases on `W.Point` (`0 ↦ AlgEquiv.refl`,
`.some _ _ h ↦ translationAlgEquivOf (kwWdp_Δ_ne_zero_of_isElliptic) h.1`).
`kw_translateFF_toAlgHom_isIntegral_charFree` is
`RingHom.isIntegral_of_surjective _ (translateFF R).surjective`. The weight is in
`kw_restrictAlong_translateFF_some_placeOfPoint_charFree` and the ~480-line
`kw_taseq_*` chain beneath it: a second-order Taylor expansion of the translation
map at `(a, b)`, producing the coordinate-seam data that lets
`kw_addSeam_restrictAlong_eq_placeOfEquation_charFree` identify the restricted
place.

### 2.2 What the port already has (verified 2026-10-06: `grep`, `#check`, co-import)

- **The translation automorphism itself.** `translationCoordHom` /
  `translationHom` / `translationAlgEquiv` / `translationAlgEquivOf` are in
  `FLTForHuman/WeierstrassCurve/Velu/Engine.lean:794–1860`, with
  `translationAlgEquivOf_polyToFunctionField_X`, `…_yGen`,
  `isIntegral_addYFun_adjoin_addXFun`, `addXFunTranscendental`, and the
  char-free hypothesis pair `hΔ : W.Δ ≠ 0`, `hA : W.Equation a b`. **Import, do not
  redeclare.** `IsogenyEndDatum/Engine.lean` transitively imports `Velu/Engine.lean`
  (verified), so one import suffices.
- **The seam lemma.** The pin's
  `kw_addSeam_restrictAlong_eq_placeOfEquation_charFree` (26 lines) is the port's
  `es1a6_addSeam_restrictAlong_eq_placeOfEquation`,
  `FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Engine.lean:979` — same statement
  (the port adds `[IsAlgClosed F]`, which the wrapper has) and the same
  `isFinitePlace_of_mem` → `eq_placeOfEquation_of_le_centre` → `AbstractSeam.map_XClass/YClass`
  proof. **Reuse it; do not write a second copy.**
- `IsogenyEndDatum.restrictAlong_algHomId` (`AbstractSeam.restrictAlong_eq_infinitePlace`)
  is `IsogenyEndDatum/Engine.lean:493`; `AbstractSeam.restrictAlong_eq_infinitePlace`
  likewise.
- The whole inlined cone — the ord calculus, `PolyToFunctionField`, `XYIdeal`,
  `mk_mem_XYIdeal_iff`, `normFormulaAlong_of_elliptic`, the `InfinitePlace`
  instance — is ported; see §1.1's 2,610 vetted lines.
- `IsogenyEndDatum/Engine.lean` and `Velu/Engine.lean` **are co-importable**
  (verified: `lake env lean` on a file importing both, exit 0).

### 2.3 What is genuinely absent

`taylorRemainder₂`, `taylor₂_polynomial`, `mk_taylorRemainder₂_mem_XYIdeal_sq`,
`taylor_linear_mem_XYIdeal_sq`, `sub_negY_eq_evalEval_polynomialY`,
`evalEval_polynomialY_eq_zero_iff_eq_negY`, `mk_sub_algebraMap_evalEval_mem_XYIdeal`,
`mk_mem_XYIdeal_iff_evalEval_eq_zero`; `kwWdp_Δ_ne_zero_of_isElliptic`;
`Point.translateFF`, `Point.translateFF_zero`; the `kwTISD*` coefficients and the
whole `kw_*_charFree` / `kw_taseq_*` chain. None of these is present under any
port name (the `es1a6_*` block is the *additivity* route, not the translation
route, and the port has no `taylorRemainder`/`taseq`/`affod` vocabulary at all).
Two of the list are present under *other* names and are **not** to be written:
`mk_mem_XYIdeal_iff_evalEval_eq_zero` (the ported `mk_mem_XYIdeal_iff`) and the
`kw_addSeam_restrictAlong_eq_placeOfEquation_charFree` helper (the ported
`es1a6_addSeam_restrictAlong_eq_placeOfEquation`). See §2.4 and §4.2.2.

### 2.4 The off-cone dependency, and the import amendment (measured 2026-10-06)

**Amendment — the first draft of this order chose the wrong import.** It proposed
`import …IsogenyEndDatum.Engine` and transcribing the pin's block privately. Reading
the dependency closure of the pin's *new* chain (L3320–4272) shows that would
re-prove ported mathematics:

- the chain names exactly **two** declarations that the port holds only in
  `IsogenyEndDatum/DualEndData.lean` — `ord_ofHeightOneSpectrum_eq_neg_log` and
  `ord_placeOfEquation_XClass_self`;
- `ord_placeOfEquation_XClass_self` is a 3-line corollary of
  `XClass_notMem_XYIdeal_sq` (itself ~40 lines), which needs
  `exists_eq_add_mul_polynomial_of_mem_XYIdeal_sq`,
  `X_sub_C_sq_dvd_eval_of_mem_span_sq`,
  `evalEval_derivative_eq_zero_of_mem_span_sq`,
  `X_sub_C_dvd_eval_of_mem_span` and `derivative_polynomial`;
- **there is no shortcut**: `kw_taseq_ord_X_sub_eq_one_charFree` needs
  `ord (X - a) = 1` at the place, and the pin's own new generalization
  `kw_taseq_ord_ge_of_mem_XYIdeal_pow_charFree` gives only the lower bound from
  `XYIdeal^n` membership. The non-membership `XClass ∉ XYIdeal²` is load-bearing.

On the `Engine` cone the worker must therefore copy that whole chain (~10 private
declarations, **≈130 lines**) into the new module; an in-flight run had done so by
line 319 of 319 written. On the `DualEndData` cone it is one import.

**Decision (amended): import `FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DualEndData`
instead of `…Engine`.** Its closure (100 modules) contains `IsogenyEndDatum.Engine`,
`Velu.Engine` and `Place.Dictionary` — verified — so it strictly dominates the
`Engine` import, and the ~10 duplicated declarations are deleted. Measured cost:
`lake env lean` on this cone is **1 m 21 s** against 23.5 s for `Engine`; with the
§4.5 batching that is a bounded handful of minutes, against ≈130 duplicated lines
that a later refactor would have to reconcile across an off-cone boundary. This is
the "a few minutes of rebuilding beats an open issue" case, and it is also the cone
the module's only future consumer already lives in (`Vocabulary.lean`).

The *structural* finding behind it is registered in
[../../CARRY-FORWARD.md](../../CARRY-FORWARD.md): the second-order `XYIdeal` block and
`ord_ofHeightOneSpectrum_*` belong lower in the DAG (two cones now need them), so a
refactor round should extract them from `DualEndData` to `Place/` and drop this
module's heavy import.

The pin's *taylor* block proper (`taylorRemainder₂`, `taylor₂_polynomial`,
`mk_taylorRemainder₂_mem_XYIdeal_sq`, `taylor_linear_mem_XYIdeal_sq`) is **not** a
duplicate: it is the *producer* side (it builds `XYIdeal²` members and the cotangent
linear part), whereas the ported block is the *consumer* side (structure theorem,
divisibility, non-membership). Both are needed.

## 3. Deliverable

### 3.1 Module

**New `FLTForHuman/WeierstrassCurve/IsogenyEndDatum/TranslationAlgEquiv.lean`**, one
import: `FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DualEndData` (amended in §2.4;
it transitively supplies `Engine`, `Velu/Engine` and `Place/Dictionary`). Namespace
`WeierstrassCurve.Affine` (and `WeierstrassCurve.Affine.Point` for the `translateFF`
pair), exactly as the pin spells them. Module header states the subject, both pin
`S_` files with raw URLs, and what it assumes from `DualEndData`.

A new file touches nothing: cascade **0 library modules**. The measured cost of the
alternatives, for the record (all priced 2026-10-06 with
`tools/deps/build_ladder.py --edit` and `lake env lean`):

| home | size | cascade of a later edit | fixed edit-loop cost |
|---|---:|---|---|
| this new module (imports `DualEndData`) | 0 → ≈1.5 k | 0 modules | **≈1 m 21 s** |
| this new module (imports `Engine` only) | 0 → ≈1.6 k | 0 modules | ≈24 s, but +≈130 duplicated lines |
| append to `IsogenyEndDatum/Vocabulary.lean` | 177 | 2 modules ≈14 s | ≈1 m 21 s |
| append to `Place/Dictionary.lean` | 1,038 | 30 modules ≈347 s | ≈24 s |
| append to `IsogenyEndDatum/Engine.lean` | 2,292 | 5 modules ≈119 s | ≈24 s |

`Vocabulary.lean` is the tempting append (177 lines, the H5 vocabulary tail, and it
is the designated home for the node this one feeds), but it reaches `DualEndData`,
and this topic is a ~1.7 k-line leaf whose every check would then pay the
1 m 37 s floor. A new leaf in the same directory is the cheaper correct home.
**The one append this topic does is the consumer zone (§3.3)** — that is the "a few
minutes of rebuilding beats an open issue" case.

### 3.2 Declarations

**Public, at the pin names, with statements verbatim from the wrappers:**

- `WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add`
  (the general, characteristic-free one — **the theorem that is proved**);
- `WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add`
  (one line: `exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add R`).

**Everything else `private`.** The `S_` files carry no `p2m_export` line for
`kw_*`/`taseq`/`taylorRemainder₂`/`translateFF` — they are pin-*local*, so V2 §4.3's
rule applies: the headline is public, the local block stays `private`. This also
keeps ~45 distinctive names out of the public surface for no verification loss the
checker was ever going to give them. Exception to consider in reconnaissance: if a
name turns out to be pin-public (one of the 286 substitutions maps it to a port
declaration, or a wrapper carries it), it is declared public at the pin name and
recorded.

**Do not** declare the pin's `solution` — the headline *is* the solution.

### 3.3 Checker wiring and consumer

- `spec/check_flt_statements.py`: append the new module to `PORT_FILES` **last**;
  append the two wrappers to `SOURCES` **last**. The `S_` files are **not** added:
  with the helpers `private` the checker never reads them, and both carry the same
  188 declaration names (the `source` map is a list and tolerates duplicates, but
  there is nothing to gain). Confirm in the report that
  `python3 spec/check_flt_statements.py` moves `5805 → 5807 identical`, with
  `promoted` unchanged at 311 and `0 mismatched / 0 missing`.
- `spec/IsogenyEndDatumConsumer.lean` (**append one zone; the only existing file
  this topic edits**): the module is in the `DualEndData` cone (which contains
  `Engine`), so it can never be imported beside `Velu/RestrictAlong.lean` (`normFormulaAlong_of_elliptic`) or
  `GenusOnePlaceGateCentred.lean` (`instInfinitePlace`). The new zone therefore
  takes `[GenusOnePlaceGate W1.toAffine] [GenusOnePlaceGate.IsCentred W1.toAffine]
  [AbelTheorem W1.toAffine]` as hypotheses exactly as zone 3 does, and is a real
  executed composition: instantiate both headlines at the consumer's `W1`
  (`y² = x³ + 1` over `AlgebraicClosure ℚ`) at a nonzero `R` and at `0`; check
  `Point.translateFF_zero`; and feed the resulting `restrictAlong` identity into
  the ported `placeOfPoint`/`restrictAlong` API so that deleting the new module
  makes the file fail. This is the **recorded negative**: the gates cannot be
  discharged from `exists_genusOnePlaceGate_isCentred_and_abelTheorem` here (§5.5 of
  V2), and no zone may import the `RRSpace` cone.

## 4. Work order

### 4.1 Scope

Port the two headlines of §0 — the translation automorphism of `W.FunctionField`
by a point `R` and its action `placeOfPoint Q ↦ placeOfPoint (Q + R)` on the
places — as one new module, reusing the ported translation machinery and the
`es1a6` seam lemma.

**Not this topic:** the collision refactor (§3.3); the downstream consumer
`IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred` (V4's subject);
`IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq`;
`exists_variableChange_forall_restrictAlong_placeOfPoint_eq_of_algEquiv`,
`exists_isogenyEndDatum_restrictAlong_placeOfPoint_eq_smul`, `algHom_ext_…` and the
other `restrictAlong_placeOfPoint` siblings; any edit to a library module other
than the new file. A worker that reaches an unported prerequisite outside this
scope **stops at the boundary and reports** (playbook §3.7) rather than editing a
closed module or weakening a statement.

### 4.2 Reconnaissance (bounded, before writing; report the outcome)

1. `diff` the pin's `taylorRemainder₂` block (L576–972) and ord pair (L2065, L2533)
   against the port's `ord_placeOfEquation_*` / `XYIdeal²` family before
   transcribing; drop or reuse anything whose statement matches, with a `grep -c`.
2. **`port_advise`'s substitution test is name-anchored** (`by_name` on the last name
   component), so a port declaration that does the same work *under a different
   name* is invisible to it and its "already in the port" figure is a **lower
   bound**. Two live cases: `kw_addSeam_restrictAlong_eq_placeOfEquation_charFree`
   ≡ the ported `es1a6_addSeam_restrictAlong_eq_placeOfEquation`, and
   `mk_mem_XYIdeal_iff_evalEval_eq_zero` ≡ the ported `mk_mem_XYIdeal_iff`
   (`Place/Dictionary.lean:567`). Check the *statement*, not the name, for every
   declaration the pin's chain reaches; drop both of these, do not write them.
3. Establish the `kw_*` ↔ `es1a6_*` map and report it; reuse
   `es1a6_addSeam_restrictAlong_eq_placeOfEquation` rather than re-proving it.
4. Confirm the §2.4 closure: the only declarations the new chain takes from
   `DualEndData` are `ord_ofHeightOneSpectrum_eq_neg_log` and
   `ord_placeOfEquation_XClass_self` (plus the latter's support chain, which the
   amended import supplies). **Delete the private copies of all of them** from the
   module — they are not this module's mathematics.
5. Scout the smallest heavy item (`kw_ord_addXFun_sub_pos_charFree`, 36 lines) in a
   gitignored `tmp/` scratch file on the amended cone; report its `lake env lean`
   time before writing the module. If it exceeds the bound, stop and report
   (playbook §2.6).

### 4.3 Source (pin)

Paths relative to the pin root
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/>):

- statements: the two wrappers of §0 (the wrappers win on any disagreement);
- proof bodies and the helper block:
  `P2M/Sol/S_WeierstrassCurve_Affine_exists_algEquiv_restrictAlong_placeOfPoint_eq_add.lean`
  (4,271 lines) — the translation/taylor block is L576–972, L2065, L2533, and
  L3195–4272; the sibling
  `P2M/Sol/S_WeierstrassCurve_Affine_exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add.lean`
  (4,316) is the same development (537 differing lines after normalizing the module
  name) with the `[CharZero F]` line removed. **Port once from the primary file**;
  take the sibling's `solution` binder list (no `CharZero`) for the general headline.

### 4.4 Route, with recorded negatives

- **Statement/`variable` hoisting.** The `S_` files hoist binders into
  `variable`s and split sections (`GenericW`, `GenericPoint`, `Translate`,
  `Pullback`, `MillerGen`, `DivisorWeil`, `TorsionWrapper`) that are empty. Take
  every public binder from the wrapper; ignore the section skeleton; drop the
  empty sections (V1's SET-1 saw 8/13 wrappers hoist).
- **The pin's `maxHeartbeats` bumps are dropped.** The file sets `3200000` globally
  and `25600000` in one section, plus `synthInstance.maxHeartbeats 1600000`; the
  port's global cap is 4,000,000. If a declaration blows the frozen cap, supply the
  explicit instance or restructure the proof — never raise the cap (playbook §6).
- **`translateFF` needs `W.Δ ≠ 0`.** The pin's `kwWdp_Δ_ne_zero_of_isElliptic` is
  `W.coe_Δ' ▸ W.Δ'.ne_zero`; both `coe_Δ'` and `Δ'` are ported
  (`Velu/Engine.lean`). `translationAlgEquivOf` takes `hΔ` and `hA : W.Equation a b`;
  the `.some a b h` case supplies `h.1`.
- **`kw_addSeam_restrictAlong_eq_placeOfEquation_charFree` is not new** — it is
  `es1a6_addSeam_restrictAlong_eq_placeOfEquation` (`Engine.lean:979`). Reuse.
- **`kw_translateFF_some_X/yGen_charFree`** are one-liners over the ported
  `translationAlgEquivOf_polyToFunctionField_X` / `_yGen`.
- **`kw_translateFF_toAlgHom_isIntegral_charFree`** is
  `RingHom.isIntegral_of_surjective _ (Point.translateFF R).surjective`.
- **The pin's `p2m_export`/`p2m_reactivate`/`p2m_open` scaffolding is not Lean
  source to port** — it is the pin's namespace machinery; the port spells the
  namespaces directly.

### 4.5 Stop-early risks (stop and report, do not push)

- **A `kw_taseq_*` step that does not transpose.** The chain is ~480 lines of
  `linear_combination`/`ring`/`simp` over `XYIdeal²` membership and ord
  inequalities. If the §4.2 scout shows the smallest item over the bound, or a
  middle item needs a route change, stop and report with the two statements.
- **A statement in the wrapper that differs from the `S_` file's copy: the wrapper
  wins**; report the difference rather than choosing.
- **Any pull toward `RRSpace`/`GenusOnePlaceGateCentred`** to discharge the gate
  instances: that is the collision boundary (§3.3). Stop and report.
  `DualEndData` is **in scope** — it is the module's import (§2.4) — but nothing
  beyond it.
- **A name that turns out to be pin-public and already declared in the port** with
  a different statement (the `generalise` class): report the two statements, do not
  weaken either.

## 5. Build discipline (copy into the work order)

`lake env lean <opts> <file>` is the edit loop, with `<opts>` =
`-DmaxHeartbeats=4000000 -DautoImplicit=false` (without them the check runs at the
default cap and lies about heavy modules); `lake build <module>` when a file is
done; **one** `lake build` per wave; the full build at the milestone. Bound every
build (`timeout 60` / `90` / `300` / `180`), serialize every `lake build` with
`flock` (the lock lives at `lean/.lake/flt_build.lock`, never `/tmp`), and time it:
high user CPU with a timeout is a real blow-up to bisect, ~0 CPU is contention.
Never raise `maxHeartbeats`; this project's global cap is already 4,000,000, so a
blow-up does **not** surface in ~20 s — the wall bound is the protection. Import
specifically — never `import Mathlib` in a library module.

Measured for this cone: `import
FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DualEndData` costs **1 m 21 s** fixed
for a tiny file (100-module closure, 8.1 MB olean); the `Engine`-only cone costs
≈23.5 s, which is why the batched edit loop matters more here than usual.
**Batch**: the edit loop re-elaborates the whole file, so put a bounded block of
declarations in the module (or in `tmp/scratch*.lean` importing only what the block
needs), check once, then extend — never check per declaration.

## 6. Verification

- `lake env lean` clean per batch; `lake build FLTForHuman.WeierstrassCurve.IsogenyEndDatum.TranslationAlgEquiv`;
  then one wave `lake build` over the module and the consumer.
- `python3 spec/check_flt_statements.py` → `5805 → 5807 identical`, `promoted`
  311 → 311, `0 mismatched / 0 missing`, 36 own-proof exempted. A mismatch is a bug,
  not a drift to accept.
- The checker's sanity probe (manager, at the milestone): mutate one token in a
  transcribed headline (`Q + R` → `Q - R`), expect exactly one `mismatched`, revert.
- `spec/IsogenyEndDatumConsumer.lean` exit 0 (it was 71 s / exit 0 after SET-1).
- `#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`; no
  `sorry`.
- `grep -c` of every declaration dropped or reused (§4.2), with the reason, in
  [../../logs/velu-port.md](../../logs/velu-port.md).

## 7. Risk register

| risk | mitigation | status |
|---|---|---|
| the 4 k-line figure prices a silo | `port_advise`/`port_plan` before a line; net new 1,814 | **measured**; §1 |
| the two nodes are priced separately | the wrappers differ by one instance; both solutions identical | **read**; §0 |
| the `taseq` chain does not transpose | scout the smallest item (§4.2) before writing | open — **the one real unknown** |
| a heavy declaration blows the frozen cap | restructure; never raise | open |
| the pin's taylor block duplicates `DualEndData`'s | it does not (§2.4): the ported block is the consumer side; the *off-cone dependency* is `ord_placeOfEquation_XClass_self` + `ord_ofHeightOneSpectrum_eq_neg_log`, resolved by the amended `DualEndData` import | **measured**; §2.4 |
| the consumer cannot discharge the gates | hypothesis form, exactly as SET-1 zone 3; recorded negative | settled (collision, V2 §2.1) |
| appending the consumer zone cascades | `spec/` only, 178 lines; one wave | measured cheap |
| the checker cannot see a `private` helper's statement | accepted: the helpers are pin-local; the wrapper is the statement authority | accepted; §3.2 |

## 8. Reproduce

```bash
cd tools/deps
python3 port_advise.py --nodes \
  WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add,\
WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add \
  --json build/phaseD_advise.json
python3 port_plan.py --json build/phaseD_advise.json --json-out build/phaseD_plan.json

# the homes that were measured and rejected (§3.1)
python3 build_ladder.py --edit lean/FLTForHuman/WeierstrassCurve/Place/Dictionary.lean
python3 build_ladder.py --edit lean/FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Engine.lean
python3 build_ladder.py --edit lean/FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Vocabulary.lean
```

The 2026-10-06 run is in `tools/deps/build/phaseD_{advise,plan}.{txt,json}`
(untracked, like the toolchain). Re-pin before re-measuring.

## 9. Close-out

**Landed and reviewed 2026-10-06**, one set and one subagent turn, with one
mid-flight route amendment (§2.4).

| artifact | lines | notes |
|---|---:|---|
| `WeierstrassCurve/IsogenyEndDatum/TranslationAlgEquiv.lean` | 1,123 | new; 1 import (`…IsogenyEndDatum.DualEndData`); 54 `private` + exactly the 2 public headlines; 0 `sorry` |
| `spec/IsogenyEndDatumConsumer.lean` | 178 → 253 | zone 5 = 68 lines, the only existing file edited |
| `spec/check_flt_statements.py` | +18 | module last in `PORT_FILES`; the two wrappers last in `SOURCES`; no `S_` files |

**Measured.** `lake env lean` on the amended cone: 149.0 s wall / 80.2 user /
38.0 sys for the finished module (115.3 s on the batch that first caught the
missing `variable {p q}`); `lake build` with `flock` 160.6 s, 9,024 jobs, exit 0;
consumer 58.0 s agent, **1 m 10 s re-run by the manager**, exit 0, warning-free;
axioms probe 59.4 s, both headlines `[propext, Classical.choice, Quot.sound]`.
The `Engine`-cone recon check was 23.7 s and the `DualEndData` fixed cost 1 m 21 s —
so the amendment roughly tripled the per-check cost to buy back ≈130 duplicated
lines.

**Checker.** `5805 → 5807 identical` (311 promoted unchanged), `0 mismatched /
0 missing`, 36 own-proof exempted, 5,843 checked, exit 0. The manager re-ran the
one-token probe independently: `Q + R → Q - R` in the characteristic-free headline
gave exactly `5806 / 1 / 0` with the diff printed, and after a byte-identical
revert (`diff -q`) `5807 / 0 / 0` again. The duplication claim was checked the same
way: **all 54 of the module's `private` names have zero occurrences elsewhere in
`FLTForHuman/`**, so the set introduced no differently-named shadow copies.

**Plan vs actual.** Estimated ≈1,500–2,000 written; measured 1,123 — the
over-estimate is the amendment's saving, since the first draft's ≈340-line "taylor
block" was span-inflated (`translateFF_zero` is a one-line `rfl` under a 101-line
span of `p2m_*` padding and empty sections) and the ≈130-line support chain was
deleted. Two differently-named substitutions were found by statement rather than
by name (§4.2.2). The `kw_*` ↔ port map came out as §2.4 predicted.

**Deviations, all recorded in [../../logs/velu-port.md](../../logs/velu-port.md).**
`Point.translateFF_zero` is `private` per §3.2, so the consumer discharges the zero
case through the headline at `R = 0` instead of by name. Dropping the pin's empty
section skeleton is not free: the two `kw_ord_*_sub_add*_pos` lemmas need an
explicit `variable {p q : F}`, which cost one round. The pin's `C_simp` tactic was
inlined, and `Submodule.pow_mem_pow`'s argument order changed on v4.34.0.

**Hand-off to V4.** `IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred`
now has this node; the module to import is
`FLTForHuman.WeierstrassCurve.IsogenyEndDatum.TranslationAlgEquiv`, and its home
(`Vocabulary.lean`) already carries the `DualEndData` cone, so the heavy import
costs nothing new there. The gate instances remain undis-chargeable in the consumer
(the `instInfinitePlace` collision), so V4's zones stay hypothesis-form too unless
the refactor round runs first.
