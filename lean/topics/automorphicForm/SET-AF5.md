# SET-AF5 — the right-convolution operator's calculus: the unipotent embedding's continuity and the translation law

**Status: landed 2026-11-02 — manager's layer and W1.** Read off the
D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
(§0 the read, §0.3 the instrument, §3 the pricing, §5.4 the surface gate, §7 the re-read), and it is
the fifth `AutomorphicForm`-serving set. Unlike SET-AF1–AF4 the instrument did **not** pick a cheap
definition leaf with a large fan-out; it picked the **engine two big families are one edge short of**.

The set is **three rows / 520 silo / 481 net new math lines**:

| step | row (`AutomorphicForm.` dropped) | silo | net | who |
|---|---|---:|---:|---|
| **G1** | `continuous_unipotentGL2` (leaf) | 28 | 17 | manager |
| **G2** | `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` (leaf) | 21 | 14 | manager |
| **W1** | `continuous_rightConv_and_contDiff_of_isFactorizableTestFn` | 471 | 450 | worker |
| | **3** | **520** | **481** | |

and its readiness return is **five rows / 7,007 silo**, all gate-free (§0.4). Two of them are the
archimedean-derivative chain's own two headline rows
(`archDerivAt{,Complex}_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn`, 1,246 + 1,248), which
SET-AF4 §7 deferred as the column's next big proof — so this set is the *door* to it, not a step away
from it.

The manager's layer is **not** a definition layer: the set's declaration-level definition gate is
**empty** (§0.4). It is the **refactor** the set forces, and it turned out to be the interesting part:

1. **one promotion and a three-fold dedup.** The port already proves the *specialised* unipotent
   continuity in three separate modules (`continuous_unipotentGL2_adele` 13 lines,
   `continuous_unipotentGL2'` 10 + its provenance comment, and a `private continuous_unipotentGL2`
   11 lines) while the
   pin node is the **general** ring statement. G1 writes the general one once, in the module that
   defines `unipotentGL2`, and deletes all three copies;
2. **two legacy migrations** (`Adelic/ConstantTerm.lean`, `Adelic/RightConvolution.lean`) — both
   were still wired through `PORT_FILES`, and both are now `spec-pin:`-wired and off the register;
3. **the FR-0095 shadow closed at the root.** `AutomorphicForm.continuous_unipotentGL2` had been
   reading as *ported* since SET-AF2 only because a `private` helper carried its last name; with the
   general statement in the port the node is ported honestly, and the `--unport` correction that
   every read since SET-AF2 needed is **no longer needed**.

§0 the read and the instrument; §1 the cut and its pricing; §2 what the three rows say; §3 homes;
§4 ground prep (done); §5 the traps W1 had to carry; §6 the gates; §7 the calls; §8 reproduce and the
two measured re-reads; §9 what this set does not do. **Appendix A** lists the 37 ready rows with each one's
readiness return, **Appendix B** the 82 leaves, both as of the read that chose the cut.

## 0. The read

### 0.1 The canonical read, and the corrected one

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af5.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
    --unport AutomorphicForm.continuous_unipotentGL2 --json > build/shelf-af5-corr.json
python3 frontier.py --selfcheck
```

**`--selfcheck` PASS** — 1,350 `Thm_` sources, 1,515 declared names, 1,515 / 756,424 raw `S_` lines.

**The read is SET-AF4's own post-landing re-read, exactly**: the corrected column below reproduces
that brief's §8 to the line, so this set opens on a measured figure and not on a delta.

| figure | instrument's read | **corrected read** | SET-AF4 §8 (corrected) |
|---|---:|---:|---:|
| `needed [F terminal]` | 900 / 370,942 | **901 / 370,970** | 901 / 370,970 |
| `needed [literal]` | 913 / 374,417 | **914 / 374,445** | 914 / 374,445 |
| frontier F (union) | 1,515 / 756,424 | **1,514 / 756,396** | 1,514 / 756,396 |
| … of F, inside the cone | 1,190 / 607,756 | **1,189 / 607,728** | — |
| port cone / avoided R | 2,103 / 982,173 · 140 / 74,620 | same | same |
| ready rows, all namespaces | 68 / 23,417 | **66 / 22,656** | 66 / 22,656 |
| leaves, all namespaces | 250 / 62,609 | **251 / 62,637** | 251 / 62,637 |
| `AutomorphicForm` ready rows | 39 / 18,073 | **37 / 17,312** | 37 / 17,312 |
| `AutomorphicForm` leaves | 81 / 16,570 | **82 / 16,598** | 82 / 16,598 |
| `AutomorphicForm` demand | 402 / 169,277 | same | same |
| withheld by the FR-0044 guard | 4 / 831 | **4 / 831** | 4 / 831 |

The withheld block is unchanged and is not this column's: the two `ModularCurve` Tate-module rows
(327 + 283), the `Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` row (126) and
`Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95) — the prunable complex-analytic subject.

### 0.2 The correction — and why it is the last one

The instrument's read differs from the corrected one by exactly the AF2 shadow:
`AutomorphicForm.continuous_unipotentGL2` (28 silo, a leaf). SET-AF2's M2 module proved
`private theorem continuous_unipotentGL2` at the **`AdeleRing` specialisation**, and `frontier.py`'s
ported set is a set of last names *including* private declarations (FR-0095), so the pin's general
node has been reading as supplied since. `--unport` restores 901 / 370,970 and puts the node back on
the shelf, which is where this set found it.

**This set removes the cause instead of the symptom.** G1 puts the pin's *general* statement in the
port at the pin's name, so the last-name tier now matches a declaration that really is the node, and
the two shadow rows (`continuous_rightConv_and_contDiff_…` 471 and
`isCuspidalFn_isKfSmooth_levelInvariant_…` 290) become ready **honestly**. The FR-0095 `--unport`
invocation is retired: from this landing on, the instrument's read and the corrected read are the same
read, and §8 measures that they are.

### 0.3 The instrument that chose the cut: readiness return

SET-AF4 introduced **return(r)** = the silo of the unported cone rows whose unported premise set is
exactly `{r}`, and this read recomputes it over the current shelf (Appendix A/B carry the per-row
figure; the query itself is §8's script).

| shelf row | silo | return | the row(s) it would ready |
|---|---:|---:|---|
| `continuous_rightConv_and_contDiff_of_isFactorizableTestFn` (the set's W1) | 471 | 3,833 | `rightConv_rightTranslate_mem_of_isCuspSubrep` |
| **`rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply`** (leaf) | **21** | **2,884** | `archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` 1,246 + `archDerivAtComplex_…` 1,248 + `hasDerivAt_rightConv_mul_unipotentGL2_…` 390 |
| `ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne` (leaf) | 94 | 2,352 | five `ModularForm`/`ModularCurve` rows |
| `NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact` (leaf) | 123 | 2,113 | six rows, 635 … 134 |
| `exists_mem_productionPinsCompact_U_mul_eq_rat` (leaf) | 63 | 2,044 | `weightOneLift_centralScalar_mul` 1,134 + 472 + 438 |
| `TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` | 63 | 1,900 | 913 + 905 + 82 |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` (leaf) | 70 | 1,445 | 1,175 + 190 + 80 |
| `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` (leaf) | 401 | 1,443 | 1,227 + four Casimir rows (216) |
| **`continuous_unipotentGL2`** (leaf) | **28** | **761** | `continuous_rightConv_and_contDiff_of_isFactorizableTestFn` 471 + `isCuspidalFn_isKfSmooth_levelInvariant_…` 290 |
| `AdeleRing.secondCountableTopology_generalLinearGroup_finTwo` | 32 | 1,057 | 514 + 429 + 80 + 34 |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 990 | 661 + 217 + 112 |

**The set is the top of this table plus its own key.** `rightConv_apply_mul_eq_…` is **2nd** by
absolute return (2,884) and **1st outright in return per silo** — 137 lines readied per line written,
5× the next row and 17× the best 400-line row; `continuous_unipotentGL2` is only **12th** (761) and is
taken because it is the *premise of row 1 of the table*: `continuous_rightConv_and_contDiff_of_isFactorizableTestFn` (471 → 3,833) is the
largest readiness event on the whole shelf and it is one 28-line row away. Together they are
7,007 silo for 49 written lines, and they are one operator (§0.3's last paragraph).

The rows above `continuous_unipotentGL2` in absolute return that this set does **not** take are each a
different column's or a different subject's; the two nearest:

* `ModularForm.exists_qExpansion_eq_aeval_mul_pow_levelOne` readies five rows of the **`ModularForm` /
  `ModularCurve`** `q`-expansion-integrality story — that is the MC column's work, not AF's;
* `finite_setOf_algebraMap_mem_of_isCompact` readies six rows of one story — the **rational
  torus/unipotent Haar-measure block** (`isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant`,
  `isClosed_rationalTorusUnipotent`, the two `integral_mul_eq_integral_mul_weight_…` rows). It is a
  genuine candidate and it is **deferred to SET-AF6** (§7 call 7) — it is one subject, 123 silo, and
  its own read must price the `RationalCentreUnipotentQuotient` gate that SET-AF4 §9 left open.

**And the choice is one *story*, not two keys.** The two rows this set takes are the same operator:
`rightConv`'s two basic laws as an integral over `GL₂(𝔸)` — it is continuous (and `C^∞` along the
unipotent direction) in its group argument, and a right translation of that argument is absorbed by
the test function. Both proofs are the *same* tool, Haar left-invariance
(`integral_mul_left_eq_self`), and the second is not a leaf of the first but its sibling: `rightConv`
read as `g ↦ ∫ x, φ (g·x) f x`.

### 0.4 The declaration-level gate: **empty**, and the FR-0099 census that confirms it

`spec/gate_scan.py` over the three rows' `Def_` closures, then the FR-0099 correction (a row can use
a declaration that reaches it through a **premise's** own imports, which neither `gate_scan` nor
`port_advise --with-defs` sees — that is what produced SET-AF4's two mis-priced gates):

| row | wrapper's `Def_` modules | used / missing | FR-0099 census (wrapper ∪ premises) |
|---|---|---|---|
| G1 (28) | `AutomorphicForm_ConstantTerm`, `AutomorphicForm_AdelicLsXi` | 4 + 0 / **0** | 0 missing |
| G2 (21) | `AutomorphicForm_RightConvolution`, `AutomorphicForm_AdelicLsXi` | 1 + 0 / **0** | 0 missing |
| W1 (471) | `Auto…_RightConvolution`, `…_AdelicLsXi`, `…_ConstantTerm`, `…_FactorizableTestFn`, `NumberField_AdelicBox` | 1 + 1 + 3 + 5 + 2 / **0** | **0 missing** (4 Def_ modules) |

**This is the first AF set with no definition ground at all.** Every declaration the three `S_` files
name — `unipotentGL2{,Hom,_coe,_zero,_add}`, `rightConv`, `IsFactorizableTestFn`, `IsArchTestFactor`,
`IsFinTestFactor`, `archEntries{,_apply}`, `AdelicBox.continuous_ringEquiv_mixedSpace` — is in the port
at the pin's statement, `gate_scan` says 0 missing, and `port_advise --with-defs` reports the closure
as four already-ported modules (68 trusted substitutions, 3 suspect). So the manager's layer here is
**refactor and migration, not `Def_` nodes** — and §1.5 is where the refactor's real content turned
out to be.

**The five rows the set readies are gate-free too**, under the same corrected census:

| row readied | silo | wrapper `Def_` modules | missing |
|---|---:|---|---:|
| `rightConv_rightTranslate_mem_of_isCuspSubrep` | 3,833 | 6 | **0** |
| `archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` | 1,246 | 4 | **0** |
| `archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` | 1,248 | 4 | **0** |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | 4 | **0** |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 6 | **0** |

All five are **writable**, which is the difference from SET-AF4 (three of its thirteen were gated).
So the `on the shelf` and `writable` columns of §8 coincide for this set.

### 0.5 The shelf, quoted whole

`AutomorphicForm` **ready block: 37 rows / 17,312 silo** (Appendix A); **leaves block: 82 rows /
16,598 silo** (Appendix B). Both are quoted in full there, with each row's readiness return, and every
row not cut is **deferred** with a reason in §9's table — the two blocks are the *same* shelf and a
brief that quotes only one of them undercounts its own deferral list (the SET 4/5 lesson).

The `AutomorphicForm` demand is 402 / 169,277, so the two blocks are 10% of the column by count and 35%
by silo: the rest is behind the two blocks (the `bigCell` family, the `inducedSection` family, the
`WhittakerCoefficient` family, the `CuspidalConstituent`/`Cusp` family).

**The family this set is the gate of.** Ten of the 119 AF shelf rows are one citation edge from the
archimedean derivative — **4,004 silo** — and this set is the door to all ten:

| the chain's rows | silo | on the shelf? |
|---|---:|---|
| `archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` | 1,246 | **ready by G2** |
| `archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` | 1,248 | **ready by G2** |
| `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` | 401 | leaf (return 1,443) |
| `archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` | 250 | leaf |
| `archDerivAt_commutator_of_isArchSmoothAt` | 208 | leaf |
| `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` | 184 | leaf |
| `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` | 133 | leaf |
| `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` | 110 | leaf |
| `apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` | 117 | leaf |
| `apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` | 107 | leaf |
| **10 rows** | **4,004** | 2 ready **+ 8 leaves: 1,510 silo → 1,001 net** (priced) |

So this set does not merely read 7,007 silo of consumers: it converts the column's biggest deferred
family from "eight leaves and two unready headlines" into "two ready rows and eight priced leaves"
(§7 call 5).

## 1. The cut

### 1.1 The story

`rightConv φ f g = ∫ x, φ (g·x) f x ∂μ` is the port's right-regular action. Everything downstream —
the smoothing engine, the cusp-subrepresentation, the archimedean-derivative chain that differentiates
`rightConv` in the unipotent direction — needs two facts about it that no module states:

1. **it is continuous in the group argument, and `C^∞` along the unipotent line.** For a
   factorizable test function `f = fa · ff` the integrand's dependence on `z` in
   `rightConv φ f (n(z) · g)` is *affine* — `archEntries` of `(n(z)·g)⁻¹·y` is
   `sliceCD g y .1 + z · sliceCD g y .2` — so the integral is `C^∞` by a dominated-convergence
   induction, and continuity in `g` is the uniform estimate `‖φ (h·x) − φ (g·x)‖ < δ` on the compact
   `tsupport f` (§2.1);
2. **a right translation of the argument moves into the test function**:
   `rightConv φ f (g·t) = rightConv φ (f ∘ (t⁻¹ ·)) g` — a single re-indexation, because the Haar
   measure is left-invariant.

That is one subject (the operator's calculus) with three rows once the two premises are named:
`continuous_unipotentGL2` is the unipotent half of (1) — it is what makes `z ↦ n(z)·g` a continuous
curve at all.

### 1.2 The steps

| step | node | silo | net | home | lane |
|---|---|---|---:|---|---|
| **G1** | `AutomorphicForm.continuous_unipotentGL2` | 28 | 17 | insert `Adelic/ConstantTerm.lean` (the module that defines `unipotentGL2`) | manager |
| **G2** | `AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` | 21 | 14 | insert `Adelic/RightConvolution.lean` (beside `rightConv_comp_mul_left`) | manager |
| **W1** | `AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn` | 471 | 450 | new `Adelic/RightConvRegularity.lean` | worker |
| | **3** | **520** | **481** | 1 new module, 2 insertions, 6 wire lines | |

**Wires.** Three per touched module for the manager's two (`Theorems/Thm_…` + its `P2M/Sol/S_…` +
the `Definitions/Def_…` the module already transcribed); two for the worker's new module
(`Theorems/Thm_…` + `P2M/Sol/S_…`).

The order is forced at one point only: W1 is stated over `unipotentGL2`'s continuity (G1) and the
`continuous_and_hasCompactSupport_of_isFactorizableTestFn` premise (ported), so G1 lands first. G2 is
independent of both.

### 1.3 Pricing

```bash
python3 port_advise.py --nodes AutomorphicForm.continuous_unipotentGL2 \
    --nodes AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn \
    --nodes AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply --json build/af5-rc-advise.json
python3 port_plan.py --json build/af5-rc-advise.json
```

**520 raw `S_` lines − 39 boilerplate = 481 declaration lines − 0 duplicate copies − 0 already in the
port = 481 net new math lines** (17 + 450 + 14). Two readings worth recording:

* **the *port once* block is empty** — the 471-line file's prelude is its own: the pin does not copy
  `exists_integrable_bound`/`integrable_of_vanish`/`continuous_shape`/`contDiff_integral_shape` into
  another `S_` file, so there is nothing to write twice and nothing to promote for sharing;
* **nothing is already in the port** — and this time the tool's three false negatives were checked by
  hand (§3), because the last four sets each found a "0 net" row that was a promotion in disguise
  (FR-0101). The nearest thing is the *three specialised copies* of G1, which the tool cannot see
  because their statements are not the pin's (they are the `R := AdeleRing` instances) — that is
  §1.5's refactor, and it is why the row is 17 net lines and not 1.

### 1.4 The lanes

| order | who | steps | file | why |
|---|---|---|---|---|
| **1** | manager | G1 | insert `Adelic/ConstantTerm.lean`; delete 3 copies in `Cusp/SpectrumCarrier.lean`, `WeylIntegrable/Assembly.lean`, `InducedSectionMaximalCompact.lean` | the row cannot be *stated* generically before it, and the port's three specialisations are then derivable in one term |
| **2** | manager | G2 | insert `Adelic/RightConvolution.lean` | 14 lines, beside the law it generalises (`rightConv_comp_mul_left`) |
| **3** | **worker** | W1 | new `Adelic/RightConvRegularity.lean` | 450 lines of analysis; the order is [WORKORDER-AF5-rightconv-regularity.md](WORKORDER-AF5-rightconv-regularity.md) |

Orders 1 and 2 both edit a legacy hub, so they are one manager lane even though the files are
disjoint: each hub edit is a tree-wide re-elaboration (§1.5's build table) and they are cheaper
batched. Order 3 is a **new, 0-importer** module — cascade-free — and depends on 1 only.

### 1.5 The landing — the manager's layer

The set's 481 net lines split 31 / 450 between the manager and the worker. The manager's part is small
in lines and large in consequence: it is where the three duplicates died and where the read was
repaired.

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---:|---|
| G1 | `AutomorphicForm/Adelic/ConstantTerm.lean` (82 → **115**, +33: the theorem, 2 imports, 3 wires, prose) | 10 → **11 ok** / 0 / 0 | silent, **2.7 s** | clean |
| G1b | `Cusp/SpectrumCarrier.lean` (**−14**: `continuous_unipotentGL2_adele` deleted, call site rewritten) | — | silent, 6.5 s | — |
| G1b | `WeylIntegrable/Assembly.lean` (**−11**: `continuous_unipotentGL2'` deleted with its `-- pin:` marker, call site rewritten) | — | silent, 5.3 s | — |
| G1b | `InducedSectionMaximalCompact.lean` (**−11**: the `private` copy deleted, call site rewritten) | — | silent, 7.9 s | — |
| G2 | `AutomorphicForm/Adelic/RightConvolution.lean` (59 → **78**, +19: the theorem, `open MeasureTheory`, 3 wires, prose) | 5 → **6 ok** / 0 / 0 | silent, 3.2 s | clean |
| — | consumer probe `spec/AutomorphicFormSetAF5Consumer.lean` (**+59**, 4 examples, 2 zones) | — | 0 errors | — |
| — | `spec/old_check_stmts.py` register: **−2 `PORT_FILES` rows**, both modules now `spec-pin:`-wired | — | — | — |

**What the manager's layer consumed**: 2 rows / **49 silo** / **31 net new math lines written**, **36
lines of specialised proof deleted** (70 inserted − 47 deleted = net **+23** source lines across the
five modules, headers included), 6 wire lines, 2 legacy migrations, 0 new modules, 0 imports added to
the AF graph (2 mathlib imports into a mathlib-only leaf), 0 `Def_` nodes, 0 markers, no tree build.

**The refactor, in detail — and why it was forced.** The pin node is

```lean
theorem continuous_unipotentGL2 {R : Type*} [CommRing R] [TopologicalSpace R] [ContinuousNeg R] :
    Continuous fun x : R => AutomorphicForm.unipotentGL2 x
```

and the port turned out to hold **three** copies of its `R := AdeleRing (𝓞 F) F` instance:

| copy | module | visibility | lines |
|---|---|---|---:|
| `continuous_unipotentGL2_adele` | `Adelic/Cusp/SpectrumCarrier.lean:168` | public | 15 |
| `continuous_unipotentGL2'` | `Adelic/WeylIntegrable/Assembly.lean:255` | public (registered in `UNWIRED-PUBLIC`) | 14 |
| `continuous_unipotentGL2` | `Adelic/InducedSectionMaximalCompact.lean:490` | **private** | 13 |

Three copies of one 15-line proof, written at one type, in one tree — and the third is the FR-0095
shadow that has been polluting every read since SET-AF2. So the set's ground prep is the playbook's
"generalise near-duplicates, do not copy them" (§5): write the general statement once **where
`unipotentGL2` lives**, and let the three modules use it at their instance. The three call sites are
one term each:

```lean
(continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F))
```

`dedup --within` on the two edited modules: **0 clusters** (18 declarations). `move_dead --dry-run` on
both: **0 declarations / 0 lines**. The two deleted public names are gone from `spec/UNWIRED-PUBLIC.md`
(the register re-generates to 112 modules / 3,474 declarations); the only surviving reference is the
prose of [SET-AF1.md](SET-AF1.md):348, which is a record of what that set landed and is left as such.

**Two legacy migrations, and what they cost.** `Adelic/ConstantTerm.lean` (D0) and
`Adelic/RightConvolution.lean` (D4) are both `PORT_FILES`-wired. Touching them invokes the
instructions' legacy rule, so each got: its `spec-pin:` wire (the `Def_` it transcribes, the `Thm_`
wrapper and the `S_` copy for its new theorem), its `PORT_FILES` row **deleted** (its `SOURCES` rows
stay — removing a pin side can un-match other modules), a silent build, `dedup`, `move_dead`. No
build-time change: `ConstantTerm` 2.7 s, `RightConvolution` 3.2 s, and the modules' own dependents
re-elaborate in the same band as before.

**The cascade, priced not avoided** (playbook §5: build time is a scheduling fact, not a homing
argument):

| hub edited | dependent cascade | re-elaboration |
|---|---|---|
| `Adelic/ConstantTerm.lean` | 90 modules / 34,963 lines | ≈421 s |
| `Adelic/RightConvolution.lean` | 45 modules / 19,858 lines | ≈239 s |

That is the price of the mathematics' own home, and it is paid once: the three specialised copies were
*below* these hubs and had to be deleted at source either way. What is **not** paid is a tree build —
no `lake build` without arguments was run for this set (§6 gate 3).

**The measured read after the manager's layer** (this is the honest read now — no `--unport`):

| figure | before (corrected) | after G1+G2 | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 901 / 370,970 | **899 / 370,921** | −2 / −49 |
| `needed [literal]` | 914 / 374,445 | **912 / 374,396** | −2 / −49 |
| frontier F | 1,514 / 756,396 | **1,516 / 756,445** | +2 / +49 |
| ready rows, all namespaces | 66 / 22,656 | **71 / 26,301** | **+5 / +3,645** |
| leaves, all namespaces | 251 / 62,637 | **249 / 62,588** | −2 / −49 |
| `AutomorphicForm` ready rows | 37 / 17,312 | **42 / 20,957** | **+5 / +3,645** |
| `AutomorphicForm` leaves | 82 / 16,598 | **80 / 16,549** | −2 / −49 |
| withheld by the FR-0044 guard | 4 / 831 | **4 / 831** | — |
| `--selfcheck` | PASS | **PASS** | — |

The `+5 / +3,645` is exactly 471 + 290 + 1,246 + 1,248 + 390: the four rows the manager's two rows
ready, plus W1 itself becoming ready. **All five are gate-free** (§0.4). The `−49` on `needed` is the
two rows themselves; the leaf block moved by the same two.

### 1.6 W1's landing — one worker order, one module

[WORKORDER-AF5-rightconv-regularity.md](WORKORDER-AF5-rightconv-regularity.md) was dispatched as one
fresh session against the workorder and closed clean, no blocker and no round trip.

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---:|---|
| W1 | `Adelic/RightConvRegularity.lean` (**new, 530**: header 52 + 8 imports + **27 `private`** pin-prelude declarations + **1 public** headline) | **1 ok** / 0 / 0 / 0 own | silent, **5.6 s** fresh (olean deleted), zero warnings | clean |
| — | consumer zone C appended to `spec/AutomorphicFormSetAF5Consumer.lean` (4 → **9** examples, 3 zones) | — | 0 errors | — |

`dedup --within`: 28 declarations, **0 clusters**. `move_dead --dry-run`: reports 2 declarations /
5 lines, and **all five are a false positive** — `private abbrev instNG`, `private abbrev instNS` and
their two `attribute [local instance]` lines, which the tool cannot see as references (it resolves
liveness by dotted name prefix); real dead = 0, nothing moved (FR-0104).

**Deviations, all measured and all recorded rather than hidden** (no statement changed; the checker
hashes the headline at the wrapper's text):

1. **`set_option linter.style.haveILetI false in` on two declarations** (`contDiff_slice`,
   `continuous_rightConv`). The pin sets no option; its `letI := glBorel` / `haveI := borelSpace_…,
   isHaarMeasure_…` wall trips the port's style linter, so the build would not be silent. The
   `letI`/`haveI` themselves are kept — the same treatment, and the same reason, as the manager
   recorded for `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` (§4 item 2).
2. **`glArch_unipotent`/`glFin_unipotent` are stated with an explicit `R :=`.** The pin writes
   `unipotentGL2 ((a, b) : AdeleRing (𝓞 K) K)` and closes with `rw [unipotentGL2_coe]`; in the port
   `AdeleRing` is a semireducible `def` (not an `abbrev`), so `rw`'s keyed matching — which runs at
   *implicit* transparency — fixes the occurrence's `R` to the product type and the rewrite fails with
   `Application type mismatch: … expected to have type AdeleRing (𝓞 K) K`. Restating the argument as
   `unipotentGL2 (R := AdeleRing (𝓞 K) K) (a, b)` and closing by `ext i j; rw [AdelicLevel.gl{Arch,Fin}_apply];
   fin_cases i <;> fin_cases j <;> rfl` is the fix (FR-0105). Both are private; the downstream rewrites
   in `archEntries_slice` still key on them by name.
3. **No mathlib rename was needed.** v4.34 moved `ContDiff`'s exponent to `ℕ∞ω = WithTop ℕ∞`, so the
   pin's `(⊤ : ℕ∞)` lands as `∞` by coercion and `contDiff_infty.1 hΦ m` still elaborates; the whole
   catalogue the row depends on (`contDiff_zero`, `contDiff_succ_iff_hasFDerivAt`,
   `hasFDerivAt_integral_of_dominated_of_fderiv_le` — six non-`hs` arguments in the pin's order —
   `continuousAt_of_dominated`, `norm_integral_le_of_norm_le`,
   `IsCompact.eventually_forall_of_forall_eventually`, `image_eq_zero_of_notMem_tsupport`,
   `HasCompactSupport.intro'`, `Continuous.matrix_mul`/`.matrix_elem`, `ContDiff.fderiv_right`) kept its
   name and shape. This is the first AF row whose drift section is empty.
4. **The `local instance` wall is kept but is no longer load-bearing in v4.34** — a measured side fact
   for the next consumer: `local instance` is file-scoped, so a *downstream* module stating
   `ContDiff`/`Continuous` at `mixedEmbedding.mixedSpace K` gets `NormedAddCommGroup` from the global
   chain, **provided it opens `scoped Classical`** (the `Fintype` of the `IsReal`/`IsComplex` subtype
   needs `Classical.propDecidable`). That is why zone C's two `mixedSpace` examples carry
   `open scoped Classical ContDiff in`.

## 2. What the three rows say

### 2.1 W1 (471) — the operator's regularity

`rightConv K φ f` is continuous for `φ` continuous and `f` a factorizable test function (hence
continuous with compact support), and for every `g` the map

```lean
z ↦ rightConv K φ f (unipotentGL2 ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g)
```

is `C^∞` of order `Module.finrank ℚ K + 1` on the archimedean mixed space. The pin's proof is a
two-part development, and its shape is what the worker reproduced — **every trap below was either
transcribed as written or is the measured deviation §1.6 records**:

1. **a generic shape block** (private, 4 theorems + 3 helpers): dominated convergence under an
   integral whose parameter dependence is `Ψ (c a + L z)` — an affine `z`-dependence through a
   continuous linear map `L` — giving `Continuous` and then `ContDiff ℝ n` by induction on `n` with
   `contDiff_succ_iff_hasFDerivAt` and `hasFDerivAt_integral_of_dominated_of_fderiv_le`;
2. **the adèlic slice** (private, ~10 declarations): `archEntries ((n(z)·g)⁻¹ · y)` is affine in `z`
   with `sliceCD g y` as the two coefficient matrices, `glFin` is `z`-independent, the support bound
   is `(z, y) ↦ n(z)·g·y` applied to `closedBall z₀ 1 × tsupport f`, and the Haar re-indexation
   `integral_mul_left_eq_self` turns `rightConv` into the shape block's integral;
3. **continuity in `g`**: the `ε/δ` estimate on `tsupport f`, using that a compact set's
   `eventually_forall_of_forall_eventually` upgrades pointwise continuity in `(h, x)`.

The headline is then two lines: `obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn K f hf`
and the two parts of the pair.

### 2.2 G1 (28) — the unipotent embedding's continuity

Both matrix entries are affine in `x` and so is the inverse's entry `-x`, so `Units.continuous_iff`
plus `continuous_matrix` closes it — at *any* topological commutative ring with continuous negation,
which is the point (§3). The pin keeps its helper `unipotentGL2_inv` private; the port needs no
helper at all (`fun x => rfl` on the inverse's matrix).

### 2.3 G2 (21) — the translation law

`rightConv φ f (g·t) = ∫ x, φ (g·t·x) f x = ∫ x, φ (g·x) f (t⁻¹·x)`: substitute `x ↦ t·x` and use
`integral_mul_left_eq_self` (the Haar measure's left invariance), then `t⁻¹·t·x = x` and `mul_assoc`.
The whole proof is four lines of re-indexation; its value is that the archDeriv chain consumes it
three times.

## 3. Homes — one new module, two insertions, and the deletions

| step | home | why not the alternative |
|---|---|---|
| G1 | **insert** `Adelic/ConstantTerm.lean` | it is the module that *defines* `unipotentGL2` and its subject sentence is the unipotent subgroup; the statement needs only `[CommRing R] [TopologicalSpace R] [ContinuousNeg R]`, so it belongs at the bottom of the layer and nowhere else. A separate `UnipotentContinuity.lean` would be a shell module around one 15-line lemma whose subject is already there (playbook §5: "a module that only restates the engine's headlines" is not a module) |
| G1b | delete the three specialisations | the general statement is *above* them (it is in `ConstantTerm`, which all three import), so they are one-term corollaries; keeping them is exactly the "real mathematics left `private` and re-derived in the next theory" the playbook forbids. The two public ones were also the reason the pin node read as ported |
| G2 | **insert** `Adelic/RightConvolution.lean` | beside `rightConv_comp_mul_left` — the sibling law (that one moves a *left* multiplication out of `φ`, this one moves a *right* translation into `f`) |
| W1 | **new** `Adelic/RightConvRegularity.lean` | `RightConvolution.lean` is *below* the row's premises (`IsFactorizableTestFn`, `AdelicBox.continuous_ringEquiv_mixedSpace`, `AdelicLevel.gl{Arch,Fin}`), so insertion there is an import cycle — the one thing that vetoes a home. The new module sits above all of them and has **0 importers**, so it is cascade-free |

**Import direction, checked by hand.** `RightConvolution.lean` imports only
`NumberTheory/AdelicHaar/GeneralLinear`; the row needs `AutomorphicForm/Adelic/FactorizableTestFn`
(which is above `AdelicLevel` and `Adelic/Basic`), `NumberTheory/AdelicBox` (for
`continuous_ringEquiv_mixedSpace`), `NumberTheory/AdelicLevel/Projections` (`continuous_glArch`,
`continuous_glFin`) and `NumberTheory/AdelicLevel/Level`. `AutomorphicForm → NumberTheory` is the only
direction the tree has, so the home must be on the `AutomorphicForm` side and above those — hence the
new module, whose import list the work order fixes.

**The three tool false negatives, checked by hand** (recipe §3): (i) **name-anchored** — the port's
`continuous_unipotentGL2` copies are *specialisations*, so `port_advise` reads the pin node as new;
that is why G1 is priced at 17 and not at 1, and why the copies had to be found by reading
`grep -rn 'theorem continuous_unipotentGL2'`. (ii) **no mathlib** — the shape block's
`continuousAt_of_dominated`, `hasFDerivAt_integral_of_dominated_of_fderiv_le`,
`contDiff_succ_iff_hasFDerivAt` and `Complex.summable`-free analysis are all mathlib's; nothing to
substitute, but the worker must not re-derive them. (iii) **statement-anchored** — no port theorem has
weaker hypotheses than either of G2's or W1's statements, so there is no generalisation to reuse;
`twin_scan` says `new`, `new`, `new`.

## 4. Ground prep (the manager's) — done

1. `Adelic/ConstantTerm.lean`: `spec-pin:` ×3 (`Definitions/Def_AutomorphicForm_ConstantTerm.lean`,
   `Theorems/Thm_AutomorphicForm_continuous_unipotentGL2.lean`, its `P2M/Sol/S_` copy), two mathlib
   imports (`Mathlib.Topology.Instances.Matrix`, `Mathlib.Topology.Algebra.Group.Units`), the
   `spec-pin:`-wired theorem, the header's subject sentence extended.
2. `Adelic/RightConvolution.lean`: `spec-pin:` ×3 (its `Def_`, the `Thm_` wrapper, the `S_` copy),
   `open MeasureTheory`, `set_option linter.style.haveILetI false in` on the theorem (the pin's
   `letI`/`haveI` wall, kept — playbook/§8 convention), the header's subject sentence extended.
3. `Cusp/SpectrumCarrier.lean`, `WeylIntegrable/Assembly.lean`,
   `InducedSectionMaximalCompact.lean`: the three duplicate proofs deleted, call sites rewritten to
   `(continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F))`. `Assembly.lean`'s `-- pin:` provenance
   marker for the deleted `'`-copy went with it.
4. `spec/old_check_stmts.py`: the two `PORT_FILES` rows deleted (both modules are `spec-pin:`-wired
   now); their `SOURCES` rows untouched.
5. `spec/AutomorphicFormSetAF5Consumer.lean`: the consumer zone (§6 gate 5).
6. Nothing else: **no `Def_` node, no promotion of a pin-private helper, no marker row, no new
   `decl_markers.tsv` entry.**

## 5. The traps (for W1, 450 lines)

**The five the pin pays for, in the order they bite.**

1. **`private abbrev Par` and the local instances.** The pin opens the slice with
   `private abbrev instNG : NormedAddCommGroup (mixedEmbedding.mixedSpace K) := inferInstance` and
   `attribute [local instance] instNG` (and the same for `NormedSpace ℝ`). Those two lines are
   load-bearing: `hasFDerivAt_integral_of_dominated_of_fderiv_le` needs a *normed* structure on the
   mixed space, which the `IsometryEquiv` route gives but which is not the instance found by search at
   that type. Transcribe them verbatim (`local instance`, not `haveI`).
2. **`L := sliceL K` is the `(0, (0, z))` embedding.** `slicePsi` evaluates `Φ` on
   `q.1 + q.2.2 * q.2.1`; the shape block is stated for an arbitrary `X →L[ℝ] P`, and the pin
   instantiates it with the *second* right injection into `Par K`. Do not re-derive the shape block
   for the `Par` type — instantiate it (that is why `contDiff_integral_shape` carries `n` as an
   explicit argument before its implicit block; keep that order or the induction breaks).
3. **The `n = 0` case needs `contDiff_zero` + `continuousAt_of_dominated`, not a lemma about
   integrals of `C^0` functions** — and the `succ` case needs the *pair* `(hH, hH')` (the shape for
   `Ψ` and for `fderiv ℝ Ψ`) because `hasFDerivAt_integral_of_dominated_of_fderiv_le` asks for the
   derivative integrand's own domination.
4. **`archEntries_slice` is where `entry_affine` is used.** The matrix identity
   `A * !![1, a; 0, 1] * B = A*B + a • (A * !![0,1;0,0] * B)` must be stated as an *entry*
   identity (`(…) i j = …`) — `Matrix.mul_add`/`Matrix.add_mul` do not rewrite under `Units.val_mul`
   without it. Then `map_neg`/`neg_mul`/`← mul_neg` finish the sign.
5. **`glFin_slice` needs `unipotentGL2_zero` and `inv_one`** in that order: `n(z)`'s finite part is
   `unipotentGL2 0 = 1`, so the finite test factor's argument collapses to
   `(glFin g)⁻¹ * glFin y` *independently of `z`* — that is exactly what makes the integrand's
   `z`-dependence affine, i.e. the mathematical content of the row.

**Two build traps.**

6. **`fun_prop` and `fin_cases`.** The pin's `hval` blocks are
   `fin_cases i <;> fin_cases j <;> simp <;> fun_prop`; that is also the shape of the port's *deleted*
   specialised copies, so a `simp`-only rewrite will leave the `1`-entry open.
7. **`exact_mod_cast h` at the end.** The `ContDiff` order is `↑(Module.finrank ℚ K + 1)` in `ℕ∞`
   against the pin's `Module.finrank ℚ K + 1` in `ℕ`; the pin closes with `exact_mod_cast`, keep it
   (a `Nat.cast` rewrite through `ContDiff ℝ n` does not fire).

**One thing NOT to do.** The pin's four shape theorems are `private` **in this file only** (the
`port once` block is empty). Keep them `private` here — this is *not* the FR-0101 case (no other pin
file copies them, and no port module states them). Run the recipe's §5 surface gate at review to check
that verdict, but expect it to confirm `private`.

**A `sorry`-shaped risk.** The row's `hsupp` (compact support of the `z`-parametrised integrand) is
proved by *image of a compact set*, not by a support argument: the map is
`(z, y) ↦ n(z)·g·y` on `closedBall z₀ 1 × tsupport f`, and the membership proof must go through
`mul_inv_cancel_left`. A worker who tries to bound the support directly will spend the round.

## 6. The gates, per step

As in SET-AF1–AF4 and the recipe §6:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, every added declaration
   `ok` (or an `own:`/`pin:` row, which the manager writes — none here). The manager's two modules
   read **11 ok / 0 / 0** and **6 ok / 0 / 0**; W1's module reads **1 ok / 0 / 0** — and *only* one row,
   which is the measured form of the `private` decision: `check_port` skips port-private declarations
   (`if priv: continue`), so the pin's 27 private prelude declarations produce neither `ok`/`promoted`
   rows nor `missing` ones. A brief that expects `promoted` rows here would read "1 ok" as a failure.
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake build` under `flock`/`timeout`, silent, **zero warnings**; no tree build, no
   dependents. A `Replayed` line is not evidence that the `.olean` exists (FR-0033).
4. `dedup.py --within --module <module>` — report clusters, do not refactor; `move_dead.py --dry-run`
   — expect 0 dead.
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; **no `set_option maxHeartbeats`** (the
   pin sets none on this file — if the module needs one, that is a finding to report, not a fix).
6. A `spec/` consumer zone with a real composition (no `#check`s): `spec/AutomorphicFormSetAF5Consumer.lean`
   is green, three zones, 9 examples, **0 errors** — zone A derives the *specialisation* the deleted
   copies provided and the shifted-continuity composition; zone B composes the translation law with
   itself; zone C composes W1's first component with `continuous_unipotentGL2` (adelic), re-indexes it
   through the translation law, and weakens the second component to `ContDiff ℝ 1` at `g = 1`. Every
   zone is load-bearing: deleting any of the three declarations breaks it.

## 7. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. **the cut** | **three rows / 520 silo / 481 net**, one manager lane (G1+G2) then one worker order (W1) | it is the shelf's highest return per silo (7,007 / 520 ≈ 13.5) and it is *one* operator's calculus |
| 2. **the instrument** | **readiness return, third time** — and this time the top of the table is an *engine*, not a definition leaf | SET-AF4 chose a def leaf because the return was 5,407 for 49 lines; here the two chosen rows are the *entry* to the largest deferred family (the arch-derivative chain), so the return lands on rows this column will write next |
| 3. **G1's home** | **`Adelic/ConstantTerm.lean`, public, general**, with the three specialised copies deleted | the alternative (keep the specialisations, add the general one) would leave 42 lines of duplicate proof and the FR-0095 shadow alive; the alternative (a new `UnipotentContinuity.lean`) is a shell module |
| 4. **the legacy rule** | **migrate both hubs in the same touch** (wires in, `PORT_FILES` rows out) | the instructions make this mandatory on any legacy touch, and both modules are on the handover path anyway |
| 5. **the arch-derivative chain** | **defer to the set after W1** — its 8 leaves are **1,510 silo → 1,001 net** (priced: 17 duplicate copies, 168 boilerplate, 324 already in the port, 51 trusted substitutions), and they stand on the two headlines G2 readies | the chain is the column's big proof (4,004 silo as a family); porting it in this set would treble the order's size |
| 6. **`finite_setOf_algebraMap_mem_of_isCompact` (123 → 2,113)** | **defer to SET-AF6 as the leading candidate** | the rational-torus/unipotent Haar block is one story of six rows, but its own read must settle the `RationalCentreUnipotentQuotient` gate (SET-AF4 §9) — this set does not touch it |
| 7. **the three definition gates** (`placeEmbed` 8, `RationalCentreUnipotentQuotient` 13, `FnTwist.isSmoothVector_rightTranslationFn_mul` 22) | **still deferred, still one sweep of 43 pin lines** | this set has no definition gate at all (§0.4), so there is nothing to bundle them with; they close the 1,043 / 179 / 325 rows' writability |
| 8. **the dispatch** | **manager first (one session), then one worker order** — taken, and it closed clean (§1.6) | W1 states over G1; the worker's module is new and 0-importer, so no file conflict and no hub edit |

Calls 1–4 and 5–8 were taken as recommended; §1.5 records the manager's landing, §1.6 the worker's,
and §8 the two re-reads.

## 8. Reproduce, and the two measured re-reads

```bash
cd tools/deps
# §0.1 — the read, and the corrected one (the correction is retired after this landing, §8.2)
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af5.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 \
    --unport AutomorphicForm.continuous_unipotentGL2 --json > build/shelf-af5-corr.json
python3 frontier.py --selfcheck
# §0.3 — the readiness return (a graph query, not a flag)
python3 ../../tmp/af5_return.py            # writes build/af5-return*.json + the corrected shelf
# §0.4 — the gate, twice: the wrapper's Def_ closure, then the FR-0099 census
python3 spec/gate_scan.py --pin Definitions/Def_AutomorphicForm_FactorizableTestFn.lean \
    --rows S_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
# §1.3 — the pricing
python3 port_advise.py --nodes <the three> --json build/af5-rc-advise.json
python3 port_plan.py --json build/af5-rc-advise.json          # 481 net, 0 duplicate, 0 in port
python3 twin_scan.py --node <each of the three>               # new × 3
# §1.5 — the landing's checks
cd ../lean
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/ConstantTerm.lean \
    FLTForHuman/AutomorphicForm/Adelic/RightConvolution.lean
python3 ../tools/deps/dedup.py --within \
    --module FLTForHuman/AutomorphicForm/Adelic/ConstantTerm.lean \
    --module FLTForHuman/AutomorphicForm/Adelic/RightConvolution.lean
python3 ../tools/deps/move_dead.py --source FLTForHuman/AutomorphicForm/Adelic/ConstantTerm.lean \
    --target Reserve/AutomorphicForm/Adelic/ConstantTermDead.lean --dry-run
timeout 300 python3 spec/old_check_stmts.py        # corpus: 6,949 identical, 3 mismatch, 18 missing
```

**Two readings of the corpus number, so nobody reads a regression into it.** `old_check_stmts.py`
is the *legacy* sweep and it reads `PORT_FILES` only — it **ignores `spec-pin:` headers** (the
`check_port` docstring says so). So the set changes the corpus in three ways that do not show up in
that one line: the two migrated modules (17 declarations: 11 + 6) leave the legacy sweep and enter
`check_port`'s, which is the intended handover and the same move SET 3–4's seven migrations made; the
legacy sweep's own figure is unchanged at 6,949 / 3 mismatch / 18 missing, and **none of the 3 + 18 is
in a module this set touched** — they are `AlgebraicCurve/Defs/{Correspondence,PlaceEvaluationAlgebra}`,
`AlgebraicCurve/Differential/PushPull`, `Elliptic/PeriodPair/JLine` and
`ModularCurve/ModularPolynomialFibreTwo`, i.e. the AC column's carried issues; and W1's new module is
**not** in the legacy sweep at all, by design — `check_port` reports its 1 `ok` and its 27 private
prelude declarations are skipped (`if priv: continue`), which is the whole reason the `private`
decision costs nothing in checker rows.

**What the set consumed** (measured, §1.5 + §1.6): 3 rows / 520 silo / **481 net new math lines** (31
manager + 450 worker, written as 530 module lines including the header and the prelude's docstrings); 2
inserts, 1 new module, 6 + 2 wire lines; **36 lines of specialised proof deleted**; 2 legacy
migrations; 0 `Def_` nodes; 0 markers; 0 tree builds.

**The W1 forecast was exact to the line.** The brief predicted the post-landing read before the order
was dispatched; the measured column is `frontier.py` re-run on the landed tree, **with no `--unport`
and no correction**:

| figure | after G1+G2 | forecast for W1 | **measured after W1** |
|---|---:|---:|---:|
| `needed [F terminal]` | 899 / 370,921 | 898 / 370,450 | **898 / 370,450** ✓ |
| `needed [literal]` | 912 / 374,396 | 911 / 373,925 | **911 / 373,925** ✓ |
| frontier F | 1,516 / 756,445 | 1,517 / 756,916 | **1,517 / 756,916** ✓ |
| ready rows, all namespaces | 71 / 26,301 | — | **71 / 29,663** |
| leaves, all namespaces | 249 / 62,588 | — | **249 / 62,588** ✓ |
| `AutomorphicForm` ready rows | 42 / 20,957 | 42 / 24,319 | **42 / 24,319** ✓ |
| `AutomorphicForm` leaves | 80 / 16,549 | — | **80 / 16,549** ✓ |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | **4 / 831** ✓ |
| `--selfcheck` | PASS | PASS | **PASS** (1,352 `Thm_` / 1,517 names) |

The set's whole arc is therefore: `needed` **901 / 370,970 → 898 / 370,450** (−3 / −520, i.e. exactly
the three rows), the frontier **+3 / +520**, and the `AutomorphicForm` shelf **37 / 17,312 → 42 /
24,319** ready with **82 → 80** leaves. Every figure is the arithmetic of the cut; none came from a
consumer count or a definition gate.

**The row it readies is the port's largest cusp-subrepresentation engine**:
`AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep` (**3,833 silo**, `NumberField`-free, 6
`Def_` modules, 0 missing) — it is the row that says a right-convolved function stays in the cusp
subrepresentation, i.e. the `AutomorphicForm` analogue of the `RightConvComm/` family. It is the
column's **next** proof after the arch-derivative chain, and its brief must price it alone.
`isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_…` (290) already became
ready with G1 and is the cheap one of the five.

### 8.1 Where the column goes after this set

Four candidates, in the order this read ranks them (§8's measured re-read confirms the ranking and
adds 3, which W1 itself readied):

1. **the arch-derivative chain** (8 leaves / 1,510 silo / **1,001 net**, `return 1,443`): the two
   `archDerivAt{,Complex}_rightConv_eq_rightConv_deriv_…` headlines (1,246 + 1,248) are the *ready*
   end of it; the eight leaves are `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` (401 →
   1,227), the two commutator/Casimir rows (208 + 133 + 110), the two character leaves (184 + 250) and
   the two `apply_mul_arch{Real,Complex}GLAt_…` (117 + 107). It is the column's one coherent big proof
   and it wants a single order;
2. **`NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact`** (123 → six rows / 2,113): the
   rational torus/unipotent Haar block — one story, cheapest per line of readiness, but gated by
   `RationalCentreUnipotentQuotient` (13 pin lines) for one of its six;
3. **`rightConv_rightTranslate_mem_of_isCuspSubrep`** (3,833): *ready as of W1* — the row
   `isCuspidalFn`/`rightConv` engine that W1's headline is the premise of. Third by ready silo and the
   cheapest of the three to start, since its only unported premise has just landed;
4. **`bigCell_eq_sum_pureTensor_of_flat_family`** (5,407, ready since SET-AF4, return 0): the cone's
   largest single row and the one SET-AF4 explicitly left "a row of its own". It is ready and
   gate-free; it is a set by itself.

The two deferred AF *families* from SET-AF4 §7 — `LocalIntertwining` (8 rows / 1,578) and
`CuspidalConstituent` (9 rows / 1,593) — remain the column's proof work at `return 729` and `28`; they
are still below the three above by return per line, and neither is unblocked by this set.

### 8.2 The read is repaired, and that is a deliverable

Before this landing every read since SET-AF2 needed the `--unport AutomorphicForm.continuous_unipotentGL2`
correction, because a `private` helper carried an unported pin node's last name (FR-0095). The general
statement and the deletions remove the *cause*: the last-name tier now matches a public declaration
whose statement the checker diffs against the `Thm_` wrapper and reports `ok`. §1.5 measured the
instrument's read and the corrected read as the same read after the landing, and `--selfcheck` PASSes.

The rule this leaves (FR-0102): **a name shadow is closed by porting the node, not by suppressing the
tool** — `--unport` is the diagnostic, and the promotion-plus-dedup is the cure. A brief that carries
an `--unport` line for three sets in a row should treat it as a work item, not as a constant.

## 9. What this set does not do

- **The archimedean-derivative chain** (§7 call 5, §8.1): its 8 leaves / 1,510 silo (1,001 net) are
  on the shelf, and its two headline rows (`archDerivAt{,Complex}_rightConv_eq_rightConv_deriv_…`,
  1,246 + 1,248) are **ready** thanks to G2 — they are the next set's core and none is written here.
  This is the set's most important *negative*: it delivers the door, not the chain.
- **`rightConv_rightTranslate_mem_of_isCuspSubrep`** (3,833): ready as of W1 (§1.6), gate-free (§0.4),
  unwritten — the column's largest single ready row after the chain.
- **The three definition gates** (`placeEmbed` 8, `RationalCentreUnipotentQuotient` 13,
  `FnTwist.isSmoothVector_rightTranslationFn_mul` 22): deferred again, still one 43-line sweep (§7
  call 7). This set needed none.
- **The six rows `finite_setOf_algebraMap_mem_of_isCompact` readies** (§7 call 6): deferred to SET-AF6.
- **Anything behind the prunable complex-analytic subject**: the withheld 4 / 831, unchanged.
- **No new `Def_` module, no promotion of a pin-private helper, no marker row, no tree build.** The two
  legacy migrations are the whole metadata surface of the set.

## Appendix A — the 37 ready `AutomorphicForm` rows, with each one's readiness return

As of the read that chose the cut (§0.1, corrected read). `return` = the unported rows of the D–S cone
whose **only** missing premise is this row; `lev` is `leverage / leverage_project`. Both of this set's
rows are leaves in this read, so they appear in Appendix B, not here — every row of the two blocks is
named, and the ones the set does not cut are deferred in §7/§9.

| ready row (`AutomorphicForm.` dropped) | silo | prem | lev | return |
|---|---:|---:|---:|---:|
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14 / 63 | 1014 |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4 / 10 | 990 |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1 / 1 | 56 |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2 / 3 | 28 |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1 / 6 | 23 |
| `bigCell_eq_sum_pureTensor_of_flat_family` | 5407 | 4 | 3 / 5 | 0 |
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1 / 1 | 0 |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1 / 1 | 0 |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1 / 3 | 0 |
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | 624 | 3 | 2 / 5 | 0 |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1 / 2 | 0 |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1 / 1 | 0 |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2 / 4 | 0 |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | 431 | 3 | 1 / 5 | 0 |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1 / 6 | 0 |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1 / 1 | 0 |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1 / 1 | 0 |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | 325 | 2 | 4 / 15 | 0 |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2 / 2 | 0 |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1 / 1 | 0 |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | 257 | 1 | 3 / 20 | 0 |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2 / 27 | 0 |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1 / 1 | 0 |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2 / 4 | 0 |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1 / 3 | 0 |
| `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul` | 208 | 2 | 4 / 12 | 0 |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5 / 8 | 0 |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1 / 1 | 0 |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2 / 2 | 0 |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1 / 11 | 0 |
| `SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient` | 146 | 1 | 1 / 2 | 0 |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2 / 5 | 0 |
| `isKfSmooth_rightConv` | 70 | 1 | 7 / 21 | 0 |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1 / 1 | 0 |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1 / 1 | 0 |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1 / 1 | 0 |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3 / 8 | 0 |
| **37** | **17,312** | | | |

## Appendix B — the 82 `AutomorphicForm` leaves, with each one's readiness return

Same read. A leaf has no premises, so it can never reach `F` and the plain `--ready` view drops it
(recipe §0: `--include-leaves` is part of the read). **◀** marks the set's two rows.

| ◀ `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` | 21 | 0 | 17 / 48 | 2884 |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | 0 | 3 / 8 | 1445 |
| `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` | 401 | 0 | 8 / 9 | 1443 |
| ◀ `continuous_unipotentGL2` | 28 | 0 | 8 / 122 | 761 |
| `LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 362 | 0 | 1 / 1 | 465 |
| `LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | 0 | 1 / 1 | 264 |
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 0 | 3 / 4 | 169 |
| `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | 0 | 5 / 18 | 133 |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 0 | 7 / 20 | 113 |
| `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | 0 | 2 / 14 | 108 |
| `whittakerCoefficient_unipotentGL2_mul` | 123 | 0 | 17 / 54 | 84 |
| `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 0 | 1 / 1 | 25 |
| `constantTerm_add` | 13 | 0 | 1 / 2 | 14 |
| `constantTerm_smul` | 11 | 0 | 1 / 1 | 11 |
| `gl2Complex_whittaker_system_of_casimir_pair_of_unipotent_covariant_of_circleWeight_of_ktype` | 695 | 0 | 2 / 2 | 0 |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 0 | 2 / 4 | 0 |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 0 | 1 / 1 | 0 |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 0 | 2 / 2 | 0 |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 0 | 1 / 3 | 0 |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 0 | 1 / 2 | 0 |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 0 | 2 / 15 | 0 |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 0 | 2 / 7 | 0 |
| `hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex` | 404 | 0 | 2 / 2 | 0 |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 0 | 3 / 4 | 0 |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 0 | 1 / 2 | 0 |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 0 | 1 / 1 | 0 |
| `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` | 347 | 0 | 1 / 1 | 0 |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 0 | 1 / 2 | 0 |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 0 | 2 / 3 | 0 |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 0 | 3 / 4 | 0 |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 0 | 1 / 1 | 0 |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 0 | 1 / 1 | 0 |
| `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt` | 298 | 0 | 2 / 3 | 0 |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 0 | 5 / 10 | 0 |
| `archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` | 250 | 0 | 2 / 2 | 0 |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 0 | 1 / 1 | 0 |
| `LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift` | 219 | 0 | 1 / 1 | 0 |
| `archDerivAt_commutator_of_isArchSmoothAt` | 208 | 0 | 1 / 4 | 0 |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 0 | 4 / 5 | 0 |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 0 | 1 / 1 | 0 |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 0 | 1 / 4 | 0 |
| `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` | 184 | 0 | 8 / 14 | 0 |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 0 | 1 / 1 | 0 |
| `LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift` | 179 | 0 | 1 / 1 | 0 |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 0 | 1 / 1 | 0 |
| `LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | 170 | 0 | 1 / 1 | 0 |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 0 | 1 / 5 | 0 |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 0 | 1 / 1 | 0 |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 0 | 8 / 19 | 0 |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 0 | 1 / 2 | 0 |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 0 | 4 / 8 | 0 |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 0 | 2 / 2 | 0 |
| `LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | 147 | 0 | 1 / 1 | 0 |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 0 | 1 / 14 | 0 |
| `RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery` | 141 | 0 | 1 / 1 | 0 |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 0 | 1 / 3 | 0 |
| `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` | 133 | 0 | 2 / 3 | 0 |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 0 | 1 / 1 | 0 |
| `apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` | 117 | 0 | 2 / 2 | 0 |
| `LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | 0 | 1 / 1 | 0 |
| `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` | 110 | 0 | 2 / 3 | 0 |
| `continuous_whittakerCoefficient` | 108 | 0 | 3 / 14 | 0 |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 0 | 2 / 3 | 0 |
| `apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` | 107 | 0 | 2 / 3 | 0 |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 0 | 1 / 1 | 0 |
| `whittakerCoefficient_sum_smul_of_continuous` | 86 | 0 | 10 / 17 | 0 |
| `SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient` | 81 | 0 | 1 / 2 | 0 |
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 0 | 2 / 2 | 0 |
| `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 0 | 1 / 1 | 0 |
| `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 0 | 2 / 4 | 0 |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | 0 | 3 / 22 | 0 |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 0 | 1 / 1 | 0 |
| `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 0 | 1 / 1 | 0 |
| `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 0 | 2 / 3 | 0 |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 0 | 2 / 2 | 0 |
| `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 0 | 1 / 2 | 0 |
| `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 0 | 1 / 1 | 0 |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 0 | 2 / 2 | 0 |
| `IsKfSmooth.finite_smul_image_of_isCompact` | 40 | 0 | 3 / 4 | 0 |
| `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 0 | 1 / 2 | 0 |
| `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 0 | 2 / 10 | 0 |
| `exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 0 | 1 / 1 | 0 |
| **82** | **16,598** | | |
