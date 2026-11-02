# SET-AF7 — the big-cell expansion: a mechanical whole-node transcription

**Status: mechanically transcribed (manager, 2026-11-02); 16 sites from green; the finishing order is
[WORKORDER-AF7-bigcell.md](WORKORDER-AF7-bigcell.md).** This set is unlike AF1–AF6 in kind: it is not a
selection of rows but the **whole of the cone's largest node**, ported by transcription rather than by
judgement, and it is the column's test of the rule that porting effort is not proportional to size.

The row is `AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family` — **5,407 silo**, ready since
SET-AF4, premises 4, leverage 3 / 5, readiness return **0**. It is the structural input of the
Rankin–Selberg machinery: a flat family's big cell is a sum of pure tensors.

## 0. What the node is

| | |
|---|---|
| pin file | `P2M/Sol/S_AutomorphicForm_bigCell_eq_sum_pureTensor_of_flat_family.lean`, **5,407 lines** (285 KB) |
| declarations | **458** — **one public** (`solution`, 174 lines) and 457 `private`, at the pin's own inner namespaces (`BigCellExpansion.{Height, Transport, RealPlaces, Iwasawa, PlaceMeasure, CellFactor, ArchFactor, FiniteShell, FlatValue, …}`, plus a file-local `NumberField`) |
| shape | median declaration **6 lines**, mean 11.7; **394 of 458 are ≤ 20 lines**; three exceed 100 (161, 132, 86); the top 20 declarations are 26% of the file — a *wide* development, not one deep proof |
| slack | 819 blank lines, 42 boilerplate (imports/`p2m`/`set_option`) |
| `port_advise` | 0 duplicate copies, **612 lines already in the port** (56 substitutions: `adelicHeight_*` in `InducedSectionFlat`, `ArchKFiniteFamily`, `ArchCompactOrbit`, `AdelicHaar/PlaceMeasure`), **4,753 net** |
| predicted dead tail | **31 declarations / 833 lines** are never referenced again in the pin (measured by occurrence count) — that is `move_dead`'s work after the fact, not a reason to curate 448 lemmas up front |

**Why one module and not five.** All but one declaration is `private`, i.e. file-local: there is
nothing to *decide* per lemma, and no public surface to design. Splitting the pin's order into subject
modules would force a visibility analysis for every cross-section dependency (the pin's sections call
across freely) and multiply the wiring for no mathematical gain. The pin's own namespaces already give
the structure inside one module. The recipe's "one module per mathematical role" is satisfied by the
pin's inner namespaces being distinct *within* the file.

## 1. The mechanical transcription (done)

`FLTForHuman/AutomorphicForm/Adelic/BigCellExpansion.lean` — **5,594 lines** (the pin's 5,407 + header,
imports and the open/`set_option` translation), **471 `private` + 1 public headline**.

The transformation, applied by script, is exactly the "strip the wrapper/boilerplate" list:

| pin | port |
|---|---|
| `import Mathlib` / `Definitions.*` / `Theorems.*` / `P2M.Util` | 11 explicit port imports + `Mathlib.Analysis.Fourier.AddCircle` |
| `namespace P2MW.S_<stem>` (+ 248 fully-qualified self-references) | `namespace AutomorphicForm` (prefix stripped) |
| `p2m_open "A B~h1 C"` (28×) | `open A` / `open B (h1)` / `open C`, each with `open scoped` |
| `p2m_open_scoped "X"` | `open scoped X` |
| `p2m_export "ns" "name"` (3×) | dropped; the declaration is stated at its own name (`coe_mul`) |
| `p2m_reactivate "ns …"` (85×) | dropped — they re-activate the file's **own** namespaces, which contain no scoped instances |
| `attribute [-instance] …`, `attribute [-simp] …` | dropped (they name pin-generation-only constants) |
| `if_pos` / `if_neg` (13 + 13) | `ite_eq_left` / `ite_eq_right` (v4.34) |
| `theorem solution` + the pin's 152-line statement | the `Theorems/` wrapper's statement verbatim (78 lines), the pin's proof kept |
| — | `set_option linter.style.haveILetI false` (85 `letI := glBorel` walls), `set_option linter.deprecated false` **temporarily** — the finishing order removes it |

**What it costs to elaborate — the measurement this set exists for.** A full pass over the 5,594-line
module is **19.4 s wall / 66 s user** (a *failing* pass; a green one is the same order). That is
**~290 lines/s**, i.e. *cheaper per line* than the column's own modules (`ArchCasimir` 1,431 lines in
8.2 s ≈ 175 lines/s, `PeterssonSlabPairing` 1,258 in 9.6 s ≈ 131/s), and far below the project's
2-minute ceiling. The fix loop for the biggest node in the cone is therefore *faster* than for a
1,200-line row — the size was never the cost.

## 2. What remains: 16 sites, eight classes

All v4.34 drift or port-side renames; none is a mathematical gap. The inventory (with the error text
and a suggested fix per site) is the work order's §3. In summary:

| class | sites | nature |
|---|---|---|
| `rfl` no longer closes a `Matrix.of`/`Pi` defeq | 1998 (×2), 2004 (×2) | `(of f i j).1 v` vs `1`/`0` — 4.34 stopped unfolding `of_apply` definitionally; `simp only [of_apply, …]` |
| `BorelSpace w.Completion` not synthesized | 2623, 2628 | the pin's deactivation/reactivation pair; the port supplies the instance locally |
| `Completion.extensionEmbeddingOfIsReal` / `piCongrLeft` no longer defeq | 2650, 2651, 2662 | `rfl` → `simp`/`exact` with the new lemma shape |
| a `Set`-membership argument shape changed | 3056, 3067 | `∩ ⋂ k, t k = ∅` — `rw` → `simp only` |
| mathlib renames (`one_apply_eq`, `Finset.prod_ite`) | 3105, 3481 | qualify (`Pi.one_apply_eq`) / rewrite the `simp` set |
| a port-side simp lemma missing (`val_finitePartUnits`) | 3639, 3641 | SET-AF4 landed `finitePartUnits`; the `val_` lemma is stated locally |
| a ported theorem under another home (`modulus_adicCompletion_eq_nnnorm`) | 5201 | it is in `EisensteinGeneral/LocalRamShells`; import + rename |
| two `unsolved goals` | 843, 5200 | the deprecated lemma's conclusion changed; close by hand |

## 3. The gates for the finishing order

1. `lake env lean` silent, then the module's own `lake build` under `flock`/`timeout 280`.
2. `check_port --force` → **1 ok / 0 mismatch / 0 missing** (the pin's 457 private declarations are
   invisible to it, as everywhere else).
3. `#print axioms` → `[propext, Classical.choice, Quot.sound]`.
4. `dedup --within` and **`--cross`** (the node's 612 ported lines are the cross-module overlap to
   check); `move_dead` → the predicted 31 declarations / 833 lines, triaged by the rule **dead
   mathematics → `Reserve/`; a duplicate or non-mathematics → delete**.
5. Zero warnings; no `set_option maxHeartbeats`; the two temporary `set_option` suppressions of §1
   reduced to the documented `haveILetI` one.
6. A `spec/AutomorphicFormSetAF7Consumer.lean` zone with a real composition (no `#check`).

## 4. What this set does not do

- **It does not touch the eight arch-derivative leaves** (SET-AF6 §9's deferral, 1,510 silo / 1,001
  net, return 1,443) — that remains the column's cheapest *unblocking* set, and this one returns 0.
  The two are independent.
- **It does not split the node across modules**, on purpose (§0).
- **It does not curate the 448 lemmas.** That is the point: the mechanical pass plus a dedup at the end
  is the whole strategy, and §1's 19.4 s is why it is affordable.

## 4.1 The read after the landing (§7 of the recipe)

`frontier.py --ds --ready --include-leaves` on the landed tree, no `--unport`, no correction:

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 896 / 367,956 | **895 / 362,549** | −1 / **−5,407** ✓ |
| `needed [literal]` | 909 / 371,431 | 908 / 366,024 | −1 / −5,407 |
| frontier F | 1,519 / 759,410 | **1,520 / 764,817** | +1 / +5,407 |
| ready rows, all namespaces | 71 / 28,162 | 70 / 22,755 | −1 / −5,407 |
| `AutomorphicForm` ready rows | 42 / 22,818 | **41 / 17,411** | −1 / −5,407 |
| `AutomorphicForm` leaves | 80 / 16,549 | 80 / 16,549 | — |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |
| `--selfcheck` | PASS | PASS | — |

The whole delta is the row's own silo: this set readies nothing (return 0), which is what it claimed
before it was cut.

## 5. The finishing order (WORKORDER-AF7), as executed

**Landed.** `FLTForHuman/AutomorphicForm/Adelic/BigCellExpansion.lean`, **5,176 lines** after §5.1's
sharing pass (5,445 as the worker left it), green:
`lake env lean` silent (18.5 s), the module's own `lake build` 21 s and silent, `check_port --force`
**1 ok / 0 mismatch / 0 missing**, `#print axioms` on the headline
`AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family`
`[propext, Classical.choice, Quot.sound]`, **zero warnings**, no `sorry`/`admit`/`axiom`/
`native_decide`/`maxHeartbeats`, and exactly one `set_option` (`linter.style.haveILetI false`, the
pin's 85 `letI` walls, documented in the header). The headline is *one* public declaration and the
other 463 are `private`, as in the pin.

**The sixteen sites, and what each needed.** All sixteen are v4.34 drift or port-side renames; none
changed a statement. The full list is in the module's header; the two that generalize are

* the *`Matrix.of` opacity* class (sites 1–5): `Matrix.of f i j` no longer reduces where the
  `↑`-coercion of `InfinitePlace.Completion` leaves the term ill-typed at `implicit` transparency,
  so `simp only [Matrix.of_apply]` is reported **unused** and does nothing. Three `rfl`-stated entry
  lemmas (`kFval_entry`, `kFinv_entry`, `projFin_mapMatrix_inclMatrixMap_apply`) put the projection
  back at exactly the shape the pin's `rfl` used;
* the *`MeasurableEquiv` wrapper* class (sites 8–10): `mR`/`mC` are no longer syntactically
  `extensionEmbedding(OfIsReal)`, so two `:= rfl` bridge lemmas carry the step and the surrounding
  `rfl`s become `Eq.trans`.

`Cell` was changed from the pin's `def` to `abbrev` (site 14): `Finset.prod_boole`'s pattern no
longer matches a `def` type alias at `implicit` transparency. That is the only kind change to a
declaration; it is `private`, no statement text moved, and it is the natural spelling for a type
alias.

**Dedup.** `dedup.py --within` on 480 declarations: **2 clusters**, the pin's own
`adele_one_snd`/`adele_zero_snd` stated twice in two namespaces (`Iwasawa`, `QuotientChar`) — kept
twice, as the pin has them, because merging them would put a cross-namespace reference into a
`private` local API the pin deliberately kept separate.

`dedup.py --cross` against the ported prelude (`InducedSectionFlat`, `ArchKFiniteFamily`,
`ArchCompactOrbit`, `PlaceMeasure`, `AdelicHeight`): **31 clusters / 489 removable lines**. Triage:

| disposition | clusters | why |
|---|---|---|
| **fixed** (deleted, port's instances registered) | 3 | `placeBorel`, `placeBorelSpace`, `infMS` are `NumberTheory/AdelicHaar/PlaceMeasure.lean` (`M4aS4.*`) **verbatim** — FR-0101's import-and-delete, and the port's own modules already write `attribute [local instance] M4aS4.placeBorel M4aS4.infMS` |
| **kept** | 28 | the port's copy is `private` in `ArchKFiniteFamily`/`ArchCompactOrbit` (`exists_forall_liftFin_mem`, `congrSet`, `liftFin`, `one_apply_eq`, …) and therefore **not importable**; the `InducedSectionFlat`/`AdelicHeight`/`ArchCompactOrbit` public ones (`finLocalHeight_mul_integral`, `rowMaxNorm_mul_le`, `flatOne`, …) sit in the pin's *other* inner namespace (`P6B.JE2aFlat`), so importing them means re-qualifying every use site inside a 5,000-line transcribed body — a refactor that belongs to a dedup wave of its own, not to the finishing touch of a green module |

The 28 kept clusters are recorded here rather than in the source; the next dedup wave can take them
one declaration at a time.

### 5.1 The sharing pass — the 31 clusters, factored and measured

The 28 kept clusters were re-opened on the rule **share the mathematics; trivial helpers stay
private**, and the result is a real refactor, not a re-triage. The measured starting point was **31
clusters / 414 removable lines**; the end point is **6 / 61**, all six either trivial or provably
non-substituting.

**Group A — the `ArchKFiniteFamily.LevelInvariance` engine (13 clusters, 219 lines).** The port's
copies were `private`. They are the arch-finiteness engine itself — `exists_forall_liftFin_mem` (36),
`exists_idealBall_subset` (30), `exists_congrSet_subset` (30), `eq_zero_of_forall_mem_idealBall` (23),
`exists_rightInvariantOn_congrSet_of_isKfSmooth` (23), `adelicArchGLInclAt_mul_comm` (18), `congrSet`
(10), `idealBall_span_mul_subset` (10), `coe_eq_liftFin` (9), `one_apply_eq` (7), `liftFin` (4),
`idealBound_span_singleton` (4), `RightInvariantOn` (3) — so they are **promoted, in place, public**,
and the big-cell module deletes its 13 copies and opens the namespace. Because they are promoted at
the names the pin's own copies carry, the checker now *verifies* them through its pin-private
fallback: that module went **1 ok → 14 ok / 0 mismatch / 0 missing**. The promotion is a
checked-surface gain, not just an API one.

**Group B — `InducedSectionFlat`'s flat family (12 clusters, 89 lines).** These were already public
(in `AutomorphicForm.FlatInducedSection`, *then* still the pin's `P6B.JE2aFlat`): `adelicHeight_mul_of_integral_of_rowIsometry` (32),
`finLocalHeight_mul_integral` (26), `norm_det_eq_one_of_integral` (17), `rowMaxNorm_mul_le` (16),
`finHeight_mul_integral` (13), `finLocalHeight_one`, `rowMaxNorm_mul_integral`, `flatOne` (the
definition), `flatOne_apply_one`, `finHeight_one`, `adelicHeight_one`, `coe_mul`. The big-cell copies
are deleted and the namespace opened. `coe_mul` was briefly promoted too and then **reverted** —
five lines of coercion law are not worth a public name (the rule).

**The six that stay (61 lines), and why each is not sharing:**

| cluster | lines | why it is not a duplicate |
|---|---:|---|
| `eq_of_glArch_eq_of_glFin_eq` | 20 | the port's twins (`adelicGL2_ext'`, `gl_ext`) take `(h₁) (h₂)`; the pin's call site needs a different shape — `rw` fails. **Kept local** |
| `continuous_adelicArchGLInclAt` | 15 | the pin's takes `(F) (w)` *explicitly* (its call sites pass `F`), the port's takes `(w)`. **Kept local** |
| `weyl_inv_mul_unipotent_val` | 11 | **Kept local** (the port's `coe_weylInv_mul_unipotent` is the same content at a different call shape; restoring was cheaper than re-qualifying five uses) |
| `adelicWeyl_inv` | 7 | the port's twin is `adelicWeyl_inv'`, in `WeylIntegrable`; the pin's is used as a bare rewrite. **Kept local** |
| `norm_ringEquivRealOfIsReal_symm` | 5 | the port's `norm_symm_ringEquivRealOfIsReal` takes an `x : ℝ`; the pin's use feeds it to `IsRowIsometry.map_ringEquiv`, which wants the point-free form. **Kept local** |
| `rTrans` | 3 | **trivial**: `rTrans g ψ = fun y => ψ (y * g)`, three lines, and the port's `rightTranslate` takes `F` explicitly. Kept private, as the rule says |

Each "kept local" was **tested by substitution and reverted** — the compilation is the evidence, not
the name match. That makes the six a measured instance of the recipe's `shape`-tier caveat ("verify at
the call sites before deleting one"): **25 of 31 shape clusters here were true duplicates and 6 were
not**, i.e. the tier's false-positive rate on a 5,000-line transcription is ~20%.

**Net effect.** The module goes **5,445 → 5,176 lines** (−269 = 283 lines of duplicate deleted, 14 of
restored local helpers and the `F` binding put back); four
temporary imports were pruned again; the dependencies it now *shares* are
`ArchKFiniteFamily` (promoted) and `InducedSectionFlat` (already public), both of which it already
imported. Gates after the pass: `lake env lean` and `lake build` silent (23 s), `check_port` **1 ok /
0 / 0**, axioms clean, consumer probe 0 errors.

**`move_dead`.** Reachability from the public headline: **12 declarations / 150 lines** unreachable
(`move_dead.py --select dead` reported 18 / 202, of which 4 were false positives — see the friction
below — and 2 were the `placeBorel`/`infMS` duplicates deleted under the cross-dedup rule). All 12
are **dead mathematics** — the real-place Fourier/Poisson route the pin abandoned, plus the
definitional-unfolding API of four of its own objects — so they were shelved, not deleted:
`Reserve/AutomorphicForm/Adelic/BigCellExpansionDead.lean` (**1,749 lines**, 130 declarations: the 12
plus the 118 live premises they need, `--copy`), green (7.4 s) and unwired.

**The consumer probe.** `spec/AutomorphicFormSetAF7Consumer.lean`, one zone, **0 errors / 0
warnings**: the headline is instantiated at the port's own flat family `φ s := P6B.JE2aFlat.flatOne F
s`, with `_hφ` from `isInducedSection_flatOne`, `_hφK` from `isArchKFinite_flatOne`, `_hφc` from
`continuous_flatOne`, `_hφne` from `flatOne_apply_one`, and the conclusion read at `μ = ν = 1`
(`μν⁻¹ = 1`, so the archimedean factor is the constant `1`). `IsKfSmooth` and the flat-family
condition are hypotheses — the port states neither for `flatOne`.

**Deviations from the pin, all recorded above and in the module header:** three `rfl` entry lemmas,
two `rfl` bridge lemmas, one `attribute [local instance]` re-registration, one `disjoint`-shaped
`hst` (local `have`, not a declaration), one `Prod`-projection at `hxall`, one qualified
`one_apply_eq`, `Cell` as `abbrev`, a locally stated `val_finitePartUnits` (the pin's text, at the
pin's statement, `private`), the `modulus_adicCompletion_eq_nnnorm` import, and six v4.34
deprecation renames. Every one is `private`-only: the headline's statement is untouched.
