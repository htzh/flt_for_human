# WORKORDER-LP4 — the local parameter and the meromorphic-order dictionary

**Status (closed 2026-10-19): landed and reviewed green.** Measured:
`Place/MeroRealize.lean` 639 lines, 60 public; `Place/LocalParamDatum.lean` 480 lines,
40 public; `spec/check_port.py` **100 ok / 0 mismatch / 0 missing** (110 at the landing,
when the pin's ten-row prelim copy was still reproduced as one-line delegations; it is
now imported from `Place/OrdCalculus.lean` and the `Defs/` modules, and the module
declares only the `Datum` layer); tier-1 build 3,681
jobs, **0 warnings**; axioms `[propext, Classical.choice, Quot.sound]`; frozen checker
unchanged at **10473**; the frontier reads `needed 0` for the target. One deprecation
(`dif_pos` → `dite_eq_left`) and two single-declaration `haveILetI` narrowings; the
feared `HahnSeries`/`FormalMultilinearSeries` drift did not occur. The ten-row prelim
copy is kept as one-line delegations (§5.1 as realized, see
[logs/localParam-family.md](../../logs/localParam-family.md) §3.5). One set, **two** modules, one public headline over a 60-declaration engine;
**110 of its 111 declarations are public**, so nearly the whole file is
statement-checked — the largest wired surface of the column.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the per-module protocol (`spec-pin:` header, `spec/check_port.py`). Read
[WORKORDER-LP2-branch-uniqueness.md](WORKORDER-LP2-branch-uniqueness.md) (the closest
sibling: same namespace, same reuse discipline) and
[TOPIC-localParam-finite-cover.md](TOPIC-localParam-finite-cover.md) for how the three
`localParam` leaves fit together.

## 1. Scope

Port the pin `S_` file **whole**:

`P2M/Sol/S_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean`,
1,142 lines, **111 declarations in three blocks**:

| block | pin lines | decls | public | what it is |
|---|---:|---:|---:|---|
| `MeroRealize` | 27–542 | 61 | 60 | a meromorphic germ at a place realised as a `LaurentSeries`: `Bdd`, `fps`/`S`/`SL` (the Fréchet-series reading of a Hahn series), the ring-law and order lemmas, `polyToLaurent`, `isAlgebraic_of_apply_eq_ofPowerSeries`, `bdd_powerSeriesPart`, then the valuation subring `RSet`/`Rfield` and `main` |
| `LocalParam` | 543–1112 | 49 | 49 | the second prelim copy (9 lemmas), `τ` (the `WithTop ℤ`-valued order with its 6 laws), `structure Datum` (8 fields: `t ρ G hG hadd hmul hC ht`) with ~35 lemmas, and `Datum.γ` |
| — | 1112 | 1 | 1 | `solution` → the headline |

The mathematics: given `t` of order one at `v`, construct a chart `γ` on a disc with
`γ 0 = v`, `ord_{γ z}(t - z) = 1`, and — for every `f` — the meromorphic reading of
`evalAt` with its order equal to `ord_{γ z} f`. The engine builds the Laurent
expansion by hand (`S` on a formal multilinear series, `SL` on a Hahn series), shows
the coefficient growth it needs from `isAlgebraic` (via LP3b's majorant), assembles the
`RSet` valuation subring, and `LocalParam.Datum` packages the reading, with `Datum.γ`
landing the place.

**Not this set:** the LP3a/LP3b modules (imported), the charted-space capstone, any
edit to an existing module.

Measured (`port_advise`, shape tier): 8 substitution rows, of which **7** are the
port's own prelim lemmas (see §2) — one false positive, treated below — so the module
imports 7 and writes 104.

## 2. Pre-round: done (LP1–LP3), plus two traps

**Imports (all landed and green):**

* `FLTForHuman/ AlgebraicCurve/Place/OrdCalculus.lean` — `Place.ord_pos_of_mem_maximalIdeal`,
  `residue_algebraMap`, `isRational_of_isCurveOver`, `evalAt_sub_algebraMap`,
  `ord_pos_of_evalAt_eq_zero` (pin lines 652, 672, 666, 679, 689);
* `Defs/PushPull.lean`, `Defs/Repartitions.lean`, `Defs/PlaceEvaluation.lean`,
  `Defs/PlaceCalculus.lean`, `Defs/Place.lean` — the rest of the prelim copy
  (`adicValuation_le_one_of_mem` 625, `adicValuation_eq_exp_neg_ord` 631,
  `mem_of_ord_nonneg` 636, `ord_nonneg_of_mem` 644, `evalAt_algebraMap`,
  `evalAt_mul`, `evalAt_zero`, `evalAt_add`);
* `FLTForHuman/AlgebraicCurve/Place/BranchUniqueness.lean` — `BranchUniqueness.eq_of_forall_ord_eq`
  (pin line 694), public there;
* **LP3a**: `Place/LaurentSeriesModel.lean` (`Place.exists_algHom_laurentSeries_of_deg_eq_one`
  and its `…_order_eq_ord` companion), `Place/TranscendentalOfOrdNeZero.lean`,
  `IsCurveOver/FinitenessTransfer.lean` (`AlgebraicCurve.finiteDimensional_adjoin_of_transcendental`);
* **LP3b**: `Analysis/PowerSeries/EisensteinAlgSeries.lean`
  (`PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex`);
* `ModularCurve/Defs/Laurent.lean` — `coeffMap`, `coeffEmb`, `laurentBaseChange` and
  their `[simp]` lemmas (pin `Def_ModularCurve_LaurentCoeff`), which the engine's
  `polyToLaurent` uses.

**So 9 prelim rows of this file are imports** (625–694); the remaining 6 of its prelim
copy are the same six LP2 had to write — `evalAt_eq_of_ord_sub_algebraMap_eq_one`,
`mem_of_ord_sub_algebraMap_eq_one`, `ne_zero_of_ord_eq_one`, `evalAt_of_not_mem`,
`evalAt_eq_inv_evalAt_inv` (all in `BranchUniqueness.lean`, public — **import them from
there**, they are the same statements) and `eq_of_forall_ord_eq` (likewise). So the
`LocalParam` block contributes **no new prelim lemma at all**; only `τ`, `Datum` and
the headline machinery are new.

**Two traps.**

1. `port_advise` reports `MeroRealize.RSet` (pin 453, a `def … : Prop`-shaped statement)
   as a substitution of `AutomorphicForm.WeylIntegrable.S2` — a **type-only `def`
   false positive**. Ignore it; `RSet` is new mathematics.
2. The pin's file-wide prelude disables **8 instances** (`attribute [-instance] …`)
   and **17 `[simp]` lemmas** (`attribute [-simp] …`) because the pin's own `S_` files
   re-declare instances and coefficient lemmas. In the port the same-named public
   declarations already exist exactly once, so **do not copy the blanket prelude**:
   if one proof needs a simp set narrowed, narrow it on that single declaration and
   report it.

## 3. Source

Pinned `anthropics/fermats-last-theorem@aa2d8b3`:

* statement: `Theorems/Thm_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean`
  (23 lines; `spec-pin:` source for the headline; its own two `attribute` lines are the
  prelude of the parenthetical above);
* proof: `P2M/Sol/S_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean`
  (1,142 lines; `spec-pin:` source for the 110 internal declarations).

Rendered:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean>
and
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean>.

## 4. Deliverable

**4.1 Two modules**, mirroring the pin's two blocks:

| module | contents | public decls |
|---|---|---:|
| `FLTForHuman/AlgebraicCurve/Place/MeroRealize.lean` | the `MeroRealize` block, namespace `AlgebraicCurve.Place.MeroRealize` | 60 |
| `FLTForHuman/AlgebraicCurve/Place/LocalParamDatum.lean` | the `LocalParam` block + the headline, namespace `AlgebraicCurve.Place.LocalParam`; headline in `AlgebraicCurve.Place` | 50 |

The split is the pin's own (`MeroRealize` ends at `main`); it keeps the 480-line engine
importable without the 570-line `Datum` layer. Both modules carry `spec-pin:` lines (both
pin files in each header), so **all 110 internal declarations are statement-checked** —
that is the point of the new wire and the reason not to hide the engine as tier 3.

**4.2 The headline**, verbatim from the wrapper:

```lean
-- pin: AlgebraicCurve.Place.exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex (Theorems/Thm_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean:20)
theorem AlgebraicCurve.Place.exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] (v : Place ℂ F) (t : F) (ht : v.ord t = 1) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ F), 0 < ρ ∧ γ 0 = v ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, (γ z).ord (t - algebraMap ℂ F z) = 1) ∧
      ∀ f : F, f ≠ 0 → ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        MeromorphicAt (fun u : ℂ => (γ u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ u).evalAt f) z = ((γ z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ u).evalAt f) z)
```

`hfg` is in the statement and is used (through the LP3a finiteness transfer, pin line
560), so no linter suppression should be needed; if Lean reports it unused, that is a
sign the finiteness step was ported wrong — stop and report.

**4.3 The `Datum` structure.** 8 fields, pin order `t ρ G hG hadd hmul hC ht`; the
checker hashes header + ordered field names + field-type text, so keep them exact.
`Datum.n`, `Datum.val`, `Datum.place`, `Datum.γ` etc. are `def`s/lemmas in
`namespace Datum` — keep them public at the pin's names.

**4.4 Module headers.** Each carries the two `spec-pin:` lines plus one paragraph: which
pin node, which block, that the prelim copy is imported (list the homes), and the role.
In `MeroRealize.lean` also record that the pin's file-wide `attribute [-instance]` /
`[-simp]` prelude is deliberately not copied (§2).

## 5. Route

**5.1 Reuse.** The 9 prelim rows and the 5 `BranchUniqueness` prelim lemmas are imports;
nothing else in the port. In particular do not re-prove `evalAt_of_not_mem`,
`evalAt_eq_inv_evalAt_inv` etc. from `BranchUniqueness` — import them.

**5.2 Faithfulness.** Statements and proofs transcribed; adapt only what mathlib
`v4.34.0` forces. Expected drift, in order of likelihood: the `HahnSeries`/`LaurentSeries`
API (`order`, `coeff`, `ofPowerSeries`, `single` arithmetic) in `MeroRealize`; the
`FormalMultilinearSeries`/`S` API (`HasFPowerSeriesOnBall`, `summable_norm`); the
`meromorphicOrderAt`/`analyticOrderAt` lemmas in `LocalParam`; and the deprecated
`if_pos`/`if_neg`/`dif_pos`/`dif_neg` (LP2's replacements: `ite_eq_left`/`ite_eq_right`/
`dite_eq_left`/`dite_eq_right`). `MeroRealize.SL_mul` (pin 240–263) and
`Datum.ord_place` (979–1008) are the two long proofs.

**5.3 Stop-early risks.**

* Pin `attribute [-simp]`/`[-instance]` sites: narrow, never blanket (§2).
* A proof that needs a `private` helper of `ModularCurve/Defs/Laurent.lean` or of a
  `Defs/` module: **stop and report** with the declaration, host and
  `build_ladder.py --edit` price, or re-derive it locally `private`.
* `Datum`'s `include hz` sections and the `omit` lines: keep them, they are part of the
  statements' binder context.
* Build-time blow-up is instance inference; diagnose, never raise `maxHeartbeats`.

## 6. Build discipline (copy, do not paraphrase)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`.
> Never raise `maxHeartbeats`, never a module-level `set_option maxHeartbeats`.
> `flock .lake/flt_build.lock timeout 300 lake build <module>` per finished file, one
> module at a time (`MeroRealize` first). Never a bare whole-tree `lake build`. Every
> tool call within 2 minutes, no loops.

## 7. Hub prohibition

Two new modules, no existing file edited, no `PORT_FILES`/`SOURCES` entry, no commit, no
promotion. Anything that seems to need one: stop and report with the price.

## 8. Verification

```bash
cd lean
python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Place/MeroRealize.lean        # expect 60 ok
python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Place/LocalParamDatum.lean     # expect 50 ok
python3 spec/check_port.py --changed                                                # none failing
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.LocalParamDatum
```

plus `#print axioms` on the headline (`[propext, Classical.choice, Quot.sound]`), the
grep sweep, 0 warnings, `git status --short` showing only the two new modules, the
frozen checker unchanged at 10473, and
`python3 tools/deps/frontier.py --ds --target AlgebraicCurve.Place.exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex --top 3`
reading `needed 0` after the landing.

## 9. Report shape

Per module: path, lines, public/`private` split, `check_port` output with the pin line
each declaration matched, build and warnings. Then the axioms line, the grep sweep,
`git status`, the frozen-checker line, the frontier line, and every deviation — with
the `HahnSeries`/`FormalMultilinearSeries` API drift named explicitly, and a note on
whether any `attribute [-simp]`/`[-instance]` narrowing was needed. Finish with what
the landing leaves on the shelf (the charted-space capstone's remaining premises and
`Place.exists_forall_ord_eq_finset`).
