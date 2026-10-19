# WORKORDER-LP3a — the Laurent-series model at a degree-one place, and two generator transfers

**Status (closed 2026-10-19): landed and reviewed green.** One set, **three** small
modules, three public headlines, **6 declarations statement-checked** (1 + 2 + 3): the
pin's own `private`/public split is kept, so module A's 27 helpers stay `private` and
only its headline is diffed. Measured: `Place/LaurentSeriesModel.lean` 544 lines,
`Place/TranscendentalOfOrdNeZero.lean` 75, `IsCurveOver/FinitenessTransfer.lean` 122;
tier-1 builds 2,552 / 2,686 / 2,024 jobs, **0 warnings**; axioms
`[propext, Classical.choice, Quot.sound]` on all three; frozen checker unchanged at
**10473**. One `HahnSeries` name drifted (`embDomain_notin_range` →
`embDomain_of_notMem_range`) plus the usual `if_pos`/`if_neg` → `ite_eq_left`/
`ite_eq_right`; the rest of the 523-line development is verbatim. The LP4 target now
needs only itself and the LP3b leaf (`needed 2 nodes / 1,597 lines`). These are the three `AlgebraicCurve`/`Place` leaves that the third
`localParam` leaf (`exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex`,
WORKORDER-LP4) needs before it can even be stated; all three are graph leaves with no
premises of their own (`frontier.py` prices each at `needed 1`). The set is a
*pre-round* in the workflow's sense (§3 step 4a) but it is not a definition layer: it
is three small theorems, so it is dispatched as a set of its own.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the new per-module protocol (`spec-pin:` header, `spec/check_port.py`).
Read [WORKORDER-LP2-branch-uniqueness.md](WORKORDER-LP2-branch-uniqueness.md) first —
it is the closest sibling (same namespace, same house style, same reuse discipline).

## 1. Scope

Three pin `S_` files, ported whole, one module each:

| # | pin `S_` file (pinned `aa2d8b3`) | lines | decls | public | headline |
|---|---|---:|---:|---:|---|
| A | `S_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one.lean` | 523 | 28 | 1 | `AlgebraicCurve.Place.exists_algHom_laurentSeries_of_deg_eq_one` |
| B | `S_AlgebraicCurve_Place_transcendental_of_ord_ne_zero.lean` | 41 | 3 | 2 | `AlgebraicCurve.Place.transcendental_of_ord_ne_zero` |
| C | `S_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean` | 91 | 3 | 3 | `AlgebraicCurve.finiteDimensional_adjoin_of_transcendental` |

The mathematics, one sentence each:

* **A** — a place of degree one of a function field over `K` has a `K`-algebra
  embedding into `LaurentSeries K` sending a uniformiser `t` to `X` and every `x` to
  a series whose order is `w.ord x`: the Laurent expansion at a rational point.
* **B** — a function with nonzero order at some place is transcendental over `K`.
* **C** — if one generator `x` makes `F` finite over `K(x)`, so does any transcendental
  `t`: `K(x) ⊆ K(t)` is algebraic when `t` is transcendental, so `[F : K(t)]` is
  finite.

**Not this set:** the LP4 leaf itself; the PowerSeries majorant leaf
(WORKORDER-LP3b); any edit to an existing module.

Measured: **0 substitutions, 0 residue** (`port_advise`, shape tier) — every
declaration of the three files is new to the port. Net new ≈ 655 lines, of which
module A is 523 with 27 `private` helpers and one public headline.

## 2. Pre-round: the definition layer is homed

* A imports `Definitions.Def_AlgebraicCurve_DivisorClassGroup` (ported: `Defs/Place.lean`,
  `Defs/Divisor.lean`) and `Definitions.Def_ModularCurve_LaurentCoeff` — homed whole at
  `FLTForHuman/ModularCurve/Defs/Laurent.lean` (`coeffMap`, `coeffEmb`,
  `laurentBaseChange` and their lemmas; the module's header records the pin
  provenance). A uses mathlib's `LaurentSeries`/`HahnSeries.single`/`order` and its own
  `resEquiv`/`resCoeff`/`remSeq` development; check the two `coeffMap` names it may
  want and import that module if so.
* B imports `Definitions.Def_AlgebraicCurve_PlacesOverDVR` — homed at
  `Defs/PlacesOverDVR.lean`.
* C imports mathlib only (`IntermediateField.Adjoin.Defs`, `RingTheory.Algebraic.Defs`,
  `LinearAlgebra.FiniteDimensional.Defs`).

**A note for module C.** The port *does* declare a `finiteDimensional_adjoin_of_transcendental`,
as `private` in `AlgebraicCurve/IsCurveOver/PerfectField.lean` and in
`ModularCurve/XH/HeckeInputs.lean`, and as a public theorem in
`ModularCurve/X1/FunctionFieldResidue.lean:929` — but that public copy states the
hypothesis as an argument `(hfin : FiniteDimensional …)`, not as an instance, and the
pin's `Theorems/` wrapper (this set's authority) states it as `[FiniteDimensional …]`.
Because of that last-name match `frontier.py` prices the pin node as already ported;
it is not, and this set ports it. Do **not** import the `ModularCurve` copy from an
`AlgebraicCurve` module (it would reverse the layering); write the pin's 91 lines.

## 3. Source

Pinned `anthropics/fermats-last-theorem@aa2d8b3`, for each of A/B/C a
`Theorems/Thm_<stem>.lean` (the statement authority) and a
`P2M/Sol/S_<stem>.lean` (the proof). Rendered, for A:

* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one.lean>

and likewise for B and C. `python3 spec/statement_db.py show <name>` prints any pin
signature from the corpus.

## 4. Deliverable

**4.1 Homes.**

| # | module | namespace |
|---|---|---|
| A | `FLTForHuman/AlgebraicCurve/Place/LaurentSeriesModel.lean` | `AlgebraicCurve.Place` (the pin declares its helpers `private` at exactly those dotted names) |
| B | `FLTForHuman/AlgebraicCurve/Place/TranscendentalOfOrdNeZero.lean` | `AlgebraicCurve.Place` |
| C | `FLTForHuman/AlgebraicCurve/IsCurveOver/FinitenessTransfer.lean` | `AlgebraicCurve` |

**4.2 The three headlines**, stated exactly as their wrappers (verbatim; keep the
`-- pin:` marker above each):

```lean
-- pin: AlgebraicCurve.Place.exists_algHom_laurentSeries_of_deg_eq_one (Theorems/Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one.lean:7)
theorem AlgebraicCurve.Place.exists_algHom_laurentSeries_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (hw : w.deg = 1)
    (t : F) (ht : w.ord t = 1) :
    ∃ φ : F →ₐ[K] LaurentSeries K,
      φ t = HahnSeries.single (1 : ℤ) (1 : K) ∧ ∀ x : F, (φ x).order = w.ord x

-- pin: AlgebraicCurve.Place.transcendental_of_ord_ne_zero (Theorems/Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero.lean:9)
theorem AlgebraicCurve.Place.transcendental_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {t : F} (ht : v.ord t ≠ 0) :
    Transcendental K t

-- pin: AlgebraicCurve.finiteDimensional_adjoin_of_transcendental (Theorems/Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental.lean:7)
theorem AlgebraicCurve.finiteDimensional_adjoin_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] {t : F} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F
```

Each body is the pin's `solution` block (a few lines): A's is
`exists_algHom_laurentSeries_of_irreducible w hw (exists_irreducible_coe_of_ord_eq_one w ht)`;
B's is `not_transcendental_iff.mp`-style from the two helpers; C's reduces to its two
public helpers `isAlgebraic_adjoin_of_transcendental'` and
`finiteDimensional_adjoin_of_transcendental'`.

**4.3 Checked surface.** Module A is 1 public declaration and 27 `private` (keep the
pin's privacy — the checker skips `private`, and that is the pin's own split). Module B
has 2 public: `AlgebraicCurve.Place.ord_eq_zero_of_isAlgebraic'` (the pin leaves it
public) and the headline, plus one `private` helper. Module C has 3 public:
`isAlgebraic_adjoin_of_transcendental'`, `finiteDimensional_adjoin_of_transcendental'`
and the headline. Keep those names: the checker matches them against the pin `S_` file.

**4.4 Module headers** — the new protocol, nothing else:

```lean
/-
  … one paragraph: what the module is (which pin node, what it feeds — the third
  `localParam` leaf and, for A, the Laurent expansion every local computation uses),
  and its role.

  spec-pin: Theorems/Thm_<stem>.lean
  spec-pin: P2M/Sol/S_<stem>.lean
-/
```

## 5. Route

**5.1 No substitutions.** All 34 declarations across the three files are new; there is
nothing to import from the port and nothing to restate. (The one name collision,
`finiteDimensional_adjoin_of_transcendental`, is a *different statement* — §2.)

**5.2 Faithfulness.** Transcribe statements and proof bodies; adapt only what mathlib
`v4.34.0` forces. A's development is `resEquiv`/`resCoeff`/`remSeq`/`expCoeff`/`expPS`
plus 13 lemmas — a substantial amount of `HahnSeries`/`LaurentSeries` API
(`HahnSeries.single`, `order`, `coeff`, `ofPowerSeries`), so expect some `v4.33.1 →
v4.34.0` drift there; adapt the proof, never the statement. `if_pos`/`if_neg` are
deprecated (LP2's order §5.2 has the replacements).

**5.3 Stop-early risks.**

* If A's proofs need a `private` helper of `ModularCurve/Defs/Laurent.lean` or of a
  `Defs/` AC module, **stop and report** with the declaration, host and
  `build_ladder.py --edit` price; re-derive it locally `private` if cheap.
* If C's proof wants the `ModularCurve.X1.FunctionFieldResidue` theorem, do not import
  it (layering); the 91 pin lines are self-contained.
* Build-time blow-up is instance inference; diagnose, never raise `maxHeartbeats`.

## 6. Build discipline (copy, do not paraphrase)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` —
> the cap is low on purpose. Never raise `maxHeartbeats`, never a module-level
> `set_option maxHeartbeats`. `flock .lake/flt_build.lock timeout 300 lake build <module>`
> per finished file. Never a bare whole-tree `lake build`; that is the session's last
> step and only with the user's agreement. Every tool call within 2 minutes, and no
> loop around that.

Build the three modules **in order A, B, C**, one at a time.

## 7. Hub prohibition

Three new modules, no existing file edited, no `PORT_FILES`/`SOURCES` entry, no commit,
no promotion. Anything that seems to require one: stop and report with the price.

## 8. Verification

```bash
cd lean
python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Place/LaurentSeriesModel.lean          # 1 ok
python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Place/TranscendentalOfOrdNeZero.lean    # 2 ok
python3 spec/check_port.py FLTForHuman/AlgebraicCurve/IsCurveOver/FinitenessTransfer.lean     # 3 ok
python3 spec/check_port.py --changed                                                          # 6 modules, none failing
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.LaurentSeriesModel
# … then the other two
```

plus `#print axioms` on the three headlines (`[propext, Classical.choice, Quot.sound]`),
a grep sweep for `sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats`,
tier 1 green with 0 warnings, `git status --short` showing only the three new modules,
and the frozen checker unchanged at 10473.

## 9. Report shape

Per module: path, lines, public/`private` split, `check_port` output, build result and
warnings, axioms line. Then the grep sweep, `git status`, the frozen-checker line, and
every deviation — with particular attention to A: name the `HahnSeries` API that
drifted and how the proof was adapted (a statement change is a stop condition, not a
deviation). Finish with what is left on the shelf: the LP4 leaf should then be ready,
and the four premise nodes gone.
