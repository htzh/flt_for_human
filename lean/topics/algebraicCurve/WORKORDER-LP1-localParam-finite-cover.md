# WORKORDER-LP1 — the local-parameter finite cover (one leaf of the D-S cone)

**Status (closed 2026-10-19): landed and reviewed green.** One set, one module, one
public headline over a shared eleven-lemma `Fam` engine. Measured outcome: module
`FLTForHuman/AlgebraicCurve/Place/FiniteCover.lean` (654 lines, 17 public: 16
internal + 1 headline); `spec/check_port.py` **17 ok / 0 mismatch / 0 missing** (and
13 ok on the manager's `OrdCalculus.lean`, 30 in all); tier-1 build **3,295 jobs,
0 warnings**; axioms `[propext, Classical.choice, Quot.sound]`; frozen checker
**unchanged at 10473**; register current; `git status` showing only the new files.
Friction: [../../logs/localParam-finite-cover.md](../../logs/localParam-finite-cover.md).
Beyond `autoImplicit false` the only suppressions in the two modules are the narrow
`linter.unusedVariables` on the headline (the pin's `hfg` is dead in the proof) and
the narrow `linter.style.haveILetI` on `isRational_of_isCurveOver`, whose two
`haveI`s are load-bearing (`Module.Finite` and `Algebra.IsIntegral` feed
`IsAlgClosed.algebraMap_bijective_of_isIntegral`). The manager's pre-round is *already landed*
and green: `FLTForHuman/AlgebraicCurve/Place/OrdCalculus.lean`, `spec/check_port.py` **13 ok /
0 mismatch / 0 missing** at the landing — **19** after the same-wave re-home of the six
generic prelim lemmas the two sibling leaves needed
([logs/localParam-family.md](../../logs/localParam-family.md) §1). This order
covers only the second module. The set's row is
`AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex`, the
857-line leaf silo `P2M/Sol/S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean`
in [PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2's `--include-leaves` view
(cone fan-in 1 / project 2, 857 silo lines).

**Audience.** A fresh coding session. The method is
[porting-playbook.md](../../porting-playbook.md) §3–§5; **the statement-checking
protocol is the new one** (playbook §4, "Per-module checking"), not the frozen
`old_check_stmts.py` lists. Read this whole order before writing a line.

**Companion.** The mathematics of the three `localParam` leaves of this cone is
[TOPIC-localParam-finite-cover.md](TOPIC-localParam-finite-cover.md). The two
siblings (`AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex`,
500 pin lines, and `…_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex`,
1,142) are **not** this set; their shared prelude now imports `Place/OrdCalculus.lean`
and they are cut separately.

## 1. Scope

Port the remainder of the pin `S_` file's 857 lines — everything except the 24-lemma
prelim block already homed:

| pin lines | block | declarations |
|---|---|---|
| 255–261 | Prelim (divisor half) | `sum_support_eq_zero` |
| 264–277 | Elementary | `exists_pos_forall_le` |
| 279–398 | Analytic | `exists_analyticAt_pow_eq`, `exists_finset_preimages_of_meromorphicOrderAt_eq` |
| 400–838 | Family | `Fam` (structure, 8 fields) and the eleven `Fam.*` lemmas |
| 843–857 | — | `solution` → **the one public headline** |

That is **17 declarations**: 16 internal, 1 headline (table in §4.4).

The mathematics in one sentence: given a family of local coordinates `(γ v, t v,
ρ v)` at every place of a curve over `ℂ` — `t v` a local parameter, `z ↦ γ v z` the
chart, `hγ` the meromorphic reading of `evalAt` — there is a **finite** set of places
`S` and a radius `r v < ρ v` at each such that the balls `γ v '' ball 0 (r v)` cover
every place.

**Not this set:** the two sibling leaves; the pin's `p2m_*` scaffolding; any edit to
an existing `.lean` module; any `PORT_FILES`/`SOURCES` append (the new protocol has
none).

Measured (playbook step 3, before the prelim block was homed):

| quantity | value |
|---|---:|
| pin `S_` lines | 857 |
| of which already in the port (9 lemmas, imported) | ≈ 55 |
| homed in `Place/OrdCalculus.lean` (manager, landed) | ≈ 210 |
| **this order's net new math lines** | **≈ 590** |
| declaration groups (this module) | 17 |
| public headlines | 1 |

## 2. Pre-round: done, and none is owed here

**(a) The definition layer is homed.** The pin `S_` file imports
`Def_AlgebraicCurve_DivisorClassGroup`, `Def_AlgebraicCurve_IsCurveOver` and
`Def_AlgebraicCurve_PlaceEvaluation`, all in the port
(`Defs/{Place,Divisor,IsCurveOver,PlaceEvaluation,PlaceCalculus,PushPull,Repartitions}.lean`).
Every API name the proofs use is present; verified by grep and by the manager's
`OrdCalculus.lean` compiling against them:

`Place.toValuationSubring`, `Place.ord`, `Place.ord_zero`, `Place.ord_mul`,
`Place.ord_inv`, `Place.ord_zpow`, `Place.ord_coe_unit`, `Place.ord_coe_irreducible`,
`Place.exists_unit_mul_zpow`, `Place.ne_top'`, `Place.algebraMap_mem'`,
`Place.coe_algebraMap`, `Place.heightOneSpectrum`, `Place.adicValuation*`,
`Place.isUnit_algebraMap`, `Place.algebraMap_residueField_injective`,
`Place.residueInv_algebraMap`, `Place.algebraMap_evalAt`, `Place.evalAt_of_mem`,
`Place.evalAt_one`, `IsLocalRing.residue_eq_zero_iff`,
`IsLocalRing.mem_maximalIdeal`, `IsCurveOver.finiteResidue`,
`IsCurveOver.deg_eq_one_of_isAlgClosed`, `HasPrincipalDivisors.exists_divisor`
(a class field of `AlgebraicCurve.HasPrincipalDivisors`, `Defs/Divisor.lean:70`),
`Divisor.degree` / `Divisor.degree_eq_sum`, `Divisor.support`.

**(b) The shared prelude is homed and statement-checked.** The pin's 24-lemma
prelim block splits in two:

* the **nine** the port already carried (same names, same statements modulo binder
  spelling), imported, never re-proved:
  `Place.adicValuation_le_one_of_mem`, `Place.adicValuation_eq_exp_neg_ord`
  (`Defs/Repartitions.lean`); `Place.mem_of_ord_nonneg`,
  `Place.ord_nonneg_of_mem` (`Defs/PushPull.lean`); `Place.evalAt_algebraMap`,
  `Place.evalAt_mul` (`Defs/PlaceEvaluation.lean`); `Place.evalAt_zero`,
  `Place.ord_sub_evalAt_pos` (`Defs/PlaceCalculus.lean`); `Place.ord_algebraMap`
  (`Defs/Place.lean`);
* the **thirteen** new ones (five of them in both sibling `S_` files, two more in
  one), landed by the manager this round in
  `FLTForHuman/AlgebraicCurve/Place/OrdCalculus.lean` (13 ok under
  `spec/check_port.py`): `not_mem_iff_ord_neg`, `ord_pos_of_mem_maximalIdeal`,
  `residue_eq_zero_of_ord_pos`, `isRational_of_isCurveOver`, `residue_algebraMap`,
  `evalAt_sub_algebraMap`, `evalAt_eq_zero_of_ord_pos`, `ord_pos_of_evalAt_eq_zero`,
  `evalAt_eq_of_ord_sub_algebraMap_pos`, `mem_of_ord_sub_algebraMap_pos`,
  `sub_algebraMap_mem_iff`, `ord_sub_algebraMap_of_not_mem`,
  `exists_mem_and_not_mem`.

The pin's `theorem solution` is not one of them; its statement is the headline.

**(c) No hub edit, no promotion, no dedup is owed.** This module re-derives nothing
the port already has and needs no `private` helper of an existing module (the pin
file is self-contained above the definitions). `port_advise` finds no shared block
*within* the target set (the two `Theorems/` and `S_` copies of the headline share it
by construction); its substitution table must be read by **shape**, not by text —
nine of the prelim lemmas are in the port as the pin's own `Theorems/` wrappers spell
them, and the shape tier (§5.1) is what names them.

## 3. Source

Pinned `anthropics/fermats-last-theorem@aa2d8b3`:

* statement (the comparable copy): `Theorems/Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean`
  (24 lines; `spec-pin:` source for the headline);
* proof: `P2M/Sol/S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean`
  (857 lines; `spec-pin:` source for the sixteen internal declarations).

Rendered:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean>
and
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean>.

The pin's `Definitions/` imports carry no `attribute [-instance]`/`[-simp]` prelude;
the wrapper's `open AlgebraicCurve` / `open scoped Manifold ContDiff Topology` is
already implied by the port's modules. Nothing to narrow.

Reading the pin's statement text without the 1.1 GB tree:
`python3 spec/statement_db.py show AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex`
or `rg -n 'exists_finset_forall_exists_localParam_eq_complex' tmp/flt-statements/statements.tsv`.

## 4. Deliverable

**4.1 Home.** `FLTForHuman/AlgebraicCurve/Place/FiniteCover.lean` (the `Place/`
directory holds `DegreeOne.lean`, `FiniteResidue.lean`, `Completion.lean`,
`AdicCompletion.lean`, `IsPrimeOverValuationSubring.lean` and, new this round,
`OrdCalculus.lean`).

**4.2 Imports.** Start from

```lean
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.Defs.Divisor
```

and add only what the edit loop shows is missing (`Defs/IsCurveOver.lean` is
already reached through `OrdCalculus`). **Do not write `import Mathlib`.**

**4.3 Namespace map.** Keep the pin's nesting — the statements do not mention
namespaces, so the checker matches by last name, and the pin's names are the ones
the sibling leaves will want:

```lean
namespace AlgebraicCurve
namespace Place
namespace FiniteCover

section Prelim      -- sum_support_eq_zero
section Elementary  -- exists_pos_forall_le
section Analytic    -- exists_analyticAt_pow_eq, exists_finset_preimages_…
section Family      -- variable (F : Type*) [Field F] [Algebra ℂ F]
                    -- structure Fam, then variable {F} [IsCurveOver ℂ F] (P : Fam F)
                    -- namespace Fam

end FiniteCover
end Place

-- the headline, outside FiniteCover, at the wrapper's name
theorem AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex …
end AlgebraicCurve   -- or `namespace AlgebraicCurve / namespace Place` around it
```

The pin's `p2m_open`/`p2m_export` lines do **not** port: they become
`open Filter Set Metric Topology Polynomial` (the pin's list, minus what
`autoImplicit false` makes unnecessary) and plain namespaces.

**4.4 Declaration inventory** (pin line → declaration):

| pin | declaration | note |
|---:|---|---|
| 255 | `sum_support_eq_zero` | divisor, `[IsAlgClosed K] [IsCurveOver K F]` |
| 267 | `exists_pos_forall_le` | finite-infimum over a `Finset` |
| 283 | `exists_analyticAt_pow_eq` | local `e`-th root: `k ^ e = h` near `0` |
| 306 | `exists_finset_preimages_of_meromorphicOrderAt_eq` | **the analytic core**: `e` preimages near a value, via `HasStrictDerivAt.localInverse` and `nthRoots` |
| 399 | `structure Fam` | 8 fields, exact order: `ρ γ t hρ h₀ ht hγ` |
| 418 | `Fam.isRational` | |
| 421 | `Fam.zero_mem_ball` | |
| 424 | `Fam.evalAt_γ_t` | |
| 428 | `Fam.γ_injOn` | |
| 434 | `Fam.analyticAt_reading` | |
| 446 | `Fam.meromorphicOrderAt_reading` | |
| 453 | `Fam.eventually_mem` | |
| 467 | `Fam.exists_radius_mem` | |
| 472 | `Fam.separation` | two charts separate near `0` |
| 518 | `Fam.fibre` | **the main engine**: a finite chart set, with radii, covering the fibre of `g` over a small disc |
| 711 | `Fam.exists_finset_cover` | the theorem, for a `Fam` |
| 843 | `solution` → **headline** | the wrapper's statement, verbatim |

**4.5 The headline.** State it exactly as the wrapper (that text is the
checker-comparable statement; carry the `-- pin:` comment above it):

```lean
-- pin: AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex (Theorems/Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean:11)
set_option linter.unusedVariables false in
theorem AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    (ρ : Place ℂ F → ℝ) (γ : Place ℂ F → ℂ → Place ℂ F) (t : Place ℂ F → F)
    (hρ : ∀ v, 0 < ρ v) (h₀ : ∀ v, γ v 0 = v)
    (ht : ∀ v, ∀ z ∈ Metric.ball (0 : ℂ) (ρ v), (γ v z).ord (t v - algebraMap ℂ F z) = 1)
    (hγ : ∀ v, ∀ f : F, f ≠ 0 → ∀ z ∈ Metric.ball (0 : ℂ) (ρ v),
        MeromorphicAt (fun u : ℂ => (γ v u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ v u).evalAt f) z = ((γ v z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ v z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ v u).evalAt f) z)) :
    ∃ (S : Finset (Place ℂ F)) (r : Place ℂ F → ℝ), (∀ v ∈ S, 0 ≤ r v ∧ r v < ρ v) ∧
      ∀ w : Place ℂ F, ∃ v ∈ S, ∃ z : ℂ, ‖z‖ ≤ r v ∧ γ v z = w :=
  FiniteCover.Fam.exists_finset_cover ⟨ρ, γ, t, hρ, h₀, ht, hγ⟩
```

`hfg` is in the statement but unused in the proof (the pin suppresses
`linter.unusedVariables` for exactly that reason); keep the narrow
`set_option … in`, do not drop the hypothesis.

The `-- pin:` marker above it names the **wrapper** row:
`-- pin: AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex (Theorems/Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean:11)`.
(The pin `S_` row `solution` at line 843 has the identical statement — the checker
would match it by content — but the wrapper is the authority.)

**4.6 The module header.** Exactly the new protocol, and nothing else:

```lean
/-
  … one paragraph: what the module is, that the 24-lemma prelim block lives in
  `Place/OrdCalculus.lean` (and the nine lemmas before it in the `Defs/` modules),
  and the tier/role of this module.

  spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex.lean
-/
```

Two `spec-pin:` lines: the wrapper for the headline, the `S_` file for the sixteen
internal declarations. **Do not add an entry to `spec/old_check_stmts.py`'s
`PORT_FILES` or `SOURCES`** — the frozen checker does not own new modules, and this
module is checked by the new one.

## 5. Route

**5.1 Reuse, never restate.** Use the thirteen `Place.*` lemmas from `OrdCalculus`
and the nine from the `Defs/` modules by their bare names — Lean resolves
`not_mem_iff_ord_neg` inside `namespace FiniteCover` up the prefix chain to
`AlgebraicCurve.Place.not_mem_iff_ord_neg`. Do not copy a lemma body to "keep the
file self-contained": a re-stated pin declaration that the checker cannot see is a
silent unverified surface.

**5.2 Scattering and section variables.** The pin's statements are written with the
section's `variable {K F …}`; keep that shape (`variable {K F : Type*} [Field K]
[Field F] [Algebra K F]`), **not** explicit `{K F : Type*}` binders. This is what
makes the statement text byte-equal to the pin row, and it is what the two blocks
already in the tree do. Where the pin writes `omit [IsCurveOver ℂ F] in`, keep it.

**5.3 Faithfulness.** Transcribe statements and proof bodies; adapt only what
mathlib `v4.34.0` forces (playbook §4). The AC column's friction log
([../../logs/ac-port.md](../../logs/ac-port.md) §11.2) records the recurrent drift:
`Set.mem_setOf_eq`, `zero_le'`, `if_pos`/`if_neg`, `finiteDimensional_adjoin`, the
`Ideal` ramification API. Prefer the new mathlib names **in proofs**; a *statement*
keeps the pin's text.

**5.4 Stop-early risks, with the deviation protocol.**

* **The analytic core (pin 306–398).** `meromorphicOrderAt_eq_int_iff`,
  `HasStrictDerivAt.localInverse`, `hstrict.map_nhds_eq`, `eventually_left_inverse`,
  `Complex.isPrimitiveRoot_exp`, `nthRoots`, `Complex.slitPlane`, `Complex.log` are
  all in mathlib `v4.34.0` (checked: `Mathlib/Analysis/Meromorphic/TrailingCoefficient.lean`,
  `…/InverseFunctionTheorem/{FDeriv,Deriv}.lean`, `…/Polynomial/Roots.lean`). If a
  name moved, fix the proof, not the statement.
* **`Fam` hash.** The checker hashes a structure as header + ordered field names +
  the field-type text. Keep the field order and types exactly as the pin's.
* **A needed port-`private` declaration.** If a proof requires one, **stop and
  report** with the declaration, host and a `build_ladder.py --edit` price; do not
  promote it yourself (hub prohibition).
* **Build-time blow-up.** Instance inference, not proof length, is the cost.
  Diagnose with `set_option diagnostics true` on the one declaration in a scratch
  copy; never raise `maxHeartbeats`.

## 6. Build discipline (copy, do not paraphrase)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` —
> the cap is **low on purpose**: a declaration that exceeds it has an
> instance-inference defect, and the low cap is what finds it. Never raise
> `maxHeartbeats`, never add a module `set_option maxHeartbeats`. `lake build
> <module>` per finished file, serialized with `flock` and bounded with `timeout`.
> Per wave, build only the wave's affected targets — **never a bare whole-tree
> `lake build`**. A whole-tree build happens once, at the session's end, only after
> the user agrees to it, and never on the agent's own initiative.

Run from `lean/`. The finished-file build is
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.FiniteCover`.
Every tool call must finish within **2 minutes**; no loop may circumvent that.

## 7. Hub prohibition

This set adds **one** module and edits **no** existing file. It must not touch any
other `.lean` module, must not add `PORT_FILES`/`SOURCES` entries, must not run
`git commit`. A subagent that believes a promotion or a host edit is genuinely
required **stops and reports** with the declaration, host and the
`build_ladder.py --edit` price. Re-derive a cheap missing helper locally `private`
and report it.

## 8. Verification

```bash
cd lean
python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Place/FiniteCover.lean   # expect 17 ok
python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Place/OrdCalculus.lean   # 13 ok, cached
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.FiniteCover
```

plus:

* `#print axioms AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex`
  — expect `[propext, Classical.choice, Quot.sound]` and nothing else;
* a grep sweep of the new module for `sorry` / `admit` / `axiom` /
  `native_decide` / `import Mathlib` / `maxHeartbeats` — all zero;
* tier 1 green with **0 warnings** (the one allowed suppression is the narrow
  `linter.unusedVariables` on the headline; report any other);
* `git status` showing exactly the one new module;
* **no** `old_check_stmts.py` run and no delta claimed from it: the module is not in
  its lists by design. The frozen checker's own count must be *unchanged* by this
  landing — that is the check that nothing was wired the old way.

## 9. Report shape

Report, in order: (1) the module path and its declaration count, public/private
split; (2) `spec/check_port.py` output for both modules (the 17 line numbers it
maps to, and any `pin:`/`own:` marker you had to add); (3) the build result, wall
and user CPU, and the warning count; (4) the `#print axioms` line; (5) the grep
sweep; (6) every deviation — statement changes, dropped hypotheses, narrowed
linter options, helpers re-derived that the port already had, and anything you
stopped on; (7) the pin line ranges you actually transcribed each declaration from,
if they differ from §4.4; (8) what the landing puts on the ready shelf (expect the
two sibling `localParam` rows to remain, both now shorn of the prelim block).
