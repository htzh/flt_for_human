# WORKORDER-LP2 — uniqueness of the analytic branch through a complex place

**Status (closed 2026-10-19): landed and reviewed green.** One set, one module, one
public headline over the `Pkg`/`Setup` development. Measured outcome:
`FLTForHuman/AlgebraicCurve/Place/BranchUniqueness.lean`, **370 lines**, **37 public**
declarations, `spec/check_port.py` **37 ok / 0 mismatch / 0 missing** (43 at the landing;
the six generic prelim lemmas it homed first moved to `Place/OrdCalculus.lean` in the
same wave); tier-1 build
3,291 jobs, **0 warnings**; axioms `[propext, Classical.choice, Quot.sound]`; frozen
checker unchanged at **10473**; one proof-body adaptation (`dif_neg` →
`dite_eq_right`). The realized import count is **15**, not the 16 this order first
estimated, so the checked surface is 43 — see §2(b) as corrected below. The set's row is
`AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex`, the 500-line pin
`S_` file
`P2M/Sol/S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean`
(pinned `aa2d8b3`) — the second of the three `localParam` leaves of the D-S cone,
and the **first row on the ready shelf** after the LP1 landing
([PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2: 1 needed node, 500 silo
lines, no premises beyond the definitions).

**Audience.** A fresh coding session. The method is
[porting-playbook.md](../../porting-playbook.md) §3–§5; the statement wire is the new
per-module protocol (`spec-pin:` header lines, `spec/check_port.py`), not the frozen
`old_check_stmts.py` lists. Read this whole order before writing a line; read
[WORKORDER-LP1-localParam-finite-cover.md](WORKORDER-LP1-localParam-finite-cover.md)
for the house style of the sibling module and
[TOPIC-localParam-finite-cover.md](TOPIC-localParam-finite-cover.md) §2–§3 for how the
three leaves relate.

## 1. Scope

Port the pin `S_` file **whole** — 500 lines, 58 declarations — except the sixteen
declarations the port already has (§2(b)). The mathematics: two charts `γ`, `γ'` at
the same place (`γ' z₀' = γ z₀`), each `Pkg`-compatible with the meromorphic reading
of `evalAt`, agree *as places* near `z₀'` — `γ' z = γ ((γ' z).evalAt t)` eventually.
The proof is the standard one: write the difference of the two readings as
`D f = f(γ' u) - f(γ(h u))`, show `D f` is analytic and divisible by
`(h u - z₀)^N` for every `N` (the `le_order` induction, via the decomposition
`f = c + (t - z₀) f₁` at the place), hence `D f = 0`; then `eq_of_forall_ord_eq`.

**Not this set:** the third `localParam` leaf
(`exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex`, 1,142 lines) and its
three premise leaves — that is LP3/LP4; any edit to an existing module; any
`PORT_FILES`/`SOURCES` append.

Measured (playbook step 3, on the tree the LP1 landing leaves):

| quantity | value |
|---|---:|
| pin `S_` lines | 500 |
| declaration lines | 475 |
| net new math lines | **381** |
| declaration groups | 58 |
| port-importable (vetted) | **15** (≈107 lines) |
| public headlines | 1 |

## 2. Pre-round: done, and nothing new is owed

**(a) The definition layer is homed**, exactly as for LP1: `Defs/{Place,Divisor,
IsCurveOver,PlaceEvaluation,PlaceCalculus,PushPull,Repartitions}.lean` carry every
name the file uses. The pin imports only `Def_AlgebraicCurve_{DivisorClassGroup,
IsCurveOver,PlaceEvaluation}` plus `P2M.Util`, and LP1 verified the whole API.

**(b) Fifteen declarations are already in the port — import them, never restate.**
`port_advise` (shape-aware; playbook §3 step 3) reports 12 substitutions and 4 more in
its residue list, of which 16 pointers resolve to 15 real pin rows (`Pkg.eventually_mem`
and `Setup.eventually_mem` are *different* lemmas — the traps below). The pin file's
21-row prelim section splits as:

| pin line | lemma | port home |
|---:|---|---|
| 26 | `adicValuation_le_one_of_mem` | `Place.adicValuation_le_one_of_mem` (`Defs/Repartitions.lean`) |
| 32 | `adicValuation_eq_exp_neg_ord` | `Place.adicValuation_eq_exp_neg_ord` (`Defs/Repartitions.lean`) |
| 37 | `mem_of_ord_nonneg` | `Place.mem_of_ord_nonneg` (`Defs/PushPull.lean`) |
| 45 | `ord_nonneg_of_mem` | `Place.ord_nonneg_of_mem` (`Defs/PushPull.lean`) |
| 53 | `ord_pos_of_mem_maximalIdeal` | `Place.ord_pos_of_mem_maximalIdeal` (`Place/OrdCalculus.lean`) |
| 67 | `residue_eq_zero_of_ord_pos` | `Place.residue_eq_zero_of_ord_pos` (`OrdCalculus`) |
| 79 | `isRational_of_isCurveOver` | `Place.isRational_of_isCurveOver` (`OrdCalculus`) |
| 85 | `evalAt_algebraMap` | `Place.evalAt_algebraMap` (`Defs/PlaceEvaluation.lean`) |
| 92 | `residue_algebraMap` | `Place.residue_algebraMap` (`OrdCalculus`) |
| 99 | `evalAt_sub_algebraMap` | `Place.evalAt_sub_algebraMap` (`OrdCalculus`) |
| 109 | `evalAt_mul` | `Place.evalAt_mul` (`Defs/PlaceEvaluation.lean`) |
| 117 | `evalAt_eq_zero_of_ord_pos` | `Place.evalAt_eq_zero_of_ord_pos` (`OrdCalculus`) |
| 123 | `ord_pos_of_evalAt_eq_zero` | `Place.ord_pos_of_evalAt_eq_zero` (`OrdCalculus`) |
| 158 | `evalAt_zero` | `Place.evalAt_zero` (`Defs/PlaceCalculus.lean`) |
| 161 | `evalAt_add` | `Place.evalAt_add` (`Defs/PlaceCalculus.lean`) |

plus `Place.ord_algebraMap` (`Defs/Place.lean`) and `Place.ord_sub_evalAt_pos`
(`Defs/PlaceCalculus.lean`), which the proofs use. **Do not restate any of them.**

**Two traps in the shape advice.** `port_advise`'s residue list also points at
`AlgebraicCurve.Place.FiniteCover.Fam.isRational` (for the pin's `Setup.isRational`,
line 281) and at `…Fam.eventually_mem` (for the pin's `Pkg.eventually_mem` line 216
and `Setup.eventually_mem` line 321). The first two are *different declarations that
happen to have identical statement text* — `Fam.isRational` takes an implicit
`P : Fam F`, so it is not the port's `Setup.isRational`, which is the pin's one-liner
`isRational_of_isCurveOver w`. The `eventually_mem`s are likewise new mathematics at
the `Pkg`/`Setup` level; `Fam.eventually_mem` is about `Fam.γ` near `0`, not about
`γ u` near `z`. Import nothing from `FiniteCover.lean` for these; write the pin's
statements.

**So 43 declarations are new** (58 pin rows − 15 importable): the six remaining
prelim lemmas (`evalAt_eq_of_ord_sub_algebraMap_eq_one`,
`mem_of_ord_sub_algebraMap_eq_one`, `ne_zero_of_ord_eq_one`, `evalAt_of_not_mem`,
`evalAt_eq_inv_evalAt_inv`, `eq_of_forall_ord_eq`), `Pkg` (a `def … : Prop`) with its
three lemmas, `evalAt_decomp`, the `structure Setup` with its eleven fields and thirty
lemmas, and the headline. (The two further names this order originally listed,
`Place.ord_algebraMap` and `Place.ord_sub_evalAt_pos`, are used by the proofs but are
not pin declarations of this file; they are imported all the same.)

**(c) No hub edit, no promotion.** Nothing in this set needs an existing module
changed: every importable lemma is public and lives at the pin's name.

## 3. Source

Pinned `anthropics/fermats-last-theorem@aa2d8b3`:

* statement: `Theorems/Thm_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean`
  (24 lines; `spec-pin:` source for the headline);
* proof: `P2M/Sol/S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean`
  (500 lines; `spec-pin:` source for the 42 internal declarations).

Rendered:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean>
and
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean>.

`python3 spec/statement_db.py show AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex`
prints the pin signature with its `file:line`; `rg -n 'localParam_eventually_eq_comp' tmp/flt-statements/statements.tsv`
gives all 58 rows.

## 4. Deliverable

**4.1 Home.** `FLTForHuman/AlgebraicCurve/Place/BranchUniqueness.lean`, namespace
`AlgebraicCurve.Place.BranchUniqueness` for the internal development (the pin's own
silo name; it keeps `Pkg`/`Setup` out of the `Place` namespace), and the headline in
`AlgebraicCurve.Place`.

**4.2 Imports.** Start from

```lean
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
```

and add only what the edit loop demands (the analysis names — `MeromorphicAt`,
`meromorphicOrderAt`, `AnalyticAt`, `analyticOrderAt`, `HasDerivAt` — come from
specific mathlib modules; LP1's `Place/FiniteCover.lean` header lists the ones the
cone needed: `Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv`,
`Mathlib.Analysis.Meromorphic.NormalForm`, `Mathlib.Analysis.Complex.Polynomial.Basic`,
`Mathlib.Analysis.SpecialFunctions.Complex.Analytic`). **Never `import Mathlib`.**

**4.3 Namespace map.**

```lean
namespace AlgebraicCurve
namespace Place
namespace BranchUniqueness

section Prelim   -- the seven new prelim lemmas, under `variable {K F : Type*} [Field K]
                 -- [Field F] [Algebra K F]`
section Param    -- `variable (F : Type*) [Field F] [Algebra ℂ F]`: `Pkg` + 3 lemmas,
                 -- then `evalAt_decomp`
section Main     -- `structure Setup` (11 fields, pin order: γ γ' t U U' z₀ z₀' hU hU'
                 -- h₀ ht hγ hγ'), `def h`, `def D`, then `namespace Setup` with the
                 -- thirty lemmas and `main`

end BranchUniqueness
end Place

-- the headline, at the wrapper's name and text
theorem AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex …
end AlgebraicCurve
```

Keep the pin's `variable` shape (section variables, **not** explicit `{K F : Type*}`
binder blocks): the checker hashes the statement text. Keep the `omit [IsCurveOver ℂ F] in`
lines and the pin's `@[scoped simp]` attributes if any.

**4.4 The headline.** Exactly as the wrapper (that text is the checker-comparable
statement; carry the `-- pin:` marker above it):

```lean
-- pin: AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex (Theorems/Thm_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean:11)
theorem AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex
    (F : Type*) [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    (γ γ' : ℂ → Place ℂ F) (t : F) (U U' : Set ℂ) (z₀ z₀' : ℂ)
    (hU : U ∈ 𝓝 z₀) (hU' : U' ∈ 𝓝 z₀') (h₀ : γ' z₀' = γ z₀)
    (ht : ∀ z ∈ U, (γ z).ord (t - algebraMap ℂ F z) = 1)
    (hγ : ∀ f : F, f ≠ 0 → ∀ z ∈ U,
        MeromorphicAt (fun u : ℂ => (γ u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ u).evalAt f) z = ((γ z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ u).evalAt f) z))
    (hγ' : ∀ f : F, f ≠ 0 → ∀ z ∈ U',
        MeromorphicAt (fun u : ℂ => (γ' u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ' u).evalAt f) z = ((γ' z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ' z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ' u).evalAt f) z)) :
    ∀ᶠ z in 𝓝 z₀', γ' z = γ ((γ' z).evalAt t) :=
  BranchUniqueness.Setup.main ⟨γ, γ', t, U, U', z₀, z₀', hU, hU', h₀, ht, hγ, hγ'⟩
```

(The pin's `solution` body is exactly this: instantiate `Setup` and apply `main`.)

**4.5 The module header.**

```lean
/-
  … one paragraph: the second of the three `localParam` leaves, that the 20-lemma
  prelim block is imported from `Place/OrdCalculus.lean` and `Defs/` (16 declarations,
  listed), and the module's role (tier 1, one headline).

  spec-pin: Theorems/Thm_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.lean
-/
```

## 5. Route

**5.1 Reuse.** The bare names resolve: inside `namespace BranchUniqueness` a use of
`evalAt_sub_algebraMap` finds `AlgebraicCurve.Place.evalAt_sub_algebraMap`. Use them
unchanged; do not re-derive and do not restate.

**5.2 Faithfulness.** Transcribe statements and proof bodies; adapt only what mathlib
`v4.34.0` forces. Two points the pin's proofs lean on that the AC friction log
([../../logs/ac-port.md](../../logs/ac-port.md) §11.2) flags as recurring drift:
`meromorphicOrderAt` API names and the `WithTop ℤ` coercions (`exact_mod_cast`,
`push_cast`), and `if_pos`/`if_neg`/`dif_pos`/`dif_neg`, which are deprecated in
`v4.34.0` — LP1 took `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right`
instead, to keep 0 warnings. Prefer the new names in proofs; statements keep the pin's
text.

**5.3 Stop-early risks, with the deviation protocol.**

* `structure Setup` is hashed by the checker as header + ordered field names +
  field-type text. Keep the field order `γ γ' t U U' z₀ z₀' hU hU' h₀ ht hγ hγ'` and
  the exact types.
* If a proof needs a `private` helper of an existing module, **stop and report** with
  the declaration, host and `build_ladder.py --edit` price; re-derive it locally
  `private` if cheap. Do not promote.
* If an instance/`haveI` warning appears, narrow it on the one declaration (LP1 did
  this once, on `isRational_of_isCurveOver`) and report it.

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
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.BranchUniqueness`.
Every tool call must finish within **2 minutes**; no loop may circumvent that.

## 7. Hub prohibition

This set adds **one** module and edits **no** existing file. No `PORT_FILES`/`SOURCES`
entry, no `git commit`, no promotion. A subagent that believes a promotion or a host
edit is required **stops and reports** with the declaration, host and the
`build_ladder.py --edit` price.

## 8. Verification

```bash
cd lean
python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Place/BranchUniqueness.lean   # expect 43 ok
python3 spec/check_port.py --changed                                                # 3 modules, 0 failing
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.BranchUniqueness
```

plus:

* `#print axioms AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex`
  — `[propext, Classical.choice, Quot.sound]`;
* grep sweep of the module for `sorry` / `admit` / `axiom` / `native_decide` /
  `import Mathlib` / `maxHeartbeats` — all zero;
* tier 1 green, **0 warnings**;
* `git status --short` showing only the new module;
* the frozen checker **unchanged at 10473** (`timeout 280 python3 spec/old_check_stmts.py`);
* `python3 tools/deps/frontier.py --ds --target AlgebraicCurve.Place.localParam_eventually_eq_comp_evalAt_complex --top 5`
  should read `needed 0` once the module is in the tree (the `names` tier scans it) — a
  one-line check that the landing is credited.

## 9. Report shape

Report: (1) module path, line count, declaration count and the 43/15 split as realized;
(2) `spec/check_port.py` output with the pin line each declaration matched; (3) build
result and warning count; (4) the axioms line; (5) the grep sweep and `git status`;
(6) every deviation (adapted proofs are expected; a changed statement or dropped
hypothesis is not); (7) the two `eventually_mem`s and `Setup.isRational` written as the
pin has them rather than imported from `FiniteCover.lean`, confirming §2(b)'s traps
were avoided; (8) what the landing leaves on the shelf (expect the third `localParam`
leaf to remain, plus its three premise leaves).
