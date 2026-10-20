# WORKORDER-SU1 — a uniformiser at a place is a separating element (twin heads)

**Status (closed 2026-10-20): landed and reviewed green.** One set, **one module, two public
headlines**, one host edit. Measured: `FLTForHuman/AlgebraicCurve/Place/SeparableUniformiser.lean`,
**149 lines**, **2 statement-checked declarations**; `spec/check_port.py` **2 ok / 0 mismatch / 0
missing**; tier-1 build 2,694 jobs, 3.9 s, **0 warnings**; axioms `[propext, Classical.choice,
Quot.sound]`; the frontier reads `needed 0` for both nodes. The host edit promotes three
declarations of `AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean` and hands that module over to
`spec/check_port.py` (4 ok); its dependent wave is 5 modules, built green.

The rows are the ready-shelf leaves
`AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one` (455-line `S_` file, cited by **23**
theorems) and its **twin**
`AlgebraicCurve.Place.isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero` (460), pinned
`aa2d8b3`. The twin pair is why the set is one: the two pin files differ by **33 diff lines** —
three imports, the namespace, one `synthInstance.maxHeartbeats` line, the order-theoretic helper,
and one hypothesis of `solution` — and share the other 400 lines byte for byte.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the per-module protocol — `spec-pin:` header, `spec/check_port.py`, no in-source
per-declaration marker.

## 1. Scope

For a perfect `K`, `F` algebraic over `K(x)` for some `x`, and a place `v` of `F` over `K`:

* `isSeparable_adjoin_of_ord_eq_one`: `v.ord t = 1` ⟹ `K(t) → F` separable — a uniformiser is a
  separating element;
* `isSeparable_adjoin_of_ord_ne_zero_of_cast_natAbs_ne_zero`: `v.ord t ≠ 0` and
  `((v.ord t).natAbs : K) ≠ 0` ⟹ separable — an element of nonzero tame order separates.

The mathematics is the classical separability criterion of Stichtenoth §III.9/§IV.1 in positive
characteristic: if the `p`-th-power Frobenius subfield of `F` has index `p` and `t` is not a
`p`-th power, then `F/K(t)` is separable. The order enters twice — `ord t ≠ 0` makes `t`
transcendental, and `ord t = 1` (or a tame order) rules out `t = a ^ p`.

| block | pin lines | the mathematics | port |
|---|---|---|---|
| `SEPEngine` generic part | 22–355 | the Frobenius subfield `frobeniusSubfield`, its `comap`/`map` transport, the index computation `finrank_frobeniusSubfield_adjoin_transcendental`, the transport `finrank_frobeniusSubfield_eq` and the `p`-digit expansion — 18 declarations, no adèles, no `GL₂` | **already in the port**, private in `IsCurveOver/FrobeniusSubfield.lean` (§2) |
| `SEPEngine` separability part | 357–405 | `not_pow_of_ord_eq_one` (or its tame twin), `D_pow_eq_zero`, `isSeparable_of_not_pow_mem_range` | **one helper re-proved**, two **not ported** (§3) |
| `solution` | 407–455 | the headline | **re-proved**, once for both heads |

**Not this set:** the 23 consumers of the headline (§6); the pin's `Def_AlgebraicCurve_Differentials`
walk beyond the substitution of §3; any edit to a module other than the one host of §2.

## 2. Measurement, and the host edit it forces

`tools/deps/port_advise.py --target … --json build/sepUnif_advise.json`,
`port_plan.py --json build/sepUnif_advise.json`, on the tree the previous landing left:

| quantity | value |
|---|---:|
| pin `S_` lines (headline 1) | 455 |
| declaration lines | 430 |
| boilerplate (imports/attrs/`p2m`) | 25 |
| distinct declaration groups | 23 |
| already in the port (vetted) | **337** (19 declarations) |
| byte-identical / shape-tier / suspect | **19 / 0 / 0** |
| **net new math lines** | **93** |

18 of the 19 in-port declarations were **private in the host**, so they are not importable: the
port could not simply import the engine it already owns. The pre-round is therefore a **promotion**
in `AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean` — and only of what a consumer states:

* `frobeniusSubfield` (the `def`: the `p`-th-power subfield, the object of the subject),
* `finrank_frobeniusSubfield_adjoin_transcendental` (its index for a transcendental simple adjoin),
* `finrank_frobeniusSubfield_eq` (its transport across a finite extension).

The other fifteen stay `private`: their proofs are internal to the host and no consumer states
them. The host is **handed over** in the same edit — `spec-pin:` lines in, `PORT_FILES` entry out
(the playbook §4 handoff) — because a promoted declaration in a frozen-registry module would be
verified by no checker at all under the one-checker protocol (§6 of the column note).

Priced with `build_ladder.py --edit` before applying: **5 dependent modules / 1,752 lines ≈ 26 s**
(`ConstantFieldExtension` 695, `QExpModL` 608, `PerfectField` 181, `X1/Structure` 175,
`Transcendental` 93). Measured wave build: 4,329 jobs, 42 s, green; the one warning printed is
`QExpModL`'s pre-existing `unusedSectionVars` linter note, not from this edit.

## 3. What is *not* re-proved: the criterion already has a general form

The pin proves a private `isSeparable_of_not_pow_mem_range` inside both silos: given
`finrank (frobeniusSubfield M p) M = p`, `t ∈ algebraMap.range` and `∀ a, a ^ p ≠ t`, the extension
is separable; its proof goes through `D F = 0` (`D_pow_eq_zero`), `Subsingleton Ω[F⁄E]` and
`FormallyUnramified.isSeparable`.

**That theorem is already public in the port**, as
`Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq`
(`Algebra/IsSeparableFrobenius.lean`, homed from the pin's
`S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq.lean`), in the same form up to spelling:
`frobeniusSubfield M p` is *defined* as `(frobenius M p).fieldRange`, and `t ∈ range ∧ ∀ a, a^p ≠ t`
is the element form of `algebraMap y ∉ fieldRange`. So the module **calls** it, with
`frobeniusSubfield` substituted by its definition at the call, and neither `D_pow_eq_zero` nor
`isSeparable_of_not_pow_mem_range` is ported. This is the `Place.exists_restrict_eq` pattern of
WORKORDER-DC1, and the def walk is one line: `Def_AlgebraicCurve_Differentials` is used *only* by
the two helpers not ported, so no definition work is owed by this set.

What remains genuinely new is the place side — `not_pow_of_ord_eq_one` ("`ord t = 1` excludes
`p`-th powers", 10 lines) and its tame twin `not_pow_of_cast_natAbs_ord_ne_zero` (order arithmetic
modulo `CharP K p`) — plus the `solution` body, and the twin pair lets the body be written once.

**Deliverable:** `FLTForHuman/AlgebraicCurve/Place/SeparableUniformiser.lean`, **149 lines**:

* `import` the general criterion, the host engine, `Place/DegreeOne.lean` (the transcendence
  transfer) and `Place/TranscendentalOfOrdNeZero.lean` (the two premises), plus
  `Mathlib.FieldTheory.Perfect`;
* `private not_pow_of_ord_eq_one`, `private not_pow_of_cast_natAbs_ord_ne_zero` — the two order
  helpers, transcribed from the pin;
* `private separable_of_transcendental_of_forall_not_pow` — the pin's `solution` body, once,
  parametrized by `htr : Transcendental K t` and `htp : ∀ p, p.Prime → CharP K p → ∀ a, a^p ≠ t`;
* the two public headlines, each supplying its own helper.

Public: the two headlines. Private: the three helpers. No tier-3 module, nothing registered.

## 4. Route and recorded negatives

* **The characteristic split stays inside the engine.** `ExpChar.exists K` gives `q = 1` (then
  `CharZero K(t)` and `infer_instance`) or a prime (then the Frobenius index `p = q`). The
  `CharP K p` that the tame helper needs is only available *inside* that split, so the engine takes
  `htp` with `CharP K p` explicit — a parameter, not an instance, at the two call sites.
* **The twin's `set_option synthInstance.maxHeartbeats 800000` is not inherited.** It is a
  30× instance-synthesis allowance, and the port needs none of it: the engine elaborates under the
  set's 200,000 cap and no declaration of the module sets a cap. (If it had needed it, the move
  would have been to diagnose the inference, not to copy the line.)
* **One `haveI` in the whole module**, in `not_pow_of_cast_natAbs_ord_ne_zero`, where the explicit
  `hchar : CharP K p` must become the instance `CharP.cast_eq_zero` consumes. Narrowly suppressed
  (`set_option linter.style.haveILetI false in` on that declaration); the engine's instance walls
  carry the same narrow suppression, with no file-wide option.
* **No `p2m_export`/`open` plumbing.** The pin's `open _root_.AlgebraicCurve
  _root_.P2MW.S_….AlgebraicCurve AlgebraicCurve.SEPEngine IntermediateField in` is gone: the port's
  engine lives in `AlgebraicCurve.PthPowerIndex` (opened) and `Place`'s own namespace, and the
  `attribute [-instance]` / `[-simp]` preludes of the wrapper are not copied — no proof needs them.
* **The two headlines are separate theorem statements**, not one with a disjunction: each is the
  pin's wrapper verbatim, and the checker verifies both.

## 5. Build discipline (verbatim)

```
tier 0  edit loop    timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>
tier 1  module done  flock .lake/flt_build.lock timeout 300 lake build <module>
tier 2  wave         the host edit's 5 dependents, once
tier 3  milestone    no whole-tree build without the user's permission
```

## 6. Successors this landing unblocks

`frontier.py --ds --rank-by silo --ready` now shows, each with every premise ported:

| row | silo lines | cone (ported / total) |
|---|---:|---|
| `AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable` | **576** | 5 / 6 nodes, 274 lines |
| `AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_eq_one` | 28 | 4 / 5, 614 |
| `AlgebraicCurve.Place.diffCoeff_smul_D_eq_of_ord_eq_one` | 26 | 4 / 5, 613 |
| `AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable` | 20 | 38 / 39, 2,967 |

The first is the natural next cut (it is the `ordDiff`-nonnegativity half of the differential
layer, and it is what the `diffCoeff` rows then consume). The 23 project consumers of the headline
include the genus rows of `ModularCurve/Frobenius/` and the `IsCurveOver` separability family.

## 7. Verification (measured on the tree this set leaves)

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Place/SeparableUniformiser.lean
#   [ok]  2 ok, 0 mismatch, 0 missing, 0 own, 0 kw
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean
#   [ok]  4 ok, 0 mismatch, 0 missing   (3 promotions + the headline)
python3 spec/check_port.py --all
#   1822 ok, 0 mismatch, 0 missing, 4 own, 0 kw — 47 module(s), 583 exempt (PORT_FILES)
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.SeparableUniformiser
#   ✔ 2,694 jobs (3.9s)
flock .lake/flt_build.lock timeout 300 lake build <the host's 5 dependents>
#   ✔ 4,329 jobs (42s)
python3 spec/unwired_register.py --check      # register is current
```

plus the `#print axioms` probe on both headlines, the `grep` sweep on the two edited modules
(no `sorry`/`admit`/`axiom`/`native_decide`/heartbeat override) and `git status` showing the two
set files, the host module and the one line removed from `spec/old_check_stmts.py`.

`spec/old_check_stmts.py` is not run. The only change to it is the **handoff deletion** of the
host's `PORT_FILES` entry (§2) — no append, and its count is history.

## 8. Report shape

The statement is each wrapper's text, verbatim and separately (checker `ok` twice); the module adds
no public declaration beyond the two headlines; the pin's `D_pow_eq_zero`/`isSeparable_of_not_pow_mem_range`
are absent *by substitution* with a recorded general theorem, not by suppression; the host gained
exactly three public declarations and a wire; the cascade is priced, built once, and green.
