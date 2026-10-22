# WORKORDER-RPF1 — the residue map preserves finrank (regular prolongation)

**Status: landed (2026-10-22).** One new module, no existing module edited; the measured reading is
§9. The node was a ready leaf of the D-S demand: its only premise, the `RegularProlongation`
definition layer, is ported and wired, and the silo cites no other pin node.

## 0. The node, and its statement

`AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank` — pin `S_` file 787 lines, 27
theorems/lemmas + 2 defs, 28 public (plus one `_root_.`-escaped helper the tools mis-classify; §3).

Statement authority, `Theorems/Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.lean`:

```lean
theorem AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) =
      Module.finrank L V
```

One sentence: along a regular prolongation, the residue map carries an `L`-span of integers onto a
span of the same dimension over the residue field — the dimension-transport step behind
residue-degree and genus computations.

**Measured price** (`port_advise` + `port_plan`, 2026-10-22): raw 787 → **769 net new math lines**,
0 duplicate, 0 already in the port, 0 substitutions; 29 distinct declaration groups, one of them the
pin's own `private` helper. Size the dispatch as one set, not a leaf.

**Not this set.** The node's six pin consumers (`RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq`,
`…exists_finset_forall_valuation_eq_one_forall_exists_degree_eq_and_ell_eq`,
`Divisor.finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction`, and the three
`ModularCurve.{FullLevel,genusFF…}` files) are separate orders. Do not edit any existing module.

## 1. Deliverable

**One new module**, `FLTForHuman/AlgebraicCurve/RegularProlongationFinrank.lean`.

* The definition module `FLTForHuman/AlgebraicCurve/RegularProlongation.lean` is a **hub** (it is
  imported by `AlgebraicCurve/GaussProlongation.lean` and `ModularCurve/X1/QExpRegularProlongation.lean`):
  **import it, never append to it.** The structure and its three lemmas stay where they are.
* Imports: `FLTForHuman.AlgebraicCurve.RegularProlongation` plus the narrow mathlib modules the proof
  needs (`RingTheory/Valuation/…`, `FieldTheory/IntermediateField/…`, `LinearAlgebra/Finrank/…`,
  `RingTheory/LocalRing/ResidueField/…`). No `import Mathlib`; `import Mathlib.Tactic` only if a tactic
  is genuinely needed.
* Header docstring in the port's style (see `RegularProlongation.lean`): what the module is, the pin
  source with pinned URLs (`aa2d8b3`), the `spec-pin:` lines, the drift note, `set_option autoImplicit false`,
  `noncomputable section`, `namespace AlgebraicCurve`, `open IsLocalRing`.
* **Namespace: `AlgebraicCurve.RegularProlongation`** — continue the existing one, so the structure's
  API and this development read as one subject. Two pin tokens are dropped, not translated:
  `P2MW.S_AutomorphicForm_…` (the pin's `S_` wrapper) and **`AJDFXA`** (a collision token with no
  meaning); `residue_eq_zero_iff` loses the pin's `_root_.` escape and is stated plainly.
* Keep the pin's phase sections as sections (`resIndep`, `adapted`, `frame`, `covering`, `core`,
  `assembly`) — they are proof phases, not names, and they make the 769 lines navigable.
* Public surface: the 28 pin-public declarations at the pin's last names (they are descriptive —
  `constHom`, `residue_constHom`, `exists_normalizer`, `exists_adapted`, `frame`,
  `linearIndependent_residue_frame`, `card_le_finrank`, `mem_of_mem_span`, …); the headline at the
  wrapper's name `AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank`; the pin's
  `solution` is the **private** assembly twin, not a public declaration.
* Drop the pin's `p2m_open`/`p2m_export`/`p2m_reactivate` staging and its `import P2M.Util` (the file
  never uses it — only the import line mentions it).

Wiring: two `spec-pin:` lines, wrapper first, then `P2M/Sol/S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.lean`
as the comparable copy. Expected reading: `0 mismatch, 0 missing, 0 own, 0 kw`, `ok` = the module's
public declaration count.

## 2. Reuse — call these, never restate

* `AlgebraicCurve.RegularProlongation` — the structure's fields (`integers`, `residue`,
  `algebraMap_mem_iff`, `residue_surjective`, `ker_residue`, `residue_algebraMap`,
  `exists_smul_mem`) and its three lemmas `isUnit_of_residue_ne_zero`,
  `residue_ne_zero_of_isUnit`, `smul_const_ne_zero`. The silo's `constHom`/normalizer arguments are
  built on exactly these; a private adapter is fine, a re-derivation is not.
* The pin cites **no other pin node** (its import block is `Mathlib`, the definition module, and the
  unused `P2M.Util`), so there is nothing to dedup against: if you find yourself proving a statement
  from another `AlgebraicCurve/` module, stop and report it (it would be a premise the graph missed).
* mathlib supplies the rest: `IntermediateField.adjoin`, `Module.finrank`, `ValuationSubring`,
  `IsLocalRing.ResidueField`, `Submodule.span`/`span_induction`.

## 3. Names

No rectification pass: the pin's declaration names in this silo are descriptive and stay. The only
edits are the two dropped tokens of §1 and the `_root_.` escape. One caution: the pin's
`theorem _root_.AlgebraicCurve.RegularProlongation.AJDFXA.residue_eq_zero_iff` is **pin-public**
(exported at the pin's line 38) although `port_advise` lists it as a helper, because the pin's
`_root_.` spelling defeats the parser. State it public at `AlgebraicCurve.RegularProlongation.residue_eq_zero_iff`;
if the checker then reports it as `MISSING` or as a `pin name …` note, **stop and report** — do not
privatise it to silence the diff.

## 4. Route

Follow the pin's own phases, in its order — each is a milestone you can elaborate:

1. `constHom` and the residue lemmas (`residue_constHom`, `residue_eq_zero_iff`, `coe_sum_constHom_mul`,
   `residue_sum_constHom_mul`, `residue_coeff_eq_zero`), then `exists_normalizer`;
2. `resIndep`: `mem_of_sum_smul_mem`, `valuation_lt_one_of_sum_smul_mem`, `linearIndependent_coe`;
3. `adapted`: `exists_adapted`;
4. `frame`: `aeval_eq_linearCombination`, `linearIndependent_pow_iff_transcendental`, `frame`,
   `linearIndependent_residue_pow`, `linearIndependent_residue_frame`, `linearIndependent_coe_frame`;
5. `covering`: `linearIndependent_adjoin`, `linearIndependent_adjoinField`, `exists_repr_adjoinField`,
   `exists_normalize_aeval`, `exists_unit_mul_mem_span`, `exists_residue_linearIndependent`;
6. `core`: `card_le_finrank`, `mem_of_mem_span`, `finrank_span_residue_eq_finrank'`;
7. `assembly`: `solution` (private) and the headline at the wrapper's statement.

Statements are the pin's verbatim (`Theorems/` wrapper for the headline, `S_` file for the rest);
proofs may be adapted where mathlib has moved (§6).

## 5. Build discipline — read before the first compile

From `lean/`, always through the lock:

```bash
flock .lake/flt_build.lock timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AlgebraicCurve/RegularProlongationFinrank.lean
```

* `lake env lean` builds nothing and writes no `.olean`; the two `-D` flags are mandatory (the
  lakefile options are not inherited). A finished file:
  `flock .lake/flt_build.lock timeout 120 lake build FLTForHuman.AlgebraicCurve.RegularProlongationFinrank`.
* **The 200,000 cap is a diagnostic.** No `set_option maxHeartbeats`, no
  `synthInstance.maxHeartbeats`, ever — the pin's own bumps are not inherited.
* **Bound the floor first**: a copy in `lean/tmp/` with every proof `sorry` (statements, defs,
  instances verbatim) gives the module floor in one run. If the floor aborts, no proof edit can reach
  it: the cost is in the frozen types. Levers in order: a section variable no statement uses becomes
  a `haveI`/term-`letI` in the proof that needs it; `private abbrev` aliases; then stop and report.
* **Probes, not bisection** (`porting-playbook.md` §3.5): statement-vs-proof first; then isolate the
  declaration with earlier proofs stubbed; then shrink the statement, not the file; one
  `set_option diagnostics true` trace kept per module; `trace.Meta.isDefEq` at
  `-DmaxHeartbeats=3000` only if needed. A probe that cannot finish in 60 s is the probe's fault.
* **Bound, do not measure**: no `time`, no durations. Anything that can run a minute is a background
  job with its own `timeout` and a log you read afterwards. One probe, one edit, one bounded compile
  per turn; every tool call under two minutes. Never a whole-tree build.
* Note for this silo: the risk is not tactic length but instance inference over
  `Submodule.span`/`IntermediateField.adjoin` of `ResidueField A` — if a declaration trips, the fix is
  a syntactic form for the type (the pin's own `inferInstance`), not a bump.

## 6. Gates

```bash
cd lean
flock .lake/flt_build.lock timeout 120 python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/RegularProlongationFinrank.lean
# expected: 0 mismatch, 0 missing, 0 own, 0 kw, ok = the module's public declaration count
python3 spec/check_port.py --changed --strict-markers
```

plus: the module elaborates at 200k with **0 warnings**; `#print axioms` on the headline is
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`native_decide`/`import Mathlib`; the
only `set_option` is `autoImplicit false`; `git status` shows exactly one new file.

## 7. Stop and report — do not improvise — if

* an edit to an existing module seems necessary (give the declaration, the host, and
  `tools/deps/build_ladder.py --edit <host>`'s price);
* the pin's proof needs a statement from another pin node (the graph says it cites none);
* a heartbeat raise looks necessary (give the statement-only probe at 200k and the reading);
* the headline reads `MISMATCH`, or `residue_eq_zero_iff` reads `MISSING` (§3);
* a `pin:` row in `spec/decl_markers.tsv` looks needed.

## 8. Report shape

(i) the module's lines and declaration count, the public/private split, its public surface; (ii) the
checker reading, `--changed --strict-markers`, and the build's jobs/warnings; (iii) axioms; (iv) every
proof deviation from the pin with its site and the mathlib drift it answers; (v) the names carried
over and the two tokens dropped; (vi) what belongs in CARRY-FORWARD.md; (vii) `git status`. Include the
floor probe (seconds, or "aborts at 200k") and the pin line ranges consumed.

Records: [TOPIC-mathlib-module-homing.md](../TOPIC-mathlib-module-homing.md) (home and namespace),
[porting-playbook.md](../../porting-playbook.md) §3.1–§3.5 and §4–§6 (the order shape, the ladder, the
checker, the failure modes).

## 9. Landed (2026-10-22)

`FLTForHuman/AlgebraicCurve/RegularProlongationFinrank.lean` — **904 lines, 30 declarations = 29
public + 1 private** (`solution`, the pin's assembly twin, private at :861). Namespace
`AlgebraicCurve` → `AlgebraicCurve.RegularProlongation` (the existing one); the pin's `P2MW.S_…`
wrapper and `AJDFXA` token namespaces, its `p2m_*` staging, its `_root_.` escape and its unused
`import P2M.Util` are gone; the six phase sections are kept.

| gate | reading |
|---|---|
| `check_port --force` (module) | **29 ok**, 0 mismatch, 0 missing, 0 own, 0 kw; headline → `Theorems/Thm_…:8`; `residue_eq_zero_iff` → `P2M/Sol/S_…:33` (the §3 caution did not fire) |
| `--changed --strict-markers` | 4141 ok, 0 / 0, 12 own (pre-existing), 0 kw — 164 modules, 0 stale markers |
| `lake build …RegularProlongationFinrank` | 2,521 jobs, green, **0 warnings** |
| edit loop at 200k | exit 0, empty log |
| axioms (headline and `…'`) | `[propext, Classical.choice, Quot.sound]` |
| hygiene | only `set_option autoImplicit false`; no `sorry`/`admit`/`native_decide`/`import Mathlib` |

**Floor**: statements are cheap — a `sorry`-stubbed copy elaborates at 200k in one pass, so no
instance-inference floor and no bisection; the whole 904-line module closes at 200k in one bounded
pass (6.8 s in the tier-1 build).

**Proof deviations (5, none in a statement).** (1) `mem_of_mem_span`'s smul case: the pin's
`rw [map_mul, residue_constHom, ← hα, Algebra.smul_def]` installs the `Ideal.Quotient` spelling of the
scalar in v4.34 and the `SMul (A ⧸ maximalIdeal A) Fbar` instance is then invisible at `implicit`
transparency; rewritten through `have hα' : IsLocalRing.residue A α = κ := hα`, which keeps the scalar
syntactic (now a drift-table row, playbook §7). (2) 14 `dif_pos`/`if_pos`/`if_neg` sites replaced by
`dite_eq_left`/`ite_eq_left`/`ite_eq_right` (`@[deprecated]` since 2026-07-21). (3) four `haveI` →
`have` for `linter.style.haveILetI`, all `Prop`-valued classes, no linter suppression. (4) the
headline's proof applies the twin as `solution A R x hx hfin hdeg V` (its `A` is explicit where the
pin's wrapper applied every binder implicitly). (5) nothing else — every other proof body is the
pin's text, including the `include` discipline and the `Module.finBasis` index trick.

**Effect on the frontier**: `F` 1145 → **1146** nodes (+787 lines), the D-S demand 1230 → **1229**
nodes / 467,399 → **466,612** lines, and the node no longer appears in the `--include-leaves` list.
Its six consumers are unported, so nothing was unblocked at the front line: the two in-demand ones
(`residue_integralClosure_surjective_of_genusFF_eq`, the `Divisor` finrank node) are now one premise
closer.

**Pin ranges consumed**: `P2M/Sol/S_…` 19–787 (19–56 prelude, 57–159 `resIndep`, 161–277 `adapted`,
279–418 `aeval`+`frame`, 420–542 `covering`, 544–618 `core`, 620–762 `assembly`, 764–787 `solution`);
`Theorems/Thm_…` 8–23, the headline statement only.
