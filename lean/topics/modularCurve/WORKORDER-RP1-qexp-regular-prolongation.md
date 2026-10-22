# WORKORDER-RP1 — the Gauss regular prolongation of the q-expansion valuation

**Status: ready to dispatch (2026-10-21).** Manager's ground is frozen (§2); no existing module may be
edited. This set is pure addition: one new module, three headlines.

## 0. The set

Three ready nodes on the D-S ready shelf — it was rank #2 by silo before this order, and the two
siblings are its `used_by (cone)`:

| node | pin `S_` lines |
|---|---:|
| `ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC` | 853 |
| `…_residue_div` | 875 |
| `…_residue_mul_eq` | 875 |

One mathematics: the Deuring/Gauss regular prolongation of the valuation of
`laurentBaseChange L (qExpFunctionFieldC ℚ Γ)` at `q = 0`, with residue target
`qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ` — a `AlgebraicCurve.RegularProlongation` whose
integers are the Gauss ring (an element is integral iff it is `x/y` with `x, y` Laurent series over
`A`, `y` reducing nonzero, and `f · y = x`), whose residue is coefficientwise reduction, and whose
`exists_smul_mem`/`residue_surjective`/`ker` fields are the pin's. The two siblings add one
conjunct each: the residue is *multiplicative on the witness form*.

**The three pin files are one development.** `diff` between the target and each sibling shows only
the `namespace`/`p2m_open` lines plus a 7–8-line assembly tail: the shared block is byte-identical
through line 815. Port it **once**.

**Not this set.** (a) `ModularCurve.FullLevel.exists_regularProlongation_fieldBar_integers_eq`
(35 own lines, `needed` now 2) — it becomes ready when this lands and is the next cut, not now;
(b) any other `FullLevel`/Igusa/Gauss-ring node; (c) the `JOne.torsionGaloisRep` deferral; (d)
anything outside `ModularCurve/X1/`.

## 1. Deliverable

**One new module** `FLTForHuman/ModularCurve/X1/QExpRegularProlongation.lean`.

* Engine `private`, inside `namespace ModularCurve.QExpDeuring` (so the sibling's names are in scope
  without an `open`), each declaration with a `-- pin <file>:<line>` provenance comment;
* the **three headlines public** at `ModularCurve.` top level, after `end QExpDeuring` and
  `open QExpDeuring in` — the exact shape `FunctionFieldResidue.lean:996–998` already uses;
* **no other public declaration.** Everything else (`resHom_mem`, `resF`, `coe_resF`,
  `resF_ne_zero_iff`, `ker_resF`, `resF_surjective`, `resF_algebraMap`, `exists_smul_mem_resF`,
  `gaussProlongation`, `mem_integers_gaussProlongation_iff`, `residue_gaussProlongation`,
  `residue_gaussProlongation_mul`, `residue_gaussProlongation_mul_eq`, `main`) is `private`.

The three public statements are the `Theorems/` wrappers **verbatim** (binders included — they carry
`(L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L) (Γ : Subgroup (SpecialLinearGroup
(Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)`); the pin's wrappers are the statement authority.

Pin sources, pinned `aa2d8b3`:

* statements — `Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean`
  and the two `…_residue_{div,mul_eq}` wrappers;
* proofs — the matching `P2M/Sol/S_…` files (853 / 875 / 875 lines).

Wire the module by its own `spec-pin:` header, **wrappers first**, then the three `S_` files (a
listed `S_` file shadows its wrapper for last-name matching unless the wrapper comes first).

## 2. Frozen ground — reuse, never restate

Import list (this is the whole of it; add nothing else without reporting):

```lean
import FLTForHuman.ModularCurve.X1.FunctionFieldResidue   -- the QExpDeuring engine (below)
import FLTForHuman.ModularCurve.X1.Defs                   -- intSeriesC / intFormRatiosC / qExpFunctionFieldC
import FLTForHuman.AlgebraicCurve.RegularProlongation     -- the structure
import FLTForHuman.RingTheory.PowerSeries.Saturation      -- the one premise (below)
```

Available and **must be called, not re-proved**:

| name | home | role |
|---|---|---|
| `ι`, `ϖ`, `IsInt`, `IsInt.{zero,one,mul,add,neg,cross,inv_of}`, `intSeriesA`, `ι_intSeriesA`, `ϖ_intSeriesA`, `ι_C`, `ϖ_C`, `ι_injective`, `ι_eq_zero_iff`, `ϖ_eq_zero_iff`, `ϖ_ne_zero_ne_zero` | `QExpDeuring` | the pin's whole `Coeff` section — drop it |
| `gaussRing`, `mem_gaussRing_iff`, `exists_witness`, `wit`, `wit_spec`, `resL`, `resL_eq`, `resHom`, `resHom_eq`, `resHom_algebraMap`, `algebraMap_mem_gaussRing_iff`, `resHom_eq_zero_iff`, `coe_algebraMap`, `exists_frac_form` (3 conjuncts) | `QExpDeuring` | the pin's `Gauss` block, stated for an arbitrary `Γ` — **strictly stronger than the pin's**, whose `hT` argument exists only because its route needs `Lam` |
| `exists_resHom_eq` | `QExpDeuring` | *is* the pin's `resF_surjective` (3 lines to adapt) |
| `intSeriesC`, `intFormRatiosC`, `qExpFunctionFieldC`, `intFormRatiosC_subset`, `div_mem_qExpFunctionFieldC`, `mem_intFormRatiosC`, `restrictForm` | `X1/Defs` | the definition layer |
| `PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated` | `RingTheory/PowerSeries/Saturation` | **the pin's one premise** (`Theorems/Thm_PowerSeries_…`), ported and wired; the pin calls it at its `exists_primitive_of_mem_homSpan` |
| `coeffEmb`, `coeffEmb_coeff`, `coeffEmb_injective`, `coeffEmb_mem_laurentBaseChange`, `algebraMap_laurentSeries_eq_single`, `algebraMap_apply_eq_single`, `coeffMap*` | `Defs/Laurent` (via `X1/Defs`) | the `BaseChange` section |
| `ModularForm.qExpansion_{add,neg,mul_coe,smul}`, `ModularFormClass.periodic_comp_ofComplex` | **mathlib** | the `Lam` layer's transport lemmas |

Two recorded negatives:

* **Do not port `resRange`, `qExpFunctionFieldC_le_resRange` (pin 711, 747, 56 lines) or the pin's
  `resF_surjective` proof.** `QExpDeuring.exists_resHom_eq` is the same `Subfield.closure_le`
  argument; `resF_surjective` becomes three lines. This is the single largest saving available.
* **Do not write a `one_mem_strictPeriods` lemma** for the `Lam` layer. The fact is mathlib's
  (`Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem`, `@[simp] strictPeriods_Gamma1`); write
  `by simp` at the site, or one `private` one-liner if it is used twice or more in this file.

## 3. The crux — `resHom_mem`, and the one block that is genuinely new

Grepping the pin's call sites settles the shape of the file:

```
420  theorem exists_frac_form (f : FF) (hf : f ≠ 0) : ∃ c, … ∧ ϖ u₀ / ϖ w₀ ∈ qExpFunctionFieldC kk Γ  -- 4 conjuncts
483  obtain ⟨…, h, -⟩ := exists_frac_form …   -- gaussRing's mem_or_inv_mem'  (4th discarded)
642  obtain ⟨…, h, -⟩ := exists_frac_form …   -- exists_smul_mem_gaussRing   (4th discarded)
656  obtain ⟨…, hfrac, hmem⟩ := …             -- resHom_mem                 ← the only consumer
650  theorem resHom_mem (f : gaussRing A hT) : resHom A hT f ∈ qExpFunctionFieldC kk Γ
```

`resHom_mem` is the **only** pin declaration in the file with no ported counterpart, and `resF`
(a ring hom *into* the residue function field) needs it. Everything the pin builds to get it —
`Lam`/`LamSub`/`homSpan`/`IsFrac` (pin 127–282, ~155 lines), `ofPS`/`homSpan_eq_map`/
`div_mem_qExpFunctionFieldC_of_mem_span`/`exists_primitive_of_mem_homSpan`/`exists_frac_form`
(pin 330–456, ~127 lines) — exists to prove that one statement, and to prove it the pin must call
`PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated`.

**Route B (the plan).** Transcribe that block faithfully, in the pin's order, calling the ported
`Saturation` premise at `exists_primitive_of_mem_homSpan`; keep the graded `homSpan K κ` (the weight
index is what makes the ratio of two forms a function-field element). The engine's statements stay
at the pin's shape except that `hT` is **not** an argument of the Gauss block (drop it there and
thread it only where a headline needs it — §1); if a transcribed proof needs `hT`, pass it to the
headline's assembly. Expect ≈ 480–550 port lines.

**Route A (optional, time-boxed to one probe).** `QExpDeuring.exists_frac_form` (via the ported
`gensZ`/`exists_primitive_form` route) already gives the decomposition and the two `ϖ`-nonvanishing
conjuncts; only the fourth conjunct is missing. A probe file under `lean/tmp/` may test whether
"for `x ∈ adjoin L (gensZ L Γ)`, a primitive form `x₀` has `ϖ x₀ ∈ qExpFunctionFieldC kk Γ`" closes
cheaply; if it does not close **in one 60-second turn**, drop it and take Route B. Do not spend more
than one turn on it, and do not delete the `Lam` block on a hope.

## 4. The three tails

The shared development ends at pin 815. The tails:

* target: `main` (pin 817) — two conjuncts — and `solution` (pin 832) at the wrapper's statement.
* `_residue_div`: adds `residue_gaussProlongation_mul (f : (gaussProlongation hT A).integers) (x y)
  (hy) (h)` — residue times `ϖ y` equals `ϖ x` — from `coe_resF` + `resHom_eq` + `div_mul_cancel₀`.
* `_residue_mul_eq`: the same fact with the other binder shape `(f : FF) (hf : f ∈ R.integers)`.
  The two binder shapes are **not** interchangeable to the checker; write both.

`main`'s conclusion is the target headline's statement with the first two conjuncts; the three
headlines differ only in which tail conjuncts they carry, so assemble them from one `gaussProlongation`
value.

## 5. Build discipline — read this before the first compile

* **Every** compile is one of these two forms, run from `lean/`, and every one goes through the lock
  (another session may hold it; a lock wait is not a blow-up):

  ```
  flock .lake/flt_build.lock timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/X1/QExpRegularProlongation.lean
  flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.ModularCurve.X1.QExpRegularProlongation
  ```

  The first writes no `.olean` and builds no dependent — it is the edit loop. The second is run
  **once**, when the file is finished.
* **The 200,000 cap is a diagnostic, not the budget.** Never raise it; never add a module-level
  `set_option maxHeartbeats`; never add `set_option synthInstance.maxHeartbeats`. The pin's
  `synthInstance.maxHeartbeats 400000 in` on each wrapper and `1600000` in its `S_` file are **not**
  inherited — test at 200k.
* **A timeout is not automatically a slow proof.** If a declaration does not close at 200k, stub its
  *proof* with `sorry` and re-probe: if the statement still exceeds the bound, the cost is a term in
  the type and no tactic change can move it. The known cure is to name the recurring type or
  hypothesis once (a `private def`/`abbrev`) so `isDefEq` stops unfolding it — that deviates the
  statement, which needs a recorded reason and a manager decision, so **stop and report** instead.
* **Never bisect by re-elaborating the file.** To isolate a declaration: copy the prelude into
  `lean/tmp/` with proofs replaced by `sorry` (statements kept), put the one target at the end, and
  elaborate that. A probe is a ≤ 60 s turn; if a probe cannot finish in 60 s, the probe is wrong,
  not the file.
* Keep turns short: one probe, one edit, one compile per turn. No `lake build` per declaration.
* **No `sorry`/`admit`/`axiom`/`native_decide` in the delivered module**; no `import Mathlib`.
* Do not run a whole-tree `lake build`. Do not edit any other file, `spec/` included. Do not commit.

## 6. Gates

```bash
cd lean
timeout 115 python3 spec/check_port.py --force FLTForHuman/ModularCurve/X1/QExpRegularProlongation.lean
# expected: 3 ok, 0 mismatch, 0 missing, 0 own, 0 kw
timeout 115 python3 spec/check_port.py --changed      # tree still green
timeout 115 python3 spec/unwired_register.py --check   # register is current
```

Plus: the module elaborates clean at 200k; `lake build` green with **0 warnings**; `#print axioms` on
each of the three headlines shows `[propext, Classical.choice, Quot.sound]`; `git status` shows this
one new file and nothing else.

## 7. Stop conditions

Stop and report — do not improvise — if:

1. a **promotion** or any edit to an existing module seems necessary (give the declaration, the host,
   and `tools/deps/build_ladder.py --edit <host>`'s price);
2. a **heartbeat raise** seems necessary (give the probe: statement-only with the proof stubbed, at
   200k, and what the timeout/`diagnostics` reading was);
3. a headline reads `MISMATCH` (give both signatures) — the statement is the wrappers', verbatim;
4. the module needs a `pin:` row in `spec/decl_markers.tsv` (say which declaration and why);
5. the pin's `Lam` block needs a pin-private declaration that is not in §2 and cannot be re-derived
   locally in a few lines.

## 8. Report shape

Return: (i) the module's line count and declaration count with the public/private split; (ii) the
three checker readings (§6) and the build's job count/warnings; (iii) `#print axioms` for the three
headlines; (iv) every deviation from the pin (there should be none in statements; list each proof
drift with its site); (v) which route (`B` or the `A` probe's outcome) was taken and what it cost;
(vi) anything that belongs in [CARRY-FORWARD.md](../../CARRY-FORWARD.md); (vii) `git status`.

Records to cite: the ground's landings are
[logs/qexp-definition-layer-homes.md](../../logs/qexp-definition-layer-homes.md) (the re-homing that
makes this module import no `WeightOne` module) and
[topics/PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §1.
