# Topic 6: the analytic model of `jq`

**Status: done (2026-09-22), one goal round.** The module is
`FLTForHuman/ModularForms/JqAnalyticModel.lean`, green with 0 warnings and no
`sorry`; the measured cost, the audit accounting (including the one prediction
that failed) and the wire test are in
[logs/phiGen-port.md](../../logs/phiGen-port.md) §6. The next topic is T7, the
Hauptmodul form ([PORTING-PhiGen.md](../PORTING-PhiGen.md) §5); this topic's
`hasSum_jq_qParam` and `E4_cube_div_discriminant_smul` are its interface. This
file is kept as the executed plan. Second topic of the Φ_p
splitting / R1 sub-effort. The plan is
[PORTING-PhiGen.md](../PORTING-PhiGen.md); the mathematics is
[base/013](../../../base/013-riemann-existence-and-the-q-expansion-principle.md);
T5 (R1's kernel) is executed and recorded in
[TOPIC-r1-kernel.md](TOPIC-r1-kernel.md) and
[logs/phiGen-port.md](../../logs/phiGen-port.md).

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured with mathlib prebuilt: a green
> `lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
> deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
> **errors in ~15–20 s** — it does not hang.
>
> - Run every build under a bound: `timeout 60 lake env lean <file>`,
>   `timeout 120 lake build <module>`. Non-return at 60 s is a blow-up.
> - **Quarantine immediately.** On a timeout, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch.lean` with
>   `set_option diagnostics true`. Do not re-run the same file hoping for a
>   different result.
> - **Never raise `maxHeartbeats`.** The cap already fails in under 20 s; raising
>   it turns that into an unbounded wait. The usual cause is a `FunLike`-quantified
>   lemma instantiated at a bare function type (`DFunLike.coe` unfolds without
>   bound) — restate it over the concrete function instead. T5's log §2.2 has the
>   worked example.

**Audience.** A fresh session taking this topic. Read, in this order:

1. [PORTING-PhiGen.md](../PORTING-PhiGen.md) §3–§5 — the cone, the R1/R2
   split, and this topic's place in the sequence;
2. [base/013](../../../base/013-riemann-existence-and-the-q-expansion-principle.md)
   §5.1 (the realization predicate) and §5.2 (why `jq`'s model is the bridge T7
   needs);
3. [TOPIC-r1-kernel.md](TOPIC-r1-kernel.md) and
   [logs/phiGen-port.md](../../logs/phiGen-port.md) §2 — the audit method and the
   one substitution that failed;
4. [porting-playbook.md](../../porting-playbook.md) §3, especially §3.11.

**Goal.** One new module, `FLTForHuman/ModularForms/JqAnalyticModel.lean` (mathlib
plus the port's `Defs/`), green, zero warnings, zero `sorry`, with exactly two
public declarations, both verbatim from their pin wrappers:

```lean
theorem ModularCurve.hasSum_jq_qParam (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => ((ModularCurve.jq.coeff m : ℚ) : ℂ) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)

theorem ModularCurve.E4_cube_div_discriminant_smul
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ)
      = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ
```

The first says the **formal** `jq` (the port's `PowerSeries`-built
`q⁻¹ · (E₄³/Δ)`) is the analytic `E₄³/Δ` on `ℍ`, coefficient by coefficient: it
is the realization hypothesis T7's headline will consume. The second is the
weight-zero invariance of that model. The pin's intermediate
`hasSum_jNum_qParam` (the `q ·` version) stays **private**.

## 1. Why this topic, and what is settled

T5 delivered R1's kernel as a statement about an *arbitrary* realized `F`. The
consumer, T7's Hauptmodul form, needs one concrete realization: `jq` itself.
`hasSum_jq_qParam` is that realization, and it is the only bridge between the
port's `PowerSeries` definition of `jq` (`Defs/Jq.lean`) and mathlib's analytic
`ModularForm.E₄`/`discriminant`.

- **Settled: statements are the pin's, verbatim.** Both have `Theorems/`
  wrappers, so `spec/check_flt_statements.py` verifies them. Add both to
  `SOURCES`.
- **Settled: audit mathlib first — but for correctness, not to save time.**
  T5 measured the point: the audit, the header and the corollary made the port
  **333 lines against a 186-line pin**. So a topic that replaces pin code with
  mathlib calls does not necessarily shrink, and may grow. Do the audit anyway:
  the port should depend on published mathematics rather than re-derive it, the
  mathlib route is the durable one, and recording each substitution is what makes
  the port's deviations visible. **Budget the audit as work.** This topic looked
  like the one where the audit had the most to gain — §2.1 predicted that mathlib
  already contained the pin's heaviest file — and the prediction **failed**: the
  file was kept. That is the sharpest instance of the rule, not a counterexample
  to it (see the post-execution note in §2.1).
- **Settled: `hasSum_jNum_qParam` is private.** It is the `q · (E₄³/Δ)` form, an
  intermediate of the `jq` statement; the port keeps it private and exports only
  the two T7-facing declarations. (The pin exports it, but the only FLT consumer
  is `hasSum_jq_qParam` itself.)
- **Settled: the module needs `Defs/Jq.lean`.** `jq`, `jNum`, `eisenstein4`,
  `etaProd`, `dedekindEtaUnit` are all defined there; the module imports it. It
  does **not** need T5's module.
- **Settled: T7 is not this session's business.** `RealL`, the closure lemmas,
  pole killing and the headline are T7.

## 2. The scouted inventory

Five pin files. The three `qExpansion_*` files are separate graph nodes but one
development; their statements:

| pin file | lines | statement |
|---|---|---|
| `S_ModularCurve_qExpansion_E4_eq_map_eisenstein4.lean` | 34 | `qExpansion 1 E₄ = PowerSeries.map (Int.castRingHom ℂ) eisenstein4` |
| `S_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.lean` | 199 | `qExpansion 1 Δ = X * ∏' n, (1 - X ^ (n+1)) ^ 24` |
| `S_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.lean` | 76 | `qExpansion 1 Δ = X * (dedekindEtaUnit.map …)` |
| `S_ModularCurve_hasSum_jNum_qParam.lean` | 235 | `jNum`'s series sums to `q · (E₄³/Δ)` |
| `S_ModularCurve_hasSum_jq_qParam.lean` | 45 | `jq`'s series sums to `E₄³/Δ` — **the exported statement** |

The 235-line file's own declarations, which is where the work is:

| declaration | pin lines | size |
|---|---|---|
| `gfun` (`∏' (1 - q^(n+1))^24`) | 22–23 | 2 |
| `differentiableOn_gfun` | 24–26 | 3 |
| `discriminant_eq_qParam_mul_gfun` | 27–31 | 5 |
| `qJ` (`q · E₄³/Δ`), `Dq` (`Δ/q`) | 32–35 | 4 |
| `Dq_eq` | 36–38 | 3 |
| `gfun_ne_zero` | 39–50 | 12 |
| `continuousAt_gfun` | 51–53 | 3 |
| `qJ_eq`, `qJ_mul_Dq` | 54–65 | 12 |
| `cuspFunction_eqOn` (general helper) | 66–88 | 23 |
| `cuspFunction_Dq`, `cuspFunction_qJ` | 89–102 | 14 |
| `analyticAt_cuspFunction_Dq`, `analyticAt_cuspFunction_qJ` | 103–118 | 16 |
| `qExpansion_qParam_fun` | 119–135 | 17 |
| `qExpansion_Dq'` | 136–150 | 15 |
| `qExpansion_qJ` | 151–169 | 19 |
| `periodic_qJ` | 170–188 | 19 |
| `gfun_zero`, `tendsto_gfun_qParam` | 189–191, 208–211 | 7 |
| `mdiff_qJ` | 192–207 | 16 |
| `isBoundedAtImInfty_qJ` | 212–229 | 18 |
| `solution` (the `HasSum`) | 230–236 | 7 |

### 2.1 The mathlib-first audit

Audited against our pinned `v4.34.0`, before execution. The prediction — that the
pin's **heaviest** file would be the one mathlib most directly replaces, the
opposite outcome to T5's — **failed in exactly that place**. The verdict column
is the pre-execution prediction; the post-execution note at the end of this
section (and [logs/phiGen-port.md](../../logs/phiGen-port.md) §6.1) gives the
measured outcome.

| pin piece | mathlib `v4.34.0` | verdict |
|---|---|---|
| `qExpansion_E4_eq_map_eisenstein4` (34) | `EisensteinSeries.E_qExpansion_coeff`, EisensteinSeries/QExpansion 324 | use; the port only bridges to its `eisenstein4` |
| **`qExpansion_discriminant_eq_X_mul_tprod` (199)** | **`ModularForm.discriminant_cuspFunction_eqOn`, Discriminant 201**; `discriminant_eq_q_prod`, 117; `differentiableOn_tprod_one_sub_pow_pow`, DedekindEta 97; `tendsto_atImInfty_tprod_one_sub_eta_q_pow`, Discriminant 157 | predicted **replaced**; actually **kept** — `discriminant_cuspFunction_eqOn` gives the *value* of `cuspFunction 1 Δ`, not the Taylor coefficients of `∏' (1-qⁿ)²⁴`, and mathlib has no lemma for the latter |
| `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` (76) | the same, glued to the port's `dedekindEtaUnit = etaProd ^ 24` | small bridge |
| `gfun`, `differentiableOn_gfun`, `gfun_ne_zero`, `continuousAt_gfun` | `differentiableOn_tprod_one_sub_pow_pow 24`; `eta_tprod_ne_zero`; `one_sub_eta_q_ne_zero` | replaced |
| `discriminant_eq_qParam_mul_gfun`, `Dq_eq` | `discriminant_eq_q_prod` | replaced |
| `cuspFunction_eqOn`, `cuspFunction_Dq` | `discriminant_cuspFunction_eqOn`; `eq_cuspFunction` | replaced |
| `analyticAt_cuspFunction_Dq`, `analyticAt_cuspFunction_qJ` | public `analyticAt_cuspFunction_zero`, QExpansion 113 | replaced |
| `tendsto_gfun_qParam` | `tendsto_atImInfty_tprod_one_sub_eta_q_pow` | replaced |
| `qExpansion_qParam_fun` | `qExpansion 1 (fun τ ↦ q(τ)) = X` — check; mathlib has the `cuspFunction`/`qExpansion` API | likely short |
| `qJ_eq`, `qJ_mul_Dq`, `cuspFunction_qJ`, `qExpansion_Dq'`, `qExpansion_qJ` | none — the gluing algebra between the port's `PowerSeries` defs and mathlib's q-expansions | **port these** |
| `periodic_qJ` | from E₄/Δ modularity plus `periodic_comp_ofComplex` | port (small) |
| `mdiff_qJ` | `ModularFormClass.holo` on `E₄` and `discriminant` + `UpperHalfPlane.mdifferentiable_iff` | port (small) |
| `isBoundedAtImInfty_qJ` | `ModularFormClass.bdd_at_infty` + `tendsto_..._inv` | port (small) |
| `solution` | `hasSum_qExpansion`, QExpansion 194: periodic + `MDiff` + bounded ⇒ the sum of its q-expansion | use |
| `hasSum_jq_qParam` (45) | multiply by `q⁻¹` (`HasSum.mul_left`) | small |
| `E4_cube_div_discriminant_smul` (38) | `SlashInvariantForm.slash_action_eqn''` on `ModularForm.E₄` (weight 4) and `CuspForm.discriminant` (weight 12) | no gap |

**Headline.** `hasSum_qExpansion` is the general engine: it needs only
`Periodic`, `MDiff` and `IsBoundedAtImInfty` of `qJ`, not a `ModularFormClass`.
So the port's own work is (i) the three prerequisites for `qJ`, (ii) the
`qExpansion_qJ = jNum.map ⋯` identity, and (iii) the `q⁻¹` step. Everything
else on the pin's path has a public mathlib statement. This is the one place in
the sub-effort where the mathlib-first audit is expected to pay for itself — but
do not count on it (T5's lesson), and **do not raise `maxHeartbeats`** if a
mathlib lemma on the path (e.g. a `FunLike`-quantified one) blows up; restate it
concretely instead.

**Post-execution note (2026-09-22).** The headline's "everything else has a
public mathlib statement" held for the *value* lemmas — `E_qExpansion_coeff`,
`discriminant_eq_q_prod`, `differentiableOn_tprod_one_sub_pow_pow`,
`hasSum_qExpansion`, `slash_action_eqn''` all applied — but **not** for the
199-line tprod file. `ModularForm.discriminant_cuspFunction_eqOn` gives the value
of `cuspFunction 1 Δ` on the disc; the `q`-expansion needs the Taylor
coefficients of `∏' (1-qⁿ)²⁴`, and no mathlib lemma computes them, so the pin's
truncated-polynomial/locally-uniform-convergence argument was ported. The
76-line map file *did* collapse (to 8 lines via a generic coefficient lemma), and
`hasSum_jq_qParam`'s `q⁻¹` step is 24 lines against the pin's 45. The port is
622 lines against the ~589-line pin. No `FunLike` blow-up occurred: the pin's
`qExpansion_coeff_unique` call is already on the bundled `CuspForm.discriminant`.
Full accounting in [logs/phiGen-port.md](../../logs/phiGen-port.md) §6.

## 3. What is different about this topic

- **It builds on the port's own definitions, not only mathlib's.** The bridge
  `qExpansion 1 qJ = jNum.map (Int.castRingHom ℂ)` relates mathlib's analytic
  `qExpansion` to `Defs/Jq.lean`'s `eisenstein4`/`dedekindEtaUnit`/`jNum`. That
  is the part with no pin-free copy, and the part to expect friction in.
- **The pin's biggest file is *not* the one mathlib replaces — measured.** The
  expectation going in was the reverse of T5's; the outcome was the same shape:
  a mathlib lemma (`discriminant_cuspFunction_eqOn`) states the neighbouring fact
  (the `cuspFunction` value), not the needed one (the Taylor coefficients of the
  eta product). The audit is still the first task, because it is what draws that
  line.
- **`jq` is a Laurent series, `qJ` a function.** The `q⁻¹` step in
  `hasSum_jq_qParam` uses `Function.Injective.hasSum_iff` and the port's
  `coeff_jq_of_lt`; keep the pin's `hq : q ≠ 0` discipline.
- **A new module in the existing area.** `FLTForHuman/ModularForms/` already
  exists (T5); no library change.

## 4. Verification and the wire test

Beyond `lake build` green / 0 warnings / no `sorry`:

1. **`#print axioms`** on both public declarations: expect only `propext,
   Classical.choice, Quot.sound`.
2. **Statement checker.** Add both wrappers to `SOURCES`; verified count
   151 → **153**, 0 mismatched. `hasSum_jNum_qParam` is private, so the checker
   skips it — say so in the module header.
3. **The wire test, cross-module.** The model should agree with the
   `jq`-coefficients topic: combine `hasSum_jq_qParam` with
   `coeff_jq_zero` (`744`) and `coeff_jq_one` (`196884`) from
   `JqCoefficients.lean` to exhibit, at a point, the classical
   `j(q) = q⁻¹ + 744 + 196884q + ⋯`. If extracting terms from the `HasSum` is
   fiddly, the minimum wire is a documented `#check` of the pin correspondence
   plus a non-vacuity `example`; say which you did. The real consumer is T7.
4. **No `sorry` and nothing half-finished in the library**: experiment in the
   gitignored `Scratch.lean`.

## 5. Budget

**3 goal rounds, checkpoint at 1; the audit is round 1.** Pin material is ~589
lines, but §2.1 replaces ~200 of them (the tprod file) and much of the 235-line
file's prerequisites, so the port's own content is plausibly 200–350 lines — and
per §1 that is not a promise. Round 1: confirm §2.1's table against the build —
that `discriminant_cuspFunction_eqOn` and `hasSum_qExpansion` apply as expected,
and that the `qExpansion_qJ = jNum.map ⋯` bridge is the only real work. If a
mathlib lemma on the path blows up, quarantine per the top block and report it.

Stop early on: `hasSum_qExpansion` not applying to `qJ` after the three
prerequisites; the `qExpansion_qJ` identity needing a private mathlib lemma
(T5's situation); or `E4_cube_div_discriminant_smul` needing more than mathlib's
slash action.

## 6. Definition of done

- [x] `FLTForHuman/ModularForms/JqAnalyticModel.lean`: both public statements
      verbatim from the wrappers; `hasSum_jNum_qParam` and the gluing helpers
      private; header naming subject, pin provenance (`aa2d8b3`), assumptions, and
      — for each pin helper not ported — the mathlib lemma that replaced it
      (§2.1).
- [x] `lake build` green, 0 warnings, no `sorry`.
- [x] `#print axioms` clean on both.
- [x] `spec/check_flt_statements.py`: both wrappers in `SOURCES`, verified count
      151 → 153, 0 mismatched; `PORT_FILES` gains the module; `hasSum_jNum_qParam`
      is private and noted as such.
- [x] the wire item from §4 recorded, with its form named (consumer Zone D).
- [x] `PORTING-PhiGen.md` §5 marks T6 done and names T7; `logs/phiGen-port.md`
      gains T6's cost and the audit accounting; README module table gains the
      module.
- [x] report in the §7 shape.

## 7. Reporting back

1. **The audit, measured again** — how many pin helpers became a mathlib call,
   how many were dropped, how many needed proof, and whether the 199-line tprod
   file really did collapse into `discriminant_cuspFunction_eqOn`. This is the
   first test of whether the audit's *rightness* and its *savings* can diverge.
   **Answer (2026-09-22):** it did **not** collapse; the file was kept, with
   ~180 lines ported. Rightness and savings diverged again — the port is 622
   lines against the ~589-line pin. [logs/phiGen-port.md](../../logs/phiGen-port.md)
   §6.1 has the accounting.
2. **The cost** — rounds, declarations, lines, and the port/pin ratio; T5's was
   333/186.
3. **Did any mathlib lemma blow up the way `qExpansion_coeff_unique` did?** If
   so, name it and how it was restated.

## 8. Where this sits: the sub-effort sequence (R1 = T5–T7; T8 = the cone)

For orientation only — do not start any of these.

| topic | deliverable | pin material | pin lines |
|---|---|---|---|
| 5 (done) | the constancy kernel + the `n = 0` corollary | `coeff_eq_zero_of_hasSum_of_slash_invariant` | 186 |
| 6 (done) | the analytic model of `jq`: `jq` sums to `E₄³/Δ`, and that is `SL₂(ℤ)`-invariant | `qExpansion_*`, `hasSum_jNum_qParam`, `hasSum_jq_qParam`, `E4_cube_div_discriminant_smul` | ~589 |
| 7 | the Hauptmodul form: `RealL` + closure, pole killing, `mem_adjoin_jq_of_hasSum_of_slash_invariant` | `hasSum_qParam_mul{,_laurent}`, `exists_aeval_jq_sub_holomorphicAtInfty`, `mem_adjoin_jq_of_hasSum_of_slash_invariant` | ~370 |
| 8 | the cone application: the descended coefficients lie in `ℚ[jq]` | the Hecke translates, `cosetPoly_smul`, `hasSum_cosetPoly_coeff`, `mem_adjoin_jq_of_phiGenDescends` | ~680 |

R1 is topics 5–7; T8 is the cone's (c). T7 needs this topic's
`hasSum_jq_qParam` and `E4_cube_div_discriminant_smul`, so they are its
interface.
