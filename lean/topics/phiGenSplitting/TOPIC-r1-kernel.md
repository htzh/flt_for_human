# Topic 5: R1, the level-one q-expansion principle — the constancy kernel

**Status: done (2026-09-21), one goal round.** The module is
`FLTForHuman/ModularForms/QExpansionPrinciple.lean`, green with 0 warnings and no
`sorry`; the measured cost, the audit accounting and the two deviations from §2.1
are in [logs/phiGen-port.md](../../logs/phiGen-port.md). The next topic is T6,
the analytic model of `jq` ([PORTING-PhiGen.md](../PORTING-PhiGen.md) §5).
This file is kept as the executed plan. First topic of the Φ_p
splitting / R1 sub-effort. The plan is
[PORTING-PhiGen.md](../PORTING-PhiGen.md); the mathematics is
[base/013](../../../base/013-riemann-existence-and-the-q-expansion-principle.md);
the parent effort is [PORTING-FFG.md](../PORTING-FFG.md).

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
>   bound) — restate it over the concrete function instead.

**Audience.** A fresh session taking this topic. Read, in this order:

1. [PORTING-PhiGen.md](../PORTING-PhiGen.md) §3–§5 — what the Φ_p cone is, why
   R1 (not R2) is the analytic input, and this topic's place in the sequence;
2. [base/013](../../../base/013-riemann-existence-and-the-q-expansion-principle.md)
   §3 (R1 in kernel and Hauptmodul form), §5.4 (the declaration chain, and the
   finding that the analysis is one mathlib theorem), §6 (why R1, at level one);
3. [porting-playbook.md](../../porting-playbook.md) §3–§5 for the method;
4. [logs/ffg-port.md](../../logs/ffg-port.md) §0 for the cost calibration.

Everything those settled still binds. The parent effort's four topics are in
[../functionFieldGeneration/](../functionFieldGeneration/) — same work-order shape,
different subject.

**Goal.** One new module, `FLTForHuman/ModularForms/QExpansionPrinciple.lean`
(mathlib plus the port's `Defs/`), green, zero warnings, zero `sorry`, containing
exactly two public declarations:

1. R1's **kernel**, stated verbatim from its pin wrapper
   (`Theorems/Thm_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean`):

```lean
theorem ModularCurve.coeff_eq_zero_of_hasSum_of_slash_invariant
    {F : UpperHalfPlane → ℂ} {c : ℕ → ℂ}
    (hF : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    {m : ℕ} (hm : m ≠ 0) : c m = 0
```

"a holomorphic, $`\mathrm{SL}_2(\mathbb{Z})`$-invariant $`q`$-series is
constant" — the minimal named form of the specialized Riemann-existence input;

2. our corollary, the $`n = 0`$ end of the Hauptmodul form. This is **not** a pin
   statement; it is the wire test (and the first rung of topic 7):

```lean
theorem ModularCurve.mem_adjoin_jq_of_poleOrderLE_zero
    (f : LaurentSeries ℚ) (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ)
    (h0 : PoleOrderLE f 0) : f ∈ Algebra.adjoin ℚ {jq}
```

Nothing else. In particular **do not** attempt the general Hauptmodul headline
`mem_adjoin_jq_of_hasSum_of_slash_invariant`, the analytic model of `jq`
(`hasSum_jq_qParam` and its chain), the `RealL` predicate, the pole-killing lemma
`exists_aeval_jq_sub_holomorphicAtInfty`, or the Hecke translates: those are
topics 6–8 (§8).

## 1. Why this topic, and what is settled

base/013 §6 answers the question this sub-effort exists for: of the two
Riemann-existence facts the modular-equation argument uses, R1 (the level-one
q-expansion principle) is the analytic input, and R2 (degree and connectedness of
$`X_0(N) \to X(1)`$) is reconstructed algebraically by the cone. R1 has two forms;
base/013 §6's recommendation is to name the kernel and state the Hauptmodul form
on top. This topic does the naming.

- **Settled: the analysis is mathlib's, and so is most of the packaging.**
  base/013 §5.4 measured the first half: the whole analytic content is
  `ModularForm.eq_const_of_weight_zero`, whose level-one input is
  `ModularFormClass.levelOne_weight_zero_const`, backed by the
  fundamental-domain/maximum-modulus argument of
  [base/003 §4.2](../../../base/003-no-level-2-weight-2-cusp-forms.md). The
  second half is this topic's **mathlib-first audit** (§2.1): mathlib's
  `QExpansion.lean` already exposes public lemmas replacing the pin's
  `tendsto_atImInfty`, `isBoundedAtImInfty`, `coeff_unique`,
  `norm_qParam_lt_one_of_pos` and the disc-differentiability block. **Check §2.1
  before transcribing any pin helper**; the only helper with no public mathlib
  counterpart is `mdifferentiable`.
- **Settled: the kernel is generic.** It quantifies over `F : ℍ → ℂ` and
  `c : ℕ → ℂ`; it mentions neither `jq` nor `jqN` nor any field. So this topic
  needs no part of the cone and no earlier topic.
- **Settled: the statement is the pin's, verbatim.** The wrapper exists, so
  `spec/check_flt_statements.py` verifies it rather than exempting it. Add the
  wrapper to `SOURCES`.
- **Settled: the corollary is ours.** It has no FLT source; handle it explicitly
  in the checker's `OWN_PROOFS` (as `coeff_jq_zero` / `coeff_jq_one` are), with a
  comment saying why.
- **Settled: the module is new and lives outside `ModularCurve/`.** The kernel is
  about modular forms on $`\mathbb{H}`$ and mentions no modular curve; topics 6–8
  are the same kind of object. `FLTForHuman/ModularForms/` is the honest home. If
  the session finds a concrete reason to prefer `ModularCurve/`, record it rather
  than choosing silently.
- **Settled: topics 6–8 are not this session's business.** §8 lists them so the
  boundary is visible.

## 2. The scouted inventory

All 15 declarations are in **one** pin file,
`P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean`
(186 lines), under `namespace ModularCurve.Realized`. It uses no other FLT
theorem, and nothing in it comes from `P2M/Util` (checked: `P2M/Util.lean`
contains no `qParam`, `cuspFunction`, `ofComplex` or `isBounded` name), so the
port's module is mathlib-only for this part.

| declaration | pin lines | size | what it does |
|---|---|---|---|
| `norm_qParam_lt_one_of_pos` | 20–23 | 4 | $`\|q(\tau)\| \lt 1`$ on $`\mathbb{H}`$ |
| `hasSum_cuspFunction_punctured` | 24–35 | 12 | the `HasSum` reads as a `cuspFunction` value on the punctured disc |
| `hasFPowerSeriesOnBall_update` | 36–56 | 21 | radius-$`1`$ power series, filling in $`q = 0`$ |
| `discFun` | 57–58 | 2 | $`\mathrm{update}\,(\mathrm{cuspFunction}\,h\,F)\,0\,(c_0)`$ |
| `hasSum_discFun` | 59–66 | 8 | `discFun` is the sum of the series |
| `apply_eq_discFun` | 67–70 | 4 | $`F(\tau) = \mathrm{discFun}(q(\tau))`$ |
| `differentiableOn_discFun` | 71–76 | 6 | complex-differentiable on the disc |
| `continuousAt_discFun` | 77–82 | 6 | continuous at each disc point |
| `discFun_zero` | 83–84 | 2 | value at $`0`$ is $`c_0`$ |
| `mdifferentiable` | 85–99 | 15 | $`F`$ is complex-differentiable on $`\mathbb{H}`$ |
| `tendsto_atImInfty` | 100–107 | 8 | $`F \to c_0`$ at the cusp |
| `isBoundedAtImInfty` | 108–112 | 5 | bounded at the cusp |
| `periodic` | 113–129 | 17 | $`F \circ \mathrm{ofComplex}`$ is $`h`$-periodic |
| `coeff_unique` | 130–150 | 26 | two `HasSum` presentations of one `F` have equal coefficients |
| `solution` (exports the kernel) | 156–186 | 32 | packages `F` as a `ModularForm 𝒮ℒ 0`, applies `eq_const_of_weight_zero`, then `coeff_unique` |

Keep the 14 helpers **private** and export only the kernel and the corollary, as
`JqCoefficients.lean` does (2 public, 22 private).

The mathlib surface, checked against our pinned `v4.34.0`:

| what the pin uses | mathlib module | v4.34.0 line |
|---|---|---|
| `Periodic.qParam`, `qParam_right_inv`, `cuspFunction_eq_of_nonzero` | `Mathlib/Analysis/Complex/Periodic.lean` | — |
| `cuspFunction` | `Mathlib/NumberTheory/ModularForms/QExpansion.lean` | 88 |
| `im_invQParam_pos_of_norm_lt_one` | `Mathlib/Analysis/Complex/UpperHalfPlane/Exp.lean` | — |
| `ofComplex_apply_of_im_pos`, `ofComplex_apply_eq_of_im_nonpos` | `Mathlib/Analysis/Complex/UpperHalfPlane/Topology.lean` | 162, 170 |
| `ModularForm`, `𝒮ℒ`, `ModularForm.SL_slash_apply` | `Mathlib/NumberTheory/ModularForms/SlashActions.lean` | 162 |
| `OnePoint.isBoundedAt_iff_forall_SL2Z` | `Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean` | 110 |
| `ModularForm.eq_const_of_weight_zero` | `Mathlib/NumberTheory/ModularForms/NormTrace.lean` | 164 |
| `ModularFormClass.levelOne_weight_zero_const` (its level-one input) | `Mathlib/NumberTheory/ModularForms/LevelOne/Basic.lean` | 103 |

The last two are base/013's citation; the private `levelOne_nonpos_wt_const` is
at line 91 in v4.34.0 (89 in the v4.33.0 that base/013 cites).

### 2.1 The mathlib-first audit — do this before transcribing anything

The pin's `Realized` block is largely a re-derivation of mathlib's
`cuspFunction`/`qExpansion` API, which has grown since FLT was written. Audited
against our pinned `v4.34.0`:

| pin helper (pin lines) | mathlib `v4.34.0` | status | verdict |
|---|---|---|---|
| `norm_qParam_lt_one_of_pos` (20–23) | `Periodic.norm_qParam_lt_one` | public | use mathlib |
| `hasSum_cuspFunction_punctured` (24–35) | `UpperHalfPlane.hasSum_cuspFunction_of_hasSum_punctured`, QExpansion 234 | **private** | re-derive only if the disc route is needed |
| `hasFPowerSeriesOnBall_update` (36–56) | `UpperHalfPlane.hasFPowerSeriesOnBall_update`, QExpansion 244 | **private** | as above |
| `discFun`, `hasSum_discFun`, `apply_eq_discFun`, `differentiableOn_discFun`, `continuousAt_discFun`, `discFun_zero` (57–84) | the public `cuspFunction` API: `eq_cuspFunction` 91, `differentiableOn_cuspFunction_ball` 107, `cuspFunction_apply_zero` 119 | public | drop, unless they are the route to `mdifferentiable` |
| **`mdifferentiable` (85–99)** | none — every public `*_cuspFunction` lemma *takes* `MDiff f` as a hypothesis; nothing public derives it from a `HasSum` | **gap** | **the one helper to port** |
| `tendsto_atImInfty` (100–107) | `UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion`, QExpansion 268 | public | **direct replacement** |
| `isBoundedAtImInfty` (108–112) | `UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion`, QExpansion 285 | public | **direct replacement** |
| `periodic` (113–129) | `UpperHalfPlane.periodic_comp_ofComplex`, Topology 184, from `q`-periodicity | public | short derivation |
| `coeff_unique` (130–150) | `UpperHalfPlane.qExpansion_coeff_unique`, QExpansion 784 (its `AnalyticAt` hypothesis follows from `mdifferentiable`) | public | use mathlib |
| `solution` (156–186) | the packaging itself: `hinv` → slash invariance, `MDiff` → `holo'`, boundedness → `bdd_at_cusps'`, then `eq_const_of_weight_zero` | — | port it (32 lines) |

So of the 186 pin lines, ~121 have a public mathlib counterpart or are avoidable;
the genuine port work is **`mdifferentiable` (~15 lines), the `ModularForm`
packaging, and the corollary**. Two bridges to expect: mathlib's
`*_of_hasSum_qExpansion` lemmas use $`c_m \bullet q^m`$ where the pin uses
$`c_m \cdot q^m`$ (equal on $`\mathbb{C}`$ via `smul_eq_mul`), and
`UpperHalfPlane.mdifferentiable_iff` is the route from "power series on the disc"
to `MDiff`.

**Rule for this topic: before transcribing any pin helper, look it up in
mathlib.** If a public lemma states it (or its conclusion), use the lemma and
record the correspondence in the module header. Only `mdifferentiable` is
expected to need proof; if a second helper turns out to need one, that is a
finding to report.

**Post-execution note (2026-09-21).** Six helpers needed a proof, not one:
`mdifferentiable` plus the two mathlib-**private** disc-route lemmas it cannot be
stated without (`hasSum_cuspFunction_punctured`, `hasFPowerSeriesOnBall_update`),
the two `discFun`-restatements, and `coeff_unique`. Five helpers were dropped and
three became public mathlib calls. And the §2.1 row `coeff_unique` →
`UpperHalfPlane.qExpansion_coeff_unique` **failed**: that lemma's
`{F : Type*} [FunLike F ℍ ℂ]` signature instantiated at the bare function type
`ℍ → ℂ` unfolds `DFunLike.coe` 5,143,553 times (a deterministic `whnf` timeout at
the default 200 000 and at the package's 4 000 000 heartbeat caps), so the pin's
26-line argument was ported. The full accounting is in
[logs/phiGen-port.md](../../logs/phiGen-port.md) §2; this blow-up is the worked
example behind [porting-playbook.md](../../porting-playbook.md) §3.11.

Notes for the transcription, so none of it has to be rediscovered:

- **Do not improve `hF` to a $`\mathbb{Z}`$-sum.** The kernel's `hF` is
  $`\mathbb{N}`$-indexed on purpose: that is holomorphy at the cusp, and it is
  exactly the hypothesis `eq_const_of_weight_zero`'s packaging needs. The
  $`\mathbb{Z}`$-indexed form belongs to the corollary.
- **Keep the general period `h : ℝ` in the helpers.** The exported kernel fixes
  $`h = 1`$, but topic 7's Hecke translates change the period, so the helper block
  is already in the right shape. It is private for now.
- **`eq_const_of_weight_zero` needs `[𝒢.IsArithmetic]`**; $`𝒮ℒ`$ carries it. The
  `bdd_at_cusps'` obligation is discharged by `isBoundedAtImInfty` after
  `OnePoint.isBoundedAt_iff_forall_SL2Z`, and `holo'` by `mdifferentiable`.
- **The corollary's route.** From `h0 : PoleOrderLE f 0`, all negative
  coefficients vanish. Restrict the $`\mathbb{Z}`$-indexed `hF` to
  $`\mathbb{N}`$ (`Nat.cast_injective.hasSum_iff`, the device the pin uses at
  `S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean` line 182);
  apply the kernel to get $`f_m = 0`$ for $`m \ge 1`$; conclude
  $`f = \mathrm{single}\,0\,(f_0) = \mathrm{algebraMap}\,\mathbb{Q}\,(f_0)`$ and
  close with `Subalgebra.algebraMap_mem`. Expect this to be the fiddliest part of
  the topic; it is a genuine $`\mathbb{Z} \to \mathbb{N}`$ conversion and the
  wire test.
- The corollary uses `jq` (`Defs/Jq.lean`) and `PoleOrderLE`
  (`Defs/PhiGen.lean`), both already in the port; so the module imports
  `FLTForHuman.ModularCurve.Defs.Jq` and `…Defs.PhiGen`.

## 3. What is different about this topic

- **It is the port's first analytic module.** Everything so far has been algebra
  on `LaurentSeries`, `Polynomial` or `IntermediateField`; this one works on
  $`\mathbb{H}`$, `ℂ`, `HasFPowerSeriesOnBall` and `ModularForm`. Expect the
  friction to be mathlib API names, not mathematics.
- **It has no pin consumer yet.** The kernel's consumer is topic 7; the corollary
  is the wire that keeps it from being a self-consumed lemma (PORTING-FFG §1.5).
  Because of that, the corollary is required, not optional — but it may be
  subsumed by topic 7's headline later, and that is fine.
- **Most of the pin's helper block is deliberately not ported.** §2.1 replaces
  ~121 of the 186 pin lines with public mathlib lemmas, so the cost ratio is
  **not** against 186. Report the port's own line count, `mdifferentiable`'s
  share, and exactly which pin helpers became a mathlib call.
- **A new area appears in the library.** `FLTForHuman/` gains `ModularForms/`
  beside `Elliptic/`, `FieldTheory/` and `ModularCurve/`. It is part of the single
  `FLTForHuman` library, so no build-target change is needed.

## 4. Verification and the wire test

Beyond `lake build` green / 0 warnings / no `sorry`:

1. **`#print axioms`** on both public declarations: expect only `propext,
   Classical.choice, Quot.sound`.
2. **Statement checker.** Add
   `Theorems/Thm_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean` to
   `SOURCES`; the verified count rises by 1 with 0 mismatched. Handle the
   corollary in `OWN_PROOFS` (or an equivalent explicit exemption) with a comment
   — it is ours, like `coeff_jq_zero`.
3. **The wire test, cross-module.** The corollary consumes the kernel and the
   port's own `jq` and `PoleOrderLE`; it is the `n = 0` case of the Hauptmodul
   headline topic 7 will state. Say in the report that it is a genuine
   cross-module composition, not a restatement.
4. **Non-vacuity.** A short `example`: the constant form
   ($`F = \mathrm{const}\ \kappa`$, $`c = \mathrm{Pi.single}\,0\,\kappa`$)
   satisfies `hF` and `hinv`; the kernel then says its $`m \ne 0`$ coefficients
   vanish. Put it in the module (as a `section Example`) or in the consumer and
   name the choice.

## 5. Budget

**2 goal rounds, checkpoint at 1; expected well under the pin's 186 lines.**
After the §2.1 audit the port's own content is `mdifferentiable` (~15 lines), the
`ModularForm` packaging, and the corollary — the rest is a mathlib call. The
record's topics came in at 207, 346, 494 and ~190 lines in **one** round each, so
one round is the expectation; two is the "something structural is wrong"
threshold. The likely causes would be the `mdifferentiable` derivation, the
`ModularForm` packaging (`IsArithmetic`, `bdd_at_cusps'`), or the corollary's
$`\mathbb{Z} \to \mathbb{N}`$ conversion.

**Round 1 is the audit and the de-risk, not the proof.** Confirm §2.1's table
against the build: that `isBoundedAtImInfty_of_hasSum_qExpansion` and
`tendsto_atImInfty_of_hasSum_qExpansion` apply to the pin's `hF` (modulo the
`smul`/`mul` bridge), that `eq_const_of_weight_zero` applies once `F` is packaged,
and that `mdifferentiable` is genuinely the only missing piece. If any *other*
helper lacks a public counterpart, or `eq_const_of_weight_zero` needs hypotheses
the pin does not carry, **stop and report** — that is the single most valuable
thing this topic could discover.

Stop early on: a helper (besides `mdifferentiable`) with no public mathlib
counterpart; `eq_const_of_weight_zero` needing more than `bdd_at_cusps'`; or the
$`\mathbb{Z} \to \mathbb{N}`$ `HasSum` restriction.

**Build discipline.** See the block at the top of this file — it is the format's
first requirement, not a §5 afterthought. The worked blow-up is
`UpperHalfPlane.qExpansion_coeff_unique` at the bare type `ℍ → ℂ` (5.1M
`DFunLike.coe` reductions), documented in the module header.

## 6. Definition of done

- [x] `FLTForHuman/ModularForms/QExpansionPrinciple.lean`: the kernel public,
      statement verbatim from the wrapper; the port's own helpers private and in
      dependency order; the header naming subject, pin provenance (`aa2d8b3`),
      assumptions, and — for each pin helper **not** ported — the mathlib lemma
      that replaced it (§2.1).
- [x] `ModularCurve.mem_adjoin_jq_of_poleOrderLE_zero` public, with a docstring
      saying it is ours and the `n = 0` end of the Hauptmodul form.
- [x] `lake build` green, 0 warnings, no `sorry`; no half-finished proof left in
      the library (experiment in the gitignored `Scratch.lean`).
- [x] `#print axioms` clean on both.
- [x] `spec/check_flt_statements.py`: wrapper added to `SOURCES`, verified count
      up by 1 (150 → 151), 0 mismatched; the corollary handled explicitly in
      `OWN_PROOFS`.
- [x] the two wire items from §4 recorded, with the non-vacuity example's
      location named.
- [x] the plan updated: `PORTING-PhiGen.md` §5 marks T5 done and names the next
      topic; `logs/phiGen-port.md` carries the measured cost; the README module
      table gains the new area.
- [x] report in the §7 shape — the answers are in `logs/phiGen-port.md` §1 (cost),
      §2 (the audit, including the one substitution that failed) and §4 (whether
      the corollary should survive).

## 7. Reporting back

Same shape as the parent effort's topics. Three things specifically:

1. **The measured cost, and how much of the pin survived the audit.** Rounds,
   declarations, lines written, the port/pin ratio and — the more useful number —
   how many of the pin's 14 helpers became a mathlib call, how many were dropped,
   and how many needed proof. That is the mathlib-first calibration for topics
   6–8.
2. **Did `eq_const_of_weight_zero` deliver as scouted?** It is the one mathlib
   theorem the whole analytic input rests on; if the packaging needed a different
   theorem, or an assumption the pin does not carry, say so exactly.
3. **Is the corollary worth keeping?** If topic 7's headline will subsume it
   cleanly, say whether it should survive as a convenience or be removed then.

## 8. Where this sits: the sub-effort sequence (R1 = T5–T7; T8 = the cone)

For orientation only — do not start any of these. Each is sized from the pin's
own file lengths, and each gets its own work order when its turn comes.

| topic | deliverable | pin material | size |
|---|---|---|---|
| **5 (this)** | the constancy kernel + the $`n = 0`$ corollary | `coeff_eq_zero_of_hasSum_of_slash_invariant` | 186 |
| 6 | the analytic model of `jq`: $`jq`$ sums to $`E_4^3/\Delta`$ on $`\mathbb{H}`$, and that is $`\mathrm{SL}_2(\mathbb{Z})`$-invariant | `qExpansion_*`, `hasSum_jNum_qParam`, `hasSum_jq_qParam`, `E4_cube_div_discriminant_smul` | ~630 |
| 7 | the Hauptmodul form: `RealL` + closure, pole killing, `mem_adjoin_jq_of_hasSum_of_slash_invariant` | `hasSum_qParam_mul{,_laurent}`, `exists_aeval_jq_sub_holomorphicAtInfty`, `mem_adjoin_jq_of_hasSum_of_slash_invariant` | ~370 |
| 8 | the cone application: the descended coefficients lie in $`\mathbb{Q}[jq]`$ | the Hecke translates, `cosetPoly_smul`, `hasSum_cosetPoly_coeff`, `mem_adjoin_jq_of_phiGenDescends` | ~680 |

T5's "186" is the **pin** size, not the port's: the §2.1 audit expects most of it
to be replaced by public mathlib lemmas. Topics 6–8 should start the same way —
audit mathlib before transcribing — because the same may hold there, especially
for T6's `qExpansion_*` chain.

R1 is topics 5–7; topic 8 is the cone's `(c)`, and it needs all of them. Topic
6 should **check mathlib first**: mathlib has `qExpansion` for modular forms,
`EisensteinSeries/QExpansion.lean` and `discriminant_qExpansion_*`
(`LevelOne/DimensionFormula.lean`), and the `jq`-coefficients topic already showed
that mathlib's power-series route can replace one of FLT's clusters. If that
substitution works, topic 6 may be much smaller than 630 lines.
