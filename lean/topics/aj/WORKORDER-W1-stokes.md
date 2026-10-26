# WORKORDER-W1 — the shared ∂̄/Stokes layer

**Status: ready to dispatch** (three groups, below). First wave of the aj subject; the plan is
[PLAN-W1-stokes.md](PLAN-W1-stokes.md). **New files only** — no existing Lean module is edited, no
existing declaration is promoted, and nothing is committed. The definition layer is already in place
(`Analysis/Complex/Dbar.lean`, written by the manager).

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

| order | module | headline | pin lines | pin `S_` file |
|---|---|---|---:|---|
| 1 | `FLTForHuman/Analysis/Complex/Pompeiu.lean` | `Complex.locallyIntegrableOn_of_simplePoles` | 74 | `S_Complex_locallyIntegrableOn_of_simplePoles` |
| 2 | idem | `Complex.integral_mul_dbar_eq_zero_of_differentiableOn` | 90 | `S_Complex_integral_mul_dbar_eq_zero_of_differentiableOn` |
| 3 | idem | `Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul` | 463 | `S_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul` |
| 4 | idem | `Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue` | 306 | `S_Complex_integral_mul_dbar_eq_neg_pi_mul_finsum_residue` |
| 5 | `FLTForHuman/Analysis/Complex/MeromorphicResidue.lean` | `Complex.integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum` | 98 | `S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum` |
| 6 | idem | `Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv` | 643 | `S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv` |
| 7 | `FLTForHuman/ModularForms/FundamentalDomainStokes.lean` | `Complex.integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt` | 639 | `S_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt` |
| 8 | `FLTForHuman/Analysis/Complex/CircleIntegralResidue.lean` | `Complex.circleIntegral_eq_sum_residue_of_simplePole` | 142 | `S_Complex_circleIntegral_eq_sum_residue_of_simplePole` |
| 9 | idem | `Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub` | 169 | `S_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub` |

Total **2,624 pin lines**, and the union of the nine premise closures is exactly these nine nodes —
nothing else in the pin is pulled in.

## 1. The mathematics

One layer, in three readings of one identity. For `h : ℂ → ℂ` a `C¹` compactly supported test function
and `∂̄h = dbar h` (`Analysis/Complex/Dbar.lean`):

* **Pompeiu.** `∫ z, G z * ∂̄h z = 0` when `G` is holomorphic on an open `V ⊇ tsupport h`; the kernel
  case `∫ z, (z−a)⁻¹ * ∂̄h z = −π * h a`; and the simple-pole case
  `∫ z, F z * ∂̄h z = −π * ∑ᶠ a, c a * h a` for `F` locally `c a/(z−a) + analytic`. Prelude: a function
  with only simple poles is locally integrable (order 1).
* **Log derivative.** The same identity with `F` replaced by `F'/F` (orders instead of residues), and
  the arbitrary-order form with `Φ = (z−τ)^{n τ} Ψ` locally, which also asserts the two integrabilities.
* **The modular region.** Green's theorem over `{z | |z.re| ≤ 1/2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}`, whose
  boundary is two vertical rays and the arc `e^{iθ}`, θ ∈ [π/3, 2π/3].
* **The circle-integral pair.** The residue formula for `∮ z in C(z₀,R)` and the differentiability in
  `t` of `∮ z in C(z₀,r), G z * deriv Φ z / (Φ z - t)`.

## 2. The statements (verbatim; transcribe exactly, including `ℂ` vs `ℍ` and `∮`)

```lean
theorem Complex.locallyIntegrableOn_of_simplePoles (U : Set ℂ) (hU : IsOpen U) (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z) :
    LocallyIntegrableOn F U

theorem Complex.integral_mul_dbar_eq_zero_of_differentiableOn (V : Set ℂ) (hV : IsOpen V)
    (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G V) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h)
    (hsupp : HasCompactSupport h) (hV' : tsupport h ⊆ V) :
    ∫ z, G z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = 0

theorem Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul (a : ℂ) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h)
    (hsupp : HasCompactSupport h) :
    ∫ z, (z - a)⁻¹ * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * h a

theorem Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue (U : Set ℂ) (hU : IsOpen U)
    (F c : ℂ → ℂ)
    (hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝[≠] a, F z = c a / (z - a) + g z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, F z * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) = -π * ∑ᶠ a, c a * h a

theorem Complex.integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum (U : Set ℂ) (hU : IsOpen U)
    (F : ℂ → ℂ) (hF : ∀ z ∈ U, MeromorphicAt F z) (hF' : ∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤)
    (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E U) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h)
    (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, E z * (deriv F z / F z) * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) =
      -π * ∑ᶠ a, (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a * h a

theorem Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv (U : Set ℂ)
    (hU : IsOpen U) (Φ : ℂ → ℂ) (n : ℂ → ℤ)
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ,
      ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧ Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    (E E' : ℂ → ℂ) (hE : ∀ z ∈ U, HasDerivAt E (E' z) z) (h : ℂ → ℂ) (hh : ContDiff ℝ 2 h)
    (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    Integrable (fun z : ℂ =>
        E z / Φ z * (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) ∧
      Integrable (fun z : ℂ =>
        E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
      I / π * (∫ z : ℂ, E z / Φ z *
          (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) +
        2 * ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a =
      2 / π * ∫ z : ℂ, E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)

theorem Complex.integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt (Φ : ℂ → ℂ)
    (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ) (hU : IsOpen U)
    (hDU : {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im} ⊆ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
    (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
    (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im)) :
    (∫ z in {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im},
        (Complex.I • Φ' z 1 - Φ' z Complex.I)) =
      Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (1 / 2 + y * Complex.I)) -
        Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (-(1 / 2) + y * Complex.I)) -
        ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
          Φ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))

theorem Complex.circleIntegral_eq_sum_residue_of_simplePole {R : ℝ} {z₀ : ℂ} (hR : 0 < R)
    (h c : ℂ → ℂ) (Z : Finset ℂ) (hZ : ∀ a ∈ Z, a ∈ Metric.ball z₀ R)
    (hh : ∀ z ∈ Metric.closedBall z₀ R, z ∉ Z → AnalyticAt ℂ h z)
    (hloc : ∀ a ∈ Z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ ∀ᶠ z in 𝓝[≠] a, h z = c a / (z - a) + g z) :
    (∮ z in C(z₀, R), h z) = 2 * Real.pi * Complex.I * ∑ a ∈ Z, c a

theorem Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub {Φ G : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hΦ : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ Φ z)
    (hG : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, Φ z ≠ t₀) :
    HasDerivAt (fun t : ℂ => ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t))
      (∮ z in C(z₀, r), deriv G z / (Φ z - t₀)) t₀
```

Read `Theorems/Thm_Complex_<stem>.lean` in the pin clone for each and transcribe the `theorem`
line **verbatim** — the checker is text-level, so a binder rename is a `mismatch`.

## 3. Premise homes

Everything in these statements is mathlib: `fderiv`, `ContDiff`/`ContDiffAt`, `HasCompactSupport`,
`tsupport`, `AnalyticAt`, `MeromorphicAt`/`meromorphicOrderAt`, `deriv`, `HasDerivAt`,
`HasFDerivAt`, `LocallyIntegrableOn`, `circleIntegral` (`∮`), `Complex.exp`, `Real.sqrt`,
`MeasureTheory` volume on `ℂ`, `intervalIntegral`, `Metric.ball`/`sphere`/`closedBall`. There is **no
pin premise** to port and **no pin definition** to transcribe: each headline's `needed` count in
`frontier` is 1–4, all of them inside this set. If a statement needs a pin-local name, **stop and
report** — it means the node is not mathlib-supplemental after all.

## 4. Homing (fixed; do not rename)

| group | module | nodes |
|---|---|---|
| **G1** | `Analysis/Complex/Pompeiu.lean` | 1, 2, 3, 4 |
| **G2** | `Analysis/Complex/MeromorphicResidue.lean` | 5, 6 |
| **G3** | `ModularForms/FundamentalDomainStokes.lean` | 7 |
| **G3** | `Analysis/Complex/CircleIntegralResidue.lean` | 8, 9 |

`Analysis/Complex/Dbar.lean` exists (manager-written) and carries `Complex.dbar` and `dbar_apply`;
**import it, do not edit it**. Helpers are `private` unless another module of this wave needs them; the
nine headlines are public at their pin names. No `W1`/`aj`/`FLT` token in any path or declaration
name, no random tokens (`x'`, `aux3`, `test1`).

**These modules are mathlib-shaped and exempt from the strict `move_dead` pass**: a theorem with no
consumer yet is completeness, not dead content. Do **not** run `move_dead.py` on them (`dedup.py` is
fine).

## 5. Build discipline

* Edit loop: `flock .lake/flt_build.lock timeout 110 lake env lean -DautoImplicit=false <file>`;
  `flock .lake/flt_build.lock timeout 110 lake build <Module>` when a file is done.
* **No whole-tree build.** Never raise `maxHeartbeats`/`maxRecDepth`; a timeout means quarantine and
  bisect (tell a blow-up from contention by CPU time) and record which step is slow.
* **A build-time blow-up is fixed, not reported.** If a proof approaches the bound or a single tactic
  block storms, split the proof: separate the `Integrable` conjuncts into their own `private` lemmas,
  factor the local model / support transfers / named intermediate integrals, and replace monolithic
  `simp`/`gcongr`/`measurability` blocks by named facts. A stubbed or capped proof is not an acceptable
  outcome; the completion report gives the split (which lemmas came out, their lines, wall/CPU before
  and after).
* Serial builds only (the `flock` is there because siblings share `.lake`). Log each run to
  `lean/tmp/w1-<module>.log` and report the tail on failure.
* **0 warnings** per module; `set_option autoImplicit false` at the top of every file.

## 6. Do not edit existing modules

No existing Lean module is edited, no existing declaration promoted. If a needed helper is `private`
in a hub, re-derive it locally as `private` and report it. If a promotion is genuinely required, stop
and report with the declaration, its host, and the reason.

## 7. Wiring (text-only, no build) — correction after G1

**The original instruction here was wrong** (it named `check_port.py`): that script has no
`SOURCES`/`PORT_FILES`. Those lists live in the frozen `spec/old_check_stmts.py`, and playbook §4 says
*do not add an entry to either list*; `instructions.md`'s legacy rule is that a touched module is
*deleted* from the old checker, not added to it. **So touch neither list.** A modern module is wired
entirely by its header: put `spec-pin: Theorems/Thm_Complex_<stem>.lean` and
`spec-pin: P2M/Sol/S_Complex_<stem>.lean` per headline, and
`python3 spec/check_port.py <module>` diffs it with no registration — which is what produced the
`4 ok / 0 mismatch / 0 missing` of G1.

Run the checker after each module and reconcile the `identical` delta to the new public surface.
Mutation-test each headline: perturb one hypothesis, confirm the checker reports a mismatch, revert and
verify the file hash is back.

## 8. Stop and report

If a statement cannot be matched without moving the pin's text; if a premise turns out pin-local; if a
helper is genuinely needed publicly and is `private` in a hub; or if a build exceeds its bound and
bisecting does not settle it.

## 9. Completion report

Module paths and line counts; public/`private` counts per module; tier-0 warnings (target 0) and
wall/CPU; the checker before → after with the `identical` delta reconciled and one mutation result per
headline; `#print axioms` per headline (`[propext, Classical.choice, Quot.sound]`); the
upstreamability grep (`ComplexPlaceDictionary`, `periodAlongOf`, `periodLatticeOf`, `UpperHalfPlane`
must not occur in any of the nine statements); `git status --porcelain` showing only this wave's files;
anything you could not match, quoted.

## 10. The three groups

* **G1** (nodes 1–4): start immediately. `Dbar.lean` imports only `FDeriv.Basic`; the statements need
  `MeasureTheory` integration on `ℂ`, so import what elaborates (`Mathlib` is acceptable in this wave —
  this is analysis, not an FLT silo; report the import set you settle on).
* **G2** (nodes 5–6): starts **after G1 lands** — 5 cites 4 (`integral_mul_dbar_eq_neg_pi_mul_finsum_residue`,
  306) and 6 cites 3 (`integral_inv_sub_mul_dbar_eq_neg_pi_mul`, 463).
* **G3** (nodes 7–9): independent of G1 and G2 in the pin's graph; start immediately, in parallel with G1.

## 11. Outcome — W1 landed (manager-reviewed)

| module | group | lines | public | checker |
|---|---|---:|---:|---|
| `Analysis/Complex/Dbar.lean` (manager) | — | 132 | 10 | no wire (vocabulary + the ∂̄/`tsupport` API) |
| `Analysis/Complex/Pompeiu.lean` | G1 | 846 | 4 | `4 ok / 0 mismatch / 0 missing` |
| `Analysis/Complex/MeromorphicResidue.lean` | G2 | 728 | 2 | `2 ok / 0 mismatch / 0 missing` |
| `ModularForms/FundamentalDomainStokes.lean` | G3 | 714 | 1 | `1 ok` |
| `Analysis/Complex/CircleIntegralResidue.lean` | G3 | 348 | 2 | `2 ok` |
| **total** | | **2,768** | **19** | **9 headlines**, 140 `private` |

`check_port.py --all` now: **5845 ok, 0 mismatch, 0 missing, 31 own, 0 kw, 266 modules** (baseline
5836 / 262); the delta is exactly the nine headlines (+2 ok from G2, +7 from G1 and G3), reconciled
module by module, and all five modules are discovered from their own `spec-pin:` headers with
`PORT_FILES` untouched. `lake build` green on every module (3,557 / 3,624 / 2,814 jobs);
`#print axioms` `[propext, Classical.choice, Quot.sound]` on all nine; every mutation test caught and
reverted with the file hash verified.

**Ruling 1 — the frozen checker.** G3 followed the original §7 and appended 16 lines to
`spec/old_check_stmts.py`. That file is frozen, playbook §4 forbids the addition, and its side effect
was to exempt both modules from the checker's default `--changed` scan. **The manager reverted it**
(`git checkout -- lean/spec/old_check_stmts.py`); the legacy count returns to its 7872 baseline and the
modules stay on the new checker's scan. §7 above is the corrected instruction; G1's no-touch behaviour
was right.

**Ruling 2 — the unused binder.** Node 7's verbatim statement carries `hU : IsOpen U`, which the Green
identity does not use (the two decay bounds already kill the boundary term). G3 silenced
`linter.unusedVariables` with a scoped `set_option … in` (four repo precedents, documented in the file);
G1 discharged the same situation with `have _ := hU`. Both leave the statement untouched and produce 0
warnings; leave both as they are, and note the inconsistency if the family is ever tidied.

**Drift, all three groups — proof text only.** mathlib v4.34 deprecated aliases (`Set.mem_setOf_eq`,
`setOf_and`, `mem_diff`, `dif_neg`/`dif_pos`, `ContinuousLinearMap.{add,smul,one}_apply`),
`MeasureTheory.`/`circleIntegral.` namespacing that the pin's private export prelude had hidden, and one
real elaboration change: `ContDiff` now takes `n : WithTop ℕ∞`, so the pin's
`have : ContDiff ℝ ∞ (f i : ℂ → ℝ)` no longer elaborates and becomes
`(contMDiff_iff_contDiff.1 (f i).contMDiff).of_le (by simp)` at `ContDiff ℝ 2`. No statement moved, and
the per-headline mutation tests confirm the checker would have caught any that did.

**The tidy is closed (manager, same day).** The eight `private` glue helpers that `MeromorphicResidue`
had re-derived from `Pompeiu` (§11 above, 63 lines, `dedup.py` name-tier) now live once, publicly, in
`Analysis/Complex/Dbar.lean` — which is their subject: `dbar_continuous`,
`dbar_eq_zero_of_notMem_tsupport`, `dbar_hasCompactSupport`, `continuous_mul_of_tsupport_subset`,
`integrable_mul_of_tsupport_subset`, `integrableOn_inv`, `integrableOn_inv_sub`,
`integrable_inv_sub_mul`. Both private copies were deleted; `Dbar.lean` grew 36 → 132 lines and took
over the import block the other two needed anyway; `Pompeiu.lean` 909 → 846, `MeromorphicResidue.lean`
792 → 728. `dedup.py` over the three modules now reports **0 duplicate clusters, 0 removable lines**
(was 8 / 63). Re-verified after the move: `lake build` green on all three (3,624 jobs) and
`check_port.py --all` unchanged at **5845 ok, 0 mismatch, 0 missing, 31 own, 266 modules**.

**Build-time ruling.** No blow-up occurred: G2's node 6 was written as 36 named private lemmas from the
start (largest 133 and 116 lines), `lake env lean` at 8.06 s wall, no cap overrides, no stub. The §5
rule stands for later waves.
