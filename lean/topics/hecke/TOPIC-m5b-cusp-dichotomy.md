# Topic m5b — the `RatFunc` dichotomy, the prime degree and the restrict-scalars identity (re-scope of the blocked `CuspDichotomy`)

**Status (2026-09-23): re-scope of a blocked piece; ready to dispatch.** This is
a focused replacement for the tail of [TOPIC-m5](TOPIC-m5-cusp-fricke-aut.md),
which the SET-M2 subagent left blocked by a **kernel deterministic timeout** (see
[../logs/mc-port.md](../logs/mc-port.md) §Friction). Everything else in SET-M2 has
landed and is green (checker **1,166 identical, 0 mismatched, 0 missing**;
`lake build` 4,099 jobs; `FrickeAut` builds in 16 s).

## 0. What this topic owns

Three wrapper targets (the m5 tail):

- `ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar` (`Theorems/Thm_...`)
- `ModularCurve.finrank_adjoin_jqNModC_eq_of_prime`
- `ModularCurve.modularFunctionFieldBar_eq_restrictScalars`

The m4 third headline (`coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant`,
`coe_frickeInvolutionFull_modularUnitSeries`) is **already delivered** in
`Analytic/FrickeAut.lean` and verified — do not touch it. The 15 other m5 nodes
are delivered in `Analytic/CuspBookkeeping.lean` and `Analytic/FrickeAut.lean`.

## 1. The blocker, precisely

The previous attempt left `Analytic/CuspDichotomy.lean.wip` (a backup is at
`/tmp/CuspDichotomy.fixed.lean`). It contains the pin's shared **160-content-line
`RatFunc` model** (the same one `eq_cuspInftyBar_or_eq_cuspZeroBar` and
`finrank_adjoin_jqNModC_eq_of_prime` share in the pin — see
[TOPIC-m5](TOPIC-m5-cusp-fricke-aut.md) §3's dedup note) plus the two targets.

- `lake env lean …CuspDichotomy.lean` runs **3 m 09 s (user 3 m 17 s)** and errors
  with `(kernel) deterministic timeout` at `TwoCuspAux.coe_jTr`, then
  `unknown constant TwoCuspAux.coe_jTr`, more kernel timeouts at `coe_φ` /
  `φ_algebraMap`. `lake build` exceeds 240 s and writes no olean.
- Root cause: `TwoCuspAux.jTr` is a `Subtype` ring equivalence whose `toFun` is
  `fun x => ⟨x, (mem_bar_iff ℓ x).mpr x.2⟩`, and `mem_bar_iff` is proved through
  a shortcut `bar_eq_restrictScalars` (`full_eq_of_prime` +
  `laurentBaseChange_modularFunctionField_local` + `adjoin_simple_adjoin_simple`).
  Checking `coe_jTr`'s definitional equality makes the kernel normalise that heavy
  proof term and hit the kernel's deterministic timeout. The previous attempt's
  file also carried a botched duplicated block (former lines 324–356:
  `le_finrank`/`finrank_tower_eq` re-declared outside `TwoCuspAux` using its local
  `𝕂`); the manager deleted it.

**Do not raise `maxHeartbeats` (or `maxRecDepth`) and do not raise the build
timeout.** Restructure instead.

**Diagnose with CPU time.** Measure every bounded build with `time` (or
`/usr/bin/time -v`). A real blow-up shows **high user CPU** plus a `timeout` kill:
the blocked module ran real 3 m 09 s with **user 3 m 17 s** and
`(kernel) deterministic timeout`. A wall-time stall with **near-zero user/sys**
(real 4 m 34 s, user 0.5 s) is lock/serialization contention, not a Lean problem
— re-run when idle instead of bisecting. Run builds one at a time and never
concurrently with another agent.

## 2. Route guidance — try in this order, in `Scratch*.lean`

1. **Reuse `bar_eq_restrictScalars` but keep it out of the kernel's way.** State
   it `@[irreducible]` (or as an opaque `theorem`) and prove `mem_bar_iff`
   separately; then define `jTr` so its coercions do not carry that proof:
   `toFun x := (⟨x, (mem_bar_iff ℓ x).mpr x.2⟩ : modularFunctionFieldBar ℓ)`, with
   `left_inv`/`right_inv`/`map_mul'`/`map_add'` by `Subtype.ext rfl`, and prove
   `coe_jTr` by `rfl` — if the kernel still unfolds the proof, make `jTr` opaque
   (`@[irreducible]`) and give `coe_jTr` a direct proof.
2. **Avoid `jTr` entirely.** The pin's `finrank_tower_eq` only needs a ring
   equivalence `𝕂⟮jqModC⟯⟮jqNModC⟯ ≃+* modularFunctionFieldBar ℓ`. Build it from
   `RingEquiv.ofBijective` of the inclusion `Subtype.val`-style map, or from the
   equality of carriers via `Subring.equivOfEq`/`RingEquiv.cast` once
   `bar_eq_restrictScalars` is available — whichever keeps the kernel check cheap.
3. **Take the pin's actual `DivUSol` route** if the shortcut is the problem. The
   pin proves `modularFunctionFieldBar_eq_restrictScalars` through the cuspidal
   divisor `(ℓ-1)·cuspidalDivisor` principal argument (m5's `CuspDichotomy` pin
   `S_` file lines 41–258: `ubar`, `fricke_ubar`, `ord_inf`, `ord_zero`,
   `isPrincipal_smul_cuspidalDivisor`, `addOrderOf_cuspidalClass_dvd`), and the
   `mem_bar_iff` there may be a definitional `rfl` because the pin's
   `modularFunctionFieldBar` membership is set up differently. Read the pin's
   `S_ModularCurve_modularFunctionFieldBar_eq_restrictScalars.lean` and
   `S_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar.lean` before choosing.

Whichever route wins, `eq_cuspInftyBar_or_eq_cuspZeroBar` and
`finrank_adjoin_jqNModC_eq_of_prime` must keep the shared model **written once**.

## 3. Verification and bookkeeping

- Restore the module as `Analytic/CuspDichotomy.lean`; build it with
  `timeout 60 lake env lean …` and `timeout 90 lake build FLTForHuman.ModularCurve.Analytic.CuspDichotomy`.
  If a build exceeds the bound, stop and bisect in `Scratch*.lean`; never raise a
  cap.
- Append the three wrappers to `SOURCES` and the module to `PORT_FILES`; run the
  checker to **0 mismatched, 0 missing** (the baseline after SET-M2's first half
  is **1,166 identical, 0 mismatched, 0 missing**). Note the wrapper binders must
  match verbatim (`eq_cuspInftyBar_or_eq_cuspZeroBar` takes `(ℓ) [Fact ℓ.Prime]
  (w) (hc)`; `finrank_adjoin_jqNModC_eq_of_prime` takes `(ℓ) [Fact ℓ.Prime]`;
  `modularFunctionFieldBar_eq_restrictScalars` takes `(ℓ) [Fact ℓ.Prime]`).
- `#print axioms` on all three; `timeout 180 lake build` green, 0 warnings, no
  `sorry`.
- Consumer: add/extend **Zone E `[cusp]`** in
  `lean/spec/ModularCurveHeckeConsumer.lean` (0 errors **and** 0 warnings):
  instantiate the dichotomy at a concrete prime, the prime degree at `ℓ = 2`, the
  restrict-scalars identity at `ℓ = 2`.
- `logs/mc-port.md`: fill the §m5b close and extend §Friction; `README.md`: rows
  for `Analytic/CuspDichotomy.lean` (and the m5 half already there).
- **No commits.** Do not edit the paused Hecke face, FFG/Φ modules, AC modules, or
  the other SET-M1/SET-M2 modules. (FFG files are now editable if a genuinely
  shared helper must move, but report before doing so.)

## 4. Budget

**2 goal rounds.** Round 1: the route scout in `Scratch*.lean` and a cheap
`jTr`/`φ` (build the module bounded). Round 2: the two other targets, the
bookkeeping, consumer, log/README.

**Stop early** only if no route makes the module build under `timeout 90`: then
leave the tree green (keep the file aside), report the exact kernel-reduction goal
and the routes tried, and let the manager decide.

## 5. Reporting back

1. Which `jTr`/`φ` route won and why the kernel check became cheap; the exact
   build time of the module.
2. The checker delta and the `#print axioms` results.
3. Whether the `RatFunc` model is written once (with `grep -c`).
4. Any statement that would not match its wrapper (quoted), and any new friction.
