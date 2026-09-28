# SET-1 — the `Γ_H` vocabulary (l1)

Run brief for the first set of [PORTING-Level.md](../PORTING-Level.md).

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured with mathlib prebuilt: a green
> `lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
> deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
> **errors in ~15–20 s** — it does not hang. A healthy full `lake build` of this
> tree is **seconds to about a minute**.
>
> - Run every build under a hard bound: `timeout 60 lake env lean <file>`,
>   `timeout 90 lake build <module>`, `timeout 180 lake build`. **A multi-minute
>   build is never acceptable, not even while experimenting** — a fifteen-minute
>   bound is a bug in the work order, not a licence to wait.
> - **Expect ≤ 30 s.** Any single build past ~60 s must be treated as a blow-up
>   and bisected, not watched; a bound that lets a build run to 15 minutes is
>   itself the failure.
> - **Quarantine immediately.** On a non-return, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch.lean` with
>   `set_option diagnostics true` and a low cap (`set_option maxHeartbeats 20000`).
>   Do not re-run the same file hoping for a different result.
> - **Never raise `maxHeartbeats` (or `maxRecDepth`).** The cap already fails in
>   under 20 s; raising it turns that into an unbounded wait.
> - **Tell a blow-up from contention by CPU time.** Measure with `time`:
>   high user CPU + timeout is a real blow-up (bisect); ~0 CPU wall-time is lock
>   contention with another agent's build (re-run when idle; never build
>   concurrently with another agent).

## Deliverable

One module:

```text
FLTForHuman/ModularForms/Defs/GammaH.lean
```

Green, 0 warnings, no `sorry`, namespace `CohCarrier`, all declarations
transcribed (statements verbatim, proofs adapted only for mathlib v4.34.0).

## Declarations, in port order

The pin references are to `aa2d8b3`; the work order for the full statements is
[TOPIC-l1-gammah-vocabulary.md](TOPIC-l1-gammah-vocabulary.md).

1. `Gamma0_d_mul_a` — `Def_CohCarrier_Level:111`.
2. `gamma0Units`, `val_gamma0Units` — `Def_CohCarrier_Level:121`.
3. `GammaH`, `mem_GammaH_iff`, `GammaH_le_Gamma0`, `GammaH_top` —
   `Def_CohCarrier_Level:133`, `:138`, `:146`, `:151`.
4. `translation_mem_GammaH`, `Gamma1_le_GammaH`, `GammaH_bot`, `GammaH_mono` —
   `Def_ModularCurve_XH:20`, `:32`, `:46`, `:64`.
5. `gamma0Units_surjective` — `Def_CohCarrier_Inst:39`.
6. `Gamma_le_GammaH`, `GammaH_finiteIndex` — `Def_CuspForm_HeckeOperatorFormsGammaH:18`, `:32`.
7. `gammaLift`, `gamma0Units_gammaLift`, `unitOfPrimeNotDvd`, `gammaLift_apply_11`,
   `mul_inv_mem_GammaH_of_gamma0Units_eq`, `slash_mapGL_eq_of_gamma0Units_eq` —
   `Def_CuspForm_HeckeOperatorFormsGammaH:36`, `:39`, `:42`, `:45`, `:51`, `:60`.
8. `H1`, `GammaH_normal_in_Gamma0`, `conj_mem_GammaH`, `conjHom`, `diamondRaw` —
   `Def_CohCarrier_Level:162`, `:261`, `:275`, `:284`, `:291`.

## Left out, with reason and count

| pin declaration | `grep -c` in pin | reason |
|---|---|---|
| `Gamma0Upper`, `mem_Gamma0Upper` (`:90`, `:107`) | 8, 4 | Hecke-compatible subgroup; needs the transfer layer, deferred to L3 |
| `conjUpperMat` + 3 lemmas, `GammaHUpper`, `dvd_of_mem_GammaHUpper`, `conjUpperMat_mem`, `conjL`, `heckeT` (`:168–259`) | 6–12 | the cohomological level-raising operator; its own topic |
| `Gamma0Upper_isCongruenceSubgroup`, `Gamma0Upper_finiteIndex` (`:242`, `:247`) | 3, 2 | follow `Gamma0Upper` |
| `LevelLE`, `iotaDeg`, `jDeg`, `coresAdd`, `pushChar` (`:15–84`, `:300–506`) | 10–25 | the level-map theory; L3 or its own topic |
| `translation_mem_GammaH`'s siblings in `ModularCurve_XH` (`xHFunctionField*`) | — | `ModularCurve` theory, not group vocabulary |
| `diamondL`, `opFamily`, `hdata`, `heckeTL` (`Def_CohCarrier_Inst:23–113`) | 1–4 | Hecke-data machinery, not group vocabulary |

## Verification

- Append the four pin `Definitions/` files to `SOURCES` and
  `FLTForHuman/ModularForms/Defs/GammaH.lean` to `PORT_FILES` in
  `spec/check_flt_statements.py`; the checker reports 0 mismatched / 0 missing
  for the new module.
- Add a `[level]` zone to `spec/ModularCurveConsumer.lean`: instantiate
  `GammaH 2 ⊤`, prove `= Gamma0 2` by `GammaH_top`, use `gammaLift`/
  `gamma0Units_gammaLift` in a cross-module composition.
- `#print axioms` on `GammaH_bot`, `gamma0Units_surjective`,
  `GammaH_normal_in_Gamma0` returns only `[propext, Classical.choice, Quot.sound]`.
- `timeout 90 lake build FLTForHuman.ModularForms.Defs.GammaH` green with
  0 warnings.

## Definition of done

Module as named; `lake build` green; checker 0/0; axioms clean; a `logs/level-port.md`
section recording the pin lines, the `grep -c` counts of what was left out, and
the measured dedup; a `README.md` row.
