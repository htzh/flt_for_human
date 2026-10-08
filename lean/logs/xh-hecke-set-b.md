# SET-H-B — the diamond-lift pair, written once

Work order: [SET-H-B.md](../topics/hecke/SET-H-B.md) of
[TOPIC-xH-hecke-diamond-inputs.md](../topics/hecke/TOPIC-xH-hecke-diamond-inputs.md) §5.
Pin `aa2d8b3`, mathlib `v4.34.0`. SET-H-A (the `X_H(M)` definition layer) landed;
see [xh-hecke-set-a.md](xh-hecke-set-a.md).

**Result.** 3 new modules (1,620 raw / 1,196 content lines, 121 public checker-visible
declarations), 1 checker wiring (2 `SOURCES` + 2 `PORT_FILES` entries), 1 consumer
zone. Checker `6365 → 6486 identical (312 promoted, 83 renamed), 0 mismatched,
0 missing, 36 own (6522 checked)`. Consumer `spec/XHConsumer.lean` error+warning
count `0`; delete-fail `6` (three uses per headline). `#print axioms` on both
headlines is `[propext, Classical.choice, Quot.sound]`. Whole-tree `lake build`
green (9,335 jobs). All three phases (P1/P2/P3) landed.

## 1. Per-module line counts and declaration counts

| module | raw | content | public decls | role |
|---|---:|---:|---:|---|
| `FLTForHuman/ModularCurve/XH/DiamondLiftPrelude.lean` | 845 | 609 | 89 | the general-`Γ` engine |
| `FLTForHuman/ModularCurve/XH/DiamondLift.lean` | 386 | 293 | 16 | `Γ_H(M)` specialisation + H headline |
| `FLTForHuman/ModularCurve/X1/DiamondLift.lean` | 389 | 294 | 16 | `Γ₁(M)` specialisation + X₁ headline |
| **new total** | **1,620** | **1,196** | **121** | 2,366 raw pin `S_` lines |

(content = raw minus `import`/`attribute`/`namespace`/`end`/`open`/`section`/
`variable`/`#`/comment/blank lines; the comment strip is the checker's
`/- … -/` pass plus leading-`--` lines.) The plan's §1 estimate was 1,403 net new
math lines; the 207-line saving is the 13 reused declarations of §3 below.

Edits (numstat):

| file | +/− | content |
|---|---|---|
| `spec/check_flt_statements.py` | +11/−0 | 2 `SOURCES` (the two `Theorems/` wrappers) + 2 `PORT_FILES` |
| `spec/XHConsumer.lean` | +54/−0 | Zone XH-D `[xh-diamondlift]` + 2 imports |

## 2. What the engine reuses instead of restating

`§3.3 item 3` names 13 declarations as "already public — import, never restate".
Measured: **7 are honestly reusable and were reused** —

* `ModularCurve.slash_inv_slash`, `ModularCurve.slash_slash_inv` — note these are
  **not** in `ModularCurve.X1DiamondPullback` (which starts at
  `X1/DiamondAut.lean:187`); they are declared in `namespace ModularCurve` proper
  at `X1/DiamondAut.lean:105,108`, so the general engine can call them
  unqualified, exactly as the pin does. (`logs/xh-hecke-set-a.md` §3 lists their
  *file*, `X1/DiamondAut.lean`, with no namespace claim; it is correct — only the
  declarations below `namespace X1DiamondPullback` (line 187), such as
  `IsRatio`, are in that inner namespace.)
* `ModularCurve.expandPS`, `coeff_expandPS`, `intSeriesC_expandPS`,
  `heckeDiagMatrix_mul_eq`, `isCusp_heckeDiagMatrix_smul` (`X1/QExpandStretch.lean`).

The other **6 cannot be reused**, because the port's copies are either
`Γ₁(M)`-specialised with the same last name or are stated against a `private`
constant:

| pin declaration | why the prelude needs its own `Γ`-general copy |
|---|---|
| `IsRatio` | the port's is `X1DiamondPullback.IsRatio (x) : Prop` under `variable (M) [NeZero M]`, body `ModularForm Γ₁(M) k`; the engine's is under `variable (Γ) [IsLevel Γ] [Γ.FiniteIndex]`, body `ModularForm GL↑(Γ) k` |
| `ratioField` | same |
| `qC_zero`, `qC_one` | the port's `X1DiamondPullback.qC` is `private`, so a prelude `def qC` cannot be related to it |
| `toC_injective`, `toC_algebraMap` | the port's `X1DiamondPullback.toC` is `private abbrev`; same |
| (`coeffEmb_qExpand`) | reused from `ModularCurve.Defs/Laurent.lean` (binder `n`), as §3.3 item 4 directed |

`Conj_mem_Gamma1`/`CohCarrier.conj_mem_GammaH` are reused by import (§3.3 item 5);
no copy is declared. The pin's `private mapGL_coe_eq` is not transcribed — it
belongs with the reused `heckeDiagMatrix_mul_eq`.

## 3. One correction to the work order: `toC_qExpand`

§3.2 says "`toC_qExpand` (Bar has it, H does not)". Measured: **both** `S_` files
declare it (`S_…diamondAutHBar.lean:907`, `S_…diamondAutBar.lean:959`), and the
statement and body are byte-identical. It is therefore in the **prelude** (one
declaration instead of two), and both consumers use it. The checker confirms: the
prelude copy resolves to the pin copy (`+1` identical where the plan expected the
Bar consumer to carry it).

`Gamma1_mul_le_level` (H only) stays in the H consumer; the Bar file inlines the
same `le_inf` in `rationalSlash_level`.

## 4. Checker

```
baseline (before SET-H-B):   6365 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6401 checked)
+ prelude (88 decls):        6453 identical                                       (+88)
+ toC_qExpand moved up:      6454 identical                                       (+1)
+ XH/DiamondLift.lean:       6470 identical                                       (+16)
+ X1/DiamondLift.lean:       6486 identical (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6522 checked)  (+16)
```

The +121 reconciles exactly as 89 (prelude) + 16 (H) + 16 (X₁); the per-module
declaration lists are printed by the checker's own `raw_declarations`. `promoted`
stays `312`: every new public declaration resolves through the public last-name
lookup against an `S_` file (the engine) or against a `Theorems/` wrapper (the two
headlines — without the wrappers the `S_` files register them only under the name
`solution`, so both wrappers were appended to `SOURCES` as §1 directed).

One-token mutation: the H headline's `(d : (ZMod M)ˣ)` → `(d : ZMod M)` gave
`6485 identical / 1 mismatched / 0 missing`, the diff naming
`Theorems/Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar.lean`
as the source; reverted → `6486 / 0 / 0`.

`--prop-bodies` (advisory): `277 Prop-valued def bodies identical, 7 differ`
(was `275 / 7`); the +2 are the engine's `IsRatio` and `RationalSlash`, both
byte-identical to the pin's. `IsLevel`/`Normalizes` are `class`es and are not
measured by that pass (it skips non-`def`/`abbrev` kinds). The 7 differences are
the pre-existing set, unchanged — including the `X1DiamondPullback.IsRatio`
collision SET-H-A §3 recorded (the pass keys by last name, so the engine's copy is
compared under `DiamondLift.IsRatio` and the port's under the unrelated
`S_…mem_laurentBaseChange_of_coeffMap_eq_qExpansion_div` body; our copy is
identical and is not reported).

## 5. Consumer

`spec/XHConsumer.lean`, new Zone XH-D `[xh-diamondlift]`, six examples:

* the engine named directly — `DiamondLift.RationalSlash (Γ₁ 2 ⊓ Γ₀ 4) (Γ₀ 4)`
  via `DiamondLift.X1.rationalSlash_level`, which exercises the shared
  `XH/DiamondLiftPrelude.lean` (so deleting the prelude fails the zone);
* the `X_H` headline at `(M, H, ℓ, d) = (2, ⊥, 2, 1)`, with the `∃ τ` destructured
  into a real `laurentBaseChange ℚ̄ (xHTopFunctionFieldC ℚ 2 ⊥ 4) ≃ₐ[ℚ̄] …`
  (`private noncomputable def hBarTau`) plus an example for each of the two
  `IntertwinesAlong` conjuncts;
* the `X₁` headline at `(M, ℓ, d) = (2, 2, 1)`, destructured the same way
  (`private noncomputable def oneBarTau`).

`lake env lean spec/XHConsumer.lean` → `0` errors / `0` warnings (9.5 s). Delete-fail
probe (copy under `tmp/`, rename the two headline names): **6** errors, three uses
per headline. The pre-existing `spec/ModularCurveHeckeConsumer.lean` still reports
`0` errors and warnings.

## 6. Axioms, build times, whole tree

`#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`;
`grep -rn sorry` over the three modules is empty.

| command | result | wall | user | sys |
|---|---|---:|---:|---:|
| `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` | edit loop, 0 warnings each | — | — | — |
| `flock … timeout 600 lake build FLTForHuman.ModularCurve.XH.DiamondLiftPrelude` | ✔ 4133 jobs | 11.8s | 16.0s | 5.2s |
| `flock … timeout 600 lake build FLTForHuman.ModularCurve.XH.DiamondLift` | ✔ 4145 jobs | 17.4s | 20.5s | 3.3s |
| `flock … timeout 600 lake build FLTForHuman.ModularCurve.X1.DiamondLift` | ✔ 4143 jobs | 14.9s | 20.2s | 3.4s |
| `flock … timeout 900 lake build` (whole tree) | ✔ 9335 jobs (cached replay) | 6.2s | 6.7s | 7.0s |
| `timeout 600 lake env lean spec/XHConsumer.lean` | 0 errors | 9.5s | 9.9s | 1.7s |
| `timeout 600 lake env lean spec/ModularCurveHeckeConsumer.lean` | 0 errors | 22.4s | 21.7s | 2.3s |

No bound was hit; `maxHeartbeats` was never raised.

## 7. Friction log (proof-level, in the order it bit)

1. **`⟨_, hdet⟩ : SL(2, ℤ)` inside `rw`.** `Matrix.SpecialLinearGroup n R` is a
   `def` of `{A // A.det = 1}`, and v4.34's elaborator unfolds it at `.implicit`
   transparency when the term is used as an argument of `Gamma0_mem`/`Gamma1_mem`,
   producing a goal that is not type-correct. The pin never sees this: its
   lakefile sets `backward.isDefEq.respectTransparency.types false` globally. Fixed
   by naming the witness first — `let γ₁ : SL(2, ℤ) := ⟨…, hdet'⟩` — which is the
   port's own idiom (`CohCarrier.gamma0Units_surjective`,
   `X1/DiamondAut.lean:143`). Affects `exists_gammas` (prelude), `cocycle` (both
   consumers).
2. **`rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at this`** failed on the same
   ill-typed hypothesis; replaced by the term form
   `(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ0)`, the port's
   idiom in `ModularForms/HeckeInvariance.lean:74`, `Eisenstein/WeightOneMultiplier.lean:238`.
3. **Deprecated aliases in the pin's proofs.** `ModularForm.coe_add`/`coe_neg`/
   `coe_zero`/`ModularForm.IsGLPos.coe_smul`/`if_pos`/`if_neg` are deprecated in
   v4.34; the transcriptions use `FunLike.coe_add`/`coe_neg`/`coe_zero`/`coe_smul`
   and `ite_eq_left`/`ite_eq_right`, as `X1/DiamondAut.lean` and
   `X1/QExpandStretch.lean` already do. No `set_option linter.deprecated false`
   was needed.
4. **`set_option backward.isDefEq.respectTransparency.types false in`** is needed
   on both `main`s: `FT M H ℓ` / `FT M ℓ` and `xHTopFunctionFieldC ℚ M H (M*ℓ)` /
   `x1x0FunctionFieldC ℚ M (M*ℓ)` are the same field spelled as two different
   `def`s, and `SemilinearAut.ofAlgAut τ` needs the algebra instance of the goal's
   spelling. This is exactly the topic's §6 risk 2. Scoped to the one declaration
   rather than the file, as `X1/DiamondAut.lean`/`X1/Inputs.lean` do. Everything
   else in the pair (including `comp_alpha_eq`/`comp_beta_eq`) elaborates without
   the option, because `algHom_ext_of_eq_adjoin`'s `S` is the *`FB`*-level field
   (`rfl` there is genuine: `laurentBaseChange L F = adjoin L (coeffEmb L '' ↑F)`).
5. **Scoped-instance activation.** The pin's `scoped instance`s (`isLevel_*`,
   `normalizes_*`, `finiteIndex_*`) are active inside their own namespace, so no
   `open scoped` was needed inside the two consumers. They stay `scoped` exactly
   as in the pin: `DECL_RE` cannot see `scoped instance`, so a plain `instance`
   would become checker-visible and report `missing`.
6. **`CohCarrier.`/`ModularForm.Level.` qualification.** `translation_mem_GammaH`,
   `Gamma1_le_GammaH` are `CohCarrier.*`; `conj_mem_Gamma1` is
   `ModularForm.Level.conj_mem_Gamma1` (`ModularForms/Level/Diamond.lean:166`, not
   `Gamma0Integral.lean` as §3.3 item 5 says — that file's copy is `private`).
   Proof-level only, no statement impact.
7. **`isLevel_Gamma1` / `isLevel_Gamma1_inf_Gamma0`.** The pin's
   `by simp [Gamma1_mem, ModularGroup.T]` / `by simp [Gamma0_mem, ModularGroup.T]`
   no longer close in v4.34 (`Gamma1_mem`/`Gamma0_mem` are already `simp` lemmas,
   and the `Submonoid`-projected goal defeats the syntactic `rw`). Replaced by the
   port's `by simp` (`X1/Inputs.lean:154`) and
   `⟨by simp, by simp [Gamma0_mem]⟩` (`X1/Inputs.lean:157`).

## 8. Deferred, and what SET-H-C inherits

* `HeckeDiamondInputsHAll`'s capstone and its producer remain deferred (SET-H-C /
  manager-reserved), unchanged by this set.
* The two headlines are unconditional: nothing in this set is `sorry`-closed and
  the consumer consumes them at concrete data.
* `X1/Inputs.lean` already carries a `private` copy of the Γ₁ `cocycle` and of
  `T_mem_Gamma1`; the X₁ consumer transcribes its own public `cocycle` rather than
  promoting, so no module outside `XH/`–`X1/DiamondLift.lean` was touched. If a
  later set wants the dedup, the promotion is a one-line `private` drop with the
  usual checker re-run.
