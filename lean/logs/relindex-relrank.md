# The `RelIndex` pair — ground, bodies, receipt

Record for the set in [../topics/modularCurve/TOPIC-relIndex-relrank.md](../topics/modularCurve/TOPIC-relIndex-relrank.md),
ordered by [../topics/modularCurve/WORKORDER-RI1-relindex-relrank-pair.md](../topics/modularCurve/WORKORDER-RI1-relindex-relrank-pair.md).
The set ports the two halves of the degeneracy-cover degree

```
[Γ : Γ ∩ Γ₀(N)]  ≤  [A(j(q^N)) : A]            (RelIndex, 1,214 pin lines)
[A(Γ') : A(Γ)]    ≤  [Γ : Γ']                    (RelrankNorm, 545 pin lines)
```

as two façade modules over one shared ground. Pin `aa2d8b3`.

## 1. What the manager landed before the bodies

Four new tier-3 modules and one promotion, plus the registry handoff of the module the promotion
lives in. No headline in this wave: the four ground modules carry no `spec-pin:` and contribute
nothing to the checker; `JqIntegralRatios.lean` moved onto its own wire and contributes **+23**.

| module | lines | decls | what |
|---|---:|---:|---|
| `FLTForHuman/ModularCurve/Analytic/AnalyticAtCusp.lean` | 116 | 10 | the pin's `Nice`/`An1` predicate and its closure (`AnalyticAtCusp.{mul,add,pow,sum}`, `qExpansion_{pow,sum}'`, `analyticAtCusp_{one,zero,of_modularForm}`) |
| `FLTForHuman/ModularCurve/RelIndex/Hermite.lean` | 160 | 26 | the Hermite normal form of `dMul N γ` (`hA`/`hB`/`hD`/`hδ`, `hermite_spec`, `nA`/`nB`/`nD`, `mul_inv_mem_Gamma0_of_hermite_eq`) |
| `FLTForHuman/ModularCurve/RelIndex/LevelRaise.lean` | 278 | 26 | `one_mem_strictPeriods`(+`natCast`, + the conjugated/diagonal/twist forms), `hP` and `heckeDiag_{mul_eq,smul_smul}`, the general `raise`/`twist`/`expU`/`twRaiseFn` |
| `FLTForHuman/ModularCurve/RelIndex/RatioField.lean` | 294 | 24 | `ratioSet`/`ratioField`, the `qC` group, `common_denominator`, `coe_finset_sum`, `qC_{eq_qExpand_of_coeff,raise,twist,twRaiseFn}` |
| `FLTForHuman/ModularCurve/JqIntegralRatios.lean` | +0 | 8 promoted | `e4cube`, `delta`, `isIntegralQExp_{e4cube,delta}`, `coe_delta`, `intSeriesC_delta_ne_zero`, `jqModC_mul_delta`, `jqModC_eq_div` — the pin's `JqMemRatios` block, `private` → public, no proof moved. The module also moved off the frozen registry onto its own wire (below) |

848 new lines, 86 declarations, 0 warnings, `lake build` of each module in the oleans (3.5 s /
5.3 s / 4.9 s / 4.7 s on a 3,100–4,100-job dependency cone). All four are registered tier 3 by
`spec/unwired_register.py` (141 modules / 4,223 public declarations after the wave).

**The registry handoff.** `JqIntegralRatios.lean` was in the frozen checker's `PORT_FILES`; it is
now off that list and carries its own five `spec-pin:` lines instead
(`Definitions/Def_ModularCurve_X1.lean`, `S_`/`Thm_` of `jqModC_mem_intFormRatiosC`, `S_`/`Thm_`
of `jqModC_eq_qExpansion_E4_cube_div_discriminant`). `spec/check_port.py` reads it
**23 ok / 0 mismatch / 0 missing / 0 own / 0 kw** — the first module of this cut whose whole public
surface, including the eight promotions, is diffed. Two consequences worth the record: the frozen
checker's reading of the module is now the new checker's business (no wave build was run to
"justify" the promotions — byte-exactness is the evidence, and a promotion changes no proof term),
and the `PORT_FILES` comment block that described the module now records where it went.

**The one structural decision worth the record** is `ratioSet`. `DiamondLift.IsRatio` is the same
predicate, public, general in `Γ` — but it carries `[IsLevel Γ]` and `[Γ.FiniteIndex]`, and
*neither* pin theorem assumes `Γ` has finite index (it is any subgroup containing `T`). Importing
it would have forced the bodies to prove an instance the pin does not have, so the definition was
stated once, without instances, and `qC` (instance-free) was imported from the same module. The
unification of the two is residue, §5.

`ratioSet` unfolding to the exact set literal both pin headlines write out was probe-verified for
both headlines before dispatch (`change` goes through, `tmp/probe/change.lean`).

## 2. The dedup findings

Measured with `tools/deps` (full `port_advise --no-drags` report captured in `tmp/scope/advise.txt`):

* `port_advise`: **23** substitutes (148 lines; 21 byte-identical, 2 binder-spelling), **12**
  binder-skeleton relatives, **29** port name clashes, **0** port-`private` matches — the last is
  the instrument's blind spot: the whole `LevelOne` block of the `RelIndex` file *is* in the port,
  as eight `private` declarations of `JqIntegralRatios.lean`, and `port_advise` cannot see them
  because their statements are at general `Γ` rather than at `SLtop`.
* `shapes.py` (pin copy parked under `lean/tmp/pin/`): of 121 theorem/lemmas, **20** have a
  same-shape twin in another port module — all in `XH/Relrank.lean` (the *twin pin file*) plus
  `JqIntegralRatios`.
* Pin copy counts over the 60,478-file corpus: `one_mem_strictPeriods` **324** files,
  `ratioField` 25, `Nice` 22, `qExpansion_pow'` 11, `qExpansion_sum'` 10, `coeff_sum_C_mul_X_pow`
  9, `mem_S_of_mem` 9, `common_denominator` 5, `SField` 3, `ratioSet` 2, `isRoot_of_rel` 2,
  `An1` 2.
* Port copies at scoping time: 3 "analytic at the cusp" predicates (two of them the pin's, one a
  different predicate), 2 public `ratioField`s, 3 `S`/`SField`s, 4 `levelRaise`s.

The full verdict table is §3 of the topic note. The two decisions taken *against* a tool reading
are recorded there too: `DiamondLift.IsRatio` not imported (wrong generality), and the pin's two
spellings collapsed into one.

## 3. The bodies

| module | lines | decls | headline |
|---|---:|---:|---|
| `FLTForHuman/ModularCurve/RelIndex/LeRelrank.lean` | 690 | 68 (1 public, 67 private) | `ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC` |
| `FLTForHuman/ModularCurve/RelIndex/LeRelIndex.lean` | 445 | 34 (1 public, 33 private) | `ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex` |

Both are façade modules: the pin's namespace for the engine (`RelrankNormSol`,
`RelIndexJqSol`) holds the private declarations, the headline sits in `ModularCurve`.

**`LeRelIndex`** (the norm side) re-verified by the manager: `lake env lean` silent, `lake build`
4,153 jobs in 6.6 s, checker `1 ok, 0 mismatch, 0 missing, 0 own, 0 kw`, axioms
`[propext, Classical.choice, Quot.sound]`. The pin's whole `Ratio` section, its `Nice` block,
`one_mem_strictPeriods` and `coe_finset_sum` were **deleted** from the transcription and taken
from the ground; what remains is the norm/characteristic-polynomial engine. Deviations reported
by the body are all deprecation-grade (`IsGLPos.coe_smul` → `FunLike.coe_smul`,
`ModularForm.coe_sub` → `FunLike.coe_sub`, `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`,
`haveI` → `have`), plus two shape notes: the ground's `qC` is a `def` (so one `congrArg` step
needs `simp only [qC, …]`), and the pin's `set_option linter.unusedSectionVars false` is not
carried, so the pin's section variables became explicit binders. It reports **no** missing ground
declaration and no local substitute.

**`LeRelrank`** (the enough-conjugates side) re-verified by the manager: `lake env lean` silent,
checker `1 ok, 0 mismatch, 0 missing, 0 own, 0 kw`, axioms
`[propext, Classical.choice, Quot.sound]`, `lake build` 4,262 jobs in 7.5 s. The pin's `Groups`,
`Raise`/`TwistRaise`, `hP` and `Ratio` blocks and its `An1` block are **taken from the ground**,
not transcribed; `AF`/`DF` are the sanctioned two-line `abbrev`s of `e4cube ⊤`/`delta ⊤`, and
`XD_ne_zero`/`jqModC_eq_jC` are one-liners off `intSeriesC_delta_ne_zero`/`jqModC_eq_div`. The
pin's `conjMat`/`conjSL`/`heckeDiag_mul_mul_inv` are **imported** from
`ModularCurve.HeckeInputsHAll` at `ℓ := N`, `hℓ := NeZero.ne N` (with `M := 1` and one `simpa` for
the `Gamma0 (1 * N)` bridge). Two drifts worth naming: v4.34's `eq_div_iff` takes its nonzero
hypothesis explicitly, so `jqModC_eq_jC` is a one-line `(eq_div_iff h).mpr`; and the pin's
`scoped instance : Finite (Q Γ N)` became a local `have` (the `haveI` linter fires on a
proposition).

**The one local substitute** is `coeff_jqModC_neg_one`, four lines re-derived from `jqModC`'s
definition — the port holds it only `private`, in three modules (`Degree/PhiDegree.lean:53`,
`ModularPolynomialStarBank.lean:93`, `X0/FunctionFieldFull.lean`). §5 records it.

**Receipt (§5.7 of the dedup note).** `shapes.py` on `LeRelIndex` against the whole pin:
26 theorem/lemmas, 8 with a same-shape twin in the pin (5 of them in pin files that are not this
module's sources — the pin writes this prelude everywhere), and **5 with a same-shape twin in
another port module**: `natDegree_linear_le`, `node_injOn`, `eval_homogenize_linear`,
`eval_homogenize_eq_sum`, `sum_div_pow_eq`, all five public in
`ModularCurve/X1/FunctionField.lean:412,440,481,486,867` (the `JOneES` norm engine, which is the
*same* pin development). They are 3–8 lines each, generic (`ℂ[X]` degree, Lagrange nodes,
`homogenize`, a field identity), and `private` here. That is the predicted residue: a home for the
norm-engine prelude is a separate order, because it would have to open `X1/FunctionField.lean`
(§6 rule 4). Recorded, not opened.

**`LeRelrank`'s receipt.** 49 theorem/lemmas; 35 have a same-shape twin in the pin (6 of them in
`S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.lean`, the twin node),
and **6 have a same-shape twin in another port module**: `hSL1`, `XA_ne_zero`,
`qExpansion_finset_sum`, `isRoot_of_rel`, `coeff_sum_C_mul_X_pow`, `natDegree_sum_le` — every one
of them against `ModularCurve/XH/Relrank.lean:449,639,693,822,841,852`, i.e. the *other node
module*, not a subject home. Same class as `LeRelIndex`'s five: the port's prelude for this family
sits inside node modules, and homing it means opening one. Recorded, not opened.

## 4. Gates

| gate | reading |
|---|---|
| `spec/check_port.py --all` (whole wired surface, every module re-checked, 0 cached) | **3,830 ok, 0 mismatch, 0 missing, 11 own, 0 kw — 151 modules, 580 `PORT_FILES` exempt** (was 3,805 / 148 / 581) |
| `--force` on the three new/modified modules | `LeRelrank` 1 ok; `LeRelIndex` 1 ok; `JqIntegralRatios` **23 ok** — 0 mismatch / 0 missing / 0 own / 0 kw each |
| `lake env lean` per module | silent, 0 warnings, all six modules |
| `lake build` per module (single module, no wave) | `AnalyticAtCusp` 3,102 jobs / 3.4 s; `Hermite` 3.5 s; `LevelRaise` 3,429 / 5.3 s; `RatioField` 4,142 / 4.9 s; `JqIntegralRatios` 4,123 / 4.7 s; `LeRelIndex` 4,153 / 6.6 s; `LeRelrank` 4,262 / 7.5 s |
| axioms, both headlines | `[propext, Classical.choice, Quot.sound]` |
| `spec/unwired_register.py --check` | `register is current` (141 modules / 4,223 public declarations) |
| forbidden-token sweep | no `sorry`, no `admit`, no `axiom`, no `native_decide`, no `import Mathlib`, no `set_option maxHeartbeats` in any of the six modules |

No wave build was run. That is the round's standing rule (user's direction, 2026-10-21): a wave
build is not evidence for a promotion or a landing — the statement hash is — and it was not run to
"justify" the eight promotions either
([../topics/TOPIC-dedup-refactoring.md](../topics/TOPIC-dedup-refactoring.md) §4).

## 5. Residue (recorded, not opened — §6 rule 4 of the dedup note)

* the two `An1`/`Nice` copies of `X1/FunctionField.lean:516` and `XH/Relrank.lean:533`, and the
  *different* `Nice` of `OmegaRowT2.lean:145`;
* the four `levelRaise`s (`XH/HeckeInputs.lean:193`, `X1/IsIntegralAtkinLehner.lean:215`,
  `X1/AtkinLehnerExchange.lean:611,1413`) and `FrickeReciprocity.liftDiag` — the new general
  `RelIndex.raise`/`twist` subsumes them;
* the two `Subfield` `ratioField`s (`XH/DiamondLiftPrelude.lean:263`, `X1/DiamondAut.lean:322`)
  and the three `S`/`SField` copies (`XH/Relrank.lean:941,1017`,
  `X1/AtkinLehnerExchange.lean:698,1499`);
* `RelrankSol`'s public `isRoot_of_rel`, `coeff_sum_C_mul_X_pow`, `natDegree_sum_le`, whose
  copies the `LeRelrank` body keeps `private`;
* `coeff_jqModC_neg_one` / `coeff_jqModC_pow_of_lt`: `private` in **two** port modules
  (`Degree/PhiDegree.lean:48,53`, `ModularPolynomialStarBank.lean:88,93`) and invisible to
  `frontier.py`, so the two pin `Thm_` nodes read as ported by name while nothing public carries
  them. The body writes its own `private` copy; a proper home (`Defs/JqCoeff.lean`, wired to the
  two `Thm_` files) is a separate order and would also close those two phantom landings.
