# The Hecke-compositum degree — ground, one body, two headlines

Record for the set in
[../topics/modularCurve/TOPIC-hecke-compositum.md](../topics/modularCurve/TOPIC-hecke-compositum.md),
ordered by [../topics/modularCurve/WORKORDER-RI2-hecke-compositum.md](../topics/modularCurve/WORKORDER-RI2-hecke-compositum.md).
Pin `aa2d8b3`.

The set is the **consumer of the `RelIndex` pair** (`logs/relindex-relrank.md`): `main_C` calls both
of that set's headlines. It is also the column's largest dedup so far — the two pin nodes
(994 + 884 lines) are one theorem, so the set lands **one body and one corollary**.

## 1. The finding

`CohCarrier.GammaH M H` is `{γ ∈ Γ₀(M) : γ₁₁ ∈ H}`, so at the trivial subgroup it is `Γ₁(M)`, and
the port has it: `CohCarrier.GammaH_bot : CohCarrier.GammaH M ⊥ = Gamma1 M`
(`ModularForms/Defs/GammaH.lean:137`, public, from the `Γ_H` definition layer). The three function
fields are `qExpFunctionFieldC K _` of those subgroups, so they collapse by `rfl`:
`xHFunctionFieldC K M ⊥ = x1FunctionFieldC K M`, `xHTopFunctionFieldC K M ⊥ t = x1x0FunctionFieldC K M t`.

Probe-verified (`tmp/probe/x1_from_xh.lean`) before dispatch, against the `xH` statement as a
hypothesis: the whole `x1` headline follows by

```lean
have h := hXH L M ⊥ ℓ ℓ' hℓ
simpa only [CohCarrier.GammaH_bot, xHFunctionFieldC, x1FunctionFieldC, xHTopFunctionFieldC,
  x1x0FunctionFieldC, xHFunctionField, x1FunctionField] using h
```

**So the `x1` pin file (884 lines) is not ported.** It is a reading cross-check: everywhere the two
files differ, the difference is the group. `shapes.py` had already said so — all 61 theorem/lemmas
of the `x1` file have a same-shape twin in the `xH` file — and the section-by-section line counts
are equal everywhere but `Groups` (239 vs 351, the `Γ_H` block being the superset).

This supersedes the set's original plan (a generic engine over an abstract subgroup plus two
façades): with the corollary, an abstract-group engine has one consumer and would be
over-engineering, so the single body takes the pin's own `Γ_H` development whole and stays private.

## 2. The ground: four legacy modules, edited in place and handed over

Per the user's direction, the ground went **into** the modules that own the subjects — not into new
modules beside them — and each was moved off the frozen registry onto its own `spec-pin:` wire
(`PORT_FILES` entry out, replaced by a comment recording where it went):

| module | gained | checker (after) |
|---|---|---|
| `ModularCurve/Defs/Laurent.lean` | `qExpAlg`, `qExpAlg_apply`, `coe_qExpAlg`, `adjoin_qExpand_image`, `charZero_of_algebraRat`, `coeffEmb_apply`, `powerSeries_map_map` | **45 ok / 0 mismatch / 0 missing / 0 own / 0 kw** |
| `ModularCurve/JqIntegralRatios.lean` | `map_ofPowerSeries`, `coeffEmb_intSeriesC`, `intSeriesC_eq_zero_iff`, `coeffEmb_image_intFormRatiosC` | **27 / 0 / 0 / 0 / 0** |
| `ModularCurve/Degree/LaurentGlue.lean` | `laurentBaseChange_map`, `laurentBaseChange_sup`, `laurentBaseChange_qExpFunctionFieldC` | **11 / 0 / 0 / 0 / 0** |
| `ModularCurve/Degree/Relfinrank.lean` | `RelFinrankKit`: `finite_extendScalars_of_relfinrank_ne_zero`, `relfinrank_sup_le`, `isIntegral_and_natDegree_minpoly_le`, `finrank_adjoin_simple_le_of_le`, `relrank_adjoin_insert_eq`, `isIntegral_and_finrank_adjoin_le_relfinrank`, `relfinrank_le_of_relrank_le`, `relfinrank_adjoin_simple_eq_finrank`, `transcendental_map`, `transcendental_coe`; and `relfinrank_laurentBaseChange_eq` | **14 / 0 / 0 / 0 / 0** |

The import graph forced the split (a `Defs/Laurent` lemma cannot use `intSeriesC`, which lives
above it), and the split coincides with the subjects: ring maps in `Laurent`, the
`intSeriesC`/`intFormRatiosC` half in `JqIntegralRatios`, the `laurentBaseChange` transport in
`LaurentGlue` (which owns `laurentBaseChange_adjoin`), the relative-degree toolkit in `Relfinrank`
(which owns `relfinrank_laurentBaseChange`).

Of the ten toolkit lemmas, two are mathlib's (`relfinrank_mul_relfinrank`,
`relfinrank_map_map`). The important new one is `relrank_adjoin_insert_eq`: it converts the
`relrank (adjoin F S) (adjoin F (insert x S))` shape that
`ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC` concludes in into a
`Module.finrank` — which is what makes the two bounds of the previous set composable.

**Whole wired surface after the handoffs:** 3,904 ok, 0 mismatch, 0 missing, 11 own, 0 kw over
**154 modules**, **577** `PORT_FILES` exempt (`spec/check_port.py --all`, every module re-checked,
0 cached). Was 3,830 / 151 / 580; the +74 is 45 + 14 + 11 (the three newly wired modules) plus the 4
declarations `JqIntegralRatios` gained.

One build incident: the killed dependent wave of the previous session had left `WeightOne/*` and
`FunctionFieldGeneration/*` oleans missing, so `JqIntegralRatios` could not be rebuilt and
`LaurentGlue` could not import it. The fix was a single-module `lake build` of `JqIntegralRatios`
(4,123 jobs, ~4 min in the background) — not a wave build, which the round's standing rule forbids
and which is not evidence anyway (`../topics/TOPIC-dedup-refactoring.md` §4).

## 3. The body

**One module, two headlines** — `FLTForHuman/ModularCurve/HeckeCompositum.lean`, 840 lines,
47 declarations: `relfinrank_xHHeckeCompositum_eq_mul` (the 994-pin-line development) and
`relfinrank_x1HeckeCompositum_eq_mul` (the six-line `H := ⊥` corollary of §1), engine `private` in
`namespace XHHeckeSol`.

The engine is the pin's `XHLDGroups` remainder + the `FF` layer over `RelIndex.ratioSet` +
`Fields` + `OverC` (`main_C`) + `BaseChange` (`main_L`). It calls the previous set's two headlines
directly (`relIndex_gamma0_le_relrank_adjoin_insert_jqNModC` at `GA` and
`relrank_adjoin_qExpansion_div_le_relIndex` at `Γ₁`/`GB`), the ground's `RelFinrankKit`,
`laurentBaseChange_map`/`_sup`/`_qExpFunctionFieldC`, `qExpAlg`, `adjoin_qExpand_image` and
`relfinrank_laurentBaseChange_eq`, and the port's `DiamondLift.XH.cocycle` for the pin's
`conj_hyp_GammaH`.

**Two placements were tried and rejected before this one**, and the rejection is the lesson:
a `X1/HeckeCompositum.lean` holding the corollary and nothing else (a whole module for six lines —
the user's ruling: *no module for a façade; things go wherever they belong*), and the corollary in
`X1/FunctionFieldDegree.lean`, its subject home, which forces this module's import into an X₁ degree
module — and that edge is not free: it re-points `coeffEmb_intSeriesC` (now published at
`ModularCurve` scope by the `Defs/Laurent`/`JqIntegralRatios` ground) inside an unrelated proof
there and breaks a `simp only`. A derived statement belongs with the development it derives from;
one module for the whole subject, named for the subject.

## 4. Gates

| gate | reading |
|---|---|
| `spec/check_port.py --all` (whole wired surface, every module re-checked, 0 cached) | **3,906 ok, 0 mismatch, 0 missing, 11 own, 0 kw — 155 modules, 577 `PORT_FILES` exempt** (was 3,830 / 151 / 580 before this set) |
| `--force` on `ModularCurve/HeckeCompositum.lean` | **2 ok, 0 mismatch, 0 missing, 0 own, 0 kw** — both headlines matched to their own `Thm_` wrappers |
| `--force` on the four handed-over modules | `Defs/Laurent` **45**, `JqIntegralRatios` **27**, `Degree/LaurentGlue` **11**, `Degree/Relfinrank` **14** — all 0 / 0 / 0 / 0 |
| `lake env lean` | silent, 0 warnings, on the module and on all four ground modules |
| `lake build` (single module, no wave) | `ModularCurve.HeckeCompositum` 4,317 jobs / 7.7 s; the ground modules 3.4–5.3 s each |
| axioms, both headlines | `[propext, Classical.choice, Quot.sound]` |
| forbidden-token sweep | no `sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats` |
| `spec/unwired_register.py --check` | current |
| shapes receipt | 40 theorem/lemmas; 40 have a same-shape twin in the pin (it is a transcription); **2 have a same-shape twin in another port module** — `T_mem_Gamma1` and `T_zpow_mem_Gamma1`, the pin's own three-line local copies of facts the port publishes in three and two places. Recorded, not opened. |

No wave build was run at any point (the round's standing rule).

## 5. Residue

* the pin's `X1LDGroups` block (239 lines) is a sub-block of `XHLDGroups` (351); the body
  transcribes the `Γ_H` version and the `Γ₁` lemmas it needs, so ~239 pin lines are written twice
  — but **once in the port**, since the `x1` file is not ported at all;
* `charZero_of_algebraRat` and `powerSeries_map_map` also exist `private` in
  `X1/FunctionFieldBaseChange.lean` and `ModularForms/WeightOne/Gamma0Integral.lean`; they are now
  public in `Defs/Laurent`, so those private copies can go when their modules are next opened;
* `coeffEmb_intSeriesC` likewise exists public in `X1/FunctionFieldResidue.lean`
  (`ModularCurve.QExpDeuring`) — the `JqIntegralRatios` copy is the wired one;
* `ModularCurve.RelFinrankKit` is the natural home for a future "relative-degree toolkit" order:
  `Degree/Relfinrank.lean` is a heavy module to import for ten generic lemmas, and
  `FieldTheory/` would be the mathlib-mirroring home if a second consumer appears.
