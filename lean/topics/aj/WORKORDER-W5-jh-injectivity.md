# WORKORDER W5 — the ℚ̄ → ℂ descent (the jH injectivity premise)

Execution order for [PLAN-W5-jh-injectivity.md](PLAN-W5-jh-injectivity.md), whose §1–§6 are the
specification: this file fixes ownership, the pin references, the order, and the discipline. Pin
`anthropics/fermats-last-theorem@aa2d8b34`, local clone `/home/haitao/proj/fermats-last-theorem`; port
mathlib `v4.34.0` (the port's `.lake` mathlib). Parent
[../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md) §1, §9.2, §12.1 chain 3.

Measured with `frontier`/`port_advise`/`port_plan`: the eighteen nodes are 6,256 raw `S_` lines, 5,837
declaration lines, −693 duplicate copies, −123 already in the port ⇒ **5,021 net new math lines**; plus
the 62-line `Def_*` module below. **No sibling pair** (no `X_of_Y`-vs-`X` derivation to take), and the
tools find **no substitution for any of the eighteen headline statements** — the 123 in-port lines are
helpers.

**Roles.** The manager owns the `Definitions/Def_*` layer (§5), every homing decision, the `spec-pin:`
wiring and `PORT_FILES` deletions, `dedup.py`/`move_dead.py`, the axioms probe and the re-measurement.
An implementer owns the **statement transcription, the proof body, the single-module build and the
blocker report** — and leaves wiring and cleanup to the manager. "This module cannot host that
declaration" is a homing finding to report, not a licence to move it.

## 1. What this wave owns — 18 nodes

Group letters are checkpoints. "lines" is the pin's raw `S_` file (what `frontier` prices); homes are
fixed, do not rename. Each node is public at the pin's name; its two `spec-pin:` sources are
`Theorems/Thm_<stem>.lean` and `P2M/Sol/S_<stem>.lean` with `<stem>` = the node's name with `.` → `_`
(the manager writes the wire; the implementer quotes the statement from those files).

| group | node | lines | home |
|---|---|---:|---|
| P1 | `AlgebraicCurve.Place.exists_of_valuationSubring` | 207 | `AlgebraicCurve/Place/FromValuationSubring.lean` (new) |
| P1 | `AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom` | 207 | same |
| P2 | `AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension` | 615 | `AlgebraicCurve/Place/ConstantFieldExtension.lean` (new) |
| P2 | `AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed` | 401 | same |
| P2 | `AlgebraicCurve.Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension` | 429 | same |
| P2 | `AlgebraicCurve.Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension` | 205 | same |
| P2 | `AlgebraicCurve.Place.exists_ord_neg_of_transcendental` | 80 | same |
| P2 | `AlgebraicCurve.Place.deg_eq_one_iff_surjective_algebraMap_residueField` | 28 | same |
| P2 | `AlgebraicCurve.Place.sum_ramificationIndex_eq_finrank` | 17 | same |
| P2 | `AlgebraicCurve.Place.inertiaDeg_eq_one_of_isRational` | 13 | same |
| P3 | `AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental` | 21 | append to `AlgebraicCurve/IsCurveOver/Transcendental.lean` |
| P3 | `AlgebraicCurve.mem_span_range_algebraMap_of_constantFieldExtension` | 859 | `AlgebraicCurve/IsCurveOver/ConstantFieldExtensionSpan.lean` (new — the legacy module is below `Place/ConstantFieldExtension.lean`, so appending is an import cycle) |
| P4 | `AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem` | 994 | `AlgebraicCurve/Differential/ConstantFieldExtension.lean` (new) |
| P5 | `AlgebraicCurve.Divisor.isPrincipal_of_constantFieldExtension` | 402 | `AlgebraicCurve/Genus/ConstantFieldExtension.lean` (new) |
| P5 | `AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension` | 878 | same |
| P0 | `Def_GaloisRep_ComplexConjugation` (62) | — | `GaloisRep/Defs/ComplexConjugation.lean` (new) |
| P6 | `ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex` | 670 | `ModularCurve/XH/JHDescent.lean` (new) |

The layer-0 roots `Place.exists_ord_algebraMap_eq_mul_ord` (137) and
`Place.exists_comap_eq_toValuationSubring` (93) are **nodes in their own right**: each has its own
`S_`/`Theorems/` pair and each is public at the pin's name, over the private engine the two P2 files
share (`Place.rowMain` in both pin files, disambiguated in the port). Port the engine once as the P2
module's private block and state the two headlines over it.

## 2. Order — the pin's own dependency layers

`port_plan --section layers` on the slice gives the order; it is strict:

```
P1  exists_of_valuationSubring (207), exists_toValuationSubring_eq_comap_ringHom (207)   → green
P2  comap lift (615), mem_range…of_isAlgClosed (401), exists_ord_neg (80),
    sum_ramificationIndex (17), inertiaDeg_eq_one_of_isRational (13),
    deg_eq_one_iff… (28), eq_of_forall_valuation_sub_lt_one (429),
    existsUnique_valuation_sub_lt_one (205)                                              → green
P3  isCurveOver_of_isAlgClosed (21) [append to Transcendental], mem_span_range (859) [new]  → green
P4  exists_derivation…map_mem (994)                                                      → green
P5  isPrincipal (402), exists_torsion_descent (878)                                      → green
P6  the jH headline (670)                                                                → green
```

Within P2 the pin's `solution`s are mostly one-line applications of private engines in the same file
(`Place.mem_range_algebraMap_of_forall_ord_eq_zero_core`, `Place.rowMain` for two of them); write the
engine, then the headline. One implementer, not two: the body is 5k and every layer is the next layer's
premise.

Report at **P1, P3, P6** and immediately on a blocker (§7). The manager does not poll.

### 2b. Write these once — `port_plan`'s factoring units

Shared by an identical set of files; write each block once in the home named, never per consumer.

| group | once / in-port | block | home |
|---|---|---|---|
| P1 | 119 / 0 | `idealOfA_ne_bot` 23, `exists_place_of_mem` 19, `place_of_idealOfA_le` 16, `integralClosure_Kx_le_A` 14, `inv_mem_of_notMem_maximalIdeal` 14, `isDedekindDomain_Kx` 12, `Kx_le_A` 8, `isDedekindDomain_integralClosure` 7, `isFractionRing_integralClosure` 6 | P1 |
| P2 | 116 / 0 | `exists_centred` 83, `mulMap_injective` 19, `mulMap` 5, `evalMap` 4, `mulMap_tmul` 3, `evalMap_tmul` 2 | P2 |
| P2 | 100 / 0 | `mem_of_ord_nonneg` 62, `exists_sub_algebraMap_mem_maximalIdeal` 22, `isUnit_add_of_mem_maximalIdeal` 9, `mem_maximalIdeal_of_ord_pos` 7 | P2 |
| P2 | 72 / 0 | `mem_iff_ord_nonneg` 55, `one_le_ord_of_mem_of_inv_not_mem` 17 | P2 |
| P3 | 165 / 0 | `exists_basis` 127, `linearIndependent_pow_of_transcendental` 26, `aeval_mem` 12 | P3 |
| P4 | 192 / 0 | `ord_sum_le` 128, `exists_linearIndependent_repr` 41, `ord_pos_of_mem_maximalIdeal` 13, `isUnit_of_ord_eq_zero` 10 | P4, imported by P5 |

The 119- and 116-line blocks are *identical private preludes* in two pin files each; porting them once
is the wave's saving. The 192 is cited by P5, so it is **public** in P4.

## 3. Already landed — import, do not re-prove

* **The place/ord vocabulary** (the 9 vetted substitutions, ≈123 lines): `Place.ord_nonneg_of_mem_vs`
  (`AlgebraicCurve/Canonical/WeilDifferential.lean`), `Place.mem_toValuationSubring_of_ord_nonneg_alt`
  (`Defs/PlaceEvaluationAlgebra.lean`), `TraceDifferentBound.mem_iff_ord_nonneg'`
  (`Differential/CorrespondenceRegular.lean`), `Place.ord_algebraMap_base` (`P1/EnginePrelude.lean`),
  `Place.ord_algebraMap_base`'s file also has `Place.mem_iff_ord_nonneg` (check its binders),
  `ModularCurve.coeffMap_qExpand` (`ModularCurve/Defs/Laurent.lean`),
  `Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq` (`Algebra/IsSeparableFrobenius.lean`).
* **Shape-equivalent, read first, then decide** (§5 D4): `ConstantFieldExtension.transcendental_algebraMap`
  (`AlgebraicCurve/IsCurveOver/ConstantFieldExtension.lean` — its form looks *stronger*; the pin's
  `[IsAlgClosed K] [CharZero K]` + existential form should be a short application),
  `constantsAreBase_of_isAlgClosed` (`ResidueTheorem/RRAssembly.lean`),
  `linearIndependent_pow_iff_transcendental` (`RegularProlongationFinrank.lean`), `ord_natCast`
  (`Differential/Hurwitz.lean`), `mk_eq_zero_iff` (`WeilExchange/Transport.lean`), and the three
  `degree_eq_sum` pointers (`WeierstrassCurve/GenusOnePlaceGate.lean`).
* **The RR block the descent consumes** (landed in W1–W4): `functionFieldRiemannRoch…`,
  `finiteDimensional_lSpace`, `lSpace_eq_bot_of_degree_neg`,
  `RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase` — `exists_torsion_descent`
  cites them; import.
* **The `IsCurveOver` constructor**: `AlgebraicCurve.isCurveOver_of_transcendental` (and its
  `_of_isSeparable` alias) in `IsCurveOver/Transcendental.lean` — P3's 21-line
  `_of_isAlgClosed` node is its `[IsAlgClosed K]` specialization.
* **The XH glue imported by P6**: `ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange`
  (`X1/FunctionFieldBaseChange.lean`), `linearIndependent_of_constantFieldExtension`
  (`IsCurveOver/ConstantFieldExtension.lean`), `ModularCurve.coeffMap` and `ModularCurve.FQ`/`FC`-level
  API as far as it exists in `XH/FunctionField.lean` / `ModularCurve/Defs/Laurent.lean`.
* **Mathlib**: `UpperHalfPlane.J`/`I` (the 302's conjugation lemmas are mathlib exercises), and
  `IsAlgClosed.lift`, `AlgEquiv.restrictNormalHom`, `starRingAut` for P0.

## 4. Decisions the implementer must not re-litigate

1. **Statements verbatim** from the pin's `Theorems/` wrapper (or the `S_` `theorem solution` where the
   wrapper only restates), with the pin's qualified spellings kept even inside a namespace.
2. **The pin's `solution := engine.main` shape is kept**: one public headline per node, the engine as
   the same file's private block; a block shared across files goes to its §2b home and is public there.
3. **Drop the global attribute walls** (`[-instance]`/`[-simp]`); keep the pin's `attribute [local
   instance]` registrations (they are the `letI`-wall in another spelling). Prefer a local
   `include`/`omit` or an explicit instance argument, and record which lemma needed which. Never
   reinstate a global attribute.
4. **Shape-tier substitutions are read, not imported** (see §3).
5. **No `--ds`, no prune**: the price is the plain reading.

## 5. P0 — done by the manager (do not redo)

`FLTForHuman/GaloisRep/Defs/ComplexConjugation.lean` is written (the pin's 62-line
`Def_GaloisRep_ComplexConjugation`: `complexEmbedding`, `complexConjAlgEquiv`, `complexConjugation`,
the `ExtCitation` archimedean block). It is a `Def_*` module, so it carries no `spec-pin:` statement
wire. P6's statement is written against `complexEmbedding`; if the build is not yet green when P6
starts, report it, do not redefine it.

## 6. Build discipline

* One module at a time: `timeout 110 lake build <Module>`, log in `lean/tmp/w5-<group>.log`, tail it.
  No tree build, ever.
* If a build legitimately needs longer, run it as a background job (the tool returns a job id and the
  command keeps going), then read the job's output — **do not** loop `lake build` to step around the
  2-minute bound, and do not start a second build while one is running.
* Zero warnings from your module: fix or `omit` them; no `set_option linter… false` blanket (a local one
  already present in the pin's file may be kept, as in W4's `haveILetI`).
* No `sorry`, `axiom`, `native_decide`.
* The implementer does **not** edit `spec/`, does not wire `spec-pin:`, does not run `dedup.py`; those
  are the manager's and happen between checkpoints.

## 7. Blocker protocol

Report to the manager, in one short message: module, node, pin file and line of the statement, the
failing goal or the unprovable step, what was tried, and whether the cause is a missing ported premise
(which one), a homing problem (which module should own it), or an instance wall. Then stop on that node
— do not re-plan the wave and do not move a declaration to make it compile.
