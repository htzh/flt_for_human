# SET MC-5 — M4 + M7: the Siegel unit, and the semisimple descent of a 2-dimensional mod-`p` representation

**Status: scoped (2026-10-27); the definition gate is landed by the MC definition wave (D6, D7);
no manager lane; three worker orders.** This is the `ModularCurve` ready shelf's **MC-5**
([TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §1): story **M4** (the Siegel unit and the weight-3
Eisenstein integrality) and story **M7** (the residual realization). It follows the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md); the def wave
is [WORKORDER-MCDEF-definition-wave.md](WORKORDER-MCDEF-definition-wave.md), and MC-4
([SET-MC4.md](SET-MC4.md)) is the immediately preceding wave.

The shelf priced MC-5 at 4 rows / 1,237 silo / ≈1,055 net with a 57-line gate (`SiegelFunction` 23 +
`ResidualRealization` 34). **Both gates are landed** (D6 = `ModularCurve/Defs/SiegelFunction.lean`,
D7 = `ModularCurve/Defs/ResidualRealization.lean`, 4 declarations, `4 ok / 0 / 0`), and no promotion,
no migration and no new definition is needed: all three homes are new modules.

| figure | value |
|---|---:|
| MC-5 rows | 4 / 1,237 silo |
| net new math lines (per-row `port_advise`, before the shared prelude is counted once) | **≈1,099** |
| definition gate | **landed** (D6, D7) |
| manager lane | **none** (all homes new, no promotion, no migration) |
| worker orders | **3** (a 390+224, b 220, c 403) |

## 0. The four rows

Read from the shelf after MC-4 (2026-10-27): `needed` **998 / 397,567**, MC ready **10 / 2,782**,
`--selfcheck` **PASS**. The MC-5 block of that shelf:

| story | row (`ModularCurve.` dropped) | silo | prem | home | order |
|---|---|---|---:|---|---|
| M4 | `siegelFun_specialLinearGroup_smul` | 390 | 1 | **new** `ModularCurve/SiegelUnit/Basic.lean` | **MC-5a** |
| M4 | `SiegelUnit.differentiableOn_siegelFun` | 224 | 1 | the same new module | **MC-5a** |
| M4 | `SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion` | 220 | 3 | **new** `ModularCurve/SiegelUnit/Eisenstein.lean` | **MC-5b** |
| M7 | `exists_semisimple_descent_of_trace_det_mem_range_finite` | 403 | 3 | **new** `ModularCurve/ResidualDescent.lean` | **MC-5c** |

**The two `siegelFun` rows are one order** because they share the definition and the S_ file's
q-product prelude (`qq`/`qa`/`pref`/`sprod`/`siegelFun_eq`); 220 is independent (`EisensteinSeries`
is ported) and 403 is independent of both.

**The false ready is excluded.** `ModularCurve.rep_tateModule_jOne_comm` (24) entered the shelf
after MC-4 and is **not** cut here: its statement names the absent `TateModule`
([SET-MC4.md](SET-MC4.md) §7).

### 0.1 The premises, verified in the port

| row | premise (`Thm_` wrapper) | port module |
|---|---|---|
| 390, 224 | `jacobiTheta_two_eq_tprod` | `ModularForms/JacobiThetaTripleProduct.lean` |
| 220 | `exists_modularForm_coe_eq_eisensteinG`, `qExpansion_eisensteinG_coeff` | `ModularForms/EisensteinSeries.lean` |
| 220 | `tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral` | `ModularForms/Eisenstein/ConstTermCubeIntegral.lean` |
| 403 | `Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue` | `RepresentationTheory/SubfieldBasis.lean` |
| 403 | `Representation.span_range_eq_top_of_isIrreducible` | `RepresentationTheory/Burnside.lean` |
| 403 | `Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top` | `GaloisRep/Deformation/FiniteDescent.lean` |

The definitions the statements name are D6's (`siegelFun`) and D7's (`CyclotomicDeterminant`); 403's
hypothesis `IsResidualRealization` is D7's *vocabulary* but its statement uses
`CyclotomicDeterminant` only.

### 0.2 The pricing, per row

| order | row | raw `S_` | decl lines | boilerplate | in port | **net** |
|---|---|---:|---:|---:|---:|---:|
| MC-5a | 390 | 390 | 374 | 16 | 0 | **358** |
| MC-5a | 224 | 224 | 207 | 17 | 0 | **190** |
| MC-5b | 220 | 220 | 204 | 16 | 0 | **188** |
| MC-5c | 403 | 403 | 383 | 20 | 0 | **363** |
| | **total** | **1,237** | | | | **≈1,099** |

The two `siegelFun` rows' S_ files carry the same q-product prelude (`qq`/`qa`/`pref`/`sprod`,
≈40 lines, `0` in port by the tool's name anchor because the names are local): the order writes it
once, `private`, in `SiegelUnit/Basic.lean` — that is the shelf's "143-line jtp engine" reduced to
what the two pin files actually share.

## 1. What each row is

**390 — `siegelFun_specialLinearGroup_smul`.** For `α ∈ SL(2, ℤ)` there is a twelfth root of unity
`μ` with `siegelFun N r s (α • τ) = μ · siegelFun N (r α₀₀ + s α₁₀) (r α₀₁ + s α₁₁) τ` for all
`r s τ`. The pin's `SiegelSL2` proof: the `qq`/`qa`/`pref`/`sprod` decomposition of the Siegel unit,
the `SL(2, ℤ)`-action on the q-product (`S`/`T` generators), and the multiplier `μ` (a twelfth root
because the eta-quotient weight is 12).

**224 — `SiegelUnit.differentiableOn_siegelFun`.** `DifferentiableOn ℂ (siegelFun N r s) {0 < im} ∧
MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (siegelFun N r s)`. The pin proves it from the q-product's uniform
convergence on the upper half plane (`qParam`/`tprod`) and the chain rule through the coercion.

**220 — `SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion`.** A weight-3
`Γ₁(N)`-form `E` and an `a : ℕ` such that `N^a · coeff n` is an integer for every `n`, the constant
coefficient is non-zero, its `N^a`-multiple inverse is integral, and the same holds for the
`S`-slash's q-expansion at `N`. The proof is the Eisenstein series `E₃`/`eisensteinG` and its
integrality (`ConstTermCubeIntegral`), assembled into a `ModularForm Γ₁(N) 3`.

**403 — `exists_semisimple_descent_of_trace_det_mem_range_finite`.** A 2-dimensional `Ω`-representation
`ρ` of `Gal(L/K)` whose trace and determinant lie in a finite field `k` (and which is irreducible and
finite-image, with cyclotomic determinant) descends to a 2-dimensional `k`-representation `ρ₀` with
the same trace/determinant, a larger kernel, and a semisimple-invariant-subspace complement. The pin
assembles the three `Representation*` premises over the image of `ι : k → Ω`.

## 2. Homes

All three are **new modules**: cascade-free, disjoint, and none is on `spec/old_check_stmts.py`'s
`PORT_FILES` — so no migration is owed and the three orders run concurrently.

| order | home | above every premise? | why |
|---|---|---|---|
| a | `ModularCurve/SiegelUnit/Basic.lean` | yes — `JacobiThetaTripleProduct` is below it and the module imports it | the Siegel unit's own home; nothing is above the jtp engine |
| b | `ModularCurve/SiegelUnit/Eisenstein.lean` | yes — `EisensteinSeries` and `Eisenstein/ConstTermCubeIntegral` are below | the weight-3 integrality, independent of the unit's analytic theory |
| c | `ModularCurve/ResidualDescent.lean` | yes — the three `RepresentationTheory`/`GaloisRep` modules are below | the descent row, above all its premises; **not** named `ResidualRealization.lean`, to keep it distinct from the def module `Defs/ResidualRealization.lean` |

## 3. The three orders

| order | rows | home | silo | net | workorder |
|---|---|---|---:|---:|---|
| **MC-5a** | 390 + 224 | `ModularCurve/SiegelUnit/Basic.lean` | 614 | ≈548 | [WORKORDER-MC5a-siegel-unit.md](WORKORDER-MC5a-siegel-unit.md) |
| **MC-5b** | 220 | `ModularCurve/SiegelUnit/Eisenstein.lean` | 220 | ≈188 | [WORKORDER-MC5b-eisenstein-integrality.md](WORKORDER-MC5b-eisenstein-integrality.md) |
| **MC-5c** | 403 | `ModularCurve/ResidualDescent.lean` | 403 | ≈363 | [WORKORDER-MC5c-semisimple-descent.md](WORKORDER-MC5c-semisimple-descent.md) |

## 4. Traps, per order

**MC-5a.** (i) The pin's prelude is `qq`/`qa`/`pref`/`sprod` plus `siegelFun_eq`; it is the shared
engine of both rows and is `private` (the wire has statements only for the two headlines).
(ii) 390's multiplier `μ` is `∏` over the `S`/`T` decomposition of `α`; the pin's proof of
`μ ^ 12 = 1` is the eta-quotient weight count — do not replace it with a weaker `μ ≠ 0` statement.
(iii) 224's `MDifferentiable` needs `open scoped Manifold` and the `𝓘(ℂ)` model; the pin opens it at
file top. (iv) The `∏'` (tprod) convergence lemmas are mathlib's `tprod` API; the port has no
`qParam`/`tprod` wrapper of its own — use mathlib directly. (v) Do not transcribe the pin's
`p2m_export`/`p2m_open` or the `P2MW.S_` namespace.

**MC-5b.** (i) The statement is the pin's five-clause existential; transcribe it verbatim
(`N^a * coeff n` integral, `coeff 0 ≠ 0`, the inverse integral, and the `S`-slash at `N`).
(ii) `eisensteinG` and its two lemmas are ported; the integrality engine
(`tsum_inv_cube_congr_one_ne_zero_and_exists_isIntegral`) is a *premise*, not to be re-proved.
(iii) `IsIntegral ℤ ((N : ℂ)^a * …)` is `IsIntegral` over `ℤ` in `ℂ` — the coercion shape matters.

**MC-5c.** (i) The statement is long: transcribe the whole existential (`V₀`, its instances,
`ρ₀`, the four conjuncts). (ii) The hypothesis `hcyc : CyclotomicDeterminant M p ρ` is D7's def in
`ModularCurve/Defs/ResidualRealization.lean` — import that module. (iii) `hV : Module.finrank Ω V =
2` and `hirr`/`htr`/`hdet` are used by the three premises; keep the pin's order of assembly.
(iv) `hp : (p : Ω) = 0` is the characteristic-`p` hypothesis; do not turn it into `[CharP Ω p]`.

## 5. Gates, per order

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; every public
   declaration `ok`; private engine exempt and private. No `spec/decl_markers.tsv` row from a worker.
2. `#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake build` under `flock` (background channel on a busy tree, FR-0060); silent
   at the project cap; **no** `set_option maxHeartbeats`/`synthInstance.maxHeartbeats` and no linter
   suppression added.
4. `dedup.py --within --tier shape` → 0 clusters (or the pin's own wrapper-over-engine shape,
   recorded).
5. The module's `spec-pin:` block names exactly its own `Thm_` wrapper and `S_` copy (two lines per
   headline; MC-5a has two headlines, so four).
6. No `sorry`/`admit`/`axiom`/`native_decide`; no git; no whole-tree build; every command under the
   2-minute cap.

**The consumer zone for the set** (`spec/ModularCurveMC5Consumer.lean`, manager-written): 390's
multiplier applied at `α = S` and `α = T` composed with `siegelFun_def`; 224's pair consumed as a
`DifferentiableOn`/`MDifferentiable` bundle and fed to `ContDiffOn`/`DifferentiableAt` machinery;
220's existential unpacked into its four clauses and its `coeff 0` fed to `IsIntegral`;
403's `ρ₀` compared with `ρ` through the trace/determinant conjuncts.

## 6. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc5.json
for row in siegelFun_specialLinearGroup_smul SiegelUnit.differentiableOn_siegelFun \
  SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion \
  exists_semisimple_descent_of_trace_det_mem_range_finite; do
  python3 port_advise.py --nodes ModularCurve.$row --json build/mc5-$row.json
  python3 port_plan.py --json build/mc5-$row.json
done
cd ../lean
python3 spec/gate_scan.py --pin Definitions/Def_ModularCurve_SiegelFunction.lean \
  --rows S_ModularCurve_siegelFun_specialLinearGroup_smul S_ModularCurve_SiegelUnit_differentiableOn_siegelFun
```

## 7. What this set does not do

- **`ModularCurve.rep_tateModule_jOne_comm` (24)** — the false ready: its statement names
  `TateModule` (absent). It belongs to the Tate-module programme, not to M7's descent.
- **The leaves block (32 / 6,797)**, including the Siegel leaves (`mem_span_levelBernoulliWeight…`
  504, `sum_totient_mul_levelBernoulliWeight…` 323, `siegelFun_add_level` 155, `sum_levelBernoulliWeight_add_mul`
  176): they become readable once the Siegel unit's analytic engine lands here, and are the natural
  next cuts of the M4 story.
- **No promotion, no migration, no tree build.**

## 7. The landing — measured (2026-10-27, all four rows in)

| figure | before | after | delta |
|---|---:|---:|---:|
| instrument `needed` | 998 / 397,567 | **992 / 395,624** | −6 / −1,943 (MC-5 + MC-6 together) |
| frontier F | 1,415 / 729,584 | **1,421 / 731,527** | +6 / +1,943 |
| `--selfcheck` | PASS | **PASS** | — |

The two waves are read together (they ran together): the six rows of MC-5 + MC-6 are
`390 + 224 + 220 + 403 + 322 + 384 = 1,943` silo, and the instrument moved by exactly that. The
set's own verdicts: **6 checked declarations `ok`, 0 mismatch, 0 missing, 0 own** over the five new
modules (`SiegelUnit/Basic.lean` 2, `SiegelUnit/Eisenstein.lean` 1, `ResidualDescent.lean` 1,
`XH/FrickeSlash.lean` 1, `XH/QExpandNorm.lean` 1); axioms `[propext, Classical.choice, Quot.sound]`
on all six headlines; every module silent with no `set_option` beyond `autoImplicit false`; 0 new
`dedup --tier shape` clusters except the recorded pin-inherited one (MC-5c's `main` ↔ headline, the
same shape as `RepresentationTheory/SubfieldBasis.lean`); consumer zone
`spec/ModularCurveMC5Consumer.lean`, **0 errors**.

The modules: `SiegelUnit/Basic.lean` 509 lines (48 private engine declarations — the pin's two `S_`
files' identical prelude written once, unified under `ModularCurve.SiegelUnitEngine`),
`SiegelUnit/Eisenstein.lean` 286 (9 private), `ResidualDescent.lean` 544 (7 private + the
`P2mWs11Glue.main` 256-line engine), `XH/FrickeSlash.lean` 424 (31 private + 3 new `mapGL`
adapters), `XH/QExpandNorm.lean` 355 (34 private). No new module was needed beyond the five, no
promotion, no migration, no `spec/decl_markers.tsv` row.

**One substitution to record (MC-6b).** The pin's `TestElement` block (S_ 26–152, ≈127 lines: the
`E₄`/`E₆`/`xq` construction with `-1728` and `decide +kernel` Bernoulli computations) is **not**
transcribed: its only role is to supply the separating element for `emb_injective`, and the port
already has `jq` with `coeff_jq_one = 196884 ≠ 0` plus `ℓ ∤ 1` killing the stretch. Three lemmas
replace the block; the statement is untouched. The rest of the proof skeleton is the pin's. (This is
the "we do not duplicate mathematics" rule applied to a *route*, not only to a lemma — the same
decision MC-7's §3 recorded for the `resRange` block.)

**What the next pass reads.** The MC ready shelf is now **5 / 2,015**: the M9 successor
`exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul` (**1,176** — it became ready with
MC-6's Fricke material and is the largest row the block has ever carried), the three first-wave
successors (611, 168, 36) and the false ready (24, `TateModule`). MC-7 is landed, the seven orders
of the ready block are closed, and the next move is the leaves programme or the 1,176 M9 successor.
