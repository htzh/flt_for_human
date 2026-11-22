# SET-AF102 — the torsion basis at `j = 0`/`j = 1728`, faithful inertia at 2 and 3, and the `jq`-integrality chain

**Status: LANDED (2026-11-23).** The next set of the AF column in the D–S cone, scoped per
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. **Five orders, eleven rows, 5,846 silo**, **five new modules and one
one-declaration insertion**; it landed **5,699 lines** (ratio 0.97 to silo) and moved
`needed [F terminal]` by exactly its cut (350/187,490 → 339/181,644) while making **four new rows
ready** (2,892 silo). It takes the whole of the ready shelf's `WeierstrassCurve` and
`ModularCurve` `jq` blocks, which are SET-AF101's and SET-AF100's priced follow-ons: SET-AF101 §8
records that W1's two 816/713 consumers *became* ready when its stabilizer order landed, and W2's 572
when the Deuring form landed; SET-AF100 §0 names the `ModularCurve` rows below as the half of the
shelf it deliberately left.

The subject is two stories, both continuations:

* **the elliptic automorphism group, acted out on torsion** — the regular action of the order-3 and
  order-4 automorphism on an `M`-torsion basis (`E[M]` free of rank one over `ℤ[X]/(M, X²+X+1)` resp.
  `ℤ[i]/M`), the char-two orbit count read by double cosets, and the good model whose inertia acts
  faithfully on the 2- resp. 3-torsion (Legendre route resp. Deuring route). W1's *order* and W2's
  *normal form* were SET-AF101; this is the structure they were for.
* **the `jq`-integrality chain** — `IsIntegral` of `Y^{2M}·jq^{M+1}·(jq-1728)^M` over `ℂ[jq⁻¹]`, of
  the `q`-expansion ratio `qExp g / qExp h` over `ℂ[jqModC]`, of `Y^6·jq^4·(jq-1728)^3` over
  `ℂ[jq]`, and the thetaL/`qExpFunctionFieldC` glue that feeds them.

**No definition-layer work.** Every `Definitions/Def_*` module the five pins import is ported under a
module this set can import: `ModularCurve/{Defs/{Laurent,JqCoeff,HeckeDifferential,X0,X1,
QExpansionDiff},Period/{QExpansionDerivative,QExpansionDiff}}`, `ModularForms/{QCoeffLevelOne,
IsArithmeticQExpansion,Defs/GammaH}`, `Elliptic/{TorsionZMod,PointArithmetic}`,
`WeierstrassCurve/{Velu/VariableChangePoint,Automorphism/{Basic,CharTwo,CharThree,DeuringForm,
NormalForm}}`, `AlgebraicCurve/Defs/RegularDifferentials.lean` and `AlgebraicCurve/Differential/*` (the `diffQExp`
layer's push-pull premises). The gate check is FR-0298's, i.e. the `S_` file's
`import Definitions.…` lines, not the wrapper's: done for all twelve rows, all clean.

| # | order | rows | silo | net | modules |
|---|---|---|---:|---:|---|
| A1 | the torsion basis at the two exceptional `j`-invariants | 2 | 1,529 | 1,375 | `WeierstrassCurve/Automorphism/TorsionBasis.lean` (new) |
| A2 | the char-two torsion orbit and its double-coset count | 1 | 697 | 675 | `ModularCurve/LevelN/TorsionOrbit.lean` (new) |
| A3 | a good model with faithful inertia at 2 and at 3 | 2 | 1,171 | 1,127 | `WeierstrassCurve/Reduction/InertiaFaithful.lean` (new) |
| M1 | `Y^(2M)·jq^(M+1)·(jq-1728)^M` is integral over `ℂ[jq⁻¹]` | 3 | 1,333 | 1,084 | `ModularCurve/Analytic/JqInverseIntegral.lean` (new) |
| M2 | `qExp g / qExp h` is integral over `ℂ[jqModC]`, and one `X1` glue row | 3 | 1,116 | 752 | `ModularCurve/Analytic/JqModCIntegral.lean` (new) + 1 insertion |
| **total** | | **11** | **5,846** | **≈4,864** | 5 new + 1 insertion |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af102_read.json
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --selfcheck
```

| figure | raw read | corrected read |
|---|---:|---:|
| `needed [F terminal]` | 349 / 187,415 | **350 / 187,490** |
| ready rows | 31 / 12,398 | **32 / 12,473** |
| leaves | 23 / 15,967 | 23 / 15,967 |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |
| avoided (`--ds` prunable set R) | 140 / 74,620 | 140 / 74,620 |

The raw read reproduces SET-AF101 §8's landing read exactly, so nothing has landed since.

**The corrected read is the one this brief quotes, and it is one command.** `--selfcheck` FAILs with
**21** `source node not covered by the name scan` rows (MD-005's phi-refactor block and MD-007's
deliberate re-spelling), so those nodes are false ported markers; the corrected read passes every one
of them to `--unport`. It moves the figure by **+1 node / +75 lines** and adds exactly one ready row,
`ModularCurve.ModularPolynomialData.eq_all` (75) — the only one of the 21 that is inside the D–S
demand at all. That row is **named and deferred** (§7): it is the phi-refactor family's metadata
story (MD-005), not this set's subject, and a row that only exists on the shelf because a wire claims
mathematics the port does not declare is a metadata job (the module's next edit), not a porting job.

`TateCurve.point_mul_eq_add_of_norm_{le,eq}_one` (471, 247) are still on the leaves shelf, as
SET-AF101 §8 predicts: they are the deferred definition-layer set (CARRY-FORWARD), not cut here.

## 1. The stories

### A1 — `E[M]` free of rank one over `ℤ[X]/(M, X²+X+1)` resp. `ℤ[i]/(M)`

`exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three` (816) and
`…_of_order_four` (713) say: over any algebraically closed field, there is a curve of `j = 0`
(resp. `j = 1728`) — an elliptic one, admissible — an admissible `σ` fixing it, an `M`-torsion basis
`(P, Q)`, and `σ` acts on it as the matrix `[[0,1],[-1,-1]]` (resp. `σ P = Q`, `σ Q = -P`) through
`Point.vcInvFun`. That is Deligne–Serre's "regular module" input for the fibre of `X` above `j = 0`
and `j = 1728`.

Both pins are three-case splits (`2 = 0`, `3 = 0`, generic), each case re-deriving its own curve model
(`E2`, `E3`, `E₀`) and calling the already-ported exceptional automorphism engines
(`Automorphism/{CharTwo,CharThree}.lean`, `DeuringForm.lean`'s
`variableChange_mk_smul_eq_self_of_{pow_three,sq_eq_neg_one}`). The point-transport prelude
(`xy`, `castPt`, `vcHom` family, 95 ported lines) is **already public** in
`Automorphism/Basic.lean`: import it, do not redeclare it. The pair also shares
`exists_common_scalar` and `eq_or_eq_neg_of_xco_eq` (110 lines, 12 proofs) — write once.

### A2 — the char-two orbit count

`natCard_torsionOrbit_and_exists_surjective_doubleCoset_of_char_two` (697) is stated on the literal
curve `⟨0, 0, 1, 0, 0⟩` over a char-two algebraically closed field: the number of `M`-torsion orbits
`{u·P : u ∈ H ⊔ ⟨-1⟩}` is the index of `GammaH M H ⊔ ⟨-1⟩`, and there is a map from those orbits onto
the double-coset quotient along `⟨ST⟩` (resp. `⟨S⟩`), surjective and injective exactly on the
`σᵏ`-translate relation (`σ = ⟨w,0,0,0⟩` resp. `⟨1,1,1,w⟩`). It is a **fibre of `X₁`** statement
stated on the curve, so its home is `ModularCurve/LevelN/` (whose `GenusFF.lean` already carries the
private `ST_pow_three`/`S_pow_two` twins of its first engine) — not `WeierstrassCurve/`: the
statement mentions `CohCarrier.GammaH` and `DoubleCoset.Quotient`, which live in `ModularForms`/
`Mathlib`, above the `WeierstrassCurve` layer (SET-AF101 §2's W4 lesson: home by the statement's
layer, then pay).

### A3 — faithful inertia, Legendre and Deuring

`exists_isGalois_goodModel_inertia_faithful_of_two_ne_zero` (599) and `…_of_three_ne_zero` (572):
over `F → Ω` with `Ω` algebraically closed and algebraic over `F`, there is a finite Galois
`S/F` such that for every intermediate `M`, every valuation subring `A` of `M` in which `2` (resp.
`3`) is a unit and which contains `j(E)`, there is a good model `W/A`, `κ • E_M = W.map`, `Δ(W)` a
unit, and inertia that fixes the 2-torsion (resp. 3-torsion) pointwise **does** act trivially on `S`.
This is the local half of the Frey/Serre–Tate good-reduction argument, and it is exactly what
SET-AF101W2's Deuring form and W3's Legendre form were proved for.

Both pins build the model (`model_and_faithful`) and the field `S = F(roots of the two-torsion
polynomial, square roots of their differences)` from scratch; the char-3 pin reuses
`DeuringLocal.val_natCast_le`. Home `WeierstrassCurve/Reduction/` — the module imports
`Automorphism/{NormalForm,DeuringForm}.lean` and `Torsion/DivisionField.lean`, all below it.

### M1 — `Y^{2M}·jq^{M+1}·(jq-1728)^M` integral over `ℂ[jq⁻¹]`

`isIntegral_adjoin_coeffEmb_jq_inv_of_mul_thetaL_eq_qExpansion_of_gamma_le` (854) and
`isIntegral_adjoin_coeffEmb_jq_of_mul_thetaL_eq_qExpansion_of_finiteIndex` (246): if a cusp form `f`
of weight 2 has `Y · thetaL(jq) = qExp f` in the Laurent series, then those monomials are integral
over `ℂ[jq⁻¹]` (resp. `ℂ[jq]`). The engine is `thetaL` (the Serre derivative), the Eisenstein
`q`-expansions `E₄/E₆/Δ` (`= 𝓔₄/𝓔₆/𝓓` in the pin), `rankinCohen`, and the quotient-function
polynomial `Pτ` whose coefficients are the `bfun`'s. **`thetaL` is ported**:
`ModularCurve/Period/QExpansionDerivative.lean` (the linear map) and `Period/QExpansionDiff.lean`
(`thetaL_mul`, and `thetaL_coeff`/`thetaL_coe`/`support_thetaL_subset` are the pin's own first five
lemmas — diff the port's copies before transcribing). The pair shares 183 lines / 13 proofs under
`port_advise`'s strongest factoring unit; write each once.

`exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral_qExpFunctionFieldC` (233) is the same
story's analytic end: a cusp form whose `q`-expansion lies in `qExpFunctionFieldC` is a `thetaL`-power
multiple of an integral form. It is **one order with M1** because its file's first five lemmas are the
same `thetaL`/`coeffEmb jq` glue (`thetaL_jqModC`, `thetaL_coeffEmb_jq`, and the already-substituted
`one_mem_strictPeriods_of_T_mem`).

### M2 — `qExp g / qExp h` integral over `ℂ[jqModC]`

`isIntegral_adjoin_jqModC_qExpansion_div_of_forall_isBoundedUnder` (550) and
`…_of_finiteIndex` (532) are the `Gamma₁ M` and the general finite-index `Gamma` forms of one
theorem: a ratio of `q`-expansions of modular forms, bounded at every cusp, is integral over
`ℂ[jqModC]`. Under `port_advise` the two pins are the set's largest factoring unit — **304 lines /
23 proofs** identical in the two files (`exists_mdifferentiable_mul_eq` 65, `exists_qParam_pow_le`
32, `isIntegral_of_forall_isBoundedUnder` 26, `key_ineq` 21, …) — and the `_of_finiteIndex` one
generalises the level parameter to `wd Γ = Γ.normalCore.index`. One module, one engine, two
headlines. `MDiff`/`CMDiff` are mathlib's `UpperHalfPlane` notation, not port definitions.

One **one-declaration insertion** rides in this order, because it is the same `X1`/`jq` layer:
`exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion` (34) →
`ModularCurve/QExpansionDifferentialLift.lean`, which carries its first premise
(`exists_coeffMap_qExpansionDiffAlong_laurentBaseChange_qExpansionFunctionFieldC_eq_qExpansion`,
`:581`) and imports the module of its second (`Period/QExpansionDiff.lean`). The order first named
the latter module; that is a **cycle** — the first premise's module is one import above it — and the
worker's report caught it (§7). (Its sibling `exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36) was cut from
the set at the pricing pass — a hidden definition gate, §5.)

## 2. The scaffolds

Each new module exists before its order starts, with its header prose, its `spec-pin:` wires (the
`Theorems/` wrapper and the `P2M/Sol/S_` file for every row), a narrow import list, and the
**headline declarations only**, at the wrapper's statement and the published name, body `sorry`.

All five scaffolds were elaborated before any order was written (`lake env lean -DautoImplicit=false`,
each silent but for its `sorry`s) and are green in the checker:

| order | module | scaffold `check_port` | engine to land |
|---|---|---:|---:|
| A1 | `Automorphism/TorsionBasis.lean` (new) | **2 ok** | 49 + 44 pin rows, ~11 already public in `Automorphism/Basic.lean` |
| A2 | `ModularCurve/LevelN/TorsionOrbit.lean` (new) | **1 ok** | 72 pin rows (58 new by last name) |
| A3 | `Reduction/InertiaFaithful.lean` (new) | **2 ok** | 25 + 21 pin rows (21 + 18 new) |
| M1 | `ModularCurve/Analytic/JqInverseIntegral.lean` (new) | **3 ok** | 80 + 14 + 8 pin rows (55 + 11 + 5 new) |
| M2 | `ModularCurve/Analytic/JqModCIntegral.lean` (new) | **2 ok** | 46 + 47 pin rows, 304 lines shared |

Two scaffold findings worth recording. **The A3 scaffold needed
`Mathlib.RingTheory.Valuation.RamificationGroup`**: `ValuationSubring.decompositionSubgroup` and
`.inertiaSubgroup` are not in the base `ValuationSubring` module, and their absence reads as
`Invalid field … The environment does not contain …`, not as a missing name. **The M2 scaffold needed
`open scoped Topology`** for the `𝓝[≠] τ` notation in the headline — the pins get it from a
`open scoped Topology in` line that a scaffold must carry.

## 3. The pricing

| order | raw `S_` lines | dup copies | boilerplate | **net new** |
|---|---:|---:|---:|---:|
| A1 (2) | 1,529 | 110 | 44 | **1,375** |
| A2 (1) | 697 | 0 | 22 | **675** |
| A3 (2) | 1,171 | 0 | 44 | **1,127** |
| M1 (3) | 1,333 | 183 | 66 | **1,084** |
| M2 (3) | 1,116 | 317 | 44 | **755** |
| **total** | **5,846** | **629** | **283** | **≈4,864** |

`port_plan` on the twelve-row slice (before the 36-row was cut) prints the same budget:
**raw 5,882 → 5,599 declaration lines, of which 629 duplicate copies and 283 boilerplate, 345 distinct
declaration groups, 70 already in the port → 4,900 net new math lines**; the cut row was 36 of those,
so the set as cut is ≈4,864. Its *substitute* block also re-finds the `Δ₀`→`JOneESRat.A12` and
`bfun`→`WLightFriOrbit.orbitCoeff` pairs (the latter the *parser's type-only `def` match* — 5 such
suspects; read the body, FR-0266) and claims `E2`/`E3` are the port's `WeierstrassCurve.E0`, which is
**wrong**: those are `private` in `Automorphism/CharTwo.lean` and the pin's `E2`/`E3` are its own
public models (A1's order says so). The dup column is `port_advise --nodes`' *port once* section (the "strongest factoring units" lines);
a further 18 declarations / ≈95 lines are already in the port and are imported, not re-proved
(`thetaL_mul`, `one_mem_strictPeriods_of_T_mem`, `T_mem_Gamma1`, `Δ₀` = `X1/FunctionField.lean`'s
`JOneESRat.A12`, the `Automorphism/Basic.lean` prelude, …). The pin row that is `private` in a pin
file contributes nothing to a `check_port` target (§AF101's corrected count rule).

## 4. The gates

Per order, as [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md)
§6: `check_port` 0 mismatch / 0 missing with every declaration `ok`; the engine gate as the
`statement_db` pin-vs-module declaration diff; `#print axioms` on every headline; the module's own
silent `lake env lean` loop and one locked `lake build`; `dedup.py --within`; `move_dead.py
--dry-run`; a heartbeat probe pair recorded and not installed. The set-level import probe is
`lean/tmp/af102/collision-probe.lean`.

## 5. Not cut — named and deferred (FR-0040)

* **The valued-field story** (`ValuationSubring` and the `NumberField`/`mixedEmbedding` leaves): the
  seven `ValuationSubring` rows (`ringKrullDim_le_ringKrullDim_comap_add_trdeg` 269,
  `exists_smul_mem_of_transcendental_residue` 262, `natDegree_map_eq_card_roots_of_splits` 174,
  `IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` 83 with fan-in 21,
  `tensorProduct_exists_primitive_factor` 78,
  `exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero` 57,
  `charP_residueField_of_liesOverPrime` 37 with fan-in 27; 960 silo) are almost `Mathlib`-only and
  are a set of their own, as SET-AF101 §7 already judged. Not opened here: this set's two subjects
  are already 4,900 net lines.
* `ModularCurve.ModularPolynomialData.eq_all` (75) — the one row the corrected read adds; MD-005's
  phi-refactor metadata block, not a porting row (§0).
* **`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36) — cut at the pricing pass, and it
  is the set's second FR-0298-class finding.** The row reads `needed = 1, premises = 0` and its `S_`
  file's two `Theorems/` imports both resolve, but its one non-elementary input is the
  **`ModularForm`-level** rational basis `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`,
  and the port holds only the `CuspForm` twin (`CuspForm.exists_basis_…`, `Gamma1IntegralBasis.lean`;
  `twin_scan` calls the relationship `relative`). The chain behind the missing statement —
  `ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even` (913), `…_mem_adjoin_exp` (448),
  `…_eq_algEquiv_apply` (341), `…_mem_range_ratCast` (261) — is unported, and
  `ModularCurve/X1/IntegralityJqNModC.lean`'s own header already says so ("**Not ported here**"). The
  readiness test cannot see it: the premise is a `ModularForm` node the frontier counts as ported by
  its `CuspForm` twin's last name. So it stays deferred until the `ModularForm` rational-structure
  chain is ported — a set of its own, priced from `Thm_ModularForm_exists_gamma1_qCoeff_eq_algEquiv_
  apply_of_even` — and the port's `IntegralityJqNModC.lean` keeps its MD-001 prose.
* The `AutomorphicForm` rows (RankinSelberg 1,194, CuspidalSpectrum 453/446/428/294/174,
  CuspidalConstituent 439/415, HaarQuotient 261) — the AF-subject remainder, each its own story and
  its own set; 1,194 is a single flat pin, not cuttable.
* `ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary` (951),
  `ModularCurve.StarBank.hassePolyDescent` (407), `card_quotient_gamma0_le_dedekindPsi` (318),
  `rep_tateModule_jOne_comm` (24), `AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_
  constantReduction` (59), `GaloisRep.exists_isSemisimpleRepresentation_…` (495).
* `M4aTorus.completedRayL_fe` (12,126) and `NumberField.exists_continuousOn_exp_eq_rayClassLSeries`
  (684) — a single giant pin, and a number-field analytic row.
* The `leaves` block's Tate-curve points-law pair (471, 247) — the deferred definition-layer set
  (CARRY-FORWARD; §AF101 §7).
* Withheld by the FR-0044 guard: `ModularCurve.moduleFinite_padicInt_tateModule_{jH,jOne}`,
  `AlgebraicCurve.Place.exists_natCast_dvd_ord_sub_single_sub_single_complex`,
  `AlgebraicCurve.Pic0.finite_torsion_of_isAlgClosed_of_charZero` (831) — the prunable subject's.

## 6. The landing

Every number below was measured twice — by the order's worker and again by the manager on the landed
files. **All five modules hold 334 `ok`** (63 + 72 + 47 + 88 + 64), 0 mismatch / 0 missing / 0 unjustified
`own`; all five are silent at the edit loop and built under `flock`; the set-level import probe
(`lean/tmp/af102/collision-probe.lean`) prints **nothing**; `#print axioms` over every public
declaration of the set is a subset of `[propext, Classical.choice, Quot.sound]` with **no `sorryAx`**;
no module carries `set_option maxHeartbeats`.

| order | module | lines | checker | engine diff | axioms | dedup | move_dead | probe (silent / fails) |
|---|---|---:|---|---|---|---:|---|---|
| A1 | `Automorphism/TorsionBasis.lean` (new) | **1,457** | **63 ok / 0 / 0** | 93 pin rows, **0 unaccounted** (10 prelude rows/pin imported, `main`+2 `solution` carried by the headlines) | 39 × 3-axiom + 24 × 2-axiom | 2 (the pins' case-splitter↔headline pairs) | 0 / 0 | 200,000 & 400,000 / 100,000 |
| A2 | `LevelN/TorsionOrbit.lean` (new) | **795** | **72 ok / 0 / 0** | 72 pin rows ↔ 72 by **hash**, 0 unaccounted | 47 + 22 + 3 | **0** | 0 / 0 | 75,000 / 70,000 |
| A3 | `Reduction/InertiaFaithful.lean` (new) | **1,292** | **47 ok / 0 / 0** | 45 declared + 1 imported (`val_natCast_le`), 0 unaccounted | 45 + 2 | 3 (2 headline↔`solution`, 1 two-route twin) | 0 / 0 | 110,000 / 100,000 |
| M1 | `Analytic/JqInverseIntegral.lean` (new) | **1,232** | **88 ok / 0 / 0** | 102 pin rows → 89 distinct statements → 89 declared, 0 unaccounted | 87 + 1 | **0** | 0 / 0 | 100,000 / 50,000 |
| M2 | `Analytic/JqModCIntegral.lean` (new) | **876** | **64 ok / 0 / 0** | 93 pin rows = 63 distinct hashes ↔ 62 declared + 1 imported, 0 unaccounted | 64 × 3-axiom | 1 (the deliberate `isIntegral_of_forall_isBoundedUnder` pair) | 0 / 0 | 5,000 / 3,000 |
| — | `QExpansionDifferentialLift.lean` (**+47**, the row-34 insertion) | 641 | **57 ok** (56 → +1) | 1 ↔ 1 | — | 0 | 0 / 0 | — |

### Plan vs actual

| order | silo (priced) | net new (predicted) | lines landed | ratio |
|---|---:|---:|---:|---:|
| A1 | 1,529 | 1,375 | 1,457 | 0.95 |
| A2 | 697 | 675 | 795 | 1.14 |
| A3 | 1,171 | 1,127 | 1,292 | 1.10 |
| M1 | 1,333 | 1,084 | 1,232 | 0.92 |
| M2 | 1,116 | 755 | 876 + 47 | 0.83 |
| **total** | **5,846** | **4,864** (port_plan 4,900) | **5,699** | **0.97** |

The set landed **5,699 lines against 5,846 silo**, i.e. slightly *fewer* lines than the pin — the first
time in this column that a set came in under its silo, and the mechanism is the porting rule working:
597 duplicate pin lines were written once (`thetaL`/Eisenstein prelude 183, the 550/532 engine 317, the
A1 pair 112), 13 pin rows were imported as substitutes (`thetaL_mul`,
`one_mem_strictPeriods_of_T_mem`, `T_mem_Gamma1`, `val_natCast_le`, the `An.*` family), and the pins'
`solution` rows are the headlines.

### Four brief claims were false, every one caught by a worker

1. **Three `check_port` sizes were under-estimates**, and the cause is the count rule again but the other
   way round: A1's ≈60 was **63**, A2's ≈59 was **72**, A3's ≈41 was **47**, M2's ≈50 was **64**. A
   last-name scan over the port (my estimate's instrument) counts a pin row as "already there" when a
   *different namespace* or a `private` declaration carries the last name — A2's 14 such hits could not
   stand in for any pin row. **A `check_port` size is measured, not estimated**; the scaffold table
   above is corrected by these.
2. **Row 34's home was a cycle** (my order): its first premise is declared one import *above*
   `Period/QExpansionDiff.lean`, so the row cannot live there (FR-0280's shape). Re-homed to
   `QExpansionDifferentialLift.lean`, which carries that premise and imports the other's module — the
   row's `+1` sits there and `Period/QExpansionDiff.lean` stays untouched at 11 `ok`. Registered as
   **FR-0300**.
3. **`Δ₀` is not `JOneESRat.A12`** (the brief's and `port_plan`'s substitution): `A12 = E₄³` and
   `E₄³ - E₆² = 1728·Δ`, so the pin's two `Δ₀`/`Δ₁` defs are transcribed, not substituted — one of the
   five *suspect* type-only matches `port_plan` itself flags (FR-0266).
4. **`MDiff` is mathlib's `scoped[Manifold]` notation**, not a `UpperHalfPlane`-scoped one: the pins'
   single `open scoped` line had to be split into `MatrixGroups Topology Manifold ModularForm
   Pointwise`, and the `𝓝[≠] τ` of the M2 headline needs `Topology` in any consumer (my scaffold table
   said this, the *reason* is the `Manifold` scope).

### Two findings the set contributes to the instruments

* **FR-0278 came back, from the manager's side.** A locked `lake build` of M1 failed on two *dependency*
  modules with `error: no such file or directory … <X>.olean` while a second `lake` process was running;
  the same build succeeded twenty minutes later, and M1's worker independently lost **20 `.olean`s**
  (their `.olean.hash` files left behind) to a killed build. The rule stands and needs the stronger
  form: a *manager* build must also hold the lock, and `lake env lean` must not be run against the tree
  while any build is in flight.
* **A module's `lake build` log is not the module's silence.** A3's build succeeded with 0 warning lines
  from `InertiaFaithful.lean` and 20+ from dependency modules (`Place/Dictionary.lean`,
  `Velu/Shift.lean`) that the cascade rebuilt. The gate is "0 warnings from *this* file", read with
  `grep -c "<file>:"`.

### The consumer zone

`lean/spec/SetAF102Consumer.lean` — a `spec/` probe with **four zones over five theorems**, elaborating
**silently**: A1 (the `j = 0` basis pair at `M = 2` over `AlgebraicClosure ℚ`, the `∃!`-property used to
prove `P ≠ Q`), A2 (the char-two orbit count, the cube root `w` produced by **A1's** `exists_cube_root`
— two orders composed), A3 (`legendreCurve 2` over `ℚ → AlgebraicClosure ℚ`, ellipticity from
`LegendreNormalForm.legendre_Δ` = 64, reading the Galois subfield), M1 (the 233 headline fired at `X = 0`,
`m = 1`, `M = 1`, producing a cusp form with vanishing `q`-expansion). **M2 has no zone**: its natural
instantiation (`Γ = ⊤`) makes the `ModularForm (⊤ : Subgroup (GL (Fin 2) ℝ)) k` instance search exceed
200k heartbeats in a *probe* file, and the module's own use is already exercised by
`QExpansionDifferentialLift.lean`'s row, which fires it in anger. Three shape notes for the next
consumer: the `∃ (_ : E.IsElliptic) (P Q : …)` telescope does **not** give the smul instance, so a zone
must avoid `n • P` in its own statement; `ZMod.val_one` needs its modulus (`rw [ZMod.val_one 2]`); and
a `CuspForm` at a coerced `⊤` is not syntactically the `CuspForm` at `⊤` — write the coercion into the
statement.

## 7. After the landing — the shelf re-read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  $(printf -- '--unport %s ' <the 21 selfcheck names>) > build/shelf_af102_landed.json
```

| figure | before the set | after the landing |
|---|---:|---:|
| `needed [F terminal]` (corrected read) | 350 / 187,490 | **339 / 181,644** |
| ready rows | 32 / 12,473 | **25 / 9,519** |
| leaves | 23 / 15,967 | 23 / 15,967 |
| withheld (FR-0044 guard) | 4 / 831 | 4 / 831 |

The delta is **−11 nodes / −5,846 lines**, which is *exactly* the cut — the eleven rows are the only
thing the set consumed, and the leaves block is untouched (the set cut from the ready block, as §0 says).
**Four rows became ready because of the set** (2,892 silo), and they are the payoff:

* `ModularCurve.exists_equivariant_torsion_reduction_ofJ` (**1,288**) — A3's consumer: the equivariant
  torsion reduction over the good model, the next step of the Frey/Serre–Tate argument;
* `ModularCurve.ord_sub_algebraMap_le_one_laurentBaseChange_qExpFunctionFieldC_of_ne_zero_of_ne_1728`
  (**1,112**) — M1's consumer (`jq - 1728` in the denominator, which is exactly the `(jq-1728)^M` the
  854 headline produces);
* `ModularCurve.ComplexPlaceDictionaryOf.exists_pt_eq_of_mem` (**370**) — the place dictionary's point
  identification, unblocked by the torsion-basis rows;
* `ModularCurve.one_sub_ord_le_ord_of_coeffMap_mul_thetaL_eq_qExpansion_of_gamma_le` (**122**) — the
  `thetaL`-ratio side of M1's engine.

## 8. What the set leaves behind

1. **`WeierstrassCurve/Automorphism/Basic.lean` is now the standing home for point transport**: the
   eleven `xy`/`castPt`/`vcHom` rows are public and both pins of A1 import them instead of
   re-declaring them (20 pin rows, 10 per pin). The next module that needs `HEq`-transport of a
   variable change over an affine point should import it, not transcribe.
2. **Two subject namespaces per pin pair, not one.** A3's `LegendreRoute`/`DeuringRoute` and M2's
   `IntegralGammaAux`/`IntegralFiniteIndex` are the working pattern for a sibling pair whose rows
   collide on last name: the *engine* is written once at the larger pin's names, and only the rows
   whose statements genuinely differ are declared twice (M2: 10 of 12 for a real statement difference,
   2 for an elaborated-signature difference).
3. **A registered promotion** (refactor round): `ModularCurve/LevelN/GenusFF.lean`'s `ST_pow_three`,
   `ST_pow_six`, `S_pow_four` (and an `S_pow_two` it lacks) are `private` twins of A2's public rows,
   and `Period/ParabolicHomsBasis.lean` carries a third copy. One home would save ≈30 lines in A2 and
   deduplicate three modules; it was not done in this set because it re-opens a hub plus a landed
   module for a 30-line saving (the AF101W3 `D0Aux` precedent). Registered in CARRY-FORWARD.
4. **`lean/tmp/af102/` — seven work orders, six reports, the review harness (`review.py`) and the
   consumer.** `review.py` is the reusable instrument this set added: one command per module for the
   checker, the pin-vs-module engine diff (reading both the `P2M/Sol/` and `Theorems/` wires),
   the silent edit loop, `dedup --within` on a *path-suffix* pattern, `move_dead --dry-run` and a
   `#print axioms` probe over every public declaration.
5. **FR-0299 and FR-0300** — the two scoping rules this set learned: a premise the frontier credits to a
   *twin* is not ported (the `CuspForm`/`ModularForm` basis pair, which cut a 36-line row), and a
   one-row insertion needs the per-premise import-direction check, not a summary of its "one premise".
6. **The deferred `ModularForm` rational-structure chain** (CARRY-FORWARD), which is what the cut row
   waits on: `span_frickeRational_E4_pow_E6_pow_eq_top` (1,524), `exists_gamma1_qCoeff_eq_algEquiv_
   apply_of_even` (913), `…_eq_algEquiv_apply` (341), `exists_basis_gamma1_qCoeff_mem_range_ratCast`
   (261).
