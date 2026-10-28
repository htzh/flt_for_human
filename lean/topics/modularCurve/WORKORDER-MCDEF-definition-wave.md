# The MC definition wave — seven modules for MC-4, MC-5 and MC-6

**Status: scoped, landed and checked (2026-10-27).** This is the definition layer that
[TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §6 call 3 handed to the manager "before MC-4 to
MC-7": the shelf priced it at **1,118 lines over 12 modules**, of which MC-7's 338 pin lines
landed separately ([SET-MC7.md](SET-MC7.md) §2). This order scopes and lands the rest —
read not from the shelf's module-level table but from the **twelve ready rows of MC-4, MC-5 and
MC-6** and the declarations they actually name. The result is **7 modules / 539 pin declaration
lines / 121 checked declarations, all `ok`**, and it is smaller than the shelf's figure for three
reasons that are the substance of this note:

1. **the shelf's gate table is module-level; the rows' need is declaration-level** (§0.1): the
   twelve rows name vocabulary from nine pin `Def_` modules (and one more inside their closure),
   and in each module a subset of the declarations — `CohCarrier_Fricke` has 28 and the M9 row
   names 7, `ModularCurve_X1HeckeModule` has 42 and the M5 row needs 17;
2. **four "gates" are already in the port**, under a different home or name
   (`gamma0Units_surjective`, `gammaLift`/`unitOfPrimeNotDvd`/`StableD`/`StableU`/`StableT`,
   `heckeOperatorOneBar`, `IsDiamondAutHBar`/`diamondAutHBar`/`HeckeDiamondInputsHAll`), and
   `CuspForm_Gamma1HeckeOperators`'s 32 lines are the H2 pair already recorded by MC-7;
3. **two of the shelf's gate modules are not any ready row's** (§0.2): `PeriodOf`'s
   `peterssonOf` block and `ModularCurve_XH`'s torsion/Tate block are deferred, with the reason
   recorded per module — and the audit also finds one module the shelf never listed,
   `Def_CohCarrier_HeckeData` (92 lines), inside `CohCarrier_Inst`'s closure.

The wave does **not** move the shelf: `needed` is unchanged (§0). Its deliverable is the surface
MC-4, MC-5 and MC-6 are statable over, plus a `spec/` consumer zone whose error count is 0.

| figure | value |
|---|---:|
| modules landed | **7** (3 inserted into existing homes, 4 new) |
| pin declaration lines transcribed | **539** (84 declarations) |
| net new port lines | **≈870** (headers and docstrings included) |
| checked declarations | **121 ok / 0 mismatch / 0 missing / 0 own** (83 of them new; 38 were already in the homes) |
| rows gated | 8 of the twelve (`350`, `220`, `384` and the 27-line `…diamondOneBar` pair need nothing new) |
| deferred declarations | 18, over 3 of the modules, each with its absent premise named (plus the 12 of the two gate modules no row needs, §0.2) |

## 0. The read, and what a definition wave can and cannot move

Canonical, on the tree after MC-7's three orders (2026-10-27):

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mcdef.json
python3 frontier.py --selfcheck
```

| figure | this read |
|---|---:|
| `needed [F terminal]` | **1,004 / 398,972** |
| ready, all namespaces | 75 / 15,689 |
| `ModularCurve` ready shelf | **15 / 4,163** |
| `ModularCurve` leaves | 32 / 6,797 |
| leaves, all namespaces | 294 / 71,671 |
| frontier F | 1,408 / 727,998 |
| `--selfcheck` | **PASS** |

The 15 MC ready rows are exactly the twelve rows of MC-4/5/6 (3,348 silo) plus the three first-wave
successors the shelf's forecast named (`meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two`
611, `c4_mul_toricPoint_fst_div_c6_mem_qExpFunctionFieldC_gamma1` 168, and MD-001's 36 row):

| story | row (`ModularCurve.` dropped) | silo | this wave |
|---|---|---:|---|
| M6 | `periodLatticeOf_gammaH_heckeDiamondStable` | 464 | **D1** |
| M7 | `exists_semisimple_descent_of_trace_det_mem_range_finite` | 403 | **D7** |
| M4 | `siegelFun_specialLinearGroup_smul` | 390 | **D6** |
| M9 | `qExpand_norm_heckeBetaHBar` | 384 | — (0) |
| M6 | `exists_linearEquiv_parabolicHoms_dual_periodLatticeOf_apply_periodOf_of_isCongruenceSubgroup` | 350 | — (0) |
| M9 | `exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion` | 322 | **D5** (+`gamma0Units_surjective`, ported) |
| M5 | `JOne.galois_smul_heckeAlgOne_smul` | 272 | **D2** |
| M5 | `galois_smul_genOpH_comm` | 265 | **D3** (+`Gen` from D4) |
| M4 | `SiegelUnit.differentiableOn_siegelFun` | 224 | **D6** |
| M4 | `SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion` | 220 | — (0) |
| M5 | `heckeOperatorHAlong_diamondHBar_comm` | 27 | **D3** |
| M5 | `heckeOperatorOneBar_comm_diamondOneBar` | 27 | — (0) |

**A definition wave cannot move `needed`, and this one was not expected to.** The frontier's
readiness is premise-based: every one of the twelve rows already reads `needed = 1` with
`premises_pruned = 0`, and the twelve are *statable in principle* only once their statement
vocabulary exists. The wave's output is therefore a **checked surface plus a consumer zone**, not
a delta on the demand graph; the delta comes from MC-4/5/6 themselves. (The instrument agrees:
the read above is identical before and after the wave's Lean.)

The withheld block is unchanged (4 rows: the two `ModularCurve` Tate-module rows / 610 silo and
two `AlgebraicCurve` complex-analytic ones), and the MC lease block is unchanged at 32 / 6,797.

## 0.1 The audit: what the twelve rows actually name

Method, and the wave leaves the instrument behind: `spec/gate_scan.py` (new, this wave) is the
declaration-level gate scan. For a pin `Def_` module and a row it lists the module's public
declarations, computes the **intra-module closure** of the declarations whose last names occur as
words in the row's `S_`/wrapper text (a declaration's body pulls in the declarations it calls:
`diamondHBar` → `diamondAutHBar` → `IsDiamondAutHBar`), strips the two lines that name without
using (`import`, and the wrappers' global `attribute [ … -simp … ]` lists), and marks each used
declaration as already in the port or missing, with its pin line span. It reuses
`spec/lean_parser.py`'s own declaration parser and the port tree's last-name index:

```bash
cd lean
python3 spec/gate_scan.py --pin Definitions/Def_CohCarrier_Fricke.lean \
  --rows S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
# -> uses 7/28 of the pin's declarations; the other 21 are not M9's gate
python3 spec/gate_scan.py --pin Definitions/Def_CohCarrier_Inst.lean \
  --rows S_ModularCurve_galois_smul_genOpH_comm S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
# -> `gamma0Units_surjective`, already homed in `ModularForms/Defs/GammaH.lean`
```

| pin `Def_` module | shelf's gate | the rows use | landed here | deferred (why) |
|---|---|---:|---|---|
| `CuspForm_HeckeOperatorFormsGammaH` | 14 / 158 | 19 (closure of 9) | **14 / 144** | — (`Gamma_le_GammaH`…`StableT` ported in `Defs/GammaH.lean`) |
| `ModularCurve_X1HeckeModule` | 36 / 203 | 17 (`JOne.galois_smul_heckeAlgOne_smul`) | **25 / 111** | `Integral`/`Rational`/`Predicate` 14 decls / 75 lines (`TateModule` absent) |
| `ModularCurve_XHOperators` | 9 / 56 | 8 + 4 | **7 / 35** | `tateGenOpH`, `tateGenOpH_apply_coe` / 12 lines (`TateModule`) |
| `CohCarrier_Inst` | 7 / 80 | `Gen` (M5), `gamma0Units_surjective` (M9) | **6 / 60** | `hdata`, `MLAt` / 21 lines (`CohCarrier.HeckeData` absent) |
| `CohCarrier_Fricke` | 28 / 164 | 7 (closure of 7) | **28 / 136** | — |
| `ModularCurve_SiegelFunction` | 2 / 23 | 1 (`siegelFun`) | **2 / 21** | — |
| `ModularCurve_ResidualRealization` | 2 / 34 | 1 (`CyclotomicDeterminant`) | **2 / 32** | — |
| **total** | **774** | | **539** | 18 declarations / 108 lines |

Per row, the gate is one line of vocabulary:

| row | needs | from |
|---|---|---|
| 464 | `CuspForm.{heckeTLinH,heckeULinH,diamondLinH}` + `_eq`/`coe_*` | D1 |
| 403 | `CyclotomicDeterminant` | D7 |
| 390, 224 | `siegelFun` | D6 |
| 322 | `CohCarrier.{frickeMat,frickeMat_apply_10,N_dvd_of_mem_Gamma0,frickeMat_mem_Gamma0,gamma0Units_frickeMat,N_dvd_of_mem_GammaH,frickeMat_mem}` | D5 |
| 272 | `HeckeAlgOne`, `heckeModuleOneBar` + 8 lemmas | D2 |
| 265 | `genOpH`, `diamondHBar`(+`_apply`), `CohCarrier.Gen` | D3, D4 |
| 27 (`…diamondHBar_comm`) | `diamondHBar`, `diamondHBar_apply` | D3 |
| 350, 220, 384 | **nothing** — every definition they name is already ported | — |
| 27 (`…diamondOneBar`) | **nothing** — `heckeOperatorOneBar`, `diamondOneBar` ported | — |

## 0.2 Two gate modules no ready row needs

These are the shelf's gate entries that the declaration-level audit removes from this wave. Each
stays a real future cost; neither is a ready row's.

- **`Def_ModularCurve_PeriodOf`'s `CuspForm` section** (5 declarations / 21 lines:
  `peterssonIntegrandOf`, `peterssonOf`, `peterssonOf_def`, `peterssonIntegrandOf_gamma0`,
  `peterssonOf_gamma0`). The 350 row imports the module but names only `periodOf`,
  `periodLatticeOf`, `periodOf_mem_periodLatticeOf` — all long ported — and the 464 row's
  vocabulary is D1's. **Deferred**, which is also what the port's
  `ModularForms/EichlerShimura/PeriodOf.lean` header already decided ("none of the 28 consumers of
  `ModularCurve.exists_hasEquivariantPrimitiveOf` reaches it"). Its `_gamma0` `rfl` lemmas need
  the pin's `Def_CuspForm_Petersson` (`peterssonIntegrand`/`petersson`, 14 lines, also unported),
  so landing the five is really a two-module job — the L-other leaf rows
  (`…_petersson_mem_periodLatticeOf_gammaH`) are where it comes back.

- **`Def_ModularCurve_XH`'s `Jacobian` sections** (7 declarations / 35 lines:
  `JH.torsionGaloisRep` + its two laws, `JH.tateGaloisRep`, `JH.tateEnd`, their two `_apply_coe`
  laws). No MC-4/5/6 row names any of them. The torsion trio is cheap (`SemilinearAut.torsionRep`
  and `arithmeticGalois` are ported) and is the M9 **successors'** surface — the shelf's own
  forecast places the `_of_dvd`/`galois_smul_…` successors behind these rows; the Tate pair is
  blocked on the same absent `TateModule` as D2's and D3's deferrals
  ([TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md) T1). **Deferred** as one block, so that
  what remains of `Def_ModularCurve_XH` is exactly the Tate layer and not half a block.

**…and one module the shelf never listed.** `CohCarrier_Inst`'s `hdata`/`MLAt` are the pin's
`Def_CohCarrier_HeckeData` (`structure HeckeData` + `FreeAlg`/`thetaTilde`/`mTheta`/`opAlgHom`/
`toMLₒ`, 92 pin lines), which the port lacks entirely. It is not a ready row's gate and is deferred
with `hdata`/`MLAt`: the only mentions of its vocabulary in the twelve rows' files are the 322
wrapper's global `attribute [ … -simp … ]` list, which the port does not reproduce — the gate scan
reports 0/17 used once that line is discounted, and 11/17 (49 pin lines) before.

## 0.3 The modules, and the homes

Three of the seven are **insertions** into a home the subject names and the import direction
allows; four are **new modules**. No promotion was needed, and one legacy migration was paid.

| # | home | pin source | kind | declarations |
|---|---|---|---|---:|
| **D1** | `ModularForms/Defs/GammaH.lean` | `Def_CuspForm_HeckeOperatorFormsGammaH:105–262` | insert | 14 |
| **D2** | `ModularCurve/X1/HeckeModule.lean` | `Def_ModularCurve_X1HeckeModule:16–170` | insert | 25 |
| **D3** | `ModularCurve/XH/Operators.lean` | `Def_ModularCurve_XHOperators:57–98` | insert | 7 |
| **D4** | `ModularForms/CohCarrier/Inst.lean` | `Def_CohCarrier_Inst` (`Gen` + `Inst` minus `hdata`/`MLAt`) | **new** | 6 |
| **D5** | `ModularForms/CohCarrier/Fricke.lean` | `Def_CohCarrier_Fricke` (whole) | **new** | 28 |
| **D6** | `ModularCurve/Defs/SiegelFunction.lean` | `Def_ModularCurve_SiegelFunction` (whole) | **new** | 2 |
| **D7** | `ModularCurve/Defs/ResidualRealization.lean` | `Def_ModularCurve_ResidualRealization` (whole) | **new** | 2 |

**The dependency order is D4 → D3.** `genOpH` is a function on `CohCarrier.Gen M S`, and `Gen` is
D4's; `ModularCurve/XH/Operators.lean` therefore imports
`FLTForHuman.ModularForms.CohCarrier.Inst` — an upward import of a definition module, which is the
direction the layering wants (`ModularForms` below `ModularCurve`). The other six are independent
and were written concurrently.

**The legacy migration.** `ModularCurve/XH/Operators.lean` was on `spec/old_check_stmts.py`'s
`PORT_FILES` (the frozen checker owned it, and its entry's comment recorded that `genOpH`/
`diamondHBar` were "deliberately absent"). The wave edits the module for its subject, so it pays
the migration in the same touch, per the recipe §4: a `spec-pin:` wire for its own pin `Def_`
module, the `PORT_FILES` row deleted (the `SOURCES` rows stay), a silent build, the checker run.
The comment that replaces the row records the hand-over and the 14-ok verdict.

**No `spec-pin:` was widened.** Each wired module names exactly the pin file it transcribes:
D1's home already carried the four `spec-pin:` lines it needs; D2's its own; D3 gained one;
D4–D7 each have one. No module's wire names a pin file it does not transcribe (MD-001's failure
mode), and none of the four new modules is a facade over another module's engine.

## 1. What landed, per module

Every statement below is the pin's verbatim — the checker's verdict is the evidence, since
`check_port` diffs by statement hash, not by name. Proofs deviate only where mathlib `v4.34.0`
forced them, and each deviation is listed.

**D1 — `CuspForm.{diamondLinH,heckeULinH,heckeTLinH}` (+11).** The pin's `GammaH` section,
lines 105–262: the three operators, each as a totalised `…Of` constructor consuming the
`StableD`/`StableU`/`StableT` hypothesis, a `Classical`-choice wrapper that falls back to `0`, and
the `_eq`/`coe_*` unfolding lemmas. Proofs: `dif_pos` → `dite_eq_left` (3×, deprecated),
`CuspForm.coe_add` → `FunLike.coe_add`, `CuspForm.IsGLPos.coe_smul` → `FunLike.coe_smul`, and the
pin's redundant `haveI : NeZero ℓ` dropped from one proof body (it is kept in the two *statements*
that carry it — see FR-0056). **The home's prelude is spelled in `CohCarrier`**, so the new
section carries a section-scoped `open CohCarrier` to keep the pin's unqualified statement text;
writing `CohCarrier.gammaLift` in the statement is a `MISMATCH` on a faithful transcription
(FR-0058).

**D2 — the `HeckeAlgOne` algebra and its module structure (25).** `HeckeAlgOne =
MvPolynomial (Nat.Primes ⊕ ℕ) ℤ` with `heckeGenOne`/`diamondGen` and the two `aeval` lemmas; the
generator family `heckeDiamondGenBar` and the commuting hypothesis `HeckeDiamondCommuteBar`; the
`ℤ`-subalgebra consequence `isMulCommutative_adjoin_heckeDiamondGenBar`, the evaluation
`heckeEvalOneBar : HeckeAlgOne →+* Module.End ℤ (JOne M)` with its six computation lemmas, and the
`Module HeckeAlgOne (JOne M)` instance `heckeModuleOneBar` with six smul lemmas. Proofs: the
`dite_eq_left`/`dite_eq_right` pair and one `rintro … _` for v4.34's `Pairwise Commute`; the pin's
`set_option synthInstance.maxHeartbeats 400000` on `heckeEvalOneBarAux_X` is **not needed** and is
not transcribed. Deferred: the pin's `Integral`/`Rational`/`Predicate` sections (14 declarations /
75 pin lines, `TateModule`).

**D3 — `diamondHBar` and `genOpH` (7).** The diamond operator on `J_H(M)` with `_apply`/`_of_not`,
and `genOpH : CohCarrier.Gen M S → (JH M H →+ JH M H)` with `genOpH_T`/`_U`/`_dia`. Statements
verbatim; every proof is the pin's `rfl` or a two-line rewrite.

**D4 — `CohCarrier.Gen` and the cohomological operators (6).** `Gen` (`T`/`U`/`dia`), `heckeTL`
and `heckeTL_apply` (the transfer built operator, identified with the ported `heckeT`), `diamondL`
(the chosen `Γ₀(M)`-lift operator), `diamondL_eq_diamondRaw` (its independence of the choice) and
`opFamily`. No proof adaptation beyond the pin's own text. `gamma0Units_surjective` is imported,
not restated; `hdata`/`MLAt` are deferred with `Def_CohCarrier_HeckeData`.

**D5 — the Fricke involution (28, whole module).** `frickeMat` with its four entry lemmas, the
`N ∣ ·₁₀` lemmas, `frickeMat_mul`, `frickeMat_frickeMat`, `trace_frickeMat`, the `Γ₀`/`Γ_H`
membership lemmas, `gamma0Units_frickeMat` (the unit character inverts), `frickeHom`,
`frickeEquiv`, and the `H1` operators `frickeH1`/`frickeH1L` with the involution laws. One proof
adaptation: v4.34's `SpecialLinearGroup` is a plain `def`, so `frickeMat_mul`'s final `simp` cannot
see the product coercion through `↑(A * B) i j`; the proof `change`s the entry to the matrix level
before `Matrix.mul_apply` (statement untouched).

**D6 — `siegelFun` (2, whole module).** The Siegel unit's `∏'` definition and its `rfl` lemma;
mathlib-only imports. The q-product *engine* (`jtp_term`, `theta_eq`, ≈143 lines) is the two M4
rows' prelude, not the definition layer, and stays with the rows.

**D7 — `IsResidualRealization` and `CyclotomicDeterminant` (2, whole module).** The seven-field
`Prop` carrier and the cyclotomic-determinant predicate. The pin's imports map to
`Defs/HeckeModule.lean` (`HeckeAlg`), `GaloisRep/Defs/Ramification.lean` (`LiesOverPrime`) and
`GaloisRep/Defs/FrobeniusTrace.lean` (`IsFrobeniusAt`).

## 2. The gates, and their verdicts

Per the recipe §6, on each module:

1. **`check_port --force`, all seven** → **121 ok / 0 mismatch / 0 missing / 0 own / 0 kw**:

   | module | verdict |
   |---|---|
   | `ModularForms/Defs/GammaH.lean` | 42 ok |
   | `ModularCurve/X1/HeckeModule.lean` | 28 ok |
   | `ModularCurve/XH/Operators.lean` | 14 ok |
   | `ModularForms/CohCarrier/Inst.lean` | 5 ok (+`Gen`, invisible to the parser — FR-0057) |
   | `ModularForms/CohCarrier/Fricke.lean` | 28 ok |
   | `ModularCurve/Defs/SiegelFunction.lean` | 2 ok |
   | `ModularCurve/Defs/ResidualRealization.lean` | 2 ok |

2. **`#print axioms`** on 19 headline declarations (the three `Γ_H` operators with their `coe_*`
   lemmas, the module instance and its `smul_def`, `diamondHBar`, `genOpH`, `Gen`, `heckeTL`,
   `diamondL`, `frickeMat`, `frickeMat_mul`, `frickeEquiv`, `frickeH1L`, `siegelFun`,
   `IsResidualRealization`, `CyclotomicDeterminant`) →
   `[propext, Classical.choice, Quot.sound]` everywhere; `Gen` (an inductive) needs only
   `[propext, Quot.sound]`.

3. **Builds** — each module's own `lake build` under `flock /tmp/lean-build.lock` and the 2-minute
   cap: the seven modules in 34 s from a warm tree, silent at the project's 200k probe cap, and
   silent at the default cap too (no `set_option maxHeartbeats`, no
   `synthInstance.maxHeartbeats`, no linter suppression anywhere in the seven modules).

4. **`dedup.py --within --tier shape`** on all seven → **0 duplicate clusters, 0 removable lines**.
   (`move_dead.py` is not run: every declaration of a definition wave is unreferenced *until its
   row lands*, so a liveness move would shelf the whole wave by construction. The wave's live
   criterion is the consumer zone.)

5. **Consumer zone** — `spec/ModularCurveDefWaveConsumer.lean`, six zones (A `siegel` … F `resid`),
   real cross-module compositions and no `#check`s: the Siegel defining equation at an
   `UpperHalfPlane` point; `frickeHom` multiplicativity, `frickeEquiv`'s involution and
   `frickeH1L`'s square; `genOpH` at a diamond generator and `diamondHBar`'s additivity; the
   `HeckeAlgOne`-module's `1` and `MvPolynomial.C` actions; `heckeTLinH`/`diamondLinH` linearity;
   the residual carrier's `finrank`/spanning fields and `CyclotomicDeterminant` applied at a
   Frobenius. **Error count: 0.**

6. **Hygiene** — no `sorry`/`admit`/`axiom`/`native_decide`, no `set_option maxHeartbeats`, no
   worker-written `spec/decl_markers.tsv` row (none was needed: the 121 declarations are `ok`
   without a marker), and no false wire (§0.3).

## 3. What this wave does not do, and what it unblocks

**Does not do.**
- **The 18 deferred declarations**, each with its absent premise: D2's `Integral`/`Rational`/
  `Predicate` (14 declarations / 75 pin lines, `TateModule`/`RationalTateModule`/
  `rationalGaloisRep`), D3's `tateGenOpH` pair (2 / 12), D4's `hdata`/`MLAt` (2 / 21,
  `CohCarrier.HeckeData`) — and, not landed at all, `PeriodOf`'s petersson block (5) and
  `ModularCurve_XH`'s Jacobian block (7), §0.2.
- **No promotion and no leaf work.** No declaration was found `private` that a row needs public;
  the leaves' gates (`PeriodHomPair` 140, `Pic0Congr` 106, `ComplexPlaceDictionaryOf` 102,
  `X0ModL` 43) are untouched.
- **No tree build, no shelf move.** `needed` is unchanged (§0); MC-4/5/6 will move it.

**Unblocks.** The four gated orders are now statable: **MC-4** (`periodLatticeOf_gammaH_heckeDiamondStable`,
`exists_linearEquiv_parabolicHoms_…`, and the four M5 rows) on D1+D2+D3+D4; **MC-5**
(`siegelFun_specialLinearGroup_smul`, `SiegelUnit.differentiableOn_siegelFun`,
`SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion`,
`exists_semisimple_descent_…`) on D6+D7 — note that 220 needs nothing from the wave, and the two
`siegelFun` rows still owe the ≈143-line jtp engine; **MC-6** (`exists_slash_fricke_eq_sum_smul_…`,
`qExpand_norm_heckeBetaHBar`) on D5 — and 384 needs nothing new at all. The four rows with no gate
(`350`, `220`, `384` and the 27-line `heckeOperatorOneBar_comm_diamondOneBar`, 981 silo between
them) were never blocked on this wave; the shelf's module-level audit had priced them as gated.

## 4. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mcdef.json
python3 frontier.py --selfcheck
cd ../lean
python3 spec/gate_scan.py --pin Definitions/Def_CohCarrier_Fricke.lean \
  --rows S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
python3 spec/check_port.py --force FLTForHuman/ModularForms/Defs/GammaH.lean \
  FLTForHuman/ModularCurve/X1/HeckeModule.lean FLTForHuman/ModularCurve/XH/Operators.lean \
  FLTForHuman/ModularForms/CohCarrier/Inst.lean FLTForHuman/ModularForms/CohCarrier/Fricke.lean \
  FLTForHuman/ModularCurve/Defs/SiegelFunction.lean \
  FLTForHuman/ModularCurve/Defs/ResidualRealization.lean
timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveDefWaveConsumer.lean 2>&1 | grep -c error
cd ../tools/deps && python3 dedup.py --module FLTForHuman/ModularForms/CohCarrier/Fricke.lean --within --tier shape
```

`spec/gate_scan.py` is the wave's instrument and ships with it (§0.1); `--json` writes the scan
for a programme's price table. Its two discounts (`import`, `attribute`) and its name anchor are
the limits of what it can claim: it is a first cut, and §0.1's table is the hand read on top of it.
