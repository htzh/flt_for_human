# Phantom landings — the Γ₀(3) and ν₃ blocks lifted out of `EisensteinChiNegThree.lean`, and the class behind them

**Status: landed 2026-10-20** (no tree build: the dependent wave is owed, see §6). Two blocks that the
port was carrying `private` inside a modular-forms module became **two public modules**, and two more
statements there became public in place. Checker **3,654 → 3,718 ok / 143 → 146 wired modules**, 0
mismatch / 0 missing / 11 own / 0 kw; the frozen registry is **one entry smaller** (582 → 581 exempt).
Tier-0/1 only: the two new modules (4 s and 3 s) and the edited host (26 s) are green with 0 warnings;
the 51-module dependent wave was **not** run, by instruction (that is the price paid for doing several
of these refactors before one wave).

| module | lines | public | checker | build |
|---|---:|---:|---|---|
| `NumberTheory/ModularForms/Gamma0Three.lean` (new) | 268 | 40 | 40 ok | 3,111 jobs, 3.0 s |
| `ModularCurve/Numerics/NuThree.lean` (new) | 246 | 21 | 21 ok | 3,111 jobs, 3.9 s |
| `ModularForms/WeightOne/EisensteinChiNegThree.lean` (edited) | 3,392 (−430) | 3 (was 1) | 3 ok | 3,944 jobs, 26 s |

## 1. The diagnosis

`EisensteinChiNegThree.lean` is not a module of the port; it is the port of a **composite pin `S_`
file**. `S_EisensteinWeightOne_e1Chi3IsModular.lean` is thirteen `section File_FLT_*` blobs
concatenated — `LatticeSumPlumbing`, `RankTwoPoissonSummation`, `TwoGeneratorSweep`,
`EisensteinModularityAssembly`, `ThetaHolomorphy`, `RepresentationNumberIdentity`,
`ModularCurve_Numerics_NuThree`, `SplittingLawHalf`, `OrbitCountMultiplicative`,
`CountIdentification`, `SplitPrimePowCount`, `E1Chi3Modular`, and its own subject — and those
`File_*` markers are the **pin's own module boundaries**. The port landed one `S_` file as one module
and, under the protocol of that era ("one headline public, every helper `private`"), privated
everything else. The registry entry said so verbatim: *"The single headline is public; the pin's
~400 helpers are all `private` here."*

Nothing was wrong by the rules of the time. The rules could not distinguish **a helper of this
headline** from **another pin module's public surface**, so two other modules' developments went
private along with the helpers:

* `FLT.AnalyticCore.Gamma0Three` — 40 declarations (the Schreier/transversal engine, `U₃`, `gens`,
  the two closure theorems). The pin writes this development into **five** `S_` files.
* `ModularCurve.Numerics` — 22 declarations (`ν₃`, prime case, multiplicativity, small values).

## 2. The Γ₀(3) block was a pure relocation

The pin's own file and the port's private block were compared declaration by declaration: 41 pin
declarations (39 real + `solution` + one `scoped instance`), 40 port declarations, and the set
difference was **only the instance's name** (`fact_prime_three_A2` → the port's
`fact_prime_three_twoGenSweep`). Thirty-five were already byte-identical per `port_advise`. So no
proof was written: the block was moved, made public, its pin attributes restored (`@[scoped simp]` on
seven `rfl`-lemmas and `scoped instance` on the `Fact (Nat.Prime 3)`, which the port had flattened to
global `@[simp]` / `instance` — a simp-set pollution, not a statement change), the pin's two
concatenation `namespace Gamma0Three` blocks merged into one, and the headline stated once:

```lean
theorem CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three (U : SL(2, ℤ))
    (hU : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -3, 1]) :
    Subgroup.closure ({ModularGroup.T, U, -1} : Set SL(2, ℤ)) = CongruenceSubgroup.Gamma0 3
```

Checker: **40 ok, 0 mismatch, 0 missing** on the first run — including the headline against the
`Theorems/` wrapper and the renamed instance through the content-hash tier.

## 3. The ν₃ block, and two headlines that were invisible

The same move for `section File_FLT_ModularCurve_Numerics_NuThree` (22 declarations, 216 lines,
self-contained: zero references to the rest of the host). Its two pin headlines —
`ModularCurve.nuThree_prime` and `ModularCurve.nuThree_mul_of_coprime` — keep their pin names, so no
statement was restated; `private` was simply dropped. Checker **21 ok, 0 mismatch, 0 missing**.

Two further statements stayed in the host and became **public in place**, because their subject *is*
this module's: `FLT.EisensteinWeightOne.chiNegThree_mul` and `FLT.EisensteinWeightOne.coeff_e1Chi3`.
Their wrappers' statements spell the coefficients differently from the `S_` files
(`(PowerSeries.coeff n) EisensteinWeightOne.e1Chi3` against `PowerSeries.coeff n e1Chi3`), so the
`spec-pin:` wire lists the `S_` files too, wrapper first — the checker's own hint names them.

The host is therefore **migrated off the frozen registry**: six `spec-pin:` lines in its header (three
wrappers, three `S_` files), `PORT_FILES` entry out, per the playbook's migration rule ("a module moves
when it is edited for another reason"). Its three publics check `ok`; its remaining ~400 helpers stay
`private`, as they are helpers of that headline.

## 4. The class behind it, measured

`frontier.py`'s `names` tier scans the port for declaration names and **does not exclude `private`**,
so a private declaration satisfies "ported". For the nodes above that was invisible only by accident
(the private copy carried the *inner* name `closure_T_U_neg_one_eq`, a different last name from the
node's); `ModularCurve.nuThree_prime` and `nuThree_mul_of_coprime` had the same last names, and
`frontier.py --target` answered **"target is ported", `needed 0`** for both, while nothing importable
stated them and no checker had diffed them.

That is a class, so it was sized. A new local tool (`tools/deps/phantom_scan.py`, untracked — the
method is reproducible from this section) parses every port module with `spec/statement_db.parse_file`,
and matches each `private` declaration's statement hash against the public declarations of the pin's
`Theorems/` files (29,512 of them). Over the whole port — 856 modules, 23,096 declarations, 6,357 of
them `private` — it finds **52 private declarations whose statement is a pin headline**, in 36
modules, in two classes:

* **`orphan` — 23, in 14 modules.** No public declaration anywhere in the port states the theorem. The
  pin node is "ported" only because a `private` name matches. **This is the defect class.**
* **`twin` — 29.** A public declaration elsewhere states the same theorem under another name — the
  pin's own `solution` wrapper shape (`theorem H := impl`, `private theorem impl : <H's statement>`).
  Benign; it is how the port wires a headline over a private body, and it is what `Saturation.main` is.

The 23 orphans (module:line — pin node):

```
Algebra/FaithfulLatticeEigenvector.lean:98                          Module.exists_ne_zero_forall_smul_eq_smul_of_algHom
AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean:386                AlgebraicCurve.existsUnique_pDigits_of_transcendental
AlgebraicCurve/P1/DivisorAction.lean:21                             AlgebraicCurve.Place.ord_add_eq_of_lt
AlgebraicCurve/WeilExchange/Transport.lean:293                      AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg
ModularCurve/Analytic/Gamma0InvariantCore.lean:116                  ModularCurve.PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq
ModularCurve/Analytic/Gamma0InvariantCore.lean:133                  ModularCurve.PhiGen.exists_galoisPerm
ModularCurve/Analytic/Gamma0InvariantCore.lean:153                  ModularCurve.PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter
ModularCurve/Degree/Roof.lean:61                                    ModularCurve.finrankAlong_heckeBetaBar
ModularCurve/Degree/Roof.lean:140                                   ModularCurve.finrankAlong_towerInclBar_of_eq
ModularCurve/Degree/Roof.lean:150                                   ModularCurve.finrankAlong_towerSubstBar_roof
ModularCurve/Degree/Roof.lean:220                                   ModularCurve.laurentBaseChange_adjoin_pair
ModularCurve/ModularPolynomialStarBank.lean:82                      ModularCurve.coeff_jqModC_pow_self
ModularCurve/ModularPolynomialStarBank.lean:88                      ModularCurve.coeff_jqModC_pow_of_lt
ModularCurve/ModularPolynomialStarBank.lean:93                      ModularCurve.coeff_jqModC_neg_one
ModularCurve/PhiGenIntegrality.lean:232                             ModularCurve.PhiGen.intCoeffs_jq_pow
ModularCurve/PhiGenPoleBounds.lean:270                              ModularCurve.PhiGen.tPoleOrderLE_phiProd_conj_of_ne_zero
ModularCurve/X0/FunctionFieldFull.lean:82                           ModularCurve.coeff_jqModC_pow_self
ModularCurve/X0/FunctionFieldFull.lean:88                           ModularCurve.coeff_jqModC_pow_of_lt
ModularCurve/X0/FunctionFieldFull.lean:93                           ModularCurve.coeff_jqModC_neg_one
ModularCurve/X1/IntegralityJqNModC.lean:89                          ModularCurve.qExpansion_E6_eq_map_mk
ModularForms/Hauptmodul.lean:342                                    ModularCurve.exists_aeval_jq_sub_holomorphicAtInfty
ModularForms/JqAnalyticModel.lean:570                               ModularCurve.hasSum_jNum_qParam
WeierstrassCurve/IsogenyEndDatum/DualEndData.lean:63                 WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero
```

Three readings of that table:

* it is **not random**: 16 of the 23 are the `ModularCurve` q-expansion / `PhiGen` / degree layer, and
  the three `coeff_jqModC_*` are privated **twice** (`ModularPolynomialStarBank` and
  `X0/FunctionFieldFull`) — a dedup case on top of a phantom;
* they are landings the column's own record lists as done (`PORTING-DeligneSerre.md` §1 names
  `qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental`, `eisenstein4_cube_sub_mk_sq`,
  `exists_modEq_and_modEq_and_isCoprime`, …) — the mathematics is there, but nothing can import it and
  no checker diffed it;
* so the demand's `needed` is understated, and every cut priced off `frontier.py` inherits the error.

The fix pattern is the one this log is an instance of: give each orphan a **public home in its own
subject module**, `private` → public where the statement is the module's own subject, or a lift into a
new module where it is not — then one dependent wave for all of them.

## 5. Two decisions recorded, not taken

* **`frontier.py` is not changed here.** Making the `names` tier ignore `private` would move every
  number in the column's notes (the 23 orphans would re-enter the demand, and so would any older
  phantom outside this scan's reach) and needs its own pass and its own record. The class is now
  measurable with `tools/deps/phantom_scan.py`, and the orphans are in
  [CARRY-FORWARD.md](../CARRY-FORWARD.md).
* **The pin's `solution`/`_impl` shape stays.** The 29 `twin` hits are the port's normal headline
  wiring, not a defect; the tool keeps them in a separate class so a future pass does not "fix" them.

## 6. Owed: the dependent wave

The host's olean changed, so its **51-module / 30,597-line** dependent cascade is stale (≈413 s to
re-elaborate, `build_ladder.py --edit`). By instruction it was not built: more old modules are
expected to be refactored first, and each such refactor pays the same wave. The stale-olean fact is
recorded in [build-time-issues.md](build-time-issues.md); nothing is red (a `private` declaration is
file-local, and the host's interface only *gained* two public names, so no importer can be affected).

## 7. Residuals

* **`ModularCurve.nuThree` is a definition of the pin's `Definitions/Def_ModularCurve_GenusNumerics`**
  (`noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}`). The port has
  no home for that definition module, so `Numerics/NuThree.lean` defines it. When the definition
  module lands, `nuThree` must move there and this module import it — recorded in the module header.
* **The host is still a composite.** Its other eleven `File_FLT_*` sections are *support* silos: no
  `Theorems/` wrapper declares anything in them (checked), so privating them is right and they are not
  demand nodes. The two that were demand surfaces are the two that moved.
* **`FLT.` prefixes are kept** (the pin's namespace, house style for this family), which is why the
  checker prints `FLT.EisensteinWeightOne.chiNegThree_mul`; the parser also shows a repeated
  `FLT.FLT.FLT.FLT.` prefix for the headline, an artefact of the host's nested `namespace FLT`
  re-openings that does not affect matching.
