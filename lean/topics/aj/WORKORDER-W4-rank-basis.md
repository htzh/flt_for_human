# WORKORDER W4 — the rank / freeness premise

Execution order for [PLAN-W4-rank-basis.md](PLAN-W4-rank-basis.md), whose §1–§8 are the
specification: this file fixes ownership, the pin references, the order, and the discipline. Pin
`anthropics/fermats-last-theorem@aa2d8b34`, local clone `/home/haitao/proj/fermats-last-theorem`; port
mathlib `v4.34.0`. Parent
[../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md) §1, §9.2, §10.4, §12.1.

Measured on the 21-node slice with `frontier` and `port_plan`: 6,016 raw pin lines; 5,490 declaration
lines, −179 duplicate copies, −260 already in the port (239 diffed + 21 registered-only) ⇒ **5,051 net
new math lines** inside ≈5,577 lines written (the other 526 are imports, attributes and `p2m_`). The tool
finds **no sibling pair** — the general/instance reductions below are real work, not duplications — and
no new `Definitions/Def_*` transcription (§5).

**Roles.** The manager owns the `Definitions/Def_*` layer (§5), every homing decision and module refactor,
the `spec-pin:` wiring and `PORT_FILES` deletions (§8), `dedup.py`/`move_dead.py` and the name-token
sweep after each module closes, the axioms probe and the re-measurement. An implementer owns the
statement transcription, the proof body, the single-module build and the blocker report — and leaves
wiring and cleanup to the manager; "this module cannot host that declaration" is a homing finding to
report, not a licence to move it.

## 1. What this wave owns — 21 nodes

Group letters are checkpoints, not a reading order (the reading order is §2). "lines" is the pin's own
declaration span. Homes are fixed; do not rename.

| group | node | lines | home |
|---|---|---:|---|
| A1 | `AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable` | 20 | `AlgebraicCurve/IsCurveOver/Transcendental.lean` |
| A1 | `AlgebraicCurve.RationalFunctionField.deg_ne_zero` | 30 | `AlgebraicCurve/Genus/RatFunc.lean` |
| A2 | `AlgebraicCurve.Place.deg_ne_zero_of_finiteDimensional_adjoin` | 53 | `AlgebraicCurve/Genus/Index.lean` |
| A2 | `AlgebraicCurve.Place.ord_sub_one_le_ordDiff_D_of_perfectField` | 181 | `AlgebraicCurve/Genus/DegreeIdentity.lean` |
| A3 | `AlgebraicCurve.Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois` | 778 | `AlgebraicCurve/Genus/DegreeIdentity.lean` |
| A3 | `AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable` | 418 | `AlgebraicCurve/Genus/DegreeIdentity.lean` |
| A4 | `AlgebraicCurve.sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable` | 76 | `AlgebraicCurve/Genus/DegreeIdentity.lean` |
| R | `AlgebraicCurve.Place.exists_of_orderMap` | 169 | `AlgebraicCurve/Place/ValueDictionary.lean` |
| R | `AlgebraicCurve.Place.exists_ord_eq_one` | 8 | `AlgebraicCurve/Place/OrdCalculus.lean` |
| R | `AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch` | 16 | `AlgebraicCurve/Canonical/PolarDifferentials.lean` |
| C1a | `ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq` | 552 | `ModularCurve/Period/ParabolicHomsBasis.lean` |
| C1b | `ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal` | 416 | `ModularCurve/Period/ParabolicHomsBasis.lean` |
| C2 | `ModularCurve.LevelN.exists_linearMap_regularDifferentials_mdifferentiable` | 813 | `ModularCurve/LevelN/Differentials.lean` (new) |
| C2 | `ModularCurve.LevelN.isZeroAtImInfty_slash_of_mem_regularDifferentials` | 870 | same |
| C2 | `ModularCurve.LevelN.exists_linearMap_regularDifferentials_cuspForm_injective` | 101 | same |
| C3 | `ModularCurve.eq_zero_of_forall_re_periodOf_eq_zero` | 310 | `ModularCurve/Period/PeriodLatticeRank.lean` (new) |
| C4 | `ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup` | 267 | `ModularCurve/Period/PeriodLatticeBasis.lean` (new) |
| B1 | `ModularCurve.LevelN.twelve_mul_add_mul_index_le_genusFF` | 597 | `ModularCurve/LevelN/GenusFF.lean` (new) |
| B2 | `ModularCurve.twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma` | 167 | `ModularCurve/LevelN/GenusFF.lean` |
| B3 | `ModularCurve.finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm` | 134 | `ModularCurve/Period/ParabolicHomsBasis.lean` |
| B4 | `ModularCurve.finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup` | 40 | `ModularCurve/Period/ParabolicHomsBasis.lean` |

Each node is public at the pin's name. Its `Theorems/` wrapper and its `P2M/Sol/S_<same stem>.lean` proof
file are the two `spec-pin:` sources — the stems are exactly the node's name with `.` written `_`.

## 2. Order — measured from the pin's own imports

The pin files import each other, and the order that matters is theirs, not the plan's sketch. What the
imports force: `twelve_mul_add_mul_index_le_genusFF` imports the **whole** A block, not only A1;
`twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma` imports the differential **injectivity**, so C2
precedes B2; `_of_le_of_normal` imports the nondegeneracy, so C3 precedes C1b; and the differential pair
imports `Place.exists_of_orderMap`, so R precedes C2. Everything else has no in-slice premise (its pin
file imports only `Definitions/Def_*`).

```
M    (manager) §5: definition layer verified, homes fixed, nothing to transcribe
A1   isCurveOver (20), RationalFunctionField.deg_ne_zero (30)          → green
R    exists_of_orderMap (169), exists_ord_eq_one (8), degree_canonical (16) → green
A2   Place.deg_ne_zero (53), ord_sub_one (181)                         → green
A3   ord_restrictAlong (778), sum_ordDiff_D (418)                      → green
A4   sum_ord_sub_one (76)                                              → green   [unblocks B1]
C1a  six_mul_level (552)                                               → green
C2   the differential trio (813, 870, 101)                            → green   [unblocks B2]
C3   eq_zero_of_forall_re (310)                                        → green
C1b  _of_le_of_normal (416)                                            → green   [unblocks B4]
B1   twelve_mul…genusFF (597)                                          → green
B2   twelve_mul…finrank (167)                                          → green
B3   finrank_parabolicHoms_Gamma (134)                                 → green
B4   the general bound (40)                                            → green
C4   the target (267)                                                  → green
```

Two writers: **implementer 1** owns A, R and C (in the order above); **implementer 2** owns B, starting
at B1 once A4 is green. Implementer 1 reaches C2 before B2 is due and C1b before B4 is due; B3 also waits
on C1a. C4 is one writer's (implementer 1) and opens only after B4.

Report at **A4, C2, B4, C4** — one short message each — and immediately on a blocker (§7). The manager
does not poll.

### 2b. Write these once — `port_plan`'s factoring units

Declarations shared by an identical set of the wave's files, with the lines already in the port. Write
each block once, in the module that hosts its group; do not re-derive it per file.

| group | block (once / already in port) | declarations |
|---|---|---|
| A3 | 199 / 62 | `restrictAlong_comp` 97, `mem_of_ord_nonneg` 62, `finiteAlong_of_finiteDimensional_adjoin` 25, `isIntegral_of_finiteAlong` 15 — all private helpers of the `ord_restrictAlong` file; `mem_of_ord_nonneg` is the pin's 35-file variant, take this binder set |
| A3 | 50 / 50 | `degree_eq_sum_support` is already public in `Genus/Index.lean:70` and used there (`Divisor.degree_nonneg_of_nonneg`) — import it, do not move it |
| C2 | 131 / 108 | the LevelN preamble (§3) — import it |
| C2 | 89 / 25 | `algebraMap_ne_zero` 26, `exists_analyticAt_eventuallyEq` 15, `eq_zero_or_eq_zero_of_mul_eq_zero` 12, `cross_mul_eq` 11, `differentiableAt_up` 6, `mul_ne_zero_of_mem` 5 — one home for both differential files |
| C1b | 50 / 0 | `lift` 45, `conj_mem` 5 |
| C1b, C3 | 41 / 41 | the derivative pair (§3) — import it (B2's file has no `hasDerivAt*` at all) |
| all | 79 / 79 | the `BaseChangeGalois` + `DivisorClassGroup` def blocks — already ported |

## 3. Already landed — import, do not re-prove

* **LevelN preamble.** 108 of the C2 block's 131 lines are already public in
  `ModularCurve/LevelN/{FieldGalois,Places,Prelude}.lean`: `Gpm`, `up`, `𝕌`, `isOpen_𝕌`,
  `isPreconnected_𝕌`, `analyticOnNhd_up`, `differentiableAt_up`, `up_eq_zero_iff`, `slash_two_apply`,
  `apply_smul_of_mem`, `precomp_mem`, `mem_Gpm_of_mem`, `neg_mem_Gpm`, `neg_one_mem_Gpm`,
  `vecMul_ne_zero`, `exists_of_mem_Gpm`, `AnalyticPlaces.moeb`, `AnalyticPlaces.moeb_denom_ne_zero`,
  `AnalyticPlaces.hasDerivAt_moeb`, `jAnalytic_smul`, `periodic_of_mem`.
  `ModularCurve.LevelN.slash_eq_self_of_mem_Gamma_of_mul_eq` is public in `FieldGalois` (C2's third node
  imports it).
* **The derivative pair.** `HeckeEis.hasDerivAt_smul_ofComplex` and `HeckeEis.hasDerivAt_comp_smul` are
  public in `ModularForms/EichlerShimura/EichlerIntegral.lean`; their 41 lines in B2 and C3's files are
  already in the port. Do not transcribe the private copies in `ExistsEquivariantPrimitive.lean`.
* **The W2 period layer.** `finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one`,
  `exists_basis_parabolicHoms_of_isAddTorsionFree`, `periodMapOf_mem_parabolicHoms`,
  `periodMapOf_apply_eq_periodOf`, `exists_hasEquivariantPrimitiveOf`,
  `periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf` — public, imported by B and C4.
* **The `IsCurveOver` constructor.** `AlgebraicCurve.isCurveOver_of_transcendental` is public in
  `IsCurveOver/Transcendental.lean:42` and has A1's statement up to binder spelling; A1's node is a
  one-line alias of it (the pin's own proof is `exact AlgebraicCurve.isCurveOver_of_transcendental …`).
  `…_of_perfectField` is the same file's other public declaration. Do not re-derive the body, and do not
  put the alias in `IsCurveOver/SeparatingTranscendental.lean`: that module is a `Defs`-only leaf below
  the constructor in the import order, and importing the constructor there is a cycle.
* **Ported def nodes.** `degree_smul` and `smul_single` are in `AlgebraicCurve/Defs/SemilinearAut.lean`;
  `PolarFinrank.degree_canonical_eq` in `AlgebraicCurve/Canonical/PolarDifferentials.lean`; `H1` is
  `CohCarrier.H1`; `fricke` and `ring` are `WLight.fricke` / `WLight.LevelGens.ring`.

## 4. Decisions already taken — do not re-litigate

* **D1** pinned statements verbatim; headlines public at the pin's names; helpers `private` unless two
  modules need them. Inside a namespace, keep the pin's qualified spellings in statements — the wire
  compares text.
* **D2** the general/instance pair (40 vs 134) is not a duplicate, and `port_plan` agrees: no sibling
  pairs in the slice. Port both; the 40-line proof reduces through `_of_le_of_normal` and
  `six_mul_level_…`.
* **D3** drop the wrapper's ~300 `attribute [-instance]` / `[-simp]` entries. Prefer a local
  `include`/`omit` or an explicit instance argument, record which lemma needed which, and never reinstate
  a global wall.
* **D4** the pin writes one lemma several ways (`T_pow_mem_Gamma` 11 files, `mem_of_ord_nonneg` 35 files,
  `Φ_apply` 7, `fricke` 11, `moeb` 3). Take the *general* file's binders and write each once, in the home
  its group's module already has; do not add a second spelling.
* **D5** the pin's rank number is not in the statement. Prove the statement, and in C4 also derive
  `finrank ℤ periodLatticeOf = 2 * finrank ℂ (CuspForm Γ 2)` from ℝ-linear independence plus span-top.
* **D6 — one import boundary keeps one duplicate.** `RationalFunctionField.deg_ne_zero` is public in
  `Genus/RatFunc.lean`; `Genus/Index.lean` cannot import it (`RatFunc` → `Stichtenoth` → `Index`), so
  Index keeps a private, line-identical copy for `deg_ne_zero_of_finiteDimensional_adjoin` (its docstring
  records the boundary). Do not promote the copy to the pin name — a `K(X)`-place fact is not Index's
  subject — and do not re-home the public node below Index: that costs the wiring of a fourteen-node
  foundational module, more than the 26 lines it saves. Same boundary the derivative pair takes.

## 5. The definition layer (manager, before the proof bodies)

The slice pulls eleven `Definitions/Def_*` files (`PeriodOf`, `PeriodMap`, `LevelNFunctionField`,
`Differentials`, `IsCurveOver`, `BaseChangeGalois`, `Correspondence`, `DivisorClassGroup`, `Repartitions`,
`RegularDifferentials`, `RiemannRochRows`). Their declarations are in the port; the one gap this wave
fills is `Def_AlgebraicCurve_Differentials`' four thin pin-named spellings (`uniformizer_alt`,
`ord_uniformizer_alt`, `ordDiff`, `ordDiff_def`) in `Differential/Coefficient.lean:139-155`, which alias
the port's `Place.uniformizer` and `Place.diffCoeff` (the pin carries both spellings: `ordDifferential`
is `Defs/CanonicalDivisor.lean:121`). No other Def-node transcription is expected; each touched
module's wire is what proves it.

The manager does, once, before A1:

* verify the seven binder-only matches the tool flags (`Φ`, `deg_eq_one_of_isAlgClosed`, `H1`,
  `differentiableAt_up`, `fricke`, `ring`, `Gpm`) against the pin text and record which module each is
  imported from;
* note that the pin's `Φ : regularDifferentials … → CuspForm … 2` has **no** port counterpart — the three
  `Φ`s in `ModularForms/WeightOne/` and `PeterssonHecke.lean` are unrelated — so C2 writes it in
  `LevelN/Differentials.lean`, publicly (its two lemma companions go beside it);
* keep `moeb` as two private spellings and the derivative pair duplicated (D1, §3), and leave the
  promotions of `LevelN/FieldGalois.lean` and `LevelN/Places.lean` alone.

`Cusp`, `instFintypeCusp` and `width` are pin declarations *inside* C1a's 552-line `S_` file — they do not
occur in B1's 597-line file — not `Def_` nodes: that module writes them as `private` copies with the pin's
names, where they coincide with `RankBound.Orbit`/`RankBound.period`; the two copies are the pin's shape and
stay. Nothing of that tail belongs in `LevelN/GenusFF.lean`.

## 6. Build discipline

* Work from `lean/`. Never a tree build. One module at a time:
  `timeout 110 lake build FLTForHuman.<Module> > tmp/w4-<module>.log 2>&1; tail -20 tmp/w4-<module>.log`
* Fix warnings; do not suppress them. No `sorry`, no `axiom`, no `native_decide`, no
  `attribute [-instance]` / `[-simp]` walls.
* Import, do not transcribe (§3). A build over ~110 s, or a module growing past ~40 s, is a stop-and-report.
* New modules import only `FLTForHuman` modules and mathlib; `Differentials.lean`,
  `GenusFF.lean` and `PeriodLatticeRank.lean` must not import each other except
  `PeriodLatticeRank` importing the two.
* No random tokens in names: declarations carry the pin's names, namespaces the pin's namespaces.

## 7. Blocker protocol

Report immediately, do not work around silently, when:

* a pin statement does not elaborate against mathlib `v4.34.0` after two attempts (deprecated aliases are
  the expected friction — check the port's own use first);
* a statement needs a hypothesis the pin does not have, or the pin's statement has one the port's
  hypotheses cannot supply;
* a proof needs one of D3's dropped attributes;
* a premise you were told is landed (§3) turns out not to be importable — say which name and module;
* a build exceeds 110 s or a target module grows past ~40 s.

A blocker report is: the headline, the exact goal state, the two things tried, and the options. Never
weaken or re-spell a pinned statement to get past a blocker; the `spec-pin:` wire is the contract.

## 8. Wiring and the legacy-module standard (manager)

The manager wires every module a checkpoint closes: one `spec-pin:` pair per node in the header — the
`Theorems/` wrapper **and** the `P2M/Sol/S_` file with `-- comparable copy` — then:

* `python3 spec/check_port.py FLTForHuman/<path> --force` → `0 mismatch / 0 missing / 0 own`;
* `AlgebraicCurve/Genus/Index.lean` and `AlgebraicCurve/IsCurveOver/Transcendental.lean` are in
  `spec/old_check_stmts.py`'s `PORT_FILES` today: delete those lines when the module is wired
  (`SeparatingTranscendental.lean` is not touched by this wave and keeps its line);
* both are also **unwired** today (0 `spec-pin`), so touching them means bringing them up to standard:
  wire, silent build, no build-time blow-up, `dedup.py` then `move_dead.py`, no random tokens;
* `ModularCurve/Period/ParabolicHomsBasis.lean` and `AlgebraicCurve/Genus/DegreeIdentity.lean` are already
  wired (3 ok each): re-run their `check_port` after the additions.

## 9. Verification before calling the wave green

* every module: `spec-pin` per node, `check_port --force` clean, single-module build silent;
* `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all 21 nodes, from one scratch module;
* `tools/deps/dedup.py` on the new and touched modules after they close, then `tools/deps/move_dead.py`
  (`--select dead` must read 0; if it does not, report the declaration rather than shelving it). Its
  token scanner covers lowercase Greek only, so a chain named `Φ`/`Φ_…` reads dead however live it is —
  verify a dead set against the file before believing it (`PeriodLatticeRank`'s eight "dead" declarations
  are all referenced from `exp_F_const`);
* the two `Place` roots are pin-side roots, so `move_dead` will see nothing: do **not** shelve them;
* re-measure, in this order: `needed(302)` should read **134 nodes / 48,880** and `needed(653)`
  **134 nodes / 49,364 with one unported direct premise**. If either is off, the difference is the finding.

## 10. Out of scope

W4a (the winding/smoothed cluster), the injectivity mouth (302), A's row-2 reciprocity, anything in
`Reserve/`, and any change to the bodies of `ModularCurve/LevelN/{FieldGalois,Places,Prelude}.lean` or
`ModularForms/EichlerShimura/EichlerIntegral.lean` — import them, do not edit them.
