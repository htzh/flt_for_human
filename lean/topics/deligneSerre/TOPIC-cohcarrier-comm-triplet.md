# The `CohCarrier` Hecke–diamond commutativity triplet — math, measurements, port state

The Deligne–Serre frontier's `--include-leaves` view surfaces three graph leaves at the
bottom of the `CohCarrier` layer, each priced at a whole ~1000-line pin file:

| node | own `S_` lines | `used_by` (cone / project) |
|---|---:|---:|
| `CohCarrier.heckeT_diamondRaw_comm` | 999 | 1 / 14 |
| `CohCarrier.heckeT_comm_of_prime` | 998 | 1 / 37 |
| `CohCarrier.diamondRaw_comm` | 998 | 1 / 4 |

This note is the handoff record: §1 the mathematics, §2 the files and how they relate,
§3 the measurements (already taken — do not re-run), §4 the definition layer that is the
manager's own ground, §5 the cut plan, §6 the landed state of the port work (the
definition layer is green; the two Lean-adaptation obstructions of the handoff are fixed),
§7 the `v4.34.0` API deviations that will bite every module of this cluster, §8 what not
to do, §9 reproduce. Column record: [PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md)
§1/§7.

## 1. The mathematics

For `M ∈ ℕ`, `H ≤ (ℤ/Mℤ)^×`, `V` an abelian group:

* `H1 M H V` is `Additive ↥(GammaH M H) →+ V` — the group cohomology `H¹` of `Γ_H(M)`
  with trivial coefficients, as additive homomorphisms of `Γ_H(M)`. Homed in
  `FLTForHuman/ModularForms/Defs/GammaH.lean`.
* `diamondRaw M H V σ` is precomposition with conjugation by `σ ∈ Γ₀(M)` (the *raw*
  diamond action, before any nebentypus normalisation).
* `heckeT M H ℓ V` is the transfer along `Γ_HUpper(M,ℓ) = Γ⁰(ℓ) ∩ Γ_H(M) ↪ Γ_H(M)`
  composed with `conjL`, the conjugation by the upper-triangular `diag`-type matrix
  recorded by `conjUpperMat`.

The three headlines are the three pairwise commutations of that family with itself:

* `DiamondRaw_comm` — `diamondRaw σ (diamondRaw σ' F) = diamondRaw σ' (diamondRaw σ F)`;
  conjugation actions commute (both are `F ↦ F ∘ conj`, and the conjugations commute in
  `Γ_H(M)` up to an element of `Γ_H(M)`).
* `heckeT_comm_of_prime` — `heckeT ℓ (heckeT ℓ' F) = heckeT ℓ' (heckeT ℓ F)` for `ℓ`
  prime and `Nat.Coprime ℓ ℓ'`.
* `heckeT_diamondRaw_comm` — `heckeT ℓ (diamondRaw σ F) = diamondRaw σ (heckeT ℓ F)`
  under the divisibility `(ℓ*M : ℤ) ∣ σ₁₀`, which is exactly what makes conjugation by
  `σ` respect the chosen `ℓ`-coset data.

These are what let the Hecke and diamond operators be treated as one commutative family
on `H¹`. The three nodes have 55 project consumers between them — `CohCarrier.opFamily_comm`,
`CohCarrier.heckeDiamondRing.exists_ringHom_ker_eq_eigenvector`,
`CohCarrier.exists_galoisModule_parabolicHoms_to_dual_charInvolution_frobenius`,
the `CuspForm.TWLevel.*` "free over `𝒪[Δ_Q]`" rows (`exists_basis_ML_monoidAlgebra_and_linearMap_ML_auxLevel_of_charpoly_frobenius_eq`,
`exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq`, `toML_diamondL_eq_toML`),
`CuspForm.AuxLevel.toML_diamondRaw_eq_toML`,
`ModularCurve.nonempty_basis_fin_two_rationalTateModule_jH`,
`CuspForm.exists_padicGaloisModule_heckeRingH_two_frobenius_relation`,
`CuspForm.span_setOf_forall_heckeRingH_qCoeff_intCast_eq_top`. Landing the triplet clears
three nodes at the bottom of the Taylor–Wiles / Eichler–Shimura stack at once.

## 2. The pin's files: one development, three headlines

Pin `anthropics/fermats-last-theorem@aa2d8b3`:

* `P2M/Sol/S_CohCarrier_{diamondRaw_comm,heckeT_comm_of_prime,heckeT_diamondRaw_comm}.lean`
  — 998 / 998 / 999 lines, 90 declarations each.
* `Theorems/Thm_CohCarrier_*.lean` — 1 declaration each, the checker's comparable copy.

`diff` after normalising the namespace stem: the three `S_` files are **byte-identical
except the final `solution` theorem**, which differs in 5–6 lines:

| file | `solution` body |
|---|---|
| `S_CohCarrier_diamondRaw_comm` | `IharaSolComm.twoDiamonds_impl M H σ σ' V F` |
| `S_CohCarrier_heckeT_comm_of_prime` | `IharaSolComm.commPrime_impl M H ℓ ℓ' hℓ hcop V F` |
| `S_CohCarrier_heckeT_diamondRaw_comm` | `IharaSolComm.heckeDiamond_impl M H ℓ σ hσ V F` |

**Each file contains all three `_impl`s** (at lines 678 / 944 / 980 of every file); only
its own `solution` picks one. So one deduped development yields all three headlines.

The development's own layout (line ranges in any of the three files):

| lines | namespace / section | content |
|---|---|---|
| 12–97 | `IharaSolRQ` | right-coset/transfer block: `coe_slip`, `cls_rep_mul`, `mulRight`, `toRight`, `secL`, `transL`, `toAdditiveLeft_transfer_apply`, `heckeT_apply_eq_sum_rq` |
| 101–300 | `IharaSolComm.HeckeFamily` | the abstract `HeckeFamily` structure `(K, δ, act, η)` with `T`, `T_comp`, `act_eq_of_sameCosets`, `T_eq_of_sameCosets`, `T_comm_of_sameCosets`, `Distinct`, `ofDistinct`, `SameCosetsComm` |
| 303–434 | `IharaSolComm` (`DockHeckeT`) | `ιQ`, `ιΓ`, `alpha`, `famT`, `heckeT_eq_famT` — the `Γ_H(M)` specialisation |
| 437–539 | `CC3` | `αZ`, `comp_famT_distinct`, `heckeT_comm_of_sameCosetsComm` — the `T/T` case |
| 542–558 | `HeckeFamily.sameCosets_of_exhibit` | a coset-exhibiting criterion |
| 561–744 | `Diamond` | `famD`, `diamondRaw_eq_famD`, `diamondRaw_congr`, `sigmaLow`, `sfac`, `gDiaSL`, `gDia`, `heckeDiamond_impl` (73 lines) — the `T`/diamond case |
| 747–815 | `CC3b` | `TwoSidedReduction`, `sameCosetsComm_of_twoSided` |
| 818–951 | `CC3bPrime` | `pMat`, `zMat`, `mem_GammaH_of_entries`, `isCoprime_of_prime_not_dvd`, `twoSidedReduction_of_prime`, `commPrime_impl` |
| 954–986 | `DiamondDiamond` | `diamondRaw_diamondRaw`, `commutator_mem_GammaH`, `twoDiamonds_impl` |

Two tiers: the `HeckeFamily` calculus (generic in `(Γ, G, ι)`; roughly 750 of the 1,828
removable lines) and the `Γ_H(M)` specialisation.

## 3. Measurements (taken; do not re-run)

Commands and outputs (artifacts in `tools/deps/build/`, untracked):

* `python3 tools/deps/port_advise.py -t CohCarrier.heckeT_diamondRaw_comm -t CohCarrier.heckeT_comm_of_prime -t CohCarrier.diamondRaw_comm --json build/coh_3_advise.json`
  → **76 names proved in all 3 files, 1,828 removable lines**, every pair factors at
  `914 lines / 76 proofs`.
* `python3 tools/deps/port_plan.py --json build/coh_3_advise.json`
  → `raw S_ lines 2995 · duplicate copies 1950 · boilerplate 51 · NET NEW MATH LINES 994
  · 92 declaration groups`; `once 914 / decls 76 / files 3`; `layers: all three layer 0`
  (no import between them); `siblings: none`.
* The same two tools over **all twelve** `needed` `CohCarrier` nodes (4,608 raw `S_`
  lines) report exactly one shared block — this triplet's. The other nine nodes are
  independent stories, including the two `--ready` rows
  (`exists_bottomRow_eq_and_torsionOrbit_bottomRow_eq_iff` 300 lines,
  `exists_surjective_doubleCoset_gammaH_zpowers_of_addOrderOf_eq` 252 lines).
* Neighbours, all **outside** the D-S demand:
  * an 8-file family (`CohCarrier_heckeSym_top`, `…_of_coprime`,
    `CohCarrier_heckeT_apply_eq_sumEquiv`, `…_comp_coeff`, `…_iDeg_{interchange,
    one_comm_of_dvd, q_eq_smul, q_eq_smul_r}`, namespace `IharaMintRQ`) sharing a
    **66-line / 9-declaration** transfer block that the triplet's prelude also contains;
    that family is 2,786 raw → 1,437 net with its own near-twins (192/13, 142/11,
    103/9-quad). Name the shared home family-neutrally; do not port the family now.
  * off-demand `CohCarrier` near-twins by declaration-name overlap:
    `exists_dirichletCharacter_pair_of_not_mem_parabolicHoms_of_heckeT_eq_smul` (89 decls)
    vs `exists_squarefree_aeval_heckeTL_mem_parabolicHoms` (96) share 87 (0.89); then a
    0.65 and a 0.57 pair behind them.
* **No other pin file contains any of the 76 prelude names** (grep over `P2M/`,
  `Theorems/`, `Definitions/`). The triplet is closed.
* `python3 tools/deps/twin_scan.py --node …` on the three: `new=3`, `prelude 1/89` each —
  the port has none of the mathematics under another name.

## 4. The definition layer (the manager's own ground)

All three `S_` files import `Definitions.Def_CohCarrier_Lower`, which imports
`Definitions.Def_CohCarrier_Level`. Neither is a graph node, so `--ready`,
`--include-leaves`, `port_advise` and `port_plan` are all blind to them: this is the
§4(a) trap of the playbook at two modules deep, and it is why the leaves' `needed == 1`
understates their cost.

| pin module | lines | decls | in the port |
|---|---:|---:|---:|
| `Definitions/Def_CohCarrier_Level.lean` | 506 | 53 | 11 (+`H1`) byte-identical in `FLTForHuman/ModularForms/Defs/GammaH.lean` |
| `Definitions/Def_CohCarrier_Lower.lean` | 203 | 27 | none |

`port_advise -t Def_CohCarrier_Level -t Def_CohCarrier_Lower` lists the 11 verbatim hits
(`GammaH`, `gamma0Units`, `val_gamma0Units`, `mem_GammaH_iff`, `GammaH_le_Gamma0`,
`GammaH_top`, `Gamma0_d_mul_a`, `GammaH_normal_in_Gamma0`, `conj_mem_GammaH`, `conjHom`,
`diamondRaw`), ≈92 lines to import rather than re-prove. The rest is ≈617 new lines.

What the triplet actually names from these modules: `heckeT`, `GammaHUpper`,
`conjUpperMat`, `conjL` (Level) and `rep`, `cls`, `slip`, `conjLowerMat` (Lower). The
wrapper's `attribute [-instance] CohCarrier.GammaHLower_finiteIndex` and six
`attribute [-simp] …uMat_apply_* / rightQuotEquivOfDvd_apply / coe_uElt` rows also name
declarations from `Def_CohCarrier_Lower`, so a faithful façade needs them to exist.

Wiring (done): `Definitions/Def_CohCarrier_Level.lean` was already a checker `SOURCES`
entry; `Definitions/Def_CohCarrier_Lower.lean` is appended beside it, and `PORT_FILES`
gained both port modules (§6).

## 5. Cut plan

1. **Definition layer (landed, see §6).** Home the two pin modules whole (§2.3 of the
   playbook): `FLTForHuman/ModularForms/Defs/CohCarrierLevel.lean` ← the remainder of
   `Def_CohCarrier_Level`, then `…/CohCarrierLower.lean` ← `Def_CohCarrier_Lower`. Both
   in namespace `CohCarrier`, importing `ModularForms/Defs/GammaH.lean`. This ground is
   shared by **all twelve** needed `CohCarrier` nodes, not only the triplet. Green and
   wired: checker `9786 → 9854 identical`, 0 mismatched / 0 missing.
2. **The triplet, one set, one subagent (landed, see
   [WORKORDER-CT1-comm-triplet.md](WORKORDER-CT1-comm-triplet.md)).** Engine (tier 3, the
   pin's 90 declarations minus its `solution`, the three `_impl`s included →
   `spec/UNWIRED-PUBLIC.md` registration, the `TateSlots`/`TateCurve` pattern) +
   tier-1 façade with the three headlines. Checker delta **+3** (`9854 → 9857`),
   0 promotions, 0 mismatched / 0 missing.
3. Then the two ready rows (300 + 252 lines), then the remaining `CohCarrier` demand.

## 6. Port state (definition layer and triplet landed 2026-10-17)

Both pin modules are homed whole and green (untracked until the user commits):

* `lean/FLTForHuman/ModularForms/Defs/CohCarrierLevel.lean` — 41 declarations: the
  transfer algebra (`transfer_diff_one`, `transfer_diff_mul`, `transfer_one`,
  `transfer_mul`, `toMultiplicativeRight_{zero,add}`, `toAdditiveLeft_{one,mul}`,
  `coresAdd`, `coresAdd_{zero,add,smul}`), `Gamma0Upper` + `mem_Gamma0Upper`,
  `conjUpperMat` + `conjUpperMat_mul` + the two `_apply` lemmas, `GammaHUpper`,
  `dvd_of_mem_GammaHUpper`, `conjUpperMat_mem`, `conjL`, `Gamma0Upper_isCongruenceSubgroup`,
  `Gamma0Upper_finiteIndex`, `heckeT`, then the level maps `conjLowerMat`,
  `conjLowerMat_mul`, `LevelLE`, `LevelLE.exists_eq`, `LevelLE.dvd_entry`,
  `LevelLE.conjLowerMat_mem`, `iotaDeg`, `iDeg'`, `iDegL`, `conjLowerMat_conjUpperMat`,
  `Gamma_subgroupOf_le_range_iotaDeg`, `iotaDeg_range_finiteIndex`, `iotaDeg_injective`,
  `pushChar`, `jDeg`, `jDegL`.
* `lean/FLTForHuman/ModularForms/Defs/CohCarrierLower.lean` — 27 declarations:
  `rep`, `cls`, `slip`, `uMat` + four `uMat_apply_*`, `uMat_mem_GammaH`,
  `uElt`, `coe_uElt`, `mul_inv_apply_01`, `rightRel_mk_eq_mk_iff`,
  `rightQuotEquivOfDvd`, `rightQuotEquivOfDvd_apply`, `coe_iotaDeg_one`,
  `iotaDeg_one_mem_GammaHUpper_iff`, `πCoset`, `πCoset_mk`, `GammaHLower`,
  `GammaHLower_finiteIndex`, `qM_dvd_of_mem_GammaHLower`, `dvd_of_mem_GammaHLower`,
  `mem_GammaHLower_iff_of_coprime`, `conjLowerMat_mem_of_GammaHLower`, `conjLowerL`,
  `heckeTlower`. Transcription is verbatim; the module compiled **without a proof
  change**, needing only the `linter.style.haveILetI` suppression below.

Both pass `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` with **zero
errors and zero warnings**, and `lake build` produces their `.olean`s. The two
obstructions of the handoff are closed:

* `coresAdd_smul`: the verified fix of `lean/tmp/probe_proof3.lean` is now in the
  module — `apply AddMonoidHom.ext; intro g`, then the two explicit
  `MonoidHom.transfer_def <φ> default (Additive.toMul g)` rewrites, then the
  `simp only` set ending in `Finset.smul_sum, AddMonoidHom.smul_apply`.
* `conjUpperMat_mul`: the pin's plain `simp` still does not unfold the product
  coercion, so the proof now rewrites
  `((conjUpperMat ℓ A hA * conjUpperMat ℓ B hB : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)`
  to the product of the two explicit `!![A 0 0, A 0 1 / ℓ; A 1 0 * ℓ, A 1 1]` matrices
  via `show … from by rw [Matrix.SpecialLinearGroup.coe_mul]; rfl`, then
  `rw [Matrix.mul_apply, Fin.sum_univ_two]`, `fin_cases i <;> fin_cases j <;> simp [conjUpperMat, hmul, h2]`,
  and closes the three residues with `h1.symm`, `ring`, `h3.symm`.
* `conjLowerMat_mul` had the same coercion obstruction (it surfaced once the other
  two were fixed) and takes the same `show … from by rw [coe_mul]; rfl` rewrite and
  the same entrywise close. **Apply this idiom from the start in every later module**
  (`conjLowerL.map_mul'` already goes through the fixed `conjLowerMat_mul`).

### The triplet's port

* `lean/FLTForHuman/ModularForms/CohCarrier/Engine/CommTriplet.lean` — tier 3, unlisted,
  1,022 lines, **89 declarations**: the `IharaSolRQ` right-coset/transfer prelude, the
  abstract `HeckeFamily` calculus, the `Γ_H(M)` specialisation (`ιQ`, `ιΓ`,
  `alpha`, `famT`, `famD`, `sigmaLow`, `gDia`, …) and the three kernels
  `heckeDiamond_impl` / `commPrime_impl` / `twoDiamonds_impl`. Every pin declaration
  except the top-level `solution` is transcribed (the parent note's 90 minus that one);
  all stay public. The ten `p2m_reactivate` calls are dropped and their scoped attributes
  made global instead — `attribute [instance] HeckeFamily.instFintype` and plain
  `@[simp]` on the eighteen entry lemmas (`ιQ_coe_apply`, `ιΓ_coe_apply`,
  `alpha_coe`, `αZ_*`, `sigmaLow_coe`, `gDia_coe`, `pMat_*`, `zMat_*`) — which
  reproduces the pin's post-activation simp set exactly, so no proof needed changing for
  it. One `v4.34.0` adaptation: `Prime.not_unit` → `Prime.not_isUnit`. Green,
  0 warnings.
* `lean/FLTForHuman/ModularForms/CohCarrier/CommTriplet.lean` — tier 1, 46 lines, the
  three headlines, each the one-line application of its kernel, statements taken from the
  `Theorems/` wrappers. `#print axioms` on all three:
  `[propext, Classical.choice, Quot.sound]`.
* Cross-check of the engine against the pin with the checker's own parser, by last name
  and statement: 89/89 match, 0 differences, only `solution` skipped (the façade
  replaces it).
* `spec/UNWIRED-PUBLIC.md` regenerated: the engine is listed with all 89 pin originals
  (the `S_` file is a `SOURCES` entry, so the register's pin-original column is filled).
  The regeneration also absorbed a pre-existing drift, `WeierstrassCurve/Velu/Shift.lean`.

Checker, measured with the four modules wired (`SOURCES` gained
`Definitions/Def_CohCarrier_Lower.lean` beside its sibling, plus the three `Theorems/`
wrappers and the `S_` development of the triplet; `PORT_FILES` gained both definition
modules and the tier-1 façade at the end):

```
9857 statements identical (667 promoted, 83 renamed), 0 mismatched, 0 missing,
42 own-proof declarations exempted (9899 port declarations checked)
```

The definition layer is **+68 identical (41 + 27)**, `9786 → 9854`, 0 promoted / 0
renamed / 0 own: the same run with the two `PORT_FILES` entries removed gives `9786`
(`9828 checked`), so the delta is exactly the two modules' public surface. The façade is
**+3**, `9854 → 9857`, again 0 promoted / 0 renamed. The `PORTING-DeligneSerre.md` §1
figure of 9569 predates other columns' landings; they account for `9569 → 9786`.

## 7. `v4.34.0` API deviations (all verified in this port)

* `MonoidHom.transfer_def` now takes the transversal **before** the group element:
  `transfer_def (ϕ) (T) [FiniteIndex] (g)`; the pin's `transfer_def _ default` must
  become `transfer_def <φ> default (Additive.toMul g)` (and never `_` inside a `simp`
  argument — the metavariable resolves against the goal's outer function).
* `ext` on an `AddMonoidHom` equality may pick the `toMultiplicativeRight` `MulEquiv`
  extensionality, leaving the goal in `Multiplicative` form. Use
  `apply AddMonoidHom.ext; intro g`, and note the pointwise argument is `Additive.toMul g`
  inside `toAdditiveLeft_apply_apply`.
* `Int.add_ediv_of_dvd_right`, `Int.ediv_eq_of_eq_mul_right`, `Int.mul_ediv_assoc`,
  `Int.mul_ediv_cancel'`, `Int.mul_ediv_cancel`, `Finset.smul_sum` all exist (the first
  two live outside `Mathlib/`, so grepping `Mathlib` misses them).
* `Matrix.two_mul_expl a b` has shape `(0,0) ∧ ((0,1) ∧ ((1,0) ∧ (1,1)))`, so `.2.1` is
  the `(0,1)` entry — as the pin assumes.
* `Set.mem_setOf_eq` is deprecated → warnings in `Gamma0Upper`'s two proof blocks; use
  `Set.mem_ofPred_eq` (the port wants 0 warnings).
* The `Subtype.val` vs `instCoeToMatrix` obstruction is **not** special to
  `conjUpperMat_mul`: it is structural. It reappeared at `conjLowerMat_mul` and the same
  `show … from by rw [Matrix.SpecialLinearGroup.coe_mul]; rfl` rewrite fixes it; carry the
  idiom into the triplet's `map_mul'`/entrywise proofs.
* `linter.style.haveILetI` fires on the local `haveI` binders of
  `Gamma0Upper_finiteIndex`, `iotaDeg_range_finiteIndex` and `GammaHLower_finiteIndex`
  (`NeZero` and `FiniteIndex` are `Prop`s, but they are real local instances). They must
  stay instances, so each declaration carries
  `set_option linter.style.haveILetI false in`; turning them into `have`/`let` breaks
  typeclass search.
* `Def_CohCarrier_Lower` needs **no** API adaptation: `Quotient.exact'`,
  `Quotient.inductionOn'`, `Quotient.map'_mk''`, `Quotient.eq''`,
  `Subgroup.fintypeQuotientOfFiniteIndex`, `Matrix.SpecialLinearGroup.coe_inv`,
  `linear_combination` all behave as in the pin.
* `SL(2, ℤ)` needs `open scoped MatrixGroups`.
* The pin's five imports suffice; add `import FLTForHuman.ModularForms.Defs.GammaH`.
  `linear_combination`, `push_cast` and `group` are all available from that set.
* `GammaHLower_finiteIndex` is a global `instance` in the pin and the wrapper disables it;
  the port keeps it a global instance (it is a legitimate low-risk instance) and drops
  the wrapper's `attribute` prelude.

## 8. Do not

* Do not "substitute" `Distinct` or `TwoSidedReduction`: `port_advise`/`port_plan` report
  six `→ PeriodPair.DiscriminantNeZero` matches and label them **suspect**. Both pin
  declarations are bare `Prop`-valued defs (`Distinct : Prop`, `TwoSidedReduction : Prop`)
  and the parser matched them to the port's `PeriodPair.DiscriminantNeZero : Prop`
  (`FLTForHuman/Elliptic/PeriodPair/Basic.lean:83`) by type only. They are different
  mathematics; `port_plan`'s 994 already prices them as new. Importing them would break
  the development at `ofDistinct`/`sameCosetsComm_of_twoSided`.
* Do not price the triplet by `--ready`: as graph leaves they never reach `F`; read them
  off `--include-leaves`, and price the definition layer by hand (§4).
* Do not port the 8-file `IharaMintRQ` family now — out of the D-S demand; only keep the
  shared home's names family-neutral.

## 9. Reproduce

```sh
cd tools/deps
python3 frontier.py --ds --include-leaves --rank-by silo --top 0        # the three rows
python3 port_advise.py -t CohCarrier.heckeT_diamondRaw_comm \
    -t CohCarrier.heckeT_comm_of_prime -t CohCarrier.diamondRaw_comm \
    --json build/coh_3_advise.json
python3 port_plan.py --json build/coh_3_advise.json                      # 994 / 76 / 3 files
python3 port_advise.py -t Def_CohCarrier_Level -t Def_CohCarrier_Lower \
    --json build/coh_defs_advise.json                                    # 11 verbatim hits
cd ../../lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/ModularForms/Defs/CohCarrierLevel.lean                   # ~8-16 s
flock .lake/flt_build.lock timeout 300 lake build \
    FLTForHuman.ModularForms.Defs.CohCarrierLevel                        # background job
flock .lake/flt_build.lock timeout 300 lake build \
    FLTForHuman.ModularForms.Defs.CohCarrierLower                        # background job
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/ModularForms/CohCarrier/Engine/CommTriplet.lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/ModularForms/CohCarrier/CommTriplet.lean
flock .lake/flt_build.lock timeout 300 lake build \
    FLTForHuman.ModularForms.CohCarrier.Engine.CommTriplet               # background job
flock .lake/flt_build.lock timeout 300 lake build \
    FLTForHuman.ModularForms.CohCarrier.CommTriplet                      # background job
python3 spec/old_check_stmts.py                                   # 9857 identical
python3 tools/deps/unwired_register.py                                 # register (tier 3)
```

Scratch probes from the handoff session (untracked, deleted once the two modules went
green): `lean/tmp/probe_api{,2,3}.lean` were `#check` batteries for the `v4.34.0` names of
§7; `probe_proof3` held the working `coresAdd_smul`; `probe_proof8` held the
`conjUpperMat_mul` state.

Baseline of the wave, measured with the two `PORT_FILES` entries removed:
`9786 identical (667 promoted, 83 renamed), 0 mismatched, 0 missing, 42 own-proof
exemptions (9828 checked)`. Landing both definition modules gives `9854 identical`
(`9896 checked`): the delta is exactly 41 + 27, all matching their pin sources.
