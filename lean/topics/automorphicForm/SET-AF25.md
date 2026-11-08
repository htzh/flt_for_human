# SET-AF25 — the cuspidal lift of a convolution operator, and its commutation

**Status: DISPATCHED 2026-11-07** — one order, one new module; §6 is the forecast, §7 records the
landing at review. Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF24 left. It is the **twenty-fifth** `AutomorphicForm`-serving set, and the head of the column's
return column after AF24.

**5 rows / 1,254 silo / 1,108 net new math lines (`port_plan`) / 19 declaration groups**, of which 10
lines are already in the port. Five of the ten declarations are single-declaration pin files.

| row (`AutomorphicForm.CuspidalSpectrum.` dropped) | silo | prem | block | what it says |
|---|---|---:|---|---|
| `exists_isLift_rightConv` | 199 | 4 | ready | for continuous compactly supported `g`, `φ ↦ rightConv F φ g` lifts to a bounded operator `T` on `cuspSubcarrier`, the flat profile's operator `T'` is its **adjoint**, and both lifts are produced |
| `exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact` | 103 | 2 | *off-shelf* | the lift of right convolution by an arch-bi-finite `U`-bi-invariant `h` commutes with `Tc`, and is the lift of `rightConv · h` on cusp members |
| `exists_commute_lift_rightTranslate_rowIsometry_of_isCompact` | 112 | 2 | *off-shelf* | the lift of a right translate by a row isometry commutes with `Tc` |
| `exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact` | 665 | 2 | *off-shelf* | the lift of the coset sum `x ↦ ∑ i, φ (x * reps i)` over a `U`-double-coset family commutes with `Tc` on the `U`-invariants — the level Hecke operator |
| `isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep` | 175 | 2 | *off-shelf* | the `K`-finite vectors of a closed cusp subrepresentation, read back through `toCuspSubcarrier`, form a `IsCuspSubrep` for `fdPins F Φ₀` |

## 0. The read (SET-AF24's post-landing read, taken before this set's scaffold)

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af24-post.json
python3 build/af-return.py build/shelf-af24-post.json AutomorphicForm. 1
```

| figure | value |
|---|---|
| `needed [F terminal]` | **791 nodes / 333,363 lines** |
| `needed [literal]` | 803 / 336,828 |
| frontier F | 1,625 / 794,013 |
| ready block | **72 / 24,200** — 44 `AutomorphicForm` / 18,061 |
| leaves block | **210 / 54,362** — 45 `AutomorphicForm` / 9,242 |
| `AutomorphicForm` demand | 300 / 133,068 |
| withheld | 4 (the prunable complex-analytic premises; not this column's) |
| `--selfcheck` | PASS (1,449 `Thm_` sources, 1,630 declared names) |
| `--unport` corrections | none |

**FR-0114 applies from here on**: this set's scaffold carries `spec-pin:` wires, so a read taken while
the dispatch is in flight counts the five rows as ported. Every read in this set's window must
`--unport` the five (or be taken off `build/shelf-af24-post.json`, as above).

## 1. Why this cut

The return column after AF24 has one clear head:

| row | silo | readies | 1-hop |
|---|---:|---:|---:|
| **`CuspidalSpectrum.exists_isLift_rightConv`** | **199** | **1,055** (4 rows) | 702 |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 552 | 0 |
| `integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn` | 635 | 210 | 0 |

and the four rows it readies are exactly the rest of this set — the recipe's "take the gate *and* the
door it opens" (SET-AF23's lesson). Note the block structure, because it is the same shape as AF24 in
mirror: **one** row is on the ready block and **four are on neither** (each `needed = 2`, one edge
behind the hub). So the set touches the ready block by a single row (−199) and takes 4 off-shelf rows
(1,055) — a brief that read only the ready block would have priced it at 199 silo (FR-0150).

The subject is one construction: the bounded lift of a function-level operator to the cuspidal
carrier, and the four commutation statements that make it an operator of the level-`N` Hecke algebra.
The 175 row is the `K`-finite companion (`IsCuspSubrep` of a closed cusp subrepresentation) and is
what makes the lift usable at level `N`.

**What it readies: nothing.** Measured with `build/af24-return.py` over all five: 0 rows, and the
rows it leaves one premise away are 363, 182, 114, 43 — the compact-operator block, whose gateway
`isCompactOperator_lift_rightConv_comp_cuspSubcarrier` (285 silo) is itself off-shelf and drags the
LsXi/Petersson bound (1,165 + 447 + 209 + 119 …). That is the honest successor story and the natural
AF26 (§7).

## 2. The price

```bash
python3 port_advise.py --nodes AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv --nodes … --json build/af25-advise.json
python3 port_plan.py --json build/af25-advise.json
```

| figure | value |
|---|---|
| raw `S_` lines | 1,254 |
| declaration lines | 1,118 |
| — duplicate copies | 0 |
| — boilerplate | 136 |
| distinct declaration groups | 19 |
| already in the port (vetted) | 10 |
| **net new math lines** | **1,108** |

One substitution, real: `eq_of_glArch_eq_of_glFin_eq` (10 lines) already exists publicly at
`AutomorphicForm.eq_of_glArch_eq_of_glFin_eq` (`Adelic/LevelCompactness.lean`, binder spelling
differs, 4 in-tree copies). The pin proves it again in the coset-sum file, and the checker needs a
declaration **of this module** at the pin's name (FR-0115's shape), so the order has the worker write
it and delegate to the port's lemma where the statements line up.

**No definition gate.** `gate_scan` over the five wrappers' `Def_` closure —
`Def_AutomorphicForm_CuspidalSpectrumCarrier` (7–15 declarations used), `_CuspidalSpectrumSubrep`
(0–1), `_ArchSpherical` (0–1), `_FactorizableTestFn` (0–4) — reads **0 missing**, with one expected
`MISS`: `continuous_unipotentGL2_adele`, the pin's specialised copy of the **general**
`continuous_unipotentGL2` the port promoted in SET-AF5 (name-anchored false negative, already recorded
there). `twin_scan --node`: `new` five times.

## 3. Home

**One new module, `AutomorphicForm/Adelic/Cusp/SpectrumLift.lean`**, above `SpectrumCarrier`,
`SpectrumSubrep`, `SpectrumTranslation` and `SpectrumConvAction`. Why not insertion into
`Cusp/SpectrumConvAction.lean`, which is the module that *consumes* `IsLift`? Because it is a
473-line four-headline module and this is five more headlines and a 665-line one; a new module is
cascade-free (recipe §5), and the subject is a distinct role — "the lift of an operator" — not
"rightConv on the carrier". The existing modules stay frozen; the new module imports them.

## 4. The cut, and the gates

One order, `lean/tmp/WORKORDER-AF25-spectrum-lift.md`, dispatched against the checker-green scaffold
(**5 ok / 0 mismatch / 0 missing**). The order carries the build ladder, the axiom gate, the silence
gate, `dedup --within` / `move_dead`, and a consumer zone
(`spec/AutomorphicFormSetAF25Consumer.lean`) with a real composition and no `#check`s.

## 5. Verification of the dispatch

| gate | result |
|---|---|
| scaffold `check_port --force` | **5 ok / 0 / 0** |
| scaffold elaboration | 1 s |
| definition gate (`gate_scan`, 4 `Def_` modules) | 0 missing (1 expected `MISS` = the general-lemma name) |
| twin (`twin_scan --node`) | `new` ×5 |
| statements | byte-identical to the wrappers (checker, not by eye) |

## 6. Forecast

| figure | before | after |
|---|---|---|
| `needed [F terminal]` | 791 / 333,363 | **786 / 332,109** |
| `needed [literal]` | 803 / 336,828 | **798 / 335,574** |
| frontier F | 1,625 / 794,013 | **1,630 / 795,267** |
| ready block | 72 / 24,200 | **71 / 24,001** (1 row out: 199; 0 in) |
| leaves block | 210 / 54,362 | **210 / 54,362** (untouched) |
| `AutomorphicForm` demand | 300 / 133,068 | **295 / 131,814** |
| rows readied | — | **0** |

The frontier figure is already observable: the scaffold's five `spec-pin:`-wired declarations make the
live read 1,630 / 795,267 (FR-0114), which is why the forecast's line column can be checked before the
proofs land. The node column follows AF24's corrected rule: `n` rows remove `n` nodes.

## 7. The landing (2026-11-07)

`Adelic/Cusp/SpectrumLift.lean` — **1,278 lines / 19 public declarations** (5 headlines + 14 helpers at
the pin's last names); one order, one dispatch.

| gate | result |
|---|---|
| `check_port --force` | **19 ok / 0 mismatch / 0 missing / 0 own** |
| build (single module, flock) | success, 4,267 jobs, 12 s |
| axioms (5 headlines) | `[propext, Classical.choice, Quot.sound]` each |
| `dedup --within` | 19 declarations, **0 clusters / 0 removable** |
| `move_dead` | 0 declarations / 0 lines |
| consumer `spec/AutomorphicFormSetAF25Consumer.lean` | **0 errors / 0 warnings** |

**The re-read is exact on every forecast figure** — the first set of the column to hit its own table on
all six rows:

| figure | before | forecast | actual |
|---|---|---|---|
| `needed [F terminal]` | 791 / 333,363 | 786 / 332,109 | **786 / 332,109** ✓ |
| `needed [literal]` | 803 / 336,828 | 798 / 335,574 | **798 / 335,574** ✓ |
| frontier F | 1,625 / 794,013 | 1,630 / 795,267 | **1,630 / 795,267** ✓ |
| ready block | 72 / 24,200 | 71 / 24,001 | **71 / 24,001** ✓ |
| leaves block | 210 / 54,362 | 210 / 54,362 | **210 / 54,362** ✓ |
| `AutomorphicForm` demand | 300 / 133,068 | 295 / 131,814 | **295 / 131,814** ✓ |

**Deviations worth carrying** (bodies only; every statement checker-faithful): the pin's `haveI` walls
became file-level `attribute [local instance]` lines plus plain `have` for the local `CompleteSpace`
instances, because `haveI` fires mathlib's default `linter.style.haveILetI` and `set_option` is
forbidden; six deprecated projections renamed (`orthogonalProjection` → `orthogonalProjectionOnto`,
`…_mem_subspace_orthogonalComplement_eq_zero` → `orthogonalProjectionOnto_apply_of_mem_orthogonal`,
`ContinuousLinearMap.coe_sum'` → `FunLike.coe_sum`); and the single `rw [inner_toCarrier]` at pin
`665:385` no longer unifies in v4.34, so it is two explicit applications of the same lemma in the same
order. Four new imports, each reported.

**The coset-sum prelude is half twin, half new.** `cuspInvSubcarrier` and
`map_cuspSubcarrier_le_cuspInvSubcarrier` are the compact-open-`U` twins of the landed
`cuspLevelSubcarrier` / `…_cuspLevelSubcarrier_of_isLift_rightConv` (`SpectrumConvAction.lean`), and
coincide definitionally at `U = (fdPins F Φ₀).U N` — the general-`U` form is what the Hecke-coset row
needs. The 237-line `apply_eq_zero_of_mem_orthogonal_cuspInvSubcarrier` has **no** port counterpart:
its level analogue, `CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant`
(260 silo), is still on the shelf — so that row is now a *specialisation of mathematics the port holds
the general form of*, and it is the cheapest open row in the carrier block (candidate for AF27).

## 8. What this set does not do, and what is named next

- **The compact-operator block** — `exists_isCompactOperator_isSymmetric_lift_rightConv` (114),
  `exists_isCuspLift_rightConv_isCompactOperator` (43) and their gateway
  `isCompactOperator_lift_rightConv_comp_cuspSubcarrier` (285), plus
  `isCuspSubrep_cuspKFiniteSubmodule_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep` (182, whose other
  premise is the 89-line `rightConv_mem_cuspKFiniteSubmodule_of_mem_cuspMemberSubmodule_of_isArchBiFinite`).
  The gateway drags the LsXi/Petersson bound (`exists_forall_setLIntegral_nnnorm_sq_le_…_of_isFundamentalDomain`
  447, `…_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain` 1,165, `…_of_isFundamentalDomain`
  209, `adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain` 119) — so this is
  a two-set story, and **AF26** is its cheap half (the 447 + 209 + 119 bound rows and the 285 gateway)
  with the 1,165 row as the following one.
- **The Weyl intertwining integrand** (`weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half`
  1,349 + `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`
  1,291 + `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` 1,043 + the two
  `apply_weylInv_unipotent_…` rows): ≈4,482 silo, the largest single subject left on the AF shelf, and
  the natural AF27 on size.
- **The LsXi/Petersson pair** (`…_of_coversModCentre` 1,361 and its 447 sibling): 1,808 silo, which the
  compact-operator gateway also needs — it is shared between AF26 and the bound rows above, which is
  why the recipe's "prefer a cone that is a subset of work the endgame needs anyway" applies.
- **The `isCuspConstituent` cluster** (`continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule`
  154 — a ready leaf with leverage 8/19 — and the 240/204/148/105/87/123 chain behind it): it is the
  whole requirement of the 458-line `exists_eq_sum_su2String_highestWeight` row that AF24 moved to two
  premises short, and it is *not* cheap: the row's closure is 107 nodes / 29,103 silo.
- Everything else on the shelf stays deferred as SET-AF24's Appendix A lists it.

**The cut taken as AF26, after this re-read**: the **LsXi/Petersson bound pair**,
`exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre`
(1,361) and its `…_of_isFundamentalDomain` sibling (447) — **1,808 silo / 1,665 net / 120 declaration
groups**, both on the ready block, with **0 duplicate lines between them** (their closures are
themselves: every premise is ported). The compact-operator block is *not* AF26 because its gateway
`isCompactOperator_lift_rightConv_comp_cuspSubcarrier` (285) is off-shelf and needs seven unported
premises, of which the LsXi pair is two (`…_of_isFundamentalDomain` 447 and
`…_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain` 1,165) — so AF26 is the first half of
that chain, and AF27 the second.

## Appendix A — the set's rows, and where they sit

| row | silo | block |
|---|---:|---|
| `exists_isLift_rightConv` | 199 | ready |
| `exists_commute_lift_rightConv_of_isArchBiFinite_of_isCompact` | 103 | off-shelf (one edge behind 199) |
| `exists_commute_lift_rightTranslate_rowIsometry_of_isCompact` | 112 | off-shelf |
| `exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact` | 665 | off-shelf |
| `isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep` | 175 | off-shelf |
