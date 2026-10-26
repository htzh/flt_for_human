# W4 — the rank / freeness premise of A's mouth

Fourth wave of the aj subject, 2026-10-26. Parent:
[../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md) (§1, §9.2, §10.4,
§12.1). Predecessors: [PLAN-W1-stokes.md](PLAN-W1-stokes.md), [PLAN-W2-parabolic-homs.md](PLAN-W2-parabolic-homs.md)
and [PLAN-W3b-hecke-equivariance.md](PLAN-W3b-hecke-equivariance.md), all landed. Pin
`anthropics/fermats-last-theorem@aa2d8b34`; port mathlib `v4.34.0`.

**Decision.** W4 is the last cheap direct premise of A's mouth. After W3b the mouth
`ModularCurve.exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf` (653) has
exactly two unported direct premises, and this wave takes the cheaper one:

```
ModularCurve.exists_basis_periodLatticeOf_linearIndependent_real_span_eq_top_of_isCongruenceSubgroup  (267)
```

It asserts: for a congruence subgroup `Γ`, the period lattice `periodLatticeOf Γ` has a **ℤ-basis whose
images in `Dual ℂ (CuspForm Γ 2)` are ℝ-linearly independent and ℝ-span everything**. Read twice, that is
freeness (a ℤ-basis exists, of finite explicit rank `n`) and discreteness/cocompactness (real span top ⇒
`V*/L` is a torus), and it is the premise the Tate identification actually consumes: without a free
finite-rank lattice there is no `ℤ_[p] ⊗[ℤ] periodLatticeOf` to state the equivalence against. The number
`2g` is **not** in the statement — it follows from ℝ-linear independence plus span-top against
`dim_ℝ (Dual ℂ (CuspForm Γ 2)) = 2 · dim_ℂ`, and deriving it is §5's D5.

## 1. Measurement (frontier, post-W3b)

`frontier --target …exists_basis_periodLatticeOf_…`:

| reading | value |
|---|---|
| needed `[F terminal]` | **22 nodes / 6,106 lines** |
| needed `[literal]` | 27 nodes / 6,167 |
| unported demand by distance | 1: 15, 2: 3 |
| by namespace | `AlgebraicCurve.` 11 / 1,839 · `ModularCurve.` 11 / 4,267 |
| target cone | 174 nodes / 92,682 lines |
| `--ds` | avoided R 140 nodes / 74,620; reported unreachable: 4 — **but the same four are unreachable with `--ds` off**, so this is not a prune effect (§5 D6) |

**The demand nests, and that is the whole reason to take this wave first.**

| node | own lines | whole demand |
|---|---:|---:|
| `LevelN.twelve_mul_add_mul_index_le_genusFF` | 597 | 2,267 |
| `twelve_mul_add_mul_index_le_finrank_cuspForm_Gamma` | 167 | 4,387 |
| `finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm` | 134 | 5,073 |
| `finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup` | 40 | **5,839** |
| this wave's target | 267 | **6,106** |

So 5,839 of the 6,106 is one tower, and the wave's own unique content is the 267-line target body. The
tower is also the *other* premise's: the injectivity premise (302) cites the same 40-line node, and
avoiding the W4 nodes drops its demand

```
needed(302):  154 nodes / 54,550   →   134 nodes / 48,880      (−20 nodes / −5,670 lines)
```

measured with `--remove` on the rank target's node names. W4 therefore buys 5,670 lines of the injectivity
silo for the price of one wave, which no other cut does: W4a (the winding/smoothed cluster, 12 nodes /
6,215) closes no premise, and its cone already contains A's row-2 opener (810), so it belongs with row-2 in
one later plan.

**Projected effect on the mouth.** `needed(653)` 156 nodes / 55,470 → **134 nodes / 49,364**, with **one**
unported direct premise (the 302). That is the first time the end of A is a single block.

**The wrapper's wall — this wave's main risk.** `Thm_…exists_basis_periodLatticeOf_…` opens with ~100
`attribute [-instance]` and ~200 `attribute [-simp]` entries, the largest instance wall in the subject.
W3b found that its fifteen could all be dropped; here that is *not* expected, because the proof runs
through the `Place`/`IsCurveOver` instance stack (`AlgebraicCurve.Place.instIsDedekindDomain…`,
`IsCurveOver.instFreeKaehler`, `parabolicHoms_int_moduleFinite`, …). §5's D3 is the policy.

## 1b. Groundwork: what `port_advise` says is already there

`frontier` prices the demand but cannot dedup — it counts citation nodes. `port_advise` reads the pin
*including `private` declarations* and the port on disk, over the wave's eighteen `S_` files and their
eighteen wrappers (36 files, 495 declarations), and it changes the price in three ways. This is the wave's
§5 input, not an appendix.

*Invocation, since it costs a minute to get wrong:* pass the nodes with repeated `--nodes <dotted name>`;
`--targets` wants a file of pin **files or stems**, not node names, and silently resolves nothing if given
`S_….lean` names.

**Substitutions: 40 declarations already have their statement in the port (≈339 lines not to re-prove)** —
35 byte-identical, 5 identical up to binder spelling; 19 importable public, 21 only as a port-`private`
declaration. The load-bearing ones:

| wave node | already in the port | state |
|---|---|---|
| `isCurveOver_of_transcendental_of_isSeparable` | `AlgebraicCurve.isCurveOver_of_transcendental` (`IsCurveOver/Transcendental.lean`) | binder spelling — **read both**: the wave may be a separability hypothesis plus re-use |
| `eq_zero_of_forall_re_periodOf_eq_zero` | `ModularCurve.PeriodMapParabolicOf.{const_eq_zero_of_tendsto_sub, tendsto_vadd_atImInfty}` (`Period/ParabolicHoms.lean`, W2) | public, import |
| the differential trio | `LevelN.{jAnalytic_smul, fricke_smul_of_mem, precomp, redMat, eq_zero_or_eq_zero_of_mul_eq_zero, mdifferentiable_of_mem}` (`LevelN/Prelude.lean`) | public, import |
| `six_mul_level_…` | the pin's `Cusp` abbrev matches the port's `GroupTheory.BassSerre.Gp` (`GroupTheory/BassSerre/MinimalPeriod.lean`), which the pin re-declares 46 times | import |

**21 are only port-`private`, so they are a prerequisite, not a saving**: `hasDerivAt_smul_ofComplex`
(private in `ModularForms/EichlerShimura/EichlerIntegral.lean`), `hasDerivAt_comp_smul` and `hasDerivAt_moeb`,
`vecMul_ne_zero`, `apply_smul_of_mem`, `precomp_mem`, `exists_of_mem_Gpm`, `up_eq_zero_iff`,
`analyticOnNhd_up`, `differentiableAt_up`, `slash_two_apply`, `{mem,neg}_mem_Gpm`, `neg_one_mem_Gpm`,
`isOpen_𝕌`, `isPreconnected_𝕌`, `moeb`, `width` — most private in `ModularCurve/LevelN/FieldGalois.lean`
and `Period/ParabolicHomsBasis.lean`. W3b hit the same wall with `sub_eq_const_of_forall_hasDerivAt` and
solved it by re-proving privately; here the right move is the opposite — **promote or lift to a home**,
because three of the wave's files need them.

**Port once: 13 names are proved in ≥2 of the wave's files, ≈100 removable lines** if each lands once. The
two strongest pairs are exactly this wave's biggest modules:

```
63 lines / 10 proofs   S_…LevelN_exists_linearMap_regularDifferentials_mdifferentiable.lean
                   <-> S_…LevelN_isZeroAtImInfty_slash_of_mem_regularDifferentials.lean
37 lines /  2 proofs   S_…eq_zero_of_forall_re_periodOf_eq_zero.lean
                   <-> S_…finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal.lean
```

with `hasDerivAt_smul_ofComplex`, `hasDerivAt_comp_smul`, `exists_analyticAt_eventuallyEq`, `cross_mul_eq`,
`exists_rep`, `algebraMap_ne_zero`, `mul_ne_zero_of_mem`, `num_div_den`, `den_ne_zero`, `isOpen_𝕌`
among the 13. So the natural home for the shared derivative/primitive prelude is one module imported by
both `LevelN/Differentials.lean` and `Period/PeriodLatticeRank.lean` — not two copies, and not
`LevelN/FieldGalois.lean`'s private block.

**Generalise: 8 names in the wave share a conclusion but not their binders** — `moeb` (3 files,
2 statements), `T_pow_mem_Gamma` (11 files, 4 statements), `mem_of_ord_nonneg` (35 files, 3 statements),
`Φ_apply` (7 files, 7), `coe_jSub`, `isIntegral_of_finiteAlong`, `apply_smul_of_mem`, `width`. §5's D4
decides these from the pin's texts; the tool only says they are the same lemma written differently.

**Prep landed (manager's layer).** Twenty-two declarations promoted to public, in place, so the wave
imports instead of re-proving — all four modules green, no warnings. Three of the four are now **wired**
and pass with **no declaration markers at all**: `FieldGalois` 20 ok, `Places` 9 ok, `FiniteResidue` 3 ok,
all at `0 mismatch / 0 missing / 0 own`. `EichlerIntegral` stays unwired because it is port-authored (its
header is a FLT-for-human copyright block and it cites no pin file), and all four were released from
`spec/old_check_stmts.py`.

That the wire needs no markers is a fact worth keeping: `check_port` parses the pin's `S_` files
themselves, so **the pin's `private` declarations are matchable** — the promoted helpers (`Gpm`,
`vecMul_ne_zero`, `precomp_mem`, `moeb`, `hasDerivAt_moeb`, `linearIndependent_lift`,
`finite_residueField`, …) each diff `ok` against the `S_` line where the pin proves them. A
`private`-in-pin declaration promoted by the port therefore costs nothing on the wire; a marker would have
been paper over a check that passes.

| module | promoted |
|---|---|
| `ModularCurve/LevelN/FieldGalois.lean` (16) | `𝕌`, `up`, `Gpm` and the lemmas `isOpen_𝕌`, `isPreconnected_𝕌`, `analyticOnNhd_up`, `differentiableAt_up`, `up_eq_zero_iff`, `apply_smul_of_mem`, `precomp_mem`, `slash_two_apply`, `mem_Gpm_of_mem`, `neg_mem_Gpm`, `neg_one_mem_Gpm`, `vecMul_ne_zero`, `exists_of_mem_Gpm` |
| `ModularCurve/LevelN/Places.lean` (2) | `moeb`, `hasDerivAt_moeb` |
| `ModularForms/EichlerShimura/EichlerIntegral.lean` (2) | `hasDerivAt_smul_ofComplex`, `hasDerivAt_comp_smul` |
| `AlgebraicCurve/Place/FiniteResidue.lean` (2) | `linearIndependent_lift`, `finite_residueField` |

Smoke-tested from outside with `lean/tmp/W4PrepProbe.lean` (`#check` on all of them): 0 errors, and no
public statement leaks a private name — the definitions had to be promoted too, or `isOpen_𝕌 : IsOpen 𝕌`
would be unusable. Their full names are nested: `ModularCurve.LevelN.WeightTwo.{𝕌, up, …}`,
`ModularCurve.LevelN.GaloisStructure.Gpm`, `ModularCurve.LevelN.AnalyticPlaces.moeb`, `HeckeEis.…`,
`AlgebraicCurve.Place.FiniteResidueAux.…`.

**Four things settled by reading rather than promoting, each recorded because the tool was wrong about it:**

* **`moeb` needs no unification.** `Places` does not import `FieldGalois`; the two definitions live in
  sibling modules with no shared consumer. The wave takes `AnalyticPlaces.moeb`; `FieldGalois`'s stays
  private. Two private spellings in two independent modules is not a duplication to resolve.
* **`Cusp`, `instFintypeCusp`, `width` are absent from the port** — the wave's definition tail (≈5 lines:
  `abbrev Cusp Γ := orbitRel.Quotient (zpowers T) (SL(2,ℤ) ⧸ Γ)`, its `Fintype` instance, and
  `def width x := minimalPeriod (T • ·) x`), to be declared in the module that ports
  `six_mul_level_…`. `port_advise`'s row placing `width` "private in `ParabolicHomsBasis.lean`" is wrong —
  no such declaration exists anywhere in the port.
* **`Cusp → GroupTheory.BassSerre.Gp` is a false substitution**: `Gp = CoprodI G23` is a different object,
  matched only in shape. Do not import it for `Cusp`.
* **The derivative pair stays duplicated.** `HeckeEis.hasDerivAt_smul_ofComplex` and
  `hasDerivAt_comp_smul` are now public and externally usable, but their two `private` copies in
  `EichlerShimura/ExistsEquivariantPrimitive.lean` are in a different namespace; swapping them costs more
  than the ≈35 lines it saves, so the wave imports `HeckeEis`'s and the local copies stay.

**Cleanup from the impact sweep — done, except one item deliberately deferred.**

*Dedup: cleared.* Re-running `dedup.py` with the **survivors in the set** (the earlier run compared only the
four touched modules, so it could not see that `Prelude` already had the declarations) found more than its
first report:

| deleted | from | why |
|---|---|---|
| `private def PB` | `Places` | word-for-word the `Prelude` one; removing the shadow makes 41 references resolve to the single definition |
| `private theorem PB.add_right` | `Places`, `FieldGalois` | `Prelude` has it, same proof |
| `private theorem good_of_PB` | `Places` | `Prelude` has it |
| `private theorem castN_pos` | `Places` | `Prelude` has it |
| `private theorem discriminant_ne_zero'` | `Places` | `Prelude` has it, same proof |
| `linearIndependent_lift`, `finite_residueField` | `FiniteResidue` | **reverted to `private`** — the pin's surface is one private helper pair plus the public headline, and nothing outside the module used them |

That is ≈24 lines out, and one definition instead of two for `PB`. The remaining dedup verdict is
**2 clusters / 12 lines and both are false positives**: the `finite_residueField` ↔
`finite_residueField_of_finiteDimensional` pair is the pin's own private-helper-plus-headline structure (the
headline is already a one-line application, so "inlining" it would grow it), and `up` ↔ `ext` match only at
the one-line-body tier. Wire unaffected: 29 ok / 0 mismatch / 0 missing on `FieldGalois` + `Places`, 1 ok on
`FiniteResidue`.

*move_dead: measured, deferred.* Each module still has **one** dead declaration — but the dead sets are whole
private blocks, not one-liners: shelving `FieldGalois`'s drags **6 private helpers / 88 lines**, `Places`'
**71 premises / 583 lines**, i.e. helper blocks that exist only for the dead lemma. A Reserve move of that
size is not a tail-of-prep operation; the port's convention and this plan both run `move_dead` **after** the
wave's modules close, and these two modules are now wired and green, so nothing decays while it waits.

**What this does to the price.** 6,106 pin lines − ≈339 substitutions − ≈100 port-once ≈ **5,667 lines of
actual transcription**, and the 21 promotions are moves, not proofs. So §6's budget is stated against
5,667, not 6,106.

## 2. Scope — three blocks

Eighteen nodes appear in the ranked list; the remaining four of the 22 are behind them.

**A — the RR / `IsCurveOver` foundation (AlgebraicCurve, 11 nodes / 1,839).** The `genusFF` and order
leaves the dimension chain stands on:

| node | lines |
|---|---:|
| `isCurveOver_of_transcendental_of_isSeparable` | 20 |
| `RationalFunctionField.deg_ne_zero` | 30 |
| `Place.deg_ne_zero_of_finiteDimensional_adjoin` | 53 |
| `sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable` | 76 |
| `Place.ord_sub_one_le_ordDiff_D_of_perfectField` | 181 |
| `sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable` | 418 |
| `Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois` | 778 |

`isCurveOver_of_transcendental_of_isSeparable` is the subject's cheapest real theorem and the gate the
whole block needs: `K → F` with a transcendental separable generator of finite degree is a curve.

**B — the dimension tower (ModularCurve, one implementer).** 597 → 167 → 134 → 40, in that order: the
`12 · index ≤ finrank S₂` computation at `Γ(N)`, its transport to a general `Γ`, the `Γ(N)` instance of the
parabolic-homs bound, and the general bound over it. **This is 5,839 of the wave and must not be split
across implementers** — each node is the sole premise of the next.

**C — the rank layer (ModularCurve).** The differential side and the nondegeneracy:

| node | lines | what it is |
|---|---:|---|
| `six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq` | 552 | the index bookkeeping the bound consumes |
| `finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_le_of_normal` | 416 | reduction of the general bound to the instance |
| `eq_zero_of_forall_re_periodOf_eq_zero` | 310 | **nondegeneracy**: all real periods zero ⇒ `f = 0` |
| `LevelN.exists_linearMap_regularDifferentials_mdifferentiable` | 813 | differentials are holomorphic |
| `LevelN.isZeroAtImInfty_slash_of_mem_regularDifferentials` | 870 | differentials vanish at cusps |
| `LevelN.exists_linearMap_regularDifferentials_cuspForm_injective` | 101 | **differentials ↪ cusp forms** |
| the target itself | 267 | the ℤ-basis with real span top |

Blocks A and C's first two are independent of B; C's last three are what make the target's
`LinearIndependent ℝ` and `span ℝ = ⊤` true, and they need A's `genusFF` leaves for the dimension count.
So the dependency is A → (B ∥ C-head) → C-tail.

## 3. Order and checkpoints

Two implementers, split by namespace — the seam is real here, unlike W3b's shared prelude:

```
A  RR foundation, in dependency order: isCurveOver (20), deg_ne_zero (30/53),
   sum_ord (76), ord_sub_one (181), sum_ordDiff_D (418), ord_restrictAlong (778)
B  the tower, one writer: 597 → 167 → 134 → 40
C  six_mul_level (552), _of_le_of_normal (416), then the differential trio
   (813, 870, 101), then eq_zero_of_forall_re (310), then the target (267)
```

Checkpoints, each a green module or module pair: **A1** `isCurveOver` + the two `deg_ne_zero`; **A2** the
two `sum_ord*` bound leaves; **A3** `ord_sub_one` + `ord_restrictAlong`; **B1** 597; **B2** 167; **B3** 134;
**B4** 40; **C1** the two index lemmas; **C2** the differential trio; **C3** the nondegeneracy; **C4** the
target. Implementer 1 owns A and C; implementer 2 owns B, and B cannot start before A1.

## 4. Homing

| block | module | why |
|---|---|---|
| A1 (`isCurveOver_of_transcendental_of_isSeparable`) | `AlgebraicCurve/IsCurveOver/SeparatingTranscendental.lean` | the file already holds the separating-transcendental generator this lemma is about; `PerfectField.lean` sits beside it |
| A2, A3 (`sum_ord*`, `ord_*`) | `AlgebraicCurve/Genus/Index.lean`, `…/DegreeIdentity.lean` | the two `genusFF` bounds are the genus-degree index computation; `Genus/` already hosts `Index`, `DegreeIdentity`, `RatFunc`, `Stichtenoth` |
| B (the tower) | `ModularCurve/LevelN/GenusFF.lean` (new) for 597, then `ModularCurve/Period/ParabolicHomsBasis.lean` (+134, +40) | `LevelN/FunctionField.lean` is 79 lines and the `twelve_mul` computation is a `LevelN` genus fact; `ParabolicHomsBasis.lean` (974 lines) already carries the parabolic-homs lattice **and** its rank inequality `finrank_parabolicHoms_add_natCard_le_finrank_addMonoidHom_add_one`, so the bound belongs beside it |
| C-head (`six_mul_level`, `_of_le_of_normal`) | `ModularCurve/Period/ParabolicHomsBasis.lean` | same subject: the index bookkeeping and the general/instance reduction of that bound |
| C-tail (the differential trio) | `ModularCurve/LevelN/Differentials.lean` (new) | `LevelN/` already hosts `Places`, `QExpBridge`, `FunctionField`; the `regularDifferentials ↪ CuspForm (Gamma N) 2` direction is `LevelN` content |
| C3, C4 (`eq_zero_of_forall_re`, the target) | `ModularCurve/Period/PeriodLatticeRank.lean` (new) | both are about `periodLatticeOf` as a lattice, which is `Period/`'s subject |

## 5. Decisions

* **D1 (inherited).** Pinned statements transcribed verbatim; headlines public at the pin's names; helpers
  `private` unless two modules need them. The pin's qualified spellings stay in the statements even inside
  a namespace (W3b's `CuspForm.stableT` lesson — `check_port` compares statement text verbatim).
* **D2 — the general/instance pair is not a duplicate; the reduction between them is the dedup surface,
  and `port_advise` has already run.** `finrank_parabolicHoms_le_two_mul_finrank_cuspForm_of_isCongruenceSubgroup`
  (40, general `Γ`) *cites* `finrank_parabolicHoms_Gamma_le_two_mul_finrank_cuspForm` (134, `Γ(N)`), so both
  land and neither is derived from the other. Two measured refinements: the 40-line proof reduces through
  `…_of_le_of_normal` (416) and `six_mul_level_…` (552), and **the second pair is the 37-line
  duplicate found in §1b** — `hasDerivAt_smul_ofComplex` and `hasDerivAt_comp_smul` are proved in both of
  those two files. So read those two files together before transcribing either, and take the general one's
  binders (§7.4 of the playbook).
* **D3 — the instance/simp wall: drop all of it, and expect this wave to be where D4 finally bites.** W3b
  dropped fifteen and needed none; this wrapper has ~300 entries and the proof genuinely climbs the
  `Place`/`IsCurveOver` instance stack. Policy unchanged: drop every wall, prefer a local `include`/`omit`
  or an explicit instance argument, **record which lemma needed which**, and never reinstate a global
  `attribute [-instance]` / `[-simp]`. If more than a handful are needed, the finding is a defect of the
  port's instance design and is reported, not papered over.
* **D4 — the two `sum_ord*` siblings, and the eight binder variants §1b lists.**
  `sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable` (76) and
  `sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable` (418) are two genus bounds, and
  `ord_sub_one_le_ordDiff_D_of_perfectField` (181) is the bridge between their summands; the names
  suggest the `ordDiff` one is the separated case and the `ord_sub_one` one the perfect-field case, i.e.
  siblings of one computation rather than a general/instance pair. `port_advise` adds eight names in the
  wave where the pin itself writes one lemma several ways (`moeb`, `T_pow_mem_Gamma`, `mem_of_ord_nonneg`,
  `Φ_apply`, `coe_jSub`, `isIntegral_of_finiteAlong`, `apply_smul_of_mem`, `width`) — take the wrapper's
  binders and write each once.
* **D5 — the statement form of the rank.** Prove the pin's statement exactly:
  `∃ n, ∃ b : Basis (Fin n) ℤ (periodLatticeOf Γ), LinearIndependent ℝ (coe ∘ b) ∧ span ℝ (range …) = ⊤`.
  The *number* `finrank ℤ periodLatticeOf = 2 * finrank ℂ (CuspForm Γ 2)` is not in it; if the wave wants
  it, it must be **derived** from ℝ-linear independence plus span-top, and that derivation written as part
  of C4. Doing so is what actually retires §9.2's borrowed-rank coupling — proving the pin's statement
  without the derivation leaves the rank number exactly where it is.
* **D6 — the four "unreachable" nodes are pin-side roots, and that is good news.** `frontier` prints
  *"N needed nodes cannot reach F without R"* whenever a demanded node has no hop distance to the ported
  frontier (`unreachable = [i for i in need if i not in hops]`, `frontier.py:830`, printed at :1206). The
  hop distance is `1 + min` over the node's **FLT** premises, so a node whose proof cites no other FLT node
  has none — and is flagged. Measured, each of the four is `needed = 1 node` with `hops to F = -`:

  | node | own lines | status |
  |---|---:|---|
  | `Place.exists_of_orderMap` | 169 | new, mathlib-only |
  | `Place.exists_ord_eq_one` | 8 | new, mathlib-only |
  | `Place.inertiaDeg_pos_of_finiteDimensional` | 90 | **already ported** as `Place.inertiaDeg_pos` (`WeilExchange/FiberOverCount.lean`) |
  | `degree_canonicalDivisor_eq_of_riemannRoch` | 16 | **already ported** as `PolarFinrank.degree_canonical_eq` (`Canonical/PolarDifferentials.lean`) |

  Two corrections to the first reading of this row, both worth keeping because the wrong reading was
  plausible: the flag is **not** a prune effect (the same four appear with `--ds` off, `R` empty), and it is
  **not** an artefact of the port renaming two of them (a renamed statement is *needed* under its pin name;
  root-ness is what makes it unreachable, and it is a property of the pin's graph alone). What it does mean
  is that two of these are cheap — but only one of them is a restatement, and the difference is worth
  knowing before the wave budgets it. Read both texts:

  * `degree_canonicalDivisor_eq_of_riemannRoch` vs `PolarFinrank.degree_canonical_eq`: **the same statement**,
    same hypotheses, same conclusion; the port's lives in a section whose `variable`s supply the instance
    binders (it even `omit`s three of them). Restating the pin's version is a statement plus
    `exact degree_canonical_eq hRR hC hω` — ≈10 lines.
  * `Place.inertiaDeg_pos_of_finiteDimensional` vs `Place.inertiaDeg_pos`: **two distinct pin nodes,
    not one statement in two spellings.** The pin's `inertiaDeg_pos` (wrapper
    `Theorems/Thm_AlgebraicCurve_Place_inertiaDeg_pos.lean`) **itself assumes
    `[Algebra.IsSeparable F F']`**; the `_of_finiteDimensional` node assumes only `[FiniteDimensional F F']`.
    The port's copy is therefore faithful and nothing is "extra" — the earlier reading of this row compared
    the port's `inertiaDeg_pos` against the *sibling* node and drew the wrong conclusion.

    *What the failed `omit` does and does not show.* `omit [Algebra.IsSeparable F F'] in` on
    `inertiaDeg_eq_inertiaDeg_fiberCenter` fails with `cannot omit referenced section variable`
    (`PlaceDictionary.lean:364`). That says the **elaborated term mentions the instance**; it does not say
    the mathematics needs separability. Every declaration of the `ValuationDictionary` section is declared
    under the same `variable` block, so each helper carries the instance in its *type* and calling one passes
    it — the instance can be referenced transitively with no genuine use anywhere. Bisecting it by pushing
    `omit` down was attempted twice and both attempts mis-targeted (a `replace` on a declaration name also
    matches its `_mk`/`_of_…` variants), so **whether the chain is mathematically separable-free is
    unsettled** — and it does not need settling: the strong form was proved by a different route below.

    **Counts, so the choice is not a guess.** The weak statement has **5 consumer sites in the port, all in
    one module and all the same shape** (`ModularCurve/Analytic/CuspDichotomy.lean:278, 280, 282, 310, 312`,
    each `exact_mod_cast Place.inertiaDeg_pos (F := RatFunc 𝕂) (…)`), and its owning module
    `WeilExchange/FiberOverCount.lean` is **unwired** (0 `spec-pin`), so removing the declaration breaks no
    wire. In the pin it is cited by **13 files / 45 occurrences** (`S_` files of the unported
    `PlaceSpecialization`, ramification-index and `modularFunctionFieldFull` columns) — none of them ported.

    **Decision: prove the strong node, then delete the weak one and retarget the five sites.** One statement,
    one proof. *Done:* the strong form is in `WeilExchange/FiberOverCount.lean` as six lines, because
    `inertiaDeg` is *defined* as `Module.finrank (w.restrict F).ResidueField w.ResidueField` and the port
    already had `finite_residueField_of_finiteDimensional` — so the pin's 90-line `S09G2` chain is not needed
    at all. `#print axioms` is `[propext, Classical.choice, Quot.sound]`; the weak lemma is deleted and its
    five `CuspDichotomy` call sites retargeted.

    **Both retargeted modules are up to code** (they were released from `spec/old_check_stmts.py`, so the
    standard applies to them now):

    | | `FiberOverCount` | `CuspDichotomy` |
    |---|---|---|
    | `spec-pin` | 3 pin sources (the two bifibre files + the strong node's) | 3 pin sources (cusp dichotomy, prime degree, `modularFunctionFieldBar_eq_restrictScalars`) |
    | `check_port` | **35 ok / 0 mismatch / 0 missing / 0 own** for the pair | same |
    | build | 4.2 s, silent | 16 s, silent |
    | `dedup.py` | 0 clusters / 0 lines | 0 |
    | `move_dead.py` | 0 declarations | 0 |

    The third pin source of `CuspDichotomy` came from the checker itself: `modularFunctionFieldBar_eq_restrictScalars`
    was reported `MISSING (identical statement at S_…:263, not in this wire)`, so the wire was completed
    rather than the declaration marked. Corpus after the two wires: **285 modules, 6084 ok, 0 mismatch,
    0 missing, 31 own**. The port's architecture permits it: parent §10.5 says the pin's *mouths* are the
    specification and "a port may design the middle freely", so an interior node may be strengthened rather
    than reproduced — recorded here as a deviation, with the consequence that the pin's
    `Place.inertiaDeg_pos` node is deliberately absent from the port and its 13 unported citers take the
    strong name when their waves land. Keep `FiberOverCount.lean` off the wire for
    `S_AlgebraicCurve_Place_inertiaDeg_pos.lean`; if it is ever wired, it is wired to the strong node's file.

    This supersedes the earlier "keep the weak one as a one-liner" reading. That version also removes the
    duplicate proof but keeps a second statement of a fact whose hypothesis is by then unused — which is the
    duplication §10.4's criterion is about.

    *And `CuspDichotomy` is a leaf only for now.* The pin cites these nodes from the unported
    `PlaceSpecialization/LevelOneProlongationPair` column (`divisorLawFst_oneSided`,
    `exists_goodRep_admissible_smul_single_sub_self_of_eq_zero_or_eq`, …) and from
    `exists_place_of_modularPolynomial_eval_eq_zero`, `place_eq_of_modularPolynomial_rootMultiplicity_eq_one`
    and the three `relfinrank_*` files — so its consumers exist and are unported, which is why `move_dead`
    sees referrers but nothing imports it.

  **A caveat about the tool that this exposes.** `port_advise`'s shape tier normalises *instance arguments*
  by design ("the same hypothesis list once the binder spelling is normalised (… an instance argument …)"), so
  it reported both as "identical up to binder spelling" although one carries a strictly stronger hypothesis.
  A `substitution` verdict is a pointer to read the two texts, not a price: §1b's "≈339 lines not to re-prove"
  is an upper bound on the saving, not a measurement of it.

  **And the prune is not a scoping instrument here.** It is known to be too broad — parent §10.4's amendment
  has it matching A's own `abelJacobi_mem_periodLattice*` lemmas, and PRUNABLE §7 records 19 dictionary
  lemmas / 5,981 lines cut with 86 nodes / 41,714 behind them — so W4 is priced on the plain reading:
  **22 nodes / 6,106 lines with or without `--ds`.**

## 6. Budget

6,106 pin lines of demand, but §1b prices the *work*: − ≈339 (statements already in the port) − ≈100
(13 names duplicated across the wave's own files) ≈ **5,667 lines of actual transcription**, plus the 21
promotions, which are moves not proofs. At a transcription ratio of 1.0–1.07 that is **≈5,700–6,100
written**. Compare W3b: 1,586 written / 2,366 pin (0.67×) because 1,031 of its pin lines were one block
copied four times — this wave's ratio is the ordinary one, and §1b's numbers are already subtracted here,
so do not subtract them twice.

Upside risk: D3's instance wall. Downside: none — the two factoring pairs are net savings, not costs.

## 7. Verification

The W3b wire, unchanged:

* `spec-pin:` per module naming the `Theorems/` wrapper **and** the `P2M/Sol/S_` file (`-- comparable copy`);
* `python3 spec/check_port.py <module> --force` → `0 mismatch / 0 missing`, and the module's `PORT_FILES`
  line removed from `spec/old_check_stmts.py` if it is there;
* `#print axioms` = `[propext, Classical.choice, Quot.sound]` on every headline, in one `tmp/AxiomsW4.lean`;
* builds one module at a time, `timeout 110 lake build <Module>`, logs in `lean/tmp`, no tree build, no
  warnings, no `sorry`/`axiom`/`native_decide`;
* `tools/deps/dedup.py` and `move_dead.py` on the new modules after they close;
* **re-measure, in this order:** `needed(302)` should read **134 nodes / 48,880** and `needed(653)`
  **134 nodes / 49,364 with one unported direct premise**. If either is off, the difference is the finding.

## 8. First moves

1. **D6 is answered** (see §5): the four are two substitutions and two new `Place` nodes, and the prune does
   not change the price. The promotions of §1b's prep are **done** (seventeen declarations, three modules,
   green); what remains of the groundwork is the two open items there — the `ExistsEquivariantPrimitive`
   namespace question and the two `moeb` definitions — plus promoting `linearIndependent_lift` and
   `finite_residueField` from `AlgebraicCurve/Place/FiniteResidue.lean`.
2. **A1**: `isCurveOver_of_transcendental_of_isSeparable` (20) — the gate, and it exercises the statement
   spelling of the whole wave.
3. **B1**: `LevelN.twelve_mul_add_mul_index_le_genusFF` (597, silo 2,267) — start the tower with the
   implementer who is not on A, since it only needs A1.
4. Then A2/A3 in parallel with B2, and C after B3.
5. Re-measure after B4 (the 40-line head) — that is the moment `needed(302)` should drop by 5,670, and it is
   the wave's half-way checkpoint in value, not in lines.
