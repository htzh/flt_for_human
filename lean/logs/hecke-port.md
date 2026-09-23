# The Hecke-operator effort — record

**Status: Tier 0 + Tier 1 complete.** This is the running record for the
Hecke-operator sub-effort of the `ModularForms` port, parallel to
[phiGen-port.md](phiGen-port.md) and [ffg-port.md](ffg-port.md). Tiers 2–4 are
scoped and priced in §6 but **not attempted**.

The work order is
[TOPIC-slash-invariance.md](../topics/hecke/TOPIC-slash-invariance.md); the
background is [studies/hecke-operator-survey.md](../../../studies/hecke-operator-survey.md)
§§2–4 and [base/014-hecke-operators.md](../../../base/014-hecke-operators.md)
§1, §3. FLT is pinned at `aa2d8b3`; mathlib at `v4.34.0`.

## 0. What shipped

| piece | module | public decls | port lines |
|---|---|---|---|
| Tier 0 — the operator block | `FLTForHuman/ModularForms/Defs/HeckeOperator.lean` (+34) | 34 new (39 total in file) | 114 → 247 |
| Tier 1 — the shared representatives block | `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` (new) | 24 | 353 |
| Tier 1 — the five invariance statements | `FLTForHuman/ModularForms/HeckeInvariance.lean` (new) | 5 | 653 |
| Dedup — `PhiGenDescends` imports the block | `FLTForHuman/ModularForms/PhiGenDescends.lean` | −5 private declarations | 509 → 354 (−155) |

Tier 0 is the pin's `Definitions/Def_ModularForm_HeckeOperator.lean:72–200`
(34 declarations) transcribed verbatim, with the pin's `@[simp]` attributes. The
only public/private change to the pre-existing half of the file is
`val_heckeMatrix`, made public (the pin has it public and the Fricke pair uses
it); the other `val_*`/`det_*`/`denom_*` helpers stay private.

## 1. The measured compression (Tier 1)

Line counts, measured (`wc -l`):

| piece | pin lines | port lines | ratio port/pin |
|---|---|---|---|
| shared representatives block (`Def_CuspForm_Gamma1HeckeOperators.lean:82–455`; the Γ₀ `S_` copy is 352) | 352–374 | 353 | ≈1.00 |
| three Γ₀ statements + the `_div` helper (the Γ₀ `S_` files minus the re-inlined block) | ~130 | ~90 | ≈0.70 |
| Fricke pair (`…_add_slash_fricke_eq_zero` 229 + `…_exists_levelOne_…` 302) | 531 | ~560 | ≈1.05 |
| **Tier 1 total** | **1,115 distinct** (1,467 if the shared Γ₀ `S_` file is counted once per statement, as the work order prices it) | **1,006** | **0.90** (0.69 against 1,467) |

**The block was not "already correct" in the port — it had to be re-derived.**
The private copy in `PhiGenDescends.lean` was a *weakening* (§2), so the 353 port
lines are the pin's stronger statements, not a promotion of the existing text.
The Γ₀ compression is real (584 pin → ~90 port, the representative workhorses
being reused): the work order's "≈300 port lines" estimate is right for the
Γ₀ corollaries. It misses the **Fricke pair**, which is *not* compressible: the
two statements are independent of the representative block and re-derive an
analytic package (`traceFun` holomorphy, `IsBoundedAtImInfty`, the `SL₂(ℤ)` trace
invariance, `heckeU_slash_W`) that is 531 pin lines → ~560 port lines. Had the
work order priced Fricke separately it would have seen a ≈1.05 ratio there.

Dedup: `PhiGenDescends.lean` lost its private `det_eq`, four `_mul_of_eq`,
`heckeRep`(+`_infty`/`_coe`), `redMatrix`(+four `apply` simps) and
`heckeRep_mul` — 0 occurrences of the private declarations remain — and gained
one import, one `open`, and a five-line section header (+1 changed proof line in
the T8 payload). Net −155 lines in that module, with `cosetPoly_smul`,
`hasSum_coeff_of_phiGenDescends` and `mem_adjoin_jq_of_phiGenDescends`
unchanged (they elaborate and build).

## 2. The weakening finding (and how it was undone)

The pin's four `_mul_of_eq` lemmas return a `g'` **together with** a `g' 1 0`
equation (`= p * g 1 0`, `= g 1 0`, or `= e`, by lemma); the port's private copy
returned only `∃ g', …` and dropped the equation entirely. The Γ₀ proofs need it:
`g' ∈ Γ₀(N)` follows from `g' 1 0 = p * g 1 0` and `g ∈ Γ₀(N)` (resp.
`g ∈ Γ₀(N/p)`), which is what lets `hf` apply in
`heckeU_slash_mapGL` / `heckeU_slash_mapGL_of_sq_dvd`.

Restored in `HeckeRepresentatives.lean`:

* `heckeMatrix_mul_of_eq`: `g' 1 0 = p * g 1 0`;
* `heckeMatrix_mul_of_eq'`: `g' 1 0 = g 1 0`;
* `heckeDiagMatrix_mul_of_eq`: `g' 1 0 = g 1 0`;
* `heckeDiagMatrix_mul_of_eq'`: `g' 1 0 = e`.

`heckeRep_mul` likewise became the pin's Γ₀/`S_` form carrying
`(N : ℤ) ∣ g' 1 0` (the old private copy had only the matrix identity). The
`PhiGenDescends` T8 payload calls it at `N := 1`, where the divisibility is
trivial.

**Was the restored conjunct the only statement divergence?** Yes for the public
surface: the checker diffs all five Tier-1 wrappers and all 24 shared-block
declarations against the pin and reports **0 mismatched**. Two deliberate,
recorded divergences remain, neither of which changes a statement:

1. **Placement/namespace.** FLT keeps the block public in the *Gamma1 definition*
   file (`CuspForm.Gamma1Hecke`); the port has no `Gamma1` yet, so it gets its own
   definition module `Defs/HeckeRepresentatives.lean` (namespace
   `ModularForm.HeckeRepresentatives`). Mathematics unchanged.
2. **The public home's extra conjuncts are not pulled in.** The pin's *public*
   home (`Def_CuspForm_Gamma1HeckeOperators.lean:97–158, 281`) additionally tracks
   `g' 1 1` and, in `heckeRep_mul`, a `wt`-equation on `ZMod N`; those are the
   Gamma1/Nebentypus refinements the Tier-2 order needs. The port takes the exact
   Γ₀ `S_`-file statements (the source of the two workhorses), so the checker
   verifies them verbatim against `S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean`.
   A Tier-2 order must strengthen `_mul_of_eq`/`heckeRep_mul` in place (the extra
   conjuncts are provable with the same `refine ⟨…, rfl, rfl, ?_⟩` scripts).

The old private copies are **not** trustworthy as promoted statements; the
weakening was silent because `private` kept them out of the checker's view.

## 3. Verification (Tier 1)

* **`spec/check_flt_statements.py`** — before: `618 statements identical (34
  promoted from pin-private declarations), 0 mismatched, 0 missing, 14 own-proof
  declarations exempted`. After: **`682 identical, 0 mismatched, 0 missing, 14
  own-proof`**. The +64 is exactly the new public surface: 34 Tier-0 operator
  declarations + 24 representatives + 5 invariance + the newly-public
  `val_heckeMatrix`. `SOURCES` gained the five Tier-1 wrappers and the Γ₀ `S_`
  carrier; `PORT_FILES` gained the two new modules. **How Tier 0 is checked:** its
  declarations are `Definitions/` statements, matched by name against
  `Definitions/Def_ModularForm_HeckeOperator.lean` (already in `SOURCES`, ahead of
  everything else) — no exemption, no special handling.
* **`#print axioms`** on all five Tier-1 theorems (and on `heckeU`, `heckeT`,
  `heckeU_add`, `heckeT_add`, `heckeU_apply`, `coeffHeckeT_add`): only
  `propext, Classical.choice, Quot.sound`.
* **Build** — `lake build` green, 0 warnings, 0 `sorry`/`admit` in `FLTForHuman/`
  (the only textual hit is a comment in `Spine.lean`). Both new modules were built
  under the bound (`lake build FLTForHuman.ModularForms.HeckeInvariance` 10 s;
  full `lake build` 4039 jobs, green).
* **Dedup check** — `grep -c` of the private names in `PhiGenDescends.lean` went
  to 0; the T8 payload (`apply_heckeRep_smul_smul`, `prod_range_eq_prod_zmod`,
  `prod_fin_eq_prod_zmod`, `cosetPoly_eq_prod_onePoint`, `cosetPoly_smul'`,
  `cosetPoly_smul`) is in place.

## 4. Statement-shape and API findings

* **No statement drift; proof-only adaptations for mathlib `v4.34.0`.**
  `if_pos`/`if_neg`/`if_true` are deprecated here, so the ported proofs use
  `ite_eq_left`/`ite_eq_right`/`ite_true`; `ModularForm.coe_zero` became
  `FunLike.coe_zero`. The Fricke matrix identities need the explicit
  `Matrix.SpecialLinearGroup.mapGL_coe_matrix` → `map_apply_coe` →
  `RingHom.mapMatrix_apply` → `Matrix.map_apply`/`Matrix.natCast_apply` chain,
  which the pin's shorter `simp` script did not need. None of this touches a
  statement (the checker's before/after is 0 mismatched).
* **The two reindexing workhorses did not stall.** `heckeU_slash_mapGL`'s
  `Equiv.sum_comp` over `ZMod p` (via `affinePerm`) and `heckeT_slash_mapGL`'s
  `MulAction.toPerm (redMatrix p g)` over `OnePoint (ZMod p)` are the pin's
  scripts, over the concrete `ℍ → ℂ`; no `maxHeartbeats` change was needed. The
  only elaboration wrinkle was the `FunLike`/`mapGL` presentation of the 2×2
  matrix identities (§4), fixed by naming the map lemmas explicitly.
* **`mapGL_apply` is public in the shared module** (the pin's `S_` files carry it
  as `@[scoped simp]`); the checker verifies it against the same `S_` file.

## 5. The `p = 0` junk case

The pin puts the `rcases Nat.eq_zero_or_pos p` split in the *corollaries*
(`…_slash_eq_self…`), not in the `_mapGL` workhorses, and the port keeps it
there: `p = 0` makes `heckeU k 0 f = 0` (`heckeU_zero_left`) and closes by
`simp`. The workhorses carry the pin's `[NeZero p]` / `[Fact p.Prime]` binder
discipline unchanged.

## 6. Tier 2–4 entry cost (scouted, not paid)

| tier | declarations | pin lines | definitional prerequisite (foreign machinery) |
|---|---|---|---|
| 2 — Γ₁, Nebentypus | `heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1`, `heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0` | 379 + 406 = 785 | mathlib `CongruenceSubgroup.Gamma1` + `DirichletCharacter`; the pin's `Def_CuspForm_Gamma1HeckeOperators.lean:457–680` (`IsDiamondLift`, `slashOfMemGamma0`, `diamondLinOne`, `heckeTOne`, `heckeTLinOne`) and the strengthened `heckeRep_mul`/`_mul_of_eq` conjuncts (§2) |
| 3 — Γ_H | `heckeU_slash_eq_self_of_mem_GammaH`, `heckeU_add_slash_slash_eq_self_of_mem_GammaH` | 481 + 489 = 970 | **`Definitions/Def_CohCarrier_Level.lean:133` (`CohCarrier.GammaH`)** plus mathlib `GroupTheory.Transfer`; the `S_` files are ~470-line re-derivations of the same representative block for `GammaH` |
| 4 — Atkin–Lehner | 8 declarations (`alSlash_*`, `heckeU_alSlash_*`, `heckeT_trace_alSlash_of_eigen`) | 40–2,388 each, ≈8,620 total | **`Definitions/Def_ModularForm_AtkinLehnerDatum.lean`** and the `alSlash`/`diamondLinH`/`traceLin` tree (`Def_CuspForm_HeckeOperatorFormsGammaH.lean`); the 2,388-line files are mostly re-derived AL machinery, not §4 |

None of these is a mathematical risk; each is a *definitional* one — a foreign
development has to be ported first. The cheap move for a later order is to port
`Def_CohCarrier_Level`'s `GammaH` (Tier 3) or the `AtkinLehnerDatum` tree
(Tier 4) as its own topic and only then open the §4 nodes. Tier 0 and Tier 1
deliberately pull in neither.

## SET-2 §T2 — the Fricke dedup

The Fricke pair left `HeckeInvariance.lean` for the new

* `FLTForHuman/ModularForms/HeckeFricke.lean` (380 lines, 2 public theorems).

`HeckeInvariance.lean` (653 → 110 lines) keeps only the three `Γ₀` statements
and imports `HeckeFricke`. The two public statements are unchanged, so the
checker stayed at **682 identical (34 promoted), 0 mismatched, 0 missing**
before and after (only `PORT_FILES` gained the new module).

### The compression

| piece | pin lines | port before | port after |
|---|---|---|---|
| Fricke pair (two `S_` files, 229 + 302) | 531 | 538 (`HeckeInvariance.lean` 116–653) | **380** (`HeckeFricke.lean`) |
| `HeckeInvariance.lean` total | — | 653 | 110 |

The pair is **531 pin → 380 port** (ratio 0.72), against SET 1's measured ≈1.05
for the same pair — the saving is exactly FLT's second, hand-rolled trace and its
generator helpers, not the mathematics.

### What was deleted, and what replaced it

The second pin file
(`S_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke.lean`,
302 lines) carries all the duplication. `grep -c` on it, and on the new port
module:

| deleted group | pin `grep -c` | port after |
|---|---|---|
| `traceFun` / `traceForm` | 14 / 2 | 0 (only the header prose names them) |
| `trace_slash_T` / `_S` / `_SL` / `_GL` | 2 / 5 / 3 / 2 | 0 |
| `trace_holo` / `trace_bdd` | 2 / 2 | 0 |
| `sum_zmod_val` | 2 | 0 (the `ZMod`-to-`range` reindex it fed died with `trace_slash_S`; the surviving `Fin p → range p` reindex uses mathlib's `Fin.sum_univ_eq_sum_range`. The sibling `HeckeRepresentatives.sum_range_eq_sum_zmod` is public if a later topic wants the `ZMod` form.) |
| 15 generator helpers (`coe_T_pow` 6, `S_T_pow_add_p` 2, `u_add_p` 2, `eta0` 6, `etaS` 5, `u_mul_S` 2, `v_slash_S` 2, `v_zero_slash_S` 2, `X_slash_S` 2, …) | 29 `grep -c` hits across those nine | 0 |

Replacement, written once: mathlib's `ModularForm.trace` (`NormTrace.lean:82`)
plus the bridge `coe_trace_eq : ⇑(ModularForm.trace 𝒮ℒ X) = ⇑X + ∑ j ∈ range p, u X j`,
built as `coe_trace` → `sum_quotientFunc_eq` (the coset-list enumeration
`{1} ∪ {R j}`, generalized from the pin's weight 2 to arbitrary weight) →
`sum_fin_eq_sum_range_u` (`Fin p ↦ range p`, `R j ↦ S * T^j`). One general
`slash_scalar` (`f ∣[k] scalar u = u^(k-2) • f`, `u : ℝˣ`) derives both the
weight-2 `slash_two_scalar` and the `scalar p` instance; one `R_eq_S_mul_T_pow`;
one general `heckeU_slash_W` (the weight-2 `heckeU_slash_fricke_eq` is its
`k = 2` instance and was deleted); one `fricke_mul_heckeMatrix` (the only
`W * heckeMatrix` rewrite in the file).

### Did the route hold?

**Yes.** `coe_trace` + `sum_quotientFunc_eq` delivered the explicit
`∑ j ∈ range p, X ∣ (S * T^j)` form with no fallback. The one friction point was
the `Fintype (Q p)` wall the work order predicted: `coe_trace` supplies its
`Fintype` as an anonymous `let Fintype.ofFinite …`, so `sum_quotientFunc_eq`
must be applied by bare `rw` (letting unification read the instance off the
occurrence) rather than with explicit arguments, which try to synthesize
`Fintype (Q p)` and fail. `ModularForm.trace` also needs no
`IsFiniteRelIndex`/`Fintype` instance block beyond what the pin's first Fricke
half already instantiated implicitly.

**Nothing was *not* duplicated.** The second pin file's `slash_scalar` is not a
duplicate of the first's `slash_two_scalar` literally, but it is the same
statement at general weight — merging them was a strict generalization, not a
loss. The only genuinely second-file content that survives is the
`U_p`-plus-Fricke assembly (`heckeU_slash_W` + `coe_trace_eq`), which is the
level-one half's real mathematics.

### SET-3 hand-off

`HeckeFricke.lean` exposes publicly only the two Fricke theorems. What the
`q`-coefficient layer / bundling may want, and currently must import or
re-derive, is `private`: `coe_trace_eq`, `sum_quotientFunc_eq`,
`slash_scalar`, `fricke_mul_heckeMatrix`, `heckeU_slash_W`. The last is the
general `U_p (X ∣ W)` display and is the natural bundling ingredient; a later
topic that needs it should promote it (and record the promotion) rather than
copy it. `HeckeInvariance.lean` imports `HeckeFricke`, so importing it gives both
the `Γ₀` and Fricke statements without a second import.

## SET-2 §T3 — the analytic regularity layer

New module

* `FLTForHuman/ModularForms/HeckeAnalytic.lean` (227 lines, 7 public targets,
  10 private helpers).

Imports `Mathlib.NumberTheory.ModularForms.Basic`,
`…ModularForms.BoundedAtCusp`, `…UpperHalfPlane.MoebiusAction` and
`Defs.HeckeOperator` — not `import Mathlib`.

### The six-to-one dedup

The pin repeats the analytic head (lines 23–154, 132 lines) verbatim in **ten**
353-line `S_` files. Six are this topic's targets:

| pin file | lines |
|---|---|
| `S_ModularForm_mdifferentiable_hecke{U,T}` | 353 + 353 |
| `S_ModularForm_isBoundedAtImInfty_hecke{U,T}` | 353 + 353 |
| `S_ModularForm_periodic_hecke{U,T}_comp_ofComplex` | 353 + 353 |
| **the six** | **2,118** |

The port writes the head once and the seven targets on top: **227 lines**,
`grep -rln "theorem mdifferentiable_heckeU" FLTForHuman/` is one file. The other
four 353-line files (`S_UpperHalfPlane_qCoeff_hecke{U,T}`,
`S_ModularFormClass_qCoeff_hecke{U,T}`) are SET 3's; the deferred tail is absent —
`grep -c` for `hasSum_qCoeff`, `hasSum_average`, `qCoeff_heckeU_bare`,
`qCoeff_heckeU`, `qParam_hecke`, `hasSum_heckeU` in the new module is **0** each.

### Did the folded `def` matter?

**No.** `Finset.sum_induction` fired directly on `heckeU k p f` (the folded
`Finset.range` sum) for `mdifferentiable_heckeU` and `isBoundedAtImInfty_heckeU`
(and on `heckeU`/`heckeT` in the private `isZeroAtImInfty_*`); `heckeU_def` was
not needed. `heckeT` goes through its definitional `heckeU + f ∣ diag` form via
`heckeT_eq_heckeU_add`-by-definition, exactly as the pin.

### The `slash` lemmas (for T4 / SET 3)

* holomorphy: `MDifferentiable.slash hf k g` (`Mathlib/NumberTheory/ModularForms/Basic.lean:63`);
* boundedness: `IsBoundedAtImInfty.slash (hg : g 1 0 = 0) hf`
  (`Mathlib/NumberTheory/ModularForms/BoundedAtCusp.lean:35`), which is why the
  block needs the two private `1 0 = 0` helpers;
* the periodicity chain is `heckeU_apply`/`heckeT_apply` (T1) → the `vadd`
  reindex `sum_heckeMatrix_smul_vadd` → `periodic_comp_ofComplex_of_vadd`.

### One promotion

`val_heckeDiagMatrix` was `private` in `Defs/HeckeOperator.lean` (T1 recorded the
choice); the `heckeDiagMatrix_one_zero` helper needs it and the pin has it public
(`Def_ModularForm_HeckeOperator.lean:28`), so it was promoted. The checker count
moves 682 → **690**: +7 targets, +1 promotion.

### Verification

* checker **690 identical (34 promoted), 0 mismatched, 0 missing**;
* `#print axioms` on all seven targets: only `propext, Classical.choice,
  Quot.sound`;
* `lake build FLTForHuman.ModularForms.HeckeAnalytic` green, 0 warnings, no
  `sorry`.

### SET-3 hand-off

The four `q`-coefficient `S_` files share this module's head. Measured against
the pin's own tail (lines 158–345), that tail references **only**
`mdifferentiable_heckeU`/`mdifferentiable_heckeT` (public here) plus T1's
`heckeU_apply`/`heckeT_apply` and the `QExpansion`/`qParam` vocabulary — it does
**not** use the private `heckeMatrix_one_zero`/`heckeDiagMatrix_one_zero`,
`isZeroAtImInfty_*` or the `vadd` machinery. So SET 3 can import this module and
add `qExpansion_coeff_unique'`, `hasSum_*`, `qCoeff_*` without any further
promotion; the private helpers can stay private.

## SET-2 §T4 — the cusp-class layer

New module

* `FLTForHuman/ModularForms/HeckeCusps.lean` (216 lines, 4 public targets,
  14 private block helpers).

Imports `Mathlib.NumberTheory.ModularForms.Basic`,
`…Compactification.OnePoint.Basic` and `Defs.HeckeOperator`.

### The four-to-one dedup

The pin's four `S_` files are all **132 lines with an identical declaration
list** through `isZeroAt_heckeT`:

| pin file | lines |
|---|---|
| `S_ModularFormClass_isBoundedAt_hecke{U,T}` | 132 + 132 |
| `S_CuspFormClass_isZeroAt_hecke{U,T}` | 132 + 132 |
| **the four** | **528** |

The port writes the shared block once and the four targets on top: **216
lines**, and `grep -rln "ratUpperTriangularGL"` / `"theorem isBoundedAt_heckeU"`
in `FLTForHuman/` is one file. The four target files differ only in the final
`solution` (`isBoundedAt` vs `isZeroAt`, `heckeU` vs `heckeT`), exactly as the
pin's four wrappers do; the port's four public theorems are five-line wrappers
over the block's private proofs.

### The promotion

`Defs/HeckeOperator.lean` exposed `upperTriangularGL` and
`val_upperTriangularGL` (T1 kept them `private`; the pin has both public at
`Def_ModularForm_HeckeOperator.lean:11,15`). The checker count moves 690 → **696**:
+4 targets, +2 promotions. No `HeckeOperator` statement changed; the header note
was amended. `grep -c "private def upperTriangularGL"` in that file is 0.

Two other T1-private helpers the block's `p = 0` branches would have used —
`heckeMatrix_zero`, `heckeDiagMatrix_zero` — were **not** promoted: the port
closes those branches with `simp [heckeMatrix]` / `simp [heckeDiagMatrix]`
(the public `def`s), keeping the promotion count to two.

### Did the class instantiation stall?

**No.** The block's helpers are stated over `[FunLike F ℍ ℂ]` and used at
`F := F` by the four targets, and all of `isCusp_ratCast_smul`,
`isBoundedAt_slash_ratCast`, `isZeroAt_slash_ratCast`, `isBoundedAt_sum`,
`isZeroAt_sum` and the four `*_hecke{U,T}` helpers elaborated on the first try
against the inferred `[ModularFormClass F Γ k]`/`[CuspFormClass F Γ k]`
instances. The `SET-2` §2 `FunLike`-at-a-bare-function warning did not
materialize: every helper keeps the pin's `Finset`-of-`ℍ → ℂ` shape. This is the
calibration for SET 3's `ModularFormClass.qCoeff_*` targets — the same class,
with only the `QExpansion` vocabulary added, so the class inference should be
equally cheap.

### Verification

* checker **696 identical (34 promoted), 0 mismatched, 0 missing**;
* `#print axioms` on all four targets: only `propext, Classical.choice,
  Quot.sound`;
* `lake build FLTForHuman.ModularForms.HeckeCusps` green, 0 warnings, no
  `sorry`.

### SET-3 hand-off

`exists_heckeMatrix_eq_map` / `exists_heckeDiagMatrix_eq_map` are the port's own
name for the pin's public declarations of the same names; they stay `private`
here because nothing downstream names them today. SET 3's `q`-coefficient
`ModularFormClass.qCoeff_*` targets need the class instances and `qExpansion`
vocabulary, not these matrix models; if a later topic wants them it should
promote them (and record it) rather than copy the block. The block also exports
nothing public beyond the four targets.

## SET-2 review (2026-09-23)

Reviewed independently, not from the runner's report. Checker re-run: **696
identical (34 promoted), 0 mismatched, 0 missing, 14 own-proof**; full
`lake build` exit 0, **4042 jobs, 0 warnings**, no `sorry`; `#print axioms`
re-run clean on all 13 SET-2 headlines; the dedup greps confirmed (the hand-rolled
trace declarations absent, the T3 deferred tail absent, `slash_two_scalar` now a
two-line corollary of the general `slash_scalar`). The measured compression is
real — **3,177 pin lines → 823 port lines (0.26)** — and both routes the work
orders flagged as risks (the `ModularForm.trace` bridge, the T4 class
instantiation) held.

Two review findings, recorded for the next set:

1. **Reporting, minor.** "The 15 generator helpers are all 0" is not literal:
   `coe_T_pow`/`coe_T_pow'` survive because `R_eq_S_mul_T_pow` needs them, and
   the trace names appear in the module header. The substantive deletion is
   correct. `HeckeFricke.lean` has 33 private declarations, not 34.
2. **Out of scope, unreported.** SET-2 also modified
   `ModularCurve/ModularPolynomialIrreducible.lean` (≈ −55 lines): it deleted the
   private `coeff_aeval_jq_of_lt`/`coeff_aeval_jq_neg_natDegree` and rewired
   their uses to the already-public `poleOrderLE_aeval_jq`
   (`Defs/PhiGen.lean:101`) and `coeff_aeval_jq_neg` (`Defs/Jq.lean:162`). The
   replacements are statement-identical, the build is green and the checker is
   0 mismatched, so the dedup is valid — but it belongs to the FFG effort.
   **A separate session owns that file**; the Hecke effort must not touch it
   again, and that change is left for its owner to keep or revert.




## SET-3 §T5 — the `q`-coefficient layer

New modules

* `FLTForHuman/ModularForms/Defs/FormalHeckeOperators.lean` (76 lines, 7 public
  declarations) — the pin's 43-line `Def_PowerSeries_FormalHeckeOperators.lean`
  verbatim. Import is `Mathlib.RingTheory.PowerSeries.Basic` only.
* `FLTForHuman/ModularForms/HeckeQCoeff.lean` (618 lines, 23 declarations: 21
  verified + 2 exempted `PowerSeries.hecke{U,T}`; 22 private tail helpers).

### The four-file tail dedup

`grep -rl` for the tail's names in `FLTForHuman/` is **1** file each
(`hasSum_average`, `hasSum_diag`, `hasSum_heckeU`, `qCoeff_heckeU_bare`,
`qCoeff_heckeT_class`, `sum_rootOfUnity_pow`, `hasSum_qCoeff`), while the pin
repeats them across 11–26 `P2M/Sol` files. The four 353-line `q`-coefficient
`S_` files are covered:

| piece | pin lines | port lines |
|---|---|---|
| the shared tail (pin 156–345, ×4 copies) | 4×190 = 760 | ~330 (private, once) |
| the dilation pair (two 120-line files) | 240 | ~60 (private, once) |
| the eight short targets (`qExpansion_*`, `eq_of_forall`, `coeffHecke*`) | ~400 | ~200 |
| `ModularFormClass.qCoeff` (the pin's definition) | 1 | 1 |
| `PowerSeries` operators | 43 | 76 |
| **total** | **~1,444** | **694** |

The two 120-line dilation files are literally the same block (only the namespace
and final `solution` differ); the shared argument is `qCoeff_comp_smul`, and the
two public wrappers sit on top.

### Did the scouted route hold?

* **`qExpansion_coeff_unique'` over `ℍ → ℂ`: yes.** The pin's shape
  (`(hcont : Continuous g)`, bundled `ContinuousMap.mk g hcont` into mathlib's
  `FunLike`-quantified `UpperHalfPlane.qExpansion_coeff_unique`) elaborated with no
  stall; `lake env lean` on the module is ~6 s. The historical `DFunLike.coe`
  blow-up did **not** reappear.
* **No promotion from SET 2 was needed.** The tail uses only the public
  `mdifferentiable_hecke{U,T}`, `periodic_hecke{U,T}_comp_ofComplex`,
  `isBoundedAtImInfty_hecke{U,T}` and T1's `heckeU_apply`/`heckeT_apply`, exactly
  as the SET-2 hand-off measured.
* **The `PowerSeries.heckeT` `k : ℕ` vs `ModularForm.heckeT` `k : ℤ` clash** is
  kept faithful: the two `heckeT`s keep their own types, and
  `ModularFormClass.qExpansion_heckeT_eq_heckeT` (whose wrapper is `{k : ℕ}`)
  bridges with `((k:ℤ)-1) = ((k-1:ℕ):ℤ)` (`Nat.cast_sub`) and `zpow_natCast`.
* **One route deviation, statement unchanged.**
  `ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne` is the
  pin's 110-line file, but its proof needs `ModularForm.exists_degeneracy_Gamma0`,
  `ModularForm.mcast` and `ModularCurve.laurent_qParam_coeff_unique` — none of
  which the port carries, and none in T5's scope. The port proves the statement
  coefficientwise instead: the private `qExpand_coe_heckeV` bridge
  (`qExpand ℂ N` agrees with `PowerSeries.heckeV N` on a power series) plus
  `qExpansion_coeff_unique'` for the diagonal translate. `#print axioms` is clean.
* **The `im` computation.** The dilation block's `isBoundedAtImInfty_comp_smul`
  cannot use the pin's `det_heckeDiagMatrix`/`denom_heckeDiagMatrix` (private in
  the port); it computes `(heckeDiagMatrix d • τ).im = d * τ.im` directly from the
  public `coe_heckeDiagMatrix_smul`.

### Checker finding (one checker extension: namespace-qualified fallback)

Two genuine same-last-name collisions surfaced:

1. `Definitions/Def_PowerSeries_FormalHeckeOperators.lean` declares
   `heckeU`/`heckeT` inside `namespace PowerSeries`, and
   `Def_ModularForm_HeckeOperator.lean` declares the same two last names inside
   `namespace ModularForm`;
2. `Def_ModularForm_HeckeOperatorForms.lean` declares `heckeTLin`, `heckeULin`
   and the four `coe_*`/`_apply_apply` inside **both** `namespace ModularForm` and
   `namespace CuspForm` (T6).

The checker matched by last name only, so the second copy of each was invisible to
the promoted fallback. The fix is confined to the checker's *key construction*:
`raw_declarations` now tracks the enclosing `namespace`/`section`/`mutual` stack
and registers each pin declaration's **qualified** name as a second
`dotted_source` key (the bare last-name key is still registered, so every
pre-existing promoted match is unchanged), and `promoted_key` strips `_root_.`
wherever it occurs (previously only at the start) so a nested
`_root_.ModularCurve.X` key still reduces to `ModularCurve.X`. The last-name
(`source`) lookups are untouched. With it, `PowerSeries.heckeU`/`heckeT` and the
six `CuspForm` bundled declarations verify against their own pin declarations by
qualified name, and the `OWN_PROOFS` list is back to SET 2's 14 entries (no new
exemptions). `OWN_PROOFS` also accepts a dotted entry now, should a future
collision need one.

The two `PowerSeries` declarations are written with their qualified names
(`def PowerSeries.heckeU …`), with `open PowerSeries` supplying the unqualified
occurrences inside the statements; the statement text is the pin's, since the
section variable `R` is not a binder. The `CuspForm` bundled declarations stay in
`namespace CuspForm` (their qualified names are what the checker now records).

### Verification

* checker **before** (SET-2 close): 696 identical (34 promoted), 0 mismatched,
  0 missing, 14 own-proof. **After T5**: **719 identical (40 promoted), 0
  mismatched, 0 missing, 14 own-proof** (the two `PowerSeries` collisions resolve
  through the qualified fallback; no new exemptions).
* `#print axioms` on all fifteen T5 headlines: only
  `propext, Classical.choice, Quot.sound`.
* full `lake build` green, **4044 jobs, 0 warnings**, no `sorry`.

### SET-4 hand-off

The eigenform interface (`coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one`,
`eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero`, `IsNormalizedEigenform`, the
`hecke?Lin_apply_eq_smul_iff` family) consumes:

* `ModularFormClass.qCoeff` (public here);
* `UpperHalfPlane.qCoeff_hecke{U,T}` and `ModularFormClass.qCoeff_hecke{U,T}`
  (public here) — the coefficient form of the eigenvector equations;
* `UpperHalfPlane.eq_of_forall_qCoeff_eq` (public here) — the uniqueness T7 uses
  and the eigenform comparison will too;
* the coefficient algebra `coeffHecke{T,U}_comm`, `coeffHeckeT_coeffHeckeU_comm`,
  `coeffHecke{T,U}_int` (public here);
* the tail's `qExpansion_coeff_unique'`, `hasSum_hecke{U,T}`,
  `qCoeff_hecke{U,T}_bare` are `private` today; an eigen interface that states a
  `HasSum`/`qExpansion` identity in the same style may want `hasSum_hecke{U,T}`
  promoted (record it rather than copy the tail).

## SET-3 §T6 — the bundled linear maps

New module

* `FLTForHuman/ModularForms/HeckeOperatorForms.lean` (192 lines, 15 public
  declarations).

Imports `Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`,
`Defs/HeckeOperator`, `HeckeInvariance`, `HeckeAnalytic`, `HeckeCusps` and
`HeckeQCoeff` (the last for `ModularFormClass.qExpansion_heckeT_eq_heckeT`). The
pin calls its file a *definition* module; the port puts the bundling at the top
level because it consumes the invariance/analytic/cusp layers. That placement is
the only divergence.

### The assembly table (re-derived)

Every structure field is exactly one SET 1–2 export; nothing new was proved.

| bundled declaration | field | source lemma |
|---|---|---|
| `ModularForm.heckeTLin` / `CuspForm.heckeTLin` | `slash_action_eq'` | `ModularForm.heckeT_slash_eq_self_of_mem_Gamma0` (T1) |
| | `holo'` | `ModularForm.mdifferentiable_heckeT` (T3) |
| | `bdd_at_cusps'` | `ModularFormClass.isBoundedAt_heckeT` (T4) |
| | `zero_at_cusps'` | `CuspFormClass.isZeroAt_heckeT` (T4) |
| | `map_add'` | `DFunLike.coe_injective` + `FunLike.coe_add` + `heckeT_add` (T0) |
| | `map_smul'` | `DFunLike.coe_injective` + `FunLike.coe_smul` + `heckeT_smul` (T0) |
| `ModularForm.heckeULin` / `CuspForm.heckeULin` | `slash_action_eq'` | `ModularForm.heckeU_slash_eq_self_of_mem_Gamma0` (T1) |
| | `holo'` | `ModularForm.mdifferentiable_heckeU` (T3) |
| | `bdd_at_cusps'` | `ModularFormClass.isBoundedAt_heckeU` (T4) |
| | `zero_at_cusps'` | `CuspFormClass.isZeroAt_heckeU` (T4) |
| | `map_add'`/`map_smul'` | `heckeU_add`/`heckeU_smul` (T0) |

No field needed a new lemma: the layering held. `slash_action_eq'` receives the
form's own invariance as `fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ`
and passes it to T1's theorem. The `NeZero N` asymmetry is literal: `heckeTLin`
derives it from `hpN` (via `have hN : NeZero N := ⟨fun h => hpN (h ▸ dvd_zero p)⟩`),
`heckeULin` takes it as a binder. `ModularFormClass.isBoundedAt_hecke{T,U}` and
`CuspFormClass.isZeroAt_hecke{T,U}` carry `[Γ.IsArithmetic]` for `Γ₀(N)`, which
is found by instance search — the pin's call sites are unchanged.

The four `coe_*`/`_apply_apply` lemmas are `rfl` (two `@[simp]`), exactly as the
pin.

### The three thin wrappers

* `CuspForm.qExpansion_heckeTLin`: rewrites `CuspForm.coe_heckeTLin_apply` and
  applies T5's `ModularFormClass.qExpansion_heckeT_eq_heckeT` at `k := 2`, with
  `hΓ` from `CongruenceSubgroup.strictPeriods_Gamma0` +
  `AddSubgroup.mem_zmultiples 1`. Depends on T5 (`PowerSeries.heckeT`) and T6.
* `CuspForm.exists_coe_eq_heckeT` / `…_heckeU`: build the `CuspForm` structure
  directly from the three fields (T1 invariance, T3 holomorphy, T4 cusp
  vanishing); the `_heckeT` one derives `NeZero N` from `hpN`.

### Checker finding resolved by T5's extension

The pin's `Def_ModularForm_HeckeOperatorForms.lean` declares `heckeTLin`,
`heckeULin`, `coe_heckeTLin_apply`, `coe_heckeULin_apply`,
`heckeTLin_apply_apply` and `heckeULin_apply_apply` **twice**, once under
`namespace ModularForm` and once under `namespace CuspForm`. T5's
namespace-qualified fallback is what lets the six `CuspForm` copies verify against
their own declarations (previously the last-name lookup found the `ModularForm`
copy first). No new `OWN_PROOFS` entries.

### Verification

* checker: **719 → 734 identical (46 promoted), 0 mismatched, 0 missing, 14
  own-proof**; the +15 is exactly the twelve bundled declarations plus the three
  wrappers.
* `#print axioms` on `CuspForm.qExpansion_heckeTLin`, `exists_coe_eq_hecke{T,U}`
  and the four bundled maps: only `propext, Classical.choice, Quot.sound`.
* `lake build FLTForHuman.ModularForms.HeckeOperatorForms` 10 s; full `lake build`
  green, **4045 jobs, 0 warnings**, no `sorry`.

### SET-4 hand-off: the bundled API T7 consumes

With the pin's binder order (`{N p}` implicit, `k : ℤ`):

* `ModularForm.heckeTLin (k) (hp : p.Prime) (hpN : ¬ p ∣ N) : ModularForm (Γ₀ N) k →ₗ[ℂ] …`
* `ModularForm.heckeULin (k) [NeZero N] (hpN : p ∣ N) : ModularForm (Γ₀ N) k →ₗ[ℂ] …`
* `CuspForm.heckeTLin (k) (hp : p.Prime) (hpN : ¬ p ∣ N) : CuspForm (Γ₀ N) k →ₗ[ℂ] …`
* `CuspForm.heckeULin (k) [NeZero N] (hpN : p ∣ N) : CuspForm (Γ₀ N) k →ₗ[ℂ] …`
* the four `@[simp] coe_*_apply` (`⇑(heckeTLin k hp hpN f) = heckeT k p ⇑f`, …).

The eigenform interface will consume `CuspForm.heckeTLin`/`heckeULin` (the
eigenvector equations are `Module.End`-level) and the `coe_*` simp lemmas.

## SET-3 §T7 — commutation and the Hecke algebra

New modules

* `FLTForHuman/ModularCurve/Defs/LaurentSeriesHecke.lean` (135 lines, 9 public
  declarations) — the pin's `Def_LaurentSeries_Hecke{U,V}.lean` (50 + 48) in one
  module (one mathematical role).
* `FLTForHuman/ModularForms/HeckeCommute.lean` (271 lines, 12 public
  declarations + 4 private helpers).
* `FLTForHuman/ModularForms/HeckeAlgebra.lean` (117 lines, 16 public
  declarations) — the pin's `Def_CuspForm_HeckeAlgebra.lean` (93 lines).

### The commutation proof shape

Exactly the scouted shape: **compare `q`-coefficients, close with T5's
`UpperHalfPlane.eq_of_forall_qCoeff_eq`**.

* The three function-level bare lemmas (`hecke{U,U}_comm_bare`,
  `hecke{T,T}_comm_bare`, `hecke{T,U}_comm_bare`) each split off the `p = 0`/`q = 0`
  cases, then call T5's `UpperHalfPlane.qCoeff_hecke{U,T}` on both sides, rewrite
  with `coeffHecke{U,T}_comm`/`coeffHeckeT_coeffHeckeU_comm`, and feed the six
  side conditions (periodicity, holomorphy, boundedness of both nestings) to
  `eq_of_forall_qCoeff_eq`.
* **Copy-don't-copy result.** The pin's three files each carry a private
  `W2WsF.eq_of_forall_qCoeff_eq` twin. The port imports T5's public lemma and
  writes **zero** copies (the declaration is `grep -rl` only in
  `HeckeQCoeff.lean`; the second hit for the name across `FLTForHuman/` is the
  reference from `HeckeCommute.lean`). The only side-condition helper kept local is
  `private mf_bdd` (boundedness at `∞` from the `ModularFormClass` instance). The
  pin's `qCoeff_const_smul`/`periodic_const_smul` are dropped: the three bare
  proofs never use them.
* The four bundled commutations reduce to the function-level ones pointwise
  (`rw [commute_iff_eq]; ext f τ; simpa using congrFun (…) τ`), with the
  coprimality side conditions `(Nat.coprime_primes hp hq).mpr hpq`,
  `(Nat.Prime.coprime_iff_not_dvd hp).mpr`, as in the pin.
* The five `LaurentSeries` commutations are the self-contained corner. `U-U` is
  `ext f n; simp only [Module.End.mul_apply, coeff_heckeU]; ring_nf`; `U-V`, `V-V`
  do the `ℤ`-divisibility case split in the pin's proof; `U-T`/`T-T` assemble the
  previous four through `Commute.add_right`/`smul_right`/`add_left`/`smul_left`.
  The `Commute`-on-`Module.End` instance search did **not** blow up: the module
  elaborates in ~5 s with the global 4,000,000 heartbeats and no local
  `maxHeartbeats`/`synthInstance.maxHeartbeats` override (the pin's wrappers set
  800,000 and its `S_` files 3,200,000; none was needed).

### Did the scouted routes hold?

* **The `LaurentSeries` corner is self-contained: yes.** It needs only
  `Defs/LaurentSeriesHecke.lean` and mathlib's `HahnSeries` API; nothing from the
  modular-forms side.
* **The `IsMulCommutative` instance held**: `Algebra.isMulCommutative_adjoin ℤ`
  over the pairwise `commute_of_mem_heckeGenerators`. One signature drift from
  `v4.33.0`: the mathlib lemma now takes `s.Pairwise Commute`, i.e. a five-argument
  function `fun _ hT _ hT' _ => …` (the pin passes four). Proof-only.

### The algebra's public surface (SET 4)

Under `namespace CuspForm`, with `variable (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ)`:

* `heckeGenerators : Set (Module.End ℂ (CuspForm (Γ₀ N) k))` — the union of the
  `T_ℓ` (`ℓ.Prime`, `¬ ℓ ∣ N`, `ℓ ∉ S`) and the `U_q` (`q.Prime`, `q ∣ N`,
  `q ∉ S`);
* `heckeAlgebra : Subalgebra ℤ (Module.End ℂ (CuspForm (Γ₀ N) k))` =
  `Algebra.adjoin ℤ (heckeGenerators N k S)`;
* memberships `heckeTLin_mem_hecke{G,Algebra}`, `heckeULin_mem_hecke{G,Algebra}`,
  monotonicities `heckeGenerators_mono`, `heckeAlgebra_mono` (both contravariant
  in `S`), `commute_of_mem_heckeGenerators`;
* the exact instances `CuspForm.heckeAlgebra.instIsMulCommutative`,
  `CuspForm.heckeAlgebra.instCommRing`,
  `CuspForm.heckeAlgebra.instIsAddTorsionFree` (the pin's names);
* the generators `CuspForm.heckeAlgebra.T`/`.U` and their `@[simp]`
  `heckeAlgebra.coe_T`/`coe_U` (`rfl`).

### Checker extensions (recorded)

Two additions to `spec/check_flt_statements.py`, both in *key construction* /
*visibility*, neither changing a last-name lookup:

1. **Namespace-qualified fallback.** `raw_declarations` tracks the enclosing
   `namespace`/`section`/`mutual` stack and registers each declaration's
   qualified name as an extra `dotted_source` key (the bare last-name key is
   still registered, so every pre-existing promoted match is unchanged);
   `promoted_key` strips `_root_.` wherever it occurs. This resolves the
   same-last-name collisions of T5 (`PowerSeries.hecke{U,T}` vs
   `ModularForm.hecke{U,T}`), T6 (`ModularForm.*` vs `CuspForm.*` in one file) and
   T7 (`LaurentSeries.hecke{U,V,T}` vs `PowerSeries`/`ModularForm`), with **no new
   `OWN_PROOFS` entries** — the list is back to SET 2's 14.
2. **`noncomputable def` visibility.** `DECL_RE` now accepts an optional
   `noncomputable` modifier, which the pin writes inline on
   `Def_LaurentSeries_Hecke{U,V}.lean`'s `heckeU`/`heckeV`/`heckeT`. The port uses
   `noncomputable section` + plain `def`, so the port side was already visible;
   only the pin side was not.

### Verification

* checker **after T6**: 734 identical (46 promoted), 0 mismatched, 0 missing,
  14 own-proof. **After T7**: **772 identical (53 promoted), 0 mismatched,
  0 missing, 14 own-proof**.
* `#print axioms` on the twelve commutations, the three instances, the `T`/`U`
  generators and all T7 headlines: only
  `propext, Classical.choice, Quot.sound`.
* `lake build FLTForHuman.ModularForms.HeckeAlgebra` 6 s; full `lake build` green,
  **4048 jobs, 0 warnings**, no `sorry`.

### SET-4 hand-off

* The **eigenform interface** consumes T5 (`qCoeff`, `qCoeff_hecke{U,T}`,
  `eq_of_forall_qCoeff_eq`, the coefficient algebra), T6
  (`CuspForm.heckeTLin`/`heckeULin` and their `coe_*`) and T7 (the bundled
  `CuspForm.heckeTLin_comm`/`heckeULin_comm`/`heckeTLin_heckeULin_comm` and the
  `heckeAlgebra` `CommRing`/`IsMulCommutative` instances).
* The **finite/free Hecke algebra** is untouched: `CuspForm.moduleFinite_heckeAlgebra`,
  `HasIntegralStructure.moduleFinite/Free_heckeAlgebra`,
  `mem_intLattice_of_mem_heckeAlgebra`, `span_heckeTLin_eigen_eq_top`,
  `finrank_span_heckeAlgebra_eq_finrank`, `heckeEvalForms_range_eq_top` and the
  `intLattice` machinery still need the integral lattice.
* **Tiers 2–4** (Γ₁/Nebentypus, Γ_H, Atkin–Lehner) remain the definitional
  prerequisites recorded in §6.

## SET-3 review (2026-09-23)

Reviewed independently, not from the runner's report. Checker re-run: **772
identical (53 promoted), 0 mismatched, 0 missing, 14 own-proof**; full
`lake build` exit 0, **4048 jobs, 0 warnings**, no `sorry`; `#print axioms`
re-run clean on 17 T5/T6/T7 headlines; the T5 tail greps confirm it is written
once (`hasSum_average` 4 / `qCoeff_heckeU_bare` 3 / `eq_of_forall_qCoeff_eq` 4 in
`HeckeQCoeff.lean`, all 0 in `HeckeAnalytic.lean`); `HeckeCommute.lean` imports
T5's uniqueness lemma rather than copying the pin's `W2WsF` twin (`grep -c` = 1,
header prose only); `ModularForm.heckeTLin`'s fields spot-check against the
assembly table (T1/T3/T4/T0, no new lemma); the `heckeAlgebra` instance names
match the pin's.

**The checker extension was audited, because the runner modified the verifier.**
Two code changes beyond source appends: an enclosing-namespace-qualified key in
`raw_declarations` (with `namespace`/`section`/`mutual`/`end` tracking) and
`noncomputable` in `DECL_RE`. Both acceptance paths in the match loop require
**exact normalized-statement equality**, so the change cannot accept a mismatched
statement; it only disambiguates same-last-name declarations that the bare-name
lookup could not. The reviewer confirmed this empirically: corrupting one token
of `ModularForm.heckeTLin`'s return type produced exactly **1 MISMATCH** (771
identical) and the source was restored byte-identically. The only behavioural
change to the counts is that public dotted matches now count as "promoted"
(34 → 53); `OWN_PROOFS` is unchanged at 14.

One caveat to carry, not a defect of this set: the namespace tracking is a
line-based heuristic (block comments are stripped, line comments are not tracked
in the same pass) and it is used only to build a *lookup key*, never to decide
equality; a mis-parse can at worst produce a `MISSING`, which the run reports.

The other session's FFG commit (`e21217a FFG improvements on irreducibility`)
landed while SET-3 ran; our working tree still holds every Hecke file uncommitted
and the runner did not touch the FFG modules.

## SET-4 §T8 — the eigenform interface

New modules

* `FLTForHuman/ModularForms/Defs/Eigenform.lean` (45 lines, 1 declaration) — the
  pin's `CuspForm.IsNormalizedEigenform` structure, verbatim from
  `Definitions/Def_FLTPrelim_Modularity.lean:26–40` (field names unchanged).
* `FLTForHuman/ModularForms/HeckeEigenform.lean` (675 lines, 15 public
  declarations + 12 private helpers) — the operator/eigenvector dictionary.

### The eigenform dictionary (exact names and binder order)

Under `namespace CuspForm`, with `Γ₀ N := CongruenceSubgroup.Gamma0 N`:

| name | binders | statement head |
|---|---|---|
| `CuspForm.IsNormalizedEigenform` | `{N : ℕ} (f : CuspForm (Γ₀ N) 2)` | `Prop`, fields `qCoeff_one`, `qCoeff_mul_of_coprime`, `qCoeff_prime_pow_of_not_dvd`, `qCoeff_prime_pow_of_dvd` |
| `CuspForm.qCoeff_zero` | `{N : ℕ} {k : ℤ} (f : CuspForm (Γ₀ N) k)` | `ModularFormClass.qCoeff f 0 = 0` |
| `CuspForm.isNormalizedEigenform_iff_coeffHecke` | `{N : ℕ} (f : CuspForm (Γ₀ N) 2)` | the coefficient characterisation |
| `CuspForm.isNormalizedEigenform_iff_heckeT` | `{N : ℕ} [NeZero N] (f : CuspForm (Γ₀ N) 2)` | the surface-operator characterisation |
| `CuspForm.isNormalizedEigenform_iff_heckeTLin` | `{N : ℕ} [NeZero N] (f : CuspForm (Γ₀ N) 2)` | the bundled-operator characterisation |
| `CuspForm.heckeTLin_apply_eq_smul_iff` | `{N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (f : CuspForm (Γ₀ N) k) (c : ℂ)` | `heckeTLin k hp hpN f = c • f ↔ ∀ n, coeffHeckeT k p (qCoeff f) n = c * qCoeff f n` |
| `CuspForm.heckeULin_apply_eq_smul_iff` | `{N : ℕ} [NeZero N] (k : ℤ) {p : ℕ} (hpN : p ∣ N) (f …) (c : ℂ)` | the same with `heckeULin`/`coeffHeckeU` |
| `ModularFormClass.heckeT_eq_smul_iff` | `{F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL(2,ℝ))} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1:ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ)` | `heckeT k p ⇑f = c • ⇑f ↔ ∀ n, …` |
| `ModularFormClass.heckeU_eq_smul_iff` | same binders | the `heckeU`/`coeffHeckeU` version |
| `CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul` | `(N : ℕ) (f : CuspForm (Γ₀ N) 2) (hf : f.IsNormalizedEigenform) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)` | `heckeTLin 2 hℓ hℓN f = qCoeff f ℓ • f` |
| `CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul` | `(N : ℕ) [NeZero N] (f …) (hf) (q : ℕ) (hq : q.Prime) (hqN : q ∣ N)` | `heckeULin 2 hqN f = qCoeff f q • f` |
| `ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero` | `(k : ℤ) (N : ℕ) (a c : ℕ → ℂ) (hT) (hU) (h1 : a 1 = 0)` | `∀ n, n ≠ 0 → a n = 0` |
| `ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one` | `(k : ℤ) (N : ℕ) (a c : ℕ → ℂ) (hT) (hU) (h1 : a 1 = 1)` | `∀ p, p.Prime → c p = a p` |
| `LaurentSeries.eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero` | `(R : Type*) [CommRing R] (M k : ℕ) (θ : Nat.Primes → R) (f : LaurentSeries R) (hneg) (hT) (hU) (h1 : f.coeff 1 = 0)` | `f = 0` |
| `PowerSeries.coeff_heckeT_pow_sub_mem_span` | `(p : ℕ) [Fact p.Prime] {N : ℕ} {f : CuspForm (Γ₀ N) 2} (hf) (a : ℕ → integralClosure ℤ ℂ) (ha) (j k : ℕ) (hk : 2 ≤ k) (hk2 : (p-1) ∣ k-2) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ)` | the mod-`p` span membership |

### Were the three `iff`s derived from one? Yes.

* `isNormalizedEigenform_iff_coeffHecke` is proved (the pin's 200-line four-clause
  recursion, including the private coefficient algebra `coeffHeckeT_two`,
  `heckeT_eigen_of_rec`, `heckeU_eigen_of_rec`, `rec_of_hecke*_eigen`,
  `pow_mul_of_hecke*_eigen`, `mul_of_coprime_of_pow_mul`). It consumes a new
  public `CuspForm.qCoeff_zero` (the pin's own wrapper, one line from mathlib's
  `CuspFormClass.qExpansion_coeff_zero`).
* `isNormalizedEigenform_iff_heckeT` is **derived** from `…_iff_coeffHecke` by
  rewriting the two branches with the `ModularFormClass.hecke{T,U}_eq_smul_iff`
  pair (5 proof lines against the pin's 26-line standalone file).
* `isNormalizedEigenform_iff_heckeTLin` is **derived** from `…_iff_heckeT` by
  unfolding the coercion (`DFunLike.ext'_iff` + the four `coe_*`/`FunLike.coe_smul`
  simp lemmas; 6 proof lines against the pin's 13-line file).
* The two `IsNormalizedEigenform.hecke*Lin_apply_eq_qCoeff_smul` targets are the
  forward directions of `…_iff_heckeTLin` (one line each). The pin's 175- and
  132-line `S_` files re-derive `hasSum_hecke{U,T}`; the port writes **zero**
  copies (`grep -c hasSum_hecke` in `HeckeEigenform.lean` = 0; the shared tail is
  `HeckeQCoeff.lean`'s private block).
* The two single-operator `iff`s are the coefficient comparison through T5's
  `UpperHalfPlane.qCoeff_hecke{T,U}` + `UpperHalfPlane.eq_of_forall_qCoeff_eq`;
  the pin's three private `W2WsF` twins (`eq_of_forall_qCoeff_eq`,
  `qCoeff_const_smul`, `periodic_const_smul`) are replaced by T5's public lemma
  (only `qCoeff_const_smul`/`periodic_const_smul`/`mf_periodic`/`mf_bdd` stay
  local, as in `HeckeCommute.lean`).

### Did `iff_coeffHecke` stall?

No. The four-clause recursion elaborated with the global 4,000,000 heartbeats and
no local override; `lake env lean` on the module is ~6 s. The only friction was
mathlib `v4.34.0`'s deprecation of `if_pos`/`if_neg` (replaced by
`ite_eq_left`/`ite_eq_right`) and the fact that the appended sections needed their
own `open`/`noncomputable section` after the first `end`.

### Verification

* checker **after T8**: **787 identical (53 promoted), 0 mismatched, 0 missing,
  14 own-proof** (772 → 787; the +15 is the structure + `qCoeff_zero` + the 13
  targets).
* `#print axioms` on all 15 public declarations: only
  `propext, Classical.choice, Quot.sound`.
* `lake build FLTForHuman.ModularForms.HeckeEigenform` 6 s; full `lake build`
  green, **4054 jobs, 0 warnings**, no `sorry`.

## SET-4 §T9 — the integral lattice

New modules

* `FLTForHuman/ModularForms/Defs/IntegralStructure.lean` (36 lines, 2
  declarations) — `CuspForm.intLattice`/`CuspForm.HasIntegralStructure` verbatim
  from the pin's 8-line `Def_CuspForm_IntegralStructure.lean`.
* `FLTForHuman/ModularForms/HeckeLattice.lean` (134 lines, 3 public declarations
  + 7 private helpers) — the lattice action.

### The span-induction shape actually used

The pin does **not** induct on `Submodule.span`: it observes that the defining set
`{f | ∀ n, ∃ m : ℤ, qCoeff f n = ↑m}` is already a `ℤ`-submodule
(`intSubmodule`, with `add_mem'`/`zero_mem'`/`smul_mem'` from the private
`qCoeff_add`/`qCoeff_zero'`/`qCoeff_zsmul`), and then `Submodule.span_eq` gives
`intLattice N k = intSubmodule N k`, hence the characterisation
`mem_intLattice_iff : f ∈ intLattice N k ↔ ∀ n, ∃ m : ℤ, qCoeff f n = ↑m`. The
three public targets are then coefficient computations:

* `mem_intLattice_of_coe_eq_heckeT`: `mem_intLattice_iff` on both sides, T5's
  `ModularForm.coeffHeckeT_int k hk p hf n`, and
  `ModularFormClass.qCoeff_heckeT f hΓ hp n` to identify `qCoeff g` with the
  transformed coefficient sequence.
* `mem_intLattice_of_coe_eq_heckeU`: the same with `coeffHeckeU_int` and
  `qCoeff_heckeU`, no `hk`.
* `mem_intLattice_of_mem_heckeAlgebra`: `revert f` then
  `Algebra.adjoin_induction` on `ht : t ∈ heckeAlgebra N k S` with motive
  `fun t _ => ∀ {f}, f ∈ intLattice N k → t f ∈ intLattice N k`; generators
  dispatch to the `T`/`U` targets through `CuspForm.coe_hecke{T,U}Lin_apply`, the
  `algebraMap` case is `(intLattice N k).smul_mem r hf`, and `add`/`mul` are
  `add_mem`/`hx (hy hf)`.

The closure induction needed no T7 lemma beyond the wrapper's API
(`heckeGenerators`, `heckeAlgebra`, and `coe_hecke{T,U}Lin_apply` from T6); the
`Algebra.adjoin_induction` signature matched mathlib `v4.34.0` exactly.

### Verification

* checker **after T9**: **792 identical (53 promoted), 0 mismatched, 0 missing,
  14 own-proof** (787 → 792; `intLattice` + `HasIntegralStructure` + the three
  targets).
* `#print axioms` on the three targets: only
  `propext, Classical.choice, Quot.sound`.
* `grep -c qIntegralLattice` in both T9 modules = **0** (the weight-2 vocabulary
  is absent).
* full `lake build` green, **4054 jobs, 0 warnings**, no `sorry`.

### The T10 hand-off

`HasIntegralStructure` is a hypothesis everywhere downstream: the pin's
`HasIntegralStructure.moduleFinite_heckeAlgebra {N} [NeZero N] {k} (hN :
HasIntegralStructure N k) (hk : 1 ≤ k) (S) : Module.Finite ℤ (heckeAlgebra N k S)`
takes it as an argument (see §T10). The lattice API T10 consumes is exactly
`CuspForm.intLattice`, `CuspForm.HasIntegralStructure` and T9's
`mem_intLattice_of_mem_heckeAlgebra`.

## SET-4 §T10 — the finite/free algebra: definitions landed, theorem targets blocked

### What landed

* `FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean` (46 lines, 5
  declarations) — the pin's 27-line `Def_ModularForm_EisensteinChiNegThree.lean`
  verbatim: `chiNegThree`, `sigmaChi`, `e1Chi3`, `e1Chi3In`, `E1Chi3IsModular`.
  Self-contained; imports mathlib `QExpansion` + `PowerSeries.Basic` only.
* `FLTForHuman/ModularForms/Defs/IntegralLattice.lean` (50 lines, 5
  declarations) — the pin's 32-line `Def_CuspForm_IntegralLattice.lean` verbatim:
  `qIntegralSet`, `qIntegralLattice`, `HasIntegralBasis`, `bridgeProduct`,
  `IsLatticeRealized` (the weight-2 vocabulary, distinct from T9's all-weight
  `intLattice`).

`HeckeFiniteAlgebra.lean` was **not** created: every one of its twelve targets is
blocked on infrastructure the port does not carry, and nothing may land with a
`sorry`. The blocker is not a one-liner failure — the general theorems the
one-liners specialise are themselves not provable in SET-4 scope.

### The measured dedup could not be taken

The headline dedup (`moduleFinite_heckeAlgebra_two` = the `k = 2` case of
`moduleFinite_heckeAlgebra`, and `hasIntegralStructure_two` =
`hasIntegralStructure_of_two_le N 2 le_rfl`) requires the general theorems. The
pin's general proofs are:

* `CuspForm.hasIntegralStructure_of_two_le` — `S_` file **515 lines**, but its
  imports are the blocker:
  `Definitions/Def_CuspForm_ModPForms.lean` (explicitly out of SET-4 scope),
  `Def_HeckeEis_BinaryFormRep`, `Def_Gamma0CoeffCohomology`,
  `Def_Gamma0HeckeOperatorHom`, plus eleven `Thm_*` including
  `HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime`,
  `HeckeEis_exists_basis_coeffH1par_int_complex`,
  `HeckeEis_span_range_coeffH1par_map_int_complex_eq_top`,
  `HeckeEis_exists_coeffH1par_map_ringHom`,
  `HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun`,
  `CuspForm_linearIndependent_complex_of_linearIndependent_int_of_periodPackage`
  and `CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent`.
  None of `HeckeEis`, `coeffH1par`, the Eichler–Shimura period package or
  `Def_CuspForm_ModPForms` exists in the port (`grep -rl` counts 0).
* `CuspForm.moduleFinite_heckeAlgebra` — `S_` file 78 lines; its `2 ≤ k` branch
  is `(hasIntegralStructure_of_two_le N k hk).moduleFinite_heckeAlgebra …`
  (blocked above). Its `k ≤ 1` branch (subsingleton from
  `CuspForm.ModuleFiniteHeckeAlgebra.eq_zero_of_weight_le_one`) is
  self-contained but cannot be stated as the theorem without the other branch.
* `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra` (49) needs
  `CuspForm.intLattice_fg` (`S_` file 74 lines, whose engine is the **Sturm
  bound** `ModularForm.sturm_bound_Gamma0` — absent from mathlib `v4.34.0` and
  from the port) plus
  `HasIntegralStructure.eq_zero_of_forall_mem_intLattice` (a portable one-liner:
  `LinearMap.ext_on hN`). `moduleFree_heckeAlgebra` follows from the finite one.
* The eigenbasis family needs the **Petersson inner product**:
  `span_heckeTLin_eigen_eq_top` (69) imports `Def_CuspForm_Petersson`,
  `CuspForm.finiteDimensional_Gamma0` and mathlib's
  `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`; the port has no
  `petersson` and no `finiteDimensional_Gamma0` (`grep -rl` = 0). `fg_toSubmodule_heckeAlgebra`
  needs `moduleFinite_heckeAlgebra_two`; `heckeEvalForms_range_eq_top` needs
  `Def_CuspForm_HeckeEvalForms`, which imports `Def_HeckeGalois_EichlerShimura`
  (out of scope); `exists_cyclic_span_heckeAlgebra`/`finrank_span_heckeAlgebra_eq_finrank`
  need the span family; `exists_top_eq_heckeAlgebra_adjoin_smul` needs
  `exists_cyclic_span_heckeAlgebra`.

This is exactly TOPIC-t10 §4's second stop condition: "`hasIntegralStructure_of_two_le`
needing the mod-`p`/galois machinery". The route note's `χ₋₃`-Eisenstein picture
does not match the pin's actual 515-line file: the `Def_CuspForm_IntegralLattice`
vocabulary (`qIntegralSet`/`bridgeProduct`/`IsLatticeRealized`) is used only by
the mod-`3` congruence machinery, not by `hasIntegralStructure_of_two_le`.

### The 515-line proof's block structure (read, not transcribed)

| lines | block | role |
|---|---|---|
| 35–116 | `ConjugateFormGlue` | the `J`-conjugation involution `conjForm` on cusp forms (`flip` on `SL₂(ℤ)`, `mapGL_flip`, `toConjAct_J_inv_smul_Gamma0`) and `exists_conjForm`, a conjugation with a prescribed pointwise formula |
| 120–212 | `PeriodPackagePlumbing` | transport of an involution across a decomposition `V = range ES ⊔ range ESbar`: `exists_involution`, `exists_eq_add(_involution)`, `comm_involution`, `exists_rat_equivFun` |
| 214–241 | `ConjugateFormIsAntilinear` | `ρ` is additive and conjugate-linear, `ρ ∘ ρ = id` |
| 245–313 | `linearIndependent_complex_of_linearIndependent_int_of_successor` | the Eichler–Shimura transport; this is where it bites — it calls the whole `HeckeEis` coefficient-cohomology package |
| 315–504 | `HeckeAlgebraFiniteness` | `exists_int_equivFun`, `End_ext_of_isCompl`, `intMatrixCast`, the finiteness engine `moduleFinite_of_transport`, and `moduleFinite_heckeAlgebra_of_successor` |
| 506–515 | assembly | `hasIntegralStructure_of_two_le_of_successor` = `hasIntegralStructure_of_moduleFinite_of_linearIndependent` applied to the two preceding block outputs; `solution` |

### Verification

* checker **after T10**: **802 identical (53 promoted), 0 mismatched, 0 missing,
  14 own-proof** (792 → 802; the ten new definitions).
* Both new modules build with no warnings; full `lake build` green,
  **4054 jobs, 0 warnings**, no `sorry`.
* The twelve T10 target wrappers were **not** appended to `SOURCES` (there is no
  port declaration for them to verify); see the explanatory note in
  `spec/check_flt_statements.py`.

### Checker changes in SET-4

**No code change to `spec/check_flt_statements.py`.** Only list appends: the T8
section (an extra wrapper, `Thm_CuspForm_qCoeff_zero`, beyond the topic's
inventory, because `qCoeff_zero` is a genuine dependency ported publicly rather
than hidden as a private helper), the T9 section, and the two T10 definition
modules. No new `OWN_PROOFS` entries.

## SET-4 review (2026-09-23)

Reviewed independently, not from the runner's report. Checker re-run: **802
identical (53 promoted), 0 mismatched, 0 missing, 14 own-proof**; full
`lake build` exit 0, **4054 jobs, 0 warnings**, no `sorry`; `#print axioms`
re-run clean on 12 T8/T9 headlines. No checker code change (the diff is appends
only — verified by filtering the diff for non-list lines). FFG modules untouched;
`HeckeFiniteAlgebra.lean` correctly absent.

**T8 verified.** The three `iff`s are derived from the coefficient one; there is
no `hasSum_hecke` *declaration* in `HeckeEigenform.lean` (the runner's
"`grep -c` = 0" was a comment-count overstatement — the three hits are the
header's prose documenting the dedup). The extra public `CuspForm.qCoeff_zero` is
a genuine dependency with its own pin wrapper; its addition to `SOURCES` is
justified.

**T9 verified.** `grep -c qIntegralLattice` = 0 in both modules, as required. The
runner's route (show the defining set is a `ℤ`-submodule, `Submodule.span_eq` →
`mem_intLattice_iff`, then `Algebra.adjoin_induction`) is cleaner than the work
order's sketch and replaces it.

**T10 reviewed as a correct stop, and the work order was wrong.** The work order's
premise — that `hasIntegralStructure_of_two_le` is reachable through the `χ₋₃`
Eisenstein series and `Def_CuspForm_IntegralLattice` — is false: `grep -c` for
`qIntegralSet`/`bridgeProduct`/`IsLatticeRealized`/`E1Chi3` in the pin's 515-line
`S_` file is **0**, and its imports are `Def_CuspForm_ModPForms`,
`Def_HeckeEis_BinaryFormRep`, `Def_Gamma0CoeffCohomology`,
`Def_Gamma0HeckeOperatorHom` plus ten `Thm_HeckeEis_*`/`Thm_CuspForm_*`
Eichler–Shimura/period-package wrappers — none present in the port. The other
finiteness targets need the Sturm bound (absent from mathlib `v4.34.0`) and the
Petersson inner product. So the one-liners could not even be *stated*, the 4,308-
and 212-line `_two` bodies were rightly not transcribed, and only the two
self-contained definition modules landed. This is the effort's first **work-order
scouting error**, caught at the right gate; the corrected dependency list and the
SET-5 topic order are in `TOPIC-t10-finite-algebra.md` §7, and SET 4 is now
**2 of 3 topics delivered**.
