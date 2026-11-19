# SET-AF85 — the archimedean `K`-types, the unramified Whittaker shell, and the volume of the Siegel slab

**Status: LANDED (2026-11-14).** The third set of the wave, cut from the shelf SET-AF84
landed on: **9 rows / 3,733 silo** in **three orders**, five modules (two new).

| # | order | rows | silo | module(s) | pin publics on the wire | manager-scaffolded | order-scaffolded |
|---|---|---|---:|---|---:|---:|---:|
| A | the archimedean `K`-types and the Weyl/Bruhat piece | 4 | 2,054 | `EisensteinGeneral/ArchKType.lean` (new), `EisensteinGeneral/ArchIntegralBound.lean` | 2 + 2 | 4 | — |
| B | the unramified Whittaker shell | 2 | 1,264 | `RepTheory/LocalLanglands/WhittakerShell.lean` (new) | 85 | 2 | 83 |
| C | the volume of the Siegel slab and the cuspidal exhaustion | 3 | 415 | `AutomorphicForm/Adelic/Siegel/SlabVolume.lean` (new), `…/Cusp/IrreducibleSpine.lean`, `…/Siegel/FiniteCover.lean` | 3 + 5 + 1 | 9 | — |

Per-order pin load is 415–2,054 lines, and the engine count is the number that matters for the workers:
**A transcribes 93 private declarations** (the two `K`-type files share 12 of them, 186 lines, written
once), C 8, and B 0 private — its two pins are *flattened* files whose 85 declarations are all public,
which makes its public surface the order's step 1.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_after_af85.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **548 / 251,878** |
| ready rows | **22 / 6,398** |
| leaves | **118 / 30,021** |
| withheld (FR-0044 guard) | 4 / 831 |

Exactly SET-AF84 §5's measured post-landing figures — no drift since that landing, so the instrument and
the tree agree. The ready block's head is the two `EisensteinGeneral.Arch` `K`-types (1,794 silo between
them), then the two `UnramifiedWhittaker` rows (1,264), then the `WeierstrassCurve` / `GaloisRep` rows of
other columns. The leaves block is unchanged from AF84 and carries this column's own subject matter
(`AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite` 576,
`LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift` 501,
`AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` 445,
`LanglandsTunnell.exists_heckeCosetSystem_productionPinsCompact_of_not_dvd` 446,
`AutomorphicForm.exists_isArchBiFinite_rightConv_comp_inv` 376,
`AutomorphicForm.WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` 282,
`AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` 328 …); none of them is
cut here, and the 12,126-line `M4aTorus.completedRayL_fe` belongs to the in-flight Hecke wave.

## 1. The cut

The three orders are SET-AF84's forecast successor (the two `Arch` `K`-types of order D's return and the
two `UnramifiedWhittaker` rows of order C's), plus the first of the rows the last set readied.

| # | row | silo | lev | pub | priv |
|---|---|---|---:|---:|---:|
| A1 | `EisensteinGeneral.Arch.exists_complexKType` | 1,004 | 2/4 | 1 | **59** |
| A2 | `EisensteinGeneral.Arch.exists_realKType` | 790 | 2/4 | 1 | 46 |
| A3 | `EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum` | 122 | 1/1 | 1 | 2 |
| A4 | `AutomorphicForm.isInducedSection_etaFst_etaSnd_neg_weylIntertwiningIntegral` | 138 | 3/10 | 1 | 0 |
| B1 | `UnramifiedWhittaker.mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero` | 646 | 1/4 | 40 | 0 |
| B2 | `UnramifiedWhittaker.exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero` | 618 | 2/3 | 45 | 0 |
| C1 | `AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul` | 273 | 1/4 | 5 | 0 |
| C2 | `AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain` | 119 | **11/81** | 3 | 0 |
| C3 | `AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat` | 23 | 3/31 | 1 | 4 |

**The three stories.** A is the archimedean factor of the Eisenstein piece: the two `K`-type existence
statements (an integral `J w ζ` holomorphic in `w`, with the pin's uniform exponential decay) and the two
rows that make the piece usable downstream — the Bruhat series' Whittaker coefficient as a finite sum, and
the Weyl intertwining integral of an induced section being an induced section with the characters
`(μ, ν)` exchanged and `s ↦ -s`. The `K`-types are pure analysis over `ℂ` and `ℝ` (their only premise is
AF84's archimedean bound row), and the two files are 80 % the same text: 12 shared declarations, 186 lines
written once. B is the local unramified Whittaker model continued: the Hecke-recursion identity on the
shell `det ↦ max(|bottom row|)²` with the vanishing of the negative half, and the nonvanishing of `W` at
`diagOne a₀ * g₀` for a function that is a Hecke eigenfunction away from a finite `S`. C is the slab's
volume and the cuspidal exhaustion: the Haar measure of a fundamental domain of the determinant-norm slab
is finite (the finite Siegel cover plus the fundamental-domain translation), the exhaustion of a compact
operator's eigenspace by pairwise orthogonal irreducible cusp subrepresentations (with the three generic
Hilbert-space lemmas it runs on), and the `ℚ` case of the production cover.

**Why C is worth its 415 silo.** Its two cheap rows are unblocking rows of the shelf, not tail work:
`adelicGLHaar_inter_…` is cited by 81 nodes project-wide and its landing readies the two
`setIntegral_archDerivAt…` rows (392 + 385 silo), and `coversModCentre_productionPinsGeneral_D_rat`
readies the 950-line `LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_…` row. 1,727 silo of
shelf is opened by 142 silo of proof.

## 2. The homes and the scaffolds

| module | home | imports the vocabulary from |
|---|---|---|
| `EisensteinGeneral/ArchKType.lean` | new, beside the archimedean core | `EisensteinGeneral/ArchIntegralBound.lean` (its premise `Arch.exists_norm_archIntegral_le`), `Mathlib.MeasureTheory.Measure.Lebesgue.Complex` |
| `EisensteinGeneral/ArchIntegralBound.lean` | append, the same subject as its four landed rows | its own closure |
| `RepTheory/LocalLanglands/WhittakerShell.lean` | new, beside `UnramifiedWhittaker` and `WhittakerRecursion` | `RepTheory/LocalLanglands/{UnramifiedWhittaker,WhittakerRecursion}`, `NumberTheory/AdelicLevel/{Level,HeckeGen}`, `AutomorphicForm/Adelic/SmoothAutomorphicFn` |
| `AutomorphicForm/Adelic/Cusp/IrreducibleSpine.lean` | append, the cuspidal-spectrum subject already there | its own closure; the three generic `Submodule` lemmas at the pin's names |
| `AutomorphicForm/Adelic/Siegel/SlabVolume.lean` | new, in the Siegel subject | `Siegel/FiniteCover` (the cover row), `Siegel/SlabCoveringTheorems` (the slab cover), `IdeleNormDet`, `NumberTheory/NumberField/TateGlobalIdeleNormDet` |
| `AutomorphicForm/Adelic/Siegel/FiniteCover.lean` | append, beside its premise `centreCutSiegelSet_coversModCentre_rat` | its own closure |

Two home decisions are worth recording.

* **The two Eisenstein rows go into `ArchIntegralBound.lean`, not into the Weyl modules.** Their premise
  `Piece.integral_smul_add_mul_addChar_neg_mul_eq` lives there, and that module is above every
  `AutomorphicForm/Adelic/WeylIntertwining*` module (it imports `WeylIntertwining`), so a home in the Weyl
  subject would be a cycle. The module is the analytic core of the same piece, and it is the file order A
  builds its own module against, so one order owns the file and no two orders can race on it.
* **`SlabVolume.lean` is a new module** rather than an insertion into `FiniteCover.lean` (a 1,846-line hub
  whose heartbeat floor sits at 29 k) or into the legacy `NumberTheory/SiegelVolume.lean` (which is *below*
  the cover and so cannot host a proof that cites it). Its subject — the finiteness of the slab's volume —
  is not the cover's and not the covering lemma's, and the module carries the pin's two public engine
  lemmas beside the row, not a headline alone.

No legacy home is touched and no hub is edited that another order builds against: A owns
`ArchIntegralBound.lean`, C owns `IrreducibleSpine.lean` / `FiniteCover.lean` / the new `SlabVolume.lean`,
B owns its own new module. All three orders run concurrently and only the build lock is shared.

| module | scaffold state | `check_port` at scaffold | `scaffold_audit` at scaffold |
|---|---|---:|---|
| `EisensteinGeneral/ArchKType.lean` | 2 headlines, `sorry` | **2 ok / 0 / 0** | complete |
| `EisensteinGeneral/ArchIntegralBound.lean` | 4 rows landed + 2 headlines, `sorry` | **6 ok / 0 / 0** | complete |
| `RepTheory/LocalLanglands/WhittakerShell.lean` | 2 headlines, `sorry` | **2 ok / 0 / 0** | 2 FOLDED + 83 MISSING (the order's step 1) |
| `AutomorphicForm/Adelic/Cusp/IrreducibleSpine.lean` | 16 landed + 5 headlines, `sorry` | **21 ok / 0 / 0** | complete |
| `AutomorphicForm/Adelic/Siegel/SlabVolume.lean` | 3 headlines, `sorry` | **3 ok / 0 / 0** | complete |
| `AutomorphicForm/Adelic/Siegel/FiniteCover.lean` | 2 landed + 1 headline, `sorry` | **3 ok / 0 / 0** | complete |

The scaffolds are transcribed **in the pin's own spelling**: `check_port` compares the parsed statement
text, so a fully qualified `AutomorphicForm.SiegelCovering.CoversModCentre` in the port against the pin's
bare `CoversModCentre` reads as `MISSING` (measured on C3's first scaffold run). The two measure lemmas are
written with the pin's `local notation "G"` / `"μH"`, and the row's statement keeps its `let α := …`
`letI` shape verbatim.

## 3. The orders and the gates

Orders in `lean/tmp/af85/WO.md`. The gates are SET-AF84's six:

1. `check_port --force` → the module's **full** pin public count `ok`, `0 mismatch / 0 missing / 0 own`.
2. `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <module>` → **silent** (`lake build` per module
   under `flock`/`timeout` for the olean).
3. `#print axioms` on every row and on the largest engine declaration → `[propext, Classical.choice, Quot.sound]`.
4. `dedup.py --within --module <stem>` → 0 clusters, or the pin's own engine/row pair with the reason recorded.
5. `move_dead.py --source <module> --target /dev/null --dry-run` → `0 declarations, 0 lines`.
6. **A heartbeat *probe*, recorded in the module header — never a `set_option`** (playbook §3.5, FR-0225).

Plus `scaffold_audit` reading **complete** at the end — which for B is the proof that step 1 happened — and a
`spec/` consumer per order written by the manager on landing.

## 4. The forecast, measured with the scaffolds on disk

The nine rows are declared (wire green, `sorry` bodies), so a re-run of §0's read *is* the post-landing
forecast:

| figure | §0 | forecast (AF85) |
|---|---:|---:|
| `needed [F terminal]` | 548 / 251,878 | **539 / 248,145** |
| ready rows | 22 / 6,398 | **16 / 4,392** |
| leaves | 118 / 30,021 | **118 / 30,021** |
| withheld | 4 / 831 | 4 / 831 |

**Three rows become ready**, one for each of the two unblocking rows of order C:

| row readied by the set | silo | by |
|---|---:|---|
| `LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable` | 950 | C3 |
| `AutomorphicForm.setIntegral_archDerivAtComplex_mul_conj_add_eq_zero_of_isFundamentalDomain` | 392 | C2 |
| `AutomorphicForm.setIntegral_archDerivAt_mul_conj_add_eq_zero_of_isFundamentalDomain` | 385 | C2 |

The next scoping pass opens on a ready block whose head is that 950-line Converse row (whose nine premises
are now ported) together with the two `setIntegral_archDerivAt` rows — 1,727 silo of one subject, the
Petersson/integral side of the cusp forms — plus the `WeierstrassCurve` (697 + 599) and `GaloisRep` (495)
rows of the other columns.

## 5. What was deferred, and why

The remaining ready block, named rather than silently dropped (FR-0040): `WeierstrassCurve` 697 / 599 and
`GaloisRep` 495 (other columns), `LanglandsTunnell.Converse` 950 and the two `setIntegral_archDerivAt` rows
392 / 385 (readied *by* this set; the next cut), `MeasureTheory.exists_integral_conj_apply_smul_ne_zero_…`
200 and `NumberField.AdelicHaar.isMulRightInvariant_…` 84 (their columns), `ValuationSubring` 138,
`NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul` 120,
`AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite` 113 (its `Def_` prefix
pulls `Def_HeckeCharacter_FiniteOrder`, a different subject — recorded in SET-AF84 §1 as well),
`ModularForm.exists_gamma0_qExpansion_div_eq_E4_cube_div_discriminant` 66, the `ModularCurve` rows 36 / 34
/ 24 and `AlgebraicCurve` 59 (other columns).

## 5. The landing

All nine rows in, no `sorry`, six modules (three new), three consumers. The measured shelf re-read is
the forecast to the line.

| file | rows | lines | decls | checker | probe (silent / fails) |
|---|---|---:|---|---|---:|
| `EisensteinGeneral/ArchKType.lean` (new) | A1–A2 | **1,656** | 95 (2 + 93) | **2 ok / 0 / 0** | 78,000 / 39,000 |
| `EisensteinGeneral/ArchIntegralBound.lean` | A3–A4 | **897** (was 728) | 31 (6 + 25) | **6 ok / 0 / 0** | 37,000 / 18,000 |
| `RepTheory/LocalLanglands/WhittakerShell.lean` (new) | B1–B2 | **1,338** | 85 (85 + 0) | **84 ok + 1 own / 0 / 0** | 20,000 / 10,000 |
| `AutomorphicForm/Adelic/Cusp/IrreducibleSpine.lean` | C1 | **1,010** (was 719) | 36 (21 + 15) | **21 ok / 0 / 0** | 35,000 / 32,000 |
| `AutomorphicForm/Adelic/Siegel/SlabVolume.lean` (new) | C2 | **162** | 3 (3 + 0) | **3 ok / 0 / 0** | 10,000 / 9,000 |
| `AutomorphicForm/Adelic/Siegel/FiniteCover.lean` | C3 | **1,867** (was 1,846) | 111 (3 + 108) | **3 ok / 0 / 0** | 30,000 / 28,000 |
| | **9** | **+3,637** | **+193 (9 rows + 184 engines)** | **119 ok + 1 own, 0 mismatch, 0 missing** | |

Every module is silent at `-DmaxHeartbeats=200000` with **no** in-file `set_option` (the pairs above are
header comments, per FR-0225); axioms `[propext, Classical.choice, Quot.sound]` on every row and on the
largest engine of each module; `move_dead` reads `0 declarations, 0 lines` on all six; `dedup --within`
reads 0 clusters on all six; `scaffold_audit` reads **complete** on all six — for B that is the proof that
its 83-declaration step 1 actually happened (`2 FOLDED + 83 MISSING` → `complete`, identical at the end of
step 1 and at the end).

Consumers, each 0 errors / 0 warnings: `spec/EisensteinGeneralSetAF85AConsumer.lean` (4 zones: the two
`K`-types at vanishing weight, the Bruhat-series row at one summand, the Weyl integral applied twice —
the `(μ, ν, s) ↦ (ν, μ, -s)` involution), `spec/UnramifiedWhittakerSetAF85BConsumer.lean` (3 zones: the
single Hecke step and the shell's zero step at `m = 1`, the nonvanishing row at `S = ∅`),
`spec/AutomorphicFormSetAF85CConsumer.lean` (4 zones: the volume row at `α = 1, β = 2`, the two engine
lemmas at a singleton covering set, the exhaustion's nontriviality `v ≠ 0 → ∃ i, vs i ≠ 0`, and the `ℚ`
cover unfolded).

### What the workers' diagnoses overrode in this brief

1. **C1's second premise was not in the scaffold's import closure.** The brief said both premises were
   imported. `Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq` lives in
   `Analysis/Normed/Operator/CompactFiniteDimensional.lean`, which nothing in `IrreducibleSpine`'s
   354-module closure imports, and its `.olean` was absent (only hash/trace in `.lake/build`). The worker
   reported it at first belief, built the one dependency, and added the single `import` line — the
   right call, and the brief's claim was a grep-level check where a BFS was needed. The order also
   misnamed the premise `…_forall_eq`; the WO now carries the real last name.
2. **C2's scaffold lacked two things the pin's proof needs**: `open scoped Pointwise` (the `Set.image_mul_right`
   / `γ • D'` set-smul notation) and the pin's countable-instance chain. Both were supplied proof-side as
   class-typed `have` binders, so the module kept its `0 own` and no `Countable` instance leaks into an
   importer — the pin's five `scoped instance`s are not transcribed (FR-0223's precedent).
3. **A's shared block is 185 lines, not 186, and not `diff`-clean**: the real pin writes the premise
   unqualified where the complex pin qualifies it. Written once anyway (the complex pin's copy).
   The pins' "59 + 46 private" are *file* counts that double-count the shared twelve; the unique engine
   count is 47 + 34, and the module's 93 private declarations confirm it.
4. **The `ArchIntegralBound` header's heartbeat figure was stale** (AF84D's 12,000 / 6,000): the module's
   floor is now 36–37 k, and the new Weyl row is its peak. Any older note quoting 12 k means "before
   AF85A".
5. **B's "85 ok" target could not hold** — see FR-0228: the equation-clause declaration is on an `own:`
   marker (`84 ok + 1 own`), and the WO's `scaledGL` was a name from a neighbouring pin (struck).
6. **`HilbertExhaust` stays** as the namespace of the two automorphic declarations of C1: it is a
   descriptive name for the Hilbert-space exhaustion (the pin's), not a pipeline label like `Ws48Perp` or
   `C8P1`; recorded here so the next pass does not re-litigate it.

### The set's numbers

| figure | before | **after** (measured) | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 548 / 251,878 | **539 / 248,145** | 539 / 248,145 ✓ exact |
| ready rows | 22 / 6,398 | **16 / 4,392** | 16 / 4,392 ✓ exact |
| leaves | 118 / 30,021 | **118 / 30,021** | 118 / 30,021 ✓ exact |
| withheld | 4 / 831 | **4 / 831** | 4 / 831 ✓ exact |

The three readied rows are the forecast's three, and each is attributable to one of order C's cheap rows:
`LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable`
(950, by `coversModCentre_productionPinsGeneral_D_rat`) and
`AutomorphicForm.setIntegral_archDerivAt{,Complex}_mul_conj_add_eq_zero_of_isFundamentalDomain` (392 + 385,
by `adelicGLHaar_inter_…`). 142 silo of proof opened 1,727 silo of shelf.

The next cut is that block: the 950-line Converse row plus the two `setIntegral_archDerivAt` rows (1,727
silo, one subject — the Petersson/integral side of the cusp forms, all premises now ported), with the
`WeierstrassCurve` 697 / 599 and `GaloisRep` 495 rows left to their own columns.
