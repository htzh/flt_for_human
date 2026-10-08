# S-3 work order — the primitive-coset / `jLattice` column

**Status: drafted 2026-10-07; the node cites no row node (leaf, 0 premises), but S-2 lands two
lemmas this file also carries (`kw_scale_lattice_toAddSubgroup`, `kwSublatticeIndex_scale`,
byte-identical statements — verified), so dispatch after S-2 lands and **import** them rather
than redeclare; the shared `check_flt_statements.py` / log edits also serialize.** Third set of
row S; reconnaissance is [TOPIC-V5-row-S-scoping.md](TOPIC-V5-row-S-scoping.md) §2.3 and §5.4,
re-measured here. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.
Depends only on landed sets: P-SET-1/P-SET-2
(`Elliptic/PeriodPair/{Basic,Lattice,Discriminant,Uniformization,JLine}.lean`) and
`ModularCurve/Defs/PrimCosetReps.lean` (the `ModularCurve.primCosetReps` API). Method:
[../../porting-playbook.md](../../porting-playbook.md) §0.2, §2.1–§2.4, §3.1–§3.5, §4–§5.

## 1. Scope

Land the row's **primitive-coset / `jLattice` column**: the node

`PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic` (848 pin lines) — given
`(L'.lattice : Set ℂ) ⊆ L.lattice`, `sublatticeIndex L L' = N` and
`IsAddCyclic (sublatticeQuotient L L')`, produce `a b d : ℕ` and `τ σ : ℍ` with
`(a, b, d) ∈ ModularCurve.primCosetReps N`, `(σ : ℂ) = ((a : ℂ) * τ + b) / d`,
`L.jLattice = (PeriodPair.ofTau τ).jLattice` and
`L'.jLattice = (PeriodPair.ofTau σ).jLattice`.

This is the bridge from an abstract lattice inclusion to the classical `τ`-model: normalise the
sublattice by an integer `SL₂(ℤ)`-type transformation to a `a, b, d` HNF triple whose coset is
primitive, then read the `j`-invariants off `ofTau`. Its hypothesis shape is exactly S-2's
conclusion shape (`(L'.scale β).lattice ⊆ L.lattice` etc.), so it is the piece SC feeds S-2's
`β` into.

**Not this set:** S-4 (the `E₄³ − E₆²` / `jLattice` modular-polynomial tail), the capstone
(SC), and S-2's lattice/index arithmetic. The node cites **no** row nodes (0 premises), so this
set has no hand-off and can be written before S-2 lands.

## 2. Source and the dedup

- `P2M/Sol/S_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean`
  (848 lines, 71 declarations).
- Statement authority:
  `Theorems/Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean`
  (15 lines). Spell its binders **exactly**:
  `{N : ℕ} [NeZero N] (L L' : PeriodPair) (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice)
  (hidx : PeriodPair.sublatticeIndex L L' = N)
  (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
  ∃ (a b d : ℕ) (τ σ : ℍ), (a, b, d) ∈ ModularCurve.primCosetReps N ∧
  (σ : ℂ) = ((a : ℂ) * τ + b) / d ∧
  L.jLattice = (PeriodPair.ofTau τ).jLattice ∧ L'.jLattice = (PeriodPair.ofTau σ).jLattice`.
  The pin's `solution` (`:808–848`) is ~40 lines.

`port_advise` on the file: **19 substitutions ≈ 198 lines**, all the ported prelude —
`kw_span_neg_fst` (34, `Discriminant.lean`), `kw_ofTau_latticeEquivProd_symm_apply` (27),
`kw_linearIndependent_tau_one` (17, `Basic.lean`), `kw_im_div_ne_zero` (13),
`scale_lattice` (13), `scaleLatticeEquiv{,_apply}` (9/6), `G_scale`/`g₂_scale`/`g₃_scale`
(6/3/3, `Lattice.lean`), `discriminant_scale` (5), `G_eq_of_lattice_eq`/`g₂_eq_of_lattice_eq`/
`g₃_eq_of_lattice_eq` (3 each), `latticeEquivOfEq` (6), `mulLeftR`/`mulLeftZ` (2 each, port-
`private`). **Content ≈ 521 lines.** `KwSublatticeQuotientZZTransport` is reported by
`port_advise` against `PeriodPair.DiscriminantNeZero` — the known `def … : Prop` blind spot;
the class is **absent** from the port (grep-verified) and is one of this set's three new
objects (the `kw_surgehgf4_qtzz_axiomAnchor` row is likewise an anchor stub, not a
substitution).

Regions, with dispositions:

| lines | contents | disposition |
|---|---|---|
| `:47–136` | `mulLeftR`/`mulLeftZ`, `scale_lattice`, `scaleLatticeEquiv`, `mem_scale_lattice_iff`, `G_scale`/`g₂_scale`/`g₃_scale`, `discriminant_scale`, `jLattice_scale`, `latticeEquivOfEq`, the `*_eq_of_lattice_eq` block | **ported** (`Elliptic/PeriodPair/{Basic,Lattice}.lean`); import (the port-`private` ones are re-derived `private`) |
| `:163–220` | `kw_linearIndependent_tau_one`, `kw_ofTau_latticeEquivProd_symm_apply`, `kw_im_div_ne_zero`, `kw_span_neg_fst` | **ported** (`Basic.lean`, `Discriminant.lean`); import |
| `:254–447` | the generic ℤ² block: `natGen`, `zmultiples_natAbs`, `zmultiples_natGen`, `natGen_cast_mem`, `index_eq_natGen`, `dvd_of_mem_natGen`, `latticeOf`, `mem_latticeOf_iff`, `ker_fst_eq_range_inr`, `index_eq_comap_inr_mul_map_fst`, `aOf`, `dOf`, `index_eq_dOf_mul_aOf`, `zero_dOf_mem`, `dOf_dvd_of_zero_mem`, `exists_over_aOf`, `bOf`, `aOf_bOf_mem`, `bOf_nonneg`, `bOf_lt`, `latticeOf_canonical_eq` | **new generic module** (§4) |
| `:449–600` | `kw_scale_lattice_toAddSubgroup`, `kw_scale_lattice_subset`, `kwSublatticeIndex_scale`, `kw_exists_scale_ofTau_lattice_eq`, `kw_phiTau*`, `kw_HZZ*`, `kw_sublattice_eq_span`, `kw_hnfPoint*` | **new**, except `kw_scale_lattice_toAddSubgroup` and `kwSublatticeIndex_scale`, which **S-2 lands** (`Elliptic/PeriodPair/LatticeIndex.lean`) with identical statements — import, do not redeclare; `kw_scale_lattice_subset` is S-3-only |
| `:602–671` | `kw_surgehgf4_hu5c_not_isAddCyclic_zmod_prod` (19), `kw_surgehgf4_hu5c_gcd_eq_one_of_isAddCyclic` (52) | **new** — the product-cyclicity / HNF-coprimality criterion |
| `:673–807` | `KwSublatticeQuotientZZTransport` (a `def … : Prop`, 33), the `qtzz_*` block (`phiTau_mem_scale`, `phiTau_invMul_mem`, `psi₀*`, `psi*`, `psi_surjective`, `psi_ker`, `qtzz_proved`) | **new**; `kw_surgehgf4_qtzz_axiomAnchor : True` is **skipped** |
| `:808–848` | `solution` | the headline, ~40 lines |

**Namespace note.** The pin wraps the generic ℤ² block in `namespace QuaternionAlgebra` — a
`p2m_*` scaffolding artefact (no quaternion content). The order re-homes it (§4); the statement
checker matches by last name, so the namespace is free.

## 3. The mathematics, and the direction of the chain

1. **The ℤ² invariants** (generic): `natGen K` is the generator of `K ≤ ℤ` (so `K.index =
   natGen K`); `latticeOf a d b` is the subgroup of `ℤ × ℤ` generated by `(a, b)` and `(0, d)`
   (`mem_latticeOf_iff`); `ker_fst_eq_range_inr` and `index_eq_comap_inr_mul_map_fst` decompose
   the index; then `aOf`/`dOf`/`bOf` extract the HNF triple from any `H ≤ ℤ × ℤ` and
   `latticeOf_canonical_eq` proves `latticeOf (aOf H) (dOf H) (bOf H) = H`. `bOf_nonneg` /
   `bOf_lt` put `bOf` in `[0, d)`.
2. **The transport** (`:449–600`): `kw_exists_scale_ofTau_lattice_eq` normalises any `L` to
   `ofTau τ` up to scaling; `kwSublatticeIndex_scale` and `kw_scale_lattice_subset` move the
   hypotheses; `kw_HZZ` and `kw_phiTau` identify the sublattice quotient with a quotient of
   `ℤ × ℤ`; `kw_hnfPoint` builds the `σ` and `kw_hnfPoint_scale_lattice` its lattice.
3. **The criterion** (`:602–671`): `IsAddCyclic (ZMod p × ZMod p)` is false for `p > 1`, and
   consequently a cyclic quotient forces `gcd (aOf H) (gcd (bOf H).toNat (dOf H)) = 1` — the
   primitive-coset hypothesis.
4. **The `qtzz` transport** (`:673–807`): `KwSublatticeQuotientZZTransport` moves the cyclicity
   from `sublatticeQuotient L L'` to `(ℤ × ℤ) ⧸ kw_HZZ τ L'` along the scaled `ofTau` model
   (`psi` surjective with the right kernel), closing `kw_surgehgf4_qtzz_proved`.
5. **The headline** (`:808`): `kw_exists_scale_ofTau_lattice_eq` gives `α, τ, hlat`; the `jL`
   equalities are `jLattice_scale`/`jLattice_eq_of_lattice_eq`; `H := kw_HZZ τ (L'.scale α)`;
   `index_eq_dOf_mul_aOf` + `kw_HZZ_index` + `hidx` give `dOf H * aOf H = N`; `hu5c` gives the
   coprimality; `kw_hnfPoint τ (aOf H) (bOf H).toNat (dOf H)` is the `σ`; `mem_primCosetReps`
   closes.

A `def … : Prop` is never dropped on a tool's word (P-2 §6): `grep -c` the body of
`KwSublatticeQuotientZZTransport` and of every class.

## 4. Deliverable — two modules, one set

**(a) `FLTForHuman/Algebra/IntPairSubgroup.lean`** (new, mathlib-only, leaf): the generic ℤ²
block `:254–447` at the pin last names, in a new namespace (suggested `IntPairSubgroup`;
the pin's `QuaternionAlgebra` is scaffolding). No `PeriodPair` import. This is the playbook
§3.2 "generic cross-theory count gets its own top-level area" decision the scoping note asked
this order to make.

**(b) `FLTForHuman/Elliptic/PeriodPair/PrimCosetReps.lean`** (new leaf; the name is the pin's
subject, distinct from the already-ported `ModularCurve/Defs/PrimCosetReps.lean`, whose
`ModularCurve.primCosetReps`/`mem_primCosetReps` are this set's **imports**). Namespaces as the
pin: the transport/`hu5c`/headline in the pin's namespaces, the `qtzz` block in `ModularCurve`
(the pin's `KwSublatticeQuotientZZTransport` is a `ModularCurve` name — check with
`grep -n "def KwSublatticeQuotientZZTransport"`).

- **Public, at the pin names**: the headline; the `:449–671` transport/criterion block; the
  `qtzz_*` block; `KwSublatticeQuotientZZTransport`; the generic block in (a).
- **Not landed**: the ported prelude (import); `kw_surgehgf4_qtzz_axiomAnchor : True` (p2m
  anchor stub); the `p2m_*` scaffolding.
- **`private` with content names**: local helpers; the port-`private` `mulLeftR`/`mulLeftZ`/
  `mem_scale_lattice_iff` are re-derived `private` (they are not importable).
- (b) imports: `Elliptic/PeriodPair/{Basic,Lattice,Discriminant,Uniformization,JLine}`,
  `Elliptic/PeriodPair/LatticeIndex` (S-2: the two shared lemmas), `Algebra/IntPairSubgroup`,
  `ModularCurve/Defs/PrimCosetReps`,
  `Analysis/UpperHalfPlane/...` via mathlib, plus `Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic`,
  `Mathlib.Algebra.Group.Subgroup.{Lattice,Basic}`, `Mathlib.LinearAlgebra.FreeModule.Int`,
  `Mathlib.GroupTheory.Archimedean` (`Int.subgroup_cyclic`). **(a)** imports mathlib only.
  Never `import Mathlib`; never `GenusOnePlaceGateCentred.lean`/`Place/RRSpace.lean`.

## 5. Route, with recorded negatives

- **The ℤ² block's foundations are mathlib's, its invariants are the pin's.** Every primitive is
  in `v4.34.0`: `Int.subgroup_cyclic` (`GroupTheory/Archimedean.lean:112`, so `natGen` is "the
  generator of a subgroup of `ℤ`"), `Int.index_zmultiples`
  (`LinearAlgebra/FreeModule/Int.lean:174`), `AddSubgroup.mem_closure_pair`
  (`Algebra/Group/Subgroup/Lattice.lean:662`), `AddSubgroup.mem_prod`
  (`Algebra/Group/Subgroup/Basic.lean:99`), `AddSubgroup.index`, and
  `AddSubgroup.index_eq_natAbs_det`/`relIndex_eq_natAbs_det`/`relIndex_eq_abs_det`
  (`LinearAlgebra/FreeModule/Finite/CardQuotient.lean:98,106,114`). **What is not in mathlib**
  is the pin's named invariants (`natGen`, `latticeOf`, `aOf`, `dOf`, `bOf`,
  `latticeOf_canonical_eq`), which the rest of the set consumes by name — write them as they
  stand. Where the determinant-index formula replaces the pin's
  `index_eq_comap_inr_mul_map_fst`/`index_eq_dOf_mul_aOf` route, prefer it and record the
  saving.
- **The `hu5c` pair is not mathlib-replaceable.** `hu5c_not_isAddCyclic_zmod_prod` is an
  `addOrderOf`/`Nat.card` argument and `hu5c_gcd_eq_one_of_isAddCyclic` a derivation over the
  pin's own `aOf`/`bOf`/`dOf`; mathlib has `IsAddCyclic` and its basics but no product
  cyclicity or HNF-coprimality criterion. Write both.
- **Reuse wins.** `ModularCurve.primCosetReps`/`mem_primCosetReps`
  (`ModularCurve/Defs/PrimCosetReps.lean`), `PeriodPair.jLattice_ofTau`/`jLattice_surjective`
  (`JLine.lean`), the whole scale/`jLattice` prelude, and `upperTriangularGL` if needed are in
  the port; do not transcribe them. The 19 substitutions are imported, not re-proved.
- **The pin's `attribute [-instance]`/`attribute [-simp]` blocks and its heartbeat bumps are
  not transcribed.** The port's cap is 4,000,000; **never raise it**; if a declaration cannot
  fit, stop and report.
- **Traps to observe:** write prose in `/- … -/` blocks, not `--` lines (playbook §4's
  namespace-tracker quirk); do not open `Polynomial.Bivariate` file-wide (playbook §6). The
  generic module must not import `PeriodPair`/`FLTForHuman` theory modules beyond mathlib.

## 6. Stop conditions

Stop and report, do not push on: an unported prerequisite outside §2 that is not the ported
prelude; a statement that does not transcribe to `v4.34.0`; a declaration that will not fit
the 4,000,000-heartbeat cap; any pull toward S-4 or the capstone; any pressure to import the
two forbidden modules. Keep the tree green.

## 7. Build discipline (binding) and pre-flight

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` is the edit loop;
> `lake build <module>` when a file is done; **one** `lake build` per wave; bound every build
> with `timeout` and serialize every `lake build` with `flock .lake/flt_build.lock`; time it.
> **Never raise `maxHeartbeats`.** Iterate in a gitignored `lean/Scratch*.lean`, in bounded
> blocks, generic module first.

**Pre-flight** (report the numbers):

1. `timeout 300 lake env lean <opts>` on a stub importing the `Elliptic/PeriodPair` modules +
   `ModularCurve/Defs/PrimCosetReps`, timed.
2. `#check` `Int.subgroup_cyclic`, `Int.index_zmultiples`, `AddSubgroup.mem_closure_pair`,
   `AddSubgroup.mem_prod`, `AddSubgroup.index_eq_natAbs_det`, and the ported
   `ModularCurve.mem_primCosetReps`, `PeriodPair.jLattice_ofTau`.
3. `port_advise --targets build/rowS3_targets.txt` against the landed tree; report the
   substitution figure as re-measured.

## 8. Verification

- `lake env lean` clean; `lake build` both modules; one `flock`ed wave build; whole-tree
  `lake build` green.
- `python3 spec/check_flt_statements.py` → **0 mismatched / 0 missing**. Baseline at drafting
  (after S-1): `6074 statements identical (313 promoted, 83 renamed), 0 mismatched, 0 missing,
  36 own-proof declarations exempted (6110 checked)` — but **re-run it at dispatch**: S-2 will
  have moved it. Reconcile every delta.
- `SOURCES`: append `Theorems/Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean`
  immediately **above** its `S_` file (wrapper = statement authority; appended last as a pair,
  as S-1/S-2 did). None is in the list today. `PORT_FILES`: append
  `FLTForHuman/Algebra/IntPairSubgroup.lean` then
  `FLTForHuman/Elliptic/PeriodPair/PrimCosetReps.lean` (last). Report the checker before/after.
- `spec/PeriodPairPrimCosetConsumer.lean` (new, `spec/` only): real executed zones, no `#check`,
  no `sorry`; deleting the two modules must make it fail; exit 0. ≥1 zone at a concrete
  `PeriodPair.ofTau`-style lattice; ≥1 consuming the generic `latticeOf_canonical_eq` at an
  abstract `H ≤ ℤ × ℤ`; ≥1 feeding S-2-shaped hypotheses (`hsub`/`hidx`/`hcyc`) into the
  headline. Run `timeout 90 lake env lean <opts>`, report exit and wall time; do not add it to
  the lakefile.
- `#print axioms` on the headline, `KwSublatticeQuotientZZTransport` and
  `kw_surgehgf4_qtzz_proved`: `[propext, Classical.choice, Quot.sound]`; no `sorry`.
- `build_ladder.py --edit` on both new modules; report the cascade.

## 9. Close-out (fill on landing)

Written lines per module; the two once-blocks with their `grep -c`; checker before → after and
the reconciliation; the measured saving against 848 raw / ≈198 substituted; consumer exit and
time; whole-tree build jobs and seconds; `#print axioms`; the friction findings — in particular
whether the determinant-index formula shortened the ℤ² block, how much of the `hu5c`/`qtzz`
work is the pin's, and whether the two-module split cost anything. Then update
`TOPIC-V5-row-S-scoping.md` §2.3/§5.4 and fold the generalizable part into
[../../porting-playbook.md](../../porting-playbook.md) and
[../../logs/velu-port.md](../../logs/velu-port.md).

### Landed 2026-10-07 — the close-out

**Two modules.** `FLTForHuman/Algebra/IntPairSubgroup.lean`, **244 lines** (21 checker-visible
public declarations, 0 `private`, mathlib-only); `FLTForHuman/Elliptic/PeriodPair/PrimCosetReps.lean`,
**506 lines** (25 checker-visible public declarations + 6 `private` helpers); plus
`spec/PeriodPairPrimCosetConsumer.lean` (158 lines, four zones / sixteen `example`s). The full record
is in [../../logs/velu-port.md](../../logs/velu-port.md) "S-3 — the primitive-coset / `jLattice`
column".

- **Saving.** 848 raw pin lines / 71 pin declarations. `port_advise` re-measured on the landed tree:
  **22 substitutions ≈218 lines** (the order's 19 ≈198) — 14 "importable" + 8 "port-`private`".
  Subtracting the two false positives (`KwSublatticeQuotientZZTransport` matched to
  `PeriodPair.DiscriminantNeZero`, the `def … : Prop` blind spot; `kw_surgehgf4_qtzz_axiomAnchor`
  matched to an anchor stub) leaves 12 importable. **750 lines written** = the order's content
  estimate 521 + the two headers/import lists and per-declaration doc comments (≈150) + the
  pin-`private` helpers re-derived (≈60) + the three prelude lemmas the port lacked (≈15).
- **Checker.** before `6135 (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6171
  checked)` → after `6181 (312, 83), 0 mismatched, 0 missing, 36 own (6217 checked)`. Delta **+46 =
  21 `IntPairSubgroup` declarations + 25 `PrimCosetReps` declarations**; `promoted`/`renamed`/`own`/
  `mismatched`/`missing` all unmoved. `--prop-bodies`: 262 identical / 6 textual (was 261 / 6) —
  **+1 = `KwSublatticeQuotientZZTransport`**; the 6 textual are the pre-existing advisory rows.
- **The once-blocks, `grep -c`.** (1) `ModularCurve.kw_scale_lattice_toAddSubgroup` and
  `kwSublatticeIndex_scale` are declared **once**, in S-2's `LatticeIndex.lean` (declaration-line
  `grep -c` over the port: 1 each); S-3 imports them and does not redeclare. (2) The generic ℤ² block
  is declared once, in `IntPairSubgroup.lean`; the pin's own copy of
  `KwSublatticeQuotientZZTransport` is at `S_…:673` and the port's at 1 (`grep -c`). Every
  dropped-as-already-present name has a declaration-line `grep -c` of 1:
  `linearIndependent_coe_upperHalfPlane_one`, `scale_lattice`, `scaleLatticeEquiv`, `G_scale`,
  `g₂_scale`, `g₃_scale`, `discriminant_scale`, `G_eq_of_lattice_eq`, `g₂_eq_of_lattice_eq`,
  `g₃_eq_of_lattice_eq`.
- **Consumer.** exit **0**. Uncontended wall times **56.2 s**, 49.7 s, 67.2 s (`timeout 90 lake env
  lean`). Two runs during a system-wide slowdown (load avg ≈1.9; S-2's own consumer ran 107 s against
  its logged 55.8 s) exceeded the 90 s bound — environmental, not S-3: the same file exits 0 with
  margin when the machine is not contended. Zone 1
  the generic invariants (`latticeOf_canonical_eq` at an abstract `H`, `mem_latticeOf_iff` at the
  concrete `latticeOf 3 5 2`, `index_eq_dOf_mul_aOf`); zone 2 a concrete `ofTau` lattice
  (`kw_exists_scale_ofTau_lattice_eq`, `kw_sublattice_eq_span`, `kw_HZZ_index`); zone 3 the criterion;
  zone 4 the S-2-shaped `hsub`/`hidx`/`hcyc` fed into the headline at an `ofTau` pair. Removing the
  two modules' `.olean`s gives exit 1 (`object file … does not exist`).
- **Axioms.** `#print axioms` on the headline, `ModularCurve.KwSublatticeQuotientZZTransport`,
  `ModularCurve.kw_surgehgf4_qtzz_proved` (and `…hu5c_gcd_eq_one_of_isAddCyclic`,
  `IntPairSubgroup.latticeOf_canonical_eq`): all `[propext, Classical.choice, Quot.sound]`; 0 `sorry`.
- **Builds.** Pre-flight stub exit 0, wall **85.4 s** / 4.9 user / 23.1 sys; all nine `#check`s
  resolve. Edit loop on the transport module clean at **43.8 s** wall / 7.3 user / 13.0 sys
  (**77.3 s** on the post-edit re-run, under load).
  `lake build FLTForHuman.Algebra.IntPairSubgroup` 3.0 s (3,093 jobs) / 7.3 s wall;
  `lake build FLTForHuman.Elliptic.PeriodPair.PrimCosetReps` **85 s (9,059 jobs)**, **100.5 s** wall /
  15.5 user / 32.1 sys, flocked `timeout 400`. `build_ladder --edit`: generic → **1** dependent
  (the transport, 508 lines, ≈9 s); transport → **0** (leaf). Whole-tree flocked `lake build` green,
  **9,323 jobs**, **11.4 s** wall / 8.5 user / 12.3 sys.
- **Friction.**
  1. **The determinant-index formula did *not* shorten the ℤ² block.** `AddSubgroup.index_eq_natAbs_det`
     wants a `Basis (Fin 2) ℤ ↥H` — an explicit HNF basis of `H`, which is the object
     `latticeOf_canonical_eq` constructs; computing the index from it would circularise the argument
     and add a basis-independence step. The pin's `index_eq_comap_inr_mul_map_fst` + `index_eq_natGen`
     projection route stands (≈24 lines). The set's one audit negative.
  2. **The `hu5c` pair and the `qtzz` block are the pin's, essentially line for line.**
     `hu5c_not_isAddCyclic_zmod_prod` (19) is an `addOrderOf`/`Nat.card` argument;
     `hu5c_gcd_eq_one_of_isAddCyclic` (52) derives the coprimality over the pin's `aOf`/`bOf`/`dOf`.
     Mathlib has `IsAddCyclic` (`∃ g, Surjective (· • g)`) but no product-cyclicity or
     HNF-coprimality criterion. The `qtzz_*` block (≈105) is likewise transcribed; mathlib supplies
     `QuotientAddGroup.{map,quotientAddEquivOfEq,quotientKerEquivOfSurjective,mk'_surjective}` and
     `isAddCyclic_of_surjective`. Mathlib shortens neither half.
  3. **The two-module split cost essentially nothing.** The generic module is mathlib-only, compiles
     in 4.8 s (edit loop) / 3.0 s (`lake build`) and cascades to exactly the one transport module;
     the transport is a leaf. The split's only cost is the second header/import list (≈15 lines). This
     is the playbook §3.2 "generic cross-theory count gets its own top-level area" decision.
  4. **Three prelude lemmas the region table listed as "ported; import" were not in the port:**
     `g₂_cubed_scale` and `jLattice_scale` (private, re-derived) and `jLattice_eq_of_lattice_eq`
     (pin-public, landed at its pin name). `jLattice_eq_of_lattice_eq` is **not** in `port_advise`'s
     substitution list, so only a `grep -c` found it. The four port-`private` helpers the order
     flagged (`mem_scale_lattice_iff`, `im_div_ne_zero`, `span_neg_fst`,
     `ofTau_latticeEquivProd_symm_apply`) were re-derived `private`;
     `mulLeftR`/`mulLeftZ`/`scaleLatticeEquiv_apply`/`latticeEquivOfEq` were not needed. The S-2
     finding recurs: an order's "ported prelude" row is a claim to `grep -c`, not a fact.
  5. **`lake env lean` writes no `.olean`.** The generic module had to be `lake build`-ed before the
     transport could be elaborated (`import FLTForHuman.Algebra.IntPairSubgroup` needs the olean), so
     "edit loop first, build once per wave" needs one tier-1 build between a new leaf and its first
     importer.
  6. **No `IsAddCyclic` instance friction:** Lean 4 typeclass search does consume a plain local
     hypothesis of class type, so the pin's `kw_surgehgf4_qtzz_proved` proof (no `haveI`) transcribes
     verbatim (probe-verified).
