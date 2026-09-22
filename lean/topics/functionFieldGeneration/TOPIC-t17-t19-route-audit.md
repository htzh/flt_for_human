# T17–T19 route audit: the chunky topics, re-measured

**Status (2026-09-22): read-only audit of the pin at `aa2d8b3`, plus four
independent sub-audits and two Lean-checked route tests.** One result changes the
plan: the serial chain T17 → T18 is an artifact of a single replaceable proof
line, and removing it drops ≈1.1k lines from the required remainder.

Read against [PORTING-FFG.md](../PORTING-FFG.md) §7.8 and the topic notes. All
pin line numbers are `anthropics/fermats-last-theorem@aa2d8b3`.

## 0. Bottom line

| | §7.8 | after this audit |
|---|---|---|
| required remainder (17 nodes) | ≈4.45k–4.90k | **≈3.0k–3.7k** |
| nodes on the critical path | a linear chain of 6 topics | **T19's two developments, then T20** |
| serial chain | T15→T16→T17→T18→T19→T20 | the only internal edges are T19 `rval_aux` → T19 private non-membership → T19 `jqN_prime_not_mem_full`; every other survivor is level 0 (T14 + Φ_p cone) |
| slot-count block (299 lines) | — | **≈110–150 lines removable** |
| `rval_aux` (680 lines) | — | ~8–12% removable; **irreducible otherwise** |

The math and the statements are unchanged. Everything below is about the route,
the proof lines, and the dependency graph.

## 1. The T17a → T18 chain is removable (the main finding)

§7.8 orders T18 (generation and squarefree degree) *after* T17 and *before* T19,
and §7.3 warns that `functionFieldGeneration_of_squarefree` **must not be
dropped**. Both rest on the pin's proof of T19's private M-arbitrary lemma
(`S_ModularCurve_jqN_prime_not_mem_full.lean`, lines 1586–1947), which uses
`functionFieldGeneration_of_squarefree` at **line 1638** to build the `Gen p`
half of the local hypothesis `hallp`.

That is the chain's *only* real link into T19:

| name | mentions in the T19 file | real uses |
|---|---|---|
| `functionFieldGeneration_of_squarefree` | 11 | **1** (L1638) |
| `full_eq_adjoin_primes` | 0 | 0 |
| `finrank_adjoin_jqN_eq_of_squarefree` | 0 | 0 |
| `relfinrank_full_of_squarefree` | 0 | 0 |
| `dedekindPsi_of_squarefree` | 0 | 0 |

The other 10 mentions are the generator's `p2m_export` boilerplate (9 lines) and
the `import` (1). Whatever the tool counted, **the file has one real proof use**,
and it is replaceable — so §7.3's "must not be dropped" conclusion does not
survive the occurrence check §1 requires.

And the one real use is replaceable, because `Gen p` for a prime is
near-definitional: both fields are `ℚ(jq, jqN p)`.

```lean
/-- `Gen p` for prime `p`: both sides are `ℚ(jq, jqN p)`. -/
theorem gen_prime (p : ℕ) [Fact p.Prime] : Gen p := by
  haveI : NeZero p := ⟨‹_›⟩
  unfold Gen
  refine le_antisymm (modularFunctionField_le_full p) ?_
  rw [modularFunctionField, modularFunctionFieldFull, divisorExpansions,
    IntermediateField.adjoin_le_iff]
  rintro x ⟨d, -, hdvd, rfl⟩
  rcases ‹Fact p.Prime›.out.eq_one_or_self_of_dvd d hdvd with h1 | h2
  · subst h1; rw [qExpand_one_apply]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
  · subst h2
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)
```

With `gen_prime` in place, the pin's `hallp` at `d = p` (lines 1634–1639) needs
only the already-ported `finrank_adjoin_jqN_eq_of_prime`. This was **verified in
Lean** against the current port by a scratch file that elaborated
`Tight p ∧ Gen p` with no errors (`gen_prime` plus
`unfold Tight; rw [dedekindPsi_prime]; exact finrank_adjoin_jqN_eq_of_prime`).

**Consequence — the drop set.** Six nodes are consumed only by each other and by
that one line, and are in neither the capstone path nor the §2.1 outbound tier:
`jqN_prime_not_mem_adjoin`, `full_eq_adjoin_primes`, `dedekindPsi_of_squarefree`,
`relfinrank_full_of_squarefree`, `finrank_adjoin_jqN_eq_of_squarefree`,
`functionFieldGeneration_of_squarefree` (≈1,094 own lines). The one remaining
`jqN_mem_of_div_primes` copy (132 lines, identical in three of the survivors'
files) is factored out too. This satisfies §1's drop rule: an occurrence count,
recorded, not inspection.

**What is *not* dropped.** T19's private M-arbitrary lemma is load-bearing — the
arbitrary-M (indeed "powerful-M", e.g. `M = 9, p = 2`) non-membership is hit by
`hall_all` and cannot be reduced to the squarefree/prime-set lemma. It stays; only
its `Gen p` detour goes. `jqN_prime_not_mem_adjoin` (T17a) has three consumers —
`relfinrank_adjoin_primes`, `relfinrank_full_mul_prime`, `jqN_sq_not_mem_adjoin` —
but all are outside the 17 nodes and outside §2.1's five-outbound-node tier, so
they are optional API, not required work.

## 2. Every surviving topic is level 0 — the serial chain disappears

Declaration-span citation analysis of the 17 nodes, plus the pin's own proofs,
shows the real prerequisites (T14 and the Φ_p cone are assumed):

| topic | node | real prereq inside the 17 |
|---|---|---|
| T15 | `jqN_div_mem_modularFunctionField`, `modularFunctionField_eq_full_of` | **none** (htw/hsp are hypotheses) |
| T16 | `finrank_adjoin_jqN_prime_of_not_mem`, `finrank_adjoin_jqN_pow_succ_of_not_mem`, `relfinrank_full_eq_mul` | **none** |
| T17 | `jqN_pow_not_mem_adjoin_full` (tower) | **none** (base membership is a hypothesis) |
| T18 | `full_eq_adjoin_full_div_prime` | **none** |
| T19 | `minpoly_jqN_map_eq_prod_slots` (`rval_aux`, 680 lines) | **none** (`hall` is a hypothesis) |
| T19 | `jqN_prime_not_mem_full` | `rval_aux` + `gen_prime` |

The pin's import-level chain (and §7.8's prereq column) reflects the generator's
file re-exports, not the proofs. In particular the largest single development,
`rval_aux`, takes `Hall M` as a hypothesis and cites no T15–T18 name at all.

**Parallel workstreams after T14** (which has landed, 503 port lines):
1. T15 (both nodes); 2. T16 (all three); 3. T17 tower; 4. T18
`full_eq_adjoin_full_div_prime`; 5. T19 `rval_aux` + the private non-membership.
T20 assembles `Inputs` and applies the already-proved capstone.

## 3. Slot counting: a real ≈110–150 line win

The block at pin lines 405–703 (299 lines) proves `slots n = dedekindPsi n`.
mathlib has **no** `dedekindPsi` and **no** Γ₀ index formula
(`Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean` has `Gamma0` and
`IsCongruenceSubgroup.finiteIndex` only), so there is no drop-in. But:

- `slotAt n d` has the closed form `(d / gcd (n/d) d) * φ (gcd (n/d) d)`
  (numerically verified for `n < 120`). Replacing the 108-line fibre-wise CRT
  `slotAt_mul` with this plus a ~24-line multiplicativity lemma, and splitting
  `divisors (M*M')` with mathlib `Nat.Coprime.divisors_mul`
  (`Mathlib/Data/Finset/NatDivisors.lean:65`), removes ≈80–105 lines and also
  obsoletes `gcd_mul_left/right_of_dvd` (17) and `gcd_eq_of_modEq` /
  `slotCond_mod_iff` (8). The reusable count pieces already exist verbatim in the
  pin's `S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean` (L18–31, L33–45,
  L132–155).
- 64 lines re-prove ψ facts the pin already publishes (`dedekindPsi_prime_pow`,
  `dedekindPsi_prime`, `dedekindPsi_mul_prime`, `dedekindPsi_pos`); the port
  already has `dedekindPsi_prime`/`_prime_pow`/`_mul_of_coprime` in
  `Defs/Jq.lean:215,221,284`, and `Spine.lean:179–201` is a *third* private copy.
- Consumers use only `slotAt` and `slots_eq_dedekindPsi`; expose one
  `Finset.card` statement instead of the whole API (~30 consumer lines).

Block after: ≈150–190 lines. See [audit-slot-counting-mathlib.md](../../logs/audit-slot-counting-mathlib.md).

**Prior art, not a dependency.** An external Lean proof of
`[SL₂(ℤ) : Γ₀(pᵏ)] = p^(k-1)(p+1)` exists — Chris Birkbeck's `CongruenceIndex.lean`
in [`Vilin97/lean-pool`](https://github.com/Vilin97/lean-pool/blob/main/LeanPool/LeanModularForms/HeckeRIngs/GL2/CongruenceIndex.lean)
(Apache-2.0, citing Shimura Theorem 3.24) — by explicit coset representatives and
`Nat.card` bijections. It is prime-power only, counts `Subgroup.index` of an
actual subgroup rather than the `(a,b)` slot set, and is outside the pinned
mathlib, so the mathlib-only port cannot import it and should not copy the file
wholesale. It is worth citing as the reference route in the docstring; it also
confirms no mathlib endpoint is being missed.

## 4. `rval_aux` is largely irreducible

`rval_aux` is 887–1566 (**680** lines, not 699 — 1567–1585 is scaffolding).
The dominant block is `have hslot_root` (905–1397, 493 lines). Category split:
~64% genuine math, ~27% polynomial/minpoly bookkeeping, ~9% instance/coercion
plumbing. Mathlib gives **no** replacement for `map_qExpand_minpoly_eq`
(`minpoly.map_eq_of_injective`/`minpoly.map` do not exist); only ~8–12 lines
collapse. Realistic cleanup: ~53 lines inside, ~18 outside (the private
`mem_range_of_eval_eq_const` at 804–821 is verbatim
`FLTForHuman/FieldTheory/CommonRoot.lean:111–126`). The two `by_cases` branches
share a byte-identical 12-line tail (hoist, ~11 lines). See
[audit-rval-aux-compressibility.md](../../logs/audit-rval-aux-compressibility.md).

## 5. Shared lemmas the port already owns

Already public in the port, to be imported rather than re-derived by T15–T19:

| pin declaration | pin lines | port home |
|---|---|---|
| `mem_range_of_eval_eq_const` | 804–821 (18) | `FieldTheory/CommonRoot.lean:111` |
| `tight_one` | 823–834 (12) | `FunctionFieldGeneration/Spine.lean:214` (promote) |
| `gen_one` | 835–857 (23) | `FunctionFieldGeneration/Spine.lean:225` (promote) |
| `mem_range_of_unique_common_root` | — | `FieldTheory/CommonRoot.lean:60` |
| `irreducible_of_transitive_ringAut` | — | `FieldTheory/CommonRoot.lean:148` |

T14 already covers the ~370-line prelude (`Defs/PhiAtSlot.lean`,
`ModularCurve/PhiSlotRoots.lean`).

**Mathlib collisions in the prelude/bridges** (audit 4; all in T14 or T16, none
change a statement):

| pin declaration | mathlib lemma | saving |
|---|---|---|
| `exists_isPrimitiveRoot_cyclotomicField` | `IsCyclotomicExtension.zeta`/`zeta_spec` (`NumberTheory/Cyclotomic/PrimitiveRoots.lean:87,93`) | 14 → ~5 |
| `cycUnit`/`cycUnit_spec`/`cycUnit_pow` | `IsPrimitiveRoot.isUnit`/`isUnit_unit`/`zeta_pow` (`RingTheory/RootsOfUnity/PrimitiveRoots.lean:126,173`; `Cyclotomic/…:106`) | — |
| `isPrimitiveRoot_pow_div` (225–236) | `IsPrimitiveRoot.pow` (`RootsOfUnity/…:263`) + `Nat.div_mul_cancel` | 12 → 3 |
| inner `pow_inj` steps | `IsPrimitiveRoot.injOn_pow` (`:270`) | small |
| `coeffMapEquiv` (T16, ×2) | `RingEquiv.ofBijective` (`Algebra/Ring/Equiv.lean:446`) | 18 → 10, ×2 |
| `exists_pow_eq_of_coprime` | `exists_pow_eq_self_of_coprime` (`GroupTheory/OrderOfElement.lean:332`) | 9 → 4 |

The rest of the prelude is FLT-specific glue already calling the right mathlib
lemmas. `rUnit`/`range_map_eq_rUnit` (T16, 70 lines ×2) is **not** a
range/local-ring statement — a pure `(ZMod p)ˣ` multiset reindexing with no
mathlib endpoint — so it is a route-test item, not a reuse. (Repo-wide, 38 files
carry this prelude and 11 more carry a parallel `jqModC` block; extending the T14
dedup beyond the remainder's ~12 files is a separate, larger opportunity outside
this effort's scope.)

## 6. Revised budget

Starting from §7.8's deduplicated ≈4,450–4,900 (which, per its own ledger row
"one of the two `jqN_prime_not_mem_adjoin` proofs −244", may *already* have netted
T17a out):

| correction | lines |
|---|---|
| drop the T18 cluster: `full_eq_adjoin_primes`, `dedekindPsi_of_squarefree`, `relfinrank_full_of_squarefree`, `finrank_adjoin_jqN_eq_of_squarefree`, `functionFieldGeneration_of_squarefree` | −850 |
| drop T17a as well (count once — §7.8's −244 row may already have removed it) | −244 *or* 0 |
| remaining `jqN_mem_of_div_primes` duplicate (132) | −132 |
| slot-count closed form + ψ reuse + consumer collapse | −110…−150 |
| `rval_aux` cleanup + shared-engine reuse + prelude/bridge mathlib collisions | −150…−220 |
| **revised required remainder** | **≈3.2k–3.7k** (≈3.0k–3.45k if T17a is additional) |

Capstone-only (defer §7.8's T20 optional tail, ≈250) is ≈250 lower again. The
outbound interface is unaffected: §2.1's five remaining nodes are
`minpoly_jqN_map_eq_prod_slots`, `jqN_prime_not_mem_full`,
`exists_phiIrreducible_of_finrank_eq`, `full_eq_adjoin_full_div_prime`,
`finrank_adjoin_jqN_prime_of_not_mem` — none in the drop set. The reduction is
therefore not a scope cut on what the rest of FLT consumes; it is proof lines on
no path.

## 7. Recommended work order

1. **Land `gen_prime`** in `Defs/Fields.lean` (or beside `gen_one`), with a
   docstring naming it as the replacement for the pin's `L1638` detour.
2. **Re-scope §7.8**: move T17a and the T18 cluster to an explicit optional tail
   (they serve only `relfinrank_adjoin_primes` / `relfinrank_full_mul_prime` /
   `jqN_sq_not_mem_adjoin`, which no §2.1 tier needs), and record the occurrence
   counts of §1.
3. **Fan out the five level-0 workstreams** in parallel; keep `rval_aux` and the
   private non-membership in one module.
4. **Route-check the slot-count closed form** before writing `slotAt_mul`.
5. Keep `check_flt_statements.py` green on the *statements*: the survivors'
   statements are the pin's verbatim, and the six dropped nodes are not in the
   outbound tier, so checker coverage of what the rest of FLT reaches is
   unchanged. Record the reduced statement count rather than claiming the full
   T15–T19 wrapper set.

## Evidence

- [audit-jqN-nonmemory.md](../../logs/audit-jqN-nonmemory.md) — the two
  `jqN_prime_not_mem_adjoin` lemmas; the private one is genuinely independent.
- [audit-rval-aux-compressibility.md](../../logs/audit-rval-aux-compressibility.md)
  — `rval_aux` block map and mathlib candidates.
- [audit-slot-counting-mathlib.md](../../logs/audit-slot-counting-mathlib.md) —
  slot block, closed form, mathlib negatives.
- [audit-prelude-bridges.md](../../logs/audit-prelude-bridges.md) — prelude and
  bridge mathlib collisions; `rUnit` and T18 route-test verdicts.
