# Topic: the conditional capstone — the spine of `functionFieldGeneration`

**Status: done (2026-09-21), 1 goal round of 4.**
`FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean` is complete: 29 declarations (5 public
— `Tight`, `Gen`, `Hall`, `Inputs`, `functionFieldGeneration_of` — and 24
`private`), 494 lines, green, 0 warnings, no `sorry`;
`#print axioms functionFieldGeneration_of` is clean; `Inputs` pruned 24 → 10; the
consumer binds `functionFieldGeneration_of` in Zone B with the `sorry` count still
1; the checker reports 0 mismatches with the 5 public exemptions. The auxiliaries
were **glue**: none of `root_shape`, `htw_of`, `hsp_of`, `full_le_adjoin_chain` or
`jqN_pow_not_mem_full` needed machinery beyond the port and mathlib, so the
substance is entirely in the 10 assumed fields. Measured cost and the final field
list with reasons are in [logs/ffg-port.md](logs/ffg-port.md) §2d and §8.4; the
post-review corrections (two unused declarations removed) are §2d.1.

**Audience.** A fresh session taking the second *topic* of the
`functionFieldGeneration` effort. Layer 0 and the `jq`-coefficients topic are
done ([logs/ffg-port.md](logs/ffg-port.md) §0). Read
[PORTING-FFG.md](PORTING-FFG.md) §0, §2 and §7.4 once for the scope argument and
the shape of this artifact, and [porting-playbook.md](porting-playbook.md) §3–§5
and §7 for the method. Everything those files settled still binds.

**Goal.** One new module, `FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean`, mathlib-only,
green, zero warnings, zero `sorry`, containing:

1. the bundled invariants `Tight`, `Gen`, `Hall`;
2. the auxiliary block the induction needs, transcribed from FLT's solution file;
3. the strong induction **`hall_all`**, proved;
4. a structure **`Inputs`** whose fields are FLT's significant remaining
   statements, with their statements taken verbatim from the pin;
5. the **conditional capstone**, proved:

```lean
theorem functionFieldGeneration_of (h : Inputs) (N : ℕ) [NeZero N] :
    FunctionFieldGeneration N
```

Nothing else. In particular **do not** discharge any of the `Inputs` fields: the
point is a checked skeleton, not the theorem.

## 1. Why this topic, and what is settled

The effort has delivered the statement landscape of math/010 and two concrete
claims. The one remaining cheap thing with a clear gain is the *architecture* of
the proof: math/010 §2 and §7 are a single strong induction carrying two
invariants over the divisor lattice, and §7.4 prescribed exactly this artifact —
`Inputs` plus a proved `functionFieldGeneration_of`, which contains no `sorryAx`.

- **Settled: the goal is conditional.** The unconditional capstone stays a
  `sorry` in the consumer, by design; it is the deferred theorem. Do not try to
  remove it. This topic *adds* a bound item.
- **Settled: the auxiliaries are ported, the significant steps are assumed.**
  `hall_all` and its helper block are glue over named assumptions; they are
  proved, not assumed. The helper block is scouted below — 32 declarations,
  286 lines, of which the `TS` block is *already ported*.
- **Settled: `Inputs` starts as all 24 remainder nodes and is then pruned.**
  Over-include, build, and remove fields that turn out unused. A minimal,
  justified field set is part of the deliverable, and a field that survives
  pruning should carry a one-line reason.
- **Settled: statements in `Inputs` are FLT's, verbatim.** So a later effort that
  discharges one is a drop-in replacement, and the pin remains the interface.
- **Settled: no `sorry`, and the module is in the default target.** Experiment in
  the gitignored `Scratch.lean`; land only finished code.
  `log`/`def`/`abbrev` here are ours or FLT's, but never a `sorry`.

## 2. The scouted inventory — do not re-derive this

`hall_all` is FLT `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean` lines
614–700. Its transitive closure *within that file* is **32 declarations / 286
lines**. Of those, **seven are already ported** — `TS`, `TS_coeff_mul`,
`TS_coeff_of_not_dvd`, `TS_coeff_neg`, `TS_coeff_of_lt`, `TS_injective`,
`qExpand_TS` are `FLTForHuman/ModularCurve/Defs/TS.lean` (Layer 0b). The rest:

| FLT lines | declaration | role |
|---|---|---|
| 102–105 | `coeffEmb_qExpand` | `coeffEmb` commutes with `qExpand`; **4 lines**, from `coeffMap_qExpand` |
| 106–109 | `iota_jqN` | `coeffEmb (qExpand ℚ N (jqN d)) = TS K (N*d) 1` |
| 110–112 | `iota_jq` | the same at level 1 |
| 199–204 | `exists_isPrimitiveRoot_cyclotomicField` | a primitive `N`-th root in `CyclotomicField N ℚ` |
| 205–207 | `cycUnit` | that root, as a unit |
| 208–212 | `cycUnit_spec` | it is primitive |
| 229–240 | `isPrimitiveRoot_pow_div` | powers of primitive roots at divided levels |
| 413–419 | `Tight`, `Gen`, `Hall` | the two invariants and their bundle (verbatim below) |
| 420–435 | `jqN_congr`, `full_congr`, `mff_congr`, `qExpand_congr'` | congruence plumbing |
| 436–466 | `dedekindPsi_prime'`, `dedekindPsi_mul_prime_not_dvd`, `dedekindPsi_mul_prime_dvd` | the `ψ` arithmetic the induction needs |
| 467–488 | `tight_one`, `gen_one` | the `d = 1` base cases |
| 489–500 | `relfinrank_full_of`, `F0_le_full` | degree and inclusion glue |
| 501–523 | `full_le_adjoin_chain` | the tower step for `Gen` |
| 524–540 | `jqN_pow_not_mem_full` | non-membership at prime powers |
| 541–567 | `root_shape` | the slot shape of a root, from `minpoly_jqN_map_eq_prod_slots` |
| 568–589 | `htw_of` | the twist hypothesis for `jqN_div_mem_modularFunctionField` |
| 590–613 | `hsp_of` | the slot hypothesis for the same |

**One node classified into the Φ_p cut is needed and is cheap — port it.**
`coeffMap_qExpand` sits in `closure(PhiGen.splits_prime_at_slot)` and so fell
outside PORTING-FFG §7.3's 24, but `coeffEmb_qExpand` uses it, and its own
solution file is **15 lines** whose proof is exactly Layer 0a's
`coeffMap_coeff` / `qExpand_coeff_mul` / `qExpand_coeff_of_not_dvd`. Port it as a
lemma in `Spine.lean` rather than assuming it. (`iota_jqN`, `iota_jq` and the
seven `TS` lemmas stay where they are: `TS` is from Layer 0b.)

**Which significant statements the helpers consume** (so these are `Inputs`
candidates; the exact set comes from pruning):

- `root_shape` uses `minpoly_jqN_map_eq_prod_slots`;
- `jqN_pow_not_mem_full` uses `jqN_prime_not_mem_full`;
- `full_le_adjoin_chain` uses `full_eq_adjoin_full_div_prime`;
- `hall_all` itself uses `modularFunctionField_eq_full_of`,
  `jqN_div_mem_modularFunctionField`, and — through the `Tight` step — the degree
  facts `relfinrank_full_eq_mul`, `finrank_adjoin_jqN_pow_succ_of_not_mem`,
  `finrank_adjoin_jqN_prime_of_not_mem`, `jqN_pow_not_mem_adjoin_full`,
  `exists_phiIrreducible_of_finrank_eq`;
- `relfinrank_full_of` uses `relfinrank_modularFunctionField`;
- the arithmetic helpers use `dedekindPsi_mul_of_coprime`, `dedekindPsi_prime_pow`.

The definitions, verbatim from FLT (private there; make them whatever you like
here, but keep the statements):

```lean
abbrev Tight (d : ℕ) [NeZero d] : Prop :=
  Module.finrank ℚ⟮jq⟯ (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
abbrev Gen (d : ℕ) [NeZero d] : Prop := modularFunctionField d = modularFunctionFieldFull d
abbrev Hall (N : ℕ) : Prop := ∀ d : ℕ, d ∣ N → ∀ [NeZero d], Tight d ∧ Gen d
```

## 3. Route

1. **Transport and cyclotomic block.** `coeffMap_qExpand` (port, 15-line proof),
   `coeffEmb_qExpand`, `iota_jqN`, `iota_jq`; then
   `exists_isPrimitiveRoot_cyclotomicField`, `cycUnit`, `cycUnit_spec`,
   `isPrimitiveRoot_pow_div`. Needs `Mathlib.NumberTheory.Cyclotomic.Basic`.
2. **Plumbing and arithmetic.** The four congruence lemmas and the three
   `dedekindPsi_*` helpers. These are where an existing `dedekindPsi` lemma may
   already do the job — check §4's checklist before transcribing.
3. **The invariants and base cases.** `Tight`/`Gen`/`Hall`, `tight_one`,
   `gen_one`, `relfinrank_full_of`, `F0_le_full`.
4. **The tower steps.** `full_le_adjoin_chain`, `jqN_pow_not_mem_full`,
   `root_shape`, `htw_of`, `hsp_of`.
5. **`Inputs`.** Start with all 24 nodes of PORTING-FFG §7.3, statements verbatim
   from the pin. Wire `hall_all` against it.
6. **`hall_all`**, then `functionFieldGeneration_of`, whose proof is the
   `functionFieldGeneration_iff_full_eq` direction applied to `hall_all` — the
   equivalence is already proved in `Collapse.lean`.
7. **Prune `Inputs`.** Remove fields `hall_all` does not use; record what
   survived and why. Report the count before and after.

## 4. What is different about this topic

- **It has a helper layer, and that layer is the risk.** The `jq`-coefficients
  topic was a flat computation. Here, ten of the scouted declarations
  (`full_le_adjoin_chain`, `jqN_pow_not_mem_full`, `root_shape`, `htw_of`,
  `hsp_of`, and the `Tight` step) are *proofs of substance*, not congruence
  shuffles. If any of them turns out to need machinery this module does not
  have, the right move is to **add it to `Inputs` as a named field and say so**,
  not to expand scope. That is the whole advantage of the conditional shape.
- **`Inputs` is a structure of `∀`-statements with `[NeZero]` instances.** Expect
  instance-management friction when calling a field (`h.minpoly_jqN_map_eq_prod_slots M …`).
  Keep the field names identical to the node names so a later discharge is a
  drop-in.
- **The consumer.** Zone A's capstone example is the *unconditional* theorem and
  stays `sorry`; `functionFieldGeneration_of` is a new bound item. Add it to
  Zone B (it is the §2 collapse's companion) and update the prose so the two are
  not confused. The `sorry` count stays at 1.
- **The checker.** The auxiliaries are FLT's statements but the script does not
  read `private` declarations, so they are invisible to it; the capstone is ours
  and must be added to `OWN_PROOFS` with a comment, exactly as the two `jq.coeff`
  theorems were. Its `SOURCES` already include the solution file.

## 5. Budget

**4 goal rounds, scouting checkpoint at round 1.** The scouting is largely done
in §2, so round 1 is about *shape*, not discovery: establish that the
transport/cyclotomic block compiles and that `Inputs` can be threaded through a
first helper. If by the end of round 1 the `Inputs` threading is fighting you, or
a helper needs material beyond §2, **stop and report** — the conditional capstone
is optional, and a report that names the missing machinery is a perfectly good
outcome.

The measured pace on three comparable pieces is 1 round each; four rounds is the
signal that something structural is wrong, not the expectation. If the auxiliaries
turn out to be glue, expect 1–2.

## 6. Definition of done

- [x] `FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean` complete as in §0, with a header
  recording the FLT provenance (the solution file and line spans), the
  conditional design, and what `Inputs` is for.
- [x] `lake build` green, 0 warnings, no `sorry`.
- [x] `#print axioms ModularCurve.functionFieldGeneration_of` — only `propext,
  Classical.choice, Quot.sound`. This is the point of the artifact: no `sorryAx`.
- [x] `Inputs` pruned, with the field count before and after and a one-line
  reason for each survivor.
- [x] Consumer: `functionFieldGeneration_of` bound in Zone B; prose updated; the
  only `sorry` still the unconditional capstone.
- [x] `spec/check_flt_statements.py` reports 0 mismatches, with
  `functionFieldGeneration_of` in `OWN_PROOFS` (commented).
- [x] `logs/ffg-port.md` gains a §2d with measured cost, and §8's option space
  updated: the conditional capstone is done, so the remainder is now a structure
  of fields to discharge one at a time.
- [x] README module table and PORTING-FFG status updated.

## 7. Reporting back

Same shape as the previous topics. Two things specifically:

1. **The `Inputs` field set, final and minimal, with the reason each survives.**
   That list is the deliverable's payload: it is the precise statement of what a
   full port would still owe.
2. **Whether the auxiliaries were glue.** If any of `root_shape`, `htw_of`,
   `hsp_of`, `full_le_adjoin_chain` or `jqN_pow_not_mem_full` carried substance,
   say which and what it needed — that is the signal for whether the remainder is
   ever worth attacking, and the log's §8 should carry it.
