# JQ2 — `j(q ^ M)` is in the level-`M * p` field: landing log

2026-10-25. Port of `ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime`
under [WORKORDER-JQ2](../topics/modularCurve/WORKORDER-JQ2-mffc-mul-prime.md).
Nothing is left `sorry`; no module outside the order's scope was edited.

## The module

`FLTForHuman/ModularCurve/FunctionFieldGeneration/MffCMulPrime.lean`, **251 lines**
(order bound: 231 net new, ≈250–280 written). Two public declarations, the pin's
names, no `def`, no `private` helper, no new import beyond
`FunctionFieldGeneration.SlotProductAnyField` (which brings the whole substitution
list transitively).

| declaration | pin source | pin lines |
|---|---|---:|
| `jqNModC_mem_mffC_mul_prime_of_prod` — the engine | `S_…_mul_prime.lean:358–505` | 148 |
| `jqNModC_mem_modularFunctionFieldC_mul_prime` — the headline | `Theorems/Thm_…_mul_prime.lean:9` (= `S_:514`, byte-identical) | 19 |

## Readings

| gate | reading |
|---|---|
| `lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.MffCMulPrime` | green, 4,033 jobs, 15 s for the module on top of replayed deps, **0 warnings**, no `sorry` |
| `#print axioms ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime` | `[propext, Classical.choice, Quot.sound]` |
| `spec/check_port.py --force` on the module | **2 ok, 0 mismatch, 0 missing, 0 own, 0 kw**, corpus `aa2d8b3` |
| `dedup.py --module '*MffCMulPrime*'` | 2 declarations, **0 duplicate clusters**, 0 removable lines |
| `move_dead.py --select dead` on the module | **0 declarations, 0 lines** |
| `frontier.py --target ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime` | `needed 0`, `target hops to F 0` — **target is ported** |
| `frontier.py --ds` (the D-S column) | 1,185 nodes / 446,852 lines; `--also <this node>` moves it by **0** |

Checker attribution: the engine diffs `ok` at `S_:358`; the headline at `S_:514`.
No `own:` row and no `pin:` row was needed (both statements are the pin's text).

## What a future reader would otherwise have to rediscover

1. **The engine ports verbatim, with zero proof edits.** The pin's argument —
   `A := phiAtSeed data ⟨jqNModC K (M * p)⟩`, `B := (minpoly K⟮jq⟯ (jqNModC K M)).map ι₀`,
   `Polynomial.mem_range_of_unique_common_root` with a uniqueness from
   `TS_injective` + `2 ≤ p` + `omega` — went through as written. Every pin-line
   number in the order's §1 is the transcribed line; nothing was re-planned.
2. **Three name resolutions, and nothing else.** `isRoot_prime_at_slot_iff` →
   `isRoot_prime_at_slot_iff_of_isPrimitiveRoot`,
   `roots_prime_at_slot_roots_nodup` →
   `roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot` (both
   `PhiGenSplitsAnyField.lean`), and `ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot` → `PhiGen.…`
   (the port keeps the `PhiGen` namespace).
3. **`dif_neg` is deprecated** in this mathlib (v4.34): the `hprod` guard's dead
   `if h : a = 0` branch is eliminated with `dite_eq_right ha0` (as
   `SlotProductAnyField.sv_eq` already does), not `dif_neg`.
4. **`set_option linter.style.haveILetI false` is required.** The engine installs
   `Algebra (modularFunctionFieldC K (M * p)) (LaurentSeries K)` by `letI` and a
   `NeZero a` by `haveI`; both are typeclass inputs, so the linter's advice is
   wrong. Same precedent as `SlotProductAnyField.lean`. Unlike that module, no
   `open scoped IntermediateField.algebraAdjoinAdjoin` is needed here (measured:
   the file compiles unchanged with the line deleted), so the module carries none.
5. **`prod_form_ne_zero` was not needed and stays `private`** in
   `PhiGenSplitsAnyField.lean`. The engine's hypotheses never mention it; the
   roots API lemmas that use it are already public. No third copy exists.
6. **`needed [literal]` is not `needed`.** The target reads `needed 0` /
   `target is ported`, but `[literal]` (cone minus ported) still shows one node,
   `ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff` (281 lines). It sits
   *below* a ported premise, is pre-existing, and is not part of the demand; the
   terminal reading never asks for it. Do not read it as JQ2 residue.
7. **The order's §1/§5 D-S figure has drifted.** `--ds` reads 1,185 nodes /
   446,852 lines, not the 1,188 / 448,136 §5.4 predicts. The prediction assumed
   the frontier as of dispatch; CL1, CL2, the `Pkg`/`hall` ground work and the
   concurrent order have since landed further D-S-cone nodes (3 nodes lower).
   What the gate actually checked — that the node's own 544 lines leave the
   column — is now unmeasurable through `--also` (the node is F-terminal, so the
   flag is a no-op); it was measured pre-landing, when `--also` moved the column
   by exactly 1 node / 544 lines.

## Residue

No paragraph was added to
`topics/functionFieldGeneration/TOPIC-qexp-function-field-c.md` §10 (which the
order's §6 asks for): §10.3 is owned by the concurrent order, and editing that
file from this session would race it. These readings are the record instead.
`CARRY-FORWARD.md` was not touched (open issues only).

**The `hall` block now has a third site.** The order's §6 carry-forward item is
live: the conjunction is spelled out in `SlotProductAnyField`'s two headlines, in
`Pkg` (`Defs/JqCoeff.lean`, an `abbrev`, not unfolded by the checker), and now in
this module's headline. If CL4 restates it as `Pkg K M` here, the same edit is
needed in `SlotProductAnyField` (frozen registry — manager approval) and the
churn is two modules' public statements; measure before doing it.

