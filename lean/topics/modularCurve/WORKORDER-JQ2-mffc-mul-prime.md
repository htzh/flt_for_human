# WORKORDER-JQ2 — `j(q ^ M)` is in the level-`M * p` field

Status: **open**, dispatched 2026-10-25. Owner: the set's agent, reviewed by the manager.

The node:

| node | pin `S_` | pin lines | declares | frontier |
|---|---|---:|---|---|
| `ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime` | `S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean` | 544 | 43 | needed 1 (itself) |

`frontier.py --target` read **needed 1 node / 544 raw lines** before landing, and `--also` on it
moved the D-S column by exactly its own lines (1,189 → 1,188 nodes, 448,680 → 448,136 raw). Every
premise was ported: the node is a leaf, and it is the last member of the `C`-layer degree group JQ1
and CL1–CL3 belong to. Its only consumer is `package_of_socket` (WORKORDER-CL4), which takes it as
the hypothesis `hKG1`. Both readings are historical now: the node is ported, so `--also` moves the
column by 0, and the D-S column reads 1,185 nodes / 446,852 raw after JQ2 and CL4's char-`p` pair.
"Removes exactly its own lines" is only observable on an *unported* F-terminal node — it is not a
property to re-measure after landing.

## 1. What the mathematics is

`F := modularFunctionFieldC K (M * p) = K⟮j(q), j(q ^ (M * p))⟯`. Show `j(q ^ M) ∈ F`.

Two polynomials over `F` vanish at the same point `x := qExpand K (M * p) (jqNModC K M)`:

1. `A := phiAtSeed data ⟨jqNModC K (M * p)⟩`, the modular relation at the level-`M * p` seed. Its
   roots are the `p + 1` slot values at slot `M * p` (`p` finite conjugates
   `TS((M*p)*M, ζ₂ ^ c)`, `c < p`, plus the `p * p` cusp `TS(p*(p*(M*p*M)), 1)`), read off the
   ported `isRoot_prime_at_slot_iff`. `x` is the `c = 0` conjugate.
2. `B := m.map ι₀`, where `m := minpoly K⟮j(q)⟯ (jqNModC K M)`. The hypothesis `hprod` — the
   pin's statement of the CL1 slot product — says `B`'s image in `LaurentSeries K` is the product
   over `a ∣ M`, `b < M/a`, `gcd(gcd a b, M/a) = 1` of `X - qExpand K (a*a) (qTwist (ζ₁ ^ (b*a)) jqModC)`.
   Hence every root of `B` is `TS(p*(a*a), ζ₁ ^ (b*a))`, and `x` is the root with `a = M`, `b = 0`.

`TS_injective` plus `2 ≤ p` and `omega` then kill every other common root: the cusp branch would
need `p * (M * p * M) = a * a`, while `a ∣ M` gives `a * a ≤ M * M` and the left side is `p^2 * M^2`;
the finite branch forces `a = M`, then `b = 0`, then `ζ₂ ^ c = 1` with `c < p` forces `c = 0`. So
`x` is the *unique* common root, and `Polynomial.mem_range_of_unique_common_root` puts it in the
range of `algebraMap F (LaurentSeries K)` — i.e. `j(q ^ M) ∈ F` after `qExpand_injective`.

This is the `C` twin of the prime step `jqNModC_mem_of_div_prime_of_mul_prime` (CL2), with the
two-prime peeling replaced by "`minpoly` product of slots + the level-`p` slot". It is the pin's
`S_:358–505` (148 lines), and it is the only genuinely new proof in the file.

## 2. Module plan

### P1 — `ModularCurve/FunctionFieldGeneration/MffCMulPrime.lean` (new, wired)

Two declarations, both public, names as the pin's:

- `jqNModC_mem_mffC_mul_prime_of_prod` — the engine, from `S_:358`.
- `jqNModC_mem_modularFunctionFieldC_mul_prime` — the headline. The pin states it **twice**: a
  `private` copy at `S_:514` (19 lines) and the `Theorems/` wrapper at `Thm_:9` (10 lines), the
  two statements byte-identical. Port **one** public declaration and take the **wrapper's**
  binder block (that is the checker's authority, per the JQ1 precedent); the `private` copy is
  the wrapper's statement verbatim and is not ported.

Estimate: 231 net new content lines (`port_plan --section budget`: 544 raw → 501 once-cost after
dedup → 270 already in the port), so ~250–280 written. No new `def`s; no new mathematics beyond §1.

## 3. What the port already has — import, do not restate

`port_advise.py -t ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime`: **31 of 43 declarations
already have the statement in the port** (31 byte-identical, ≈270 lines), 30 of them public and
importable. Importing `FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProductAnyField`
transitively brings the whole list. The ones §1 uses, with their homes:

| pin declaration | port home |
|---|---|
| `phiAtSeed`, `_map`, `_monic`, `_natDegree`, `_eval_map` | `ModularCurve/Defs/PhiAtSlot.lean` |
| `isRoot_prime_at_slot_iff`, `roots_prime_at_slot(_nodup)(_roots_nodup)`, `roots_phiAtSeed_TS` (all `_of_isPrimitiveRoot`) | `ModularCurve/PhiGenSplitsAnyField.lean` |
| `TS`, `TS_injective`, `TS_congr`, `qExpand_*_TS`, `qTwist_TS_one_cycle`, `qTwistEquiv`, `coe_qTwistEquiv` | `ModularCurve/Defs/TS.lean` |
| `isPrimitiveRoot_pow_div`, `units_pow_eq_one_of_isPrimitiveRoot` | `ModularCurve/Defs/Cyclotomic.lean`, `Degree/JqCyclotomicConjugates.lean` |
| `prod_form_ne_zero` | `ModularCurve/PhiGenSplitsAnyField.lean` — `private` there **by design** (7 lines): its public home is `PhiSlotRoots.prod_form_ne_zero`, which states the `ℚ`/`coeffEmb` spelling, so a public copy of the `C` spelling would collide. Nothing in §1 needs it |
| `Polynomial.mem_range_of_unique_common_root` | `FLTForHuman/FieldTheory/CommonRoot.lean` |
| `jqModC_mem`, `jqNModC_mem`, `modularFunctionFieldC` | `ModularCurve/Defs/JqCoeff.lean` |
| `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot`, `exists_phiIrreducible_evalSymm` | `PhiGenSplitsAnyField.lean`, `ModularPolynomialProperties.lean` |

Two declarations exist in the port under **different binders**, and are the ones §1 needs at
`R = K`:

- `coeff_jqModC_of_lt` — `X0/FunctionFieldFull.lean` states it for `[CommRing R]`; the pin's `K`
  spelling is a specialisation. Use the port's.
- `qTwist_qExpand_of_pow_eq_one` — `Defs/KatzLevelPCusps.lean` states it for `[CommRing R]` with
  `ζ`; use the port's (`rfl` between the spellings).

`coeffMap_TS` is the same lemma with the pin's section `variable`s; `coeffMap_qTwist` is one of
four statement variants already in the pool — call the nearest one, do not add a fifth.

## 4. Known drifts — read these before transcribing

1. **The statement is the wrapper's, not the `S_` file's.** Copy binders from
   `Theorems/Thm_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean:9`, which is
   `{K : Type*} [Field K] (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
   (hζ : IsPrimitiveRoot (ζ : K) (M * p)) (hall : …)`. Spell the `hall` block out **verbatim**:
   `ModularCurve.Pkg` now exists (`Defs/JqCoeff.lean`, the same statement as an `abbrev`), but the
   checker hashes statement text and does not unfold abbreviations, so `Pkg K M` in a *pinned*
   statement reads `MISMATCH`. Use `Pkg` freely inside the engine's own `private` helpers.
2. **Keep the `hprod` guard.** The engine's hypothesis has `if h : a = 0 then 0 else …`; `a ∣ M`
   and `M ≠ 0` make the `else` branch dead, but the checker diffs the statement, so it stays.
3. **`ζ₁`/`ζ₂` are `Kˣ`, not `K`.** The slot lemmas take `IsPrimitiveRoot (ζ₂ : K) p` but the
   products exponentiate `ζ₁`, so the two `ζ`s never need to be equal — do not unify them.
4. **Drop the pin's plumbing:** `namespace W1`/`p2m_export`/`p2m_open_scoped`/`p2m_reactivate`, the
   20-line `attribute [-simp]` block, and the `set_option autoImplicit false` line (the project's
   `lakefile` already sets `autoImplicit := false`).
5. **`S_:533`'s `solution` and `#print axioms`** are the wrapper's content; in the port the
   headline *is* the wrapper, so add only the `#print axioms` line the JQ1 modules carry.

## 5. Gates (all green, and report the readings)

1. `lake env lean FLTForHuman/ModularCurve/FunctionFieldGeneration/MffCMulPrime.lean`, then
   `lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.MffCMulPrime` — **single-module
   builds only, never a tree build**, each call bounded (the project allows 2 minutes per call;
   log to `lean/tmp/`). 0 warnings, `#print axioms` reads `[propext, Classical.choice, Quot.sound]`.
2. `cd lean && python3 spec/check_port.py <the module>` with the two `spec-pin:` header lines
   (`P2M/Sol/S_…`, `Theorems/Thm_…`): expect **2 ok / 0 mismatch / 0 missing / 0 own**, and — once
   CL4 lands — the same for the socket module that consumes it.
3. `cd tools/deps && python3 dedup.py --module '*MffCMulPrime*'` → **0 clusters** (the engine is
   unique in the port); `python3 move_dead.py --source <module> --target /tmp/shelf.lean
   --select dead` → **0 declarations**.
4. `python3 tools/deps/frontier.py --target ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime`
   → **needed 0**, "target is ported"; `--ds --also <node>` must now read 1,188 nodes / 448,136.
5. `tools/check_math_delimiters.py` on this order's §7 note if it grows math.

## 6. Recording

`CARRY-FORWARD.md` is **open issues only** — no landing entry. The record goes in
`topics/functionFieldGeneration/TOPIC-qexp-function-field-c.md` §10 (one paragraph with the
readings) and in §7 below. Two things must be carried forward, not silently absorbed:

- `prod_form_ne_zero`: the `C` spelling stays `private` in `PhiGenSplitsAnyField.lean`, by design —
  promoting it would collide with `PhiSlotRoots.prod_form_ne_zero`, the `ℚ` spelling. The engine
  should not need it at all; if a proof does, report the blocker rather than adding a third copy.
- The `hall` binder block is repeated in `SlotProductAnyField`'s declarations and now here. If
  CL4 lands `Pkg K M` first, restate both here and — with the manager's approval, since it is a
  frozen-registry module — in `SlotProductAnyField`; measure the churn first.

## 7. Result

Landed 2026-10-25 (worker). New wired module
`FLTForHuman/ModularCurve/FunctionFieldGeneration/MffCMulPrime.lean`, **251 lines** against the
231-line bound (inside the predicted 250–280): two public declarations, the pin's names, no `def`,
no `private` helper, one import (`FunctionFieldGeneration.SlotProductAnyField`, which brings the
whole substitution list transitively).

| declaration | pin | pin lines |
|---|---|---:|
| `jqNModC_mem_mffC_mul_prime_of_prod` (engine) | `S_…_mul_prime.lean:358–505` | 148 |
| `jqNModC_mem_modularFunctionFieldC_mul_prime` (headline) | `Theorems/Thm_…_mul_prime.lean:9` (= `S_:514`) | 19 |

**The pin's argument ported with no proof change.** `A := phiAtSeed data ⟨jqNModC K (M * p)⟩`,
`B := (minpoly K⟮jq⟯ (jqNModC K M)).map ι₀`, then
`Polynomial.mem_range_of_unique_common_root` with uniqueness from `TS_injective`, `2 ≤ p` and
`omega`, went through as written. The only edits were three name resolutions
(`isRoot_prime_at_slot_iff` and `roots_prime_at_slot_roots_nodup` gain the port's
`_of_isPrimitiveRoot` suffix; the splitting lemma lives under `PhiGen` in the port) and
`dif_neg` → `dite_eq_right` (deprecated alias in mathlib v4.34). `set_option
linter.style.haveILetI false` is needed for the engine's `letI`/`haveI` instances, as in
`SlotProductAnyField.lean`.

**`prod_form_ne_zero` was not promoted, and was not needed.** The engine's hypotheses never
mention it and the roots-API lemmas that use it are already public; the `C` spelling stays
`private` in `PhiGenSplitsAnyField.lean` by design. No third copy was added.

| gate | reading |
|---|---|
| `lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.MffCMulPrime` | green, 4,033 jobs, 15 s for the module, **0 warnings**, no `sorry` |
| `#print axioms` on the headline | `[propext, Classical.choice, Quot.sound]` |
| `spec/check_port.py --force` on the module | **2 ok, 0 mismatch, 0 missing, 0 own, 0 kw**, corpus `aa2d8b3` |
| `dedup.py --module '*MffCMulPrime*'` | 2 declarations, **0 duplicate clusters**, 0 removable lines |
| `move_dead.py --select dead` on the module | **0 declarations, 0 lines** |
| `frontier.py --target ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime` | `needed 0`, `target hops to F 0` — **target is ported** |

Checker attribution: the engine diffs `ok` at `S_:358`, the headline at `S_:514` (the pin's
`private` copy, byte-identical to the wrapper whose binder block was taken; the two hash the
same). No `own:` and no `pin:` rows were added.

**Frontier detail, and one stale figure.** `needed [F terminal]` is 0 as above; `[literal]`
(cone minus ported) still reads 1 node / 281 lines,
`ModularCurve.PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff` — a node *below* a ported premise,
pre-existing and unrelated, which the terminal reading never demands. It was already one of the
two literal leftovers before landing (alongside this node itself), so it is not JQ2 residue.

§1/§5's D-S figure has drifted: `frontier.py --ds` now reads **1,185 nodes / 446,852 lines**, not
1,188 / 448,136, and `--also <this node>` now moves it by **0** (the node is ported and
F-terminal, so the flag is a no-op). The prediction assumed the frontier as of dispatch; CL1, CL2,
the `Pkg`/`hall` ground work and the concurrent order have since landed further nodes in the D-S
cone — three nodes' worth. What §5.4 was testing, that this node's own 544 lines leave the
column, was measured pre-landing, when `--also` moved it by exactly 1 node / 544 lines.

**Not done, deliberately.** No paragraph was added to
`topics/functionFieldGeneration/TOPIC-qexp-function-field-c.md` §10 (this order's §6): §10.3 is
owned by the concurrent order and editing that file from this session would race it. The readings
are in §7 here and in `logs/jq2-mffc-mul-prime.md`.
