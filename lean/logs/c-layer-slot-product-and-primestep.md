# The `C`-layer slot product and prime-power step — WORKORDER-CL1/CL2 landing

Landing record for the three largest ready `ModularCurve` nodes of the D-S demand, 2026-10-25.
Scope: [modularCurve/TOPIC-c-layer-slot-product-and-prime-power-step.md](../topics/modularCurve/TOPIC-c-layer-slot-product-and-prime-power-step.md).
Orders: [WORKORDER-CL1](../topics/modularCurve/WORKORDER-CL1-slot-product-any-field.md) (two
headlines, one module), [WORKORDER-CL2](../topics/modularCurve/WORKORDER-CL2-fullc-prime-power-step.md)
(the prime-power step, one module). Ground: [x0-function-field-general-index.md](x0-function-field-general-index.md).

## 1. The nodes

| node | pin `S_` | raw | frontier before | after |
|---|---|---:|---|---|
| `ModularCurve.minpoly_jqNModC_map_eq_prod_slots` | 1,914 | | needed 1 | ported |
| `ModularCurve.jqNModC_prime_not_mem_fullC` | 1,909 | | needed 1 | ported |
| `ModularCurve.relfinrank_fullC_mul_prime_pow` | 1,175 | | needed 1 | ported |

All three were `needed 1` — every premise ported — so this was transcription with the field
general, which the measured `C`-vs-`ℚ` line diffs confirmed before dispatch (`rval_aux` 206 of 663
lines differ, the adjoin separation 151 of 334, the two-prime descent 125 of 249).

## 2. The two modules

| module | lines | declarations | build | checker | axioms |
|---|---:|---|---|---|---|
| `FunctionFieldGeneration/SlotProductAnyField.lean` | 1,283 | 17 (2 public, 15 `private`) | 60 s, 0 warnings | **2 ok / 0 own** | clean |
| `FunctionFieldGeneration/PrimePowerStepAnyField.lean` | 1,108 | 45 (all public) | 15 s, 0 warnings | **45 ok / 0 own** | clean |

The two `S_` twin files of CL1 (1,914 and 1,909 lines, `diff` = 85 lines of `p2m_*` plumbing)
became **one** module — they are one 80-declaration development, and each proves both headlines.
The pin's own prelude (40 declarations, lines 34–354) and its 108-line CRT slot-count chain are
imports/the public counting export, not transcriptions. CL2's three respellings
(`divSet`/`fullC`/`qExpandₐK`) are one-line `abbrev`s of homed objects, which is what held its
checker at 0 `own:` rows: **62 declarations across the two modules, 0 duplicate clusters,
0 removable lines**, `move_dead.py` 0 dead.

**Manager's cleanups.** CL2 kept the pin's two `private` re-exports
(`fullC_mul_prime_pow_eq_adjoin`, `finrank_adjoin_jqNModC_prime_of_not_mem`); both are dead in the
pin (`grep` over the whole pin tree: one occurrence each, its own declaration) and restate public
declarations, so they were dropped (−31 lines, header records them, and the one `dedup.py` cluster
they formed is gone). Both headers' prelude counts were corrected to the measured 40.

## 3. The wave readings

- **D-S demand**: `needed` **1,192 → 1,189 nodes**, **453,678 → 448,680 raw `S_` lines** (−3 /
  −4,998 = the three files). `F` is now 1,197 nodes / 671,969 lines.
- **The parent `C`-layer cone** (`qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull`):
  **22 → 19 nodes**, **10,662 → 5,664 raw** — the three were its three largest ready nodes.
- **Statement check** (`check_port.py --changed --strict-markers`): **5,455 ok / 0 mismatch /
  0 missing / 30 own (all registered) / 0 kw**, exit 0, 243 modules.
- **Build**: both modules green (4,193 jobs together), 0 warnings, no `sorry`, **no
  `set_option maxHeartbeats`** in either.
- **Axioms**: all four public theorems `[propext, Classical.choice, Quot.sound]`.
- **Consumer**: `spec/ModularCurveConsumer.lean` gained **Zone X** (the three headlines + `eFull` /
  `divSet` / `fullC`, and applications of the slot product and of the prime-power step at
  `a = 0`). **0 errors**, exit 0 — and see §4.

## 4. Two findings worth carrying

1. **The consumer had drifted off 0 errors, and nobody noticed.** At `HEAD`, before this wave,
   `spec/ModularCurveConsumer.lean` already had four error sites: (i) the Zone C `TS` identity
   `TS K e u = qExpand K e (qTwist u (coeffEmb K jq))` was `rfl`, which the 2026-10-25 `[Field K]`
   generalization of `TS` ([ts-general-field.md](ts-general-field.md)) turned into
   `rfl`-false (it is definition + `coeffEmb_jq` now); (ii) `roots_phiProd_conj_nodup` lost its
   `[Algebra ℚ K]` binder in the same refactor, so the consumer's `@… ℂ _ _ 2 …` had one argument
   too many; (iii) and (iv) `dedekindPsi` was already **ambiguous** under `open ModularCurve`
   (`_root_.dedekindPsi` vs `ModularCurve.dedekindPsi`). All four are fixed (`rw [TS, coeffEmb_jq]`;
   one `_` dropped; the two sites qualified), and the file now reads **0 errors** with Zone X
   included. The lesson is mechanical: **the consumer is not in any build and its "compiles today"
   claim is only as fresh as the last hand run** — re-run it at the end of every wave that touches
   `Defs/TS.lean`, `Defs/PhiAtSlot.lean` or the `ψ` homes.
2. **The 200k edit loop is not a defect signal in this tree, and `rval_aux`'s cost is the proof's
   shape, not the `C` layer.** Profiled (`-Dprofiler=true`): the module's ~65 s is `import` 3.2 s,
   prelude ~2 s, `rval_aux` ≈46 s, separation + headlines ≈15 s; inside `rval_aux`, **19.3 s is one
   single `type checking` event** — the check of the finished 661-line proof term against its
   statement — with ~14 s of tactics and ~10 s of typeclass search. The *landed* `ℚ` twin pays the
   identical single 18.9 s check (tactics 12.6 s), so the `C` layer is within ~15 % of it and the
   cost is inherent to one 660-line strong induction. Thresholds: 200k and 300k fail, 350k is
   clean; the `ℚ` twin also fails 200k. Both are 11–13× under the project's 4,000,000. The only
   real lever is splitting `rval_aux` into 2–3 lemmas; not worth a 661-line refactor of a green
   leaf module. Recorded in the CL1 order's §7 so the next worker does not chase it.

## 5. Clarity debt: the census that justifies the refactor wave

Scanning all 22,436 declarations of `FLTForHuman` for body length (declaration line to the line
before the next declaration, trailing docstrings/commas trimmed), the two `rval_aux` monoliths are
**the two longest proofs in the port**:

| span | declaration |
|---:|---|
| 692 | `FunctionFieldGeneration/SlotProduct.lean` :: `rval_aux` (the `ℚ` layer) |
| 661 | `FunctionFieldGeneration/SlotProductAnyField.lean` :: `rval_aux` (this wave) |
| 530 | `NumberTheory/NumberField/CompletedDedekindZeta/Poisson.lean` :: `poissonLawBlock_of_poissonLaw` |
| 514 | `AlgebraicCurve/Genus/DegreeIdentity.lean` :: `degree_le_finrank_adjoin_of_eq_max_neg_ord` |
| 429 | `AlgebraicCurve/Tate/Agreement.lean` :: `ringEquiv_of` |
| 428 | `ModularForms/WeightOne/LevelN.lean` :: `exists_monicRel_j_K_of_mdifferentiable_frickeQuotient` |
| 369 | `SlotProduct.lean` :: `jqN_prime_not_mem_adjoin` |
| 322 | `SlotProductAnyField.lean` :: `jqNModC_prime_not_mem_adjoin` |

So the two `functionFieldGeneration` slot-product modules alone hold the four worst proofs in the
port, and they are the same development twice — which is why the refactor wave starts there (split
into named private lemmas, with a docstring per sub-goal) and why the `ℚ` twin comes second: it is
larger, it is imported by the FFG capstone chain, and it must be refactored *after* CL1's module
because CL1 imports it. The 200–530-line tail beyond that is real clarity debt but not low-hanging:
each needs its own mathematical judgement.

## 5b. Refactor wave (2026-10-25, second dispatch)

Both landed modules were cut for readability. One of them was also genuinely slow, and the split
fixed that too:

| module | wall | heartbeat peak | longest body |
|---|---|---|---|
| `SlotProductAnyField` before | **54 s** | **350k** | 661 |
| `SlotProductAnyField` after | **34–36 s** (−36 %) | **100k** (75k fails) | 148 |
| `PrimePowerStepAnyField` before | 13.4 s | 45k | 119 |
| `PrimePowerStepAnyField` after | 13–15 s (unchanged) | 45k | 60 |

So `SlotProductAnyField` was **four times** its sibling's build cost for a similar line count, and
the two monoliths were most of that; cutting them cut the cost. (`PrimePowerStepAnyField` was
already fast — its pass is clarity only.) Footnote: on the big module **user CPU rose 60.6 → 73.4
s** — smaller declarations parallelise better in codegen, so part of the 36 % wall gain is
parallelism rather than less work; wall is what the edit loop and the build pay, so the gain
stands, but it is not "less total computation".

| module | lines | longest body | headline/step body | gates |
|---|---|---|---|---|
| `PrimePowerStepAnyField` | 1,108 → 1,296 | 119 → 60 | 104 → 23 | identical |
| `SlotProductAnyField` | 1,283 → 1,512 | 661 → 148 | 661 → 96, 322 → 94 | identical |

`SlotProductAnyField`'s wall did fall (**54.1 s → 35.9 s**, manager's interleaved A/B) but **user
CPU rose 60.6 → 73.4 s** — smaller declarations parallelise better in codegen, so wall drops while
the work grows. What genuinely fell is the heartbeat *peak*: 350k → 100k (75k fails). The single
19–20 s type check is unchanged in both modules and was bisected to a named sub-proof
(`finrank_adjoin_mul_dedekindPsi`: the pin's `finrank_mul_finrank`/`adjoin_adjoin_left`/
`restrictScalars` tower block) that used to be buried inside `rval_aux`.

**The reusable finding — do not `set` a large subterm.** Naming a big term with `set` and then
rewriting with it makes `rw`/unification unfold the local definition at every occurrence: tactic
execution went 9.5 s → 15–17 s on `PrimePowerStepAnyField`, and reverting to the literal terms
restored it (8.69 s). The same effect for a redundant `rw [phiAtSeed]` (≈1.5 s per use) and for
`rw … at h` on a root disjunction (≈1.5 s each). A small `set` (a `ℕ` like `Nat.gcd d M`) is free.
Rule of thumb: `set` pays when the term is small and the rewrite frequent; for large terms it is a
pessimisation. This is the kind of trap a split can walk into, so every split is A/B'd before it is
believed.

## 5c. `SlotProduct.lean` refactored and upgraded (2026-10-25)

The legacy `ℚ` module landed: 1,457 → 1,748 lines, 25 → 55 declarations, `rval_aux` **692 → 91**,
`jqN_prime_not_mem_adjoin` **369 → 110**, max body 152. Interleaved A/B: wall **41.0 → 32.1 s**
(−22 %, user CPU 46.8 → 56.6 s); heartbeat peak **220k → 65k**. It is now wired (4 `spec-pin:`
lines + one `own:` row), deleted from `PORT_FILES` (522 → 521), silent, token-clean, `move_dead` 0,
both frontier targets `needed 0`; tree-wide checker **5,457 ok / 0 mismatch / 0 missing / 31 own**.

**The dedup residue was attempted and retired, with a measured reason.** Moving the six `sv`-block
declarations to one home works (silent; checker 25 ok / 0 own) but **costs the `ℚ` proof its
definitional equality**: the pinned headline states its product in the `coeffEmb` spelling, `sv`'s
body is definitionally that `ite` today, and `coeffEmb K jq = jqModC K` is propositional
(`coeffEmb_jq`), not `rfl`. Generalizing `sv` therefore forces a `Polynomial.map`/`Finset.prod`
conversion at the headline and turns a declaration that closes at **≤70k heartbeats** into one that
times out at 400k (and a genuine `Type mismatch` at 4M). Reverted. The 25 duplicate lines are the
price of keeping the `ℚ` proof definitional — `private`, inert, now documented as irreducible at
this layer.

**The API half was shared — `FunctionFieldGeneration/SlotValues.lean` (new, 198 lines, 7
declarations).** `slotValues`, `mem_slotValues`, `card_slotValues`, `prod_slotValues`,
`nodup_slotValues`, `exists_slot_descent_data` and `not_isRoot_minpoly_of_prime_deg` are generic
over `F : ℕ → ℕ → LaurentSeries K`, so they cross the two `sv` spellings; both slot-product modules
now import them (`SlotProduct` 1,748 → 1,609 lines, `SlotProductAnyField` 1,512 → 1,375). Two
adaptations keep the home *upstream* of the counting core: `card_slotValues` takes the ψ-count
identity as a hypothesis (each module passes `card_slotFilter_eq_dedekindPsi` at its three call
sites), and `nodup_slotValues` keeps taking the slot-parameter injection as a hypothesis (the `sv`
discharge stays with `sv`). The module is deliberately **tier 3** (no wire, no markers): every declaration is ours, so a wire
plus seven `own:` rows would record "ours" seven times and diff nothing. The tier-3 register lists
it as *"the port's own, no pin source. Imported by 2 port module(s)"*, and `--check` keeps that
fresh; what pins the statements is use — both slot-product modules cite all seven at specific
arguments. (The first pass did wire it with 7 `own:` rows; removed as pure bookkeeping.)

**Residue: `dedup` 11 clusters / 192 lines → 6 / 89**, all of the `sv`-instantiation layer:
`nodup_slotValues_qExpand` 32, `sv_inj_slot` 22, `sv_inj` 16, `nodup_slotValues_sv` 10,
`TS_congr'` 5, `sv_eq_TS` 4 — blocked by the same definitional reason as the `sv` block itself.

## 6. `SlotProduct.lean` is legacy: measured, and queued

The `ℚ` twin (`FunctionFieldGeneration/SlotProduct.lean`) is the next refactor
([WORKORDER-CL3](../topics/modularCurve/WORKORDER-CL3-slotproduct-refactor-and-upgrade.md)), and it
is a **legacy module**, so touching it means bringing it up to standards. Measured 2026-10-25
before any edit:

| criterion | reading |
|---|---|
| `spec-pin:` | **absent** — the module is only in the frozen registry (`old_check_stmts.py:3555`), so **its statements are not diffed at all** |
| trial wire (the two `S_` + two `Theorems` files) | **2 ok / 0 mismatch / 1 missing**; the missing row is `card_slotFilter_eq_dedekindPsi` (the port's own closed-form counting export) and needs one `own:` row |
| `dedup.py` isolated | 0 clusters, 0 removable |
| `dedup.py` over all 11 `FunctionFieldGeneration` modules | 3 clusters / 25 removable lines — `sv_inj` 16, `TS_congr'` 5–7, `sv_eq_TS` 4–6, each `private` vs `private` with `SlotProductAnyField.lean` (the deliberate duplication CL1 documents) |
| `move_dead.py` | 0 declarations, 0 lines |
| token hygiene | clean |
| build | ≈56 s elaboration, of which one single 18.9 s final type check; needs >200k heartbeats |

So the order wires it first (a 5-line safety net that makes the refactor statement-checked), then
splits the 692- and 369-line proofs mirroring CL1's decomposition, then deletes the `PORT_FILES`
line and re-reads every gate.

## 7. What is next in the `C` layer (not in scope here)

The parent cone's 19 remaining nodes / 5,664 raw: `package_of_socket` (1,003) — which imports
CL2's public `eFull` vocabulary instead of re-declaring it —
`finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket` (518),
`finrank_adjoin_jqNModC_modularFunctionFieldFullC_eq_dedekindPsi` (238), the `StarBank` group and
the `JOneES` pair. Re-measure with `frontier.py --target …` before cutting the next orders.
