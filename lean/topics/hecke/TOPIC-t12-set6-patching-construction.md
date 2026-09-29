# Topic 12, SET 6: the patching construction

**Status: planned (not started).** Sixth set of T12, the driver port of
[../../studies/t-side-driver.md](../../studies/t-side-driver.md). SETs 1–5 are
complete; the record is [../../logs/t-side-port.md](../../logs/t-side-port.md)
§§6–36.

This set ports the one large node that makes the R≅T assembly unconditional:
`Algebra.PatchingDatum.nonempty_patchingLevel_bot` — the Taylor–Wiles patching
construction, 3,789 pin lines (3,192 non-blank, 129 of them `p2m_*` boilerplate to
drop). It is **one public theorem plus ~3,000 lines of private scaffolding**.

This is the largest set of the effort and the only one expected to need more than
one session. §3 gives the milestone order and the **green-prefix** rule: if the
whole construction cannot be finished, stop with the module compiling on the
scaffolding ported so far and report where. SET 7 (the 31-line abstract patching
exit and the 145-line **verbatim** unconditional assembly) follows.

**Audience.** A fresh session. Read [porting-playbook.md](../../porting-playbook.md)
(all of it; §3.11, §5, §7.1, §7.4), then the pin file
`P2M/Sol/S_Algebra_PatchingDatum_nonempty_patchingLevel_bot.lean` and its
wrapper, and the SET 5 record (§§31–36) for the three facts this consumes.

**Build discipline — read this first.** Every build is bounded and a blow-up is
quarantined, not waited on. Measured with mathlib prebuilt: a green
`lake env lean <module>` of this size is **~4–10 s**, `lake build <module>` with
deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
**errors in ~15–20 s** — it does not hang. A healthy full `lake build` of this
tree is **seconds to about a minute**.

- Run every build under a hard bound: `timeout 60 lake env lean <file>`,
  `timeout 90 lake build <module>`, `timeout 180 lake build`. **A multi-minute
  build is never acceptable.**
- **Expect ≤ 30 s.** Any single build past ~60 s is a blow-up: bisect it.
- **Quarantine immediately**; use `Scratch.lean` with
  `set_option maxHeartbeats 20000` and `set_option diagnostics true`.
- **Never raise `maxHeartbeats` (or `maxRecDepth`).** The pin raises them in
  three places; **do not** copy those.
- **Tell a blow-up from contention by CPU time**; never build concurrently.

## 0. The node

Public statement, verbatim from the `Theorems/` wrapper:

```lean
theorem Algebra.PatchingDatum.nonempty_patchingLevel_bot
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ℓ r : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R] {M : Type} [AddCommGroup M] [Module R M]
    (P : Algebra.PatchingDatum 𝒪 ℓ r R M) :
    Nonempty (Algebra.PatchingLevel 𝒪 r R M ⊥)
```

The pin's `solution` (lines 3779–3787) is six lines: split on
`subsingleton_or_nontrivial M`, use `FrobDictPC.Limit.trivialLevel` in the
subsingleton case and `FrobDictPC.Limit.patchedLevel` in the nontrivial case
under `haveI : Fact ((ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)`. Everything else in
the file builds those two definitions.

## 1. Layout

| pin source | port module |
|---|---|
| `S_Algebra_PatchingDatum_nonempty_patchingLevel_bot` (3,789 L) | `FLTForHuman/Patching/PatchingConstruction.lean` |

The construction is patching-specific, so it lives under `Patching/`; the
scaffolding stays **private** in that module (the pin makes it private, and
playbook §7.1/§9 keeps proof-local adaptations private). Do **not** promote the
scaffolding into `Algebra/`/`Topology/` speculatively — but if a scaffolding
lemma is clearly generic *and* already has a natural home with a second consumer,
flag it in the log rather than promoting it in this set.

## 2. What the pin contains, and the known drift

The pin's structure, in order (section markers in the source):

- `PCPortSpine0`–`PCPortSpine8` (lines 56–~1500) — topology, Mittag–Leffler,
  `TwoSidedIdeal`, `WellFoundedGT/LT`, local-ring topology, `Submodule`,
  `Pi.liftQuotientₗ`, the type-cardinality carriers (`ModuleTypeCardLT`,
  `AlgebraTypeCardLT`, `TopologicalModuleTypeCardLT`, …), and the functorial
  machinery. Pure generic scaffolding, private.
- `UltraProduct`/`PatchingAlgebra`/`PatchingModule`/`IsPatchingSystem`
  (~1500–2500) — the patching carriers.
- The core construction (~2500–3260): `FrobDictPC.{Coeff,Input,Bφ,viaφ,Base}`,
  `Levels`, `Output`.
- `FrobDictPC.Limit` (3263–3775): `ConstEquiv`, `LimHom`, `LimMap`, `Semilinear`,
  `Concrete` (`PiInf`, `PsiInf`), ending in `patchedLevelMain` (3719) and
  `trivialLevel` (3757).
- `solution` (3779).

Known v4.34 drift, from SET 5's experience and this file:

1. **`MvPowerSeries.isNoetherianRing_of_finite` is used by name four times**
   (lines 2573, 2861, 3558, 3574). That name does not exist in the port — mathlib
   has the **instance** `MvPowerSeries.instIsNoetherianRing`
   (`Mathlib/RingTheory/MvPowerSeries/Equiv.lean:225`). Replace each with
   `inferInstance` (the two `(… : IsNoetherianRing …)` ascriptions become
   `(inferInstance : IsNoetherianRing (MvPowerSeries (Fin r) 𝒪))`; the two
   `haveI := …` become `haveI := inferInstance`). This needs
   `[IsNoetherianRing 𝒪]` in scope, which the statement's `IsDiscreteValuationRing`
   provides. **Do not port the wrapper or add it to `SOURCES`.**
2. `MvPowerSeries` is a non-reducible `def`: an existential witness
   `⟨fun m => c m, …⟩` does not elaborate — name the witness with `let` first
   (SET 5 deviation 1).
3. `rw [smodEq_pow_smul_top_iff]` fails at an `MvPowerSeries`-valued goal;
   use the explicit `.mpr` application (SET 5 deviation 2).
4. `haveI` in a `Prop` goal trips `linter.style.haveILetI`; prefer `have`
   (SET 5 deviation 3).
5. `if_pos/if_neg` → `ite_eq_left/ite_eq_right`; `dif_pos/dif_neg` →
   `dite_eq_left/dite_eq_right`; `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`;
   `Ideal.eq_bot_of_comap_eq_bot`/`mem_comap` → `eq_bot_of_under_eq_bot`/`mem_under`
   (with an explicit `change`); `Module.Finite.of_restrict_scalars_finite` →
   `of_restrictScalars_finite`; `TensorProduct.induction_on` →
   `TensorProduct.inductionOn` (no `zero` case);
   `IsArtinianRing.setOf_isMaximal_finite` → `setOf_pred` form.

The three SET-5 facts it consumes are public and checker-verified:
`MvPowerSeries.isAdicComplete_maximalIdeal` (2583, 2866, 3576),
`MvPowerSeries.residue_comp_C_surjective` (2597),
`MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero` (2675), and
`IsAdicComplete.map_of_surjective` (3581). Do not re-derive them.

**What to drop.** All `p2m_open`/`p2m_export`/`p2m_reactivate`/`p2m_exact_reverting`
lines (129 occurrences) — they exist only for the pin's tooling. The pin's blanket
`import Mathlib` becomes the specific mathlib modules actually used; the pin's
import list is already fairly specific (46 mathlib modules, mostly topology,
category theory and adic completion) — keep the ones the transcribed proofs need
and no more (playbook §7.2).

## 3. Strategy: milestones and the green-prefix rule

Port **in pin order**, building after each section:

1. `PCPortSpine0`–`2` (topology, Mittag–Leffler, `TwoSidedIdeal`, local-ring
   topology). Build.
2. `PCPortSpine3`–`8` and the type-cardinality/functorial carriers. Build.
3. The patching carriers (`UltraProduct`, `PatchingAlgebra`, `PatchingModule`,
   `IsPatchingSystem`). Build.
4. The `FrobDictPC` construction and `Limit`. Build.
5. `solution`, then wire the public theorem into the checker. Build.

**The green-prefix rule.** This set may not fit one session. Work on the single
module `PatchingConstruction.lean` and keep it compiling at every step: the
scaffolding sections are independent private declarations, so a partially ported
module **does** build (it simply has no public theorem yet). If you must stop,
stop after a section that builds, say exactly which pin section was the last one
ported, and leave the wrapper **out** of `SOURCES`/the public theorem unwritten so
the checker stays clean. The next session continues the same file at the next
section.

Quarantine a single scaffolding lemma that resists (comment it out, bisect at a
low cap) rather than blocking the whole set, and list every quarantine in the
report.

## 4. Wiring

- Add `Theorems/Thm_Algebra_PatchingDatum_nonempty_patchingLevel_bot.lean` to
  `SOURCES` and `FLTForHuman/Patching/PatchingConstruction.lean` to `PORT_FILES`
  **only once the public theorem is written**; while the module is a partial
  (scaffolding-only) port, leave both out so `0 missing` stays meaningful.
- The scaffolding is private, so no `OWN_PROOFS` entries are expected for it.
- Consumer: once the public theorem lands, add a zone that builds the
  `Algebra.PatchingDatum` inputs and applies `nonempty_patchingLevel_bot`,
  composing with `Algebra.PatchingLevel.free_and_ker_eq_span` (SET 4) — a real
  cross-module composition.

## 5. Verification gates

1. `cd lean && timeout 180 lake build` — green, no `sorry`/`admit`.
2. `python3 spec/check_flt_statements.py` — after the public theorem lands, it is
   identical to the wrapper, **0 mismatched, 0 missing**; mutate one token and
   confirm `1 mismatched`, then revert.
3. `#print axioms` on `Algebra.PatchingDatum.nonempty_patchingLevel_bot` — only
   `propext, Classical.choice, Quot.sound`.
4. Record a SET-6 section in `logs/t-side-port.md` (including any partial state)
   and update `README.md`.

## 6. Risks

- **Size.** 3,789 lines is ~2.5× the largest set so far. Use §3's milestones and
  the green-prefix rule; do not attempt to transcribe the whole file before the
  first build.
- **The `PCPortSpine` scaffolding is topology- and category-theory-heavy**
  (profinite spaces, ultrafilters, cofiltered systems, `IsModuleTopology`,
  `ContinuousFunctionalCalculus`). Expect `#check @name` probing (playbook §3.9).
- **The pin raises `maxHeartbeats`/`synthInstance.maxHeartbeats` in three places.**
  Do not copy them; if a declaration needs more than the default it is a blow-up —
  quarantine and restate.
- **`IsLocalRing` namespacing drift** (SET 5 friction: `exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`,
  `map_maximalIdeal_le` live under `IsLocalRing`).
- **Do not touch** T11, the Hecke port modules, WeightOne, the FFG modules,
  `studies/`, or the SET 1–5 modules.

## 7. Pointers

- [../../logs/t-side-port.md](../../logs/t-side-port.md) §§31–36 — SET 5's
  friction and the four name-drift points.
- [TOPIC-t12-set5-power-series-algebra.md](TOPIC-t12-set5-power-series-algebra.md)
  — the facts this consumes, and the format this file follows.
- [TOPIC-t12-set3-conditional-capstone.md](TOPIC-t12-set3-conditional-capstone.md)
  §0 — the three hypotheses SET 7 discharges with this construction's output.
- [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
  §5 — patching levels and data.
- [porting-playbook.md](../../porting-playbook.md) §3.11, §5, §7.1/§7.4.
