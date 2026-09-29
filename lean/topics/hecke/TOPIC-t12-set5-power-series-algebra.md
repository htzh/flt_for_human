# Topic 12, SET 5: the power-series patching algebra

**Status: planned (not started).** Fifth set of T12, the driver port of
[../../studies/t-side-driver.md](../../studies/t-side-driver.md). SETs 1–4 are
complete; the record is [../../logs/t-side-port.md](../../logs/t-side-port.md)
§§6–30.

**Re-scoped from SET 4's deviation.** The original plan put six
`MvPowerSeries.*` lemmas in SET 5. SET 4 discovered that
`Algebra.PatchingLevel.free_and_ker_eq_span` *does* consume four of them (the
work order's "self-contained" claim was wrong — see the SET 4 log §30), so
SET 4 already ported three:

- `MvPowerSeries.isRegular_C_cons_X`,
  `MvPowerSeries.ofList_C_cons_X_eq_maximalIdeal`,
  `MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero` — public and checker-verified in
  `FLTForHuman/Algebra/MvPowerSeriesRegular.lean` (with the pin's duplicated
  `vanishIdeal` engine written **once**);
- `MvPowerSeries.isNoetherianRing_of_finite` — now a mathlib **instance**
  (`MvPowerSeries.instIsNoetherianRing`, `Mathlib/RingTheory/MvPowerSeries/Equiv.lean`),
  so it is not ported; the descent calls `inferInstance`.

This set ports the **remaining three**: `isAdicComplete_maximalIdeal`,
`residue_comp_C_surjective` and `IsAdicComplete.map_of_surjective` — 434 pin
lines. All three are consumed by SET 6's
`Algebra.PatchingDatum.nonempty_patchingLevel_bot`.

**Audience.** A fresh session. Read [porting-playbook.md](../../porting-playbook.md)
(all of it; §2, §3.11, §5, §7.1/§9), then the three pin files of §0 and their
wrappers, and the existing `FLTForHuman/Algebra/MvPowerSeriesRegular.lean`.

**Build discipline — read this first.** Every build is bounded and a blow-up is
quarantined, not waited on. Measured with mathlib prebuilt: a green
`lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
**errors in ~15–20 s** — it does not hang. A healthy full `lake build` of this
tree is **seconds to about a minute**.

- Run every build under a hard bound: `timeout 60 lake env lean <file>`,
  `timeout 90 lake build <module>`, `timeout 180 lake build`. **A multi-minute
  build is never acceptable.**
- **Expect ≤ 30 s.** Any single build past ~60 s is a blow-up: bisect it.
- **Quarantine immediately**; use `Scratch.lean` with
  `set_option maxHeartbeats 20000` and `set_option diagnostics true`.
- **Never raise `maxHeartbeats` (or `maxRecDepth`).**
- **Tell a blow-up from contention by CPU time**; never build concurrently.

## 0. The cone

Three nodes / 434 pin `S_` lines, all unported. Statements verbatim from the
`Theorems/` wrappers.

```lean
theorem MvPowerSeries.isAdicComplete_maximalIdeal {σ : Type u} {R : Type v} [Finite σ]
    [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
    IsAdicComplete (IsLocalRing.maximalIdeal (MvPowerSeries σ R)) (MvPowerSeries σ R)

theorem MvPowerSeries.residue_comp_C_surjective {σ : Type u} {R : Type v} [CommRing R]
    [IsLocalRing R] :
    Function.Surjective (⇑(IsLocalRing.residue (MvPowerSeries σ R)) ∘
      ⇑(MvPowerSeries.C (σ := σ) (R := R)))

theorem IsAdicComplete.map_of_surjective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (f : R →+* S)
    (hf : Function.Surjective f) : IsAdicComplete (I.map f) S
```

## 1. Layout — extend, do not re-derive

| pin source | where it goes | why |
|---|---|---|
| `S_MvPowerSeries_isAdicComplete_maximalIdeal` (234 L) | **extend** `FLTForHuman/Algebra/MvPowerSeriesRegular.lean` | same subject as the three ported facts |
| `S_MvPowerSeries_residue_comp_C_surjective` (114 L) | **extend** the same module | same subject |
| `S_IsAdicComplete_map_of_surjective` (86 L) | new `FLTForHuman/Algebra/AdicCompleteMap.lean` | generic adic completion, no multivariate power series |

`MvPowerSeriesRegular.lean` already carries `vanishIdeal` and its twelve private
lemmas; the new `isAdicComplete_maximalIdeal`/`residue_comp_C_surjective` proofs
must **reuse** them and the existing `mem_pow_span_X_of_coeff_eq_zero`, not
re-derive. Add only what is genuinely new, and keep it `private` except the two
public statements.

## 2. Redundancy to reduce

The pin repeats the same helper block in all three files (and a fourth time in
`S_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero`, already deduplicated by SET 4):

- `smodEq_pow_smul_top_iff` — in `isAdicComplete_maximalIdeal` (line 17) and
  `IsAdicComplete.map_of_surjective` (line 18);
- `maximalIdeal_eq_comap` — in `isAdicComplete_maximalIdeal` (line 21) and
  `residue_comp_C_surjective` (line 16);
- `dropVar` — in `isAdicComplete_maximalIdeal` (line 27) and
  `residue_comp_C_surjective` (line 22). **Note:** `MvPowerSeriesRegular.lean`
  already has this argument *inline* inside `mem_pow_span_X_of_coeff_eq_zero`
  (around line 356). Extract it into one private named `dropVar` (plus
  `coeff_dropVar`) and use it in all three places.

Write each helper **once**. The two tiny `smodEq_pow_smul_top_iff` copies may
stay separate if the module split makes sharing awkward — it is four lines — but
state which you chose.

## 3. Port order (build after every module)

1. Extend `Algebra/MvPowerSeriesRegular.lean`: factor the inline `dropVar`, add
   the private `maximalIdeal_eq_comap`, `mem_span_X_of_constantCoeff_eq_zero`,
   `maximalIdeal_eq_map_C_sup_span_X`, the `LocalCoeff` block
   (`coeff_mem_pow_of_mem_pow`, `C_mem_pow`, `span_X_le`,
   `monomial_one_mem_pow`, `monomial_mem_pow`, …), then
   `MvPowerSeries.residue_comp_C_surjective` and
   `MvPowerSeries.isAdicComplete_maximalIdeal`.
2. New `Algebra/AdicCompleteMap.lean`: private `smodEq_pow_smul_top_iff`, then
   `IsAdicComplete.map_of_surjective` (and its private
   `isAdicComplete_map_maximalIdeal_quotient` if the pin's proof uses it).

## 4. Wiring

- Append the three `Theorems/Thm_*` wrappers of §0 to `SOURCES`. The three SET-4
  MvPowerSeries wrappers and `Thm_MvPowerSeries_isNoetherianRing_of_finite` are
  already handled/absent — **do not** add the latter.
- Add `FLTForHuman/Algebra/AdicCompleteMap.lean` to `PORT_FILES`;
  `MvPowerSeriesRegular.lean` is already listed.
- No new `OWN_PROOFS` entry is expected.
- Add a SET-5 zone to the newest consumer (or a new
  `spec/TsideSet5Consumer.lean`) with a real cross-module composition:
  instantiate `MvPowerSeries.isAdicComplete_maximalIdeal` at a DVR and feed it,
  with `MvPowerSeries.residue_comp_C_surjective`, into
  `IsAdicComplete.map_of_surjective`. It must import from two new modules.

## 5. Verification gates

1. `cd lean && timeout 180 lake build` — green, no `sorry`/`admit`.
2. `python3 spec/check_flt_statements.py` — the three statements identical,
   **0 mismatched, 0 missing**; mutate one token and confirm `1 mismatched`, then
   revert.
3. `#print axioms` on the three new statements — only
   `propext, Classical.choice, Quot.sound`.
4. The consumer zone builds with 0 errors.
5. Record a SET-5 section in `logs/t-side-port.md` and update `README.md`.

## 6. Risks

- **The `LocalCoeff` block in `isAdicComplete_maximalIdeal`** (coefficient
  membership, `monomial_mem_pow`, the `𝔐`-adic argument) is the substantive part;
  bisect if a build blows up.
- **`IsLocalRing.maximalIdeal`/`IsAdicComplete`/`IsPrecomplete` API drift** is
  likely; probe with `#check @name`.
- **Import weight.** SET 4 took the tree from 4409 to 4634 jobs by importing
  `Regular.ProjectiveDimension`/`FiniteLength`. Keep this set's imports as
  narrow as the pin's (playbook §7.2) and check the job count does not jump
  further than the three files justify.
- **Do not raise `maxHeartbeats`; do not build concurrently.**
- **Do not touch** T11, the Hecke port modules, WeightOne, the FFG modules,
  `studies/`, or the SET 1–4 modules except the additive extension of
  `MvPowerSeriesRegular.lean` and the consumer.

## 7. Pointers

- [../../logs/t-side-port.md](../../logs/t-side-port.md) §30 — SET 4's deviation
  and the re-scope this file implements.
- [TOPIC-t12-set4-patching-descent.md](TOPIC-t12-set4-patching-descent.md) — the
  module this set extends, and the format this file follows.
- [../../studies/t-side-driver.md](../../studies/t-side-driver.md) §2, §4 — the
  patching-cluster split and the SET 6 scope.
- [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
  §5 — patching levels and data.
