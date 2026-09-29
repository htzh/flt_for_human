# Topic 12, SET 4: patching descent and freeness

**Status: planned (not started).** Fourth set of T12, the driver port of
[../../studies/t-side-driver.md](../../studies/t-side-driver.md). SETs 1–3 are
complete — [TOPIC-t12-set1-surjection.md](TOPIC-t12-set1-surjection.md),
[TOPIC-t12-set2-eigenform-extraction.md](TOPIC-t12-set2-eigenform-extraction.md),
[TOPIC-t12-set3-conditional-capstone.md](TOPIC-t12-set3-conditional-capstone.md),
record [../../logs/t-side-port.md](../../logs/t-side-port.md) §§6–23.

This set ports the **descent and freeness engine** of the patching exit: the two
`smul_eq` lemmas, the freeness-from-a-regular-sequence lemma, and
`Algebra.PatchingLevel.free_and_ker_eq_span` — the lemma that turns an
`Algebra.PatchingLevel 𝒪 r R M ⊥` into the three hypotheses SET 3 froze
(`Module.Free R M`, zero annihilator, the kernel description).

> **Correction (from execution, log §30).** This file originally claimed the four
> nodes were independent of SET 5. That was false: the pin's
> `free_and_ker_eq_span` imports and uses four `MvPowerSeries.*` lemmas, so the
> executed set also ported three of them (publicly, in the new
> `Algebra/MvPowerSeriesRegular.lean`) and reused mathlib's
> `MvPowerSeries.instIsNoetherianRing` for the fourth. SET 5 was re-scoped
> accordingly — see [TOPIC-t12-set5-power-series-algebra.md](TOPIC-t12-set5-power-series-algebra.md).

The deferred split, recorded so the plan stays visible:
**SET 4 (this)** descent + freeness · **SET 5** the power-series patching algebra
(the six `MvPowerSeries.*` lemmas and `IsAdicComplete.map_of_surjective`) ·
**SET 6** `Algebra.PatchingDatum.nonempty_patchingLevel_bot` (3,789 lines) + the
abstract patching exit + the **verbatim** unconditional
`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`.

**Audience.** A fresh session. Read [porting-playbook.md](../../porting-playbook.md)
(all of it; §2 dedup, §3.11, §5, §7.1/§9), then the four pin files of §0 and
their `Theorems/` wrappers.

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

Four nodes / 443 pin `S_` lines, all unported. Statements verbatim from the
`Theorems/` wrappers.

```lean
theorem RingHom.bijective_of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T]
    [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] [Nontrivial N]
    (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) :
    Function.Bijective g

theorem Module.Free.of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T]
    [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N]
    (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) :
    Module.Free T N

theorem Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (xs : List R) (hxs : RingTheory.Sequence.IsRegular R xs)
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal R)
    (s : List R) (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M s) (hlen : s.length = xs.length)
    (hfl : IsFiniteLength R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M))) :
    Module.Free R M

theorem Algebra.PatchingLevel.free_and_ker_eq_span
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (L : Algebra.PatchingLevel 𝒪 r R M ⊥) :
    Module.Free R M ∧ Module.annihilator R M = ⊥ ∧
      RingHom.ker L.ψ = Ideal.span (Set.range fun i : Fin r => L.φ (MvPowerSeries.X i))
```

## 1. Layout — natural subject homes

The three generic facts go under `FLTForHuman/Algebra/`; only the patching-level
statement goes under `FLTForHuman/Patching/`.

| pin source | port module | why |
|---|---|---|
| `S_RingHom_bijective_of_surjective_of_smul_eq` (13 L) | `FLTForHuman/Algebra/FaithfulFreeness.lean` | generic: surjection compatible with a faithful free action is bijective |
| `S_Module_Free_of_surjective_of_smul_eq` (22 L) | same module | same mechanism, freeness on the target |
| `S_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal` (98 L) | `FLTForHuman/Algebra/RegularSequenceFreeness.lean` | generic: freeness from a full-length weakly regular sequence |
| `S_Algebra_PatchingLevel_free_and_ker_eq_span` (310 L) | `FLTForHuman/Patching/LevelDescent.lean` | the patching level's descent at zero relation ideal; `Patching/` already holds `Defs/PatchingDatum.lean` |

Import T11's `FLTForHuman.Patching.Defs.PatchingDatum` for
`Algebra.PatchingLevel` and its fields. Do not redefine anything.

## 2. Redundancy to reduce

- **`RingHom.bijective_of_surjective_of_smul_eq` and
  `Module.Free.of_surjective_of_smul_eq` prove the same bijectivity twice.** The
  pin's `S_Module_Free_of_surjective_of_smul_eq` carries a private
  `FrobChareqDock.bijective_aux` (lines 7–16) that is **byte-identical** to the
  `RingHom` file's `solution` (lines 7–13). Prove bijectivity **once**
  (`RingHom.bijective_of_surjective_of_smul_eq`) and derive `Module.Free T N`
  from it, as the pin's own `solution` already does
  (`Module.Free.of_basis … (RingEquiv.ofBijective g …)`). Do not port the
  duplicate `bijective_aux`.
- **The `PDescent` helper block in `free_and_ker_eq_span`** (`I`, `I_le_ker`,
  `ker_π_iff`, `theta`, `theta_apply`, `theta_smul`, `theta_injective`,
  `theta_bijective`, `thetaEquiv`, `span_range_b`, `finite_N`, …) is private and
  used once; keep it `private` and do not promote anything the public statement
  does not need.
- **Check `Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal`'s
  `OnePrime` block** (`le_zero_of_add_natCast_le`, `hasProjectiveDimensionLT_of_isFiniteLength`,
  `free_of_hasProjectiveDimensionLT_one`) against mathlib: it is generic
  projective-dimension/finite-length material, and mathlib may already have part
  of it. `#check` before porting; if mathlib has it, rewrite the `solution` in
  terms of mathlib's lemma and record the saving (playbook §2, §5.6).

## 3. Port order (build after every module)

1. `Algebra/FaithfulFreeness.lean` — `RingHom.bijective_of_surjective_of_smul_eq`,
   then `Module.Free.of_surjective_of_smul_eq` using it. This is the engine SET 6's
   abstract patching exit consumes.
2. `Algebra/RegularSequenceFreeness.lean` — the freeness-from-a-regular-sequence
   lemma.
3. `Patching/LevelDescent.lean` — `Algebra.PatchingLevel.free_and_ker_eq_span`,
   with the private `PDescent` block.

## 4. Wiring

- Append the four `Theorems/Thm_*` wrappers of §0 to `SOURCES`; append the three
  new port modules to `PORT_FILES`.
- No new `OWN_PROOFS` entry is expected — all four statements are verbatim. If a
  mathlib reuse in §2 changes a declaration's shape, note it in the log rather
  than exempting silently.
- Add a SET-4 zone to `spec/TsideSet3Consumer.lean` or a new
  `spec/TsideSet4Consumer.lean` with a **real cross-module composition**: build
  an `Algebra.PatchingLevel`, apply
  `Algebra.PatchingLevel.free_and_ker_eq_span`, and use
  `RingHom.bijective_of_surjective_of_smul_eq` on the resulting free module. It
  must import from two different new modules.

## 5. Verification gates

1. `cd lean && timeout 180 lake build` — green, no `sorry`/`admit`.
2. `python3 spec/check_flt_statements.py` — the four statements identical,
   **0 mismatched, 0 missing**; mutate one token and confirm `1 mismatched`, then
   revert.
3. `#print axioms` on `Algebra.PatchingLevel.free_and_ker_eq_span` and
   `RingHom.bijective_of_surjective_of_smul_eq` — only
   `propext, Classical.choice, Quot.sound`.
4. The consumer zone builds with 0 errors.
5. Record a SET-4 section in `logs/t-side-port.md` and update `README.md`.

## 6. Risks

- **`free_and_ker_eq_span` is 310 lines of finite-length/Nakayama machinery**
  (regular sequences, Artinian modules, tensor products, DVRs). It is the one
  substantive file; bisect if a build blows up. The pin's `free_M` helper is
  load-bearing for `Module.Free R M`; keep its structure.
- **`IsFiniteLength` / projective-dimension API drift** in the regular-sequence
  file; probe with `#check @name`.
- **Do not raise `maxHeartbeats`; do not build concurrently.**
- **Do not touch** T11, the Hecke port modules, WeightOne, the FFG modules,
  `studies/`, or the SET 1–3 modules except to add the consumer zone.

## 7. Pointers

- [../../studies/t-side-driver.md](../../studies/t-side-driver.md) §2, §4 — the
  patching-cluster split (SET 4/5/6) and the estimate.
- [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
  §5 — patching levels and data.
- [TOPIC-t12-set3-conditional-capstone.md](TOPIC-t12-set3-conditional-capstone.md)
  §0 — the frozen three hypotheses this set's `free_and_ker_eq_span` produces,
  and the format this file follows.
- [../../logs/t-side-port.md](../../logs/t-side-port.md) §23 — SET 3's hand-off to
  the patching cluster.
- [porting-playbook.md](../../porting-playbook.md) §2 (dedup at the source),
  §3.11 (build discipline), §7.3 (frozen inputs).
