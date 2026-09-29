# Topic 12, SET 3: the conditional capstone — the $`R \cong T`$ assembly

**Status: planned (not started).** Third set of T12, the driver port of
[../../studies/t-side-driver.md](../../studies/t-side-driver.md). SET 1 (the
surjection half) and SET 2 (the eigenform-extraction chain) are complete —
[TOPIC-t12-set1-surjection.md](TOPIC-t12-set1-surjection.md),
[TOPIC-t12-set2-eigenform-extraction.md](TOPIC-t12-set2-eigenform-extraction.md),
record [../../logs/t-side-port.md](../../logs/t-side-port.md) §§6–17. This set is
the capstone itself, ported **conditionally**: the patching facts are hypotheses,
so the 3,789-line patching construction does not gate it.

**Mathematics.** [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
§4. **Driver plan and why conditional.** [../../studies/t-side-driver.md](../../studies/t-side-driver.md)
§2, §4; [porting-playbook.md](../../porting-playbook.md) §7.3 (the conditional
capstone).

**Audience.** A fresh session taking SET 3. Read
[porting-playbook.md](../../porting-playbook.md) (all of it; §3.11, §5, §7.3),
then the pin file `P2M/Sol/S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean`
(145 lines) and its wrapper.

**Build discipline — read this first.** Every build is bounded and a blow-up is
quarantined, not waited on. Measured with mathlib prebuilt: a green
`lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
**errors in ~15–20 s** — it does not hang. A healthy full `lake build` of this
tree is **seconds to about a minute**.

- Run every build under a hard bound: `timeout 60 lake env lean <file>`,
  `timeout 90 lake build <module>`, `timeout 180 lake build`. **A multi-minute
  build is never acceptable.**
- **Expect ≤ 30 s.** Any single build past ~60 s is a blow-up: bisect, do not
  wait.
- **Quarantine immediately**; use `Scratch.lean` with
  `set_option maxHeartbeats 20000` and `set_option diagnostics true`.
- **Never raise `maxHeartbeats` (or `maxRecDepth`).**
- **Tell a blow-up from contention by CPU time**; never build concurrently with
  another agent.

## 0. The node, and the one substitution

**One node, 145 pin lines:**
`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`. Read the pin; its
proof has five parts:

1. `hsurj : Function.Surjective φ` — `H.surjective_of_isEquiv_baseChangeAlong`
   (**SET 1**, ported);
2. **the patching input** — `P.nonempty_patchingLevel_bot hp𝒪` then
   `L.free_and_ker_eq_span` (pin lines 61–62) — **this is what SET 4 defers**;
3. `hinj` — from the free nontrivial patched module via
   `Module.annihilator_eq_bot` (mathlib);
4. `e : D.R ≃ₐ[𝒪] T := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩` — the equality;
5. the post-isomorphism argument: apply `D.universal` at `A = 𝒪`, build
   `ψW : T →ₐ[𝒪] 𝒪`, compare Frobenius characteristic polynomials with
   `GaloisRepAdic.charpoly_baseChangeAlong` / `charpoly_eq_of_isEquiv`
   (**SET 1**) and `ValuationSubring.exists_isFrobeniusAt_rat` (**SET 1**),
   extract the eigenform with
   `HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq` (+
   `Ideal.exists_ringHom_integralClosure_ker_eq`, both **SET 2**), raise the
   level with `CuspForm.exists_isNormalizedEigenform_of_dvd` (**SET 2**), and
   finish.

**The substitution.** Replace the pin's binder
`(P : Algebra.PatchingDatum 𝒪 p r D.R M)` and the two lines that consume it with
the *output* of `Algebra.PatchingLevel.free_and_ker_eq_span` taken as
hypotheses:

```lean
{r : ℕ} (L : Algebra.PatchingLevel 𝒪 r D.R M ⊥)
(hfree : Module.Free D.R M) (hann : Module.annihilator D.R M = ⊥)
(hker : RingHom.ker L.ψ = Ideal.span (Set.range fun i : Fin r => L.φ (MvPowerSeries.X i)))
```

Keep the rest of the pin's binder list and conclusion identical, so SET 4 can
discharge the three hypotheses and recover the verbatim statement. A small
structure bundling `(L, hfree, hann, hker)` is acceptable if it reads better
(playbook §7.3), but plain hypotheses are preferred for a one-input assembly —
freeze whichever you choose, because SET 4 discharges it.

Because the statement differs from the pin's, this declaration is **own-proof**:
add it to `OWN_PROOFS` with the reason. The **verbatim**
`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum` is **not** ported here;
SET 4 adds it once the patching cluster lands. Add its wrapper to `SOURCES` now
anyway, so SET 4 needs no checker edit for it.

## 1. Layout

| pin source | port module |
|---|---|
| `S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum` (145 L) | `FLTForHuman/WeierstrassCurve/ModularityLifting.lean` |

The conclusion is about `WeierstrassCurve`, so this is its natural subject home;
it sits beside `WeierstrassCurve/Defs/Modularity.lean` (SET A of T11) and imports
`HeckeGalois.Defs.HeckeGaloisRepDatum`, `GaloisRep.Defs.DeformationRingData`,
`Patching.Defs.PatchingDatum`, `Algebra.FiniteAlgebraCharacters`,
`ModularForms.EigenformExtraction`, and the SET 1 modules. Do not re-derive any
of them.

## 2. Redundancy and reuse

Almost the whole proof is **application** of SET 1/SET 2/T10 lemmas; the only new
mathematics is the `ψW` construction and the coefficient comparison in
step 5. Concretely, reuse and do not restate:

- `CuspForm.HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong` (SET 1);
- `GaloisRepAdic.charpoly_baseChangeAlong`, `GaloisRepAdic.charpoly_eq_of_isEquiv`,
  `ValuationSubring.exists_isFrobeniusAt_rat` (SET 1);
- `CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq`,
  `Ideal.exists_ringHom_integralClosure_ker_eq`,
  `CuspForm.exists_isNormalizedEigenform_of_dvd` (SET 2);
- `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra` (T10, ported at the
  assembly's pin line 108);
- `Module.annihilator_eq_bot`, `AlgEquiv.ofBijective`, `Polynomial` coefficient
  API (mathlib).

The pin's `hχ` coefficient simplification (`coeff 1` of the charpoly comparison)
is the one piece to transcribe with care — it is a `simp only` over `coeff_*`
followed by `neg_injective`. Do not invent a new route through `Polynomial`
extensionality if the pin's coefficient read-off works.

## 3. Port order

Single module; build after the conditional statement typechecks and again after
the proof. If the `hχ` block resists, quarantine it in `Scratch.lean` at a low
cap and bisect the `simp only` set (playbook §3.5).

## 4. Wiring

- Append `Theorems/Thm_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean`
  to `SOURCES` (prepares SET 4) and
  `FLTForHuman/WeierstrassCurve/ModularityLifting.lean` to `PORT_FILES`.
- Add the conditional capstone's name to `OWN_PROOFS` with the reason ("the
  patching facts are hypotheses; the verbatim statement lands in SET 4").
- Extend `spec/TsideSet2Consumer.lean` or add `spec/TsideSet3Consumer.lean` with a
  real composition: state the conditional capstone's *hypotheses* from a
  `GaloisRep.DeformationRingData`, a `CuspForm.HeckeGaloisRepDatum`, a
  `GaloisRepAdic` and a `PatchingLevel`, and invoke the capstone to obtain
  `W.IsModularModelOfLevel`. It must import from two different new modules.

## 5. Verification gates

1. `cd lean && timeout 180 lake build` — green, no `sorry`/`admit`.
2. `python3 spec/check_flt_statements.py` — **0 mismatched, 0 missing**; the
   identical count is unchanged by this set (the capstone is `OWN_PROOFS`), the
   exempted count rises by one. Confirm no other declaration moved.
3. `#print axioms` on the conditional capstone — only
   `propext, Classical.choice, Quot.sound`, i.e. the architecture is checked,
   not asserted (playbook §7.3).
4. The consumer zone builds with 0 errors.
5. Record a SET-3 section in `logs/t-side-port.md` and update `README.md`.

## 6. Risks

- **`hχ` and the `Polynomial` coefficient read-off** are the delicate part; the
  pin's `simp only` set is the guide.
- **Unused patching/`hp𝒪` binders.** If you keep `hp𝒪` or
  `[Finite (ResidueField 𝒪)]` from the pin's signature because SET 4 will need
  them, no linter objects; but do not keep `P : Algebra.PatchingDatum` — its only
  use is the deferred construction.
- **The `own-proof` statement must not accidentally redefine a pinned name.** The
  conditional name must be new (e.g. `…_of_patchingLevel` or `…_of_free`), so the
  verbatim `…_of_patchingDatum` remains free for SET 4.
- **Do not raise `maxHeartbeats`; do not build concurrently.**
- **Do not touch** T11, the Hecke port modules, WeightOne, the FFG modules,
  `studies/`, or the SET 1/2 modules except to add the consumer zone.

## 7. Pointers

- [../../studies/t-side-driver.md](../../studies/t-side-driver.md) §2, §4 — the
  conditional-capstone split and the SET-4 deferral.
- [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
  §4 (the Hecke–Galois datum) and §5 (patching levels).
- [TOPIC-t12-set1-surjection.md](TOPIC-t12-set1-surjection.md),
  [TOPIC-t12-set2-eigenform-extraction.md](TOPIC-t12-set2-eigenform-extraction.md)
  — the ported lemmas this capstone applies, and the format this file follows.
- [../../logs/t-side-port.md](../../logs/t-side-port.md) §17 — SET 2's hand-off.
- [porting-playbook.md](../../porting-playbook.md) §7.3 — keep the capstone
  conditional and keep its input structure frozen.
