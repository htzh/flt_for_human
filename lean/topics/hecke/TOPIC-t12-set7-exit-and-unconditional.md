# Topic 12, SET 7: the patching exit and the unconditional $`R \cong T`$ assembly

**Status: planned (not started).** Final set of T12, the driver port of
[../../studies/t-side-driver.md](../../studies/t-side-driver.md). SETs 1–6 are
complete — the record is [../../logs/t-side-port.md](../../logs/t-side-port.md)
§§6–37. SET 6 landed the 3,761-line patching construction and its public theorem.

This set closes the loop: the **abstract patching exit** (31 lines) and the
**verbatim unconditional** `WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`
(145 lines), which discharges the three hypotheses SET 3 froze. Two nodes / 176
pin lines — small, and the payoff of the whole driver.

**Audience.** A fresh session. Read [porting-playbook.md](../../porting-playbook.md)
(§3.11, §5, §7.4), then the two pin files of §0 and their wrappers, and
`FLTForHuman/WeierstrassCurve/ModularityLifting.lean` (SET 3's conditional form).

**Build discipline — read this first.** Every build is bounded and a blow-up is
quarantined, not waited on. Measured with mathlib prebuilt: a green
`lake env lean <module>` of this size is **~4 s once its dependencies' oleans
exist**, and a full `lake build` of this tree is **seconds to about a minute**.

- Run every build under a hard bound: `timeout 60 lake env lean <file>`,
  `timeout 90 lake build <module>`, `timeout 180 lake build`. **A multi-minute
  build is never acceptable.**
- **Expect ≤ 30 s**, with the one caveat below.
- **Quarantine immediately**; use `Scratch.lean` with
  `set_option maxHeartbeats 20000` and `set_option diagnostics true`.
- **Never raise `maxHeartbeats` (or `maxRecDepth`).**
- **Tell a blow-up from contention by CPU time**; never build concurrently.

> **The one caveat: SET 6's construction is intrinsically slow.** Elaborating
> `FLTForHuman/Patching/PatchingConstruction.lean` from source takes **~50 s**
> (84 s user CPU across ~370 private declarations). That is cumulative, not a
> blow-up. Both modules here **import** it, so run `timeout 120 lake build
> FLTForHuman.Patching.PatchingConstruction` once to build its olean first; after
> that, `lake env lean` on the new modules is seconds. Never re-elaborate the
> construction from source unless you changed it.

## 0. The two nodes

Statements verbatim from the `Theorems/` wrappers.

```lean
theorem Algebra.PatchingDatum.bijective_and_free_of_surjective
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ℓ r : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (P : Algebra.PatchingDatum 𝒪 ℓ r R M)
    {T : Type} [CommRing T] [Algebra 𝒪 T] [Module T M]
    (RtoT : R →ₐ[𝒪] T) (hsurj : Function.Surjective RtoT)
    (hcompat : ∀ (x : R) (m : M), RtoT x • m = x • m) :
    Function.Bijective RtoT ∧ Module.Free R M ∧ Module.Free T M ∧
      Module.annihilator R M = ⊥ ∧
      ∃ f : Fin r → MvPowerSeries (Fin r) 𝒪,
        Nonempty ((MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)

theorem WeierstrassCurve.isModularModelOfLevel_of_patchingDatum
    (p : ℕ) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    [CharZero 𝒪] (hp𝒪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    {N : ℕ} [NeZero N] {S : Finset ℕ} (hSprime : ∀ q ∈ S, q.Prime)
    (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (hN : CuspForm.HasIntegralStructure N 2)
    {θ : CuspForm.HeckeGaloisRepDatum …} (H : …) (φ : D.R →ₐ[𝒪] T) (hφ : …) (hφρ : …)
    {M : Type} [AddCommGroup M] [Module D.R M] [Module T M] [Nontrivial M]
    (hcompat : ∀ (x : D.R) (m : M), φ x • m = x • m)
    {r : ℕ} (P : Algebra.PatchingDatum 𝒪 p r D.R M)
    (ρW : GaloisRepAdic 𝒪) (h𝒟W : 𝒟 ρW) (hWres : …) (hWfrob : …) :
    W.IsModularModelOfLevel (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q)
```

**The exit** is the pin's four-line proof: `P.nonempty_patchingLevel_bot hℓ`,
`L.free_and_ker_eq_span`, `bijective_of_surjective_of_smul_eq` (**SET 4**),
`Module.Free.of_surjective_of_smul_eq` (**SET 4**), and the quotient presentation
via `Ideal.quotientEquivAlgOfEq`/`quotientKerAlgEquivOfSurjective`. Every input is
public and ported. Its home is `FLTForHuman/Patching/Exit.lean`.

**The verbatim assembly** is the pin's 145-line proof; SET 3 already ported it
**conditionally** as `WeierstrassCurve.isModularModelOfLevel_of_patchingLevel` in
`FLTForHuman/WeierstrassCurve/ModularityLifting.lean`, with the frozen inputs
`{r} (L : Algebra.PatchingLevel 𝒪 r D.R M ⊥) (hfree) (hann) (hker)` in place of
`(P : Algebra.PatchingDatum 𝒪 p r D.R M)`. Add the verbatim statement to that
**same module** and discharge:

```lean
obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hp𝒪
obtain ⟨hfree, hann, hker⟩ := L.free_and_ker_eq_span
exact WeierstrassCurve.isModularModelOfLevel_of_patchingLevel … L hfree hann hker …
```

The wrapper `Thm_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean` is
**already in `SOURCES`** and `ModularityLifting.lean` is **already in
`PORT_FILES`** (SET 3), so the verbatim theorem needs no checker edit.

## 1. Layout

| pin source | port module |
|---|---|
| `S_Algebra_PatchingDatum_bijective_and_free_of_surjective` (31 L) | `FLTForHuman/Patching/Exit.lean` |
| `S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum` (145 L) | **extend** `FLTForHuman/WeierstrassCurve/ModularityLifting.lean` |

`Exit.lean` imports `FLTForHuman.Patching.PatchingConstruction` (SET 6),
`FLTForHuman.Patching.LevelDescent` (SET 4) and
`FLTForHuman.Algebra.FaithfulFreeness` (SET 4). `ModularityLifting.lean` gains an
import of `FLTForHuman.Patching.PatchingConstruction`.

## 2. Redundancy and reuse

Nothing new to prove. Both nodes are assemblies of ported lemmas:

- the exit: `nonempty_patchingLevel_bot` (SET 6), `free_and_ker_eq_span` (SET 4),
  `RingHom.bijective_of_surjective_of_smul_eq` and
  `Module.Free.of_surjective_of_smul_eq` (SET 4);
- the verbatim assembly: the conditional theorem (SET 3) plus
  `nonempty_patchingLevel_bot` (SET 6) and `free_and_ker_eq_span` (SET 4).

Do not restate the conditional's argument. The verbatim theorem should be a
short application, not a copy.

## 3. Wiring

- Add `Theorems/Thm_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean`
  to `SOURCES` and `FLTForHuman/Patching/Exit.lean` to `PORT_FILES`. The
  assembly's wrapper and module are already wired.
- The conditional theorem's `OWN_PROOFS` entry stays (it is not the pinned name);
  the verbatim theorem is verified, so `OWN_PROOFS` is unchanged.
- Consumer: add a zone (new `spec/TsideSet7Consumer.lean` or extend the newest)
  with the end-to-end composition — build the `PatchingDatum`, `HeckeGaloisRepDatum`
  and `DeformationRingData` inputs, apply the verbatim assembly to get
  `W.IsModularModelOfLevel …`, and separately apply the exit. It must import from
  both new/changed modules.

## 4. Verification gates

1. `cd lean && timeout 180 lake build` — green, no `sorry`/`admit`.
2. `python3 spec/check_flt_statements.py` — the **verbatim** assembly and the exit
   both identical to their wrappers, **0 mismatched, 0 missing**; the exempted
   count is unchanged at 28 (the conditional stays an own-proof). Mutate one token
   of each and confirm `1 mismatched`, then revert.
3. `#print axioms` on both new public theorems — only
   `propext, Classical.choice, Quot.sound`. **This is the deliverable**: the
   unconditional R≅T assembly, axiom-clean, with the patching construction on its
   import path.
4. The consumer zone builds with 0 errors.
5. Record a SET-7 section in `logs/t-side-port.md`, update `README.md`, and add
   the closing entry to
   [../../studies/t-side-driver.md](../../studies/t-side-driver.md) noting that
   the driver is complete.

## 5. Risks

- **Import weight / build time.** Both modules import the 3,761-line
  `PatchingConstruction`; build its olean once (§caveat) and do not edit it.
- **The verbatim assembly's binders must match the wrapper exactly** — it is a
  *second* declaration of the same name in the same namespace as the wrapper, so
  a typo in a binder shows up as `1 mismatched`, not a build error.
- **The conditional and the verbatim theorem share the module**; keep the
  conditional's name unchanged (SET 4/6 consumers reference it) and do not
  `OWN_PROOFS`-exempt the verbatim one.
- **Do not raise `maxHeartbeats`; do not build concurrently.**
- **Do not touch** T11, the Hecke port modules, WeightOne, the FFG modules,
  `studies/`, or the SET 1–6 modules except the additive extension of
  `ModularityLifting.lean` and the consumer.

## 6. Pointers

- [TOPIC-t12-set3-conditional-capstone.md](TOPIC-t12-set3-conditional-capstone.md)
  §0 — the frozen hypotheses this set discharges.
- [TOPIC-t12-set6-patching-construction.md](TOPIC-t12-set6-patching-construction.md)
  — the construction and its build-time note.
- [../../logs/t-side-port.md](../../logs/t-side-port.md) §37 — SET 6's hand-off.
- [../../studies/t-side-driver.md](../../studies/t-side-driver.md) — the driver
  plan; its §1 records where the unconditional assembly sits on the critical path.
- [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
  §5 — patching levels and data.
