# Topic 12, SET 1: the surjection half of $`R = T`$

**Status: planned (not started).** First set of T12, the driver port of
[../../studies/t-side-driver.md](../../studies/t-side-driver.md) — the
$`R \cong T`$ assembly
`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`. This set ports the
**surjection half**: the existence of $`\varphi : R \twoheadrightarrow T`$ and
the four lemmas it needs. SETs 2–4 (eigenform extraction, the conditional
capstone, the deferred patching cluster) are separate work orders.

**Mathematics.** [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
§§1.4, 3.1, 4. **Driver plan and estimate.**
[../../studies/t-side-driver.md](../../studies/t-side-driver.md) §1–§4.
**Definitions this builds on.** T11 —
[TOPIC-t11-t-side-definitions.md](TOPIC-t11-t-side-definitions.md), record
[../../logs/t-side-port.md](../../logs/t-side-port.md).

**Audience.** A fresh session taking SET 1. Read
[porting-playbook.md](../../porting-playbook.md) (all of it, especially §3.11,
§4, §5, §7.1 and §9), then the seven pin files in §0 and their `Theorems/`
wrappers.

**Build discipline — read this first.** Every build is bounded and a blow-up is
quarantined, not waited on. Measured with mathlib prebuilt: a green
`lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
**errors in ~15–20 s** — it does not hang. A healthy full `lake build` of this
tree is **seconds to about a minute**.

- Run every build under a hard bound: `timeout 60 lake env lean <file>`,
  `timeout 90 lake build <module>`, `timeout 180 lake build`. **A multi-minute
  build is never acceptable, not even while experimenting** — a fifteen-minute
  bound is a bug in the work order, not a licence to wait.
- **Expect ≤ 30 s.** Any single build past ~60 s must be treated as a blow-up
  and bisected, not watched; a bound that lets a build run to 15 minutes is
  itself the failure.
- **Quarantine immediately.** On a non-return, comment the declaration out and
  bisect, or reproduce in the gitignored `Scratch.lean` with
  `set_option diagnostics true` and a low cap (`set_option maxHeartbeats 20000`).
  Do not re-run the same file hoping for a different result.
- **Never raise `maxHeartbeats` (or `maxRecDepth`).** The cap already fails in
  under 20 s; raising it turns that into an unbounded wait.
- **Tell a blow-up from contention by CPU time.** Measure with `time` (or
  `/usr/bin/time -v`): high user CPU + timeout is a real blow-up (bisect);
  ~0 CPU wall-time is lock contention with another agent's build (re-run when
  idle; never build concurrently with another agent).

## 0. The cone

Seven nodes / 610 pin `S_` lines, all unported. Statements are verbatim from the
`Theorems/` wrappers (the checker matches textually; take binders from the
wrapper).

```lean
theorem ValuationSubring.exists_integral_mul_eq_of_liesOverPrime
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime)
    (hA : A.LiesOverPrime q) (a : AlgebraicClosure ℚ) (ha : a ∈ A) :
    ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ),
      (s : AlgebraicClosure ℚ) ∉ A.nonunits ∧ a * s = x

theorem ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), A.IsFrobeniusAt φ q

theorem ValuationSubring.exists_isFrobeniusAt_rat (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ ∧
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ

theorem GaloisRepAdic.charpoly_baseChangeAlong {A : Type} [CommRing A] [IsLocalRing A]
    {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ)
    (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly ((ρ.baseChangeAlong φ hφ).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map φ

theorem GaloisRepAdic.charpoly_eq_of_isEquiv {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (h : ρ₁.IsEquiv ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly (ρ₁.ρ σ) = LinearMap.charpoly (ρ₂.ρ σ)

theorem CuspForm.HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong {N : ℕ}
    [NeZero N] {S : Set ℕ} {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type}
    [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T]
    [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T)
    (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) {R : Type} [CommRing R] [IsLocalRing R]
    [Algebra 𝒪 R] (ρR : GaloisRepAdic R) (φ : R →ₐ[𝒪] T)
    (hφ : IsLocalHom (φ : R →+* T))
    (he : (ρR.baseChangeAlong (φ : R →+* T) hφ).IsEquiv H.ρ) : Function.Surjective φ

theorem GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪)}
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) {N : ℕ} [NeZero N] {S : Set ℕ}
    {θ : CuspForm.heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪} {T : Type}
    [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T]
    [IsLocalHom (algebraMap 𝒪 T)] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T)
    (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) (h𝒟 : 𝒟 H.ρ)
    (hres : H.ρ.residual.IsEquiv
      (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 T)))) :
    ∃ φ : D.R →ₐ[𝒪] T, Function.Surjective φ ∧
      ∃ hφ : IsLocalHom (φ : D.R →+* T),
        (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ
```

## 1. Layout — natural subject homes

The user's rule for this port: **generic definitions and theorems go to their
natural subject home, not under a T-side directory.** Concretely:

| pin source | port module | why there |
|---|---|---|
| `S_GaloisRepAdic_charpoly_baseChangeAlong` (9 L) | `FLTForHuman/GaloisRep/AdicCharpoly.lean` | charpoly functoriality of adic Galois representations — Galois-rep vocabulary |
| `S_GaloisRepAdic_charpoly_eq_of_isEquiv` (13 L) | same module | same |
| `S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime` (184 L) | `FLTForHuman/NumberTheory/ValuationAtPlace.lean` | number theory: places of $`\overline{\mathbb{Q}}`$, $`\mathcal{O}_F`$, Dedekind domains |
| `S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime` (314 L) | `FLTForHuman/NumberTheory/FrobeniusAtPlace.lean` | same (existence of Frobenius at a place) |
| `S_ValuationSubring_exists_isFrobeniusAt_rat` (30 L) | same module | a corollary of the above |
| `S_CuspForm_HeckeGaloisRepDatum_surjective_of_isEquiv_baseChangeAlong` (51 L) | `FLTForHuman/HeckeGalois/Surjective.lean` | the $`R \to T`$ interface: Hecke side generating $`T`$ |
| `S_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum` (9 L) | same module | the $`R \twoheadrightarrow T`$ map, the T12 driver's first half |

Do **not** reimplement any T11 declaration. Import
`FLTForHuman.GaloisRep.Defs.Adic` (for `GaloisRepAdic`, `IsEquiv`,
`baseChangeAlong`), `FLTForHuman.GaloisRep.Defs.FrobeniusTrace` (for
`ValuationSubring.IsFrobeniusAt`), `FLTForHuman.GaloisRep.Defs.Ramification`
(for `LiesOverPrime`), `FLTForHuman.GaloisRep.Defs.DeformationRingData`,
`FLTForHuman.HeckeGalois.Defs.HeckeGaloisRepDatum`, and the ported
`CuspForm.heckeAlgebra` layer.

## 2. Redundancy to reduce

- **`IsIntegral ℤ b → b ∈ A` is proved twice in the pin.** In
  `…exists_integral_mul_eq…` it is the local `int_mem : ∀ b, IsIntegral ℤ b → b ∈ A`
  (lines 97–111); in `…exists_isFrobeniusAt…` it is
  `PlaceTransitivity.coe_mem (A) (b : ℤ̄)` (lines 17–28), which is the same result
  specialised to `b : integralClosure ℤ ℚ̄`. **Write it once**, as a public
  lemma in `NumberTheory/ValuationAtPlace.lean` (e.g.
  `ValuationSubring.integralClosure_le` or `…coe_integralClosure_mem`), and use
  it in both modules. This is the one obvious dedup in the set.
- **`charpoly_baseChangeAlong` and `charpoly_eq_of_isEquiv` are one-liners** over
  `LinearMap.charpoly_baseChange` and `LinearEquiv.charpoly_conj`. Port them as
  the named bridges (they are the interface the surjection proof consumes), with
  no helper block and no alternative proof.
- **`exists_isFrobeniusAt_rat` is a short corollary** of
  `exists_isFrobeniusAt_of_liesOverPrime` (it builds a place over $`\ell`$ via
  `Ideal.exists_ideal_over_maximal_of_isIntegral`); keep it in the same module
  and do not duplicate the Frobenius construction.
- **`isGalois_Qbar` / `isAlgebraic_Qbar`** (pin lines 91–97) are one-line
  `inferInstance` restatements. Before porting them, `#check` the port for an
  existing `IsGalois ℚ (AlgebraicClosure ℚ)` / `Algebra.IsAlgebraic` lemma
  (playbook §3.9, §5.6); prefer reusing or `haveI`, and drop them if unused.
- The pin's `namespace M3dS12D0` / `namespace PlaceTransitivity` helper blocks
  stay **`private`** where the checker does not need them public (playbook §7.1,
  §9): only the seven statements of §0 are public, plus the shared
  `IsIntegral`-membership lemma of the first bullet.

## 3. Port order (build after every module, playbook §5.5)

1. `NumberTheory/ValuationAtPlace.lean` — the shared membership lemma and
   `ValuationSubring.exists_integral_mul_eq_of_liesOverPrime`, with the pin's
   private `exists_div_rep_or_inv_div_rep_of_ne_bot` block.
   `timeout 60 lake env lean` until green, then `timeout 90 lake build`.
2. `NumberTheory/FrobeniusAtPlace.lean` — the `PlaceTransitivity` block
   (`Zbar`, `toPlace`, `center`, `mem_center_iff`, `center_under`,
   `mem_smul_nonunits_iff`, `le_of_forall_not_mem_nonunits`,
   `exists_smul_center_eq`, `smul_eq_of_smul_center_eq`,
   `exists_frobenius_algEquiv`), then
   `exists_isFrobeniusAt_of_liesOverPrime` and `exists_isFrobeniusAt_rat`. This
   is the largest file (314 pin lines) and the one to bisect if a build blows up.
3. `GaloisRep/AdicCharpoly.lean` — the two charpoly bridges.
4. `HeckeGalois/Surjective.lean` — `surjective_of_isEquiv_baseChangeAlong`
   (the traces-generate-$`T`$ argument), then
   `exists_surjective_algHom_of_heckeGaloisRepDatum` (the 9-line universal
   property application).

## 4. Wiring

- Append to `SOURCES` in `spec/check_flt_statements.py`:
  `Theorems/Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.lean`,
  `Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean`,
  `Theorems/Thm_ValuationSubring_exists_isFrobeniusAt_rat.lean`,
  `Theorems/Thm_GaloisRepAdic_charpoly_baseChangeAlong.lean`,
  `Theorems/Thm_GaloisRepAdic_charpoly_eq_of_isEquiv.lean`,
  `Theorems/Thm_CuspForm_HeckeGaloisRepDatum_surjective_of_isEquiv_baseChangeAlong.lean`,
  `Theorems/Thm_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum.lean`.
  Append the four new port modules to `PORT_FILES` (playbook §9).
- The shared `IsIntegral`-membership lemma of §2 is a port promotion that has no
  standalone pin wrapper: add it to `OWN_PROOFS` with the reason (it dedups the
  pin's two copies), or state it privately in each module if the checker is
  cleanly matched without it. Prefer the public shared lemma plus one `OWN_PROOFS`
  entry.
- Add a SET-1 zone to `spec/TsideConsumer.lean` (or a new
  `spec/TsideSet1Consumer.lean`) with a **real cross-module composition**:
  instantiate `ValuationSubring.exists_isFrobeniusAt_rat` (NumberTheory) at a
  prime, feed it to `GaloisRepAdic.charpoly_eq_of_isEquiv` (GaloisRep), and use
  the result to discharge a `Function.Surjective` hypothesis of
  `HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong` (HeckeGalois).
  `#check`s alone are not enough (playbook §7.2).

## 5. Verification gates

1. `cd lean && timeout 180 lake build` — green, no `sorry`/`admit`.
2. `python3 spec/check_flt_statements.py` — the seven new statements identical,
   **0 mismatched, 0 missing**; the identical count rises by the number of new
   public declarations and the exempted count by the §2 promotion. Mutate one
   token of one new statement and confirm it reports `1 mismatched`, then revert
   (playbook §7.4).
3. `#print axioms` on `exists_surjective_algHom_of_heckeGaloisRepDatum`,
   `surjective_of_isEquiv_baseChangeAlong` and `exists_isFrobeniusAt_rat` —
   expect only `propext, Classical.choice, Quot.sound`.
4. The consumer zone builds with 0 errors.
5. Append a SET-1 section to `logs/t-side-port.md` (or a new
   `logs/t-side-set1.md`) with the friction log kept during the port; update the
   module table in `README.md`.

## 6. Risks

- **The Frobenius existence file is the only heavy one** (314 lines, number-field
  `𝓞 F`, `IsLocalization.AtPrime`, `ValuationRing.cond`, discrete valuation
  rings). Expect v4.34 API drift in `ValuationSubring`/`IsLocalization`; probe
  with `#check @name` in `Scratch.lean` on the first name error (playbook §3.9).
- **The `charpoly` bridges must match the wrapper's binder order**: `(φ) (hφ)
  (ρ) (σ)` for the first, `(h) (σ)` for the second. The checker is textual.
- **Do not raise `maxHeartbeats`; do not build concurrently with another agent.**
- **Do not touch** the T11 modules, the Hecke port modules, WeightOne, or the FFG
  modules.

## 7. Pointers

- [../../studies/t-side-driver.md](../../studies/t-side-driver.md) — why this
  half is the driver's first step, and the C′-adjusted estimate for the whole
  assembly.
- [../../math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
  §1.4 (Frobenius at a place), §3.1 (Hecke algebra), §4 (the T package).
- [TOPIC-t11-t-side-definitions.md](TOPIC-t11-t-side-definitions.md) and
  [../../logs/t-side-port.md](../../logs/t-side-port.md) — the definition layer
  this builds on, and the format this file follows.
- [porting-playbook.md](../../porting-playbook.md) §2 (dedup at the source), §3.5
  (rewrite-search gap), §3.11 (build discipline), §7.1/§9 (homes and privacy).
