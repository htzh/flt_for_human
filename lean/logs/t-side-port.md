# The T side of `R = T` — the definition-layer record

**Status: T11 (SET A–E) complete.** This is the running record for the T-side
definition layer, the successor to T10 of [hecke-port.md](hecke-port.md) and the
first port of the T side of `R = T`. The work order is
[TOPIC-t11-t-side-definitions.md](../topics/hecke/TOPIC-t11-t-side-definitions.md);
the mathematics is [math/018](../../math/018-t-side-definitions.md); the context
is [studies/r-equals-t-in-the-proof-base.md](../../studies/r-equals-t-in-the-proof-base.md)
§§6–7. FLT is pinned at `aa2d8b3`; mathlib at `v4.34.0`.

The layer ports the **definitions only**: the Galois substrate the T package is
stated against, the Hecke–Galois datum, the local Hecke algebra, the patching
vocabulary, and the three algebra theorems the local Hecke algebra pulls in. The
theorem layer above the definitions (the 24 `GaloisRep.DeformationRingData.*` lemmas, the 18
`HeckeGaloisRepDatum.*` lemmas, the `PatchingDatum` exit and the `R ≅ T`
assembly) is a later topic.

## 0. What shipped

| pin module | port module | pin lines | port lines | public / private |
|---|---|---:|---:|---|
| `Def_Algebra_PatchingDatum` | `FLTForHuman/Patching/Defs/PatchingDatum.lean` | 44 | 62 | 2 / 0 |
| `Def_FLTPrelim_Modularity` (Weierstrass block) | `FLTForHuman/WeierstrassCurve/Defs/Modularity.lean` | 61 | 89 | 11 / 2 |
| `Def_FLTPrelim_FreyPackage` | `FLTForHuman/WeierstrassCurve/Defs/FreyPackage.lean` | 97 | 102 | 11 / 0 |
| `Def_FLTPrelim_GaloisRep` | `FLTForHuman/GaloisRep/Defs/GaloisAction.lean` | 83 | 91 | 11 / 0 |
| `Def_FLTPrelim_Ramification` | `FLTForHuman/GaloisRep/Defs/Ramification.lean` | 52 | 61 | 4 / 0 |
| `Def_EllipticCurve_FrobeniusTrace` | `FLTForHuman/GaloisRep/Defs/FrobeniusTrace.lean` | 66 | 77 | 8 / 0 |
| `Def_GaloisRep_Residual` | `FLTForHuman/GaloisRep/Defs/Residual.lean` | 105 | 116 | 11 / 0 |
| `Def_GaloisRep_ResidualEquiv` | `FLTForHuman/GaloisRep/Defs/ResidualEquiv.lean` | 54 | 64 | 6 / 0 |
| `Def_GaloisRep_Adic` | `FLTForHuman/GaloisRep/Defs/Adic.lean` | 207 | 219 | 16 / 0 |
| `Def_GaloisRep_DeformationRingData` | `FLTForHuman/GaloisRep/Defs/DeformationRingData.lean` | 46 | 58 | 1 / 0 |
| the three `Thm_*` wrappers + three `S_*` | `FLTForHuman/Algebra/FiniteAlgebraComplete.lean` | 792 | 672 | 3 / 24 |
| `Def_CuspForm_HeckeGaloisRepDatum` | `FLTForHuman/HeckeGalois/Defs/HeckeGaloisRepDatum.lean` | 38 | 57 | 1 / 0 |
| `Def_CuspForm_HeckeLocal` | `FLTForHuman/HeckeGalois/Defs/HeckeLocal.lean` | 440 | 458 | 57 / 10 |
| **total** | | **2,085** | **2,126** | **142 / 36** |

The definition half is ~1:1 (1,293 pin → 1,454 port lines, ratio ≈1.12: the
module headers and docstrings are the difference). The algebra cluster is
792 pin proof lines → 672 port lines, the compression being the dedup in §1.

Public declarations **142**, of which the checker verifies 138 as identical and
exempts 4 (§2).

The three theorem statements are the pin's `Theorems/` wrappers verbatim:

```lean
theorem IsAdicComplete.of_module_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsAdicComplete I M

theorem IsLocalRing.isAdicComplete_of_module_finite {𝒪 : Type u} {T : Type v} [CommRing 𝒪]
    [IsNoetherianRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsLocalRing T]
    [IsLocalHom (algebraMap 𝒪 T)] : IsAdicComplete (IsLocalRing.maximalIdeal T) T

theorem Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] :
    Finite (MaximalSpectrum A) ∧
    Function.Bijective
      (RingHom.pi fun I : MaximalSpectrum A =>
        algebraMap A (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A, Module.Finite 𝒪 (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A,
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime I.asIdeal))
        (Localization.AtPrime I.asIdeal))
```

## 1. Reuse, and the one dedup

Nothing in the Hecke vocabulary was re-derived. `HeckeLocal` consumes the ported
`CuspForm.heckeAlgebra` (`ModularForms/HeckeAlgebra.lean`),
`CuspForm.intLattice`/`HasIntegralStructure`
(`Defs/IntegralStructure.lean`), `mem_intLattice_of_mem_heckeAlgebra` and
`intLattice_fg` (`HeckeLattice.lean`), and `Defs/Eigenform.lean` supplies the
`IsNormalizedEigenform` that `Modularity.lean`'s `IsModularModelOfLevel` names.
`Modularity.lean` ports only the `WeierstrassCurve` block (pin 44–104); the
`qCoeff`/`IsNormalizedEigenform` half (pin 17–42) is imported.

**Dedup: the two `IsAdicComplete` `S_` files are byte-identical.** The pin's
`S_IsAdicComplete_of_module_finite.lean` (148 lines) and
`S_IsLocalRing_isAdicComplete_of_module_finite.lean` (149 lines) share the whole
`Compare` section (lines 18–74) and the whole `ModuleFinite` section (76–116),
differing only in the `Local` section and the final `solution`. The port writes
the shared prelude once, `private`, then the two named solutions against it. That
is the algebra cluster's 792 → 672 compression; the third `S_` file's 495-line
`Row5Aux`/`Row5` block is transcribed whole and kept `private` (24 private
declarations), so the checker's public-surface diff is exact.

The pin's three local heartbeat bumps in `Def_CuspForm_HeckeLocal` —
`set_option synthInstance.maxHeartbeats 400000 in` on `latticeActionHom_injective`
(pin line 89) and the section-level `set_option synthInstance.maxHeartbeats
400000`/`set_option maxHeartbeats 1000000` pairs opening the `Structure` and
`TrioEngines` sections — are **omitted**: the file elaborates under the
`lake env lean` default cap and under the lakefile's cap, so none of the bumps is
needed. No `maxHeartbeats`/`maxRecDepth`/`synthInstance.maxHeartbeats` is set
anywhere in the new modules.

## 2. Wiring, and the one checker finding

`spec/check_flt_statements.py` gained the ten definition pin files, the three
`Theorems/` wrappers, and the thirteen port modules (`SOURCES`, `PORT_FILES`).
`Definitions/Def_FLTPrelim_Modularity.lean` was already listed, so the
`WeierstrassCurve` block is verified without a new entry.

**Finding: the `GaloisRepAdic.Equiv` groupoid laws collide with the
`ResidualGaloisRep.Equiv` copies in *both* of the checker's keys.**
`Def_GaloisRep_ResidualEquiv.lean` and `Def_GaloisRep_Adic.lean` each declare
`refl`/`symm`/`trans`/`baseChangeAlong` for their `Equiv` structures. The
first-name lookup keeps one value per last name, and the promoted-declaration
dotted fallback reduces `GaloisRepAdic.Equiv.refl` and
`ResidualGaloisRep.Equiv.refl` both to the two-component key `Equiv.refl`, so no
`SOURCES` ordering can verify both — the `correspondence` situation recorded in
`OWN_PROOFS`. Both port copies are transcribed verbatim; the **residual** copies
verify (`source['refl']` is theirs), and the four **adic** copies are exempted by
full dotted name, so no unrelated `refl`/`symm`/`trans` is affected:

```python
"GaloisRepAdic.Equiv.refl",
"GaloisRepAdic.Equiv.symm",
"GaloisRepAdic.Equiv.trans",
"GaloisRepAdic.Equiv.baseChangeAlong",
```

The checker was verified by mutating one token of a new statement
(`FreyPackage.ha4` → `ha5`, a structure field name, which the checker compares as
part of the ordered `FIELDS` list): it reported exactly
`1622 statements identical …, 1 mismatched, 0 missing`, and the mutation was
reverted.

The consumer `spec/TsideConsumer.lean` has four zones, each a real cross-module
composition (not `#check`s, no `sorry`):

- `[residual]` — `WeierstrassCurve.residualGaloisRepOf` (`Residual`) with
  `Equiv.refl`/`Equiv.baseChangeAlong`/`.symm`/`.trans` (`ResidualEquiv`), plus
  `smul_mem_torsionBy` and `galoisTrace_def` (`GaloisAction`, `FrobeniusTrace`),
  `IsFrobeniusAt.mem_decompositionSubgroup` (`FrobeniusTrace`), the
  `IsModularModel` unfolding (`Modularity`) and the Frey-curve unramified
  predicate (`FreyPackage` + `Ramification`);
- `[adic]` — `ρ.residual` (`Adic`) with `IsAbsolutelyIrreducible` (`Residual`)
  and `Equiv.residual` read through `IsEquiv` (`ResidualEquiv`);
- `[deformation]` — `GaloisRep.DeformationRingData.universal` (`DeformationRingData`)
  at a test algebra, mentioning the residual isomorphisms of
  `Residual`/`ResidualEquiv` and the adic representations of `Adic`;
- `[hecke]` — `HeckeGaloisRepDatum` over `CuspForm.heckeLocal` exposing
  `charpoly_frob` (`HeckeGaloisRepDatum` + `HeckeLocal` + `HeckeAlgebra`), the
  local-ring/local-hom/adic-complete instances of `heckeLocal` (which consume
  `FiniteAlgebraComplete`), `IsAdicComplete.of_module_finite` directly, and an
  `Algebra.PatchingLevel` instantiation (`PatchingDatum`) at `r = 0` (the
  power-series ring on no variables is the base ring, so the presentation is
  trivial but every field is discharged).

## 3. Verification

Measured, in order.

| command | result |
|---|---|
| `timeout 60 lake env lean <file>` per module | green, 1.6–6.8 s each; `HeckeLocal.lean` 36.6 s |
| `timeout 90 lake build <module>` per module | green, 2.0–5.2 s each; `HeckeLocal` 41 s |
| `timeout 180 lake build` | `Build completed successfully (4375 jobs).` |
| `python3 spec/check_flt_statements.py` | `1623 statements identical (91 promoted from pin-private declarations), 0 mismatched, 0 missing, 26 own-proof declarations exempted (1649 port declarations checked)` |
| `lake env lean spec/TsideConsumer.lean 2>&1 \| grep -c error` | `0` (≈5 s) |

Before this topic the checker read `1485 identical, 0 mismatched, 0 missing,
22 exempted, 1507 checked`; the delta is `+138 identical`, `+4 exempted`,
`+142 checked` — exactly the 142 new public declarations.

`#print axioms` (the three algebra theorems, every `heckeLocal` instance,
`residualGaloisRepOf`, and the datum's `charpoly_frob` field):

```
'IsAdicComplete.of_module_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsLocalRing.isAdicComplete_of_module_finite' depends on axioms: [propext, Classical.choice, Quot.sound]
'Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'WeierstrassCurve.residualGaloisRepOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.heckeLocal.instIsNoetherianRing' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.heckeLocal.instModuleFinite' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.heckeLocal.instModuleFree' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.heckeLocal.instIsLocalRing' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.heckeLocal.instIsAdicComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.heckeLocal.instIsLocalHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.HeckeGaloisRepDatum.charpoly_frob' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`: none of the new modules contains `sorry`/`admit`.

## 4. Friction log (kept during the port, playbook §3.10)

The known shape risks of the work order §5 did **not** materialise: no
`rw`/`simp` rewrite-search gap on `LinearMap.baseChange_*`, no `haveI`-in-`Prop`
blocker (kept by suppressing the style linter, below), and no `abbrev`-unfolding
trap. The `MaximalSpectrum`/`Localization.AtPrime` API in SET C did not drift
apart from the three items below. What did bite, in the order hit:

1. **`TensorProduct.induction_on` is deprecated** (v4.34, since 2026-09-07).
   Replacement `TensorProduct.inductionOn` has **no `zero` case** (its base is
   discharged internally by `tmul 0 0`), so the pin's three-case `induction … with
   | zero | tmul | add` blocks become two-case blocks. Hit in `ResidualEquiv`,
   `Adic.baseChangeAlong` and twice in `Adic.residual`/`Equiv.residual`. The
   deprecation message misspells the replacement as `TensorProduction.inductionOn`;
   the real name is `TensorProduct.inductionOn`.
2. **`Submodule.torsionBy.zmodModule` does not exist under that name, and the
   `AddSubgroup` instance does not fire by search.** The work order §5 (and
   playbook §4) says to drop the pin's `instModuleZModTorsionBy` for
   `Submodule.torsionBy.zmodModule`; in v4.34 the instance is
   `AddSubgroup.torsionBy.zmodModule`, and typeclass search does **not** reach it
   from the `Submodule.torsionBy ℤ M n` carrier (the two carriers are
   definitionally equal but the instance head is `A[n] = (Submodule.torsionBy ℤ A
   n).toAddSubgroup`). The module does not elaborate without an instance, so the
   pin's `instModuleZModTorsionBy` is kept — same name, same statement — with
   `AddSubgroup.torsionBy.zmodModule` as its value. The work order's intent
   (adopt mathlib's proof) is met; its letter (drop the declaration) is not, and
   could not be.
3. **`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal` changed shape** (v4.34,
   since 2026-09-03). It now takes the ring hom and its integrality *first*:
   `(f : R →+* S) (hf : f.IsIntegral) (I : Ideal S)`, where the pin applied it at
   `(P : Ideal A)` and let instance search fill the rest. The port writes
   `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap 𝒪 A) hint.isIntegral P`
   with `hint : Algebra.IsIntegral 𝒪 A := Algebra.IsIntegral.of_finite 𝒪 A`.
4. **Two `S_`-file lemmas live under `IsLocalRing`**: `exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`
   and `map_maximalIdeal_le`. The pin's `open IsLocalRing` in `M4cP1X1` made them
   visible; the port adds the same `open IsLocalRing` at file scope. (Their
   `IsLocalRing.` qualification is *not* part of any compared statement, since
   both occurrences are inside proof bodies.)
5. **`IsArtinianRing.setOf_isMaximal_finite` → `IsArtinianRing.setOfPred_isMaximal_finite`**
   (the `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` family; playbook §4).
6. **`linter.style.haveILetI` fires on the pin's `haveI`/`letI` in `Prop` goals.**
   The proofs are transcribed verbatim, so the linter is suppressed at file scope
   in `FiniteAlgebraComplete.lean` and `HeckeLocal.lean`, as in the other ported
   proof files (`SturmBound.lean`, `WeightOne/*`, …). Deleting the `haveI`s was
   not attempted: they are load-bearing instance introductions inside the pin's
   proofs and the suppression is the established port convention.
7. **`Mathlib.Data.Finite.Card` is a deprecated module** (`deprecated_module`,
   since 2026-06-05) but the pin's `Def_FLTPrelim_Modularity` imports it for
   `Nat.card`. The port drops the import (`Nat.card` arrives transitively through
   the eigenform import), so the module builds warning-free.
8. **`Mathlib.Tactic.ModCases` is not needed** for `FreyPackage`: the only `ZMod`
   fact used is `ZMod.intCast_zmod_eq_zero_iff_dvd`, and the two `omega` goals
   need only `Mathlib.Data.Nat.Prime.Basic`.
9. **Cost sits entirely in `HeckeLocal.lean`.** `lake build
   FLTForHuman.HeckeGalois.Defs.HeckeLocal` is **41 s** while every other new
   module is 2–5 s; the pin's own local heartbeat bumps are omitted and the time
   is tensor-product/`Localization` defeq and instance synthesis, not a heartbeat
   blow-up (it is well under the default cap under `lake env lean`). It is the
   number to watch if the theorem layer above it grows.
10. **The checker's two-key collision is structural, not a bug to fix here.**
    Widening `promoted_key` to the full namespace would break the many existing
    promoted matches (`TPoleOrderLE.mono` against the pin's
    `_root_.ModularCurve.PhiGen.TPoleOrderLE.mono`), so the precise dotted-name
    exemption is the right instrument (§2).

## 5. Hand-off to the theorem layer

The definitions now compile against the Hecke vocabulary and the checker verifies
their statements, so the theorem layer above them has a fixed interface. What the
next topic inherits:

- **`HeckeGaloisRepDatum`'s eight fields** are first-class hypotheses; the
  concrete discharge at `T = heckeLocal N S 𝒪 θ` is the target instance, and
  `charpoly_frob` is exposed in the consumer exactly as the pin spells it.
- **`DeformationRingData.universal`** is the universal property the R≅T assembly
  applies; its binders are the pin's wrappers, so a later proof can be written
  against the same statement.
- **The three algebra theorems are done and axiom-clean** — no debt there.
- **`heckeLocal`'s instances are unconditional for `Module.Finite`/`Module.Free`/
  `IsNoetherianRing` and conditional on `[Fact (HasIntegralStructure N 2)]` for
  `IsLocalRing`/`IsAdicComplete`/`IsLocalHom`**, matching the pin. A route that
  wants unconditional local-ring structure must discharge
  `HasIntegralStructure N 2` first (it is available from
  `WeightOne/IntegralStructure.lean` for `2 ≤ k`).
- **Build budget:** budget `HeckeLocal`-sized modules at ~40 s each, and keep the
  `lake env lean` / `lake build` bounds of the work order.

# SET 1 — the surjection half of `R = T` (T12)

**Status: complete.** The first theorem set above the T11 definition layer. The
work order is
[TOPIC-t12-set1-surjection.md](../topics/hecke/TOPIC-t12-set1-surjection.md); the
driver plan is [studies/t-side-driver.md](../../studies/t-side-driver.md). It ports
the seven nodes of the work order §0 — the existence of `φ : R → T` and the four
lemmas it needs — into four modules at their **natural subject homes**, not under
a T-side directory.

## 6. What shipped

| pin source (lines) | port module | port lines | public / private |
|---|---|---:|---|
| `S_…exists_integral_mul_eq_of_liesOverPrime` (184) | `FLTForHuman/NumberTheory/ValuationAtPlace.lean` | 209 | 2 / 2 |
| `S_…exists_isFrobeniusAt_of_liesOverPrime` (314) + `S_…exists_isFrobeniusAt_rat` (30) | `FLTForHuman/NumberTheory/FrobeniusAtPlace.lean` | 349 | 2 / 10 |
| `S_GaloisRepAdic_charpoly_baseChangeAlong` (9) + `S_…charpoly_eq_of_isEquiv` (13) | `FLTForHuman/GaloisRep/AdicCharpoly.lean` | 39 | 2 / 0 |
| `S_CuspForm_HeckeGaloisRepDatum_surjective_of_isEquiv_baseChangeAlong` (51) + `S_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum` (9) | `FLTForHuman/HeckeGalois/Surjective.lean` | 101 | 2 / 0 |
| **total** | | **698** | **8 / 12** |

The public surface is exactly the seven §0 statements (verbatim from their
`Theorems/` wrappers) plus the one shared promotion
`ValuationSubring.mem_of_isIntegral`. Every other pin helper is `private`: the
`PlaceTransitivity` block (`toPlace`, `center`, `mem_center_iff`,
`center_isPrime`, `center_under`, `mem_smul_nonunits_iff`,
`le_of_forall_not_mem_nonunits`, `exists_smul_center_eq`,
`smul_eq_of_smul_center_eq`, `exists_frobenius_algEquiv`) and the private
`exists_div_rep_or_inv_div_rep_of_ne_bot` remain invisible to the checker.

## 7. Deduplication (playbook §2)

Two pin duplications were removed at the source:

- **`IsIntegral ℤ b → b ∈ A` was proved twice.** The local `int_mem` of
  `S_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.lean` (lines
  97–111, 15 lines) and `PlaceTransitivity.coe_mem` of
  `S_…exists_isFrobeniusAt_of_liesOverPrime.lean` (lines 17–28, 12 lines) are the
  same argument; the second is the first specialised to `b : ℤ̄`. The port writes
  it once as the public `ValuationSubring.mem_of_isIntegral`, in the number-theory
  subject home, and both modules call it (the two `coe_mem` call sites become
  `ValuationSubring.mem_of_isIntegral W (x' : ℚ̄) x'.2`). **Saves 12 pin lines**
  (the smaller copy), and removes the risk of the two copies drifting.
- **`isGalois_Qbar` / `isAlgebraic_Qbar` (pin lines 91–97, 7 lines) are
  `inferInstance` restatements.** `IsGalois ℚ (AlgebraicClosure ℚ)`,
  `Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ)` and (via
  `Algebra.isAlgebraic_iff_isIntegral.mp`) `Algebra.IsIntegral ℚ ℚ̄` are all found
  by `inferInstance`, so the two private lemmas are dropped and their uses become
  `haveI : … := inferInstance`. **Saves 7 pin lines.**

Total: **~19 pin lines**.

**One duplication left, deliberately.** The pin's 28-line profinite setup —
`letI : TopologicalSpace ℤ̄ := ⊥`, `DiscreteTopology`, the `ContinuousSMul`
instance and the `Algebra.IsInvariant` instance — is byte-identical in
`exists_smul_center_eq` (lines 110–137) and in the final `solution` (lines
226–253), plus the two-line `letI`/`DiscreteTopology` pair each. The port keeps
both copies. The instances are about a **local** topology override, so they cannot
be made global instances, and bundling them in a private structure is a defeq risk
not worth taking in this set (playbook §3.4). It is the one remaining ~30-line
duplication in the file and the obvious candidate for a later cleanup.

## 8. Wiring

`spec/check_flt_statements.py` gained the seven `Theorems/` wrappers in `SOURCES`
(appended **last** so no earlier last-name match can flip; `charpoly_baseChangeAlong`
also names a `ResidualGaloisRep` node, and the two `exists_isFrobeniusAt_*` names
have many `S_` copies outside this cone), the four port modules in `PORT_FILES`,
and one `OWN_PROOFS` entry — the *dotted* `ValuationSubring.mem_of_isIntegral`, so
the exemption cannot leak to any other `mem_of_isIntegral`. No `S_` carrier is
listed: the whole `PlaceTransitivity` block is `private` in the port, so the
checker never asks for it.

The consumer is the new [spec/TsideSet1Consumer.lean](../spec/TsideSet1Consumer.lean),
whose `[surjection]` zone is one real cross-module composition (no `#check`s, no
`sorry`): `ValuationSubring.exists_isFrobeniusAt_rat` (NumberTheory) supplies a
place and a Frobenius, T11's `charpoly_frob` supplies the equation, the two
`GaloisRepAdic` charpoly bridges transport it to
`ρR.baseChangeAlong φ`, and the resulting `X`-coefficient is the membership
`H.π (T_ℓ) ∈ φ.range`; the HeckeGalois theorems then close the loop, including the
`DeformationRingData` universal-property form. Deleting any one of the four
modules fails this file.

## 9. Verification

Measured, in order.

| command | result |
|---|---|
| `timeout 60 lake env lean <file>` per module | green, 3.9–5.8 s each (the first, cold-cache `ValuationAtPlace` run was 17.4 s); all warning-free |
| `timeout 90 lake build <module>` per module | green, 3.2–5.2 s each |
| `timeout 180 lake build` | `Build completed successfully (4400 jobs).` |
| `python3 spec/check_flt_statements.py` | `1630 statements identical (91 promoted from pin-private declarations), 0 mismatched, 0 missing, 27 own-proof declarations exempted (1657 port declarations checked)` |
| `lake env lean spec/TsideSet1Consumer.lean 2>&1 \| grep -c error` | `0` (5.1 s) |

Before this set the checker read `1623 identical, 0 mismatched, 0 missing, 26
exempted, 1649 checked`; the delta is `+7 identical`, `+1 exempted`, `+8 checked` —
exactly the seven public statements plus the shared lemma. The checker was verified
by mutating one token of `exists_integral_mul_eq_of_liesOverPrime`'s statement
(`A.nonunits` → `A.nonunitsX`): it reported `1629 statements identical … 1
mismatched, 0 missing`, and the mutation was reverted.

`#print axioms` (every new public declaration):

```
'GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CuspForm.HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ValuationSubring.exists_isFrobeniusAt_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'ValuationSubring.exists_integral_mul_eq_of_liesOverPrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'ValuationSubring.mem_of_isIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepAdic.charpoly_baseChangeAlong' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaloisRepAdic.charpoly_eq_of_isEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`: none of the four modules or the consumer contains `sorry`/`admit`,
and no `maxHeartbeats`/`maxRecDepth`/`synthInstance.maxHeartbeats` is set anywhere.

## 10. Friction log (kept during the port, playbook §3.10)

The work order §6's expected risk — v4.34 API drift in the heavy
`ValuationSubring`/`IsLocalization` file — did **not** materialise: the pin's
proofs elaborate under the default cap, and `FrobeniusAtPlace` is 5.8 s. What did
bite, in the order hit:

1. **The pin's `import Mathlib` hid four specific dependencies of the profinite
   step.** With the port's specific imports, `CompactSpace Gal(ℚ̄/ℚ)` is not
   synthesised until `Mathlib.FieldTheory.Galois.Profinite` is imported (its
   `instance [IsGalois k K] : CompactSpace Gal(K/k)`); the remaining names came
   from `Mathlib.FieldTheory.KrullTopology`
   (`IntermediateField.fixingSubgroup_isOpen`),
   `Mathlib.FieldTheory.Galois.Infinite`
   (`InfiniteGalois.mem_range_algebraMap_iff_fixed`) and
   `Mathlib.RingTheory.Invariant.Profinite` (the two
   `…of_profinite` lemmas). The pin's `P2M.Util`/`Def_FLTPrelim_Ramification`
   imports had pulled these in transitively in the pin's tree; naming them is the
   port's job.
2. **`Ideal.under` is not syntactically `Ideal.comap` under `rw`** (the
   abbrev/def gap, playbook §3.7). In `exists_isFrobeniusAt_rat` the pin's
   `rw [h𝔔]`, with `h𝔔 : Ideal.under ℤ 𝔔 = …`, fails on the goal
   `(ℓ : ℤ) ∈ Ideal.comap (algebraMap ℤ O) 𝔔`; the port inserts
   `change (ℓ : ℤ) ∈ Ideal.under ℤ 𝔔` first.
3. **`if_neg` is deprecated** (playbook §4) → `ite_eq_right`, twice in the trace
   coefficients of `surjective_of_isEquiv_baseChangeAlong`.
4. **`linter.style.haveILetI` fires in the two number-theory modules** on the
   pin's `haveI` instance introductions in `Prop` goals; suppressed at file scope
   as in the other ported proof files. It also fires on
   `letI : Algebra A B := φ.toAlgebra` in `AdicCharpoly`; there the port writes
   plain `let`, and typeclass search still finds the local instance — no
   suppression needed.
5. **`isGalois_Qbar`/`isAlgebraic_Qbar` are redundant** (see §7): `inferInstance`
   supplies both, so the two private restatements are dropped. This is the
   playbook §3.9/§5.6 probe paying off.
6. **`exists_smul_center_eq` has no consumer inside this cone.** The pin's other
   `S_` files (`…exists_forall_apply_eq_and_isFrobeniusAt_natCard_of_liesOverPrime`
   and friends) use it, so it is ported `private` per work order §3; the port's
   `solution` needs only `smul_eq_of_smul_center_eq` and `exists_frobenius_algEquiv`.

## 11. Hand-off to SETs 2–4

- **The four homes are fixed and the checker verifies the seven statements.** SET
  2 (eigenform extraction) can consume `ValuationSubring.exists_isFrobeniusAt_rat`
  and the two `GaloisRepAdic` charpoly bridges directly; the trace-coefficient
  argument of `surjective_of_isEquiv_baseChangeAlong` is the template for its
  charpoly identities and is reproduced as an executable wire test in the
  consumer.
- **`ValuationSubring.mem_of_isIntegral` is the single public membership lemma**
  for "integral over `ℤ` lies in the place"; do not re-derive the pin's `int_mem`
  or `coe_mem` copies.
- **Build budget:** these four modules are 3–6 s each; the T side no longer has a
  heavy file. The `HeckeLocal` 41 s from T11 remains the largest in the tree.

# SET 2 — the eigenform-extraction chain (T12)

**Status: complete.** The second theorem set above the T11 definition layer: the
nine nodes of [TOPIC-t12-set2-eigenform-extraction.md](../topics/hecke/TOPIC-t12-set2-eigenform-extraction.md)
§0, ported into five modules at their **natural subject homes**. It consumes the
ported `HeckeQCoeff`/`HeckeEigenform`/`HeckeLattice`/`HeckeFiniteAlgebra`
vocabulary and SET 1's `ValuationSubring.exists_isFrobeniusAt_rat` only
indirectly (SET 3 does the wiring).

## 12. What shipped

| pin source (lines) | port module | port lines | public / private |
|---|---|---:|---|
| `S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed` (30) | `FLTForHuman/Algebra/IntegralExtensionCharacters.lean` | 135 | 2 / 0 |
| `S_Ideal_exists_ringHom_integralClosure_ker_eq` (76) | same module | | |
| `S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_ringHom` (246) | `FLTForHuman/Algebra/FaithfulLatticeEigenvector.lean` | 289 | 1 / 3 |
| `S_CuspForm_exists_degeneracy_Gamma0` (115) | `FLTForHuman/ModularForms/Level/Degeneracy.lean` | 122 | 1 / 3 |
| `S_CuspForm_exists_isNormalizedEigenform_level_mul` (147) | `FLTForHuman/ModularForms/EigenformLevel.lean` | 212 | 2 / 2 |
| `S_CuspForm_exists_isNormalizedEigenform_of_dvd` (39) | same module | | |
| `S_CuspForm_linearIndependent_of_mem_intLattice` (95) | `FLTForHuman/ModularForms/EigenformExtraction.lean` | 279 | 3 / 6 |
| `S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul` (25) | same module | | |
| `S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq` (144) | same module | | |
| **total** | | **1,037** | **9 / 14** |

The public surface is exactly the nine §0 statements (verbatim from their
`Theorems/` wrappers) plus the one shared promotion
`CuspForm.mem_intLattice_iff` (§13). Every pin helper is `private`: the
`FrobChareqEngine.engine3/4/5a` block, the `PStab.pow_sub_beta_mul`/`stab_clauses`
arithmetic block, the whole `DegeneracyPort` block, and the `FrobChareqC2`
q-coefficient helpers (`qCoeff_zero'`, `qCoeff_smul`,
`qCoeff_hecke{T,U}Lin_one`, `C2_7a`).

## 13. Deduplication (playbook §2)

**The truncation (§2, the design decision).** The port already carried the Sturm
truncation twice: `HeckeLattice`'s private `sturmB`/`trunc`/`trunc_injective`
(`ℤ`-linear) and `SturmBound`'s public `qCoeffTrunc` (`ℂ`-linear) +
`Gamma0_eq_zero_of_qExpansion_coeff_eq_zero`. The pin's
`S_CuspForm_linearIndependent_of_mem_intLattice` re-derived a **third** copy in
its `FrobChareqC2` namespace:

| pin item | pin lines |
|---|---:|
| `hΓ` (`one_mem_strictPeriods_Gamma0`) | 3 |
| `qCoeff_add` | 4 |
| `qCoeff_smul` | 6 |
| `trunc` (ℂ-linear) | 4 |
| `sturmB` | 1 |
| `trunc_injective` | 10 |
| **total third-copy block** | **28** |

The port writes **none** of it: `linearIndependent_of_mem_intLattice` uses the
public `CuspForm.qCoeffTrunc N k d` (which already carries the linearity the pin's
`hΓ`/`qCoeff_add`/`qCoeff_smul` supply) and derives injectivity once, privately,
in the 9-line `qCoeffTrunc_injective` from
`CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero`. **Pin lines saved: 28 → 9
= 19**, and — the point of §2 — the third `sturmB`/`trunc`/`trunc_injective`
simply does not exist. The cost is the 11-line Sturm-length arithmetic (`c`, `d`,
`hd`, `hd'`) at the call site, which the pin had hidden inside its `sturmB`; it is
the *same* block `finiteDimensional_Gamma0` already proves inline, and it was left
duplicated rather than refactoring `SturmBound.lean` (the work order's "keep the
change additive"). Net module content: the pin's first-theorem region is 69
non-blank lines, the port's is 66.

**The degeneracy block.** `S_CuspForm_exists_degeneracy_Gamma0`'s
`DegeneracyPort` is shared in the pin with `ModularForm.exists_degeneracy_Gamma0`.
That node is **not** in this cone, and its helpers `restrictMF`,
`coe_restrictMF` and `exists_modularForm` (23 pin lines) are therefore dropped
rather than ported (playbook §7.1, "no self-consumed lemmas"); `restrictCF`,
`coe_restrictCF`, `Gamma0_le_conj_Gamma0` and `exists_cuspForm` remain `private`.

**The `FrobChareqC2` q-coefficient helpers.** `hΓ` is the ported
`CongruenceSubgroup.one_mem_strictPeriods_Gamma0`; `qCoeff_zero'` is **not** the
ported `CuspForm.qCoeff_zero` (that one is `qCoeff f 0 = 0`, the pin's helper is
"the zero form has all coefficients zero"), so it stays `private` here, as do the
ℂ-scalar `qCoeff_smul` and the two `qCoeff_hecke{T,U}Lin_one` lemmas (which use
the ported `heckeTLin_apply_eq_smul_iff`/`coeffHeckeT_apply` rather than
re-deriving the coefficient identity). This is the §2 instruction "reuse **or**
keep `private`; do not re-prove what exists".

**Boilerplate dropped.** The pin's `p2m_open`/`p2m_exact_reverting` shims are not
transcribed (state and prove directly), and every `import Mathlib` is replaced by
the specific modules used.

## 14. Wiring

`spec/check_flt_statements.py` gained the nine `Theorems/` wrappers of §0 plus
`Thm_CuspForm_mem_intLattice_iff.lean` in `SOURCES` (appended **last**, so no
earlier last-name match can flip; `exists_degeneracy_Gamma0` also names the
unported `ModularForm` node), the five new port modules in `PORT_FILES`, and
**no** `OWN_PROOFS` entry: the one promotion `CuspForm.mem_intLattice_iff` has a
pin wrapper, so it is *verified* rather than exempted. `HeckeLattice.lean` is
already in `PORT_FILES`, so the additive `private` → public change is diffed
there.

The consumer is the new [spec/TsideSet2Consumer.lean](../spec/TsideSet2Consumer.lean),
whose `[extraction]` zone is a real cross-module composition (no `#check`s, no
`sorry`): a Hecke character `χ` is fed to
`HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq`
(EigenformExtraction), the resulting normalised eigenform is handed to the ported
`IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul` dictionary to read off its
`T_ℓ` eigenvalue, and the same form is raised to level `N * p` by
`exists_isNormalizedEigenform_level_mul` (EigenformLevel). The `U_q` half, the
degeneracy map, the level-divisibility iteration and the two generic algebra
nodes get their own zones. Deleting any one of the five modules fails this file.

## 15. Verification

Measured, in order.

| command | result |
|---|---|
| `timeout 60 lake env lean <file>` per module | green and warning-free, 1.7–6.4 s each |
| `timeout 90 lake build <module>` per module | green, 3.7–4.6 s each (module 5 cascaded `HeckeFiniteAlgebra` at 31 s) |
| `timeout 300 lake build` | `Build completed successfully (4408 jobs).` (39 s) |
| `python3 spec/check_flt_statements.py` | `1640 statements identical (91 promoted from pin-private declarations), 0 mismatched, 0 missing, 27 own-proof declarations exempted (1667 port declarations checked)` |
| `lake env lean spec/TsideSet2Consumer.lean 2>&1 \| grep -c error` | `0` (5.0 s) |

Before this set the checker read `1630 identical, 0 mismatched, 0 missing, 27
exempted, 1657 checked`; the delta is `+10 identical`, `+10 checked` — exactly the
nine §0 statements plus the `mem_intLattice_iff` promotion. The checker was
verified by mutating one token of `linearIndependent_of_mem_intLattice`'s
statement (`LinearIndependent ℤ f` → `LinearIndependent ℤx f`): it reported
`1639 statements identical … 1 mismatched, 0 missing`, and the mutation was
reverted.

`#print axioms` (all ten public declarations):

```
'RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Ideal.exists_ringHom_integralClosure_ker_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.exists_degeneracy_Gamma0' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.exists_isNormalizedEigenform_level_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.exists_isNormalizedEigenform_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.linearIndependent_of_mem_intLattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CuspForm.mem_intLattice_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`: none of the five modules or the consumer contains `sorry`/`admit`,
and no `maxHeartbeats`/`maxRecDepth`/`synthInstance.maxHeartbeats` is set anywhere.

## 16. Friction log (kept during the port, playbook §3.10)

The heavy module's expected risk — associated primes / minimal primes /
Hopkins–Levitzki — did **not** materialise: `engine3`'s
`Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes` and
`Submodule.isAssociatedPrime_iff` are unchanged in v4.34, and the whole 246-line
`Module.End` node elaborates in 2.6 s. What did bite, in the order hit:

1. **The blanket `import Mathlib` hid a tensor-product finiteness instance.**
   `Module.Finite K (K ⊗[ℤ] D) := inferInstance` needed
   `Mathlib.RingTheory.TensorProduct.Finite` (the pin's `TensorProduct.Free` /
   `.Maps` imports do not pull it in). The same class of SET 1 friction item 1.
2. **`TensorProduct.induction_on` is deprecated and its replacement has no `zero`
   case.** The pin's three-case `induction a using TensorProduct.induction_on with
   | zero | tmul | add` becomes the two-case `TensorProduct.inductionOn with |
   tmul | add` (the base is discharged internally by `tmul 0 0`).
3. **`Module.Finite.of_restrict_scalars_finite` → `of_restrictScalars_finite`**
   (one occurrence, module 2).
4. **`Ideal.eq_bot_of_comap_eq_bot`/`Ideal.mem_comap` → `eq_bot_of_under_eq_bot`/
   `Ideal.mem_under`, plus the `under`/`comap` abbrev gap.** The pin's `rw [hQP]`
   on `a ∈ Q.comap (algebraMap A B)` fails; the port inserts
   `change a ∈ Ideal.under A Q at ha` first (playbook §3.7). The deprecated
   `Ideal.mem_comap` still exists but the goal is spelled `Ideal.under`.
5. **The `if`/`dif` renames.** `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`
   (module 4 `PStab`, module 3 `exists_cuspForm`); `dif_pos`/`dif_neg` →
   `dite_eq_left`/`dite_eq_right` (module 5's `c` character). The `dite` names take
   the membership proof as the explicit argument, as the old names did.
6. **`CuspForm.IsGLPos.coe_smul` and `CuspForm.coe_sub` are deprecated aliases**
   for `FunLike.coe_smul`/`FunLike.coe_sub`; the port writes the new names.
7. **`Matrix.SpecialLinearGroup.mapGL_coe_matrix` only rewrites half-way in
   v4.34.** It takes `↑(mapGL ℝ B)` to `↑(map (algebraMap ℤ ℝ) B)`, and the pin's
   single closing `simp` no longer reaches the matrix entries; the port needs an
   explicit `rw [Matrix.SpecialLinearGroup.map_apply_coe]` before the case split.
   This is the playbook §3.5 rewrite-search gap on a coercion whose head changed.
8. **`Mathlib.NumberTheory.ModularForms.CongruenceSubgroups` does not import
   `Basic`.** `CuspForm` is unknown after importing only `CongruenceSubgroups` (and
   `CongruenceSubgroups` also does not re-export it); `Level/Degeneracy.lean` needs
   the explicit `Mathlib.NumberTheory.ModularForms.Basic` import. A one-line probe
   in `Scratch.lean` (`#check CuspForm`) caught it.
9. **`Nat.recOnMul` lives in `Mathlib.Data.Nat.Factorization.Induction`** — the
   blanket import had carried it; the specific-import fix is explicit.
10. **`CuspForm.qCoeff_zero` is not the pin's `qCoeff_zero'`.** The ported public
    lemma is `qCoeff f 0 = 0`; the pin's private helper is "the **zero** form has
    *all* coefficients zero". The port keeps a private `qCoeff_zero'` (2 lines)
    rather than promoting the equivalent `HeckeLattice.qCoeff_zero'`.
11. **`lake env lean` resolves imports from the Lake build directory.** After
    promoting `HeckeLattice.mem_intLattice_iff`, `lake env lean
    EigenformExtraction.lean` still saw the stale olean and reported
    `Unknown constant CuspForm.mem_intLattice_iff`; `lake build
    FLTForHuman.ModularForms.HeckeLattice` first fixed it. The other four new
    modules were unaffected because they were freshly lake-built.
12. **The additive promotion touches `HeckeLattice.lean` only as a `private` →
    public publication**, keeping the same name and statement (spelled with
    `ModularFormClass.qCoeff` and explicit `{N : ℕ} {k : ℤ}` to match the wrapper
    textually). No existing declaration was renamed or renumbered; the two
    internal `rw [mem_intLattice_iff]` call sites are unchanged.

## 17. Hand-off to SET 3

- **The extraction interface is fixed.** SET 3's conditional capstone consumes
  `CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq` (a
  normalised eigenform whose `T_ℓ`/`U_q` coefficients are the character values)
  together with T11's `CuspForm.HeckeGaloisRepDatum`; the consumer zone shows the
  exact composition with the ported `IsNormalizedEigenform` dictionary.
- **`CuspForm.mem_intLattice_iff` is now public** (verified against its pin
  wrapper). Do not re-derive it.
- **`CuspForm.qCoeffTrunc` is the single truncation.** The private
  `qCoeffTrunc_injective` is not an interface; a later module needing an injective
  coefficient truncation should use `qCoeffTrunc` + the same
  `Gamma0_eq_zero_of_qExpansion_coeff_eq_zero` route rather than writing a
  `sturmB`.
- **The generic algebra nodes are reusable.** `RingHom.exists_comp_...` and
  `Module.End.exists_ne_zero_...` are stated over arbitrary rings; SET 3's
  character arguments can call them directly.
- **Build budget:** the five modules are 2–7 s each; `EigenformExtraction.lean`
  pulls `HeckeFiniteAlgebra` (31 s when its cascade is cold), so an edit to
  `HeckeLattice.lean` re-checks that module first. `HeckeLocal` (41 s) remains the
  largest file in the tree.


# SET 3 — the conditional capstone of `R = T` (T12)

**Status: complete.** The third theorem set above the T11 definition layer and the
capstone of the T-side driver: the pin's `R ≅ T` assembly,
`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum` (145 pin lines), ported
**conditionally** into the single module
`FLTForHuman/WeierstrassCurve/ModularityLifting.lean` so the 3,789-line patching
construction does not gate it. The work order is
[TOPIC-t12-set3-conditional-capstone.md](../topics/hecke/TOPIC-t12-set3-conditional-capstone.md);
the driver plan and the conditional split are
[studies/t-side-driver.md](../../studies/t-side-driver.md) §2, §4 and
[porting-playbook.md](../../porting-playbook.md) §7.3. The mathematics is
[math/018-t-side-definitions.md](../../math/018-t-side-definitions.md) §4.

## 18. What shipped

| pin source (lines) | port module | port lines | public / private |
|---|---|---:|---|
| `S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum` (145) | `FLTForHuman/WeierstrassCurve/ModularityLifting.lean` | 202 | 1 / 0 |
| **total** | | **202** | **1 / 0** |

The single public declaration is the conditional capstone
`WeierstrassCurve.isModularModelOfLevel_of_patchingLevel`; every helper is inline
(the pin has no auxiliary declarations beyond its two `obtain`ed inputs), so the
checker sees exactly one declaration and `OWN_PROOFS` has exactly one new entry.

**The frozen conditional statement** (the binder block SET 4 discharges; the rest
of the binder list and the conclusion are the pin's verbatim):

```lean
    {M : Type} [AddCommGroup M] [Module D.R M] [Module T M] [Nontrivial M]
    (hcompat : ∀ (x : D.R) (m : M), φ x • m = x • m)
    {r : ℕ} (L : Algebra.PatchingLevel 𝒪 r D.R M ⊥)
    (hfree : Module.Free D.R M) (hann : Module.annihilator D.R M = ⊥)
    (hker : RingHom.ker L.ψ = Ideal.span (Set.range fun i : Fin r => L.φ (MvPowerSeries.X i)))
    (ρW : GaloisRepAdic 𝒪) (h𝒟W : 𝒟 ρW)
    …
    W.IsModularModelOfLevel (N * ∏ q ∈ S.filter (fun q => ¬ q ∣ N), q)
```

The `p` and `hp𝒪` binders from the pin's signature are kept (unused here) so SET 4
recovers the verbatim wrapper without a statement edit; the only difference from
the pin is the substitution of `(P : Algebra.PatchingDatum 𝒪 p r D.R M)` and the
two lines that consume it by `L`/`hfree`/`hann`/`hker`.

## 19. Reuse, and the only new content

The proof is the pin's with the two patching lines deleted, so almost all of it is
**application** of already-ported lemmas — no restatement:

- `CuspForm.HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong` (SET 1) for
  `hsurj`;
- `Module.annihilator_eq_bot` (mathlib) is the bridge the pin used to turn the free
  nontrivial module into `Module.annihilator D.R M = ⊥`;
- `AlgEquiv.ofBijective` (mathlib) for `e : D.R ≃ₐ[𝒪] T`;
- `D.universal` (T11) for `φW` and its base-change isomorphism `hEqW`;
- `GaloisRepAdic.charpoly_baseChangeAlong`, `…charpoly_eq_of_isEquiv` and
  `ValuationSubring.exists_isFrobeniusAt_rat` (SET 1) for the charpoly comparison;
- `CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq`,
  `Ideal.exists_ringHom_integralClosure_ker_eq` and
  `CuspForm.exists_isNormalizedEigenform_of_dvd` (SET 2) for the eigenform; and
- `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra` (T10) for the
  finiteness input of the prime-kernel lemma.

The **only** genuinely new proof content is the pin's `ψW` construction
(`φW.comp e.symm`, with `hψW` from `e.symm_apply_apply`) and the `hχ` charpoly
coefficient read-off. The latter is the pin's `congrArg (coeff 1)` followed by a
`simp only`; the `Polynomial.map_add/sub/mul/pow/X/C` set pushes the coefficient map
inward, so **no `coeff_map` is needed** here (unlike SET 1's trace-coefficient
block, whose equation keeps the `map` outside). The v4.34 renames in the set are
the two `if_neg` → `ite_eq_right` (playbook §4, the same two as SET 1).

## 20. Wiring

`spec/check_flt_statements.py` gained one `SOURCES` entry — the wrapper
`Theorems/Thm_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean`,
appended **last** (its last name is unique in the pin, so it cannot flip an earlier
match). The wrapper is registered now, though the verbatim declaration is not
ported, so SET 4 needs no checker edit for it. `PORT_FILES` gained
`FLTForHuman/WeierstrassCurve/ModularityLifting.lean`, and `OWN_PROOFS` gained the
dotted name `WeierstrassCurve.isModularModelOfLevel_of_patchingLevel`, with the
reason "the patching facts are hypotheses; the verbatim statement lands in SET 4" —
dotted so the exemption cannot leak to any other `isModularModelOfLevel_*`.

The consumer is the new [spec/TsideSet3Consumer.lean](../spec/TsideSet3Consumer.lean).
Its `[capstone]` zone is a real cross-module composition (no `#check`s, no `sorry`):
SET 1's `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum`
produces `φ : D.R → T`, its `IsLocalHom` proof and the base-change isomorphism of
its adic representation from a `DeformationRingData` and a `HeckeGaloisRepDatum`;
the conditional capstone then consumes them with the three patching hypotheses and
a `GaloisRepAdic`'s `hWfrob`, concluding `W.IsModularModelOfLevel`. Deleting either
`HeckeGalois/Surjective.lean` or `WeierstrassCurve/ModularityLifting.lean` fails the
file. Its `[inputs]` zone records that `hann` is also derivable from
`hfree` + `[Nontrivial M]` through mathlib's `Module.annihilator_eq_bot`.

## 21. Verification

Measured, in order.

| command | result |
|---|---|
| `timeout 60 lake env lean` on the conditional statement (`sorry` placeholder) | green, 5.2 s |
| `timeout 60 lake env lean FLTForHuman/WeierstrassCurve/ModularityLifting.lean` | green and warning-free, 4.0 s |
| `timeout 90 lake build FLTForHuman.WeierstrassCurve.ModularityLifting` | green, 9.1 s (module 6.5 s) |
| `timeout 180 lake build` | `Build completed successfully (4409 jobs).` (3 s, replayed) |
| `python3 spec/check_flt_statements.py` | `1640 statements identical (91 promoted from pin-private declarations), 0 mismatched, 0 missing, 28 own-proof declarations exempted (1668 port declarations checked)` |
| `lake env lean spec/TsideSet3Consumer.lean 2>&1 \| grep -c error` | `0` (4.9 s) |

Before this set the checker read `1640 identical, 0 mismatched, 0 missing, 27
exempted, 1667 checked`; the delta is `+1 exempted`, `+1 checked` — the identical
count is **unchanged**, exactly as the work order §5 predicts (the capstone is
`OWN_PROOFS`), and no other declaration moved.

`#print axioms` on the conditional capstone:

```
'WeierstrassCurve.isModularModelOfLevel_of_patchingLevel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`: neither the module nor the consumer contains `sorry`/`admit`, and no
`maxHeartbeats`/`maxRecDepth`/`synthInstance.maxHeartbeats` is set anywhere. The
two file-scope linter suppressions (`linter.style.haveILetI`,
`linter.unusedVariables`) follow the established port convention for verbatim
proof bodies and for pin binders that SET 4 will consume.

## 22. Friction log (kept during the port, playbook §3.10)

The work order §6's named risk — the `hχ` coefficient read-off — did **not**
materialise: the pin's `simp only` set transcribed with only the two `if_neg` →
`ite_eq_right` renames, and the whole proof elaborated on the first attempt
(6.4 s) with no heartbeat issue. What did bite:

1. **The two patching inputs are not interchangeable with the pin's.** The pin's
   `hfree` looked unused (`obtain ⟨hfree, -, -⟩ := L.free_and_ker_eq_span`) but was
   load-bearing through instance search: `inferInstance : FaithfulSMul D.R M` is
   `Module.Free.instFaithfulSMulOfNontrivial`, which needs the local `hfree`. In the
   conditional statement the annihilator is a *hypothesis*, so `hfree` is genuinely
   unused and `Module.annihilator_eq_bot` is not needed in the proof. `hfree`/`hker`
   stay as binders for SET 4 and are covered by the file-scope
   `linter.unusedVariables false` (as `Gamma1Basis.lean` already does for pin
   binders); so are the pin's `hΔ` and `hp𝒪`.
2. **`exists_surjective_algHom_of_heckeGaloisRepDatum` takes `H` explicitly.** The
   consumer's first draft passed `D` then the `hS` lambda and got
   "Application type mismatch … expected to have type `CuspForm.HeckeGaloisRepDatum`"
   — the lemma's binder order is `(D) {N} [NeZero N] {S} {θ} {T} [instances]
   (H) (hS) (h𝒟) (hres)`, with `H` explicit. Passing `D H hS h𝒟 hres` fixed it.
   Not drift, but the one consumer-side cost of the set.
3. **`hcompat` and `φ` produced inside the consumer.** Because the composition
   derives `φ` from the universal property, the module-compatibility input cannot
   be a binder *about that `φ`*; the consumer takes it in the quantified form
   `∀ φ hφ, IsEquiv … → compatible`, which is the shape the capstone's `hcompat`
   has once `φ` is fixed. SET 4 applies the capstone at a `φ` that is already fixed,
   so its `hcompat` is the pin's plain pointwise statement.

## 23. Hand-off to SET 4 (the patching cluster)

- **The capstone's input is frozen** at `{r} (L : Algebra.PatchingLevel 𝒪 r D.R M ⊥)
  (hfree) (hann) (hker)`. To recover the verbatim pinned statement, SET 4 ports the
  patching cluster, obtains `L` from
  `Algebra.PatchingDatum.nonempty_patchingLevel_bot hp𝒪`, and discharges the three
  facts with `obtain ⟨hfree, hann, hker⟩ := L.free_and_ker_eq_span` before calling
  `WeierstrassCurve.isModularModelOfLevel_of_patchingLevel`. The `p`/`hp𝒪` binders
  are kept unused precisely so the wrapper's binder block needs no edit.
- **`hann` has two routes.** It is one component of
  `Algebra.PatchingLevel.free_and_ker_eq_span`, but it is also
  `Module.annihilator_eq_bot.mpr inferInstance` from `hfree` + `[Nontrivial M]`
  (the consumer's `[inputs]` zone proves exactly that), so a shape change in the
  patching lemma does not block the assembly.
- **The verbatim name is free.** `WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`
  is declared nowhere in the port; its `Theorems/` wrapper is already in `SOURCES`,
  and `PORT_FILES` already lists this module (SET 4 may add the declaration here or
  in a new module — if new, list it in `PORT_FILES`). The `OWN_PROOFS` entry covers
  only the `…_of_patchingLevel` spelling.
- **Build budget:** this module and its dependencies are 4–9 s; the T side still has
  no heavy file (`HeckeLocal` at 41 s remains the largest in the tree).

# SET 4 — the patching descent-and-freeness engine (T12)

**Status: complete.** The fourth theorem set above the T11 definition layer and the
first half of the patching cluster: `Algebra.PatchingLevel.free_and_ker_eq_span`,
the node that turns an `Algebra.PatchingLevel 𝒪 r R M ⊥` into the three hypotheses
SET 3 froze (`Module.Free R M`, zero annihilator, the kernel description), with the
two `smul_eq` engine lemmas and the freeness-from-a-regular-sequence lemma it needs.
The work order is
[TOPIC-t12-set4-patching-descent.md](../topics/hecke/TOPIC-t12-set4-patching-descent.md);
the driver plan is [studies/t-side-driver.md](../../studies/t-side-driver.md) §2, §4;
the mathematics is [math/018-t-side-definitions.md](../../math/018-t-side-definitions.md)
§5. FLT is pinned at `aa2d8b3`; mathlib at `v4.34.0`.

## 24. What shipped

| pin source (lines) | port module | port lines | public / private |
|---|---|---:|---|
| `S_RingHom_bijective_of_surjective_of_smul_eq` (13) + `S_Module_Free_of_surjective_of_smul_eq` (22) | `FLTForHuman/Algebra/FaithfulFreeness.lean` | 59 | 2 / 0 |
| `S_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal` (98) | `FLTForHuman/Algebra/RegularSequenceFreeness.lean` | 149 | 1 / 3 |
| `S_MvPowerSeries_isRegular_C_cons_X` (280) + `S_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero` (326)† | `FLTForHuman/Algebra/MvPowerSeriesRegular.lean` | 390 | 3 / 19 |
| `S_Algebra_PatchingLevel_free_and_ker_eq_span` (310) | `FLTForHuman/Patching/LevelDescent.lean` | 351 | 1 / 36 |
| **total** | | **949** | **7 / 58** |

The public surface is exactly the four §0 statements of the work order plus the
three `MvPowerSeries.*` facts `free_and_ker_eq_span` imports and uses (§26). Every
`OnePrime`/`PDescent`/`vanishIdeal` helper is `private`, so the checker's
public-surface diff is exact and no `OWN_PROOFS` entry was needed.

† The `isNoetherianRing_of_finite` fourth fact is *not* ported: `MvPowerSeries`'s
`IsNoetherianRing` instance is now mathlib's (`MvPowerSeries.instIsNoetherianRing`,
`Mathlib/RingTheory/MvPowerSeries/Equiv.lean`), so `LevelDescent.free_N` uses
`inferInstance`.

## 25. Deduplication and reuse (playbook §2)

**The `smul_eq` bijectivity is proved once.** The pin's
`S_Module_Free_of_surjective_of_smul_eq.lean` carries a private
`FrobChareqDock.bijective_aux` (pin lines 7–16) that is **byte-identical** to
`S_RingHom_bijective_of_surjective_of_smul_eq.lean`'s `solution` (pin lines 7–13).
The port proves `RingHom.bijective_of_surjective_of_smul_eq` once and derives
`Module.Free T N` from it through `Module.Free.of_basis` +
`RingEquiv.ofBijective` (the pin's own `Free` `solution` already took exactly this
route); the duplicate `bijective_aux` is not ported. Saved: 10 pin lines, and one
fewer proof to keep in sync.

**The `OnePrime` projective-dimension block was `#check`ed against mathlib before
porting.** Six of its ingredients are already mathlib and are called directly:
`ModuleCat.projectiveDimension_quotient_eq_length`,
`ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular`,
`projective_iff_hasProjectiveDimensionLT_one`, `IsProjective.iff_projective`,
`Module.Projective.of_equiv`, `Module.Flat.of_projective`,
`Module.free_of_flat_of_isLocalRing`, `hasProjectiveDimensionLT_of_iso`,
`hasProjectiveDimensionLT_of_ge` and
`ShortComplex.ShortExact.hasProjectiveDimensionLT_X₂`. Only two members are
mathlib-absent and are kept: `hasProjectiveDimensionLT_of_isFiniteLength` (the
induction over mathlib's `IsFiniteLength`; mathlib has no
`IsFiniteLength → projectiveDimension` lemma) and `le_zero_of_add_natCast_le`
(`WithBot ℕ∞` arithmetic). `free_of_hasProjectiveDimensionLT_one` is a six-line
derivation from the mathlib API, not a re-proof. **No `maxHeartbeats` was added or
raised.**

**The `MvPowerSeries` `vanishIdeal` engine is written once.** The pin declares the
whole development (the `vanishIdeal` ideal, its 15 helpers, and the two targets
`isRegular_X_append_C`/`ofList_X_append_C_eq_maximalIdeal`) in
`S_MvPowerSeries_isRegular_C_cons_X.lean`, and **repeats** its two conclusion
lemmas' development in `S_MvPowerSeries_ofList_C_cons_X_eq_maximalIdeal.lean`. The
port writes it once, privately, in `MvPowerSeriesRegular.lean`, and `isRegular_C_cons_X`
and `ofList_C_cons_X_eq_maximalIdeal` are thin permutations of it. The pin's
`isNoetherianRing_of_finite` (a 107-line port of a proof now superseded) is
dropped for the mathlib instance.

**The `PDescent` block stays `private`** (work order §2): all 36 declarations
(`I`, `I_le_ker`, `ker_π_iff`, `theta`/`theta_apply`/`theta_smul`,
`theta_injective`/`theta_bijective`/`thetaEquiv`, `span_range_b`, `finite_N`,
`isWeaklyRegular_s`, `isFiniteLength_quotient`, `free_N`, `ker_le_I`, `free_M`, …)
are invisible to the checker, which sees exactly one public declaration in the
module. `free_M`'s structure (freeness of `N` over `B`, then the span/independence
argument for `R`) is kept as the pin wrote it.

## 26. Deviation: the node is **not** independent of SET 5

Work order §0 states that all four nodes are "self-contained (mathlib plus T11's
`PatchingDatum`), so this set is independent of SET 5". That premise is false:
`S_Algebra_PatchingLevel_free_and_ker_eq_span.lean` imports and uses **four**
`MvPowerSeries.*` lemmas, three of which are among the six the work order assigns
to SET 5:

| pin lemma | use in `free_and_ker_eq_span` | disposition |
|---|---|---|
| `MvPowerSeries.isRegular_C_cons_X` (S 280) | `isWeaklyRegular_s`, `free_N` | ported publicly (pin name) |
| `MvPowerSeries.ofList_C_cons_X_eq_maximalIdeal` (S 280) | `free_N` | ported publicly (pin name) |
| `MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero` (S 326) | `sub_C_constantCoeff_mem_span_X` | ported publicly (pin name) |
| `MvPowerSeries.isNoetherianRing_of_finite` (S 107) | `free_N` | **mathlib instance**, not ported |

Since the descent cannot build without them, the three absent ones are ported in
the new module `FLTForHuman/Algebra/MvPowerSeriesRegular.lean` and wired into
`SOURCES`/`PORT_FILES` alongside the four §0 wrappers. This is the one structural
deviation from the work order's three-module layout of §1; it is recorded here and
in `README.md`. SET 5 should extend `MvPowerSeriesRegular.lean` (and reuse its
`vanishIdeal` engine) rather than re-derive it — the two pin `S_` files are
byte-identical in that region.

## 27. Wiring

`spec/check_flt_statements.py` gained the four §0 `Theorems/` wrappers **and** the
three `MvPowerSeries` wrappers in `SOURCES` (all appended last; every last name is
unique in the pin, so no earlier match can flip), the four port modules in
`PORT_FILES`, and **no** `OWN_PROOFS` entry: all seven public declarations have a
pin wrapper and verify by direct name match. The `isRegular_C_cons_X` and
`ofList_C_cons_X_eq_maximalIdeal` wrappers are the statement authority over the
pin's two duplicated `S_` copies.

The consumer is the new [spec/TsideSet4Consumer.lean](../spec/TsideSet4Consumer.lean),
importing four new modules. Zone `[descent]` **builds** an
`Algebra.PatchingLevel 𝒪 0 (MvPowerSeries (Fin 0) 𝒪) (MvPowerSeries (Fin 0) 𝒪) ⊥`
over a DVR (the `r = 0` level of T11's consumer, where the power-series ring is the
base ring) and applies `Algebra.PatchingLevel.free_and_ker_eq_span` to read off all
three outputs. Zone `[engine]` is the cross-module composition (no `#check`s, no
`sorry`): it applies `free_and_ker_eq_span` to an abstract `L : PatchingLevel 𝒪 r R M ⊥`
and hands the resulting `Module.Free R M` instance to
`RingHom.bijective_of_surjective_of_smul_eq`, so a compatible surjection `g : R →+* T`
is bijective. Zone `[regular]` keeps `RegularSequenceFreeness` on the import path
as a live dependency. Deleting any of `LevelDescent.lean`, `FaithfulFreeness.lean`
or `RegularSequenceFreeness.lean` fails the file.

## 28. Verification

Measured, in order.

| command | result |
|---|---|
| `timeout 60 lake env lean <file>` per module | green and warning-free, 2.8–5.4 s each |
| `timeout 90 lake build <module>` per module | green, 3.4 s / 4.9 s / 5.0 s / 6.6 s |
| `timeout 180 lake build` | `Build completed successfully (4634 jobs).` (3 s, replayed) |
| `python3 spec/check_flt_statements.py` | `1647 statements identical (91 promoted from pin-private declarations), 0 mismatched, 0 missing, 28 own-proof declarations exempted (1675 port declarations checked)` |
| `lake env lean spec/TsideSet4Consumer.lean 2>&1 \| grep -c error` | `0` (3.8 s, warning-free) |

Before this set the checker read `1640 identical, 0 mismatched, 0 missing, 28
exempted, 1668 checked`; the delta is `+7 identical`, `+7 checked` — exactly the
seven new public declarations (four §0 statements plus the three `MvPowerSeries`
facts). The checker was verified by mutating one token of the headline
(`IsDiscreteValuationRing` → `IsDiscreteValuationRingX` in the
`free_and_ker_eq_span` binder): it reported
`1646 statements identical …, 1 mismatched, 0 missing, 28 own-proof declarations
exempted (1675 port declarations checked)`, and the mutation was reverted.

`#print axioms` (the two §5 headlines and the other five public declarations):

```
'Algebra.PatchingLevel.free_and_ker_eq_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'RingHom.bijective_of_surjective_of_smul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Module.Free.of_surjective_of_smul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'MvPowerSeries.isRegular_C_cons_X' depends on axioms: [propext, Classical.choice, Quot.sound]
'MvPowerSeries.ofList_C_cons_X_eq_maximalIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
'MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`: none of the four modules or the consumer contains `sorry`/`admit`,
and no `maxHeartbeats`/`maxRecDepth`/`synthInstance.maxHeartbeats` is set anywhere.
The one file-scope linter suppression is `linter.style.haveILetI false` in
`LevelDescent.lean` (the pin's `haveI`/`letI` instance walls are transcribed
verbatim, the established port convention).

## 29. Friction log (kept during the port, playbook §3.10)

1. **The work order's SET-4/SET-5 split does not follow the pin's import graph**
   (§26). This is the set's one structural cost: the `MvPowerSeries` facts are not
   optional and are not in mathlib. The pin's own `S_MvPowerSeries_ofList_…` file
   duplicates the `vanishIdeal` engine, so porting it once is also a dedup — but
   SET 5's plan should be re-scoped from "six `MvPowerSeries` lemmas" to "the three
   remaining power-series facts plus `IsAdicComplete.map_of_surjective`".
2. **`ENat` deprecations (v4.34, since 2026-07-17).** The pin's
   `le_zero_of_add_natCast_le` uses `ENat.coe_add`, `ENat.coe_le_coe` and
   `ENat.coe_lt_top`; the port writes `ENat.natCast_add`, `ENat.natCast_le_natCast`
   and `ENat.natCast_lt_top`. (Note `ℕ∞ = ENat = WithTop ℕ`, while the projective
   dimension lives in `WithBot ℕ∞` — the two are different types, and the pin's
   proof mixes `WithBot.coe_*` and `ENat.*` deliberately.)
3. **`Module.Finite.of_restrict_scalars_finite` → `of_restrictScalars_finite`**
   (playbook §4), one occurrence in `LevelDescent.isFiniteLength_quotient`.
4. **`linter.style.haveILetI` fires on the pin's `haveI`/`letI` in `Prop` goals**
   in `LevelDescent`, as in every other ported proof file; suppressed at file scope
   rather than deleting load-bearing instance introductions. The two isolated
   occurrences in `RegularSequenceFreeness` (`have` for `HasProjectiveDimensionLT`)
   and `MvPowerSeriesRegular` (`have` for `Fintype.ofFinite`) were converted, since
   the linter's suggestion is safe there.
5. **The `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` rename** (playbook §4)
   fires four times in the `MvPowerSeries` proofs.
6. **`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`** (playbook §4) in `setOf_mem_take_ofFn`.
7. **The projective-dimension `Shrink`/`ULift` universe bookkeeping is delicate but
   unchanged from the pin**: `OnePrime.hasProjectiveDimensionLT_of_isFiniteLength`
   needs `[Small.{w} R]`, and the `solution` bridges `ULift.{u} M`'s finite-length
   quotient to `M`'s with `Submodule.Quotient.equiv`, exactly as the pin wrote it.

## 30. Hand-off to SET 5 (the power-series patching algebra)

- **Three of SET 5's six `MvPowerSeries.*` lemmas are already done**, publicly and
  checker-verified, in `FLTForHuman/Algebra/MvPowerSeriesRegular.lean`:
  `isRegular_C_cons_X`, `ofList_C_cons_X_eq_maximalIdeal`, and
  `mem_pow_span_X_of_coeff_eq_zero`. The fourth, `isNoetherianRing_of_finite`, is
  mathlib's instance. **Do not re-port or re-derive them.** The `vanishIdeal` engine
  is `private` there and can be reused by extending the module (or promoting it) —
  the pin declares it in two byte-identical copies.
- **What remains on SET 5's list** is the rest of the power-series patching algebra
  for `nonempty_patchingLevel_bot`: `isAdicComplete_maximalIdeal`,
  `residue_comp_C_surjective`, and `IsAdicComplete.map_of_surjective` (the pin's
  `S_MvPowerSeries_isAdicComplete_maximalIdeal`, `…_residue_comp_C_surjective`,
  `S_IsAdicComplete_map_of_surjective`). `isNoetherianRing_of_finite` is free.
- **The three frozen hypotheses are now produced.** SET 6's verbatim unconditional
  `WeierstrassCurve.isModularModelOfLevel_of_patchingDatum` recovers the pin's
  binder block by `obtain ⟨hfree, hann, hker⟩ := L.free_and_ker_eq_span` at the
  call site of `WeierstrassCurve.isModularModelOfLevel_of_patchingLevel` (SET 3),
  exactly as the hand-off §23 anticipated.
- **Build budget:** the four modules are 3–7 s each; none is heavy. `HeckeLocal`
  (41 s) remains the largest file in the tree.


# SET 5 — the power-series patching algebra (T12)

**Status: complete.** The fifth theorem set above the T11 definition layer and the
second half of the patching cluster: the three remaining power-series/adic facts
`Algebra.PatchingDatum.nonempty_patchingLevel_bot` consumes —
`MvPowerSeries.residue_comp_C_surjective`,
`MvPowerSeries.isAdicComplete_maximalIdeal` and `IsAdicComplete.map_of_surjective`.
The work order is
[TOPIC-t12-set5-power-series-algebra.md](../topics/hecke/TOPIC-t12-set5-power-series-algebra.md);
the re-scope it implements is §30 above; the driver plan is
[studies/t-side-driver.md](../../studies/t-side-driver.md) §2, §4. FLT is pinned at
`aa2d8b3`; mathlib at `v4.34.0`.

## 31. What shipped

| pin source (lines) | port module | port lines | public / private |
|---|---|---:|---|
| `S_MvPowerSeries_residue_comp_C_surjective` (114) + `S_MvPowerSeries_isAdicComplete_maximalIdeal` (234) | `FLTForHuman/Algebra/MvPowerSeriesRegular.lean` (extended) | 390 → **687** | +2 / +15 |
| `S_IsAdicComplete_map_of_surjective` (86) | `FLTForHuman/Algebra/AdicCompleteMap.lean` (new) | **98** | 1 / 2 |
| `S_Algebra_PatchingDatum_bijective_and_free_of_surjective` (31) | `spec/TsideSet5Consumer.lean` (consumer, not in a library) | 73 | — |
| **total (library)** | | **395 new lines** | **3 / 17** |

The public surface is exactly the three §0 statements. Every helper — the factored
`dropVar`/`coeff_dropVar`, `maximalIdeal_eq_comap`,
`mem_span_X_of_constantCoeff_eq_zero`, `maximalIdeal_eq_map_C_sup_span_X`,
`smodEq_pow_smul_top_iff`, `sub_truncTotal_mem_pow_span_X`, the whole `LocalCoeff`
block (`coeff_mem_pow_of_mem_pow`, `C_mem_pow`, `span_X_le`,
`monomial_one_mem_pow`, `monomial_mem_pow`, `mem_pow_of_coeff_mem_pow`,
`isAdicComplete_maximalIdeal`) and `residue_comp_C_surjective` — is `private`, so
the checker's public-surface diff is exact and no `OWN_PROOFS` entry was needed.
The pin's fourth `MvPowerSeries` fact, `isNoetherianRing_of_finite`, is **not**
ported (mathlib's `MvPowerSeries.instIsNoetherianRing`), so its `Theorems/`
wrapper is not in `SOURCES`.

## 32. Deduplication (playbook §2)

**The `dropVar` argument is now one definition used three times.** SET 4 had left
the pin's `dropVar`/`coeff_dropVar` *inline* inside the public
`mem_pow_span_X_of_coeff_eq_zero` (the `let dropVar`/`hdrop` pair). SET 5 factors
it into a private `dropVar`/`coeff_dropVar` in `MvPowerSeriesReg`; the public
theorem now calls `MvPowerSeriesReg.dropVar i ψ`, and the two proofs added by this
set (`mem_span_X_of_constantCoeff_eq_zero` and the `LocalCoeff` block) use the same
definition. This removes the pin's four `dropVar` copies (two `def`s in
`S_MvPowerSeries_isAdicComplete_maximalIdeal`/`S_MvPowerSeries_residue_comp_C_surjective`
plus the two inline copies in the `mem_pow_span`-style inductions).

**`maximalIdeal_eq_comap` is proved once.** The pin declares it, identically, in
both `S_MvPowerSeries_isAdicComplete_maximalIdeal.lean` (lines 21–25) and
`S_MvPowerSeries_residue_comp_C_surjective.lean` (lines 16–20); the port keeps one
private copy.

**Pin lines saved:** `maximalIdeal_eq_comap` 5 lines and
`dropVar`/`coeff_dropVar` 4 lines (each written once instead of the pin's two
copies), plus the inline `dropVar` argument that SET 4 had embedded in
`mem_pow_span_X_of_coeff_eq_zero` — one private definition now serves all three
uses.

**`smodEq_pow_smul_top_iff` is stated twice, deliberately.** The four-line helper
occurs in `S_MvPowerSeries_isAdicComplete_maximalIdeal.lean` (line 17) and
`S_IsAdicComplete_map_of_surjective.lean` (line 18). Work order §2 allows the two
copies when the module split makes sharing awkward; sharing here would force
`AdicCompleteMap.lean` (generic algebra, import
`Mathlib.RingTheory.AdicCompletion.Noetherian` only) to import the whole
`MvPowerSeriesRegular` cone, so the helper is written once per module. This is the
one exception to "write each helper once" in this set.

**No new `OWN_PROOFS` entry.** `maximalIdeal_eq_map_C_sup_span_X` is transcribed
(and private, so invisible to the checker); everything public has a pin wrapper.

## 33. Wiring

`spec/check_flt_statements.py` appends the three §0 `Theorems/` wrappers to
`SOURCES` (all appended last; every last name is unique in the pin, so no earlier
match can flip) and adds `FLTForHuman/Algebra/AdicCompleteMap.lean` to
`PORT_FILES` (`MvPowerSeriesRegular.lean` is already listed). The pin's
`Theorems/Thm_MvPowerSeries_isNoetherianRing_of_finite.lean` is **not** added, per
work order §4.

The consumer is the new [spec/TsideSet5Consumer.lean](../spec/TsideSet5Consumer.lean),
importing the two new modules. Zone `[fact]` instantiates
`isAdicComplete_maximalIdeal` at a DVR (with `[IsAdicComplete (maximalIdeal 𝒪) 𝒪]`
as a hypothesis — a DVR need not be adically complete); zone `[residue]` reads off
`residue_comp_C_surjective`; zone `[compose]` is the cross-module composition: the
completeness instance produced by `isAdicComplete_maximalIdeal` is handed to
`IsAdicComplete.map_of_surjective` applied to the residue map, whose surjectivity is
*derived* from `residue_comp_C_surjective` via `Function.Surjective.of_comp`
(`residue ∘ C` surjective ⇒ `residue` surjective). No `#check`s, no `sorry`:
deleting either new module fails the file.

## 34. Verification

Measured, in order.

| command | result |
|---|---|
| `timeout 60 lake env lean FLTForHuman/Algebra/MvPowerSeriesRegular.lean` | green and warning-free, 5.8 s |
| `timeout 90 lake build FLTForHuman.Algebra.MvPowerSeriesRegular` | green, 5.3 s / 2253 jobs |
| `timeout 60 lake env lean FLTForHuman/Algebra/AdicCompleteMap.lean` | green and warning-free, 1.7 s |
| `timeout 90 lake build FLTForHuman.Algebra.AdicCompleteMap` | green, 3.2 s / 2075 jobs |
| `timeout 180 lake build` | `Build completed successfully (4635 jobs).` (8.7 s) |
| `python3 spec/check_flt_statements.py` | `1650 statements identical (91 promoted from pin-private declarations), 0 mismatched, 0 missing, 28 own-proof declarations exempted (1678 port declarations checked)` |
| `lake env lean spec/TsideSet5Consumer.lean 2>&1 \| grep -c error` | `0` (3.4 s, warning-free) |

Before this set the checker read `1647 identical, 0 mismatched, 0 missing, 28
exempted, 1675 checked`; the delta is `+3 identical`, `+3 checked` — exactly the
three new public declarations. The checker was verified by mutating one token of
`map_of_surjective` (`[IsNoetherianRing R]` → `[IsNoetherianRingX R]`): it reported
`1649 statements identical …, 1 mismatched, 0 missing, 28 own-proof declarations
exempted (1678 port declarations checked)`, and the mutation was reverted.

`#print axioms` (the three §5 headlines):

```
'MvPowerSeries.residue_comp_C_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'MvPowerSeries.isAdicComplete_maximalIdeal' depends on axioms: [propext, Classical.choice, Quot.sound]
'IsAdicComplete.map_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Import weight.** SET 5 adds exactly two imports to
`MvPowerSeriesRegular.lean` (`Mathlib.RingTheory.MvPowerSeries.Trunc`,
`Mathlib.RingTheory.AdicCompletion.Noetherian`) and one to `AdicCompleteMap.lean`.
The full build moved from SET 4's 4634 to **4635** jobs — the one new module; the
added imports were already in the graph. No `sorry`/`admit`, no
`maxHeartbeats`/`maxRecDepth`, no file-scope linter suppression; the
`linter.style.haveILetI` warnings were avoided by converting the pin's `haveI`s to
`have`s (see §35.3).

## 35. Friction log (kept during the port, playbook §3.10)

1. **`MvPowerSeries` is a non-reducible `def`, so the pin's `∃` witness does not
   elaborate.** In `isAdicComplete_maximalIdeal` the pin writes
   `refine ⟨fun m => c m, fun n => ?_⟩` against `∃ L : MvPowerSeries σ R, …`.
   Under v4.34 that leaves the witness as `(σ →₀ ℕ) → R` and every later tactic
   on `g n - L` is ill-typed ("`fun m => c m` has type `(σ →₀ ℕ) → R` but is
   expected to have type `MvPowerSeries σ R`"); an ascription inside the anonymous
   constructor does not survive. The fix is to bind the witness first —
   `let L : MvPowerSeries σ R := fun m => c m` — and then `refine ⟨L, …⟩`. This is
   the playbook §3.7 class of shape mismatch (a `def` that `rw`/elaboration will
   not unfold), not a bug in the mathematics.
2. **`rw [smodEq_pow_smul_top_iff]` fails on the `MvPowerSeries`-valued goal.** On
   the base-ring goals (the `IsPrecomplete.prec` Cauchy proof) the same lemma
   rewrites fine, but on `g n ≡ L [SMOD 𝔐^n • ⊤]` `rw` reports "did not find an
   occurrence" with a note about implicit transparency. The explicit application
   `(smodEq_pow_smul_top_iff 𝔐 n (g n) L).mpr` works. (The pin's `rw` compiled on
   Lean 4.33.1 / mathlib v4.33.0; this is v4.34 elaboration drift.)
3. **`have`/`haveI` and the `IsAdicComplete` constructor.** The pin builds
   `IsAdicComplete` with `haveI : IsHausdorff …` / `haveI : IsPrecomplete …` then
   `exact ⟨⟩`. `IsAdicComplete.mk` has no explicit fields (the `extends` fields are
   instance-implicit), so `exact ⟨hH, hP⟩` is rejected; and `haveI` in a `Prop` goal
   trips `linter.style.haveILetI`. Plain `have`s *are* found by instance search, so
   the port uses `have hH`/`have hP` plus `exact ⟨⟩` — warning-free, no file-scope
   suppression. The same conversion applies to `haveI := Fintype.ofFinite σ`
   (playbook §4).
4. **`Finsupp.finite_of_degree_lt` must be qualified.** The pin's `open Finsupp`
   is not in `MvPowerSeriesRegular.lean` (it opens `MvPowerSeries` and, in the new
   block, `IsLocalRing`), so the `LocalCoeff` truncation proof writes
   `(Finsupp.finite_of_degree_lt (σ := σ) n).toFinset`.
5. **`if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`** (playbook §4) fires in
   `mem_span_X_of_constantCoeff_eq_zero` and `monomial_one_mem_pow`, as in the
   SET-4 `MvPowerSeries` proofs.
6. **A DVR supplies `IsLocalRing` and `IsNoetherianRing` by instance search**, so
   the consumer can instantiate `isAdicComplete_maximalIdeal` and then
   `map_of_surjective` with no named instance lemmas (no
   `IsDiscreteValuationRing.isNoetherianRing`).
7. **`AdicCompletion.Noetherian` alone is enough** for the generic module:
   `IsAdicComplete.le_jacobson_bot` lives in `AdicCompletion.Basic`, and
   `isNoetherianRing_of_surjective`, `Ideal.mem_map_iff_of_surjective`,
   `Ideal.mem_jacobson_bot` come transitively; the 2075-job module is lighter than
   `MvPowerSeriesRegular.lean`'s 2253.

## 36. Hand-off to SET 6 (the abstract patching exit and the verbatim assembly)

- **The three frozen facts are produced.** `nonempty_patchingLevel_bot` uses
  `MvPowerSeries.isAdicComplete_maximalIdeal` (pin lines 2583, 2866),
  `MvPowerSeries.residue_comp_C_surjective` (2597) and
  `IsAdicComplete.map_of_surjective` (3581); all three are now public, and the
  `Theorems/` wrappers are in `SOURCES`.
- **`MvPowerSeries.isNoetherianRing_of_finite` is used *by name* four times** in
  `S_Algebra_PatchingDatum_nonempty_patchingLevel_bot.lean` (lines 2573, 2861,
  3558, 3574, each with a type ascription). That name does **not** exist in the
  port — replace each with `inferInstance` (or
  `(inferInstance : IsNoetherianRing (MvPowerSeries (Fin r) 𝒪))`), which needs
  `[IsNoetherianRing 𝒪]`. This is the single biggest mechanical drift risk in SET 6.
- **Nothing needs promoting from SET 5's private block.** SET 6's pin file declares
  its own `mem_span_X_of_constantCoeff_eq_zero` (line 2672) and never uses
  `dropVar`, `maximalIdeal_eq_comap` or `smodEq_pow_smul_top_iff`; the private
  helpers here are invisible to it by design, and its own copies should stay
  private in its module.
- **The abstract patching exit** is
  `S_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean` (31 lines): it is
  `obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hℓ`, `L.free_and_ker_eq_span`,
  `bijective_of_surjective_of_smul_eq`, `Module.Free.of_surjective_of_smul_eq`,
  then the quotient `AlgEquiv` assembly
  `(Ideal.quotientEquivAlgOfEq 𝒪 hker.symm).trans
  (Ideal.quotientKerAlgEquivOfSurjective L.ψ_surjective)).trans
  (AlgEquiv.ofBijective RtoT hbij)`. All four inputs are already public
  (SET 4's descent and `bijective_of_surjective_of_smul_eq`, this set's
  `nonempty_patchingLevel_bot`).
- **The verbatim unconditional assembly** is
  `S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean` (145 lines):
  SET 3 already ported its *conditional* form (`…_of_patchingLevel`,
  `FLTForHuman/WeierstrassCurve/ModularityLifting.lean`), so SET 6 discharges the
  three frozen hypotheses by `obtain ⟨hfree, hann, hker⟩ := L.free_and_ker_eq_span`
  at the call site rather than re-proving the assembly.
- **Budget.** The 3,789-line `S_Algebra_PatchingDatum_nonempty_patchingLevel_bot`
  carries 102 `namespace`/`end` pairs of private scaffolding; bisect it (the
  helper block around lines 2550–2900 and the `isNoetherianRing_R`/`isAdicComplete_R`
  tail around 3550–3600 are the load-bearing parts). Everything is mathlib-only
  plus the three SET-5 facts; no new heavy import is expected.

## 37. SET 6 — the patching construction

**Status: complete.** `Algebra.PatchingDatum.nonempty_patchingLevel_bot` is
ported into the single module `FLTForHuman/Patching/PatchingConstruction.lean`
(3,761 lines). One public declaration; everything below it is `private`.

### 37.1 What shipped

| pin source (lines) | port module | port lines | public / private |
|---|---|---:|---|
| `S_Algebra_PatchingDatum_nonempty_patchingLevel_bot` (3,789; 3,660 after the 129 `p2m_*` lines) | `FLTForHuman/Patching/PatchingConstruction.lean` | **3,761** | 1 / ~370 |

All five milestones of work order §3 landed: `PCPortSpine0`–`11`, the
`UltraProduct`/`PatchingAlgebra`/`PatchingModule`/`IsPatchingSystem` carriers, the
type-cardinality/functorial machinery, `FrobDictPC.{Coeff,Input,Bφ,viaφ,Base}`,
`FrobDictPC.Limit.{ConstEquiv,LimHom,LimMap,Semilinear,Concrete(PiInf,PsiInf)}`,
`patchedLevelMain`, `trivialLevel`, `solution`. The public statement is the
`Theorems/` wrapper verbatim.

**Wiring.** `Theorems/Thm_Algebra_PatchingDatum_nonempty_patchingLevel_bot.lean`
is appended to `SOURCES` and `FLTForHuman/Patching/PatchingConstruction.lean` to
`PORT_FILES` (both last; the last name is unique in the pin). No `OWN_PROOFS`
entry was needed — the checker's public surface is exactly the one headline.

### 37.2 Deduplication (playbook §2)

No dedup was applied: the pin's ~370 scaffolding declarations each occur once, so
there is no repeated lemma to generalise. The one `dropVar`-style repetition SET 4
factored (`MvPowerSeriesReg.dropVar`) is not used by this file; the pin declares
its own `mem_span_X_of_constantCoeff_eq_zero` (line 2672) and never calls the
SET-5 private helpers.

### 37.3 Verification

Measured, in order.

| command | result |
|---|---|
| `timeout 150 lake env lean FLTForHuman/Patching/PatchingConstruction.lean` | green, warning-free, **53.4 s** |
| `timeout 180 lake build FLTForHuman.Patching.PatchingConstruction` | green, **2726 jobs**, 64 s (module step 54 s) |
| `timeout 180 lake build` | `Build completed successfully (4642 jobs).` (59 s) |
| `python3 spec/check_flt_statements.py` | `1651 statements identical (91 promoted from pin-private declarations), 0 mismatched, 0 missing, 28 own-proof declarations exempted (1679 port declarations checked)` |

The checker was verified by mutating `Nonempty` to `NonemptyX` in the public
statement: it reported `1650 statements identical …, 1 mismatched, 0 missing, 28
own-proof declarations exempted (1679 port declarations checked)`, and the mutation
was reverted. The delta from SET 5's close (`1650 identical / 1678 checked`) is
`+1 identical / +1 checked` — exactly the one new public declaration.

`#print axioms`:

```
'Algebra.PatchingDatum.nonempty_patchingLevel_bot' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Import weight.** The pin's 46 specific mathlib modules are kept as written; the
only import changes are `Definitions.Def_Algebra_PatchingDatum` →
`FLTForHuman/Patching/Defs/PatchingDatum`, the three `Theorems/Thm_MvPowerSeries_*`
and `Theorems/Thm_IsAdicComplete_map_of_surjective` wrappers → the two SET-4/5
modules `MvPowerSeriesRegular`/`AdicCompleteMap`, and the dropped
`P2M.Util`/`Thm_MvPowerSeries_isNoetherianRing_of_finite`. Full `lake build` moved
from SET 5's 4,635 to **4,642** jobs — the one new module plus the
`Mathlib.RingTheory.Ideal.Over` transitives it pulls (`Ideal.mem_under`).
No `sorry`/`admit`, no `maxHeartbeats`/`maxRecDepth` (the pin has none in this
file either — its project-wide bumps are not transcribed), and no file-scope
linter suppression beyond the two documented in §37.5(9).

**Build-clock note.** This module is the port's slowest: 53–62 s for
`lake env lean`, 54 s of `lake build`. That is cumulative, not a single blow-up —
the work order §3 bisection is: §0 4.5 s, +`Spine3`–`8` 30 s, +`Spine9/11` 50 s,
+`FrobDictPC`/`Limit` 53–62 s, and no declaration needs more than the default
heartbeat cap (the same file with the global `backward.isDefEq` compatibility
option removed still takes 62 s and simply fails, so that option is not the cost).
The expense is the ~370 private topology/typeclass declarations themselves; the
next session should not "fix" it by raising a cap.

### 37.4 Friction log (playbook §3.10)

1. **The pin's `S_` file does not elaborate standalone, and its `p2m_*` tooling is
   the reason.** The flattened file declares `theorem TwoSidedIdeal.span_le'` at
   top level and its body uses unqualified `span`/`subset_span`/`mem_span_iff`;
   `p2m_export` puts aliases in `PC.TwoSidedIdeal` (I verified with a local elab
   that `getCurrNamespace` inside `namespace TwoSidedIdeal p2m_export … end
   TwoSidedIdeal` is `PC.TwoSidedIdeal`, and that the aliases alone leave `span`
   unknown). The port therefore (a) turns `p2m_open "X …"` into `open`, (b) turns
   `p2m_open_scoped "X …" in` into a **local** `open X in` — local, so the
   `TwoSidedIdeal`/`Submodule`/`Pi` opens do not collide with each other across the
   file — and (c) moves the pin's `_root_.`-prefixed own declarations (the
   `Module.UniformlyBoundedRank`/`Algebra.UniformlyBoundedRank` classes and their
   lemmas, `FrobDictPC.πₗ`, `FrobDictPC.Limit.constEquiv`, `AlgHom.eq_constantCoeff_of_map_X`,
   the `IsLocalRing.Submodule`/`IsLocalRing.ResidueField`/`IsModuleTopology`
   helpers) into the port's own namespace, stripping the leading `_root_.<enclosing
   namespace>.` so the flattened references resolve. The first `p2m_*`-free build
   failed at `span` (pin 162) and at `bound` (pin 1473) exactly for these reasons.
2. **`backward.isDefEq.respectTransparency false` is load-bearing, file-wide.** The
   pin sets it itself in eleven places (819, 911, 956, 1134, 1919, 2022, 2176, 2258,
   2300, 2466, 3261, and `true in` at 3343) — so this is the pin's own behaviour,
   not a port hack. Without it `simp [hx₂, H]` at pin 544 fails:
   `Ideal.quotientMap (𝔪^i) (RingHom.id R) H` has `H : 𝔪^j ≤ 𝔪^i` but the
   application expects `𝔪^j ≤ (𝔪^i).comap (RingHom.id R)`, which is not defeq under
   the v4.34 default (implicit-transparency) matching, and
   `Ideal.quotientMap_mk` (a `@[simp]` lemma) then never fires. I also set
   `backward.isDefEq.respectTransparency.types false`; removing both still costs
   62 s and yields eleven errors, so the options are cheap.
3. **`OrderDual` is a non-reducible `def` in v4.34, so typeclass search no longer
   sees through `ιᵒᵈ`** — the same class as SET 5's `MvPowerSeries` deviation.
   Three fixes: name the dual element at `ι` before `Set (α i)` (pin 79); supply
   `Finite`/`Nonempty (f'.obj j)` at `OrderDual.ofDual j.1` (pin 109–121); state the
   `f'` `map_id` equation with `congrFun (hf₀ (Opposite.unop i)) x` because
   `simp [hf₀]` no longer matches the identity morphism's proof term.
4. **v4.34 changed the `Monoid`/`Group`/`Ring` structure layout**, so the pin's
   `.1.1.1` (`Monoid`) / `.1.1.1.1.1` (`Group`) / `(g.toMonoid, g.toAddMonoid)`
   (`Ring`) projection chains no longer name the multiplication (pin 624, 629,
   638). Replaced by `(g.mul : α → α → α)` / `((g.mul, g.add))` injections, with the
   `Ring` extensionality bullets ordered `add` then `mul`.
5. **`Equiv.module`/`Equiv.linearEquiv` became `AddEquiv.module`/`AddEquiv.linearEquiv`,
   and the transported `Fin` structure is a diamond** (pin 681, 684, 746, 764, 766).
   `Equiv.addEquiv`'s source addition is `e.add`, while `AddEquiv.module`'s ambient
   `[AddCommMonoid (Fin n)]` search picks `Fin.addCommMonoid` (or the `ZMod` ring's
   `AddCommMonoid`), so the structures are not the same instance. The port binds
   `letI hAC : AddCommGroup (Fin (Nat.card M)) := …` and passes the module/linear
   structure with explicit instances:
   `@AddEquiv.module R (Fin (Nat.card M)) M _ hAC.toAddCommMonoid _ _ (Equiv.addEquiv …)`.
   The `.symm.ring`/`.symm.algebra`/`.symm.algEquiv` uses needed no change.
6. **`TFAE.out` is 1-based in v4.34**: `.out 0 2` → `.out 1 3` (pin 557, 1272,
   2563, 2734). The old form is a `TFAE indices start at 1` error, not a rename.
7. **`congr(f $h)` no longer produces the expected equation.** In
   `Submodule.liftModIdealEquiv` (pin 1080, 1086) the pin's
   `simpa using congr(f.symm $hy)` / `congr(f $hy)` is replaced by
   `rw [hy, LinearEquiv.symm_apply_apply]` / `rw [hy, LinearEquiv.apply_symm_apply]`,
   with `Quotient.mk` qualified to `Submodule.Quotient.mk` (the pin's unqualified
   `Quotient.mk y` now reads `y` as the setoid).
8. **Renames, all drop-in**: `dif_pos` → `dite_eq_left` (seven uses: 1057, 1080,
   1086, 1093, 1595, 1606, 2141); `Set.mem_setOf`/`Set.mem_setOf_eq` →
   `Set.mem_ofPred`/`Set.mem_ofPred_eq`.
   `MvPowerSeries.isNoetherianRing_of_finite` → `inferInstance` (pin 2573, 2861,
   3558, 3574; two ascriptions and two `haveI`s), as SET 5's hand-off predicted.
   The pin's `MvPowerSeries.isAdicComplete_maximalIdeal`,
   `residue_comp_C_surjective`, `mem_pow_span_X_of_coeff_eq_zero` and
   `IsAdicComplete.map_of_surjective` are used unqualified and resolve directly.
9. **Two linter suppressions, both justified.** `linter.style.haveILetI false`
   (the pin's `haveI`/`letI` instance walls are transcribed verbatim, as in
   `LevelDescent.lean`); `linter.overlappingInstances false` because the pin's
   statements carry both `[IsTopologicalRing R]` and `[NonarchimedeanRing R]` and
   the work order forbids changing the statements. The port is warning-free with
   both.
10. **`@[scoped simp]` → `@[simp]` and `scoped instance` → `instance`.** The pin's
    `activateScoped` bookkeeping cannot be reproduced by a plain `open`, and since
    the declarations are all `private` in one module the scoped/global distinction
    has no effect on the public surface (the checker's `DECL_RE` does not match
    `scoped instance`, which is why the conversion exposed eight declarations for a
    first checker run: `IsPatchingSystem.isModuleQuotient`/`'`,
    `FrobDictPC.Input.isLocalHom_algHom`, `FrobDictPC.isPatchingSystem`,
    `FrobDictPC.Coeff.{algEquiv_apply,equiv_symm_apply_apply,equiv_apply_symm_apply}`,
    `FrobDictPC.ePA_apply`; all are now `private`).
11. **The checker reads the `private` modifier from the declaration's own line.**
    The pin writes `private noncomputable` on a line of its own before the keyword;
    the port merges the modifiers onto the declaration line (`private noncomputable
    instance …`) so the public-surface diff is exact.

### 37.5 Hand-off to SET 7

- **The frozen fact is produced.** `Algebra.PatchingDatum.nonempty_patchingLevel_bot`
  is public and `#print axioms`-clean; SET 7's abstract exit
  (`S_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean`) can be ported
  directly: `obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hℓ`, then
  `L.free_and_ker_eq_span` (SET 4) and `bijective_of_surjective_of_smul_eq`
  (SET 4), then the `AlgEquiv` assembly.
- **The verbatim unconditional assembly** is
  `S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean` (145 lines);
  SET 3 ported its conditional form in
  `FLTForHuman/WeierstrassCurve/ModularityLifting.lean`, so SET 7 only discharges
  the three frozen hypotheses at the call site.
- **Consumer written.** [spec/TsideSet6Consumer.lean](../spec/TsideSet6Consumer.lean)
  has three zones: `[apply]` applies the SET-6 headline to an arbitrary
  `Algebra.PatchingDatum`; `[compose]` is the wire test — the level produced by SET
  6 is handed to SET 4's `Algebra.PatchingLevel.free_and_ker_eq_span`, yielding
  `Module.Free R M ∧ Module.annihilator R M = ⊥ ∧ RingHom.ker L.ψ = Ideal.span …`;
  `[subsingleton]` exercises the other branch of the theorem's
  `subsingleton_or_nontrivial` split. It imports both modules, so deleting either
  fails it, and it runs at **0 errors**. Unlike the SET-5 consumer it does not
  construct a concrete datum: the pin's `PatchingDatum` fields are SET 7's assembly
  data, so what is checked here is the wire, not a concrete instantiation (recorded
  in the consumer's header).

## 38. SET 7 — the patching exit and the unconditional `R ≅ T` assembly

**Status: complete. The T-side driver is closed.** Two nodes / 176 pin lines: the
abstract patching exit `Algebra.PatchingDatum.bijective_and_free_of_surjective`
(new module `FLTForHuman/Patching/Exit.lean`, 31 pin lines) and the **verbatim
unconditional** `WeierstrassCurve.isModularModelOfLevel_of_patchingDatum` (145 pin
lines), added to the SET-3 module
`FLTForHuman/WeierstrassCurve/ModularityLifting.lean`.

### 38.1 What shipped

| pin source (lines) | port module | port lines | public / private |
|---|---|---:|---|
| `S_Algebra_PatchingDatum_bijective_and_free_of_surjective` (31) | `FLTForHuman/Patching/Exit.lean` | 64 | 1 / 0 |
| `S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum` (145) | `FLTForHuman/WeierstrassCurve/ModularityLifting.lean` (extended by 39 lines) | 240 | 2 / 0 |

Both statements are their `Theorems/` wrappers verbatim. Both proofs are pure
assembly, as work order §2 predicted — nothing was re-proved:

- **the exit** is the pin's four lines: `P.nonempty_patchingLevel_bot hℓ` (SET 6),
  `L.free_and_ker_eq_span` (SET 4),
  `(RtoT : R →+* T).bijective_of_surjective_of_smul_eq` and
  `Module.Free.of_surjective_of_smul_eq` (SET 4, `FaithfulFreeness`), and the
  quotient presentation `Ideal.quotientEquivAlgOfEq 𝒪 hker.symm` trans
  `Ideal.quotientKerAlgEquivOfSurjective L.ψ_surjective` trans
  `AlgEquiv.ofBijective RtoT hbij`. The extracted `hfree` is found by typeclass
  search as a local instance; `hann`/`hker` feed the two quotient steps.
- **the assembly** discharges SET 3's frozen `{r} (L) (hfree) (hann) (hker)`:
  `obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hp𝒪`, then
  `obtain ⟨hfree, hann, hker⟩ := L.free_and_ker_eq_span`, then the conditional
  `WeierstrassCurve.isModularModelOfLevel_of_patchingLevel` applied to them. The
  conditional's name is unchanged and its `OWN_PROOFS` entry is untouched.

**Wiring.**
`Theorems/Thm_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean` is
appended to `SOURCES` (last; its only last name is unique in the pin) and
`FLTForHuman/Patching/Exit.lean` to `PORT_FILES` (last).
`ModularityLifting.lean` is already in `PORT_FILES` (SET 3), and the verbatim
theorem's wrapper was registered there too, so the assembly needed no checker edit.
No `OWN_PROOFS` entry was added.

### 38.2 Verification

Measured, in order.

| command | result |
|---|---|
| `timeout 120 lake build FLTForHuman.Patching.PatchingConstruction` | olean current, **1.8 s** (no re-elaboration; §37 caveat) |
| `timeout 60 lake env lean FLTForHuman/Patching/Exit.lean` | green, warning-free, **3.4 s** |
| `timeout 60 lake env lean FLTForHuman/WeierstrassCurve/ModularityLifting.lean` | green, warning-free, **26.3 s** (import I/O of the 16 MB construction olean) |
| `timeout 90 lake build FLTForHuman.Patching.Exit FLTForHuman.WeierstrassCurve.ModularityLifting` | green, **4479 jobs**, 8.2 s / 10 s module steps |
| `timeout 180 lake build` | `Build completed successfully (4643 jobs).` (3.2 s replayed) |
| `python3 spec/check_flt_statements.py` | `1653 statements identical (91 promoted from pin-private declarations), 0 mismatched, 0 missing, 28 own-proof declarations exempted (1681 port declarations checked)` |

The checker was verified twice, one token per node: `Function.Bijective` →
`Function.BijectiveX` in `Exit.lean` and `N * ∏` → `N + ∏` in the assembly both
reported `1652 statements identical …, 1 mismatched, 0 missing, 28 own-proof
declarations exempted (1681 port declarations checked)`, and both mutations were
reverted. The delta from SET 6's close (`1651 identical / 1679 checked`) is
`+2 identical / +2 checked` — exactly the two new public declarations; the
conditional capstone stays `OWN_PROOFS`, so the exempted count is unchanged at 28.

`#print axioms` (the deliverable — the unconditional assembly is axiom-clean with
the 3,761-line patching construction on its import path):

```
'Algebra.PatchingDatum.bijective_and_free_of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.isModularModelOfLevel_of_patchingDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`/`admit`, no `maxHeartbeats`/`maxRecDepth`, no new linter suppression
beyond the two SET-3 file-scope options already in `ModularityLifting.lean` (both
the docstring blocks and the new declaration are warning-free).

### 38.3 Deviation from work order §1 (one necessary import)

The work order says `ModularityLifting.lean` "gains an import of
`FLTForHuman.Patching.PatchingConstruction`". That is not sufficient: the
assembly's second line is `L.free_and_ker_eq_span`, which is SET 4's declaration in
`FLTForHuman/Patching/LevelDescent.lean`, and `PatchingConstruction` does not
import `LevelDescent` (their import graphs meet only at
`Patching/Defs/PatchingDatum.lean`). The module therefore imports **both**
`FLTForHuman.Patching.PatchingConstruction` and
`FLTForHuman.Patching.LevelDescent` (an additive change in the sanctioned
extension). `Exit.lean` takes the work order's three imports plus
`Mathlib.RingTheory.Ideal.Quotient.Operations`, which the quotient presentation uses
directly and which the pin's own import block contains.

### 38.4 Consumer

[spec/TsideSet7Consumer.lean](../spec/TsideSet7Consumer.lean) has three zones.
`[exit]` applies the exit to an arbitrary patching datum, a compatible surjection
and its two side conditions. `[assembly]` applies the verbatim capstone to a full
T-side context (`DeformationRingData`, `HeckeGaloisRepDatum`, `φ`, and the datum
`P`). `[compose]` is the end-to-end composition: from the single datum `P` and map
`φ` it derives `Function.Surjective φ` with SET 1's
`surjective_of_isEquiv_baseChangeAlong`, runs the exit for `Function.Bijective φ`
and the freeness over both `R` and `T`, and runs the assembly for
`W.IsModularModelOfLevel …`, returning the conjunction. It imports both new/changed
modules (plus SET 1), so deleting any node fails it, and it runs at **0 errors**
(6.1 s).

### 38.5 Hand-off

Nothing outstanding: the driver of
[../../studies/t-side-driver.md](../../studies/t-side-driver.md) is complete. The
unconditional `R ≅ T` statement
(`WeierstrassCurve.isModularModelOfLevel_of_patchingDatum`) and the abstract
patching exit (`Algebra.PatchingDatum.bijective_and_free_of_surjective`) are both
public, verbatim to their wrappers, and axiom-clean.

