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
