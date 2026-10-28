# WORKORDER MC-5c — semisimple descent of a 2-dimensional mod-`p` representation

**SET**: [SET-MC5.md](SET-MC5.md) §0–§5. **Story**: M7. **Silk**: 403. **Net**: ≈363.
**Home**: **new** `lean/FLTForHuman/ModularCurve/ResidualDescent.lean` (not
`ResidualRealization.lean`, to keep it distinct from the def module `Defs/ResidualRealization.lean`).

## The declaration

Pin wrapper `Theorems/Thm_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.lean`:

```
theorem ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite
    {K L : Type} [Field K] [Field L] [Algebra K L] (M p : ℕ) [Fact p.Prime]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (k : Type) [Field k] [Finite k] (ι : k →+* Ω)
    (V : Type) [AddCommGroup V] [Module Ω V] (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[Ω] V))
    (hp : (p : Ω) = 0) (hV : Module.finrank Ω V = 2) (hfin : Finite ρ.range)
    (hirr : ∀ W : Submodule Ω V, (∀ σ, ∀ v ∈ W, ρ σ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ σ, LinearMap.trace Ω V (ρ σ).toLinearMap ∈ ι.range)
    (hdet : ∀ σ, LinearMap.det (ρ σ).toLinearMap ∈ ι.range)
    (hcyc : ModularCurve.CyclotomicDeterminant M p ρ) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module k V₀)
      (ρ₀ : (L ≃ₐ[K] L) →* (V₀ ≃ₗ[k] V₀)),
      Module.finrank k V₀ = 2 ∧
      ModularCurve.CyclotomicDeterminant M p ρ₀ ∧
      ρ.ker ≤ ρ₀.ker ∧
      (∀ σ, ι (LinearMap.trace k V₀ (ρ₀ σ).toLinearMap) = LinearMap.trace Ω V (ρ σ).toLinearMap) ∧
      (∀ σ, ι (LinearMap.det (ρ₀ σ).toLinearMap) = LinearMap.det (ρ σ).toLinearMap) ∧
      (∀ W : Submodule k V₀, (∀ σ, ∀ v ∈ W, ρ₀ σ v ∈ W) →
        ∃ W' : Submodule k V₀, (∀ σ, ∀ v ∈ W', ρ₀ σ v ∈ W') ∧ IsCompl W W')
```

Pin proof: `P2M/Sol/S_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite.lean`
(403 lines), assembling the three ported `Representation*` premises over `ι`'s range.

## Vocabulary

- `ModularCurve.CyclotomicDeterminant` — `ModularCurve/Defs/ResidualRealization.lean` (D7; import).
- The three premises (import their modules): `RepresentationTheory/SubfieldBasis.lean`,
  `RepresentationTheory/Burnside.lean`, `GaloisRep/Deformation/FiniteDescent.lean`.
- `IsCompl`, `LinearMap.trace`/`det` — mathlib.

## Traps

1. Transcribe the whole existential **and** all six conjuncts, with the anonymous instance binders
   (`(_ : AddCommGroup V₀) (_ : Module k V₀)`) exactly as the wrapper has them.
2. `hp : (p : Ω) = 0` is the characteristic-`p` hypothesis — do not replace it with `[CharP Ω p]`.
3. `hV`, `hirr`, `htr`, `hdet`, `hfin` are each consumed by one of the three premises; keep the
   pin's assembly order (the `exists_conj_eq_map_of_charpoly_coeff_mem_range…` one is the last).
4. The `ι`-embeddings of trace/determinant appear as `ι (… ) = …`; do not commute the sides.
5. Do not reproduce the pin's `attribute [-instance]`/`attribute [-simp]` preludes.

## Gates

As WORKORDER-MC5a's §Gates, with: `check_port` → the headline `ok`; **two** `spec-pin:` lines; one
module build; axioms; silent; no `set_option`; no other file.
