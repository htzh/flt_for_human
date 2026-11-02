/-
  Cross-module wire test for SET-AF7 (the big-cell expansion: a flat family's big cell is a sum
  of pure tensors).

  A `spec/` probe, not a library module. One zone, and it is a real composition, not a `#check`:
  the AF7 headline `AutomorphicForm.bigCell_eq_sum_pureTensor_of_flat_family` is **instantiated at
  the port's own flat family** `φ s := AutomorphicForm.FlatInducedSection.flatOne F s` (from
  `Adelic/InducedSectionFlat.lean`), with

  * the induced-section premise `_hφ` discharged by `isInducedSection_flatOne`, whose modulus
    hypothesis is the port's `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm`
    — the same pair AF7's own headline uses through its `let α`;
  * the archimedean `K`-finiteness premise `_hφK` discharged by `isArchKFinite_flatOne`;
  * the non-vanishing premise `_hφne` discharged at `(s, g) = (0, 1)` by `flatOne_apply_one`;
  * the continuity premise `_hφc` discharged by `continuous_flatOne`, from `Continuous (adelicHeight F)`.

  The two premises the port does *not* yet state for `flatOne` (`IsKfSmooth` and the flat-family
  condition on integral-row-isometric `k`) are hypotheses of the example, as the playbook prescribes
  for a concrete instantiation that needs unported hypotheses.

  The conclusion is read off the headline's existential at `μ = ν = 1` (so `μ * ν⁻¹ = 1`): the
  archimedean factor `Rr` of the expansion is the constant `1` on the positive part of every real
  place, and the shell parameter satisfies `1 ≤ m`.  Delete `BigCellExpansion.lean`, or either of the
  two `InducedSectionFlat` statements, and the example dies.

  The probe imports only the set's own module and the modules it consumes.
-/
import FLTForHuman.AutomorphicForm.Adelic.BigCellExpansion
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open NumberField.AdelicHeight NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

namespace SetAF7BigCellConsumer

variable {F : Type} [Field F] [NumberField F]

/-- Zone A: the AF7 headline applied to the port's flat family `flatOne F ·`, with the
induced-section, `K`-finiteness, continuity and non-vanishing premises discharged from
`InducedSectionFlat`; the archimedean factor of the resulting pure-tensor expansion is the constant
`1` at `μ = ν = 1`, and the shell parameter is at least one. -/
example (hH : Continuous (adelicHeight F))
    (hKf : ∀ s : ℂ, IsKfSmooth F (AutomorphicForm.FlatInducedSection.flatOne F s))
    (hflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      AutomorphicForm.FlatInducedSection.flatOne F s k
        = AutomorphicForm.FlatInducedSection.flatOne F s' k) :
    ∃ (m : ℕ) (Rr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ),
      1 ≤ m ∧
        ∀ (i : {w : InfinitePlace F // w.IsReal}) (u : (i.1.Completion)ˣ),
          0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
          Rr i (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion)) = 1 := by
  obtain ⟨S, n, c, kdat, abm, m, A, B, Rr, Rc, _h1, hm, _h3, _h4, _h5, _h6, hRr, _h8, _h9⟩ :=
    bigCell_eq_sum_pureTensor_of_flat_family F
      (fun _ => by
        rw [MonoidHom.coe_toHomUnits]
        exact MeasureTheory.distribHaarChar_pos)
      1 1 (fun s => AutomorphicForm.FlatInducedSection.flatOne F s)
      (fun s => AutomorphicForm.FlatInducedSection.isInducedSection_flatOne _
        (fun _ => by
          rw [MonoidHom.coe_toHomUnits]
          exact MeasureTheory.distribHaarChar_pos)
        (fun x => NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F x) s)
      (fun s => AutomorphicForm.FlatInducedSection.isArchKFinite_flatOne s)
      hKf
      (fun s => AutomorphicForm.FlatInducedSection.continuous_flatOne hH s)
      hflat
      ⟨0, 1, by
        rw [AutomorphicForm.FlatInducedSection.flatOne_apply_one]
        exact one_ne_zero⟩
  exact ⟨m, Rr, hm, fun i u hu => by
    -- `μ * ν⁻¹ = 1` at `μ = ν = 1`, so the archimedean factor is the constant `1`
    simpa using hRr i u hu⟩

end SetAF7BigCellConsumer
