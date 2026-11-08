/-
  SET-AF19A consumer: the two averaging rows of `Adelic/Cusp/SpectrumIntegration.lean` read at
  concrete data.

  **Zone 1 — the finite row at the trivial compact subgroup, with a real lift.** The row

  `∫ u, c u • S u (toCuspSubcarrier φ) = toCuspSubcarrier (fun x => ∫ u, c u * φ (x * u))`

  is instantiated at `U = ⊥` (compact, and below `finiteAdelicGL2Subgroup`), at the Dirac measure of
  the identity, at the constant weight `c = 1`, and — the real content — at a lift `S` *produced by*
  `CuspidalSpectrum.exists_isCuspLift_rightTranslate_and_norm_le` for `rightTranslate 1`, i.e. an
  honest cusp lift rather than a hypothesis. The conclusion is read back: the averaged function is
  `φ` itself (the group is a singleton, so the Bochner integral is evaluation at `1`), and the
  row's identity collapses to `S 1` fixing `toCuspSubcarrier φ` — the lift of the identity acts as
  the identity on the cuspidal subcarrier. Two modules are consumed: the lift-existence row of
  `Cusp/SpectrumTranslation.lean` and the finite averaging headline of `Cusp/SpectrumIntegration.lean`
  (deleting either one breaks this zone).

  **Zone 2 — the archimedean row at the canonical inclusion.** A natural reading of the second
  headline would be `ι := 1`, but the row's hypothesis `hι` makes that *impossible*: `archComponent`
  is a monoid homomorphism, so `archComponent F w (1 : GL …) = 1`, and `hι` then forces
  `((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) = 1` for **every** `κ`,
  i.e. the whole product of row-isometry groups to be trivial. `iota_one_forces_trivial` states that
  obstruction; the row is therefore read at the one homomorphism that does satisfy `hι` definitionally
  up to `ArchInfra.archComponent_inclArch`, the canonical inclusion
  `ArchInfra.inclArch : (∀ w, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F)`
  of the archimedean row-isometry product (the one `NumberField.AdelicLevel.archComponent` reads back
  place by place). The lift family stays a hypothesis, exactly as the headline has it.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumIntegration
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumTranslation
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.InfinitePlace NumberField.AdelicLevel NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.CuspidalSpectrum AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate ENNReal InnerProductSpace

-- the pin's wrappers register the adelic Borel structures as local instances for these statements
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm
namespace CuspidalSpectrum

namespace SetAF19AConsumer

variable {F : Type} [Field F] [NumberField F]

/-! ### Zone 1: the finite row at `⊥`, at the Dirac measure, with a produced lift -/

theorem finite_row_trivial_subgroup {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    (fun x => ∫ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
        φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂Measure.dirac 1) ∈ cuspMemberSubmodule F Φ₀ ξ ∧
      (fun x => ∫ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
          φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂Measure.dirac 1) = φ ∧
        ∃ S : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)) →
            (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
          (∀ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
            IsCuspLift F hΦ₀ σ ξ (rightTranslate F (u : AdelicGL2 (𝓞 F) F)) (S u)) ∧
            (∫ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
                (1 : ℂ) • S u (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∂Measure.dirac 1
              = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)
:= by
  classical
  -- the lift of `rightTranslate 1`, from SET-AF18B's existence row
  obtain ⟨S, hS, -⟩ :=
    exists_isCuspLift_rightTranslate_and_norm_le F hΦ₀ σ ξ hσ (1 : AdelicGL2 (𝓞 F) F)
  -- one lift serves the whole family, because the trivial subgroup is a singleton
  let Sfun : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)) →
      (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) := fun _ => S
  have hS' : ∀ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F (u : AdelicGL2 (𝓞 F) F)) (Sfun u) := by
    intro u
    have hu : (u : AdelicGL2 (𝓞 F) F) = 1 := Subgroup.mem_bot.mp u.2
    show IsCuspLift F hΦ₀ σ ξ (rightTranslate F (u : AdelicGL2 (𝓞 F) F)) S
    rw [hu]
    exact hS
  have hSc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ),
      Continuous fun u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)) => Sfun u v := by
    intro v
    show Continuous fun _ : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)) => S v
    exact continuous_const
  have hU : IsCompact ((⊥ : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by
    rw [Subgroup.coe_bot]
    exact isCompact_singleton
  -- the finite averaging row, at `⊥`, at the Dirac measure of the identity and at weight `1`
  obtain ⟨h, hid⟩ :=
    integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact
      F hΦ₀ σ ξ (⊥ : Subgroup (AdelicGL2 (𝓞 F) F)) hU bot_le
      (Measure.dirac (1 : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)))) Sfun hS' hSc
      (fun _ => (1 : ℂ)) continuous_const φ hφ
  -- the row's average, with the weight `1` folded away
  have havg : (fun x => ∫ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
      (1 : ℂ) * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂Measure.dirac 1)
      = fun x => ∫ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
          φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂Measure.dirac 1 := by
    funext x
    simp only [one_mul]
  -- ... the membership transfers
  have hmem : (fun x => ∫ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
      φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂Measure.dirac 1) ∈ cuspMemberSubmodule F Φ₀ ξ :=
    havg ▸ h
  -- ... and on a singleton the Bochner integral is evaluation, so the average is `φ` itself
  have hval : (fun x => ∫ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
      φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂Measure.dirac 1) = φ := by
    funext x
    simp
  refine ⟨hmem, hval, Sfun, hS', ?_⟩
  -- the row's identity, read through `havg`: the lift of the identity fixes every cusp member
  have hsub : (⟨fun x => ∫ u : ↥(⊥ : Subgroup (AdelicGL2 (𝓞 F) F)),
      (1 : ℂ) * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂Measure.dirac 1, h⟩ :
        ↥(cuspMemberSubmodule F Φ₀ ξ)) = ⟨φ, hφ⟩ :=
    Subtype.ext (havg.trans hval)
  rw [hid]
  exact congrArg (toCuspSubcarrier F hΦ₀ σ ξ) hsub

/-! ### Zone 2: the archimedean row at the canonical inclusion -/

omit [NumberField F] in
/-- The obstruction that rules out reading the archimedean row at `ι := 1`: `archComponent` is a
monoid homomorphism, so the row's `hι` at the trivial homomorphism already forces every `κ w` to be
trivial. -/
theorem iota_one_forces_trivial (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)
    (w : InfinitePlace F)
    (hι : archComponent F w (1 : GL (Fin 2) (InfiniteAdeleRing F)) =
      ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) :
    κ w = 1 := by
  rw [map_one] at hι
  exact Subtype.ext (by simpa using hι.symm)

/-- The archimedean averaging row at the canonical inclusion `ArchInfra.inclArch` of the
archimedean row-isometry product — the one `ι` for which the row's `hι` holds by
`ArchInfra.archComponent_inclArch`, and the lift family kept as the row's own hypothesis. -/
theorem archimedean_row_at_the_canonical_inclusion {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    [MeasurableSpace (ArchInfra.Kprod F)] [BorelSpace (ArchInfra.Kprod F)]
    (μ : Measure (ArchInfra.Kprod F)) [IsFiniteMeasure μ]
    (π : ArchInfra.Kprod F →
      (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hπ : ∀ κ : ArchInfra.Kprod F,
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F (adelicArchGLIncl F (ArchInfra.inclArch F κ))) (π κ))
    (hπc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ),
      Continuous fun κ : ArchInfra.Kprod F => π κ v)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    ∃ h : (fun x => ∫ κ : ArchInfra.Kprod F,
        φ (x * adelicArchGLIncl F (ArchInfra.inclArch F κ)) ∂μ) ∈ cuspMemberSubmodule F Φ₀ ξ,
      (∫ κ : ArchInfra.Kprod F,
          π κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∂μ)
        = toCuspSubcarrier F hΦ₀ σ ξ
          ⟨fun x => ∫ κ : ArchInfra.Kprod F,
            φ (x * adelicArchGLIncl F (ArchInfra.inclArch F κ)) ∂μ, h⟩ := by
  obtain ⟨h, hid⟩ :=
    integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate
      F hΦ₀ σ ξ μ (ArchInfra.inclArch F) ArchInfra.archComponent_inclArch π hπ hπc
      (fun _ => (1 : ℂ)) continuous_const φ hφ
  have havg : (fun x => ∫ κ : ArchInfra.Kprod F,
      (1 : ℂ) * φ (x * adelicArchGLIncl F (ArchInfra.inclArch F κ)) ∂μ)
      = fun x => ∫ κ : ArchInfra.Kprod F,
          φ (x * adelicArchGLIncl F (ArchInfra.inclArch F κ)) ∂μ := by
    funext x
    simp only [one_mul]
  refine ⟨havg ▸ h, ?_⟩
  -- the row's identity with the constant weight `1` folded away
  have hid' : (∫ κ : ArchInfra.Kprod F,
      π κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∂μ)
      = toCuspSubcarrier F hΦ₀ σ ξ
        ⟨fun x => ∫ κ : ArchInfra.Kprod F,
          (1 : ℂ) * φ (x * adelicArchGLIncl F (ArchInfra.inclArch F κ)) ∂μ, h⟩ := by
    simpa only [one_smul] using hid
  rw [hid']
  exact congrArg (toCuspSubcarrier F hΦ₀ σ ξ) (Subtype.ext havg)

end SetAF19AConsumer

end CuspidalSpectrum

end AutomorphicForm
