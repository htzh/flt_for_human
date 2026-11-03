/-
  Whittaker coefficients of an adelic `GL₂`-function.

  `IsPrincipalInvariantAddChar ψ` says a character of the adele ring is trivial on the
  principal ideles; `IsGlobalAddChar ψ` bundles that with continuity and nontriviality (the
  standard global additive character of a number field is the unique-up-to-scalars instance).
  Both are predicates on a character of the adèle ring and live in the number-field character
  layer; the API headlines below take them as hypotheses.
  For carrier data `pins : CarrierPins F`, an additive character `ψ` and `φ` on
  `GL₂(𝔸_F)`,

    `whittakerCoefficient pins ψ φ α g = ∫ x, φ (unipotentGL2 x * g) * ψ (-(α * x)) ∂pins.ν`

  is the adelic Whittaker coefficient at the additive parameter `α : F`, integrated against
  the carrier's unipotent measure `pins.ν`; `WhittakerCoefficientIntegrable` is its
  integrability. The two lemmas record the degenerate cases: the coefficient of `0` vanishes,
  and at `α = 0` it is the constant term (`constantTerm` of `ConstantTerm.lean`).

  **The coefficient's API.** The module is also the home of what the coefficient *does*: below
  the definition layer it states, one public headline per property and at the pin's statements:

  * the transformation law under the unipotent, `whittakerCoefficient_unipotentGL2_mul`: a
    coefficient whose integrand is invariant under the principal adeles at `g` transforms by
    the character factor `ψ (α x)` under `g ↦ n(x) g` — the identity every later rewrite of a
    `diagOne` value uses;
  * additivity over a finite sum of a continuous coefficient
    (`whittakerCoefficient_sum_smul_of_continuous`), and continuity in the group variable
    (`continuous_whittakerCoefficient`);
  * the diagonal reduction `whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul`:
    for `α ≠ 0` and a left-`GL₂(F)`-invariant `φ`, the coefficient at `α` is the coefficient at
    `1` at `diagOne α · g`;
  * the shell-surgery identity for the `diagOne` value
    (`RankinSelberg.whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery`): the
    value of a sum of unipotent translates of a maximal-compact point is its value on the
    un-translated point, the adèlic trace collapsing the sum to `1` on the shell;
  * the two realization-scalar identities at a finite place where the coefficient is a Hecke
    eigenfunction: the sum over the `q + 1` local representatives
    (`SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient`)
    and the value at the central scalar
    (`SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient`),
    with the eigensystem's `a v` and `b v`;
  * differentiability along the archimedean flow at a real place
    (`hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt`) and at a complex one
    (`hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex`): under
    continuity of `φ` and of its first two archimedean derivatives the derivative passes
    through the integral, so the derivative of the coefficient is the coefficient of the
    derivative, and the Casimir of the coefficient is the corresponding combination of
    coefficients.

  The last five are stated in the pin's `RankinSelberg.` and `SmoothCuspRealizationAt.`
  namespaces: those are the consumers' namespaces (the Rankin–Selberg and cusp-realization
  developments, not yet ported), while the subject of each statement is the coefficient, so
  the declarations live here at the pin's qualified names.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean`
  (pinned `aa2d8b3`, 61 lines, 8 declarations, no `private`; 653 pin importers) — the
  coefficient and its integrability, the other four declarations of that file being the
  character predicates in the character layer — and, for the nine API headlines below, from
  their `Theorems/` wrappers. Its two `Definitions/` imports are the already-ported
  `CarrierPins` and `ConstantTerm`; the pin reached `AddChar` through `ConstantTerm`'s
  `import Mathlib`, so the one mathlib module that defines it is imported here explicitly.
  spec-pin: Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean
  spec-pin: Theorems/Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul.lean
  spec-pin: Theorems/Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous.lean
  spec-pin: Theorems/Thm_AutomorphicForm_continuous_whittakerCoefficient.lean
  spec-pin: Theorems/Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul.lean
  spec-pin: Theorems/Thm_AutomorphicForm_RankinSelberg_whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery.lean
  spec-pin: Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient.lean
  spec-pin: Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient.lean
  spec-pin: Theorems/Thm_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt.lean
  spec-pin: Theorems/Thm_AutomorphicForm_hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex.lean
  spec-pin: Theorems/Thm_AutomorphicForm_whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SmoothRealization
import FLTForHuman.AutomorphicForm.Adelic.HeckeEigensystem
import FLTForHuman.AutomorphicForm.Adelic.Siegel.Covering
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry
import FLTForHuman.NumberTheory.NumberField.AdelicTraceFin
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.RepTheory.LocalLanglands.HeckeCosetLocal
import FLTForHuman.RepTheory.LocalLanglands.HeckeCosetSystem
import FLTForHuman.RepTheory.LocalLanglands.UnramifiedWhittaker
import Mathlib.Algebra.Group.AddChar
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicLevel
  NumberField.AdelicHaar NumberField.AdelicVolume
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
open LocalGL2 AdelicDock
open scoped ENNReal NNReal

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def whittakerCoefficient (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  letI := pins.nS
  ∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂pins.ν

def WhittakerCoefficientIntegrable (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : Prop :=
  letI := pins.nS
  Integrable
    (fun x => φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) pins.ν

@[simp] theorem whittakerCoefficient_zero (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun _ => (0 : ℂ)) α g = 0 := by
  simp only [whittakerCoefficient, zero_mul, integral_zero]

theorem whittakerCoefficient_zero_eq_constantTerm (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 0 g
      = @constantTerm _ pins.nS _ _ pins.ν unipotentGL2 φ g := by
  simp only [whittakerCoefficient, map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one,
    mul_one]
  rfl

/-! ## The coefficient's API, I: the transformation law under the unipotent

`whittakerCoefficient_unipotentGL2_mul` is the identity every later rewrite of a `diagOne`
value uses; its two private helpers move an integral over the adèlic box along a translation
by an element of the principal adèles, using that the box is a fundamental domain for the
principal subgroup of the adèles. -/

attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
  NumberField.AdelicHaar.regular_adelicAddHaar
  NumberField.AdelicHaar.countable_principalSubgroup

private theorem setIntegral_adelicBox_comp_add_right (F : Type) [Field F] [NumberField F]
    (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u in adelicBox F, G (u + x) ∂(adelicAddHaar (𝓞 F) F) =
      ∫ u in adelicBox F, G u ∂(adelicAddHaar (𝓞 F) F) := by
  set μ := adelicAddHaar (𝓞 F) F with hμ
  have h1 : ∫ u in adelicBox F, G (u + x) ∂μ =
      ∫ w in (fun u => u + x) '' adelicBox F, G w ∂μ := by
    have hme : MeasurableEmbedding (fun u : AdeleRing (𝓞 F) F => u + x) :=
      (Homeomorph.addRight x).measurableEmbedding
    conv_lhs => rw [← Set.preimage_image_eq (adelicBox F) (add_left_injective x)]
    rw [← hme.setIntegral_map, map_add_right_eq_self]
  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (adelicBox F) μ :=
    isAddFundamentalDomain_adelicBox F μ
  have hFD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun u => u + x) '' adelicBox F) μ := by
    refine hFD.image_of_equiv (ν := μ) (Equiv.addRight x) ?_ (Equiv.refl _) ?_
    · simpa using (measurePreserving_add_right μ (-x)).quasiMeasurePreserving
    · intro γ u
      show (γ +ᵥ u) + x = γ +ᵥ (u + x)
      simp only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc]
  have hinv : ∀ (γ : AdeleRing.principalSubgroup (𝓞 F) F) (u : AdeleRing (𝓞 F) F),
      G (γ +ᵥ u) = G u := by
    rintro ⟨_, β, rfl⟩ u
    exact hG β u
  rw [h1]
  exact hFD'.setIntegral_eq hFD hinv

private theorem integral_cond_adelicBox_comp_add_right (F : Type) [Field F] [NumberField F]
    (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u, G (u + x) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) =
      ∫ u, G u ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  simp only [ProbabilityTheory.cond, integral_smul_measure,
    setIntegral_adelicBox_comp_add_right F G hG x]

theorem whittakerCoefficient_unipotentGL2_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (α : F) (x : AdeleRing (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α (unipotentGL2 x * g) =
      ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g := by
  set a := algebraMap F (AdeleRing (𝓞 F) F) α with ha
  set G : AdeleRing (𝓞 F) F → ℂ := fun w => φ (unipotentGL2 w * g) * ψ (-(a * w)) with hGdef
  have hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u := by
    intro β u
    have h1 : ψ (-(a * algebraMap F (AdeleRing (𝓞 F) F) β)) = 1 := by
      rw [ha, ← map_mul, ← map_neg]
      exact hψ _
    simp only [hGdef]
    rw [hper β u, mul_add, neg_add, AddChar.map_add_eq_mul, h1, one_mul]
  have hint : ∀ u : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 u * (unipotentGL2 x * g)) * ψ (-(a * u)) = ψ (a * x) * G (u + x) := by
    intro u
    simp only [hGdef]
    rw [← mul_assoc, ← unipotentGL2_add,
      show -(a * u) = a * x + -(a * (u + x)) by ring, AddChar.map_add_eq_mul]
    ring
  show (∫ u, φ (unipotentGL2 u * (unipotentGL2 x * g)) * ψ (-(a * u))
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) =
    ψ (a * x) * ∫ u, φ (unipotentGL2 u * g) * ψ (-(a * u))
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
  simp_rw [hint]
  rw [integral_const_mul, integral_cond_adelicBox_comp_add_right F G hG x]

/-! ## The coefficient's API, II: additivity over a finite sum and continuity

The two cheap algebraic/analytic rows: the coefficient is additive over a finite sum of
continuous terms, and it is continuous in the group variable. Both reduce the coefficient to
its defining integral over the adèlic box by `integral_smul_measure`, then use that a continuous
function on the compact box is bounded. -/

theorem whittakerCoefficient_sum_smul_of_continuous
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (m : ℕ) (φ : Fin m → (AdelicGL2 (𝓞 F) F → ℂ)) (hφ : ∀ j, Continuous (φ j)) (cs : Fin m → ℂ)
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (fun x => ∑ j, cs j * φ j x) α g =
      ∑ j, cs j * whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ (φ j) α g := by
  classical
  set μ : Measure (AdeleRing (𝓞 F) F) := adelicAddHaar (𝓞 F) F with hμ
  set B : Set (AdeleRing (𝓞 F) F) := adelicBox F with hB

  have hW : ∀ f : AdelicGL2 (𝓞 F) F → ℂ,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ f α g =
        ((μ B)⁻¹).toReal • ∫ x in B, f (unipotentGL2 x * g) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂μ := by
    intro f
    unfold whittakerCoefficient
    dsimp only [productionPinsOf]
    exact integral_smul_measure _ _

  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset F
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top F
  have hBmeas : MeasurableSet B := measurableSet_adelicBox F
  set G : Fin m → AdeleRing (𝓞 F) F → ℂ := fun j x =>
    φ j (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) with hG
  have hint : ∀ j, IntegrableOn (G j) B μ := by
    intro j
    have hc : Continuous (G j) :=
      ((hφ j).comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul
        continuous_const)).mul (hψ.comp ((continuous_const.mul continuous_id).neg))
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (f := G j) hc.continuousOn
    exact Measure.integrableOn_of_bounded hBfin.ne hc.aestronglyMeasurable
      (ae_restrict_of_forall_mem hBmeas fun x hx => hM x (hBC hx))
  rw [hW, show (∑ j, cs j * whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F))
        ψ (φ j) α g) =
      ∑ j, cs j * (((μ B)⁻¹).toReal • ∫ x in B, G j x ∂μ) from
    Finset.sum_congr rfl (fun j _ => by rw [hW])]
  have hsum : (fun x => (∑ j, cs j * φ j (unipotentGL2 x * g)) *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) =
      fun x => ∑ j, cs j * G j x := by
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hG, mul_assoc]
  rw [hsum, integral_finsetSum _ (fun j _ => (hint j).const_mul (cs j))]
  simp_rw [integral_const_mul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.real_smul, Complex.real_smul]
  ring

theorem continuous_whittakerCoefficient
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (α : F) :
    Continuous (fun g : AdelicGL2 (𝓞 F) F =>
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) := by
  set G : AdelicGL2 (𝓞 F) F → AdeleRing (𝓞 F) F → ℂ := fun g x =>
    φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) with hG
  have hW : (fun g : AdelicGL2 (𝓞 F) F =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g)
      = fun g => (((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹).toReal •
          ∫ x in adelicBox F, G g x ∂(adelicAddHaar (𝓞 F) F) := by
    funext g
    unfold whittakerCoefficient
    dsimp only [productionPinsOf]
    exact integral_smul_measure _ _
  rw [hW]
  refine Continuous.fun_smul continuous_const ?_
  set μ : Measure (AdeleRing (𝓞 F) F) := adelicAddHaar (𝓞 F) F with hμ
  set B : Set (AdeleRing (𝓞 F) F) := adelicBox F with hB

  have hGc : Continuous (fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F => G p.2 p.1) := by
    have h1 : Continuous (fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        (unipotentGL2 p.1 : AdelicGL2 (𝓞 F) F) * p.2) :=
      ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).comp continuous_fst).mul continuous_snd
    have h2 : Continuous (fun p : AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F =>
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * p.1))) :=
      hψ.comp ((continuous_const.mul continuous_fst).neg)
    exact (hφ.comp h1).mul h2
  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset F
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top F
  have hBmeas : MeasurableSet B := measurableSet_adelicBox F

  have hint : ∀ g, IntegrableOn (G g) B μ := by
    intro g
    have hc : Continuous (fun x => G g x) := by
      rw [hG]
      exact (hφ.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul
        continuous_const)).mul (hψ.comp ((continuous_const.mul continuous_id).neg))
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (f := fun x => G g x) hc.continuousOn
    exact Measure.integrableOn_of_bounded hBfin.ne hc.aestronglyMeasurable
      (ae_restrict_of_forall_mem hBmeas fun x hx => hM x (hBC hx))
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set ε' : ℝ := ε / (μ.real B + 1) with hε'
  have hm0 : 0 ≤ μ.real B := measureReal_nonneg
  have hε'0 : 0 < ε' := div_pos hε (by linarith)

  set O : Set (AdeleRing (𝓞 F) F × AdelicGL2 (𝓞 F) F) :=
    {p | dist (G p.2 p.1) (G g₀ p.1) < ε'} with hO
  have hOopen : IsOpen O :=
    isOpen_lt (continuous_dist.comp (hGc.prodMk (hGc.comp (continuous_fst.prodMk continuous_const))))
      continuous_const
  have hsub : C ×ˢ ({g₀} : Set (AdelicGL2 (𝓞 F) F)) ⊆ O := by
    rintro ⟨x, g⟩ ⟨-, hg⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    show dist (G g x) (G g x) < ε'
    rw [dist_self]
    exact hε'0
  obtain ⟨u, v, hu, hv, hCu, hg₀v, huv⟩ :=
    generalized_tube_lemma hCc isCompact_singleton hOopen hsub
  have hg₀ : g₀ ∈ v := hg₀v (Set.mem_singleton g₀)
  filter_upwards [hv.mem_nhds hg₀] with g hg
  rw [dist_eq_norm, ← integral_sub (hint g) (hint g₀)]
  have hpt : ∀ x ∈ B, ‖G g x - G g₀ x‖ ≤ ε' := by
    intro x hx
    have hxO : (x, g) ∈ O := huv ⟨hCu (hBC hx), hg⟩
    have : dist (G g x) (G g₀ x) < ε' := hxO
    rw [dist_eq_norm] at this
    exact this.le
  calc ‖∫ x in B, G g x - G g₀ x ∂μ‖ ≤ ε' * μ.real B :=
        norm_setIntegral_le_of_norm_le_const hBfin hpt
    _ < ε := by
      rw [hε', div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

/-! ## The coefficient's API, III: the diagonal reduction

For `α ≠ 0` and a left-`GL₂(F)`-invariant `φ`, the coefficient at `α` is the coefficient at `1`
at `diagOne α · g`. The prelude builds the `α`-adic class `principalIdeleOf`, the diagonal matrix
`diagGL2`, and the measure preservation of `x ↦ principalIdeleOf a • x` on the adèlic box, which
is where the principal-idele product formula enters. -/

namespace WhittakerGenericity

private theorem globalPoints_coe_apply (F : Type) [Field F] [NumberField F]
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (i j : Fin 2) :
    (globalPoints (𝓞 F) F γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = algebraMap F (AdeleRing (𝓞 F) F) ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

private def diagGL2 (F : Type) [Field F] [NumberField F] (α : F) (hα : α ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![α, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hα])

private theorem unipotentGL2_mul_globalPoints_diagGL2 (F : Type) [Field F] [NumberField F]
    (α : F) (hα : α ≠ 0) (x : AdeleRing (𝓞 F) F) :
    unipotentGL2 x * globalPoints (𝓞 F) F (diagGL2 F α hα)
      = globalPoints (𝓞 F) F (diagGL2 F α hα)
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ * x) := by
  have hinv : algebraMap F (AdeleRing (𝓞 F) F) α * algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hα, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [globalPoints_coe_apply, diagGL2, Matrix.mul_apply, Fin.sum_univ_two, ← mul_assoc, hinv]

private theorem globalPoints_unipotentGL2 (F : Type) [Field F] [NumberField F] (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [globalPoints_coe_apply]

private theorem integrand_vadd (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (α : F) (g : AdelicGL2 (𝓞 F) F) (γ : AdeleRing.principalSubgroup (𝓞 F) F)
    (x : AdeleRing (𝓞 F) F) :
    φ (unipotentGL2 (γ +ᵥ x) * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * (γ +ᵥ x)))
      = φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) := by
  obtain ⟨_, β, rfl⟩ := γ
  have hv : ((⟨algebraMap F _ β, β, rfl⟩ : AdeleRing.principalSubgroup (𝓞 F) F) +ᵥ x)
      = algebraMap F (AdeleRing (𝓞 F) F) β + x := rfl
  rw [hv]
  congr 1
  · rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hleft]
  · rw [mul_add, neg_add, ψ.map_add_eq_mul]
    have h1 :
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * algebraMap F (AdeleRing (𝓞 F) F) β)) = 1 := by
      rw [← map_mul, ← map_neg]
      exact hψ.principalInvariant (-(α * β))
    rw [h1, one_mul]

private def principalIdeleOf (F : Type) [Field F] [NumberField F] (a : Fˣ) :
    (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a

private theorem principalIdeleOf_smul (F : Type) [Field F] [NumberField F] (a : Fˣ)
    (x : AdeleRing (𝓞 F) F) :
    principalIdeleOf F a • x = algebraMap F (AdeleRing (𝓞 F) F) (a : F) * x := rfl

private theorem distribHaarChar_principalIdeleOf (F : Type) [Field F] [NumberField F] (a : Fˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (principalIdeleOf F a) = 1 :=
  NumberField.AdeleRing.distribHaarChar_algebraMap F a

private theorem measurePreserving_principalIdeleOf_smul (F : Type) [Field F] [NumberField F]
    (a : Fˣ) :
    MeasurePreserving (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F a • x)
      (adelicAddHaar (𝓞 F) F) (adelicAddHaar (𝓞 F) F) := by
  have hmeas : Measurable (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F a • x) := by
    simp only [principalIdeleOf_smul]
    exact (continuous_const.mul continuous_id).measurable
  refine ⟨hmeas, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeas hs, Set.preimage_smul,
    ← distribHaarChar_mul (adelicAddHaar (𝓞 F) F) (principalIdeleOf F a)⁻¹ s]
  have h1 : distribHaarChar (AdeleRing (𝓞 F) F) (principalIdeleOf F a)⁻¹ = 1 := by
    rw [map_inv, distribHaarChar_principalIdeleOf, inv_one]
  rw [h1, ENNReal.coe_one, one_mul]

private theorem measurableEmbedding_principalIdeleOf_smul (F : Type) [Field F] [NumberField F]
    (a : Fˣ) :
    MeasurableEmbedding (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F a • x) :=
  (Homeomorph.smul (α := AdeleRing (𝓞 F) F) (principalIdeleOf F a)).measurableEmbedding

private theorem whittakerCoefficient_productionPinsOf_eq (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g
      = ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹.toReal •
          ∫ x in adelicBox F,
            φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
              ∂(adelicAddHaar (𝓞 F) F) := by
  show (∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) = _
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure]

private theorem image_principalIdeleOf_inv_smul_adelicBox (F : Type) [Field F] [NumberField F]
    (α : F) (hα : α ≠ 0) :
    (fun x : AdeleRing (𝓞 F) F => principalIdeleOf F (Units.mk0 α hα)⁻¹ • x) '' adelicBox F
      = (fun x : AdeleRing (𝓞 F) F => algebraMap F (AdeleRing (𝓞 F) F) α * x) ⁻¹' adelicBox F := by
  refine congrFun (Set.image_eq_preimage_of_inverse ?_ ?_) (adelicBox F)
  · intro x
    simp only [principalIdeleOf_smul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
  · intro x
    simp only [principalIdeleOf_smul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_assoc,
      ← map_mul, inv_mul_cancel₀ hα, map_one, one_mul]

private theorem whittakerCoefficient_eq_one_diagGL2_mul (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (α : F) (hα : α ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g
      = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (globalPoints (𝓞 F) F (diagGL2 F α hα) * g) := by
  rw [whittakerCoefficient_productionPinsOf_eq, whittakerCoefficient_productionPinsOf_eq]

  have hpt : ∀ x : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 x * (globalPoints (𝓞 F) F (diagGL2 F α hα) * g))
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * x))
        = φ (unipotentGL2 (principalIdeleOf F (Units.mk0 α hα)⁻¹ • x) * g)
          * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α
                * (principalIdeleOf F (Units.mk0 α hα)⁻¹ • x))) := by
    intro x
    simp only [principalIdeleOf_smul, Units.val_inv_eq_inv_val, Units.val_mk0, map_one, one_mul]
    rw [← mul_assoc, unipotentGL2_mul_globalPoints_diagGL2 F α hα x, mul_assoc, hleft]
    have hx :
        algebraMap F (AdeleRing (𝓞 F) F) α * (algebraMap F (AdeleRing (𝓞 F) F) α⁻¹ * x) = x := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hα, map_one, one_mul]
    rw [hx]

  have himg := (measurePreserving_principalIdeleOf_smul F (Units.mk0 α hα)⁻¹).setIntegral_image_emb
    (measurableEmbedding_principalIdeleOf_smul F (Units.mk0 α hα)⁻¹)
    (fun y => φ (unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * y))) (adelicBox F)
  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun x : AdeleRing (𝓞 F) F => principalIdeleOf F (Units.mk0 α hα)⁻¹ • x) '' adelicBox F)
      (adelicAddHaar (𝓞 F) F) := by
    rw [image_principalIdeleOf_inv_smul_adelicBox F α hα]
    exact NumberField.AdelicBox.isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox F
      (adelicAddHaar (𝓞 F) F) α hα
  have hdom := (isAddFundamentalDomain_adelicBox_adelicAddHaar F).setIntegral_eq hFD
    (f := fun y => φ (unipotentGL2 y * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * y)))
    (fun γ x => integrand_vadd F ψ hψ φ hleft α g γ x)
  have hint :
      (∫ x in adelicBox F, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
          ∂(adelicAddHaar (𝓞 F) F))
        = ∫ x in adelicBox F,
            φ (unipotentGL2 x * (globalPoints (𝓞 F) F (diagGL2 F α hα) * g))
              * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * x)) ∂(adelicAddHaar (𝓞 F) F) := by
    rw [funext hpt]
    exact hdom.trans himg
  rw [hint]

private theorem diagOne_mk0_eq_diagGL2 (F : Type) [Field F] [NumberField F]
    (α : F) (hα : α ≠ 0) :
    AdelicLevel.diagOne (Units.mk0 α hα) = diagGL2 F α hα := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [AdelicLevel.diagOne_coe_apply, Matrix.diagonal, diagGL2]

end WhittakerGenericity

theorem whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (α : F) (hα : α ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ α g
      = whittakerCoefficient F (productionPinsOf F D U gen (AdelicBox.adelicBox F)) ψ φ 1
          (globalPoints (𝓞 F) F (AdelicLevel.diagOne (Units.mk0 α hα)) * g) := by
  rw [WhittakerGenericity.diagOne_mk0_eq_diagGL2]
  exact WhittakerGenericity.whittakerCoefficient_eq_one_diagGL2_mul F D U gen ψ hψ φ hleft α hα g

/-! ## The coefficient's API, IV: shell surgery on the `diagOne` value

The identity a Rankin–Selberg consumer uses to read the coefficient at a `diagOne` point off a
sum of unipotent translates: the adèlic trace collapses the sum to `1` on the shell. The
headline lives in the consumer's namespace, with the pin's nine `_`-prefixed hypotheses. -/

namespace RankinSelberg

private theorem whittakerCoefficient_mul_right (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (a : F)
    (g k : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ a (g * k) = whittakerCoefficient F pins ψ (fun y => φ (y * k)) a g := by
  simp only [whittakerCoefficient, mul_assoc]

private theorem glArch_unipotentGL2_eq_one {K : Type} [Field K] [NumberField K]
    (y : AdeleRing (𝓞 K) K) (hy : y.1 = 0) : glArch (𝓞 K) K (unipotentGL2 y) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, unipotentGL2_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> first | rfl | simp [hy]

private theorem mul_comm_of_glArch_eq_one_of_glFin_eq_one {K : Type} [Field K] [NumberField K]
    {a b : AdelicGL2 (𝓞 K) K} (ha : glArch (𝓞 K) K a = 1) (hb : glFin (𝓞 K) K b = 1) :
    a * b = b * a :=
  eq_of_glArch_eq_of_glFin_eq (by rw [map_mul, map_mul, ha, one_mul, mul_one])
    (by rw [map_mul, map_mul, hb, mul_one, one_mul])

theorem whittakerCoefficient_diagOne_mul_mul_inv_finEmbed_eq_of_shell_surgery (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (t₀ : (AdeleRing (𝓞 K) K)ˣ)
    (k₀ : AdelicGL2 (𝓞 K) K)
    (_hk₀ : k₀ ∈ maximalCompactAt K S)
    (_hWpt : whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t₀ * k₀) ≠ 0)
    (κ : AdelicGL2 (𝓞 K) K)
    (_hκ : κ = AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K k₀))
    (aexp : HeightOneSpectrum (𝓞 K) → ℤ)
    (_haexp : ∀ v : HeightOneSpectrum (𝓞 K), Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) =
        ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (r : ℕ)
    (y : Fin r → AdeleRing (𝓞 K) K)
    (cs : Fin r → ℂ)
    (m : ℕ)
    (_hysupp : ∀ i, (y i).1 = 0 ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → (y i).2 v = 0)
    (_hWmult : ∀ (t : (AdeleRing (𝓞 K) K)ˣ) (g' : AdelicGL2 (𝓞 K) K),
        (∀ i, g' * unipotentGL2 (y i) = unipotentGL2 (y i) * g') →
        whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (y i) * κ)) 1
          (diagOne t * g') =
          (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) *
            whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => x₀ (g * κ)) 1
          (diagOne t * g'))
    (_hμbox : ∀ t : (AdeleRing (𝓞 K) K)ˣ,
        (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) ≤
            ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
        (∑ i, cs i * NumberField.StandardAddChar.stdAddChar K ((t : AdeleRing (𝓞 K) K) * y i)) =
          if ∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) =
              ((Multiplicative.ofAdd (aexp v) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) then 1 else 0)
    (_hboxvan : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
        ∀ t : (AdeleRing (𝓞 K) K)ˣ,
          (∃ v ∈ S, ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) <
            Valued.v (((t : AdeleRing (𝓞 K) K)).2 v)) →
          whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * k * κ) = 0)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * (unipotentGL2 (y i) * κ))) :
    whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne t₀ * (k₀ * κ⁻¹)) =
      whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t₀ * k₀) := by
  classical
  have hκfin : glFin (𝓞 K) K κ = glFin (𝓞 K) K k₀ := by rw [_hκ, AdelicDock.glFin_finEmbed]
  have hκarch : glArch (𝓞 K) K κ = 1 := by rw [_hκ, AdelicDock.glArch_finEmbed]
  have hk₀f : glFin (𝓞 K) K (k₀ * κ⁻¹) = 1 := by rw [map_mul, map_inv, hκfin, mul_inv_cancel]
  have hk₀a : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K (k₀ * κ⁻¹))) := by
    intro pl
    rw [map_mul, map_inv, hκarch, inv_one, mul_one]
    exact (mem_adelicMaximalCompact_iff.mp (maximalCompactAt_le K S _hk₀)).2 pl
  have hk₀κ : k₀ * κ⁻¹ * κ = k₀ := inv_mul_cancel_right _ _
  have ht₀box : ∀ v ∈ S, Valued.v (((t₀ : AdeleRing (𝓞 K) K)).2 v) ≤
      ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro v hv
    by_contra hlt
    rw [not_le] at hlt
    have h0 := _hboxvan (k₀ * κ⁻¹) hk₀f hk₀a t₀ ⟨v, hv, hlt⟩
    rw [mul_assoc, hk₀κ] at h0
    exact _hWpt h0
  have hxfun : (fun g => ∑ i, cs i * x₀ (g * unipotentGL2 (y i) * κ)) = x := by
    funext g
    rw [_hxsum g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc]
  have hcommk : ∀ i, (k₀ * κ⁻¹) * unipotentGL2 (y i) = unipotentGL2 (y i) * (k₀ * κ⁻¹) := fun i =>
    (mul_comm_of_glArch_eq_one_of_glFin_eq_one (glArch_unipotentGL2_eq_one (y i) (_hysupp i).1)
      hk₀f).symm
  have hmul := _hWmult t₀ (k₀ * κ⁻¹) hcommk
  have hμ1 := _hμbox t₀ ht₀box
  rw [ite_eq_left (fun v _ => _haexp v)] at hμ1
  rw [hxfun, hμ1, one_mul] at hmul
  rw [hmul, ← whittakerCoefficient_mul_right K _ _ x₀ 1 (diagOne t₀ * (k₀ * κ⁻¹)) κ, mul_assoc, hk₀κ]

end RankinSelberg

/-! ## The coefficient's API, V: the two realization-scalar identities

At a finite place where the coefficient is a Hecke eigenfunction, the sum over the `q + 1`
local representatives is `Ψ.a v` times the coefficient, and the value at the central scalar is
`Ψ.b v` times it. Both live in the cusp-realization consumer's namespace. -/

namespace SmoothCuspRealizationAt

private theorem placeEmbed_scalarPi_eq_centralScalar_det {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0) :
    UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)
      = centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det
          (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)))) := by
  apply Units.ext
  rw [centralScalar_val]
  simp only [UnramifiedWhittaker.placeEmbed, MonoidHom.comp_apply, coe_finEmbed, coe_localEmbed,
    Matrix.GeneralLinearGroup.val_det_apply]
  have hsc : ((UnramifiedWhittaker.scalarPi (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
      : GL (Fin 2) (v.adicCompletion F)) : Matrix _ _ _)
      = !![algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ, 0;
           0, algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ] := rfl
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [mapMatrix_arch_finMat, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _), RingHom.map_det, mapMatrix_arch_finMat, Matrix.det_one, Matrix.diagonal_one]
  · rw [mapMatrix_fin_finMat, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _), RingHom.map_det, mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [mapMatrix_localMat_self, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _), RingHom.map_det, mapMatrix_localMat_self, hsc, coe_diagPi, Matrix.det_fin_two_of]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
    · rw [mapMatrix_localMat_of_ne (𝓞 F) F v _ hw, RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _),
        RingHom.map_det, mapMatrix_localMat_of_ne (𝓞 F) F v _ hw, Matrix.det_one,
        Matrix.diagonal_one]

theorem sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Ψ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hint : ∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ R.toFun α g)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R.exceptionalSet)
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    {I : Type*} [Fintype I] (b : I → v.adicCompletionIntegers F)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem
      (levelOne (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
      (fun i : Option I => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
        (i.elim (localRepInf ϖ hϖ0) (fun c => localRepSome ϖ hϖ0 (b c))))))
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    (∑ i, whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α
        (g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b i))))) +
      whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α
        (g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)) =
      Ψ.a v * whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α g := by
  classical

  have hSome : ∀ c : I, UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repSome
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b c)))
      = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepSome ϖ hϖ0 (b c))) := by
    intro c
    have hloc : UnramifiedWhittaker.repSome
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b c)) = localRepSome ϖ hϖ0 (b c) := by
      apply Units.ext
      simp [UnramifiedWhittaker.repSome, localRepSome, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul,
        coe_unipotentInt, coe_diagPi]
    unfold UnramifiedWhittaker.placeEmbed
    rw [MonoidHom.comp_apply, hloc]
  have hInf : UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repInf
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)
      = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0)) := by
    have hloc : UnramifiedWhittaker.repInf
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0 = localRepInf ϖ hϖ0 := by
      apply Units.ext
      simp [UnramifiedWhittaker.repInf, localRepInf, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul,
        coe_weylInt, coe_diagPi]
    unfold UnramifiedWhittaker.placeEmbed
    rw [MonoidHom.comp_apply, hloc]

  set fam : Option I → AdelicGL2 (𝓞 F) F := fun i => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
    (i.elim (localRepInf ϖ hϖ0) (fun c => localRepSome ϖ hϖ0 (b c)))) with hfam
  have hcard : Fintype.card (Option I) = Ideal.absNorm v.asIdeal + 1 := by
    rw [Fintype.card_option, hI]
  set e : Option I ≃ Fin (Ideal.absNorm v.asIdeal + 1) := Fintype.equivFinOfCardEq hcard with he
  set reps' : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F := fun i => fam (e.symm i) with hreps'
  have hsys' : HeckeIntegralSeam.IsHeckeCosetSystem (levelOne (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F)
      (heckeGen (𝓞 F) F v) reps' := by
    refine ⟨fun i => hsys.mem_doubleCoset _, fun x hx => ?_, fun i j hij => ?_⟩
    · obtain ⟨j, hj⟩ := hsys.covers x hx
      refine ⟨e j, ?_⟩
      rw [hj, hreps']
      simp only [Equiv.symm_apply_apply]
    · have h2 : (QuotientGroup.mk (fam (e.symm i)) : AdelicGL2 (𝓞 F) F ⧸ (levelOne (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F))
          = QuotientGroup.mk (fam (e.symm j)) := hij
      have := hsys.mk_injective h2
      exact e.symm.injective this

  obtain ⟨reps, hreps, hsum⟩ := R.hecke_eigen v hv
  have hinv : ∀ y : AdelicGL2 (𝓞 F) F, ∀ u ∈ levelOne (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F,
      R.toFun (y * u) = R.toFun y := R.level_invariant
  have heq : ∀ y : AdelicGL2 (𝓞 F) F, (∑ i, R.toFun (y * reps' i)) = Ψ.a v * R.toFun y := by
    intro y
    rw [HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hreps hsys' hinv y]
    exact hsum y

  have hW : ∀ y : AdelicGL2 (𝓞 F) F, whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α y
      = ∫ x, R.toFun (unipotentGL2 x * y) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
          ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := fun y => rfl
  have hint' : ∀ y : AdelicGL2 (𝓞 F) F, Integrable
      (fun x => R.toFun (unipotentGL2 x * y) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)))
      (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := fun y => hint α y
  have hsumW : (∑ i, whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α (g * reps' i))
      = Ψ.a v * whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α g := by
    simp_rw [hW]
    rw [← integral_finsetSum _ (fun i _ => hint' (g * reps' i)), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have h1 : (∑ i, R.toFun (unipotentGL2 x * (g * reps' i)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)))
        = (∑ i, R.toFun (unipotentGL2 x * g * reps' i)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc]
    show (∑ i, R.toFun (unipotentGL2 x * (g * reps' i)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)))
      = Ψ.a v * (R.toFun (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)))
    rw [h1, heq (unipotentGL2 x * g), mul_assoc]

  have hreindex : (∑ i, whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α (g * reps' i))
      = ∑ j : Option I, whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α (g * fam j) :=
    Fintype.sum_equiv e.symm _ _ (fun i => rfl)
  rw [hreindex, Fintype.sum_option] at hsumW
  have hS : ∀ c : I, g * fam (some c) = g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repSome
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b c))) := fun c => by
    simp only [hfam, Option.elim_some, hSome]
  have hN : g * fam none = g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repInf
      (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0) := by
    simp only [hfam, Option.elim_none, hInf]
  simp_rw [hS, hN] at hsumW
  rw [add_comm]
  exact hsumW

theorem whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Ψ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R.exceptionalSet)
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hgen : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v)
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α
        (g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.scalarPi
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)) =
      Ψ.b v * whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α g := by
  have hc := R.central_eigen v hv
  rw [placeEmbed_scalarPi_eq_centralScalar_det v ϖ hϖ0, hgen]
  set c : AdelicGL2 (𝓞 F) F := centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) with hcdef
  have hc' : ∀ y : AdelicGL2 (𝓞 F) F, R.toFun (c * y) = Ψ.b v * R.toFun y := hc
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show R.toFun (unipotentGL2 x * (g * c)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))
    = Ψ.b v * (R.toFun (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)))
  rw [← mul_assoc (unipotentGL2 x) g c, hcdef, mul_centralScalar_comm, ← hcdef, hc' (unipotentGL2 x * g), mul_assoc]

end SmoothCuspRealizationAt


/-! ## The coefficient's API, VI: the archimedean flows

The two differentiability rows: under continuity of `φ` and of its first two archimedean
derivatives, the derivative passes through the defining integral (dominated convergence,
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), so the derivative of the coefficient is the
coefficient of the derivative. The real place first, then the complex twin; both flows are the
port's `archFlowAt`/`archFlowAtComplex`, so the pin's `Function.update` coefficient form is
re-established here in the port's `archMatrixUpdate` form (still `rfl`). -/

variable {K : Type} [Field K] [NumberField K]

private theorem continuous_archFlowMatrix_apply (d : ArchDir) (i j : Fin 2) :
    Continuous fun t : ℝ => (archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp [archFlowMatrix, splitTorusGL2_coe, unipotentGL2_coe, lowerUnipotentGL2_coe,
      Real.continuous_exp, continuous_const] <;>
    first
      | exact Real.continuous_exp.comp continuous_neg
      | exact continuous_id

private theorem archFlowAt_coe_apply {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ)
    (i j : Fin 2) :
    ((archFlowAt hw d t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      (archMatrixUpdate K w
        ((glEquivOfRingEquiv (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
            (archFlowMatrix d t) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :=
  rfl

private theorem archFlowAt_neg {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) (t : ℝ) :
    archFlowAt hw d (-t) = (archFlowAt hw d t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← archFlowAt_add, neg_add_cancel, archFlowAt_zero]

private theorem continuous_archFlowAt {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir) :
    Continuous fun t : ℝ => archFlowAt hw d t := by
  classical
  have hval : Continuous fun t : ℝ =>
      ((archFlowAt hw d t : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    apply continuous_pi; intro i; apply continuous_pi; intro j
    simp only [archFlowAt_coe_apply]
    refine Continuous.prodMk ?_ continuous_const
    apply continuous_pi; intro v
    by_cases hv : v = w
    · subst hv
      simp only [archMatrixUpdate_apply_self]
      show Continuous fun t : ℝ =>
        (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
          ((archFlowMatrix d t : Matrix (Fin 2) (Fin 2) ℝ) i j)
      exact (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.comp
        (continuous_archFlowMatrix_apply d i j)
    · refine Continuous.congr (f := fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j)
        continuous_const (fun a => ?_)
      exact (archMatrixUpdate_apply_of_ne _ _ _ _ _ hv).symm
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have : (fun t : ℝ => (((archFlowAt hw d t)⁻¹ : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) =
      fun t : ℝ => ((archFlowAt hw d (-t) : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    funext t; rw [archFlowAt_neg]
  rw [this]
  exact hval.comp continuous_neg

private theorem hasDerivAt_flow_of_isArchSmoothAt {w : InfinitePlace K} {hw : w.IsReal}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAt hw φ) (d : ArchDir)
    (g : AdelicGL2 (𝓞 K) K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (g * archFlowAt hw d s)) (archDerivAt hw d φ (g * archFlowAt hw d t)) t := by
  have h0 : HasDerivAt (fun s : ℝ => φ ((g * archFlowAt hw d t) * archFlowAt hw d s))
      (archDerivAt hw d φ (g * archFlowAt hw d t)) 0 :=
    (hφ.differentiableAt_flow d (g * archFlowAt hw d t)).hasDerivAt
  have hsub : HasDerivAt (fun s : ℝ => s - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have h0' : HasDerivAt (fun s : ℝ => φ ((g * archFlowAt hw d t) * archFlowAt hw d s))
      (archDerivAt hw d φ (g * archFlowAt hw d t)) ((fun s : ℝ => s - t) t) := by
    simp only [sub_self]; exact h0
  have h1 := HasDerivAt.scomp (h := fun s : ℝ => s - t) t h0' hsub
  rw [one_smul] at h1
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show φ (g * archFlowAt hw d s) = φ (g * archFlowAt hw d t * archFlowAt hw d (s - t))
  rw [mul_assoc, ← archFlowAt_add, show t + (s - t) = s by ring]

private theorem hasDerivAt_setIntegral_flow (K : Type) [Field K] [NumberField K]
    {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hc : Continuous φ) (hs : IsArchSmoothAt hw φ)
    (hD : Continuous (archDerivAt hw d φ))
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : Continuous ψ) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
    HasDerivAt (fun t : ℝ => ∫ x in adelicBox K,
        φ (unipotentGL2 x * g * archFlowAt hw d t) *
          ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) ∂(adelicAddHaar (𝓞 K) K))
      (∫ x in adelicBox K, archDerivAt hw d φ (unipotentGL2 x * g) *
        ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))
        ∂(adelicAddHaar (𝓞 K) K)) 0 := by
  let _ : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  have _ : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  set μ : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμ
  set B : Set (AdeleRing (𝓞 K) K) := adelicBox K with hB
  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset K
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top K
  have hBmeas : MeasurableSet B := measurableSet_adelicBox K

  set Fn : ℝ → (AdeleRing (𝓞 K) K) → ℂ := fun t x =>
    φ (unipotentGL2 x * g * archFlowAt hw d t) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))
    with hFn
  set Fn' : ℝ → (AdeleRing (𝓞 K) K) → ℂ := fun t x =>
    archDerivAt hw d φ (unipotentGL2 x * g * archFlowAt hw d t) *
      ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) with hFn'
  have hpt : Continuous fun p : (AdeleRing (𝓞 K) K) × ℝ =>
      unipotentGL2 p.1 * g * archFlowAt hw d p.2 :=
    (((continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)).comp continuous_fst).mul continuous_const).mul
      ((continuous_archFlowAt hw d).comp continuous_snd)
  have hψc : Continuous fun x : (AdeleRing (𝓞 K) K) =>
      ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) :=
    hψ.comp ((continuous_const.mul continuous_id).neg)
  have hFn_cont : ∀ t, Continuous (Fn t) := fun t =>
    (hc.comp (hpt.comp (Continuous.prodMk continuous_id continuous_const))).mul hψc
  have hFn'_cont : ∀ t, Continuous (Fn' t) := fun t =>
    (hD.comp (hpt.comp (Continuous.prodMk continuous_id continuous_const))).mul hψc

  have hK : IsCompact (C ×ˢ Set.Icc (-2 : ℝ) 2) := hCc.prod isCompact_Icc
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn (f := fun p : (AdeleRing (𝓞 K) K) × ℝ =>
    archDerivAt hw d φ (unipotentGL2 p.1 * g * archFlowAt hw d p.2)) (hD.comp hpt).continuousOn
  obtain ⟨M₂, hM₂⟩ := hCc.exists_bound_of_continuousOn
    (f := fun x : (AdeleRing (𝓞 K) K) => ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)))
    hψc.continuousOn
  have hM₁0 : 0 ≤ M₁ := by
    obtain ⟨x₀, hx₀⟩ : B.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have := adelicAddHaar_adelicBox_pos K
      rw [← hB, h, measure_empty] at this
      exact lt_irrefl _ this
    exact (norm_nonneg _).trans (hM₁ ⟨x₀, 0⟩ ⟨hBC hx₀, by norm_num, by norm_num⟩)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict B) (F := Fn)
    (F' := Fn') (x₀ := (0 : ℝ)) (bound := fun _ => M₁ * M₂) (s := Set.Icc (-2 : ℝ) 2)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t => (hFn_cont t).aestronglyMeasurable)
    (by
      obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (f := Fn 0) (hFn_cont 0).continuousOn
      exact Measure.integrableOn_of_bounded hBfin.ne (hFn_cont 0).aestronglyMeasurable
        (ae_restrict_of_forall_mem hBmeas fun x hx => hM x (hBC hx)))
    (hFn'_cont 0).aestronglyMeasurable
    (by
      refine ae_restrict_of_forall_mem hBmeas fun x hx t ht => ?_
      rw [hFn', norm_mul]
      exact mul_le_mul (hM₁ ⟨x, t⟩ ⟨hBC hx, ht⟩) (hM₂ x (hBC hx)) (norm_nonneg _) hM₁0)
    (integrableOn_const hBfin.ne)
    (by
      refine ae_restrict_of_forall_mem hBmeas fun x hx t ht => ?_
      exact (hasDerivAt_flow_of_isArchSmoothAt hs d (unipotentGL2 x * g) t).mul_const _)
  have h2 := key.2
  simp only [hFn', archFlowAt_zero, mul_one] at h2
  exact h2

theorem hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφs : IsArchSmoothAt hw φ)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d φ))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' φ)))
    (g₀ : AdelicGL2 (𝓞 K) K) :
    (∀ (d : ArchDir) (h : GL (Fin 2) ℝ),
        HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (φ) 1 (g₀ * archRealGLAt hw (h * archFlowMatrix d t)))
          (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d φ) 1 (g₀ * archRealGLAt hw h)) 0) ∧
    (∀ (d d' : ArchDir) (h : GL (Fin 2) ℝ),
        HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d' φ) 1 (g₀ * archRealGLAt hw (h * archFlowMatrix d t)))
          (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d (archDerivAt hw d' φ)) 1 (g₀ * archRealGLAt hw h)) 0) ∧
    (∀ h : GL (Fin 2) ℝ,
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archCasimirAt hw φ) 1 (g₀ * archRealGLAt hw h) =
          -((1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw .H (archDerivAt hw .H φ)) 1 (g₀ * archRealGLAt hw h)
            - (1 / 2 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw .H φ) 1 (g₀ * archRealGLAt hw h)
            + whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw .E (archDerivAt hw .Fm φ)) 1 (g₀ * archRealGLAt hw h))) := by
  classical
  let _ : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  have _ : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  set μ : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμ
  set B : Set (AdeleRing (𝓞 K) K) := adelicBox K with hB
  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
  have hW : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) f 1 g =
        ((μ B)⁻¹).toReal • ∫ x in B, f (unipotentGL2 x * g) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ := by
    intro f g
    unfold whittakerCoefficient
    dsimp only [productionPinsOf]
    exact integral_smul_measure _ _
  have hflow : ∀ (h : GL (Fin 2) ℝ) (d : ArchDir) (t : ℝ) (x : (AdeleRing (𝓞 K) K)),
      unipotentGL2 x * (g₀ * archRealGLAt hw (h * archFlowMatrix d t)) =
        unipotentGL2 x * (g₀ * archRealGLAt hw h) * archFlowAt hw d t := by
    intro h d t x; simp only [map_mul, archFlowAt, mul_assoc]

  have core : ∀ (φ' : AdelicGL2 (𝓞 K) K → ℂ), Continuous φ' → IsArchSmoothAt hw φ' →
      ∀ d : ArchDir, Continuous (archDerivAt hw d φ') → ∀ h : GL (Fin 2) ℝ,
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ' 1 (g₀ * archRealGLAt hw (h * archFlowMatrix d t)))
        (whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (archDerivAt hw d φ') 1 (g₀ * archRealGLAt hw h)) 0 := by
    intro φ' hc' hs' d hD' h
    have hk := (hasDerivAt_setIntegral_flow K hw d φ' hc' hs' hD'
      (NumberField.StandardAddChar.stdAddChar K) hψ 1
      (g₀ * archRealGLAt hw h)).const_smul ((μ B)⁻¹).toReal
    have hfun : (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ' 1 (g₀ * archRealGLAt hw (h * archFlowMatrix d t))) =
        fun t : ℝ => ((μ B)⁻¹).toReal • ∫ x in B, φ' (unipotentGL2 x * (g₀ * archRealGLAt hw h) * archFlowAt hw d t) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ := by
      funext t; rw [hW]; simp only [hflow]
    rw [hfun, hW]
    exact hk
  refine ⟨fun d h => core φ hφc hφs d (hD1 d) h,
    fun d d' h => core (archDerivAt hw d' φ) (hD1 d') (hφs.archDerivAt d') d (hD2 d d') h, ?_⟩

  intro h
  set G : AdelicGL2 (𝓞 K) K := g₀ * archRealGLAt hw h with hG
  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset K
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top K
  have hBmeas : MeasurableSet B := measurableSet_adelicBox K
  have hint : ∀ f : AdelicGL2 (𝓞 K) K → ℂ, Continuous f →
      IntegrableOn (fun x => f (unipotentGL2 x * G) * NumberField.StandardAddChar.stdAddChar K
        (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) B μ := by
    intro f hf
    have hcf : Continuous (fun x => f (unipotentGL2 x * G) *
        NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) :=
      (hf.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)).mul continuous_const)).mul
        (hψ.comp ((continuous_const.mul continuous_id).neg))
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (f := fun x => f (unipotentGL2 x * G) *
      NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) hcf.continuousOn
    exact Measure.integrableOn_of_bounded hBfin.ne hcf.aestronglyMeasurable
      (ae_restrict_of_forall_mem hBmeas fun x hx => hM x (hBC hx))
  have hA := hint _ (hD2 .H .H)
  have hBf := hint _ (hD1 .H)
  have hCf := hint _ (hD2 .E .Fm)
  rw [hW, hW, hW, hW]
  have hcas : (fun x => archCasimirAt hw φ (unipotentGL2 x * G) *
        NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) =
      fun x => -((1 / 4 : ℂ) * (archDerivAt hw .H (archDerivAt hw .H φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        - (1 / 2 : ℂ) * (archDerivAt hw .H φ (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        + archDerivAt hw .E (archDerivAt hw .Fm φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) := by
    funext x
    simp only [archCasimirAt, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcas, integral_neg]
  have h1 : ∫ x in B, ((1 / 4 : ℂ) * (archDerivAt hw .H (archDerivAt hw .H φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        - (1 / 2 : ℂ) * (archDerivAt hw .H φ (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        + archDerivAt hw .E (archDerivAt hw .Fm φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x))) ∂μ =
      (1 / 4 : ℂ) * ∫ x in B, archDerivAt hw .H (archDerivAt hw .H φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ
      - (1 / 2 : ℂ) * ∫ x in B, archDerivAt hw .H φ (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ
      + ∫ x in B, archDerivAt hw .E (archDerivAt hw .Fm φ) (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ := by
    have hfg : Integrable (fun x => (1 / 4 : ℂ) * (archDerivAt hw .H (archDerivAt hw .H φ)
          (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))
        - (1 / 2 : ℂ) * (archDerivAt hw .H φ (unipotentGL2 x * G) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)))) (μ.restrict B) :=
      (hA.const_mul _).sub (hBf.const_mul _)
    rw [integral_add hfg hCf, integral_sub (hA.const_mul _) (hBf.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [h1]
  simp only [Complex.real_smul]
  ring

/-! ### The flow's continuity and derivative -/

private theorem continuous_archFlowMatrixComplex_apply (d : ArchDirComplex) (i j : Fin 2) :
    Continuous fun t : ℝ => (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  have c1 : Continuous fun s : ℝ => (s : ℂ) := Complex.continuous_ofReal
  have c2 : Continuous fun s : ℝ => (s : ℂ) * Complex.I :=
    Complex.continuous_ofReal.mul continuous_const
  have c3 : Continuous fun s : ℝ => Complex.exp (s : ℂ) := Complex.continuous_exp.comp c1
  have c4 : Continuous fun s : ℝ => Complex.exp (-(s : ℂ)) := Complex.continuous_exp.comp c1.neg
  have c5 : Continuous fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I) :=
    Complex.continuous_exp.comp c2
  have c6 : Continuous fun s : ℝ => Complex.exp (-((s : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp c2.neg
  cases d <;> fin_cases i <;> fin_cases j <;>
    simp only [archFlowMatrixComplex, splitTorusGL2Complex_coe, unipotentGL2_coe,
      lowerUnipotentGL2_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first
      | exact continuous_const
      | exact c3 | exact c4 | exact c5 | exact c6 | exact c1 | exact c2

private theorem archFlowAtComplex_coe_apply {F : Type} [Field F] [NumberField F]
    {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) (i j : Fin 2) :
    ((archFlowAtComplex hw d t : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (archMatrixUpdate F w ((glEquivOfRingEquiv
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
          (archFlowMatrixComplex d t) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) := rfl

private theorem archFlowAtComplex_neg {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}
    (hw : w.IsComplex) (d : ArchDirComplex) (t : ℝ) :
    archFlowAtComplex hw d (-t) = (archFlowAtComplex hw d t)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← archFlowAtComplex_add, neg_add_cancel, archFlowAtComplex_zero]

private theorem continuous_archFlowAtComplex {F : Type} [Field F] [NumberField F]
    {w : InfinitePlace F} (hw : w.IsComplex) (d : ArchDirComplex) :
    Continuous fun t : ℝ => archFlowAtComplex hw d t := by
  have hval : Continuous fun t : ℝ =>
      ((archFlowAtComplex hw d t : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have hfun : (fun t : ℝ => ((archFlowAtComplex hw d t : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) =
        fun t : ℝ => (archMatrixUpdate F w ((glEquivOfRingEquiv
            (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm
            (archFlowMatrixComplex d t) : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion) i j,
          (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) :=
      funext fun t => archFlowAtComplex_coe_apply hw d t i j
    rw [hfun]
    refine Continuous.prodMk ?_ continuous_const
    refine continuous_pi fun v => ?_
    by_cases hv : v = w
    · subst hv
      refine ((NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.comp
        (continuous_archFlowMatrixComplex_apply d i j)).congr fun t => ?_
      simp only [archMatrixUpdate_apply_self, glEquivOfRingEquiv_apply_entry]
      rfl
    · refine (continuous_const :
        Continuous fun _ : ℝ => (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j).congr fun t => ?_
      exact (archMatrixUpdate_apply_of_ne F w _ i j hv).symm
  rw [Units.continuous_iff]
  refine ⟨hval, ?_⟩
  have hfin : (fun t : ℝ => (((archFlowAtComplex hw d t)⁻¹ : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
      fun t : ℝ => ((archFlowAtComplex hw d (-t) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    funext t
    rw [archFlowAtComplex_neg]
  rw [hfin]
  exact hval.comp continuous_neg

private theorem hasDerivAt_flow_of_isArchSmoothAtComplex {F : Type} [Field F] [NumberField F]
    {w : InfinitePlace F} {hw : w.IsComplex} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex) (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (g * archFlowAtComplex hw d s))
      (archDerivAtComplex hw d φ (g * archFlowAtComplex hw d t)) t := by
  have h0 : HasDerivAt (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s))
      (archDerivAtComplex hw d φ (g * archFlowAtComplex hw d t)) 0 :=
    (IsArchSmoothAtComplex.differentiableAt_flow hφ d (g * archFlowAtComplex hw d t)).hasDerivAt
  have hsub : HasDerivAt (fun s : ℝ => s - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have h0' : HasDerivAt (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s))
      (archDerivAtComplex hw d φ (g * archFlowAtComplex hw d t)) ((fun s : ℝ => s - t) t) := by
    simp only [sub_self]
    exact h0
  have h1 := HasDerivAt.scomp (𝕜 := ℝ) t (h := fun s : ℝ => s - t) h0' hsub
  rw [one_smul] at h1
  refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  show φ (g * archFlowAtComplex hw d s) =
    φ (g * archFlowAtComplex hw d t * archFlowAtComplex hw d (s - t))
  have hst : t + (s - t) = s := by ring
  rw [mul_assoc, ← archFlowAtComplex_add, hst]

/-! ### Differentiation under the integral -/

private theorem hasDerivAt_setIntegral_flowComplex (K : Type) [Field K] [NumberField K]
    {w : InfinitePlace K} (hw : w.IsComplex) (d : ArchDirComplex)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hc : Continuous φ) (hs : IsArchSmoothAtComplex hw φ)
    (hD : Continuous (archDerivAtComplex hw d φ))
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : Continuous ψ) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    letI : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
    HasDerivAt (fun t : ℝ => ∫ x in adelicBox K,
        φ (unipotentGL2 x * g * archFlowAtComplex hw d t) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))
          ∂(adelicAddHaar (𝓞 K) K))
      (∫ x in adelicBox K, archDerivAtComplex hw d φ (unipotentGL2 x * g) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))
        ∂(adelicAddHaar (𝓞 K) K)) 0 := by
  let m : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  have hb : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  set μ : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμ
  set B : Set (AdeleRing (𝓞 K) K) := adelicBox K with hB
  obtain ⟨C, hCc, hBC⟩ := exists_isCompact_adelicBox_subset K
  have hBfin : μ B < ⊤ := adelicAddHaar_adelicBox_lt_top K
  have hBmeas : MeasurableSet B := measurableSet_adelicBox K
  set Fn : ℝ → (AdeleRing (𝓞 K) K) → ℂ := fun t x =>
    φ (unipotentGL2 x * g * archFlowAtComplex hw d t) * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) with hFn
  set Fn' : ℝ → (AdeleRing (𝓞 K) K) → ℂ := fun t x =>
    archDerivAtComplex hw d φ (unipotentGL2 x * g * archFlowAtComplex hw d t) *
      ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) with hFn'
  have hpt : Continuous fun p : (AdeleRing (𝓞 K) K) × ℝ =>
      unipotentGL2 p.1 * g * archFlowAtComplex hw d p.2 :=
    (((continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K)).comp continuous_fst).mul continuous_const).mul
      ((continuous_archFlowAtComplex hw d).comp continuous_snd)
  have hψc : Continuous fun x : (AdeleRing (𝓞 K) K) => ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x)) :=
    hψ.comp ((continuous_const.mul continuous_id).neg)
  have hFn_cont : ∀ t, Continuous (Fn t) := fun t =>
    (hc.comp (hpt.comp (Continuous.prodMk continuous_id continuous_const))).mul hψc
  have hFn'_cont : ∀ t, Continuous (Fn' t) := fun t =>
    (hD.comp (hpt.comp (Continuous.prodMk continuous_id continuous_const))).mul hψc
  have hK : IsCompact (C ×ˢ Set.Icc (-2 : ℝ) 2) := hCc.prod isCompact_Icc
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn (f := fun p : (AdeleRing (𝓞 K) K) × ℝ =>
    archDerivAtComplex hw d φ (unipotentGL2 p.1 * g * archFlowAtComplex hw d p.2)) (hD.comp hpt).continuousOn
  obtain ⟨M₂, hM₂⟩ := hCc.exists_bound_of_continuousOn
    (f := fun x : (AdeleRing (𝓞 K) K) => ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))) hψc.continuousOn
  have hM₁0 : 0 ≤ M₁ := by
    obtain ⟨x₀, hx₀⟩ : B.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have := adelicAddHaar_adelicBox_pos K
      rw [← hB, h, measure_empty] at this
      exact lt_irrefl _ this
    exact (norm_nonneg _).trans (hM₁ ⟨x₀, 0⟩ ⟨hBC hx₀, by norm_num, by norm_num⟩)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict B) (F := Fn) (F' := Fn')
    (x₀ := (0 : ℝ)) (bound := fun _ => M₁ * M₂) (s := Set.Icc (-2 : ℝ) 2)
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t => (hFn_cont t).aestronglyMeasurable)
    (by
      obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (f := Fn 0) (hFn_cont 0).continuousOn
      exact Measure.integrableOn_of_bounded hBfin.ne (hFn_cont 0).aestronglyMeasurable
        (ae_restrict_of_forall_mem hBmeas fun x hx => hM x (hBC hx)))
    (hFn'_cont 0).aestronglyMeasurable
    (by
      refine ae_restrict_of_forall_mem hBmeas fun x hx t ht => ?_
      rw [hFn', norm_mul]
      exact mul_le_mul (hM₁ ⟨x, t⟩ ⟨hBC hx, ht⟩) (hM₂ x (hBC hx)) (norm_nonneg _) hM₁0)
    (integrableOn_const hBfin.ne)
    (by
      refine ae_restrict_of_forall_mem hBmeas fun x hx t ht => ?_
      exact (hasDerivAt_flow_of_isArchSmoothAtComplex hs d (unipotentGL2 x * g) t).mul_const _)
  have h2 := key.2
  simp only [hFn', archFlowAtComplex_zero, mul_one] at h2
  exact h2

/-! ### The complex mirror: the same three steps at a complex place -/

theorem hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφs : IsArchSmoothAtComplex hw φ)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d φ))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' φ)))
    (g₀ : AdelicGL2 (𝓞 K) K) :
    (∀ (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
        HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (φ) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
          (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d φ) 1 (g₀ * archComplexGLAt hw h)) 0) ∧
    (∀ (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
        HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' φ) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
          (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (archDerivAtComplex hw d' φ)) 1 (g₀ * archComplexGLAt hw h)) 0) := by
  classical
  let m : MeasurableSpace (AdeleRing (𝓞 K) K) := adeleBorel (𝓞 K) K
  have hb : BorelSpace (AdeleRing (𝓞 K) K) := borelSpace_adeleBorel (𝓞 K) K
  set μ : Measure (AdeleRing (𝓞 K) K) := adelicAddHaar (𝓞 K) K with hμ
  set B : Set (AdeleRing (𝓞 K) K) := adelicBox K with hB
  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
  have hW : ∀ (f : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) f 1 g =
        ((μ B)⁻¹).toReal • ∫ x in B, f (unipotentGL2 x * g) *
          NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ := by
    intro f g
    unfold whittakerCoefficient
    dsimp only [productionPinsOf]
    exact integral_smul_measure _ _
  have hflow : ∀ (h : GL (Fin 2) ℂ) (d : ArchDirComplex) (t : ℝ) (x : (AdeleRing (𝓞 K) K)),
      unipotentGL2 x * (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t)) =
        unipotentGL2 x * (g₀ * archComplexGLAt hw h) * archFlowAtComplex hw d t := by
    intro h d t x
    simp only [map_mul, archFlowAtComplex, mul_assoc]
  have core : ∀ (φ' : AdelicGL2 (𝓞 K) K → ℂ), Continuous φ' → IsArchSmoothAtComplex hw φ' →
      ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d φ') → ∀ h : GL (Fin 2) ℂ,
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ' 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
        (whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d φ') 1 (g₀ * archComplexGLAt hw h)) 0 := by
    intro φ' hc' hs' d hD' h
    have hk := (hasDerivAt_setIntegral_flowComplex K hw d φ' hc' hs' hD' (NumberField.StandardAddChar.stdAddChar K)
      hψ 1 (g₀ * archComplexGLAt hw h)).const_smul ((μ B)⁻¹).toReal
    have hfun : (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) φ' 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t))) =
        fun t : ℝ => ((μ B)⁻¹).toReal • ∫ x in B, φ' (unipotentGL2 x * (g₀ * archComplexGLAt hw h) *
          archFlowAtComplex hw d t) * NumberField.StandardAddChar.stdAddChar K (-(algebraMap K (AdeleRing (𝓞 K) K) 1 * x)) ∂μ := by
      funext t
      rw [hW]
      simp only [hflow]
    rw [hfun, hW]
    exact hk
  exact ⟨fun d h => core φ hφc hφs d (hD1 d) h,
    fun d d' h => core (archDerivAtComplex hw d' φ) (hD1 d') (IsArchSmoothAtComplex.archDerivAtComplex hφs d') d
      (hD2 d d') h⟩

/-! ## The coefficient's API, VII: the unipotent average at a `diagOne` point

The identity a Rankin–Selberg unfolding uses to read a coefficient at `diagOne` off a sum of
unipotent translates: for `G` invariant under the left unipotent and a finite set `ι` of adelic
parameters whose unipotent translates commute with `g`, the coefficient of the averaged
function is the character-weighted sum times the coefficient of the un-averaged one. -/

theorem whittakerCoefficient_finset_sum_mul_unipotentGL2_diagOne_mul
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (G : AdelicGL2 (𝓞 F) F → ℂ)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F) (h : AdelicGL2 (𝓞 F) F),
      G (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * h) = G (unipotentGL2 u * h))
    (ι : Finset (AdeleRing (𝓞 F) F)) (c : AdeleRing (𝓞 F) F → ℂ)
    (α : F) (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F)
    (hcomm : ∀ y ∈ ι, g * unipotentGL2 y = unipotentGL2 y * g)
    (hint : ∀ y ∈ ι, WhittakerCoefficientIntegrable F (productionPinsOf F D U gen (adelicBox F)) ψ
      (fun x => G (x * unipotentGL2 y)) α (diagOne a * g)) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ
        (fun x => ∑ y ∈ ι, c y * G (x * unipotentGL2 y)) α (diagOne a * g) =
      (∑ y ∈ ι, c y * ψ (algebraMap F (AdeleRing (𝓞 F) F) α * ((a : AdeleRing (𝓞 F) F) * y))) *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ G α (diagOne a * g) := by
  classical
  set pins := productionPinsOf F D U gen (adelicBox F) with hpins

  have hconj : ∀ y : AdeleRing (𝓞 F) F,
      diagOne a * unipotentGL2 y = unipotentGL2 ((a : AdeleRing (𝓞 F) F) * y) * diagOne a := by
    intro y
    apply Units.ext
    ext i j
    simp only [Units.val_mul, diagOne_coe_apply, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp

  have hterm : ∀ y ∈ ι,
      whittakerCoefficient F pins ψ (fun x => G (x * unipotentGL2 y)) α (diagOne a * g) =
        ψ (algebraMap F (AdeleRing (𝓞 F) F) α * ((a : AdeleRing (𝓞 F) F) * y)) *
          whittakerCoefficient F pins ψ G α (diagOne a * g) := by
    intro y hy
    have h1 : whittakerCoefficient F pins ψ (fun x => G (x * unipotentGL2 y)) α (diagOne a * g) =
        whittakerCoefficient F pins ψ G α (unipotentGL2 ((a : AdeleRing (𝓞 F) F) * y) * (diagOne a * g)) := by
      simp only [whittakerCoefficient]
      congr 1
      funext x
      congr 2
      rw [mul_assoc, mul_assoc, hcomm y hy, ← mul_assoc (diagOne a), hconj y, mul_assoc, ← mul_assoc]
    rw [h1, hpins]
    exact AutomorphicForm.whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ G (diagOne a * g)
      (fun β u => hper β u _) α _

  have hI : ∀ y ∈ ι, Integrable (fun x : AdeleRing (𝓞 F) F =>
      G (unipotentGL2 x * (diagOne a * g) * unipotentGL2 y) *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) pins.ν := by
    intro y hy
    have := hint y hy
    simp only [WhittakerCoefficientIntegrable] at this
    exact this
  have hlin : whittakerCoefficient F pins ψ (fun x => ∑ y ∈ ι, c y * G (x * unipotentGL2 y)) α (diagOne a * g) =
      ∑ y ∈ ι, c y * whittakerCoefficient F pins ψ (fun x => G (x * unipotentGL2 y)) α (diagOne a * g) := by
    simp only [whittakerCoefficient]
    rw [show (fun x : AdeleRing (𝓞 F) F => (∑ y ∈ ι, c y * G (unipotentGL2 x * (diagOne a * g) * unipotentGL2 y)) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) =
        fun x => ∑ y ∈ ι, c y * (G (unipotentGL2 x * (diagOne a * g) * unipotentGL2 y) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) from
      funext fun x => by rw [Finset.sum_mul]; simp only [mul_assoc]]
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
    · intro y hy
      exact (hI y hy).const_mul (c y)
  rw [hlin, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [hterm y hy, mul_assoc]


end AutomorphicForm

end
