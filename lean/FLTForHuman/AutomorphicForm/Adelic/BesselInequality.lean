/-
  The Bessel inequality for the Whittaker coefficient, and the character basis behind it.

  `AutomorphicForm.sum_norm_whittakerCoefficient_sq_le_integral_norm_sq`: for a global additive
  character `ψ`, an integrable family of coefficient functions and a finite set `A` of rational
  parameters, `∑_{α ∈ A} ‖W_ψ φ α g‖ ^ 2 ≤ ∫ u, ‖φ (u · g)‖ ^ 2` against the box-normalized measure.
  The proof exhibits the characters `ech ψ α u = ψ (α · u)` as an orthonormal family in `L²` of the
  box-normalized adèle ring: each is a unit-modulus continuous function (`continuous_ech`,
  `norm_ech`), hence `L²` (`memLp_ech`), their inner products are the character integrals
  (`integral_addChar_mul_eq_zero`), which makes them orthonormal (`orthonormal_ech`), and Bessel's
  inequality for the coefficients of an orthonormal family (`norm_toLp_sq`, `inner_toLp`) finishes.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq.lean`, whose label
  namespace `Bessel17` is renamed to the module's `BesselInequality`, and whose `main` is the headline
  at the graph node's name.  The box-normalized measure `nuBox` and the conditional-probability
  instance are the pin's own.

  spec-pin: P2M/Sol/S_AutomorphicForm_sum_norm_whittakerCoefficient_sq_le_integral_norm_sq.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicBox NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

namespace AutomorphicForm

namespace BesselInequality

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

abbrev nuBox : Measure (AdeleRing (𝓞 F) F) := ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)

-- v4.34 binder drift: the pin's section variable `F` is implicit from here on, as its own Lean
-- inserted it; the port spells it out so `ech ψ α` and the two instances elaborate (`nuBox` keeps
-- its explicit `F`, which is what `nuBox F` in the statements below calls).
variable {F}

scoped instance : IsProbabilityMeasure (nuBox F) := isProbabilityMeasure_cond_adelicBox F

scoped instance countablePrincipal : Countable ↥(AdeleRing.principalSubgroup (𝓞 F) F) := by
  have : Countable F := Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm
  refine Function.Surjective.countable (f := fun k : F =>
    (⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩ : ↥(AdeleRing.principalSubgroup (𝓞 F) F))) ?_
  rintro ⟨_, k, rfl⟩
  exact ⟨k, rfl⟩

theorem setIntegral_adelicBox_comp_add_right (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u in adelicBox F, G (u + x) ∂(adelicAddHaar (𝓞 F) F) =
      ∫ u in adelicBox F, G u ∂(adelicAddHaar (𝓞 F) F) := by
  set μ := adelicAddHaar (𝓞 F) F with hμ
  have h1 : ∫ u in adelicBox F, G (u + x) ∂μ = ∫ w in (fun u => u + x) '' adelicBox F, G w ∂μ := by
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

theorem integral_nuBox_comp_add_right (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u, G (u + x) ∂(nuBox F) = ∫ u, G u ∂(nuBox F) := by
  simp only [nuBox, ProbabilityTheory.cond, integral_smul_measure,
    setIntegral_adelicBox_comp_add_right G hG x]

theorem integral_addChar_mul_eq_zero {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {γ : F} (hγ : γ ≠ 0) :
    ∫ u, ψ (algebraMap F (AdeleRing (𝓞 F) F) γ * u) ∂(nuBox F) = 0 := by
  set a := algebraMap F (AdeleRing (𝓞 F) F) γ with ha
  set I := ∫ u, ψ (a * u) ∂(nuBox F) with hI
  have hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      ψ (a * (algebraMap F (AdeleRing (𝓞 F) F) β + u)) = ψ (a * u) := by
    intro β u
    rw [mul_add, AddChar.map_add_eq_mul, ha, ← (algebraMap F (AdeleRing (𝓞 F) F)).map_mul,
      hψ.principalInvariant, one_mul]
  have hshift : ∀ x, ψ (a * x) * I = I := by
    intro x
    have h := integral_nuBox_comp_add_right (fun u => ψ (a * u)) hper x
    simp only [mul_add, AddChar.map_add_eq_mul] at h
    rw [integral_mul_const] at h
    rw [mul_comm]
    exact h
  by_contra hne
  have hone : ∀ x, ψ (a * x) = 1 := fun x =>
    mul_left_injective₀ hne ((hshift x).trans (one_mul I).symm)
  apply hψ.nontrivial
  ext y
  have hy : y = a * (algebraMap F (AdeleRing (𝓞 F) F) γ⁻¹ * y) := by
    rw [← mul_assoc, ha, ← map_mul, mul_inv_cancel₀ hγ, map_one, one_mul]
  rw [hy, hone, AddChar.one_apply]


variable (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
  (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)

theorem productionPinsOf_ν_eq : (productionPinsOf F D U gen (adelicBox F)).ν = nuBox F := rfl

variable {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}

def ech (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (u : AdeleRing (𝓞 F) F) : ℂ :=
  ψ (algebraMap F (AdeleRing (𝓞 F) F) α * u)

theorem continuous_ech (hψ : IsGlobalAddChar F ψ) (α : F) : Continuous (ech ψ α) :=
  hψ.continuous.comp (continuous_const.mul continuous_id)

theorem norm_ech (hψ : IsGlobalAddChar F ψ) (α : F) (u : AdeleRing (𝓞 F) F) : ‖ech ψ α u‖ = 1 :=
  norm_apply_eq_one_of_isGlobalAddChar F hψ _

theorem memLp_ech (hψ : IsGlobalAddChar F ψ) (α : F) : MemLp (ech ψ α) 2 (nuBox F) :=
  MemLp.of_bound (continuous_ech hψ α).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun u => (norm_ech hψ α u).le)

theorem conj_ech (hψ : IsGlobalAddChar F ψ) (α : F) (u : AdeleRing (𝓞 F) F) :
    conj (ech ψ α u) = ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * u)) := by
  rw [ech, AddChar.map_neg_eq_inv,
    Complex.inv_eq_conj (norm_apply_eq_one_of_isGlobalAddChar F hψ _)]

theorem memLp_of_continuous {h : AdeleRing (𝓞 F) F → ℂ} (hh : Continuous h) : MemLp h 2 (nuBox F) := by
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hh.continuousOn
  refine MemLp.of_bound hh.aestronglyMeasurable M ?_
  have : ∀ᵐ u ∂((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)), ‖h u‖ ≤ M :=
    (ae_restrict_iff' (measurableSet_adelicBox F)).mpr
      (Filter.Eventually.of_forall fun u hu => hM u (hBC hu))
  exact Measure.ae_smul_measure this _

theorem inner_toLp {f g : AdeleRing (𝓞 F) F → ℂ} (hf : MemLp f 2 (nuBox F)) (hg : MemLp g 2 (nuBox F)) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ u, conj (f u) * g u ∂(nuBox F) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with u hfu hgu
  rw [hfu, hgu, RCLike.inner_apply, mul_comm]

theorem norm_toLp_sq {f : AdeleRing (𝓞 F) F → ℂ} (hf : MemLp f 2 (nuBox F)) :
    ‖hf.toLp f‖ ^ 2 = ∫ u, ‖f u‖ ^ 2 ∂(nuBox F) := by
  conv_lhs => rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [inner_toLp hf hf]
  have : (fun u => conj (f u) * f u) = fun u => ((‖f u‖ ^ 2 : ℝ) : ℂ) := funext fun u => by
    rw [Complex.conj_mul', Complex.ofReal_pow]
  rw [this]
  have h2 : ∫ u, ((‖f u‖ ^ 2 : ℝ) : ℂ) ∂(nuBox F) = ((∫ u, ‖f u‖ ^ 2 ∂(nuBox F) : ℝ) : ℂ) :=
    integral_ofReal
  rw [h2]
  exact Complex.ofReal_re _

theorem orthonormal_ech (hψ : IsGlobalAddChar F ψ) :
    Orthonormal ℂ (fun α : F => (memLp_ech hψ α).toLp (ech ψ α)) := by
  classical
  rw [orthonormal_iff_ite]
  intro α β
  rw [inner_toLp]
  have hprod : ∀ u, conj (ech ψ α u) * ech ψ β u =
      ψ (algebraMap F (AdeleRing (𝓞 F) F) (β - α) * u) := by
    intro u
    rw [conj_ech hψ, ech, ← AddChar.map_add_eq_mul, map_sub]
    congr 1
    ring
  simp_rw [hprod]
  by_cases h : α = β
  · subst h
    simp
  · rw [ite_eq_right h]
    exact integral_addChar_mul_eq_zero hψ (sub_ne_zero.mpr (Ne.symm h))

end BesselInequality

/-- Bessel's inequality for the Whittaker coefficient: the squared Whittaker coefficients of a
square-integrable family, summed over a finite set of parameters, are bounded by its `L²` norm. -/
theorem sum_norm_whittakerCoefficient_sq_le_integral_norm_sq
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hcont : Continuous fun u : AdeleRing (𝓞 F) F => φ (unipotentGL2 u * g))
    (A : Finset F) :
    ∑ α ∈ A, ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 ≤
      ∫ u, ‖φ (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν := by
  set h : AdeleRing (𝓞 F) F → ℂ := fun u => φ (unipotentGL2 u * g) with hh
  have hmem : MemLp h 2 (BesselInequality.nuBox F) := BesselInequality.memLp_of_continuous hcont
  have hW : ∀ α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g =
      inner ℂ ((BesselInequality.memLp_ech hψ α).toLp (BesselInequality.ech ψ α)) (hmem.toLp h) := by
    intro α
    rw [BesselInequality.inner_toLp]
    show (∫ x, φ (unipotentGL2 x * g) *
        ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂(BesselInequality.nuBox F)) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show φ (unipotentGL2 u * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * u)) =
      conj (BesselInequality.ech ψ α u) * h u
    rw [BesselInequality.conj_ech hψ, mul_comm]
  show ∑ α ∈ A, ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g‖ ^ 2 ≤
      ∫ u, ‖h u‖ ^ 2 ∂(BesselInequality.nuBox F)
  simp_rw [hW, ← BesselInequality.norm_toLp_sq hmem]
  exact (BesselInequality.orthonormal_ech hψ).sum_inner_products_le _

end AutomorphicForm

end
