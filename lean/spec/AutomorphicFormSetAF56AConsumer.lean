/-
  SET-AF56A consumer: the flat level-spherical test functions.

  **The zone.** Three rows in two modules, hence three executed compositions:

  * `FLTForHuman/AutomorphicForm/Adelic/RightConvProductIntegral.lean` (A):
    `AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq`;
  * `FLTForHuman/AutomorphicForm/Adelic/Cusp/LevelSphericalTestFn.lean` (B, C):
    `AutomorphicForm.CuspidalSpectrum.isFactorizableTestFn_flat` and
    `AutomorphicForm.CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType`.

  **The readings.**

  * Zone A. The reproducing-convolution row is a constant `C > 0` together with the identity
    `rightConv … = C * ∫ …`. The consumer *spends* the constant twice over: it carries the
    positivity into the vanishing statement, so that the convolved form vanishes at `g` exactly
    when the archimedean integral `∫ a, x (g * adelicArchGLIncl a) * h a` does. That is the
    reading the (non-)vanishing estimates use: a positive multiple cannot kill or create zeros.
  * Zone B. `isFactorizableTestFn_flat` is a closure property of the test functions under the
    conjugated-inverted modulus twist `flat`. The consumer *iterates* it: two twists, two
    applications, `flat σ₂ (flat σ₁ f)` is again a factorizable test function.
  * Zone C. The level-spherical row produces an operator `S` commuting with the lift `Tc`, whose
    action on a level-`N` member is the Hecke coset sum. The consumer *composes it with a right
    convolution*: through the lift dictionary `Tc (φ) = ⟨rightConv F φ f⟩` the commutation reads
    `S ⟨rightConv F φ f⟩ = Tc (S φ)` — the identity moved past the right convolution rather than
    past the abstract lift.

  Statement-level data (`hΦ₀`, `hσ`, `hrep`, `h1`–`h3`, `T`, `reps`, `U`) cannot be instantiated
  concretely — they are properties of an arbitrary slab fundamental domain, modulus, reproducing
  kernel and Hecke covering — so they enter in hypothesis form, which is the legitimate reading
  for these rows.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvProductIntegral
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelSphericalTestFn

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm.SetAF56AConsumer

/-! ### Zone A: the reproducing constant, spent on a vanishing statement -/

section repro

variable (F : Type) [Field F] [NumberField F]
variable [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
variable [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
variable (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
variable [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
variable (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →*
  GL (Fin 2) (InfiniteAdeleRing F))
variable [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F))]
variable [BorelSpace (GL (Fin 2) (InfiniteAdeleRing F))]
variable (μa : Measure (GL (Fin 2) (InfiniteAdeleRing F)))
variable [μa.IsHaarMeasure] [μa.IsMulRightInvariant]
variable (U : Subgroup (AdelicGL2 (𝓞 F) F))

/-- **Zone A.** The reproducing-convolution identity, read at the level of zeros: because the
constant `C` is positive, the right convolution of `x` against the product integral times the
level indicator vanishes at `g` exactly when the archimedean integral does. -/
theorem consumer_A_vanishing_iff
    (hιc : Continuous ι)
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (hUf : U ≤ finiteAdelicGL2Subgroup F)
    (hUo : IsOpen ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (hUc : IsCompact ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))))
    (e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ) (he : Continuous e)
    (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hhc : Continuous h) (hhK : HasCompactSupport h)
    (hconj : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
      (y : GL (Fin 2) (InfiniteAdeleRing F)),
        h (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = h y)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hxc : Continuous x)
    (hxU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, x (g * u) = x g)
    (hrep : ∀ z : AdelicGL2 (𝓞 F) F,
      ∫ κ, e κ * x (z * adelicArchGLIncl F (ι κ)) ∂μ = x z) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : AdelicGL2 (𝓞 F) F,
      (rightConv F x
            (fun y => (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
                e p.1 * e p.2 * h ((ι p.1)⁻¹ * glArch (𝓞 F) F y * (ι p.2)⁻¹) ∂(μ.prod μ)) *
              Set.indicator ((glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)) (glFin (𝓞 F) F y)) g
          = 0 ↔ ∫ a, x (g * adelicArchGLIncl F a) * h a ∂μa = 0) := by
  obtain ⟨C, hC, hrow⟩ :=
    AutomorphicForm.exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq
      F μ ι hιc hι μa U hUf hUo hUc
  refine ⟨C, hC, fun g => ?_⟩
  rw [hrow e he h hhc hhK hconj x hxc hxU hrep g]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with h0 | h0
    · exact absurd h0 (by exact_mod_cast hC.ne')
    · exact h0
  · intro hzero
    rw [hzero, mul_zero]

end repro

/-! ### Zone B: the modulus twist is closed, iterated once -/

section flatTwist

variable (F : Type) [Field F] [NumberField F]

/-- **Zone B.** Iterated closure: the conjugated-inverted modulus twist of a conjugated-inverted
modulus twist of a factorizable test function is again factorizable. -/
theorem consumer_B_flat_iterate (σ₁ σ₂ : ℝ) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsFactorizableTestFn F f) :
    IsFactorizableTestFn F (flat F σ₂ (flat F σ₁ f)) :=
  CuspidalSpectrum.isFactorizableTestFn_flat F σ₂ (flat F σ₁ f)
    (CuspidalSpectrum.isFactorizableTestFn_flat F σ₁ f hf)

end flatTwist

/-! ### Zone C: the commuting operator, composed with a right convolution -/

section commuteLift

variable (F : Type) [Field F] [NumberField F]

/-- **Zone C.** The level-spherical row, composed with a right convolution: the operator `S`
commuting with the lift `Tc` also moves past the right convolution, i.e. through the dictionary
`Tc (φ) = ⟨rightConv F φ f⟩` the commutation reads `S ⟨rightConv F φ f⟩ = Tc (S φ)`. -/
theorem consumer_C_commute_through_rightConv
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hσ : HasModulus F ξ σ) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N) f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F) (n : ℕ)
    (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (h1 : ∀ i, ∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, ∃ u'' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, reps i = u' * g * u'')
    (h2 : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, ∃ u'' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, x = u' * g * u'') → ∃ i, ∃ u' ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N, x = reps i * u')
    (h3 : ∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N → i = j)
    (φ : ↥(cuspMemberSubmodule F Φ₀ ξ))
    (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      S.comp Tc = Tc.comp S ∧
        S (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩) =
          Tc (S (toCuspSubcarrier F hΦ₀ σ ξ φ)) := by
  obtain ⟨S, hS, -⟩ :=
    CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType
      F c u d₁ d₂ T hΦ₀ σ ξ hσ N hN tys f hf hsph Tc hcomm g hg n reps h1 h2 h3
  refine ⟨S, hS, ?_⟩
  rw [← hcomm φ hφ']
  simpa only [ContinuousLinearMap.comp_apply] using
    congrArg (fun A : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) =>
      A (toCuspSubcarrier F hΦ₀ σ ξ φ)) hS

end commuteLift

end AutomorphicForm.SetAF56AConsumer
