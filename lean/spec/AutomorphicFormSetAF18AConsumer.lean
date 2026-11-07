/-
  SET-AF18A consumer: the twisted pairing at `(u * g, v)` read off the pairing at `(u, v * g*)`.

  The headline of `AutomorphicForm/Adelic/RightConvAdjoint.lean` is the adjointness of right
  convolution for the `|det|^{-σ}`-twisted pairing on a fundamental domain `Φ₀`: for a pair `u`, `v`
  of `ξ`-eigen square-integrable functions and a continuous compactly supported test function `g`,
  the convolutions `u * g` and `v * g*` are again `L²`, and

  `∫_{Φ₀} (u * g) x conj (v x) |det x|^{-σ} = ∫_{Φ₀} u x conj ((v * g*) x) |det x|^{-σ}`,

  where `g* y = conj (g y⁻¹) |det y|^{-σ}` is the adjoint kernel of `|det|^{-σ}`-weighted
  convolution.

  **This zone.** The kernel is written out (`adjKernel`), the two `MemLp` conjuncts are kept as
  explicit conjuncts (they are what makes both sides of the identity honest Bochner integrals), and
  the pairing is read in the direction the statement asks for: the pairing of the convolved kernel
  `(u * g, v)` is the pairing `(u, v * g*)` against the un-convolved kernel. Since `g ↦ g*` is an
  involution (`adjKernel_adjKernel`), the adjointness at `g*` in turn returns the pairing at the
  original kernel — the adjoint operation is inverted by itself.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvAdjoint
import FLTForHuman.AutomorphicForm.Adelic.RightTranslateAdjoint

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.InfinitePlace NumberField.AdelicLevel NumberField.AdelicHaar
open AutomorphicForm
open scoped ComplexConjugate NNReal ENNReal

-- the pin's wrappers register the adelic Borel space as a local instance for these statements
-- (`Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean:11`)
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm
namespace LocalIntertwining

/-- The adjoint kernel of `|det|^{-σ}`-weighted convolution: `g* y = conj (g y⁻¹) |det y|^{-σ}`. -/
def adjKernel (K : Type) [Field K] [NumberField K] (σ : ℝ)
    (g : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => conj (g y⁻¹) *
    ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)

/-- `ideleNorm` inverts, from multiplicativity. The port carries this only as `private` copies
(`Adelic/RightTranslateAdjoint.lean:92`, `Adelic/RightConvAdjoint.lean:154`,
`Adelic/Siegel/SlabCovering.lean:352`); promoting one is the manager's call. -/
theorem ideleNorm_inv_consumer (K : Type) [Field K] [NumberField K]
    (c : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K c⁻¹ = (NumberField.TateGlobal.ideleNorm K c)⁻¹ := by
  have h1 : NumberField.TateGlobal.ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
    have h := NumberField.TateGlobal.ideleNorm_mul (F := K) 1 1
    rw [mul_one] at h
    exact (mul_right_cancel₀ (NumberField.TateGlobal.ideleNorm_pos (F := K) 1).ne'
      (h.symm.trans (one_mul _).symm))
  have h := NumberField.TateGlobal.ideleNorm_mul (F := K) c c⁻¹
  rw [mul_inv_cancel, h1] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- The adjoint kernel is an involution: `(g*)* = g`. -/
theorem adjKernel_adjKernel (K : Type) [Field K] [NumberField K] (σ : ℝ)
    (g : AdelicGL2 (𝓞 K) K → ℂ) : adjKernel K σ (adjKernel K σ g) = g := by
  funext y
  have hpos : 0 < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hinv : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y⁻¹) =
      (NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y))⁻¹ := by
    rw [map_inv]
    exact ideleNorm_inv_consumer K _
  -- `(g*) (y⁻¹)`, in closed form: `(ideleNorm (det y)⁻¹) ^ (-σ)` is `ideleNorm (det y) ^ σ`
  have hval : adjKernel K σ g y⁻¹ =
      conj (g y) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) := by
    simp only [adjKernel, inv_inv, hinv, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv]
  calc adjKernel K σ (adjKernel K σ g) y
      = conj ((adjKernel K σ g) y⁻¹) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ) :=
        rfl
    _ = conj (conj (g y) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ)) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ) := by
        rw [hval]
    _ = g y := by
        rw [map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_assoc, ← Complex.ofReal_mul,
          Real.rpow_neg hpos.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos σ).ne',
          Complex.ofReal_one, mul_one]

/-- **Zone (order A).** The adjointness of right convolution for the twisted pairing, at the level
of a pair `u`, `v` of `ξ`-eigen functions: the two convolutions are `L²` on `Φ₀`, the pairing of
`(u * g, v)` is the pairing of `(u, v * g*)` — with `g* y = conj (g y⁻¹) |det y|^{-σ}` explicit —
and, because `g ↦ g*` is an involution, the same adjointness at `g*` returns the pairing at the
original kernel `g`. -/
theorem consumer_zoneA_rightConv_adjoint
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (u v : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hv : IsLsXiFunction (𝓞 K) K ⊤ ξ v)
    (huc : Continuous u) (hvc : Continuous v)
    (hu₂ : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hg'c : Continuous (adjKernel K σ g)) (hg's : HasCompactSupport (adjKernel K σ g)) :
    -- the two `MemLp` conjuncts: both convolved functions are square-integrable on `Φ₀`
    MemLp (rightConv K u g) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (rightConv K v (adjKernel K σ g)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    -- the pairing at `(u * g, v)` is the pairing at `(u, v * g*)`
    (∫ x in Φ₀, rightConv K u g x * conj (v x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in Φ₀, u x * conj (rightConv K v (adjKernel K σ g) x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    -- read backwards: the pairing at `(u, v * g*)` determines the pairing at `(u * g, v)`
    (∫ x in Φ₀, u x * conj (rightConv K v (adjKernel K σ g) x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in Φ₀, rightConv K u g x * conj (v x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    -- the adjoint operation is inverted by itself: at `g*` it returns the pairing at `g`
    (MemLp (rightConv K u (adjKernel K σ g)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
      ∫ x in Φ₀, rightConv K u (adjKernel K σ g) x * conj (v x) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
        ∫ x in Φ₀, u x * conj (rightConv K v g x) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  obtain ⟨h1, h2, h3⟩ :=
    adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ u v hu hv
      huc hvc hu₂ hv₂ g hg hgc
  refine ⟨h1, h2, h3, h3.symm, ?_⟩
  -- the same adjointness at the adjoint kernel, whose adjoint kernel is `g` again
  obtain ⟨h1', h2', h3'⟩ :=
    adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ u v hu hv
      huc hvc hu₂ hv₂ (adjKernel K σ g) hg'c hg's
  -- the headline states the kernel as a `fun`-term; read it back as `adjKernel` and collapse `(g*)*`
  have h3'' : ∫ x in Φ₀, rightConv K u (adjKernel K σ g) x * conj (v x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in Φ₀, u x * conj (rightConv K v (adjKernel K σ (adjKernel K σ g)) x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := h3'
  rw [adjKernel_adjKernel] at h3''
  exact ⟨h1', h3''⟩

end LocalIntertwining
end AutomorphicForm
