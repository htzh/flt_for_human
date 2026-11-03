/-
  SET-AF17 consumer: the three compositions this set's headlines are for.

  **Zone 1 (order A) — the twisted pairing at `y` read off the pairing at `y⁻¹`.** The adjointness
  headline says `⟨R_y u, v⟩ = |det y|^σ · ⟨u, R_{y⁻¹} v⟩` on a fundamental domain, with the two
  `MemLp` side conditions that make every pairing in sight an honest Bochner integral. Reading the
  same identity backwards divides the character factor out:
  `⟨u, R_{y⁻¹} v⟩ = |det y|^{-σ} · ⟨R_y u, v⟩` — the pairing at `y` determines the pairing at `y⁻¹`
  with the `|det y|^σ` twist explicit. The `MemLp` conjuncts are not decoration: they are exactly the
  `AEStronglyMeasurable` hypotheses the two sides of the integral identity are read with.

  **Zone 2 (order B) — differentiating the Casimir of a right convolution along the unipotent flow.**
  Row 2 differentiates `t ↦ rightConv x f (g · n(t v))` at `0`, with derivative `rightConv x (∂_v f)`
  and with `∂_v f` again factorizable; row 3 commutes both Casimirs past a right convolution. Composed:
  `t ↦ archCasimirAtComplex (rightConv x f) (g · n(t v))` is differentiable at `0`, with derivative
  `archCasimirAtComplex (rightConv x (∂_v f)) g` — the Casimir and the unipotent derivative commute.
  The two side conditions are exactly row 2's: continuity of the convolved function (here
  `archCasimirAtComplex x`, continuous because it is a finite combination of the archimedean
  derivatives the hypotheses make continuous) and factorizability of `∂_v f`.

  **Zone 3 (order C) — what preservation feeds.** The preservation row returns cuspidality,
  `K_f`-smoothness, level invariance and the Hecke-eigen property of `rightConv R.toFun f`, the first
  conjunct being an `@`-applied `IsCuspidalFn`. Unfolding that definitional form turns it into the
  vanishing of the unipotent constant term
  `g ↦ ∫ q, rightConv R.toFun f (unipotentGL2 q * g) ∂ν`, which together with the level invariance is
  the pair of facts the cuspidal-spectrum development consumes.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightTranslateAdjoint
import FLTForHuman.AutomorphicForm.Adelic.RightConvDerivatives
import FLTForHuman.AutomorphicForm.Adelic.RightConvStructurePreservation

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.InfinitePlace NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SmoothCusp
open Filter Set Topology Complex
open scoped NNReal ComplexConjugate ProbabilityTheory

-- the pin's wrappers register the adelic Borel space as a local instance for these statements
-- (`Definitions/Def_AutomorphicForm_AdelicMaximalCompact.lean:11`)
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm
namespace LocalIntertwining

/-! ### Zone 1 (order A) — the pairing at `y` and the pairing at `y⁻¹` -/

/-- **Zone 1.** For a pair `u`, `v` of `ξ`-eigen square-integrable functions on a fundamental domain
`Φ₀` inside a determinant window, the right translate `u (· * y)`, the inverse right translate
`v (· * y⁻¹)` are again `L²`, and the twisted pairing at `y` is `|det y|^σ` times the pairing at
`y⁻¹`; dividing the character factor out reads the pairing at `y⁻¹` off the pairing at `y`. -/
theorem consumer_zoneA_rightTranslate_adjoint
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
    (y : AdelicGL2 (𝓞 K) K) :
    MemLp (fun x => u (x * y)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (fun x => v (x * y⁻¹)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    -- the pairing at `y` is `|det y|^σ` times the pairing at `y⁻¹`
    (∫ x in Φ₀, u (x * y) * conj (v x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
        ∫ x in Φ₀, u x * conj (v (x * y⁻¹)) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
    -- ... and read backwards: the pairing at `y⁻¹` is the pairing at `y` over `|det y|^σ`
    (∫ x in Φ₀, u x * conj (v (x * y⁻¹)) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ) *
        ∫ x in Φ₀, u (x * y) * conj (v x) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by
  obtain ⟨h1, h2, h3⟩ :=
    rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ u v hu hv
      huc hvc hu₂ hv₂ y
  refine ⟨h1, h2, h3, ?_⟩
  -- the `MemLp` conjuncts are what the two integrals are measurable against
  have hm1 : AEStronglyMeasurable (fun x => u (x * y)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) :=
    h1.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x => v (x * y⁻¹)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) :=
    h2.aestronglyMeasurable
  have hpos : (0 : ℝ) < NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) :=
    NumberField.TateGlobal.ideleNorm_pos _
  have hne : ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hpos σ).ne'
  have _ := hm1
  have _ := hm2
  rw [h3, Real.rpow_neg hpos.le]
  push_cast
  exact (inv_mul_cancel_left₀ hne _).symm

/-! ### Zone 2 (order B) — the Casimir commutes with the unipotent derivative -/

/-- **Zone 2.** With `x` continuous and archimedean-smooth with continuous first and second
`archDerivAtComplex` derivatives, and `f` factorizable: differentiating
`archCasimirAtComplex (rightConv x f)` along the unipotent flow `t ↦ g * n(t v)` at `0` gives
`archCasimirAtComplex (rightConv x (∂_v f)) g`. The two side conditions are row 2's — `rightConv x f`
is continuous (row 3) and `∂_v f` is factorizable (row 2) — and the identification of the two
derivative values is row 3's Casimir commutation. -/
theorem consumer_zoneB_casimir_unipotent_deriv
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAtComplex hw x)
    (hD1 : ∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d x))
    (hD2 : ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' x)))
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (tys tys' : ArchTypeFamily K) (hbf : IsArchBiFinite K tys f)
    (hbfv : ∀ v : mixedEmbedding.mixedSpace K,
      IsArchBiFinite K tys' (fun y => deriv (fun t : ℝ =>
        f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0)) :
    ∀ (v : mixedEmbedding.mixedSpace K) (g : AdelicGL2 (𝓞 K) K),
      HasDerivAt (fun t : ℝ => archCasimirAtComplex hw (rightConv K x f)
          (g * unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0)))
        (archCasimirAtComplex hw (rightConv K x (fun y => deriv (fun t : ℝ =>
          f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0)) g) 0 := by
  intro v g
  -- row 2: the unipotent derivative, with `∂_v f` again factorizable
  obtain ⟨hderiv, hfact, -⟩ :=
    hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear K x hxc f hf
  -- row 3: the Casimir commutes past the convolution with `x`
  have hrow3 := archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex
    K w hw x hxc hxs hD1 hD2
  obtain ⟨-, hDconv, -, hcas, -⟩ := hrow3 f tys hf hbf
  -- the Casimir of `x` is continuous: a finite combination of archimedean derivatives
  have hwordcont : ∀ k : Fin 10,
      Continuous (ComplexCasimirComm.word (archDerivAtComplex hw) x k) := by
    intro k
    fin_cases k <;> simp only [ComplexCasimirComm.word, Matrix.cons_val_zero, Fin.zero_eta, Fin.mk_one,
      Fin.isValue] <;> first | exact hD2 _ _ | exact hD1 _
  have hcontcas : Continuous (archCasimirAtComplex hw x) := by
    have hsum : archCasimirAtComplex hw x = fun y => ∑ k : Fin 10,
        ComplexCasimirComm.coef (-Complex.I) k *
          ComplexCasimirComm.word (archDerivAtComplex hw) x k y :=
      funext fun y => ComplexCasimirComm.casimir_apply_eq_sum hw hxs y
    rw [hsum]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (hwordcont k)
  -- row 2 at the Casimir of `x`: differentiating the commuted family
  have hd := (hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear
    K (archCasimirAtComplex hw x) hcontcas f hf).1 v g
  -- the family is the Casimir of the convolved family (row 3)
  rw [show (fun t : ℝ => archCasimirAtComplex hw (rightConv K x f)
        (g * unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0)))
      = fun t : ℝ => rightConv K (archCasimirAtComplex hw x) f
          (g * unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v), 0)) from
    funext fun t => congrFun hcas _]
  -- and its derivative is the Casimir of the derived convolution (row 3 at `∂_v f`)
  have hcasv : archCasimirAtComplex hw (rightConv K x (fun y => deriv (fun t : ℝ =>
      f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0)) =
      rightConv K (archCasimirAtComplex hw x) (fun y => deriv (fun t : ℝ =>
        f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0) :=
    (hrow3 (fun y => deriv (fun t : ℝ =>
        f (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0) tys'
      (hfact v) (hbfv v)).2.2.2.1
  rw [hcasv]
  exact hd

/-! ### Zone 3 (order C) — cuspidality unfolded, and level invariance read at `k` -/

/-- **Zone 3.** The preservation row's output, fed into `IsCuspidalFn`'s definitional form: the
`@`-applied cuspidality conjunct is the vanishing of the unipotent constant term
`g ↦ ∫ q, rightConv R.toFun f (unipotentGL2 q * g) ∂ν`, and the level invariance can be read at any
`k` in the level subgroup. -/
theorem consumer_zoneC_preservation_unfolded
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (Ψ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Ψ)
    (hcont : Continuous R.toFun)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
      glFin (𝓞 K) K a = 1 ∧ k ∈ levelOne (𝓞 K) K Ψ.level ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) :
    (∀ g : AdelicGL2 (𝓞 K) K,
        ∫ q, rightConv K R.toFun f (unipotentGL2 q * g)
          ∂((adelicAddHaar (𝓞 K) K)[|adelicBox K]) = 0) ∧
      IsKfSmooth K (rightConv K R.toFun f) ∧
      (∀ (k : AdelicGL2 (𝓞 K) K),
        k ∈ levelOne (𝓞 K) K Ψ.level ⊓ finiteAdelicGL2Subgroup K →
          ∀ g : AdelicGL2 (𝓞 K) K,
            rightConv K R.toFun f (g * k) = rightConv K R.toFun f g) := by
  obtain ⟨hcus, hkf, hlev, -⟩ :=
    isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset
      K c u d₁ d₂ T Ψ R hcont f hf hfs
  refine ⟨fun g => ?_, hkf, fun k hk g => hlev g k hk⟩
  -- `IsCuspidalFn` is `∀ g, constantTerm μ unipotentGL2 · g = 0`, and `constantTerm` is the integral
  exact hcus g

end LocalIntertwining
end AutomorphicForm
