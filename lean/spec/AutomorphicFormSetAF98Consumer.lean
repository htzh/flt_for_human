/-
  SET-AF98 consumer: the archimedean Whittaker system read quantitatively, and the shell bound read
  at the trivial compact point.

  **The rows.** `AutomorphicForm/Adelic/WhittakerSystem.lean` (order A) states the global Whittaker
  coefficient's archimedean system at a real and at a complex place, with the `diagOne` profile's
  second-order Whittaker equation among its conclusions;
  `AutomorphicForm/Adelic/WhittakerDiagOneBound.lean` (order B) bounds the coefficient at `diagOne`
  at a complex place by a power of the torus coordinate;
  `AutomorphicForm/Adelic/RankinSelbergShellIndicator.lean` (order C) states the shell-surgery bound
  of the Rankin–Selberg unfolding; `AutomorphicForm/Adelic/RankinSelbergTorusIntegral.lean` and
  `…/BorelFundamentalDomain.lean` (order D) are its measure-theoretic floor, and
  `LanglandsTunnell/IsotypicCuspSubmodule.lean` (order E) the spectral-decomposition step.

  **The reading.** Both theorems turn a stated system into the shape its next consumer reads: the
  archimedean equation is solved for the profile's second derivative (the form an integral comparison
  against a growth bound uses), and the `∃ δ ∃ C` bound is evaluated at the unramified torus point of
  its own hypotheses (the form the cuspidal-constituent row consumes). Each deletes a module if that
  module is removed, so the pair is the set's real cross-module composition.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF98Consumer.lean` and never enters the build.
-/

import FLTForHuman.AutomorphicForm.Adelic.WhittakerSystem
import FLTForHuman.AutomorphicForm.Adelic.WhittakerDiagOneBound
import FLTForHuman.AutomorphicForm.Adelic.RankinSelbergShellIndicator

set_option autoImplicit false
noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent
open scoped ENNReal NNReal

namespace AutomorphicFormSetAF98Consumer

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

/-- **The archimedean equation solved for the second derivative.** At a real place, the `diagOne`
profile of the global Whittaker coefficient is twice differentiable and its second derivative is
the Casimir polynomial times its value over `y²` — the form in which the equation is integrated
against a growth bound. -/
theorem profile_second_deriv_eq
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ) (lam : ℂ) (ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hφs : IsArchSmoothAt hw φ)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d φ))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' φ)))
    (hφΩ : archCasimirAt hw φ = lam • φ)
    (hφn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) φ)
    (g₀ : AdelicGL2 (𝓞 K) K) (hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    let f : ℝ → ℂ := fun y =>
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1
        (g₀ * archRealLiftAt hw (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]))
    ∀ y : ℝ, 0 < y →
      deriv (deriv f) y =
        -((1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * n : ℝ) : ℂ) * (y : ℂ)
            - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y) / ((y : ℂ) ^ 2) := by
  intro f y hy
  obtain ⟨-, -, hode⟩ :=
    whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
      K D w hw n lam ν hν φ hφc hper hφs hD1 hD2 hφΩ hφn g₀ hg₀ ε hε
  have hy0 : ((y : ℂ)) ^ 2 ≠ 0 := by
    have : (y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hy
    exact pow_ne_zero 2 this
  rw [eq_div_iff hy0]
  linear_combination hode y hy


/-- **The `diagOne` bound at an unramified torus point.** Reading the `∃ δ ∃ C` bound at the
`b` of the hypotheses — the idele that is a unit at the finite places and fixed at the other
infinite places — is the form the cuspidal growth analysis consumes. -/
theorem norm_whittakerCoefficient_diagOne_le_at_b
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hE₁ : E₁ 0 = 1) (hE₂ : E₂ 0 = 1)
    (hE₁' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₁ s i j)
      (if (i : ℕ) = j + 1 then 1 else if (j : ℕ) = i + 1 then -((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hE₂' : ∀ i j : Fin (n + 1), HasDerivAt (fun s : ℝ => E₂ s i j)
      (if (i : ℕ) = j + 1 then Complex.I else if (j : ℕ) = i + 1 then Complex.I * ((j : ℂ) * ((n : ℂ) + 1 - j)) else 0) 0)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₂ s p' p * x p' g)
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p)
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖
        ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (hU : lam' = (starRingEnd ℂ) lam)
    (hR : lam' = lam → lam.im = 0 → n = 0 ∨ -(((n : ℝ) ^ 2 + 4 * (n : ℝ)) / 16) < lam.re)
    (hZ : lam = 0 → n = 0 → ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℂ),
      Matrix.GeneralLinearGroup.det h = 1 → x 0 (g * archComplexGLAt hw h) = x 0 g)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ p : Fin (n + 1),
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
          (diagOne b)‖ ≤
        C * ‖((b : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((b : AdeleRing (𝓞 K) K)).1 w‖) ^ δ := by
  obtain ⟨δ, hδ, C, hC⟩ :=
    exists_norm_whittakerCoefficient_diagOne_le_min_norm_rpow_of_isComplex_of_su2String
      K D ξ w₀ hξ w hw n x hxc hxG hxZ hreg hwt E₁ E₂ hE₁ hE₂ hE₁' hE₂' hK₁ hK₂ lam lam' hcas hgr hU hR hZ b hb
  exact ⟨δ, hδ, C, fun p => hC p b hb (fun w' _ => rfl)⟩

end AutomorphicFormSetAF98Consumer
