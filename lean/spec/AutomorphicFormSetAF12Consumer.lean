/-
  SET-AF12 consumer zone — the real-place Whittaker equation at the local component of the
  adelic coefficient.

  `gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight` (SET-AF12, order A row 1)
  is instantiated at the local component of the global coefficient,

    `F h := whittakerCoefficient K pins (stdAddChar K) φ 1 (g₀ * archRealGLAt hw h)`,

  whose derivative hypotheses are AF11's `hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt`
  (its first conjunct for `hD`, its second for `hDHH` and `hDEF`) and whose Casimir equation `hΩ`
  is that row's Casimir conjunct together with the eigenvalue relation `hΩφ`. `hCas`, the
  coefficient-level form of `hΩφ`, is obtained from the module's additivity row
  `whittakerCoefficient_sum_smul_of_continuous` (`m = 1`).

  The two local equivariance laws `hN` (unipotent character of frequency `ε`) and `hK` (weight
  `n` under the row-isometry subgroup) are hypotheses here: deriving them from the adelic
  transformation law needs the `stdAddChar` evaluation at a real place
  (`NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal`), which is not ported.

  The conclusion is the classical statement the three unported consumer rows need: the profile
  `y ↦ whittakerCoefficient … (g₀ * archRealGLAt hw (splitTorusGL2 (Real.log y / 2)))` is twice
  differentiable on `y > 0` and satisfies the Whittaker equation
  `y² f'' + (1/4 − ν² + 2π ε n y − 4π² y²) f = 0`.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchWhittaker
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicLevel
  NumberField.AdelicHaar NumberField.AdelicVolume
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
open LocalGL2 AdelicDock

namespace AutomorphicForm

theorem whittakerCoefficient_archRealGLAt_splitTorus_satisfies_whittaker_ode
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (w : InfinitePlace K) (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφc : Continuous φ) (hφs : IsArchSmoothAt hw φ)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d φ))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' φ)))
    (g₀ : AdelicGL2 (𝓞 K) K)
    (pins : CarrierPins K)
    (hpins : pins = productionPinsOf K D
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (n : ℤ) (lam ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam)
    (hΩφ : ∀ h : AdelicGL2 (𝓞 K) K, archCasimirAt hw φ h = lam * φ h)
    (hN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      whittakerCoefficient K pins (NumberField.StandardAddChar.stdAddChar K) φ 1
        (g₀ * archRealGLAt hw (unipotentGL2 x * h)) =
      Complex.exp (2 * Real.pi * Complex.I * ((ε : ℂ) * (x : ℂ))) *
        whittakerCoefficient K pins (NumberField.StandardAddChar.stdAddChar K) φ 1
          (g₀ * archRealGLAt hw h))
    (hK : ∀ (k : GL (Fin 2) ℝ) (hk : k ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
      whittakerCoefficient K pins (NumberField.StandardAddChar.stdAddChar K) φ 1
        (g₀ * archRealGLAt hw (h * k)) =
      ((archWeightCharℝ n ⟨k, hk⟩ : ℂˣ) : ℂ) *
        whittakerCoefficient K pins (NumberField.StandardAddChar.stdAddChar K) φ 1
          (g₀ * archRealGLAt hw h)) :
    let f : ℝ → ℂ := fun y =>
      whittakerCoefficient K pins (NumberField.StandardAddChar.stdAddChar K) φ 1
        (g₀ * archRealGLAt hw (splitTorusGL2 (Real.log y / 2)))
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * n : ℝ) : ℂ) * (y : ℂ)
                - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0 := by
  classical
  rw [hpins] at *
  have hψc : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
  have hWsmul : ∀ (c : ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (fun x => c * φ x) 1 g =
      c * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g := by
    intro c g
    have h := whittakerCoefficient_sum_smul_of_continuous K D
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) (NumberField.StandardAddChar.stdAddChar K) hψc
      1 (fun _ => φ) (fun _ => hφc) (fun _ => c) 1 g
    simpa using h
  have hCas : ∀ h : GL (Fin 2) ℝ,
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archCasimirAt hw φ) 1
        (g₀ * archRealGLAt hw h) =
      lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g₀ * archRealGLAt hw h) := by
    intro h
    rw [show archCasimirAt hw φ = fun x => lam * φ x from funext hΩφ]
    exact hWsmul lam _
  obtain ⟨hD, hDD, hCasim⟩ :=
    hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt K D w hw φ hφc hφs hD1 hD2 g₀
  exact gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
    (fun h => whittakerCoefficient K _ (NumberField.StandardAddChar.stdAddChar K) φ 1
      (g₀ * archRealGLAt hw h))
    ε hε n lam ν hν
    (fun d h => whittakerCoefficient K _ (NumberField.StandardAddChar.stdAddChar K)
      (archDerivAt hw d φ) 1 (g₀ * archRealGLAt hw h))
    (fun h => whittakerCoefficient K _ (NumberField.StandardAddChar.stdAddChar K)
      (archDerivAt hw .H (archDerivAt hw .H φ)) 1 (g₀ * archRealGLAt hw h))
    (fun h => whittakerCoefficient K _ (NumberField.StandardAddChar.stdAddChar K)
      (archDerivAt hw .E (archDerivAt hw .Fm φ)) 1 (g₀ * archRealGLAt hw h))
    hD (fun h => hDD .H .H h) (fun h => hDD .E .Fm h)
    (fun h => (hCasim h).symm.trans (hCas h)) hN hK

end AutomorphicForm

end
