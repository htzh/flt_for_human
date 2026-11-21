/-
  The global Whittaker coefficient as an archimedean Whittaker system.

  The adelic Whittaker coefficient of an automorphic function, evaluated along the diagonal torus at
  a place `w`, is the local Whittaker function of that place. The three statements here are that
  identification's archimedean content, at a real and at a complex place.

  At a real place, the profile `f y = W (g₀ * archRealLiftAt hw (diag (ε √y, (√y)⁻¹)))` is twice
  differentiable on `y > 0` and satisfies the classical Whittaker equation

    `y² f'' + (1/4 - ν² + 2π ε n y - 4π² y²) f = 0`,   `ν² = 1/4 - lam`,

  with `lam` the Casimir eigenvalue and `n` the character's weight — the second-order equation whose
  solutions are the archimedean Whittaker functions. The same profile vanishes identically on the
  determinant-one torus once the lowering operator has been iterated enough times and the last
  iterate is only polynomially bounded there: the equation has no solution that is small at the
  origin and polynomially bounded at infinity unless it is zero.

  At a complex place the coefficient of a `Fin (n + 1)`-family of circle-weight vectors obeys the
  whole system: the two flow derivatives act by the Casimir eigenvalues `lam`, `lam'`, the unipotent
  acts by the character `exp (2 π i · 2 Re z)`, the circle acts by the weight, and the two Casimir
  equations transport the `k`-type indices up and down by the matrices `E₁`, `E₂`. That is the
  coupled `𝔰𝔩₂` Whittaker system of the place.

  The two real-place rows share their archimedean engines (the Iwasawa calculus of the two lift
  charts, the sign-twisted diagonal, the unipotent character laws) and are written once here. The
  local profile equation lives in the archimedean Whittaker module; the coefficient's own API is
  what this module consumes and does not restate.

  **Reuse.** 39 of the pins' 105 declarations are already in the port and are imported, not
  re-proved: `ElemLR` (`ArchCasimir.lean`) carries `glArch_ext`, `glArch_archRealGLAt`,
  `archComponent_glArch_archRealGLAt_self`/`_of_ne`, `glFin_archRealGLAt` and
  `archRealGLAt_mul_comm_of_archComponent_eq_one`; `NumberField.AdelicLevel.ArchLevel`
  (`ArchLevelLattice.lean`) and `NumberField.TateGlobal` (`IdeleNormValues.lean`) carry the
  `diagOne`/`centralScalar` component dictionary and the three `_unipotentGL2` rows; `DCFN`
  (`WhittakerDiagOne.lean`) carries `eC`, `iotaW`, `bprime`, `g0`, `W`, `Fstr`/`DFstr`/`DDstr`/
  `fstr`, the two `whittakerCoefficient_*` rows, `glInf_ext`, `archComplexGLAt_mul_comm_…`,
  `archComponent_glArch_g0` and `archComplexGLAt_mul_g0`; and the archimedean engines
  `hasDerivAt_whittakerCoefficient_archFlow{,Complex}_of_continuous_archDerivAt{,Complex}`,
  `whittakerCoefficient_unipotentGL2_mul`, `gl2Real_whittaker_ode_…`,
  `iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul` and
  `eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow` are this module's premises. What is
  transcribed is the residue: the pin's real-place `TorusOdeAux` engine, the whole `DiagOneZero`
  development (the pin's 41 `private` helpers, kept `private`), and the complex-place Casimir
  dictionary `casWords`/`casCoeff`/`casBarCoeff` with the `k`-type transport. The pin's private
  `W` is `DCFN.W`'s statement; `splitTorus_mul_unipotent` is the real-place row (the port's is the
  complex one), so both are local.

  **Drift** (mathlib `v4.34.0`). `AdeleRing` and `InfinitePlace.Completion` being `def`s, the pin's
  `((1 : …ˣ) : AdeleRing …).1 w` is only type-correct at `default` transparency and poisons every
  later `simp`/`rw` (FR-0238/FR-0257): the two unipotent-character steps restate the pin's point
  identity with the scalar already reduced to `1`. `Matrix.of` is no longer `fun f => f` and the
  `!![…]` literal is a `Matrix`, so the `k`-type rows prove `Matrix.of (!!…) = k` by `show` at the
  literal (the pin's `simp [Complex.ofReal_cos, …]` then needs no `Matrix.*` helper). The `!![…]`
  indexing lemmas the pin lists in `simp only` are split by which of them still fire. `letI :=
  pins.nS` → `let` and one `haveI` → `have`; `hδ`/`hyc` are `_`-prefixed (both dead in the pin).

  **Heartbeat probe** (never installed, FR-0225): silent at `maxHeartbeats=20000`, deterministic
  timeout at `10000` — so the natural per-declaration cost is ≲20 k, a 1/10 margin on the
  edit loop's cap and 1/200 on the build's.

  spec-pin: P2M/Sol/S_AutomorphicForm_whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses.lean
-/


import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.ArchWhittaker
import FLTForHuman.AutomorphicForm.Adelic.WhittakerDiagOne
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.Su2Strings
import FLTForHuman.NumberTheory.StandardAddChar.GlobalAndInfinite
import FLTForHuman.NumberTheory.AdelicLevel.ArchLevelLattice
import FLTForHuman.LanglandsTunnell.RankinSelberg.EulerPolyRecursion

set_option autoImplicit false

attribute [-ext] NumberField.InfinitePlace.Completion.ext

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm

/-! ## The real-place prelude

The pin states its real-place prelude twice, once per `S_` file. Most of it is already in the port
and is imported rather than re-proved: `AutomorphicForm.ElemLR` (`ArchCasimir.lean`) carries
`glArch_ext`, `glArch_archRealGLAt`, `archComponent_glArch_archRealGLAt_self`,
`archComponent_glArch_archRealGLAt_of_ne`, `glFin_archRealGLAt` and
`archRealGLAt_mul_comm_of_archComponent_eq_one`; `NumberField.AdelicLevel.ArchLevel`
(`ArchLevelLattice.lean`) and `NumberField.TateGlobal` (`IdeleNormValues.lean`) carry
`map_diagOne`, `map_scalar`, `scalar_coe_apply`, `archComponent_glArch_diagOne`,
`glFin_diagOne_of_snd_eq_one`, `archComponent_glArch_centralScalar` and
`glFin_centralScalar_of_snd_eq_one`.

What is left — `diagSign_mul_unipotent` (the pin ships it in both real-place files) and the two
coefficient-linearity rows — is written once here, at the pin's names, in the pin's own
`TorusOdeAux` namespace. -/

namespace TorusOdeAux

theorem diagSign_mul_unipotent (ε : ℝ) (hε0 : ε ≠ 0) (x : ℝ) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![ε, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hε0]) * unipotentGL2 x =
      unipotentGL2 (ε * x) * Matrix.GeneralLinearGroup.mkOfDetNeZero !![ε, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hε0]) := by
  ext i j
  simp only [Units.val_mul, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.mkOfDetNeZero]

variable (K : Type) [Field K] [NumberField K]

theorem whittakerCoefficient_smul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (c : ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ (c • φ) α g = c * whittakerCoefficient K pins ψ φ α g := by
  let := pins.nS
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1; funext x; simp [Pi.smul_apply, smul_eq_mul]; ring

theorem whittakerCoefficient_mul_of_rightChar
    (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (k : AdelicGL2 (𝓞 K) K) (c : ℂ) (hφ : ∀ g, φ (g * k) = c * φ g) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = c * whittakerCoefficient K pins ψ φ α g := by
  let := pins.nS
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [← mul_assoc, hφ]; ring

end TorusOdeAux

open TorusOdeAux

theorem whittakerCoefficient_diagOne_satisfies_whittaker_ode_of_archCasimirAt_eq_smul_of_hasArchCharacterAt
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
    DifferentiableOn ℝ f (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv f) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * n : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0
  := by
  intro f
  classical
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he_def
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hdetP : (!![ε, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    simp [Matrix.det_fin_two_of, hε0]
  let P : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![ε, 0; 0, 1] hdetP
  let g₁ : AdelicGL2 (𝓞 K) K := g₀ * archRealGLAt hw P
  let W : (AdelicGL2 (𝓞 K) K → ℂ) → AdelicGL2 (𝓞 K) K → ℂ := fun φ' g =>
    whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (φ') 1 (g)
  let F : GL (Fin 2) ℝ → ℂ := fun h => W φ (g₁ * archRealGLAt hw h)
  have hFg : ∀ h : GL (Fin 2) ℝ, g₀ * archRealGLAt hw (P * h) = g₁ * archRealGLAt hw h := by
    intro h; simp only [g₁, map_mul, mul_assoc]

  obtain ⟨hT1, hT2, hT3⟩ :=
    hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt K D w hw φ hφc hφs hD1 hD2 g₁
  let DF : ArchDir → GL (Fin 2) ℝ → ℂ := fun d h => W (archDerivAt hw d φ) (g₁ * archRealGLAt hw h)
  let DHH : GL (Fin 2) ℝ → ℂ := fun h => W (archDerivAt hw .H (archDerivAt hw .H φ)) (g₁ * archRealGLAt hw h)
  let DEF : GL (Fin 2) ℝ → ℂ := fun h => W (archDerivAt hw .E (archDerivAt hw .Fm φ)) (g₁ * archRealGLAt hw h)
  have hD : ∀ (d : ArchDir) (h : GL (Fin 2) ℝ), HasDerivAt (fun t : ℝ => F (h * archFlowMatrix d t)) (DF d h) 0 :=
    fun d h => hT1 d h
  have hDHH : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .H (h * archFlowMatrix .H t)) (DHH h) 0 :=
    fun h => hT2 .H .H h
  have hDEF : ∀ h : GL (Fin 2) ℝ, HasDerivAt (fun t : ℝ => DF .Fm (h * archFlowMatrix .E t)) (DEF h) 0 :=
    fun h => hT2 .E .Fm h
  have hΩ : ∀ h : GL (Fin 2) ℝ, -((1 / 4 : ℂ) * DHH h - (1 / 2 : ℂ) * DF .H h + DEF h) = lam * F h := by
    intro h
    have h3 := hT3 h
    show -((1 / 4 : ℂ) * W _ _ - (1 / 2 : ℂ) * W _ _ + W _ _) = lam * W φ _
    rw [← h3]
    show W (archCasimirAt hw φ) _ = _
    rw [hφΩ]
    exact whittakerCoefficient_smul K _ _ lam φ 1 _

  have hper' : ∀ (G : AdelicGL2 (𝓞 K) K) (β : K) (uA : (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uA) * G) = φ (unipotentGL2 uA * G) := by
    intro G β uA; rw [unipotentGL2_add, mul_assoc, hper]
  have hN : ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
      F (unipotentGL2 x * h) = Complex.exp (2 * Real.pi * Complex.I * (ε * x)) * F h := by
    intro x h
    dsimp only [F, W]
    have h1 : g₁ * archRealGLAt hw (unipotentGL2 x * h) =
        archRealGLAt hw (unipotentGL2 (ε * x)) * (g₁ * archRealGLAt hw h) := by
      have hc := ElemLR.archRealGLAt_mul_comm_of_archComponent_eq_one hw (unipotentGL2 (ε * x)) hg₀
      calc g₁ * archRealGLAt hw (unipotentGL2 x * h)
          = g₀ * (archRealGLAt hw (P * unipotentGL2 x)) * archRealGLAt hw h := by
            simp only [g₁, map_mul, mul_assoc]
        _ = g₀ * (archRealGLAt hw (unipotentGL2 (ε * x) * P)) * archRealGLAt hw h := by
            rw [diagSign_mul_unipotent ε hε0 x]
        _ = (g₀ * archRealGLAt hw (unipotentGL2 (ε * x))) * archRealGLAt hw P * archRealGLAt hw h := by
            simp only [map_mul, mul_assoc]
        _ = (archRealGLAt hw (unipotentGL2 (ε * x)) * g₀) * archRealGLAt hw P * archRealGLAt hw h := by rw [hc]
        _ = archRealGLAt hw (unipotentGL2 (ε * x)) * (g₁ * archRealGLAt hw h) := by
            simp only [g₁, mul_assoc]

    obtain ⟨hE, -⟩ := NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
      K w hw 1 (by rfl) (ε * x)
    rw [map_one, one_mul, mul_one] at hE
    dsimp only at hE
    -- `AdeleRing` is a `def`, so the pin's `((1 : …ˣ) : AdeleRing …).1 w` — a `Prod.fst` on an
    -- unfolded product — is only type-correct at `default` transparency and poisons every later
    -- `simp`/`rw`. Restate the pin's point identity with the scalar already reduced.
    have ha : (((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) :
        InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K).1 w = (1 : w.Completion) := by
      rw [Units.val_one]; rfl
    have hU : archRealGLAt hw (unipotentGL2 (ε * x)) =
        unipotentGL2 (show (AdeleRing (𝓞 K) K) from
          ((Pi.single w (e.symm (ε * x)), 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)) := by
      rw [hE, ha, one_mul]
    rw [h1, hU]
    have hcov := whittakerCoefficient_unipotentGL2_mul K D
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (NumberField.StandardAddChar.stdAddChar K)
      (NumberField.StandardAddChar.adelicTraceData K).isGlobalAddChar_psiK.principalInvariant φ
      (g₁ * archRealGLAt hw h) (hper' _) 1
      (show (AdeleRing (𝓞 K) K) from
        ((Pi.single w (e.symm (ε * x)), 0) : InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K))
    rw [hcov, map_one, one_mul]
    congr 1
    have hψ := NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal K w hw (ε * x)
    rw [← he_def] at hψ
    rw [hψ]; push_cast; ring_nf

  have he' : ∀ x : ℝ, ‖e.symm x‖ = ‖x‖ := fun x => by
    rw [← norm_ringEquivRealOfIsReal hw (e.symm x), ← he_def, e.apply_symm_apply]
  have hK : ∀ (k : GL (Fin 2) ℝ) (hk : k ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
      F (h * k) = ((archWeightCharℝ n ⟨k, hk⟩ : ℂˣ) : ℂ) * F h := by
    intro k hk h
    let k' : rowIsometrySubgroup₀ w.Completion := rowIsometrySubgroup₀Map e.symm he' ⟨k, hk⟩
    have hkk : archRealGLAt hw k = adelicArchGLInclAt K w (k' : GL (Fin 2) w.Completion) := rfl
    have hchar : archWeightCharAt hw n k' = archWeightCharℝ n ⟨k, hk⟩ := by
      show (zpowGroupHom n) (archWeightOneℝ (rowIsometrySubgroup₀Map e (norm_ringEquivRealOfIsReal hw)
        (rowIsometrySubgroup₀Map e.symm he' ⟨k, hk⟩))) = (zpowGroupHom n) (archWeightOneℝ ⟨k, hk⟩)
      congr 2
      apply Subtype.ext
      apply Units.ext
      ext i j
      show e (e.symm ((k : Matrix (Fin 2) (Fin 2) ℝ) i j)) = (k : Matrix (Fin 2) (Fin 2) ℝ) i j
      exact e.apply_symm_apply _
    dsimp only [F, W]
    rw [map_mul, ← mul_assoc, hkk]
    rw [whittakerCoefficient_mul_of_rightChar K _ _ φ _ _ (fun g => hφn k' g) 1, hchar]

  obtain ⟨hdiff, hdiff', hode⟩ :=
    gl2Real_whittaker_ode_of_casimir_of_unipotent_covariant_of_weight
      F ε hε n lam ν hν DF DHH DEF hD hDHH hDEF hΩ hN hK

  have heq : ∀ y : ℝ, 0 < y → f y = F (splitTorusGL2 (Real.log y / 2)) := by
    intro y hy
    have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
    have hA : Matrix.of (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) =
        !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := Equiv.apply_symm_apply _ _
    have hdet : (Matrix.of (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])).det ≠ 0 := by
      rw [hA, Matrix.det_fin_two_of]; simp [hsq, hε0]
    have hM : Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet = P * splitTorusGL2 (Real.log y / 2) := by
      apply Units.ext
      show Matrix.of (Matrix.of.symm !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) =
        (!![ε, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (splitTorusGL2 (Real.log y / 2) : Matrix (Fin 2) (Fin 2) ℝ)
      rw [hA]
      have hexp : Real.exp (Real.log y / 2) = Real.sqrt y := by
        rw [show Real.log y / 2 = Real.log (Real.sqrt y) by rw [Real.log_sqrt hy.le], Real.exp_log (Real.sqrt_pos.2 hy)]
      have hexp' : Real.exp (-(Real.log y / 2)) = (Real.sqrt y)⁻¹ := by rw [Real.exp_neg, hexp]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, splitTorusGL2, hexp, hexp']
    show W φ (g₀ * archRealLiftAt hw _) = W φ (g₁ * archRealGLAt hw _)
    rw [archRealLiftAt_of_det_ne_zero hw hdet, hM, hFg]
  have heqOn : Set.EqOn f (fun y => F (splitTorusGL2 (Real.log y / 2))) (Set.Ioi 0) := fun y hy => heq y hy
  have hev : ∀ y : ℝ, 0 < y → f =ᶠ[nhds y] fun y => F (splitTorusGL2 (Real.log y / 2)) := by
    intro y hy
    filter_upwards [Ioi_mem_nhds hy] with s hs using heq s hs
  have hder : ∀ y : ℝ, 0 < y → deriv f y = deriv (fun y => F (splitTorusGL2 (Real.log y / 2))) y :=
    fun y hy => (hev y hy).deriv_eq
  have hevd : ∀ y : ℝ, 0 < y → deriv f =ᶠ[nhds y] deriv (fun y => F (splitTorusGL2 (Real.log y / 2))) := by
    intro y hy
    filter_upwards [Ioi_mem_nhds hy] with s hs using hder s hs
  refine ⟨hdiff.congr heqOn, hdiff'.congr (fun y hy => hder y hy), ?_⟩
  intro y hy
  rw [(hevd y hy).deriv_eq, heq y hy]
  exact hode y hy

/-! ## The determinant-one torus: a lowering iterate that kills the coefficient

The pin's whole development here is `private` (`statement_db.parse_file` reads 41 private
declarations and one public row). It is transcribed at the pin's names, in one namespace
(`DiagOneZero`). Three helpers are *not* copied: `glArch_ext` and
`archRealGLAt_mul_comm_of_archComponent_eq_one` are `ElemLR`'s (imported), and the pin's private
`W` is the same abbreviation as the imported `DCFN.W`; `continuous_unipotentGL2` is the pin's own
generic form and is kept. `splitTorus_mul_unipotent` is the *real*-place row — `ArchWhittaker`'s
is the complex one — and is the pin's own. -/

namespace DiagOneZero

private theorem splitTorus_mul_unipotent (s x : ℝ) :
    splitTorusGL2 s * unipotentGL2 x = unipotentGL2 (Real.exp (2 * s) * x) * splitTorusGL2 s := by
  ext i j
  simp only [Units.val_mul, unipotentGL2_coe, splitTorusGL2_coe]
  have h2 : Real.exp (2 * s) * x * Real.exp (-s) = Real.exp s * x := by
    rw [show (2 : ℝ) * s = s + s by ring, Real.exp_add, Real.exp_neg]; field_simp
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

private theorem continuous_unipotentGL2 {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (fun x : A => (unipotentGL2 x : GL (Fin 2) A)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · have : (Units.val ∘ fun x : A => (unipotentGL2 x : GL (Fin 2) A)) = fun x => !![(1 : A), x; 0, 1] :=
      funext fun x => unipotentGL2_coe x
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : (fun x : A => (((unipotentGL2 x : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)) =
        fun x => !![(1 : A), -x; 0, 1] := funext fun x => rfl
    rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

end DiagOneZero

namespace DiagOneZero

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicHaar

variable {F : Type} [Field F] [NumberField F]

private abbrev pins (D : Set (AdelicGL2 (𝓞 F) F)) :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

private abbrev W (D : Set (AdelicGL2 (𝓞 F) F)) (x : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  whittakerCoefficient F (pins D) (NumberField.StandardAddChar.stdAddChar F) x 1 g

private theorem W_smul (D : Set (AdelicGL2 (𝓞 F) F)) (c : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    W D (c • x) g = c * W D x g := by
  let := (pins (F := F) D).nS
  show (∫ u, (c • x) (unipotentGL2 u * g) * _ ∂(pins D).ν) = c * ∫ u, x (unipotentGL2 u * g) * _ ∂(pins D).ν
  rw [← integral_const_mul]
  congr 1; funext u; simp only [Pi.smul_apply, smul_eq_mul]; ring

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem psi_continuous : Continuous (NumberField.StandardAddChar.stdAddChar F : AdeleRing (𝓞 F) F → ℂ) :=
  (NumberField.StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK.continuous

private theorem integrable_integrand (D : Set (AdelicGL2 (𝓞 F) F)) {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Continuous x) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (fun u : AdeleRing (𝓞 F) F => x (unipotentGL2 u * g) *
      NumberField.StandardAddChar.stdAddChar F (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u))) (pins D).ν := by
  have hc : Continuous fun u : AdeleRing (𝓞 F) F => x (unipotentGL2 u * g) *
      NumberField.StandardAddChar.stdAddChar F (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u)) :=
    (hx.comp ((continuous_unipotentGL2 (A := AdeleRing (𝓞 F) F)).mul continuous_const)).mul (psi_continuous.comp (continuous_const.mul continuous_id).neg)
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  have : IsProbabilityMeasure (pins (F := F) D).ν := isProbabilityMeasure_cond_adelicBox F
  refine Integrable.of_bound hc.aestronglyMeasurable M ?_
  have : ∀ᵐ u ∂((adelicAddHaar (𝓞 F) F).restrict (adelicBox F)), ‖x (unipotentGL2 u * g) *
      NumberField.StandardAddChar.stdAddChar F (-(algebraMap F (AdeleRing (𝓞 F) F) 1 * u))‖ ≤ M :=
    (ae_restrict_iff' (measurableSet_adelicBox F)).mpr (Filter.Eventually.of_forall fun u hu => hM u (hBC hu))
  show ∀ᵐ u ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)), _
  exact Measure.ae_smul_measure this _

private theorem W_sub (D : Set (AdelicGL2 (𝓞 F) F)) {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous x₁) (h₂ : Continuous x₂) (g : AdelicGL2 (𝓞 F) F) :
    W D (x₁ - x₂) g = W D x₁ g - W D x₂ g := by
  let := (pins (F := F) D).nS
  show (∫ u, (x₁ - x₂) (unipotentGL2 u * g) * _ ∂(pins D).ν) = (∫ u, x₁ (unipotentGL2 u * g) * _ ∂(pins D).ν) - ∫ u, x₂ (unipotentGL2 u * g) * _ ∂(pins D).ν
  rw [← integral_sub (integrable_integrand D h₁ g) (integrable_integrand D h₂ g)]
  congr 1; funext u; simp only [Pi.sub_apply]; ring

private theorem W_add (D : Set (AdelicGL2 (𝓞 F) F)) {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous x₁) (h₂ : Continuous x₂) (g : AdelicGL2 (𝓞 F) F) :
    W D (x₁ + x₂) g = W D x₁ g + W D x₂ g := by
  let := (pins (F := F) D).nS
  show (∫ u, (x₁ + x₂) (unipotentGL2 u * g) * _ ∂(pins D).ν) = (∫ u, x₁ (unipotentGL2 u * g) * _ ∂(pins D).ν) + ∫ u, x₂ (unipotentGL2 u * g) * _ ∂(pins D).ν
  rw [← integral_add (integrable_integrand D h₁ g) (integrable_integrand D h₂ g)]
  congr 1; funext u; simp only [Pi.add_apply]; ring

end DiagOneZero

namespace DiagOneZero

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicHaar

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

private structure Reg (x : AdelicGL2 (𝓞 F) F → ℂ) : Prop where
  cont : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) x)
  smooth : IsArchSmoothAt hw x
  per : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F), x (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = x g

private theorem smooth_foldr {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : IsArchSmoothAt hw x) (l : List ArchDir) :
    IsArchSmoothAt hw (l.foldr (archDerivAt hw) x) := by
  induction l with
  | nil => exact hx
  | cons d l ih => exact ih.archDerivAt d

private theorem foldr_smul (c : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) (l : List ArchDir) :
    l.foldr (archDerivAt hw) (c • x) = c • l.foldr (archDerivAt hw) x := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [List.foldr_cons, List.foldr_cons, ih, archDerivAt_smul]

private theorem foldr_add {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : IsArchSmoothAt hw x₁) (h₂ : IsArchSmoothAt hw x₂) (l : List ArchDir) :
    l.foldr (archDerivAt hw) (x₁ + x₂) = l.foldr (archDerivAt hw) x₁ + l.foldr (archDerivAt hw) x₂ := by
  induction l with
  | nil => rfl
  | cons d l ih => rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, archDerivAt_add (smooth_foldr hw h₁ l) (smooth_foldr hw h₂ l)]

private theorem reg_deriv {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (d : ArchDir) : Reg hw (archDerivAt hw d x) where
  cont l := by
    have h := hx.cont (l ++ [d])
    rwa [List.foldr_append] at h
  smooth := hx.smooth.archDerivAt d
  per β g := by
    show _root_.deriv (fun t : ℝ => x (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g * archFlowAt hw d t)) 0 =
      _root_.deriv (fun t : ℝ => x (g * archFlowAt hw d t)) 0
    congr 1; funext t; rw [mul_assoc, hx.per]

private theorem reg_smul {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (c : ℂ) : Reg hw (c • x) where
  cont l := by rw [foldr_smul]; exact (hx.cont l).const_smul c
  smooth := hx.smooth.smul c
  per β g := by simp only [Pi.smul_apply, hx.per]

private theorem reg_add {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Reg hw x₁) (h₂ : Reg hw x₂) : Reg hw (x₁ + x₂) where
  cont l := by rw [foldr_add hw h₁.smooth h₂.smooth]; exact (h₁.cont l).add (h₂.cont l)
  smooth := h₁.smooth.add h₂.smooth
  per β g := by simp only [Pi.add_apply, h₁.per, h₂.per]

private theorem reg_sub {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Reg hw x₁) (h₂ : Reg hw x₂) : Reg hw (x₁ - x₂) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ x₂]; exact reg_add hw h₁ (reg_smul hw h₂ (-1))

private theorem reg_continuous {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) : Continuous x := hx.cont []

private theorem reg_hD1 {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (d : ArchDir) : Continuous (archDerivAt hw d x) := hx.cont [d]

private theorem reg_hD2 {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (d d' : ArchDir) :
    Continuous (archDerivAt hw d (archDerivAt hw d' x)) := hx.cont [d, d']

private def op (σ : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  archDerivAt hw .H x + σ • (archDerivAt hw .E x + archDerivAt hw .Fm x)

private theorem reg_op {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (σ : ℂ) : Reg hw (op hw σ x) :=
  reg_add hw (reg_deriv hw hx .H) (reg_smul hw (reg_add hw (reg_deriv hw hx .E) (reg_deriv hw hx .Fm)) σ)

private theorem reg_op_iter {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (σ : ℂ) (j : ℕ) : Reg hw ((op hw σ)^[j] x) := by
  induction j with
  | zero => exact hx
  | succ j ih => rw [Function.iterate_succ_apply']; exact reg_op hw ih σ

private theorem op_apply (σ : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    op hw σ x g = archDerivAt hw .H x g + σ * (archDerivAt hw .E x g + archDerivAt hw .Fm x g) := by
  simp only [op, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

section Torus

variable (D : Set (AdelicGL2 (𝓞 F) F)) (g₀ : AdelicGL2 (𝓞 F) F) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)

private theorem hε0' (hε : ε = 1 ∨ ε = -1) : -ε ≠ 0 := by rcases hε with h | h <;> simp [h]

private def P : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero !![-ε, 0; 0, 1] (by simp [Matrix.det_fin_two_of, hε0' ε hε])

private def g₁ : AdelicGL2 (𝓞 F) F := g₀ * archRealGLAt hw (P ε hε)

private def Fx (x : AdelicGL2 (𝓞 F) F → ℂ) (h : GL (Fin 2) ℝ) : ℂ := W D x (g₁ hw g₀ ε hε * archRealGLAt hw h)

private def φ (x : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) : ℂ := Fx hw D g₀ ε hε x (splitTorusGL2 (Real.log t / 2))

private theorem hasDerivAt_Fx_flow {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (d : ArchDir) (h : GL (Fin 2) ℝ) :
    HasDerivAt (fun s : ℝ => Fx hw D g₀ ε hε x (h * archFlowMatrix d s)) (Fx hw D g₀ ε hε (archDerivAt hw d x) h) 0 :=
  (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlow_of_continuous_archDerivAt F D w hw x (reg_continuous hw hx) hx.smooth
    (reg_hD1 hw hx) (reg_hD2 hw hx) (g₁ hw g₀ ε hε)).1 d h

private theorem Fx_unipotent (hg₀ : archComponent F w (glArch (𝓞 F) F g₀) = 1) {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (u : ℝ) (h : GL (Fin 2) ℝ) :
    Fx hw D g₀ ε hε x (unipotentGL2 u * h) = Complex.exp (2 * Real.pi * Complex.I * ((-ε) * u)) * Fx hw D g₀ ε hε x h := by
  classical
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw with he_def
  have hper' : ∀ (G : AdelicGL2 (𝓞 F) F) (β : F) (uA : (AdeleRing (𝓞 F) F)),
      x (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + uA) * G) = x (unipotentGL2 uA * G) := by
    intro G β uA; rw [unipotentGL2_add, mul_assoc, hx.per]
  dsimp only [Fx, W]
  have h1 : g₁ hw g₀ ε hε * archRealGLAt hw (unipotentGL2 u * h) =
      archRealGLAt hw (unipotentGL2 ((-ε) * u)) * (g₁ hw g₀ ε hε * archRealGLAt hw h) := by
    have hc := ElemLR.archRealGLAt_mul_comm_of_archComponent_eq_one hw (unipotentGL2 ((-ε) * u)) hg₀
    calc g₁ hw g₀ ε hε * archRealGLAt hw (unipotentGL2 u * h)
        = g₀ * (archRealGLAt hw (P ε hε * unipotentGL2 u)) * archRealGLAt hw h := by
          simp only [g₁, map_mul, mul_assoc]
      _ = g₀ * (archRealGLAt hw (unipotentGL2 ((-ε) * u) * P ε hε)) * archRealGLAt hw h := by
          rw [P, diagSign_mul_unipotent (-ε) (hε0' ε hε) u]
      _ = (g₀ * archRealGLAt hw (unipotentGL2 ((-ε) * u))) * archRealGLAt hw (P ε hε) * archRealGLAt hw h := by
          simp only [map_mul, mul_assoc]
      _ = (archRealGLAt hw (unipotentGL2 ((-ε) * u)) * g₀) * archRealGLAt hw (P ε hε) * archRealGLAt hw h := by rw [hc]
      _ = archRealGLAt hw (unipotentGL2 ((-ε) * u)) * (g₁ hw g₀ ε hε * archRealGLAt hw h) := by
          simp only [g₁, mul_assoc]
  obtain ⟨hE, -⟩ := NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
    F w hw 1 (by rfl) ((-ε) * u)
  rw [map_one, one_mul, mul_one] at hE
  dsimp only at hE
  have ha : (((1 : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).1 w = (1 : w.Completion) := by
    rw [Units.val_one]; rfl
  have hU : archRealGLAt hw (unipotentGL2 ((-ε) * u)) =
      unipotentGL2 (show (AdeleRing (𝓞 F) F) from
        ((Pi.single w (e.symm ((-ε) * u)), 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) := by
    rw [hE, ha, one_mul]
  rw [h1, hU]
  have hcov := whittakerCoefficient_unipotentGL2_mul F D
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
    (NumberField.StandardAddChar.stdAddChar F)
    (NumberField.StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK.principalInvariant x
    (g₁ hw g₀ ε hε * archRealGLAt hw h) (hper' _) 1
    (show (AdeleRing (𝓞 F) F) from
      ((Pi.single w (e.symm ((-ε) * u)), 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  rw [hcov, map_one, one_mul]
  congr 1
  have hψ := NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal F w hw ((-ε) * u)
  rw [← he_def] at hψ
  rw [hψ]; push_cast; ring_nf

private theorem hasDerivAt_φ {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (φ hw D g₀ ε hε x) (((t⁻¹ / 2 : ℝ) : ℂ) * φ hw D g₀ ε hε (archDerivAt hw .H x) t) t := by

  set s₀ := Real.log t / 2 with hs₀
  have h1 : HasDerivAt (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 (s₀ + s)))
      (Fx hw D g₀ ε hε (archDerivAt hw .H x) (splitTorusGL2 s₀)) 0 := by
    have h := hasDerivAt_Fx_flow hw D g₀ ε hε hx .H (splitTorusGL2 s₀)
    have hfun : (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 s₀ * archFlowMatrix .H s)) =
        fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 (s₀ + s)) := by
      funext s; rw [show archFlowMatrix .H s = splitTorusGL2 s from rfl, ← splitTorusGL2_add]
    rwa [hfun] at h
  have h2 : HasDerivAt (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 s))
      (Fx hw D g₀ ε hε (archDerivAt hw .H x) (splitTorusGL2 s₀)) s₀ := by
    have h1' : HasDerivAt (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 (s₀ + s)))
        (Fx hw D g₀ ε hε (archDerivAt hw .H x) (splitTorusGL2 s₀)) (-s₀ + s₀) := by rwa [neg_add_cancel]
    have h := h1'.comp_const_add (-s₀) s₀
    simp only [add_neg_cancel_left] at h
    exact h
  have h3 : HasDerivAt (fun t : ℝ => Real.log t / 2) (t⁻¹ / 2) t := (Real.hasDerivAt_log ht.ne').div_const 2
  have h4 := h2.scomp t h3
  simp [Function.comp_def, φ, hs₀] at h4 ⊢
  exact h4

private theorem φ_E (hg₀ : archComponent F w (glArch (𝓞 F) F g₀) = 1) {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) {t : ℝ} (ht : 0 < t) :
    φ hw D g₀ ε hε (archDerivAt hw .E x) t = (2 * Real.pi * Complex.I * ((-ε) * t)) * φ hw D g₀ ε hε x t := by
  set s₀ := Real.log t / 2 with hs₀
  have hexp : Real.exp (2 * s₀) = t := by rw [hs₀, mul_div_cancel₀ _ (two_ne_zero), Real.exp_log ht]
  have h := hasDerivAt_Fx_flow hw D g₀ ε hε hx .E (splitTorusGL2 s₀)
  set c : ℂ := 2 * Real.pi * Complex.I * ((-ε) * t) with hc
  set Kx : ℂ := Fx hw D g₀ ε hε x (splitTorusGL2 s₀) with hKx
  have hfun : (fun s : ℝ => Fx hw D g₀ ε hε x (splitTorusGL2 s₀ * archFlowMatrix .E s)) =
      fun s : ℝ => Complex.exp (c * (s : ℂ)) * Kx := by
    funext s
    rw [show archFlowMatrix .E s = unipotentGL2 s from rfl, splitTorus_mul_unipotent, Fx_unipotent hw D g₀ ε hε hg₀ hx, hexp]
    congr 2; push_cast; ring
  rw [hfun] at h
  have h5 : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c
  have h' : HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ)) * Kx) (c * Kx) 0 := by
    have h6 := (h5.cexp).mul_const Kx
    simpa using h6
  have := h.unique h'
  show Fx hw D g₀ ε hε (archDerivAt hw .E x) (splitTorusGL2 s₀) = c * Kx
  exact this

private theorem point_eq {t : ℝ} (ht : 0 < t) :
    g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]) =
      g₁ hw g₀ ε hε * archRealGLAt hw (splitTorusGL2 (Real.log t / 2)) := by
  have hsq : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have hA : Matrix.of (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]) =
      !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] := Equiv.apply_symm_apply _ _
  have hdet : (Matrix.of (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])).det ≠ 0 := by
    rw [hA, Matrix.det_fin_two_of]; simp [hsq, hε0' ε hε]
  have hM : Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet = P ε hε * splitTorusGL2 (Real.log t / 2) := by
    apply Units.ext
    show Matrix.of (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]) =
      (!![-ε, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) * (splitTorusGL2 (Real.log t / 2) : Matrix (Fin 2) (Fin 2) ℝ)
    rw [hA]
    have hexp : Real.exp (Real.log t / 2) = Real.sqrt t := by
      rw [show Real.log t / 2 = Real.log (Real.sqrt t) by rw [Real.log_sqrt ht.le], Real.exp_log (Real.sqrt_pos.2 ht)]
    have hexp' : Real.exp (-(Real.log t / 2)) = (Real.sqrt t)⁻¹ := by rw [Real.exp_neg, hexp]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, splitTorusGL2, hexp, hexp']
  rw [archRealLiftAt_of_det_ne_zero hw hdet, hM, g₁, map_mul, mul_assoc]

end Torus

end DiagOneZero

namespace DiagOneZero

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.AdelicHaar

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

section Lin

variable (D : Set (AdelicGL2 (𝓞 F) F)) (g₀ : AdelicGL2 (𝓞 F) F) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)

private theorem φ_smul (c : ℂ) (x : AdelicGL2 (𝓞 F) F → ℂ) (t : ℝ) : φ hw D g₀ ε hε (c • x) t = c * φ hw D g₀ ε hε x t :=
  W_smul D c x _

private theorem φ_add {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous x₁) (h₂ : Continuous x₂) (t : ℝ) :
    φ hw D g₀ ε hε (x₁ + x₂) t = φ hw D g₀ ε hε x₁ t + φ hw D g₀ ε hε x₂ t :=
  W_add D h₁ h₂ _

private theorem φ_sub {x₁ x₂ : AdelicGL2 (𝓞 F) F → ℂ} (h₁ : Continuous x₁) (h₂ : Continuous x₂) (t : ℝ) :
    φ hw D g₀ ε hε (x₁ - x₂) t = φ hw D g₀ ε hε x₁ t - φ hw D g₀ ε hε x₂ t :=
  W_sub D h₁ h₂ _

private theorem φ_op {x : AdelicGL2 (𝓞 F) F → ℂ} (hx : Reg hw x) (σ μ : ℂ)
    (hμ : archDerivAt hw .E x - archDerivAt hw .Fm x = μ • x) (t : ℝ) :
    φ hw D g₀ ε hε (op hw σ x) t = φ hw D g₀ ε hε (archDerivAt hw .H x) t +
      σ * (2 * φ hw D g₀ ε hε (archDerivAt hw .E x) t - μ * φ hw D g₀ ε hε x t) := by
  have hF : archDerivAt hw .Fm x = archDerivAt hw .E x - μ • x := by
    rw [← hμ]; abel
  have hEF : archDerivAt hw .E x + archDerivAt hw .Fm x = (2 : ℂ) • archDerivAt hw .E x - μ • x := by
    rw [hF, two_smul]; abel
  unfold op
  have c1 : Continuous ((2 : ℂ) • archDerivAt hw .E x - μ • x) := ((reg_hD1 hw hx .E).const_smul (2 : ℂ)).sub ((reg_continuous hw hx).const_smul μ)
  have c2 : Continuous (σ • ((2 : ℂ) • archDerivAt hw .E x - μ • x)) := c1.const_smul σ
  rw [hEF, φ_add hw D g₀ ε hε (x₁ := archDerivAt hw .H x) (x₂ := σ • ((2 : ℂ) • archDerivAt hw .E x - μ • x)) (reg_hD1 hw hx .H) c2,
    φ_smul, φ_sub hw D g₀ ε hε (x₁ := (2 : ℂ) • archDerivAt hw .E x) (x₂ := μ • x) ((reg_hD1 hw hx .E).const_smul (2 : ℂ))
      ((reg_continuous hw hx).const_smul μ), φ_smul, φ_smul]

end Lin

private theorem main (D : Set (AdelicGL2 (𝓞 F) F))
    (y : AdelicGL2 (𝓞 F) F → ℂ) (_hyc : Continuous y)
    (hper : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F), y (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = y g)
    (hys : IsArchSmoothAt hw y)
    (hD : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) y))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (k₀ M : ℕ) (hk₀ : 1 ≤ k₀) (n : ℤ) (hn : (n : ℝ) = ε * (k₀ + 2 * M))
    (hm : archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y)
    (hΩ : archCasimirAt hw y = (((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2)) • y)
    (hlow : (fun x : AdelicGL2 (𝓞 F) F → ℂ =>
        archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M + 1] y = 0)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : archComponent F w (glArch (𝓞 F) F g₀) = 1)
    (C : ℝ) (Ngr : ℕ)
    (hgrowth : ∀ t : ℝ, 1 ≤ t →
      ‖W D (((fun x : AdelicGL2 (𝓞 F) F → ℂ =>
            archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M] y))
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]))‖ ≤ C * t ^ Ngr)
    (t : ℝ) (ht : 0 < t) :
    W D y (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])) = 0 := by

  set σR : ℂ := (ε : ℂ) * Complex.I with hσR
  set σL : ℂ := -σR with hσL
  have hL : (fun x : AdelicGL2 (𝓞 F) F → ℂ =>
      archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x)) = op hw σL := by
    funext x; simp only [op, hσL, hσR, neg_smul, sub_eq_add_neg]
  rw [hL] at hlow hgrowth
  have hε2 : (ε : ℂ) ^ 2 = 1 := by rcases hε with h | h <;> simp [h]
  have regy : Reg hw y := ⟨hD, hys, hper⟩

  set y₀ := (op hw σL)^[M] y with hy₀
  have regy₀ : Reg hw y₀ := reg_op_iter hw regy σL M
  have hLy₀ : op hw σL y₀ = 0 := by rw [hy₀, ← Function.iterate_succ_apply' (op hw σL) M y]; exact hlow

  set lam : ℂ := ((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2) with hlam
  have halg : (∀ j : ℕ, archDerivAt hw .E ((op hw σR)^[j] y₀) - archDerivAt hw .Fm ((op hw σR)^[j] y₀) =
        (Complex.I * ε * ((k₀ : ℂ) + 2 * j)) • (op hw σR)^[j] y₀) ∧
      ∃ Pc : ℂ, Pc ≠ 0 ∧ (op hw σR)^[M] y₀ = Pc • y := by
    have HA := AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul F w hw y hys (Complex.I * n) lam hm hΩ
    obtain ⟨hlo, hra, hRL, hLR⟩ := HA

    have hfac : ∀ j : ℕ, j < M → ∀ q : ℂ, q = (k₀ : ℂ) + 2 * ((M - j : ℕ) : ℂ) → -4 * lam - q ^ 2 + 2 * q ≠ 0 := by
      intro j hj q hq
      have h1 : -4 * lam - q ^ 2 + 2 * q = ((k₀ : ℂ) - q) * ((k₀ : ℂ) + q - 2) := by rw [hlam]; ring
      rw [h1, hq]
      have hMj : 1 ≤ M - j := by omega
      refine mul_ne_zero ?_ ?_
      · have : ((k₀ : ℂ) - ((k₀ : ℂ) + 2 * ((M - j : ℕ) : ℂ))) = -(2 * ((M - j : ℕ) : ℂ)) := by ring
        rw [this, neg_ne_zero]
        exact_mod_cast (show (2 * (M - j) : ℕ) ≠ 0 by omega)
      · have : ((k₀ : ℂ) + ((k₀ : ℂ) + 2 * ((M - j : ℕ) : ℂ)) - 2) = (((2 * k₀ + 2 * (M - j) - 2 : ℕ)) : ℂ) := by
          have h2 : 2 ≤ 2 * k₀ + 2 * (M - j) := by omega
          push_cast [Nat.cast_sub h2]
          ring
        rw [this]
        exact_mod_cast (show (2 * k₀ + 2 * (M - j) - 2 : ℕ) ≠ 0 by omega)
    rcases hε with rfl | rfl
    ·
      have hn1 : (n : ℝ) = ((k₀ + 2 * M : ℕ) : ℝ) := by rw [hn]; push_cast; ring
      have hn2 : n = ((k₀ + 2 * M : ℕ) : ℤ) := by exact_mod_cast hn1
      have hnZ : (n : ℂ) = (k₀ : ℂ) + 2 * M := by rw [hn2]; push_cast; ring
      have eL : op hw σL = fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x) := by
        funext x; simp only [op, hσL, hσR, Complex.ofReal_one, one_mul, neg_smul, sub_eq_add_neg]
      have eR : op hw σR = fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x) := by
        funext x; simp only [op, hσR, Complex.ofReal_one, one_mul]

      obtain ⟨hy₀s, hy₀w, hy₀Ω⟩ := hlo M
      rw [← eL] at hy₀s hy₀w hy₀Ω
      have HB := AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul F w hw y₀ hy₀s _ lam hy₀w hy₀Ω
      obtain ⟨-, hra₀, -, -⟩ := HB
      refine ⟨fun j => ?_, ⟨∏ j ∈ Finset.range M, (-4 * lam + (Complex.I * n - 2 * Complex.I * j) ^ 2 -
        2 * Complex.I * (Complex.I * n - 2 * Complex.I * j)), ?_, ?_⟩⟩
      · obtain ⟨-, hwj, -⟩ := hra₀ j
        rw [← eR] at hwj
        rw [hwj]; congr 1; rw [hnZ]; push_cast; ring
      · rw [Finset.prod_ne_zero_iff]
        intro j hj
        rw [Finset.mem_range] at hj
        have := hfac j hj ((n : ℂ) - 2 * j) (by rw [hnZ]; push_cast [Nat.cast_sub hj.le]; ring)
        convert this using 1
        ring_nf; simp only [Complex.I_sq]; ring
      · rw [← eR, ← eL] at hRL; exact hRL M
    ·
      have hn1 : (n : ℝ) = -((k₀ + 2 * M : ℕ) : ℝ) := by rw [hn]; push_cast; ring
      have hn2 : n = -((k₀ + 2 * M : ℕ) : ℤ) := by exact_mod_cast hn1
      have hnZ : (n : ℂ) = -((k₀ : ℂ) + 2 * M) := by rw [hn2]; push_cast; ring
      have eL : op hw σL = fun x => archDerivAt hw .H x + Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x) := by
        funext x; simp only [op, hσL, hσR]; push_cast; simp only [neg_mul, one_mul, neg_neg]
      have eR : op hw σR = fun x => archDerivAt hw .H x - Complex.I • (archDerivAt hw .E x + archDerivAt hw .Fm x) := by
        funext x; simp only [op, hσR]; push_cast; simp only [neg_mul, one_mul, neg_smul, sub_eq_add_neg]
      obtain ⟨hy₀s, hy₀w, hy₀Ω⟩ := hra M
      rw [← eL] at hy₀s hy₀w hy₀Ω
      have HB := AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul F w hw y₀ hy₀s _ lam hy₀w hy₀Ω
      obtain ⟨hlo₀, -, -, -⟩ := HB
      refine ⟨fun j => ?_, ⟨∏ j ∈ Finset.range M, (-4 * lam + (Complex.I * n + 2 * Complex.I * j) ^ 2 +
        2 * Complex.I * (Complex.I * n + 2 * Complex.I * j)), ?_, ?_⟩⟩
      · obtain ⟨-, hwj, -⟩ := hlo₀ j
        rw [← eR] at hwj
        rw [hwj]; congr 1; rw [hnZ]; push_cast; ring
      · rw [Finset.prod_ne_zero_iff]
        intro j hj
        rw [Finset.mem_range] at hj
        have := hfac j hj (-((n : ℂ) + 2 * j)) (by rw [hnZ]; push_cast [Nat.cast_sub hj.le]; ring)
        convert this using 1
        ring_nf; simp only [Complex.I_sq]; ring
      · rw [← eR, ← eL] at hLR; exact hLR M
  obtain ⟨hwt, Pc, hPc, hRM⟩ := halg
  have hε' : ε = 1 ∨ ε = -1 := hε

  have hφE := fun (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : Reg hw x) {s : ℝ} (hs : 0 < s) => φ_E hw D g₀ ε hε' hg₀ hx hs

  have hμ₀ := hwt 0
  simp only [Function.iterate_zero, id_eq, Nat.cast_zero, mul_zero, add_zero] at hμ₀
  have hHy₀ : archDerivAt hw .H y₀ = (-σL) • (archDerivAt hw .E y₀ + archDerivAt hw .Fm y₀) := by
    have h := hLy₀
    unfold op at h
    rw [neg_smul, eq_neg_iff_add_eq_zero, h]
  have hderiv₀ : ∀ s : ℝ, 0 < s → HasDerivAt (φ hw D g₀ ε hε' y₀)
      ((((k₀ : ℂ) / 2) / (s : ℂ) + 2 * Real.pi) * φ hw D g₀ ε hε' y₀ s) s := by
    intro s hs
    have h1 := hasDerivAt_φ hw D g₀ ε hε' regy₀ hs
    have hF : archDerivAt hw .Fm y₀ = archDerivAt hw .E y₀ - (Complex.I * ε * k₀) • y₀ := by rw [← hμ₀]; abel
    have h2 : φ hw D g₀ ε hε' (archDerivAt hw .H y₀) s = (-σL) * (2 * φ hw D g₀ ε hε' (archDerivAt hw .E y₀) s
        - (Complex.I * ε * k₀) * φ hw D g₀ ε hε' y₀ s) := by
      rw [hHy₀, φ_smul, hF, show archDerivAt hw .E y₀ + (archDerivAt hw .E y₀ - (Complex.I * ε * k₀) • y₀) =
        (2 : ℂ) • archDerivAt hw .E y₀ - (Complex.I * ε * k₀) • y₀ by rw [two_smul]; abel,
        φ_sub hw D g₀ ε hε' (x₁ := (2 : ℂ) • archDerivAt hw .E y₀) (x₂ := (Complex.I * ε * k₀) • y₀)
          ((reg_hD1 hw regy₀ .E).const_smul (2 : ℂ)) ((reg_continuous hw regy₀).const_smul (Complex.I * ε * k₀)), φ_smul, φ_smul]
    rw [h2, hφE y₀ regy₀ hs] at h1
    convert h1 using 1
    rw [hσL, hσR]
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq, hε2]
    ring
  have hzero₀ : ∀ s : ℝ, 0 < s → φ hw D g₀ ε hε' y₀ s = 0 := by
    refine LanglandsTunnell.eq_zero_of_deriv_eq_div_add_mul_of_re_pos_of_isBigO_pow ((k₀ : ℂ) / 2) (2 * Real.pi) (by simp [Real.pi_pos])
      (φ hw D g₀ ε hε' y₀) (fun s hs => (hderiv₀ s hs).differentiableAt.differentiableWithinAt) (fun s hs => (hderiv₀ s hs).deriv)
      C Ngr (fun s hs => ?_)
    have h := hgrowth s hs
    rwa [point_eq hw g₀ ε hε' (lt_of_lt_of_le one_pos hs)] at h

  have hzero : ∀ j : ℕ, ∀ s : ℝ, 0 < s → φ hw D g₀ ε hε' ((op hw σR)^[j] y₀) s = 0 := by
    intro j
    induction j with
    | zero => exact hzero₀
    | succ j ih =>
      intro s hs
      have regj : Reg hw ((op hw σR)^[j] y₀) := reg_op_iter hw regy₀ σR j
      rw [Function.iterate_succ_apply', φ_op hw D g₀ ε hε' regj σR _ (hwt j), hφE _ regj hs, ih s hs]

      have h1 := hasDerivAt_φ hw D g₀ ε hε' regj hs
      have h0 : HasDerivAt (φ hw D g₀ ε hε' ((op hw σR)^[j] y₀)) 0 s := by
        refine (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq ?_
        filter_upwards [Ioi_mem_nhds hs] with u hu using ih u hu
      have huniq := h1.unique h0
      have hs0 : ((s⁻¹ / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      have hH : φ hw D g₀ ε hε' (archDerivAt hw .H ((op hw σR)^[j] y₀)) s = 0 := (mul_eq_zero.mp huniq).resolve_left hs0
      rw [hH]; ring

  have hy : y = Pc⁻¹ • (op hw σR)^[M] y₀ := by rw [hRM, smul_smul, inv_mul_cancel₀ hPc, one_smul]
  have := hzero M t ht
  rw [point_eq hw g₀ ε hε' ht, hy, W_smul]
  show Pc⁻¹ * φ hw D g₀ ε hε' ((op hw σR)^[M] y₀) t = 0
  rw [this, mul_zero]

end DiagOneZero

open DiagOneZero

theorem whittakerCoefficient_detOneTorus_eq_zero_of_iterate_lower_eq_zero
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hyc : Continuous y)
    (hper : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K), y (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = y g)
    (hys : IsArchSmoothAt hw y)
    (hD : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) y))
    (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (k₀ M : ℕ) (hk₀ : 1 ≤ k₀) (n : ℤ) (hn : (n : ℝ) = ε * (k₀ + 2 * M))
    (hm : archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y)
    (hΩ : archCasimirAt hw y = (((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2)) • y)
    (hlow : (fun x : AdelicGL2 (𝓞 K) K → ℂ =>
        archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M + 1] y = 0)
    (g₀ : AdelicGL2 (𝓞 K) K) (hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (C : ℝ) (Ngr : ℕ)
    (hgrowth : ∀ t : ℝ, 1 ≤ t →
      ‖whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (((fun x : AdelicGL2 (𝓞 K) K → ℂ =>
            archDerivAt hw .H x - ((ε : ℂ) * Complex.I) • (archDerivAt hw .E x + archDerivAt hw .Fm x))^[M] y)) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹]))‖ ≤ C * t ^ Ngr)
    (t : ℝ) (ht : 0 < t) :
    whittakerCoefficient K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (y) 1
          (g₀ * archRealLiftAt hw (Matrix.of.symm !![-ε * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹])) = 0
  :=
  DiagOneZero.main hw D y hyc hper hys hD ε hε k₀ M hk₀ n hn hm hΩ hlow g₀ hg₀ C Ngr hgrowth t ht

/-! ## The complex place: the coupled `𝔰𝔩₂` Whittaker system

The pin's `E40DCFN` prelude (`eC`, `iotaW`, `bprime`, `g0`, `W`, `Fstr`/`DFstr`/`DDstr`/`fstr`,
`bprime_fst_self`, `bprime_fst_of_ne`, `bprime_snd`, `glInf_ext`,
`archComplexGLAt_mul_comm_of_archComponent_eq_one`, `archComponent_glArch_g0`,
`archComplexGLAt_mul_g0`, `whittakerCoefficient_mul_right`, `whittakerCoefficient_const_mul`) and
`E40UNI`'s `map_unipotentGL2`/`archComponent_glArch_unipotentGL2`/`glFin_unipotentGL2`/
`glEquivOfRingEquiv_unipotentGL2` are already in the port — `DCFN` of `WhittakerDiagOne.lean` and
`NumberField.AdelicLevel.ArchLevel` of `ArchLevelLattice.lean` — and are imported, not re-proved.
The pin's `casWords`/`casCoeff`/`casBarCoeff` dictionary is *not*: `port_advise`'s
type-only-`def` substitutions for those three (`LeftCasimirComplex.W10`,
`ComplexCasimirComm.sgn`) are the parser's `def` false positives, and `ArchWhittaker`'s
`splitTorus_mul_unipotent` is the complex-place row. What follows is the residue: the Casimir
dictionary at the pin's names, the `E40UNI` residue, and the `E37K` `k`-type transport. -/

namespace DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

theorem hasDerivAt_W_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex)
    (b : (AdeleRing (𝓞 K) K)ˣ) {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p))) :
    (∀ (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
        (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g0 w b * archComplexGLAt hw h)) 0) ∧
    (∀ (p : Fin (n + 1)) (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' (x p)) 1 (g0 w b * archComplexGLAt hw (h * archFlowMatrixComplex d t)))
        (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (archDerivAtComplex hw d' (x p))) 1 (g0 w b * archComplexGLAt hw h)) 0) := by
  have hs : ∀ p, IsArchSmoothAtComplex hw (x p) := fun p => by simpa only [List.foldr] using (hreg p []).1
  have h1 : ∀ p (d : ArchDirComplex), Continuous (archDerivAtComplex hw d (x p)) := fun p d => by
    simpa only [List.foldr] using (hreg p [d]).2
  have h2 : ∀ p (d d' : ArchDirComplex), Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (x p))) := fun p d d' => by
    simpa only [List.foldr] using (hreg p [d, d']).2
  exact ⟨fun p => (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) (g0 w b)).1,
    fun p => (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) (g0 w b)).2⟩

section Casimir

variable {w : InfinitePlace K} (hw : w.IsComplex)

theorem archDelAt_apply' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDelAt hw d ψ g = (1 / 2 : ℂ) * (archDerivAtComplex hw d.toComplex ψ g - Complex.I * archDerivAtComplex hw d.toComplexI ψ g) := by
  simp only [archDelAt, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem archDelBarAt_apply' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (d : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDelBarAt hw d ψ g = (1 / 2 : ℂ) * (archDerivAtComplex hw d.toComplex ψ g + Complex.I * archDerivAtComplex hw d.toComplexI ψ g) := by
  simp only [archDelBarAt, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem archDerivAtComplex_sub'' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDirComplex) :
    archDerivAtComplex hw d (φ - ψ) = archDerivAtComplex hw d φ - archDerivAtComplex hw d ψ := by
  rw [sub_eq_add_neg, archDerivAtComplex_add hφ hψ.neg, ← neg_one_smul ℂ ψ, archDerivAtComplex_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem archDerivAtComplex_archDelAt' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAtComplex hw ψ)
    (d : ArchDirComplex) (d' : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d (archDelAt hw d' ψ) g =
      (1 / 2 : ℂ) * (archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplex ψ) g -
        Complex.I * archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplexI ψ) g) := by
  unfold AutomorphicForm.archDelAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_sub'' hw (hψ.archDerivAtComplex _) ((hψ.archDerivAtComplex _).smul _),
    archDerivAtComplex_smul]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem archDerivAtComplex_archDelBarAt' {ψ : AdelicGL2 (𝓞 K) K → ℂ} (hψ : IsArchSmoothAtComplex hw ψ)
    (d : ArchDirComplex) (d' : ArchDir) (g : AdelicGL2 (𝓞 K) K) :
    archDerivAtComplex hw d (archDelBarAt hw d' ψ) g =
      (1 / 2 : ℂ) * (archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplex ψ) g +
        Complex.I * archDerivAtComplex hw d (archDerivAtComplex hw d'.toComplexI ψ) g) := by
  unfold AutomorphicForm.archDelBarAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_add (hψ.archDerivAtComplex _) ((hψ.archDerivAtComplex _).smul _),
    archDerivAtComplex_smul]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]

def casWords (φ : AdelicGL2 (𝓞 K) K → ℂ) : Fin 10 → (AdelicGL2 (𝓞 K) K → ℂ) :=
  ![archDerivAtComplex hw .H (archDerivAtComplex hw .H φ), archDerivAtComplex hw .H (archDerivAtComplex hw .iH φ),
    archDerivAtComplex hw .iH (archDerivAtComplex hw .H φ), archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ),
    archDerivAtComplex hw .H φ, archDerivAtComplex hw .iH φ,
    archDerivAtComplex hw .E (archDerivAtComplex hw .Fm φ), archDerivAtComplex hw .E (archDerivAtComplex hw .iFm φ),
    archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm φ), archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ)]

def casCoeff : Fin 10 → ℂ :=
  ![-(1 / 16 : ℂ), Complex.I / 16, Complex.I / 16, 1 / 16, 1 / 4, -(Complex.I / 4), -(1 / 4 : ℂ), Complex.I / 4, Complex.I / 4, 1 / 4]

def casBarCoeff : Fin 10 → ℂ :=
  ![-(1 / 16 : ℂ), -(Complex.I / 16), -(Complex.I / 16), 1 / 16, 1 / 4, Complex.I / 4, -(1 / 4 : ℂ), -(Complex.I / 4),
    -(Complex.I / 4), 1 / 4]

theorem archCasimirAtComplex_eq_sum {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirAtComplex hw φ = fun g => ∑ j : Fin 10, casCoeff j * casWords hw φ j g := by
  funext g
  simp only [archCasimirAtComplex, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [archDelAt_apply' hw .H (ψ := archDelAt hw .H φ), archDerivAtComplex_archDelAt' hw hφ, archDerivAtComplex_archDelAt' hw hφ,
    archDelAt_apply' hw .H (ψ := φ), archDelAt_apply' hw .E (ψ := archDelAt hw .Fm φ), archDerivAtComplex_archDelAt' hw hφ,
    archDerivAtComplex_archDelAt' hw hφ]
  simp only [casCoeff, casWords, ArchDir.toComplex, ArchDir.toComplexI, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (-(1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) g -
    (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g) * Complex.I_sq

theorem archCasimirBarAtComplex_eq_sum {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ) :
    archCasimirBarAtComplex hw φ = fun g => ∑ j : Fin 10, casBarCoeff j * casWords hw φ j g := by
  funext g
  simp only [archCasimirBarAtComplex, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [archDelBarAt_apply' hw .H (ψ := archDelBarAt hw .H φ), archDerivAtComplex_archDelBarAt' hw hφ, archDerivAtComplex_archDelBarAt' hw hφ,
    archDelBarAt_apply' hw .H (ψ := φ), archDelBarAt_apply' hw .E (ψ := archDelBarAt hw .Fm φ), archDerivAtComplex_archDelBarAt' hw hφ,
    archDerivAtComplex_archDelBarAt' hw hφ]
  simp only [casBarCoeff, casWords, ArchDir.toComplex, ArchDir.toComplexI, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  linear_combination (-(1 / 16 : ℂ) * archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) g -
    (1 / 4 : ℂ) * archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g) * Complex.I_sq

end Casimir

end DCFN

namespace UnipotentPoint

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem glArch_ext' {x y : GL (Fin 2) (InfiniteAdeleRing K)}
    (h : ∀ w : InfinitePlace K, archComponent K w x = archComponent K w y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => funext fun w => ?_
  exact congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

open scoped Classical in

theorem archComplexGLAt_unipotentGL2 {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂ) :
    archComplexGLAt hw (unipotentGL2 z) =
      unipotentGL2 (show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0)) := by
  refine eq_of_glArch_eq_of_glFin_eq K (glArch_ext' fun w' => ?_) ?_
  · rw [ArchLevel.archComponent_glArch_unipotentGL2]
    have hL : glArch (𝓞 K) K (archComplexGLAt hw (unipotentGL2 z)) =
        archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm (unipotentGL2 z)) :=
      glArch_adelicArchGLIncl K _
    rw [hL, ArchLevel.glEquivOfRingEquiv_unipotentGL2]
    by_cases hww : w' = w
    · subst hww
      rw [archComponent_archGLIncl_self]
      congr 1
      show _ = Pi.single (M := fun v : InfinitePlace K => v.Completion) w' ((ringEquivComplexOfIsComplex hw).symm z) w'
      rw [Pi.single_eq_same]
    · rw [archComponent_archGLIncl_of_ne K hww]
      have h0 : ((show (AdeleRing (𝓞 K) K) from (Pi.single w ((ringEquivComplexOfIsComplex hw).symm z), 0))).1 w' = 0 := by
        show Pi.single (M := fun v : InfinitePlace K => v.Completion) w ((ringEquivComplexOfIsComplex hw).symm z) w' = 0
        exact Pi.single_eq_of_ne hww _
      rw [h0, unipotentGL2_zero]
  · rw [ArchLevel.glFin_unipotentGL2]
    have hF : glFin (𝓞 K) K (archComplexGLAt hw (unipotentGL2 z)) = 1 := glFin_adelicArchGLIncl K _
    rw [hF]
    show (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) = unipotentGL2 0
    rw [unipotentGL2_zero]

theorem unipotentGL2_algebraMap_eq_globalPoints (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  refine Units.ext ?_
  ext i j
  simp only [unipotentGL2_coe, globalPoints, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp

end UnipotentPoint

namespace KType

variable (K : Type) [Field K] [NumberField K]

theorem archComplexGLAt_eq_lift_rot {w : InfinitePlace K} (hw : w.IsComplex) (s : ℝ) (k : GL (Fin 2) ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s]) :
    archComplexGLAt hw k =
      archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] := by
  have hmat : (Matrix.of !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) =
      (k : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hk]
    show (!![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) =
      !![Complex.cos (s : ℂ), -Complex.sin (s : ℂ); Complex.sin (s : ℂ), Complex.cos (s : ℂ)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_cos, Complex.ofReal_sin]
  have hdet : (Matrix.of !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [hmat, ← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [archComplexLiftAt_of_det_ne_zero hw hdet]
  congr 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hmat]

theorem archComplexGLAt_eq_lift_irot {w : InfinitePlace K} (hw : w.IsComplex) (s : ℝ) (k : GL (Fin 2) ℂ)
    (hk : (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s]) :
    archComplexGLAt hw k =
      archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] := by
  have hmat : (Matrix.of !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hk]
    show (!![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos (s : ℂ), Complex.I * Complex.sin (s : ℂ); Complex.I * Complex.sin (s : ℂ), Complex.cos (s : ℂ)]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_cos, Complex.ofReal_sin, mul_comm]
  have hdet : (Matrix.of !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [hmat, ← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.ne_zero _
  rw [archComplexLiftAt_of_det_ne_zero hw hdet]
  congr 1
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hmat]

theorem hK_of_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (g₀ : AdelicGL2 (𝓞 K) K)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (hxc : ∀ p, Continuous (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) =
        ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) =
        ∑ p' : Fin (n + 1), E₂ s p' p * x p' g) :
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) =
          ∑ p' : Fin (n + 1), E₁ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) =
          ∑ p' : Fin (n + 1), E₂ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) := by
  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous
  constructor
  · intro p s h k hk
    rw [map_mul, ← mul_assoc, DCFN.whittakerCoefficient_mul_right, archComplexGLAt_eq_lift_rot K hw s k hk]
    rw [show (fun y => x p (y * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)])) =
        fun y => ∑ p' : Fin (n + 1), E₁ s p' p * x p' y from funext fun y => hK₁ p s y]
    exact AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ (n + 1) x hxc (fun p' => E₁ s p' p) 1 _
  · intro p s h k hk
    rw [map_mul, ← mul_assoc, DCFN.whittakerCoefficient_mul_right, archComplexGLAt_eq_lift_irot K hw s k hk]
    rw [show (fun y => x p (y * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)])) =
        fun y => ∑ p' : Fin (n + 1), E₂ s p' p * x p' y from funext fun y => hK₂ p s y]
    exact AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ (n + 1) x hxc (fun p' => E₂ s p' p) 1 _

theorem final_bound (V C B w₀ δ r : ℝ) (hr : 0 < r) (_hδ : 0 ≤ δ)
    (hsmall : r ≤ 1 → V ≤ C * r ^ w₀ * r ^ δ) (hlarge : V ≤ B * r ^ w₀) :
    V ≤ max C B * r ^ ((2 : ℝ) * w₀ / 2) * (min 1 r) ^ δ := by
  rw [show (2 : ℝ) * w₀ / 2 = w₀ by ring]
  have hrw : 0 ≤ r ^ w₀ := Real.rpow_nonneg hr.le _
  by_cases h1 : r ≤ 1
  · rw [min_eq_right h1]
    have hrδ : 0 ≤ r ^ δ := Real.rpow_nonneg hr.le _
    calc V ≤ C * r ^ w₀ * r ^ δ := hsmall h1
      _ ≤ max C B * r ^ w₀ * r ^ δ := by
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C B) hrw) hrδ
          exact this
  · rw [min_eq_left (le_of_lt (not_le.mp h1)), Real.one_rpow, mul_one]
    calc V ≤ B * r ^ w₀ := hlarge
      _ ≤ max C B * r ^ w₀ := mul_le_mul_of_nonneg_right (le_max_right C B) hrw

end KType

open DCFN UnipotentPoint KType

theorem whittakerCoefficient_su2String_gl2Complex_whittaker_system_hypotheses
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (g₀ : AdelicGL2 (𝓞 K) K) (_hg₀ : archComponent K w (glArch (𝓞 K) K g₀) = 1)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxc : ∀ p, Continuous (x p))
    (hxG : ∀ p (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x p (globalPoints (𝓞 K) K γ * g) = x p g)
    (hreg : ∀ p (l : List ArchDirComplex),
      IsArchSmoothAtComplex hw (l.foldr (archDerivAtComplex hw) (x p)) ∧ Continuous (l.foldr (archDerivAtComplex hw) (x p)))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (E₁ E₂ : ℝ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hK₁ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₁ s p' p * x p' g)
    (hK₂ : ∀ (p : Fin (n + 1)) (s : ℝ) (g : AdelicGL2 (𝓞 K) K),
      x p (g * archComplexLiftAt hw !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]) = ∑ p' : Fin (n + 1), E₂ s p' p * x p' g)
    (lam lam' : ℂ)
    (hcas : ∀ p, archCasimirAtComplex hw (x p) = lam • x p ∧ archCasimirBarAtComplex hw (x p) = lam' • x p) :
    (∀ (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d t))) (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g₀ * archComplexGLAt hw h)) 0) ∧
    (∀ (p : Fin (n + 1)) (d d' : ArchDirComplex) (h : GL (Fin 2) ℂ),
      HasDerivAt (fun t : ℝ => whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d (x p)) 1 (g₀ * archComplexGLAt hw (h * archFlowMatrixComplex d' t))) (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw d' (archDerivAtComplex hw d (x p))) 1 (g₀ * archComplexGLAt hw h)) 0) ∧
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g₀ * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h)) -
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) - Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h))))) = lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (h : GL (Fin 2) ℂ),
      -((1 / 4 : ℂ) * ((1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .H (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 (g₀ * archComplexGLAt hw h))))) -
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .H (x p)) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (x p)) 1 (g₀ * archComplexGLAt hw h))) +
          (1 / 2 : ℂ) * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .E (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h)) +
            Complex.I * ((1 / 2 : ℂ) * (whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .Fm (x p))) 1 (g₀ * archComplexGLAt hw h) + Complex.I * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 (g₀ * archComplexGLAt hw h))))) = lam' * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (z : ℂ) (h : GL (Fin 2) ℂ),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (unipotentGL2 z * h)) = Complex.exp (2 * Real.pi * Complex.I * ((2 * ((1 : ℂ) * z).re : ℝ) : ℂ)) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * circleGL2 ζ)) = (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, -Complex.sin s; Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) = ∑ p' : Fin (n + 1), E₁ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h)) ∧
    (∀ (p : Fin (n + 1)) (s : ℝ) (h k : GL (Fin 2) ℂ),
      (k : Matrix (Fin 2) (Fin 2) ℂ) = !![Complex.cos s, Complex.I * Complex.sin s; Complex.I * Complex.sin s, Complex.cos s] →
        whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g₀ * archComplexGLAt hw (h * k)) = ∑ p' : Fin (n + 1), E₂ s p' p * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p') 1 (g₀ * archComplexGLAt hw h))
  := by
  classical
  have hs : ∀ p, IsArchSmoothAtComplex hw (x p) := fun p => by simpa only [List.foldr] using (hreg p []).1
  have h1 : ∀ p (d : ArchDirComplex), Continuous (archDerivAtComplex hw d (x p)) := fun p d => by
    simpa only [List.foldr] using (hreg p [d]).2
  have h2 : ∀ p (d d' : ArchDirComplex), Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' (x p))) := fun p d d' => by
    simpa only [List.foldr] using (hreg p [d, d']).2
  have hcomm : ∀ m : GL (Fin 2) ℂ, archComplexGLAt hw m * g₀ = g₀ * archComplexGLAt hw m := fun m =>
    DCFN.archComplexGLAt_mul_comm_of_archComponent_eq_one K hw m _hg₀

  have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar K).continuous

  have hcw : ∀ (p : Fin (n + 1)) (j : Fin 10), Continuous (casWords hw (x p) j) := by
    intro p j
    have h2 : ∀ a b' : ArchDirComplex, Continuous (archDerivAtComplex hw a (archDerivAtComplex hw b' (x p))) :=
      fun a b' => by simpa only [List.foldr] using (hreg p [a, b']).2
    have h1 : ∀ a : ArchDirComplex, Continuous (archDerivAtComplex hw a (x p)) :=
      fun a => by simpa only [List.foldr] using (hreg p [a]).2
    fin_cases j <;> simp only [casWords] <;> first | exact h2 _ _ | exact h1 _
  have hsm : ∀ p : Fin (n + 1), IsArchSmoothAtComplex hw (x p) := fun p => by simpa only [List.foldr] using (hreg p []).1

  have hWsmul : ∀ (p : Fin (n + 1)) (c : ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (c • x p) 1 g = c * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
    intro p c g
    have h := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ 1 (fun _ => x p) (fun _ => hxc p) (fun _ => c) 1 g
    simp only [Fin.sum_univ_one] at h
    rw [show (c • x p) = fun g' => c * x p g' from funext fun g' => by simp [Pi.smul_apply, smul_eq_mul]]
    exact h
  have hWsum : ∀ (p : Fin (n + 1)) (cf : Fin 10 → ℂ) (g : AdelicGL2 (𝓞 K) K),
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (fun g' => ∑ j : Fin 10, cf j * casWords hw (x p) j g') 1 g =
        ∑ j : Fin 10, cf j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g := fun p cf g =>
    AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
      (fun v => heckeGen (𝓞 K) K v) _ hψ 10 (casWords hw (x p)) (hcw p) cf 1 g
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    exact (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) g₀).1
  · intro p d d' h
    exact (AutomorphicForm.hasDerivAt_whittakerCoefficient_archFlowComplex_of_continuous_archDerivAtComplex K D w hw (x p)
      (hxc p) (hs p) (h1 p) (h2 p) g₀).2 d' d h
  · intro p h
    set g : AdelicGL2 (𝓞 K) K := g₀ * archComplexGLAt hw h with hg
    have key : ∑ j : Fin 10, casCoeff j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g = lam * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
      rw [← hWsum, ← hWsmul, ← archCasimirAtComplex_eq_sum hw (hsm p), (hcas p).1]
    rw [← key]
    simp only [casCoeff, casWords, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.isValue]
    linear_combination (-(1 / 16 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 g -
      (1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 g) * Complex.I_sq
  · intro p h
    set g : AdelicGL2 (𝓞 K) K := g₀ * archComplexGLAt hw h with hg
    have key : ∑ j : Fin 10, casBarCoeff j * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (casWords hw (x p) j) 1 g = lam' * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g := by
      rw [← hWsum, ← hWsmul, ← archCasimirBarAtComplex_eq_sum hw (hsm p), (hcas p).2]
    rw [← key]
    simp only [casBarCoeff, casWords, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.isValue]
    linear_combination (-(1 / 16 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iH (archDerivAtComplex hw .iH (x p))) 1 g -
      (1 / 4 : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm (x p))) 1 g) * Complex.I_sq
  · intro p z h
    set X : AdeleRing (𝓞 K) K := (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0))
      with hX
    have hgeom : g₀ * archComplexGLAt hw (unipotentGL2 z * h) = unipotentGL2 X * (g₀ * archComplexGLAt hw h) := by
      rw [map_mul, ← mul_assoc, ← hcomm, archComplexGLAt_unipotentGL2, mul_assoc]
    rw [hgeom]
    have hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K),
        x p (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * (g₀ * archComplexGLAt hw h)) =
          x p (unipotentGL2 u * (g₀ * archComplexGLAt hw h)) := by
      intro β u
      rw [unipotentGL2_add, mul_assoc, unipotentGL2_algebraMap_eq_globalPoints, hxG]
    have hcov := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul K D
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (NumberField.StandardAddChar.stdAddChar K)
      (NumberField.StandardAddChar.adelicTraceData K).isGlobalAddChar_psiK.principalInvariant
      (x p) (g₀ * archComplexGLAt hw h) hper 1 X
    rw [map_one, one_mul] at hcov
    rw [hcov, hX, NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex K w hw z, one_mul]
  · intro p ζ hζ h
    rw [map_mul, ← mul_assoc, DCFN.whittakerCoefficient_mul_right]
    have hfun : (fun y => x p (y * archComplexGLAt hw (circleGL2 ζ))) = fun y => (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * x p y :=
      funext fun y => hwt p ζ hζ y
    rw [hfun, DCFN.whittakerCoefficient_const_mul]
  · exact (KType.hK_of_string K D hw g₀ n x hxc E₁ E₂ hK₁ hK₂).1
  · exact (KType.hK_of_string K D hw g₀ n x hxc E₁ E₂ hK₁ hK₂).2

end AutomorphicForm

end
