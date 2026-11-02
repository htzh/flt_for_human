/-
  Cross-module wire test for SET-AF6 (differentiating a right convolution along an
  archimedean flow).

  A `spec/` probe, not a library module. Four zones — A/B for R1
  (`Adelic/ArchDerivRightConv.lean`, a real place), C/D for R2
  (`Adelic/ArchDerivRightConvComplex.lean`, a complex place). Each zone is a real
  composition of two or three landed statements; none is a `#check`.

  * zone A composes R1's **first** conjunct with `RightConvRegularity`'s continuity — so it
    dies if either `ArchDerivRightConv` or `RightConvRegularity` goes away — and re-indexes
    the derivative identity through `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply`,
    which moves a right translation of the group variable into the test function;
  * zone B reads R1's **third** conjunct at `ω ≡ 1` (the adjointness) and composes it with
    the second conjunct's tensor form at `ff ≡ 1`, ending in an actual `rightConv` identity
    between a differentiated archimedean factor and the derivative of `φ`;
  * zones C and D are the same two compositions at a complex place, through R2
    (`…Complex.lean`) and the same two AF5 modules, with `archDerivAtComplex` /
    `IsArchSmoothAtComplex` / `archFlowAtComplex` in place of the real vocabulary.

  The probe imports only the two SET-AF6 modules and the AF5 modules they consume, so every
  statement it names is one of the set's own or one of its premises.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivRightConv
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivRightConvComplex
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel

namespace SetAF6ArchDerivRightConvConsumer

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F}

/-! ### Zone A — R1: the first conjunct, composed with AF5's continuity and the translation law -/

/-- Zone A: `rightConv φ α` is both `Continuity`-regular and archimedean-smooth — R1's first
conjunct and `RightConvRegularity`'s first component, side by side. The example dies if either
module loses its statement. -/
example (hw : w.IsReal) (d : ArchDir) (φ α : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hα : IsFactorizableTestFn F α) :
    Continuous (rightConv F φ α) ∧ IsArchSmoothAt hw (rightConv F φ α) :=
  ⟨(continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hφ α hα).1,
    (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).1 φ α hφ hα |>.1⟩

/-- Zone A: R1's derivative identity re-indexed through the translation law — the derivative of
`rightConv φ α` at a right translate `g * t` is the right convolution of `φ` with the
`t⁻¹`-translate of the differentiated test function, tested at `g`. -/
example (hw : w.IsReal) (d : ArchDir) (φ α : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hα : IsFactorizableTestFn F α) (g t : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d (rightConv F φ α) (g * t) =
      rightConv F φ
        (fun y => deriv (fun s : ℝ => α (archFlowAt hw d (-s) * (t⁻¹ * y))) 0) g := by
  rw [((archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).1 φ α hφ hα).2]
  exact rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F φ _ g t

/-! ### Zone B — R1: the third conjunct at `ω ≡ 1`, composed with the second -/

/-- Zone B: the adjointness at `ω ≡ 1` — both sides are `rightConv`'s, so the statement is a
genuine identity of convolutions, not a restatement. -/
example (hw : w.IsReal) (d : ArchDir) (φ γ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφs : IsArchSmoothAt hw φ) (hφ' : Continuous (archDerivAt hw d φ)) (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (hγs : IsArchSmoothAt hw γ) (hγ' : Continuous (archDerivAt hw d γ)) :
    rightConv F φ (fun y => archDerivAt hw d γ y) =
      -rightConv F (archDerivAt hw d φ) γ := by
  have h := (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.2
  simpa using h φ γ (fun _ => 1) hφ hφs hφ' hγ hγc hγs hγ' continuous_const (fun _ _ => rfl)

/-- Zone B: the second conjunct at `ff ≡ 1` produces the archimedean test factor `fa'` of the
left-derivative chart, and that same pair is then fed to the third conjunct, so the two halves
of the row meet in one `rightConv` identity. -/
example (hw : w.IsReal) (d : ArchDir) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa)
    (hφ : Continuous φ) (hφs : IsArchSmoothAt hw φ) (hφ' : Continuous (archDerivAt hw d φ))
    (hγ : Continuous fun y => fa (glArch (𝓞 F) F y))
    (hγc : HasCompactSupport fun y => fa (glArch (𝓞 F) F y))
    (hγs : IsArchSmoothAt hw fun y => fa (glArch (𝓞 F) F y))
    (hγ' : Continuous (archDerivAt hw d fun y => fa (glArch (𝓞 F) F y))) :
    ∃ fa' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F fa' ∧
      (fun y => deriv (fun t : ℝ => fa (glArch (𝓞 F) F (archFlowAt hw d (-t) * y))) 0) =
        (fun y => fa' (glArch (𝓞 F) F y)) ∧
      rightConv F φ (fun y => archDerivAt hw d (fun z => fa (glArch (𝓞 F) F z)) y) =
        -rightConv F (archDerivAt hw d φ) (fun y => fa (glArch (𝓞 F) F y)) := by
  obtain ⟨fa', hfa', hEq⟩ :=
    (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.1 fa (fun _ => 1) hfa
  have hid := (archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.2
    φ _ (fun _ => 1) hφ hφs hφ' hγ hγc hγs hγ' continuous_const (fun _ _ => rfl)
  exact ⟨fa', hfa', by simpa using hEq, by simpa using hid⟩

/-! ### Zone C — R2: the complex mirror of zone A -/

/-- Zone C: the complex mirror of zone A — R2's first conjunct composed with AF5's continuity. -/
example (hw : w.IsComplex) (d : ArchDirComplex) (φ α : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hα : IsFactorizableTestFn F α) :
    Continuous (rightConv F φ α) ∧ IsArchSmoothAtComplex hw (rightConv F φ α) :=
  ⟨(continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hφ α hα).1,
    (archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).1 φ α hφ hα |>.1⟩

/-- Zone C: the complex derivative identity re-indexed through the translation law. -/
example (hw : w.IsComplex) (d : ArchDirComplex) (φ α : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hα : IsFactorizableTestFn F α) (g t : AdelicGL2 (𝓞 F) F) :
    archDerivAtComplex hw d (rightConv F φ α) (g * t) =
      rightConv F φ
        (fun y => deriv (fun s : ℝ => α (archFlowAtComplex hw d (-s) * (t⁻¹ * y))) 0) g := by
  rw [((archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).1 φ α hφ hα).2]
  exact rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F φ _ g t

/-! ### Zone D — R2: the complex mirror of zone B -/

/-- Zone D: the complex adjointness at `ω ≡ 1`. -/
example (hw : w.IsComplex) (d : ArchDirComplex) (φ γ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hφs : IsArchSmoothAtComplex hw φ) (hφ' : Continuous (archDerivAtComplex hw d φ)) (hγ : Continuous γ)
    (hγc : HasCompactSupport γ) (hγs : IsArchSmoothAtComplex hw γ)
    (hγ' : Continuous (archDerivAtComplex hw d γ)) :
    rightConv F φ (fun y => archDerivAtComplex hw d γ y) =
      -rightConv F (archDerivAtComplex hw d φ) γ := by
  have h := (archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.2
  simpa using h φ γ (fun _ => 1) hφ hφs hφ' hγ hγc hγs hγ' continuous_const (fun _ _ => rfl)

/-- Zone D: the complex second conjunct's tensor form and the complex adjointness in one
`rightConv` identity. -/
example (hw : w.IsComplex) (d : ArchDirComplex) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa)
    (hφ : Continuous φ) (hφs : IsArchSmoothAtComplex hw φ)
    (hφ' : Continuous (archDerivAtComplex hw d φ))
    (hγ : Continuous fun y => fa (glArch (𝓞 F) F y))
    (hγc : HasCompactSupport fun y => fa (glArch (𝓞 F) F y))
    (hγs : IsArchSmoothAtComplex hw fun y => fa (glArch (𝓞 F) F y))
    (hγ' : Continuous (archDerivAtComplex hw d fun y => fa (glArch (𝓞 F) F y))) :
    ∃ fa' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ, IsArchTestFactor F fa' ∧
      (fun y => deriv (fun t : ℝ => fa (glArch (𝓞 F) F (archFlowAtComplex hw d (-t) * y))) 0) =
        (fun y => fa' (glArch (𝓞 F) F y)) ∧
      rightConv F φ (fun y => archDerivAtComplex hw d (fun z => fa (glArch (𝓞 F) F z)) y) =
        -rightConv F (archDerivAtComplex hw d φ) (fun y => fa (glArch (𝓞 F) F y)) := by
  obtain ⟨fa', hfa', hEq⟩ :=
    (archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.1 fa
      (fun _ => 1) hfa
  have hid := (archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn F hw d).2.2
    φ _ (fun _ => 1) hφ hφs hφ' hγ hγc hγs hγ' continuous_const (fun _ _ => rfl)
  exact ⟨fa', hfa', by simpa using hEq, by simpa using hid⟩

end SetAF6ArchDerivRightConvConsumer
