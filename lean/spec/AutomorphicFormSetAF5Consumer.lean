/-
  Cross-module wire test for SET-AF5 (the right-convolution operator's calculus).

  A `spec/` probe, not a library module. Three zones:

  * zone A composes the **general** unipotent continuity with the group structure: additivity
    `unipotentGL2_add` turns it into continuity of `x ↦ unipotentGL2 (x₀ + x)`, and the two
    statements the deleted specialisations used to provide are read off it directly. The zone
    fails if `Adelic/ConstantTerm.lean` loses `continuous_unipotentGL2`;
  * zone B composes the **translation law** with itself, so an iterated right translation
    `g * (t₁ * t₂)` is absorbed into a doubly-composed test function, and reads the law at
    `t = 1`. The zone fails if `Adelic/RightConvolution.lean` loses
    `rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply`;
  * zone C composes the **regularity headline** with the rest of the port: its first
    component read off directly, then re-indexed through the translation law (so the zone
    fails if either the headline or the law goes away), and composed with the general
    unipotent continuity in the adelic unipotent coordinate; its second component at
    `g = 1`, weakened along the `ℕ∞` order to `C^1` and then to continuity of the
    unipotent line. The zone fails if
    `Adelic/RightConvRegularity.lean` loses
    `continuous_rightConv_and_contDiff_of_isFactorizableTestFn`.

  Every zone is a real composition — no `#check`.
-/
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity

set_option autoImplicit false

open NumberField Matrix AutomorphicForm

namespace SetAF5RightConvConsumer

variable {F : Type} [Field F] [NumberField F]

/-- Zone A: continuity of the unipotent embedding at an arbitrary point, from the general
lemma plus additivity. -/
example (x₀ : AdeleRing (𝓞 F) F) :
    Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 (x₀ + x) : AdelicGL2 (𝓞 F) F) := by
  have h : Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) :=
    continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)
  have hfun : (fun x : AdeleRing (𝓞 F) F => (unipotentGL2 (x₀ + x) : AdelicGL2 (𝓞 F) F)) =
      fun x => (unipotentGL2 x₀ : AdelicGL2 (𝓞 F) F) * unipotentGL2 x := by
    funext x
    rw [unipotentGL2_add]
  rw [hfun]
  exact continuous_const.mul h

/-- Zone A: the deleted `…_adele`/`…'` specialisations are instances of the general lemma. -/
example : Continuous fun x : AdeleRing (𝓞 F) F => (unipotentGL2 x : AdelicGL2 (𝓞 F) F) :=
  continuous_unipotentGL2

/-- Zone B: the translation law read at `t = 1`. -/
example (φ f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (g * 1) = rightConv F φ f g := by
  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
  simp

/-- Zone B: the law composed with itself — an iterated right translation. -/
example (φ f : AdelicGL2 (𝓞 F) F → ℂ) (g t₁ t₂ : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (g * (t₁ * t₂)) =
      rightConv F φ (fun y => f (t₂⁻¹ * (t₁⁻¹ * y))) g := by
  rw [← mul_assoc, rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply,
    rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]

/-- Zone C: the operator is continuous in the group variable — the headline's first
component at the pin's statement. -/
example (φ f : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hf : IsFactorizableTestFn F f) : Continuous (rightConv F φ f) :=
  (continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).1

/-- Zone C: continuity in the **adelic** unipotent coordinate, the headline's first
component composed with the general unipotent continuity. -/
example (φ f : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hf : IsFactorizableTestFn F f) (g : AdelicGL2 (𝓞 F) F) :
    Continuous fun x : AdeleRing (𝓞 F) F => rightConv F φ f (unipotentGL2 x * g) := by
  have h := (continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).1
  exact h.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul continuous_const)

/-- Zone C: the translation law re-indexes the headline's continuity — a right
translation of the group variable is absorbed into the test function. -/
example (φ f : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hf : IsFactorizableTestFn F f) (t : AdelicGL2 (𝓞 F) F) :
    Continuous fun g => rightConv F φ (fun y => f (t⁻¹ * y)) g := by
  have h := (continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).1
  have hfun : (fun g => rightConv F φ (fun y => f (t⁻¹ * y)) g) =
      fun g => rightConv F φ f (g * t) := by
    funext g
    rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
  rw [hfun]
  exact h.comp (continuous_id.mul continuous_const)

open scoped Classical ContDiff in
/-- Zone C: the unipotent line is `C^1` at `g = 1` — the headline's second component
weakened along the `ℕ∞` order. -/
example (φ f : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hf : IsFactorizableTestFn F f) :
    ContDiff ℝ 1 (fun z : mixedEmbedding.mixedSpace F =>
      rightConv F φ f (unipotentGL2 (R := AdeleRing (𝓞 F) F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0) * 1)) :=
  ((continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).2 1).of_le
    (show (1 : ℕ∞ω) ≤ ↑(Module.finrank ℚ F + 1) by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _))

open scoped Classical ContDiff in
/-- Zone C: hence the unipotent line is continuous in the archimedean variable. -/
example (φ f : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hf : IsFactorizableTestFn F f) :
    Continuous fun z : mixedEmbedding.mixedSpace F =>
      rightConv F φ f (unipotentGL2 (R := AdeleRing (𝓞 F) F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0) * 1) :=
  ((continuous_rightConv_and_contDiff_of_isFactorizableTestFn F φ hcont f hf).2 1).continuous

end SetAF5RightConvConsumer
