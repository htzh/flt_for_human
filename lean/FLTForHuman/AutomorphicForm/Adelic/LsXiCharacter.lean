/-
  The character of an `LsXi` function is trivial on the principal idèles, and continuous.

  `IsLsXiFunction (𝓞 K) K ⊤ χ φ` makes `φ` invariant under `GL₂(K)` and transform by `χ` under the
  centre; if moreover `φ` is continuous and not identically zero, then its central character `χ`

  * is **trivial on the principal idèles** `Kˣ` (the diagonal action of `Kˣ` is already absorbed by
    the `GL₂(K)`-invariance, and `φ` has a point where it does not vanish), and
  * is **continuous** (it is `φ (k · g) / φ g` at a fixed `g` with `φ g ≠ 0`, and `φ` is continuous).

  This is the entrance to the whole idèle-class-character API: `IsIdeleClassChar`, `IsUnitaryChar`
  and `SquaresToXi` are stated for characters that satisfy exactly these two properties, and the
  weight-one and Rankin–Selberg rows consume them through
  `AutomorphicForm.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` (199) and the
  `SmoothCuspRealizationAt` chain.

  The pin proves it inside `S_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous.lean`
  (62 declaration lines, 3 declarations) as one row; it is homed here rather than inserted into
  `AutomorphicForm/Adelic/LsXi.lean` because that module is the pin `Def_` transcription (its own
  wire, its own section variables), and this is a theorem *about* the definition.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import Mathlib.Topology.Algebra.Group.Units

set_option autoImplicit false

open MeasureTheory NumberField Matrix

noncomputable section

namespace AutomorphicForm

section CentralCharFromInvariance

variable (K : Type) [Field K] [NumberField K]

theorem globalPoints_scalar (u : Kˣ) :
    AutomorphicForm.globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) u)
      = AutomorphicForm.centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) := by
  apply Units.ext
  change (algebraMap K (AdeleRing (𝓞 K) K)).mapMatrix (Matrix.scalar (Fin 2) (u : K))
      = Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (u : K))
  rw [RingHom.mapMatrix_apply, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]

theorem continuous_centralScalar :
    Continuous (AutomorphicForm.centralScalar (𝓞 K) K : (AdeleRing (𝓞 K) K)ˣ → _) := by
  have hsc : Continuous fun r : AdeleRing (𝓞 K) K => Matrix.scalar (Fin 2) r := by
    refine continuous_matrix fun i j => ?_
    by_cases h : i = j
    · subst h
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      exact continuous_id
    · simp only [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h]
      exact continuous_const
  exact Continuous.units_map (Matrix.scalar (Fin 2) : AdeleRing (𝓞 K) K →+* _).toMonoidHom hsc

end CentralCharFromInvariance

/-- A continuous, non-vanishing `LsXi` function has a character that is trivial on the principal
idèles and continuous. -/
theorem isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
    (K : Type) [Field K] [NumberField K]
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ)
    (hcont : Continuous φ)
    (hne : ∃ g, φ g ≠ 0) :
    (∀ u : Kˣ, χ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u, Subgroup.mem_top _⟩ = 1) ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => χ ⟨z, Subgroup.mem_top z⟩ := by
  obtain ⟨g₀, hg₀⟩ := hne
  have hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)
        = φ (centralScalar (𝓞 K) K z * g₀) * (φ g₀)⁻¹ := by
    intro z
    have h := hφ.central_transform ⟨z, Subgroup.mem_top z⟩ g₀
    change φ (centralScalar (𝓞 K) K z * g₀)
        = ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g₀ at h
    rw [h, mul_inv_cancel_right₀ hg₀]
  refine ⟨fun u => ?_, ?_⟩
  · have h1 := hφ.left_invariant (Matrix.GeneralLinearGroup.scalar (Fin 2) u) g₀
    rw [globalPoints_scalar] at h1
    have h2 := hχ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u)
    rw [h1, mul_inv_cancel₀ hg₀] at h2
    exact Units.val_eq_one.mp h2
  · have hF : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      simp_rw [hχ]
      exact (hcont.comp ((continuous_centralScalar K).mul continuous_const)).mul continuous_const
    refine Units.continuous_iff.2 ⟨hF, ?_⟩
    have hinv : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        (((χ ⟨z, Subgroup.mem_top z⟩)⁻¹ : ℂˣ) : ℂ)
          = ((χ ⟨z⁻¹, Subgroup.mem_top z⁻¹⟩ : ℂˣ) : ℂ) := by
      intro z
      rw [← map_inv]
      rfl
    simp_rw [hinv]
    exact hF.comp continuous_inv

end AutomorphicForm

end
