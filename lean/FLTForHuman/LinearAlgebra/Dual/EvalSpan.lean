/-
  The shared prelude of the matrix-group right-finite pair: every functional on a
  finite-dimensional space of functions is a finite combination of point evaluations.

  The port of the two leaves
  `Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite` and
  `Matrix.OrthogonalGroup.exists_polynomial_eq_of_continuous_of_rightFinite` writes this
  lemma twice, byte for byte (`P2M/Sol/S_…Unitary….lean`, `P2M/Sol/S_…Orthogonal….lean`,
  namespace `M4aP3C.TensorSplit`). It has no matrix or analytic content, so it is homed
  once here, at the pin's name, and imported by both group modules
  (`Analysis/MatrixGroup/{Unitary,Orthogonal}RightFinite.lean`).

  It is the point-evaluation form of "the dual of a finite-dimensional space of functions
  has no nontrivial annihilator": the evaluation maps `ev x : w ↦ w x` span the dual of a
  finite-dimensional `W ≤ G → ℂ`, because their common coannihilator is `⊥`, so the
  double-annihilator of their span is everything (`Subspace.dualCoannihilator_dualAnnihilator_eq`).

  spec-pin: P2M/Sol/S_Matrix_UnitaryGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean
  spec-pin: P2M/Sol/S_Matrix_OrthogonalGroup_exists_polynomial_eq_of_continuous_of_rightFinite.lean
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false

noncomputable section

namespace Submodule

variable {G : Type*}

/-- Every functional on a finite-dimensional space of functions is a finite linear
combination of point evaluations: there are `e : Fin m → ℂ` and `x : Fin m → G` with
`φ w = ∑ l, e l * w (x l)` for all `w`. -/
theorem exists_eval_combination (W : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → G), ∀ w : W, φ w = ∑ l, e l * (w : G → ℂ) (x l) := by
  classical
  let ev : G → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : G → ℂ) x := fun x w => rfl
  let Φ : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev)
  have hco : Φ.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext x
    have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
    rw [hev] at this
    simpa using this
  have hΦ : Φ = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Φ)
    rw [hco, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  have hφ : φ ∈ Φ := by rw [hΦ]; exact Submodule.mem_top
  rw [Submodule.mem_span_set'] at hφ
  obtain ⟨m, e, g, hg⟩ := hφ
  have hg' : ∀ l, ∃ x, ev x = ((g l : Set.range ev) : Module.Dual ℂ W) := fun l => (g l).2
  choose x hx using hg'
  refine ⟨m, e, x, fun w => ?_⟩
  rw [← hg]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [LinearMap.smul_apply, ← hx l, hev, smul_eq_mul]

end Submodule
