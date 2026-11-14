/-
  SET-AF69A consumer: the high part of a compact self-adjoint operator, fired at the terminal
  data — the zero operator on `ℂ`.

  **The zone.** Five rows, hence five compositions, all on the one module
  `FLTForHuman/Analysis/InnerProductSpace/HighPart.lean`:

  * A — `ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq`
    (`SymmetricRangeDensity`);
  * B — `ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal`;
  * C — `ContinuousLinearMap.map_highPart_orthogonal_le_of_commute`;
  * D — `ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker`;
  * E — `ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute`.

  **The data.** `𝕜 = ℂ` and `E = ℂ` (one-dimensional, so *every* operator is compact), with
  `T = 0` and `S = 0`: the zero operator is compact (`isCompactOperator_zero`), self-adjoint
  (`IsSymmetric` of the zero linear map is `simp`), and commutes with everything, so all the
  hypotheses of B–E are met at this single datum. `X` is the whole space, as the order prescribes.

  **The readings.**

  * Zone A. The `SymmetricRangeDensity` engine is fired at `H = ℂ`, `T = 0`, `E = ⊤`, `v = 0`,
    with the surjectivity hypothesis instantiated at the witness `0` (for `T = 0` and `v = 0`,
    `T w - c • w = v` is `0 = 0` for every `c`). The conclusion `v = 0` is then spent as `‖v‖ = 0`.
  * Zone B. At `X = ⊤` the alternative hypothesis is met in its *second* branch: for `r > 0` no
    eigenvalue of `T = 0` satisfies `r ≤ ‖μ‖` with `μ ≠ 0`, so every `eigenspace T μ` occurring in
    the join is `⊥`, the join is `⊥`, and its orthogonal complement is `⊤`. The headline then
    delivers `⊤ ≤ ker 0 ∨ FiniteDimensional ℂ ↥⊤`; the consumer eliminates the alternative and,
    in the kernel branch, reads it as `(0 : ℂ →L[ℂ] ℂ) x = 0` for the arbitrary `x` it carries —
    the first branch is exactly the statement that the zero operator annihilates the space.
  * Zone C. The commuting map is `S = 0`: the headline gives
    `map 0 (highPart 0 r)ᗮ ≤ (highPart 0 r)ᗮ`, and the consumer spends it on the image of `0`,
    which lies in the mapped submodule because `0` lies in the source.
  * Zone D. For `T = 0` the join of the nonzero eigenspaces is `⊥` and the kernel is `⊤`; the
    headline is read as an equality of subspaces and instantiated at an arbitrary `x : ℂ`,
    which it places in that kernel.
  * Zone E. At `T = 0`, `S = 0` and `μ = 1` (so `hμ : (1 : ℂ) ≠ 0`), the first conjunct of the
    headline sends `0` — the image of `0` under `S` — into the eigenspace `eigenspace 0 1`.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.Analysis.InnerProductSpace.HighPart

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace
open Module.End

namespace AF69AConsumer

/-- The zero operator on `ℂ` is symmetric: this is the `hT'` of B–E at the terminal data. -/
theorem zero_isSymmetric : ((0 : ℂ →L[ℂ] ℂ) : ℂ →ₗ[ℂ] ℂ).IsSymmetric := by
  intro x y
  simp

/-- Zone A: the symmetric-range engine at `T = 0`, `E = ⊤`, `v = 0`, the surjectivity hypothesis
being met by the witness `0`. The conclusion `v = 0` is spent as `‖v‖ = 0`. -/
theorem norm_eq_zero_of_symmetricRangeDensity :
    ‖(0 : ℂ)‖ = 0 := by
  have h := ContinuousLinearMap.eq_zero_of_forall_exists_mem_sub_real_smul_eq
    (T := (0 : ℂ →L[ℂ] ℂ)) ⊤ (by intro x _ y _; simp) (0 : ℂ)
    (fun c => ⟨0, Submodule.mem_top, by simp⟩)
  rw [h, norm_zero]

/-- Zone B, the alternative hypothesis in its second branch: for `r > 0` every eigenspace of the
zero operator that occurs in `highPart 0 r` is `⊥`, so the whole space sits in the orthogonal
complement of the high part. -/
theorem le_highPart_orthogonal_of_zero {r : ℝ} (hr : 0 < r) :
    (⊤ : Submodule ℂ ℂ) ≤
      (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (0 : Module.End ℂ ℂ) μ)ᗮ := by
  have hp : ∀ μ : ℂ, r ≤ ‖μ‖ → Module.End.eigenspace (0 : Module.End ℂ ℂ) μ = ⊥ := by
    intro μ hμ
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx
    have hμ0 : μ ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hμ
      exact absurd hμ (not_le.mpr hr)
    rw [LinearMap.zero_apply] at hx
    exact (smul_eq_zero.mp hx.symm).resolve_left hμ0
  have hbot : (⨆ (μ : ℂ) (_ : r ≤ ‖μ‖), Module.End.eigenspace (0 : Module.End ℂ ℂ) μ) = ⊥ := by
    refine le_antisymm (iSup₂_le fun μ hμ => ?_) bot_le
    rw [hp μ hμ]
  rw [hbot, Submodule.bot_orthogonal_eq_top]

/-- Zone B: the high-part alternative headline at `T = 0` and `X = ⊤`, eliminated on the arbitrary
`x` it carries — the kernel branch is the statement that `T = 0` annihilates the space. -/
theorem apply_zero_eq_zero (x : ℂ) : (0 : ℂ →L[ℂ] ℂ) x = 0 := by
  rcases ContinuousLinearMap.le_ker_or_finiteDimensional_of_forall_inf_highPart_orthogonal
      (𝕜 := ℂ) (E := ℂ) (T := 0) isCompactOperator_zero zero_isSymmetric ⊤
      (fun r hr => Or.inr (le_highPart_orthogonal_of_zero hr)) with h | h
  · exact h Submodule.mem_top
  · rfl

/-- Zone C: the commuting map is `S = 0`, and the headline's conclusion is spent on the image of
`0`, which is in the mapped submodule because `0` is in the source. -/
theorem zero_mem_highPart_orthogonal :
    (0 : ℂ) ∈
      (⨆ (μ : ℂ) (_ : (0 : ℝ) ≤ ‖μ‖), Module.End.eigenspace (0 : Module.End ℂ ℂ) μ)ᗮ := by
  have h := ContinuousLinearMap.map_highPart_orthogonal_le_of_commute
    (T := (0 : ℂ →L[ℂ] ℂ)) (S := 0) zero_isSymmetric rfl (0 : ℝ)
  exact h (Submodule.mem_map_of_mem (Submodule.zero_mem _))

/-- Zone D: the kernel description of the orthogonal complement at `T = 0`, instantiated at an
arbitrary `x : ℂ`, which it places in `ker 0`. -/
theorem mem_orthogonal_iSup_eigenspace (x : ℂ) :
    x ∈ (⨆ (μ : ℂ) (_ : μ ≠ 0),
      Module.End.eigenspace ((0 : ℂ →L[ℂ] ℂ) : Module.End ℂ ℂ) μ)ᗮ := by
  rw [ContinuousLinearMap.orthogonal_iSup_eigenspace_ne_zero_eq_ker
    (T := (0 : ℂ →L[ℂ] ℂ)) isCompactOperator_zero zero_isSymmetric]
  simp

/-- Zone E: at `S = 0`, `μ = 1`, the eigenspace-preservation conjunct sends the image of `0` into
`eigenspace 0 1`. -/
theorem zero_mem_eigenspace :
    (0 : ℂ) ∈ Module.End.eigenspace (0 : Module.End ℂ ℂ) (1 : ℂ) := by
  have h := (ContinuousLinearMap.map_eigenspace_orthogonal_le_of_commute
    (T := (0 : ℂ →L[ℂ] ℂ)) isCompactOperator_zero zero_isSymmetric (0 : ℂ →L[ℂ] ℂ)
    rfl (1 : ℂ) one_ne_zero).1
  exact h (Submodule.mem_map_of_mem (Submodule.zero_mem _))

end AF69AConsumer
