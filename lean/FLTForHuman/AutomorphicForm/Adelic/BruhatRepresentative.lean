/-
  The Bruhat representative of a coset is unique up to the subgroup.

  The Bruhat cell of `GL₂(K)` is `B w B`, where `w` is the transposition `gl2Weyl`: every
  matrix of `GL₂(K)` can be written as `w u(ξ) γ ∈ B` for exactly one `ξ`, or as `u(0) γ ∈ B`
  and no `ξ` works — the "`o = none`" case, which is the big cell. Uniqueness is what the
  determinant buys: the `(1,0)` entry of `w u(ξ) γ` is `γ₀₀ + ξ γ₁₀`, an affine function of `ξ`
  with nonzero slope whenever `γ₁₀ ≠ 0`, and it must vanish for `w u(ξ) γ` to be upper
  triangular. So `∃! o : Option K` with `(o.elim 1 fun ξ => gl2Weyl * unipotentGL2 ξ) * γ ∈ B`,
  `none` being the big cell and `some ξ` the cell on which the transposition is undone.

  spec-pin: P2M/Sol/S_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup.lean

  ## Port deltas

  - Namespaces: the pin's workspace label `BruhatC5` is dropped, so its two engines sit
    directly in `AutomorphicForm`. The statements are the pin's text verbatim (nothing in
    them is qualified through the label); `check_port` hashes them to the pin's rows.
  - Public/private: the pin marks neither engine `private`, so both are transcribed public and
    `check_port` reads all three declarations `ok`.
  - Imports unchanged from the scaffold; `gl2Weyl_val` (`WeylIntertwining`) and
    `unipotentGL2_coe` (`ConstantTerm`) are both in its closure.
  - No body deviation: the pin's proof replays verbatim, including its case split on the
    `(1,0)` entry of `γ` (the `none`/`some ξ` dichotomy above).

  ## Heartbeat probe (recorded, never installed — FR-0225)

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N
  FLTForHuman/AutomorphicForm/Adelic/BruhatRepresentative.lean` is **silent at N = 4 000** and
  **fails at N = 2 000** (`elaborator` timeout in the row's second `refine` block); 1 000 fails
  earlier, inside `simp` at the `entry_weyl_unipotent_mul` rewrite. The measured pair for the
  probe is 4 000 / 2 000. No `set_option maxHeartbeats` is in this module.
-/

import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm MeasureTheory

namespace AutomorphicForm

section Engines

variable {K : Type*} [Field K]

/-- The `(1,0)` entry of `w u(ξ) γ` is `γ₀₀ + ξ γ₁₀`: the affine coordinate of the Bruhat cell. -/
theorem entry_weyl_unipotent_mul (ξ : K) (γ : GL (Fin 2) K) :
    ((((gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 + ξ * (γ : Matrix (Fin 2) (Fin 2) K) 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, gl2Weyl_val, unipotentGL2_coe]

/-- The determinant of a matrix in `GL₂(K)` is nonzero: the slope of the affine coordinate. -/
theorem det_ne_zero (γ : GL (Fin 2) K) : (γ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact (Matrix.GeneralLinearGroup.det γ).ne_zero

end Engines

theorem existsUnique_bruhatRepresentative_mul_mem_borelSubgroup
    (K : Type*) [Field K] (γ : GL (Fin 2) K) :
    ∃! o : Option K, (o.elim 1 fun ξ => (gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ ∈ borelSubgroup K := by
  have hdet := det_ne_zero γ
  rw [Matrix.det_fin_two] at hdet
  by_cases h10 : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · refine ⟨none, ?_, ?_⟩
    · show (Option.elim none 1 fun ξ => (gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ ∈ borelSubgroup K
      simp only [Option.elim, one_mul, mem_borelSubgroup_iff]
      exact h10
    · intro o ho
      cases o with
      | none => rfl
      | some ξ =>
        exfalso
        have h := ho
        simp only [Option.elim, mem_borelSubgroup_iff] at h
        rw [entry_weyl_unipotent_mul, h10, mul_zero, add_zero] at h
        apply hdet
        rw [h, h10]; ring
  · refine ⟨some (-((γ : Matrix (Fin 2) (Fin 2) K) 0 0) / (γ : Matrix (Fin 2) (Fin 2) K) 1 0), ?_, ?_⟩
    · show (Option.elim (some _) 1 fun ξ => (gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ ∈ borelSubgroup K
      simp only [Option.elim, mem_borelSubgroup_iff]
      rw [entry_weyl_unipotent_mul]
      field_simp
      ring
    · intro o ho
      cases o with
      | none =>
        exfalso
        have h := ho
        simp only [Option.elim, one_mul, mem_borelSubgroup_iff] at h
        exact h10 h
      | some ξ =>
        have h := ho
        simp only [Option.elim, mem_borelSubgroup_iff] at h
        rw [entry_weyl_unipotent_mul] at h
        congr 1
        field_simp
        linear_combination h

end AutomorphicForm

end
