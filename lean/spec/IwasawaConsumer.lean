/-
  Cross-module wire test for the Iwasawa analytic core's definition layer.

  A `spec/` probe, not a library module. One executed zone per layer
  (`topics/automorphicForm/TOPIC-iwasawa-analytic-core.md` §4): D the complex Iwasawa
  vocabulary (`Definitions/Def_AutomorphicForm_ComplexIwasawa` homed whole), F the shared
  generic Fourier-decay bound (`M4aP3B.FourierDecay` homed once for both waves). Every zone
  is a real composition — no `#check` — so deleting either module makes the probe fail.
-/
import FLTForHuman.AutomorphicForm.Iwasawa.Complex.Basic
import FLTForHuman.AutomorphicForm.Iwasawa.Complex.Estimates
import FLTForHuman.AutomorphicForm.Iwasawa.Real.Estimates
import FLTForHuman.MeasureTheory.FourierDecay

open MeasureTheory
open scoped ContDiff FourierTransform

namespace IwasawaConsumer

/-! ### Zone D — the complex Iwasawa vocabulary

The pin's `botP`/`botQ`/`radC`/`kC` are public at `AutomorphicForm.ComplexIwasawa.*`.
Deleting `FLTForHuman/AutomorphicForm/Iwasawa/Complex/Basic.lean` breaks this zone. -/

open AutomorphicForm.ComplexIwasawa

-- The concrete instantiation: at the identity matrix and `z = 0` the bottom row is
-- `(1, 0)`, so the radial length is `1` (`Real.sqrt 1 = 1`).
example : botP (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 = 1 := by
  rw [botP]
  simp

example : botQ (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 = 0 := by
  rw [botQ]
  simp

example : radC (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 = 1 := by
  rw [radC, botP, botQ]
  norm_num [Complex.normSq]

-- The two `def`s are genuinely the module's: their bodies unfold to the stated rows.
example (z : ℂ) : botP (1 : Matrix (Fin 2) (Fin 2) ℂ) z = 1 := by
  rw [botP]
  simp

example (z : ℂ) : botQ (1 : Matrix (Fin 2) (Fin 2) ℂ) z = z := by
  rw [botQ]
  simp

/-! ### Zone F — the shared generic Fourier-decay bound

Concrete instantiation at `V = W = E = ℂ` with the degenerate coercive map `L = 0`, so the
hypothesis `hL` is exactly the other landed declaration, `gate_degenerate`. Deleting
`FLTForHuman/MeasureTheory/FourierDecay.lean` breaks this zone. -/

example (n : ℕ) (f : ℂ → ℂ) (hf : ContDiff ℝ n f)
    (h'f : ∀ j : ℕ, j ≤ n → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) volume)
    (w : ℂ) :
    ((0 : ℝ) * ‖w‖) ^ n
        * ‖VectorFourier.fourierIntegral 𝐞 volume
            (0 : ℂ →L[ℝ] ℂ →L[ℝ] ℝ).toLinearMap₁₂ f w‖
      ≤ 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume :=
  MeasureTheory.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive
    (0 : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) hf h'f le_rfl
    (fun w => MeasureTheory.FourierDecay.gate_degenerate volume w) w

example (w : ℂ) :
    ∃ v : ℂ, ‖v‖ ≤ 1 ∧ (0 : ℝ) * ‖w‖
      ≤ ‖(0 : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) v w‖ :=
  MeasureTheory.FourierDecay.gate_degenerate volume w

/-! ### Zone E — the headline estimates

Concrete applications of the nine complex and four real public headlines (the tier-1
`Estimates.lean` façades over the tier-3 `Engine.*` kernels), at the identity matrix. Deleting
either façade breaks this zone. -/

open AutomorphicForm.ComplexIwasawa

example (z : ℂ) :
    kC (1 : Matrix (Fin 2) (Fin 2) ℂ) z ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
  kC_mem_specialUnitaryGroup (g := 1) (by simp) z

example (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i j : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ n (fun w => kC (1 : Matrix (Fin 2) (Fin 2) ℂ) w i j) z‖ ≤ C :=
  (contDiff_and_exists_bound_iteratedFDeriv_kC_apply
    (g := 1) (by simp)).2 n

example (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : g.det ≠ 0) :
    ∀ i j : Fin 2, ContDiff ℝ ∞
      (fun x => (Real.sqrt ((g 0 0 + x * g 1 0) ^ 2 + (g 0 1 + x * g 1 1) ^ 2))⁻¹
        * (!![g 0 1 + x * g 1 1, -(g 0 0 + x * g 1 0);
              g 0 0 + x * g 1 0, g 0 1 + x * g 1 1] : Matrix (Fin 2) (Fin 2) ℝ) i j) :=
  (AutomorphicForm.RealIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kR_apply hg).1

end IwasawaConsumer
