/-
  The complex Iwasawa compact factor and its radial length.

  For a `2×2` complex matrix `g` with `g.det ≠ 0` and `z : ℂ`, the pin's `botP`/`botQ` are the
  bottom-row entries `g₀₀ + z g₁₀` and `g₀₁ + z g₁₁` of the unipotent translate `n(z) g`, `radC`
  is their Euclidean (real) radial length `√(‖botP‖² + ‖botQ‖²)`, and `kC` is the compact
  `SU(2)` factor of the Iwasawa decomposition of the Weyl–unipotent translate `w n(z) g`:

  `kC g z = !![conj (botQ g z) / r, -conj (botP g z) / r; botP g z / r, botQ g z / r]`.

  These four are the statement vocabulary of the complex-place archimedean estimates
  (`contDiff_and_exists_bound_iteratedFDeriv_kC_apply`,
  `norm_fourierIntegral_cpow_radC_mul_le_polyDecay`, …), so they are public at the pin's
  namespace and names. The complex engine writes its own proof-local copies of them under a
  mangled namespace; those are byte-identical to this module and are dropped (playbook §2.4).

  Transcribed whole from `Definitions/Def_AutomorphicForm_ComplexIwasawa.lean` (pinned
  `aa2d8b3`, 25 lines / 4 declarations), the pin's one role module for the complex compact
  factor (playbook §2.3). Its home is the complex theory directory of the Iwasawa analytic
  core ([../topics/automorphicForm/TOPIC-iwasawa-analytic-core.md](../topics/automorphicForm/TOPIC-iwasawa-analytic-core.md));
  the pin namespace `AutomorphicForm.ComplexIwasawa` is kept for checker fidelity.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_AutomorphicForm_ComplexIwasawa.lean
-/
-- The pin's `Mathlib.Data.Complex.Basic` / `Mathlib.Data.Real.Sqrt` are deprecated module paths
-- in v4.34.0; the declarations are unchanged.
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false

noncomputable section

open ComplexConjugate

namespace AutomorphicForm.ComplexIwasawa

variable (g : Matrix (Fin 2) (Fin 2) ℂ)

-- pin: botP (Def_AutomorphicForm_ComplexIwasawa.lean:13)
def botP (z : ℂ) : ℂ := g 0 0 + z * g 1 0

-- pin: botQ (Def_AutomorphicForm_ComplexIwasawa.lean:15)
def botQ (z : ℂ) : ℂ := g 0 1 + z * g 1 1

-- pin: radC (Def_AutomorphicForm_ComplexIwasawa.lean:17)
def radC (z : ℂ) : ℝ := Real.sqrt (Complex.normSq (botP g z) + Complex.normSq (botQ g z))

-- pin: kC (Def_AutomorphicForm_ComplexIwasawa.lean:19)
def kC (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![conj (botQ g z) / (radC g z : ℂ), -conj (botP g z) / (radC g z : ℂ);
     botP g z / (radC g z : ℂ), botQ g z / (radC g z : ℂ)]

end AutomorphicForm.ComplexIwasawa

end
