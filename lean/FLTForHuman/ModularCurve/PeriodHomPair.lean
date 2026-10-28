/-
  The involution on `Γ₀(N)`-characters and the pair of period maps.

  `jConjMat` conjugates a `2 × 2` integer matrix by `diag(1, -1)`: it flips the
  signs of the two off-diagonal entries (`jConjMat_apply_zero_one`,
  `jConjMat_apply_one_zero`) and leaves the diagonal alone (its four `@[simp]`
  entry lemmas). It preserves the determinant (`jConjMat_det`) and the trace
  (`jConjMat_trace`), is multiplicative (`jConjMat_mul`), fixes `1`
  (`jConjMat_one`) and is an involution (`jConjMat_jConjMat`). Hence it induces a
  monoid homomorphism `jConjSL : SL(2, ℤ) →* SL(2, ℤ)` (`jConjSL_coe`,
  `jConjSL_jConjSL`); because it only negates the `(1, 0)` entry it preserves
  `Γ₀(N)` (`jConjSL_mem_Gamma0`), so it restricts to `jConjGamma0 : Γ₀(N) →* Γ₀(N)`
  (`jConjGamma0_coe`), again an involution (`jConjGamma0_jConjGamma0`).

  `charInvolution N R A` pulls a character `Additive (Gamma0 N) →+ A` back along
  `jConjGamma0` (`charInvolution_apply`); it is an `R`-linear involution
  (`charInvolution_charInvolution`) and it preserves the *parabolic* characters
  (`charInvolution_mem_parabolicHoms`), because conjugating an element does not
  move its trace. `ExistsPeriodMapLinear` says some linear `periodMap` lifts, and
  `periodHomPair` is the pair of period maps: the coproduct of `(id + χ) ∘ pml`
  and `(id - χ) ∘ pml` on a chosen lift, `0` if no lift exists;
  `periodHomPair_def` unfolds it on a given lift.

  Transcribed from `Definitions/Def_ModularCurve_PeriodHomPair.lean` (pinned
  `aa2d8b3`, 156 lines, 24 declarations) whole: `namespace ModularCurve.Period`
  with the pin's `JConj` and `CharInvolution` sections, then `ModularCurve`'s
  `PeriodHomPair` section. It sits on
  `ModularForms/EichlerShimura/PeriodPrimitive.lean` (`CuspForm`, `periodMap`,
  `parabolicHoms`, `mem_parabolicHoms_iff`) and `Mathlib.LinearAlgebra.Prod`
  (`LinearMap.coprod`); mathlib-only otherwise. Every statement is the pin's, and
  every proof is the pin's except for one mathlib-v4.34 API move:
  `periodHomPair_def` closes with `dite_eq_left h` where the pin writes
  `dif_pos h` (`dif_pos` is deprecated in favour of `dite_eq_left`; the same
  substitution the port's `periodMap_def` already makes).

  The wire is the pin `Def_` module **only**. The four `Theorems/` wrappers naming
  the pair (`periodHomPair_injective`, `periodHomPair_range_eq_parabolicHoms`,
  `range_periodHomPair_le_parabolicHoms`, `periodHomPair_eichlerShimura`) are the
  leaves' rows and this module hosts none of their statements, so their files are
  **not** on the wire: a `spec-pin:` line for a statement the module does not carry
  would make the frontier read that node as ported (MD-001's failure mode).

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_PeriodHomPair.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_periodHomPair_eichlerShimura.lean>

  spec-pin: Definitions/Def_ModularCurve_PeriodHomPair.lean
-/
import FLTForHuman.ModularForms.EichlerShimura.PeriodPrimitive
import Mathlib.LinearAlgebra.Prod

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace ModularCurve.Period

section JConj

def jConjMat (A : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![A 0 0, -A 0 1; -A 1 0, A 1 1]

@[simp] theorem jConjMat_apply_zero_zero (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 0 0 = A 0 0 := by simp [jConjMat]

@[simp] theorem jConjMat_apply_zero_one (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 0 1 = -A 0 1 := by simp [jConjMat]

@[simp] theorem jConjMat_apply_one_zero (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 1 0 = -A 1 0 := by simp [jConjMat]

@[simp] theorem jConjMat_apply_one_one (A : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat A 1 1 = A 1 1 := by simp [jConjMat]

theorem jConjMat_det (A : Matrix (Fin 2) (Fin 2) ℤ) : (jConjMat A).det = A.det := by
  rw [jConjMat, Matrix.det_fin_two_of, Matrix.det_fin_two]; ring

theorem jConjMat_trace (A : Matrix (Fin 2) (Fin 2) ℤ) : (jConjMat A).trace = A.trace := by
  rw [jConjMat, Matrix.trace_fin_two_of, Matrix.trace_fin_two]

theorem jConjMat_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    jConjMat (A * B) = jConjMat A * jConjMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jConjMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem jConjMat_jConjMat (A : Matrix (Fin 2) (Fin 2) ℤ) : jConjMat (jConjMat A) = A := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jConjMat]

theorem jConjMat_one : jConjMat (1 : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [jConjMat]

def jConjSL : SL(2, ℤ) →* SL(2, ℤ) where
  toFun A := ⟨jConjMat ((A : Matrix (Fin 2) (Fin 2) ℤ)), by rw [jConjMat_det]; exact A.2⟩
  map_one' := by
    apply Subtype.ext
    show jConjMat ((1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = _
    rw [Matrix.SpecialLinearGroup.coe_one, jConjMat_one]
  map_mul' A B := by
    apply Subtype.ext
    show jConjMat (((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, jConjMat_mul]; rfl

@[simp] theorem jConjSL_coe (A : SL(2, ℤ)) :
    ((jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = jConjMat ((A : Matrix (Fin 2) (Fin 2) ℤ)) := rfl

theorem jConjSL_jConjSL (A : SL(2, ℤ)) : jConjSL (jConjSL A) = A := by
  apply Subtype.ext; rw [jConjSL_coe, jConjSL_coe, jConjMat_jConjMat]

theorem jConjSL_mem_Gamma0 {N : ℕ} {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) :
    jConjSL A ∈ Gamma0 N := by
  have hA' : ((((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 :=
    Gamma0_mem.mp hA
  rw [Gamma0_mem]
  show ((((jConjSL A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0
  rw [jConjSL_coe, jConjMat_apply_one_zero]; push_cast; rw [hA', neg_zero]

variable (N : ℕ)

def jConjGamma0 : Gamma0 N →* Gamma0 N where
  toFun γ := ⟨jConjSL ↑γ, jConjSL_mem_Gamma0 γ.2⟩
  map_one' := by apply Subtype.ext; show jConjSL ↑(1 : Gamma0 N) = _;
                 rw [OneMemClass.coe_one, map_one]
  map_mul' γ δ := by apply Subtype.ext; show jConjSL ↑(γ * δ) = _;
                     rw [MulMemClass.coe_mul, map_mul]; rfl

@[simp] theorem jConjGamma0_coe (γ : Gamma0 N) :
    ((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) = jConjSL ↑γ := rfl

theorem jConjGamma0_jConjGamma0 (γ : Gamma0 N) :
    jConjGamma0 N (jConjGamma0 N γ) = γ := by
  apply Subtype.ext; rw [jConjGamma0_coe, jConjGamma0_coe, jConjSL_jConjSL]

end JConj

section CharInvolution

variable (N : ℕ) (R : Type*) [Semiring R] (A : Type*) [AddCommGroup A] [Module R A]

def charInvolution : (Additive (Gamma0 N) →+ A) →ₗ[R] (Additive (Gamma0 N) →+ A) where
  toFun ψ := ψ.comp (MonoidHom.toAdditive (jConjGamma0 N))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem charInvolution_apply (ψ : Additive (Gamma0 N) →+ A) (γ : Additive (Gamma0 N)) :
    (charInvolution N R A ψ) γ = ψ (Additive.ofMul (jConjGamma0 N (Additive.toMul γ))) := rfl

theorem charInvolution_charInvolution (ψ : Additive (Gamma0 N) →+ A) :
    charInvolution N R A (charInvolution N R A ψ) = ψ := by
  refine AddMonoidHom.ext fun γ => ?_
  show ψ (Additive.ofMul (jConjGamma0 N (jConjGamma0 N (Additive.toMul γ)))) = ψ γ
  rw [jConjGamma0_jConjGamma0]; rfl

theorem charInvolution_mem_parabolicHoms {ψ : Additive (Gamma0 N) →+ A}
    (hψ : ψ ∈ parabolicHoms R (Gamma0 N) A) :
    charInvolution N R A ψ ∈ parabolicHoms R (Gamma0 N) A := by
  rw [mem_parabolicHoms_iff] at hψ ⊢
  intro γ hγ
  refine hψ (jConjGamma0 N γ) ?_
  have htr : (((jConjGamma0 N γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace
      = (((γ : Gamma0 N) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
    rw [jConjGamma0_coe, jConjSL_coe, jConjMat_trace]
  rw [htr]; exact hγ

end CharInvolution

end ModularCurve.Period

namespace ModularCurve

section PeriodHomPair

open ModularCurve.Period

variable (N : ℕ)

def ExistsPeriodMapLinear : Prop :=
  ∃ pml : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ), ∀ f, pml f = periodMap N f

noncomputable def periodHomPair :
    (CuspForm (Gamma0 N) 2 × CuspForm (Gamma0 N) 2) →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ) :=
  open scoped Classical in
  if h : ExistsPeriodMapLinear N then
    LinearMap.coprod
      ((LinearMap.id + charInvolution N ℂ ℂ) ∘ₗ h.choose)
      ((LinearMap.id - charInvolution N ℂ ℂ) ∘ₗ h.choose)
  else 0

theorem periodHomPair_def (h : ExistsPeriodMapLinear N) :
    ∃ (pml : CuspForm (Gamma0 N) 2 →ₗ[ℂ] (Additive (Gamma0 N) →+ ℂ))
      (_ : ∀ f, pml f = periodMap N f),
      periodHomPair N = LinearMap.coprod
        ((LinearMap.id + charInvolution N ℂ ℂ) ∘ₗ pml)
        ((LinearMap.id - charInvolution N ℂ ℂ) ∘ₗ pml) := by
  refine ⟨h.choose, h.choose_spec, ?_⟩
  unfold periodHomPair
  rw [dite_eq_left h]

end PeriodHomPair

end ModularCurve
