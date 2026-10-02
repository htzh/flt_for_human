/-
X₁'s diamond operators, after FLT's `Definitions/Def_ModularCurve_X1Diamond.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1Diamond.lean>),
verbatim except for the two `diamondOneBar` declarations.

`diamondOneBar`/`diamondOneBar_apply` (pin lines 98–103) are **deferred with
`SET-X1-A`'s boundary** (recorded by the manager): they need the unported
`DistribSMul (SemilinearAut K F) (Pic0 K F)` action block
(`Def_AlgebraicCurve_BaseChangeGalois.lean:206–356`), whose decided home is
`AlgebraicCurve/Defs/SemilinearAut.lean`. They belong to the successor targets
(`heckeDiamondCommuteBar`), not to the `heckeDiamondInputsAll` cone.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1Diamond.lean
-/
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.Defs.Laurent

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve

section BaseChangeAut

variable (L : Type*) [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

/-- A `ℚ`-automorphism `σ₀` of `F₀` and a `L`-automorphism `σ` of its base change
agree coefficientwise on the image of `F₀`. -/
def IsBaseChangeAutOf (σ₀ : F₀ ≃ₐ[ℚ] F₀)
    (σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀) : Prop :=
  ∀ y : F₀,
    ((σ ⟨coeffEmb L (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L y.2⟩ :
        laurentBaseChange L F₀) : LaurentSeries L)
      = coeffEmb L ((σ₀ y : F₀) : LaurentSeries ℚ)

/-- The base change of `σ₀`, or the identity when no such base change exists. -/
def baseChangeAut (σ₀ : F₀ ≃ₐ[ℚ] F₀) :
    laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀ :=
  haveI := Classical.dec
    (∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ σ)
  if h : ∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ σ
  then h.choose else AlgEquiv.refl

variable {L}

theorem isBaseChangeAutOf_baseChangeAut {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    (h : ∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ σ) :
    IsBaseChangeAutOf L σ₀ (baseChangeAut L σ₀) := by
  rw [baseChangeAut, dite_eq_left h]
  exact h.choose_spec

theorem baseChangeAut_of_not {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    (h : ¬ ∃ σ : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀, IsBaseChangeAutOf L σ₀ σ) :
    baseChangeAut L σ₀ = AlgEquiv.refl := by
  rw [baseChangeAut, dite_eq_right h]

end BaseChangeAut

section Diamond

variable (M : ℕ)

/-- The `q`-expansion of `f ∣[k] γ`, as a Laurent series over `ℂ`. -/
def slashQExpC (k : ℤ) (f : ℍ → ℂ) (γ : SL(2, ℤ)) : LaurentSeries ℂ :=
  HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (f ∣[k] (γ : GL (Fin 2) ℝ)))

/-- The diamond automorphism of `X₁(M)` attached to `d`: it is the `ℚ`-algebra
automorphism multiplying the `q`-expansion of a ratio by the `γ`-slash with
`γ 0 0 ≡ d (mod M)`. -/
def IsDiamondAut (d : ℕ) (σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M) : Prop :=
  Nat.Coprime d M ∧
    ∀ (k : ℤ) (f g : ModularForm (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k) (pf pg : PowerSeries ℤ)
      (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
      (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
        coeffMap (algebraMap ℚ ℂ)
            ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ :
                x1FunctionField M) : LaurentSeries ℚ)
          * slashQExpC k g γ = slashQExpC k f γ

theorem IsDiamondAut.coprime {d : ℕ} {σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M}
    (h : IsDiamondAut M d σ) : Nat.Coprime d M := h.1

/-- The diamond automorphism at `d`, or the identity when none exists. -/
def diamondAut (d : ℕ) : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M :=
  haveI := Classical.dec (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ)
  if h : ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ
  then h.choose else AlgEquiv.refl

variable {M}

theorem isDiamondAut_diamondAut {d : ℕ}
    (h : ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ) :
    IsDiamondAut M d (diamondAut M d) := by
  rw [diamondAut, dite_eq_left h]
  exact h.choose_spec

theorem diamondAut_of_not {d : ℕ}
    (h : ¬ ∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ) :
    diamondAut M d = AlgEquiv.refl := by
  rw [diamondAut, dite_eq_right h]

theorem diamondAut_of_not_coprime {d : ℕ} (h : ¬ Nat.Coprime d M) :
    diamondAut M d = AlgEquiv.refl :=
  diamondAut_of_not fun ⟨_, hσ⟩ => h hσ.coprime

end Diamond

section DiamondBar

variable (M : ℕ)

/-- The base change of `diamondAut M d` to `ℚ̄`. -/
def diamondAutBar (d : ℕ) :
    x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M :=
  baseChangeAut (AlgebraicClosure ℚ) (diamondAut M d)

end DiamondBar

end ModularCurve

end
