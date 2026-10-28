/-
  The Gauss regular prolongation of the `q`-expansion valuation at `q = 0`:
  `ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC` and its two
  `_residue_div` / `_residue_mul_eq` siblings.

  Proof transcribed from FLT's
  `P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean`
  and its two siblings, which repeat the shared block verbatim (they differ only in the
  `namespace` line and a 7–8-line assembly tail).  Statements verbatim from the matching
  `Theorems/` wrappers.

  Reuse.  The pin's `Coeff` and `Gauss` blocks are already ported — stated for an arbitrary `Γ`,
  hence without the pin's `hT` — in `X1/FunctionFieldResidue.lean`
  (`ModularCurve.QExpDeuring.{ι, ϖ, IsInt, gaussRing, exists_witness, wit, wit_spec, resL,
  resHom, resHom_eq, resHom_algebraMap, algebraMap_mem_gaussRing_iff, resHom_eq_zero_iff,
  coe_algebraMap, exists_frac_form}`), together with `exists_resHom_eq`, which *is* the pin's
  `resF_surjective` argument.  The `Lam` / `homSpan` / `IsFrac` fractional-form layer (the
  pin's `Forms` block), the fourth conjunct of `exists_frac_form` (that the reduced ratio lies
  in the residue function field — the pin's only consumer of it is `resHom_mem`) and the
  `resF` assembly (`resF`, `coe_resF`, `resF_ne_zero_iff`, `ker_resF`, `resF_surjective`,
  `resF_algebraMap`, `exists_smul_mem_resF`, with `ι_mem_gaussRing`, `resHom_ι`,
  `inv_mem_gaussRing_of_resHom_ne_zero`, `coe_smul'`, `exists_smul_mem_gaussRing`,
  `resHom_mem`) have moved to **`X1/GaussResidue.lean`**, which this module now imports:
  that is the single public home for the assembly (the constant-reduction row
  `ModularCurve/ConstantReductionQExp.lean` reads it too).  This module keeps only what is
  its own: `gaussProlongation` and the three headlines.  The pin's
  `resRange` / `div_intSeriesC_mem` / `qExpFunctionFieldC_le_resRange` block is not ported.

  Not transcribed: the pin's `set_option synthInstance.maxHeartbeats 1600000` (and the
  `400000` bumps on its wrappers).  The file must close at the project's default diagnostic
  bound.

  The three files are one development: their shared block is byte-identical through line 815
  (`diff` shows only the `namespace` lines and the assembly tail), and the two siblings' tails both
  start at 816.  The port transcribes that block once, in the target file's line numbering, so a
  declaration near the end comes from either tail.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq.lean

  spec-pin: Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean
  spec-pin: Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div.lean
  spec-pin: Theorems/Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq.lean
-/
import FLTForHuman.ModularCurve.X1.GaussResidue
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.AlgebraicCurve.RegularProlongation

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped Classical MatrixGroups
open IntermediateField HahnSeries PowerSeries

namespace ModularCurve

namespace QExpDeuring

/-! ## The three assembly tails -/

section Assembly

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)
variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)

local notation "FF" => laurentBaseChange L (qExpFunctionFieldC ℚ Γ)
local notation "kk" => IsLocalRing.ResidueField A

private abbrev gaussProlongation :
    AlgebraicCurve.RegularProlongation A FF (qExpFunctionFieldC kk Γ) where
  integers := gaussRing A Γ
  residue := resF A hT
  algebraMap_mem_iff := algebraMap_mem_gaussRing_iff A Γ
  residue_surjective := resF_surjective A hT
  ker_residue := ker_resF A hT
  residue_algebraMap a := resF_algebraMap A hT a _
  exists_smul_mem := exists_smul_mem_resF A hT

private theorem mem_integers_gaussProlongation_iff (f : FF) :
    f ∈ (gaussProlongation hT A).integers ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x :=
  Iff.rfl

private theorem residue_gaussProlongation (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF) :
    ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ (gaussProlongation hT A).integers,
      (((gaussProlongation hT A).residue ⟨_, hO⟩ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) =
        coeffMap (IsLocalRing.residue A) y :=
  ⟨ι_mem_gaussRing A hy, by
    change ((resF A hT _ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) = _
    rw [coe_resF]
    exact resHom_ι A hy⟩

private theorem residue_gaussProlongation_mul (f : (gaussProlongation hT A).integers)
    (x y : LaurentSeries A) (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (h : ((f : FF) : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x) :
    (((gaussProlongation hT A).residue f : qExpFunctionFieldC kk Γ) : LaurentSeries kk) *
        coeffMap (IsLocalRing.residue A) y = coeffMap (IsLocalRing.residue A) x := by
  change ((resF A hT f : qExpFunctionFieldC kk Γ) : LaurentSeries kk) * ϖ A y = ϖ A x
  rw [coe_resF, resHom_eq A Γ (f := f) hy h, div_mul_cancel₀ _ hy]

private theorem residue_gaussProlongation_mul_eq (f : FF)
    (hf : f ∈ (gaussProlongation hT A).integers) (x y : LaurentSeries A)
    (hy : coeffMap (IsLocalRing.residue A) y ≠ 0)
    (h : (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x) :
    (((gaussProlongation hT A).residue ⟨f, hf⟩ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) *
        coeffMap (IsLocalRing.residue A) y = coeffMap (IsLocalRing.residue A) x := by
  change ((resF A hT ⟨f, hf⟩ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) * _ = _
  rw [coe_resF, resHom_eq A Γ (f := ⟨f, hf⟩) (x := x) (y := y) hy h]
  exact div_mul_cancel₀ _ hy

include hT in
private theorem main :
    ∃ R : AlgebraicCurve.RegularProlongation A FF (qExpFunctionFieldC kk Γ),
      (∀ f : FF, f ∈ R.integers ↔
        ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
          (f : LaurentSeries L) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ FF),
        ∃ hO : (⟨coeffMap A.subtype y, hy⟩ : FF) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : qExpFunctionFieldC kk Γ) : LaurentSeries kk) =
            coeffMap (IsLocalRing.residue A) y :=
  ⟨gaussProlongation hT A, mem_integers_gaussProlongation_iff hT A, residue_gaussProlongation hT A⟩

end Assembly

end QExpDeuring

/-! ## The three headlines (the `Theorems/` wrappers' statements, verbatim) -/

open QExpDeuring in
theorem exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) :
    ∃ R : AlgebraicCurve.RegularProlongation A
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      (∀ f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
        f ∈ R.integers ↔
          ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            (f : LaurentSeries L) * ModularCurve.coeffMap A.subtype y =
              ModularCurve.coeffMap A.subtype x) ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y :=
  main hT A

open QExpDeuring in
theorem exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_div
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) :
    ∃ R : AlgebraicCurve.RegularProlongation A
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      (∀ f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
        f ∈ R.integers ↔
          ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            (f : LaurentSeries L) * ModularCurve.coeffMap A.subtype y =
              ModularCurve.coeffMap A.subtype x) ∧
      (∀ (f : R.integers) (x y : LaurentSeries A),
        ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 →
        ((f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) :
            LaurentSeries L) *
            ModularCurve.coeffMap A.subtype y = ModularCurve.coeffMap A.subtype x →
        ((R.residue f : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
            LaurentSeries (IsLocalRing.ResidueField A)) *
            ModularCurve.coeffMap (IsLocalRing.residue A) y =
          ModularCurve.coeffMap (IsLocalRing.residue A) x) ∧
      ∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y :=
  ⟨gaussProlongation hT A, mem_integers_gaussProlongation_iff hT A,
    residue_gaussProlongation_mul hT A, residue_gaussProlongation hT A⟩

open QExpDeuring in
theorem exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ) :
    ∃ R : AlgebraicCurve.RegularProlongation A
        (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
      (∀ f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
        f ∈ R.integers ↔
          ∃ x y : LaurentSeries A, ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
            (f : LaurentSeries L) * ModularCurve.coeffMap A.subtype y =
              ModularCurve.coeffMap A.subtype x) ∧
      (∀ (y : LaurentSeries A)
        (hy : ModularCurve.coeffMap A.subtype y ∈
          ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)),
        ∃ hO : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ :
            ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) ∈ R.integers,
          ((R.residue ⟨_, hO⟩ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
              LaurentSeries (IsLocalRing.ResidueField A)) =
            ModularCurve.coeffMap (IsLocalRing.residue A) y) ∧
      (∀ (f : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
        (hf : f ∈ R.integers) (x y : LaurentSeries A),
        ModularCurve.coeffMap (IsLocalRing.residue A) y ≠ 0 →
        (f : LaurentSeries L) * ModularCurve.coeffMap A.subtype y = ModularCurve.coeffMap A.subtype x →
        ((R.residue ⟨f, hf⟩ : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :
            LaurentSeries (IsLocalRing.ResidueField A)) *
            ModularCurve.coeffMap (IsLocalRing.residue A) y =
          ModularCurve.coeffMap (IsLocalRing.residue A) x) :=
  ⟨gaussProlongation hT A, mem_integers_gaussProlongation_iff hT A,
    residue_gaussProlongation hT A, residue_gaussProlongation_mul_eq hT A⟩

end ModularCurve

end
