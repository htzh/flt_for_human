/-
The Hecke-row commutativity on `J₁(M)`: the `X₁` half.

`ModularCurve.heckeOperatorOneBar_comm` says the `ℓ`- and `ℓ'`-Hecke correspondences commute
on `J₁(M)`.  It is **unconditional**: every prime `ℓ`, including `ℓ ∣ M` (the `U_ℓ` case)
and `ℓ = ℓ'` (trivial).

`heckeOperatorOneBar` is the `Module.End ℤ (JOne M)` wrapper of the total operator
`heckeOperatorOneAlong` (`ModularCurve/X1/HeckeOperator.lean`), and the proof below is the pin's
`S_ModularCurve_heckeOperatorOneBar_comm.lean`: the `X_H(M)` development with the group
substituted (`CohCarrier.GammaH M H` ↦ `Gamma1 M`, no standalone `H` argument).  It is
transcribed at the pin's names and **public**, as the pin has it: these are pin-public statements,
so they keep both their names and their visibility and the statement checker diffs them all against
`S_ModularCurve_heckeOperatorOneBar_comm.lean`.  The engine is the `X_H` half
(`ModularCurve/XH/HeckeCommute.lean`, which this module imports and whose group-agnostic prelude
`XHHeckeCommute.Generic` is shared, not copied); only elaboration scaffolding here is `private`.  The `H = ⊥` reduction does not reach
this layer: the row predicates carry the *map* in a type position and `xHFunctionField M ⊥` is
only propositionally equal to `x1FunctionField M`, so the two vocabularies cannot be identified
by a bridge.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeOperatorOneBar_comm.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeOperatorOneBar_comm.lean

  spec-pin: Theorems/Thm_ModularCurve_heckeOperatorOneBar_comm.lean
  spec-pin: P2M/Sol/S_ModularCurve_heckeOperatorOneBar_comm.lean
-/
import FLTForHuman.ModularCurve.XH.HeckeCommute

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped IntermediateField MatrixGroups

namespace ModularCurve

open AlgebraicCurve CohCarrier CongruenceSubgroup HahnSeries IntermediateField

open HeckeDegree


/- The `Algebra K ↥A` goals whose carrier is a *variable* intermediate field (`Nice.*`, the
prelude's `qExpTo`/`fieldRange_val_comp_qExpTo`) are the other half of the `algebra'` bill: no
`algebra_*` brick below can name them, and `IntermediateField.algebra'`'s conclusion is
`Algebra ?R ?S` with both arguments metavariables, so it is a candidate for *every* `Algebra` goal
and re-derives `SMul`/`Mul`/`Distrib`/`Semiring` from scratch (~250 ms) at each occurrence.  One
keyed instance (`Algebra K ↥?A`, key `Subtype`) answers all of them, in both halves. -/
private instance algebra_subtype {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : IntermediateField K L) : Algebra K ↥A := inferInstance

/-- The `[Semiring ↥A]` argument of every such goal is a search of its own (~25 ms: the derivation
runs `SubfieldClass`/`SubringClass`/`Subring` down to the ambient ring) and it is paid once per
*occurrence* of a carrier, so it gets the same treatment. -/
private instance semiring_subtype {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : IntermediateField K L) : Semiring ↥A := inferInstance

/-- `Algebra ℚ (LaurentSeries ℚ)` is a search of its own (~68 ms: `DivisionRing.toRatAlgebra` over
the Hahn-series fraction field) and the four `intFormRatiosC ℚ _` proofs (`qExpand_KK_subset`,
`qExpand_KT_subset`, `betaHDefined_input`) ask for it several times each, in both halves. -/
private instance algebra_laurent_rat : Algebra ℚ (LaurentSeries ℚ) := inferInstance

/-! ## The `X₁` transcription

The pin's `S_ModularCurve_heckeOperatorOneBar_comm.lean` at the pin's names and its visibility:
the `Γ₁` fields, `Nice`, the legs and the divisor-level square are public (the pin states them
publicly and the checker diffs them), the headline is at the bottom. -/

namespace X1HeckeCommute

open XHHeckeCommute.Generic

open scoped XHHeckeCommute.Generic

section Groups

variable (M : ℕ)

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

theorem T_mem_Gamma1_inf_Gamma0 (t : ℕ) : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 t := by
  have hT0 : ModularGroup.T ∈ Gamma0 t := by
    rw [Gamma0_mem]
    simp [ModularGroup.T]
  exact Subgroup.mem_inf.mpr ⟨T_mem_Gamma1 M, hT0⟩

scoped instance finiteIndex_Gamma1_inf_Gamma0 [NeZero M] (t : ℕ) [NeZero t] :
    (Gamma1 M ⊓ Gamma0 t).FiniteIndex := by
  infer_instance

theorem cocycle_inf {s ℓ t : ℕ} [NeZero ℓ] (hs : M ∣ s) (ht : t = s * ℓ) :
    ∀ γ ∈ Gamma1 M ⊓ Gamma0 t, ∃ γ₁ ∈ Gamma1 M ⊓ Gamma0 s,
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨hγ1, hγ0⟩ := Subgroup.mem_inf.mp hγ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have htc : ((t : ℕ) : ℤ) ∣ γ 1 0 := by
    have := Gamma0_mem.mp hγ0; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨c', hc'⟩ := htc
  rw [ht, Nat.cast_mul] at hc'
  have hdet' : Matrix.det !![(γ 0 0 : ℤ), (ℓ : ℤ) * γ 0 1; (s : ℤ) * c', γ 1 1] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet + (γ 0 1 : ℤ) * hc'
  obtain ⟨m, hm⟩ := hs
  refine ⟨⟨_, hdet'⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Gamma1_mem] at hγ1
      obtain ⟨h00, h11, -⟩ := hγ1
      refine (Gamma1_mem M _).mpr ⟨h00, h11, ?_⟩
      show (((s : ℤ) * c' : ℤ) : ZMod M) = 0
      rw [hm]; push_cast; rw [ZMod.natCast_self, zero_mul, zero_mul]
    · refine Gamma0_mem.mpr ?_
      show (((s : ℤ) * c' : ℤ) : ZMod s) = 0
      push_cast; rw [ZMod.natCast_self, zero_mul]
  · rfl
  · rfl
  · show (ℓ : ℤ) * ((s : ℤ) * c') = γ 1 0
    linear_combination -hc'
  · rfl

theorem cocycle_one (ℓ : ℕ) [NeZero ℓ] : ∀ γ ∈ Gamma1 M ⊓ Gamma0 (M * ℓ), ∃ γ₁ ∈ Gamma1 M,
    γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (ℓ : ℤ) * γ 0 1 ∧ (ℓ : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨γ₁, hγ₁, h⟩ := cocycle_inf M (s := M) (ℓ := ℓ) (t := M * ℓ) dvd_rfl rfl γ hγ
  exact ⟨γ₁, (Subgroup.mem_inf.mp hγ₁).1, h⟩

end Groups

section Fields

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M]

abbrev KK : IntermediateField L (LaurentSeries L) := laurentBaseChange L (x1FunctionField M)

abbrev KT (t : ℕ) : IntermediateField L (LaurentSeries L) :=
  laurentBaseChange L (x1x0FunctionFieldC ℚ M t)

theorem KK_le_KT (t : ℕ) : KK L M ≤ KT L M t :=
  laurentBaseChange_mono L (x1FunctionFieldC_le_x1x0 ℚ M t)

theorem KT_mono {s t : ℕ} (h : s ∣ t) : KT L M s ≤ KT L M t :=
  laurentBaseChange_mono L (qExpFunctionFieldC_mono ℚ (inf_le_inf_left _ (Gamma0_le_of_dvd h)))

theorem qExpand_KK_subset (ℓ : ℕ) [NeZero ℓ] :
    qExpand L ℓ '' (KK L M : Set (LaurentSeries L)) ⊆ KT L M (M * ℓ) := by
  rintro _ ⟨x, hx, rfl⟩
  refine qExpand_mem_laurentBaseChange ℓ (fun y hy => ?_) hx
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ (T_mem_Gamma1 M) ℓ
    (cocycle_one M ℓ)
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M))).map (qExpandₐ ℓ)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 (M * ℓ))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy, rfl⟩

theorem qExpand_KT_subset {s ℓ t : ℕ} [NeZero s] [NeZero ℓ] (hs : M ∣ s) (ht : t = s * ℓ) :
    qExpand L ℓ '' (KT L M s : Set (LaurentSeries L)) ⊆ KT L M t := by
  rintro _ ⟨x, hx, rfl⟩
  refine qExpand_mem_laurentBaseChange ℓ (fun y hy => ?_) hx
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ (T_mem_Gamma1_inf_Gamma0 M s) ℓ
    (cocycle_inf M hs ht)
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 s))).map (qExpandₐ ℓ)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 t)) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy, rfl⟩

theorem heckeBetaOneDefined (ℓ : ℕ) [NeZero ℓ] : HeckeBetaOneDefined M ℓ := by
  intro y hy
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset ℚ (T_mem_Gamma1 M) ℓ (cocycle_one M ℓ)
  have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M)) := hy
  have hmap : (IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M))).map (qExpandₐ ℓ)
      ≤ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M ⊓ Gamma0 (M * ℓ))) := by
    rw [IntermediateField.adjoin_map]
    exact IntermediateField.adjoin.mono ℚ _ _ hsub
  exact hmap ⟨y, hy', rfl⟩

theorem exists_transcendental_KK : ∃ x₀ : LaurentSeries L, x₀ ∈ KK L M ∧ Transcendental L x₀ := by
  obtain ⟨x, hx, -⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L (Gamma1 M)
      (T_mem_Gamma1 M)
  refine ⟨x, x.2, ?_⟩
  exact (transcendental_algebraMap_iff (R := L) (A := LaurentSeries L)
    (algebraMap (KK L M) (LaurentSeries L)).injective).mpr hx

theorem finiteDimensional_KT (t : ℕ) [NeZero t] {y : KT L M t} (hy : Transcendental L y) :
    FiniteDimensional L⟮y⟯ (KT L M t) := by
  obtain ⟨x, hx, hfin⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
      (Gamma1 M ⊓ Gamma0 t) (T_mem_Gamma1_inf_Gamma0 M t)
  exact XHHeckeCommute.Generic.finiteDimensional_adjoin_of_transcendental' (x := x) hx hfin hy

end Fields

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

abbrev QQ : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L (qExpand L ℓ '' (KK L M : Set (LaurentSeries L)))

abbrev roof : IntermediateField L (LaurentSeries L) :=
  KT L M (M * ℓ) ⊔ IntermediateField.adjoin L (qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L)))

abbrev BB : IntermediateField L (LaurentSeries L) := KT L M (M * ℓ * ℓ')

-- See the `algebra_*` bricks in the `X_H` half: the same unkeyed `Algebra L ↥A` derivation,
-- named once so every later occurrence is an assumption lookup.
private instance algebra_KK : Algebra L ↥(KK L M) := inferInstance

private instance algebra_KT : Algebra L ↥(KT L M (M * ℓ)) := inferInstance

private instance algebra_KT' : Algebra L ↥(KT L M (M * ℓ')) := inferInstance

theorem KT_le_roof : KT L M (M * ℓ) ≤ roof L M ℓ ℓ' := le_sup_left

theorem qExpand_KT_subset_roof :
    qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L)) ⊆ roof L M ℓ ℓ' :=
  (IntermediateField.subset_adjoin L _).trans (SetLike.coe_subset_coe.mpr le_sup_right)

private instance algebra_QQ : Algebra L ↥(QQ L M ℓ) := inferInstance

private instance algebra_roof : Algebra L ↥(roof L M ℓ ℓ') := inferInstance

private instance algebra_BB : Algebra L ↥(BB L M ℓ ℓ') := inferInstance

theorem KK_le_roof : KK L M ≤ roof L M ℓ ℓ' := (KK_le_KT L M _).trans (KT_le_roof L M ℓ ℓ')

theorem QQ_le_KT : QQ L M ℓ ≤ KT L M (M * ℓ) :=
  IntermediateField.adjoin_le_iff.mpr (qExpand_KK_subset L M ℓ)

theorem QQ_le_roof : QQ L M ℓ ≤ roof L M ℓ ℓ' := (QQ_le_KT L M ℓ).trans (KT_le_roof L M ℓ ℓ')

theorem roof_le_BB : roof L M ℓ ℓ' ≤ BB L M ℓ ℓ' := by
  refine sup_le (KT_mono L M ⟨ℓ', rfl⟩) (IntermediateField.adjoin_le_iff.mpr ?_)
  exact qExpand_KT_subset L M (s := M * ℓ') (ℓ := ℓ) (t := M * ℓ * ℓ') ⟨ℓ', rfl⟩ (by ring)

theorem KK_le_BB : KK L M ≤ BB L M ℓ ℓ' := (KK_le_roof L M ℓ ℓ').trans (roof_le_BB L M ℓ ℓ')

structure Nice (A : IntermediateField L (LaurentSeries L)) : Prop where
  le : A ≤ BB L M ℓ ℓ'
  tr : ∃ y ∈ A, Transcendental L y

variable {L M ℓ ℓ'}

theorem Nice.klShape {A : IntermediateField L (LaurentSeries L)} (hA : Nice L M ℓ ℓ' A)
    {y : LaurentSeries L} (hyA : y ∈ A) (hy : Transcendental L y) :
    FiniteDimensional L⟮(⟨y, hyA⟩ : A)⟯ A := by
  have hyB : y ∈ BB L M ℓ ℓ' := hA.le hyA
  have hfin : FiniteDimensional L⟮(⟨y, hyB⟩ : BB L M ℓ ℓ')⟯ (BB L M ℓ ℓ') :=
    finiteDimensional_KT L M (M * ℓ * ℓ') ((transcendental_coe_iff L (A := BB L M ℓ ℓ') ⟨y, hyB⟩).mp hy)
  exact finiteDimensional_adjoin_of_le hA.le hyA hfin

theorem Nice.hasPrincipalDivisors {A : IntermediateField L (LaurentSeries L)} (hA : Nice L M ℓ ℓ' A) :
    HasPrincipalDivisors L A := by
  haveI : CharZero L := charZero_base L
  obtain ⟨y, hyA, hy⟩ := hA.tr
  haveI := hA.klShape hyA hy
  exact AlgebraicCurve.hasPrincipalDivisors_of_transcendental L (⟨y, hyA⟩ : A)
    ((transcendental_coe_iff L (A := A) ⟨y, hyA⟩).mp hy)

theorem Nice.finiteAlong {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M ℓ ℓ' A)
    (hA' : Nice L M ℓ ℓ' A') (φ : A →ₐ[L] A') : FiniteAlong L φ := by
  obtain ⟨y, hyA, hy⟩ := hA.tr
  obtain ⟨y', hyA', hy'⟩ := hA'.tr
  haveI := hA'.klShape hyA' hy'
  exact finiteAlong_of_transcendental φ ((transcendental_coe_iff L (A := A) ⟨y, hyA⟩).mp hy)
    ((transcendental_coe_iff L (A := A') ⟨y', hyA'⟩).mp hy')

theorem Nice.isIntegral {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M ℓ ℓ' A)
    (hA' : Nice L M ℓ ℓ' A') (φ : A →ₐ[L] A') : φ.toRingHom.IsIntegral :=
  isIntegral_of_finiteAlong φ (hA.finiteAlong hA' φ)

theorem Nice.separableAlong {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M ℓ ℓ' A)
    (hA' : Nice L M ℓ ℓ' A') (φ : A →ₐ[L] A') : SeparableAlong L φ :=
  AlgebraicCurve.separableAlong_of_charZero φ (hA.isIntegral hA' φ)

theorem Nice.finrankAlong_ne_zero {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M ℓ ℓ' A)
    (hA' : Nice L M ℓ ℓ' A') (φ : A →ₐ[L] A') : finrankAlong L φ ≠ 0 :=
  (finrankAlong_pos_of_finiteAlong φ (hA.finiteAlong hA' φ)).ne'

theorem Nice.relfinrank_ne_zero {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M ℓ ℓ' A)
    (hA' : Nice L M ℓ ℓ' A') (h : A ≤ A') : IntermediateField.relfinrank A A' ≠ 0 := by
  rw [← finrankAlong_inclusion h]
  exact hA.finrankAlong_ne_zero hA' _

theorem Nice.mono {A A' : IntermediateField L (LaurentSeries L)} (hA : Nice L M ℓ ℓ' A)
    (h : A ≤ A') (h' : A' ≤ BB L M ℓ ℓ') : Nice L M ℓ ℓ' A' :=
  ⟨h', let ⟨y, hyA, hy⟩ := hA.tr; ⟨y, h hyA, hy⟩⟩

variable (L M ℓ ℓ')

theorem nice_KK : Nice L M ℓ ℓ' (KK L M) :=
  ⟨KK_le_BB L M ℓ ℓ', exists_transcendental_KK L M⟩

theorem nice_KT : Nice L M ℓ ℓ' (KT L M (M * ℓ)) :=
  (nice_KK L M ℓ ℓ').mono (KK_le_KT L M _) ((KT_le_roof L M ℓ ℓ').trans (roof_le_BB L M ℓ ℓ'))

theorem nice_KT' : Nice L M ℓ ℓ' (KT L M (M * ℓ')) :=
  (nice_KK L M ℓ ℓ').mono (KK_le_KT L M _) (KT_mono L M ⟨ℓ, by ring⟩)

theorem nice_QQ : Nice L M ℓ ℓ' (QQ L M ℓ) := by
  refine ⟨(QQ_le_roof L M ℓ ℓ').trans (roof_le_BB L M ℓ ℓ'), ?_⟩
  obtain ⟨y, hy, htr⟩ := exists_transcendental_KK L M
  exact ⟨qExpand L ℓ y, IntermediateField.subset_adjoin L _ ⟨y, hy, rfl⟩, transcendental_qExpand L htr ℓ⟩

theorem nice_roof : Nice L M ℓ ℓ' (roof L M ℓ ℓ') :=
  (nice_KK L M ℓ ℓ').mono (KK_le_roof L M ℓ ℓ') (roof_le_BB L M ℓ ℓ')

theorem nice_BB : Nice L M ℓ ℓ' (BB L M ℓ ℓ') :=
  (nice_KK L M ℓ ℓ').mono (KK_le_BB L M ℓ ℓ') le_rfl

theorem nice_symm {A : IntermediateField L (LaurentSeries L)} (hA : Nice L M ℓ' ℓ A) : Nice L M ℓ ℓ' A := by
  refine ⟨hA.le.trans ?_, hA.tr⟩
  exact KT_mono L M ⟨1, by ring⟩

abbrev legU : KT L M (M * ℓ) →ₐ[L] roof L M ℓ ℓ' := IntermediateField.inclusion (KT_le_roof L M ℓ ℓ')

abbrev legU' : KT L M (M * ℓ') →ₐ[L] roof L M ℓ ℓ' :=
  qExpTo ℓ (KT L M (M * ℓ')) (roof L M ℓ ℓ') (qExpand_KT_subset_roof L M ℓ ℓ')

theorem coe_legU (y : KT L M (M * ℓ)) : (legU L M ℓ ℓ' y : LaurentSeries L) = y :=
  IntermediateField.coe_inclusion _ y

theorem coe_legU' (y : KT L M (M * ℓ')) : (legU' L M ℓ ℓ' y : LaurentSeries L) = qExpand L ℓ y :=
  coe_qExpTo ℓ _ y

theorem mem_algebraAdjoin_iff (x : LaurentSeries L) :
    x ∈ Algebra.adjoin L ((KT L M (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L))) ↔
      x ∈ Algebra.adjoin (KT L M (M * ℓ)) (qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L))) := by
  constructor
  · intro hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
        rcases hy with hy | hy
        · exact Subalgebra.algebraMap_mem
            (Algebra.adjoin (KT L M (M * ℓ)) (qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L))))
            (⟨y, hy⟩ : KT L M (M * ℓ))
        · exact Algebra.subset_adjoin hy
    | algebraMap r =>
        have : algebraMap L (LaurentSeries L) r
            = algebraMap (KT L M (M * ℓ)) (LaurentSeries L) (algebraMap L (KT L M (M * ℓ)) r) :=
          (IsScalarTower.algebraMap_apply L (KT L M (M * ℓ)) (LaurentSeries L) r)
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  · intro hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin (Or.inr hy)
    | algebraMap r => exact Algebra.subset_adjoin (Or.inl r.2)
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz

theorem isAlgebraic_of_mem_BB {x : LaurentSeries L} (hx : x ∈ BB L M ℓ ℓ') :
    IsAlgebraic (KT L M (M * ℓ)) x := by
  have hle : KT L M (M * ℓ) ≤ BB L M ℓ ℓ' := (KT_le_roof L M ℓ ℓ').trans (roof_le_BB L M ℓ ℓ')
  let φ : KT L M (M * ℓ) →ₐ[L] BB L M ℓ ℓ' := IntermediateField.inclusion hle
  have hint : φ.toRingHom.IsIntegral := (nice_KT L M ℓ ℓ').isIntegral (nice_BB L M ℓ ℓ') φ
  obtain ⟨p, hp, hpx⟩ := hint ⟨x, hx⟩
  refine IsIntegral.isAlgebraic ⟨p, hp, ?_⟩
  have h := Polynomial.hom_eval₂ p φ.toRingHom (BB L M ℓ ℓ').val.toRingHom ⟨x, hx⟩
  rw [hpx, map_zero] at h
  have hcomp : (BB L M ℓ ℓ').val.toRingHom.comp φ.toRingHom
      = algebraMap (KT L M (M * ℓ)) (LaurentSeries L) := RingHom.ext fun c => rfl
  rw [hcomp] at h
  exact h.symm

theorem inv_mem_algebraAdjoin {x : LaurentSeries L}
    (hx : x ∈ Algebra.adjoin L ((KT L M (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L)))) :
    x⁻¹ ∈ Algebra.adjoin L ((KT L M (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L))) := by
  have hx' := (mem_algebraAdjoin_iff L M ℓ ℓ' x).mp hx
  have hxB : x ∈ BB L M ℓ ℓ' := by
    have hle : Algebra.adjoin L ((KT L M (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L))) ≤ (roof L M ℓ ℓ').toSubalgebra :=
      Algebra.adjoin_le (Set.union_subset (KT_le_roof L M ℓ ℓ') (qExpand_KT_subset_roof L M ℓ ℓ'))
    exact roof_le_BB L M ℓ ℓ' (hle hx)
  have halg := isAlgebraic_of_mem_BB L M ℓ ℓ' hxB
  have h := Subalgebra.inv_mem_of_algebraic
    (Algebra.adjoin (KT L M (M * ℓ)) (qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L))))
    (x := ⟨x, hx'⟩) halg
  exact (mem_algebraAdjoin_iff L M ℓ ℓ' x⁻¹).mpr h

theorem roof_toSubalgebra :
    (roof L M ℓ ℓ').toSubalgebra = Algebra.adjoin L ((KT L M (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L))) := by
  have h : roof L M ℓ ℓ' = IntermediateField.adjoin L ((KT L M (M * ℓ) : Set (LaurentSeries L)) ∪
      qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L))) := by
    rw [IntermediateField.adjoin_union, IntermediateField.adjoin_self]
  rw [h]
  exact IntermediateField.adjoin_eq_algebra_adjoin L _ (fun x hx => inv_mem_algebraAdjoin L M ℓ ℓ' hx)

theorem hgen : Algebra.adjoin L (Set.range (legU' L M ℓ ℓ') ∪ Set.range (legU L M ℓ ℓ')) = ⊤ := by
  have hle : Algebra.adjoin L ((KT L M (M * ℓ) : Set (LaurentSeries L)) ∪
        qExpand L ℓ '' (KT L M (M * ℓ') : Set (LaurentSeries L)))
      ≤ (Algebra.adjoin L (Set.range (legU' L M ℓ ℓ') ∪ Set.range (legU L M ℓ ℓ'))).map
          (roof L M ℓ ℓ').val := by
    refine Algebra.adjoin_le ?_
    rintro y (hy | ⟨a, ha, rfl⟩)
    · exact ⟨legU L M ℓ ℓ' ⟨y, hy⟩, Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩), rfl⟩
    · exact ⟨legU' L M ℓ ℓ' ⟨a, ha⟩, Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩), rfl⟩
  refine eq_top_iff.mpr fun z _ => ?_
  have hz : (z : LaurentSeries L) ∈ (roof L M ℓ ℓ').toSubalgebra := z.2
  rw [roof_toSubalgebra] at hz
  obtain ⟨w, hw, hwz⟩ := Subalgebra.mem_map.mp (hle hz)
  have hwz' : w = z := Subtype.ext hwz
  exact hwz' ▸ hw

theorem QQ_eq_map : QQ L M ℓ = (KK L M).map (qExpAlgHom L ℓ) := by
  have h := IntermediateField.adjoin_map L ((KK L M : Set (LaurentSeries L))) (qExpAlgHom L ℓ)
  rw [IntermediateField.adjoin_self] at h
  exact h.symm

theorem finrankAlong_beta (h0 : HeckeBetaOneDefined M ℓ) :
    finrankAlong L (heckeBetaOneBar L M ℓ) = IntermediateField.relfinrank (QQ L M ℓ) (KT L M (M * ℓ)) := by
  refine (AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange (KK L M) (KT L M (M * ℓ))
    (heckeBetaOneBar L M ℓ)).trans ?_
  congr 1
  rw [QQ_eq_map]
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, a.2, ?_⟩
    show qExpand L ℓ a = (heckeBetaOneBar L M ℓ a : LaurentSeries L)
    rw [coe_heckeBetaOneBar M ℓ h0]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    show ((heckeBetaOneBar L M ℓ ⟨a, ha⟩ : KT L M (M * ℓ)) : LaurentSeries L) = qExpand L ℓ a
    rw [coe_heckeBetaOneBar M ℓ h0]

theorem finrankAlong_alpha :
    finrankAlong L (heckeAlphaOneBar L M ℓ') = IntermediateField.relfinrank (KK L M) (KT L M (M * ℓ')) :=
  finrankAlong_inclusion (KK_le_KT L M _)

theorem coe_legU'_alpha (a : KK L M) :
    (((legU' L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ')) a : LaurentSeries L) = qExpand L ℓ a := by
  rw [AlgHom.comp_apply, coe_legU', coe_heckeAlphaOneBar]

theorem finrankAlong_diag :
    finrankAlong L ((legU' L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ'))
      = IntermediateField.relfinrank (QQ L M ℓ) (roof L M ℓ ℓ') := by
  refine (AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange (KK L M) (roof L M ℓ ℓ')
    ((legU' L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ'))).trans ?_
  congr 1
  rw [QQ_eq_map]
  ext x
  rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, a.2, ?_⟩
    show qExpand L ℓ a = (((legU' L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ')) a : LaurentSeries L)
    rw [coe_legU'_alpha]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha⟩, ?_⟩
    show (((legU' L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ')) ⟨a, ha⟩ : LaurentSeries L) = qExpand L ℓ a
    rw [coe_legU'_alpha]

theorem hLD (hcop : Nat.Coprime ℓ ℓ') (h0 : HeckeBetaOneDefined M ℓ) :
    finrankAlong L ((legU' L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ'))
      = finrankAlong L (heckeAlphaOneBar L M ℓ') * finrankAlong L (heckeBetaOneBar L M ℓ) := by
  rw [finrankAlong_diag, finrankAlong_alpha, finrankAlong_beta L M ℓ h0]
  exact ModularCurve.relfinrank_x1HeckeCompositum_eq_mul L M ℓ ℓ' hcop

theorem relfinrank_KK_roof (hcop : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank (KK L M) (roof L M ℓ ℓ')
      = IntermediateField.relfinrank (KK L M) (KT L M (M * ℓ))
        * IntermediateField.relfinrank (KK L M) (KT L M (M * ℓ')) := by
  have t1 := IntermediateField.relfinrank_mul_relfinrank (KK_le_KT L M (M * ℓ)) (KT_le_roof L M ℓ ℓ')
  have t2 := IntermediateField.relfinrank_mul_relfinrank (QQ_le_KT L M ℓ) (KT_le_roof L M ℓ ℓ')
  have hLD := ModularCurve.relfinrank_x1HeckeCompositum_eq_mul L M ℓ ℓ' hcop
  have hne : IntermediateField.relfinrank (QQ L M ℓ) (KT L M (M * ℓ)) ≠ 0 :=
    (nice_QQ L M ℓ ℓ').relfinrank_ne_zero (nice_KT L M ℓ ℓ') (QQ_le_KT L M ℓ)
  have key : IntermediateField.relfinrank (KT L M (M * ℓ)) (roof L M ℓ ℓ')
      = IntermediateField.relfinrank (KK L M) (KT L M (M * ℓ')) := by
    apply mul_left_cancel₀ hne
    rw [t2, hLD, mul_comm]
  rw [← t1, key]

theorem hsq (h0 : HeckeBetaOneDefined M ℓ) :
    (legU L M ℓ ℓ').comp (heckeBetaOneBar L M ℓ) = (legU' L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ') := by
  refine AlgHom.ext fun x => Subtype.ext ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_legU, coe_legU',
    coe_heckeBetaOneBar M ℓ h0, coe_heckeAlphaOneBar]

theorem exchange (hcop : Nat.Coprime ℓ ℓ') (h0 : HeckeBetaOneDefined M ℓ)
    [HasPrincipalDivisors L (KT L M (M * ℓ))] [HasPrincipalDivisors L (roof L M ℓ ℓ')]
    (hβ : (heckeBetaOneBar L M ℓ).toRingHom.IsIntegral)
    (hα' : (heckeAlphaOneBar L M ℓ').toRingHom.IsIntegral)
    (hu : (legU L M ℓ ℓ').toRingHom.IsIntegral) (hu' : (legU' L M ℓ ℓ').toRingHom.IsIntegral)
    (D : Divisor L (KT L M (M * ℓ'))) :
    Divisor.pullbackAlong (heckeBetaOneBar L M ℓ) hβ (Divisor.pushforwardAlong (heckeAlphaOneBar L M ℓ') hα' D)
      = Divisor.pushforwardAlong (legU L M ℓ ℓ') hu (Divisor.pullbackAlong (legU' L M ℓ ℓ') hu' D) := by
  have hfin : FiniteAlong L ((legU' L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ')) :=
    (nice_KK L M ℓ ℓ').finiteAlong (nice_roof L M ℓ ℓ') _
  have hsep : SeparableAlong L ((legU' L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ')) :=
    (nice_KK L M ℓ ℓ').separableAlong (nice_roof L M ℓ ℓ') _
  exact Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    (heckeAlphaOneBar L M ℓ') (heckeBetaOneBar L M ℓ) (legU' L M ℓ ℓ') (legU L M ℓ ℓ')
    hα' hβ hu' hu (hsq L M ℓ ℓ' h0) hfin hsep (hgen L M ℓ ℓ') (hLD L M ℓ ℓ' hcop h0) D

abbrev legP : KK L M →ₐ[L] roof L M ℓ ℓ' := (legU' L M ℓ ℓ').comp (heckeBetaOneBar L M ℓ')

abbrev legI : KK L M →ₐ[L] roof L M ℓ ℓ' := (legU L M ℓ ℓ').comp (heckeAlphaOneBar L M ℓ)

theorem coe_legP (h0' : HeckeBetaOneDefined M ℓ') (x : KK L M) :
    (legP L M ℓ ℓ' x : LaurentSeries L) = qExpand L (ℓ * ℓ') x := by
  rw [AlgHom.comp_apply, coe_legU', coe_heckeBetaOneBar M ℓ' h0', qExpand_qExpand]

theorem coe_legI (x : KK L M) : (legI L M ℓ ℓ' x : LaurentSeries L) = x := by
  rw [AlgHom.comp_apply, coe_legU, coe_heckeAlphaOneBar]

theorem heckeDiv_heckeDiv (hcop : Nat.Coprime ℓ ℓ') (h0 : HeckeBetaOneDefined M ℓ)
    [HasPrincipalDivisors L (KT L M (M * ℓ))] [HasPrincipalDivisors L (KT L M (M * ℓ'))]
    [HasPrincipalDivisors L (roof L M ℓ ℓ')]
    (hα : (heckeAlphaOneBar L M ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaOneBar L M ℓ).toRingHom.IsIntegral)
    (hα' : (heckeAlphaOneBar L M ℓ').toRingHom.IsIntegral) (hβ' : (heckeBetaOneBar L M ℓ').toRingHom.IsIntegral)
    (hP : (legP L M ℓ ℓ').toRingHom.IsIntegral) (hI : (legI L M ℓ ℓ').toRingHom.IsIntegral)
    (D : Divisor L (KK L M)) :
    Divisor.correspondence (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) hβ hα
        (Divisor.correspondence (heckeBetaOneBar L M ℓ') (heckeAlphaOneBar L M ℓ') hβ' hα' D)
      = Divisor.correspondence (legP L M ℓ ℓ') (legI L M ℓ ℓ') hP hI D := by
  have hu : (legU L M ℓ ℓ').toRingHom.IsIntegral := (nice_KT L M ℓ ℓ').isIntegral (nice_roof L M ℓ ℓ') _
  have hu' : (legU' L M ℓ ℓ').toRingHom.IsIntegral := (nice_KT' L M ℓ ℓ').isIntegral (nice_roof L M ℓ ℓ') _
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply, Divisor.correspondence_apply,
    exchange L M ℓ ℓ' hcop h0 hβ hα' hu hu',
    Divisor.pushforwardAlong_pushforwardAlong (heckeAlphaOneBar L M ℓ) (legU L M ℓ ℓ') hα hu hI,
    Divisor.pullbackAlong_pullbackAlong (heckeBetaOneBar L M ℓ') (legU' L M ℓ ℓ') hβ' hu' hP]

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

abbrev RR : IntermediateField L (LaurentSeries L) := roof L M ℓ ℓ' ⊔ roof L M ℓ' ℓ

theorem roof_le_RR : roof L M ℓ ℓ' ≤ RR L M ℓ ℓ' := le_sup_left

theorem roof'_le_RR : roof L M ℓ' ℓ ≤ RR L M ℓ ℓ' := le_sup_right

abbrev legJ : roof L M ℓ ℓ' →ₐ[L] RR L M ℓ ℓ' := IntermediateField.inclusion (roof_le_RR L M ℓ ℓ')

abbrev legJ' : roof L M ℓ' ℓ →ₐ[L] RR L M ℓ ℓ' := IntermediateField.inclusion (roof'_le_RR L M ℓ ℓ')

theorem coe_legJ (y : roof L M ℓ ℓ') : (legJ L M ℓ ℓ' y : LaurentSeries L) = y :=
  IntermediateField.coe_inclusion _ y

theorem coe_legJ' (y : roof L M ℓ' ℓ) : (legJ' L M ℓ ℓ' y : LaurentSeries L) = y :=
  IntermediateField.coe_inclusion _ y

theorem nice_RR : Nice L M ℓ ℓ' (RR L M ℓ ℓ') :=
  (nice_roof L M ℓ ℓ').mono (roof_le_RR L M ℓ ℓ')
    (sup_le (roof_le_BB L M ℓ ℓ') ((nice_symm L M ℓ ℓ' (nice_roof L M ℓ' ℓ)).le))

theorem heckeDiv_comm (hcop : Nat.Coprime ℓ ℓ')
    [HasPrincipalDivisors L (KT L M (M * ℓ))] [HasPrincipalDivisors L (KT L M (M * ℓ'))]
    (hα : (heckeAlphaOneBar L M ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaOneBar L M ℓ).toRingHom.IsIntegral)
    (hα' : (heckeAlphaOneBar L M ℓ').toRingHom.IsIntegral) (hβ' : (heckeBetaOneBar L M ℓ').toRingHom.IsIntegral)
    (D : Divisor L (KK L M)) :
    Divisor.correspondence (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) hβ hα
        (Divisor.correspondence (heckeBetaOneBar L M ℓ') (heckeAlphaOneBar L M ℓ') hβ' hα' D)
      = Divisor.correspondence (heckeBetaOneBar L M ℓ') (heckeAlphaOneBar L M ℓ') hβ' hα'
        (Divisor.correspondence (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) hβ hα D) := by
  have h0 : HeckeBetaOneDefined M ℓ := heckeBetaOneDefined M ℓ
  have h0' : HeckeBetaOneDefined M ℓ' := heckeBetaOneDefined M ℓ'

  haveI : HasPrincipalDivisors L (roof L M ℓ ℓ') := (nice_roof L M ℓ ℓ').hasPrincipalDivisors
  haveI : HasPrincipalDivisors L (roof L M ℓ' ℓ) := (nice_roof L M ℓ' ℓ).hasPrincipalDivisors
  haveI : HasPrincipalDivisors L (RR L M ℓ ℓ') := (nice_RR L M ℓ ℓ').hasPrincipalDivisors
  have nK := nice_KK L M ℓ ℓ'
  have nR := nice_roof L M ℓ ℓ'
  have nR' : Nice L M ℓ ℓ' (roof L M ℓ' ℓ) := nice_symm L M ℓ ℓ' (nice_roof L M ℓ' ℓ)
  have nRR := nice_RR L M ℓ ℓ'
  have hP := nK.isIntegral nR (legP L M ℓ ℓ')
  have hI := nK.isIntegral nR (legI L M ℓ ℓ')
  have hP' := nK.isIntegral nR' (legP L M ℓ' ℓ)
  have hI' := nK.isIntegral nR' (legI L M ℓ' ℓ)

  rw [heckeDiv_heckeDiv L M ℓ ℓ' hcop h0 hα hβ hα' hβ' hP hI D,
    heckeDiv_heckeDiv L M ℓ' ℓ hcop.symm h0' hα' hβ' hα hβ hP' hI' D]

  have hj := nR.isIntegral nRR (legJ L M ℓ ℓ')
  have hj' := nR'.isIntegral nRR (legJ' L M ℓ ℓ')
  have hjP := nK.isIntegral nRR ((legJ L M ℓ ℓ').comp (legP L M ℓ ℓ'))
  have hjI := nK.isIntegral nRR ((legJ L M ℓ ℓ').comp (legI L M ℓ ℓ'))
  have hjP' := nK.isIntegral nRR ((legJ' L M ℓ ℓ').comp (legP L M ℓ' ℓ))
  have hjI' := nK.isIntegral nRR ((legJ' L M ℓ ℓ').comp (legI L M ℓ' ℓ))
  have e1 := correspondence_comp_eq_smul (legP L M ℓ ℓ') (legI L M ℓ ℓ') (legJ L M ℓ ℓ') hP hI hj hjP hjI
    (nR.finiteAlong nRR _) (nR.separableAlong nRR _) D
  have e2 := correspondence_comp_eq_smul (legP L M ℓ' ℓ) (legI L M ℓ' ℓ) (legJ' L M ℓ ℓ') hP' hI' hj' hjP' hjI'
    (nR'.finiteAlong nRR _) (nR'.separableAlong nRR _) D

  have hPeq : (legJ L M ℓ ℓ').comp (legP L M ℓ ℓ') = (legJ' L M ℓ ℓ').comp (legP L M ℓ' ℓ) := by
    refine AlgHom.ext fun x => Subtype.ext ?_
    rw [AlgHom.comp_apply (legJ L M ℓ ℓ') (legP L M ℓ ℓ') x,
      AlgHom.comp_apply (legJ' L M ℓ ℓ') (legP L M ℓ' ℓ) x, coe_legJ, coe_legJ', coe_legP L M ℓ ℓ' h0',
      coe_legP L M ℓ' ℓ h0, qExpand_congr (Nat.mul_comm ℓ ℓ')]
  have hIeq : (legJ L M ℓ ℓ').comp (legI L M ℓ ℓ') = (legJ' L M ℓ ℓ').comp (legI L M ℓ' ℓ) := by
    refine AlgHom.ext fun x => Subtype.ext ?_
    rw [AlgHom.comp_apply (legJ L M ℓ ℓ') (legI L M ℓ ℓ') x,
      AlgHom.comp_apply (legJ' L M ℓ ℓ') (legI L M ℓ' ℓ) x, coe_legJ, coe_legJ', coe_legI, coe_legI]
  have e3 := Divisor.correspondence_congr hPeq hIeq hjP hjI hjP' hjI' D

  have hdeg : finrankAlong L (legJ L M ℓ ℓ') = finrankAlong L (legJ' L M ℓ ℓ') := by
    have d1 : finrankAlong L (legJ L M ℓ ℓ') = IntermediateField.relfinrank (roof L M ℓ ℓ') (RR L M ℓ ℓ') :=
      finrankAlong_inclusion _
    have d2 : finrankAlong L (legJ' L M ℓ ℓ') = IntermediateField.relfinrank (roof L M ℓ' ℓ) (RR L M ℓ ℓ') :=
      finrankAlong_inclusion _
    rw [d1, d2]
    have t1 := IntermediateField.relfinrank_mul_relfinrank (KK_le_roof L M ℓ ℓ') (roof_le_RR L M ℓ ℓ')
    have t2 := IntermediateField.relfinrank_mul_relfinrank (KK_le_roof L M ℓ' ℓ) (roof'_le_RR L M ℓ ℓ')
    have hs : IntermediateField.relfinrank (KK L M) (roof L M ℓ ℓ')
        = IntermediateField.relfinrank (KK L M) (roof L M ℓ' ℓ) := by
      rw [relfinrank_KK_roof L M ℓ ℓ' hcop, relfinrank_KK_roof L M ℓ' ℓ hcop.symm, mul_comm]
    have hne : IntermediateField.relfinrank (KK L M) (roof L M ℓ ℓ') ≠ 0 :=
      nK.relfinrank_ne_zero nR (KK_le_roof L M ℓ ℓ')
    apply mul_left_cancel₀ hne
    rw [t1, hs, t2]
  have hne : (finrankAlong L (legJ L M ℓ ℓ') : ℤ) ≠ 0 := by
    exact_mod_cast nR.finrankAlong_ne_zero nRR (legJ L M ℓ ℓ')
  rw [e3, e2, ← hdeg] at e1
  exact eq_of_zsmul_eq_zsmul hne e1.symm

theorem heckeOperatorOneAlong_comm (hℓ : ℓ = ℓ' ∨ Nat.Coprime ℓ ℓ') (x : Pic0 L (KK L M)) :
    heckeOperatorOneAlong L M ℓ (heckeOperatorOneAlong L M ℓ' x)
      = heckeOperatorOneAlong L M ℓ' (heckeOperatorOneAlong L M ℓ x) := by
  by_cases heq : ℓ = ℓ'
  · subst heq; rfl
  have hcop : Nat.Coprime ℓ ℓ' := hℓ.resolve_left heq
  by_cases h : HeckeInputsOneAlong L M ℓ
  swap
  · rw [heckeOperatorOneAlong_of_not h]; simp
  by_cases h' : HeckeInputsOneAlong L M ℓ'
  swap
  · rw [heckeOperatorOneAlong_of_not h']; simp
  obtain ⟨h0, hα, hβ, hPr, hfin, hFI, hN⟩ := h
  obtain ⟨h0', hα', hβ', hPr', hfin', hFI', hN'⟩ := h'
  haveI := hPr
  haveI := hPr'
  rw [heckeOperatorOneAlong_eq h0 hα hβ hFI hfin hN, heckeOperatorOneAlong_eq h0' hα' hβ' hFI' hfin' hN']
  exact AlgebraicCurve.Pic0.correspondence_correspondence_comm
    (heckeBetaOneBar L M ℓ) (heckeAlphaOneBar L M ℓ) (heckeBetaOneBar L M ℓ') (heckeAlphaOneBar L M ℓ')
    hβ hα hβ' hα' hFI hfin hN hFI' hfin' hN'
    (fun D => heckeDiv_comm L M ℓ ℓ' hcop hα hβ hα' hβ' D) x

end X1HeckeCommute

/-- **The `X₁(M)` Hecke row commutes.**  The `Module.End ℤ` form: `Module.End.mul_apply` reduces it
to the pointwise statement of the `X₁` block above.  Verbatim from `Theorems/Thm_ModularCurve_heckeOperatorOneBar_comm.lean:12-15`. -/
theorem heckeOperatorOneBar_comm (M : ℕ) [NeZero M] (ℓ ℓ' : Nat.Primes) :
    ModularCurve.heckeOperatorOneBar M ℓ * ModularCurve.heckeOperatorOneBar M ℓ' =
      ModularCurve.heckeOperatorOneBar M ℓ' * ModularCurve.heckeOperatorOneBar M ℓ := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : NeZero (ℓ' : ℕ) := ⟨ℓ'.2.ne_zero⟩
  have hℓ : (ℓ : ℕ) = ℓ' ∨ Nat.Coprime ℓ ℓ' := by
    by_cases h : (ℓ : ℕ) = ℓ'
    · exact Or.inl h
    · exact Or.inr ((Nat.coprime_primes ℓ.2 ℓ'.2).mpr h)
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, ModularCurve.heckeOperatorOneBar_apply]
  exact X1HeckeCommute.heckeOperatorOneAlong_comm (AlgebraicClosure ℚ) M ℓ ℓ' hℓ x

end ModularCurve

end
