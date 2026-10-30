/-
  The finrank/index bound for `K(j)` inside the `q`-expansion function field
  (`ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index`).

  Statement verbatim from
  `Theorems/Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index.lean`,
  proof transcribed from
  `P2M/Sol/S_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index.lean`
  (442 lines, 16 declarations), pin `aa2d8b3`.

  The pin's four sections, and where each lives in the port:

  * `Transfer` — `Φ` (`coeffMap φ`), `Φ_injective`, `Φ_ne_zero_iff`, `Φ_intSeriesC`,
    `algebraMap_laurentSeries_eq_C`, `Φ_algebraMap`, `co_mem_adjoin_of_mem_adjoin`,
    `image_intFormRatiosC`, `map_mem_adjoin`, `map_mem_qExpFunctionFieldC` are **public in
    `X1/FunctionFieldIsAlgClosed.lean`** (`ModularCurve.QExpBaseChange`) and imported, not
    restated.  Only the section's last declaration has no port home: the pin's `transfer`
    there is the *finrank*-transfer (`finrank` of the `k`-side adjoin ≤ `finrank` of the
    `κ`-side adjoin), while `QExpBaseChange.transfer` is the *existence* transfer of
    `S_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed`
    (a different pin statement, `∃ x'` + `FiniteDimensional`).  It is transcribed here as the
    `private` `transfer_finrank`.
  * `Residue` — `isAlgebraic_residueField`: public in `X1/FunctionFieldIsAlgClosed.lean`;
    imported.
  * `CharZero` — `coe_eq_zero_of_mem_maximalIdeal_top`, `residueTopHom`: public there;
    imported.
  * `Bound` — `bound_of_isAlgClosed` (private here) and the headline itself.  The
    characteristic-`p` branch reads the residue field through
    `ValuationSubring.exists_liesOverPrime_algebraicClosure_rat` and the `p`-adic
    `ValuationSubring` of `AlgebraicClosure ℚ`, and transports the finrank inequality along
    `IsAlgClosed.lift`; the characteristic-`0` branch uses the top valuation subring and
    `residueTopHom`.  Both then compare with `Γ'.index` through
    `finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index`.  Over an
    arbitrary `K`, `bound_of_isAlgClosed` at `AlgebraicClosure K` is pulled back by the
    `coeffMap` finrank inequality `finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap`
    (`X1/CoeffMap.lean`).

  The pin's file-scope `maxHeartbeats 6400000` / `synthInstance.maxHeartbeats 1600000`
  (its lines 23–24) and its `attribute [-instance]`/`[-simp]` preludes are **not**
  transcribed (FR-0067: the port has never needed a pin cap).  No `set_option` is used
  here; every declaration fits the project's 200,000-heartbeat edit loop.  The pin's
  `p2m_export`/`p2m_open`/`p2m_reactivate` plumbing is not transcribed either.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index.lean

spec-pin: Theorems/Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index.lean
spec-pin: P2M/Sol/S_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index.lean
-/

import FLTForHuman.ModularCurve.X1.FunctionFieldResidue
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.X1.FunctionFieldDegree
import FLTForHuman.ModularCurve.X1.FunctionFieldIsAlgClosed
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.Degree.PhiDegree
import FLTForHuman.NumberTheory.FrobeniusAtPlace

set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField Polynomial
open scoped MatrixGroups

namespace ModularCurve

namespace QExpIndex

open QExpBaseChange

section Transfer

variable {κ k : Type*} [Field κ] [Field k] (φ : κ →+* k)
variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

local notation "Fκ" => qExpFunctionFieldC κ Γ
local notation "Fk" => qExpFunctionFieldC k Γ

include φ in
/-- The pin's `transfer`: the finrank of `k⟮j⟯ ↪ k(Γ)` is at most the finrank of
`κ⟮j⟯ ↪ κ(Γ)`, transported along `coeffMap φ`. -/
theorem transfer_finrank (x : Fκ) (hx : (x : LaurentSeries κ) = jqModC κ)
    (x' : Fk) (hx' : (x' : LaurentSeries k) = jqModC k)
    (hfd : FiniteDimensional (adjoin κ ({x} : Set Fκ)) Fκ) :
    FiniteDimensional (adjoin k ({x'} : Set Fk)) Fk ∧
      Module.finrank (adjoin k ({x'} : Set Fk)) Fk ≤ Module.finrank (adjoin κ ({x} : Set Fκ)) Fκ := by
  classical
  have hjk : jqModC k ∈ Fk := intFormRatiosC_subset k Γ (ModularCurve.jqModC_mem_intFormRatiosC k Γ)
  have hΦx : Φ φ (x : LaurentSeries κ) = jqModC k := by rw [hx, coeffMap_jqModC]

  set Lκ : IntermediateField κ Fκ := adjoin κ ({x} : Set Fκ) with hLκ
  set K₀ : IntermediateField k Fk := adjoin k ({x'} : Set Fk) with hK₀
  set K₁ : IntermediateField k (LaurentSeries k) := adjoin k ({jqModC k} : Set (LaurentSeries k)) with hK₁
  refine (haveI : FiniteDimensional Lκ Fκ := hfd; ?_)

  let ψ₀ : Lκ →+* LaurentSeries k :=
    (Φ φ).comp (((qExpFunctionFieldC κ Γ).val : Fκ →+* LaurentSeries κ).comp (algebraMap Lκ Fκ))
  have hψ₀ : ∀ a : Lκ, ψ₀ a = Φ φ ((a : Fκ) : LaurentSeries κ) := fun a => rfl
  have hLκmap : ∀ a : Lκ, ((a : Fκ) : LaurentSeries κ) ∈
      adjoin κ ({(x : LaurentSeries κ)} : Set (LaurentSeries κ)) :=
    fun a => coe_mem_adjoin_of_mem_adjoin (qExpFunctionFieldC κ Γ) x a.2
  have hψ₀mem : ∀ a : Lκ, ψ₀ a ∈ K₁ := by
    intro a
    rw [hψ₀]
    have h := map_mem_adjoin φ (hLκmap a)
    rwa [Set.image_singleton, hΦx] at h
  let ψ : Lκ →+* K₁ := ψ₀.codRestrict K₁ hψ₀mem
  have hψval : ∀ a : Lκ, ((ψ a : K₁) : LaurentSeries k) = Φ φ ((a : Fκ) : LaurentSeries κ) :=
    fun a => rfl

  refine (haveI : Module.Free Lκ Fκ := Module.Free.of_divisionRing _ _; ?_)
  set n := Module.finrank Lκ Fκ with hn
  let v := Module.finBasis Lκ Fκ
  let w : Fin n → LaurentSeries k := fun i => Φ φ ((v i : Fκ) : LaurentSeries κ)
  set S : Submodule K₁ (LaurentSeries k) := Submodule.span K₁ (Set.range w) with hS
  refine (haveI hSfin : Module.Finite K₁ S := Module.Finite.span_of_finite K₁ (Set.finite_range w); ?_)
  have hSrank : Module.finrank K₁ S ≤ n := (finrank_range_le_card w).trans (by rw [Fintype.card_fin])

  have hsub : ∀ y : LaurentSeries κ, y ∈ Fκ → Φ φ y ∈ S := by
    intro y hy
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun Lκ).mp
      (show (⟨y, hy⟩ : Fκ) ∈ Submodule.span Lκ (Set.range v) by rw [v.span_eq]; trivial)
    have hy' : y = ∑ i, ((c i : Fκ) : LaurentSeries κ) * ((v i : Fκ) : LaurentSeries κ) := by
      have h := congrArg (fun z : Fκ => (z : LaurentSeries κ)) hc
      simp only at h
      rw [← h, AddSubmonoidClass.coe_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.smul_def, smul_eq_mul, MulMemClass.coe_mul]
    rw [hy', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_mul]
    have : Φ φ ((c i : Fκ) : LaurentSeries κ) * w i = (ψ (c i)) • w i := by
      rw [IntermediateField.smul_def, smul_eq_mul, hψval]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

  have hone : (1 : LaurentSeries k) ∈ S := by
    have h := hsub 1 (one_mem _)
    rwa [map_one] at h
  have hww : ∀ i j, w i * w j ∈ S := by
    intro i j
    have h := hsub (((v i : Fκ) : LaurentSeries κ) * ((v j : Fκ) : LaurentSeries κ))
      (mul_mem (v i).2 (v j).2)
    rwa [map_mul] at h
  have hmul : ∀ a b : LaurentSeries k, a ∈ S → b ∈ S → a * b ∈ S := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      induction hb using Submodule.span_induction with
      | mem t' ht' => obtain ⟨j, rfl⟩ := ht'; exact hww i j
      | zero => rw [mul_zero]; exact zero_mem _
      | add b₁ b₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
      | smul r b _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
    | zero => rw [zero_mul]; exact zero_mem _
    | add a₁ a₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul r a _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h

  have hinv : ∀ a : LaurentSeries k, a ∈ S → a⁻¹ ∈ S := by
    intro a ha
    by_cases ha0 : a = 0
    · rw [ha0, inv_zero]; exact zero_mem _
    let μ : S →ₗ[K₁] S :=
      { toFun := fun s => ⟨a * s, hmul a s ha s.2⟩
        map_add' := fun s t => by apply Subtype.ext; simp [mul_add]
        map_smul' := fun r s => by
          apply Subtype.ext
          simp only [SetLike.val_smul, RingHom.id_apply]
          rw [mul_smul_comm] }
    have hμinj : Function.Injective μ := by
      intro s t h
      have h' := congrArg Subtype.val h
      simp only [μ, LinearMap.coe_mk, AddHom.coe_mk] at h'
      exact Subtype.ext (mul_left_cancel₀ ha0 h')
    have hμsurj : Function.Surjective μ := LinearMap.injective_iff_surjective.mp hμinj
    obtain ⟨t, ht⟩ := hμsurj ⟨1, hone⟩
    have ht' : a * (t : LaurentSeries k) = 1 := congrArg Subtype.val ht
    have : a⁻¹ = t := by rw [inv_eq_of_mul_eq_one_right ht']
    rw [this]; exact t.2

  let SF : IntermediateField k (LaurentSeries k) :=
    { carrier := S
      mul_mem' := fun {a b} ha hb => hmul a b ha hb
      one_mem' := hone
      add_mem' := fun {a b} ha hb => add_mem ha hb
      zero_mem' := zero_mem _
      algebraMap_mem' := fun r => by
        show algebraMap k (LaurentSeries k) r ∈ S
        rw [IsScalarTower.algebraMap_apply k K₁ (LaurentSeries k) r, Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem _ _ hone
      inv_mem' := fun a ha => hinv a ha }
  have hFkS : Fk ≤ SF := by
    show adjoin k (intFormRatiosC k Γ) ≤ SF
    rw [adjoin_le_iff, ← image_intFormRatiosC φ Γ]
    rintro _ ⟨y, hy, rfl⟩
    exact hsub y (intFormRatiosC_subset κ Γ hy)

  have hK₁F : K₁ ≤ Fk := by
    rw [hK₁, adjoin_le_iff, Set.singleton_subset_iff]
    exact hjk
  let N₁ : IntermediateField K₁ (LaurentSeries k) := extendScalars hK₁F
  have hN₁S : Subalgebra.toSubmodule N₁.toSubalgebra ≤ S := by
    intro z hz
    have hz' : z ∈ Fk := hz
    exact hFkS hz'
  refine (haveI hfdN : FiniteDimensional K₁ N₁ :=
    FiniteDimensional.of_injective (Submodule.inclusion hN₁S) (Submodule.inclusion_injective hN₁S); ?_)
  have hrankN : Module.finrank K₁ N₁ ≤ n := by
    have h1 : Module.finrank K₁ (Subalgebra.toSubmodule N₁.toSubalgebra) ≤ Module.finrank K₁ S :=
      Submodule.finrank_mono hN₁S
    exact h1.trans hSrank

  have hmap : K₀.map (qExpFunctionFieldC k Γ).val = K₁ := by
    have h := adjoin_map k ({x'} : Set Fk) (qExpFunctionFieldC k Γ).val
    rw [Set.image_singleton] at h
    rw [show (qExpFunctionFieldC k Γ).val x' = jqModC k from hx'] at h
    exact h
  let e₀ : K₀ ≃ₐ[k] K₁ := (K₀.equivMap (qExpFunctionFieldC k Γ).val).trans (equivOfEq hmap)
  have he₀ : ∀ b : K₀, ((e₀ b : K₁) : LaurentSeries k) = ((b : Fk) : LaurentSeries k) := by
    intro b
    rfl
  let e₂ : N₁ ≃+* Fk := RingEquiv.refl Fk
  have hcomm : (algebraMap K₀ Fk).comp e₀.symm.toRingEquiv.toRingHom =
      e₂.toRingHom.comp (algebraMap K₁ N₁) := by
    refine RingHom.ext fun a => ?_
    apply Subtype.ext
    change (((e₀.symm a : K₀) : Fk) : LaurentSeries k) = (a : LaurentSeries k)
    rw [← he₀ (e₀.symm a), AlgEquiv.apply_symm_apply]
  refine ⟨Module.Finite.of_equiv_equiv (A₁ := K₁) (B₁ := N₁) (A₂ := K₀) (B₂ := Fk)
    e₀.symm.toRingEquiv e₂ hcomm, ?_⟩
  rw [← Algebra.finrank_eq_of_equiv_equiv (R₀ := K₁) (S₀ := N₁) (R₁ := K₀) (S₁ := Fk)
    e₀.symm.toRingEquiv e₂ hcomm]
  exact hrankN

end Transfer

section Bound

open ModularCurve IntermediateField

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
  (hT : ModularGroup.T ∈ Γ)
  (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
  (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)

include hT hΓ' hneg in
/-- Over an algebraically closed `K'`, `K'(j)` has finite and at most `Γ'.index` codimension
in the `q`-expansion function field. -/
theorem bound_of_isAlgClosed (K' : Type*) [Field K'] [IsAlgClosed K']
    (x' : qExpFunctionFieldC K' Γ) (hx' : (x' : LaurentSeries K') = jqModC K') :
    FiniteDimensional (adjoin K' ({x'} : Set (qExpFunctionFieldC K' Γ))) (qExpFunctionFieldC K' Γ) ∧
      Module.finrank (adjoin K' ({x'} : Set (qExpFunctionFieldC K' Γ)))
        (qExpFunctionFieldC K' Γ) ≤ Γ'.index := by
  classical
  obtain ⟨p, hchar⟩ := CharP.exists K'
  rcases CharP.char_is_prime_or_zero K' p with hp | rfl
  ·
    refine (haveI : Fact p.Prime := ⟨hp⟩; ?_)
    obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp⟩
    refine (haveI : CharP (IsLocalRing.ResidueField A) p :=
      ValuationSubring.charP_residueField_of_liesOverPrime_def hp hA; ?_)
    refine (letI := ZMod.algebra (IsLocalRing.ResidueField A) p; ?_)
    refine (letI := ZMod.algebra K' p; ?_)
    refine (haveI : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) :=
      isAlgebraic_residueField p A hA; ?_)
    let φ : IsLocalRing.ResidueField A →+* K' :=
      (IsAlgClosed.lift (R := ZMod p) (S := IsLocalRing.ResidueField A) (M := K')).toRingHom
    obtain ⟨xκ, hxκ, -, hfd, hle⟩ :=
      ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
        (AlgebraicClosure ℚ) A Γ hT

    have hy : jqModC (AlgebraicClosure ℚ) ∈
        laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ) := by
      have h := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (F₀ := qExpFunctionFieldC ℚ Γ)
        (intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ))
      rwa [coeffEmb, coeffMap_jqModC] at h
    have hb := hle ⟨_, hy⟩ rfl
    have hidx := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
      (AlgebraicClosure ℚ) Γ hT Γ' hΓ' hneg ⟨_, hy⟩ rfl
    obtain ⟨hfd', hle'⟩ := transfer_finrank φ Γ xκ hxκ x' hx' hfd
    exact ⟨hfd', hle'.trans (hb.trans hidx)⟩
  ·
    refine (haveI : CharZero K' := CharP.charP_to_charZero K'; ?_)
    obtain ⟨xκ, hxκ, -, hfd, hle⟩ :=
      ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
        K' (⊤ : ValuationSubring K') Γ hT
    have hy : jqModC K' ∈ laurentBaseChange K' (qExpFunctionFieldC ℚ Γ) := by
      have h := coeffEmb_mem_laurentBaseChange K' (F₀ := qExpFunctionFieldC ℚ Γ)
        (intFormRatiosC_subset ℚ Γ (ModularCurve.jqModC_mem_intFormRatiosC ℚ Γ))
      rwa [coeffEmb, coeffMap_jqModC] at h
    have hb := hle ⟨_, hy⟩ rfl
    have hidx := ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
      K' Γ hT Γ' hΓ' hneg ⟨_, hy⟩ rfl
    obtain ⟨hfd', hle'⟩ := transfer_finrank (residueTopHom K') Γ xκ hxκ x' hx' hfd
    exact ⟨hfd', hle'.trans (hb.trans hidx)⟩

end Bound

end QExpIndex

theorem finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
    (K : Type*) [Field K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ)
    (Γ' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hΓ' : Γ ≤ Γ')
    (hneg : ∀ γ ∈ Γ', γ ∈ Γ ∨ -γ ∈ Γ)
    (x : qExpFunctionFieldC K Γ)
    (hx : (x : LaurentSeries K) = jqModC K) :
    FiniteDimensional
        (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
        (qExpFunctionFieldC K Γ) ∧
      Module.finrank
          (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
          (qExpFunctionFieldC K Γ) ≤ Γ'.index := by
  classical
  have hjK' : jqModC (AlgebraicClosure K) ∈ qExpFunctionFieldC (AlgebraicClosure K) Γ :=
    intFormRatiosC_subset (AlgebraicClosure K) Γ
      (ModularCurve.jqModC_mem_intFormRatiosC (AlgebraicClosure K) Γ)
  obtain ⟨hfd', hle'⟩ :=
    QExpIndex.bound_of_isAlgClosed Γ hT Γ' hΓ' hneg (AlgebraicClosure K) ⟨_, hjK'⟩ rfl
  refine (haveI := hfd'; ?_)
  have hxt : Transcendental K (x : LaurentSeries K) := by rw [hx]; exact transcendental_jqModC K
  have hxx' : ((⟨_, hjK'⟩ : qExpFunctionFieldC (AlgebraicClosure K) Γ) :
      LaurentSeries (AlgebraicClosure K)) =
      coeffMap (algebraMap K (AlgebraicClosure K)) (x : LaurentSeries K) := by
    rw [hx, coeffMap_jqModC]
  obtain ⟨hfdK, hleK⟩ :=
    ModularCurve.finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
      (algebraMap K (AlgebraicClosure K)) Γ x ⟨_, hjK'⟩ hxt hxx'
  exact ⟨hfdK, hleK.trans hle'⟩

end ModularCurve
