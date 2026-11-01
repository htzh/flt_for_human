/-
  C — the constant extension of the `q`-expansion function field.

  Two rows, one transfer engine.  For a field map `φ : K₀ →+* K`, the coefficient map
  `coeffMap φ` carries `qExpFunctionFieldC K₀ Γ` into `qExpFunctionFieldC K Γ`, and:

  * `genusFF_qExpFunctionFieldC_eq_of_ringHom` — the genus of the `q`-expansion function
    field does not change under the constant extension, once it is a curve with a
    transcendental generator of finite degree (`genusFF_eq` through SET 10's
    `genusFF_eq_of_constantFieldExtension_of_isAlgClosed`);
  * `transcendental_and_finiteDimensional_adjoin_laurentBaseChange_…` — the
    `laurentBaseChange` of `qExpFunctionFieldC ℚ Γ` is the whole of
    `qExpFunctionFieldC K Γ`, and `jqModC K` generates it over `K` as a finite extension
    (the `coeffEmb` form of the same transfer, fed by MS-6's finrank/index bound).

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.lean` (265 lines, 13
  declarations) and
  `P2M/Sol/S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC.lean`
  (171 lines, 10 declarations); the public statements are the matching `Theorems/`
  wrappers, verbatim.

  ## Reused, not restated

  `QExpAutBaseChange.coeffMap_mem`, `…coeffMap_algebraMap'`, `…coeffMap_intSeriesC` (the
  promoted copy of the pin's `coeffMap_intSeriesC`), `ModularCurve.coeffMap_ofPowerSeries`,
  `ModularCurve.coeffMap_injective`, `ModularCurve.coeffMap_single`,
  `BCEqProof.image_intFormRatiosC`, `BCEqProof.coeffEmb_mem_adjoin`,
  `ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq`, `ModularCurve.coeffEmb_injective`,
  `ModularCurve.coeffEmb_intSeriesC`, `ModularCurve.algebraMap_laurentSeries_eq_C`,
  `ModularCurve.coeffEmb_algebraMap` and
  `ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index`
  are imported.  The pin's `set_option maxHeartbeats 3200000` /
  `set_option synthInstance.maxHeartbeats 1600000` marks are not transcribed; the pin's
  `attribute [-instance]`/`[-simp]` walls are not either.

  spec-pin: Theorems/Thm_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.lean
  spec-pin: P2M/Sol/S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.lean
  spec-pin: Theorems/Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC.lean
  spec-pin: P2M/Sol/S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC.lean
-/
import FLTForHuman.ModularCurve.X1.FunctionFieldIndex
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.RingTheory.LaurentSeriesAlgebraic

set_option autoImplicit false

noncomputable section

open ModularCurve IntermediateField HahnSeries Module Polynomial
open scoped MatrixGroups

namespace ModularCurve

/-! ## The transfer along `φ : K₀ →+* K` -/

namespace QExpConstExt

section CoeffChange

variable {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))

theorem coeffMap_C (c : K₀) : coeffMap φ (HahnSeries.C c) = HahnSeries.C (φ c) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

/-- `coeffMap φ` as a ring hom between the two `q`-expansion function fields. -/
def qMap : qExpFunctionFieldC K₀ Γ →+* qExpFunctionFieldC K Γ :=
  ((coeffMap φ).comp (qExpFunctionFieldC K₀ Γ).subtype).codRestrict
    (qExpFunctionFieldC K Γ).toSubring fun x => QExpAutBaseChange.coeffMap_mem φ Γ x.2

@[scoped simp] theorem coe_qMap (x : qExpFunctionFieldC K₀ Γ) :
    (qMap φ Γ x : LaurentSeries K) = coeffMap φ x := rfl

/-- The constants and the `coeffMap` image of the source ring generate the target: the
two fields have the same `q`-expansion source. -/
theorem le_map_adjoin_range :
    qExpFunctionFieldC K Γ ≤
      (IntermediateField.adjoin K (Set.range (qMap φ Γ))).map (qExpFunctionFieldC K Γ).val := by
  change IntermediateField.adjoin K (intFormRatiosC K Γ) ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩
  have hg0' : intSeriesC K₀ pg ≠ 0 := by
    intro h
    apply hg0
    rw [← QExpAutBaseChange.coeffMap_intSeriesC φ, h, map_zero]
  refine (IntermediateField.mem_map _).mpr
    ⟨⟨intSeriesC K pf / intSeriesC K pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩, ?_, rfl⟩
  apply IntermediateField.subset_adjoin
  refine ⟨⟨intSeriesC K₀ pf / intSeriesC K₀ pg, div_mem_qExpFunctionFieldC f g hf hg hg0'⟩, ?_⟩
  apply Subtype.ext
  change coeffMap φ (intSeriesC K₀ pf / intSeriesC K₀ pg) = intSeriesC K pf / intSeriesC K pg
  rw [map_div₀, QExpAutBaseChange.coeffMap_intSeriesC, QExpAutBaseChange.coeffMap_intSeriesC]

end CoeffChange

section Transfer

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']

/-- Finiteness of the adjoin of a generator transports along a scalar extension. -/
theorem finiteDimensional_adjoin_algebraMap
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (x : F) (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    FiniteDimensional (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F' := by
  classical
  let ψ : F →+* F' := algebraMap F F'
  let ψa : F →ₐ[K] F' := IsScalarTower.toAlgHom K F F'
  have hψa : ∀ y, ψa y = ψ y := fun _ => rfl
  let Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  let M : IntermediateField K' F' := IntermediateField.adjoin K' ({ψ x} : Set F')

  have hθmem : ∀ c : Kx, ψ (c : F) ∈ M := by
    intro c
    have h1 : ψa (c : F) ∈ Kx.map ψa := (IntermediateField.mem_map _).mpr ⟨c, c.2, rfl⟩
    have h2 : Kx.map ψa = IntermediateField.adjoin K ({ψa x} : Set F') := by
      change (IntermediateField.adjoin K ({x} : Set F)).map ψa = _
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    rw [h2] at h1
    have hle : IntermediateField.adjoin K ({ψa x} : Set F') ≤ M.restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin K' _ (Set.mem_singleton _)
    exact hle h1
  let θ : Kx →+* M := (ψ.comp Kx.subtype).codRestrict M.toSubring fun c => hθmem c
  have hθ : ∀ c : Kx, ((θ c : M) : F') = ψ c := fun _ => rfl

  let instKxM : Algebra Kx M := θ.toAlgebra
  have hST : IsScalarTower Kx M F' := IsScalarTower.of_algebraMap_eq fun c => (hθ c).symm

  have : Algebra.IsIntegral Kx F := Algebra.IsIntegral.of_finite Kx F
  have hint : ∀ y : F, IsIntegral M (ψ y) := by
    intro y
    have h1 : IsIntegral Kx y := Algebra.IsIntegral.isIntegral y
    have h2 : IsIntegral Kx (ψ y) := h1.map (IsScalarTower.toAlgHom Kx F F')
    exact h2.tower_top

  let b := Module.finBasis Kx F
  let S : Set F' := Set.range fun i => ψ (b i)
  have : Finite S := (Set.finite_range _).to_subtype
  have hfd : FiniteDimensional M (IntermediateField.adjoin M S) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      obtain ⟨i, rfl⟩ := hy
      exact hint (b i)
  have hrange : Set.range ψ ⊆ (IntermediateField.adjoin M S : Set F') := by
    rintro _ ⟨y, rfl⟩
    have hy : y = ∑ i, (b.repr y i) • b i := (b.sum_repr y).symm
    rw [hy, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    have h1 : ψ (algebraMap Kx F (b.repr y i)) = algebraMap M F' (θ (b.repr y i)) := rfl
    rw [h1]
    refine mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    exact IntermediateField.subset_adjoin M S ⟨i, rfl⟩
  have htop : IntermediateField.adjoin M S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ (⊤ : IntermediateField K' F') := IntermediateField.mem_top
    rw [← hgen] at hz
    have hle : IntermediateField.adjoin K' (Set.range ψ) ≤
        (IntermediateField.adjoin M S).restrictScalars K' :=
      IntermediateField.adjoin_le_iff.mpr hrange
    exact hle hz
  have e : (IntermediateField.adjoin M S) ≃ₗ[M] F' :=
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv
  exact LinearEquiv.finiteDimensional e

end Transfer

section Transc

variable {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))

theorem transcendental_qMap {x : qExpFunctionFieldC K₀ Γ} (hx : Transcendental K₀ x) :
    Transcendental K (qMap φ Γ x) := by
  intro halg
  apply hx

  have halg' : IsAlgebraic K ((qMap φ Γ x : qExpFunctionFieldC K Γ) : LaurentSeries K) :=
    halg.algebraMap
  have hconst := LaurentSeries.eq_C_coeff_zero_of_isAlgebraic halg'
  rw [coe_qMap, coeffMap_coeff] at hconst

  have hx0 : (x : LaurentSeries K₀) = HahnSeries.C ((x : LaurentSeries K₀).coeff 0) := by
    apply coeffMap_injective φ.injective
    rw [coeffMap_C]
    exact hconst
  have halgx : IsAlgebraic K₀ (x : LaurentSeries K₀) := by
    rw [hx0, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]
    exact isAlgebraic_algebraMap _
  exact (isAlgebraic_algebraMap_iff (R := K₀) (A := LaurentSeries K₀)
    (FaithfulSMul.algebraMap_injective (qExpFunctionFieldC K₀ Γ) (LaurentSeries K₀))).mp halgx

end Transc

section Main

variable {K₀ K : Type*} [Field K₀] [Field K]

/-- **The genus is constant under a constant field extension.** -/
theorem genusFF_eq [IsAlgClosed K₀] [IsAlgClosed K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))
    (hfg : ∃ x : qExpFunctionFieldC K₀ Γ, Transcendental K₀ x ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set (qExpFunctionFieldC K₀ Γ)))
        (qExpFunctionFieldC K₀ Γ)) :
    AlgebraicCurve.genusFF K (qExpFunctionFieldC K Γ) = AlgebraicCurve.genusFF K₀ (qExpFunctionFieldC K₀ Γ) := by
  let instK : Algebra K₀ K := φ.toAlgebra
  let instFE : Algebra (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ) := (qMap φ Γ).toAlgebra
  let instKE : Algebra K₀ (qExpFunctionFieldC K Γ) :=
    ((algebraMap K (qExpFunctionFieldC K Γ)).comp φ).toAlgebra
  have hST₁ : IsScalarTower K₀ K (qExpFunctionFieldC K Γ) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hST₂ : IsScalarTower K₀ (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ) := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    apply Subtype.ext
    change algebraMap K (LaurentSeries K) (φ c) = coeffMap φ (algebraMap K₀ (LaurentSeries K₀) c)
    rw [QExpAutBaseChange.coeffMap_algebraMap']
  have hψ : ∀ y, algebraMap (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ) y = qMap φ Γ y :=
    fun _ => rfl

  have hgen : IntermediateField.adjoin K
      (Set.range (algebraMap (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ))) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, hy, hyz⟩ := (IntermediateField.mem_map _).mp (le_map_adjoin_range φ Γ z.2)
    rwa [← Subtype.ext hyz]
  obtain ⟨x, hx, hfin⟩ := hfg
  have hx' : Transcendental K (algebraMap (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ) x) := by
    rw [hψ]; exact transcendental_qMap φ Γ hx
  have hfin' := finiteDimensional_adjoin_algebraMap (K := K₀) (K' := K) hgen x hfin
  have : AlgebraicCurve.IsCurveOver K₀ (qExpFunctionFieldC K₀ Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hx hfin
  have : AlgebraicCurve.IsCurveOver K (qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hx' hfin'
  exact AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed K₀ (qExpFunctionFieldC K₀ Γ) K
    (qExpFunctionFieldC K Γ) ⟨x, hx, hfin⟩ ⟨_, hx', hfin'⟩ hgen

end Main

end QExpConstExt

/-- **The genus of the `q`-expansion function field is constant under a constant field
extension.** -/
theorem genusFF_qExpFunctionFieldC_eq_of_ringHom
    {K₀ K : Type*} [Field K₀] [Field K] [IsAlgClosed K₀] [IsAlgClosed K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hfg : ∃ x : ModularCurve.qExpFunctionFieldC K₀ Γ, Transcendental K₀ x ∧
      FiniteDimensional
        (IntermediateField.adjoin K₀ ({x} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
        (ModularCurve.qExpFunctionFieldC K₀ Γ)) :
    AlgebraicCurve.genusFF K (ModularCurve.qExpFunctionFieldC K Γ) =
      AlgebraicCurve.genusFF K₀ (ModularCurve.qExpFunctionFieldC K₀ Γ) :=
  QExpConstExt.genusFF_eq φ Γ hfg

/-! ## The fullness of `laurentBaseChange` at `jqModC`

The same transfer, read through `coeffEmb` instead of `coeffMap φ`: `laurentBaseChange K`
of `qExpFunctionFieldC ℚ Γ` is the whole of `qExpFunctionFieldC K Γ`, so the image of
`jqModC K` generates the target over `K` as a finite extension. -/

namespace FullnessGamma1

variable (K : Type*) [Field K] [Algebra ℚ K]

/-- `coeffEmb K` does not kill a nonzero series. -/
theorem coeffEmb_ne_zero_iff (x : LaurentSeries ℚ) : coeffEmb K x ≠ 0 ↔ x ≠ 0 := by
  rw [Ne, ← map_zero (coeffEmb K)]
  constructor
  · intro h hx
    exact h (by rw [hx, map_zero])
  · intro hx h0
    apply hx
    ext n
    have h1 := congrArg (fun s : LaurentSeries K => s.coeff n) h0
    simpa [coeffEmb_coeff] using (algebraMap ℚ K).injective h1

variable {K}

/-- The `K`-degree of the adjoin of a generator of an intermediate field equals its
relative degree over that field. -/
theorem finrank_adjoin_eq_relfinrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : IntermediateField K E) (x : F) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F =
      (IntermediateField.adjoin K ({(x : E)} : Set E)).relfinrank F := by
  have hlift : IntermediateField.lift (IntermediateField.adjoin K ({x} : Set F)) =
      IntermediateField.adjoin K ({(x : E)} : Set E) := by
    rw [IntermediateField.lift_adjoin]; simp
  have hle : IntermediateField.adjoin K ({(x : E)} : Set E) ≤ F := by
    rw [← hlift]; exact IntermediateField.lift_le _
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  let i : (IntermediateField.adjoin K ({x} : Set F)) ≃+*
      (IntermediateField.adjoin K ({(x : E)} : Set E)) :=
    ((IntermediateField.liftAlgEquiv (IntermediateField.adjoin K ({x} : Set F))).trans
      (IntermediateField.equivOfEq hlift)).toRingEquiv
  let j : F ≃+* (IntermediateField.extendScalars hle) := RingEquiv.refl _
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  ext a
  rfl

end FullnessGamma1

open FullnessGamma1 in
/-- **`jqModC K` generates `laurentBaseChange K (qExpFunctionFieldC ℚ Γ)` finitely.** -/
theorem transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
    (K : Type*) [Field K] [Algebra ℚ K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    Transcendental K y ∧
      FiniteDimensional
        ↥(IntermediateField.adjoin K ({y} : Set ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ))))
        ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by
  classical
  constructor
  ·
    have hinj : Function.Injective
        (algebraMap ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) (LaurentSeries K)) :=
      (algebraMap ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) (LaurentSeries K)).injective
    rw [← transcendental_algebraMap_iff hinj]
    change Transcendental K (y : LaurentSeries K)
    rw [hy]
    exact ModularCurve.transcendental_jqModC K
  ·
    have hEE : laurentBaseChange K (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC K Γ :=
      ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq K Γ
    have hjE' : jqModC K ∈ laurentBaseChange K (qExpFunctionFieldC ℚ Γ) := hy ▸ y.2
    have hjE : jqModC K ∈ qExpFunctionFieldC K Γ := hEE ▸ hjE'
    obtain ⟨hfin, -⟩ :=
      ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
        Γ hT Γ le_rfl (fun γ hγ => Or.inl hγ) ⟨jqModC K, hjE⟩ rfl
    have := hfin
    have hFree : Module.Free
        ↥(IntermediateField.adjoin K ({(⟨jqModC K, hjE⟩ : qExpFunctionFieldC K Γ)} :
          Set (qExpFunctionFieldC K Γ))) ↥(qExpFunctionFieldC K Γ) :=
      Module.Free.of_divisionRing _ _
    have := hFree
    have hpos : 0 < Module.finrank
        ↥(IntermediateField.adjoin K ({(⟨jqModC K, hjE⟩ : qExpFunctionFieldC K Γ)} : Set (qExpFunctionFieldC K Γ)))
        ↥(qExpFunctionFieldC K Γ) :=
      (Module.finrank_pos_iff_of_free _ _).mpr inferInstance
    have e1 := finrank_adjoin_eq_relfinrank (qExpFunctionFieldC K Γ) ⟨jqModC K, hjE⟩
    have e2 := finrank_adjoin_eq_relfinrank (laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) y
    have e12 : (IntermediateField.adjoin K ({((⟨jqModC K, hjE⟩ : qExpFunctionFieldC K Γ) : LaurentSeries K)} :
          Set (LaurentSeries K))).relfinrank (qExpFunctionFieldC K Γ) =
        (IntermediateField.adjoin K ({(y : LaurentSeries K)} : Set (LaurentSeries K))).relfinrank
          (laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) := by
      rw [hy, hEE]
    have hpos' : 0 < Module.finrank
        ↥(IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ))))
        ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) :=
      lt_of_lt_of_eq hpos ((e1.trans e12).trans e2.symm)
    have : Module.Free
        ↥(IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ))))
        ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) := Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_pos hpos'

end ModularCurve

end
