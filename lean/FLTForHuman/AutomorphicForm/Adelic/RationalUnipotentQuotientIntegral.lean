/-
  The two rational quotient integrals agree after summing over the units.

  `rationalTorusUnipotent` is `rationalCentreUnipotent` enlarged by the rational *diagonal*
  `Kˣ`; passing from one quotient to the other is therefore a sum over `Kˣ`, and this module proves
  that the two quotient measures compute the same integral:

  for a `Γ`-invariant `k` (`Γ = rationalCentreUnipotent F`) and a fundamental domain `𝓕B` of the
  image of the Borel in `GL₂(𝔸_F)`,

  * `∫_{q ∈ CentreUnipotentQuotient} k q.out` is `∫_{g ∈ 𝓕B} ∑' a : Fˣ, k (diagOne a · g)`,
  * the sum `∑' a, k (diagOne a · q.out)` is integrable on the torus quotient, and its integral is
    the same number.

  The content is the **box-sheet** machinery of `RationalUnipotentBoxSheet.lean` fed into the
  Haar-quotient integral calculus (`MeasureTheory/HaarQuotient.lean`): the finite index set is the
  fundamental domain of `Kˣ` inside the torus-unipotent group, which is where
  `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` — the Bruhat
  decomposition of the Borel — is used.

  Transcribed from `Theorems/Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient.lean`
  and its `S_` file (pinned `aa2d8b3`, 366 lines). It is the headline of the SET-AF21 story and the
  last row of the rational-unipotent quotient block.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.RationalUnipotentBoxSheet
import FLTForHuman.AutomorphicForm.Adelic.RationalUnipotentClosed
import FLTForHuman.MeasureTheory.HaarQuotient
import FLTForHuman.MeasureTheory.IsFundamentalDomainCosets

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open scoped ENNReal Pointwise

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

/- The rational diagonal `diagHom` lives in the torus-unipotent chart namespace of
`RationalUnipotentHaar.lean`; the pin has it in scope unqualified, so the port opens it. -/
open TorusUnipotent

/-! ### Two generic measure-theory lemmas

The pin proves both in its `S_` file; they are generic and stated here at the same names. -/

/-- A pointwise `tsum` of measurable `ℂ`-valued functions is measurable. -/
theorem measurable_tsum_complex {α ι : Type*} [MeasurableSpace α] [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x :=
  Measurable.tsum hf

/-- The `enorm` of a `tsum` is bounded by the `tsum` of the `enorm`s. -/
theorem enorm_tsum_le {ι : Type*} (f : ι → ℂ) : ‖∑' i, f i‖ₑ ≤ ∑' i, ‖f i‖ₑ := by
  by_cases h : Summable f
  · have hn : Summable fun i => ‖f i‖₊ := by
      rw [← NNReal.summable_coe]; simp only [coe_nnnorm]; exact summable_norm_iff.mpr h
    calc ‖∑' i, f i‖ₑ = ((‖∑' i, f i‖₊ : NNReal) : ℝ≥0∞) := rfl
      _ ≤ ((∑' i, ‖f i‖₊ : NNReal) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr (nnnorm_tsum_le hn)
      _ = ∑' i, ‖f i‖ₑ := by rw [ENNReal.coe_tsum hn]; rfl
  · rw [tsum_eq_zero_of_not_summable h, enorm_zero]
    exact bot_le

section

variable (F : Type) [Field F] [NumberField F]

/-- `diagHom` on the other side: a rational diagonal moves past a unipotent element. -/
theorem diagHom_mul_unipotentGL2 (a : Fˣ) (u : AdeleRing (𝓞 F) F) :
    diagHom F a * unipotentGL2 u =
      unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (a : F) * u) * diagHom F a := by
  rw [TorusUnipotent.unipotentGL2_mul_diagHom, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val,
    inv_mul_cancel₀ a.ne_zero, map_one, one_mul]

/-- The rational points embed injectively in `GL₂(𝔸_F)`. -/
theorem globalPoints_injective : Function.Injective (globalPoints (𝓞 F) F) := by
  intro x y h
  apply Units.ext
  ext i j
  have := congrArg (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) h
  simp only [globalPoints_apply] at this
  exact (NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F)) this

/-- The subgroup of elements that do not move `f` from the left. -/
def leftStabilizer (f : AdelicGL2 (𝓞 F) F → ℂ) : Subgroup (AdelicGL2 (𝓞 F) F) where
  carrier := {x | ∀ g, f (x * g) = f g}
  mul_mem' := by
    intro a b ha hb g
    rw [mul_assoc, ha, hb]
  one_mem' := by
    intro g
    rw [one_mul]
  inv_mem' := by
    intro a ha g
    rw [← ha (a⁻¹ * g), mul_inv_cancel_left]

/-- The scalars times the unipotent radical inside `GL₂(F)`. -/
abbrev scalarUnipotent : Subgroup (GL (Fin 2) F) :=
  (Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom).range ⊔
    (unipotentGL2Hom (R := F)).range

/-- The rational image of the scalars times the unipotent radical: the "parabolic" whose
fundamental domain is cut by the diagonal. -/
abbrev ratP : Subgroup (AdelicGL2 (𝓞 F) F) :=
  rationalCentre F ⊔ ((globalPoints (𝓞 F) F).comp (unipotentGL2Hom (R := F))).range

/-- `ratP` is the image of `scalarUnipotent` under the rational points. -/
theorem ratP_eq_map : ratP F = (scalarUnipotent F).map (globalPoints (𝓞 F) F) := by
  rw [Subgroup.map_sup, ← MonoidHom.range_comp, ← MonoidHom.range_comp]

/- `scalarUnipotent` sits in the Borel. A plain comment rather than a docstring: a docstring cannot
precede `omit … in`, and the `NumberField` variable is not needed for this inequality. -/
omit [NumberField F] in
theorem scalarUnipotent_le_borel : scalarUnipotent F ≤ borelSubgroup F := by
  refine sup_le ?_ ?_
  · rintro _ ⟨a, rfl⟩
    show (Matrix.scalar (Fin 2) ((a : Fˣ) : F)) 1 0 = 0
    simp
  · rintro _ ⟨t, rfl⟩
    exact unipotentGL2_mem_borelSubgroup _

/-- `ratP` sits in the image of the Borel. -/
theorem ratP_le_borelMap : ratP F ≤ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  rw [ratP_eq_map]
  exact Subgroup.map_mono (scalarUnipotent_le_borel F)

/-- The rational diagonal sits in the image of the Borel. -/
theorem diagHom_mem_borelMap (a : Fˣ) :
    diagHom F a ∈ (borelSubgroup F).map (globalPoints (𝓞 F) F) := by
  refine ⟨diagOne a, ?_, rfl⟩
  show (diagOne a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  rw [diagOne_coe_apply]; simp

/-- **The Bruhat dictionary.** Every element of the image of the Borel has a unique diagonal
representative modulo `ratP`. -/
theorem existsUnique_repr (γ : (borelSubgroup F).map (globalPoints (𝓞 F) F)) :
    ∃! a : Fˣ, (((⟨diagHom F a, diagHom_mem_borelMap F a⟩ :
      (borelSubgroup F).map (globalPoints (𝓞 F) F))⁻¹ * γ :
      (borelSubgroup F).map (globalPoints (𝓞 F) F)) : AdelicGL2 (𝓞 F) F) ∈ ratP F := by
  obtain ⟨b, hb, hbγ⟩ := γ.2
  have h := existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup F b hb
  refine (existsUnique_congr fun a => ?_).mp h
  rw [ratP_eq_map]
  have hval : (((⟨diagHom F a, diagHom_mem_borelMap F a⟩ :
      (borelSubgroup F).map (globalPoints (𝓞 F) F))⁻¹ * γ :
      (borelSubgroup F).map (globalPoints (𝓞 F) F)) : AdelicGL2 (𝓞 F) F) =
      globalPoints (𝓞 F) F ((diagOne a)⁻¹ * b) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, ← hbγ]
    rfl
  rw [hval, Subgroup.mem_map_iff_mem (globalPoints_injective F)]

end

/-! ### The headline -/

/-- Summing over the rational diagonal identifies the torus-unipotent quotient integral with the
centre-unipotent one. -/
theorem integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
    (F : Type) [Field F] [NumberField F]
    (𝓕B : Set (AdelicGL2 (𝓞 F) F))
    (h𝓕B : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F))
    (k : AdelicGL2 (𝓞 F) F → ℂ) (hk : Measurable k)
    (hkH : ∀ h ∈ rationalCentreUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, k (h * g) = k g)
    (hfin : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    Integrable (fun q : RationalCentreUnipotentQuotient F => k q.out) (rationalCentreUnipotentQuotientMeasure F) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F => ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out))
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q : RationalTorusUnipotentQuotient F, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) =
      ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q : RationalCentreUnipotentQuotient F, k q.out ∂(rationalCentreUnipotentQuotientMeasure F) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable Fˣ := Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set Bm : Subgroup (AdelicGL2 (𝓞 F) F) := (borelSubgroup F).map (globalPoints (𝓞 F) F) with hBm
  have : SecondCountableTopology (AdelicGL2 (𝓞 F) F) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo F
  have : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have := (isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant F).1
  have := (isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant F).2
  have := (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).1
  have := (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).2

  obtain ⟨hPle, hPcount, hT₁m, hT₁fd, hT₁int⟩ := isFundamentalDomain_boxSheet_rationalCentreUnipotent F
  obtain ⟨hBle, hBcount, hT₂m, hT₂fd, hT₂int⟩ := isFundamentalDomain_boxSheet_rationalTorusUnipotent F
  have : Countable (ratP F) := hPcount
  have : Countable Bm := hBcount

  have hδ : ∀ a : Fˣ, globalPoints (𝓞 F) F (diagOne a) = diagHom F a := fun a => rfl
  set K₃ : AdelicGL2 (𝓞 F) F → ℂ := fun g => ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) with hK₃
  have hK₃m : Measurable K₃ :=
    measurable_tsum_complex fun a => hk.comp (measurable_const_mul (globalPoints (𝓞 F) F (diagOne a)))

  have hkδn : ∀ (a : Fˣ) (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
      k (diagHom F a * (unipotentGL2 u * g)) = k (diagHom F a * g) := by
    intro a u g
    rw [← mul_assoc, diagHom_mul_unipotentGL2, mul_assoc]
    exact hkH (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) (a : F) * u))
      (Subgroup.mem_sup_right ⟨Multiplicative.ofAdd (algebraMap F (AdeleRing (𝓞 F) F) (a : F) * u), rfl⟩)
      (diagHom F a * g)
  have hkδz : ∀ (a z : Fˣ) (g : AdelicGL2 (𝓞 F) F),
      k (diagHom F a * (ratCentralHom F z * g)) = k (diagHom F a * g) := by
    intro a z g
    rw [← mul_assoc, ← ratCentralHom_comm, mul_assoc]
    exact hkH (ratCentralHom F z) (Subgroup.mem_sup_left ⟨z, rfl⟩) (diagHom F a * g)
  have hK₃inv : rationalTorusUnipotent F ≤ leftStabilizer F K₃ := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rintro _ ⟨z, rfl⟩ g
      show ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * (_ * g)) =
        ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g)
      exact tsum_congr fun a => hkδz a z g
    · rintro _ ⟨a₀, rfl⟩ g
      show ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * (diagHom F a₀ * g)) =
        ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g)
      have h1 : ∀ a : Fˣ,
          k (globalPoints (𝓞 F) F (diagOne a) * (diagHom F a₀ * g)) =
            k (diagHom F (a * a₀) * g) := by
        intro a; rw [hδ, ← mul_assoc, ← map_mul]
      simp_rw [h1]
      exact (Equiv.mulRight a₀).tsum_eq (fun b => k (diagHom F b * g))
    · rintro _ ⟨t, rfl⟩ g
      show ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * (unipotentGL2 t.toAdd * g)) =
        ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g)
      exact tsum_congr fun a => hkδn a _ g
  have hK₃H₂ : ∀ h ∈ rationalTorusUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, K₃ (h * g) = K₃ g :=
    fun h hh g => hK₃inv hh g
  have hK₃B : ∀ γ ∈ Bm, ∀ g : AdelicGL2 (𝓞 F) F, K₃ (γ * g) = K₃ g := fun γ hγ g => hK₃H₂ γ (hBle hγ) g

  set R : Fˣ → Bm := fun a => ⟨diagHom F a, diagHom_mem_borelMap F a⟩ with hR_def
  have hR : ∀ γ : Bm, ∃! a : Fˣ, (((R a)⁻¹ * γ : Bm) : AdelicGL2 (𝓞 F) F) ∈ ratP F := existsUnique_repr F
  have hFD₂ : IsFundamentalDomain (ratP F) (⋃ a : Fˣ, ((R a : AdelicGL2 (𝓞 F) F)⁻¹) • 𝓕B) μ :=
    MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives μ Bm (ratP F)
      (ratP_le_borelMap F) 𝓕B h𝓕B R hR
  obtain ⟨hC1l, hC1b⟩ :=
    MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
      μ Bm (ratP F) (ratP_le_borelMap F) 𝓕B h𝓕B R hR
  have hRinv : ∀ (a : Fˣ) (g : AdelicGL2 (𝓞 F) F),
      ((R a : AdelicGL2 (𝓞 F) F))⁻¹ • g = diagHom F a⁻¹ * g := by
    intro a g
    rw [smul_eq_mul, hR_def]
    simp only [map_inv]
  have hreidx_e : ∀ g : AdelicGL2 (𝓞 F) F,
      (∑' a : Fˣ, ‖k (((R a : AdelicGL2 (𝓞 F) F))⁻¹ • g)‖ₑ) =
        ∑' a : Fˣ, ‖k (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ := by
    intro g
    simp_rw [hRinv, hδ]
    exact (Equiv.inv Fˣ).tsum_eq (fun a => ‖k (diagHom F a * g)‖ₑ)
  have hreidx : ∀ g : AdelicGL2 (𝓞 F) F,
      (∑' a : Fˣ, k (((R a : AdelicGL2 (𝓞 F) F))⁻¹ • g)) = K₃ g := by
    intro g
    simp_rw [hRinv, hK₃, hδ]
    exact (Equiv.inv Fˣ).tsum_eq (fun a => k (diagHom F a * g))
  have hnormfin : ∫⁻ g in ⋃ a : Fˣ, ((R a : AdelicGL2 (𝓞 F) F)⁻¹) • 𝓕B, ‖k g‖ₑ ∂μ < ∞ := by
    rw [hC1l _ hk.enorm]
    simp_rw [hreidx_e]
    exact hfin
  obtain ⟨-, -, hA⟩ := hC1b k hk.aestronglyMeasurable (by simp_rw [hreidx_e]; exact hfin)
  simp_rw [hreidx] at hA

  have hkP : ∀ γ ∈ ratP F, ∀ g : AdelicGL2 (𝓞 F) F, k (γ * g) = k g := fun γ hγ g => hkH γ (hPle hγ) g
  obtain ⟨-, hIB, hB⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μ
      (rationalCentreUnipotent F) (isClosed_rationalCentreUnipotent F) (rationalCentreUnipotentHaar F)
      (ratP F) hPle k hk hkP _ hFD₂ _ hT₁fd hnormfin
  have hmass₁ : rationalCentreUnipotentHaar F
      ((fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F) = 1 := by
    have h := hT₁int (fun _ => 1) measurable_const
    rw [setLIntegral_one, setLIntegral_one, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne] at h
    exact h
  have hfib₁ : ∀ q : RationalCentreUnipotentQuotient F,
      (∫ x in (fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F,
        k ((x : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalCentreUnipotentHaar F)) = k q.out := by
    intro q
    have : (fun x : rationalCentreUnipotent F => k ((x : AdelicGL2 (𝓞 F) F) * q.out)) = fun _ => k q.out :=
      funext fun x => hkH x x.2 _
    rw [this, setIntegral_const]
    simp [Measure.real, hmass₁]
  simp_rw [hfib₁] at hIB hB

  have hK₃fin : ∫⁻ g in 𝓕B, ‖K₃ g‖ₑ ∂μ < ∞ :=
    lt_of_le_of_lt (lintegral_mono fun g => enorm_tsum_le _) hfin
  obtain ⟨-, hIC, hC⟩ :=
    HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out μ
      (rationalTorusUnipotent F) (isClosed_rationalTorusUnipotent F) (rationalTorusUnipotentHaar F)
      Bm hBle K₃ hK₃m hK₃B 𝓕B h𝓕B _ hT₂fd hK₃fin
  have hmass₂ : rationalTorusUnipotentHaar F
      ((fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F) = 1 := by
    have h := hT₂int (fun _ => 1) measurable_const
    rw [setLIntegral_one, setLIntegral_one, Measure.smul_apply, smul_eq_mul,
      ENNReal.inv_mul_cancel (adelicAddHaar_adelicBox_pos F).ne' (adelicAddHaar_adelicBox_lt_top F).ne] at h
    exact h
  have hfib₂ : ∀ q : RationalTorusUnipotentQuotient F,
      (∫ x in (fun u : AdeleRing (𝓞 F) F => Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F,
        K₃ ((x : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F)) = K₃ q.out := by
    intro q
    have : (fun x : rationalTorusUnipotent F => K₃ ((x : AdelicGL2 (𝓞 F) F) * q.out)) = fun _ => K₃ q.out :=
      funext fun x => hK₃H₂ x x.2 _
    rw [this, setIntegral_const]
    simp [Measure.real, hmass₂]
  simp_rw [hfib₂] at hIC hC

  refine ⟨hIB, hIC, hC.symm, ?_⟩
  rw [hA.symm.trans hB]
  rfl

end AutomorphicForm

end
