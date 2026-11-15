/-
  Three rows of the unipotent–Haar family, in one module and one namespace.

  **The centre-unipotent Haar integral under a Hecke conjugation.** `rationalCentreUnipotentHaar`
  is the countable sum over `Kˣ` of the translates of the unipotent Haar measure
  (`AutomorphicForm/Adelic/UnipotentQuotient.lean`). The first two sections here compute with it:
  it is a sum over the rational scalars (`lintegral_rationalCentreUnipotentHaar`), the additive
  Haar measure of `𝔸_K` scales by the inverse modulus character under a multiplicative
  translation (`lintegral_comp_mul_adelicAddHaar`), and the conjugation by
  `heckeGen v * centralScalar u` — a diagonal times a central scalar, whose action on the
  rational points is the uniformizer shift `y ↦ τ * y` — multiplies the integral by the absolute
  norm of `v` (`lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj`).

  **The adèlic constant term at a Borelíser rational point.** The second row is the invariance of
  `constantTerm` along `globalPoints γ * g` for `γ` upper triangular: over the conditional
  probability measure of the adèlic box, the unipotent translation by the rational scalar
  `(borelDiagFst γ)⁻¹ * borelDiagSnd γ` leaves the integral alone
  (`constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup`). Its engine is the matrix
  identity `unipotentGL2 x * γ = γ * unipotentGL2 y` for a triangular `γ` — two lemmas here
  (`unipotentGL2_mul_eq_mul_unipotentGL2` in the general commutative-ring form, and its
  adèlic/global-points instantiation `globalPoints_unipotentGL2`, `unipotentGL2_mul_globalPoints`).

  **The isotypic cuspidal subspace at the principal level.** The third row: for the production
  pins at `levelOne ⊓ K_f`, the Hecke-isotypic cuspidal submodule at a finite exceptional set is
  trivial (`isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf`). Its engine is
  `infinite_heightOneSpectrum`, the infinitude of the nonarchimedean places of a number field —
  a new place can always be found outside a finite `S`, and the pin's smooth-cusp obstruction at
  that place closes the statement.

  Transcribed from the three `S_` files below (pinned `aa2d8b3`, 179 + 104 + 56 lines). The pins'
  `P2m*`/`FltWs24.*`/`Ws20.*` label namespaces are dropped — no tokens in names — and the three
  files' preludes are written once in the namespace the graph nodes name.

  **Two pin declarations are not restated**, because the port already has them:
  `continuous_unipotentGL2` (pin file 1 `:68`) is `AutomorphicForm.continuous_unipotentGL2` in
  `AutomorphicForm/Adelic/ConstantTerm.lean`, stated for an arbitrary commutative topological ring
  and hence subsuming the pin's `𝔸_K` instance (the same call the sibling module
  `RationalUnipotentHaar.lean` records in its header); and pin file 1's `solution` restates its own
  in-file headline byte for byte, so declaring both would be a duplicate inside one module.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: P2M/Sol/S_AutomorphicForm_lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.UnipotentQuotient
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelBotObstruction
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues
import FLTForHuman.NumberTheory.AdelicBoxPeriodicIntegral

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open IsDedekindDomain

open scoped ENNReal NNReal

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

/-! ### The rational centre-unipotent Haar integral -/

section RationalCentreHaar

variable (K : Type) [Field K] [NumberField K]

theorem centralScalar_mul_comm' (u : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    centralScalar (𝓞 K) K u * g = g * centralScalar (𝓞 K) K u := by
  refine Units.ext ?_
  change Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K)
  exact (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq

theorem diagOne_mul_unipotentGL2_mul_inv' (τ : (AdeleRing (𝓞 K) K)ˣ) (x : AdeleRing (𝓞 K) K) :
    diagOne τ * unipotentGL2 x * (diagOne τ)⁻¹ = unipotentGL2 ((τ : AdeleRing (𝓞 K) K) * x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [← map_inv]
  change (Matrix.diagonal ![((τ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] * !![1, x; 0, 1] *
      Matrix.diagonal ![((τ⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1]) i j = !![1, (τ : AdeleRing (𝓞 K) K) * x; 0, 1] i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_mul, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp

abbrev ratCentral (a : Kˣ) : AdelicGL2 (𝓞 K) K :=
  globalPoints (𝓞 K) K (Units.map (Matrix.scalar (Fin 2) : K →+* Matrix (Fin 2) (Fin 2) K).toMonoidHom a)

theorem ratCentral_eq_centralScalar (a : Kˣ) :
    ratCentral K a = centralScalar (𝓞 K) K (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap K (AdeleRing (𝓞 K) K) ((Matrix.scalar (Fin 2) (a : K)) i j) =
    (Matrix.scalar (Fin 2) (algebraMap K (AdeleRing (𝓞 K) K) (a : K))) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem conj_ratCentral_mul_unipotentGL2 (τ u : (AdeleRing (𝓞 K) K)ˣ) (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    (diagOne τ * centralScalar (𝓞 K) K u) * (ratCentral K a * unipotentGL2 y) * (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ =
      ratCentral K a * unipotentGL2 ((τ : AdeleRing (𝓞 K) K) * y) := by
  have hz : ∀ g : AdelicGL2 (𝓞 K) K, ratCentral K a * g = g * ratCentral K a := fun g => by
    rw [ratCentral_eq_centralScalar, centralScalar_mul_comm']
  set c := diagOne τ * centralScalar (𝓞 K) K u with hc
  rw [← mul_assoc c, ← hz c, mul_assoc (ratCentral K a), mul_assoc (ratCentral K a)]
  congr 1
  rw [hc, mul_inv_rev,
    show diagOne τ * centralScalar (𝓞 K) K u * unipotentGL2 y * ((centralScalar (𝓞 K) K u)⁻¹ * (diagOne τ)⁻¹) =
      diagOne τ * (centralScalar (𝓞 K) K u * unipotentGL2 y * (centralScalar (𝓞 K) K u)⁻¹) * (diagOne τ)⁻¹ by group,
    centralScalar_mul_comm' K u, mul_inv_cancel_right, diagOne_mul_unipotentGL2_mul_inv']

theorem ratCentral_mul_unipotentGL2_mem (a : Kˣ) (y : AdeleRing (𝓞 K) K) :
    ratCentral K a * unipotentGL2 y ∈ rationalCentreUnipotent K :=
  Subgroup.mul_mem_sup ⟨a, rfl⟩ ⟨Multiplicative.ofAdd y, rfl⟩

theorem lintegral_rationalCentreUnipotentHaar (G : rationalCentreUnipotent K → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ x, G x ∂(rationalCentreUnipotentHaar K) =
      ∑' a : Kˣ, ((adelicAddHaar (𝓞 K) K) (adelicBox K))⁻¹ *
        ∫⁻ y, G ⟨ratCentral K a * unipotentGL2 y, ratCentral_mul_unipotentGL2_mem K a y⟩ ∂(adelicAddHaar (𝓞 K) K) := by
  rw [rationalCentreUnipotentHaar, lintegral_sum_measure]
  refine tsum_congr fun a => ?_

  have hι : Measurable (fun n : adelicUnipotent K =>
      (⟨ratCentral K a * (n : AdelicGL2 (𝓞 K) K), Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩ : rationalCentreUnipotent K)) :=
    ((continuous_const.mul continuous_subtype_val).measurable).subtype_mk
  rw [lintegral_map hG hι, unipotentHaar]
  have hto : Measurable (toAdelicUnipotent K) := by
    refine (Continuous.subtype_mk ?_ _).measurable
    exact (continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K))
  have hGι : Measurable (fun n : adelicUnipotent K =>
      G ⟨ratCentral K a * (n : AdelicGL2 (𝓞 K) K), Subgroup.mul_mem_sup ⟨a, rfl⟩ n.2⟩) := hG.comp hι
  rw [lintegral_map hGι hto, lintegral_smul_measure, smul_eq_mul]
  rfl

open scoped Pointwise in
theorem lintegral_comp_mul_adelicAddHaar (τ : (AdeleRing (𝓞 K) K)ˣ) (φ : AdeleRing (𝓞 K) K → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ y, φ ((τ : AdeleRing (𝓞 K) K) * y) ∂(adelicAddHaar (𝓞 K) K) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) τ)⁻¹ : ℝ≥0) : ℝ≥0∞) * ∫⁻ y, φ y ∂(adelicAddHaar (𝓞 K) K) := by
  have hAddHaar := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hReg : (adelicAddHaar (𝓞 K) K).Regular := NumberField.AdelicHaar.regular_adelicAddHaar K
  have hmap : (adelicAddHaar (𝓞 K) K).map (fun y => (τ : AdeleRing (𝓞 K) K) * y) =
      (((distribHaarChar (AdeleRing (𝓞 K) K) τ)⁻¹ : ℝ≥0) : ℝ≥0∞) • adelicAddHaar (𝓞 K) K := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.smul_apply, smul_eq_mul,
      show (fun y => (τ : AdeleRing (𝓞 K) K) * y) ⁻¹' s = τ⁻¹ • s from Set.preimage_smul τ s,
      ← distribHaarChar_mul (adelicAddHaar (𝓞 K) K) τ⁻¹ s, map_inv]
  rw [← lintegral_map hφ (measurable_const_mul _), hmap, lintegral_smul_measure, smul_eq_mul]

theorem heckeGen_eq_diagOne_uniformizerIdele (v : HeightOneSpectrum (𝓞 K)) :
    heckeGen (𝓞 K) K v = diagOne (uniformizerIdele K v) := rfl

theorem coe_inv_distribHaarChar_uniformizerIdele (v : HeightOneSpectrum (𝓞 K)) :
    (((distribHaarChar (AdeleRing (𝓞 K) K) (uniformizerIdele K v))⁻¹ : ℝ≥0) : ℝ≥0∞) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) := by
  have h := NumberField.TateGlobal.ideleNorm_uniformizerIdele K v
  rw [NumberField.TateGlobal.ideleNorm] at h
  have h' : distribHaarChar (AdeleRing (𝓞 K) K) (uniformizerIdele K v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    rw [h, NNReal.coe_inv, NNReal.coe_natCast]
  rw [h', inv_inv, ENNReal.coe_natCast]

theorem lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj
    (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hb : ∀ y : AdelicGL2 (𝓞 K) K, y ∈ rationalCentreUnipotent K ↔
      (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * y * (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹ ∈
        rationalCentreUnipotent K)
    (F : rationalCentreUnipotent K → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ⟨(heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * (x : AdelicGL2 (𝓞 K) K) *
        (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹, (hb (x : AdelicGL2 (𝓞 K) K)).mp x.2⟩
      ∂(rationalCentreUnipotentHaar K) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) * ∫⁻ x, F x ∂(rationalCentreUnipotentHaar K) := by
  set τ := uniformizerIdele K v with hτ
  set b := heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u with hb_def
  have hbτ : b = diagOne τ * centralScalar (𝓞 K) K u := rfl

  set G : rationalCentreUnipotent K → ℝ≥0∞ := fun x => F ⟨b * (x : AdelicGL2 (𝓞 K) K) * b⁻¹, (hb _).mp x.2⟩ with hG_def
  have hG : Measurable G :=
    hF.comp (((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable.subtype_mk)
  change ∫⁻ x, G x ∂(rationalCentreUnipotentHaar K) = _
  rw [lintegral_rationalCentreUnipotentHaar K G hG, lintegral_rationalCentreUnipotentHaar K F hF, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => ?_

  set Φ : AdeleRing (𝓞 K) K → ℝ≥0∞ := fun y => F ⟨ratCentral K a * unipotentGL2 y, ratCentral_mul_unipotentGL2_mem K a y⟩ with hΦ_def
  have hΦ : Measurable Φ := hF.comp ((continuous_const.mul (continuous_unipotentGL2 (R := AdeleRing (𝓞 K) K))).measurable.subtype_mk)
  have hGΦ : ∀ y : AdeleRing (𝓞 K) K,
      G ⟨ratCentral K a * unipotentGL2 y, ratCentral_mul_unipotentGL2_mem K a y⟩ = Φ ((τ : AdeleRing (𝓞 K) K) * y) := by
    intro y
    simp only [hG_def, hΦ_def]
    refine congrArg F (Subtype.ext ?_)
    change b * (ratCentral K a * unipotentGL2 y) * b⁻¹ = ratCentral K a * unipotentGL2 ((τ : AdeleRing (𝓞 K) K) * y)
    rw [hbτ]
    exact conj_ratCentral_mul_unipotentGL2 K τ u a y
  simp_rw [hGΦ]
  rw [lintegral_comp_mul_adelicAddHaar K τ Φ hΦ, coe_inv_distribHaarChar_uniformizerIdele]
  ring

end RationalCentreHaar

/-! ### The adèlic constant term at a Borelíser rational point -/

section ConstantTermBorel

theorem unipotentGL2_mul_eq_mul_unipotentGL2 {A : Type*} [CommRing A] (γ : GL (Fin 2) A)
    (hγ : γ ∈ borelSubgroup A) (x y : A)
    (hy : (γ : Matrix (Fin 2) (Fin 2) A) 0 0 * y = x * (γ : Matrix (Fin 2) (Fin 2) A) 1 1) :
    unipotentGL2 x * γ = γ * unipotentGL2 y := by
  apply Units.ext
  have h10 : (γ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := hγ
  simp only [Units.val_mul, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hy, mul_comm, add_comm]

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

theorem globalPoints_unipotentGL2 (k : K) :
    globalPoints (𝓞 K) K (unipotentGL2 k) = unipotentGL2 (algebraMap K 𝔸 k) := by
  apply Units.ext
  ext i j
  change algebraMap K 𝔸 ((unipotentGL2 k : Matrix (Fin 2) (Fin 2) K) i j)
    = (unipotentGL2 (algebraMap K 𝔸 k) : Matrix (Fin 2) (Fin 2) 𝔸) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_mul_globalPoints (γ : Matrix.GeneralLinearGroup (Fin 2) K) (hγ : γ ∈ borelSubgroup K)
    (x : 𝔸) :
    unipotentGL2 x * globalPoints (𝓞 K) K γ
      = globalPoints (𝓞 K) K γ
        * unipotentGL2 (algebraMap K 𝔸
            ((((borelDiagFst ⟨γ, hγ⟩)⁻¹ * borelDiagSnd ⟨γ, hγ⟩ : Kˣ) : K)) * x) := by
  refine unipotentGL2_mul_eq_mul_unipotentGL2 (globalPoints (𝓞 K) K γ) (globalPoints_mem_adelicBorel (𝓞 K) K hγ) x _ ?_

  have h00 : ((globalPoints (𝓞 K) K γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) 𝔸) 0 0
      = algebraMap K 𝔸 ((γ : Matrix (Fin 2) (Fin 2) K) 0 0) := globalPoints_apply (𝓞 K) K γ 0 0
  have h11 : ((globalPoints (𝓞 K) K γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1
      = algebraMap K 𝔸 ((γ : Matrix (Fin 2) (Fin 2) K) 1 1) := globalPoints_apply (𝓞 K) K γ 1 1
  have hne : (γ : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := (borelDiagFst ⟨γ, hγ⟩).ne_zero
  rw [h00, h11, Units.val_mul, Units.val_inv_eq_inv_val, borelDiagFst_apply_val, borelDiagSnd_apply_val]
  change algebraMap K 𝔸 ((γ : Matrix (Fin 2) (Fin 2) K) 0 0)
      * (algebraMap K 𝔸 (((γ : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ * (γ : Matrix (Fin 2) (Fin 2) K) 1 1) * x)
    = x * algebraMap K 𝔸 ((γ : Matrix (Fin 2) (Fin 2) K) 1 1)
  rw [← mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_comm]

theorem constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
    (K : Type) [Field K] [NumberField K]
    {φ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : ∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ h : AutomorphicForm.AdelicGL2 (𝓞 K) K,
      φ (AutomorphicForm.globalPoints (𝓞 K) K γ * h) = φ h)
    {γ : Matrix.GeneralLinearGroup (Fin 2) K} (hγ : γ ∈ AutomorphicForm.borelSubgroup K)
    (g : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    AutomorphicForm.constantTerm
        (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
        (fun x => AutomorphicForm.unipotentGL2 x) φ (AutomorphicForm.globalPoints (𝓞 K) K γ * g)
      = AutomorphicForm.constantTerm
          (ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
          (fun x => AutomorphicForm.unipotentGL2 x) φ g := by
  set c : Kˣ := (AutomorphicForm.borelDiagFst ⟨γ, hγ⟩)⁻¹ * AutomorphicForm.borelDiagSnd ⟨γ, hγ⟩ with hc

  have hper : ∀ (k : K) (x : AdeleRing (𝓞 K) K),
      φ (AutomorphicForm.unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k + x) * g)
        = φ (AutomorphicForm.unipotentGL2 x * g) := by
    intro k x
    rw [AutomorphicForm.unipotentGL2_add, mul_assoc,
      ← globalPoints_unipotentGL2 K k,
      hφ _ (AutomorphicForm.unipotentGL2_mem_borelSubgroup k)]

  have hint : (fun x => φ (AutomorphicForm.unipotentGL2 x * (AutomorphicForm.globalPoints (𝓞 K) K γ * g)))
      = fun x => φ (AutomorphicForm.unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) (c : K) * x) * g) := by
    funext x
    rw [← mul_assoc, unipotentGL2_mul_globalPoints K γ hγ x, mul_assoc,
      hφ γ hγ]
  show ∫ x, φ (AutomorphicForm.unipotentGL2 x * (AutomorphicForm.globalPoints (𝓞 K) K γ * g))
      ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
    = ∫ x, φ (AutomorphicForm.unipotentGL2 x * g)
      ∂(ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 K) K) (AdelicBox.adelicBox K))
  rw [hint]
  exact NumberField.AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap K
    (f := fun x => φ (AutomorphicForm.unipotentGL2 x * g)) hper (c : K) c.ne_zero

end ConstantTermBorel

/-! ### The isotypic cuspidal subspace at the principal level -/

section IsotypicLevelBot

theorem infinite_heightOneSpectrum (F : Type) [Field F] [NumberField F] :
    Infinite (HeightOneSpectrum (𝓞 F)) := by
  classical
  have key : ∀ p : Nat.Primes, ∃ P : HeightOneSpectrum (𝓞 F),
      P.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {(p : ℤ)} := by
    intro p
    have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp p.2
    have hMax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 F) (Ideal.span {(p : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 F)).injective_int]; exact bot_le)
    refine ⟨⟨Q, hQmax.isPrime, fun hQ0 => ?_⟩, hQ⟩
    rw [hQ0, Ideal.under_bot ℤ (𝓞 F)] at hQ
    exact hp.ne_zero (Ideal.span_singleton_eq_bot.mp hQ.symm)
  choose P hP using key
  have hPrime : Infinite Nat.Primes := Set.infinite_coe_iff.mpr Nat.infinite_setOfPred_prime
  refine Infinite.of_injective P fun p q hpq => ?_
  have h := hP p
  rw [hpq, hP q, Ideal.span_singleton_eq_span_singleton] at h
  have h2 := Int.associated_iff_natAbs.mp h
  rw [Int.natAbs_natCast, Int.natAbs_natCast] at h2
  exact Subtype.ext h2.symm

theorem isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) :
    isotypicCuspSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) B) ξ ⊥ S Ψ = ⊥ := by
  classical
  rw [isotypicCuspSubmodule_eq_bot_iff]
  intro φ hφ
  have hInf := infinite_heightOneSpectrum F
  obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset S
  exact absurd (hφ.hecke_eigen v hv)
    (AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup F v φ (Ψ.a v))

end IsotypicLevelBot

end AutomorphicForm
