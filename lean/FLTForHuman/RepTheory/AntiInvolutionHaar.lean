/-
  The anti-involution commutation engine and the 2×2 conjugacy normal forms.

  `AntiInvolutionHaar.convKer_comm` is the generic two-sided commutation
  `convKer_ν(P, Q) (θ x) = convKer_ν(Q ∘ θ, P ∘ θ) x` for a continuous anti-involution
  `θ` of a locally compact group that preserves a Haar measure; `PlaceClassData`
  applies it to the place-wise archimedean anti-involution `thetaArch`, which is why
  the `RotationConjugacy`/`HalfTurnConjugacy`/`HalfTurnAxis` blocks are here: they
  provide the conjugating normal form of a `2×2` real or complex matrix into the
  reflection/transpose normal form the place argument puts `thetaArch` into.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean:461–669`
  (`AntiInvolutionHaar`) and `:1383–1591` (`RotationConjugacy`, `HalfTurnConjugacy`,
  `HalfTurnAxis`), pinned `aa2d8b3`. All four namespaces are `private` at the pin and
  land here public as the shared engine; the statements are verbatim.
-/
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.Support
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic

set_option autoImplicit false

-- The pin's `haveI` walls feed instance search (the Haar-measure record fields).
set_option linter.style.haveILetI false

open MeasureTheory

noncomputable section

namespace AntiInvolutionHaar

structure AntiInvolution (A : Type*) [Group A] [TopologicalSpace A] where
  θ : A → A
  continuous : Continuous θ
  anti : ∀ x y, θ (x * y) = θ y * θ x
  invol : ∀ x, θ (θ x) = x

section Basic

variable {A : Type*} [Group A] [TopologicalSpace A] (Θ : AntiInvolution A)

theorem θ_one : Θ.θ 1 = 1 := by
  have h := Θ.anti 1 1
  rw [one_mul] at h
  have h2 : Θ.θ 1 * Θ.θ 1 = Θ.θ 1 * 1 := by rw [mul_one, ← h]
  exact mul_left_cancel h2

theorem θ_inv (x : A) : Θ.θ x⁻¹ = (Θ.θ x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← Θ.anti, mul_inv_cancel, θ_one]

def mulInvol : A ≃* A where
  toFun x := (Θ.θ x)⁻¹
  invFun x := (Θ.θ x)⁻¹
  left_inv x := by simp only [θ_inv, Θ.invol, inv_inv]
  right_inv x := by simp only [θ_inv, Θ.invol, inv_inv]
  map_mul' x y := by rw [Θ.anti, _root_.mul_inv_rev]

theorem mulInvol_apply (x : A) : mulInvol Θ x = (Θ.θ x)⁻¹ := rfl

theorem mulInvol_symm_apply (x : A) : (mulInvol Θ).symm x = (Θ.θ x)⁻¹ := rfl

theorem mulInvol_mulInvol (x : A) : mulInvol Θ (mulInvol Θ x) = x := (mulInvol Θ).symm_apply_apply x

end Basic

section Continuity

variable {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] (Θ : AntiInvolution A)

theorem continuous_mulInvol : Continuous (mulInvol Θ) := Θ.continuous.inv

theorem continuous_mulInvol_symm : Continuous (mulInvol Θ).symm := Θ.continuous.inv

def invAnti : AntiInvolution A where
  θ x := x⁻¹
  continuous := continuous_inv
  anti x y := _root_.mul_inv_rev x y
  invol x := inv_inv x

end Continuity

section Haar

variable {A : Type*} [Group A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] (ν : Measure A)
  (Θ : AntiInvolution A)

theorem map_mulInvol_isMulRightInvariant [IsTopologicalGroup A] [ν.IsMulRightInvariant] :
    (ν.map (mulInvol Θ)).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hm : Measurable (mulInvol Θ) := (continuous_mulInvol Θ).measurable
  have hcomp : (fun x : A => x * g) ∘ (mulInvol Θ) = (mulInvol Θ) ∘ (fun y : A => y * mulInvol Θ g) := by
    funext y
    simp only [Function.comp_apply, map_mul, mulInvol_mulInvol]
  rw [Measure.map_map (measurable_mul_const g) hm, hcomp, ← Measure.map_map hm (measurable_mul_const _),
    map_mul_right_eq_self ν _]

theorem map_mulInvol_isHaarMeasure [IsTopologicalGroup A] [ν.IsHaarMeasure] :
    (ν.map (mulInvol Θ)).IsHaarMeasure :=
  (mulInvol Θ).isHaarMeasure_map (μ := ν) (continuous_mulInvol Θ) (continuous_mulInvol_symm Θ)

theorem map_θ_eq [IsTopologicalGroup A] : ν.map Θ.θ = (ν.map (mulInvol Θ)).inv := by
  have hm : Measurable (mulInvol Θ) := (continuous_mulInvol Θ).measurable
  show ν.map Θ.θ = (ν.map (mulInvol Θ)).map Inv.inv
  rw [Measure.map_map measurable_inv hm]
  congr 1
  funext x
  simp only [Function.comp_apply, mulInvol_apply, inv_inv]

theorem map_θ_isHaarMeasure [IsTopologicalGroup A] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] :
    (ν.map Θ.θ).IsHaarMeasure := by
  rw [map_θ_eq]
  haveI := map_mulInvol_isHaarMeasure ν Θ
  haveI := map_mulInvol_isMulRightInvariant ν Θ
  exact { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
          toIsOpenPosMeasure := inferInstance }

theorem map_θ_map_θ : (ν.map Θ.θ).map Θ.θ = ν := by
  rw [Measure.map_map Θ.continuous.measurable Θ.continuous.measurable]
  have : Θ.θ ∘ Θ.θ = id := funext Θ.invol
  rw [this, Measure.map_id]

theorem map_θ_eq_self [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] : ν.map Θ.θ = ν := by
  haveI := map_θ_isHaarMeasure ν Θ
  set c : NNReal := Measure.haarScalarFactor (ν.map Θ.θ) ν with hcdef
  have hc : ν.map Θ.θ = c • ν := Measure.isMulLeftInvariant_eq_smul (ν.map Θ.θ) ν
  have hsq : ν = (c * c) • ν := by
    calc ν = (ν.map Θ.θ).map Θ.θ := (map_θ_map_θ ν Θ).symm
      _ = (c • ν).map Θ.θ := by rw [← hc]
      _ = c • ν.map Θ.θ := Measure.map_smul c Θ.continuous.aemeasurable
      _ = c • (c • ν) := by rw [hc]
      _ = (c * c) • ν := smul_smul c c ν
  obtain ⟨K, hK, hKmem⟩ := exists_compact_mem_nhds (1 : A)
  have hKpos : 0 < ν K := Measure.measure_pos_of_mem_nhds (μ := ν) hKmem
  have hKfin : ν K < ⊤ := hK.measure_lt_top
  have hcc : c * c = 1 := by
    have h1 : ((c * c : NNReal) : ENNReal) * ν K = 1 * ν K := by
      rw [one_mul]
      conv_rhs => rw [hsq]
      rw [Measure.coe_nnreal_smul_apply]
    have h2 : ((c * c : NNReal) : ENNReal) = 1 := (ENNReal.mul_left_inj hKpos.ne' hKfin.ne).mp h1
    exact_mod_cast h2
  have hc1 : c = 1 := by
    rcases lt_trichotomy c 1 with hlt | heq | hgt
    · have h := mul_self_lt_mul_self (zero_le : (0 : NNReal) ≤ c) hlt
      rw [mul_one] at h
      exact absurd hcc h.ne
    · exact heq
    · have h := mul_self_lt_mul_self (zero_le : (0 : NNReal) ≤ 1) hgt
      rw [mul_one] at h
      exact absurd hcc h.ne'
  rw [hc, hc1, one_smul]

theorem isInvInvariant [IsTopologicalGroup A] [LocallyCompactSpace A] [SecondCountableTopology A]
    [ν.IsHaarMeasure]
    [ν.IsMulRightInvariant] : ν.IsInvInvariant :=
  ⟨map_θ_eq_self ν invAnti⟩

end Haar

end AntiInvolutionHaar

namespace AntiInvolutionHaar

def _root_.AntiInvolutionHaar.convKer {H : Type*} [Group H] [MeasurableSpace H] (m : Measure H) (P Q : H → ℂ) (x : H) : ℂ :=
  ∫ y, P y * Q (y⁻¹ * x) ∂m

section Transport

variable {A : Type*} [Group A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] (ν : Measure A)
  (Θ : AntiInvolution A) (hΘ : ν.map Θ.θ = ν)

def toHomeomorph : A ≃ₜ A where
  toFun := Θ.θ
  invFun := Θ.θ
  left_inv := Θ.invol
  right_inv := Θ.invol
  continuous_toFun := Θ.continuous
  continuous_invFun := Θ.continuous

include hΘ in
theorem integral_θ (F : A → ℂ) : ∫ y, F (Θ.θ y) ∂ν = ∫ y, F y ∂ν :=
  (MeasurePreserving.mk Θ.continuous.measurable hΘ).integral_comp (toHomeomorph Θ).measurableEmbedding F

include hΘ in

theorem convKer_θ [IsTopologicalGroup A] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (P Q : A → ℂ) (x : A) :
    convKer ν P Q (Θ.θ x) = convKer ν (fun y => Q (Θ.θ y)) (fun y => P (Θ.θ y)) x := by
  unfold convKer
  rw [← integral_θ ν Θ hΘ (fun y => P y * Q (y⁻¹ * Θ.θ x))]
  rw [← integral_inv_eq_self (fun z => P (Θ.θ z) * Q ((Θ.θ z)⁻¹ * Θ.θ x)) ν]
  rw [← integral_mul_left_eq_self (fun z => P (Θ.θ z⁻¹) * Q ((Θ.θ z⁻¹)⁻¹ * Θ.θ x)) x⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only
  have h1 : (x⁻¹ * w)⁻¹ = w⁻¹ * x := by group
  have h2 : (Θ.θ (w⁻¹ * x))⁻¹ * Θ.θ x = Θ.θ w := by
    rw [Θ.anti, _root_.mul_inv_rev, θ_inv, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  rw [h1, h2, mul_comm]

theorem convKer_conj [IsTopologicalGroup A] [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (P Q : A → ℂ)
    (k : A)
    (hP : ∀ y, P (k * y * k⁻¹) = P y) (hQ : ∀ y, Q (k * y * k⁻¹) = Q y) (x : A) :
    convKer ν P Q (k * x * k⁻¹) = convKer ν P Q x := by
  unfold convKer
  rw [← integral_mul_right_eq_self (fun y => P y * Q (y⁻¹ * (k * x * k⁻¹))) k⁻¹]
  rw [← integral_mul_left_eq_self (fun y => P (y * k⁻¹) * Q ((y * k⁻¹)⁻¹ * (k * x * k⁻¹))) k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  have h1 : (k * z * k⁻¹)⁻¹ * (k * x * k⁻¹) = k * (z⁻¹ * x) * k⁻¹ := by group
  rw [h1, hP, hQ]

include hΘ in

theorem convKer_comm [IsTopologicalGroup A] [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] [ν.IsInvInvariant]
    (S : Set A) (hclass : ∀ x, ∃ k ∈ S, Θ.θ x = k * x * k⁻¹) (P Q : A → ℂ)
    (hP : ∀ k ∈ S, ∀ y, P (k * y * k⁻¹) = P y) (hQ : ∀ k ∈ S, ∀ y, Q (k * y * k⁻¹) = Q y) :
    convKer ν P Q = convKer ν Q P := by
  have hPθ : (fun y => P (Θ.θ y)) = P := by
    funext y
    obtain ⟨k, hk, hky⟩ := hclass y
    rw [hky, hP k hk]
  have hQθ : (fun y => Q (Θ.θ y)) = Q := by
    funext y
    obtain ⟨k, hk, hky⟩ := hclass y
    rw [hky, hQ k hk]
  funext x
  obtain ⟨k, hk, hkx⟩ := hclass x
  calc convKer ν P Q x = convKer ν P Q (k * x * k⁻¹) := (convKer_conj ν P Q k (hP k hk) (hQ k hk) x).symm
    _ = convKer ν P Q (Θ.θ x) := by rw [hkx]
    _ = convKer ν (fun y => Q (Θ.θ y)) (fun y => P (Θ.θ y)) x := convKer_θ ν Θ hΘ P Q x
    _ = convKer ν Q P x := by rw [hPθ, hQθ]

end Transport

end AntiInvolutionHaar

namespace RotationConjugacy

theorem transpose_fin_two' (a b c d : ℝ) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ).transpose = !![a, c; b, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem refl_mul_transpose_mul_refl (a b c d : ℝ) :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ).transpose *
      !![1, 0; 0, -1] = !![a, -c; -b, d] := by
  rw [transpose_fin_two']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def rot (p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![p, q; -q, p]

theorem rot_transpose_mul_rot (p q : ℝ) :
    (rot p q).transpose * rot p q = (p ^ 2 + q ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  unfold rot
  rw [transpose_fin_two']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_rot (p q : ℝ) : (rot p q).det = p ^ 2 + q ^ 2 := by
  unfold rot
  rw [Matrix.det_fin_two_of]
  ring

theorem rot_mul_mul_rot_transpose (a b c d p q : ℝ) (hp : p = (a - d) / 2) (hq : q = (b + c) / 2) :
    rot p q * !![a, b; c, d] * (rot p q).transpose =
      (p ^ 2 + q ^ 2) • (!![a, -c; -b, d] : Matrix (Fin 2) (Fin 2) ℝ) := by
  subst hp hq
  unfold rot
  rw [transpose_fin_two']
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem exists_rotation_mul_mul_transpose_eq (g : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ k : Matrix (Fin 2) (Fin 2) ℝ, k.transpose * k = 1 ∧ k.det = 1 ∧
      k * g * k.transpose = !![1, 0; 0, -1] * g.transpose * !![1, 0; 0, -1] := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℝ, g = !![a, b; c, d] :=
    ⟨g 0 0, g 0 1, g 1 0, g 1 1, Matrix.eta_fin_two g⟩
  rw [refl_mul_transpose_mul_refl]
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (a - d) / 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (b + c) / 2 := ⟨_, rfl⟩
  by_cases hs : p ^ 2 + q ^ 2 = 0
  ·
    have hq2 : q ^ 2 = 0 := by nlinarith [sq_nonneg p, sq_nonneg q]
    have hq0 : q = 0 := (pow_eq_zero_iff two_ne_zero).mp hq2
    have hbc : c = -b := by
      rw [hq0] at hq
      linarith
    subst hbc
    refine ⟨1, by simp, by simp, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have hpos : 0 < p ^ 2 + q ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hs)
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r = Real.sqrt (p ^ 2 + q ^ 2) := ⟨_, rfl⟩
    have hr_sq : r ^ 2 = p ^ 2 + q ^ 2 := by
      rw [hr]
      exact Real.sq_sqrt hpos.le
    have hr_ne : r ≠ 0 := by
      rw [hr]
      exact (Real.sqrt_pos.mpr hpos).ne'
    have hsc : r⁻¹ * r⁻¹ * (p ^ 2 + q ^ 2) = 1 := by
      rw [← hr_sq, ← mul_inv, ← pow_two, inv_mul_cancel₀ (pow_ne_zero 2 hr_ne)]
    have hconj := rot_mul_mul_rot_transpose a b c d p q hp hq
    refine ⟨r⁻¹ • rot p q, ?_, ?_, ?_⟩
    · simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [rot_transpose_mul_rot, smul_smul, hsc, one_smul]
    · rw [Matrix.det_smul, det_rot, Fintype.card_fin, ← hr_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr_ne)]
    · simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [hconj, smul_smul, hsc, one_smul]

end RotationConjugacy

namespace HalfTurnConjugacy

open Complex

theorem transpose_fin_two' (a b c d : ℂ) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ).transpose = !![a, c; b, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def jmat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem jmat_conjTranspose : jmat.conjTranspose = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.conjTranspose_apply] <;> simp [jmat]

theorem jmat_conjTranspose_mul_jmat : jmat.conjTranspose * jmat = 1 := by
  rw [jmat_conjTranspose]
  unfold jmat
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem det_jmat : jmat.det = 1 := by
  unfold jmat
  rw [Matrix.det_fin_two_of]
  ring

theorem transpose_eq_jmat_conjTranspose_mul_adjugate_mul_jmat (a b c d : ℂ) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ).transpose = jmat.conjTranspose * !![d, -b; -c, a] * jmat := by
  rw [transpose_fin_two', jmat_conjTranspose]
  unfold jmat
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

def halfTurn (m₁ n₂ m₃ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![m₃, m₁ + n₂; m₁ - n₂, -m₃]

def halfTurnStar (m₁ n₂ m₃ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![-m₃, -m₁ - n₂; -m₁ + n₂, m₃]

theorem halfTurn_mul_halfTurnStar (m₁ n₂ m₃ : ℂ) :
    halfTurn m₁ n₂ m₃ * halfTurnStar m₁ n₂ m₃ = (n₂ ^ 2 - m₁ ^ 2 - m₃ ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold halfTurn halfTurnStar
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem det_halfTurn (m₁ n₂ m₃ : ℂ) : (halfTurn m₁ n₂ m₃).det = n₂ ^ 2 - m₁ ^ 2 - m₃ ^ 2 := by
  unfold halfTurn
  rw [Matrix.det_fin_two_of]
  ring

theorem halfTurn_mul_mul_halfTurnStar (a b c d m₁ n₂ m₃ : ℂ) :
    halfTurn m₁ n₂ m₃ * !![a, b; c, d] * halfTurnStar m₁ n₂ m₃ =
      (n₂ ^ 2 - m₁ ^ 2 - m₃ ^ 2) • (!![d, -b; -c, a] : Matrix (Fin 2) (Fin 2) ℂ) +
        (m₁ * (b + c) + n₂ * (c - b) + m₃ * (a - d)) • halfTurnStar m₁ n₂ m₃ := by
  unfold halfTurn halfTurnStar
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem halfTurnStar_eq_conjTranspose (n₁ n₂ n₃ : ℝ) :
    halfTurnStar (I * n₁) n₂ (I * n₃) = (halfTurn (I * n₁) n₂ (I * n₃)).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.conjTranspose_apply] <;> simp [halfTurn, halfTurnStar]

theorem unit_relation (n₁ n₂ n₃ : ℝ) (hn : n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = 1) :
    (n₂ : ℂ) ^ 2 - (I * n₁) ^ 2 - (I * n₃) ^ 2 = 1 := by
  have hn' : (n₁ : ℂ) ^ 2 + (n₂ : ℂ) ^ 2 + (n₃ : ℂ) ^ 2 = 1 := by exact_mod_cast hn
  linear_combination hn' - ((n₁ : ℂ) ^ 2 + (n₃ : ℂ) ^ 2) * I_sq

theorem exists_mul_mul_conjTranspose_eq_adjugate (a b c d : ℂ) (n₁ n₂ n₃ : ℝ)
    (hn : n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = 1)
    (horth : I * n₁ * (b + c) + (n₂ : ℂ) * (c - b) + I * n₃ * (a - d) = 0) :
    ∃ u : Matrix (Fin 2) (Fin 2) ℂ, u * u.conjTranspose = 1 ∧ u.det = 1 ∧
      u * !![a, b; c, d] * u.conjTranspose = !![d, -b; -c, a] := by
  refine ⟨halfTurn (I * n₁) n₂ (I * n₃), ?_, ?_, ?_⟩
  · rw [← halfTurnStar_eq_conjTranspose, halfTurn_mul_halfTurnStar, unit_relation n₁ n₂ n₃ hn, one_smul]
  · rw [det_halfTurn, unit_relation n₁ n₂ n₃ hn]
  · rw [← halfTurnStar_eq_conjTranspose, halfTurn_mul_mul_halfTurnStar, unit_relation n₁ n₂ n₃ hn, horth,
      one_smul, zero_smul, add_zero]

theorem exists_special_unitary_mul_mul_conjTranspose_eq_transpose_of_axis (a b c d : ℂ) (n₁ n₂ n₃ : ℝ)
    (hn : n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = 1)
    (horth : I * n₁ * (b + c) + (n₂ : ℂ) * (c - b) + I * n₃ * (a - d) = 0) :
    ∃ v : Matrix (Fin 2) (Fin 2) ℂ, v * v.conjTranspose = 1 ∧ v.det = 1 ∧
      v * !![a, b; c, d] * v.conjTranspose = (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℂ).transpose := by
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_mul_mul_conjTranspose_eq_adjugate a b c d n₁ n₂ n₃ hn horth
  refine ⟨jmat.conjTranspose * u, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc u,
      hu1, Matrix.one_mul, jmat_conjTranspose_mul_jmat]
  · rw [Matrix.det_mul, hu2, mul_one, Matrix.det_conjTranspose, det_jmat, star_one]
  · rw [transpose_eq_jmat_conjTranspose_mul_adjugate_mul_jmat, ← hu3, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]

end HalfTurnConjugacy

namespace HalfTurnAxis

open Complex

theorem exists_real_unit_axis (w₁ w₂ w₃ : ℂ) :
    ∃ n₁ n₂ n₃ : ℝ, n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = 1 ∧ (n₁ : ℂ) * w₁ + (n₂ : ℂ) * w₂ + (n₃ : ℂ) * w₃ = 0 := by
  let f : (Fin 3 → ℝ) →ₗ[ℝ] ℂ :=
    (LinearMap.proj 0).smulRight w₁ + (LinearMap.proj 1).smulRight w₂ + (LinearMap.proj 2).smulRight w₃
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hfv : (v 0 : ℂ) * w₁ + (v 1 : ℂ) * w₂ + (v 2 : ℂ) * w₃ = 0 := by
    simpa [f, LinearMap.smulRight_apply, Complex.real_smul] using LinearMap.mem_ker.mp hv
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hi' : 0 < v i ^ 2 := lt_of_le_of_ne (sq_nonneg (v i)) (Ne.symm (pow_ne_zero 2 hi))
  have hle : v i ^ 2 ≤ ∑ k, v k ^ 2 := Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ i)
  have hpos : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    have h := lt_of_lt_of_le hi' hle
    rwa [Fin.sum_univ_three] at h
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := ⟨_, rfl⟩
  have hs_sq : s ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [hs]
    exact Real.sq_sqrt hpos.le
  have hs_ne : s ≠ 0 := by
    rw [hs]
    exact (Real.sqrt_pos.mpr hpos).ne'
  refine ⟨v 0 / s, v 1 / s, v 2 / s, ?_, ?_⟩
  · rw [div_pow, div_pow, div_pow, ← add_div, ← add_div, ← hs_sq, div_self (pow_ne_zero 2 hs_ne)]
  · push_cast
    linear_combination (1 / (s : ℂ)) * hfv

theorem exists_axis (a b c d : ℂ) :
    ∃ n₁ n₂ n₃ : ℝ, n₁ ^ 2 + n₂ ^ 2 + n₃ ^ 2 = 1 ∧
      I * n₁ * (b + c) + (n₂ : ℂ) * (c - b) + I * n₃ * (a - d) = 0 := by
  obtain ⟨n₁, n₂, n₃, hn, h⟩ := exists_real_unit_axis (I * (b + c)) (c - b) (I * (a - d))
  exact ⟨n₁, n₂, n₃, hn, by linear_combination h⟩

end HalfTurnAxis

end
