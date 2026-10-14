/-
  The complex-place Iwasawa engine -- uniform decay (tier 3, unlisted).

  The uniform-in-`g` half of the complex Iwasawa development of the pinned FLT
  repository `anthropics/fermats-last-theorem@aa2d8b3`.  It rests on
  `Core.lean`'s `CplxIwasawa`/`CplxSmooth`/`KCUnif` blocks and on `Decay.lean`'s
  `CplxDecay` block, and writes once:

  * `B2bCL1` -- the uniform symbol estimate: on a compact set of invertible `g`
    and a compact set `U` of exponents, every iterated real derivative of
    `radC g · ^ (-u)` is dominated by the undifferentiated majorant
    `radC g · ^ (-Re u)`, with a constant uniform in `g` and `u`;
  * `Engine` -- the two uniform kernels.

  The pin's `B2bCL1` re-carries the whole `radC` prelude of `CplxIwasawa` and
  the `cpow` block of `CplxDecay` (byte-identical statements); those are dropped
  and the landed copies imported, so the block is written once.  Its local copy
  of `B2bCKit.pow_mul_norm_fourierIntegral_le_of_coercive` is homed at
  `FLTForHuman/MeasureTheory/FourierDecay.lean` and imported.  Every transcribed
  declaration carries a `-- pin:` provenance comment.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`;
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact.lean
-/
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import FLTForHuman.AutomorphicForm.Iwasawa.Complex.Decay
import FLTForHuman.MeasureTheory.FourierDecay

set_option autoImplicit false

noncomputable section

open ComplexConjugate
open scoped ContDiff

namespace AutomorphicForm.ComplexIwasawa


open MeasureTheory CplxSmooth Real VectorFourier Complex
open scoped ContDiff FourierTransform

namespace B2bCL1

open ComplexConjugate
open CplxIwasawa KCUnif CplxDecay
open scoped Nat

variable {g : Matrix (Fin 2) (Fin 2) ℂ}

-- pin: reFun (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:136)
def reFun : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  Complex.reCLM.smulRight (Complex.reCLM : ℂ →L[ℝ] ℝ)
    + Complex.imCLM.smulRight (Complex.imCLM : ℂ →L[ℝ] ℝ)

-- pin: reFun_apply_apply (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:140)
theorem reFun_apply_apply (a v : ℂ) : reFun a v = a.re * v.re + a.im * v.im := by
  simp [reFun, smul_eq_mul]

-- pin: slopeC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:143)
def slopeC (g : Matrix (Fin 2) (Fin 2) ℂ) (w : ℂ) : ℂ :=
  conj (g 1 0) * kC g w 1 0 + conj (g 1 1) * kC g w 1 1

-- pin: kC_one_zero (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:146)
theorem kC_one_zero (w : ℂ) : kC g w 1 0 = botP g w / (radC g w : ℂ) := by
  simp [kC]

-- pin: kC_one_one (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:149)
theorem kC_one_one (w : ℂ) : kC g w 1 1 = botQ g w / (radC g w : ℂ) := by
  simp [kC]

-- pin: hasFDerivAt_botP (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:152)
theorem hasFDerivAt_botP (w : ℂ) :
    HasFDerivAt (botP g) ((g 1 0) • ContinuousLinearMap.id ℝ ℂ) w := by
  have h : botP g = fun y : ℂ => g 0 0 + y * g 1 0 := rfl
  rw [h]
  exact ((hasFDerivAt_id w).mul_const (g 1 0)).const_add (g 0 0)

-- pin: hasFDerivAt_botQ (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:158)
theorem hasFDerivAt_botQ (w : ℂ) :
    HasFDerivAt (botQ g) ((g 1 1) • ContinuousLinearMap.id ℝ ℂ) w := by
  have h : botQ g = fun y : ℂ => g 0 1 + y * g 1 1 := rfl
  rw [h]
  exact ((hasFDerivAt_id w).mul_const (g 1 1)).const_add (g 0 1)

-- pin: radC_eq_sqrt_norm_sq (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:164)
theorem radC_eq_sqrt_norm_sq (g : Matrix (Fin 2) (Fin 2) ℂ) :
    radC g = fun y => Real.sqrt (‖botP g y‖ ^ 2 + ‖botQ g y‖ ^ 2) := by
  funext y
  simp [radC, Complex.normSq_eq_norm_sq]

-- pin: hasFDerivAt_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:169)
theorem hasFDerivAt_radC (hg : g.det ≠ 0) (w : ℂ) :
    HasFDerivAt (radC g) (reFun (slopeC g w)) w := by
  have hF : HasFDerivAt (fun y : ℂ => ‖botP g y‖ ^ 2 + ‖botQ g y‖ ^ 2)
      (2 • (innerSL ℝ (botP g w)).comp ((g 1 0) • ContinuousLinearMap.id ℝ ℂ)
        + 2 • (innerSL ℝ (botQ g w)).comp ((g 1 1) • ContinuousLinearMap.id ℝ ℂ)) w :=
    (hasFDerivAt_botP w).norm_sq.add (hasFDerivAt_botQ w).norm_sq
  have hrad : 0 < radC g w := radC_pos hg w
  have hF0 : ‖botP g w‖ ^ 2 + ‖botQ g w‖ ^ 2 ≠ 0 := by
    have h := congrFun (radC_eq_sqrt_norm_sq g) w
    intro h0
    rw [h0, Real.sqrt_zero] at h
    exact hrad.ne' h
  have hR := hF.sqrt hF0
  rw [← radC_eq_sqrt_norm_sq g] at hR
  have hsq : Real.sqrt (‖botP g w‖ ^ 2 + ‖botQ g w‖ ^ 2) = radC g w :=
    (congrFun (radC_eq_sqrt_norm_sq g) w).symm
  rw [hsq] at hR
  convert hR using 1
  ext v
  rw [reFun_apply_apply]
  -- v4.34.0: `ContinuousLinearMap.add_apply`/`smul_apply` are deprecated aliases of the
  -- root lemmas (the pin's v4.33.1 names).
  simp only [slopeC, kC_one_zero, kC_one_one, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    innerSL_apply_apply, Complex.inner, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.div_ofReal_re, Complex.div_ofReal_im]
  field_simp
  ring

-- pin: fderiv_radC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:197)
theorem fderiv_radC (hg : g.det ≠ 0) : fderiv ℝ (radC g) = fun w => reFun (slopeC g w) :=
  funext fun w => (hasFDerivAt_radC hg w).fderiv

-- pin: contDiff_slopeC (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:203)
theorem contDiff_slopeC (hg : g.det ≠ 0) : ContDiff ℝ ∞ (slopeC g) := by
  unfold slopeC
  exact (contDiff_const.mul (contDiff_kC_apply hg 1 0)).add
    (contDiff_const.mul (contDiff_kC_apply hg 1 1))

-- pin: norm_iteratedFDeriv_radC_succ_le (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:208)
theorem norm_iteratedFDeriv_radC_succ_le (hg : g.det ≠ 0) (i : ℕ) (w : ℂ) {C : ℝ}
    (h10 : ‖iteratedFDeriv ℝ i (fun w => kC g w 1 0) w‖ ≤ C)
    (h11 : ‖iteratedFDeriv ℝ i (fun w => kC g w 1 1) w‖ ≤ C) :
    ‖iteratedFDeriv ℝ (i + 1) (radC g) w‖ ≤ ‖reFun‖ * ((‖g 1 0‖ + ‖g 1 1‖) * C) := by
  rw [← norm_iteratedFDeriv_fderiv, fderiv_radC hg]
  have hcomp : (fun w => reFun (slopeC g w)) = reFun ∘ slopeC g := rfl
  rw [hcomp]
  have hS : ContDiffAt ℝ (i : ℕ∞) (slopeC g) w :=
    ((contDiff_slopeC hg).of_le (mod_cast le_top)).contDiffAt
  refine (reFun.norm_iteratedFDeriv_comp_left hS le_rfl).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 : slopeC g = (fun w => conj (g 1 0) * kC g w 1 0) + fun w => conj (g 1 1) * kC g w 1 1 :=
    rfl
  have hA : ContDiffAt ℝ (i : ℕ∞) (fun w => conj (g 1 0) * kC g w 1 0) w :=
    ((contDiff_const.mul (contDiff_kC_apply hg 1 0)).of_le (mod_cast le_top)).contDiffAt
  have hB : ContDiffAt ℝ (i : ℕ∞) (fun w => conj (g 1 1) * kC g w 1 1) w :=
    ((contDiff_const.mul (contDiff_kC_apply hg 1 1)).of_le (mod_cast le_top)).contDiffAt
  have h10' : ContDiffAt ℝ (i : ℕ∞) (fun w => kC g w 1 0) w :=
    ((contDiff_kC_apply hg 1 0).of_le (mod_cast le_top)).contDiffAt
  have h11' : ContDiffAt ℝ (i : ℕ∞) (fun w => kC g w 1 1) w :=
    ((contDiff_kC_apply hg 1 1).of_le (mod_cast le_top)).contDiffAt
  rw [h1, iteratedFDeriv_add_apply hA hB]
  refine (norm_add_le _ _).trans ?_
  have e10 : (fun w => conj (g 1 0) * kC g w 1 0)
      = (ContinuousLinearMap.mul ℝ ℂ (conj (g 1 0))) ∘ (fun w => kC g w 1 0) := rfl
  have e11 : (fun w => conj (g 1 1) * kC g w 1 1)
      = (ContinuousLinearMap.mul ℝ ℂ (conj (g 1 1))) ∘ (fun w => kC g w 1 1) := rfl
  have n10 : ‖ContinuousLinearMap.mul ℝ ℂ (conj (g 1 0))‖ ≤ ‖g 1 0‖ :=
    (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ _).trans (le_of_eq (Complex.norm_conj _))
  have n11 : ‖ContinuousLinearMap.mul ℝ ℂ (conj (g 1 1))‖ ≤ ‖g 1 1‖ :=
    (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ _).trans (le_of_eq (Complex.norm_conj _))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans h10
  rw [e10, e11]
  calc ‖iteratedFDeriv ℝ i (⇑(ContinuousLinearMap.mul ℝ ℂ (conj (g 1 0))) ∘ fun w => kC g w 1 0) w‖
        + ‖iteratedFDeriv ℝ i (⇑(ContinuousLinearMap.mul ℝ ℂ (conj (g 1 1))) ∘ fun w => kC g w 1 1) w‖
      ≤ ‖ContinuousLinearMap.mul ℝ ℂ (conj (g 1 0))‖ * ‖iteratedFDeriv ℝ i (fun w => kC g w 1 0) w‖
        + ‖ContinuousLinearMap.mul ℝ ℂ (conj (g 1 1))‖ * ‖iteratedFDeriv ℝ i (fun w => kC g w 1 1) w‖ :=
        add_le_add (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ h10' le_rfl)
          (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ h11' le_rfl)
    _ ≤ ‖g 1 0‖ * C + ‖g 1 1‖ * C :=
        add_le_add (mul_le_mul n10 h10 (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul n11 h11 (norm_nonneg _) (norm_nonneg _))
    _ = (‖g 1 0‖ + ‖g 1 1‖) * C := by ring

-- pin: norm_iteratedFDeriv_cpow_neg_radC_le (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:298)
theorem norm_iteratedFDeriv_cpow_neg_radC_le (hg : g.det ≠ 0) (u : ℂ) (n : ℕ) {m D : ℝ}
    (hm : 0 < m) (hmle : ∀ z : ℂ, m ≤ radC g z)
    (hD : ∀ z : ℂ, ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (radC g) z‖ ≤ D ^ i) (z : ℂ) :
    ‖iteratedFDeriv ℝ n (fun w => ((radC g w : ℂ)) ^ (-u)) z‖
      ≤ n ! * (((‖u‖ + n + 1) ^ n) * (max 1 (2 / m)) ^ n * radC g z ^ (-u.re)) * D ^ n := by
  have hP : (0:ℝ) < (‖u‖ + n + 1) ^ n := pow_pos (by positivity) n
  have hrad := radC_pos hg z
  have hradm := hmle z
  have hm2 : m / 2 < radC g z := by nlinarith
  have hrange : Set.range (radC g)
      ⊆ Set.Ioi (m / 2) := by
    rintro y ⟨w, rfl⟩
    have h1 := hmle w
    exact Set.mem_Ioi.2 (by nlinarith [radC_pos hg w])
  have hgOn : ContDiffOn ℝ ∞ (fun y : ℝ => ((y : ℂ)) ^ (-u))
      (Set.Ioi (m / 2)) :=
    contDiffOn_ofReal_cpow_neg (by linarith) u
  have hC : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i (fun y : ℝ => ((y : ℂ)) ^ (-u))
          (Set.Ioi (m / 2)) (radC g z)‖
        ≤ ((‖u‖ + n + 1) ^ n)
          * (max 1 (2 / (m))) ^ n * radC g z ^ (-u.re) := by
    intro i hi
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    refine (norm_iteratedDerivWithin_ofReal_cpow_le (by linarith) u i
      (Set.mem_Ioi.2 hm2)).trans ?_
    have hsplit : radC g z ^ (-u.re - (i:ℝ))
        = radC g z ^ (-u.re) * (radC g z ^ ((i:ℝ)))⁻¹ := by
      rw [show -u.re - (i:ℝ) = -u.re + -(i:ℝ) from by ring, Real.rpow_add hrad,
        Real.rpow_neg hrad.le ((i:ℝ))]
    have hpowinv : (radC g z ^ ((i:ℝ)))⁻¹
        ≤ (max 1 (2 / (m))) ^ n := by
      rw [Real.rpow_natCast]
      have hmh : (0:ℝ) < (m / 2) ^ i :=
        pow_pos (by linarith) i
      have h1 : (m / 2) ^ i ≤ radC g z ^ i :=
        pow_le_pow_left₀ (by linarith) (by linarith) i
      have h2 := one_div_le_one_div_of_le hmh h1
      rw [one_div, one_div] at h2
      refine h2.trans ?_
      rw [← inv_pow, inv_div]
      exact (pow_le_pow_left₀ (by positivity) (le_max_right _ _) i).trans
        (pow_le_pow_right₀ (le_max_left _ _) hi)
    have hprod : (∏ j ∈ Finset.range i, (‖u‖ + (j:ℝ)))
        ≤ (‖u‖ + n + 1) ^ n := by
      have hstep1 : (∏ j ∈ Finset.range i, (‖u‖ + (j:ℝ)))
          ≤ ∏ _j ∈ Finset.range i, (‖u‖ + (n:ℝ) + 1) := by
        refine Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j hj => ?_)
        have hjn : (j:ℝ) ≤ (n:ℝ) := by
          exact_mod_cast le_of_lt (lt_of_lt_of_le (Finset.mem_range.1 hj) hi)
        linarith [norm_nonneg u]
      refine hstep1.trans ?_
      rw [Finset.prod_const, Finset.card_range]
      exact pow_le_pow_right₀ (by linarith [norm_nonneg u]) hi
    rw [hsplit]
    have hr0 : (0:ℝ) ≤ radC g z ^ (-u.re) := Real.rpow_nonneg hrad.le _
    calc (∏ j ∈ Finset.range i, (‖u‖ + (j:ℝ)))
          * (radC g z ^ (-u.re) * (radC g z ^ ((i:ℝ)))⁻¹)
        ≤ ((‖u‖ + n + 1) ^ n)
          * (radC g z ^ (-u.re)
            * (max 1 (2 / (m))) ^ n) :=
          mul_le_mul hprod (mul_le_mul_of_nonneg_left hpowinv hr0)
            (mul_nonneg hr0 (inv_nonneg.2 (Real.rpow_nonneg hrad.le _))) hP.le
      _ = ((‖u‖ + n + 1) ^ n)
          * (max 1 (2 / (m))) ^ n
          * radC g z ^ (-u.re) := by ring
  have hcomp := norm_iteratedFDeriv_comp_le' (𝕜 := ℝ) hrange isOpen_Ioi.uniqueDiffOn hgOn
    (contDiff_radC hg) (mod_cast le_top) z hC (hD z)
  have hfun : (fun w => ((radC g w : ℂ)) ^ (-u))
      = (fun y : ℝ => ((y : ℂ)) ^ (-u)) ∘ radC g := rfl
  rw [hfun]
  refine hcomp.trans (le_of_eq ?_)
  ring

-- pin: main (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:384)
theorem main (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (n : ℕ) :
    (∀ g ∈ 𝒢, ∀ u : ℂ, ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u)))) ∧
    ∃ K : ℝ, 0 < K ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) z‖ ≤ K * radC g z ^ (-u.re) := by
  refine ⟨fun g hg u => contDiff_cpow_neg_radC (hdet g hg) u, ?_⟩

  have hT : ∀ i : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ (k l : Fin 2) (z : ℂ),
      ‖iteratedFDeriv ℝ i (fun w => kC g w k l) z‖ ≤ C := fun i =>
    AutomorphicForm.ComplexIwasawa.Engine.exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact 𝒢 h𝒢 hdet i
  choose Ck hCk using hT

  obtain ⟨E₁, hE₁⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => g 1 0)
    (continuous_id.matrix_elem 1 0).continuousOn
  obtain ⟨E₂, hE₂⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => g 1 1)
    (continuous_id.matrix_elem 1 1).continuousOn

  obtain ⟨A₀, hA₀⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => botNormSqC g)
    continuous_botNormSqC.continuousOn
  obtain ⟨cD, hcD⟩ := h𝒢.exists_bound_of_continuousOn (f := fun g => ‖g.det‖⁻¹)
    (continuous_detC.continuousOn.norm.inv₀ fun g hg => (norm_pos_iff.2 (hdet g hg)).ne')

  obtain ⟨R₀, hR₀⟩ := hU.exists_bound_of_continuousOn (f := fun u : ℂ => u) continuous_id.continuousOn
  set E : ℝ := max 0 (max E₁ E₂) with hEdef
  set A₁ : ℝ := max 1 A₀ with hA₁def
  set d : ℝ := max 1 cD with hddef
  set R : ℝ := max 0 R₀ with hRdef
  set m₀ : ℝ := d⁻¹ / Real.sqrt A₁ with hm₀def
  set S : ℝ := ∑ i ∈ Finset.range n, Ck i with hSdef
  set D : ℝ := 1 + ‖reFun‖ * ((E + E) * S) with hDdef
  have hE0 : 0 ≤ E := le_max_left _ _
  have hA₁1 : 1 ≤ A₁ := le_max_left _ _
  have hd1 : 1 ≤ d := le_max_left _ _
  have hR0 : 0 ≤ R := le_max_left _ _
  have hm₀ : 0 < m₀ := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (hCk i).1.le
  have hD1 : 1 ≤ D := by
    have : 0 ≤ ‖reFun‖ * ((E + E) * S) := by positivity
    linarith
  have hMx : (0:ℝ) < max 1 (2 / m₀) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hfac : (0:ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  refine ⟨(n ! : ℝ) * ((R + n + 1) ^ n * (max 1 (2 / m₀)) ^ n) * D ^ n,
    mul_pos (mul_pos hfac (mul_pos (pow_pos (by positivity) n) (pow_pos hMx n)))
      (pow_pos (by linarith) n), fun g hg u hu z => ?_⟩
  have hg' : g.det ≠ 0 := hdet g hg

  have hApos := botNormSqC_pos hg'
  have hdet0 : 0 < ‖g.det‖ := norm_pos_iff.2 hg'
  have hAup : botNormSqC g ≤ A₁ := by
    have := hA₀ g hg
    rw [Real.norm_of_nonneg hApos.le] at this
    exact this.trans (le_max_right _ _)
  have hdinv : d⁻¹ ≤ ‖g.det‖ := by
    have h2 : ‖g.det‖⁻¹ ≤ d := by
      have := hcD g hg
      rw [norm_inv, norm_norm] at this
      exact this.trans (le_max_right _ _)
    exact (inv_le_comm₀ (by positivity) hdet0).mpr h2
  have hmle : ∀ w : ℂ, m₀ ≤ radC g w := by
    intro w
    refine le_trans ?_ (norm_det_div_sqrt_le_radC hg' w)
    exact div_le_div₀ (norm_nonneg _) hdinv (Real.sqrt_pos.2 hApos) (Real.sqrt_le_sqrt hAup)

  have hEc : ‖g 1 0‖ ≤ E := (hE₁ g hg).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hEd : ‖g 1 1‖ ≤ E := (hE₂ g hg).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hDg : ∀ w : ℂ, ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (radC g) w‖ ≤ D ^ i := by
    intro w i hi1 hin
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < n := by omega
    have hstep := norm_iteratedFDeriv_radC_succ_le hg' k w ((hCk k).2 g hg 1 0 w)
      ((hCk k).2 g hg 1 1 w)
    refine hstep.trans (le_trans ?_ (le_self_pow₀ hD1 (by omega)))
    have hCkS : Ck k ≤ S :=
      Finset.single_le_sum (f := Ck) (fun j _ => (hCk j).1.le) (Finset.mem_range.2 hk)
    have h1 : (‖g 1 0‖ + ‖g 1 1‖) * Ck k ≤ (E + E) * S :=
      mul_le_mul (add_le_add hEc hEd) hCkS (hCk k).1.le (by positivity)
    have h2 : ‖reFun‖ * ((‖g 1 0‖ + ‖g 1 1‖) * Ck k) ≤ ‖reFun‖ * ((E + E) * S) :=
      mul_le_mul_of_nonneg_left h1 (norm_nonneg reFun)
    linarith
  have key := norm_iteratedFDeriv_cpow_neg_radC_le hg' u n hm₀ hmle hDg z
  refine key.trans ?_
  have hr0 : (0:ℝ) ≤ radC g z ^ (-u.re) := Real.rpow_nonneg (radC_pos hg' z).le _
  have huR : ‖u‖ ≤ R := by
    have := hR₀ u hu
    exact this.trans (le_max_right _ _)
  have hpow : (‖u‖ + n + 1) ^ n ≤ (R + n + 1) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  have hrest : 0 ≤ (n ! : ℝ) * (max 1 (2 / m₀)) ^ n * D ^ n * radC g z ^ (-u.re) :=
    mul_nonneg (mul_nonneg (mul_nonneg hfac.le (pow_pos hMx n).le) (pow_pos (by linarith) n).le) hr0
  calc (n ! : ℝ) * ((‖u‖ + n + 1) ^ n * (max 1 (2 / m₀)) ^ n * radC g z ^ (-u.re)) * D ^ n
      = ((n ! : ℝ) * (max 1 (2 / m₀)) ^ n * D ^ n * radC g z ^ (-u.re)) * (‖u‖ + n + 1) ^ n := by
        ring
    _ ≤ ((n ! : ℝ) * (max 1 (2 / m₀)) ^ n * D ^ n * radC g z ^ (-u.re)) * (R + n + 1) ^ n :=
        mul_le_mul_of_nonneg_left hpow hrest
    _ = (n ! : ℝ) * ((R + n + 1) ^ n * (max 1 (2 / m₀)) ^ n) * D ^ n * radC g z ^ (-u.re) := by
        ring

end B2bCL1

namespace Engine

open MeasureTheory CplxSmooth Real VectorFourier Complex
open scoped FourierTransform

-- pin: contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact (S_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact.lean:487)
theorem contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (_hU : IsCompact U) (n : ℕ) :
    (∀ g ∈ 𝒢, ∀ u : ℂ, ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u)))) ∧
    ∃ K : ℝ, 0 < K ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) z‖ ≤ K * radC g z ^ (-u.re) :=
  B2bCL1.main 𝒢 _h𝒢 _hdet U _hU n

-- pin: exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact (S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact.lean:63)
theorem exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (h𝒢 : IsCompact 𝒢) (hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (U : Set ℂ) (hU : IsCompact U) (hU2 : ∀ u ∈ U, 2 < u.re)
    (P : Matrix (Fin 2) (Fin 2) ℂ → ℂ → ℂ) (hPC : ∀ g ∈ 𝒢, ContDiff ℝ ∞ (P g))
    (hPB : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ z : ℂ, ‖iteratedFDeriv ℝ n (P g) z‖ ≤ C)
    (L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c)
    (hL : ∀ ξ : ℂ, ∃ v : ℂ, ‖v‖ ≤ 1 ∧ c * ‖ξ‖ ≤ ‖L v ξ‖)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g ∈ 𝒢, ∀ u ∈ U, ∀ ξ : ℂ,
      ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
          (fun z => ((radC g z : ℂ) ^ (-u)) * P g z) ξ‖
        ≤ C * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by

  rcases U.eq_empty_or_nonempty with hUe | hUne
  · exact ⟨1, one_pos, fun g _ u hu => by simp [hUe] at hu⟩

  obtain ⟨R, hR⟩ := hU.exists_bound_of_continuousOn (f := fun u : ℂ => u) continuousOn_id
  obtain ⟨u₀, hu₀U, hu₀⟩ := hU.exists_isMinOn hUne Complex.continuous_re.continuousOn
  set κ₀ : ℝ := u₀.re with hκ₀
  have hκ₀2 : 2 < κ₀ := hU2 u₀ hu₀U
  set κ₁ : ℝ := max κ₀ R with hκ₁

  choose Ch hCh using hPB
  have hW := fun n => AutomorphicForm.ComplexIwasawa.Engine.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact
    𝒢 h𝒢 hdet U hU n
  have hWcd : ∀ g ∈ 𝒢, ∀ u : ℂ, ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) := (hW 0).1
  choose K hK0 hK using fun n => (hW n).2
  obtain ⟨J, hJ0, hJ⟩ := AutomorphicForm.ComplexIwasawa.Engine.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
    𝒢 h𝒢 hdet κ₀ κ₁ hκ₀2

  set D : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K i * Ch (n - i) with hD
  have hCh0 : ∀ m, 0 ≤ Ch m := fun m => (hCh m).1.le
  have hD0 : ∀ n, 0 ≤ D n := fun n =>
    Finset.sum_nonneg fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK0 i).le) (hCh0 _)
  set M0' : ℝ := D 0 * J with hM0'
  set MN' : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), D j * J with hMN'
  have hM0'0 : 0 ≤ M0' := mul_nonneg (hD0 0) hJ0.le
  have hMN'0 : 0 ≤ MN' := mul_nonneg (pow_nonneg (by norm_num) N)
    (Finset.sum_nonneg fun j _ => mul_nonneg (hD0 j) hJ0.le)
  refine ⟨(M0' * 2 ^ N + MN' * (2 / c) ^ N) + 1, by positivity, fun g hg u hu ξ => ?_⟩

  have huR : ‖u‖ ≤ R := by simpa using hR u hu
  have hure : κ₀ ≤ u.re := by have := hu₀ hu; simpa [hκ₀] using this
  have hure1 : u.re ≤ κ₁ := ((Complex.re_le_norm u).trans huR).trans (le_max_right _ _)
  have hrad0 : ∀ z : ℂ, 0 ≤ radC g z := fun z => Real.sqrt_nonneg _
  set f : ℂ → ℂ := fun z => ((radC g z : ℂ) ^ (-u)) * P g z with hfdef
  have hwC : ContDiff ℝ ∞ (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) := hWcd g hg u
  have hCB : ∀ n z, ‖iteratedFDeriv ℝ n f z‖ ≤ D n * radC g z ^ (-u.re) := by
    intro n z
    refine (norm_iteratedFDeriv_mul_le hwC (hPC g hg) z (mod_cast le_top)).trans ?_
    rw [hD]
    dsimp only
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    calc (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun z : ℂ => ((radC g z : ℂ) ^ (-u))) z‖
          * ‖iteratedFDeriv ℝ (n - i) (P g) z‖
        ≤ (n.choose i : ℝ) * (K i * radC g z ^ (-u.re)) * Ch (n - i) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hK i g hg u hu z) (Nat.cast_nonneg _))
            ((hCh (n - i)).2 g hg z) (norm_nonneg _) ?_
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hK0 i).le (Real.rpow_nonneg (hrad0 z) _))
      _ = (n.choose i : ℝ) * K i * Ch (n - i) * radC g z ^ (-u.re) := by ring
  obtain ⟨hintr, hintJ⟩ := hJ g hg u.re hure hure1
  have hfC : ContDiff ℝ ∞ f := hwC.mul (hPC g hg)
  have hfCn : ContDiff ℝ (N : ℕ∞) f := hfC.of_le (mod_cast le_top)
  have h'f : ∀ j : ℕ, j ≤ N → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) volume := by
    intro j _
    refine (hintr.const_mul (D j)).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (hfC.continuous_iteratedFDeriv (mod_cast le_top)).norm.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (norm_nonneg _)]
      exact hCB j z
  have hIj : ∀ j, ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume ≤ D j * J := by
    intro j
    calc ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume ≤ ∫ v, D j * radC g v ^ (-u.re) ∂volume :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => norm_nonneg _) (hintr.const_mul _)
            (Filter.Eventually.of_forall (hCB j))
      _ = D j * ∫ v, radC g v ^ (-u.re) ∂volume := integral_const_mul _ _
      _ ≤ D j * J := mul_le_mul_of_nonneg_left hintJ (hD0 j)

  have key := MeasureTheory.FourierDecay.pow_mul_norm_fourierIntegral_le_of_coercive L (f := f) hfCn h'f hc.le hL
  set MN : ℝ := 2 ^ N * ∑ j ∈ Finset.range (N + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂volume with hMN
  have hMNle : MN ≤ MN' :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hIj j) (pow_nonneg (by norm_num) N)
  have hMN0 : (0 : ℝ) ≤ MN :=
    mul_nonneg (pow_nonneg (by norm_num) N)
      (Finset.sum_nonneg fun j _ => integral_nonneg fun v => norm_nonneg _)
  have hfint : Integrable f volume := by
    refine (hintr.const_mul (D 0)).mono' hfC.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    have h0 := hCB 0 z
    rwa [norm_iteratedFDeriv_zero] at h0
  set M0 : ℝ := ∫ v, ‖f v‖ ∂volume with hM0
  have hM00 : (0 : ℝ) ≤ M0 := integral_nonneg fun v => norm_nonneg _
  have hM0le : M0 ≤ M0' := by
    have := hIj 0
    simp only [norm_iteratedFDeriv_zero] at this
    exact this
  have hξ0 : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg _
  have h1ξ : (0 : ℝ) < 1 + ‖ξ‖ := by linarith
  have hrpow0 : (0 : ℝ) < (1 + ‖ξ‖) ^ (-(N : ℝ)) := Real.rpow_pos_of_pos h1ξ _
  have hc2 : (0 : ℝ) ≤ (2 / c) ^ N := pow_nonneg (div_nonneg (by norm_num) hc.le) N
  rcases lt_or_ge ‖ξ‖ 1 with hlt | hge
  · have hbd : (2 : ℝ) ^ (-(N : ℝ)) ≤ (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos h1ξ (by linarith) (neg_nonpos_of_nonneg (Nat.cast_nonneg N))
    have hstep1 : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ M0 :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    have hstep2 : (M0' : ℝ) = M0' * 2 ^ N * (2 : ℝ) ^ (-(N : ℝ)) := by
      rw [mul_assoc, show ((2 : ℝ) ^ N : ℝ) = (2 : ℝ) ^ (N : ℝ) from (Real.rpow_natCast 2 N).symm,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel, Real.rpow_zero, mul_one]
    have hstep3 : M0' * 2 ^ N * (2 : ℝ) ^ (-(N : ℝ)) ≤ M0' * 2 ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_left hbd (mul_nonneg hM0'0 (pow_nonneg (by norm_num) N))
    have hstep4 : (M0' * 2 ^ N : ℝ) ≤ M0' * 2 ^ N + MN' * (2 / c) ^ N + 1 := by
      have := mul_nonneg hMN'0 hc2; linarith
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ M0' := hstep1.trans hM0le
      _ = M0' * 2 ^ N * (2 : ℝ) ^ (-(N : ℝ)) := hstep2
      _ ≤ M0' * 2 ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ)) := hstep3
      _ ≤ (M0' * 2 ^ N + MN' * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le
  · have hkey := key ξ
    have hcξ : (0 : ℝ) < c * ‖ξ‖ := mul_pos hc (by linarith)
    have hdiv : ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖ ≤ MN * (c * ‖ξ‖) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg hcξ.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hcξ N), mul_comm]
      exact hkey
    have h2 : (1 : ℝ) + ‖ξ‖ ≤ 2 * ‖ξ‖ := by linarith
    have hcmp : (c * ‖ξ‖) ^ (-(N : ℝ)) ≤ (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
      have hsplit : (c * ‖ξ‖ : ℝ) = (c / 2) * (2 * ‖ξ‖) := by ring
      rw [hsplit, Real.mul_rpow (div_nonneg hc.le (by norm_num)) (by linarith)]
      have hp1 : ((c / 2 : ℝ)) ^ (-(N : ℝ)) = (2 / c) ^ N := by
        rw [Real.rpow_neg (div_nonneg hc.le (by norm_num)), Real.rpow_natCast, ← inv_pow, inv_div]
      rw [hp1]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos h1ξ h2 (neg_nonpos_of_nonneg (Nat.cast_nonneg N))) hc2
    have hstep4 : (MN' * (2 / c) ^ N : ℝ) ≤ M0' * 2 ^ N + MN' * (2 / c) ^ N + 1 := by
      have := mul_nonneg hM0'0 (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N); linarith
    calc ‖VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂ f ξ‖
        ≤ MN * (c * ‖ξ‖) ^ (-(N : ℝ)) := hdiv
      _ ≤ MN' * ((2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ))) :=
          mul_le_mul hMNle hcmp (Real.rpow_nonneg hcξ.le _) hMN'0
      _ = MN' * (2 / c) ^ N * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by ring
      _ ≤ (M0' * 2 ^ N + MN' * (2 / c) ^ N + 1) * (1 + ‖ξ‖) ^ (-(N : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep4 hrpow0.le

end Engine


end AutomorphicForm.ComplexIwasawa

end
