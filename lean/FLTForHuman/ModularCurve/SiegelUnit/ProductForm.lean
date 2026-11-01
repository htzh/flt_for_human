/-
  The Siegel product form `u_μ Δ^t` on `Γ₁(N)`: its modularity and its two
  `q`-expansion conclusions.

  The subject is the product
  `u_μ τ = ∏_{r s : ZMod N} siegelFun N r s τ ^ (12 N m r s)` of Siegel units with
  the discriminant power `Δ^t`, and the three theorems are the pin's three layers of
  one story:

  * `exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` — under
    the positivity hypothesis `ht` on the weight `Ord β`, there is a `ModularForm` on
    `Γ₁(N)` of weight `12 t` whose value is the product, and every `S`-slash of it is
    `O (exp (-2π ((Ord β) / N + t) im))` at `i∞`;
  * `isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` —
    the width-`N` `q`-expansion of the `S`-slash `ϑ ∣[12t] S` has coefficients integral
    over `ℤ` after multiplying by `N ^ a`;
  * `qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow` — the
    width-`1` `q`-expansion of `ϑ` vanishes below the order `m₀`, is non-zero at `m₀`,
    and `N ^ a` times every coefficient (and the inverse of the `m₀` coefficient) is
    integral.

  The last two take the first theorem's conclusion as their hypothesis `hϑ`, so they are
  its consumers: the pin proves them in three files, the port states them once, in the
  pin's own order.

  Transcribed from the pin's three `S_` files,
  `P2M/Sol/S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean`
  (249 lines), `P2M/Sol/S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean`
  (469 lines) and
  `P2M/Sol/S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean`
  (457 lines), pinned `aa2d8b3`. The three statements are the `Theorems/` wrappers'
  verbatim; the proofs are the `S_` files' `solution` bodies, with the wrapper `solution`
  theorems folded into the headlines and the pin's `p2m_export`/`p2m_open`/`p2m_reactivate`
  prelude and its `attribute [-simp]` wall dropped. Everything below the three headlines
  is `private`, so the module's public surface is exactly the three theorems.

  The pin's seven type-only `def` matches in the port (`uFun → LevelN.jAnalytic`,
  `thetaFun → EIS2K1.qN`, `P144`/`P1728`/`deltaZ → e1Chi3`, `sigmaSeries → EtaQSeries.f`,
  `GammaS → CohCarrier.Gamma0Upper`) are **not** imports: they share a type, not a value,
  and the pin's own definitions are written here.

  FLT provenance, pinned `aa2d8b3`:
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean>
  spec-pin: Theorems/Thm_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean
  spec-pin: P2M/Sol/S_ModularCurve_SiegelUnit_exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean
  spec-pin: P2M/Sol/S_ModularCurve_SiegelUnit_isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean
  spec-pin: P2M/Sol/S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.SiegelUnit.Integrality
import FLTForHuman.ModularCurve.JqCoefficients
import FLTForHuman.NumberTheory.ModularForms.QExpansionCoeff
import FLTForHuman.ModularForms.Level.Gamma1Slash
import FLTForHuman.ModularForms.WeightOne.Defs.RatAt

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped Real Manifold MatrixGroups ModularForm Topology Pointwise

namespace ModularCurve

namespace SiegelUnit

local notation "Γ₁(" M ")" => ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-! ## The product form and its modularity (249) -/

namespace FORM

variable (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ)

/-- The Siegel product `∏_{r s} siegelFun N r s ^ (12 N m r s)`. -/
private noncomputable def uFun (τ : ℍ) : ℂ :=
  ∏ r : ZMod N, ∏ s : ZMod N, siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)

/-- The weight of the product form at `(x, y)`. -/
private def Ord (x y : ZMod N) : ℤ :=
  ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
    (6 * ((r * x + s * y).val : ℤ) ^ 2 - 6 * (N : ℤ) * ((r * x + s * y).val : ℤ) + (N : ℤ) ^ 2)

private noncomputable def thetaFun (t : ℕ) (τ : ℍ) : ℂ := uFun N m τ * ModularForm.discriminant τ ^ t

private theorem discr_slash (β : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (β • τ) * UpperHalfPlane.denom β τ ^ (-(12 : ℤ)) =
      ModularForm.discriminant τ := by
  have h := congrFun (SlashInvariantForm.slash_action_generators_SL2Z ModularForm.discriminant_S_invariant
    ModularForm.discriminant_T_invariant β) τ
  rwa [ModularForm.SL_slash_apply] at h

private theorem thetaFun_slash_apply (t : ℕ) (β : SL(2, ℤ)) (τ : ℍ) :
    ((thetaFun N m t) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) τ =
      uFun N m (β • τ) * ModularForm.discriminant τ ^ t := by
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, thetaFun, ← discr_slash β τ, mul_pow,
    mul_assoc]
  congr 2
  rw [← zpow_natCast (UpperHalfPlane.denom β τ ^ (-(12 : ℤ))) t, ← zpow_mul]
  congr 1

private def e00 (β : SL(2, ℤ)) : ZMod N := ((β 0 0 : ℤ) : ZMod N)
private def e01 (β : SL(2, ℤ)) : ZMod N := ((β 0 1 : ℤ) : ZMod N)
private def e10 (β : SL(2, ℤ)) : ZMod N := ((β 1 0 : ℤ) : ZMod N)
private def e11 (β : SL(2, ℤ)) : ZMod N := ((β 1 1 : ℤ) : ZMod N)

omit [NeZero N] in
private theorem det_rel (β : SL(2, ℤ)) : e00 N β * e11 N β - e01 N β * e10 N β = 1 := by
  have h := β.det_coe
  rw [Matrix.det_fin_two] at h
  have h' := congrArg (fun z : ℤ => (z : ZMod N)) h
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h'
  simpa [e00, e01, e10, e11] using h'

private def rowMul (β : SL(2, ℤ)) : ZMod N × ZMod N ≃ ZMod N × ZMod N where
  toFun p := (p.1 * e00 N β + p.2 * e10 N β, p.1 * e01 N β + p.2 * e11 N β)
  invFun p := (p.1 * e11 N β - p.2 * e10 N β, -(p.1 * e01 N β) + p.2 * e00 N β)
  left_inv p := by
    obtain ⟨r, s⟩ := p
    have h := det_rel N β
    ext
    · simp only; linear_combination r * h
    · simp only; linear_combination s * h
  right_inv p := by
    obtain ⟨x, y⟩ := p
    have h := det_rel N β
    ext
    · simp only; linear_combination x * h
    · simp only; linear_combination y * h

private def mT (β : SL(2, ℤ)) (r' s' : ZMod N) : ℕ :=
  m ((rowMul N β).symm (r', s')).1 ((rowMul N β).symm (r', s')).2

omit [NeZero N] in
private theorem mT_zero (hm0 : m 0 0 = 0) (β : SL(2, ℤ)) : mT N m β 0 0 = 0 := by
  have : (rowMul N β).symm (0, 0) = (0, 0) := by
    rw [Equiv.symm_apply_eq]; ext <;> simp [rowMul]
  simp [mT, this, hm0]

omit [NeZero N] in
private theorem mT_rowMul (β : SL(2, ℤ)) (r s : ZMod N) :
    mT N m β (rowMul N β (r, s)).1 (rowMul N β (r, s)).2 = m r s := by
  simp [mT]

private theorem idx_cast (r s : ZMod N) (a b : ℤ) :
    ((((r.val : ℤ) * a + (s.val : ℤ) * b : ℤ) : ZMod N).val : ℤ) =
      (((r * (a : ZMod N) + s * (b : ZMod N)) : ZMod N).val : ℤ) := by
  congr 2
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

private theorem uFun_smul (β : SL(2, ℤ)) (τ : ℍ) : uFun N m (β • τ) = uFun N (mT N m β) τ := by
  rw [uFun, (ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul N m).1 β τ, uFun]
  simp_rw [idx_cast]
  rw [← Fintype.prod_prod_type' (f := fun r s =>
      siegelFun N ((r * (↑(β 0 0) : ZMod N) + s * ↑(β 1 0)).val : ℤ)
        ((r * (↑(β 0 1) : ZMod N) + s * ↑(β 1 1)).val : ℤ) (τ : ℂ) ^ (12 * N * m r s)),
    ← Fintype.prod_prod_type' (f := fun r s =>
      siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * mT N m β r s))]
  refine Fintype.prod_equiv (rowMul N β) _ _ fun p => ?_
  obtain ⟨r, s⟩ := p
  rw [mT_rowMul]
  rfl

private theorem ord_eq (β : SL(2, ℤ)) :
    Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) =
      ∑ r : ZMod N, ∑ s : ZMod N, (mT N m β r s : ℤ) *
        (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) := by
  rw [Ord, ← Fintype.sum_prod_type' (f := fun r s => (m r s : ℤ) *
      (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
        - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) +
        (N : ℤ) ^ 2)),
    ← Fintype.sum_prod_type' (f := fun r s => (mT N m β r s : ℤ) *
      (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2))]
  refine Fintype.sum_equiv (rowMul N β) _ _ fun p => ?_
  obtain ⟨r, s⟩ := p
  rw [mT_rowMul]
  rfl

private theorem discr_isBigO :
    (fun τ : ℍ => ModularForm.discriminant τ) =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi) * τ.im) := by
  have h := CuspFormClass.exp_decay_atImInfty (h := 1) CuspForm.discriminant one_pos one_mem_strictPeriods_SL
  rw [CuspForm.coe_discriminant] at h
  refine h.congr_right fun τ => ?_
  congr 1
  ring

private theorem norm_C_eq_one {C : ℂ} (hC : C ^ N = 1) : ‖C‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one hC (NeZero.ne N)

private theorem thetaFun_slash_isBigO (hm0 : m 0 0 = 0) (t : ℕ) (β : SL(2, ℤ)) :
    ((thetaFun N m t) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) =O[atImInfty]
      fun τ : ℍ => Real.exp (-(2 * Real.pi *
        (((Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) / (N : ℝ) +
          (t : ℝ))) * τ.im) := by
  obtain ⟨C, d, hC, -, -, hd0, -, -, htend⟩ :=
    ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow N (mT N m β) (mT_zero N m hm0 β)
  set E : ℤ := ∑ r : ZMod N, ∑ s : ZMod N, (mT N m β r s : ℤ) *
    (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) with hE
  have hOrd : Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) = E := ord_eq N m β
  have hEC : ((∑ r : ZMod N, ∑ s : ZMod N,
      (mT N m β r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) +
        (N : ℤ) ^ 2)) : ℂ) = ((E : ℤ) : ℂ) := by
    rw [hE]; push_cast; rfl
  rw [hEC] at htend
  set L : ℍ → ℂ := fun τ =>
    C * Complex.exp (2 * Real.pi * Complex.I * ((E : ℤ) : ℂ) * (τ : ℂ) / (N : ℂ)) with hL
  set F : ℍ → ℂ := fun τ => (∏ r : ZMod N, ∏ s : ZMod N,
      siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * mT N m β r s)) / L τ with hF
  have hCne : C ≠ 0 := fun h0 => by
    rw [h0, zero_pow (NeZero.ne N)] at hC; exact zero_ne_one hC
  have hLne : ∀ τ, L τ ≠ 0 := fun τ => mul_ne_zero hCne (Complex.exp_ne_zero _)
  have hsplit : ∀ τ : ℍ,
      ((thetaFun N m t) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) τ =
        L τ * F τ * ModularForm.discriminant τ ^ t := by
    intro τ
    rw [thetaFun_slash_apply, uFun_smul, hF]
    simp only
    rw [mul_div_cancel₀ _ (hLne τ)]
    rfl
  have hLnorm : ∀ τ : ℍ, ‖L τ‖ = Real.exp (-(2 * Real.pi * ((E : ℝ) / (N : ℝ))) * τ.im) := by
    intro τ
    rw [hL]
    simp only [norm_mul, norm_C_eq_one N hC, one_mul, Complex.norm_exp]
    congr 1
    have : (2 * (Real.pi : ℂ) * Complex.I * (E : ℂ) * (τ : ℂ) / (N : ℂ)).re =
        -(2 * Real.pi * ((E : ℝ) / (N : ℝ))) * τ.im := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I * (E : ℂ) * (τ : ℂ) / (N : ℂ)) =
          ((2 * Real.pi * (E : ℝ) / (N : ℝ) : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) by
        push_cast; ring]
      rw [Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
      ring
    exact this
  have hLO : L =O[atImInfty] fun τ : ℍ => Real.exp (-(2 * Real.pi * ((E : ℝ) / (N : ℝ))) * τ.im) :=
    Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => by
      rw [hLnorm, one_mul, Real.norm_of_nonneg (Real.exp_nonneg _)])
  have hFO : F =O[atImInfty] (fun _ : ℍ => (1 : ℝ)) := htend.isBigO_one ℝ
  have hΔO : (fun τ : ℍ => ModularForm.discriminant τ ^ t) =O[atImInfty]
      fun τ : ℍ => Real.exp (-(2 * Real.pi) * τ.im) ^ t :=
    discr_isBigO.pow t
  have hprod := (hLO.mul hFO).mul hΔO
  refine (hprod.congr_left fun τ => (hsplit τ).symm).congr_right fun τ => ?_
  rw [mul_one, ← Real.exp_nat_mul, ← Real.exp_add, hOrd]
  congr 1
  ring

private theorem mdifferentiable_thetaFun (t : ℕ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (thetaFun N m t) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hΔ : DifferentiableOn ℂ (ModularForm.discriminant ∘ UpperHalfPlane.ofComplex)
      {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 CuspForm.discriminant.holo'
  have hu : DifferentiableOn ℂ (fun z : ℂ => ∏ r : ZMod N, ∏ s : ZMod N,
      siegelFun N (r.val : ℤ) (s.val : ℤ) z ^ (12 * N * m r s)) {z : ℂ | 0 < z.im} := by
    have h1 : ∀ r : ZMod N, DifferentiableOn ℂ (fun z : ℂ => ∏ s : ZMod N,
        siegelFun N (r.val : ℤ) (s.val : ℤ) z ^ (12 * N * m r s)) {z : ℂ | 0 < z.im} := fun r => by
      have h := DifferentiableOn.finsetProd (u := Finset.univ)
        (f := fun (s : ZMod N) (z : ℂ) => siegelFun N (r.val : ℤ) (s.val : ℤ) z ^ (12 * N * m r s))
        (fun s _ => ((ModularCurve.SiegelUnit.differentiableOn_siegelFun N (r.val : ℤ) (s.val : ℤ)).1).pow _)
      rwa [Finset.prod_fn] at h
    have h2 := DifferentiableOn.finsetProd (u := Finset.univ)
      (f := fun (r : ZMod N) (z : ℂ) => ∏ s : ZMod N,
        siegelFun N (r.val : ℤ) (s.val : ℤ) z ^ (12 * N * m r s)) (fun r _ => h1 r)
    rwa [Finset.prod_fn] at h2
  refine ((hu.mul (hΔ.pow t)).congr fun z hz => ?_)
  simp only [Function.comp_apply, thetaFun, uFun, UpperHalfPlane.ofComplex_apply_of_im_pos hz,
    Pi.mul_apply, Pi.pow_apply]

private noncomputable def theta (hm0 : m 0 0 = 0) (hm : ∀ r s : ZMod N, m r (s + r) = m r s) (t : ℕ)
    (ht : ∀ β : SL(2, ℤ),
      0 ≤ Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) + (N : ℤ) * t) :
    ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)) where
  toFun := thetaFun N m t
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    funext τ
    change ((thetaFun N m t) ∣[12 * (t : ℤ)] (γ : GL (Fin 2) ℝ)) τ = thetaFun N m t τ
    rw [thetaFun_slash_apply, thetaFun, uFun, uFun,
      (ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul N m).2 hm γ hγ τ]
  holo' := mdifferentiable_thetaFun N m t
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    have hO := thetaFun_slash_isBigO N m hm0 t γ
    rw [ModularForm.SL_slash]
    change Filter.BoundedAtFilter atImInfty ((thetaFun N m t) ∣[12 * (t : ℤ)] (γ : GL (Fin 2) ℝ))
    refine hO.trans (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_))
    have hpos : 0 ≤ (((Ord N m ((γ 0 0 : ℤ) : ZMod N) ((γ 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) / (N : ℝ) +
        (t : ℝ)) := by
      have h1 := ht γ
      have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.2 (NeZero.pos N)
      have h2 : (0 : ℝ) ≤ ((Ord N m ((γ 0 0 : ℤ) : ZMod N) ((γ 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) +
          (N : ℝ) * (t : ℝ) := by
        exact_mod_cast h1
      have : (((Ord N m ((γ 0 0 : ℤ) : ZMod N) ((γ 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) / (N : ℝ) +
          (t : ℝ)) =
          ((((Ord N m ((γ 0 0 : ℤ) : ZMod N) ((γ 1 0 : ℤ) : ZMod N) : ℤ) : ℝ) +
            (N : ℝ) * (t : ℝ))) / (N : ℝ) := by
        field_simp
      rw [this]
      exact div_nonneg h2 hNpos.le
    rw [Real.norm_of_nonneg (Real.exp_nonneg _), Pi.one_apply, norm_one, mul_one, Real.exp_le_one_iff,
      neg_mul]
    exact neg_nonpos.2 (mul_nonneg (mul_nonneg (by positivity) hpos) τ.im_pos.le)

private theorem theta_apply (hm0 : m 0 0 = 0) (hm : ∀ r s : ZMod N, m r (s + r) = m r s) (t : ℕ)
    (ht : ∀ β : SL(2, ℤ),
      0 ≤ Ord N m ((β 0 0 : ℤ) : ZMod N) ((β 1 0 : ℤ) : ZMod N) + (N : ℤ) * t) (τ : ℍ) :
    theta N m hm0 hm t ht τ = uFun N m τ * ModularForm.discriminant τ ^ t := rfl

end FORM

open scoped MatrixGroups ModularForm in
/-- **The Siegel product form on `Γ₁(N)`.**  There is a modular form of weight `12 t` on
`Γ₁(N)` equal to the Siegel product `∏_{r s} siegelFun N r s ^ (12 N m r s)` times `Δ ^ t`,
and each of its `S`-slashes decays at `i∞` at the rate `exp (-2π (Ord β / N + t) im)`. -/
theorem exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (hm0 : m 0 0 = 0)
    (hm : ∀ r s : ZMod N, m r (s + r) = m r s) (t : ℕ)
    (ht : ∀ β : SL(2, ℤ),
      0 ≤ (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
          (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
            - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) +
            (N : ℤ) ^ 2)) + (N : ℤ) * t) :
    ∃ ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)),
      (∀ τ : UpperHalfPlane, ϑ τ =
        (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
          ModularForm.discriminant τ ^ t) ∧
      ∀ β : SL(2, ℤ),
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
          fun τ : UpperHalfPlane =>
            Real.exp (-(2 * Real.pi *
              ((((∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
                (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
                  - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) +
                  (N : ℤ) ^ 2)) : ℤ) : ℝ) / (N : ℝ) + (t : ℝ))) * τ.im) := by
  exact ⟨FORM.theta N m hm0 hm t ht, fun τ => FORM.theta_apply N m hm0 hm t ht τ,
    fun β => FORM.thetaFun_slash_isBigO N m hm0 t β⟩

/-! ## The width-`N` integrality of the `S`-slash (469) -/

namespace IntZero

section Group

variable {N : ℕ}

theorem conj_mem_Gamma (α : SL(2, ℤ)) {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma N) :
    α * g * α⁻¹ ∈ CongruenceSubgroup.Gamma N :=
  (Gamma_normal N).conj_mem g hg α

theorem coeGL_mul (β γ : SL(2, ℤ)) :
    ((β * γ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ) * (γ : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) β γ

theorem coeGL_inv (β : SL(2, ℤ)) :
    ((β⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) = (β : GL (Fin 2) ℝ)⁻¹ :=
  map_inv (Matrix.SpecialLinearGroup.mapGL ℝ) β

/-- The `S`-conjugate of `Γ₁(N)`, read back inside `SL(2, ℤ)`. -/
def GammaS (N : ℕ) : Subgroup SL(2, ℤ) :=
  (ConjAct.toConjAct ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N)).comap
    (Matrix.SpecialLinearGroup.mapGL ℝ)

theorem mem_conj_iff (g x : GL (Fin 2) ℝ) (Γ : Subgroup (GL (Fin 2) ℝ)) :
    x ∈ ConjAct.toConjAct g⁻¹ • Γ ↔ g * x * g⁻¹ ∈ Γ := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]

theorem mem_GammaS_iff {γ : SL(2, ℤ)} :
    γ ∈ GammaS N ↔ ((ModularGroup.S * γ * ModularGroup.S⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈ Γ₁(N) := by
  rw [GammaS, Subgroup.mem_comap, mem_conj_iff, coeGL_mul, coeGL_mul, coeGL_inv]
  rfl

theorem mem_GammaS_of {γ : SL(2, ℤ)} (h : ModularGroup.S * γ * ModularGroup.S⁻¹ ∈ Gamma1 N) :
    γ ∈ GammaS N :=
  mem_GammaS_iff.mpr ⟨_, h, rfl⟩

theorem Gamma_le_GammaS (N : ℕ) : CongruenceSubgroup.Gamma N ≤ GammaS N := fun _ hγ =>
  mem_GammaS_of (ModularForm.Level.Gamma_le_Gamma1 N (conj_mem_Gamma ModularGroup.S hγ))

private instance instFiniteIndexGammaS (N : ℕ) [NeZero N] : (GammaS N).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaS N)

theorem T_pow_mem_Gamma (N : ℕ) : ModularGroup.T ^ N ∈ CongruenceSubgroup.Gamma N := by
  rw [Gamma_mem, ← zpow_natCast]
  simp only [ModularGroup.coe_T_zpow]
  simp

theorem T_pow_mem_GammaS (N : ℕ) : ModularGroup.T ^ N ∈ GammaS N :=
  Gamma_le_GammaS N (T_pow_mem_Gamma N)

theorem natCast_mem_strictPeriods_GammaS (N : ℕ) :
    (N : ℝ) ∈ ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T ^ N, T_pow_mem_GammaS N, ?_⟩
  apply Units.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    ← zpow_natCast, ModularGroup.coe_T_zpow]
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.upperRightHom_apply]

theorem GammaS_le_conjS (N : ℕ) :
    ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)⁻¹ • Γ₁(N) :=
  Subgroup.map_comap_le _ _

end Group

section Forms

/-- Restriction of scalars along an inclusion of level subgroups. -/
def restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ) (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

private theorem coe_restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ)
    (f : ModularForm Γ k) : (⇑(restrictMF h f) : ℍ → ℂ) = f := rfl

section

variable {N : ℕ} [NeZero N] {w : ℤ}

/-- The `S`-translate `ϑ ∣[w] S` as a form on `ΓS`. -/
def Thetaform (ϑ : ModularForm Γ₁(N) w) :
    ModularForm ((GammaS N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w :=
  restrictMF (GammaS_le_conjS N)
    (ModularForm.translate ϑ ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))

omit [NeZero N] in
theorem coe_Thetaform (ϑ : ModularForm Γ₁(N) w) :
    (⇑(Thetaform ϑ) : ℍ → ℂ) = (⇑ϑ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) :=
  rfl

end

private theorem natCast_pos {N : ℕ} [NeZero N] : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)

end Forms

section QSeries

private theorem hasSum_shift {q : ℂ} {b : ℕ → ℂ} {v : ℂ} (M : ℕ)
    (h : HasSum (fun n : ℕ => b n * q ^ (n + M)) v) :
    HasSum (fun n : ℕ => (if M ≤ n then b (n - M) else 0) * q ^ n) v := by
  set a : ℕ → ℂ := fun n => (if M ≤ n then b (n - M) else 0) * q ^ n with ha
  have h1 : (fun n : ℕ => a (n + M)) = fun n : ℕ => b n * q ^ (n + M) := by
    funext n
    simp [ha]
  have h2 : ∑ i ∈ Finset.range M, a i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : ¬ M ≤ i := Nat.not_le.mpr (Finset.mem_range.mp hi)
    simp [ha, hi']
  rw [← h1] at h
  have h3 := (hasSum_nat_add_iff (f := a) M).mp h
  rwa [h2, add_zero] at h3

private theorem hasSum_spread {q : ℂ} {c : ℕ → ℂ} {v : ℂ} (N : ℕ) (hN : 0 < N)
    (h : HasSum (fun k : ℕ => c k * (q ^ N) ^ k) v) :
    HasSum (fun n : ℕ => (if N ∣ n then c (n / N) else 0) * q ^ n) v := by
  have hinj : Function.Injective (fun k : ℕ => N * k) := fun a b hab =>
    Nat.eq_of_mul_eq_mul_left hN hab
  have key : (fun n : ℕ => (if N ∣ n then c (n / N) else 0) * q ^ n) =
      Function.extend (fun k : ℕ => N * k) (fun k : ℕ => c k * (q ^ N) ^ k) 0 := by
    funext n
    by_cases hn : N ∣ n
    · obtain ⟨k, rfl⟩ := hn
      rw [hinj.extend_apply]
      simp [Nat.mul_div_cancel_left k hN, pow_mul]
    · rw [Function.extend_apply' _ _ _ (by rintro ⟨k, rfl⟩; exact hn ⟨k, rfl⟩)]
      simp [hn]
  rw [key]
  exact (hasSum_extend_zero hinj).mpr h

private theorem qExpansion_coeff_eq_of_hasSum_div_qParam_zpow {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : ModularForm Γ k) (h : ℝ) (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (M : ℤ) (b : ℕ → ℂ)
    (hb0 : b 0 ≠ 0)
    (hb : ∀ τ : ℍ, HasSum (fun n : ℕ => b n * Periodic.qParam h (τ : ℂ) ^ n)
      (f τ / Periodic.qParam h (τ : ℂ) ^ M)) :
    0 ≤ M ∧ ∀ n : ℕ, (qExpansion h (⇑f : ℍ → ℂ)).coeff n =
      if M ≤ (n : ℤ) then b (n - M.toNat) else 0 := by
  have : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hq0 : ∀ τ : ℍ, Periodic.qParam h (τ : ℂ) ≠ 0 := fun τ => Periodic.qParam_ne_zero _
  have hf : ∀ τ : ℍ, HasSum (fun n : ℕ => (qExpansion h (⇑f : ℍ → ℂ)).coeff n *
      Periodic.qParam h (τ : ℂ) ^ n) (f τ) := fun τ => by
    simpa only [smul_eq_mul] using hasSum_qExpansion hh
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) f.holo' (ModularFormClass.bdd_at_infty f) τ
  rcases le_or_gt 0 M with hM | hM
  · obtain ⟨M', rfl⟩ := Int.eq_ofNat_of_zero_le hM
    refine ⟨hM, fun n => ?_⟩
    have hb' : ∀ τ : ℍ, HasSum (fun n : ℕ => (if M' ≤ n then b (n - M') else 0) *
        Periodic.qParam h (τ : ℂ) ^ n) (f τ) := fun τ => by
      refine hasSum_shift (b := b) M' ?_
      have h1 := (hb τ).mul_right (Periodic.qParam h (τ : ℂ) ^ M')
      rw [zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ (hq0 τ))] at h1
      (convert h1 using 1; try with_reducible_and_instances rfl)
      funext n
      rw [pow_add]
      ring
    have huniq := ModularCurve.qParam_coeff_unique h hh (⇑f) _ _ hf hb'
    rw [congr_fun huniq n]
    simp only [Int.toNat_natCast, Nat.cast_le]
  · exfalso
    obtain ⟨M', hM'⟩ := Int.exists_eq_neg_ofNat hM.le
    have hM'pos : 0 < M' := by omega
    have hb2 : ∀ τ : ℍ, HasSum (fun n : ℕ => b n * Periodic.qParam h (τ : ℂ) ^ n)
        (f τ * Periodic.qParam h (τ : ℂ) ^ M') := fun τ => by
      have h1 := hb τ
      rwa [hM', zpow_neg, zpow_natCast, div_inv_eq_mul] at h1
    have hf2 : ∀ τ : ℍ, HasSum (fun n : ℕ =>
        (if M' ≤ n then (qExpansion h (⇑f : ℍ → ℂ)).coeff (n - M') else 0) *
          Periodic.qParam h (τ : ℂ) ^ n) (f τ * Periodic.qParam h (τ : ℂ) ^ M') := fun τ => by
      refine hasSum_shift (b := fun n : ℕ => (qExpansion h (⇑f : ℍ → ℂ)).coeff n) M' ?_
      have h1 := (hf τ).mul_right (Periodic.qParam h (τ : ℂ) ^ M')
      (convert h1 using 1; try with_reducible_and_instances rfl)
      funext n
      rw [pow_add]
      ring
    have huniq := ModularCurve.qParam_coeff_unique h hh
      (fun τ : ℍ => f τ * Periodic.qParam h (τ : ℂ) ^ M') _ _ hf2 hb2
    have h0 := congr_fun huniq 0
    have : ¬ M' ≤ 0 := Nat.not_le.mpr hM'pos
    simp only [this, ite_false] at h0
    exact hb0 h0.symm

end QSeries

section Siegel

variable (N : ℕ)

private def uProd [NeZero N] (m : ZMod N → ZMod N → ℕ) (τ : ℍ) : ℂ :=
  ∏ r : ZMod N, ∏ s : ZMod N, siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)

private theorem siegelFun_zero_zero (z : ℂ) : siegelFun N 0 0 z = 0 := by
  simp [ModularCurve.siegelFun]

private theorem uProd_eq_zero [NeZero N] {m : ZMod N → ZMod N → ℕ} (hm : m 0 0 ≠ 0) (τ : ℍ) :
    uProd N m τ = 0 := by
  unfold uProd
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : ZMod N))
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : ZMod N))
  rw [ZMod.val_zero, Nat.cast_zero, siegelFun_zero_zero, zero_pow]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (NeZero.ne N)) hm

private theorem uProd_S_smul [NeZero N] (m : ZMod N → ZMod N → ℕ) (τ : ℍ) :
    uProd N m (ModularGroup.S • τ) = uProd N (fun r s => m (-s) r) τ := by
  have h := (ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul N m).1 ModularGroup.S τ
  have e00 : ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 0 := by
    rw [ModularGroup.coe_S]; rfl
  have e01 : ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -1 := by
    rw [ModularGroup.coe_S]; rfl
  have e10 : ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [ModularGroup.coe_S]; rfl
  have e11 : ((ModularGroup.S : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by
    rw [ModularGroup.coe_S]; rfl
  unfold uProd
  rw [h]
  simp only [e00, e01, e10, e11, mul_zero, zero_add, mul_one, add_zero, mul_neg, Int.cast_neg,
    Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  exact Fintype.prod_equiv (Equiv.neg (ZMod N)) _ _ (fun r => by simp)

private theorem slash_S_apply [NeZero N] (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm Γ₁(N) (12 * (t : ℤ)))
    (hϑ : ∀ τ : ℍ, ϑ τ = uProd N m τ * ModularForm.discriminant τ ^ t) (τ : ℍ) :
    ((⇑ϑ : ℍ → ℂ) ∣[12 * (t : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ =
      uProd N m (ModularGroup.S • τ) * ModularForm.discriminant τ ^ t := by
  have hz : ((τ : ℍ) : ℂ) ≠ 0 := τ.ne_zero
  have hS := congrFun ModularForm.discriminant_S_invariant τ
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S] at hS
  have hΔ : ModularForm.discriminant (ModularGroup.S • τ) =
      ModularForm.discriminant τ * (τ : ℂ) ^ (12 : ℕ) := by
    have h12 : ((τ : ℂ) ^ (-(12 : ℤ))) * (τ : ℂ) ^ (12 : ℕ) = 1 := by
      rw [zpow_neg, show ((12 : ℤ)) = ((12 : ℕ) : ℤ) by norm_num, zpow_natCast,
        inv_mul_cancel₀ (pow_ne_zero _ hz)]
    calc ModularForm.discriminant (ModularGroup.S • τ)
        = ModularForm.discriminant (ModularGroup.S • τ) *
            (((τ : ℂ) ^ (-(12 : ℤ))) * (τ : ℂ) ^ (12 : ℕ)) := by
          rw [h12, mul_one]
      _ = (ModularForm.discriminant (ModularGroup.S • τ) * (τ : ℂ) ^ (-(12 : ℤ))) *
            (τ : ℂ) ^ (12 : ℕ) := by
          ring
      _ = ModularForm.discriminant τ * (τ : ℂ) ^ (12 : ℕ) := by rw [hS]
  rw [← ModularForm.SL_slash, ModularForm.SL_slash_apply, ModularGroup.denom_S, hϑ, hΔ]
  have h2 : ((τ : ℂ) ^ (12 : ℕ)) ^ t * (τ : ℂ) ^ (-(12 * (t : ℤ))) = 1 := by
    rw [← pow_mul, zpow_neg, show (12 * (t : ℤ)) = ((12 * t : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hz)]
  rw [mul_pow]
  calc uProd N m (ModularGroup.S • τ) *
        (ModularForm.discriminant τ ^ t * ((τ : ℂ) ^ (12 : ℕ)) ^ t) * (τ : ℂ) ^ (-(12 * (t : ℤ)))
      = uProd N m (ModularGroup.S • τ) * ModularForm.discriminant τ ^ t *
          (((τ : ℂ) ^ (12 : ℕ)) ^ t * (τ : ℂ) ^ (-(12 * (t : ℤ)))) := by ring
    _ = uProd N m (ModularGroup.S • τ) * ModularForm.discriminant τ ^ t := by rw [h2, mul_one]

end Siegel

section Delta

private theorem qParam_one_eq_pow (N : ℕ) (hN : 0 < N) (z : ℂ) :
    Periodic.qParam 1 z = Periodic.qParam N z ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

private theorem hasSum_discriminant_pow (t : ℕ) (τ : ℍ) :
    HasSum (fun k : ℕ => ((PowerSeries.coeff k (etaProd ^ (24 * t)) : ℤ) : ℂ) *
        Periodic.qParam 1 (τ : ℂ) ^ k)
      (ModularForm.discriminant τ ^ t / Periodic.qParam 1 (τ : ℂ) ^ t) := by
  have hq : ‖Periodic.qParam 1 (τ : ℂ)‖ < 1 := by
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have h24 : Periodic.qParam 24 (τ : ℂ) ^ 24 = Periodic.qParam 1 (τ : ℂ) :=
    (qParam_one_eq_pow 24 (by norm_num) (τ : ℂ)).symm
  have hΔ : ModularForm.discriminant τ =
      Periodic.qParam 1 (τ : ℂ) * (∏' n : ℕ, (1 - Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ 24 := by
    simp only [ModularForm.discriminant, ModularForm.eta, ModularForm.eta_q, mul_pow, h24]
  have key : ModularForm.discriminant τ ^ t / Periodic.qParam 1 (τ : ℂ) ^ t =
      (∏' n : ℕ, (1 - Periodic.qParam 1 (τ : ℂ) ^ (n + 1))) ^ (24 * t) := by
    rw [hΔ, mul_pow, ← pow_mul,
      mul_div_cancel_left₀ _ (pow_ne_zero _ (Periodic.qParam_ne_zero _))]
  rw [key]
  exact ModularCurve.hasSum_coeff_etaProd_pow (24 * t) hq

end Delta

section Main

variable (N : ℕ) [NeZero N]

private theorem isIntegral_intCast (z : ℤ) : IsIntegral ℤ (z : ℂ) := by
  have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := z)
  simpa using this

private theorem main (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm Γ₁(N) (12 * (t : ℤ)))
    (hϑ : ∀ τ : ℍ, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) (n : ℕ) :
    IsIntegral ℤ ((qExpansion (N : ℝ) (⇑(Thetaform ϑ) : ℍ → ℂ)).coeff n) := by
  have hN : 0 < N := NeZero.pos N
  have hϑ' : ∀ τ : ℍ, ϑ τ = uProd N m τ * ModularForm.discriminant τ ^ t := hϑ
  set Θ := Thetaform ϑ with hΘdef
  have hΘ : ∀ τ : ℍ, Θ τ = uProd N m (ModularGroup.S • τ) * ModularForm.discriminant τ ^ t :=
    fun τ => slash_S_apply N m t ϑ hϑ' τ
  by_cases hm : m 0 0 = 0
  swap
  ·
    have hΘ0 : ∀ τ : ℍ, Θ τ = 0 := fun τ => by
      rw [hΘ, uProd_eq_zero N hm, zero_mul]
    have hs : ∀ τ : ℍ, HasSum (fun k : ℕ => (fun _ : ℕ => (0 : ℂ)) k •
        Periodic.qParam (N : ℝ) (τ : ℂ) ^ k) (Θ τ) := fun τ => by
      simp [hΘ0 τ]
    have h0 := ModularFormClass.qExpansion_coeff_unique natCast_pos
      (natCast_mem_strictPeriods_GammaS N) (f := Θ) hs n
    rw [← h0]
    exact isIntegral_zero
  ·
    set e : ZMod N → ZMod N → ℕ := fun r s => m (-s) r with he_def
    have he : e 0 0 = 0 := by simp [he_def, hm]
    obtain ⟨C, d, hCN, hdint, -, hd0, -, hsum, -⟩ :=
      ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow N e he
    set Ord : ℤ := ∑ r : ZMod N, ∑ s : ZMod N,
      (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) with hOrd
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hCN
      exact zero_ne_one hCN
    have hCint : IsIntegral ℤ C :=
      IsIntegral.of_pow hN (by rw [hCN]; exact isIntegral_one)
    set qN : ℍ → ℂ := fun τ => Periodic.qParam (N : ℝ) (τ : ℂ) with hqN
    have hqN0 : ∀ τ : ℍ, qN τ ≠ 0 := fun τ => Periodic.qParam_ne_zero _
    have hqn : ∀ (τ : ℍ) (k : ℕ),
        cexp (2 * π * Complex.I * (k : ℂ) * (τ : ℂ) / (N : ℂ)) = qN τ ^ k := fun τ k => by
      change _ = cexp (2 * π * Complex.I * (τ : ℂ) / ((N : ℝ) : ℂ)) ^ k
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hOrdC : (∑ r : ZMod N, ∑ s : ZMod N, ((e r s : ℤ) : ℂ) *
        (6 * ((r.val : ℤ) : ℂ) ^ 2 - 6 * ((N : ℤ) : ℂ) * ((r.val : ℤ) : ℂ) + ((N : ℤ) : ℂ) ^ 2)) =
        ((Ord : ℤ) : ℂ) := by
      rw [hOrd]
      norm_cast
    have hqZ : ∀ τ : ℍ,
        cexp (2 * π * Complex.I * (∑ r : ZMod N, ∑ s : ZMod N, ((e r s : ℤ) : ℂ) *
          (6 * ((r.val : ℤ) : ℂ) ^ 2 - 6 * ((N : ℤ) : ℂ) * ((r.val : ℤ) : ℂ) +
            ((N : ℤ) : ℂ) ^ 2)) * (τ : ℂ) / (N : ℂ)) = qN τ ^ Ord := fun τ => by
      rw [hOrdC]
      change _ = cexp (2 * π * Complex.I * (τ : ℂ) / ((N : ℝ) : ℂ)) ^ Ord
      rw [← Complex.exp_int_mul]
      congr 1
      push_cast
      ring
    have hu : ∀ τ : ℍ, HasSum (fun k : ℕ => (C * d k) * qN τ ^ k) (uProd N e τ / qN τ ^ Ord) :=
      fun τ => by
      have h1 := (hsum τ).mul_left C
      (convert h1 using 1; try with_reducible_and_instances rfl)
      · funext k
        rw [hqn]
        ring
      · change uProd N e τ / qN τ ^ Ord = C * (uProd N e τ / (C * _))
        rw [hqZ]
        field_simp
    set cN : ℕ → ℂ := fun k =>
      if N ∣ k then ((PowerSeries.coeff (k / N) (etaProd ^ (24 * t)) : ℤ) : ℂ) else 0 with hcN
    have hΔ : ∀ τ : ℍ, HasSum (fun k : ℕ => cN k * qN τ ^ k)
        (ModularForm.discriminant τ ^ t / qN τ ^ (N * t)) := fun τ => by
      have h1 := hasSum_discriminant_pow t τ
      rw [qParam_one_eq_pow N hN (τ : ℂ)] at h1
      have h2 := hasSum_spread (q := qN τ)
        (c := fun k : ℕ => ((PowerSeries.coeff k (etaProd ^ (24 * t)) : ℤ) : ℂ)) N hN h1
      rwa [← pow_mul] at h2
    set A : PowerSeries ℂ := PowerSeries.mk fun k => C * d k with hA
    set B : PowerSeries ℂ := PowerSeries.mk cN with hB
    have hAB : ∀ τ : ℍ, HasSum (fun k : ℕ => PowerSeries.coeff k (A * B) * qN τ ^ k)
        (Θ τ / qN τ ^ (Ord + ((N * t : ℕ) : ℤ))) := fun τ => by
      have h1 := ModularCurve.hasSum_qParam_mul (N : ℝ) natCast_pos A B
        (fun τ => uProd N e τ / qN τ ^ Ord)
        (fun τ => ModularForm.discriminant τ ^ t / qN τ ^ (N * t))
        (fun τ => by simpa only [hA, PowerSeries.coeff_mk] using hu τ)
        (fun τ => by simpa only [hB, PowerSeries.coeff_mk] using hΔ τ) τ
      have h2 : Θ τ = uProd N e τ * ModularForm.discriminant τ ^ t := by
        rw [hΘ, uProd_S_smul]
      convert h1 using 1
      rw [zpow_add₀ (hqN0 τ), zpow_natCast, div_mul_div_comm, h2]
    have hcN0 : cN 0 = 1 := by
      simp [hcN, PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_etaProd]
    have hb0 : PowerSeries.coeff 0 (A * B) ≠ 0 := by
      rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
      simp only [hA, hB, PowerSeries.coeff_mk, hcN0, mul_one]
      exact mul_ne_zero hC0 hd0
    have hcNint : ∀ k : ℕ, IsIntegral ℤ (cN k) := fun k => by
      simp only [hcN]
      split_ifs
      · exact isIntegral_intCast _
      · exact isIntegral_zero
    have hABint : ∀ k : ℕ, IsIntegral ℤ (PowerSeries.coeff k (A * B)) := fun k => by
      rw [PowerSeries.coeff_mul]
      refine IsIntegral.sum _ fun p _ => ?_
      simp only [hA, hB, PowerSeries.coeff_mk]
      exact (hCint.mul (hdint _)).mul (hcNint _)
    obtain ⟨-, hcoeff⟩ := qExpansion_coeff_eq_of_hasSum_div_qParam_zpow Θ (N : ℝ) natCast_pos
      (natCast_mem_strictPeriods_GammaS N) (Ord + ((N * t : ℕ) : ℤ))
      (fun k => PowerSeries.coeff k (A * B)) hb0 hAB
    rw [hcoeff n]
    split_ifs
    · exact hABint _
    · exact isIntegral_zero

end Main

end IntZero

open scoped MatrixGroups ModularForm in
/-- **The width-`N` integrality of the `S`-slash.**  For a `Γ₁(N)`-form `ϑ` equal to the
Siegel product, the coefficients of the width-`N` `q`-expansion of its `S`-slash are
integral over `ℤ` after multiplication by a fixed power of `N`. -/
theorem isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (t : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t) :
    ∃ a : ℕ, ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
      ((⇑ϑ : UpperHalfPlane → ℂ) ∣[12 * (t : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n) := by
  refine ⟨0, fun n => ?_⟩
  rw [pow_zero, one_mul]
  exact IntZero.main N m t ϑ hϑ n

/-! ## The width-`1` `q`-expansion at `m₀` (457) -/

namespace DeltaQExpInt

open UpperHalfPlane ModularForm EisensteinSeries PowerSeries
open scoped MatrixGroups ArithmeticFunction.sigma

private def sigmaSeries (k : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (σ k n : ℤ)

private theorem coeff_sigmaSeries (k n : ℕ) :
    coeff n (sigmaSeries k) = if n = 0 then 0 else (σ k n : ℤ) := by
  simp [sigmaSeries]

private def E4Z : PowerSeries ℤ := 1 + C 240 * sigmaSeries 3

private def E6Z : PowerSeries ℤ := 1 - C 504 * sigmaSeries 5

private theorem qExpansion_E₄_eq_map : qExpansion 1 E₄ = map (Int.castRingHom ℂ) E4Z := by
  ext m
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, show _root_.bernoulli 4 = -1 / 30 by decide +kernel, E4Z,
    map_add, map_one, map_mul, PowerSeries.map_C, map_add, coeff_C_mul, coeff_map, coeff_one,
    coeff_sigmaSeries, eq_intCast, eq_intCast]
  split_ifs <;> push_cast <;> ring

private theorem qExpansion_E₆_eq_map : qExpansion 1 E₆ = map (Int.castRingHom ℂ) E6Z := by
  ext m
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, show _root_.bernoulli 6 = 1 / 42 by decide +kernel, E6Z,
    map_sub, map_one, map_mul, PowerSeries.map_C, map_sub, coeff_C_mul, coeff_map, coeff_one,
    coeff_sigmaSeries, eq_intCast, eq_intCast]
  split_ifs <;> push_cast <;> ring

private def P144 : PowerSeries ℤ := C 5 * sigmaSeries 3 + C 7 * sigmaSeries 5

private def P1728 : PowerSeries ℤ :=
  C 100 * sigmaSeries 3 ^ 2 + C 8000 * sigmaSeries 3 ^ 3 - C 147 * sigmaSeries 5 ^ 2

private theorem E4Z_cube_sub_E6Z_sq : E4Z ^ 3 - E6Z ^ 2 = C 144 * P144 + C 1728 * P1728 := by
  simp only [E4Z, E6Z, P144, P1728]
  have h : ∀ a : ℤ, (C a : PowerSeries ℤ) = (a : PowerSeries ℤ) := fun a => by simp
  simp only [h]
  push_cast
  ring

private theorem twelve_dvd (d : ℕ) : (12 : ℤ) ∣ 5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5 := by
  have h : ∀ e : ZMod 12, 5 * e ^ 3 + 7 * e ^ 5 = 0 := by decide
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) 12).mp
  push_cast
  exact h _

private theorem twelve_dvd_coeff_P144 (n : ℕ) : (12 : ℤ) ∣ coeff n P144 := by
  simp only [P144, map_add, coeff_C_mul, coeff_sigmaSeries]
  split_ifs with hn
  · simp
  · rw [ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.dvd_sum fun d _ => twelve_dvd d

private def deltaZ : PowerSeries ℤ :=
  PowerSeries.mk fun n => coeff n P144 / 12 + coeff n P1728

private theorem C_mul_deltaZ : C 1728 * deltaZ = E4Z ^ 3 - E6Z ^ 2 := by
  rw [E4Z_cube_sub_E6Z_sq]
  ext n
  simp only [deltaZ, coeff_C_mul, coeff_mk, map_add]
  have h := Int.mul_ediv_cancel' (twelve_dvd_coeff_P144 n)
  linear_combination (144 : ℤ) * h

private theorem qExpansion_discriminant_eq :
    qExpansion 1 ModularForm.discriminant =
      (1728 : ℂ)⁻¹ • (qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2) := by
  set G : ModularForm 𝒮ℒ 12 :=
    ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2) with hG
  have hGq : qExpansion 1 G = qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
    simp only [hG, FunLike.coe_sub, coe_mcast,
      ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  have hcoe : (ModularForm.discriminant : UpperHalfPlane → ℂ) = (1728 : ℂ)⁻¹ • (⇑G) := by
    ext z
    simp only [hG, Pi.smul_apply, FunLike.coe_sub, ModularForm.coe_mcast, ModularForm.coe_pow,
      Pi.sub_apply, Pi.pow_apply, smul_eq_mul, discriminant_eq_E₄_cube_sub_E₆_sq z]
    ring
  rw [hcoe, UpperHalfPlane.qExpansion_smul
    (ModularFormClass.analyticAt_cuspFunction_zero G one_pos one_mem_strictPeriods_SL), hGq]

private theorem discriminant_qExpansion_coeff_eq_intCast (n : ℕ) :
    (qExpansion 1 ModularForm.discriminant).coeff n = ((coeff n deltaZ : ℤ) : ℂ) := by
  rw [qExpansion_discriminant_eq, qExpansion_E₄_eq_map, qExpansion_E₆_eq_map, ← map_pow, ← map_pow,
    ← map_sub, ← C_mul_deltaZ, map_mul, PowerSeries.map_C, map_smul, coeff_C_mul, coeff_map,
    smul_eq_mul, eq_intCast, eq_intCast]
  push_cast
  ring

private theorem exists_int_discriminant_qExpansion_coeff (n : ℕ) :
    ∃ z : ℤ, (qExpansion 1 ModularForm.discriminant).coeff n = (z : ℂ) :=
  ⟨_, discriminant_qExpansion_coeff_eq_intCast n⟩

private theorem discriminant_qExpansion_coeff_zero :
    (qExpansion 1 ModularForm.discriminant).coeff 0 = 0 := by
  simpa using CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

private theorem coeff_zero_deltaZ : coeff 0 deltaZ = 0 := by
  have h := discriminant_qExpansion_coeff_eq_intCast 0
  rw [discriminant_qExpansion_coeff_zero] at h
  exact_mod_cast h.symm

private theorem coeff_one_deltaZ : coeff 1 deltaZ = 1 := by
  have h := discriminant_qExpansion_coeff_eq_intCast 1
  rw [ModularForm.discriminant_qExpansion_coeff_one] at h
  exact_mod_cast h.symm

end DeltaQExpInt

namespace INTINF

open Complex UpperHalfPlane PowerSeries Filter Topology

local notation "𝕢" => Function.Periodic.qParam

private def EvA (S : PowerSeries ℂ) (q v : ℂ) : Prop :=
  HasSum (fun n : ℕ => coeff n S * q ^ n) v ∧ Summable fun n : ℕ => ‖coeff n S * q ^ n‖

private theorem EvA.mul {S T : PowerSeries ℂ} {q v w : ℂ} (hS : EvA S q v) (hT : EvA T q w) :
    EvA (S * T) q (v * w) := by
  have key : ∀ n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (coeff kl.1 S * q ^ kl.1) * (coeff kl.2 T * q ^ kl.2) = coeff n (S * T) * q ^ n := by
    intro n
    rw [coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm hS.2 hT.2
  refine ⟨?_, by simpa only [key] using hsum⟩
  have h1 := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hS.2 hT.2
  rw [hS.1.tsum_eq, hT.1.tsum_eq] at h1
  have h3 := hsum.of_norm.hasSum
  rw [← h1] at h3
  simpa only [key] using h3

private theorem EvA_X_pow (q : ℂ) (k : ℕ) : EvA (X ^ k) q (q ^ k) := by
  have hf : (fun n : ℕ => coeff n ((X : PowerSeries ℂ) ^ k) * q ^ n) =
      fun n => if n = k then q ^ k else 0 := by
    funext n
    rw [coeff_X_pow]
    split_ifs with h
    · rw [h, one_mul]
    · rw [zero_mul]
  have hg : (fun n : ℕ => ‖coeff n ((X : PowerSeries ℂ) ^ k) * q ^ n‖) =
      fun n => if n = k then ‖q ^ k‖ else 0 := by
    funext n
    rw [congrFun hf n]
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [hf]; exact hasSum_ite_eq k (q ^ k)
  · rw [hg]; exact (hasSum_ite_eq k ‖q ^ k‖).summable

private theorem EvA_one (q : ℂ) : EvA 1 q 1 := by
  simpa using EvA_X_pow q 0

private theorem EvA.pow {S : PowerSeries ℂ} {q v : ℂ} (hS : EvA S q v) : ∀ n : ℕ, EvA (S ^ n) q (v ^ n)
  | 0 => by simpa using EvA_one q
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (EvA.pow hS n).mul hS

private theorem EvA.smul {S : PowerSeries ℂ} {q v : ℂ} (hS : EvA S q v) (c : ℂ) :
    EvA (c • S) q (c * v) := by
  refine ⟨?_, ?_⟩
  · have := hS.1.mul_left c
    simpa only [coeff_smul, smul_eq_mul, mul_assoc] using this
  · have := hS.2.mul_left ‖c‖
    refine this.congr fun n => ?_
    simp only [coeff_smul, smul_eq_mul, norm_mul, mul_assoc]

private theorem EvA_of_forall_hasSum {S : PowerSeries ℂ} {F : ℍ → ℂ} {h : ℝ} (hh : 0 < h)
    (hF : ∀ τ : ℍ, HasSum (fun n : ℕ => coeff n S * 𝕢 h τ ^ n) (F τ)) (τ : ℍ) :
    EvA S (𝕢 h τ) (F τ) := by
  refine ⟨hF τ, ?_⟩
  let τ' : ℍ := ⟨(τ : ℂ) / 2, by rw [Complex.div_ofNat_im]; exact half_pos τ.im_pos⟩
  have hq : 𝕢 h τ = 𝕢 h τ' ^ 2 := by
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    change 2 * ↑Real.pi * Complex.I * (τ : ℂ) / h =
      ((2 : ℕ) : ℂ) * (2 * ↑Real.pi * Complex.I * ((τ : ℂ) / 2) / h)
    push_cast
    ring
  obtain ⟨M, hM⟩ := (hF τ').summable.tendsto_atTop_zero.norm.bddAbove_range
  have hM' : ∀ n, ‖coeff n S * 𝕢 h τ' ^ n‖ ≤ M := fun n => hM ⟨n, rfl⟩
  have hr : ‖𝕢 h τ'‖ < 1 := by
    rw [Function.Periodic.norm_qParam, Real.exp_lt_one_iff]
    have : 0 < 2 * Real.pi * (τ' : ℂ).im / h := by
      have := τ'.im_pos
      rw [UpperHalfPlane.im] at this
      positivity
    have e : -2 * Real.pi * (τ' : ℂ).im / h = -(2 * Real.pi * (τ' : ℂ).im / h) := by ring
    rw [e]
    linarith
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg _) hr).mul_left M)
  rw [hq, ← pow_mul, mul_comm 2 n, pow_mul, sq, ← mul_assoc, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hM' n) (pow_nonneg (norm_nonneg _) n)

private theorem qParam_natCast_pow (N : ℕ) (τ : ℍ) (n : ℕ) :
    𝕢 (N : ℝ) τ ^ n = cexp (2 * Real.pi * Complex.I * (n : ℂ) * (τ : ℂ) / (N : ℂ)) := by
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem qParam_natCast_zpow (N : ℕ) (τ : ℍ) (z : ℤ) :
    𝕢 (N : ℝ) τ ^ z = cexp (2 * Real.pi * Complex.I * (z : ℂ) * (τ : ℂ) / (N : ℂ)) := by
  rw [Function.Periodic.qParam, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

private theorem strictPeriods_Gamma1 (N : ℕ) :
    ((CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods =
      AddSubgroup.zmultiples 1 :=
  Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (ModularForm.Level.T_mem_Gamma1 N)

private theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

private theorem natCast_mem_strictPeriods_Gamma1 (N n : ℕ) :
    (n : ℝ) ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact ⟨n, by simp⟩

private def deltaN (N : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun i =>
    if N ∣ i then ((coeff (i / N + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) else 0

private theorem coeff_deltaN (N i : ℕ) :
    coeff i (deltaN N) =
      if N ∣ i then ((coeff (i / N + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) else 0 := by
  rw [deltaN, coeff_mk]

private theorem constantCoeff_deltaN (N : ℕ) : constantCoeff (deltaN N) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_deltaN, ite_eq_left (dvd_zero N), Nat.zero_div, zero_add,
    DeltaQExpInt.coeff_one_deltaZ, Int.cast_one]

private theorem qParam_one_eq_pow (N : ℕ) [NeZero N] (τ : ℍ) : 𝕢 1 τ = 𝕢 (N : ℝ) τ ^ N :=
  X1DiamondRational.qParam_one_eq_pow N τ

private theorem hasSum_discriminant (τ : ℍ) :
    HasSum (fun n : ℕ => ((coeff n DeltaQExpInt.deltaZ : ℤ) : ℂ) * 𝕢 1 τ ^ n)
      (ModularForm.discriminant τ) := by
  have h := UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex (f := CuspForm.discriminant)
      one_mem_strictPeriods_SL)
    (ModularFormClass.holo CuspForm.discriminant) (ModularFormClass.bdd_at_infty CuspForm.discriminant) τ
  refine h.congr_fun fun n => ?_
  rw [CuspForm.coe_discriminant, DeltaQExpInt.discriminant_qExpansion_coeff_eq_intCast, smul_eq_mul]

private theorem EvA_deltaN (N : ℕ) [NeZero N] (τ : ℍ) :
    EvA (deltaN N) (𝕢 (N : ℝ) τ) (ModularForm.discriminant τ / 𝕢 (N : ℝ) τ ^ N) := by
  have hN : 0 < N := NeZero.pos N
  refine EvA_of_forall_hasSum (F := fun τ : ℍ => ModularForm.discriminant τ / 𝕢 (N : ℝ) τ ^ N)
    (Nat.cast_pos.mpr hN) (fun τ => ?_) τ
  set q := 𝕢 (N : ℝ) τ with hqdef
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have h1 := hasSum_discriminant τ
  rw [qParam_one_eq_pow N τ, ← hqdef] at h1
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  rw [Finset.sum_range_one, pow_zero, mul_one, DeltaQExpInt.coeff_zero_deltaZ, Int.cast_zero,
    sub_zero] at h2
  have h3 : HasSum (fun j : ℕ => ((coeff (j + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) * q ^ (N * j))
      (ModularForm.discriminant τ / q ^ N) := by
    have e : (fun j : ℕ => ((coeff (j + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) * q ^ (N * j)) =
        fun j : ℕ => ((coeff (j + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) * (q ^ N) ^ (j + 1) / q ^ N := by
      funext j
      rw [pow_succ, ← mul_assoc, mul_div_assoc, div_self (pow_ne_zero _ hq0), mul_one, ← pow_mul]
    rw [e]
    exact h2.div_const (q ^ N)
  have hinj : Function.Injective fun j : ℕ => N * j := fun a b hab =>
    Nat.eq_of_mul_eq_mul_left hN hab
  refine (hinj.hasSum_iff ?_).mp ?_
  · intro i hi
    rw [coeff_deltaN, ite_eq_right, zero_mul]
    rintro ⟨j, rfl⟩
    exact hi ⟨j, rfl⟩
  · have e : ((fun i : ℕ => coeff i (deltaN N) * q ^ i) ∘ fun j : ℕ => N * j) =
        fun j : ℕ => ((coeff (j + 1) DeltaQExpInt.deltaZ : ℤ) : ℂ) * q ^ (N * j) := by
      funext j
      simp only [Function.comp_apply, coeff_deltaN, ite_eq_left (dvd_mul_right N j),
        Nat.mul_div_cancel_left j hN]
    rw [e]
    exact h3

private def CoeffMem (A : Subalgebra ℤ ℂ) (S : PowerSeries ℂ) : Prop := ∀ n : ℕ, coeff n S ∈ A

private theorem CoeffMem.mul {A : Subalgebra ℤ ℂ} {S T : PowerSeries ℂ} (hS : CoeffMem A S)
    (hT : CoeffMem A T) : CoeffMem A (S * T) := fun n => by
  rw [coeff_mul]
  exact Subalgebra.sum_mem _ fun kl _ => Subalgebra.mul_mem _ (hS _) (hT _)

private theorem CoeffMem_X_pow (A : Subalgebra ℤ ℂ) (k : ℕ) : CoeffMem A (X ^ k) := fun n => by
  rw [coeff_X_pow]
  split_ifs
  exacts [one_mem _, zero_mem _]

private theorem CoeffMem.pow {A : Subalgebra ℤ ℂ} {S : PowerSeries ℂ} (hS : CoeffMem A S) :
    ∀ n : ℕ, CoeffMem A (S ^ n)
  | 0 => by simpa using CoeffMem_X_pow A 0
  | n + 1 => by
    rw [pow_succ]
    exact (CoeffMem.pow hS n).mul hS

private theorem CoeffMem.smul {A : Subalgebra ℤ ℂ} {S : PowerSeries ℂ} (hS : CoeffMem A S) {c : ℂ}
    (hc : c ∈ A) : CoeffMem A (c • S) := fun n => by
  rw [coeff_smul, smul_eq_mul]
  exact mul_mem hc (hS n)

private theorem isIntegral_natCast (n : ℕ) : IsIntegral ℤ (n : ℂ) := by
  have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (n : ℤ))
  simpa using this

end INTINF

open scoped MatrixGroups ModularForm in
/-- **The width-`1` `q`-expansion at `m₀`.**  With `m₀` pinned by
`N m₀ = Ord + N t`, the width-`1` `q`-expansion of `ϑ` vanishes below `m₀`, is non-zero at
`m₀`, and a fixed power of `N` makes every coefficient — and the inverse of the `m₀`
coefficient — integral over `ℤ`. -/
theorem qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow
    (N : ℕ) [NeZero N] (m : ZMod N → ZMod N → ℕ) (hm0 : m 0 0 = 0) (t : ℕ)
    (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) (12 * (t : ℤ)))
    (hϑ : ∀ τ : UpperHalfPlane, ϑ τ =
      (∏ r : ZMod N, ∏ s : ZMod N,
          ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s)) *
        ModularForm.discriminant τ ^ t)
    (m₀ : ℕ)
    (hm₀ : (N : ℤ) * m₀ =
      (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
        (6 * (r.val : ℤ) ^ 2
          - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) + (N : ℤ) * t) :
    ∃ a : ℕ,
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n) := by
  classical
  obtain ⟨C, d, hCN, hdint, -, hd0ne, hd0inv, hsum, -⟩ :=
    ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow N m hm0
  set Ord : ℤ := ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
      (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) with hOrd
  have hNpos : 0 < N := NeZero.pos N
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hC0 : C ≠ 0 := by
    rintro rfl
    rw [zero_pow hNpos.ne'] at hCN
    exact zero_ne_one hCN
  have hCint : IsIntegral ℤ C := IsIntegral.of_pow hNpos (by rw [hCN]; exact isIntegral_one)
  let D : PowerSeries ℂ := PowerSeries.mk d
  let T : PowerSeries ℂ := C • (PowerSeries.X ^ (N * m₀) * (D * INTINF.deltaN N ^ t))
  have hT : ∀ τ : UpperHalfPlane,
      HasSum (fun k : ℕ => PowerSeries.coeff k T • Function.Periodic.qParam (N : ℝ) τ ^ k) (ϑ τ) := by
    intro τ
    set q := Function.Periodic.qParam (N : ℝ) τ with hqdef
    have hq0 : q ≠ 0 := Complex.exp_ne_zero _
    set u : UpperHalfPlane → ℂ := fun τ => ∏ r : ZMod N, ∏ s : ZMod N,
        ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * m r s) with hu
    set e : UpperHalfPlane → ℂ := fun τ =>
        Complex.exp (2 * Real.pi * Complex.I * (Ord : ℂ) * (τ : ℂ) / (N : ℂ)) with he
    have hD : INTINF.EvA D q (u τ / (C * e τ)) := by
      refine INTINF.EvA_of_forall_hasSum (S := D) (F := fun τ => u τ / (C * e τ)) hNR (fun τ' => ?_) τ
      have h' := hsum τ'
      simp only [D, PowerSeries.coeff_mk, INTINF.qParam_natCast_pow]
      convert h' using 3
      simp only [he, hOrd]
      push_cast
      ring
    have hall := ((INTINF.EvA_X_pow q (N * m₀)).mul (hD.mul ((INTINF.EvA_deltaN N τ).pow t))).smul C
    have he' : e τ * q ^ (N * t) = q ^ (N * m₀) := by
      have h1 : e τ = q ^ Ord := by
        rw [he, hqdef, INTINF.qParam_natCast_zpow]
      have h2 : (Ord : ℤ) + ((N * t : ℕ) : ℤ) = ((N * m₀ : ℕ) : ℤ) := by push_cast; linarith
      rw [h1, ← zpow_natCast, ← zpow_add₀ hq0, h2, zpow_natCast]
    have he0 : e τ ≠ 0 := Complex.exp_ne_zero _
    have hval : C * (q ^ (N * m₀) * (u τ / (C * e τ) * (ModularForm.discriminant τ / q ^ N) ^ t)) =
        ϑ τ := by
      rw [hϑ τ]
      change _ = u τ * ModularForm.discriminant τ ^ t
      rw [div_pow, ← pow_mul, ← he']
      field_simp
    rw [← hval]
    simpa only [smul_eq_mul] using hall.1
  have hcoefN : ∀ k : ℕ, PowerSeries.coeff k T =
      (UpperHalfPlane.qExpansion (N : ℝ) (⇑ϑ : UpperHalfPlane → ℂ)).coeff k := fun k =>
    ModularFormClass.qExpansion_coeff_unique hNR (INTINF.natCast_mem_strictPeriods_Gamma1 N N) hT k
  have hper : Function.Periodic ((⇑ϑ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex (f := ϑ) (INTINF.one_mem_strictPeriods_Gamma1 N)
  have : Fact (IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (INTINF.one_mem_strictPeriods_Gamma1 N)⟩
  have hcoef1 : ∀ n : ℕ, (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n =
      PowerSeries.coeff (N * n) T := fun n => by
    have h := UpperHalfPlane.qExpansion_coeff_mul_width (⇑ϑ) 1 one_pos hper (ModularFormClass.holo ϑ)
      (ModularFormClass.bdd_at_infty ϑ) N hNpos (N * n)
    rw [mul_one, ite_eq_left (dvd_mul_right N n), Nat.mul_div_cancel_left n hNpos] at h
    rw [← h, hcoefN]
  have hTcoef : ∀ k : ℕ, PowerSeries.coeff k T =
      C * if N * m₀ ≤ k then PowerSeries.coeff (k - N * m₀) (D * INTINF.deltaN N ^ t) else 0 := by
    intro k
    simp only [T, PowerSeries.coeff_smul, smul_eq_mul, PowerSeries.coeff_X_pow_mul']
  have hT0 : PowerSeries.coeff (N * m₀) T = C * d 0 := by
    rw [hTcoef, ite_eq_left le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
      map_pow, INTINF.constantCoeff_deltaN, one_pow, mul_one,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  have hTmem : INTINF.CoeffMem (integralClosure ℤ ℂ) T := by
    refine INTINF.CoeffMem.smul ((INTINF.CoeffMem_X_pow _ _).mul
      (INTINF.CoeffMem.mul (fun n => ?_) (INTINF.CoeffMem.pow (fun i => ?_) t)))
      ((mem_integralClosure_iff ℤ ℂ).mpr hCint)
    · rw [PowerSeries.coeff_mk]
      exact (mem_integralClosure_iff ℤ ℂ).mpr (hdint n)
    · rw [INTINF.coeff_deltaN]
      split_ifs
      exacts [intCast_mem _ _, zero_mem _]
  refine ⟨12 * N * ∑ r : ZMod N, ∑ s : ZMod N, m r s, fun n hn => ?_, ?_, ?_, fun n => ?_⟩
  · rw [hcoef1, hTcoef, ite_eq_right (not_le.mpr (Nat.mul_lt_mul_left hNpos |>.mpr hn)), mul_zero]
  · rw [hcoef1, hT0]
    exact mul_ne_zero hC0 hd0ne
  · rw [hcoef1, hT0]
    have hCinv : C⁻¹ = C ^ (N - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel hNpos, hCN]
    rw [mul_inv, hCinv, show (N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, m r s) *
        (C ^ (N - 1) * (d 0)⁻¹) = C ^ (N - 1) *
        ((N : ℂ) ^ (12 * N * ∑ r : ZMod N, ∑ s : ZMod N, m r s) * (d 0)⁻¹) by ring]
    exact (hCint.pow _).mul hd0inv
  · rw [hcoef1]
    exact ((INTINF.isIntegral_natCast N).pow _).mul ((mem_integralClosure_iff ℤ ℂ).mp (hTmem _))

end SiegelUnit

end ModularCurve
