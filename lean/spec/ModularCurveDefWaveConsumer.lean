/-
  Consumer specification for the **MC definition wave** — the seven modules that gate
  the `ModularCurve` ready shelf's orders MC-4, MC-5 and MC-6
  (`lean/topics/modularCurve/WORKORDER-MCDEF-definition-wave.md`):

    `ModularForms/Defs/GammaH.lean`                 (inserted)  CuspForm.{diamondLinH,heckeULinH,heckeTLinH}
    `ModularCurve/X1/HeckeModule.lean`              (inserted)  HeckeAlgOne + heckeModuleOneBar
    `ModularCurve/XH/Operators.lean`                (inserted)  diamondHBar, genOpH
    `ModularForms/CohCarrier/Inst.lean`             (new)       CohCarrier.Gen, heckeTL, diamondL, opFamily
    `ModularForms/CohCarrier/Fricke.lean`           (new)       frickeMat/frickeHom/frickeEquiv/frickeH1(L)
    `ModularCurve/Defs/SiegelFunction.lean`         (new)       siegelFun
    `ModularCurve/Defs/ResidualRealization.lean`    (new)       IsResidualRealization, CyclotomicDeterminant

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the new definition layer, composed across modules, expressed in
  Lean so that each is either bound or not.  It is a deliverable measure, not a proof
  obligation.  It is **not part of any library** (`lake build` does not see `spec/`); run
  it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveDefWaveConsumer.lean 2>&1 | grep -c error

  The error count is the metric.  The row modules of MC-4/5/6 extend these zones once they
  land; the brief's §3 is the plan.

  ZONES
  -----
    [siegel]   ZONE A — the Siegel unit's defining equation, read at an `UpperHalfPlane`
               point and factored through `Complex.exp`/`∏'`: the shape the MC-5 row
               `siegelFun_specialLinearGroup_smul` rewrites in.
    [fricke]   ZONE B — the Fricke involution on `Γ_H`: `frickeHom` is multiplicative, its
               square is the identity through `frickeEquiv`, and the `H¹` operator
               `frickeH1L` squares to the identity.  Composes the wave with `Subgroup`
               multiplication and `AddMonoidHom.comp`.
    [genop]    ZONE C — `genOpH` at a diamond generator is `diamondHBar`, and the diamond
               operator is additive: the interface the MC-4 rows `galois_smul_genOpH_comm`
               and `heckeOperatorHAlong_diamondHBar_comm` open with.
    [module]   ZONE D — the `HeckeAlgOne`-module structure on `J₁(M)`: `1` acts as the
               identity and `MvPolynomial.C` acts through the scalar action.  Composes
               `heckeModuleOneBar` with the `Module`/`MvPolynomial` API.
    [tlin]     ZONE E — the `Γ_H` Hecke and diamond operators are `ℂ`-linear: `heckeTLinH`
               and `diamondLinH` distribute over addition and scalar multiplication.  The
               interface of the MC-4 row `periodLatticeOf_gammaH_heckeDiamondStable`.
    [resid]    ZONE F — the residual-realization carrier: the `finrank`/spanning fields and
               the cyclotomic-determinant condition applied at a Frobenius.  The interface
               of the MC-5 row `exists_semisimple_descent_of_trace_det_mem_range_finite`.
-/

import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularCurve.X1.HeckeModule
import FLTForHuman.ModularCurve.XH.Operators
import FLTForHuman.ModularForms.CohCarrier.Inst
import FLTForHuman.ModularForms.CohCarrier.Fricke
import FLTForHuman.ModularCurve.Defs.SiegelFunction
import FLTForHuman.ModularCurve.Defs.ResidualRealization

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane

namespace MCDefWaveConsumer

/-! ## Zone A — `[siegel]` the Siegel unit's defining equation -/

/-- The pin's product form, read at a point of the upper half plane (the coercion the MC-5
row carries) and with the two `Complex.exp` factors kept together. -/
theorem siegelFun_coe_eq (N : ℕ) (r s : ℤ) (τ : UpperHalfPlane) :
    ModularCurve.siegelFun N r s (τ : ℂ) =
      -Complex.exp (Real.pi * Complex.I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
        Complex.exp
          (Real.pi * Complex.I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * (τ : ℂ)) *
        (1 - Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (N : ℂ))) *
        ∏' n : ℕ, ((1 - Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (n + 1) *
            Complex.exp (2 * Real.pi * Complex.I * ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (N : ℂ))) *
          (1 - Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) ^ (n + 1) *
            (Complex.exp
              (2 * Real.pi * Complex.I * ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / (N : ℂ)))⁻¹)) :=
  ModularCurve.siegelFun_def N r s (τ : ℂ)

/-! ## Zone B — `[fricke]` the Fricke involution -/

theorem frickeHom_mul {N : ℕ} {H : Subgroup (ZMod N)ˣ} (γ δ : ↥(CohCarrier.GammaH N H)) :
    CohCarrier.frickeHom N H (γ * δ) = CohCarrier.frickeHom N H γ * CohCarrier.frickeHom N H δ :=
  map_mul _ γ δ

theorem frickeEquiv_symm_eq_inv {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ}
    (γ : ↥(CohCarrier.GammaH N H)) :
    (CohCarrier.frickeEquiv N H).symm γ = CohCarrier.frickeEquiv N H γ :=
  CohCarrier.frickeEquiv_symm_apply N H γ

theorem frickeH1L_frickeH1L {N : ℕ} [NeZero N] {H : Subgroup (ZMod N)ˣ}
    {A : Type*} [AddCommGroup A] (R : Type*) [Semiring R] [Module R A]
    (φ : CohCarrier.H1 N H A) :
    CohCarrier.frickeH1L N H A R (CohCarrier.frickeH1L N H A R φ) = φ :=
  CohCarrier.frickeH1_frickeH1 N H A φ

/-! ## Zone C — `[genop]` `genOpH` and the diamond operator -/

theorem genOpH_dia_apply {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (d : (ZMod M)ˣ) (P : ModularCurve.JH M H) :
    ModularCurve.genOpH M H S (.dia d) P = ModularCurve.diamondHBar M H d P := by
  rw [ModularCurve.genOpH_dia]

theorem diamondHBar_add {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ) (d : (ZMod M)ˣ)
    (P Q : ModularCurve.JH M H) :
    ModularCurve.diamondHBar M H d (P + Q) =
      ModularCurve.diamondHBar M H d P + ModularCurve.diamondHBar M H d Q :=
  map_add _ P Q

/-! ## Zone D — `[module]` the `HeckeAlgOne` module on `J₁(M)` -/

theorem heckeModuleOneBar_one_smul {M : ℕ} [NeZero M] (x : ModularCurve.JOne M) :
    (letI := ModularCurve.heckeModuleOneBar M; (1 : ModularCurve.HeckeAlgOne) • x = x) :=
  letI := ModularCurve.heckeModuleOneBar M
  one_smul _ x

theorem heckeModuleOneBar_C_one_smul {M : ℕ} [NeZero M] (x : ModularCurve.JOne M) :
    (letI := ModularCurve.heckeModuleOneBar M;
      (MvPolynomial.C (1 : ℤ) : ModularCurve.HeckeAlgOne) • x = x) := by
  letI := ModularCurve.heckeModuleOneBar M
  rw [ModularCurve.heckeModuleOneBar_C_smul, one_zsmul]

/-! ## Zone E — `[tlin]` the `Γ_H` Hecke and diamond operators are `ℂ`-linear -/

theorem heckeTLinH_add {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓM : ¬ ℓ ∣ M) (f g : CuspForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2) :
    CuspForm.heckeTLinH 2 hℓ hℓM (f + g) =
      CuspForm.heckeTLinH 2 hℓ hℓM f + CuspForm.heckeTLinH 2 hℓ hℓM g :=
  map_add _ f g

theorem diamondLinH_smul {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} (d : (ZMod M)ˣ)
    (c : ℂ) (f : CuspForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) 2) :
    CuspForm.diamondLinH 2 d (c • f) = c • CuspForm.diamondLinH 2 d f :=
  map_smul _ c f

/-! ## Zone F — `[resid]` the residual-realization carrier -/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {J : Type*} [AddCommGroup J] [Module ModularCurve.HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
  {k : Type*} [Field k] {φ : ModularCurve.HeckeAlg →+* k}
  {V : Type*} [AddCommGroup V] [Module k V] {π : J → V} {ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V)}

theorem IsResidualRealization.finrank_eq_two (p : ℕ)
    (h : ModularCurve.IsResidualRealization p J k φ V π ρ) : Module.finrank k V = 2 :=
  h.finrank_eq

theorem IsResidualRealization.span_le_top (p : ℕ)
    (h : ModularCurve.IsResidualRealization p J k φ V π ρ) :
    Submodule.span k (π '' {x : J | p • x = 0}) ≤ ⊤ :=
  h.spanning.le

theorem CyclotomicDeterminant.apply (N p : ℕ) (hρ : ModularCurve.CyclotomicDeterminant N p ρ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hN : ¬ ℓ ∣ N * p) (A : ValuationSubring L)
    (hA : A.LiesOverPrime ℓ) (σ : L ≃ₐ[K] L) (hσ : A.IsFrobeniusAt σ ℓ) :
    LinearMap.det (ρ σ).toLinearMap = (ℓ : k) :=
  hρ ℓ hℓ hN A hA σ hσ

end MCDefWaveConsumer
