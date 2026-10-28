/-
The diamond correspondence on the `X₁(M)` function field: for `f : CuspForm Γ₁(M) 2` whose
differential has `q`-expansion `qExpansion f`, the `q`-expansion of the correspondence
`correspondence (diamondAutBar M d) id ω` is `qExpansion (CuspForm.diamondLinOne M 2 d f)`.

Proof transcribed from FLT's
`P2M/Sol/S_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean`
(pin `aa2d8b3`), statement from
`Theorems/Thm_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean`.
The pin's `namespace R1G1Hd` is a proof-search label, not mathematics; the declarations keep
their pin last names, inside `ModularCurve.DiamondCorrespondence` (a nested namespace is needed
because the pin's `coeffMap_algebraMap` would otherwise collide with `ModularCurve.coeffMap_algebraMap`,
`Defs/Laurent.lean`, which is a different statement).  The pin's
`set_option synthInstance.maxHeartbeats 1600000` / `set_option maxHeartbeats 3200000` are not
transcribed (the project cap governs).

What is *imported rather than re-proved* — no proof is copied:

* the pin's `AutTrace` sextet: `pullbackAlong_pullbackAlong` is the port's
  `AlgebraicCurve.Differential.TraceAtPoints.pullbackAlong_pullbackAlong`, and
  `pullbackAlong_id`/`separableAlong_algEquiv`/`trace_one_along_algEquiv`/`traceAlong_algEquiv`/
  `correspondence_algEquiv_id` are the shared landing `AlgebraicCurve/Differential/AutTrace.lean`
  (the same block serves the concurrent β-correspondence row);
* the level-one Eisenstein block (`P4`, `P6`, `isIntegralQExp_E4`, `isIntegralQExp_E6`,
  `constantCoeff_P4`/`_P6`, `coeff_one_P4`/`_P6`, `intSeriesC_ne_zero_of_constantCoeff`,
  `intSeriesC_P4_cube_ne_zero`, `xq`) from `ModularCurve/XH/Relrank.lean` (`RelrankSol`);
* `coeffMap_injective` (`Defs/Laurent.lean`), `coeffMap_ofPowerSeries` (`Frobenius/Defs.lean`),
  `intSeriesC_eq_zero_iff` (`JqIntegralRatios.lean`), `intSeriesC_add`
  (`X1/FunctionFieldDegree.lean`), `conj_mem_Gamma1` (`ModularForm.Level`),
  `mem_intFormRatiosC_of_mem` (`X1/AtkinLehnerExchange.lean`, as `A2K1A.X1x0.mem_Sb_of_mem`),
  `coeffEmb_intSeriesC` (`JqIntegralRatios.lean`, general form).

Two one-line aliases keep the pin's *names* for the level-one top forms so that the pin
statements (`coe_D12top`, `qExpansion_D12top`, `slash_top_eq`, `exists_RCtop`, `sigma_x0`) can be
written at the pin's text: `D12top := RelrankSol.AF`, `N12top := RelrankSol.BF` (no proof is
duplicated; `RelrankSol`'s `AF`/`BF` are the same forms built by `restrictForm`).

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean

  The leaf row `ModularCurve.diamondOneBar_comm` (LV-6) is inserted at the end of
  this module, over an engine ported from its `S_` copy (`X1DiaComm`); its wrapper
  and `S_` copy are the last two `spec-pin:` lines.

spec-pin: Theorems/Thm_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean
spec-pin: P2M/Sol/S_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean
spec-pin: Theorems/Thm_ModularCurve_diamondOneBar_comm.lean
spec-pin: P2M/Sol/S_ModularCurve_diamondOneBar_comm.lean
-/
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.ModularCurve.X1.DiamondAut
import FLTForHuman.ModularCurve.X1.DiamondLift
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.XH.Relrank
import FLTForHuman.ModularCurve.Defs.HeckeDifferential
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.Frobenius.Defs
import FLTForHuman.ModularCurve.X1.AtkinLehnerExchange
import FLTForHuman.ModularForms.QCoeffLevelOne
import FLTForHuman.ModularForms.Defs.Gamma1HeckeOperators
import FLTForHuman.ModularForms.Level.Diamond
import FLTForHuman.ModularForms.HeckeNebentypus
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Differential.PushPull
import FLTForHuman.AlgebraicCurve.Differential.AutTrace
import FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegular

set_option autoImplicit false


noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve AlgebraicCurve.Differential IntermediateField

open scoped MatrixGroups Pointwise

namespace ModularCurve

namespace DiamondCorrespondence

section Laurent

variable {R S : Type*} [CommRing R] [CommRing S]

theorem ofPowerSeries_coeff_negSucc (p : PowerSeries R) (n : ℕ) :
    (ofPowerSeries ℤ R p).coeff (Int.negSucc n) = 0 := by
  rw [ofPowerSeries_apply, embDomain_of_notMem_range]
  simp

theorem coeffMap_qEuler (f : R →+* S) (x : LaurentSeries R) :
    coeffMap f (qEuler R x) = qEuler S (coeffMap f x) := by
  ext k
  rw [coeffMap_coeff, qEuler_coeff, qEuler_coeff, coeffMap_coeff, map_mul, map_intCast]

theorem qEuler_ofPowerSeries (p : PowerSeries R) :
    qEuler R (ofPowerSeries ℤ R p) =
      ofPowerSeries ℤ R (PowerSeries.mk fun n : ℕ => (n : R) * PowerSeries.coeff n p) := by
  ext k
  rw [qEuler_coeff]
  cases k with
  | ofNat n =>
      simp only [Int.ofNat_eq_natCast]
      rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, Int.cast_natCast]
  | negSucc n =>
      rw [ofPowerSeries_coeff_negSucc, ofPowerSeries_coeff_negSucc, mul_zero]

theorem qEuler_div_mul_sq {L : Type*} [Field L] (B A : LaurentSeries L) (hA : A ≠ 0) :
    qEuler L (B / A) * (A * A) = qEuler L B * A - B * qEuler L A := by
  have h : B = B / A * A := (div_mul_cancel₀ B hA).symm
  have hl := (qEuler L).leibniz (B / A) A
  rw [← h] at hl

  rw [hl, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

end Laurent

section LevelOne

open ModularForm UpperHalfPlane EisensteinSeries CongruenceSubgroup

open scoped MatrixGroups ModularForm

open RelrankSol

def D12top : ModularForm ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  RelrankSol.AF

def N12top : ModularForm ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  RelrankSol.BF

theorem coe_D12top : (⇑D12top : ℍ → ℂ) = (⇑E₄ : ℍ → ℂ) ^ 3 := RelrankSol.coe_AF
theorem coe_N12top : (⇑N12top : ℍ → ℂ) = (⇑E₆ : ℍ → ℂ) ^ 2 := RelrankSol.coe_BF

theorem qExpansion_D12top : qExpansion 1 (⇑D12top : ℍ → ℂ) = (P4 ^ 3).map (Int.castRingHom ℂ) := by
  rw [coe_D12top, map_pow, RelrankSol.isIntegralQExp_E4]
  exact ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3

theorem qExpansion_N12top : qExpansion 1 (⇑N12top : ℍ → ℂ) = (P6 ^ 2).map (Int.castRingHom ℂ) := by
  rw [coe_N12top, map_pow, RelrankSol.isIntegralQExp_E6]
  exact ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ 2

theorem slash_top_eq {k : ℤ} (B : ModularForm ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (g : SL(2, ℤ)) : (⇑B : ℍ → ℂ) ∣[k] (g : GL (Fin 2) ℝ) = ⇑B :=
  SlashInvariantForm.slash_action_eqn B _ (Subgroup.mem_map.mpr ⟨g, Subgroup.mem_top g, rfl⟩)

theorem one_mem_strictPeriods_of {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples 1

theorem exists_RCtop :
    ∃ B : ModularForm ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 26,
      ofPowerSeries ℤ ℂ (qExpansion 1 (⇑B : ℍ → ℂ)) =
        HahnSeries.C (12 : ℂ) *
          (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑N12top : ℍ → ℂ)) *
              qEuler ℂ (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑D12top : ℍ → ℂ))) -
            qEuler ℂ (ofPowerSeries ℤ ℂ (qExpansion 1 (⇑N12top : ℍ → ℂ))) *
              ofPowerSeries ℤ ℂ (qExpansion 1 (⇑D12top : ℍ → ℂ))) := by
  obtain ⟨B, -, hB⟩ := ModularForm.exists_rankinCohen_one_qExpansion_eq (Γ := ⊤)
    (one_mem_strictPeriods_of (Subgroup.mem_top _)) N12top D12top
  refine ⟨B.mcast (by norm_num), ?_⟩
  rw [ModularForm.coe_mcast, hB]
  simp only [map_sub, map_mul, HahnSeries.ofPowerSeries_C]
  rw [qEuler_ofPowerSeries, qEuler_ofPowerSeries]
  push_cast
  ring

end LevelOne

section Forms

open ModularForm UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

local notation "Γ₁ℝ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ(M)).strictPeriods := by
  simp [CongruenceSubgroup.strictPeriods_Gamma1]

variable {M : ℕ}

open ConjAct Pointwise in

theorem gamma1_le_conj {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    Γ₁ℝ(M) ≤ toConjAct (γ : GL (Fin 2) ℝ)⁻¹ • Γ₁ℝ(M) := by
  intro x hx
  obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
  refine Subgroup.mem_map.mpr ⟨γ * A * γ⁻¹, ModularForm.Level.conj_mem_Gamma1 hγ hA, ?_⟩
  show Matrix.SpecialLinearGroup.mapGL ℝ (γ * A * γ⁻¹) =
    Matrix.SpecialLinearGroup.mapGL ℝ γ * Matrix.SpecialLinearGroup.mapGL ℝ A *
      (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹
  rw [map_mul, map_mul, map_inv]

open ConjAct Pointwise in

def conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁ℝ(M) k) :
    ModularForm Γ₁ℝ(M) k :=
  restrictForm (gamma1_le_conj hγ) (ModularForm.translate f (γ : GL (Fin 2) ℝ))

@[scoped simp]
theorem coe_conjForm {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁ℝ(M) k) :
    (⇑(conjForm γ hγ f) : ℍ → ℂ) = (⇑f) ∣[k] (γ : GL (Fin 2) ℝ) :=
  rfl

abbrev QQ (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem slashQExpC_eq {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (f : ModularForm Γ₁ℝ(M) k) :
    slashQExpC k f γ = QQ ⇑(conjForm γ hγ f) :=
  rfl

theorem QQ_mul {a b : ℤ} (F : ModularForm Γ₁ℝ(M) a) (G : ModularForm Γ₁ℝ(M) b) :
    QQ (⇑F * ⇑G) = QQ ⇑F * QQ ⇑G := by
  rw [QQ, ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) F G, map_mul]

theorem QQ_add {a b : ℤ} (F : ModularForm Γ₁ℝ(M) a) (G : ModularForm Γ₁ℝ(M) b) :
    QQ (⇑F + ⇑G) = QQ ⇑F + QQ ⇑G := by
  rw [QQ, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods M) F G, map_add]

theorem QQ_neg {a : ℤ} (F : ModularForm Γ₁ℝ(M) a) : QQ ⇑(-F) = -QQ ⇑F := by
  rw [QQ, FunLike.coe_neg, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods M) F, map_neg]

theorem QQ_smul {a : ℤ} (c : ℂ) (F : ModularForm Γ₁ℝ(M) a) : QQ ⇑(c • F) = HahnSeries.C c * QQ ⇑F := by
  have han : AnalyticAt ℂ (cuspFunction 1 (⇑F)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero F one_pos (one_mem_strictPeriods M)
  rw [QQ, FunLike.coe_smul, qExpansion_smul han c, PowerSeries.smul_eq_C_mul, map_mul,
    HahnSeries.ofPowerSeries_C]

theorem QQ_one : QQ ⇑(1 : ModularForm Γ₁ℝ(M) 0) = 1 := by
  rw [QQ, ModularForm.one_coe_eq_one, qExpansion_one, map_one]

theorem eq_of_QQ_eq {k : ℤ} {F G : ModularForm Γ₁ℝ(M) k} (h : QQ ⇑F = QQ ⇑G) : (⇑F : ℍ → ℂ) = ⇑G := by
  have h' : qExpansion 1 (⇑F) = qExpansion 1 (⇑G) := ofPowerSeries_injective h
  have h0 : F - G = 0 := by
    refine (ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M) (F - G)).mp ?_
    rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods M), h', sub_self]
  rw [sub_eq_zero.mp h0]

theorem QQ_eq_zero_iff {k : ℤ} (F : ModularForm Γ₁ℝ(M) k) : QQ ⇑F = 0 ↔ F = 0 := by
  rw [QQ, map_eq_zero_iff _ ofPowerSeries_injective,
    ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M)]

theorem conjForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {g : ModularForm Γ₁ℝ(M) k}
    (hg : g ≠ 0) : conjForm γ hγ g ≠ 0 := by
  intro h
  apply hg
  have h1 : (⇑g : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ) = 0 := by
    rw [← coe_conjForm γ hγ g, h, FunLike.coe_zero]
  have h2 : (⇑g : ℍ → ℂ) = 0 := (SlashAction.slash_eq_zero_iff _ _ _).mp h1
  exact DFunLike.ext' (by rw [h2, FunLike.coe_zero])

theorem QQ_conjForm_ne_zero {k : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) {g : ModularForm Γ₁ℝ(M) k}
    (hg : QQ ⇑g ≠ 0) : QQ ⇑(conjForm γ hγ g) ≠ 0 := by
  rw [Ne, QQ_eq_zero_iff] at hg ⊢
  exact conjForm_ne_zero γ hγ hg

theorem coeGL_mul (a b : SL(2, ℤ)) :
    ((a * b : SL(2, ℤ)) : GL (Fin 2) ℝ) = (a : GL (Fin 2) ℝ) * (b : GL (Fin 2) ℝ) :=
  map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) a b

theorem coe_conjForm_mul {a b : ℤ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (F : ModularForm Γ₁ℝ(M) a)
    (G : ModularForm Γ₁ℝ(M) b) :
    (⇑(conjForm γ hγ (F.mul G)) : ℍ → ℂ) = ⇑(conjForm γ hγ F) * ⇑(conjForm γ hγ G) := by
  rw [coe_conjForm, coe_conjForm, coe_conjForm, ModularForm.coe_mul, ← ModularForm.SL_slash,
    ModularForm.mul_slash_SL2, ModularForm.SL_slash, ModularForm.SL_slash]

def toMF {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k) : ModularForm Γ k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  bdd_at_cusps' hc g hg := (f.zero_at_cusps' hc g hg).boundedAtFilter

@[scoped simp] theorem coe_toMF {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : CuspForm Γ k) :
    (⇑(toMF f) : ℍ → ℂ) = ⇑f := rfl

end Forms

section Ratios

open ModularForm UpperHalfPlane CongruenceSubgroup EisensteinSeries
open scoped MatrixGroups ModularForm

local notation "Γ₁ℝ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ}

open RelrankSol

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = intSeriesC ℂ p := by
  rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
  congr 1

theorem intSeriesC_C (K : Type*) [Field K] (z : ℤ) :
    intSeriesC K (PowerSeries.C z) = HahnSeries.C (z : K) := by
  rw [intSeriesC, PowerSeries.map_C, ofPowerSeries_C]
  simp

theorem intSeriesC_eq_of_isIntegralQExp {f : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp f p) :
    intSeriesC ℂ p = QQ f := by
  rw [intSeriesC]
  exact congrArg (ofPowerSeries ℤ ℂ) h

theorem ne_zero_of_isIntegralQExp {k : ℤ} {g : ModularForm Γ₁ℝ(M) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 := by
  intro h
  apply hg0
  rw [intSeriesC_eq_zero_iff]
  have h1 : qExpansion 1 (⇑g) = 0 := by rw [h, FunLike.coe_zero, qExpansion_zero]
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  rw [map_zero]
  exact hg.trans h1

theorem QQ_ne_zero_of_isIntegralQExp {k : ℤ} {g : ModularForm Γ₁ℝ(M) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : QQ ⇑g ≠ 0 := by
  rw [Ne, QQ_eq_zero_iff]
  exact ne_zero_of_isIntegralQExp hg hg0

theorem isIntegralQExp_intCast (z : ℤ) :
    IsIntegralQExp (⇑(z : ModularForm Γ₁ℝ(M) 0)) (PowerSeries.C z) := by
  rw [IsIntegralQExp, PowerSeries.map_C]
  have h1 : (⇑(z : ModularForm Γ₁ℝ(M) 0) : ℍ → ℂ) = (z : ℂ) • ⇑(1 : ModularForm Γ₁ℝ(M) 0) := by
    funext τ
    simp [ModularForm.coe_intCast, ModularForm.one_coe_eq_one]
  rw [h1, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero _ one_pos
    (one_mem_strictPeriods M)), ModularForm.one_coe_eq_one, qExpansion_one, Algebra.smul_def, mul_one,
    PowerSeries.algebraMap_eq]
  simp

variable (M) in

def A12M : ModularForm Γ₁ℝ(M) 12 := restrictForm (Subgroup.map_mono le_top) D12top

variable (M) in

def B12M : ModularForm Γ₁ℝ(M) 12 := restrictForm (Subgroup.map_mono le_top) N12top

theorem coe_A12M : (⇑(A12M M) : ℍ → ℂ) = ⇑D12top := rfl
theorem coe_B12M : (⇑(B12M M) : ℍ → ℂ) = ⇑N12top := rfl

theorem isIntegralQExp_A12M : IsIntegralQExp (A12M M : ℍ → ℂ) (P4 ^ 3) := by
  rw [IsIntegralQExp, coe_A12M, qExpansion_D12top]

theorem isIntegralQExp_B12M : IsIntegralQExp (B12M M : ℍ → ℂ) (P6 ^ 2) := by
  rw [IsIntegralQExp, coe_B12M, qExpansion_N12top]

theorem coeffMap_xq : coeffMap (algebraMap ℚ ℂ) xq = QQ ⇑(B12M M) / QQ ⇑(A12M M) := by
  rw [show xq = intSeriesC ℚ (P6 ^ 2) / intSeriesC ℚ (P4 ^ 3) from rfl, map_div₀,
    coeffMap_intSeriesC, coeffMap_intSeriesC, intSeriesC_eq_of_isIntegralQExp isIntegralQExp_B12M,
    intSeriesC_eq_of_isIntegralQExp isIntegralQExp_A12M]

theorem QQ_A12M_ne_zero : QQ ⇑(A12M M) ≠ 0 :=
  QQ_ne_zero_of_isIntegralQExp isIntegralQExp_A12M (intSeriesC_PA_ne_zero ℚ)

theorem slash_A12M (g : SL(2, ℤ)) : (⇑(A12M M) : ℍ → ℂ) ∣[(12 : ℤ)] (g : GL (Fin 2) ℝ) = ⇑(A12M M) := by
  rw [coe_A12M]; exact slash_top_eq D12top g

theorem slash_B12M (g : SL(2, ℤ)) : (⇑(B12M M) : ℍ → ℂ) ∣[(12 : ℤ)] (g : GL (Fin 2) ℝ) = ⇑(B12M M) := by
  rw [coe_B12M]; exact slash_top_eq N12top g

theorem qEuler_ratio_ne_zero (K : Type*) [Field K] [CharZero K] :
    qEuler K (intSeriesC K (P6 ^ 2) / intSeriesC K (P4 ^ 3)) ≠ 0 := by
  intro h
  have hA := intSeriesC_PA_ne_zero K
  have h2 := qEuler_div_mul_sq (intSeriesC K (P6 ^ 2)) (intSeriesC K (P4 ^ 3)) hA
  rw [h, zero_mul] at h2

  rw [intSeriesC, intSeriesC, qEuler_ofPowerSeries, qEuler_ofPowerSeries, ← map_mul, ← map_mul,
    eq_comm, sub_eq_zero] at h2
  have h3 := congrArg (PowerSeries.coeff 1) (ofPowerSeries_injective h2)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, Finset.sum_cons,
    Finset.sum_cons, Finset.Nat.antidiagonal_zero] at h3
  have c0A : PowerSeries.coeff 0 ((P4 ^ 3).map (Int.castRingHom K)) = 1 := by
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_P4]
    simp
  have c0B : PowerSeries.coeff 0 ((P6 ^ 2).map (Int.castRingHom K)) = 1 := by
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_P6]
    simp
  have c1A : PowerSeries.coeff 1 ((P4 ^ 3).map (Int.castRingHom K)) = 720 := by
    rw [PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P4, constantCoeff_P4]; norm_num
  have c1B : PowerSeries.coeff 1 ((P6 ^ 2).map (Int.castRingHom K)) = -1008 := by
    rw [PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P6, constantCoeff_P6]; norm_num
  simp only [Finset.map_singleton, Finset.sum_singleton, Function.Embedding.coe_prodMap,
    Function.Embedding.coeFn_mk, Prod.map_apply, Nat.succ_eq_add_one, zero_add,
    Function.Embedding.refl_apply, PowerSeries.coeff_mk, Nat.cast_zero, zero_mul, Nat.cast_one,
    one_mul, c0A, c0B, c1A, c1B] at h3
  norm_num at h3


end Ratios
section Dictionary

open ModularForm UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

local notation "Γ₁ℝ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M)

def PairProp (x y : LaurentSeries ℂ) : Prop :=
  ∃ (k : ℤ) (G H : ModularForm Γ₁ℝ(M) k), QQ ⇑H ≠ 0 ∧ x * QQ ⇑H = QQ ⇑G ∧
    y * QQ ⇑(conjForm γ hγ H) = QQ ⇑(conjForm γ hγ G)

theorem coe_conjForm_one : (⇑(conjForm γ hγ (1 : ModularForm Γ₁ℝ(M) 0)) : ℍ → ℂ) = ⇑(1 : ModularForm Γ₁ℝ(M) 0) := by
  rw [coe_conjForm, ModularForm.one_coe_eq_one, ← ModularForm.SL_slash, ModularForm.is_invariant_one]

theorem coe_conjForm_smul {k : ℤ} (c : ℂ) (F : ModularForm Γ₁ℝ(M) k) :
    (⇑(conjForm γ hγ (c • F)) : ℍ → ℂ) = ⇑(c • conjForm γ hγ F) := by
  rw [coe_conjForm, FunLike.coe_smul, FunLike.coe_smul, coe_conjForm, ← ModularForm.SL_slash,
    ModularForm.SL_smul_slash, ModularForm.SL_slash]

theorem pair_const (a : ℂ) : PairProp γ hγ (HahnSeries.C a) (HahnSeries.C a) := by
  refine ⟨0, a • (1 : ModularForm Γ₁ℝ(M) 0), 1, ?_, ?_, ?_⟩
  · rw [QQ_one]; exact one_ne_zero
  · rw [QQ_one, mul_one, QQ_smul, QQ_one, mul_one]
  · rw [coe_conjForm_one, coe_conjForm_smul, QQ_one, mul_one, QQ_smul, coe_conjForm_one, QQ_one, mul_one]

theorem pair_zero : PairProp γ hγ 0 0 := by
  refine ⟨0, 0, 1, ?_, ?_, ?_⟩
  · rw [QQ_one]; exact one_ne_zero
  · rw [zero_mul, FunLike.coe_zero, QQ, qExpansion_zero, map_zero]
  · rw [zero_mul, coe_conjForm, FunLike.coe_zero, SlashAction.zero_slash, QQ, qExpansion_zero, map_zero]

theorem pair_mul {x y x' y' : LaurentSeries ℂ} (h : PairProp γ hγ x y) (h' : PairProp γ hγ x' y') :
    PairProp γ hγ (x * x') (y * y') := by
  obtain ⟨k, G, H, hH, h1, h2⟩ := h
  obtain ⟨k', G', H', hH', h1', h2'⟩ := h'
  refine ⟨k + k', G.mul G', H.mul H', ?_, ?_, ?_⟩
  · rw [ModularForm.coe_mul, QQ_mul]; exact mul_ne_zero hH hH'
  · rw [ModularForm.coe_mul, ModularForm.coe_mul, QQ_mul, QQ_mul, ← h1, ← h1']; ring
  · rw [coe_conjForm_mul, coe_conjForm_mul, QQ_mul, QQ_mul, ← h2, ← h2']; ring

theorem pair_add {x y x' y' : LaurentSeries ℂ} (h : PairProp γ hγ x y) (h' : PairProp γ hγ x' y') :
    PairProp γ hγ (x + x') (y + y') := by
  obtain ⟨k, G, H, hH, h1, h2⟩ := h
  obtain ⟨k', G', H', hH', h1', h2'⟩ := h'
  refine ⟨k + k', G.mul H' + H.mul G', H.mul H', ?_, ?_, ?_⟩
  · rw [ModularForm.coe_mul, QQ_mul]; exact mul_ne_zero hH hH'
  · rw [FunLike.coe_add, QQ_add, ModularForm.coe_mul, ModularForm.coe_mul, ModularForm.coe_mul,
      QQ_mul, QQ_mul, QQ_mul, ← h1, ← h1']
    ring
  · have e : (⇑(conjForm γ hγ (G.mul H' + H.mul G')) : ℍ → ℂ) =
        ⇑(conjForm γ hγ (G.mul H')) + ⇑(conjForm γ hγ (H.mul G')) := by
      rw [coe_conjForm, coe_conjForm, coe_conjForm, FunLike.coe_add, SlashAction.add_slash]
    rw [e, QQ_add, coe_conjForm_mul, coe_conjForm_mul, coe_conjForm_mul, QQ_mul, QQ_mul, QQ_mul,
      ← h2, ← h2']
    ring

theorem pair_neg {x y : LaurentSeries ℂ} (h : PairProp γ hγ x y) : PairProp γ hγ (-x) (-y) := by
  obtain ⟨k, G, H, hH, h1, h2⟩ := h
  refine ⟨k, -G, H, hH, ?_, ?_⟩
  · rw [QQ_neg, ← h1]; ring
  · have e : (⇑(conjForm γ hγ (-G)) : ℍ → ℂ) = ⇑(-conjForm γ hγ G) := by
      rw [coe_conjForm, FunLike.coe_neg, FunLike.coe_neg, SlashAction.neg_slash, coe_conjForm]
    rw [e, QQ_neg, ← h2]; ring

theorem pair_inv {x y : LaurentSeries ℂ} (h : PairProp γ hγ x y) : PairProp γ hγ x⁻¹ y⁻¹ := by
  obtain ⟨k, G, H, hH, h1, h2⟩ := h
  by_cases hx : x = 0
  ·
    have hG : G = 0 := by
      rw [hx, zero_mul, eq_comm, QQ_eq_zero_iff] at h1; exact h1
    have hy : y = 0 := by
      rw [hG] at h2
      have : QQ (⇑(conjForm γ hγ (0 : ModularForm Γ₁ℝ(M) k))) = 0 := by
        rw [coe_conjForm, FunLike.coe_zero, SlashAction.zero_slash, QQ, qExpansion_zero, map_zero]
      rw [this] at h2
      exact (mul_eq_zero.mp h2).resolve_right (QQ_conjForm_ne_zero γ hγ hH)
    rw [hx, hy, inv_zero]
    exact pair_zero γ hγ
  · have hG : QQ ⇑G ≠ 0 := by rw [← h1]; exact mul_ne_zero hx hH
    refine ⟨k, H, G, hG, ?_, ?_⟩
    · rw [← h1]; field_simp
    · have hcG : QQ ⇑(conjForm γ hγ G) ≠ 0 := QQ_conjForm_ne_zero γ hγ hG
      have hy : y ≠ 0 := by
        intro hy; rw [hy, zero_mul] at h2; exact hcG h2.symm
      rw [← h2]; field_simp

theorem pair_gen {d : ℕ} {σ₀ : ↥(x1FunctionField M) ≃ₐ[ℚ] ↥(x1FunctionField M)} (hσ₀ : IsDiamondAut M d σ₀)
    (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) {y : LaurentSeries ℚ} (hy : y ∈ x1FunctionField M) :
    PairProp γ hγ (coeffMap (algebraMap ℚ ℂ) y)
      (coeffMap (algebraMap ℚ ℂ) ((σ₀ ⟨y, hy⟩ : ↥(x1FunctionField M)) : LaurentSeries ℚ)) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := A2K1A.X1x0.mem_Sb_of_mem hy
  refine ⟨k, f, g, QQ_ne_zero_of_isIntegralQExp hg hg0, ?_, ?_⟩
  · rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC, intSeriesC_eq_of_isIntegralQExp hf,
      intSeriesC_eq_of_isIntegralQExp hg, div_mul_cancel₀ _ (QQ_ne_zero_of_isIntegralQExp hg hg0)]
  · exact hσ₀.2 k f g pf pg hf hg hg0 γ hγ hγd

theorem coeffMap_coeffEmb (ι₀ : Qb →+* ℂ) (z : LaurentSeries ℚ) :
    coeffMap ι₀ (coeffEmb Qb z) = coeffMap (algebraMap ℚ ℂ) z := by
  rw [coeffEmb, coeffMap_coeffMap,
    show ι₀.comp (algebraMap ℚ Qb) = algebraMap ℚ ℂ from Subsingleton.elim _ _]

theorem coeffMap_algebraMap (ι₀ : Qb →+* ℂ) (c : Qb) :
    coeffMap ι₀ (algebraMap Qb (LaurentSeries Qb) c) = HahnSeries.C (ι₀ c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffMap_single, HahnSeries.C_apply]

theorem pair_all {d : ℕ} (hda : IsDiamondAut M d (diamondAut M d))
    (hbc : IsBaseChangeAutOf Qb (diamondAut M d) (diamondAutBar M d))
    (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) (ι₀ : Qb →+* ℂ) (x : ↥(x1FunctionFieldBar M)) :
    PairProp γ hγ (coeffMap ι₀ (x : LaurentSeries Qb))
      (coeffMap ι₀ ((diamondAutBar M d x : ↥(x1FunctionFieldBar M)) : LaurentSeries Qb)) := by
  obtain ⟨x, hx⟩ := x
  set σ := diamondAutBar M d with hσdef
  have hx' := (mem_laurentBaseChange_iff (L := Qb) (F₀ := x1FunctionField M)).mp hx

  have memF : ∀ {z : LaurentSeries Qb},
      z ∈ Subfield.closure (Set.range (algebraMap Qb (LaurentSeries Qb)) ∪
        (⇑(coeffEmb Qb) '' ((x1FunctionField M : IntermediateField ℚ (LaurentSeries ℚ)) :
          Set (LaurentSeries ℚ)))) → z ∈ x1FunctionFieldBar M :=
    fun hz => (mem_laurentBaseChange_iff (L := Qb) (F₀ := x1FunctionField M)).mpr hz
  suffices h : ∀ (z : LaurentSeries Qb) (hz : z ∈ Subfield.closure
      (Set.range (algebraMap Qb (LaurentSeries Qb)) ∪
        (⇑(coeffEmb Qb) '' ((x1FunctionField M : IntermediateField ℚ (LaurentSeries ℚ)) :
          Set (LaurentSeries ℚ))))),
      PairProp γ hγ (coeffMap ι₀ z) (coeffMap ι₀ ((σ ⟨z, memF hz⟩ : ↥(x1FunctionFieldBar M)) :
        LaurentSeries Qb)) by
    exact h x hx'
  intro z hz
  induction hz using Subfield.closure_induction with
  | mem z hz =>
      rcases hz with ⟨c, rfl⟩ | ⟨y, hy, rfl⟩
      ·
        have e : (⟨algebraMap Qb (LaurentSeries Qb) c, memF (Subfield.subset_closure (Or.inl ⟨c, rfl⟩))⟩ :
            ↥(x1FunctionFieldBar M)) = algebraMap Qb ↥(x1FunctionFieldBar M) c :=
          Subtype.ext (SubalgebraClass.coe_algebraMap _ c).symm
        rw [e, AlgEquiv.commutes, SubalgebraClass.coe_algebraMap, coeffMap_algebraMap]
        exact pair_const γ hγ _
      ·
        have e := hbc ⟨y, hy⟩
        have e' : (σ ⟨coeffEmb Qb y, memF (Subfield.subset_closure (Or.inr ⟨y, hy, rfl⟩))⟩ :
            LaurentSeries Qb) = coeffEmb Qb ((diamondAut M d ⟨y, hy⟩ : ↥(x1FunctionField M)) :
              LaurentSeries ℚ) := e
        rw [e', coeffMap_coeffEmb, coeffMap_coeffEmb]
        exact pair_gen γ hγ hda hγd hy
  | one =>
      have e : (⟨(1 : LaurentSeries Qb), memF (Subfield.closure _).one_mem⟩ : ↥(x1FunctionFieldBar M)) = 1 := rfl
      rw [e, show σ 1 = 1 from map_one σ, OneMemClass.coe_one, map_one]
      have := pair_const γ hγ 1
      rwa [map_one] at this
  | add a b ha hb iha ihb =>
      have e : (⟨a + b, memF ((Subfield.closure _).add_mem ha hb)⟩ : ↥(x1FunctionFieldBar M)) =
          ⟨a, memF ha⟩ + ⟨b, memF hb⟩ := rfl
      rw [e, map_add σ, AddMemClass.coe_add, map_add, map_add]
      exact pair_add γ hγ iha ihb
  | neg a ha iha =>
      have e : (⟨-a, memF ((Subfield.closure _).neg_mem ha)⟩ : ↥(x1FunctionFieldBar M)) =
          -⟨a, memF ha⟩ := rfl
      rw [e, map_neg σ, NegMemClass.coe_neg, map_neg, map_neg]
      exact pair_neg γ hγ iha
  | inv a ha iha =>
      have e : (⟨a⁻¹, memF ((Subfield.closure _).inv_mem ha)⟩ : ↥(x1FunctionFieldBar M)) =
          (⟨a, memF ha⟩)⁻¹ := rfl
      rw [e, map_inv₀ σ, IntermediateField.coe_inv, map_inv₀, map_inv₀]
      exact pair_inv γ hγ iha
  | mul a b ha hb iha ihb =>
      have e : (⟨a * b, memF ((Subfield.closure _).mul_mem ha hb)⟩ : ↥(x1FunctionFieldBar M)) =
          ⟨a, memF ha⟩ * ⟨b, memF hb⟩ := rfl
      rw [e, map_mul σ, MulMemClass.coe_mul, map_mul, map_mul]
      exact pair_mul γ hγ iha ihb

end Dictionary


section Assembly

open ModularForm UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

local notation "Γ₁ℝ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Qb" => AlgebraicClosure ℚ

open RelrankSol

variable {M : ℕ} [NeZero M]

theorem isCurveOver_bar : IsCurveOver Qb ↥(x1FunctionFieldBar M) := by
  have hT : ModularGroup.T ∈ Gamma1 M := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  obtain ⟨x, hx, hfin⟩ :
      ∃ x : ↥(x1FunctionFieldBar M), Transcendental Qb x ∧
        FiniteDimensional (IntermediateField.adjoin Qb ({x} : Set ↥(x1FunctionFieldBar M)))
          ↥(x1FunctionFieldBar M) :=
    JOneES.exists_transcendental_finiteDimensional_laurentBaseChange Qb (Gamma1 M) hT
  have := hfin
  exact isCurveOver_of_isAlgClosed_of_transcendental x hx

omit [NeZero M] in
theorem charZero_bar : CharZero ↥(x1FunctionFieldBar M) :=
  charZero_of_injective_algebraMap (algebraMap Qb _).injective

def x0 (M : ℕ) : ↥(x1FunctionFieldBar M) :=
  ⟨coeffEmb Qb xq, coeffEmb_mem_laurentBaseChange Qb (RelrankSol.xq_mem (Gamma1 M))⟩

omit [NeZero M] in

theorem coe_x0 : ((x0 M : ↥(x1FunctionFieldBar M)) : LaurentSeries Qb) = coeffEmb Qb xq := rfl

omit [NeZero M] in

theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) : coeffEmb Qb (intSeriesC ℚ p) = intSeriesC Qb p :=
  ModularCurve.coeffEmb_intSeriesC Qb p

omit [NeZero M] in

theorem D_x0_ne_zero : D Qb ↥(x1FunctionFieldBar M) (x0 M) ≠ 0 := by
  intro h
  have h1 := congrArg (diffQExp (x1FunctionFieldBar M)) h
  rw [diffQExp_D, map_zero, coe_x0, show xq = intSeriesC ℚ (P6 ^ 2) / intSeriesC ℚ (P4 ^ 3) from rfl,
    map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC] at h1
  exact qEuler_ratio_ne_zero Qb h1

omit [NeZero M] in

theorem sigma_x0 {d : ℕ} (hda : IsDiamondAut M d (diamondAut M d))
    (hbc : IsBaseChangeAutOf Qb (diamondAut M d) (diamondAutBar M d))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M)) :
    diamondAutBar M d (x0 M) = x0 M := by
  apply Subtype.ext
  rw [coe_x0]
  have e := hbc ⟨xq, RelrankSol.xq_mem (Gamma1 M)⟩
  refine (e.trans ?_)
  congr 1

  apply coeffMap_injective (algebraMap ℚ ℂ).injective
  have key := hda.2 12 (B12M M) (A12M M) (P6 ^ 2) (P4 ^ 3) isIntegralQExp_B12M isIntegralQExp_A12M
    (intSeriesC_PA_ne_zero ℚ) γ hγ hγd
  rw [slashQExpC_eq γ hγ, slashQExpC_eq γ hγ, coe_conjForm, coe_conjForm, slash_A12M, slash_B12M] at key
  have hA := QQ_A12M_ne_zero (M := M)
  rw [coeffMap_xq]
  exact (eq_div_iff hA).mpr key

theorem main {d : ℕ}
    (hσ : ∃ σ : ↥(x1FunctionField M) ≃ₐ[ℚ] ↥(x1FunctionField M), IsDiamondAut M d σ)
    (hσ' : ∃ σ' : ↥(x1FunctionFieldBar M) ≃ₐ[Qb] ↥(x1FunctionFieldBar M),
      IsBaseChangeAutOf Qb (diamondAut M d) σ')
    (ι₀ : Qb →+* ℂ) (ω : Ω[↥(x1FunctionFieldBar M)⁄Qb]) (f : CuspForm Γ₁ℝ(M) 2)
    (hω : coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) ω) = QQ ⇑f) :
    coeffMap ι₀ (diffQExp (x1FunctionFieldBar M)
        (Differential.correspondence (diamondAutBar M d).toAlgHom (AlgHom.id Qb _) ω)) =
      QQ ⇑(CuspForm.diamondLinOne M 2 d f) := by

  have hda : IsDiamondAut M d (diamondAut M d) := isDiamondAut_diamondAut hσ
  have hbc : IsBaseChangeAutOf Qb (diamondAut M d) (diamondAutBar M d) := isBaseChangeAutOf_baseChangeAut hσ'

  obtain ⟨γ', hγ'⟩ := ModularForm.Level.exists_isDiamondLift_of_coprime hda.1
  have hγ : γ'⁻¹ ∈ Gamma0 M := (Gamma0 M).inv_mem hγ'.1
  have hγd : (((γ'⁻¹ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using hγ'.2
  have hγγ' : ((γ'⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) * (γ' : GL (Fin 2) ℝ) = 1 := by
    rw [← coeGL_mul, inv_mul_cancel]
    exact map_one (Matrix.SpecialLinearGroup.mapGL ℝ)

  have hdia : (⇑(CuspForm.diamondLinOne M 2 d f) : ℍ → ℂ) = ⇑f ∣[(2 : ℤ)] (γ' : GL (Fin 2) ℝ) :=
    ModularForm.Level.coe_diamondLinOne_apply hγ' f

  have := charZero_bar (M := M)
  have := isCurveOver_bar (M := M)

  have hrk : Module.finrank ↥(x1FunctionFieldBar M) Ω[↥(x1FunctionFieldBar M)⁄Qb] = 1 :=
    IsCurveOver.finrank_kaehler
  obtain ⟨w, hw⟩ := (finrank_eq_one_iff_of_nonzero' _ (D_x0_ne_zero (M := M))).mp hrk ω

  set σ := diamondAutBar M d with hσdef
  have hσx0 : σ (x0 M) = x0 M := sigma_x0 hda hbc hγ hγd
  have hσx0' : σ.symm (x0 M) = x0 M := by rw [AlgEquiv.symm_apply_eq]; exact hσx0.symm

  have hΘω : diffQExp (x1FunctionFieldBar M) ω =
      ((w : ↥(x1FunctionFieldBar M)) : LaurentSeries Qb) *
        qEuler Qb ((x0 M : ↥(x1FunctionFieldBar M)) : LaurentSeries Qb) := by
    rw [← hw, diffQExp_smul_D]
  have hΘσ : diffQExp (x1FunctionFieldBar M)
        (Differential.correspondence σ.toAlgHom (AlgHom.id Qb _) ω) =
      ((σ.symm w : ↥(x1FunctionFieldBar M)) : LaurentSeries Qb) *
        qEuler Qb ((x0 M : ↥(x1FunctionFieldBar M)) : LaurentSeries Qb) := by
    rw [correspondence_algEquiv_id, ← hw, pullbackAlong_smul, pullbackAlong_D]
    show diffQExp (x1FunctionFieldBar M) (σ.symm w • D Qb _ (σ.symm (x0 M))) = _
    rw [hσx0', diffQExp_smul_D]

  obtain ⟨k, G, H, hH0, h1, h2⟩ := pair_all (γ'⁻¹) hγ hda hbc hγd ι₀ (σ.symm w)
  rw [AlgEquiv.apply_symm_apply] at h2

  set xw : LaurentSeries ℂ := coeffMap ι₀ ((w : ↥(x1FunctionFieldBar M)) : LaurentSeries Qb) with hxw
  set xs : LaurentSeries ℂ :=
    coeffMap ι₀ ((σ.symm w : ↥(x1FunctionFieldBar M)) : LaurentSeries Qb) with hxs
  set qA : LaurentSeries ℂ := QQ ⇑(A12M M) with hqA
  set qB : LaurentSeries ℂ := QQ ⇑(B12M M) with hqB
  have hAne : qA ≠ 0 := QQ_A12M_ne_zero
  have hx0C : coeffMap ι₀ (qEuler Qb ((x0 M : ↥(x1FunctionFieldBar M)) : LaurentSeries Qb)) =
      qEuler ℂ (qB / qA) := by
    rw [coeffMap_qEuler, coe_x0, coeffMap_coeffEmb, coeffMap_xq]

  obtain ⟨Btop, hBtop⟩ := exists_RCtop
  set RC12 : ModularForm Γ₁ℝ(M) 26 := restrictForm (Subgroup.map_mono le_top) Btop with hRC12
  set RCn : ModularForm Γ₁ℝ(M) 26 := (-(1 / 12 : ℂ)) • RC12 with hRCn
  set A₂ : ModularForm Γ₁ℝ(M) (12 + 12) := (A12M M).mul (A12M M) with hA₂
  have hRC : QQ ⇑RC12 = HahnSeries.C (12 : ℂ) * (qB * qEuler ℂ qA - qEuler ℂ qB * qA) := hBtop
  have hA2 : QQ ⇑A₂ = qA * qA := by
    show QQ (⇑(A12M M) * ⇑(A12M M)) = _
    rw [QQ_mul]
  have hkey : qEuler ℂ (qB / qA) * (qA * qA) = QQ ⇑RCn := by
    rw [qEuler_div_mul_sq qB qA hAne, hRCn, QQ_smul, hRC, ← mul_assoc, ← map_mul,
      show (-(1 / 12 : ℂ)) * 12 = -1 by norm_num, map_neg, map_one]
    ring

  have hslA : (⇑(A12M M) : ℍ → ℂ) ∣[(12 : ℤ)] γ' = ⇑(A12M M) := by
    rw [ModularForm.SL_slash]; exact slash_A12M γ'
  have hslR : (⇑RCn : ℍ → ℂ) ∣[(26 : ℤ)] γ' = ⇑RCn := by
    rw [hRCn, FunLike.coe_smul, ModularForm.SL_smul_slash]
    congr 1
    rw [ModularForm.SL_slash]
    exact slash_top_eq Btop γ'

  have hωC : xw * qEuler ℂ (qB / qA) = QQ ⇑f := by rw [← hω, hΘω, map_mul, hx0C]
  have hQ1 : QQ ⇑(((toMF f).mul (conjForm (γ'⁻¹) hγ H)).mul A₂) =
      QQ ⇑(((conjForm (γ'⁻¹) hγ G).mul RCn).mcast (show k + 26 = 2 + k + (12 + 12) by ring)) := by
    rw [ModularForm.coe_mcast, ModularForm.coe_mul, QQ_mul, ModularForm.coe_mul, QQ_mul, coe_toMF, hA2,
      ModularForm.coe_mul, QQ_mul, ← hωC, ← h2, ← hkey]
    ring
  have hF1 := eq_of_QQ_eq hQ1
  rw [ModularForm.coe_mcast] at hF1

  have hL : (⇑(((toMF f).mul (conjForm (γ'⁻¹) hγ H)).mul A₂) : ℍ → ℂ) ∣[(2 + k) + (12 + 12)] γ' =
      ⇑(CuspForm.diamondLinOne M 2 d f) * ⇑H * (⇑(A12M M) * ⇑(A12M M)) := by
    rw [ModularForm.coe_mul, ModularForm.coe_mul, hA₂, ModularForm.coe_mul, ModularForm.mul_slash_SL2,
      ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2, hslA, coe_toMF, hdia, coe_conjForm,
      ModularForm.SL_slash, ModularForm.SL_slash, ← SlashAction.slash_mul, hγγ', SlashAction.slash_one]
  have hR : (⇑((conjForm (γ'⁻¹) hγ G).mul RCn) : ℍ → ℂ) ∣[k + 26] γ' = ⇑G * ⇑RCn := by
    rw [ModularForm.coe_mul, ModularForm.mul_slash_SL2, hslR, coe_conjForm, ModularForm.SL_slash,
      ← SlashAction.slash_mul, hγγ', SlashAction.slash_one]
  have hF2 : ⇑(CuspForm.diamondLinOne M 2 d f) * ⇑H * (⇑(A12M M) * ⇑(A12M M)) = ⇑G * ⇑RCn := by
    rw [← hL, ← hR, hF1, show (2 + k + (12 + 12) : ℤ) = k + 26 by ring]

  have e1 : QQ ⇑(((toMF (CuspForm.diamondLinOne M 2 d f)).mul H).mul A₂) =
      QQ ⇑(CuspForm.diamondLinOne M 2 d f) * QQ ⇑H * (qA * qA) := by
    rw [ModularForm.coe_mul, QQ_mul, ModularForm.coe_mul, QQ_mul, coe_toMF, hA2]
  have e2 : QQ ⇑(G.mul RCn) = QQ ⇑G * QQ ⇑RCn := by
    rw [ModularForm.coe_mul, QQ_mul]
  have hQ2 : QQ ⇑(CuspForm.diamondLinOne M 2 d f) * QQ ⇑H * (qA * qA) = QQ ⇑G * QQ ⇑RCn := by
    rw [← e1, ← e2]
    exact congrArg QQ hF2

  rw [hΘσ, map_mul, hx0C]
  have hne : QQ ⇑H * (qA * qA) ≠ 0 := mul_ne_zero hH0 (mul_ne_zero hAne hAne)
  apply mul_right_cancel₀ hne
  linear_combination (qEuler ℂ (qB / qA) * (qA * qA)) * h1 + (QQ ⇑G) * hkey - hQ2

end Assembly

/-- The diamond correspondence on the `X₁` function field: the `q`-expansion of
`correspondence (diamondAutBar M d) id ω` is the diamond operator applied to `f`. -/
theorem coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne
    (M : ℕ) [NeZero M] {d : ℕ}
    (hσ : ∃ σ : ↥(ModularCurve.x1FunctionField M) ≃ₐ[ℚ] ↥(ModularCurve.x1FunctionField M),
      ModularCurve.IsDiamondAut M d σ)
    (hσ' : ∃ σ' : ↥(ModularCurve.x1FunctionFieldBar M) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.x1FunctionFieldBar M),
      ModularCurve.IsBaseChangeAutOf (AlgebraicClosure ℚ) (ModularCurve.diamondAut M d) σ')
    (ι₀ : AlgebraicClosure ℚ →+* ℂ)
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ])
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (hω : ModularCurve.coeffMap ι₀ (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f)) :
    ModularCurve.coeffMap ι₀
        (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
          (AlgebraicCurve.Differential.correspondence
            (ModularCurve.diamondAutBar M d).toAlgHom
            (AlgHom.id (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)) ω)) =
      HahnSeries.ofPowerSeries ℤ ℂ
        (UpperHalfPlane.qExpansion 1 ⇑(CuspForm.diamondLinOne M 2 d f)) :=
  main hσ hσ' ι₀ ω f hω


section DiamondComm

open CongruenceSubgroup UpperHalfPlane ModularForm

local notation "Γ₁ℝ(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {M : ℕ}

/-! ### The diamond operators commute

The leaf row `ModularCurve.diamondOneBar_comm` (LV-6), over the `S_` copy's
`X1DiaComm` engine.  The engine is transcribed with the port's spellings for the
q-expansion bookkeeping (`QQ`, `eq_of_QQ_eq`, `slashQExpC_eq`) and the port's
`mem_ratios_of_mem`; the diamond-side statements are the pin's. -/

theorem exists_gamma0 {M d : ℕ} (h : Nat.Coprime d M) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M ∧ ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr h : IsCoprime (d : ℤ) (M : ℤ))
  refine ⟨?_, Gamma0_mem.mpr ?_, ?_⟩
  · exact ⟨!![(d : ℤ), -v; (M : ℤ), u], by
      rw [Matrix.det_fin_two_of]; linear_combination huv⟩
  · simp
  · simp

theorem entry_inv_mul {M : ℕ} {γ₁ γ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 M) (h : γ ∈ Gamma0 M)
    {a b : ZMod M} (ha : ((γ₁ 0 0 : ℤ) : ZMod M) = a) (hab : ((γ 0 0 : ℤ) : ZMod M) = a * b) :
    (((γ₁⁻¹ * γ) 0 0 : ℤ) : ZMod M) = b := by
  have hdet : (γ₁ 0 0 : ℤ) * γ₁ 1 1 - γ₁ 0 1 * γ₁ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ₁
    rwa [Matrix.det_fin_two] at this
  have hdet' : ((γ₁ 0 0 : ℤ) : ZMod M) * ((γ₁ 1 1 : ℤ) : ZMod M)
      - ((γ₁ 0 1 : ℤ) : ZMod M) * ((γ₁ 1 0 : ℤ) : ZMod M) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod M) hdet
  have hC : ((γ₁ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp h₁
  have hg : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp h
  have hentry : ((γ₁⁻¹ * γ) 0 0 : ℤ) = γ₁ 1 1 * γ 0 0 + (-γ₁ 0 1) * γ 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.SL2_inv_expl,
      Matrix.mul_apply]
    simp [Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hentry]
  push_cast
  linear_combination ((γ₁ 1 1 : ℤ) : ZMod M) * hab + (-((γ₁ 0 1 : ℤ) : ZMod M)) * hg
    + (-(b * ((γ₁ 1 1 : ℤ) : ZMod M))) * ha + b * hdet' + (b * ((γ₁ 0 1 : ℤ) : ZMod M)) * hC

theorem qexp_mul {a b : ℤ} (F : ModularForm Γ₁ℝ(M) a) (G : ModularForm Γ₁ℝ(M) b) :
    qExpansion 1 (⇑F * ⇑G) = qExpansion 1 F * qExpansion 1 G :=
  ModularForm.qExpansion_mul_coe one_pos (one_mem_strictPeriods M) F G

theorem eq_of_qexp_eq {k : ℤ} {F G : ModularForm Γ₁ℝ(M) k}
    (h : qExpansion 1 (⇑F) = qExpansion 1 (⇑G)) : (⇑F : ℍ → ℂ) = ⇑G :=
  eq_of_QQ_eq (show QQ ⇑F = QQ ⇑G from congrArg (ofPowerSeries ℤ ℂ) h)

theorem slashQExpC_ne_zero {k : ℤ} {g : ModularForm Γ₁ℝ(M) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    slashQExpC k g γ ≠ 0 := by
  rw [slashQExpC_eq γ hγ]
  refine (map_ne_zero_iff _ ofPowerSeries_injective).mpr ?_
  rw [Ne, ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods M)]
  exact conjForm_ne_zero γ hγ (ne_zero_of_isIntegralQExp hg hg0)

theorem ofPowerSeries_qexp_ne_zero {k : ℤ} {g : ModularForm Γ₁ℝ(M) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g)) ≠ 0 := by
  change QQ ⇑g ≠ 0
  rw [show QQ ⇑g = intSeriesC ℂ pg from (intSeriesC_eq_of_isIntegralQExp hg).symm, Ne,
    intSeriesC_eq_zero_iff]
  exact fun h => hg0 (by rw [h, intSeriesC_zero])

theorem mem_intFormRatiosC_of_mem {y : LaurentSeries ℚ} (hy : y ∈ x1FunctionField M) :
    y ∈ intFormRatiosC ℚ (Gamma1 M) :=
  A2K1A.mem_ratios_of_mem (one_mem_strictPeriods M) hy

theorem isDiamondAut_apply {d : ℕ} {σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M}
    (h : IsDiamondAut M d σ) (k : ℤ) (f g : ModularForm Γ₁ℝ(M) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγd : ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M))
    (hx : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ x1FunctionField M) :
    coeffMap (algebraMap ℚ ℂ)
        ((σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, hx⟩ : x1FunctionField M) : LaurentSeries ℚ)
      * slashQExpC k g γ = slashQExpC k f γ :=
  h.2 k f g pf pg hf hg hg0 γ hγ hγd

theorem algEquiv_ext_of_ratios {σ σ' : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M}
    (h : ∀ (x : LaurentSeries ℚ) (hx : x ∈ intFormRatiosC ℚ (Gamma1 M)),
      σ ⟨x, intFormRatiosC_subset ℚ _ hx⟩ = σ' ⟨x, intFormRatiosC_subset ℚ _ hx⟩) : σ = σ' := by
  apply AlgEquiv.ext
  rintro ⟨y, hy⟩
  have hy' : y ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (Gamma1 M)) := hy
  induction hy' using IntermediateField.adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r =>
      have e : (⟨algebraMap ℚ (LaurentSeries ℚ) r, IntermediateField.algebraMap_mem _ r⟩ :
          x1FunctionField M) = (r : x1FunctionField M) := by
        apply Subtype.ext
        rw [SubfieldClass.coe_ratCast]
        exact eq_ratCast _ r
      rw [e, map_ratCast, map_ratCast]
  | add x x' hx hx' ihx ihx' =>
      have e : (⟨x + x', add_mem hx hx'⟩ : x1FunctionField M) = ⟨x, hx⟩ + ⟨x', hx'⟩ := rfl
      rw [e, map_add, map_add, ihx hx, ihx' hx']
  | inv x hx ihx =>
      have e : (⟨x⁻¹, inv_mem hx⟩ : x1FunctionField M) = ⟨x, hx⟩⁻¹ := rfl
      rw [e, map_inv₀, map_inv₀, ihx hx]
  | mul x x' hx hx' ihx ihx' =>
      have e : (⟨x * x', mul_mem hx hx'⟩ : x1FunctionField M) = ⟨x, hx⟩ * ⟨x', hx'⟩ := rfl
      rw [e, map_mul, map_mul, ihx hx, ihx' hx']

theorem isDiamondAut_unique {d : ℕ} {σ σ' : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M}
    (hσ : IsDiamondAut M d σ) (hσ' : IsDiamondAut M d σ') : σ = σ' := by
  obtain ⟨γ, hγ, hγd⟩ := exists_gamma0 hσ.1
  refine algEquiv_ext_of_ratios fun x hx => ?_
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  apply Subtype.ext
  apply coeffMap_injective (algebraMap ℚ ℂ).injective
  apply mul_right_cancel₀ (slashQExpC_ne_zero hg hg0 hγ)
  exact (isDiamondAut_apply hσ k f g pf pg hf hg hg0 γ hγ hγd _).trans
    (isDiamondAut_apply hσ' k f g pf pg hf hg hg0 γ hγ hγd _).symm

theorem isDiamondAut_trans {d e : ℕ} {σ τ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M}
    (hσ : IsDiamondAut M d σ) (hτ : IsDiamondAut M e τ) :
    IsDiamondAut M (d * e) (σ.trans τ) := by
  refine ⟨Nat.Coprime.mul_left hσ.1 hτ.1, fun k f g pf pg hf hg hg0 γ hγ hγde => ?_⟩
  obtain ⟨γd, hγd, hγdd⟩ := exists_gamma0 hσ.1
  set γe : SL(2, ℤ) := γd⁻¹ * γ with hγe_def
  have hγe : γe ∈ Gamma0 M := (Gamma0 M).mul_mem ((Gamma0 M).inv_mem hγd) hγ
  have hγee : ((γe 0 0 : ℤ) : ZMod M) = (e : ZMod M) :=
    entry_inv_mul hγd hγ hγdd (by rw [hγde, Nat.cast_mul])
  have hγfac : (γd : GL (Fin 2) ℝ) * (γe : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) := by
    rw [← coeGL_mul, hγe_def, mul_inv_cancel_left]

  set y : x1FunctionField M :=
    σ ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ with hy_def
  have H1 := isDiamondAut_apply hσ k f g pf pg hf hg hg0 γd hγd hγdd
    (div_mem_qExpFunctionFieldC f g hf hg hg0)
  rw [← hy_def] at H1
  obtain ⟨k', f', g', pf', pg', hf', hg', hg0', hyv⟩ := mem_intFormRatiosC_of_mem y.2
  have hy : y = ⟨intSeriesC ℚ pf' / intSeriesC ℚ pg', div_mem_qExpFunctionFieldC f' g' hf' hg' hg0'⟩ :=
    Subtype.ext hyv
  have H2 := isDiamondAut_apply hτ k' f' g' pf' pg' hf' hg' hg0' γe hγe hγee
    (div_mem_qExpFunctionFieldC f' g' hf' hg' hg0')
  rw [AlgEquiv.trans_apply, ← hy_def, hy]

  set Fd := conjForm γd hγd f
  set Gd := conjForm γd hγd g
  set F'e := conjForm γe hγe f'
  set G'e := conjForm γe hγe g'
  set Fγ := conjForm γ hγ f
  set Gγ := conjForm γ hγ g

  have hyC : coeffMap (algebraMap ℚ ℂ) (y : LaurentSeries ℚ) =
      ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f')) / ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g')) := by
    rw [hyv, map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC, intSeriesC_eq_of_isIntegralQExp hf',
      intSeriesC_eq_of_isIntegralQExp hg']
  have hg'C := ofPowerSeries_qexp_ne_zero hg' hg0'
  rw [hyC, slashQExpC_eq γd hγd, slashQExpC_eq γd hγd,
    div_mul_eq_mul_div, div_eq_iff hg'C, ← map_mul, ← map_mul] at H1
  have H1' : qExpansion 1 (⇑f' * ⇑Gd) = qExpansion 1 (⇑g' * ⇑Fd) := by
    rw [qexp_mul, qexp_mul, mul_comm (qExpansion 1 (⇑g'))]
    exact ofPowerSeries_injective H1

  have E1 : (⇑f' : ℍ → ℂ) * ⇑Gd = ⇑g' * ⇑Fd := by
    have := eq_of_qexp_eq (F := f'.mul Gd) (G := g'.mul Fd)
      (by rw [ModularForm.coe_mul, ModularForm.coe_mul]; exact H1')
    rwa [ModularForm.coe_mul, ModularForm.coe_mul] at this
  have E2 : (⇑F'e : ℍ → ℂ) * ⇑Gγ = ⇑G'e * ⇑Fγ := by
    have := congrArg (fun F : ℍ → ℂ => F ∣[k' + k] γe) E1
    rw [ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2] at this
    simp only [ModularForm.SL_slash] at this
    simp only [Fd, Gd, coe_conjForm, ← SlashAction.slash_mul, hγfac] at this
    simpa only [F'e, G'e, Fγ, Gγ, coe_conjForm] using this

  have E3 : slashQExpC k' f' γe * slashQExpC k g γ = slashQExpC k' g' γe * slashQExpC k f γ := by
    rw [slashQExpC_eq γe hγe, slashQExpC_eq γe hγe, slashQExpC_eq γ hγ,
      slashQExpC_eq γ hγ, ← map_mul, ← map_mul, ← qexp_mul, ← qexp_mul]
    exact congrArg _ (congrArg _ E2)

  apply mul_right_cancel₀ (slashQExpC_ne_zero hg' hg0' hγe)
  linear_combination (slashQExpC k g γ) * H2 + E3

theorem diamondAut_comm (M d e : ℕ) :
    (diamondAut M d).trans (diamondAut M e) = (diamondAut M e).trans (diamondAut M d) := by
  rcases Classical.em (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M d σ)
    with hd | hd
  · rcases Classical.em (∃ σ : x1FunctionField M ≃ₐ[ℚ] x1FunctionField M, IsDiamondAut M e σ)
      with he | he
    · have h1 := isDiamondAut_trans (isDiamondAut_diamondAut hd) (isDiamondAut_diamondAut he)
      have h2 := isDiamondAut_trans (isDiamondAut_diamondAut he) (isDiamondAut_diamondAut hd)
      rw [Nat.mul_comm] at h2
      exact isDiamondAut_unique h1 h2
    · rw [diamondAut_of_not he]
      ext x
      rfl
  · rw [diamondAut_of_not hd]
    ext x
    rfl

section BaseChange

variable {L : Type*} [Field L] [Algebra ℚ L] {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

theorem isBaseChangeAutOf_unique {σ₀ : F₀ ≃ₐ[ℚ] F₀}
    {τ τ' : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀}
    (h : IsBaseChangeAutOf L σ₀ τ) (h' : IsBaseChangeAutOf L σ₀ τ') : τ = τ' := by
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := L)
    (s := ⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ))) rfl ?_
  rintro x ⟨y, hy, rfl⟩
  apply Subtype.ext
  exact (h ⟨y, hy⟩).trans (h' ⟨y, hy⟩).symm

theorem isBaseChangeAutOf_trans {σ₀ σ₁ : F₀ ≃ₐ[ℚ] F₀}
    {τ τ' : laurentBaseChange L F₀ ≃ₐ[L] laurentBaseChange L F₀}
    (h : IsBaseChangeAutOf L σ₀ τ) (h' : IsBaseChangeAutOf L σ₁ τ') :
    IsBaseChangeAutOf L (σ₀.trans σ₁) (τ.trans τ') := by
  intro y
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have e : τ ⟨coeffEmb L (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L y.2⟩ =
      ⟨coeffEmb L ((σ₀ y : F₀) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L (σ₀ y).2⟩ :=
    Subtype.ext (h y)
  rw [e]
  exact h' (σ₀ y)

theorem baseChangeAut_refl :
    baseChangeAut L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) = AlgEquiv.refl := by
  have h0 : IsBaseChangeAutOf L (AlgEquiv.refl : F₀ ≃ₐ[ℚ] F₀) AlgEquiv.refl := fun _ => rfl
  exact isBaseChangeAutOf_unique (isBaseChangeAutOf_baseChangeAut ⟨_, h0⟩) h0

end BaseChange

theorem diamondAutBar_comm (M d e : ℕ) :
    (diamondAutBar M d).trans (diamondAutBar M e) = (diamondAutBar M e).trans (diamondAutBar M d) := by
  have hcomm := diamondAut_comm M d e
  rcases Classical.em (∃ τ : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
      IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M d) τ) with hd | hd
  · rcases Classical.em (∃ τ : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
        IsBaseChangeAutOf (AlgebraicClosure ℚ) (diamondAut M e) τ) with he | he
    · have h1 := isBaseChangeAutOf_trans (isBaseChangeAutOf_baseChangeAut hd)
        (isBaseChangeAutOf_baseChangeAut he)
      have h2 := isBaseChangeAutOf_trans (isBaseChangeAutOf_baseChangeAut he)
        (isBaseChangeAutOf_baseChangeAut hd)
      rw [← hcomm] at h2
      exact isBaseChangeAutOf_unique h1 h2
    · rw [diamondAutBar, diamondAutBar, baseChangeAut_of_not he]
      ext x
      rfl
  · rw [diamondAutBar, diamondAutBar, baseChangeAut_of_not hd]
    ext x
    rfl

end DiamondComm

end DiamondCorrespondence

/-- **The diamond operators commute.** The endomorphisms `diamondOneBar M d` of
`J₁(M)` (the `diamondAutBar` action) commute. -/
theorem diamondOneBar_comm (M d e : ℕ) :
    diamondOneBar M d * diamondOneBar M e =
      diamondOneBar M e * diamondOneBar M d := by
  have h : diamondAutBar M d * diamondAutBar M e = diamondAutBar M e * diamondAutBar M d :=
    (DiamondCorrespondence.diamondAutBar_comm M d e).symm
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, diamondOneBar_apply]
  rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, h]

end ModularCurve

end
