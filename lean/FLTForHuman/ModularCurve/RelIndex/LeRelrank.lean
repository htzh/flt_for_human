/-
  `[Γ : Γ₀(N)] ≤ [A(j(q^N)) : A]` — the degeneracy-cover degree, the `relIndex` side.

  For `Γ ≤ SL(2, ℤ)` with `T ∈ Γ` and `N ≠ 0`, and `A = A(Γ)` the field of ratios of
  `q`-expansions of modular forms on `Γ`:

  `[Γ : Γ₀(N)] ≤ [A(j(q^N)) : A]`  ("enough conjugates").

  The proof exhibits `relIndex`-many distinct series `ρ(γ)` — the `nA²`-stretched twists
  of `j` indexed by the `Γ₀(N)`-cosets of `Γ` — as roots of a polynomial of degree
  `< relIndex`; the cosets are parametrised by the Hermite normal form of `γ`, and the
  injectivity `ρ(γ₁) = ρ(γ₂) → γ₂γ₁⁻¹ ∈ Γ₀(N)` is read off the coefficient of `q⁻¹`.

  This is `P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean`
  (pin `aa2d8b3`), whose wrapper is the headline below. The engine is `private`: the
  module's public surface is the one headline.

  Reuse, not restatement. The frozen ground of this set carries everything the pin's
  prelude spells out inline:

  * `RelIndex.one_mem_strictPeriods`, `natCast_mem_strictPeriods`,
    `one_mem_strictPeriods_{conj,conjDiag,twist}`, `raise`/`raise_apply`/`coe_raise`/
    `coeff_qExpansion_raise`, `twist`/`twist_apply`/`coe_twist`, `expU`/`val_expU`,
    `twRaiseFn`/`twRaiseFn_eq`, `hP`/`val_hP`/`heckeDiag_mul_eq`/`heckeDiag_smul_smul`/
    `coe_hP_smul`/`hP_smul_heckeDiag_smul`, `qParam_Ux_smul`, `coeff_qExpansion_twist`
    (`ModularCurve/RelIndex/LevelRaise.lean`);
  * `dMul` … `mul_inv_mem_Gamma0_of_hermite_eq` (`ModularCurve/RelIndex/Hermite.lean`);
  * `ratioSet`/`ratioField`, `qC_mul`/`qC_add`/`qC_neg`, `qC_const`, the `*_mem_ratioSet`
    block, `mem_ratioSet_of_mem_adjoin`, `common_denominator`, `coe_finset_sum`,
    `qC_raise`/`qC_twist`/`qC_twRaiseFn` (`ModularCurve/RelIndex/RatioField.lean`);
  * `AnalyticAtCusp` (the pin's `An1`) and its `q`-expansion API
    (`ModularCurve/Analytic/AnalyticAtCusp.lean`);
  * `e4cube`/`delta`/`isIntegralQExp_{e4cube,delta}`/`coe_delta`/`intSeriesC_delta_ne_zero`/
    `jqModC_mul_delta`/`jqModC_eq_div` (`ModularCurve/JqIntegralRatios.lean`).

  The pin's `S`/`SField` spelling is not reproduced: this body uses `ratioSet` (the port's
  one home for it) and `change`s the headline's set literal to it.

  The pin's `conjMat`/`det_conjMat`/`conjSL`/`heckeDiag_mul_mul_inv`/`dvd_of_mem_Gamma0`
  are *not* in this set's frozen ground. They are imported from the port's subject home
  `ModularCurve.HeckeInputsHAll` (`XH/HeckeInputs.lean`), where the same block lives at a
  general `ℓ` with an extra `hℓ : ℓ ≠ 0`; this body instantiates `ℓ := N` and supplies
  `NeZero.ne N`, and its `dvd_of_mem_Gamma0` is that module's `dvd_of_mem_Gamma0_mul` at
  `M := 1` (`Gamma0 (1 * N)`, bridged by `Nat.one_mul`).

  Dead code, pruned (`tools/deps/move_dead.py --select dead`). The pin's level-one pair
  `XA_ne_zero`/`jC_ne_zero` (`S_` lines 103, 110) and its `coe_DF` (line 56, `rfl` in the
  pin) are transcribed *public* in the `S_` file but the headline does not reach the port's
  copies; they were `private` here, so nothing could import them, and each is at most seven
  lines from the public API the module already has (`coe_delta`, `XD_ne_zero`,
  `jqModC_eq_jC` + `coeff_jqModC_neg_one`). Pruned rather than shelved — a shelf would
  duplicate the five live premises `XA`/`XD`/`DF`/`jC`/`jqModC_eq_jC` for twelve lines
  (playbook §3.8's bin rule).

  `coeff_jqModC_neg_one` is imported, not re-proved: its one home is `Defs/JqCoeff.lean`
  (the pole at the cusp), which replaces the local copy this module used to carry.

  FLT provenance, pinned `aa2d8b3`:
  spec-pin: Theorems/Thm_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean
  spec-pin: P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relIndex_gamma0_le_relrank_adjoin_insert_jqNModC.lean
-/
import FLTForHuman.ModularCurve.Analytic.AnalyticAtCusp
import FLTForHuman.ModularCurve.RelIndex.Hermite
import FLTForHuman.ModularCurve.RelIndex.LevelRaise
import FLTForHuman.ModularCurve.RelIndex.RatioField
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.XH.HeckeInputs
import FLTForHuman.ModularCurve.Defs.Twist
import Mathlib.FieldTheory.Relrank

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

open ModularCurve HahnSeries UpperHalfPlane CongruenceSubgroup IntermediateField ModularForm Matrix

namespace ModularCurve

open ModularCurve.DiamondLift (qC)

namespace RelIndexJqSol

open RelIndex

/-! ## The level-one forms `E₄³` and `Δ`, and `j = E₄³/Δ` -/

section LevelOne

private abbrev SLtop : Subgroup (GL (Fin 2) ℝ) :=
  ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem hSL1 : (1 : ℝ) ∈ (SLtop).strictPeriods :=
  one_mem_strictPeriods (Subgroup.mem_top _)

private abbrev AF : ModularForm SLtop 12 := e4cube ⊤

private abbrev DF : ModularForm SLtop 12 := delta ⊤

private theorem isIntegralQExp_AF : IsIntegralQExp (AF : ℍ → ℂ) (eisenstein4 ^ 3) :=
  isIntegralQExp_e4cube ⊤

private theorem isIntegralQExp_DF :
    IsIntegralQExp (DF : ℍ → ℂ) (PowerSeries.X * dedekindEtaUnit) :=
  isIntegralQExp_delta ⊤

private theorem intSeriesC_eq_qC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    intSeriesC ℂ p = qC F := by
  rw [intSeriesC, qC]
  exact congrArg _ h

private def XA : LaurentSeries ℂ := qC AF

private def XD : LaurentSeries ℂ := qC DF

private def jC : LaurentSeries ℂ := XA / XD

private theorem XD_ne_zero : XD ≠ 0 := by
  rw [XD, ← intSeriesC_eq_qC isIntegralQExp_DF]
  exact intSeriesC_delta_ne_zero ℂ

private theorem jqModC_eq_jC : jqModC ℂ = jC := by
  have hXA : intSeriesC ℂ (eisenstein4 ^ 3) = XA := intSeriesC_eq_qC isIntegralQExp_AF
  have hXD : intSeriesC ℂ (PowerSeries.X * dedekindEtaUnit) = XD :=
    intSeriesC_eq_qC isIntegralQExp_DF
  rw [jC, ← hXA, ← hXD]
  exact (eq_div_iff (intSeriesC_delta_ne_zero ℂ)).mpr (jqModC_mul_delta (K := ℂ))

private theorem jC_coeff_neg_one : jC.coeff (-1) = 1 := by
  rw [← jqModC_eq_jC]
  exact coeff_jqModC_neg_one (K := ℂ)

private theorem jC_coeff_of_lt {m : ℤ} (hm : m < -1) : jC.coeff m = 0 := by
  rw [← jqModC_eq_jC, jqModC, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

end LevelOne

/-! ## The two level structures of `Γ` -/

section Core

variable (Γ : Subgroup SL(2, ℤ)) (N : ℕ) [NeZero N]

private abbrev GamGL : Subgroup (GL (Fin 2) ℝ) :=
  ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private abbrev Gam'GL : Subgroup (GL (Fin 2) ℝ) :=
  ((Γ ⊓ Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

variable {Γ N}

omit [NeZero N] in
private theorem T_mem_inf (hT : ModularGroup.T ∈ Γ) : ModularGroup.T ∈ Γ ⊓ Gamma0 N := by
  refine Subgroup.mem_inf.mpr ⟨hT, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

private theorem hΓ1 (hT : ModularGroup.T ∈ Γ) : (1 : ℝ) ∈ (GamGL Γ).strictPeriods :=
  one_mem_strictPeriods hT

omit [NeZero N] in
private theorem hΓ'1 (hT : ModularGroup.T ∈ Γ) : (1 : ℝ) ∈ (Gam'GL Γ N).strictPeriods :=
  one_mem_strictPeriods (T_mem_inf hT)

variable (Γ N) in

private theorem gam'_le_conj :
    Gam'GL Γ N ≤ ConjAct.toConjAct (heckeDiagMatrix N)⁻¹ • SLtop := by
  rintro x ⟨γ, hγ, rfl⟩
  obtain ⟨-, hγ0⟩ := Subgroup.mem_inf.mp hγ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have hγ0' : γ ∈ Gamma0 (1 * N) := by simpa using hγ0
  exact ⟨_, Subgroup.mem_top _,
    (HeckeInputsHAll.heckeDiag_mul_mul_inv
      (HeckeInputsHAll.dvd_of_mem_Gamma0_mul (M := 1) hγ0') (NeZero.ne N)).symm⟩

/-! ## The raised level-one forms and the `Φ` construction -/

variable (Γ N) in

private def LA : ModularForm (Gam'GL Γ N) 12 := restrictForm (gam'_le_conj Γ N) (raise N AF)

variable (Γ N) in

private def LD : ModularForm (Gam'GL Γ N) 12 := restrictForm (gam'_le_conj Γ N) (raise N DF)

private theorem LA_apply (τ : ℍ) : LA Γ N τ = AF (heckeDiagMatrix N • τ) := by
  rw [LA, restrictForm_apply, raise_apply]

private theorem LD_apply (τ : ℍ) : LD Γ N τ = DF (heckeDiagMatrix N • τ) := by
  rw [LD, restrictForm_apply, raise_apply]

private theorem qC_LA : qC (LA Γ N) = qExpand ℂ N XA := by
  rw [LA, coe_restrictForm]; exact qC_raise hSL1 N AF

private theorem qC_LD : qC (LD Γ N) = qExpand ℂ N XD := by
  rw [LD, coe_restrictForm]; exact qC_raise hSL1 N DF

private theorem weight_eq (k : ℤ) {m : ℕ} (i : Fin (m + 1)) :
    k + ((((i : ℕ) : ℤ)) * 12 + ((m - (i : ℕ) : ℕ) : ℤ) * 12) = k + 12 * m := by
  have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.is_lt
  push_cast [Nat.cast_sub hi]
  ring

variable (Γ N) in

private def termF {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (i : Fin (m + 1)) : ModularForm (Gam'GL Γ N) (k + 12 * m) :=
  ((restrictForm (Subgroup.map_mono inf_le_left) (f i)).mul
    (((LA Γ N).pow (i : ℕ)).mul ((LD Γ N).pow (m - (i : ℕ))))).mcast (weight_eq k i)

variable (Γ N) in

private def Phi {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k) :
    ModularForm (Gam'GL Γ N) (k + 12 * m) :=
  ∑ i, termF Γ N f i

private theorem coe_termF {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (i : Fin (m + 1)) (τ : ℍ) :
    termF Γ N f i τ = f i τ * LA Γ N τ ^ (i : ℕ) * LD Γ N τ ^ (m - (i : ℕ)) := by
  rw [termF, coe_mcast]
  simp only [coe_mul, coe_pow, Pi.mul_apply, Pi.pow_apply, coe_restrictForm]
  ring

private theorem Phi_apply {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k) (τ : ℍ) :
    Phi Γ N f τ = ∑ i, f i τ * LA Γ N τ ^ (i : ℕ) * LD Γ N τ ^ (m - (i : ℕ)) := by
  rw [Phi, coe_finset_sum, Finset.sum_apply]
  simp only [coe_termF]

private theorem qExpansion_finset_sum {Γg : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (hΓ : (1 : ℝ) ∈ Γg.strictPeriods) {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm Γg k) :
    qExpansion 1 (⇑(∑ i ∈ s, F i)) = ∑ i ∈ s, qExpansion 1 (F i) :=
  map_sum (ModularForm.qExpansionAddHom one_pos hΓ k) F s

private theorem qC_termF (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ}
    (f : Fin (m + 1) → ModularForm (GamGL Γ) k) (i : Fin (m + 1)) :
    qC (termF Γ N f i) =
      qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) := by
  rw [qC, termF, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos (hΓ'1 hT),
    ModularForm.qExpansion_mul one_pos (hΓ'1 hT), ModularForm.qExpansion_pow one_pos (hΓ'1 hT),
    ModularForm.qExpansion_pow one_pos (hΓ'1 hT), map_mul, map_mul, map_pow, map_pow,
    ← qC_LA (Γ := Γ) (N := N), ← qC_LD (Γ := Γ) (N := N), mul_assoc]
  rfl

private theorem qC_Phi (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ}
    (f : Fin (m + 1) → ModularForm (GamGL Γ) k) :
    qC (Phi Γ N f) =
      ∑ i, qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) := by
  rw [qC, Phi, qExpansion_finset_sum (hΓ'1 hT), map_sum]
  exact Finset.sum_congr rfl fun i _ => qC_termF hT f i

private theorem Phi_eq_zero (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ}
    (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (hrel : ∑ i, qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) = 0) :
    Phi Γ N f = 0 := by
  have h1 : qC (Phi Γ N f) = 0 := by rw [qC_Phi hT, hrel]
  have h2 : qExpansion 1 (Phi Γ N f) = 0 := by
    rw [qC, ← map_zero (ofPowerSeries ℤ ℂ)] at h1
    exact ofPowerSeries_injective h1
  exact (ModularForm.qExpansion_eq_zero_iff one_pos (hΓ'1 hT) _).mp h2

/-! ## Evaluating the raised `Φ` at the cusps of `Γ` -/

private theorem rel_at_P {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (hΦ : Phi Γ N f = 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    ∑ i, f i τ * AF (hP N γ • τ) ^ (i : ℕ) * DF (hP N γ • τ) ^ (m - (i : ℕ)) = 0 := by
  have h0 : Phi Γ N f ((γ : SL(2, ℤ)) • τ) = 0 := by rw [hΦ]; rfl
  rw [Phi_apply] at h0
  set d : ℂ := UpperHalfPlane.denom (γ : SL(2, ℤ)) τ with hd
  set w : ℍ := hP N γ • τ with hw
  set e : ℂ := UpperHalfPlane.denom (hδ N γ : SL(2, ℤ)) w with he
  have hd0 : d ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have he0 : e ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hf : ∀ i, f i ((γ : SL(2, ℤ)) • τ) = d ^ k * f i τ := fun i =>
    SlashInvariantForm.slash_action_eqn_SL'' (f i) hγ τ
  have hA : LA Γ N ((γ : SL(2, ℤ)) • τ) = e ^ (12 : ℤ) * AF w := by
    rw [LA_apply, heckeDiag_smul_smul]
    exact SlashInvariantForm.slash_action_eqn_SL'' AF (Subgroup.mem_top _) w
  have hD : LD Γ N ((γ : SL(2, ℤ)) • τ) = e ^ (12 : ℤ) * DF w := by
    rw [LD_apply, heckeDiag_smul_smul]
    exact SlashInvariantForm.slash_action_eqn_SL'' DF (Subgroup.mem_top _) w
  simp only [hf, hA, hD] at h0
  have key : ∀ i : Fin (m + 1),
      d ^ k * f i τ * (e ^ (12 : ℤ) * AF w) ^ (i : ℕ) * (e ^ (12 : ℤ) * DF w) ^ (m - (i : ℕ)) =
        (d ^ k * (e ^ (12 : ℤ)) ^ m) * (f i τ * AF w ^ (i : ℕ) * DF w ^ (m - (i : ℕ))) := by
    intro i
    have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.is_lt
    have hE : (e ^ (12 : ℤ)) ^ (i : ℕ) * (e ^ (12 : ℤ)) ^ (m - (i : ℕ)) = (e ^ (12 : ℤ)) ^ m := by
      rw [← _root_.pow_add, Nat.add_sub_cancel' hi]
    rw [mul_pow, mul_pow, ← hE]
    ring
  simp only [key, ← Finset.mul_sum] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exfalso
    exact mul_ne_zero (zpow_ne_zero _ hd0) (pow_ne_zero _ (zpow_ne_zero _ he0)) h
  · exact h

/-! ## The twisted form of the relation -/

private def xOf (γ : SL(2, ℤ)) : ℝ := (hB N γ : ℝ) / (hD N γ : ℝ)

private theorem rel_twisted {k : ℤ} {m : ℕ} (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (hΦ : Phi Γ N f = 0) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    ∑ i, raise N (f i) τ * twRaiseFn (xOf (N := N) γ) (nA N γ ^ 2) AF τ ^ (i : ℕ) *
      twRaiseFn (xOf (N := N) γ) (nA N γ ^ 2) DF τ ^ (m - (i : ℕ)) = 0 := by
  have := rel_at_P f hΦ hγ (heckeDiagMatrix N • τ)
  rw [hP_smul_heckeDiag_smul] at this
  simp only [raise_apply]
  exact this

/-! ## The ring hom `ρ` on `q`-expansions -/

private def RHom (γ : SL(2, ℤ)) : LaurentSeries ℂ →+* LaurentSeries ℂ :=
  haveI : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  (qExpand ℂ (nA N γ ^ 2)).comp (qTwist (expU (xOf (N := N) γ)))

private theorem RHom_apply (γ : SL(2, ℤ)) (Y : LaurentSeries ℂ) :
    RHom (N := N) γ Y = (haveI : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩;
      qExpand ℂ (nA N γ ^ 2) (qTwist (expU (xOf (N := N) γ)) Y)) := rfl

private theorem RHom_injective (γ : SL(2, ℤ)) : Function.Injective (RHom (N := N) γ) := by
  have : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  intro Y Z h
  rw [RHom_apply, RHom_apply] at h
  have h1 := qExpand_injective (nA N γ ^ 2) h
  ext n
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff n) h1
  simp only [qTwist_coeff] at this
  exact mul_left_cancel₀ (Units.ne_zero _) this

private theorem rel_R (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ}
    (f : Fin (m + 1) → ModularForm (GamGL Γ) k) (hΦ : Phi Γ N f = 0) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Γ) :
    ∑ i, qExpand ℂ N (qC (f i)) * RHom (N := N) γ XA ^ (i : ℕ) *
      RHom (N := N) γ XD ^ (m - (i : ℕ)) = 0 := by
  have : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  set x := xOf (N := N) γ with hx
  set t := nA N γ ^ 2 with ht
  set ψ : ℍ → ℂ := ∑ i : Fin (m + 1), (⇑(raise N (f i)) * twRaiseFn x t AF ^ (i : ℕ) *
    twRaiseFn x t DF ^ (m - (i : ℕ))) with hψ
  have hψ0 : ψ = 0 := by
    funext τ
    simp only [hψ, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    exact rel_twisted f hΦ hγ τ
  have hLR : ∀ i, AnalyticAtCusp (⇑(raise N (f i))) := fun i =>
    analyticAtCusp_of_modularForm (one_mem_strictPeriods_conjDiag (hΓ1 hT) (NeZero.ne N)) _
  have hTA : AnalyticAtCusp (twRaiseFn x t AF) := by
    rw [twRaiseFn_eq]
    exact analyticAtCusp_of_modularForm
      (one_mem_strictPeriods_conjDiag (one_mem_strictPeriods_twist hSL1 x) (NeZero.ne t)) _
  have hTD : AnalyticAtCusp (twRaiseFn x t DF) := by
    rw [twRaiseFn_eq]
    exact analyticAtCusp_of_modularForm
      (one_mem_strictPeriods_conjDiag (one_mem_strictPeriods_twist hSL1 x) (NeZero.ne t)) _
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      AnalyticAtCusp (⇑(raise N (f i)) * twRaiseFn x t AF ^ (i : ℕ) *
        twRaiseFn x t DF ^ (m - (i : ℕ))) := fun i _ =>
    ((hLR i).mul (hTA.pow _)).mul (hTD.pow _)
  have hq : qExpansion 1 ψ = ∑ i : Fin (m + 1), qExpansion 1 (raise N (f i)) *
      qExpansion 1 (twRaiseFn x t AF) ^ (i : ℕ) *
        qExpansion 1 (twRaiseFn x t DF) ^ (m - (i : ℕ)) := by
    rw [hψ, qExpansion_sum' _ hterm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [qExpansion_mul ((hLR i).mul (hTA.pow _)) (hTD.pow _), qExpansion_mul (hLR i) (hTA.pow _),
      qExpansion_pow' hTA, qExpansion_pow' hTD]
  rw [hψ0, qExpansion_zero] at hq
  have h2 := congrArg (ofPowerSeries ℤ ℂ) hq
  rw [map_zero, map_sum] at h2
  refine Eq.trans ?_ h2.symm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow]
  have e1 : ofPowerSeries ℤ ℂ (qExpansion 1 (raise N (f i))) = qExpand ℂ N (qC (f i)) :=
    qC_raise (hΓ1 hT) N (f i)
  have e2 : ofPowerSeries ℤ ℂ (qExpansion 1 (twRaiseFn x t AF)) = RHom (N := N) γ XA := by
    rw [RHom_apply]; exact qC_twRaiseFn hSL1 x t AF
  have e3 : ofPowerSeries ℤ ℂ (qExpansion 1 (twRaiseFn x t DF)) = RHom (N := N) γ XD := by
    rw [RHom_apply]; exact qC_twRaiseFn hSL1 x t DF
  rw [e1, e2, e3]

private def rho (γ : SL(2, ℤ)) : LaurentSeries ℂ := RHom (N := N) γ jC

private theorem rho_eq_div (γ : SL(2, ℤ)) :
    rho (N := N) γ = RHom (N := N) γ XA / RHom (N := N) γ XD := by
  rw [rho, jC, map_div₀]

/-! ## The polynomial whose roots are the `ρ(γ)` -/

private theorem isRoot_of_rel {R : Type*} [Field R] {n : ℕ} (a : Fin (n + 1) → R) {u v : R}
    (hv : v ≠ 0) (h : ∑ i, a i * u ^ (i : ℕ) * v ^ (n - (i : ℕ)) = 0) :
    (∑ i : Fin (n + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).IsRoot (u / v) := by
  rw [Polynomial.IsRoot, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have key : (∑ i : Fin (n + 1), a i * (u / v) ^ (i : ℕ)) * v ^ n =
      ∑ i : Fin (n + 1), a i * u ^ (i : ℕ) * v ^ (n - (i : ℕ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.is_lt
    have hv' : v ^ n = v ^ (i : ℕ) * v ^ (n - (i : ℕ)) := by
      rw [← _root_.pow_add, Nat.add_sub_cancel' hi]
    rw [hv', div_pow]
    field_simp
  rw [h] at key
  rcases mul_eq_zero.mp key with h1 | h1
  · exact h1
  · exact absurd h1 (pow_ne_zero _ hv)

private theorem coeff_sum_C_mul_X_pow {R : Type*} [Semiring R] {n : ℕ} (a : Fin (n + 1) → R)
    (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).coeff (i : ℕ) = a i := by
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have h : ¬ (i : ℕ) = (j : ℕ) := fun h' => hji (Fin.ext h'.symm)
    simp [h]
  · intro h; exact absurd (Finset.mem_univ i) h

private theorem natDegree_sum_le {R : Type*} [Semiring R] {n : ℕ} (a : Fin (n + 1) → R) :
    (∑ j : Fin (n + 1), Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp j.is_lt)

private theorem rho_coeff_mul (γ : SL(2, ℤ)) (m' : ℤ) :
    (rho (N := N) γ).coeff (((nA N γ ^ 2 : ℕ) : ℤ) * m') =
      ((expU (xOf (N := N) γ) ^ m' : ℂˣ) : ℂ) * jC.coeff m' := by
  have : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  rw [rho, RHom_apply, qExpand_coeff_mul, qTwist_coeff]

private theorem rho_coeff_of_not_dvd (γ : SL(2, ℤ)) {m' : ℤ}
    (h : ¬ ((nA N γ ^ 2 : ℕ) : ℤ) ∣ m') : (rho (N := N) γ).coeff m' = 0 := by
  have : NeZero (nA N γ ^ 2) := ⟨pow_ne_zero _ (nA_ne_zero N γ)⟩
  rw [rho, RHom_apply, qExpand_coeff_of_not_dvd _ _ h]

private theorem rho_coeff_neg_sq (γ : SL(2, ℤ)) :
    (rho (N := N) γ).coeff (-((nA N γ ^ 2 : ℕ) : ℤ)) = ((expU (xOf (N := N) γ))⁻¹ : ℂˣ) := by
  have := rho_coeff_mul (N := N) γ (-1)
  rw [mul_neg_one] at this
  rw [this, jC_coeff_neg_one, mul_one, _root_.zpow_neg_one]

private theorem nA_eq_of_rho_eq {γ₁ γ₂ : SL(2, ℤ)}
    (h : rho (N := N) γ₁ = rho (N := N) γ₂) : nA N γ₁ = nA N γ₂ := by
  have h1 : (rho (N := N) γ₂).coeff (-((nA N γ₁ ^ 2 : ℕ) : ℤ)) ≠ 0 := by
    rw [← h, rho_coeff_neg_sq]
    exact Units.ne_zero _
  by_cases hdvd : ((nA N γ₂ ^ 2 : ℕ) : ℤ) ∣ -((nA N γ₁ ^ 2 : ℕ) : ℤ)
  · obtain ⟨m', hm'⟩ := hdvd
    rw [hm', rho_coeff_mul] at h1
    have hj : jC.coeff m' ≠ 0 := fun h0 => h1 (by rw [h0, mul_zero])
    have hm'ge : -1 ≤ m' := by
      by_contra hlt
      exact hj (jC_coeff_of_lt (by omega))
    have hpos1 : (0 : ℤ) < ((nA N γ₁ ^ 2 : ℕ) : ℤ) := by
      have := pow_pos (Nat.pos_of_ne_zero (nA_ne_zero N γ₁)) 2
      exact_mod_cast this
    have hpos2 : (0 : ℤ) < ((nA N γ₂ ^ 2 : ℕ) : ℤ) := by
      have := pow_pos (Nat.pos_of_ne_zero (nA_ne_zero N γ₂)) 2
      exact_mod_cast this
    have hm'neg : m' < 0 := by
      by_contra hge
      push Not at hge
      have : (0 : ℤ) ≤ ((nA N γ₂ ^ 2 : ℕ) : ℤ) * m' := mul_nonneg hpos2.le hge
      rw [← hm'] at this
      linarith
    have hm1 : m' = -1 := by omega
    rw [hm1, mul_neg_one, neg_inj] at hm'
    have hsq : nA N γ₁ ^ 2 = nA N γ₂ ^ 2 := by exact_mod_cast hm'
    exact Nat.pow_left_injective (by norm_num) hsq
  · exact absurd (rho_coeff_of_not_dvd γ₂ hdvd) h1

private theorem expU_xOf_eq (γ : SL(2, ℤ)) :
    (expU (xOf (N := N) γ) : ℂ) = Complex.exp (2 * Real.pi * Complex.I / (nD N γ)) ^ (nB N γ) := by
  rw [val_expU, ← Complex.exp_nat_mul, xOf]
  congr 1
  have h1 : (hB N γ : ℂ) = (nB N γ : ℂ) := by rw [← nB_cast N γ]; norm_cast
  have h2 : (hD N γ : ℂ) = (nD N γ : ℂ) := by rw [← nD_cast N γ]; norm_cast
  push_cast
  rw [h1, h2]
  have hd : (nD N γ : ℂ) ≠ 0 := by exact_mod_cast nD_ne_zero N γ
  field_simp

private theorem mul_inv_mem_of_rho_eq {γ₁ γ₂ : SL(2, ℤ)}
    (h : rho (N := N) γ₁ = rho (N := N) γ₂) : γ₂ * γ₁⁻¹ ∈ Gamma0 N := by
  have ha : nA N γ₁ = nA N γ₂ := nA_eq_of_rho_eq h
  have haI : hA N γ₁ = hA N γ₂ := by rw [← nA_cast, ← nA_cast, ha]
  have hdI : hD N γ₁ = hD N γ₂ := by
    have h1 := hA_mul_hD N γ₁
    have h2 := hA_mul_hD N γ₂
    rw [haI] at h1
    exact mul_left_cancel₀ (hA_pos N γ₂).ne' (h1.trans h2.symm)
  have hd : nD N γ₁ = nD N γ₂ := by
    have := nD_cast N γ₁; have := nD_cast N γ₂; omega
  have hu : (expU (xOf (N := N) γ₁) : ℂ) = expU (xOf (N := N) γ₂) := by
    have h1 := rho_coeff_neg_sq (N := N) γ₁
    have h2 := rho_coeff_neg_sq (N := N) γ₂
    rw [h, ha] at h1
    rw [h1] at h2
    have h3 : (expU (xOf (N := N) γ₁))⁻¹ = (expU (xOf (N := N) γ₂))⁻¹ :=
      Units.val_injective h2
    rw [_root_.inv_inj] at h3
    rw [h3]
  rw [expU_xOf_eq, expU_xOf_eq, hd] at hu
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (nD N γ₂))) (nD N γ₂) :=
    Complex.isPrimitiveRoot_exp _ (nD_ne_zero N γ₂)
  have hb : nB N γ₁ = nB N γ₂ :=
    hprim.pow_inj (lt_of_lt_of_eq (nB_lt_nD N γ₁) hd) (nB_lt_nD N γ₂) hu
  have hbI : hB N γ₁ = hB N γ₂ := by rw [← nB_cast, ← nB_cast, hb]
  exact mul_inv_mem_Gamma0_of_hermite_eq N haI hbI hdI

/-! ## The cosets and the core degeneracy statement -/

variable (Γ N) in

private abbrev Q : Type := ↥Γ ⧸ (Gamma0 N).subgroupOf Γ

omit [NeZero N] in
private theorem card_Q : Nat.card (Q Γ N) = (Gamma0 N).relIndex Γ := rfl

private def rep (q : Q Γ N) : ↥Γ := (Quotient.out q)⁻¹

omit [NeZero N] in
private theorem rep_spec (q : Q Γ N) : (QuotientGroup.mk ((rep q)⁻¹) : Q Γ N) = q := by
  rw [rep, inv_inv]; exact Quotient.out_eq q

private theorem rho_rep_injective :
    Function.Injective fun q : Q Γ N => rho (N := N) ((rep q : ↥Γ) : SL(2, ℤ)) := by
  intro q₁ q₂ h
  have hmem := mul_inv_mem_of_rho_eq (N := N) h
  rw [← rep_spec q₁, ← rep_spec q₂]
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  rw [Subgroup.mem_subgroupOf]
  simpa [rep] using hmem

private theorem core (hT : ModularGroup.T ∈ Γ) {k : ℤ} {m : ℕ}
    (hm : m < (Gamma0 N).relIndex Γ) (f : Fin (m + 1) → ModularForm (GamGL Γ) k)
    (hrel : ∑ i, qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) = 0) :
    ∀ i, f i = 0 := by
  classical
  have : Finite (Q Γ N) := Subgroup.finite_quotient_of_finiteIndex
  have hΦ := Phi_eq_zero hT f hrel
  set a : Fin (m + 1) → LaurentSeries ℂ := fun i => qExpand ℂ N (qC (f i)) with ha
  set P : Polynomial (LaurentSeries ℂ) :=
    ∑ i : Fin (m + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) with hP
  have hroot : ∀ q : Q Γ N, P.IsRoot (rho (N := N) ((rep q : ↥Γ) : SL(2, ℤ))) := by
    intro q
    have h := rel_R hT f hΦ (rep q).2
    have hv : RHom (N := N) ((rep q : ↥Γ) : SL(2, ℤ)) XD ≠ 0 := fun h0 =>
      XD_ne_zero (RHom_injective _ (by rw [h0, map_zero]))
    have := isRoot_of_rel a hv h
    rwa [← rho_eq_div] at this
  have : Fintype (Q Γ N) := Fintype.ofFinite _
  set Z : Finset (LaurentSeries ℂ) :=
    Finset.univ.image (fun q : Q Γ N => rho (N := N) ((rep q : ↥Γ) : SL(2, ℤ))) with hZ
  have hcard : Z.card = (Gamma0 N).relIndex Γ := by
    rw [hZ, Finset.card_image_of_injective _ rho_rep_injective, Finset.card_univ, ← card_Q,
      Nat.card_eq_fintype_card]
  have hP0 : P = 0 := by
    by_contra hP0
    have hsub : Z.val ⊆ P.roots := by
      intro z hz'
      rw [Polynomial.mem_roots hP0]
      have hz'' : z ∈ Z := hz'
      rw [hZ, Finset.mem_image] at hz''
      obtain ⟨q, -, rfl⟩ := hz''
      exact hroot q
    have h1 := Polynomial.card_le_degree_of_subset_roots hsub
    have h2 : P.natDegree ≤ m := natDegree_sum_le a
    rw [hcard] at h1
    omega
  intro i
  have hai : qExpand ℂ N (qC (f i)) = 0 := by
    have := coeff_sum_C_mul_X_pow a i
    rw [← hP, hP0, Polynomial.coeff_zero] at this
    exact this.symm
  have hq : qC (f i) = 0 := qExpand_injective N (by rw [map_zero, hai])
  have hq' : qExpansion 1 (f i) = 0 := by
    apply ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [map_zero]
    exact hq
  exact (ModularForm.qExpansion_eq_zero_iff one_pos (hΓ1 hT) _).mp hq'

end Core

/-! ## The headline -/

section Final

variable (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) (N : ℕ) [NeZero N]

private theorem jqNModC_eq : jqNModC ℂ N = qExpand ℂ N XA / qExpand ℂ N XD := by
  rw [jqNModC, jqModC_eq_jC, jC, map_div₀]

private theorem theta_mem :
    jqNModC ℂ N ∈ IntermediateField.adjoin ℂ (insert (jqNModC ℂ N) (ratioSet Γ)) :=
  IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)

private theorem le_insert :
    IntermediateField.adjoin ℂ (ratioSet Γ) ≤
      IntermediateField.adjoin ℂ (insert (jqNModC ℂ N) (ratioSet Γ)) :=
  IntermediateField.adjoin.mono ℂ _ _ (Set.subset_insert _ _)

include hT in

private theorem linearIndependent_pow_theta :
    LinearIndependent (IntermediateField.adjoin ℂ (ratioSet Γ))
      (fun i : Fin ((Gamma0 N).relIndex Γ) =>
        (⟨jqNModC ℂ N ^ (i : ℕ), pow_mem (theta_mem Γ N) _⟩ :
          extendScalars (le_insert Γ N))) := by
  obtain ⟨m, hm⟩ : ∃ m, (Gamma0 N).relIndex Γ = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := (Gamma0 N).subgroupOf Γ))
  rw [hm]
  rw [Fintype.linearIndependent_iff]
  intro g hg i₀
  have hrelQ : ∑ i, ((g i : IntermediateField.adjoin ℂ (ratioSet Γ)) : LaurentSeries ℂ) *
      jqNModC ℂ N ^ (i : ℕ) = 0 := by
    have := congrArg (fun z : extendScalars (le_insert Γ N) =>
      ((z : IntermediateField.adjoin ℂ (insert (jqNModC ℂ N) (ratioSet Γ))) : LaurentSeries ℂ)) hg
    simp at this
    exact this
  obtain ⟨k, gF, f, hg0, hf⟩ :=
    common_denominator hT (m + 1) (fun i => ((g i : IntermediateField.adjoin ℂ (ratioSet Γ)) :
      LaurentSeries ℂ)) (fun i => mem_ratioSet_of_mem_adjoin hT (g i).2)
  have hrel1 : ∑ i, qC (f i) * jqNModC ℂ N ^ (i : ℕ) = 0 := by
    have := congrArg (· * qC gF) hrelQ
    simp only [zero_mul, Finset.sum_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hf i]; ring
  have hYD : qExpand ℂ N XD ≠ 0 := fun h0 => XD_ne_zero (qExpand_injective N (by rw [h0, map_zero]))
  have hrel2 : ∑ i, qC (f i) * qExpand ℂ N XA ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) = 0 := by
    have key : (∑ i : Fin (m + 1), qC (f i) * jqNModC ℂ N ^ (i : ℕ)) * qExpand ℂ N XD ^ m =
        ∑ i : Fin (m + 1), qC (f i) * qExpand ℂ N XA ^ (i : ℕ) *
          qExpand ℂ N XD ^ (m - (i : ℕ)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (i : ℕ) ≤ m := Nat.lt_succ_iff.mp i.is_lt
      have hv' : qExpand ℂ N XD ^ m =
          qExpand ℂ N XD ^ (i : ℕ) * qExpand ℂ N XD ^ (m - (i : ℕ)) := by
        rw [← _root_.pow_add, Nat.add_sub_cancel' hi]
      rw [jqNModC_eq, hv', div_pow]
      field_simp
    rw [hrel1, zero_mul] at key
    exact key.symm
  have hlt : m < (Gamma0 N).relIndex Γ := by omega
  have hfi := core hT hlt f hrel2 i₀
  have h3 : ((g i₀ : IntermediateField.adjoin ℂ (ratioSet Γ)) : LaurentSeries ℂ) = 0 := by
    have := hf i₀
    rw [hfi, FunLike.coe_zero,
      show qC (0 : ℍ → ℂ) = 0 by rw [qC, qExpansion_zero, map_zero]] at this
    exact (mul_eq_zero.mp this).resolve_right hg0
  exact_mod_cast h3

end Final

end RelIndexJqSol

theorem relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) (hT : ModularGroup.T ∈ Γ)
    (N : ℕ) [NeZero N] :
    (((CongruenceSubgroup.Gamma0 N).relIndex Γ : ℕ) : Cardinal) ≤
      IntermediateField.relrank
        (IntermediateField.adjoin ℂ {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})
        (IntermediateField.adjoin ℂ (insert (ModularCurve.jqNModC ℂ N)
          {x : LaurentSeries ℂ | ∃ (k : ℤ)
            (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k),
            UpperHalfPlane.qExpansion 1 (⇑g) ≠ 0 ∧
              x = HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
                HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g)})) := by
  change (((CongruenceSubgroup.Gamma0 N).relIndex Γ : ℕ) : Cardinal) ≤
    IntermediateField.relrank (IntermediateField.adjoin ℂ (RelIndex.ratioSet Γ))
      (IntermediateField.adjoin ℂ (insert (ModularCurve.jqNModC ℂ N) (RelIndex.ratioSet Γ)))
  rw [IntermediateField.relrank_eq_rank_of_le (RelIndexJqSol.le_insert Γ N)]
  have h := (RelIndexJqSol.linearIndependent_pow_theta Γ hT N).cardinal_le_rank
  rw [Cardinal.mk_fin] at h
  exact h

end ModularCurve
