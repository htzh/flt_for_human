/-
The seven inputs `ModularCurve.HeckeInputsHAlong`: the α/β degeneracy maps of
`X_H(M) → X_H(M) ∩ X₀(Mℓ)` are finite and integral, the top field has principal
divisors, the bottom field has characteristic zero, and the bundle
`HeckeInputsHAlong` holds.

This is FLT's `P2M/Sol/S_ModularCurve_heckeInputsHAlong.lean` (pin `aa2d8b3`)
together with its wrapper `Theorems/Thm_ModularCurve_heckeInputsHAlong.lean`. The
pin's file is a public `S_` file, so all its declarations are transcribed at the
pin's own names and are public; the outer headline spells the wrapper's explicit
binders (the `S_` file's own copy is the inner `HeckeInputsHAll.heckeInputsHAlong`,
whose binders are the section variables). The two `scoped instance`s stay `scoped`
exactly as the pin writes them.

Reuse, not restatement: `restrictForm` is `ModularCurve.restrictForm`
(`JqIntegralRatios.lean:43`); `heckeDiagMatrix`/`translate`/
`slash_heckeDiagMatrix_apply` are `ModularForms/Defs/HeckeOperator.lean` (the
first two of those are mathlib's); `qCoeff_comp_heckeDiagMatrix_smul` is
`ModularForms/HeckeQCoeff.lean`; `CohCarrier.GammaH`, `mem_GammaH_iff`,
`Gamma1_le_GammaH`, `translation_mem_GammaH` are `ModularForms/Defs/GammaH.lean`;
`intSeriesC`, `intFormRatiosC`, `mem_intFormRatiosC`, `div_mem_qExpFunctionFieldC`
are `ModularCurve/JqIntegralRatios.lean`; `qExpand`/`qExpandₐ` and the Laurent
vocabulary are `ModularCurve/Defs/Laurent.lean`; `Gamma1_le_of_dvd` is
`ModularCurve.X1.Defs`; the `Along` facts are
`AlgebraicCurve/WeilExchange/Transport.lean`; `hasPrincipalDivisors_of_transcendental`
is `AlgebraicCurve/PrincipalDivisors/Transcendence.lean`; and
`exists_transcendental_finiteDimensional_laurentBaseChange` is
`ModularCurve.JOneES` (`X1/FunctionFieldBaseChange.lean`).

**The set's one substitution.** `port_advise` reports the pin's `def expandInt` as
byte-identical to the ported `ModularCurve.expandPS`
(`X1/QExpandStretch.lean:147`), so its body is not restated: `expandInt` is a
one-line bridge to `expandPS`, and the two dependent statements
`coeff_expandInt`/`intSeriesC_expandInt` are proved by `coeff_expandPS`/
`intSeriesC_expandPS`. The names cannot be dropped: the pin's `coeff_expandInt`
and `intSeriesC_expandInt` state their conclusions with `expandInt`, and the
checker diffs those statements textually, so `expandInt` must exist at its pin
name with the pin's byte-identical statement.

The pin calls the public `AlgebraicCurve.finiteDimensional_adjoin_of_transcendental`
inside `finiteAlong_of_exists`; its port copy is `private` inside
`AlgebraicCurve.SeparatingTranscendentalOfPerfectField`
(`AlgebraicCurve/IsCurveOver/PerfectField.lean:71`), so this module carries its own
`private` copy at the pin's instance-spelled statement — the arrangement
`X1/Inputs.lean:62` already uses. Private declarations are invisible to the
checker, so the module's public surface is exactly the 33 transcribed
declarations: the pin's `HeckeInputsHAll` block (32) plus the wrapper's headline.
The pin `S_` file's own `solution` (last name `solution`, the same statement as
the headline) is not transcribed; the checker reads the port against the pin, so
its absence is not a `missing`.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_heckeInputsHAlong.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_heckeInputsHAlong.lean
-/
import FLTForHuman.ModularCurve.XH.HeckeOperator
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.X1.QExpandStretch
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence
import FLTForHuman.AlgebraicCurve.Place.DegreeOne

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix AlgebraicCurve IntermediateField
  HahnSeries

open scoped MatrixGroups ModularForm Pointwise

namespace ModularCurve

namespace HeckeInputsHAll

/-! ## The conjugation by the diagonal Hecke matrix -/

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ}

/-- The `ℓ`-conjugate `!![γ₀₀, ℓγ₀₁; γ₁₀/ℓ, γ₁₁]` of a special-linear matrix. -/
def conjMat (ℓ : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0, (ℓ : ℤ) * γ 0 1; γ 1 0 / ℓ, γ 1 1]

theorem det_conjMat (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : (conjMat ℓ γ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
  rw [Matrix.det_fin_two] at hdet ⊢
  rcases eq_or_ne (ℓ : ℤ) 0 with h0 | h0
  · simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h0, zero_mul, Int.zero_ediv,
      mul_zero, sub_zero] at hdet ⊢
    linear_combination hdet
  · have h1 : (ℓ : ℤ) * c / ℓ = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
    linear_combination hdet

/-- The conjugate of `γ ∈ Γ₀(Mℓ)` with `(ℓ : ℤ) ∣ γ 1 0`, as an element of `SL(2, ℤ)`. -/
def conjSL (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : SL(2, ℤ) := ⟨conjMat ℓ γ, det_conjMat γ h⟩

@[scoped simp] theorem conjSL_apply_00 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) :
    conjSL γ h 0 0 = γ 0 0 := rfl

@[scoped simp] theorem conjSL_apply_01 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) :
    conjSL γ h 0 1 = (ℓ : ℤ) * γ 0 1 := rfl

@[scoped simp] theorem conjSL_apply_10 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) :
    conjSL γ h 1 0 = γ 1 0 / ℓ := rfl

@[scoped simp] theorem conjSL_apply_11 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) :
    conjSL γ h 1 1 = γ 1 1 := rfl

theorem dvd_of_mem_Gamma0_mul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) : (ℓ : ℤ) ∣ γ 1 0 := by
  have hMℓ : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  exact (show (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans hMℓ

theorem conjSL_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL γ (dvd_of_mem_Gamma0_mul hγ) ∈ Gamma0 M := by
  rw [Gamma0_mem]
  have hd : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨c, hc⟩ := hd
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : (conjSL γ (dvd_of_mem_Gamma0_mul hγ)) 1 0 = M * c := by
    show γ 1 0 / ℓ = M * c
    rw [hc]; push_cast
    rw [show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring]
    exact Int.mul_ediv_cancel_left _ hℓ'
  rw [h10]; push_cast
  simp

theorem conjSL_mem_GammaH {γ : SL(2, ℤ)} (hγH : γ ∈ CohCarrier.GammaH M H)
    (hγ : γ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL γ (dvd_of_mem_Gamma0_mul hγ) ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff] at hγH ⊢
  obtain ⟨hγ0, hH⟩ := hγH
  refine ⟨conjSL_mem_Gamma0 hγ hℓ, ?_⟩
  convert hH using 1
  rfl

theorem heckeDiag_mul_mul_inv {γ : SL(2, ℤ)} (h : (ℓ : ℤ) ∣ γ 1 0) (hℓ : ℓ ≠ 0) :
    ModularForm.heckeDiagMatrix ℓ * (γ : GL (Fin 2) ℝ) * (ModularForm.heckeDiagMatrix ℓ)⁻¹ =
      ((conjSL γ h : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : (conjSL γ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show γ 1 0 / ℓ = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hℓ'
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem inf_le_conj (hℓ : ℓ ≠ 0) :
    ((CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (ModularForm.heckeDiagMatrix ℓ)⁻¹ •
        (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) := by
  rintro x ⟨γ, hγ, rfl⟩
  obtain ⟨hγH, hγ0⟩ := Subgroup.mem_inf.mp hγ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, conjSL_mem_GammaH hγH hγ0 hℓ,
    (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hγ0) hℓ).symm⟩

theorem T_mem_inf : ModularGroup.T ∈ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) := by
  refine Subgroup.mem_inf.mpr ⟨CohCarrier.translation_mem_GammaH M H, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods : (1 : ℝ) ∈ ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (CohCarrier.translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

end Group

/-! ## Raising the level of a form on `Γ_H(M)` to `Γ_H(M) ⊓ Γ₀(Mℓ)` -/

section LevelRaise

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ]

/-- The level raise `f(ℓτ)`, from `Γ_H(M)` to `Γ_H(M) ⊓ Γ₀(Mℓ)`. -/
def levelRaise {k : ℤ} (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm ((CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ •
    restrictForm (inf_le_conj (NeZero.ne ℓ)) (ModularForm.translate f (ModularForm.heckeDiagMatrix ℓ))

theorem levelRaise_apply {k : ℤ} (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (τ : ℍ) : levelRaise (ℓ := ℓ) f τ = f (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] ModularForm.heckeDiagMatrix ℓ) τ) = _
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]

theorem coe_levelRaise {k : ℤ} (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) :
    ⇑(levelRaise (ℓ := ℓ) f) = fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ) :=
  funext (levelRaise_apply f)

theorem coeff_qExpansion_levelRaise {k : ℤ}
    (f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 (levelRaise (ℓ := ℓ) f)) =
      if ℓ ∣ n then PowerSeries.coeff (n / ℓ) (qExpansion 1 f) else 0 := by
  rw [coe_levelRaise]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f one_mem_strictPeriods (NeZero.ne ℓ) n

/-- The stretch of an integral `q`-expansion, `expandPS` under the pin's name. The
pin's body is byte-identical to `ModularCurve.expandPS`, which is reused here. -/
def expandInt (ℓ : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  expandPS ℓ p

omit [NeZero ℓ] in
theorem coeff_expandInt (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (expandInt ℓ p) = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0 :=
  coeff_expandPS ℓ p n

theorem isIntegralQExp_levelRaise {k : ℤ}
    {f : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k} {pf : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) : IsIntegralQExp (levelRaise (ℓ := ℓ) f) (expandInt ℓ pf) := by
  rw [isIntegralQExp_iff]
  intro n
  rw [coeff_expandInt, coeff_qExpansion_levelRaise]
  split_ifs with h
  · exact hf.coeff _
  · simp

theorem intSeriesC_expandInt (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (expandInt ℓ p) = qExpand K ℓ (intSeriesC K p) :=
  intSeriesC_expandPS K ℓ p

theorem heckeBetaHDefined : HeckeBetaHDefined M H ℓ := by
  intro y hy
  suffices h : xHFunctionField M H ≤ (xHTopFunctionFieldC ℚ M H (M * ℓ)).comap (qExpandₐ ℓ) from
    h hy
  change IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H)) ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  change qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ xHTopFunctionFieldC ℚ M H (M * ℓ)
  rw [map_div₀, ← intSeriesC_expandInt, ← intSeriesC_expandInt]
  have hg0' : intSeriesC ℚ (expandInt ℓ pg) ≠ 0 := by
    rw [intSeriesC_expandInt]
    exact fun h => hg0 (qExpand_injective ℓ (by rw [h, map_zero]))
  exact div_mem_qExpFunctionFieldC (levelRaise (ℓ := ℓ) f) (levelRaise (ℓ := ℓ) g)
    (isIntegralQExp_levelRaise hf) (isIntegralQExp_levelRaise hg) hg0'

end LevelRaise

/-! ## The generic `Along` facts -/

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem transcendental_map (φ : F →ₐ[K] F') {x : F} (hx : Transcendental K x) :
    Transcendental K (φ x) := by
  rintro ⟨p, hp0, hp⟩
  refine hx ⟨p, hp0, ?_⟩
  rw [Polynomial.aeval_algHom_apply] at hp
  exact (map_eq_zero_iff φ (RingHom.injective (φ : F →+* F'))).mp hp

theorem finiteAlong_of_finiteDimensional_adjoin (φ : F →ₐ[K] F') (x : F)
    [h : FiniteDimensional (IntermediateField.adjoin K ({φ x} : Set F')) F'] : FiniteAlong K φ := by
  letI := algebraAlong φ
  show Module.Finite F F'
  set E := IntermediateField.adjoin K ({φ x} : Set F')
  have hE : E ≤ φ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := Module.finite_def.mp h
  refine Module.finite_def.mpr ⟨s, ?_⟩
  rw [eq_top_iff]
  rintro y -
  have hy : y ∈ Submodule.span E (s : Set F') := by rw [hs]; trivial
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha =>
      obtain ⟨b, hb⟩ := AlgHom.mem_fieldRange.mp (hE c.2)
      have : (c • a : F') = b • a := by
        show (c : F') * a = φ.toRingHom b * a
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hb]
      rw [this]
      exact Submodule.smul_mem _ b ha

theorem isIntegral_of_finiteAlong (φ : F →ₐ[K] F') (h : FiniteAlong K φ) :
    φ.toRingHom.IsIntegral := by
  letI := algebraAlong φ
  haveI : Module.Finite F F' := h
  intro y
  exact Algebra.IsIntegral.isIntegral (R := F) y

theorem hasPrincipalDivisors_of_exists [CharZero K]
    (hT : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F') :
    HasPrincipalDivisors K F' := by
  obtain ⟨x, hx, hfd⟩ := hT
  haveI := hfd
  exact AlgebraicCurve.hasPrincipalDivisors_of_transcendental K x hx

/-- The pin's public `AlgebraicCurve.finiteDimensional_adjoin_of_transcendental`,
carried `private` here because its port copy is `private` in
`AlgebraicCurve.SeparatingTranscendentalOfPerfectField`. -/
private theorem finiteDimensional_adjoin_of_transcendental (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] {t : F}
    (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := by
  classical
  have halg : Algebra.IsAlgebraic K⟮t⟯ F :=
    AlgebraicCurve.isAlgebraic_adjoin_of_transcendental (K := K) x ht
  obtain ⟨s, hs⟩ := Module.finite_def.mp (inferInstance : Module.Finite K⟮x⟯ F)
  set E : IntermediateField K⟮t⟯ F := IntermediateField.adjoin K⟮t⟯ (insert x (↑s : Set F)) with hE
  have hxE : x ∈ E := IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hrange : ∀ r : K⟮x⟯, (r : F) ∈ E := by
    intro r
    have hle : K⟮x⟯ ≤ E.restrictScalars K :=
      IntermediateField.adjoin_simple_le_iff.mpr
        ((IntermediateField.mem_restrictScalars K).mpr hxE)
    exact (IntermediateField.mem_restrictScalars K).mp (hle r.2)
  have hmem : ∀ y : F, y ∈ E := by
    intro y
    have hy : y ∈ Submodule.span K⟮x⟯ (↑s : Set F) := by rw [hs]; exact Submodule.mem_top
    refine Submodule.span_induction (fun z hz => ?_) ?_ (fun z w _ _ hz hw => ?_)
      (fun r z _ hz => ?_) hy
    · exact IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ hz)
    · exact zero_mem E
    · exact add_mem hz hw
    · rw [Algebra.smul_def]
      exact mul_mem (hrange r) hz
  have htop : E = ⊤ := by
    rw [eq_top_iff]
    intro y _
    exact hmem y
  haveI : Finite ↥(insert x (↑s : Set F)) :=
    Set.Finite.to_subtype ((s.finite_toSet).insert x)
  have hfdE : FiniteDimensional K⟮t⟯ ↥E := by
    rw [hE]
    exact IntermediateField.finiteDimensional_adjoin
      (fun z _ => (halg.isAlgebraic z).isIntegral)
  rw [htop] at hfdE
  haveI := hfdE
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := K⟮t⟯) (E := F)).toLinearEquiv

theorem finiteAlong_of_exists
    (hT : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hB : ∃ x : F, Transcendental K x) (φ : F →ₐ[K] F') : FiniteAlong K φ := by
  obtain ⟨xT, hxT, hfdT⟩ := hT
  obtain ⟨xB, hxB⟩ := hB
  haveI := hfdT
  have htr : Transcendental K (φ xB) := transcendental_map φ hxB
  haveI := finiteDimensional_adjoin_of_transcendental xT htr
  exact finiteAlong_of_finiteDimensional_adjoin φ xB

end Along

/-! ## The bundle `HeckeInputsHAlong` -/

section Hecke

variable (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
  (ℓ : ℕ) [NeZero ℓ]

scoped instance gammaH_finiteIndex : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (CohCarrier.Gamma1_le_GammaH M H)

scoped instance gammaH_inf_finiteIndex : (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ)⟩
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M ℓ)).trans (CohCarrier.Gamma1_le_GammaH M H)

theorem hasPrincipalDivisors_top :
    HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  exact hasPrincipalDivisors_of_exists
    (ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
      (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) T_mem_inf)

theorem finiteAlong_of_hom
    (φ : laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : FiniteAlong L φ :=
  finiteAlong_of_exists
    (ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
      (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) T_mem_inf)
    ((ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
      (CohCarrier.GammaH M H) (CohCarrier.translation_mem_GammaH M H)).imp fun _ hx => hx.1) φ

omit [NeZero M] in
theorem charZero_bot : CharZero (laurentBaseChange L (xHFunctionField M H)) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  exact charZero_of_injective_algebraMap
    (algebraMap L (laurentBaseChange L (xHFunctionField M H))).injective

theorem heckeInputsHAlong : HeckeInputsHAlong L M H ℓ := by
  have hfinα : FiniteAlong L (heckeAlphaHBar L M H ℓ) := finiteAlong_of_hom L M H ℓ _
  have hfinβ : FiniteAlong L (heckeBetaHBar L M H ℓ) := finiteAlong_of_hom L M H ℓ _
  have hα : HeckeAlphaHBarIntegral L M H ℓ := isIntegral_of_finiteAlong _ hfinα
  have hβ : HeckeBetaHBarIntegral L M H ℓ := isIntegral_of_finiteAlong _ hfinβ
  haveI := hasPrincipalDivisors_top L M H ℓ
  haveI := charZero_bot L M H
  have hsepα := AlgebraicCurve.separableAlong_of_charZero _ hα
  have hsepβ := AlgebraicCurve.separableAlong_of_charZero _ hβ
  exact heckeInputsHAlong_intro heckeBetaHDefined hα hβ
    (AlgebraicCurve.fundamentalIdentityAlong _ hβ hfinβ hsepβ) hfinα
    (AlgebraicCurve.normFormulaAlong _ hfinα hsepα)

end Hecke

end HeckeInputsHAll

/-- **The seven inputs hold**: for any field `L` with a `ℚ`-algebra structure, any
`M ≠ 0`, any `H ≤ (ZMod M)ˣ` and any `ℓ ≠ 0`, the α/β degeneracy maps of
`X_H(M) → X_H(M) ∩ X₀(Mℓ)` are finite and integral and the associated
principal-divisor and norm-formula inputs hold. Verbatim from
`Theorems/Thm_ModularCurve_heckeInputsHAlong.lean`. -/
theorem heckeInputsHAlong (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    ModularCurve.HeckeInputsHAlong L M H ℓ :=
  HeckeInputsHAll.heckeInputsHAlong L M H ℓ

end ModularCurve

end
