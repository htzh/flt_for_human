/-
  Level-one forms as a source: restriction, slash sums, integral q-expansions, the E₄/Δ basis.

  Four rows, one per pin, each with its pin's proof block transcribed at the pin's own last
  names: the level-one source is used four ways.

  * A level-one form restricts to any `Γ : Subgroup SL(2, ℤ)`: the structure literal only needs
    `Γ ≤ 𝒮ℒ`, which holds by construction (`exists_coe_eq_of_levelOne`).
  * A `Γ`-form covered by a finite set `s` of level-one slashes, *separated* modulo `±Γ`, is the
    sum of those slashes and that sum is a level-one form: the trace to level one, carried by the
    relation `PM Γ g := g ∈ Γ ∨ -g ∈ Γ` — a subgroup (`PM.mul`, `PM.inv`) on which the even-weight
    slash action is trivial (`slash_pm_mul`, via `slash_neg`) — so that a choice of coset
    representatives `ρ` makes the sum invariant (`exists_levelOne_coe_eq_sum_slash`). `Γ` gains a
    `FiniteIndex` instance from the finite cover itself, so no arithmeticity hypothesis enters.
  * A level-one form of weight `4a + 6b` has an *integral* `q`-expansion with constant term `1`:
    `E₄^a E₆^b`, with the pin's `EMONO.P 240 3` and `P (-504) 5` (the truncated `σ₃`/`σ₅` series,
    `map_P4`/`map_P6` identifying their complexifications with the `q`-expansions of `E₄`/`E₆`)
    (`exists_levelOne_qExpansion_eq_map_int_constantCoeff_one`).
  * A level-one form of weight `12N` is `P(E₄³/Δ)·Δ^N` for a polynomial `P` of natDegree at most
    `N` — the `E₄³/Δ` model of the graded ring of level-one forms, by induction on `N`: subtract
    the constant term of the `q`-expansion, divide by `Δ` (`CuspForm.discriminantEquiv`), recurse
    (`exists_qExpansion_eq_aeval_mul_pow_levelOne`).

  spec-pin: P2M/Sol/S_ModularForm_exists_coe_eq_of_levelOne.lean
  spec-pin: P2M/Sol/S_ModularForm_exists_levelOne_coe_eq_sum_slash.lean
  spec-pin: P2M/Sol/S_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one.lean
  spec-pin: P2M/Sol/S_ModularForm_exists_qExpansion_eq_aeval_mul_pow_levelOne.lean

  The four pins' public surface is transcribed in full — 19 declarations, no `private` marker in
  any pin, so none here. The pins' proof blocks keep their own labels: `TraceToLevelOne` (the
  coset trace of the second pin) and `EMONO` (the Eisenstein monoid of the third), both nested
  inside `namespace ModularForm`; `check_port` matches them by content hash and reads 19 `ok`.

  ## Port deltas

  - imports: the scaffold's five narrow modules plus **one**,
    `Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula`, which is the fourth pin's own
    first import; it carries `CuspForm.discriminantEquiv`, `ModularForm.toCuspForm` and
    `qExpansion_eq_qExpansion_discriminant_mul`. No umbrella import (FR-0254).
  - visibility: the pins mark nothing `private`, so every transcription is public and the checker
    diffs it (`19 ok / 0 mismatch / 0 missing / 0 own`). Nothing was invented, so nothing needed a
    `private` marker.
  - body-only drift from the pins, all forced by `v4.34` (`statement`-neutral, FR-0255): the
    `haveI : Γ.FiniteIndex` / `haveI : Finite (SL(2, ℤ) ⧸ Γ)` pair became `have` (same instance
    behaviour, `linter.style.haveILetI` quiet); `ModularForm.IsGLPos.coe_smul` →
    `FunLike.coe_smul` and `ModularForm.coe_sub` → `FunLike.coe_sub` (deprecated aliases, which
    abort the elaboration here rather than warn); `if_pos rfl` → `ite_eq_left rfl` in
    `constantCoeff_P` (same deprecation class).
  - statements: every one is the pin's byte-for-byte, including the pins' `⇑E`, `𝒮ℒ` and
    `((x : SL(2, ℤ)) : GL (Fin 2) ℝ)` spellings; the four row statements are the scaffold's, which
    already hashed to the pins' `solution` rows.
  - heartbeat probe (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N`, never installed):
    silent at **8000**, first failure at **4000** (`isDefEq` in the `E₄³/Δ` induction's `aeval`
    rewrite); measured pair 8000 / 4000 against the project cap 4,000,000.
  - `#print axioms` on all 19 declarations: `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.RingTheory.LaurentSeries
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.HeckeQExpansion
import FLTForHuman.ModularForms.EisensteinSeries

set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane ModularForm
open scoped ModularForm MatrixGroups

namespace ModularForm

theorem exists_coe_eq_of_levelOne (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {k : ℤ} (F : ModularForm 𝒮ℒ k) :
    ∃ G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, (G : ℍ → ℂ) = (F : ℍ → ℂ) := by
  have hle : ((Γ : Subgroup (GL (Fin 2) ℝ))) ≤ 𝒮ℒ := by
    rintro _ ⟨γ, -, rfl⟩
    exact ⟨γ, rfl⟩
  refine ⟨{ toFun := F
            slash_action_eq' := fun γ hγ => F.slash_action_eq' γ (hle hγ)
            holo' := F.holo'
            bdd_at_cusps' := fun hc => F.bdd_at_cusps' (hc.mono hle) }, rfl⟩

namespace TraceToLevelOne

open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

def PM (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) : Prop := g ∈ Γ ∨ -g ∈ Γ

theorem PM.mul {g h : SL(2, ℤ)} (hg : PM Γ g) (hh : PM Γ h) : PM Γ (g * h) := by
  rcases hg with hg | hg <;> rcases hh with hh | hh
  · exact Or.inl (Γ.mul_mem hg hh)
  · refine Or.inr ?_
    rw [show -(g * h) = g * (-h) by rw [mul_neg]]
    exact Γ.mul_mem hg hh
  · refine Or.inr ?_
    rw [show -(g * h) = (-g) * h by rw [neg_mul]]
    exact Γ.mul_mem hg hh
  · refine Or.inl ?_
    rw [show g * h = (-g) * (-h) by rw [neg_mul_neg]]
    exact Γ.mul_mem hg hh

theorem PM.inv {g : SL(2, ℤ)} (hg : PM Γ g) : PM Γ g⁻¹ := by
  rcases hg with hg | hg
  · exact Or.inl (Γ.inv_mem hg)
  · refine Or.inr ?_
    rw [show -g⁻¹ = (-g)⁻¹ by rw [neg_inv]]
    exact Γ.inv_mem hg

theorem slash_neg (hk : Even k) (F : ℍ → ℂ) (y : SL(2, ℤ)) : F ∣[k] (-y) = F ∣[k] y := by
  ext τ
  rw [ModularForm.SL_slash_apply, ModularForm.SL_slash_apply, ModularGroup.SL_neg_smul]
  congr 1
  have : ((-y : SL(2, ℤ)) : GL (Fin 2) ℝ) = -(y : GL (Fin 2) ℝ) := by
    ext i j
    simp [Matrix.SpecialLinearGroup.toGL]
  rw [this, denom_neg, Even.neg_zpow (Even.neg hk)]

variable (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)

theorem slash_pm_mul (hk : Even k) {γ : SL(2, ℤ)} (hγ : PM Γ γ) (y : SL(2, ℤ)) :
    (⇑f : ℍ → ℂ) ∣[k] (γ * y) = (⇑f : ℍ → ℂ) ∣[k] y := by
  rcases hγ with hγ | hγ
  · rw [SlashAction.slash_mul]
    exact congrArg (fun F : ℍ → ℂ => F ∣[k] y)
      (SlashInvariantFormClass.slash_action_eq f ((Matrix.SpecialLinearGroup.mapGL ℝ) γ) (Subgroup.mem_map_of_mem _ hγ))
  · rw [show γ * y = -((-γ) * y) by rw [neg_mul, neg_neg], slash_neg hk, SlashAction.slash_mul]
    exact congrArg (fun F : ℍ → ℂ => F ∣[k] y)
      (SlashInvariantFormClass.slash_action_eq f ((Matrix.SpecialLinearGroup.mapGL ℝ) (-γ)) (Subgroup.mem_map_of_mem _ hγ))

theorem mdifferentiable_sum {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (g i)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact fun _ => mdifferentiableAt_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isBoundedAtImInfty_sum {ι : Type*} (s : Finset ι) (g : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, IsBoundedAtImInfty (g i)) : IsBoundedAtImInfty (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Filter.const_boundedAtFilter _ _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end TraceToLevelOne

open scoped MatrixGroups ModularForm Manifold in
open UpperHalfPlane TraceToLevelOne in
theorem exists_levelOne_coe_eq_sum_slash
    (Γ : Subgroup SL(2, ℤ)) {k : ℤ} (hk : Even k)
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (s : Finset SL(2, ℤ))
    (hcover : ∀ g : SL(2, ℤ), ∃ x ∈ s, g * x⁻¹ ∈ Γ ∨ -(g * x⁻¹) ∈ Γ)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, (x * y⁻¹ ∈ Γ ∨ -(x * y⁻¹) ∈ Γ) → x = y) :
    ∃ F : ModularForm 𝒮ℒ k,
      (⇑F : UpperHalfPlane → ℂ) = ∑ x ∈ s, ((⇑f : UpperHalfPlane → ℂ) ∣[k] ((x : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  classical

  have : Γ.FiniteIndex := by
    have : Finite (SL(2, ℤ) ⧸ Γ) := by
      refine Finite.of_surjective
        (fun p : s × Bool => (QuotientGroup.mk (if p.2 then ((p.1 : SL(2, ℤ)))⁻¹ else (-(p.1 : SL(2, ℤ)))⁻¹) : SL(2, ℤ) ⧸ Γ))
        (fun q => ?_)
      induction q using QuotientGroup.induction_on with
      | H h =>
        obtain ⟨x, hx, hgx⟩ := hcover h⁻¹
        rcases hgx with hgx | hgx
        · refine ⟨⟨⟨x, hx⟩, true⟩, ?_⟩
          simp only [ite_true]
          rw [QuotientGroup.eq, inv_inv]
          have h1 : (h⁻¹ * x⁻¹)⁻¹ ∈ Γ := Γ.inv_mem hgx
          rwa [mul_inv_rev, inv_inv, inv_inv] at h1
        · refine ⟨⟨⟨x, hx⟩, false⟩, ?_⟩
          simp only [Bool.false_eq_true, ite_false]
          rw [QuotientGroup.eq, inv_inv]
          have h1 : (-(h⁻¹ * x⁻¹))⁻¹ ∈ Γ := Γ.inv_mem hgx
          have h2 : (-(h⁻¹ * x⁻¹))⁻¹ = -x * h := by
            rw [← neg_inv, mul_inv_rev, inv_inv, inv_inv, neg_mul]
          rwa [h2] at h1
    exact Subgroup.finiteIndex_of_finite_quotient

  have rep : ∀ g : SL(2, ℤ), ∃ x ∈ s, PM Γ (g * x⁻¹) := hcover
  choose ρ hρs hρ using rep

  have ρ_eq : ∀ (g : SL(2, ℤ)) (x : SL(2, ℤ)), x ∈ s → PM Γ (g * x⁻¹) → ρ g = x := fun g x hx hgx =>
    hsep _ (hρs g) _ hx (by
      have := (hρ g).inv.mul hgx
      rwa [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] at this)

  set T : ℍ → ℂ := ∑ x ∈ s, ((⇑f : ℍ → ℂ) ∣[k] ((x : SL(2, ℤ)) : GL (Fin 2) ℝ)) with hT
  have hTx : T = ∑ x ∈ s, ((⇑f : ℍ → ℂ) ∣[k] x) := by
    rw [hT]; exact Finset.sum_congr rfl fun x _ => (ModularForm.SL_slash _ x).symm

  have hinv : ∀ a : SL(2, ℤ), T ∣[k] a = T := by
    intro a
    rw [hTx, SlashAction.sum_slash]
    simp_rw [← SlashAction.slash_mul]
    refine Finset.sum_nbij' (fun x => ρ (x * a)) (fun x => ρ (x * a⁻¹)) (fun x _ => hρs _) (fun x _ => hρs _)
      (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · apply ρ_eq _ _ hx
      have := (hρ (x * a)).inv
      rw [mul_inv_rev, inv_inv, mul_inv_rev, ← mul_assoc] at this
      exact this
    · apply ρ_eq _ _ hx
      have := (hρ (x * a⁻¹)).inv
      rw [mul_inv_rev, inv_inv, mul_inv_rev, inv_inv, ← mul_assoc] at this
      exact this
    ·
      have h := slash_pm_mul f hk (hρ (x * a)) (ρ (x * a))
      rw [inv_mul_cancel_right] at h
      exact h
  have hslash : ∀ A ∈ 𝒮ℒ, T ∣[k] A = T := by
    intro A hA
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hA
    exact hinv a
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) T := by
    rw [hT]
    exact mdifferentiable_sum s _ fun x _ => (ModularFormClass.holo f).slash k _
  have hbdd : ∀ {c : OnePoint ℝ}, IsCusp c 𝒮ℒ → c.IsBoundedAt T k := by
    intro c hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ hγ
    rw [hTx, SlashAction.sum_slash]
    refine isBoundedAtImInfty_sum s _ fun x _ => ?_
    rw [← SlashAction.slash_mul]
    exact ModularFormClass.bdd_at_infty_slash f (x * γ)
  exact ⟨ModularForm.mk (SlashInvariantForm.mk T hslash) hholo (fun hc => hbdd hc), rfl⟩

namespace EMONO

open EisensteinSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, h5]
  norm_num [Nat.choose]

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]

noncomputable def P (c : ℤ) (k : ℕ) : PowerSeries ℤ := PowerSeries.mk fun m => if m = 0 then 1 else c * (ArithmeticFunction.sigma k m : ℤ)

theorem constantCoeff_P (c : ℤ) (k : ℕ) : PowerSeries.constantCoeff (P c k) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P, PowerSeries.coeff_mk, ite_eq_left rfl]

theorem map_P_eq {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (c : ℤ) (hc : (c : ℂ) = -(2 * k / bernoulli k : ℂ)) :
    (P c (k - 1)).map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑(E hk) : UpperHalfPlane → ℂ) := by
  ext m
  rw [PowerSeries.coeff_map, E_qExpansion_coeff hk hk2 m, P, PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · simp only [map_mul, eq_intCast, Int.cast_natCast]
    rw [hc]

theorem map_P4 : (P 240 3).map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑E₄ : UpperHalfPlane → ℂ) := by
  refine map_P_eq (k := 4) (by norm_num) ⟨2, rfl⟩ 240 ?_
  rw [bernoulli_four]; push_cast; norm_num

theorem map_P6 : (P (-504) 5).map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑E₆ : UpperHalfPlane → ℂ) := by
  refine map_P_eq (k := 6) (by norm_num) ⟨3, rfl⟩ (-504) ?_
  rw [bernoulli_six]; push_cast; norm_num

end EMONO

open EMONO in
theorem exists_levelOne_qExpansion_eq_map_int_constantCoeff_one (a b : ℕ) (e : ℤ)
    (he : 4 * (a : ℤ) + 6 * (b : ℤ) = e) :
    ∃ (E : ModularForm 𝒮ℒ e) (P : PowerSeries ℤ),
      P.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ) ∧
      PowerSeries.constantCoeff P = 1 := by
  have hw : (a : ℤ) * 4 + (b : ℤ) * 6 = e := by rw [← he]; ring
  refine ⟨ModularForm.mcast hw ((E₄.pow a).mul (E₆.pow b)), EMONO.P 240 3 ^ a * EMONO.P (-504) 5 ^ b, ?_, ?_⟩
  · rw [map_mul, map_pow, map_pow, map_P4, map_P6, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  · rw [map_mul, map_pow, map_pow, constantCoeff_P, constantCoeff_P, one_pow, one_pow, one_mul]

theorem exists_qExpansion_eq_aeval_mul_pow_levelOne (N : ℕ) (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) : ∃ P : Polynomial ℂ, P.natDegree ≤ N ∧ ((qExpansion 1 (F : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = Polynomial.aeval (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3 / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) P * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ N := by
  induction N with
  | zero =>
    obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const
      (ModularForm.mcast (show (12 * ((0 : ℕ) : ℤ)) = 0 by simp) F)
    rw [ModularForm.coe_mcast] at hc
    have hconst : Function.const ℍ c = ⇑(c • (1 : ModularForm 𝒮ℒ 0)) := by
      funext τ
      simp
    have hq : qExpansion 1 (F : ℍ → ℂ) = c • (1 : PowerSeries ℂ) := by
      rw [hc, hconst, FunLike.coe_smul,
        ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
        ModularForm.qExpansion_one]
    have hbridge : (algebraMap ℂ (LaurentSeries ℂ)) c
        = ((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ) := by
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq]
    refine ⟨Polynomial.C c, by simp, ?_⟩
    rw [hq, PowerSeries.smul_eq_C_mul, mul_one, Polynomial.aeval_C, pow_zero, mul_one, hbridge]
  | succ N ih =>
    have hw : ((3 * (N + 1) : ℕ) : ℤ) * 4 = 12 * ((N + 1 : ℕ) : ℤ) := by push_cast; ring
    set c : ℂ := (qExpansion 1 (F : ℍ → ℂ)).coeff 0 with hcdef
    set Epow : ModularForm 𝒮ℒ (12 * ((N + 1 : ℕ) : ℤ)) :=
      ModularForm.mcast hw (ModularForm.E₄.pow (3 * (N + 1))) with hEpow
    set G : ModularForm 𝒮ℒ (12 * ((N + 1 : ℕ) : ℤ)) := F - c • Epow with hGdef
    have hE40 : (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)).coeff 0 = 1 :=
      EisensteinSeries.E_qExpansion_coeff_zero (by norm_num) ⟨2, rfl⟩
    have hGq : qExpansion 1 (G : ℍ → ℂ) = qExpansion 1 (F : ℍ → ℂ)
        - PowerSeries.C c * (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ (3 * (N + 1)) := by
      rw [hGdef, FunLike.coe_sub, ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
        FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
        hEpow, ModularForm.qExpansion_mcast,
        ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, PowerSeries.smul_eq_C_mul]
    have hpow0 : ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ (3 * (N + 1))).coeff 0 = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hE40, one_pow]
    have hCc : (PowerSeries.C c
        * (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ (3 * (N + 1))).coeff 0 = c := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, PowerSeries.constantCoeff_C,
        ← PowerSeries.coeff_zero_eq_constantCoeff_apply, hpow0, mul_one]
    have h0 : (qExpansion 1 (G : ℍ → ℂ)).coeff 0 = 0 := by
      rw [hGq, map_sub, hCc, ← hcdef, sub_self]
    have hkey := ModularForm.qExpansion_eq_qExpansion_discriminant_mul G h0
    have hw2 : (12 * ((N + 1 : ℕ) : ℤ)) - 12 = 12 * ((N : ℕ) : ℤ) := by push_cast; ring
    obtain ⟨P', hdeg', hP'⟩ :=
      ih (ModularForm.mcast hw2 (CuspForm.discriminantEquiv (ModularForm.toCuspForm G h0)))
    rw [ModularForm.coe_mcast] at hP'
    refine ⟨Polynomial.C c * Polynomial.X ^ (N + 1) + P', ?_, ?_⟩
    · exact Polynomial.natDegree_add_le_of_degree_le
        (Polynomial.natDegree_C_mul_X_pow_le c (N + 1)) (hdeg'.trans (Nat.le_succ N))
    · have hsum : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ)
          * qExpansion 1 (CuspForm.discriminantEquiv (ModularForm.toCuspForm G h0) : ℍ → ℂ)
          + PowerSeries.C c * (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ (3 * (N + 1))
          = qExpansion 1 (F : ℍ → ℂ) := by
        rw [← hkey]
        exact eq_sub_iff_add_eq.mp hGq
      have hL : ((qExpansion 1 (F : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
          = ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
            * ((qExpansion 1 (CuspForm.discriminantEquiv (ModularForm.toCuspForm G h0) : ℍ → ℂ) :
                PowerSeries ℂ) : LaurentSeries ℂ)
            + ((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ)
              * ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
                ^ (3 * (N + 1)) := by
        rw [← hsum]
        push_cast
        ring
      rw [hL, hP']
      have hΔ0 : qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) ≠ 0 := by
        intro h
        simpa [h] using ModularForm.discriminant_qExpansion_coeff_one
      have hΔL0 : ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) :
          LaurentSeries ℂ) ≠ 0 := by
        rw [Ne, ← PowerSeries.coe_zero]
        exact fun h => hΔ0 (HahnSeries.ofPowerSeries_injective h)
      have hsplit : (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3)
            ^ (N + 1)
          = (((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) ^ 3
              / ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
              ^ (N + 1)
            * ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
              ^ (N + 1) := by
        rw [← mul_pow, div_mul_cancel₀ _ hΔL0]
      have hbridge : (algebraMap ℂ (LaurentSeries ℂ)) c
          = ((PowerSeries.C c : PowerSeries ℂ) : LaurentSeries ℂ) := by
        rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq]
      rw [pow_mul, hsplit, map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, hbridge]
      ring

end ModularForm

end
