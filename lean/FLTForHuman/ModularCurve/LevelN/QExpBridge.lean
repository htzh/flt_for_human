/-
  The level-`N` `q`-expansion bridge: the ring homomorphism `Φ` out of the
  `q`-expansion function field of `X(N)` and its `q`-expansion `ℂ`-algebra map `E`.

  This is the twin development the pin writes twice in
  `P2M/Sol/S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN.lean`
  (955 ln) and its `_qExpansion` form (982 ln).  The two files are the same
  transcription: 98 of their 101 declaration groups are statement-identical and
  only three declarations live in one file alone — the stronger file's `main2`
  and `solution` and the weaker file's `solution`, which is the stronger
  headline with the two `E` conjuncts deleted.  So the port writes the stronger
  development once, `private`, in the pin's own sub-namespace, and derives the
  weaker headline from it (`WORKORDER-E-levelN-qexp-bridge.md`).

  The pin's per-file prelude (the `Good`/`Q` toolkit, the `ring N` action
  lemmas, `PB`, `Q_natCast_eq_qExpand` and the `Δ`-non-vanishing block) is
  already public in `LevelN/Prelude.lean` from subject A and is imported here,
  not re-derived: of the 101 groups, 46 match a port declaration byte for byte
  and `good_of_PB` matches after the pin's `M` is read as the port's `N`
  (port_advise's near-duplicate list, ratio 0.976).  The three few-line
  adaptors the pin declares publicly — `algebraMap_laurentSeries`,
  `one_mem_strictPeriods` and `coeffMap_ofPowerSeries` — stay `private` here:
  they adapt `HahnSeries`/`PowerSeries` and `Subgroup.strictPeriods` and carry
  no mathematics another theory states, so no promotion is made (playbook
  section 4(b)).

  The two public theorems are the pin's `Theorems/` wrappers verbatim, proved by
  the private `main` (`_levelN`) and `main2` (`_qExpansion`).

  FLT provenance, pinned `aa2d8b3`:
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion.lean
-/
import FLTForHuman.ModularCurve.LevelN.FieldGalois
import FLTForHuman.ModularCurve.LevelN.Prelude

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter Topology Function

open scoped MatrixGroups Manifold Real ModularForm

namespace ModularCurve

namespace LevelN

namespace QExpBridge

section Forms

local notation "Δ" => ModularForm.discriminant

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

private abbrev den (γ : SL(2, ℤ)) (τ : ℍ) : ℂ := denom (γ : GL (Fin 2) ℝ) τ

private theorem den_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : den γ τ ≠ 0 := denom_ne_zero _ _

private theorem apply_smul_eq_slash (f : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = (f ∣[k] γ) τ * den γ τ ^ k := by
  rw [ModularForm.SL_slash_apply, mul_assoc, ← zpow_add₀ (den_ne_zero γ τ), neg_add_cancel, zpow_zero,
    mul_one]

private theorem discriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) : Δ (γ • τ) = den γ τ ^ (12 : ℤ) * Δ τ := by
  have hmem : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  have := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hmem τ
  simpa [ModularGroup.sl_moeb] using this

private theorem apply_smul_of_mem (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ)
    (τ : ℍ) : f (δ • τ) = den δ τ ^ k * f τ := by
  have hmem : (δ : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := ⟨δ, hδ, rfl⟩
  have := SlashInvariantForm.slash_action_eqn'' f hmem τ
  simpa [ModularGroup.sl_moeb] using this

private theorem one_mem_strictPeriods (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

private theorem good_coe (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : Good 1 (f : ℍ → ℂ) where
  periodic := SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods hT)
  mdiff := f.holo'
  bdd := ModularFormClass.bdd_at_infty f

private theorem isBoundedAtImInfty_slash [Γ.FiniteIndex] (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) : IsBoundedAtImInfty ((f : ℍ → ℂ) ∣[k] γ) :=
  ModularFormClass.bdd_at_infty_slash f γ

end Forms

section Quotients

local notation "Δ" => ModularForm.discriminant

private def FF (k : ℤ) (f g : ℍ → ℂ) : ℍ → ℂ := fun τ => f τ * g τ ^ 11 * Δ τ ^ (-k)

private theorem FF_apply (k : ℤ) (f g : ℍ → ℂ) (τ : ℍ) : FF k f g τ = f τ * g τ ^ 11 * Δ τ ^ (-k) := rfl

private theorem zpow_neg_mul_pow_toNat (x : ℂ) (hx : x ≠ 0) (k : ℤ) :
    x ^ (-k) * x ^ k.toNat = x ^ (-k).toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  have := Int.toNat_sub_toNat_neg k
  omega

private theorem FF_mul_pow (k : ℤ) (f g : ℍ → ℂ) :
    FF k f g * (Δ : ℍ → ℂ) ^ k.toNat = f * g ^ 11 * (Δ : ℍ → ℂ) ^ (-k).toNat := by
  funext τ
  simp only [Pi.mul_apply, Pi.pow_apply, FF_apply]
  rw [mul_assoc, zpow_neg_mul_pow_toNat _ (ModularForm.discriminant_ne_zero τ)]

private theorem mdifferentiable_discriminant : MDiff (Δ : ℍ → ℂ) := CuspForm.discriminant.holo'

private theorem mdifferentiable_discriminant_zpow (n : ℤ) : MDiff (fun τ : ℍ => Δ τ ^ n) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hd : DifferentiableOn ℂ ((Δ : ℍ → ℂ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_discriminant
  have : (fun τ : ℍ => Δ τ ^ n) ∘ ofComplex = fun z => ((Δ : ℍ → ℂ) ∘ ofComplex) z ^ n := rfl
  rw [this]
  exact hd.zpow (Or.inl fun z hz => by
    rw [Function.comp_apply]; exact ModularForm.discriminant_ne_zero _)

private theorem mdifferentiable_FF (k : ℤ) {f g : ℍ → ℂ} (hf : MDiff f) (hg : MDiff g) : MDiff (FF k f g) := by
  have : FF k f g = f * g ^ 11 * (fun τ : ℍ => Δ τ ^ (-k)) := by
    funext τ; simp [FF_apply]
  rw [this]
  exact (hf.mul (hg.pow 11)).mul (mdifferentiable_discriminant_zpow (-k))

private theorem factor_cancel (d : ℂ) (hd : d ≠ 0) (k : ℤ) :
    d ^ k * (d ^ k) ^ 11 * (d ^ (12 : ℤ)) ^ (-k) = 1 := by
  rw [← zpow_natCast (d ^ k) 11, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hd, ← zpow_add₀ hd]
  have : k + k * ((11 : ℕ) : ℤ) + 12 * -k = 0 := by push_cast; ring
  rw [this, zpow_zero]

private theorem FF_smul (k : ℤ) (f g : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    FF k f g (γ • τ) = FF k (f ∣[k] γ) (g ∣[k] γ) τ := by
  rw [FF_apply, FF_apply, apply_smul_eq_slash f γ τ, apply_smul_eq_slash g γ τ, discriminant_smul γ τ]
  have hd := den_ne_zero γ τ
  set d := den γ τ
  rw [mul_pow, mul_zpow]
  have hc := factor_cancel d hd k
  calc (f ∣[k] γ) τ * d ^ k * ((g ∣[k] γ) τ ^ 11 * (d ^ k) ^ 11) * ((d ^ (12 : ℤ)) ^ (-k) * Δ τ ^ (-k))
      = (f ∣[k] γ) τ * (g ∣[k] γ) τ ^ 11 * Δ τ ^ (-k) * (d ^ k * (d ^ k) ^ 11 * (d ^ (12 : ℤ)) ^ (-k)) := by
        ring
    _ = (f ∣[k] γ) τ * (g ∣[k] γ) τ ^ 11 * Δ τ ^ (-k) := by rw [hc, mul_one]

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

private theorem FF_smul_of_mem (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) {δ : SL(2, ℤ)} (hδ : δ ∈ Γ)
    (τ : ℍ) : FF k f g (δ • τ) = FF k f g τ := by
  rw [FF_smul]
  have hmem : (δ : GL (Fin 2) ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := ⟨δ, hδ, rfl⟩
  have hf : (f : ℍ → ℂ) ∣[k] δ = f := by
    rw [ModularForm.SL_slash]; exact SlashInvariantFormClass.slash_action_eq f _ hmem
  have hg : (g : ℍ → ℂ) ∣[k] δ = g := by
    rw [ModularForm.SL_slash]; exact SlashInvariantFormClass.slash_action_eq g _ hmem
  rw [hf, hg]

private theorem isBoundedAtImInfty_FF_smul [Γ.FiniteIndex] (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (γ : SL(2, ℤ)) : IsBoundedAtImInfty ((fun τ => FF k f g (γ • τ)) * (Δ : ℍ → ℂ) ^ k.toNat) := by
  have : (fun τ => FF k f g (γ • τ)) = FF k ((f : ℍ → ℂ) ∣[k] γ) ((g : ℍ → ℂ) ∣[k] γ) := by
    funext τ; exact FF_smul k f g γ τ
  rw [this, FF_mul_pow]
  have hg11 : IsBoundedAtImInfty (((g : ℍ → ℂ) ∣[k] γ) ^ 11) := by
    have hb := isBoundedAtImInfty_slash g γ
    have : ∀ n : ℕ, IsBoundedAtImInfty (((g : ℍ → ℂ) ∣[k] γ) ^ n) := by
      intro n
      induction n with
      | zero => rw [pow_zero]; exact Filter.const_boundedAtFilter _ _
      | succ n ih => rw [pow_succ]; exact ih.mul hb
    exact this 11
  exact ((isBoundedAtImInfty_slash f γ).mul hg11).mul (((good_discriminant 1).pow _).bdd)

end Quotients

section Family

local notation "Δ" => ModularForm.discriminant

variable (M : ℕ) [NeZero M]

private theorem castM_pos : (0 : ℝ) < M := Nat.cast_pos.mpr (NeZero.pos M)

private def famS : Set (ℍ → ℂ) :=
  {G | MDiff G ∧ (∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, G (δ • τ) = G τ) ∧
    ∀ γ : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty ((fun τ => G (γ • τ)) * (Δ : ℍ → ℂ) ^ m)}

private theorem mdifferentiable_sl_smul (γ : SL(2, ℤ)) : MDiff (fun τ : ℍ => γ • τ) := by
  have : (fun τ : ℍ => γ • τ) = fun τ : ℍ => (γ : GL (Fin 2) ℝ) • τ := by
    funext τ; exact ModularGroup.sl_moeb γ τ
  rw [this]
  apply UpperHalfPlane.mdifferentiable_smul
  simp

set_option linter.unusedSectionVars false in
private theorem famS_stable (γ : SL(2, ℤ)) : ∀ G ∈ famS M, (G ∘ (γ • ·)) ∈ famS M := by
  rintro G ⟨hG, hinv, hpb⟩
  have : (CongruenceSubgroup.Gamma M).Normal := CongruenceSubgroup.Gamma_normal M
  refine ⟨hG.comp (mdifferentiable_sl_smul γ), fun δ hδ τ => ?_, fun γ' => ?_⟩
  · change G (γ • δ • τ) = G (γ • τ)
    have hconj : γ * δ * γ⁻¹ ∈ CongruenceSubgroup.Gamma M := Subgroup.Normal.conj_mem inferInstance δ hδ γ
    have := hinv _ hconj (γ • τ)
    rw [← this, ← mul_smul, ← mul_smul]
    congr 1
    group
  · obtain ⟨m, hm⟩ := hpb (γ * γ')
    refine ⟨m, ?_⟩
    have : (fun τ => (G ∘ (γ • ·)) (γ' • τ)) = fun τ => G ((γ * γ') • τ) := by
      funext τ; simp [mul_smul]
    rw [this]; exact hm

private theorem exists_levelFraction {G : ℍ → ℂ} (hG : G ∈ famS M) :
    ∃ a b : ℍ → ℂ, a ∈ ring M ∧ b ∈ ring M ∧ b ≠ 0 ∧ G * b = a :=
  WLight.exists_levelFraction_of_stable_family M PeriodPair.ofTau (fun τ => ⟨rfl, rfl⟩) (wp M)
    (fun v τ => rfl) (fricke M) (fun v τ => rfl) jAnalytic (fun τ => rfl) (famS M)
    (fun G hG => hG.1)
    (fun G hG => by
      obtain ⟨m, hm⟩ := hG.2.2 1
      exact ⟨m, by simpa using hm⟩)
    (famS_stable M) (fun G hG => hG.2.1) hG

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

set_option linter.unusedSectionVars false in
private theorem FF_mem_famS (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) [Γ.FiniteIndex]
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : FF k f g ∈ famS M :=
  ⟨mdifferentiable_FF k f.holo' g.holo', fun _δ hδ τ => FF_smul_of_mem f g (hΓ hδ) τ,
    fun γ => ⟨k.toNat, isBoundedAtImInfty_FF_smul f g γ⟩⟩

private theorem periodic_FF (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : Periodic (FF k f g ∘ ofComplex) 1 := by
  intro z
  have hf := (good_coe hT f).periodic z
  have hg := (good_coe hT g).periodic z
  have hΔ := (by simpa using (good_discriminant 1).periodic : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) 1) z
  simp only [Function.comp_apply, Complex.ofReal_one] at hf hg hΔ ⊢
  rw [FF_apply, FF_apply, hf, hg, hΔ]

set_option linter.unusedSectionVars false in
private theorem good_FF_mul_pow (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    Good M (FF k f g * (Δ : ℍ → ℂ) ^ k.toNat) where
  periodic := by
    have h1 : Periodic ((FF k f g * (Δ : ℍ → ℂ) ^ k.toNat) ∘ ofComplex) 1 := by
      have : (FF k f g * (Δ : ℍ → ℂ) ^ k.toNat) ∘ ofComplex =
          (FF k f g ∘ ofComplex) * (((Δ : ℍ → ℂ) ^ k.toNat) ∘ ofComplex) := rfl
      rw [this]
      exact (periodic_FF hT f g).mul (by simpa using ((good_discriminant 1).pow k.toNat).periodic)
    simpa using h1.nat_mul M
  mdiff := (mdifferentiable_FF k f.holo' g.holo').mul ((good_discriminant M).pow _).mdiff
  bdd := by simpa using isBoundedAtImInfty_FF_smul f g 1

set_option linter.unusedSectionVars false in
private theorem Good.of_one {f : ℍ → ℂ} (hf : Good 1 f) : Good M f where
  periodic := by simpa using hf.periodic.nat_mul M
  mdiff := hf.mdiff
  bdd := hf.bdd

private theorem Q_FF_mul_pow (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    Q M (FF k f g * (Δ : ℍ → ℂ) ^ k.toNat) =
      Q M f * Q M g ^ 11 * Q M (Δ : ℍ → ℂ) ^ (-k).toNat := by
  have hM := castM_pos M
  have hf : Good M (f : ℍ → ℂ) := Good.of_one M (good_coe hT f)
  have hg : Good M (g : ℍ → ℂ) := Good.of_one M (good_coe hT g)
  rw [FF_mul_pow, Q_mul hM (hf.mul (hg.pow 11)) ((good_discriminant M).pow _), Q_mul hM hf (hg.pow 11),
    Q_pow hM hg, Q_pow hM (good_discriminant M)]

end Family

section Expansion

local notation "Δ" => ModularForm.discriminant

variable (M : ℕ) [NeZero M]
variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring M) K] [IsScalarTower ℂ (ring M) K]
  [IsFractionRing (ring M) K]

private def E : K →ₐ[ℂ] LaurentSeries ℂ :=
  (ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion M K).choose

private theorem E_jGen : E M K (algebraMap (ring M) K (jGen M)) = ModularCurve.qExpand ℂ M (jqModC ℂ) :=
  (ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion M K).choose_spec.1

private theorem E_mul_pow (F : ℍ → ℂ) (hF : F ∈ ring M) (m : ℕ) (hm : IsBoundedAtImInfty (F * (Δ : ℍ → ℂ) ^ m)) :
    E M K (algebraMap (ring M) K ⟨F, hF⟩) * Q M (Δ : ℍ → ℂ) ^ m = Q M (F * (Δ : ℍ → ℂ) ^ m) :=
  (ModularCurve.LevelN.exists_algHom_laurentSeries_qExpansion M K).choose_spec.2 F hF m hm

private theorem E_injective : Function.Injective (E M K) := (E M K).toRingHom.injective

set_option linter.unusedSectionVars false in
private theorem algebraMap_ne_zero {b : ℍ → ℂ} (hb : b ∈ ring M) (hb0 : b ≠ 0) :
    algebraMap (ring M) K ⟨b, hb⟩ ≠ 0 := by
  intro h
  have : (⟨b, hb⟩ : ring M) = 0 := (IsFractionRing.injective (ring M) K) (by rw [h, map_zero])
  exact hb0 (congrArg Subtype.val this)


private theorem E_div_eq {G a b : ℍ → ℂ} (ha : a ∈ ring M) (hb : b ∈ ring M) (hb0 : b ≠ 0) (hGb : G * b = a)
    {p : ℕ} (hGp : Good M (G * (Δ : ℍ → ℂ) ^ p)) :
    E M K (algebraMap (ring M) K ⟨a, ha⟩) / E M K (algebraMap (ring M) K ⟨b, hb⟩) =
      Q M (G * (Δ : ℍ → ℂ) ^ p) / Q M (Δ : ℍ → ℂ) ^ p := by
  have hM := castM_pos M
  have hΔ0 : Q M (Δ : ℍ → ℂ) ≠ 0 := Q_discriminant_ne_zero M
  obtain ⟨mb, hmb⟩ := exists_isBoundedAtImInfty_mul_pow M hb
  have hgoodb := good_of_PB M hb hmb
  have ham : IsBoundedAtImInfty (a * (Δ : ℍ → ℂ) ^ (mb + p)) := by
    have : a * (Δ : ℍ → ℂ) ^ (mb + p) = (b * (Δ : ℍ → ℂ) ^ mb) * (G * (Δ : ℍ → ℂ) ^ p) := by
      rw [← hGb]; ring
    rw [this]; exact hmb.mul hGp.bdd
  have hEa := E_mul_pow M K a ha (mb + p) ham
  have hEb := E_mul_pow M K b hb mb hmb
  have hsplit : Q M (a * (Δ : ℍ → ℂ) ^ (mb + p)) = Q M (b * (Δ : ℍ → ℂ) ^ mb) * Q M (G * (Δ : ℍ → ℂ) ^ p) := by
    rw [← Q_mul hM hgoodb hGp]
    congr 1
    rw [← hGb]; ring
  have hEb0 : E M K (algebraMap (ring M) K ⟨b, hb⟩) ≠ 0 :=
    (map_ne_zero_iff _ (E_injective M K)).mpr (algebraMap_ne_zero M K hb hb0)
  have hQb0 : Q M (b * (Δ : ℍ → ℂ) ^ mb) ≠ 0 := by
    rw [ne_eq, Q_eq_zero_iff hM hgoodb, mul_discriminant_pow_eq_zero_iff]
    exact hb0
  rw [hsplit, pow_add] at hEa

  rw [eq_div_iff (pow_ne_zero p hΔ0), div_mul_eq_mul_div, div_eq_iff hEb0]
  apply mul_right_cancel₀ (pow_ne_zero mb hΔ0)
  calc E M K (algebraMap (ring M) K ⟨a, ha⟩) * Q M (Δ : ℍ → ℂ) ^ p * Q M (Δ : ℍ → ℂ) ^ mb
      = E M K (algebraMap (ring M) K ⟨a, ha⟩) * (Q M (Δ : ℍ → ℂ) ^ mb * Q M (Δ : ℍ → ℂ) ^ p) := by ring
    _ = Q M (b * (Δ : ℍ → ℂ) ^ mb) * Q M (G * (Δ : ℍ → ℂ) ^ p) := hEa
    _ = Q M (G * (Δ : ℍ → ℂ) ^ p) * (E M K (algebraMap (ring M) K ⟨b, hb⟩) * Q M (Δ : ℍ → ℂ) ^ mb) := by
        rw [hEb]; ring
    _ = Q M (G * (Δ : ℍ → ℂ) ^ p) * E M K (algebraMap (ring M) K ⟨b, hb⟩) * Q M (Δ : ℍ → ℂ) ^ mb := by
        ring

variable {Γ : Subgroup SL(2, ℤ)} {k : ℤ}

private theorem comp_smul_ne_zero {b : ℍ → ℂ} (hb0 : b ≠ 0) (γ : SL(2, ℤ)) : (fun τ : ℍ => b (γ • τ)) ≠ 0 := by
  intro h
  apply hb0
  funext τ
  have := congrFun h (γ⁻¹ • τ)
  simpa using this

private theorem exists_kappa (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (f g : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hg0 : (g : ℍ → ℂ) ≠ 0) :
    ∃ κ : K, E M K κ = Q M f / Q M g ∧
      ∀ γ ∈ Γ, ∀ (hst : ∀ G ∈ ring M, (fun τ : ℍ => G (γ⁻¹ • τ)) ∈ ring M) (φ : K ≃ₐ[ℂ] K),
        (∀ (G : ℍ → ℂ) (hG : G ∈ ring M),
            φ (algebraMap (ring M) K ⟨G, hG⟩) = algebraMap (ring M) K ⟨fun τ : ℍ => G (γ⁻¹ • τ), hst G hG⟩) →
        φ κ = κ := by
  have hM := castM_pos M
  have hΔ0 : Q M (Δ : ℍ → ℂ) ≠ 0 := Q_discriminant_ne_zero M
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := exists_levelFraction M (FF_mem_famS M hΓ f g)
  obtain ⟨a', b', ha', hb', hb0', hab'⟩ := exists_levelFraction M (FF_mem_famS M hΓ g g)
  refine ⟨(algebraMap (ring M) K ⟨a, ha⟩ / algebraMap (ring M) K ⟨b, hb⟩) /
    (algebraMap (ring M) K ⟨a', ha'⟩ / algebraMap (ring M) K ⟨b', hb'⟩), ?_, ?_⟩
  ·
    have h1 := E_div_eq M K ha hb hb0 hab (good_FF_mul_pow M hT f g)
    have h2 := E_div_eq M K ha' hb' hb0' hab' (good_FF_mul_pow M hT g g)
    simp only [map_div₀]
    rw [h1, h2, Q_FF_mul_pow M hT f g, Q_FF_mul_pow M hT g g]
    have hQg : Q M (g : ℍ → ℂ) ≠ 0 := by
      rw [ne_eq, Q_eq_zero_iff hM (Good.of_one M (good_coe hT g))]; exact hg0
    field_simp
  ·
    intro γ hγ hst φ hφ
    have hγ' : γ⁻¹ ∈ Γ := Γ.inv_mem hγ

    have key : ∀ (G a b : ℍ → ℂ) (ha : a ∈ ring M) (hb : b ∈ ring M), b ≠ 0 → G * b = a →
        (∀ τ, G (γ⁻¹ • τ) = G τ) →
        φ (algebraMap (ring M) K ⟨a, ha⟩ / algebraMap (ring M) K ⟨b, hb⟩) =
          algebraMap (ring M) K ⟨a, ha⟩ / algebraMap (ring M) K ⟨b, hb⟩ := by
      intro G a b ha hb hb0 hGb hGinv
      rw [map_div₀, hφ a ha, hφ b hb]
      have hb0'' : (fun τ : ℍ => b (γ⁻¹ • τ)) ≠ 0 := comp_smul_ne_zero hb0 γ⁻¹
      rw [div_eq_div_iff (algebraMap_ne_zero M K (hst b hb) hb0'') (algebraMap_ne_zero M K hb hb0),
        ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      change (fun τ : ℍ => a (γ⁻¹ • τ)) * b = a * (fun τ : ℍ => b (γ⁻¹ • τ))
      funext τ
      simp only [Pi.mul_apply]
      have h1 := congrFun hGb (γ⁻¹ • τ)
      have h2 := congrFun hGb τ
      simp only [Pi.mul_apply] at h1 h2
      rw [← h1, ← h2, hGinv τ]
      ring
    rw [map_div₀, key _ a b ha hb hb0 hab (fun τ => FF_smul_of_mem f g hγ' τ),
      key _ a' b' ha' hb' hb0' hab' (fun τ => FF_smul_of_mem g g hγ' τ)]

end Expansion

section Bridge

local notation "ℚ̄" => AlgebraicClosure ℚ

variable (M : ℕ) [NeZero M]
variable (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ring M) K] [IsScalarTower ℂ (ring M) K]
  [IsFractionRing (ring M) K]
variable (Γ : Subgroup SL(2, ℤ))

private def fixedSub : Subfield K where
  carrier := {κ | ∀ γ ∈ Γ, ∀ (hst : ∀ G ∈ ring M, (fun τ : ℍ => G (γ⁻¹ • τ)) ∈ ring M) (φ : K ≃ₐ[ℂ] K),
    (∀ (G : ℍ → ℂ) (hG : G ∈ ring M),
        φ (algebraMap (ring M) K ⟨G, hG⟩) = algebraMap (ring M) K ⟨fun τ : ℍ => G (γ⁻¹ • τ), hst G hG⟩) →
    φ κ = κ}
  mul_mem' {x y} hx hy := fun γ hγ hst φ hφ => by rw [map_mul, hx γ hγ hst φ hφ, hy γ hγ hst φ hφ]
  one_mem' := fun γ hγ hst φ hφ => map_one φ
  add_mem' {x y} hx hy := fun γ hγ hst φ hφ => by rw [map_add, hx γ hγ hst φ hφ, hy γ hγ hst φ hφ]
  zero_mem' := fun γ hγ hst φ hφ => map_zero φ
  neg_mem' {x} hx := fun γ hγ hst φ hφ => by rw [map_neg, hx γ hγ hst φ hφ]
  inv_mem' x hx := fun γ hγ hst φ hφ => by rw [map_inv₀, hx γ hγ hst φ hφ]

set_option linter.unusedSectionVars false in
private theorem algebraMap_mem_fixedSub (c : ℂ) : algebraMap ℂ K c ∈ fixedSub M K Γ :=
  fun _γ _hγ _hst φ _hφ => φ.commutes c

private def goodSeries : Subfield (LaurentSeries ℂ) := (fixedSub M K Γ).map (E M K).toRingHom

variable (ι : ℚ̄ →+* ℂ)

private theorem algebraMap_laurentSeries (c : ℂ) : algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := by
  have h1 : algebraMap ℂ (PowerSeries ℂ) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

private theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : PowerSeries R) :
    coeffMap φ (HahnSeries.ofPowerSeries ℤ R p) = HahnSeries.ofPowerSeries ℤ S (p.map φ) := by
  ext n
  rw [coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]
  · lift n to ℕ using hn
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

private def iotaM : LaurentSeries ℚ̄ →+* LaurentSeries ℂ :=
  (ModularCurve.qExpand ℂ M).comp (ModularCurve.coeffMap ι)

private theorem iotaM_algebraMap (c : ℚ̄) :
    iotaM M ι (algebraMap ℚ̄ (LaurentSeries ℚ̄) c) = HahnSeries.C (ι c) := by
  rw [iotaM, RingHom.comp_apply, ModularCurve.algebraMap_laurentSeries_eq_single,
    ModularCurve.coeffMap_single, ModularCurve.qExpand_single, mul_zero, HahnSeries.C_apply]

private theorem const_mem_goodSeries (c : ℚ̄) :
    iotaM M ι (algebraMap ℚ̄ (LaurentSeries ℚ̄) c) ∈ goodSeries M K Γ :=
  Subfield.mem_map.mpr ⟨algebraMap ℂ K (ι c), algebraMap_mem_fixedSub M K Γ _, by
    rw [iotaM_algebraMap]
    change E M K (algebraMap ℂ K (ι c)) = _
    rw [AlgHom.commutes, algebraMap_laurentSeries]⟩

private theorem iotaM_coeffEmb_intSeriesC {h : ℍ → ℂ} {p : PowerSeries ℤ} (hp : IsIntegralQExp h p) :
    iotaM M ι (coeffEmb ℚ̄ (intSeriesC ℚ p)) = ModularCurve.qExpand ℂ M (Q 1 h) := by
  rw [iotaM, RingHom.comp_apply]
  congr 1
  rw [coeffEmb, intSeriesC, ModularCurve.coeffMap_coeffMap, coeffMap_ofPowerSeries]
  have hmap : PowerSeries.map (ι.comp (algebraMap ℚ ℚ̄)) (PowerSeries.map (Int.castRingHom ℚ) p) =
      PowerSeries.map (Int.castRingHom ℂ) p := by
    rw [← RingHom.comp_apply (PowerSeries.map (ι.comp (algebraMap ℚ ℚ̄))) (PowerSeries.map (Int.castRingHom ℚ)),
      ← PowerSeries.map_comp,
      RingHom.ext_int ((ι.comp (algebraMap ℚ ℚ̄)).comp (Int.castRingHom ℚ)) (Int.castRingHom ℂ)]
  rw [hmap, Q, hp]

variable {Γ}

private theorem gen_mem_goodSeries (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    {x : LaurentSeries ℚ} (hx : x ∈ intFormRatiosC ℚ Γ) :
    iotaM M ι (coeffEmb ℚ̄ x) ∈ goodSeries M K Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hpg0, rfl⟩ := hx
  have hg0 : (g : ℍ → ℂ) ≠ 0 := by
    intro h0
    apply hpg0
    have h1 : pg.map (Int.castRingHom ℂ) = 0 := by
      rw [hg, h0, qExpansion_zero]
    have h2 : pg = 0 :=
      PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective (by rw [h1, map_zero])
    rw [h2, intSeriesC_zero]
  obtain ⟨κ, hκ, hfix⟩ := exists_kappa M K hΓ hT f g hg0
  refine Subfield.mem_map.mpr ⟨κ, fun γ hγ hst φ hφ => hfix γ hγ hst φ hφ, ?_⟩
  change E M K κ = _
  rw [hκ, map_div₀, map_div₀, iotaM_coeffEmb_intSeriesC M ι hf, iotaM_coeffEmb_intSeriesC M ι hg,
    Q_natCast_eq_qExpand M (good_coe hT f), Q_natCast_eq_qExpand M (good_coe hT g)]

private theorem laurentBaseChange_le (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    {u : LaurentSeries ℚ̄} (hu : u ∈ laurentBaseChange ℚ̄ (qExpFunctionFieldC ℚ Γ)) :
    iotaM M ι u ∈ goodSeries M K Γ := by
  have hF : (laurentBaseChange ℚ̄ (qExpFunctionFieldC ℚ Γ)).toSubfield ≤
      (goodSeries M K Γ).comap (iotaM M ι) := by
    rw [laurentBaseChange, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    apply Set.union_subset
    · rintro _ ⟨c, rfl⟩
      exact const_mem_goodSeries M K Γ ι c
    · rintro _ ⟨x, hx, rfl⟩
      change iotaM M ι (coeffEmb ℚ̄ x) ∈ goodSeries M K Γ
      have hF₀ : (qExpFunctionFieldC ℚ Γ).toSubfield ≤
          ((goodSeries M K Γ).comap (iotaM M ι)).comap (coeffEmb ℚ̄) := by
        rw [qExpFunctionFieldC, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        apply Set.union_subset
        · rintro _ ⟨r, rfl⟩
          change iotaM M ι (coeffEmb ℚ̄ (algebraMap ℚ (LaurentSeries ℚ) r)) ∈ goodSeries M K Γ
          have : coeffEmb ℚ̄ (algebraMap ℚ (LaurentSeries ℚ) r) =
              algebraMap ℚ̄ (LaurentSeries ℚ̄) (algebraMap ℚ ℚ̄ r) := by
            rw [ModularCurve.algebraMap_apply_eq_single, coeffEmb, ModularCurve.coeffMap_single,
              ModularCurve.algebraMap_laurentSeries_eq_single]
          rw [this]
          exact const_mem_goodSeries M K Γ ι _
        · intro x hx
          exact gen_mem_goodSeries M K ι hΓ hT hx
      exact hF₀ hx
  exact hF hu

variable (Γ)

local notation "FFq" => laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)

private theorem exists_kappa_of_mem (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex]
    (u : FFq) : ∃ κ : K, κ ∈ fixedSub M K Γ ∧ E M K κ = iotaM M ι (u : LaurentSeries ℚ̄) :=
  Subfield.mem_map.mp (laurentBaseChange_le M K ι hΓ hT u.2)

private def Phi (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex] : FFq →+* K where
  toFun u := (exists_kappa_of_mem M K Γ ι hΓ hT u).choose
  map_one' := by
    apply E_injective M K
    rw [(exists_kappa_of_mem M K Γ ι hΓ hT 1).choose_spec.2, map_one, OneMemClass.coe_one, map_one]
  map_mul' u v := by
    apply E_injective M K
    rw [(exists_kappa_of_mem M K Γ ι hΓ hT (u * v)).choose_spec.2, map_mul,
      (exists_kappa_of_mem M K Γ ι hΓ hT u).choose_spec.2, (exists_kappa_of_mem M K Γ ι hΓ hT v).choose_spec.2,
      MulMemClass.coe_mul, map_mul]
  map_zero' := by
    apply E_injective M K
    rw [(exists_kappa_of_mem M K Γ ι hΓ hT 0).choose_spec.2, map_zero, ZeroMemClass.coe_zero, map_zero]
  map_add' u v := by
    apply E_injective M K
    rw [(exists_kappa_of_mem M K Γ ι hΓ hT (u + v)).choose_spec.2, map_add,
      (exists_kappa_of_mem M K Γ ι hΓ hT u).choose_spec.2, (exists_kappa_of_mem M K Γ ι hΓ hT v).choose_spec.2,
      AddMemClass.coe_add, map_add]

private theorem E_Phi (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex] (u : FFq) :
    E M K (Phi M K Γ ι hΓ hT u) = iotaM M ι (u : LaurentSeries ℚ̄) :=
  (exists_kappa_of_mem M K Γ ι hΓ hT u).choose_spec.2

private theorem Phi_mem (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) [Γ.FiniteIndex] (u : FFq) :
    Phi M K Γ ι hΓ hT u ∈ fixedSub M K Γ :=
  (exists_kappa_of_mem M K Γ ι hΓ hT u).choose_spec.1

private theorem main (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) :
    ∃ Φ : FFq →+* K,
      (∀ c : ℚ̄, Φ (algebraMap ℚ̄ FFq c) = algebraMap ℂ K (ι c)) ∧
      (∀ y : FFq, (y : LaurentSeries ℚ̄) = jqModC ℚ̄ → Φ y = algebraMap (ring M) K (jGen M)) ∧
      ∀ γ ∈ Γ, ∀ (hst : ∀ G ∈ ring M, (fun τ : ℍ => G (γ⁻¹ • τ)) ∈ ring M) (φ : K ≃ₐ[ℂ] K),
        (∀ (G : ℍ → ℂ) (hG : G ∈ ring M),
            φ (algebraMap (ring M) K ⟨G, hG⟩) = algebraMap (ring M) K ⟨fun τ : ℍ => G (γ⁻¹ • τ), hst G hG⟩) →
        ∀ u, φ (Φ u) = Φ u := by
  have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  refine ⟨Phi M K Γ ι hΓ hT, fun c => ?_, fun y hy => ?_,
    fun γ hγ hst φ hφ u => (Phi_mem M K Γ ι hΓ hT u) γ hγ hst φ hφ⟩
  · apply E_injective M K
    rw [E_Phi]
    change iotaM M ι (algebraMap ℚ̄ (LaurentSeries ℚ̄) c) = _
    rw [iotaM_algebraMap, AlgHom.commutes, algebraMap_laurentSeries]
  · apply E_injective M K
    rw [E_Phi, hy, E_jGen, iotaM, RingHom.comp_apply]
    congr 1
    exact map_jqModC ι

private theorem main2 (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ) :
    ∃ (Φ : FFq →+* K) (E' : K →ₐ[ℂ] LaurentSeries ℂ),
      E' (algebraMap (ring M) K (jGen M)) = ModularCurve.qExpand ℂ M (jqModC ℂ) ∧
      (∀ u : FFq, E' (Φ u) = ModularCurve.qExpand ℂ M (ModularCurve.coeffMap ι (u : LaurentSeries ℚ̄))) ∧
      (∀ c : ℚ̄, Φ (algebraMap ℚ̄ FFq c) = algebraMap ℂ K (ι c)) ∧
      (∀ y : FFq, (y : LaurentSeries ℚ̄) = jqModC ℚ̄ → Φ y = algebraMap (ring M) K (jGen M)) ∧
      ∀ γ ∈ Γ, ∀ (hst : ∀ G ∈ ring M, (fun τ : ℍ => G (γ⁻¹ • τ)) ∈ ring M) (φ : K ≃ₐ[ℂ] K),
        (∀ (G : ℍ → ℂ) (hG : G ∈ ring M),
            φ (algebraMap (ring M) K ⟨G, hG⟩) = algebraMap (ring M) K ⟨fun τ : ℍ => G (γ⁻¹ • τ), hst G hG⟩) →
        ∀ u, φ (Φ u) = Φ u := by
  have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hΓ
  refine ⟨Phi M K Γ ι hΓ hT, E M K, E_jGen M K, fun u => ?_, fun c => ?_, fun y hy => ?_,
    fun γ hγ hst φ hφ u => (Phi_mem M K Γ ι hΓ hT u) γ hγ hst φ hφ⟩
  · rw [E_Phi]; rfl
  · apply E_injective M K
    rw [E_Phi]
    change iotaM M ι (algebraMap ℚ̄ (LaurentSeries ℚ̄) c) = _
    rw [iotaM_algebraMap, AlgHom.commutes, algebraMap_laurentSeries]
  · apply E_injective M K
    rw [E_Phi, hy, E_jGen, iotaM, RingHom.comp_apply]
    congr 1
    exact map_jqModC ι

end Bridge

end QExpBridge

end LevelN

end ModularCurve

namespace ModularCurve

/-- Pin `ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN`, at the
wrapper's statement: the `ℂ`-algebra homomorphism `Φ`` out of the level-`N` `q`-expansion
function field.  The pin proves it as `QExpBridge.solution` from the same `QExpBridge.main`. -/
theorem exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K] :
    ∃ Φ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ) →+* K,
      (∀ c : AlgebraicClosure ℚ,
          Φ (algebraMap (AlgebraicClosure ℚ)
            (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ)) c) =
            algebraMap ℂ K (ι c)) ∧
      (∀ y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ),
          (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
          Φ y = algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) ∧
      ∀ γ ∈ Γ, ∀ (hst : ∀ G ∈ ModularCurve.LevelN.ring M,
          (fun τ : UpperHalfPlane => G (γ⁻¹ • τ)) ∈ ModularCurve.LevelN.ring M)
        (φ : K ≃ₐ[ℂ] K),
        (∀ (G : UpperHalfPlane → ℂ) (hG : G ∈ ModularCurve.LevelN.ring M),
            φ (algebraMap (ModularCurve.LevelN.ring M) K ⟨G, hG⟩) =
              algebraMap (ModularCurve.LevelN.ring M) K
                ⟨fun τ : UpperHalfPlane => G (γ⁻¹ • τ), hst G hG⟩) →
        ∀ u, φ (Φ u) = Φ u :=
  ModularCurve.LevelN.QExpBridge.main M K Γ ι hΓ hT

/-- Pin `ModularCurve.exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion`,
at the wrapper's statement: `Φ` together with the `ℂ`-algebra map `E : K →ₐ[ℂ] LaurentSeries ℂ`
realizing the `q`-expansion on `K` and intertwining it with `Φ`.  The pin proves it as
`QExpBridge.solution` from `QExpBridge.main2`; the `_levelN` headline above is its projection. -/
theorem exists_ringHom_laurentBaseChange_qExpFunctionFieldC_levelN_qExpansion
    (M : ℕ) [NeZero M] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (ι : AlgebraicClosure ℚ →+* ℂ)
    (K : Type*) [Field K] [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring M) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring M) K]
    [IsFractionRing (ModularCurve.LevelN.ring M) K] :
    ∃ (Φ : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.qExpFunctionFieldC ℚ Γ) →+* K) (E : K →ₐ[ℂ] LaurentSeries ℂ),
      E (algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) =
          ModularCurve.qExpand ℂ M (ModularCurve.jqModC ℂ) ∧
      (∀ u : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ Γ),
          E (Φ u) = ModularCurve.qExpand ℂ M (ModularCurve.coeffMap ι (u : LaurentSeries (AlgebraicClosure ℚ)))) ∧
      (∀ c : AlgebraicClosure ℚ,
          Φ (algebraMap (AlgebraicClosure ℚ)
            (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.qExpFunctionFieldC ℚ Γ)) c) =
            algebraMap ℂ K (ι c)) ∧
      (∀ y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ Γ),
          (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ) →
          Φ y = algebraMap (ModularCurve.LevelN.ring M) K (ModularCurve.LevelN.jGen M)) ∧
      ∀ γ ∈ Γ, ∀ (hst : ∀ G ∈ ModularCurve.LevelN.ring M,
          (fun τ : UpperHalfPlane => G (γ⁻¹ • τ)) ∈ ModularCurve.LevelN.ring M)
        (φ : K ≃ₐ[ℂ] K),
        (∀ (G : UpperHalfPlane → ℂ) (hG : G ∈ ModularCurve.LevelN.ring M),
            φ (algebraMap (ModularCurve.LevelN.ring M) K ⟨G, hG⟩) =
              algebraMap (ModularCurve.LevelN.ring M) K
                ⟨fun τ : UpperHalfPlane => G (γ⁻¹ • τ), hst G hG⟩) →
        ∀ u, φ (Φ u) = Φ u :=
  ModularCurve.LevelN.QExpBridge.main2 M K Γ ι hΓ hT

end ModularCurve
