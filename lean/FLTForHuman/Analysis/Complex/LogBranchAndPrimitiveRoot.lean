/-
  Two `ℂ`-supplements:

  * `Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto` — a continuous
    branch `Λ` of the logarithm of a function `ℓ` on `(a, ∞)` which tends to a
    nonzero limit at `a` is bounded near `a`;
  * `Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot` — for
    `ℓ` prime, `M` prime to `ℓ`, an algebraically closed field `K` of
    characteristic `ℓ` and a primitive `M`-th root `ζ ∈ K`, there is a ring
    homomorphism `integralClosure ℤ ℂ →+* K` sending the distinguished
    `exp (2 π i / M)` to `ζ`.

  The ports of the two pin leaves (161 and 111 pin lines), together with the
  statements of their `Theorems/` wrappers, grouped as the order's `Complex`
  family.

  The mathematics of the first: near `a` the values of `ℓ` stay in the disc of
  radius `‖c‖ / 2` around `c`, so `w = ℓ / c` is close to `1` and
  `log (w s)` is bounded by `Complex.norm_log_one_add_half_le_self`; the two
  branches `Λ` and `Λ' = log w + log c` differ by a locally constant integer
  multiple of `2 π i` (a continuous `ℝ`-valued function taking integer values on
  an interval is constant), so `Λ` is bounded too.

  The mathematics of the second: `z = exp (2 π i / M)` is a primitive `M`-th root
  of unity in `ℂ` whose minimal polynomial over `ℤ` is `Φ_M`, so the evaluation
  `ℤ[z] → K` at `ζ` is a ring homomorphism; its kernel `𝔭` lifts to a prime `𝔔` of
  the integral closure, and `IsAlgClosed.lift` extends the residue field
  embedding `k₀ → K` to `ℤ̄ ⧸ 𝔔`.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has neither statement — `rg -n
  "exists_norm_le_of_continuousOn_of_exp_eq"` and `rg -n
  "integralClosure_int_apply_eq_of_isPrimitiveRoot"` over `Mathlib/` find nothing.
  The ingredients (`Complex.norm_log_one_add_half_le_self`,
  `Complex.exp_eq_one_iff`, `Complex.isPrimitiveRoot_exp`,
  `cyclotomic_eq_minpoly`, `AdjoinRoot.lift`, `minpoly.equivAdjoin`,
  `Ideal.exists_ideal_over_prime_of_isIntegral`, `IsAlgClosed.lift`) are imported,
  not restated.

  Heartbeats — the pin's own bumps, and where they went. The second pin file sets
  `set_option linter.unusedVariables false`, `synthInstance.maxHeartbeats 1600000`
  and `maxHeartbeats 8000000`; **all three are dropped**, and the port elaborates
  inside the 200,000 edit-loop budget (~20 s) because two instance-inference
  hotspots were fixed rather than budgeted:

  (a) `Function.Injective ι` (the pin: `rw [injective_iff_map_eq_zero]`) needs
      `AddGroup`/`AddMonoidHomClass` for the quotient `A₀ ⧸ 𝔔.comap (algebraMap A₀ ℤ̄)`;
      each candidate instance re-unfolds `Subalgebra` and `Ideal.comap`, and the
      search died at the default 20,000 `synthInstance` cap (measured: "timeout at
      `typeclass`, maximum number of heartbeats (20000) has been reached"). The port
      replaces it by mathlib's `RingHom.lift_injective_of_ker_le_ideal I (f := φ₁) hker
      hker_le`, whose only extra input is one `RingHom.ker φ₁ ≤ I` rewrite;
  (b) the pin's `set k₀ : Type _ := A₀ ⧸ …` makes every later instance goal
      (`IsDomain`, `FaithfulSMul`, `Module.IsTorsionFree`, `Algebra`) unfold the
      quotient *and* the `comap` again, and `Nontrivial k₀` alone exhausted the
      20,000-heart class budget. The port keeps the ideal as the named local
      `I : Ideal A₀` and writes the quotient type `A₀ ⧸ I`, and supplies
      `Nontrivial (A₀ ⧸ I)` explicitly from `hIprime.ne_top`
      (`Ideal.Quotient.nontrivial_iff`); every later search then matches a local
      instance syntactically.

  With (a) and (b) in place no `set_option` is needed: the module is green at
  `-DmaxHeartbeats=200000` and at the lakefile's 4,000,000 alike.

  Drift (beyond the two instance fixes above): the pin's
  `Ideal.Quotient.lift _ φ₁ (fun a ha => by rwa [hcomap] at ha)` does not elaborate
  in `v4.34.0`, where `hcomap : 𝔔.under A₀ = 𝔭` is stated with the `Ideal.under`
  abbreviation while the goal shows `Ideal.comap (algebraMap A₀ ℤ̄) 𝔔`; the port
  folds in `Ideal.under_def` (an `abbrev`-level `rfl`, so the statement is
  untouched) and carries the kernel condition as a `have hker`. The same
  `Ideal.under_def` conversion is needed in `hker_le`. `haveI`/`letI` → `have`/`let`
  (18 sites, the linter's preference; `have`/`let` still act as local instances).

  The pin `S_` files' block namespaces `P2mLogBranch` and `RedIntClosure` are not kept: their
  single public declaration each is the pin's `solution` wrapper, a duplicate of the headline,
  so both are `private` (`main_logBranch`, `main_primRoot`) and the headlines carry the API.

  spec-pin: Theorems/Thm_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.lean
  spec-pin: P2M/Sol/S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.lean
  spec-pin: Theorems/Thm_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot.lean
  spec-pin: P2M/Sol/S_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot.lean
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.CharP.Basic

set_option autoImplicit false

open Filter Topology Complex

private theorem main_logBranch {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
    (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
    (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C := by

  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨δ, hδ, hδball⟩ : ∃ δ > 0, ∀ s : ℝ, a < s → s < a + δ → ‖ℓ s - c‖ < ‖c‖ / 2 := by
    rw [Metric.tendsto_nhdsWithin_nhds] at hlim
    obtain ⟨δ, hδ, h⟩ := hlim (‖c‖ / 2) (half_pos hcpos)
    refine ⟨δ, hδ, fun s hs hsδ => ?_⟩
    have h' := h (Set.mem_Ioi.mpr hs) (by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith)
    rwa [dist_eq_norm] at h'

  set w : ℝ → ℂ := fun s => ℓ s / c with hw
  set Λ' : ℝ → ℂ := fun s => Complex.log (w s) + Complex.log c with hΛ'
  have hwball : ∀ s : ℝ, a < s → s < a + δ → ‖w s - 1‖ < 1 / 2 := by
    intro s hs hsδ
    have h1 : w s - 1 = (ℓ s - c) / c := by
      rw [hw]
      field_simp
    rw [h1, norm_div, div_lt_iff₀ hcpos]
    have := hδball s hs hsδ
    linarith
  have hw0 : ∀ s : ℝ, a < s → s < a + δ → w s ≠ 0 := by
    intro s hs hsδ h0
    have := hwball s hs hsδ
    rw [h0, zero_sub, norm_neg, norm_one] at this
    linarith
  have hexp' : ∀ s : ℝ, a < s → s < a + δ → Complex.exp (Λ' s) = ℓ s := by
    intro s hs hsδ
    rw [hΛ', Complex.exp_add, Complex.exp_log (hw0 s hs hsδ), Complex.exp_log hc, hw]
    field_simp
  have hbound' : ∀ s : ℝ, a < s → s < a + δ → ‖Λ' s‖ ≤ 3 / 4 + ‖Complex.log c‖ := by
    intro s hs hsδ
    have h1 : ‖Complex.log (w s)‖ ≤ 3 / 4 := by
      have h2 := Complex.norm_log_one_add_half_le_self (z := w s - 1) (hwball s hs hsδ).le
      rw [add_sub_cancel] at h2
      have := hwball s hs hsδ
      linarith
    calc ‖Λ' s‖ ≤ ‖Complex.log (w s)‖ + ‖Complex.log c‖ := norm_add_le _ _
      _ ≤ 3 / 4 + ‖Complex.log c‖ := by linarith

  have hℓcont : ContinuousOn ℓ (Set.Ioi a) := by
    have : ContinuousOn (fun s => Complex.exp (Λ s)) (Set.Ioi a) := hΛ.cexp
    exact this.congr fun s hs => (hexp s hs).symm
  have hΛ'cont : ContinuousOn Λ' (Set.Ioo a (a + δ)) := by
    apply ContinuousOn.add _ continuousOn_const
    have hwcont : ContinuousOn w (Set.Ioo a (a + δ)) :=
      (hℓcont.mono Set.Ioo_subset_Ioi_self).div_const c
    refine ContinuousOn.comp (s := Set.Ioo a (a + δ)) (t := slitPlane) (g := Complex.log) ?_ hwcont ?_
    · intro z hz
      exact (continuousAt_clog hz).continuousWithinAt
    · intro s hs
      have h := Complex.mem_slitPlane_of_norm_lt_one (z := w s - 1)
        (by linarith [hwball s hs.1 hs.2])
      rwa [add_sub_cancel] at h

  set d : ℝ → ℂ := fun s => Λ s - Λ' s with hd
  have hdint : ∀ s : ℝ, a < s → s < a + δ → ∃ n : ℤ, d s = n * (2 * Real.pi * Complex.I) := by
    intro s hs hsδ
    have h1 : Complex.exp (d s) = 1 := by
      rw [hd]
      simp only
      rw [Complex.exp_sub, hexp s hs, hexp' s hs hsδ, div_self]
      rw [← hexp s hs]
      exact Complex.exp_ne_zero _
    exact Complex.exp_eq_one_iff.mp h1
  have hdcont : ContinuousOn d (Set.Ioo a (a + δ)) := (hΛ.mono Set.Ioo_subset_Ioi_self).sub hΛ'cont

  set f : ℝ → ℝ := fun s => (d s).im / (2 * Real.pi) with hf
  have hfcont : ContinuousOn f (Set.Ioo a (a + δ)) := by
    refine ContinuousOn.div_const ?_ _
    exact Complex.continuous_im.comp_continuousOn hdcont
  have hfint : ∀ s : ℝ, a < s → s < a + δ → ∃ n : ℤ, f s = n ∧ d s = n * (2 * Real.pi * Complex.I) := by
    intro s hs hsδ
    obtain ⟨n, hn⟩ := hdint s hs hsδ
    refine ⟨n, ?_, hn⟩
    rw [hf]
    simp only
    rw [hn]
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re,
      Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.I_re, Complex.I_im, zero_mul, add_zero, mul_one]
    field_simp
  have hfconst : ∀ s₁ s₂ : ℝ, a < s₁ → s₁ < a + δ → a < s₂ → s₂ < a + δ → f s₁ = f s₂ := by
    intro s₁ s₂ h1 h1' h2 h2'
    obtain ⟨n₁, hn₁, -⟩ := hfint s₁ h1 h1'
    obtain ⟨n₂, hn₂, -⟩ := hfint s₂ h2 h2'
    by_contra hne
    rw [hn₁, hn₂] at hne
    have hne' : n₁ ≠ n₂ := fun h => hne (by rw [h])

    set y : ℝ := (min n₁ n₂ : ℤ) + 1 / 2 with hy
    have hymem : y ∈ Set.uIcc (f s₁) (f s₂) := by
      rw [hn₁, hn₂, Set.mem_uIcc]
      rcases lt_or_gt_of_ne hne' with h | h
      · left
        have : min n₁ n₂ = n₁ := min_eq_left h.le
        rw [hy, this]
        constructor
        · linarith
        · have : (n₁ : ℝ) + 1 ≤ n₂ := by exact_mod_cast h
          linarith
      · right
        have : min n₁ n₂ = n₂ := min_eq_right h.le
        rw [hy, this]
        constructor
        · linarith
        · have : (n₂ : ℝ) + 1 ≤ n₁ := by exact_mod_cast h
          linarith
    have hsub : Set.uIcc s₁ s₂ ⊆ Set.Ioo a (a + δ) := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      constructor
      · rcases ht with h | h <;> linarith [h.1]
      · rcases ht with h | h <;> linarith [h.2]
    obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc (hfcont.mono hsub) hymem
    obtain ⟨n, hn, -⟩ := hfint t (hsub ht).1 (hsub ht).2
    rw [hn, hy] at hft

    have h2 : (2 * n : ℤ) = 2 * min n₁ n₂ + 1 := by
      have : (2 : ℝ) * n = 2 * (min n₁ n₂ : ℤ) + 1 := by rw [hft]; ring
      exact_mod_cast this
    omega

  set s₀ : ℝ := a + δ / 2 with hs₀
  have hs₀a : a < s₀ := by rw [hs₀]; linarith
  have hs₀δ : s₀ < a + δ := by rw [hs₀]; linarith
  refine ⟨3 / 4 + ‖Complex.log c‖ + ‖d s₀‖, δ, hδ, fun s hs hsδ => ?_⟩
  have hds : d s = d s₀ := by
    obtain ⟨n, hn, hdn⟩ := hfint s hs hsδ
    obtain ⟨n₀, hn₀, hdn₀⟩ := hfint s₀ hs₀a hs₀δ
    have := hfconst s s₀ hs hsδ hs₀a hs₀δ
    rw [hn, hn₀] at this
    have hnn : n = n₀ := by exact_mod_cast this
    rw [hdn, hdn₀, hnn]
  have hΛeq : Λ s = Λ' s + d s := by rw [hd]; simp
  rw [hΛeq, hds]
  calc ‖Λ' s + d s₀‖ ≤ ‖Λ' s‖ + ‖d s₀‖ := norm_add_le _ _
    _ ≤ 3 / 4 + ‖Complex.log c‖ + ‖d s₀‖ := by linarith [hbound' s hs hsδ]


theorem Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto
    {Λ ℓ : ℝ → ℂ} {a : ℝ} {c : ℂ} (hΛ : ContinuousOn Λ (Set.Ioi a))
    (hexp : ∀ s : ℝ, a < s → Complex.exp (Λ s) = ℓ s)
    (hlim : Filter.Tendsto ℓ (nhdsWithin a (Set.Ioi a)) (nhds c)) (hc : c ≠ 0) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ s : ℝ, a < s → s < a + δ → ‖Λ s‖ ≤ C :=
  main_logBranch hΛ hexp hlim hc

open Polynomial

local notation "ℤ̄" => (integralClosure ℤ ℂ)

private theorem main_primRoot (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ φ : ℤ̄ →+* K, ∀ z : ℤ̄, (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M) → φ z = ζ := by
  classical
  have hMK : NeZero (M : K) := ⟨by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hℓM h⟩

  set μ : ℂ := Complex.exp (2 * Real.pi * Complex.I / M) with hμdef
  have hμ : IsPrimitiveRoot μ M := Complex.isPrimitiveRoot_exp M (NeZero.ne M)
  have hμint : IsIntegral ℤ μ := hμ.isIntegral (NeZero.pos M)
  set z : ℤ̄ := ⟨μ, hμint⟩ with hzdef
  have hval : Function.Injective (algebraMap ℤ̄ ℂ) := Subtype.val_injective
  have hz : IsIntegral ℤ z := (isIntegral_algHom_iff (integralClosure ℤ ℂ).val hval).mp hμint
  have hmin : minpoly ℤ z = cyclotomic M ℤ := by
    rw [← minpoly.algebraMap_eq hval z]
    exact (cyclotomic_eq_minpoly hμ (NeZero.pos M)).symm

  have hζroot : Polynomial.eval₂ (Int.castRingHom K) ζ (minpoly ℤ z) = 0 := by
    rw [hmin, eval₂_eq_eval_map, map_cyclotomic_int, ← IsRoot.def, isRoot_cyclotomic_iff]
    exact hζ
  set A₀ : Subalgebra ℤ ℤ̄ := Algebra.adjoin ℤ ({z} : Set ℤ̄) with hA₀
  set φ₁ : A₀ →+* K :=
    (AdjoinRoot.lift (Int.castRingHom K) ζ hζroot).comp
      (minpoly.equivAdjoin hz).symm.toRingEquiv.toRingHom with hφ₁
  have hzA₀ : z ∈ A₀ := Algebra.self_mem_adjoin_singleton ℤ z
  have hφ₁z : φ₁ ⟨z, hzA₀⟩ = ζ := by
    have e : (minpoly.equivAdjoin hz).symm ⟨z, hzA₀⟩ = AdjoinRoot.root (minpoly ℤ z) := by
      rw [AlgEquiv.symm_apply_eq]
      apply Subtype.ext
      rw [minpoly.coe_equivAdjoin]
      exact (AdjoinRoot.Minpoly.coe_toAdjoin_mk_X).symm
    rw [hφ₁, RingHom.comp_apply]
    change AdjoinRoot.lift (Int.castRingHom K) ζ hζroot ((minpoly.equivAdjoin hz).symm ⟨z, hzA₀⟩) = ζ
    rw [e, AdjoinRoot.lift_root]

  set 𝔭 : Ideal A₀ := RingHom.ker φ₁ with h𝔭
  have : 𝔭.IsPrime := RingHom.ker_isPrime φ₁
  have : Algebra.IsIntegral A₀ ℤ̄ := Algebra.IsIntegral.tower_top (R := ℤ)
  have hinjA : Function.Injective (algebraMap A₀ ℤ̄) := Subtype.val_injective
  obtain ⟨𝔔, -, h𝔔, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 (⊥ : Ideal ℤ̄) (by
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_bot] at ha
    have : a = 0 := hinjA (by rw [ha, map_zero])
    rw [this]; exact zero_mem _)
  have := h𝔔

  set I : Ideal A₀ := 𝔔.comap (algebraMap A₀ ℤ̄) with hI
  have hIprime : I.IsPrime := by
    rw [hI]
    exact h𝔔.comap (algebraMap A₀ ℤ̄)
  have hker : ∀ a : A₀, a ∈ I → φ₁ a = 0 := by
    intro a ha
    rw [hI] at ha
    rw [← Ideal.under_def] at ha
    rw [hcomap] at ha
    exact ha
  set ι : (A₀ ⧸ I) →+* K := Ideal.Quotient.lift I φ₁ hker with hι
  have hker_le : RingHom.ker φ₁ ≤ I := by
    rw [← h𝔭, hI, ← Ideal.under_def, ← hcomap]
  have hιinj : Function.Injective ι := by
    rw [hι]
    exact RingHom.lift_injective_of_ker_le_ideal I (f := φ₁) hker hker_le
  let algK : Algebra (A₀ ⧸ I) K := ι.toAlgebra
  let algQ : Algebra (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔) := Ideal.quotientAlgebra
  let smulK : SMul (A₀ ⧸ I) K := algK.toSMul
  let smulQ : SMul (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔) := algQ.toSMul
  let modK : Module (A₀ ⧸ I) K := algK.toModule
  let modQ : Module (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔) := algQ.toModule
  have : IsDomain (ℤ̄ ⧸ 𝔔) := Ideal.Quotient.isDomain 𝔔
  have hntA₀ : Nontrivial (A₀ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIprime.ne_top
  have domA₀ : IsDomain (A₀ ⧸ I) := Ideal.Quotient.isDomain _
  have fQ : FaithfulSMul (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔) :=
    (faithfulSMul_iff_algebraMap_injective (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔)).mpr Ideal.algebraMap_quotient_injective
  have fK : FaithfulSMul (A₀ ⧸ I) K := (faithfulSMul_iff_algebraMap_injective (A₀ ⧸ I) K).mpr hιinj
  have tQ : Module.IsTorsionFree (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔) :=
    FaithfulSMul.to_isTorsionFree (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔)
  have tK : Module.IsTorsionFree (A₀ ⧸ I) K := FaithfulSMul.to_isTorsionFree (A₀ ⧸ I) K
  have hint : Algebra.IsIntegral (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔) := Algebra.IsIntegral.quotient
  have halg : Algebra.IsAlgebraic (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔) := Algebra.IsIntegral.isAlgebraic

  set Λ : (ℤ̄ ⧸ 𝔔) →ₐ[(A₀ ⧸ I)] K := IsAlgClosed.lift (M := K) (R := (A₀ ⧸ I)) (S := ℤ̄ ⧸ 𝔔) with hΛ
  refine ⟨Λ.toRingHom.comp (Ideal.Quotient.mk 𝔔), fun w hw => ?_⟩
  have hwz : w = z := Subtype.ext hw
  rw [hwz, RingHom.comp_apply]
  have e1 : Ideal.Quotient.mk 𝔔 z = @algebraMap (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔) _ _ algQ (Ideal.Quotient.mk _ ⟨z, hzA₀⟩) := by
    rw [show @algebraMap (A₀ ⧸ I) (ℤ̄ ⧸ 𝔔) _ _ algQ = Ideal.quotientMap 𝔔 (algebraMap A₀ ℤ̄) le_rfl from rfl,
      Ideal.quotientMap_mk]
    rfl
  rw [e1, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  change ι (Ideal.Quotient.mk _ ⟨z, hzA₀⟩) = ζ
  rw [hι, Ideal.Quotient.lift_mk, hφ₁z]


theorem Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot
    (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ φ : integralClosure ℤ ℂ →+* K,
      ∀ z : integralClosure ℤ ℂ,
        (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M) → φ z = ζ :=
  main_primRoot ℓ M hℓM K ζ hζ
