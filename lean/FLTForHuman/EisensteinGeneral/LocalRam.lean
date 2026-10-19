/-
  The local twisted integral at a ramified place: the three headlines.

  `integrable_twisted_smooth` — the integrand
  `A.indicator + (charExt χ⁻¹ · modulus^(-(2s+1)) · B(·⁻¹)).indicator` twisted by an
  additive character `ψ(-(ξ·))` is `L¹`; `integral_twisted_smooth_eq` — its integral is
  the integral of `A·ψ(-(ξ·))` over the integers plus the sum over the finitely many low
  spheres `{Valued.v x = exp k}` of `N^(-(2s+1))^k` times the sphere integrals, the
  geometric tail above the level `K = max (m-1) (n + c - e)` vanishing by the
  character-translation trick; and `integral_twisted_smooth_eq_zero_of_exp_lt` — if
  `ξ` is deeper than `n + max m c` the whole integral is `0`.

  This is the **listed** module of the set: its three statements are copied verbatim from
  the pin's `Theorems/` wrappers, which are the statement authority the checker diffs
  (`Thm_EisensteinGeneral_LocalRam_{integral_twisted_smooth_eq,integrable_twisted_smooth,
  integral_twisted_smooth_eq_zero_of_exp_lt}.lean`).  The pin declares each of the three
  as a `private theorem` inside `namespace TwistedSmoothLocal` and then re-states it in
  the wrapper at the dotted name `EisensteinGeneral.LocalRam.*`; the port keeps only that
  dotted name, so the pin's private copies are not ported twice.

  The proofs are the pin's `solution` bodies, transcribed unchanged:
  `S_EisensteinGeneral_LocalRam_integrable_twisted_smooth.lean:541-542` (B),
  `S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:653-833` (A) and
  `S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq_zero_of_exp_lt.lean:190-231`
  (C).  They work through the two engine modules:
  `EisensteinGeneral.TwistedSmoothLocal` (the prelude, `LocalTwisted.lean`) and the shell
  machinery (`LocalRamShells.lean`), which is why both are opened below.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`, mathlib `v4.34.0`.  The wrappers'
  `attribute [-instance]`/`[-simp]` preludes are not reproduced (the port's definition
  layer already carries those instances) and no `maxHeartbeats` is set.  Drift
  adaptations in the proofs: `Set.mem_setOf_eq` -> `Set.mem_ofPred_eq`, `zero_le'` ->
  `zero_le`, and the pin's local `ofReal_pow_cpow` is the port's
  `NumberField.TateGlobal.WeylShell.ofReal_pow_cpow`.
-/
import FLTForHuman.EisensteinGeneral.LocalTwisted
import FLTForHuman.EisensteinGeneral.LocalRamShells
import FLTForHuman.LanglandsTunnell.TateLocalConstantsAt
import FLTForHuman.NumberTheory.NumberField.TateGlobal.WeylShell

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField

open IsDedekindDomain.HeightOneSpectrum Filter Topology
open LanglandsTunnell.TateLocal NumberField.AdelicLevel
open NumberField.TateGlobal NumberField.TateGlobal.WeylSmooth
open NumberField.TateGlobal.LocalZetaUnramified
open EisensteinGeneral.TwistedSmoothLocal

-- pin: integrable_twisted_smooth (Thm_EisensteinGeneral_LocalRam_integrable_twisted_smooth.lean:10)
theorem EisensteinGeneral.LocalRam.integrable_twisted_smooth
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (ξ : v.adicCompletion F) :
    Integrable (fun x => (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x)))) μ := by
  have _ := hc
  exact integrable_twisted_aux μ ϖ hϖ χ c hχ m hm A hA B hB s hs ψ n hψn ξ

-- pin: integral_twisted_smooth_eq (Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean:10)
theorem EisensteinGeneral.LocalRam.integral_twisted_smooth_eq
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (e : ℤ) (hξ : Valued.v ξ = WithZero.exp e) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x))) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x * ψ (-(ξ * x)) ∂μ)
        + ∑ k ∈ Finset.Icc 1 (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k
              * ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψ (-(ξ * x)) ∂μ := by
  set K : ℕ := (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat with hK
  have hKm : (m : ℤ) - 1 ≤ K := (le_max_left _ _).trans (Int.self_le_toNat _)
  have hKn : n + (c : ℤ) - e ≤ K := (le_max_right _ _).trans (Int.self_le_toNat _)
  change ∫ x, untwisted χ s A B x * ψ (-(ξ * x)) ∂μ = _
  set g : v.adicCompletion F → ℂ := fun x => untwisted χ s A B x * ψ (-(ξ * x)) with hg_def
  have hgi : Integrable g μ := integrable_twisted_aux μ ϖ hϖ χ c hχ m hm A hA B hB s hs ψ n hψn ξ
  have hO : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    isOpen_integers.measurableSet
  set tail : Set (v.adicCompletion F) := {x | WithZero.exp (K : ℤ) < Valued.v x} with htail_def
  have hmeasT : MeasurableSet tail := measurableSet_setOf_exp_lt (K : ℤ)
  have hmeasS : ∀ k ∈ Finset.Icc 1 K,
      MeasurableSet {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)} :=
    fun k _ => measurableSet_setOf_valued_eq (k : ℤ)

  have hsplit1 : ∫ x, g x ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), g x ∂μ)
        + ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ, g x ∂μ :=
    (integral_add_compl hO hgi).symm
  have hOterm : ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), g x ∂μ
      = ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x * ψ (-(ξ * x)) ∂μ := by
    refine setIntegral_congr_fun hO fun x hx => ?_
    simp only [hg_def, untwisted, Set.indicator_of_mem hx,
      Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hx), add_zero]

  have hcover : (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ
      = (⋃ k ∈ Finset.Icc 1 K, {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}) ∪ tail := by
    ext x
    simp only [Set.mem_compl_iff, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, not_le, Set.mem_union,
      Set.mem_iUnion, Finset.mem_Icc, exists_prop, htail_def, Set.mem_ofPred_eq]
    constructor
    · intro h1
      have hx0 : Valued.v x ≠ 0 := (lt_trans zero_lt_one h1).ne'
      obtain ⟨j, hj⟩ : ∃ j : ℤ, Valued.v x = WithZero.exp j := ⟨_, (WithZero.exp_log hx0).symm⟩
      have hj0 : 0 < j := by
        rw [hj, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
        exact h1
      by_cases hjK : j ≤ K
      · left
        refine ⟨j.toNat, ⟨by omega, by omega⟩, ?_⟩
        rw [hj]
        congr 1
        omega
      · right
        rw [hj, WithZero.exp_lt_exp]
        omega
    · rintro (⟨k, ⟨hk1, -⟩, hxk⟩ | hxt)
      · rw [hxk, ← WithZero.exp_zero, WithZero.exp_lt_exp]
        omega
      · refine lt_of_le_of_lt ?_ hxt
        rw [← WithZero.exp_zero, WithZero.exp_le_exp]
        omega
  have hpair : Set.Pairwise (↑(Finset.Icc 1 K) : Set ℕ)
      (Function.onFun Disjoint
        fun k : ℕ => {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}) := by
    intro i _ j _ hij
    show Disjoint {x : v.adicCompletion F | Valued.v x = WithZero.exp (i : ℤ)}
      {x : v.adicCompletion F | Valued.v x = WithZero.exp (j : ℤ)}
    rw [Set.disjoint_left]
    intro x hxi hxj
    change Valued.v x = WithZero.exp (i : ℤ) at hxi
    change Valued.v x = WithZero.exp (j : ℤ) at hxj
    apply hij
    have h := WithZero.exp_inj.mp (hxi.symm.trans hxj)
    exact_mod_cast h
  have hdisjUT : Disjoint
      (⋃ k ∈ Finset.Icc 1 K, {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}) tail := by
    rw [Set.disjoint_left]
    intro x hx hxt
    simp only [Set.mem_iUnion, exists_prop, Finset.mem_Icc] at hx
    obtain ⟨k, ⟨-, hkK⟩, hxk⟩ := hx
    change Valued.v x = WithZero.exp (k : ℤ) at hxk
    change WithZero.exp (K : ℤ) < Valued.v x at hxt
    rw [hxk, WithZero.exp_lt_exp] at hxt
    omega
  have hsplit2 : ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ, g x ∂μ
      = (∑ k ∈ Finset.Icc 1 K,
          ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}, g x ∂μ)
        + ∫ x in tail, g x ∂μ := by
    rw [hcover, setIntegral_union hdisjUT hmeasT hgi.integrableOn hgi.integrableOn,
      integral_biUnion_finset _ hmeasS hpair fun k _ => hgi.integrableOn]

  have htail0 : ∫ x in tail, g x ∂μ = 0 := by
    obtain ⟨x₀, hx₀v, hx₀⟩ := hψn'
    have hvξ : Valued.v ξ ≠ 0 := by
      rw [hξ]
      exact WithZero.coe_ne_zero
    have hξ0 : ξ ≠ 0 := (Valuation.ne_zero_iff _).mp hvξ
    set t : v.adicCompletion F := -(ξ⁻¹ * x₀) with ht_def
    have hvt : Valued.v t ≤ WithZero.exp (n + 1 - e) := by
      rw [ht_def, Valuation.map_neg, map_mul, map_inv₀, hξ, ← WithZero.exp_neg]
      calc WithZero.exp (-e) * Valued.v x₀
          ≤ WithZero.exp (-e) * WithZero.exp (n + 1) := by gcongr
        _ = WithZero.exp (n + 1 - e) := by
          rw [← WithZero.exp_add]
          congr 1
          ring
    have hψt : ∀ x : v.adicCompletion F, ψ (-(ξ * (t + x))) = ψ (-(ξ * x)) * ψ x₀ := by
      intro x
      have h : -(ξ * (t + x)) = -(ξ * x) + x₀ := by
        rw [ht_def]
        field_simp
        ring
      rw [h, AddChar.map_add_eq_mul]
    have hinv : ∀ x : v.adicCompletion F, tail.indicator g (t + x) = tail.indicator g x * ψ x₀ := by
      intro x
      by_cases hx : x ∈ tail
      · have hx' : WithZero.exp (K : ℤ) < Valued.v x := hx
        have hx0 : Valued.v x ≠ 0 := (lt_of_le_of_lt zero_le hx').ne'
        obtain ⟨j, hj⟩ : ∃ j : ℤ, Valued.v x = WithZero.exp j := ⟨_, (WithZero.exp_log hx0).symm⟩
        have hjK : (K : ℤ) < j := by
          rw [hj, WithZero.exp_lt_exp] at hx'
          exact hx'
        have htj : Valued.v t ≤ WithZero.exp (j - c) :=
          hvt.trans (WithZero.exp_le_exp.mpr (by omega))
        have htlt : Valued.v t < Valued.v x := by
          rw [hj]
          exact lt_of_le_of_lt htj (WithZero.exp_lt_exp.mpr (by omega))
        have hvtx : Valued.v (t + x) = Valued.v x := Valued.v.map_add_eq_of_lt_right htlt
        have htx : t + x ∈ tail := by
          show WithZero.exp (K : ℤ) < Valued.v (t + x)
          rw [hvtx]
          exact hx'
        rw [Set.indicator_of_mem htx, Set.indicator_of_mem hx, hg_def]
        simp only
        rw [untwisted_add_eq_of_sphere χ c hc hχ m hm s A B hB (by omega) hj htj, hψt x, mul_assoc]
      · have htx : t + x ∉ tail := by
          intro htx
          apply hx
          have htx' : WithZero.exp (K : ℤ) < Valued.v (t + x) := htx
          have h0 : Valued.v (t + x) ≠ 0 := (lt_of_le_of_lt zero_le htx').ne'
          obtain ⟨j, hj⟩ : ∃ j : ℤ, Valued.v (t + x) = WithZero.exp j := ⟨_, (WithZero.exp_log h0).symm⟩
          have hjK : (K : ℤ) < j := by
            rw [hj, WithZero.exp_lt_exp] at htx'
            exact htx'
          have htlt : Valued.v (-t) < Valued.v (t + x) := by
            rw [Valuation.map_neg, hj]
            exact lt_of_le_of_lt hvt (WithZero.exp_lt_exp.mpr (by omega))
          have hxeq : Valued.v x = Valued.v (t + x) := by
            have hx' : x = (t + x) + -t := by ring
            conv_lhs => rw [hx']
            exact Valued.v.map_add_eq_of_lt_left htlt
          show WithZero.exp (K : ℤ) < Valued.v x
          rw [hxeq]
          exact htx'
        rw [Set.indicator_of_notMem htx, Set.indicator_of_notMem hx, zero_mul]
    rw [← integral_indicator hmeasT]
    have h2 : ∫ x, tail.indicator g x ∂μ = (∫ x, tail.indicator g x ∂μ) * ψ x₀ := by
      calc ∫ x, tail.indicator g x ∂μ
          = ∫ x, tail.indicator g (t + x) ∂μ := (integral_add_left_eq_self (tail.indicator g) t).symm
        _ = ∫ x, tail.indicator g x * ψ x₀ ∂μ := by
            congr 1
            funext x
            exact hinv x
        _ = (∫ x, tail.indicator g x ∂μ) * ψ x₀ := by rw [integral_mul_const]
    have h3 : (∫ x, tail.indicator g x ∂μ) * (ψ x₀ - 1) = 0 := by
      rw [mul_sub, mul_one, ← h2, sub_self]
    exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr hx₀)

  have hsphere : ∀ k ∈ Finset.Icc 1 K,
      ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}, g x ∂μ
        = (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k
            * ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
                LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψ (-(ξ * x)) ∂μ := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_setOf_valued_eq (k : ℤ)) fun x hx => ?_
    change Valued.v x = WithZero.exp (k : ℤ) at hx
    have hxO : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      show x ∉ v.adicCompletionIntegers F
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, hx, ← WithZero.exp_zero, not_le, WithZero.exp_lt_exp]
      omega
    simp only [hg_def, untwisted, Set.indicator_of_notMem hxO, Set.indicator_of_mem (Set.mem_compl hxO),
      zero_add]
    rw [coe_modulus_of_valued_eq hx, zpow_natCast, NumberField.TateGlobal.WeylShell.ofReal_pow_cpow (Nat.cast_nonneg _)]
    push_cast
    ring

  rw [hsplit1, hsplit2, htail0, add_zero, hOterm]
  congr 1
  exact Finset.sum_congr rfl hsphere

-- pin: integral_twisted_smooth_eq_zero_of_exp_lt (Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq_zero_of_exp_lt.lean:10)
theorem EisensteinGeneral.LocalRam.integral_twisted_smooth_eq_zero_of_exp_lt
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (hA' : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (hξ : WithZero.exp (n + (max m c : ℕ)) < Valued.v ξ) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x))) ∂μ = 0 := by
  have _ := hϖ; have _ := hc; have _ := hm; have _ := hA; have _ := hs; have _ := hψn
  obtain ⟨x₀, hx₀v, hx₀⟩ := hψn'
  have hvξpos : 0 < Valued.v ξ := lt_of_le_of_lt zero_le hξ
  have hvξ : Valued.v ξ ≠ 0 := hvξpos.ne'
  have hξ0 : ξ ≠ 0 := (Valuation.ne_zero_iff _).mp hvξ
  set t : v.adicCompletion F := -(ξ⁻¹ * x₀) with ht_def
  have hvt : Valued.v t ≤ WithZero.exp (-((max m c : ℕ) : ℤ)) := by
    obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v ξ = WithZero.exp k := by
      obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hvξ
      exact ⟨Multiplicative.toAdd a, by rw [← ha]; rfl⟩
    have hk' : (n + ((max m c : ℕ) : ℤ)) < k := by
      rw [hk] at hξ
      exact WithZero.exp_lt_exp.mp hξ
    rw [ht_def, Valuation.map_neg, map_mul, map_inv₀, hk, ← WithZero.exp_neg]
    calc WithZero.exp (-k) * Valued.v x₀
        ≤ WithZero.exp (-k) * WithZero.exp (n + 1) := by gcongr
      _ = WithZero.exp (-k + (n + 1)) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-((max m c : ℕ) : ℤ)) := WithZero.exp_le_exp.mpr (by omega)
  have hinv : ∀ x, untwisted χ s A B (t + x) = untwisted χ s A B x :=
    untwisted_add_eq χ c hχ m s A B hA' hB hvt
  have hψt : ∀ x : v.adicCompletion F, ψ (-(ξ * (t + x))) = ψ (-(ξ * x)) * ψ x₀ := by
    intro x
    have h : -(ξ * (t + x)) = -(ξ * x) + x₀ := by
      rw [ht_def]
      field_simp
      ring
    rw [h, AddChar.map_add_eq_mul]
  change ∫ x, untwisted χ s A B x * ψ (-(ξ * x)) ∂μ = 0
  have hI : ∫ x, untwisted χ s A B x * ψ (-(ξ * x)) ∂μ
      = (∫ x, untwisted χ s A B x * ψ (-(ξ * x)) ∂μ) * ψ x₀ := by
    calc ∫ x, untwisted χ s A B x * ψ (-(ξ * x)) ∂μ
        = ∫ x, untwisted χ s A B (t + x) * ψ (-(ξ * (t + x))) ∂μ :=
          (integral_add_left_eq_self (fun y => untwisted χ s A B y * ψ (-(ξ * y))) t).symm
      _ = ∫ x, untwisted χ s A B x * ψ (-(ξ * x)) * ψ x₀ ∂μ := by
          congr 1
          funext x
          rw [hinv x, hψt x, mul_assoc]
      _ = (∫ x, untwisted χ s A B x * ψ (-(ξ * x)) ∂μ) * ψ x₀ := by
          rw [integral_mul_const]
  have h2 : (∫ x, untwisted χ s A B x * ψ (-(ξ * x)) ∂μ) * (ψ x₀ - 1) = 0 := by
    rw [mul_sub, mul_one, ← hI, sub_self]
  exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hx₀)
