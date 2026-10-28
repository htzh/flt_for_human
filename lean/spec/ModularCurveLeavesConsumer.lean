/-
  Consumer specification for **SET-LEAVES** (the `ModularCurve` leaves block's rows).

  Written-down *uses* of the set's headlines, composed across modules.  Not part of any
  library; run by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveLeavesConsumer.lean 2>&1 | grep -c error

  ZONES
  -----
    [starbank] ZONE A — the star datum closed: `StarBank.press` (the ported M10 module) supplies
               `closure`'s `hpress` slot and `StarBank.deltaNorm` (this set's LV-2 module) its
               `hnorm` slot, so the two rows plus the legacy `press` produce the closure
               statement with both hypotheses discharged.

    [bernoulli] ZONE B — the weight span's two faces: the dilate family is `even` by the span
               characterisation (row 504's forward direction), and the totient-weighted sum of
               its `s`-dilate vanishes (row 323) — the two rows read off one membership.
    [siegel]   ZONE C — the level shift's multiplier is a unit: `siegelFun`'s vanishing at
               `(r, s + N)` is exactly its vanishing at `(r, s)` (row 155 composed with
               mathlib's `Complex.exp_ne_zero`).
    [hasse]    ZONE D — the star datum's root count: `press` + `deltaNorm` + `closure` (LV-2)
               discharge `count`'s divisibility hypothesis (LV-3), so the four rows of the two
               StarBank modules plus the ported `press` produce the one-point root theorem.
    [coset]    ZONE E — uniqueness plus separability: the primitive-coset polynomial is the only
               monic polynomial of degree `card (primCosetReps N)` with the prescribed roots, and
               every such polynomial is separable (the two LV-4 coset rows in one rewrite).
    [eta]      ZONE F — the `jq` coefficients by the index shift: `jNum`'s coefficients 0-6 (LV-4's
               237 row) read through `jq = q⁻¹ · jNum`, tying the new row to the module's two
               pre-existing coefficient rows.
    [coeffmap] ZONE G — the uniqueness content of 468 read at the identity: an algEquiv of the
               q-expansion function field whose coefficient action is `coeffMap φ` of the
               preimage's *identity* is the identity itself.
    [pic0]     ZONE H — the Pic0 identification is additive, so its Hecke commutation extends to
               the difference `T_ell x - x` (the headline's first conjunct plus `map_sub`).
    [period]   ZONE I — the `J`-conjugation law plus the antiderivative form of `periodAlongOf`
               identify the integral of the conjugate form with the `J`-transported path.
    [qexpdiff] ZONE J — the q-expansion differential is unique: two maps with the defining
               property agree, read off the row twice.
    [cusp]     ZONE K — a q-expansion's limit at the cusp plus the coefficient uniqueness: two
               expansions of one function force one coefficient sequence and one limit.
-/

import FLTForHuman.ModularCurve.StarBank.Norm
import FLTForHuman.ModularCurve.ModularPolynomialStarBank
import FLTForHuman.ModularCurve.SiegelUnit.BernoulliWeight
import FLTForHuman.ModularCurve.SiegelUnit.Basic
import FLTForHuman.ModularCurve.StarBank.Hasse
import FLTForHuman.ModularCurve.ModularPolynomialCoset
import FLTForHuman.ModularCurve.JqCoefficients
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.X1.Pic0Correspondence
import FLTForHuman.ModularCurve.Period.QExpansionDiff
import FLTForHuman.ModularCurve.Analytic.QParamUnique
import FLTForHuman.ModularForms.EichlerShimura.PeriodOf

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries Finset
open scoped MatrixGroups UpperHalfPlane

namespace ModularCurveLeavesConsumer

/-! ## Zone A — `[starbank]` the star datum closed -/

/-- The closure headline with `hpress` taken from `StarBank.press` and `hnorm` from
`StarBank.deltaNorm`: a real three-module composition (`Defs/JqCoeff`'s `jqModC`/`jqNModC`, the
legacy `ModularPolynomialStarBank`'s `press`, and this set's `StarBank/Norm`). -/
theorem star_closure_of_press_and_deltaNorm (K : Type*) [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    {M : ℕ} {G R : Polynomial K}
    (hstar : Polynomial.aeval (ModularCurve.jqModC K) G *
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K)
            ModularCurve.etaProd) ^ 24) ^ M = 1)
    (hR : Polynomial.aeval (ModularCurve.jqModC K) R = ModularCurve.jqNModC K p) :
    ∃ c : K, c ≠ 0 ∧ G.comp R ∣ Polynomial.C c * G ^ (p + 1) :=
  ModularCurve.StarBank.closure p ζ hstar hR
    (ModularCurve.StarBank.press p ζ hζ hR).2.2
    (ModularCurve.StarBank.deltaNorm p ζ hζ)

/-- The same composition with the closure's conclusion unpacked at `G = 1`: the divisor is
`R` itself, which is the form the star-polynomial arguments consume. -/
theorem star_R_dvd_of_deltaNorm (K : Type*) [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    {M : ℕ} {R : Polynomial K}
    (hstar : Polynomial.aeval (ModularCurve.jqModC K) (1 : Polynomial K) *
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K)
            ModularCurve.etaProd) ^ 24) ^ M = 1)
    (hR : Polynomial.aeval (ModularCurve.jqModC K) R = ModularCurve.jqNModC K p) :
    ∃ c : K, c ≠ 0 ∧ (1 : Polynomial K).comp R ∣ Polynomial.C c * (1 : Polynomial K) ^ (p + 1) :=
  star_closure_of_press_and_deltaNorm K p ζ hζ hstar hR

/-! ## Zone B — `[bernoulli]` the weight span's two faces -/

/-- Row 504's forward direction applied to the `s`-dilate itself, composed with row 323's
totient-weighted vanishing: the two rows are two readings of one span membership. -/
theorem wt_dilate_even_and_totient_sum_zero (N : ℕ) [NeZero N] (s : ZMod N) (hs : s ≠ 0) :
    (∀ r : ZMod N,
        ((ModularCurve.SiegelUnit.Ws47.BSpan.wt N (((-s) * r).val) : ℤ) : ℚ) =
          ((ModularCurve.SiegelUnit.Ws47.BSpan.wt N ((s * r).val) : ℤ) : ℚ)) ∧
      ∑ r : ZMod N,
          (((N / Nat.gcd r.val N) * Nat.totient (Nat.gcd r.val N) : ℕ) : ℤ) *
            ModularCurve.SiegelUnit.Ws47.BSpan.wt N ((s * r).val) = 0 := by
  have hmem : (fun r : ZMod N =>
      ((ModularCurve.SiegelUnit.Ws47.BSpan.wt N ((s * r).val) : ℤ) : ℚ)) ∈
      Submodule.span ℚ (Set.range fun t : ZMod N => fun r : ZMod N =>
        ((ModularCurve.SiegelUnit.Ws47.BSpan.wt N ((t * r).val) : ℤ) : ℚ)) :=
    Submodule.subset_span ⟨s, rfl⟩
  have heven := (ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even N _).mp hmem
  refine ⟨fun r => ?_, ?_⟩
  · have := heven r
    simpa [neg_mul, mul_neg] using this
  · simpa only [ModularCurve.SiegelUnit.Ws47.BSpan.wt]
      using ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero N s hs

/-! ## Zone C — `[siegel]` the level shift's multiplier is a unit -/

/-- Row 155's two vanishing statements: the `(r, s + N)` level shift multiplies `siegelFun` by
the nonzero unit `exp (π i (r - N) / N)`, so it preserves vanishing at every complex point. -/
theorem siegelFun_add_level_eq_zero_iff (N : ℕ) (r s : ℤ) (z : ℂ) :
    ModularCurve.siegelFun N r (s + N) z = 0 ↔ ModularCurve.siegelFun N r s z = 0 := by
  have hadd := (ModularCurve.SiegelUnit.siegelFun_add_level N r s).1 z
  rw [hadd]
  simp [Complex.exp_ne_zero]

/-! ## Zone D — `[hasse]` the star datum's root count -/

/-- `count` fed by `closure`, itself fed by `press` and `deltaNorm`: the divisibility
hypothesis of the root count is not assumed but produced by the LV-2 rows, and the monicity and
degree by the ported `press`. -/
theorem star_root_count_of_star_datum (K : Type*) [Field K] [IsAlgClosed K]
    (p : ℕ) [Fact p.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (hp0 : (p : K) ≠ 0) (hp2 : 2 ≤ p)
    {M : ℕ} {G R : Polynomial K} (hG : 0 < G.natDegree)
    (hstar : Polynomial.aeval (ModularCurve.jqModC K) G *
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K)
            ModularCurve.etaProd) ^ 24) ^ M = 1)
    (hR : Polynomial.aeval (ModularCurve.jqModC K) R = ModularCurve.jqNModC K p) :
    ∃ β₀ : K, (∀ β : K, G.IsRoot β → β = β₀) ∧
      R = (Polynomial.X - Polynomial.C β₀) ^ p + Polynomial.C β₀ := by
  have hpress := (ModularCurve.StarBank.press p ζ hζ hR)
  obtain ⟨c, hc, hdvd⟩ :=
    ModularCurve.StarBank.closure p ζ hstar hR hpress.2.2
      (ModularCurve.StarBank.deltaNorm p ζ hζ)
  exact ModularCurve.StarBank.count hp0 hp2 hpress.1 hpress.2.1 hG hc hdvd

/-! ## Zone E — `[coset]` uniqueness plus separability -/

/-- The two coset rows in one rewrite: anything monic of the primitive coset degree with the
prescribed roots is `cosetTwoVarPoly`, hence separable. -/
theorem separable_of_forall_isRoot_cosetConj (K : Type*) [Field K] (N : ℕ) (hN : N ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (J : LaurentSeries K)
    (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0)
    (P : Polynomial (LaurentSeries K)) (hP : P.Monic)
    (hdeg : P.natDegree = (ModularCurve.primCosetReps N).card)
    (hroot : ∀ t ∈ ModularCurve.primCosetReps N, P.IsRoot (ModularCurve.cosetConj ζ J t)) :
    P.Separable := by
  rw [ModularCurve.eq_cosetTwoVarPoly_of_forall_isRoot K N hN ζ hζ J hJ hJ' P hP hdeg hroot]
  exact ModularCurve.separable_cosetTwoVarPoly K N hN ζ hζ J hJ hJ'

/-! ## Zone F — `[eta]` the `jq` coefficients by the index shift -/

/-- `jq = q⁻¹ · jNum`, so `jq`'s low coefficients are `jNum`'s at one higher index. The first two
are the module's own (already-port) rows; the third is this set's `coeff_jNum_le_six`. -/
theorem jq_coeff_zero_one_five :
    ModularCurve.jq.coeff 0 = 744 ∧ ModularCurve.jq.coeff 1 = 196884 ∧
      ModularCurve.jq.coeff 5 = 333202640600 := by
  refine ⟨ModularCurve.coeff_jq_zero, ModularCurve.coeff_jq_one, ?_⟩
  have h6 := (ModularCurve.coeff_jNum_le_six).2.2.2.2.2.2
  rw [ModularCurve.jq, HahnSeries.coeff_single_mul, one_mul]
  rw [show (5 : ℤ) - -1 = ((6 : ℕ) : ℤ) by norm_num]
  rw [HahnSeries.ofPowerSeries_apply_coeff, ModularCurve.jNumQ, PowerSeries.coeff_map]
  change ((PowerSeries.coeff 6 ModularCurve.jNum : ℤ) : ℚ) = ((333202640600 : ℤ) : ℚ)
  exact_mod_cast h6

/-! ## Zone G — `[coeffmap]` the uniqueness content at the identity -/

/-- The `∃!` of row 468 at `σ₀ = AlgEquiv.refl`: an automorphism that acts on coefficients as
`coeffMap φ` of the identity action is itself the identity. Uses the uniqueness half of the row,
not just its existence half. -/
theorem algEquiv_eq_one_of_coeffMap_action (K₀ K : Type*) [Field K₀] [Field K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (σ : ModularCurve.qExpFunctionFieldC K Γ ≃ₐ[K] ModularCurve.qExpFunctionFieldC K Γ)
    (hσ : ∀ (x₀ : ModularCurve.qExpFunctionFieldC K₀ Γ)
        (x : ModularCurve.qExpFunctionFieldC K Γ),
        (x : LaurentSeries K) = ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀) →
        ((σ x : ModularCurve.qExpFunctionFieldC K Γ) : LaurentSeries K) =
          ModularCurve.coeffMap φ (x₀ : LaurentSeries K₀)) :
    σ = 1 := by
  obtain ⟨σ₀, _hσ₀, huniq⟩ :=
    ModularCurve.existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap (K₀ := K₀) (K := K)
      φ Γ (1 : ModularCurve.qExpFunctionFieldC K₀ Γ ≃ₐ[K₀] ModularCurve.qExpFunctionFieldC K₀ Γ)
  have h1 : (1 : ModularCurve.qExpFunctionFieldC K Γ ≃ₐ[K]
      ModularCurve.qExpFunctionFieldC K Γ) = σ₀ :=
    huniq 1 (fun x₀ x hx => by simpa using hx)
  exact (huniq σ (fun x₀ x hx => by simpa using hσ x₀ x hx)).trans h1.symm

/-! ## Zone H — `[pic0]` the Pic0 identification is additive -/

/-- The headline's Hecke conjunct, extended by `map_sub`: `e (T_ell x - x) = T_ell (e x) - e x`.
A downstream consumer uses the `≃+` structure, not just the equation. -/
theorem pic0Congr_heckeOperator_sub (M : ℕ) [NeZero M]
    (hin : ModularCurve.HeckeDiamondInputsAll M)
    (hinH : ModularCurve.HeckeDiamondInputsHAll M ⊥)
    (h : ModularCurve.x1FunctionFieldBar M = ModularCurve.xHFunctionFieldBar M ⊥)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (x : ModularCurve.JOne M) :
    let e : ModularCurve.JOne M ≃+ ModularCurve.JH M ⊥ :=
      AlgebraicCurve.Pic0.congr (IntermediateField.equivOfEq h).toRingEquiv
        (IntermediateField.equivOfEq h).commutes
    e (ModularCurve.heckeOperatorOneBar M ⟨ℓ, hℓ⟩ x - x) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M ⊥ ℓ) (e x) - e x := by
  intro e
  have hb := (ModularCurve.pic0Congr_jOne_jH_bot_compat M hin hinH h).1 ℓ hℓ x
  rw [map_sub, hb]

/-! ## Zone I — `[period]` the `J`-conjugation law and the antiderivative form -/

/-- Row 98 plus `periodAlongOf_eq_sub`: the difference of an antiderivative of `g` along the
segment is minus the conjugate of `f`'s period along the `J`-transported segment. -/
theorem periodAlongOf_eq_sub_of_conj (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : ℍ, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)))
    {F : ℍ → ℂ} (hF : ∀ τ : ℍ, HasDerivAt (F ∘ UpperHalfPlane.ofComplex) (g τ) ↑τ)
    (τ₀ τ₁ : ℍ) :
    F τ₁ - F τ₀ =
      -(starRingEnd ℂ)
        (ModularCurve.periodAlongOf Γ (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) f) := by
  rw [← ModularCurve.periodAlongOf_eq_sub Γ g hF τ₀ τ₁]
  exact ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul Γ f g hg τ₀ τ₁

/-! ## Zone J — `[qexpdiff]` the q-expansion differential is unique -/

/-- Row 167 read twice: two `K`-linear maps satisfying the defining property of the q-expansion
differential coincide, so the property determines the map. -/
theorem isQExpansionDiffAlong_unique {K F L : Type*} [Field K] [Field F] [Algebra K F]
    [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) {φ ψ : Ω[F⁄K] →ₗ[K] LaurentSeries L}
    (hφ : ModularCurve.IsQExpansionDiffAlong σ φ) (hψ : ModularCurve.IsQExpansionDiffAlong σ ψ) :
    φ = ψ := by
  rw [ModularCurve.eq_qExpansionDiffAlong_of_isQExpansionDiffAlong σ hφ,
    ModularCurve.eq_qExpansionDiffAlong_of_isQExpansionDiffAlong σ hψ]

/-! ## Zone K — `[cusp]` one limit, one coefficient sequence -/

/-- Row 159 plus `qParam_coeff_unique`: a function with two `q`-expansions has one coefficient
sequence and one limit at the cusp. -/
theorem tendsto_atImInfty_and_coeff_unique (h : ℝ) (hh : 0 < h) (F : UpperHalfPlane → ℂ)
    (c d : ℕ → ℂ)
    (hc : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ))
    (hd : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => d m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ)) :
    c = d ∧ Filter.Tendsto F UpperHalfPlane.atImInfty (nhds (c 0)) ∧
      Filter.Tendsto F UpperHalfPlane.atImInfty (nhds (d 0)) := by
  refine ⟨ModularCurve.qParam_coeff_unique h hh F c d hc hd, ?_, ?_⟩
  · exact ModularCurve.tendsto_atImInfty_of_hasSum_qParam h hh F c hc
  · exact ModularCurve.tendsto_atImInfty_of_hasSum_qParam h hh F d hd

end ModularCurveLeavesConsumer
