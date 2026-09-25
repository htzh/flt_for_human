/-
  Cross-module wire test for the route-C′ weight-one layers (SET-5 – SET-11).

  This is a `spec/` probe, not a library module. It `#check`s the headlines of
  SET-5 orders 1–2 (seven in `WeightOne/Basic.lean`, two in
  `WeightOne/EisensteinSeries.lean`), SET-6 orders 1–2 (four in
  `WeightOne/LevelOneHauptmodul.lean`, one in `WeightOne/EisensteinChiNegThree.lean`)
  and SET-7's three packages (two in the extended `LevelOneHauptmodul.lean`, one
  in `WeightOne/WeierstrassPTorsion.lean`), then SET-8's four monic-relation
  leaves (`WeightOne/MonicRel.lean`) and three fricke-function packages
  (`WeightOne/FrickeFunction.lean`), then SET-9's four level-fraction headlines
  (`WeightOne/LevelFraction.lean`) and three level-`N` headlines
  (`WeightOne/LevelN.lean`), and runs one executed application per order as noted
  in each `example`'s docstring.
-/
import FLTForHuman.ModularForms.WeightOne.Basic
import FLTForHuman.ModularForms.WeightOne.EisensteinSeries
import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import FLTForHuman.ModularForms.WeightOne.EisensteinChiNegThree
import FLTForHuman.ModularForms.WeightOne.WeierstrassPTorsion
import FLTForHuman.ModularForms.WeightOne.MonicRel
import FLTForHuman.ModularForms.WeightOne.FrickeFunction
import FLTForHuman.ModularForms.WeightOne.LevelFraction
import FLTForHuman.ModularForms.WeightOne.LevelN
import FLTForHuman.ModularForms.WeightOne.Gamma0Rationality
import FLTForHuman.ModularForms.WeightOne.Gamma0Integral
import FLTForHuman.ModularForms.WeightOne.Gamma1Basis
import FLTForHuman.ModularForms.WeightOne.Gamma1IntegralBasis
import FLTForHuman.ModularForms.WeightOne.IntegralStructure

open scoped ModularForm CongruenceSubgroup MatrixGroups Manifold UpperHalfPlane
open Complex

-- Order 1, `ModularForms/WeightOne/Basic.lean`.
#check PowerSeries.mem_range_map_of_monic_of_mul_mem_range
#check IsIntegral.mem_span_of_adjoin_simple_constants
#check IsIntegral.mem_span_of_adjoin_simple_constants_transcendental
#check IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range
#check UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem
#check ModularForm.finiteDimensional_of_isArithmetic
#check CuspForm.finiteDimensional_of_isArithmetic

-- Order 2, `ModularForms/WeightOne/EisensteinSeries.lean`.
#check EisensteinSeries.exists_modularForm_coe_eq_eisensteinG
#check EisensteinSeries.qExpansion_eisensteinG_coeff

-- SET-6 order 1, `ModularForms/WeightOne/LevelOneHauptmodul.lean`.
#check ModularCurve.surjective_specialLinearGroup_map_zmod
#check ModularCurve.qExpansion_discriminant_eq_X_mul_tprod
#check WLight.isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le
#check WLight.linearIndependent_complex_of_qExpansion_rational

-- SET-6 order 2, `ModularForms/WeightOne/EisensteinChiNegThree.lean`.
#check EisensteinWeightOne.e1Chi3IsModular

/-- **Executed cross-module application.** For an arithmetic level `N` and weight
`k ≥ 3`, the Eisenstein series `eisensteinG N k a` is the coercion of a modular
form on `Γ(N)` (order 2), and the space of modular forms on `Γ(N)` is
finite-dimensional over `ℂ` (order 1). The two headlines are used in one proof
term, so the composition is elaborated and checked, not merely `#check`ed. -/
example (N : ℕ) [NeZero N] (k : ℤ) (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    ∃ F : ModularForm (CongruenceSubgroup.Gamma N) k,
      ⇑F = EisensteinSeries.eisensteinG N k a ∧
        FiniteDimensional ℂ (ModularForm (CongruenceSubgroup.Gamma N) k) := by
  obtain ⟨F, hF⟩ := (EisensteinSeries.exists_modularForm_coe_eq_eisensteinG N k hk a).1
  exact ⟨F, hF, ModularForm.finiteDimensional_of_isArithmetic (CongruenceSubgroup.Gamma N) k⟩

/-- **SET-6 order 1, executed application.** The discriminant's `q`-expansion
identity is consumed in a proof: `q · ∏(1 - qⁿ)²⁴` has vanishing constant term,
so the identity transports that vanishing to `qExpansion 1 Δ`. The surjectivity
headline is applied at the same time, so two of order 1's four leaves are
elaborated into one term. -/
example (N : ℕ) [NeZero N] :
    (UpperHalfPlane.qExpansion 1 ModularForm.discriminant).coeff 0 = 0 ∧
      Function.Surjective
        (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  refine ⟨?_, ModularCurve.surjective_specialLinearGroup_map_zmod N⟩
  rw [ModularCurve.qExpansion_discriminant_eq_X_mul_tprod]
  simp [PowerSeries.coeff_zero_X_mul]

/-- **SET-6 order 2, executed application.** The `E1Chi3IsModular` conclusion is
consumed as a `Prop`: its existential is eliminated to produce the bundled
weight-one modular form on `Γ₁(3)` together with its defining `q`-series, so the
headline is elaborated into a term, not merely `#check`ed. -/
example : ∃ f : ModularForm (CongruenceSubgroup.Gamma1 3) 1,
    ∀ z : UpperHalfPlane, f z = ∑' n : ℕ,
      ((PowerSeries.coeff n EisensteinWeightOne.e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ)) :=
  EisensteinWeightOne.e1Chi3IsModular

-- SET-7 order 1, `ModularForms/WeightOne/LevelOneHauptmodul.lean` (extended).
#check WLight.levelOne_hauptmodul_package
#check WLight.weierstrassP_qExpansion_package

-- SET-7 order 2, `ModularForms/WeightOne/WeierstrassPTorsion.lean`.
#check ModularForm.weierstrassP_torsion_qExpansion_package

/-- **SET-7 order 1, executed application (`j`-surjectivity).** The Hauptmodul
package's surjectivity conjunct is applied at `0`: the map `E₄³/Δ` is onto, so
some `τ : UpperHalfPlane` realises the value `0`. -/
example : ∃ τ : UpperHalfPlane, ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ = 0 :=
  WLight.levelOne_hauptmodul_package.2.2.1 0

/-- **SET-7 order 1, executed application (℘ Lipschitz expansion).** The first
conjunct of `weierstrassP_qExpansion_package` is instantiated at `w = I`
(`im I = 1 > 0`), producing the closed `q`-expansion of `∑' 1/(w+n)²`. -/
example : ∑' n : ℤ, 1 / (Complex.I + (n : ℂ)) ^ 2 =
    (2 * (Real.pi : ℂ) * Complex.I) ^ 2 *
      ∑' m : ℕ, (m : ℂ) * Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * Complex.I) ^ m :=
  WLight.weierstrassP_qExpansion_package.1 Complex.I (by simp [Complex.I_im])

/-- The standard period pair `(τ, 1)`, for the order-2 application below. -/
private noncomputable def specPeriodPairOfTau (τ : UpperHalfPlane) : PeriodPair where
  ω₁ := (τ : ℂ)
  ω₂ := 1
  indep := LinearIndependent.pair_iff.mpr fun s t hst ↦ by
    have him : s * (τ : ℂ).im = 0 := by
      have := congrArg Complex.im hst
      simpa [Complex.add_im, Complex.smul_im, smul_eq_mul] using this
    have hs : s = 0 :=
      (mul_eq_zero.mp him).resolve_right (UpperHalfPlane.coe_im τ ▸ τ.im_ne_zero)
    subst hs
    simpa using hst

private lemma specPeriodPairOfTau_omega (τ : UpperHalfPlane) :
    (specPeriodPairOfTau τ).ω₁ = (τ : ℂ) ∧ (specPeriodPairOfTau τ).ω₂ = 1 :=
  ⟨rfl, rfl⟩

/-- **SET-7 order 2, executed application (torsion `q`-expansion).** The torsion
bundle is instantiated at `N = 1` and the standard period pair; its last conjunct
(the rationality of `Δ`'s level-one `q`-coefficients) is then consumed. -/
example : ∀ n, ∃ q : ℚ,
    (UpperHalfPlane.qExpansion 1 (ModularForm.discriminant : UpperHalfPlane → ℂ)).coeff n = (q : ℂ) := by
  obtain ⟨-, -, -, -, -, -, hG⟩ :=
    ModularForm.weierstrassP_torsion_qExpansion_package 1 one_ne_zero
      specPeriodPairOfTau specPeriodPairOfTau_omega
  exact hG

-- SET-8 order 1, `ModularForms/WeightOne/MonicRel.lean`.
#check WLight.exists_analyticOnNhd_div_of_monicRel
#check WLight.exists_mdifferentiable_div_of_monicRel
#check WLight.exists_twist_of_flat
#check WLight.span_inter_rational_of_twist_stable

-- SET-8 order 2, `ModularForms/WeightOne/FrickeFunction.lean`.
#check WLight.frickeFunction_modularity_package
#check WLight.frickeFunction_orbit_package
#check WLight.frickeFunction_intBaseChange

/-- **SET-8 order 1, executed application (manifold division).** The monic-relation
division is applied at `a = 0`, `b = 1`, `d = 1`, `c = 0`: the relation holds, so
the leaf produces an `MDifferentiable` quotient `F` with `F * 1 = 0`. The proof
term is elaborated, not merely `#check`ed. -/
example : ∃ F : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧
    F * (fun _ : UpperHalfPlane => (1 : ℂ)) = fun _ : UpperHalfPlane => (0 : ℂ) :=
  WLight.exists_mdifferentiable_div_of_monicRel
    (a := fun _ : UpperHalfPlane => (0 : ℂ)) (b := fun _ : UpperHalfPlane => (1 : ℂ))
    (c := fun _ _ => (0 : ℂ)) (d := 1)
    mdifferentiable_const mdifferentiable_const
    (fun h => one_ne_zero (congrFun h UpperHalfPlane.I))
    (fun k hk => mdifferentiable_const)
    (by funext τ; simp)

/-- **SET-8 order 2, executed application (`j`-holomorphy from the orbit package).**
The orbit bundle is instantiated at the standard period pair, the `℘`-normalised
`W` and its fricke multiple, and `jf = E₄³/Δ`; its first conjunct then yields
`MDifferentiable jf`. Three of its hypotheses are discharged by `rfl`, so the
bundle's defining equations are exercised. -/
example (N : ℕ) [NeZero N] :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : UpperHalfPlane => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) := by
  let W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ := fun v τ =>
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (specPeriodPairOfTau τ)
        ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))
  let fricke : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ := fun v τ =>
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ
  exact (WLight.frickeFunction_orbit_package N specPeriodPairOfTau specPeriodPairOfTau_omega
    W (fun v τ => rfl) fricke (fun v τ => rfl)
    (fun τ : UpperHalfPlane => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (fun τ => rfl)).1.1

-- SET-9 order 1, `ModularForms/WeightOne/LevelFraction.lean`.
#check WLight.qExpansion_sigmaTransport_package
#check WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction
#check WLight.exists_levelFraction_of_stable_family
#check WLight.exists_monicRel_j_of_mdifferentiable_levelFraction

-- SET-9 order 2, `ModularForms/WeightOne/LevelN.lean`.
#check WLight.levelN_structure_package
#check WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient
#check ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient

/-- **SET-9 order 1, executed application (level-fraction monic relation).** The
monic-relation leaf is applied at `F = 0`, `a = 0`, `b = 1` with the standard
period pair and the `℘`-normalised `W`/`fricke` data: the membership and
pole-boundedness hypotheses are discharged concretely, and the resulting monic
relation over `E₄³/Δ` is produced, so the headline is elaborated into a term. -/
example (N : ℕ) [NeZero N] :
    ∃ (d : ℕ) (p : Fin d → Polynomial ℂ),
      ∀ τ : UpperHalfPlane,
        (0 : ℂ) ^ d +
            ∑ i : Fin d, (p i).eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) *
              (0 : ℂ) ^ (i : ℕ) = 0 := by
  let W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ := fun v τ =>
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (specPeriodPairOfTau τ)
        ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))
  let fricke : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ := fun v τ =>
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ
  exact WLight.exists_monicRel_j_of_mdifferentiable_levelFraction N
    specPeriodPairOfTau specPeriodPairOfTau_omega W (fun v τ => rfl) fricke (fun v τ => rfl)
    (fun τ : UpperHalfPlane => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) (fun τ => rfl)
    (a := fun _ : UpperHalfPlane => (0 : ℂ)) (b := fun _ : UpperHalfPlane => (1 : ℂ))
    (F := fun _ : UpperHalfPlane => (0 : ℂ))
    (zero_mem _) (one_mem _)
    (by intro h; exact one_ne_zero (congrFun h UpperHalfPlane.I))
    mdifferentiable_const
    (by funext τ; simp)
    (fun γ => ⟨0, by
      have h0 : ((fun _ : UpperHalfPlane => (0 : ℂ)) ∘ (γ • ·)) *
          ModularForm.discriminant ^ 0 = fun _ : UpperHalfPlane => (0 : ℂ) := by
        funext τ; simp
      rw [h0]
      exact Filter.const_boundedAtFilter UpperHalfPlane.atImInfty (0 : ℂ)⟩)

/-- **SET-9 order 2, executed application (`j`-faithfulness from the level-`N`
package).** The level-`N` structure package is instantiated with the standard
period pair and the `℘`-normalised `W`/`fricke` data; its fourth conjunct — that
`P ↦ P(E₄³/Δ)` has no nonzero polynomial in its kernel — is then extracted as a
proof term, so the package's defining equations and conjunct order are exercised,
not merely `#check`ed. -/
example (N : ℕ) [NeZero N] :
    ∀ P : Polynomial ℂ,
      (∀ τ : UpperHalfPlane,
        P.eval (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) = 0) → P = 0 := by
  let W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ := fun v τ =>
    ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (specPeriodPairOfTau τ)
        ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))
  let fricke : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ := fun v τ =>
    -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ
  exact (WLight.levelN_structure_package N specPeriodPairOfTau specPeriodPairOfTau_omega
    W (fun v τ => rfl) fricke (fun v τ => rfl)
    (fun τ : UpperHalfPlane => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (fun τ => rfl)).2.2.2.1

-- SET-10 order 1, `ModularForms/WeightOne/Gamma0Rationality.lean`.
#check ModularCurve.exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin
#check ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational
#check ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0
#check ModularCurve.exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem

-- SET-10 order 2, `ModularForms/WeightOne/Gamma0Integral.lean`.
#check ModularCurve.exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant
#check ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0
#check ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion

/-- **SET-10 order 1, executed application (Γ₀-rationality of a twist).** The
`comp_smul` headline is instantiated at the zero form `G = 0`, `m = 0` and the
identity `γ = 1 ∈ Γ₀ N`: holomorphy, invariance, boundedness and rationality are
discharged concretely, so the headline is elaborated into a term (not merely
`#check`ed) and its existential conclusion consumed. -/
example (N : ℕ) [NeZero N] (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion 1
      ((fun _ : UpperHalfPlane => (0 : ℂ)) * ModularForm.discriminant ^ 0)).coeff n = (r : ℂ) := by
  refine ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0 N 0
    (fun _ : UpperHalfPlane => (0 : ℂ)) mdifferentiable_const (fun _ _ _ => rfl) ?_ ?_
    (1 : SL(2, ℤ)) (one_mem _) n
  · intro _
    have h : (fun _ : UpperHalfPlane => (0 : ℂ)) * ModularForm.discriminant ^ 0 =
        (0 : UpperHalfPlane → ℂ) := by funext τ; simp
    rw [h]
    exact Filter.const_boundedAtFilter UpperHalfPlane.atImInfty (0 : ℂ)
  · intro n
    refine ⟨0, ?_⟩
    have h0 : (fun _ : UpperHalfPlane => (0 : ℂ)) * ModularForm.discriminant ^ 0 =
        (0 : UpperHalfPlane → ℂ) := by funext τ; simp
    rw [h0, UpperHalfPlane.qExpansion_zero]
    simp

/-- **SET-10 order 2, executed application (Γ₀-slash rationality).** The slash
headline is instantiated at the zero weight-`k` form on `Γ₁ M` and the identity
`γ = 1 ∈ Γ₀ M`; rationality holds because the zero form's `q`-expansion is zero,
so the headline is elaborated and its existential conclusion used. -/
example (M : ℕ) [NeZero M] {k : ℤ} (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion 1
      (((0 : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k) :
        UpperHalfPlane → ℂ) ∣[k] (1 : SL(2, ℤ)))).coeff n = (r : ℂ) :=
  ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0 M
    (0 : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (fun n => ⟨0, by
      have h0 : (⇑(0 : ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k) :
          UpperHalfPlane → ℂ) = (0 : UpperHalfPlane → ℂ) := by funext τ; simp
      rw [h0, UpperHalfPlane.qExpansion_zero]
      simp⟩) 1 (one_mem _) n

-- SET-11 order 1, `ModularForms/WeightOne/Gamma1Basis.lean`.
#check CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff
#check ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq
#check CuspForm.exists_gamma1_frickeRational_sigmaTransport
#check CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top
#check CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even
#check CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply

-- SET-11 order 2, `ModularForms/WeightOne/Gamma1IntegralBasis.lean`.
#check CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even
#check CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp
#check CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast
#check CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast

/-- **SET-11 order 1, executed application (Γ₁ Eisenstein integral model).** The
Eisenstein headline is instantiated at `M = 2`, `k = 3`: the existential is
eliminated and its slash-equivariance conjunct extracted, so the headline (with
its `ModularCurve.IsIntegralQExp` vocabulary) is elaborated into a term. -/
example : ∃ G : ZMod 2 → ModularForm (CongruenceSubgroup.Gamma1 2 : Subgroup (GL (Fin 2) ℝ)) 3,
    ∀ (c : ZMod 2) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 2 →
      ((⇑(G c) : ℍ → ℂ) ∣[(3 : ℤ)] γ) = ⇑(G (c * ((γ 0 0 : ℤ) : ZMod 2))) := by
  obtain ⟨G, -, hslash⟩ :=
    ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq 2 3 le_rfl
  exact ⟨G, hslash⟩

/-- **SET-11 order 2, executed application (integral-slash Γ₁ basis).** The last
headline is applied at the concrete `N = 3`, `k = 2` — the shape the capstone
`WeightOne/IntegralStructure.lean` reuses — so its `Module.Basis` existential and
the `q`-coefficient slash-integrality conjunct are elaborated into a term. -/
example : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 3) 2)),
    ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 3 → ∀ m : ℕ,
      ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[(2 : ℤ)] γ) m ∈ Set.range ((↑) : ℤ → ℂ) :=
  CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast 3 2

-- The capstone, `ModularForms/WeightOne/IntegralStructure.lean`.
#check CuspForm.hasIntegralStructure_of_basis_gamma1
#check CuspForm.hasIntegralStructure_of_two_le
#check CuspForm.hasIntegralStructure_two

/-- **Capstone, executed application of the trace lemma to SET-11's basis.** The
`hasIntegralStructure_of_basis_gamma1` trace lemma is applied at `N = 3`, `k = 2`
to SET-11 order 2's `exists_basis_gamma1_qCoeff_slash_mem_range_intCast`, so the
capstone's hypothesis (a `ℂ`-basis of `S_2(Γ₁(3))` whose `Γ₀(3)`-slashes have
integral `q`-coefficients) is discharged by the previous headline and the two
modules are elaborated into one proof term. -/
example : CuspForm.HasIntegralStructure 3 2 :=
  CuspForm.hasIntegralStructure_of_basis_gamma1
    (CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast 3 2)

/-- **Capstone, executed application of the `k ≥ 2` corollary.** The corollary is
instantiated at the concrete `N' = 3`, `k = 4`: the weight bound `2 ≤ 4` is
discharged, so the unconditional `HasIntegralStructure 3 4` is produced. -/
example : CuspForm.HasIntegralStructure 3 4 :=
  CuspForm.hasIntegralStructure_of_two_le 3 4 (by norm_num)

/-- **Capstone, executed application at `k = 2`.** The `k = 2` instance is
instantiated at `N = 3`, closing the `WeightOne` layer's `Γ₀`-integral-structure
target at weight two. -/
example : CuspForm.HasIntegralStructure 3 2 := CuspForm.hasIntegralStructure_two 3
