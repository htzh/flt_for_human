/-
  WORKORDER-C2 phase 2 — the `X₁` integrality / `q`-expansion leaves.

  Statements verbatim from the pinned wrappers, proofs transcribed from the
  matching `P2M/Sol/S_*` files (pin `aa2d8b3`), adapted to mathlib `v4.34.0`:

  * `ModularCurve.isIntegral_jqNModC_of_modularPolynomialData` —
    `Theorems/Thm_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData.lean`
    (`P2M/Sol/S_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData.lean`,
    262 lines). Only the pin's `SepFibre`→`isIntegral_jqNModC` cone is transcribed;
    its separability branch (`root`, `slice_jqNModC_eq_prod`,
    `slice_jqModC_separable*`, `isSeparable_jqNModC`) serves the pin's
    `isIntegral_jqNModC_all` headlines rather than this one and is left out,
    together with `ev_comm_of_evalSymm` whose only consumer there is that branch.
  * `ModularCurve.exists_gamma0_qExpansion_div_eq_jqNModC` —
    `Theorems/Thm_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC.lean`
    (`P2M/Sol/S_…`, 141 lines), the pin's `SolJJLAux` block kept `private`.
  * `ModularCurve.eisenstein4_cube_sub_mk_sq` —
    `Theorems/Thm_ModularCurve_eisenstein4_cube_sub_mk_sq.lean`
    (`P2M/Sol/S_…`, 121 lines); the pin's `example`s and its `eisenstein6` /
    `qExpansion_E6_eq_map_eisenstein6` / `eisenstein4_cube_sub_eisenstein6_sq`
    aliases have no consumer on this cone and are dropped, as are the pin's two
    `#print axioms` lines.

  Dedup against the port. The pin's `SepFibre.eval` prelude and
  `swap_eq_of_evalSymm` are `private` in
  `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` (`SwapBivarGlue`,
  `EvalSymmSwap`); the pin's `coeffMap_jqModC` is `private` in
  `FLTForHuman/ModularCurve/X1/FunctionFieldResidue.lean`; the pin's
  `SolJJLAux.{gamma0_one_eq_top, gamma0_one_coe, one_mem_sp, e4cube, delta1}` are
  public as `ModularCurve.DeepCosetAux.*` in
  `FLTForHuman/ModularCurve/ModularPolynomialE4Cube.lean`. No hub shares this
  module's subject, so each needed helper is re-derived locally `private` (in the
  pin's own inner namespace) rather than promoted; the pin's `ev_eq_evalEval` and
  `map_ev` exist in no port module and are transcribed from the pin. The public
  `ModularForm.exists_degeneracy_Gamma0`, `ModularCurve.laurent_qParam_coeff_unique`,
  `ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant`,
  `ModularCurve.qExpansion_E4_eq_map_eisenstein4` and
  `ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` are imported
  and used as they stand.

  **Not ported here**: `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`
  (`Theorems/Thm_ModularCurve_exists_sum_smul_eq_of_isIntegralQExp_gamma1.lean`).
  Its proof's only non-elementary input is the *modular-form* Gamma₁ rational
  structure `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, which does
  **not** exist publicly anywhere in the port: only its `CuspForm` twin
  `CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`
  (`FLTForHuman/ModularForms/WeightOne/Gamma1IntegralBasis.lean`) was ported, and
  the pin's `ModularForm`-level chain behind the missing statement
  (`ModularForm.span_frickeRational_E4_pow_E6_pow_eq_top`,
  `ModularForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even` (128 lines),
  `…_mem_adjoin_exp` (448), `ModularForm.exists_gamma1_qCoeff_eq_algEquiv_apply_of_even`
  (913), `…_eq_algEquiv_apply` (341), `…_mem_range_ratCast` (261)) is unported, so
  the headline is left out rather than invented, weakened, or smuggled through a
  hub edit. See the workorder's §"stop and report".

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_eisenstein4_cube_sub_mk_sq.lean
-/
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.JqIntegralRatios
import FLTForHuman.ModularCurve.Analytic.QParamUnique
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.JqAnalyticModel
import FLTForHuman.ModularForms.Level.Degeneracy
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups

namespace ModularCurve

/-! ## `eisenstein4 ^ 3 - (eisenstein6) ^ 2 = 1728 * (X * dedekindEtaUnit)` -/

namespace EisensteinCube

/-- The `q`-expansion of `E₆` against the pin's explicit `mk` series — the pin's
spelling of the `σ₅` sum (`∑ d ∈ n.divisors, d ^ 5`, as it appears in the
headline) rather than the port's `ArithmeticFunction.sigma`-shaped `P6`. -/
private theorem qExpansion_E6_eq_map_mk :
    UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ =
      PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) := by
  ext m
  rw [EisensteinSeries.E_qExpansion_coeff (k := 6) (by norm_num) (by decide),
    PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [ite_eq_right hm.ne', ite_eq_right hm.ne',
      show _root_.bernoulli 6 = 1 / 42 by decide +kernel,
      ArithmeticFunction.sigma_apply, show (6 : ℕ) - 1 = 5 from rfl]
    simp only [map_mul, map_neg, map_sum, map_pow, map_natCast, map_ofNat]
    push_cast
    ring

/-- `q(E₄) ^ 3 - q(E₆) ^ 2 = 1728 * q(Δ)`, from mathlib's pointwise
`discriminant_eq_E₄_cube_sub_E₆_sq`. -/
private theorem qExpansion_E4_cube_sub_E6_sq :
    UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ ^ 3 -
        UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ ^ 2 =
      1728 * UpperHalfPlane.qExpansion 1 ModularForm.discriminant := by
  have hfun : ((1728 : ℂ) • ⇑CuspForm.discriminant : ℍ → ℂ) =
      ⇑(ModularForm.mcast (b := 12) (Γ' := 𝒮ℒ) (by decide) (ModularForm.E₄.pow 3)) -
        ⇑(ModularForm.mcast (b := 12) (Γ' := 𝒮ℒ) (by decide) (ModularForm.E₆.pow 2)) := by
    funext z
    simp only [Pi.smul_apply, Pi.sub_apply, ModularForm.coe_mcast, ModularForm.coe_pow,
      Pi.pow_apply, CuspForm.coe_discriminant, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq,
      smul_eq_mul]
    ring
  have hq := congrArg (UpperHalfPlane.qExpansion 1) hfun
  rw [ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_mcast, ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    CuspForm.coe_discriminant, PowerSeries.smul_eq_C_mul, map_ofNat] at hq
  exact hq.symm

/-- The pin's `eisenstein4_cube_sub_mk_sq`, transferred across
`PowerSeries.map_injective` from the two `q`-expansions. -/
private theorem eisenstein4_cube_sub_mk_sq_aux :
    eisenstein4 ^ 3 -
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) ^ 2 =
      1728 * (PowerSeries.X * dedekindEtaUnit) := by
  have hC := qExpansion_E4_cube_sub_E6_sq
  rw [qExpansion_E4_eq_map_eisenstein4, qExpansion_E6_eq_map_mk,
    qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit] at hC
  apply PowerSeries.map_injective (Int.castRingHom ℂ) fun _ _ h => Int.cast_injective (α := ℂ) h
  rw [map_sub, map_pow, map_pow, map_mul, map_ofNat]
  exact hC

end EisensteinCube

/-! ## `jqNModC` is integral over `K[jqModC]`

The pin's `SepFibre` block. `ev`, `aeval_toRingHom_eq`, `ev_eq_aevalAeval`, `ev_swap`,
`ev_int`, `ev_sub` and `swap_eq_of_evalSymm` are `private` in
`FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean`; `coeffMap_jqModC` is
`private` in `FLTForHuman/ModularCurve/X1/FunctionFieldResidue.lean`. Neither hub
shares this headline's subject, so each is re-derived here `private`; the pin's
`ev_eq_evalEval` / `map_ev` belong to no port module and are transcribed from the
pin. -/

namespace SepFibre

open Polynomial

section Eval

variable {A : Type*} [CommRing A]

/-- The pin's `SepFibre.ev`: `Φ` evaluated at `(x, y)` with the integer
coefficients cast into `A`. -/
private def ev (Φ : Polynomial (Polynomial ℤ)) (x y : A) : A :=
  Φ.eval₂ (eval₂RingHom (Int.castRingHom A) x) y

private theorem aeval_toRingHom_eq [Algebra ℤ A] (x : A) :
    (Polynomial.aeval (R := ℤ) x).toRingHom = eval₂RingHom (Int.castRingHom A) x :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

/-- `ev` is mathlib's coefficient-cast `evalEval`. -/
private theorem ev_eq_evalEval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = (Φ.map (mapRingHom (Int.castRingHom A))).evalEval x y := by
  rw [ev, ← eval₂_eval₂RingHom_apply]

/-- `ev` is mathlib's `aevalAeval`. -/
private theorem ev_eq_aevalAeval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = aevalAeval x y Φ := by
  have h : eval₂RingHom (eval₂RingHom (Int.castRingHom A) x) y
      = (aevalAeval (R := ℤ) x y).toRingHom := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
    · simp
    · simp
  exact RingHom.congr_fun h Φ

/-- `ev` is natural in the coefficient ring. -/
private theorem map_ev {B : Type*} [CommRing B] (φ : A →+* B) (Φ : Polynomial (Polynomial ℤ))
    (x y : A) : φ (ev Φ x y) = ev Φ (φ x) (φ y) := by
  rw [ev_eq_evalEval, ev_eq_evalEval, ← map_mapRingHom_evalEval φ, Polynomial.map_map,
    mapRingHom_comp, RingHom.ext_int (φ.comp (Int.castRingHom A)) (Int.castRingHom B)]

private theorem ev_swap (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev (Bivariate.swap Φ) x y = ev Φ y x := by
  rw [ev_eq_aevalAeval, ev_eq_aevalAeval, Bivariate.aevalAeval_swap]

private theorem ev_int (Φ : Polynomial (Polynomial ℤ)) (a b : ℤ) :
    ev Φ (a : A) (b : A) = ((Φ.evalEval a b : ℤ) : A) := by
  rw [ev, eval₂_eval₂RingHom_apply]
  exact map_mapRingHom_evalEval (Int.castRingHom A) Φ a b

private theorem ev_sub (Φ Ψ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev (Φ - Ψ) x y = ev Φ x y - ev Ψ x y := by
  rw [ev_eq_aevalAeval, map_sub, ← ev_eq_aevalAeval, ← ev_eq_aevalAeval]

end Eval

/-- Evaluated symmetry forces the transpose to be `Φ` itself. The port's copy is
`private` in `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean`; re-derived
here. -/
private theorem swap_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) :
    Bivariate.swap Φ = Φ := by
  set G : Polynomial (Polynomial ℤ) := Bivariate.swap Φ - Φ with hG
  have hL : ∀ x y : LaurentSeries ℚ, ev G x y = 0 := fun x y => by
    have hxy := h x y
    rw [aeval_toRingHom_eq, aeval_toRingHom_eq] at hxy
    rw [hG, ev_sub, ev_swap, sub_eq_zero]
    exact hxy.symm
  have hZ : ∀ a b : ℤ, G.evalEval a b = 0 := fun a b => by
    have h0 : ((G.evalEval a b : ℤ) : LaurentSeries ℚ) = 0 := by
      rw [← ev_int G a b]
      simpa using hL (a : LaurentSeries ℚ) (b : LaurentSeries ℚ)
    exact Int.cast_injective (α := ℚ)
      ((algebraMap ℚ (LaurentSeries ℚ)).injective (by simpa using h0))
  have h1 : ∀ b : ℤ, G.eval (Polynomial.C b) = 0 := fun b =>
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun a : ℤ => a) (fun _ _ h => h) fun a => hZ a b)
  have h2 : G = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun b : ℤ => Polynomial.C b) (fun _ _ h => Polynomial.C_injective h) fun b => h1 b)
  exact sub_eq_zero.mp h2

section Rel

variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)

/-- The pin's `coeffMap_jqModC`, i.e. `map_jqModC` read through `coeffMap`. The port's
copy is `private` in `FLTForHuman/ModularCurve/X1/FunctionFieldResidue.lean`. -/
private theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

private theorem coeffMap_jqNModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (N : ℕ) [NeZero N] : coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, coeffMap_qExpand, coeffMap_jqModC, jqNModC]

private theorem ev_jq_int : ev data.Φ (jqModC ℤ) (jqNModC ℤ N) = 0 := by
  apply coeffMap_injective (f := Int.castRingHom ℚ) Int.cast_injective
  rw [map_ev, coeffMap_jqModC, coeffMap_jqNModC, map_zero, jqModC_rat, jqNModC, jqModC_rat]
  have h0 := data.eval_eq_zero
  rw [evalAtJ_def, aeval_toRingHom_eq] at h0
  exact h0

private theorem ev_jq (A : Type*) [CommRing A] : ev data.Φ (jqModC A) (jqNModC A N) = 0 := by
  have h := congrArg (coeffMap (Int.castRingHom A)) (ev_jq_int data)
  rwa [map_ev, coeffMap_jqModC, coeffMap_jqNModC, map_zero] at h

end Rel

section Slice

variable {A : Type*} [CommRing A]

/-- The pin's `SepFibre.slice`: `Φ` with its first variable specialised to `x`. -/
private def slice (Φ : Polynomial (Polynomial ℤ)) (x : A) : Polynomial A :=
  (Φ.map (mapRingHom (Int.castRingHom A))).map (evalRingHom x)

private theorem eval_slice (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    (slice Φ x).eval y = ev Φ x y := by
  rw [slice, map_evalRingHom_eval, ev_eq_evalEval]

private theorem slice_monic {Φ : Polynomial (Polynomial ℤ)} (hΦ : Φ.Monic) (x : A) :
    (slice Φ x).Monic :=
  (hΦ.map _).map _

private theorem slice_map {B : Type*} [CommRing B] (Φ : Polynomial (Polynomial ℤ)) (x : A)
    (φ : A →+* B) : (slice Φ x).map φ = slice Φ (φ x) := by
  simp only [slice, Polynomial.map_map]
  refine congrArg (fun f : Polynomial ℤ →+* B => Φ.map f) ?_
  exact Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

end Slice

section Integral

variable (K : Type*) [Field K]

-- `data` occurs only in the proof, not in the statement, so it is bound explicitly
-- (a `variable` binder invisible to the type is dropped from the signature).
private theorem isIntegral_jqNModC {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) := by
  set E := IntermediateField.adjoin K {jqModC K}
  let jE : E := ⟨jqModC K, IntermediateField.mem_adjoin_simple_self K (jqModC K)⟩
  refine ⟨slice data.Φ jE, slice_monic data.monic _, ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_def, ← Polynomial.eval_map, slice_map, eval_slice]
  exact ev_jq data K

end Integral

end SepFibre

/-! ## `jqNModC ℂ ℓ` is a quotient of `Γ₀`-forms of weight `12`

The pin's `SolJJLAux` block. Its five helpers all have public twins in
`FLTForHuman/ModularCurve/ModularPolynomialE4Cube.lean`
(`ModularCurve.DeepCosetAux.*`), but that hub is about the `E₄³`/`Δ` modular
polynomial, not this headline, so they are re-derived here `private` rather than
imported; `e4cube` is written through `E₄.pow 3` as in the pin (the hub spells it
with two `mul`s). -/

namespace SolJJLAux

private theorem gamma0_one_eq_top : CongruenceSubgroup.Gamma0 1 = ⊤ := by
  ext A
  simp [CongruenceSubgroup.Gamma0_mem, eq_iff_true_of_subsingleton]

private theorem gamma0_one_coe :
    ((CongruenceSubgroup.Gamma0 1 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [gamma0_one_eq_top, MonoidHom.range_eq_map]

private noncomputable def e4cube : ModularForm (CongruenceSubgroup.Gamma0 1) 12 :=
  ModularForm.mcast (by norm_num) (ModularForm.E₄.pow 3) gamma0_one_coe

private noncomputable def delta1 : ModularForm (CongruenceSubgroup.Gamma0 1) 12 :=
  ModularForm.mcast rfl (CuspForm.toModularFormₗ CuspForm.discriminant) gamma0_one_coe

private theorem coe_e4cube : ⇑e4cube = ⇑(ModularForm.E₄.pow 3) := rfl

private theorem coe_delta1 : ⇑delta1 = ModularForm.discriminant := rfl

private theorem one_mem_sp (N : ℕ) : (1 : ℝ) ∈
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

/-- The pin's `SolJJLAux.hasSum_int`: the `q`-expansion of a `ModularFormClass`,
displayed as a `HasSum` over `ℤ` (the pin's Laurent form of
`UpperHalfPlane.hasSum_qExpansion`). -/
private theorem hasSum_int {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m : ℤ =>
      ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ).coeff m *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ) := by
  have hI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have h0 := UpperHalfPlane.hasSum_qExpansion (f := (f : ℍ → ℂ)) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
    (ModularFormClass.bdd_at_infty f) τ
  refine (Function.Injective.hasSum_iff Nat.cast_injective ?_).mp ?_
  · intro m hm
    rcases m with n | n
    · exact absurd ⟨n, rfl⟩ hm
    · rw [ofPowerSeries_coeff_of_neg _ (Int.negSucc_lt_zero n), zero_mul]
  · have hcomp : ((fun m : ℤ =>
        ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ).coeff m *
          Function.Periodic.qParam 1 (τ : ℂ) ^ m) ∘ (Nat.cast : ℕ → ℤ)) =
        fun n : ℕ => (qExpansion 1 (f : ℍ → ℂ)).coeff n •
          Function.Periodic.qParam 1 (τ : ℂ) ^ n := by
      funext n
      simp only [Function.comp_apply, smul_eq_mul, zpow_natCast,
        LaurentSeries.coeff_coe_powerSeries]
    rw [hcomp]
    exact h0

/-- The pin's `SolJJLAux.hasSum_qExpand`: a `HasSum` at `τ` becomes one at
`heckeDiagMatrix ℓ • τ` for the `q ↦ q ^ ℓ` substitution. -/
private theorem hasSum_qExpand (ℓ : ℕ) [NeZero ℓ] {A : LaurentSeries ℂ} {S : ℂ} {τ : ℍ}
    (h : HasSum (fun m : ℤ => A.coeff m *
      Function.Periodic.qParam 1 (((ModularForm.heckeDiagMatrix ℓ • τ : ℍ)) : ℂ) ^ m) S) :
    HasSum (fun m : ℤ => (qExpand ℂ ℓ A).coeff m *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) S := by
  have hq : Function.Periodic.qParam 1 (((ModularForm.heckeDiagMatrix ℓ • τ : ℍ)) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ (ℓ : ℕ) := by
    rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ) τ]
    unfold Function.Periodic.qParam
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hq] at h
  have hinj : Function.Injective (fun m : ℤ => (ℓ : ℤ) * m) :=
    mul_right_injective₀ (by exact_mod_cast NeZero.ne ℓ)
  refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
  · intro m hm
    have hnd : ¬ ((ℓ : ℕ) : ℤ) ∣ m := by
      rintro ⟨c, rfl⟩
      exact hm ⟨c, rfl⟩
    rw [qExpand_coeff_of_not_dvd ℓ A hnd, zero_mul]
  · have hcomp : ((fun m : ℤ => (qExpand ℂ ℓ A).coeff m *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) ∘ (fun m : ℤ => (ℓ : ℤ) * m)) =
        fun m : ℤ => A.coeff m *
          (Function.Periodic.qParam 1 (τ : ℂ) ^ (ℓ : ℕ)) ^ m := by
      funext m
      simp only [Function.comp_apply]
      rw [qExpand_coeff_mul, zpow_mul, zpow_natCast]
    rw [hcomp]
    exact h

/-- The pin's `SolJJLAux.qExpansion_coe_dilate`, by `laurent_qParam_coeff_unique`
against `hasSum_int`/`hasSum_qExpand`. -/
private theorem qExpansion_coe_dilate {ℓ : ℕ} [NeZero ℓ] {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 1) k)
    (g : ModularForm (CongruenceSubgroup.Gamma0 ℓ) k)
    (hg : ⇑g = fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ)) :
    ((qExpansion 1 (g : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      qExpand ℂ ℓ ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  refine laurent_qParam_coeff_unique 1 one_pos (g : ℍ → ℂ) _ _
    (hasSum_int g (one_mem_sp ℓ)) ?_
  intro τ
  have h := hasSum_qExpand ℓ (hasSum_int f (one_mem_sp 1) (ModularForm.heckeDiagMatrix ℓ • τ))
  rw [show f (ModularForm.heckeDiagMatrix ℓ • τ) = g τ from by rw [hg]] at h
  exact h

end SolJJLAux

end ModularCurve

open ModularCurve

/-- The power-series identity `eisenstein4 ^ 3 - (…mk…) ^ 2 = 1728 * (X * dedekindEtaUnit)`,
verbatim from `Theorems/Thm_ModularCurve_eisenstein4_cube_sub_mk_sq.lean`. -/
theorem ModularCurve.eisenstein4_cube_sub_mk_sq :
    eisenstein4 ^ 3 -
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) ^ 2 =
      1728 * (PowerSeries.X * dedekindEtaUnit) :=
  ModularCurve.EisensteinCube.eisenstein4_cube_sub_mk_sq_aux

/-- `jqNModC K N` is integral over `K[jqModC K]` for every `ModularPolynomialData N`,
verbatim from `Theorems/Thm_ModularCurve_isIntegral_jqNModC_of_modularPolynomialData.lean`. -/
theorem ModularCurve.isIntegral_jqNModC_of_modularPolynomialData (K : Type*) [Field K] {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) :=
  ModularCurve.SepFibre.isIntegral_jqNModC K data

/-- `jqNModC ℂ ℓ` is the quotient of two level-`ℓ` `Γ₀` forms of weight `12`,
verbatim from `Theorems/Thm_ModularCurve_exists_gamma0_qExpansion_div_eq_jqNModC.lean`. -/
theorem ModularCurve.exists_gamma0_qExpansion_div_eq_jqNModC (ℓ : ℕ) [NeZero ℓ] : ∃ G H : ModularForm (CongruenceSubgroup.Gamma0 ℓ) 12, H ≠ 0 ∧ ((qExpansion 1 (G : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) / ((qExpansion 1 (H : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) = ModularCurve.jqNModC ℂ ℓ := by
  obtain ⟨G, hG⟩ := ModularForm.exists_degeneracy_Gamma0
    (show ℓ * 1 ∣ ℓ by simp) SolJJLAux.e4cube
  obtain ⟨H, hH⟩ := ModularForm.exists_degeneracy_Gamma0
    (show ℓ * 1 ∣ ℓ by simp) SolJJLAux.delta1
  have hGL := SolJJLAux.qExpansion_coe_dilate SolJJLAux.e4cube G hG
  have hHL := SolJJLAux.qExpansion_coe_dilate SolJJLAux.delta1 H hH
  refine ⟨G, H, ?_, ?_⟩
  · intro h0
    refine ModularForm.discriminant_ne_zero
      (ModularForm.heckeDiagMatrix ℓ • UpperHalfPlane.I) ?_
    have h1 := congrFun hH UpperHalfPlane.I
    rw [h0] at h1
    have h__af := h1.symm
    simp at h__af
    exact h__af
  · have he4 : qExpansion 1 (SolJJLAux.e4cube : ℍ → ℂ) =
        (qExpansion 1 (ModularForm.E₄ : ℍ → ℂ)) ^ 3 := by
      rw [SolJJLAux.coe_e4cube]
      exact ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL ModularForm.E₄ 3
    have hΔ1 : qExpansion 1 (SolJJLAux.delta1 : ℍ → ℂ) =
        qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) := by
      rw [SolJJLAux.coe_delta1]
    rw [hGL, hHL, he4, hΔ1,
      show ModularCurve.jqNModC ℂ ℓ = ModularCurve.qExpand ℂ ℓ (ModularCurve.jqModC ℂ) from rfl,
      ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant, map_div₀,
      PowerSeries.coe_pow]

end
