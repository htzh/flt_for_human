/-
  Consumer specification for SET 7 of the `AlgebraicCurve` layer.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the set's headlines, composed across modules, expressed in Lean so
  that each is either bound or not. It is a deliverable measure, not a proof obligation. It
  is **not part of any library** (`lake build` does not see `spec/`); run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/AlgebraicCurveSet7Consumer.lean 2>&1 | grep -c error

  The error count is the metric.

  ZONES
  -----
    [weil]     ZONE A — the new `Pic0.torsion.exists_addMonoidHom_eval_eq_pairing`
               (`Pic0/WeilPairing.lean`) is the pairing hom; at the zero `WeilDatum`
               (`Defs/WeilDatum.lean`) its value on the zero classes is the pairing
               `evalFun 1 0 / evalFun 1 0`, which is `1`. This is the hom's public statement
               and the `WeilDatum`/`evalFun` API from two other modules, nothing private.
    [ell]      ZONE B — the CFE rows compose: the `ell(N·D)` growth
               (`Genus/ConstantFieldExtensionConsequences.lean`) at `N = M` has
               `Divisor.degree D` on the right; the degree identity of the same module
               rewrites it to `[F : K⟮x⟯]`, the two rows of the set in one statement.
    [pullback] ZONE C — `Divisor.evalFun_pullback` (`Place/EvalAtNorm.lean`) reads the value of
               a norm on a pullback; unfolded by `Divisor.evalFun_def` it is the fibre product
               over the support, the place-evaluation dictionary's form.
    [span]     ZONE D — the char-free `mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed`
               (`IsCurveOver/ConstantFieldExtensionSpan.lean`, the manager's generalisation)
               implies the char-0 statement of the same module: the general theorem under
               `[CharZero K]` is the special one, with no separate proof.
-/

import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionSpan
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences
import FLTForHuman.AlgebraicCurve.Pic0.WeilPairing
import FLTForHuman.AlgebraicCurve.Place.EvalAtNorm
import FLTForHuman.AlgebraicCurve.WeilExchange.FiberOverCount

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve

universe u v w

/-! ## Zone A — `[weil]` the pairing hom at the zero datum -/

/-- The zero `WeilDatum`: both divisors and both functions trivial; the disjointness and
rationality fields are vacuous.  Public constructors only. -/
private def zeroDatum (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F]
    (n : ℕ) : WeilDatum K F n where
  D₁ := 0
  D₂ := 0
  f₁ := 1
  f₂ := 1
  f₁_ne_zero := one_ne_zero
  f₂_ne_zero := one_ne_zero
  ord_f₁ := by intro v; simp
  ord_f₂ := by intro v; simp
  disjoint := by intro v; exact Or.inl rfl
  rational := by intro v hv; rcases hv with h | h <;> exact absurd (by simp) h

/-- The hom's value on the zero datum's classes is `1`. -/
theorem set7_weil_hom_zero {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S)) :
    ∃ hom : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n),
      (Additive.toMul (hom 0)) 0 = 1 := by
  obtain ⟨hom, hhom⟩ := Pic0.torsion.exists_addMonoidHom_eval_eq_pairing hrec hconst hmove
  refine ⟨hom, ?_⟩
  have h := hhom (zeroDatum K F n) 0 0 ⟨0, rfl, rfl⟩ ⟨0, rfl, rfl⟩
  rw [h]
  simp [zeroDatum, WeilDatum.pairing]

/-! ## Zone B — `[ell]` the growth and the degree identity in one statement -/

theorem set7_ell_growth_degree {K : Type u} {F : Type v} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ N, M ≤ N →
      (ell (N • D) : ℤ) =
        (N : ℤ) * (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ)
          + 1 - genusFF K F := by
  obtain ⟨-, M, hM, hN⟩ :=
    exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD
  refine ⟨M, hM, fun N hN' => ?_⟩
  rw [hN N hN',
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx D hD]

/-! ## Zone C — `[pullback]` the pullback value is the fibre product -/

theorem set7_evalFun_pullback_fibre {K : Type u} {F F' : Type v} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    {f : F'} (hf : f ≠ 0) (E : Divisor K F)
    (hrat : ∀ v ∈ E.support, Place.IsRational v)
    (hratw : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', Place.IsRational w)
    (hord : ∀ v ∈ E.support, ∀ w ∈ v.fiber F', w.ord f = 0) :
    Divisor.evalFun f (Divisor.pullback F' E)
      = ∏ v ∈ E.support, v.evalAt (Algebra.norm F f) ^ E v := by
  rw [Divisor.evalFun_pullback hf E hrat hratw hord, Divisor.evalFun_def]

/-! ## Zone D — `[span]` the general spanning theorem covers the char-0 one -/

theorem set7_span_general_implies_char0 {K : Type u} {F : Type v} {K' : Type v}
    {F' : Type v} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
    [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (z : F')
    (hz : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        z ∈ v'.toValuationSubring) :
    z ∈ Submodule.span K' (Set.range (algebraMap F F')) :=
  mem_span_range_algebraMap_of_constantFieldExtension_of_isAlgClosed
    K F K' F' hfg hfg' hgen z hz

/-! ## Zone E — `[inertia]` the weak inertia-degree positivity from the strong form -/

theorem set7_inertiaDeg_pos {K : Type u} {F F' : Type v} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] (w : Place K F') :
    0 < w.inertiaDeg F :=
  Place.inertiaDeg_pos w
