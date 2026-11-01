/-
  The primitive-coset two-variable polynomial at level `N`.

  `cosetTwoVarPoly ζ N J = ∏ t ∈ primCosetReps N, (X - C (cosetConj ζ J t))` is the
  `q`-expansion side of the level-`N` modular polynomial. This module carries the
  four facts about it that the splitting input needs:

  * `ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex` — the root
    property descends from `ℂ` to an arbitrary field `K`: `coeffMap` along
    `ℤ → K`, the evaluation `phiAt` and `coeffMap_injective` transport it.
  * `eq_cosetTwoVarPoly_of_forall_isRoot` — a monic polynomial of the right degree
    vanishing at every `cosetConj ζ J t` *is* `cosetTwoVarPoly ζ N J`.
  * `separable_cosetTwoVarPoly` — `cosetTwoVarPoly ζ N J` is separable.
  * `hasSum_cosetSubst_coeff_mul_qParam_pow` — the `qParam`/`HasSum` form of the
    `cosetSubst` substitution.

  The two coset-polynomial rows share the `cosetConj_injOn` engine (the conjugates
  of `J` are pairwise distinct once `J` has a simple pole at `q = 0` with no lower
  terms), written once here.

  The module's second subject is the **separability of `Φ_N` over `K(X)`**
  (`ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero`): for a field
  `K` with `(N : K) ≠ 0`, `Φ_N` with its coefficients cast to `K` and then mapped
  into the rational function field `K(X)` is separable. The `IgusaSepAux` block at
  the end of the module proves the general transfer
  (`separable_map_ratFunc_of_transcendental`: separability descends along a
  transcendental generator), the `ℤ`-coefficient compatibility
  (`map_aeval_comp_mapRingHom_intCast`) and the transcendence of
  `qExpand L M (jqModC L)`; the headline then reads the hypothesis off the
  coset-root engine above at the algebraic closure of `K`.

  FLT provenance, pinned `aa2d8b3` — the `Theorems/` wrapper (the statement
  authority) and the `P2M/Sol/S_*.lean` proof source of each row:
  `Theorems/Thm_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex.lean`,
  `Theorems/Thm_ModularCurve_eq_cosetTwoVarPoly_of_forall_isRoot.lean`,
  `Theorems/Thm_ModularCurve_separable_cosetTwoVarPoly.lean`,
  `Theorems/Thm_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow.lean`
  and the four matching `P2M/Sol/S_*.lean` copies.

  The wrappers are rendered, e.g.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_separable_cosetTwoVarPoly.lean#L7-L11

  The pin's three `S_` namespaces (`CosetDescentAux`, `CosetSepAux`, `CosetQParamAux`)
  are named here by their subject — `CosetDescent`, `CosetPoly`, `CosetQParam` — as
  `check_port` matches a declaration by its last name and statement hash, not by its
  namespace.

  The module's second half is the primitive-coset *root* row: for a primitive `N`-th
  root `ζ`, `Φ_N` evaluated at `jqModC ℂ` and `q^(N)` vanishes at every
  `cosetConj ζ (jqModC ℂ) t`, `t ∈ primCosetReps N`
  (`ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex`).
  Its proof needs the `q`-expansion bookkeeping at **width `N`**, so the pin's
  `CosetRootFormalAux` prelude is carried at width `h` in `CosetRoot` — the width-`1`
  `An`/`qExpansion_finset_prod` block of `ModularPolynomialE4Cube` is the
  specialisation and cannot serve (the root argument's monomials have period `N`).
  `cosetPt`, `coe_cosetPt`, `pow_mul_div_pow`, `UpperHalfPlaneAux.qParam_one_eq_pow`
  and this file's `hasSum_laurent` are reused, not restated.

  `primCosetReps`/`cosetConj`/`cosetTwoVarPoly` (`Defs/PrimCosetReps.lean`),
  `cosetSubst` (`Defs/PhiGen.lean`), `qExpand`/`qTwist`/`coeffMap`
  (`Defs/Laurent.lean`, `Defs/Twist.lean`), `jqModC`/`map_jqModC`
  (`Defs/JqCoeff.lean`) and `ModularPolynomialData` (`Defs/Polynomial.lean`) are
  the port's legacy definition layer: imported, not edited.

  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex.lean
  spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_forall_isRoot_cosetConj_jqModC_of_complex.lean
  spec-pin: Theorems/Thm_ModularCurve_eq_cosetTwoVarPoly_of_forall_isRoot.lean
  spec-pin: P2M/Sol/S_ModularCurve_eq_cosetTwoVarPoly_of_forall_isRoot.lean
  spec-pin: Theorems/Thm_ModularCurve_separable_cosetTwoVarPoly.lean
  spec-pin: P2M/Sol/S_ModularCurve_separable_cosetTwoVarPoly.lean
  spec-pin: Theorems/Thm_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow.lean
  spec-pin: P2M/Sol/S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow.lean
  spec-pin: Theorems/Thm_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst.lean
  spec-pin: P2M/Sol/S_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex.lean
  spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero.lean
  spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero.lean   -- comparable copy
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Analysis.Complex.Periodic
import FLTForHuman.ModularCurve.Defs.PrimCosetReps
import FLTForHuman.ModularCurve.Defs.Polynomial
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Analytic.QParamUnique
import FLTForHuman.ModularCurve.ModularPolynomialE4Cube
import FLTForHuman.ModularCurve.Degree.PhiDegree
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve

/-! ## Descent from `ℂ` to an arbitrary field

The root property of `Φ` at the conjugates of `jq` is a statement about the
coefficients of `Φ` and of `cosetConj ζ (jqModC ·) t`. Both are read by
`coeffMap`, which is injective along an injective coefficient map; so it suffices
to check the property over `ℂ` and push it along `ℤ → K`. The bridge is the
`q`-expansion of `j` at a primitive `N`-th root, which lives over the subalgebra
`ℤ[ζ_N] ⊆ ℂ` and maps onto `K` through `AdjoinRoot (minpoly ℤ ζ_N)`. -/

namespace CosetDescent

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The conjugate `cosetSubst ζ t.1 t.2.1 J` with the `a = 0` case sent to `0`, so
that it is defined for every triple (not only for the primitive coset reps). -/
def conjR (u : Rˣ) (J : LaurentSeries R) (t : ℕ × ℕ × ℕ) : LaurentSeries R :=
  if h : t.1 = 0 then 0 else
    haveI : NeZero (t.1 * t.1) := ⟨Nat.mul_ne_zero h h⟩
    qExpand R (t.1 * t.1) (qTwist (u ^ (t.1 * t.2.1)) J)

theorem conjR_eq_cosetConj {K : Type*} [Field K] (ζ : Kˣ) (J : LaurentSeries K) (t : ℕ × ℕ × ℕ) :
    conjR ζ J t = cosetConj ζ J t := by
  unfold conjR cosetConj
  by_cases h : t.1 = 0
  · rw [dite_eq_left h, dite_eq_left h]
  · rw [dite_eq_right h, dite_eq_right h]
    rfl

/-- The evaluation of `Φ` at `jqModC R` and its `N`-th `q`-expansion, as a
polynomial over `LaurentSeries R`. -/
def phiAt (N : ℕ) [NeZero N] (Φ : Polynomial (Polynomial ℤ)) (R : Type*) [CommRing R] :
    Polynomial (LaurentSeries R) :=
  Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries R)) (qExpand R N (jqModC R)))

theorem coeffMap_jqModC (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem coeffMap_conjR (f : R →+* S) (u : Rˣ) (J : LaurentSeries R) (t : ℕ × ℕ × ℕ) :
    coeffMap f (conjR u J t) = conjR (Units.map (f : R →* S) u) (coeffMap f J) t := by
  unfold conjR
  by_cases h : t.1 = 0
  · rw [dite_eq_left h, dite_eq_left h, map_zero]
  · rw [dite_eq_right h, dite_eq_right h, coeffMap_qExpand,
      coeffMap_qTwist f (u ^ (t.1 * t.2.1)) (Units.map (f : R →* S) (u ^ (t.1 * t.2.1))) rfl,
      map_pow]

theorem phiAt_map (N : ℕ) [NeZero N] (Φ : Polynomial (Polynomial ℤ)) (f : R →+* S) :
    (phiAt N Φ R).map (coeffMap f) = phiAt N Φ S := by
  unfold phiAt
  rw [Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, coeffMap_qExpand, coeffMap_jqModC]

theorem coeffMap_eval_conjR (N : ℕ) [NeZero N] (Φ : Polynomial (Polynomial ℤ)) (f : R →+* S)
    (u : Rˣ) (t : ℕ × ℕ × ℕ) :
    coeffMap f ((phiAt N Φ R).eval (conjR u (jqModC R) t))
      = (phiAt N Φ S).eval (conjR (Units.map (f : R →* S) u) (jqModC S) t) := by
  rw [← Polynomial.coe_evalRingHom, ← phiAt_map N Φ f, ← coeffMap_jqModC f, ← coeffMap_conjR]
  rw [Polynomial.coe_evalRingHom, Polynomial.eval_map, ← Polynomial.coe_eval₂RingHom]
  exact Polynomial.hom_eval₂ _ _ _ _ |>.trans (by simp)

end CosetDescent

open CosetDescent

theorem ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (hC : ∃ ζ : ℂˣ, IsPrimitiveRoot ζ N ∧ ∀ t ∈ ModularCurve.primCosetReps N,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ))
        (ModularCurve.qExpand ℂ N (ModularCurve.jqModC ℂ)))).IsRoot
        (ModularCurve.cosetConj ζ (ModularCurve.jqModC ℂ) t))
    (K : Type*) [Field K] (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) :
    ∀ t ∈ ModularCurve.primCosetReps N,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (ModularCurve.qExpand K N (ModularCurve.jqModC K)))).IsRoot
        (ModularCurve.cosetConj ζ (ModularCurve.jqModC K) t) := by
  classical
  obtain ⟨ζC, hζCu, hrootC⟩ := hC
  have hζC : IsPrimitiveRoot (ζC : ℂ) N := IsPrimitiveRoot.coe_units_iff.mpr hζCu
  intro t ht
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)

  set R : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {(ζC : ℂ)} with hR
  have hzmem : (ζC : ℂ) ∈ R := Algebra.self_mem_adjoin_singleton ℤ (ζC : ℂ)
  set z : R := ⟨(ζC : ℂ), hzmem⟩ with hz
  have hzpow : z ^ N = 1 := by
    apply Subtype.ext
    show ((ζC : ℂ)) ^ N = 1
    exact hζC.pow_eq_one
  have hzmul : z * z ^ (N - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hN, hzpow]
  set u : Rˣ := Units.mkOfMulEqOne z (z ^ (N - 1)) hzmul with hu

  let ι : R →+* ℂ := (R.val : R →ₐ[ℤ] ℂ).toRingHom
  have hι : Function.Injective ι := Subtype.val_injective
  have hιu : Units.map (ι : R →* ℂ) u = ζC := by
    ext
    rfl
  have hR0 : (phiAt N data.Φ R).eval (conjR u (jqModC R) t) = 0 := by
    apply coeffMap_injective hι
    rw [map_zero, coeffMap_eval_conjR, hιu, conjR_eq_cosetConj]
    exact hrootC t ht

  have hint : IsIntegral ℤ (ζC : ℂ) := hζC.isIntegral hN
  have hmin : minpoly ℤ (ζC : ℂ) = Polynomial.cyclotomic N ℤ :=
    (Polynomial.cyclotomic_eq_minpoly hζC hN).symm
  have hζroot : Polynomial.eval₂ (Int.castRingHom K) (ζ : K) (minpoly ℤ (ζC : ℂ)) = 0 := by
    rw [hmin, ← Polynomial.eval_map, Polynomial.map_cyclotomic_int]
    exact (IsPrimitiveRoot.coe_units_iff.mpr hζ).isRoot_cyclotomic hN
  let e : AdjoinRoot (minpoly ℤ (ζC : ℂ)) ≃ₐ[ℤ] R := minpoly.equivAdjoin hint
  let φ : R →+* K := (AdjoinRoot.lift (Int.castRingHom K) (ζ : K) hζroot).comp e.symm.toAlgHom.toRingHom
  have heroot : e (AdjoinRoot.root _) = z := by
    have hee : e = minpoly.equivAdjoin hint := rfl
    rw [hee, minpoly.equivAdjoin]
    apply Subtype.ext
    change ((AdjoinRoot.Minpoly.toAdjoin ℤ (ζC : ℂ))
      ((AdjoinRoot.mk (minpoly ℤ (ζC : ℂ))) Polynomial.X)).val = (ζC : ℂ)
    exact AdjoinRoot.Minpoly.coe_toAdjoin_mk_X
  have hφz : φ z = (ζ : K) := by
    show AdjoinRoot.lift (Int.castRingHom K) (ζ : K) hζroot (e.symm z) = ζ
    rw [← heroot, AlgEquiv.symm_apply_apply, AdjoinRoot.lift_root]
  have hφu : Units.map (φ : R →* K) u = ζ := by
    ext
    exact hφz

  have := congrArg (coeffMap φ) hR0
  rw [coeffMap_eval_conjR, hφu, conjR_eq_cosetConj, map_zero] at this
  exact this


/-! ## The conjugates are pairwise distinct

`cosetSubst ζ a b J` is `ζ ^ (a b) q ^ (a a)`-substituted and `q ^ (a a)`-expanded;
the `q ^ (-(a a))` coefficient of it is `(ζ ^ (a b))⁻¹ · J.coeff (-1)`, so distinct
`a`'s give distinct series, and for a fixed `a` the map `b ↦ ζ ^ (a b)` is injective
on `{0, …, d - 1}`. That is the whole engine of the two coset-polynomial rows. -/

namespace CosetPoly

variable {K : Type*} [Field K]

theorem coeff_cosetSubst_neg_sq (ζ : Kˣ) (a b : ℕ) [NeZero a] (J : LaurentSeries K) :
    (cosetSubst ζ a b J).coeff (-((a * a : ℕ) : ℤ)) = ((ζ ^ (a * b)) ^ (-1 : ℤ) : Kˣ) * J.coeff (-1) := by
  show ((qExpand K (a * a)) (qTwist (ζ ^ (a * b)) J)).coeff _ = _
  rw [show (-((a * a : ℕ) : ℤ)) = ((a * a : ℕ) : ℤ) * (-1 : ℤ) by ring, qExpand_coeff_mul,
    qTwist_coeff]

theorem coeff_cosetSubst_of_lt (ζ : Kˣ) (a b : ℕ) [NeZero a] (J : LaurentSeries K)
    (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0) (k : ℤ) (hk : k < -((a * a : ℕ) : ℤ)) :
    (cosetSubst ζ a b J).coeff k = 0 := by
  show ((qExpand K (a * a)) (qTwist (ζ ^ (a * b)) J)).coeff k = 0
  by_cases hdvd : ((a * a : ℕ) : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hdvd
    have hpos : (0 : ℤ) < ((a * a : ℕ) : ℤ) := by
      have : 0 < a * a := Nat.pos_of_ne_zero (NeZero.ne (a * a))
      exact_mod_cast this
    have hm : m < -1 := by
      by_contra h
      push Not at h
      have : ((a * a : ℕ) : ℤ) * (-1) ≤ ((a * a : ℕ) : ℤ) * m :=
        mul_le_mul_of_nonneg_left h hpos.le
      omega
    rw [qExpand_coeff_mul, qTwist_coeff, hJ' m hm, mul_zero]
  · exact qExpand_coeff_of_not_dvd (a * a) _ hdvd

theorem ne_zero_of_mem {N : ℕ} (hN : N ≠ 0) {t : ℕ × ℕ × ℕ} (ht : t ∈ primCosetReps N) :
    t.1 ≠ 0 := by
  obtain ⟨a, b, d⟩ := t
  rw [mem_primCosetReps hN] at ht
  rintro rfl
  exact hN (by simpa using ht.1.symm)

theorem cosetConj_injOn {N : ℕ} (hN : N ≠ 0) (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N)
    (J : LaurentSeries K) (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0)
    {t t' : ℕ × ℕ × ℕ} (ht : t ∈ primCosetReps N) (ht' : t' ∈ primCosetReps N)
    (heq : cosetConj ζ J t = cosetConj ζ J t') : t = t' := by
  obtain ⟨a, b, d⟩ := t
  obtain ⟨a', b', d'⟩ := t'
  have ha0 : a ≠ 0 := ne_zero_of_mem hN ht
  have ha0' : a' ≠ 0 := ne_zero_of_mem hN ht'
  rw [mem_primCosetReps hN] at ht ht'
  obtain ⟨had, hbd, -⟩ := ht
  obtain ⟨had', hbd', -⟩ := ht'
  rw [@cosetConj_eq K _ ζ J a b d ⟨ha0⟩, @cosetConj_eq K _ ζ J a' b' d' ⟨ha0'⟩] at heq

  have key : ∀ {a₁ b₁ a₂ b₂ : ℕ} [NeZero a₁] [NeZero a₂], a₁ < a₂ →
      cosetSubst ζ a₁ b₁ J ≠ cosetSubst ζ a₂ b₂ J := by
    intro a₁ b₁ a₂ b₂ _ _ hlt h
    have h1 := coeff_cosetSubst_neg_sq ζ a₂ b₂ J
    have h2 : (cosetSubst ζ a₁ b₁ J).coeff (-((a₂ * a₂ : ℕ) : ℤ)) = 0 := by
      refine coeff_cosetSubst_of_lt ζ a₁ b₁ J hJ' _ ?_
      have : a₁ * a₁ < a₂ * a₂ := Nat.mul_self_lt_mul_self hlt
      omega
    rw [h] at h2
    rw [h2] at h1
    exact (mul_ne_zero (Units.ne_zero _) hJ) h1.symm
  have haa : a = a' := by
    rcases lt_trichotomy a a' with h | h | h
    · exact absurd heq (@key a b a' b' ⟨ha0⟩ ⟨ha0'⟩ h)
    · exact h
    · exact absurd heq.symm (@key a' b' a b ⟨ha0'⟩ ⟨ha0⟩ h)
  subst haa
  have hdd : d = d' := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) (had.trans had'.symm)
  subst hdd

  have hlead := congrArg (fun f : LaurentSeries K => f.coeff (-((a * a : ℕ) : ℤ))) heq
  simp only [coeff_cosetSubst_neg_sq] at hlead
  have hu : ((ζ ^ (a * b)) ^ (-1 : ℤ) : Kˣ) = (ζ ^ (a * b')) ^ (-1 : ℤ) :=
    Units.ext (mul_right_cancel₀ hJ hlead)
  have hpow : ζ ^ (a * b) = ζ ^ (a * b') := by
    have := congrArg (fun u : Kˣ => u ^ (-1 : ℤ)) hu
    simpa using this

  suffices hmain : ∀ {b₁ b₂ : ℕ}, b₁ < d → b₂ < d → b₁ ≤ b₂ →
      ζ ^ (a * b₁) = ζ ^ (a * b₂) → b₁ = b₂ by
    rcases le_total b b' with h | h
    · rw [hmain hbd hbd' h hpow]
    · rw [hmain hbd' hbd h hpow.symm]
  intro b₁ b₂ _ _ _ h
  have hζu : IsPrimitiveRoot ζ (a * d) := had.symm ▸ hζ
  have h1 : ζ ^ (a * (b₂ - b₁)) = 1 := by
    have hexp : a * b₁ + a * (b₂ - b₁) = a * b₂ := by
      rw [← Nat.mul_add]; congr 1; omega
    have e : ζ ^ (a * b₁) * ζ ^ (a * (b₂ - b₁)) = ζ ^ (a * b₁) * 1 := by
      rw [mul_one, ← _root_.pow_add, hexp, ← h]
    exact mul_left_cancel e
  have hdvd : a * d ∣ a * (b₂ - b₁) := (hζu.pow_eq_one_iff_dvd _).mp h1
  have hdvd' : d ∣ (b₂ - b₁) := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero ha0) hdvd
  have : b₂ - b₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
  omega

end CosetPoly

open CosetPoly

theorem eq_cosetTwoVarPoly_of_forall_isRoot (K : Type*) [Field K] (N : ℕ) (hN : N ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (J : LaurentSeries K)
    (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0)
    (P : Polynomial (LaurentSeries K)) (hP : P.Monic) (hdeg : P.natDegree = (ModularCurve.primCosetReps N).card)
    (hroot : ∀ t ∈ ModularCurve.primCosetReps N, P.IsRoot (ModularCurve.cosetConj ζ J t)) :
    P = ModularCurve.cosetTwoVarPoly ζ N J := by
  classical
  have hmonic : (ModularCurve.cosetTwoVarPoly ζ N J).Monic := by
    unfold ModularCurve.cosetTwoVarPoly
    exact Polynomial.monic_prod_of_monic _ _ (fun t _ => Polynomial.monic_X_sub_C _)
  have hdeg' : (ModularCurve.cosetTwoVarPoly ζ N J).natDegree = (ModularCurve.primCosetReps N).card := by
    unfold ModularCurve.cosetTwoVarPoly
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun t _ => Polynomial.monic_X_sub_C _)]
    simp
  have hdvd : ModularCurve.cosetTwoVarPoly ζ N J ∣ P := by
    unfold ModularCurve.cosetTwoVarPoly
    refine Finset.prod_dvd_of_coprime ?_ ?_
    · intro t ht t' ht' hne
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.mpr ?_))
      exact fun h => hne (cosetConj_injOn hN ζ hζ J hJ hJ' ht ht' h)
    · intro t ht
      exact Polynomial.dvd_iff_isRoot.mpr (hroot t ht)
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic hP hdvd (by rw [hdeg, hdeg'])

theorem separable_cosetTwoVarPoly (K : Type*) [Field K] (N : ℕ) (hN : N ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) (J : LaurentSeries K)
    (hJ : J.coeff (-1) ≠ 0) (hJ' : ∀ m : ℤ, m < -1 → J.coeff m = 0) :
    (ModularCurve.cosetTwoVarPoly ζ N J).Separable := by
  unfold ModularCurve.cosetTwoVarPoly
  refine Polynomial.separable_prod' ?_ (fun t _ => Polynomial.separable_X_sub_C)
  intro t ht t' ht' hne
  refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.mpr ?_))
  exact fun h => hne (cosetConj_injOn hN ζ hζ J hJ hJ' ht ht' h)


/-! ## The `qParam` form of `cosetSubst`

`cosetSubst ζ a b` is `q ↦ ζ ^ (a b) q ^ (a a)`, so the `q`-parameter at level `1`
evaluated at `(a τ + b) / d` is `ζ ^ (a b)` times the level-`N` `q`-parameter at `τ`,
raised to `a * a`. Feeding a `HasSum` through the injective rescaling `m ↦ (a * a) m`
turns the coefficients of `S` into those of `cosetSubst ζ a b S`. -/

namespace CosetQParam

theorem qParam_coset {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (τ : ℂ) :
    Function.Periodic.qParam 1 ((a * τ + b) / d) =
      Complex.exp (2 * Real.pi * Complex.I / N) ^ (a * b) * Function.Periodic.qParam N τ ^ (a * a) := by
  have hd0 : (d : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; exact hN (by simpa using had.symm)
    exact_mod_cast this
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have hNad : (N : ℂ) = a * d := by exact_mod_cast had.symm
  have ha0 : (a : ℂ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; exact hN (by simpa using had.symm)
    exact_mod_cast this
  push_cast
  rw [hNad]
  field_simp
  ring

end CosetQParam

open CosetQParam

theorem hasSum_cosetSubst_coeff_mul_qParam_pow {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N)
    [NeZero a] (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (S : LaurentSeries ℂ) (τ : ℂ) (x : ℂ)
    (h : HasSum (fun m : ℤ => S.coeff m * Function.Periodic.qParam 1 ((a * τ + b) / d) ^ m) x) :
    HasSum (fun m : ℤ => (ModularCurve.cosetSubst ζ a b S).coeff m * Function.Periodic.qParam N τ ^ m) x := by
  set t : ℂ := Function.Periodic.qParam N τ with ht
  set u : ℂˣ := ζ ^ (a * b) with hu
  rw [qParam_coset hN had τ, ← hζ, ← ht] at h

  have hinj : Function.Injective (fun m : ℤ => ((a * a : ℕ) : ℤ) * m) :=
    mul_right_injective₀ (by exact_mod_cast (NeZero.ne (a * a)))
  refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
  · intro k hk
    have hnd : ¬ ((a * a : ℕ) : ℤ) ∣ k := by
      rintro ⟨c, rfl⟩
      exact hk ⟨c, rfl⟩
    show ((qExpand ℂ (a * a)) (qTwist (ζ ^ (a * b)) S)).coeff k * t ^ k = 0
    rw [qExpand_coeff_of_not_dvd (a * a) _ hnd, zero_mul]
  · have hcomp : ((fun m : ℤ => (ModularCurve.cosetSubst ζ a b S).coeff m * t ^ m) ∘
        (fun m : ℤ => ((a * a : ℕ) : ℤ) * m))
        = fun m : ℤ => S.coeff m * ((ζ : ℂ) ^ (a * b) * t ^ (a * a)) ^ m := by
      funext m
      simp only [Function.comp_apply]
      show ((qExpand ℂ (a * a)) (qTwist (ζ ^ (a * b)) S)).coeff (((a * a : ℕ) : ℤ) * m) * t ^ _ = _
      rw [qExpand_coeff_mul, qTwist_coeff, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
        mul_zpow, zpow_mul, zpow_natCast]
      ring
    rw [hcomp]
    exact h

/-! ## The coset translate of a `q`-expansion

The pin's `S_` copy
(`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_qExpansion_cosetTranslate_eq_cosetSubst.lean`,
144 ln): if `G τ = F ((a τ + b) / d)` with `a d = N`, then `G`'s level-`N` `q`-expansion
is the `cosetSubst ζ a b` image of `F`'s level-`1` one.  Three of the four clauses
(`Periodic`, `MDifferentiable`, `IsBoundedAtImInfty`) transport along the coset map; the
last is the coefficient identity, which follows from the two `HasSum` forms
(`hasSum_laurent` at level `N` and the ported
`hasSum_cosetSubst_coeff_mul_qParam_pow` at level `1`) and the canonicity
`laurent_qParam_coeff_unique`.

The pin's `CosetTranslateAux` engine is `private` here: the pin's `S_` file states it in
its own namespace, but it is scaffolding for the row, not part of the port's API. -/

open UpperHalfPlane

namespace CosetTranslate

/-- `τ ↦ (a τ + b) / d` as a point of `ℍ`, for `a`, `d > 0`. -/
def cosetPt (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) : ℍ :=
  ⟨((a : ℂ) * τ + b) / d, by
    rw [Complex.div_natCast_im]
    apply div_pos _ (by exact_mod_cast hd)
    simpa [Complex.add_im, Complex.mul_im] using mul_pos (by exact_mod_cast ha : (0:ℝ) < a) τ.im_pos⟩

theorem coe_cosetPt (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    ((cosetPt a b d ha hd τ : ℍ) : ℂ) = ((a : ℂ) * τ + b) / d := rfl

theorem cosetPt_im (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : ℍ) :
    (cosetPt a b d ha hd τ).im = a * τ.im / d := by
  rw [← UpperHalfPlane.coe_im, coe_cosetPt, Complex.div_natCast_im]
  simp [Complex.add_im, Complex.mul_im]

/-- The pin's `hasSum_laurent`: the level-`h` `q`-expansion of `F`, read in
`LaurentSeries ℂ`, sums to `F τ`. -/
private theorem hasSum_laurent {h : ℝ} (hh : 0 < h) {F : ℍ → ℂ}
    (hper : Function.Periodic (F ∘ ofComplex) h)
    (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F)
    (hbd : UpperHalfPlane.IsBoundedAtImInfty F) (τ : ℍ) :
    HasSum (fun m : ℤ => ((qExpansion h F : PowerSeries ℂ) : LaurentSeries ℂ).coeff m *
      Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ) := by
  have h0 := UpperHalfPlane.hasSum_qExpansion hh hper hhol hbd τ
  refine (Function.Injective.hasSum_iff Nat.cast_injective ?_).mp ?_
  · intro m hm
    rcases m with n | n
    · exact absurd ⟨n, rfl⟩ hm
    · rw [ModularCurve.ofPowerSeries_coeff_of_neg _ (Int.negSucc_lt_zero n), zero_mul]
  · have hcomp : ((fun m : ℤ => ((qExpansion h F : PowerSeries ℂ) : LaurentSeries ℂ).coeff m *
          Function.Periodic.qParam h (τ : ℂ) ^ m) ∘ (Nat.cast : ℕ → ℤ)) =
        fun n : ℕ => (qExpansion h F).coeff n • Function.Periodic.qParam h (τ : ℂ) ^ n := by
      funext n
      simp only [Function.comp_apply, smul_eq_mul, zpow_natCast, LaurentSeries.coeff_coe_powerSeries]
    rw [hcomp]
    exact h0

end CosetTranslate

open CosetTranslate

/-- **The coset translate of a `q`-expansion is the `cosetSubst` image.** -/
theorem qExpansion_cosetTranslate_eq_cosetSubst {N a b d : ℕ} (hN : N ≠ 0)
    (had : a * d = N) [NeZero a] (ζ : ℂˣ)
    (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (F G : ℍ → ℂ) (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F)
    (hFbd : UpperHalfPlane.IsBoundedAtImInfty F)
    (hG : ∀ τ τ' : ℍ, ((τ' : ℂ) = ((a : ℂ) * τ + b) / d) → G τ = F τ') :
    Function.Periodic (G ∘ UpperHalfPlane.ofComplex) N ∧
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G ∧
      UpperHalfPlane.IsBoundedAtImInfty G ∧
      ((qExpansion N G : PowerSeries ℂ) : LaurentSeries ℂ)
        = ModularCurve.cosetSubst ζ a b ((qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by simpa using had.symm))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hGpt : ∀ τ : ℍ, G τ = F (cosetPt a b d ha hd τ) := fun τ => hG τ _ (coe_cosetPt a b d ha hd τ)

  have hGof : ∀ z : ℂ, 0 < z.im → (G ∘ ofComplex) z = (F ∘ ofComplex) (((a : ℂ) * z + b) / d) := by
    intro z hz
    have hz' : 0 < ((((a : ℂ) * z + b) / d)).im := by
      rw [Complex.div_natCast_im]
      apply div_pos _ (by exact_mod_cast hd)
      simpa [Complex.add_im, Complex.mul_im] using mul_pos (by exact_mod_cast ha : (0:ℝ) < a) hz
    simp only [Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.ofComplex_apply_of_im_pos hz', hGpt]
    rfl

  have hper : Function.Periodic (G ∘ UpperHalfPlane.ofComplex) N := by
    intro z
    by_cases hz : 0 < z.im
    · have hzN : 0 < (z + N).im := by simpa using hz
      rw [hGof z hz, hGof (z + N) hzN]
      have : ((a : ℂ) * (z + N) + b) / d = ((a : ℂ) * z + b) / d + ((a * a : ℕ) : ℕ) * (1 : ℝ) := by
        have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
        have hNad : (N : ℂ) = a * d := by exact_mod_cast had.symm
        push_cast
        rw [hNad]
        field_simp
        ring
      rw [this]
      exact hFper.nat_mul (a * a) _
    · push Not at hz
      have hzN : (z + N).im ≤ 0 := by simpa using hz
      simp only [Function.comp_apply]
      rw [UpperHalfPlane.ofComplex_apply_of_im_nonpos hz, UpperHalfPlane.ofComplex_apply_of_im_nonpos hzN]

  have hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) G := by
    rw [UpperHalfPlane.mdifferentiable_iff] at hFhol ⊢
    have haff : DifferentiableOn ℂ (fun z : ℂ => ((a : ℂ) * z + b) / d) {z : ℂ | 0 < z.im} :=
      ((differentiable_id.const_mul _).add_const _).div_const _ |>.differentiableOn
    have hmaps : Set.MapsTo (fun z : ℂ => ((a : ℂ) * z + b) / d) {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz ⊢
      rw [Complex.div_natCast_im]
      apply div_pos _ (by exact_mod_cast hd)
      simpa [Complex.add_im, Complex.mul_im] using mul_pos (by exact_mod_cast ha : (0:ℝ) < a) hz
    refine (hFhol.comp haff hmaps).congr ?_
    intro z hz
    exact hGof z hz

  have hbd : UpperHalfPlane.IsBoundedAtImInfty G := by
    rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hFbd ⊢
    obtain ⟨M, A, hM⟩ := hFbd
    refine ⟨M, max A 0 * d, fun τ hτ => ?_⟩
    rw [hGpt]
    apply hM
    rw [cosetPt_im]
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    rw [le_div_iff₀ hd']
    calc A * d ≤ max A 0 * d := by gcongr; exact le_max_left _ _
      _ ≤ τ.im := hτ
      _ = 1 * τ.im := (one_mul _).symm
      _ ≤ a * τ.im := by gcongr
  refine ⟨hper, hhol, hbd, ?_⟩

  refine ModularCurve.laurent_qParam_coeff_unique N hNpos G _ _ (hasSum_laurent hNpos hper hhol hbd) ?_
  intro τ
  rw [hGpt]
  have h1 := hasSum_laurent one_pos hFper hFhol hFbd (cosetPt a b d ha hd τ)
  rw [coe_cosetPt] at h1
  have := ModularCurve.hasSum_cosetSubst_coeff_mul_qParam_pow hN had ζ hζ _ (τ : ℂ) _
    (by simpa using h1)
  simpa using this

/-! ## The roots of `Φ_N(j(q^N), ·)` at the primitive-coset conjugates

`cosetConj ζ J (a, b, d)` is `J` under `q ↦ ζ^(a b) q^(a a)`.  The row states that the
level-`N` modular polynomial evaluated at `jqModC ℂ` and `q^(N)` vanishes at all of
them, for a primitive `N`-th root `ζ`.

The argument is the pin's.  With `A = q(E₄)`, `D = q(Δ)` and `J = jqModC ℂ`, the
identity `J = A³/D` rewrites the evaluation at `cosetConj ζ J (a, b, d)` as the
`q`-expansion of the finite `ℂ`-linear combination
`∑ c_{i,k} (E₄³)^k Δ^(m-k) ((E₄³ ∘ t)³)^i (Δ ∘ t)^(n-i)`, which is the zero function
by `eval_E4_cube_div_discriminant_coset_eq_zero`; multiplying by `D^m (cosetSubst ζ t D)^n`
(the two denominators, cleared by `pow_mul_div_pow`) makes its `q`-expansion vanish,
and the substitution is injective.

Everything here is at width `h`, because the monomials above are `N`-periodic.  The
width-`1` block of `ModularPolynomialE4Cube` is a specialisation, not a binder
variant, so the pin's `CosetRootFormalAux` prelude is carried at width `h` in
`CosetRoot`; `cosetPt`/`coe_cosetPt` (`CosetTranslate`), `pow_mul_div_pow`
(`DeepCosetAux`), `UpperHalfPlaneAux.qParam_one_eq_pow` and this file's own
`hasSum_laurent` are reused. -/

namespace CosetRoot

open scoped Manifold MatrixGroups

/-- `f` is periodic with period `h`, holomorphic on `ℍ`, and bounded at `i∞`. -/
structure Nice (h : ℝ) (f : ℍ → ℂ) : Prop where
  per : Function.Periodic (f ∘ ofComplex) h
  hol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f
  bdd : IsBoundedAtImInfty f

/-- The width-`h` `q`-expansion of `f` is analytic at `0`. -/
def An (h : ℝ) (f : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction h f) 0

theorem Nice.an {h : ℝ} (hh : 0 < h) {f : ℍ → ℂ} (hf : Nice h f) : An h f :=
  UpperHalfPlane.analyticAt_cuspFunction_zero hh hf.per hf.hol hf.bdd

theorem nice_const (h : ℝ) (c : ℂ) : Nice h (fun _ : ℍ => c) :=
  ⟨fun _ => rfl, mdifferentiable_const, Filter.const_boundedAtFilter _ _⟩

theorem An.mul {h : ℝ} {f g : ℍ → ℂ} (hf : An h f) (hg : An h g) : An h (f * g) := by
  unfold An at *
  rw [UpperHalfPlane.cuspFunction_mul hf.continuousAt hg.continuousAt]
  exact hf.mul hg

theorem An.add {h : ℝ} {f g : ℍ → ℂ} (hf : An h f) (hg : An h g) : An h (f + g) := by
  unfold An at *
  rw [UpperHalfPlane.cuspFunction_add hf.continuousAt hg.continuousAt]
  exact hf.add hg

theorem An.smul {h : ℝ} {f : ℍ → ℂ} (hf : An h f) (c : ℂ) : An h (c • f) := by
  unfold An at *
  rw [UpperHalfPlane.cuspFunction_smul hf.continuousAt]
  exact hf.const_smul

theorem qExpansion_finset_prod {h : ℝ} {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (hs : ∀ l ∈ s, An h (f l))
    (h1 : An h (1 : ℍ → ℂ)) :
    An h (∏ l ∈ s, f l) ∧ qExpansion h (∏ l ∈ s, f l) = ∏ l ∈ s, qExpansion h (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using h1, by simp [UpperHalfPlane.qExpansion_one]⟩
  | insert a s ha ih =>
    obtain ⟨hA, hq⟩ := ih (fun l hl => hs l (Finset.mem_insert_of_mem hl))
    have hfa : An h (f a) := hs a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ⟨hfa.mul hA, by rw [UpperHalfPlane.qExpansion_mul hfa hA, hq]⟩

theorem qExpansion_pow' {h : ℝ} (f : ℍ → ℂ) (hf : An h f) (h1 : An h (1 : ℍ → ℂ)) (p : ℕ) :
    An h (f ^ p) ∧ qExpansion h (f ^ p) = qExpansion h f ^ p := by
  have := qExpansion_finset_prod (Finset.range p) (fun _ => f) (fun _ _ => hf) h1
  simpa [Finset.prod_const, Finset.card_range] using this

theorem qExpansion_finset_sum_smul {h : ℝ} {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → ℍ → ℂ)
    (hs : ∀ l ∈ s, An h (f l)) (h0 : An h (0 : ℍ → ℂ)) :
    An h (∑ l ∈ s, c l • f l) ∧ qExpansion h (∑ l ∈ s, c l • f l) = ∑ l ∈ s, c l • qExpansion h (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using h0, by simp [UpperHalfPlane.qExpansion_zero]⟩
  | insert a s ha ih =>
    obtain ⟨hA, hq⟩ := ih (fun l hl => hs l (Finset.mem_insert_of_mem hl))
    have hfa : An h (c a • f a) := (hs a (Finset.mem_insert_self a s)).smul (c a)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨hfa.add hA, ?_⟩
    rw [UpperHalfPlane.qExpansion_add hfa hA, hq, UpperHalfPlane.qExpansion_smul (hs a (Finset.mem_insert_self a s))]

/-- A level-`1` `Nice` function whose width-`1` `q`-expansion is re-read at width `N`:
the two `q`-expansions agree after the substitution `q ↦ q^N`. -/
theorem nice_qExpansion_base {N : ℕ} [NeZero N] (hN : N ≠ 0) {F : ℍ → ℂ} (hF : Nice 1 F) :
    Nice N F ∧ ((qExpansion N F : PowerSeries ℂ) : LaurentSeries ℂ)
      = qExpand ℂ N ((qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hper : Function.Periodic (F ∘ ofComplex) N := by
    simpa using hF.per.nat_mul N
  have hnice : Nice N F := ⟨hper, hF.hol, hF.bdd⟩
  refine ⟨hnice, ?_⟩
  refine ModularCurve.laurent_qParam_coeff_unique N hNpos F _ _
    (CosetTranslate.hasSum_laurent hNpos hnice.per hnice.hol hnice.bdd) ?_
  intro τ
  have h1 := CosetTranslate.hasSum_laurent one_pos hF.per hF.hol hF.bdd τ
  rw [UpperHalfPlaneAux.qParam_one_eq_pow hN] at h1
  set t := Function.Periodic.qParam N (τ : ℂ) with ht
  set S := ((qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) with hS
  have hinj : Function.Injective (fun m : ℤ => (N : ℤ) * m) := mul_right_injective₀ (by exact_mod_cast hN)
  refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
  · intro k hk
    have hnd : ¬ (N : ℤ) ∣ k := by rintro ⟨r, rfl⟩; exact hk ⟨r, rfl⟩
    rw [qExpand_coeff_of_not_dvd N _ hnd, zero_mul]
  · have hcomp : ((fun k : ℤ => (qExpand ℂ N S).coeff k * t ^ k) ∘ (fun m : ℤ => (N : ℤ) * m))
        = fun m : ℤ => S.coeff m * (t ^ N) ^ m := by
      funext m
      simp only [Function.comp_apply]
      rw [qExpand_coeff_mul, zpow_mul, zpow_natCast]
    rw [hcomp]
    exact h1

theorem nice_of_levelOne {k : ℤ} (F : ModularForm 𝒮ℒ k) : Nice 1 ⇑F := by
  have : Fact (IsCusp OnePoint.infty 𝒮ℒ) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods_SL⟩
  exact ⟨SlashInvariantFormClass.periodic_comp_ofComplex F one_mem_strictPeriods_SL, ModularFormClass.holo F,
    ModularFormClass.bdd_at_infty F⟩

theorem nice_discriminant : Nice 1 ModularForm.discriminant := by
  have : Fact (IsCusp OnePoint.infty 𝒮ℒ) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods_SL⟩
  rw [← CuspForm.coe_discriminant]
  exact ⟨SlashInvariantFormClass.periodic_comp_ofComplex _ one_mem_strictPeriods_SL, ModularFormClass.holo _,
    ModularFormClass.bdd_at_infty _⟩

end CosetRoot

open CosetRoot CosetTranslate

/-- **The coset roots of `Φ_N(j(q^N), ·)` over `ℂ`.** -/
theorem ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) :
    ∃ ζ : ℂˣ, IsPrimitiveRoot ζ N ∧ ∀ t ∈ ModularCurve.primCosetReps N,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℂ))
        (ModularCurve.qExpand ℂ N (ModularCurve.jqModC ℂ)))).IsRoot
        (ModularCurve.cosetConj ζ (ModularCurve.jqModC ℂ) t) := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos

  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / N)) N := Complex.isPrimitiveRoot_exp N hN
  set ζ : ℂˣ := (hprim.isUnit hN).unit with hζdef
  have hζval : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N) := IsUnit.unit_spec _
  refine ⟨ζ, IsPrimitiveRoot.coe_units_iff.mp (by rw [hζval]; exact hprim), ?_⟩
  rintro ⟨a, b, d⟩ ht
  have ht' := ht
  rw [mem_primCosetReps hN] at ht'
  obtain ⟨had, hbd, hgcd⟩ := ht'
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by simpa using had.symm))
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by simpa using had.symm))
  have : NeZero a := ⟨ha.ne'⟩
  rw [cosetConj_eq, Polynomial.IsRoot]

  set A : LaurentSeries ℂ := ((qExpansion 1 (ModularForm.E₄ : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) with hA
  set D : LaurentSeries ℂ := ((qExpansion 1 (ModularForm.discriminant : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    with hD
  set J : LaurentSeries ℂ := jqModC ℂ with hJ
  have hJAD : J = A ^ 3 / D := ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant
  have hD0 : D ≠ 0 := by
    intro h0
    have : J = 0 := by rw [hJAD, h0, div_zero]
    have h1 : J.coeff (-1) = 1 := by
      rw [hJ, jqModC]
      have h := HahnSeries.coeff_single_mul_add (a := (0 : ℤ)) (b := (-1 : ℤ)) (r := (1 : ℂ))
        (x := HahnSeries.ofPowerSeries ℤ ℂ (jNum.map (Int.castRingHom ℂ)))
      rw [zero_add, one_mul] at h
      rw [h]
      have h0' := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (jNum.map (Int.castRingHom ℂ)) 0
      rw [Nat.cast_zero] at h0'
      rw [h0', PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]
    rw [this, HahnSeries.coeff_zero] at h1
    exact zero_ne_one h1
  set cs : LaurentSeries ℂ →+* LaurentSeries ℂ := cosetSubst ζ a b with hcs
  have hcs_inj : Function.Injective cs := by
    have : NeZero (a * a) := ⟨Nat.mul_ne_zero ha.ne' ha.ne'⟩
    show Function.Injective ((qExpand ℂ (a * a)).comp (qTwist (ζ ^ (a * b))))
    exact (qExpand_injective (a * a)).comp (qTwist_injective _)
  have hDN0 : qExpand ℂ N D ≠ 0 := fun h => hD0 (qExpand_injective N (by rw [h, map_zero]))
  have hDC0 : cs D ≠ 0 := fun h => hD0 (hcs_inj (by rw [h, map_zero]))

  set F₁ : ℍ → ℂ := (ModularForm.E₄ : ℍ → ℂ) with hF₁
  set F₂ : ℍ → ℂ := ModularForm.discriminant with hF₂
  set G₁ : ℍ → ℂ := fun τ => F₁ (cosetPt a b d ha hd τ) with hG₁
  set G₂ : ℍ → ℂ := fun τ => F₂ (cosetPt a b d ha hd τ) with hG₂
  have hn1 : Nice 1 F₁ := nice_of_levelOne ModularForm.E₄
  have hn2 : Nice 1 F₂ := nice_discriminant
  obtain ⟨hN1, hq1⟩ := nice_qExpansion_base hN hn1
  obtain ⟨hN2, hq2⟩ := nice_qExpansion_base hN hn2
  have hGspec : ∀ (F G : ℍ → ℂ), (G = fun τ => F (cosetPt a b d ha hd τ)) →
      ∀ τ τ' : ℍ, ((τ' : ℂ) = ((a : ℂ) * τ + b) / d) → G τ = F τ' := by
    intro F G hG τ τ' hτ'
    rw [hG]
    show F (cosetPt a b d ha hd τ) = F τ'
    congr 1
    refine UpperHalfPlane.ext ?_
    simp only [coe_cosetPt]
    exact hτ'.symm
  obtain ⟨hpG1, hhG1, hbG1, hqG1⟩ := ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst hN had ζ hζval F₁ G₁
    hn1.per hn1.hol hn1.bdd (hGspec F₁ G₁ rfl)
  obtain ⟨hpG2, hhG2, hbG2, hqG2⟩ := ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst hN had ζ hζval F₂ G₂
    hn2.per hn2.hol hn2.bdd (hGspec F₂ G₂ rfl)
  have hNG1 : Nice N G₁ := ⟨hpG1, hhG1, hbG1⟩
  have hNG2 : Nice N G₂ := ⟨hpG2, hhG2, hbG2⟩
  have an1 : An N (1 : ℍ → ℂ) := (nice_const N 1).an hNr
  have an0 : An N (0 : ℍ → ℂ) := (nice_const N 0).an hNr

  set n : ℕ := data.Φ.natDegree with hn
  set m : ℕ := (Finset.range (n + 1)).sup (fun i => (data.Φ.coeff i).natDegree) with hm
  have hmi : ∀ i ∈ Finset.range (n + 1), (data.Φ.coeff i).natDegree ≤ m := fun i hi =>
    Finset.le_sup (f := fun i => (data.Φ.coeff i).natDegree) hi
  set c : ℕ → ℕ → ℂ := fun i k => (((data.Φ.coeff i).coeff k : ℤ) : ℂ) with hc
  let idx : Finset (ℕ × ℕ) := Finset.range (n + 1) ×ˢ Finset.range (m + 1)
  have hidx : ∀ p ∈ idx, p.1 ≤ n ∧ p.2 ≤ m := by
    intro p hp
    simp only [idx, Finset.mem_product, Finset.mem_range] at hp
    omega

  set mono : ℕ × ℕ → ℍ → ℂ := fun p => (F₁ ^ 3) ^ p.2 * F₂ ^ (m - p.2) * ((G₁ ^ 3) ^ p.1 * G₂ ^ (n - p.1)) with hmono
  set H : ℍ → ℂ := ∑ p ∈ idx, c p.1 p.2 • mono p with hH
  have hH0 : H = 0 := by
    funext τ
    rw [hH, Finset.sum_apply, Pi.zero_apply]
    have hanal := ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero N data ht τ
      (cosetPt a b d ha hd τ) (coe_cosetPt a b d ha hd τ)
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_self _)] at hanal
    have hd1 : ModularForm.discriminant τ ≠ 0 := ModularForm.discriminant_ne_zero τ
    have hd2 : ModularForm.discriminant (cosetPt a b d ha hd τ) ≠ 0 := ModularForm.discriminant_ne_zero _
    have hterm : ∀ p ∈ idx, (c p.1 p.2 • mono p) τ = ModularForm.discriminant τ ^ m *
        ModularForm.discriminant (cosetPt a b d ha hd τ) ^ n *
        (c p.1 p.2 * ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) ^ p.2 *
          ((ModularForm.E₄ : ℍ → ℂ) (cosetPt a b d ha hd τ) ^ 3 / ModularForm.discriminant (cosetPt a b d ha hd τ)) ^ p.1) := by
      intro p hp
      obtain ⟨hi, hk⟩ := hidx p hp
      simp only [hmono, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul, hG₁, hG₂, hF₁, hF₂]
      rw [show ModularForm.discriminant τ ^ m * ModularForm.discriminant (cosetPt a b d ha hd τ) ^ n *
            (c p.1 p.2 * ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) ^ p.2 *
              ((ModularForm.E₄ : ℍ → ℂ) (cosetPt a b d ha hd τ) ^ 3 / ModularForm.discriminant (cosetPt a b d ha hd τ)) ^ p.1)
          = c p.1 p.2 * (ModularForm.discriminant τ ^ m * ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) ^ p.2) *
            (ModularForm.discriminant (cosetPt a b d ha hd τ) ^ n *
              ((ModularForm.E₄ : ℍ → ℂ) (cosetPt a b d ha hd τ) ^ 3 / ModularForm.discriminant (cosetPt a b d ha hd τ)) ^ p.1) by ring,
        DeepCosetAux.pow_mul_div_pow _ _ hd1 hk, DeepCosetAux.pow_mul_div_pow _ _ hd2 hi]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    suffices hsum : ∑ p ∈ idx, c p.1 p.2 * ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) ^ p.2 *
        ((ModularForm.E₄ : ℍ → ℂ) (cosetPt a b d ha hd τ) ^ 3 / ModularForm.discriminant (cosetPt a b d ha hd τ)) ^ p.1 = 0 by
      rw [hsum, mul_zero]
    rw [← hanal, Finset.sum_product]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (hmi i hi)), Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [hc, eq_intCast]
    try ring

  have anF1 : An N F₁ := hN1.an hNr
  have anF2 : An N F₂ := hN2.an hNr
  have anG1 : An N G₁ := hNG1.an hNr
  have anG2 : An N G₂ := hNG2.an hNr
  have qmono : ∀ p ∈ idx, An N (mono p) ∧ (((qExpansion N (mono p)) : PowerSeries ℂ) : LaurentSeries ℂ)
      = (qExpand ℂ N A ^ 3) ^ p.2 * qExpand ℂ N D ^ (m - p.2) * ((cs A ^ 3) ^ p.1 * cs D ^ (n - p.1)) := by
    intro p hp
    obtain ⟨a3, q3⟩ := qExpansion_pow' F₁ anF1 an1 3
    obtain ⟨a1, q1'⟩ := qExpansion_pow' _ a3 an1 p.2
    obtain ⟨a2, q2'⟩ := qExpansion_pow' F₂ anF2 an1 (m - p.2)
    obtain ⟨b3, r3⟩ := qExpansion_pow' G₁ anG1 an1 3
    obtain ⟨b1, r1'⟩ := qExpansion_pow' _ b3 an1 p.1
    obtain ⟨b2, r2'⟩ := qExpansion_pow' G₂ anG2 an1 (n - p.1)
    refine ⟨(a1.mul a2).mul (b1.mul b2), ?_⟩
    rw [hmono]
    simp only []
    rw [UpperHalfPlane.qExpansion_mul (a1.mul a2) (b1.mul b2), UpperHalfPlane.qExpansion_mul a1 a2,
      UpperHalfPlane.qExpansion_mul b1 b2, q1', q2', r1', r2', q3, r3]
    simp only [PowerSeries.coe_mul, PowerSeries.coe_pow]
    rw [hq1, hq2, hqG1, hqG2]
  have hqH : (((qExpansion N H) : PowerSeries ℂ) : LaurentSeries ℂ)
      = qExpand ℂ N D ^ m * cs D ^ n * ∑ p ∈ idx, HahnSeries.C (c p.1 p.2) * (qExpand ℂ N J) ^ p.2 * (cs J) ^ p.1 := by
    rw [hH]
    obtain ⟨-, hq⟩ := qExpansion_finset_sum_smul idx (fun p => c p.1 p.2) mono (fun p hp => (qmono p hp).1) an0
    rw [hq, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    obtain ⟨hi, hk⟩ := hidx p hp
    rw [PowerSeries.coe_smul, (qmono p hp).2, hJAD, map_div₀, map_pow, map_div₀, map_pow, ← HahnSeries.C_mul_eq_smul]
    rw [show qExpand ℂ N D ^ m * cs D ^ n * (HahnSeries.C (c p.1 p.2) * (qExpand ℂ N A ^ 3 / qExpand ℂ N D) ^ p.2 *
          (cs A ^ 3 / cs D) ^ p.1)
        = HahnSeries.C (c p.1 p.2) * (qExpand ℂ N D ^ m * (qExpand ℂ N A ^ 3 / qExpand ℂ N D) ^ p.2) *
          (cs D ^ n * (cs A ^ 3 / cs D) ^ p.1) by ring,
      DeepCosetAux.pow_mul_div_pow _ _ hDN0 hk, DeepCosetAux.pow_mul_div_pow _ _ hDC0 hi]
    ring

  have hzero : ∑ p ∈ idx, HahnSeries.C (c p.1 p.2) * (qExpand ℂ N J) ^ p.2 * (cs J) ^ p.1 = 0 := by
    have h0 : (((qExpansion N H) : PowerSeries ℂ) : LaurentSeries ℂ) = 0 := by
      rw [hH0, UpperHalfPlane.qExpansion_zero, map_zero]
    rw [hqH] at h0
    exact (mul_eq_zero.mp h0).resolve_left (mul_ne_zero (pow_ne_zero _ hDN0) (pow_ne_zero _ hDC0))

  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_self _)]
  rw [Finset.sum_product] at hzero
  rw [← hzero]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (hmi i hi)), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [hc, eq_intCast]
  rw [← map_intCast (HahnSeries.C : ℂ →+* LaurentSeries ℂ)]
  try ring

/-! ## Separability of `Φ_N` over `K(X)`

The two-variable modular polynomial `Φ_N` is separable after casting its
coefficients to a field `K` in which `N` is invertible: `Φ_N` evaluated at
`X = jqModC` has separable `X`-polynomial, and separability descends along the
transcendental generator `qExpand K N (jqModC K)` of `K(X)`. The transfer
`separable_map_ratFunc_of_transcendental` is the general statement; the coset-root
engine above (`eq_cosetTwoVarPoly_of_forall_isRoot`, `separable_cosetTwoVarPoly`)
supplies its hypothesis over the algebraic closure. -/

namespace IgusaSepAux

/-- Separability descends along a transcendental generator: if `P` evaluated at `x`
is separable over a field `E` containing `F(x)` transcendentally, then `P` is
separable over the rational function field `F(X)`. -/
private theorem separable_map_ratFunc_of_transcendental {F E : Type*} [Field F] [Field E]
    [Algebra F E] (x : E) (hx : Transcendental F x) (P : Polynomial (Polynomial F))
    (h : (P.map (Polynomial.aeval x).toRingHom).Separable) :
    (P.map (algebraMap (Polynomial F) (RatFunc F))).Separable := by
  have hinj : Function.Injective (Polynomial.aeval (R := F) x).toRingHom :=
    fun a b hab => (transcendental_iff_injective.mp hx) hab
  let θ : RatFunc F →+* E := IsFractionRing.lift hinj
  have hθ : θ.comp (algebraMap (Polynomial F) (RatFunc F)) = (Polynomial.aeval x).toRingHom :=
    RingHom.ext fun p => IsFractionRing.lift_algebraMap hinj p
  rw [← Polynomial.separable_map θ, Polynomial.map_map, hθ]
  exact h

/-- The two evaluations of `Φ` agree: casting the inner coefficients from `ℤ` to `K`
and then evaluating at `x : E` is evaluating the `ℤ`-coefficients in `E` at `x`. -/
private theorem map_aeval_comp_mapRingHom_intCast {K E : Type*} [Field K] [CommRing E] [Algebra K E]
    (x : E) (Φ : Polynomial (Polynomial ℤ)) :
    (Φ.map (mapRingHom (Int.castRingHom K))).map (Polynomial.aeval x).toRingHom
      = Φ.map (eval₂RingHom (Int.castRingHom E) x) := by
  rw [Polynomial.map_map]
  refine congrArg (fun f : Polynomial ℤ →+* E => Φ.map f) ?_
  exact Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

/-- The `q`-coefficients of `jqModC` below `q⁻¹` vanish (the pole is simple). -/
private theorem coeff_jqModC_of_lt (R : Type*) [CommRing R] {m : ℤ} (hm : m < -1) :
    (jqModC R).coeff m = 0 := by
  simpa using coeff_jqModC_pow_of_lt R (b := 1) (m := m) (by simpa using hm)

/-- `qExpand` preserves transcendence of `jqModC`. -/
private theorem transcendental_qExpand_jqModC (L : Type*) [Field L] (M : ℕ) [NeZero M] :
    Transcendental L (qExpand L M (jqModC L)) := by
  intro halg
  obtain ⟨p, hp0, hp⟩ := halg
  apply transcendental_jqModC L
  refine ⟨p, hp0, ?_⟩
  have h := Polynomial.aeval_algHom_apply (qExpandAlg L M) (jqModC L) p
  have h' : (qExpandAlg L M) (jqModC L) = qExpand L M (jqModC L) := rfl
  rw [h'] at h
  rw [h] at hp
  exact qExpand_injective M (by rw [map_zero]; exact hp)

end IgusaSepAux

open ModularCurve.IgusaSepAux in
/-- **Separability of `Φ_N` over `K(X)`.**  For a field `K` with `(N : K) ≠ 0`, the
modular polynomial `Φ_N`, with its coefficients cast to `K` and then into the
rational function field `K(X)`, is separable. -/
theorem ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero (K : Type*) [Field K]
    (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (hNK : (N : K) ≠ 0) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N
  let L := AlgebraicClosure K
  let E := LaurentSeries L
  let : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  have : NeZero ((N : ℕ) : K) := ⟨hNK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := N)
  set ζ : Lˣ := (hz.isUnit hN0).unit with hζdef
  have hζ : IsPrimitiveRoot ζ N := by
    rw [← IsPrimitiveRoot.coe_units_iff]
    simpa [hζdef] using hz
  set x : E := qExpand L N (jqModC L) with hx
  set P : Polynomial E := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom E) x) with hP
  have hroots : ∀ t ∈ primCosetReps N, P.IsRoot (cosetConj ζ (jqModC L) t) :=
    ModularCurve.ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex N data
      (ModularCurve.ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex N data)
      L ζ hζ
  have hmonic : P.Monic := data.monic.map _
  have hdeg : P.natDegree = (primCosetReps N).card := by
    rw [hP, (data.monic).natDegree_map, data.natDegree_eq,
      ModularCurve.card_primCosetReps_eq_dedekindPsi N hN0]
  have hPeq : P = cosetTwoVarPoly ζ N (jqModC L) :=
    ModularCurve.eq_cosetTwoVarPoly_of_forall_isRoot L N hN0 ζ hζ (jqModC L)
      (by rw [coeff_jqModC_neg_one]; exact one_ne_zero) (fun m hm => coeff_jqModC_of_lt L hm)
      P hmonic hdeg hroots
  have hPsep : P.Separable := by
    rw [hPeq]
    exact ModularCurve.separable_cosetTwoVarPoly L N hN0 ζ hζ (jqModC L)
      (by rw [coeff_jqModC_neg_one]; exact one_ne_zero) (fun m hm => coeff_jqModC_of_lt L hm)
  have hxK : Transcendental K x := by
    rintro ⟨p, hp0, hp⟩
    apply transcendental_qExpand_jqModC L N
    refine ⟨p.map (algebraMap K L), (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hp0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hp
    convert hp using 2
  apply separable_map_ratFunc_of_transcendental x hxK
  rw [map_aeval_comp_mapRingHom_intCast]
  exact hPsep

end ModularCurve

end
