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
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Analysis.Complex.Periodic
import FLTForHuman.ModularCurve.Defs.PrimCosetReps
import FLTForHuman.ModularCurve.Defs.Polynomial
import FLTForHuman.ModularCurve.Defs.JqCoeff

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

end ModularCurve

end
