/-
The counting argument for `#E[n](K) = n²`.

Ported from `P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean`, pinned
at `aa2d8b3` (sections `PortTorsionSmulFormulaEngine`, `PortGenNetIdentities`,
`PortGenInduction`, `PortGenSmulFormula`, `PortGenCardViaFibers`, `PortGenCard`,
`PortGenCardAll`). See `logs/card-torsion-port.md`.

`isCoprime_ΨSq_succ` is the first place the multiplication bridge is consumed:
`ΨSq n` and `ΨSq (n + 1)` are coprime because a common root would give a point
killed by both `n` and `n + 1`, hence zero — and the bridge
`smul_eq_zero_iff_evalEval_ψ` turns each vanishing into a torsion statement.

The module is named for its subject — the cardinality of the `n`-torsion, as the
port order's `TorsionCard` — rather than for the fibre device it uses. It holds
the whole argument as one narrative, because splitting the fibre engine out would
cut the thread between `ΨSq`-coprimality and the count: separability
(`isCoprime_Φ_ΨSq`, `wronskian_Φ_ΨSq_ne_zero`), the double-fibre engine
(`exists_double_fiber_card`), the odd-`n` and 2-torsion cases, and the assembly
`card_nTorsion` ending in `card_torsion_of_isAlgClosed`.
-/
import FLTForHuman.Elliptic.Bridge
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

open scoped Polynomial Polynomial.Bivariate
open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine

namespace FLTForHuman.Elliptic

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

omit [DecidableEq F] in
/-- On a point of the curve, `(y - negY x y)²` is the value of `Ψ₂Sq`. -/
theorem sub_negY_sq_eq_Ψ₂Sq_eval {x y : F} (e : W.Equation x y) :
    (y - W.negY x y) ^ 2 = (WeierstrassCurve.Ψ₂Sq W).eval x := by
  rw [equation_iff] at e
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination 4 * e

section Gen

open WeierstrassCurve Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable (W : WeierstrassCurve F)

theorem ΨSq_eval_eq_zero_of_preΨ {m : ℕ} {x₀ : K}
    (h : ((W.baseChange K).preΨ (m : ℤ)).eval x₀ = 0) :
    ((W.baseChange K).ΨSq m).eval x₀ = 0 := by
  rw [preΨ_ofNat] at h
  rw [ΨSq_ofNat, eval_mul, eval_pow, h, zero_pow two_ne_zero, zero_mul]

variable [IsAlgClosed K] [DecidableEq K]

/-- `ΨSq n` and `ΨSq (n + 1)` are coprime. -/
theorem isCoprime_ΨSq_succ [W.IsElliptic] (n : ℕ) :
    IsCoprime ((W.baseChange K).ΨSq n) ((W.baseChange K).ΨSq (n + 1)) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
  intro x₀
  by_contra hcon
  push Not at hcon
  obtain ⟨hn0, hn1⟩ := hcon
  rw [coe_aeval_eq_eval] at hn0 hn1
  obtain ⟨y₀, hy₀⟩ := IsAlgClosed.exists_root
    (C (1 : K) * X ^ 2 + C ((W.baseChange K).a₁ * x₀ + (W.baseChange K).a₃) * X +
      C (-(x₀ ^ 3 + (W.baseChange K).a₂ * x₀ ^ 2 + (W.baseChange K).a₄ * x₀ +
        (W.baseChange K).a₆)))
    (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  have heq : (W.baseChange K).toAffine.Equation x₀ y₀ := by
    rw [Affine.equation_iff]
    simp only [IsRoot.def, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hy₀
    linear_combination hy₀
  have hns : (W.baseChange K).toAffine.Nonsingular x₀ y₀ :=
    (Affine.equation_iff_nonsingular).mp heq
  have hψ0 : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ = 0 := by
    have h2 := evalEval_ψ_sq (W.baseChange K) heq (n : ℤ)
    rw [hn0] at h2
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have hψ1 : ((W.baseChange K).ψ ((n : ℤ) + 1)).evalEval x₀ y₀ = 0 := by
    have h2 := evalEval_ψ_sq (W.baseChange K) heq ((n : ℤ) + 1)
    rw [hn1] at h2
    exact (pow_eq_zero_iff two_ne_zero).mp h2
  have h0 : (n : ℤ) • (Affine.Point.some x₀ y₀ hns) = 0 :=
    (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) hns (n : ℤ)).mpr hψ0
  have h1 : ((n : ℤ) + 1) • (Affine.Point.some x₀ y₀ hns) = 0 :=
    (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) hns ((n : ℤ) + 1)).mpr hψ1
  have hP : (Affine.Point.some x₀ y₀ hns : (W.baseChange K).toAffine.Point) = 0 := by
    have hsub := sub_smul ((n : ℤ) + 1) (n : ℤ) (Affine.Point.some x₀ y₀ hns)
    rw [h1, h0, sub_zero, add_sub_cancel_left, one_smul] at hsub
    exact hsub
  exact Affine.Point.some_ne_zero hns hP

end Gen

section Induction

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

/-- FLT's `smul_formula_or_zero`: away from the roots of `ΨSq n` the coordinate
formula holds, and at them `n • P = 0`. -/
theorem smul_formula_or_zero [W.IsElliptic] {n : ℕ} (_hn : 0 < n) {x₀ y₀ : K}
    (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀) :
    (((W.baseChange K).ΨSq n).eval x₀ ≠ 0 →
      ∃ (x' y' : K) (h' : (W.baseChange K).toAffine.Nonsingular x' y'),
        n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = Point.some x' y' h' ∧
          x' * ((W.baseChange K).ΨSq n).eval x₀ = ((W.baseChange K).Φ n).eval x₀) ∧
    (((W.baseChange K).ΨSq n).eval x₀ = 0 →
      n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = 0) := by
  have heq : (W.baseChange K).toAffine.Equation x₀ y₀ := h.left
  have hψsq := evalEval_ψ_sq (W.baseChange K) heq (n : ℤ)
  constructor
  · intro hΨ
    have hψ : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ ≠ 0 := by
      intro h0
      exact hΨ (by rw [← hψsq, h0]; exact zero_pow two_ne_zero)
    have key := zsmul_eq_smulEval (W.baseChange K) h (n : ℤ)
    have hVz : smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 2 ≠ 0 := hψ
    have hV := key ▸ ((n : ℤ) • Jacobian.Point.fromAffine (Point.some x₀ y₀ h)).nonsingular
    have hQeq : ((n : ℤ) • Jacobian.Point.fromAffine (Point.some x₀ y₀ h)) =
        Jacobian.Point.mk hV := Jacobian.Point.ext key
    refine ⟨smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 0 /
        smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 2 ^ 2,
      smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 1 /
        smulEval (W.baseChange K) x₀ y₀ (n : ℤ) 2 ^ 3,
      (Jacobian.nonsingular_of_Z_ne_zero hVz).mp hV, ?_, ?_⟩
    · calc n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point)
          = Jacobian.Point.toAffineAddEquiv (W.baseChange K)
            ((n : ℤ) • Jacobian.Point.fromAffine (Point.some x₀ y₀ h)) := by
            rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply,
              AddEquiv.apply_symm_apply, natCast_zsmul]
        _ = _ := by
            rw [hQeq, Jacobian.Point.toAffineAddEquiv_apply]
            exact Jacobian.Point.toAffineLift_of_Z_ne_zero hVz
    · show ((W.baseChange K).φ (n : ℤ)).evalEval x₀ y₀ /
          ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ ^ 2 *
          ((W.baseChange K).ΨSq (n : ℤ)).eval x₀ =
          ((W.baseChange K).Φ (n : ℤ)).eval x₀
      rw [← hψsq, div_mul_cancel₀ _ (pow_ne_zero 2 hψ), evalEval_φ (W.baseChange K) heq]
  · intro hΨ
    have hψ0 : ((W.baseChange K).ψ (n : ℤ)).evalEval x₀ y₀ = 0 :=
      sq_eq_zero_iff.mp (hψsq.trans hΨ)
    rw [← natCast_zsmul]
    exact (smul_eq_zero_iff_evalEval_ψ (W.baseChange K) h (n : ℤ)).mpr hψ0

theorem smul_x_eq [W.IsElliptic] {n : ℕ} (hn : 0 < n) {x₀ y₀ : K}
    (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀)
    (hns : ((W.baseChange K).ΨSq n).eval x₀ ≠ 0) :
    ∃ (x' y' : K) (h' : (W.baseChange K).toAffine.Nonsingular x' y'),
      n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = Point.some x' y' h' ∧
        x' * ((W.baseChange K).ΨSq n).eval x₀ = ((W.baseChange K).Φ n).eval x₀ :=
  (smul_formula_or_zero W hn h).1 hns

omit [DecidableEq K] in
private lemma eval_ne_of_isCoprime {f g : Polynomial K} (h : IsCoprime f g) {x₀ : K}
    (hf : f.eval x₀ = 0) (hg : g.eval x₀ = 0) : False := by
  obtain ⟨a, b, hab⟩ := h
  have h1 := congrArg (Polynomial.eval x₀) hab
  simp only [eval_add, eval_mul, hf, hg, mul_zero, add_zero, eval_one] at h1
  exact zero_ne_one h1

/-- FLT's `isCoprime_Φ_ΨSq`: the `x`-numerator and the `n`-division polynomial
are coprime, so the `n`-torsion `x`-coordinates are simple roots. -/
theorem isCoprime_Φ_ΨSq [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hn : 0 < n) :
    IsCoprime ((W.baseChange K).Φ n) ((W.baseChange K).ΨSq n) := by
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed (k := K) (K := K)]
  intro x₀
  by_contra hcon
  push Not at hcon
  obtain ⟨hΦ0, hΨ0⟩ := hcon
  rw [coe_aeval_eq_eval] at hΦ0 hΨ0
  have hΦdef : (W.baseChange K).Φ (n : ℤ) =
      X * (W.baseChange K).ΨSq (n : ℤ) -
        (W.baseChange K).preΨ ((n : ℤ) + 1) * (W.baseChange K).preΨ ((n : ℤ) - 1) *
          (if Even (n : ℤ) then 1 else (W.baseChange K).Ψ₂Sq) := rfl
  have h0 : ((W.baseChange K).preΨ ((n : ℤ) + 1)).eval x₀ *
      ((W.baseChange K).preΨ ((n : ℤ) - 1)).eval x₀ *
      (if Even (n : ℤ) then (1 : K) else ((W.baseChange K).Ψ₂Sq).eval x₀) = 0 := by
    have h1 := congrArg (Polynomial.eval x₀) hΦdef
    rw [hΦ0] at h1
    simp only [eval_sub, eval_mul, eval_X, apply_ite (Polynomial.eval x₀), eval_one, hΨ0,
      mul_zero, zero_sub] at h1
    linear_combination h1
  rcases mul_eq_zero.mp h0 with h12 | hG
  · rcases mul_eq_zero.mp h12 with hE | hF
    · have hb : ((W.baseChange K).ΨSq ((n : ℤ) + 1)).eval x₀ = 0 := by
        have h2 := ΨSq_eval_eq_zero_of_preΨ W (m := n + 1) (K := K)
          (by rwa [Nat.cast_add, Nat.cast_one])
        rwa [Nat.cast_add, Nat.cast_one] at h2
      exact eval_ne_of_isCoprime (isCoprime_ΨSq_succ W n) hΨ0 hb
    · have hb : ((W.baseChange K).ΨSq ((n - 1 : ℕ) : ℤ)).eval x₀ = 0 :=
        ΨSq_eval_eq_zero_of_preΨ W (m := n - 1) (K := K)
          (by rwa [Nat.cast_sub hn, Nat.cast_one])
      have hA := isCoprime_ΨSq_succ W (K := K) (n - 1)
      have hc : ((n - 1 : ℕ) : ℤ) + 1 = (n : ℤ) := by omega
      rw [hc] at hA
      exact eval_ne_of_isCoprime hA hb hΨ0
  · by_cases hev : Even (n : ℤ)
    · rw [ite_eq_left hev] at hG
      exact one_ne_zero hG
    · rw [ite_eq_right hev] at hG
      have hnodd : ¬Even n := fun h => hev (by exact_mod_cast h)
      have hb : ((W.baseChange K).ΨSq ((n : ℤ) + 1)).eval x₀ = 0 := by
        have h2 : ((W.baseChange K).ΨSq ((n + 1 : ℕ) : ℤ)).eval x₀ = 0 := by
          rw [ΨSq_ofNat, ite_eq_left (Nat.even_add_one.mpr hnodd), eval_mul, hG, mul_zero]
        rwa [Nat.cast_add, Nat.cast_one] at h2
      exact eval_ne_of_isCoprime (isCoprime_ΨSq_succ W n) hΨ0 hb

theorem smul_eq_zero_of_ΨSq_eval_eq_zero [W.IsElliptic] {n : ℕ} (hn : 0 < n)
    {x₀ y₀ : K} (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀)
    (hz : ((W.baseChange K).ΨSq n).eval x₀ = 0) :
    n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = 0 :=
  (smul_formula_or_zero W hn h).2 hz

end Induction

section Roots

open Polynomial

theorem squarefree_roots_nodup {R : Type*} [CommRing R] [IsDomain R] {p : R[X]}
    (hsq : Squarefree p) : p.roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro a
  rw [count_roots]
  by_contra h
  push Not at h
  have h2 : (X - C a) * (X - C a) ∣ p := by
    calc (X - C a) * (X - C a) = (X - C a) ^ 2 := (sq _).symm
      _ ∣ (X - C a) ^ rootMultiplicity a p := pow_dvd_pow _ h
      _ ∣ p := pow_rootMultiplicity_dvd p a
  exact not_isUnit_X_sub_C a (hsq _ h2)

theorem separable_of_splits_of_squarefree {L : Type*} [Field L] {p : L[X]}
    (hp : p ≠ 0) (hs : p.Splits) (hsq : Squarefree p) : p.Separable :=
  (nodup_roots_iff_of_splits hp hs).mp (squarefree_roots_nodup hsq)

end Roots

section Wronskian

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

omit [DecidableEq K] in
/-- FLT's `wronskian_Φ_ΨSq_ne_zero`: the Wronskian of `Φ n` and `ΨSq n` is
nonzero — the degree bookkeeping that makes `Φ n - c·ΨSq n` squarefree. -/
theorem wronskian_Φ_ΨSq_ne_zero [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    derivative ((W.baseChange K).Φ n) * (W.baseChange K).ΨSq n -
      (W.baseChange K).Φ n * derivative ((W.baseChange K).ΨSq n) ≠ 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain rfl | h2 : n = 1 ∨ 2 ≤ n := by omega
  · simp [Φ_one, ΨSq_one]
  · set E := W.baseChange K with hE
    have hnQ : ((n : ℕ) : K) ≠ 0 := hn
    have hm4 : 4 ≤ n ^ 2 := by nlinarith
    have hFlc : (E.Φ n).coeff (n ^ 2) = 1 := by
      simpa using WeierstrassCurve.coeff_Φ E (n : ℤ)
    have hGlc : (E.ΨSq n).coeff (n ^ 2 - 1) = (n : K) ^ 2 := by
      simpa using WeierstrassCurve.coeff_ΨSq E (n : ℤ)
    have hF'c : (derivative (E.Φ n)).coeff (n ^ 2 - 1) =
        ((n ^ 2 - 1 : ℕ) : K) + 1 := by
      rw [coeff_derivative, Nat.sub_add_cancel (by omega : 1 ≤ n ^ 2), hFlc, one_mul]
    have hG'c : (derivative (E.ΨSq n)).coeff (n ^ 2 - 2) =
        (n : K) ^ 2 * (((n ^ 2 - 2 : ℕ) : K) + 1) := by
      rw [coeff_derivative, (by omega : n ^ 2 - 2 + 1 = n ^ 2 - 1), hGlc]
    have hFdegle : (E.Φ n).natDegree ≤ n ^ 2 := by
      have h := WeierstrassCurve.natDegree_Φ_le E (n : ℤ)
      rwa [Int.natAbs_natCast] at h
    have hGdegle : (E.ΨSq n).natDegree ≤ n ^ 2 - 1 := by
      have h := WeierstrassCurve.natDegree_ΨSq_le E (n : ℤ)
      rwa [Int.natAbs_natCast] at h
    have hF'le : (derivative (E.Φ n)).natDegree ≤ n ^ 2 - 1 := by
      have h := natDegree_derivative_le (E.Φ (n : ℤ))
      omega
    have hG'le : (derivative (E.ΨSq n)).natDegree ≤ n ^ 2 - 2 := by
      have h := natDegree_derivative_le (E.ΨSq (n : ℤ))
      omega
    intro hzero
    have hco : (derivative (E.Φ n) * E.ΨSq n - E.Φ n * derivative (E.ΨSq n)).coeff
        (2 * n ^ 2 - 2) = 0 := by rw [hzero, coeff_zero]
    have e1 : (derivative (E.Φ n) * E.ΨSq n).coeff (2 * n ^ 2 - 2) =
        (((n ^ 2 - 1 : ℕ) : K) + 1) * (n : K) ^ 2 := by
      rw [(by omega : 2 * n ^ 2 - 2 = (n ^ 2 - 1) + (n ^ 2 - 1)),
        coeff_mul_add_eq_of_natDegree_le hF'le hGdegle, hF'c, hGlc]
    have e2 : (E.Φ n * derivative (E.ΨSq n)).coeff (2 * n ^ 2 - 2) =
        1 * ((n : K) ^ 2 * (((n ^ 2 - 2 : ℕ) : K) + 1)) := by
      rw [(by omega : 2 * n ^ 2 - 2 = n ^ 2 + (n ^ 2 - 2)),
        coeff_mul_add_eq_of_natDegree_le hFdegle hG'le, hFlc, hG'c]
    rw [coeff_sub, e1, e2] at hco
    have c1 : ((n ^ 2 - 1 : ℕ) : K) = (n : K) ^ 2 - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n ^ 2)]
      ring
    have c2 : ((n ^ 2 - 2 : ℕ) : K) = (n : K) ^ 2 - 2 := by
      push_cast [Nat.cast_sub (by omega : 2 ≤ n ^ 2)]
      ring
    rw [c1, c2] at hco
    exact pow_ne_zero 2 hnQ (by linear_combination hco)

/-- FLT's `finite_not_squarefree_fiber`: only finitely many `c` make
`Φ n - c·ΨSq n` non-squarefree. -/
theorem finite_not_squarefree_fiber [IsAlgClosed K] [W.IsElliptic] {n : ℕ}
    (hn : (n : K) ≠ 0) :
    {c : K | ¬ Squarefree
      ((W.baseChange K).Φ n - C c * (W.baseChange K).ΨSq n)}.Finite := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  set F' := (W.baseChange K).Φ n with hFdef
  set G := (W.baseChange K).ΨSq n with hGdef
  have hWr : derivative F' * G - F' * derivative G ≠ 0 := wronskian_Φ_ΨSq_ne_zero W hn
  have hroots : {x : K | (derivative F' * G - F' * derivative G).IsRoot x}.Finite :=
    finite_setOfPred_isRoot hWr
  refine Set.Finite.subset (hroots.image (fun x => F'.eval x / G.eval x)) ?_
  intro c hc
  rw [Set.mem_ofPred_eq] at hc
  unfold Squarefree at hc
  push Not at hc
  obtain ⟨q, hq2, hqu⟩ := hc
  have hqdeg : q.degree ≠ 0 := fun h => hqu (isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root q hqdeg
  have hdvd : (X - C x) * (X - C x) ∣ F' - C c * G :=
    dvd_trans (mul_dvd_mul (dvd_iff_isRoot.mpr hx) (dvd_iff_isRoot.mpr hx)) hq2
  obtain ⟨r, hr⟩ := hdvd
  have hpx : (F' - C c * G).eval x = 0 := by rw [hr]; simp
  have hp'x : (derivative (F' - C c * G)).eval x = 0 := by
    rw [hr]
    simp [derivative_mul, derivative_sub, derivative_X, derivative_C]
  have hFx : F'.eval x = c * G.eval x := by
    have h := hpx
    simp only [eval_sub, eval_mul, eval_C] at h
    exact sub_eq_zero.mp h
  have hF'x : (derivative F').eval x = c * (derivative G).eval x := by
    have h := hp'x
    rw [derivative_sub, derivative_C_mul] at h
    simp only [eval_sub, eval_mul, eval_C] at h
    exact sub_eq_zero.mp h
  have hGx : G.eval x ≠ 0 := by
    intro hG0
    have hF0 : F'.eval x = 0 := by rw [hFx, hG0, mul_zero]
    obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W (K := K) hpos
    rw [← hFdef, ← hGdef] at hab
    have h1 := congrArg (Polynomial.eval x) hab
    rw [eval_add, eval_mul, eval_mul, eval_one, hF0, hG0, mul_zero, mul_zero,
      add_zero] at h1
    exact zero_ne_one h1
  refine ⟨x, ?_, ?_⟩
  · show (derivative F' * G - F' * derivative G).IsRoot x
    simp only [IsRoot, eval_sub, eval_mul]
    rw [hFx, hF'x]
    ring
  · show F'.eval x / G.eval x = c
    rw [hFx, mul_div_assoc, div_self hGx, mul_one]

end Wronskian

section FiberEngine

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

/-- FLT's `smul_surjective`: for odd `n` invertible in `K`, multiplication by
`n` is surjective on `E(K)`. -/
theorem smul_surjective [IsAlgClosed K] [W.IsElliptic] {n : ℕ}
    (hn : (n : K) ≠ 0) :
    Function.Surjective (fun P : (W.baseChange K).toAffine.Point => n • P) := by
  have hpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  intro Q
  rcases Q with _ | ⟨xQ, yQ, hQ⟩
  · refine ⟨0, ?_⟩
    show n • (0 : (W.baseChange K).toAffine.Point) = Point.zero
    rw [nsmul_zero]
    exact Point.zero_def
  set F' := (W.baseChange K).Φ n with hFdef
  set G := (W.baseChange K).ΨSq n with hGdef
  have hnQ : ((n : ℕ) : K) ≠ 0 := hn
  have hnZ : (((n : ℕ) : ℤ) : K) ≠ 0 := by exact_mod_cast hnQ
  have hFdeg : F'.natDegree = n ^ 2 := by
    have h := WeierstrassCurve.natDegree_Φ (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hFdef, h]
  have hGdeg : G.natDegree = n ^ 2 - 1 := by
    have h := WeierstrassCurve.natDegree_ΨSq (W.baseChange K) hnZ
    rw [Int.natAbs_natCast] at h
    rw [hGdef, h]
  have h1n : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
  set p : K[X] := F' - C xQ * G with hpdef
  have hpdeg : p.natDegree = n ^ 2 := by
    rw [hpdef]
    rw [natDegree_sub_eq_left_of_natDegree_lt, hFdeg]
    refine lt_of_le_of_lt (natDegree_C_mul_le xQ G) ?_
    rw [hFdeg, hGdeg]
    omega
  have hpdegne : p.degree ≠ 0 := by
    have hpos' : 0 < p.natDegree := by rw [hpdeg]; omega
    exact (natDegree_pos_iff_degree_pos.mp hpos').ne'
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_root p hpdegne
  have hpx : p.eval x₀ = 0 := hx₀
  have hroot : F'.eval x₀ = xQ * G.eval x₀ := by
    rw [hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero] at hpx
    exact hpx
  have hGx : G.eval x₀ ≠ 0 := by
    intro hG0
    have hF0 : F'.eval x₀ = 0 := by rw [hroot, hG0, mul_zero]
    obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W (K := K) hpos
    rw [← hFdef, ← hGdef] at hab
    have h1 := congrArg (Polynomial.eval x₀) hab
    rw [eval_add, eval_mul, eval_mul, eval_one, hF0, hG0, mul_zero, mul_zero,
      add_zero] at h1
    exact zero_ne_one h1
  obtain ⟨y₀, hy₀⟩ : ∃ y : K, (W.baseChange K).toAffine.Equation x₀ y := by
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
      (C 1 * X ^ 2 + C ((W.baseChange K).a₁ * x₀ + (W.baseChange K).a₃) * X
        + C (-(x₀ ^ 3 + (W.baseChange K).a₂ * x₀ ^ 2 + (W.baseChange K).a₄ * x₀ +
            (W.baseChange K).a₆)))
      (by rw [degree_quadratic one_ne_zero]; norm_num)
    refine ⟨y, ?_⟩
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at hy
    linear_combination hy
  have h₀ : (W.baseChange K).toAffine.Nonsingular x₀ y₀ :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hy₀
  obtain ⟨x', y', h', hsmul, hx'⟩ := smul_x_eq W hpos h₀ hGx
  rw [← hFdef, ← hGdef] at hx'
  have hx'Q : x' = xQ := by
    rw [hroot] at hx'
    exact mul_right_cancel₀ hGx hx'
  subst hx'Q
  rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 hQ.1 rfl with rfl | rfl
  · exact ⟨Point.some x₀ y₀ h₀, hsmul⟩
  · have hnegQ : -(Point.some x' yQ hQ : (W.baseChange K).toAffine.Point) =
        Point.some x' ((W.baseChange K).toAffine.negY x' yQ)
          ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr hQ) := Point.neg_some hQ
    have hprev : n • (Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point) =
        -(Point.some x' yQ hQ) := by
      rw [hnegQ]
      exact hsmul
    have hsn : n • -(Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point) =
        -(n • (Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point)) :=
      neg_nsmul (Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point) n
    refine ⟨-(Point.some x₀ y₀ h₀), ?_⟩
    show n • -(Point.some x₀ y₀ h₀ : (W.baseChange K).toAffine.Point) = Point.some x' yQ hQ
    rw [hsn, hprev, neg_neg]

/-- FLT's `card_smul_fiber`: every fiber of `n •` has the cardinality of the
`n`-torsion. FLT's local `nTorsion` wrapper is replaced by mathlib's
`Submodule.torsionBy`. -/
theorem card_smul_fiber [IsAlgClosed K] [W.IsElliptic] {n : ℕ}
    (hn : (n : K) ≠ 0) (Q : (W.baseChange K).toAffine.Point) :
    Nat.card {P : (W.baseChange K).toAffine.Point // n • P = Q} =
      Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) := by
  obtain ⟨P₀, hP₀⟩ := smul_surjective W hn Q
  have hP₀' : n • P₀ = Q := hP₀
  have e : Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n ≃
      {P : (W.baseChange K).toAffine.Point // n • P = Q} := by
    refine Equiv.subtypeEquiv (Equiv.addRight P₀) fun P => ?_
    show (P ∈ Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) ↔ n • (P + P₀) = Q
    have hsa : n • (P + P₀) = n • P + n • P₀ := nsmul_add P P₀ n
    rw [hsa, hP₀']
    constructor
    · intro h
      have h' : n • P = 0 := h
      rw [h', zero_add]
    · intro h
      show n • P = 0
      exact add_right_cancel (h.trans (zero_add Q).symm)
  exact (Nat.card_congr e).symm

end FiberEngine

section AlgClosed

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable [IsAlgClosed K]
variable (W : WeierstrassCurve F)

private noncomputable def qpoly (x : K) : K[X] :=
  X ^ 2 + (C ((W.baseChange K).a₁ * x + (W.baseChange K).a₃) * X +
    C (-(x ^ 3 + (W.baseChange K).a₂ * x ^ 2 + (W.baseChange K).a₄ * x +
      (W.baseChange K).a₆)))

omit [DecidableEq K] [IsAlgClosed K] in
private lemma degree_qpoly (x : K) : (qpoly W x).degree = 2 := by
  have hlt : (C ((W.baseChange K).a₁ * x + (W.baseChange K).a₃) * X +
      C (-(x ^ 3 + (W.baseChange K).a₂ * x ^ 2 + (W.baseChange K).a₄ * x +
        (W.baseChange K).a₆))).degree < ((X : K[X]) ^ 2).degree := by
    refine lt_of_le_of_lt degree_linear_le ?_
    rw [degree_X_pow]
    exact_mod_cast one_lt_two
  unfold qpoly
  rw [degree_add_eq_left_of_degree_lt hlt, degree_X_pow]
  exact Nat.cast_ofNat

omit [DecidableEq K] [IsAlgClosed K] in
private lemma qpoly_ne_zero (x : K) : qpoly W x ≠ 0 := by
  intro h
  have hd := degree_qpoly W x
  rw [h, degree_zero] at hd
  simp at hd

omit [DecidableEq K] [IsAlgClosed K] in
private lemma isRoot_qpoly_iff (x y : K) :
    (qpoly W x).IsRoot y ↔ (W.baseChange K).toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  unfold qpoly
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  constructor <;> intro h <;> linear_combination h

omit [DecidableEq K] in
private lemma exists_equation_y (x : K) :
    ∃ y : K, (W.baseChange K).toAffine.Equation x y := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (qpoly W x)
    (by rw [degree_qpoly]; norm_num)
  exact ⟨y, (isRoot_qpoly_iff W x y).mp hy⟩

private noncomputable def coords : (W.baseChange K).toAffine.Point → K × K
  | .zero => (0, 0)
  | .some x y _ => (x, y)

omit [DecidableEq K] [IsAlgClosed K] in
/-- FLT's `Ψ₂Sq_ne_zero_of_isElliptic`. -/
theorem Ψ₂Sq_ne_zero_of_isElliptic [W.IsElliptic] : (W.baseChange K).Ψ₂Sq ≠ 0 := by
  intro h0
  set E := W.baseChange K with hE
  rw [Ψ₂Sq_eq, Cubic.toPoly_eq_zero_iff] at h0
  have h4 : (4 : K) = 0 := congrArg Cubic.a h0
  have hb₂ : E.b₂ = 0 := congrArg Cubic.b h0
  have hb₆ : E.b₆ = 0 := congrArg Cubic.d h0
  have h2 : (2 : K) = 0 := by
    have h22 : (2 : K) * 2 = 0 := by linear_combination h4
    rcases mul_eq_zero.mp h22 with h | h <;> exact h
  have hΔ : E.Δ = 0 := by
    rw [show E.Δ = -E.b₂ ^ 2 * E.b₈ - 8 * E.b₄ ^ 3 - 27 * E.b₆ ^ 2 +
        9 * E.b₂ * E.b₄ * E.b₆ from rfl]
    linear_combination (-E.b₂ * E.b₈ + 9 * E.b₄ * E.b₆) * hb₂ +
      (-27 * E.b₆) * hb₆ + (-4 * E.b₄ ^ 3) * h2
  exact E.isUnit_Δ.ne_zero hΔ

/-- FLT's `exists_double_fiber_card`: some `Q` has `2 * n ^ 2` preimages under
`n •` counting both signs, which forces `#E[n] = n²`. -/
theorem exists_double_fiber_card [W.IsElliptic] {n : ℕ} (hodd : Odd n)
    (hn : (n : K) ≠ 0) :
    ∃ Q : (W.baseChange K).toAffine.Point,
      Nat.card {P : (W.baseChange K).toAffine.Point // n • P = Q ∨ n • P = -Q} = 2 * n ^ 2 := by
  classical
  have hpos : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  set F' := (W.baseChange K).Φ n with hFdef
  set G := (W.baseChange K).ΨSq n with hGdef
  have hnQ : ((n : ℕ) : K) ≠ 0 := hn
  have hnZ : (((n : ℕ) : ℤ) : K) ≠ 0 := by exact_mod_cast hnQ

  have hB : {c : K | ¬ Squarefree (F' - C c * G)}.Finite := finite_not_squarefree_fiber W hn
  have hΨ₂ne : (W.baseChange K).Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero_of_isElliptic W
  have hB' : ((fun x => F'.eval x / G.eval x) ''
      {x : K | (W.baseChange K).Ψ₂Sq.IsRoot x}).Finite :=
    (finite_setOfPred_isRoot hΨ₂ne).image _
  obtain ⟨c, hc⟩ := (hB.union hB').infinite_compl.nonempty
  rw [Set.mem_compl_iff, Set.mem_union] at hc
  push Not at hc
  obtain ⟨hcB, hcB'⟩ := hc
  have hsqf : Squarefree (F' - C c * G) := not_not.mp hcB

  obtain ⟨yQ, hyQ⟩ := exists_equation_y W c
  have hQns : (W.baseChange K).toAffine.Nonsingular c yQ :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp hyQ
  refine ⟨Point.some c yQ hQns, ?_⟩
  set p : K[X] := F' - C c * G with hpdef

  have hFdeg : F'.natDegree = n ^ 2 := by
    have h := WeierstrassCurve.natDegree_Φ (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hFdef, h]
  have hGdeg : G.natDegree = n ^ 2 - 1 := by
    have h := WeierstrassCurve.natDegree_ΨSq (W.baseChange K) hnZ
    rw [Int.natAbs_natCast] at h
    rw [hGdef, h]
  have hpdeg : p.natDegree = n ^ 2 := by
    rw [hpdef]
    rw [natDegree_sub_eq_left_of_natDegree_lt, hFdeg]
    refine lt_of_le_of_lt (natDegree_C_mul_le c G) ?_
    rw [hFdeg, hGdeg]
    have : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
    omega
  have hpco : p.coeff (n ^ 2) = 1 := by
    have hF1 : F'.coeff (n ^ 2) = 1 := by
      have h := WeierstrassCurve.coeff_Φ (W.baseChange K) (n : ℤ)
      rw [Int.natAbs_natCast] at h
      rw [hFdef, h]
    have hG0 : G.coeff (n ^ 2) = 0 := by
      refine coeff_eq_zero_of_natDegree_lt ?_
      rw [hGdeg]
      have : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
      omega
    rw [hpdef, coeff_sub, coeff_C_mul, hF1, hG0, mul_zero, sub_zero]
  have hpne : p ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hpco
    exact zero_ne_one hpco

  have hnodup : p.roots.Nodup := squarefree_roots_nodup hsqf
  have hroots_card : p.roots.toFinset.card = n ^ 2 := by
    rw [Multiset.toFinset_card_of_nodup hnodup,
      ← (IsAlgClosed.splits p).natDegree_eq_card_roots, hpdeg]

  have key_F : ∀ x : K, p.eval x = 0 → F'.eval x = c * G.eval x := by
    intro x hx
    rw [hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero] at hx
    exact hx
  have key_G : ∀ x : K, p.eval x = 0 → G.eval x ≠ 0 := by
    intro x hx hG0
    have hF0 : F'.eval x = 0 := by rw [key_F x hx, hG0, mul_zero]
    obtain ⟨a, b, hab⟩ := isCoprime_Φ_ΨSq W (K := K) hpos
    rw [← hFdef, ← hGdef] at hab
    have h1 := congrArg (Polynomial.eval x) hab
    rw [eval_add, eval_mul, eval_mul, eval_one, hF0, hG0, mul_zero, mul_zero,
      add_zero] at h1
    exact zero_ne_one h1
  have key_Ψ₂ : ∀ x : K, p.eval x = 0 → (W.baseChange K).Ψ₂Sq.eval x ≠ 0 := by
    intro x hx h2
    refine hcB' ⟨x, h2, ?_⟩
    show F'.eval x / G.eval x = c
    rw [key_F x hx, mul_div_assoc, div_self (key_G x hx), mul_one]

  set R2fin : Finset (K × K) := p.roots.toFinset.biUnion
    (fun x => (qpoly W x).roots.toFinset.image (fun y => (x, y))) with hR2def
  have hmemR2 : ∀ z : K × K, z ∈ R2fin ↔
      p.eval z.1 = 0 ∧ (W.baseChange K).toAffine.Equation z.1 z.2 := by
    intro z
    rw [hR2def, Finset.mem_biUnion]
    constructor
    · rintro ⟨x, hx, hz⟩
      rw [Finset.mem_image] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [Multiset.mem_toFinset, mem_roots hpne] at hx
      rw [Multiset.mem_toFinset, mem_roots (qpoly_ne_zero W x)] at hy
      exact ⟨hx, (isRoot_qpoly_iff W x y).mp hy⟩
    · rintro ⟨h1, h2⟩
      refine ⟨z.1, ?_, ?_⟩
      · rw [Multiset.mem_toFinset, mem_roots hpne]
        exact h1
      · rw [Finset.mem_image]
        exact ⟨z.2, by
          rw [Multiset.mem_toFinset, mem_roots (qpoly_ne_zero W z.1)]
          exact (isRoot_qpoly_iff W z.1 z.2).mpr h2, rfl⟩

  have hfiber2 : ∀ x ∈ p.roots.toFinset,
      ((qpoly W x).roots.toFinset.image (fun y => (x, y))).card = 2 := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hpne] at hx
    obtain ⟨y₀, hy₀⟩ := exists_equation_y W x
    have hny₀ : (W.baseChange K).toAffine.Equation x
        ((W.baseChange K).toAffine.negY x y₀) :=
      (WeierstrassCurve.Affine.equation_neg x y₀).mpr hy₀
    have hyne : y₀ ≠ (W.baseChange K).toAffine.negY x y₀ := by
      intro hy
      refine key_Ψ₂ x hx ?_
      have hsq := sub_negY_sq_eq_Ψ₂Sq_eval ((W.baseChange K).toAffine) hy₀
      rw [← hsq, ← hy, sub_self]
      ring
    rw [Finset.card_image_of_injective _ (fun a b hab => (Prod.ext_iff.mp hab).2)]
    refine le_antisymm ?_ ?_
    · refine le_trans (Multiset.toFinset_card_le _) (le_trans (card_roots' _) ?_)
      rw [natDegree_eq_of_degree_eq_some (degree_qpoly W x)]
    · have hsub : ({y₀, (W.baseChange K).toAffine.negY x y₀} : Finset K) ⊆
          (qpoly W x).roots.toFinset := by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rw [Multiset.mem_toFinset, mem_roots (qpoly_ne_zero W x)]
        rcases hy with rfl | rfl
        · exact (isRoot_qpoly_iff W x y).mpr hy₀
        · exact (isRoot_qpoly_iff W x _).mpr hny₀
      calc 2 = ({y₀, (W.baseChange K).toAffine.negY x y₀} : Finset K).card :=
            (Finset.card_pair hyne).symm
        _ ≤ _ := Finset.card_le_card hsub

  have hR2card : R2fin.card = 2 * n ^ 2 := by
    rw [hR2def, Finset.card_biUnion]
    · rw [Finset.sum_congr rfl hfiber2, Finset.sum_const, smul_eq_mul, hroots_card,
        mul_comm]
    · intro x₁ hx₁ x₂ hx₂ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      rintro z hz₁ hz₂
      rw [Finset.mem_image] at hz₁ hz₂
      obtain ⟨y₁, -, rfl⟩ := hz₁
      obtain ⟨y₂, -, hz⟩ := hz₂
      exact hne ((Prod.ext_iff.mp hz).1.symm)

  set Q : (W.baseChange K).toAffine.Point := Point.some c yQ hQns with hQdef
  have hQ0 : Q ≠ 0 := Point.some_ne_zero hQns
  have hnegQ : -Q = Point.some c ((W.baseChange K).toAffine.negY c yQ)
      ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr hQns) := Point.neg_some hQns
  have hPne0 : ∀ P : (W.baseChange K).toAffine.Point, (n • P = Q ∨ n • P = -Q) → P ≠ 0 := by
    rintro P hP rfl
    rw [nsmul_zero] at hP
    rcases hP with h | h
    · exact hQ0 h.symm
    · exact hQ0 (neg_eq_zero.mp h.symm)

  have hmaps : Set.MapsTo (coords W) {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q}
      ↑R2fin := by
    rintro P hP
    have hP0 : P ≠ 0 := hPne0 P hP
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd Point.zero_def.symm hP0
    · have hP' : n • (Point.some x y h : (W.baseChange K).toAffine.Point) = Q ∨
          n • (Point.some x y h : (W.baseChange K).toAffine.Point) = -Q := hP
      have hGx : G.eval x ≠ 0 := by
        intro hG0
        have hz : n • (Point.some x y h : (W.baseChange K).toAffine.Point) = 0 :=
          smul_eq_zero_of_ΨSq_eval_eq_zero W hpos h hG0
        rw [hz] at hP'
        rcases hP' with h' | h'
        · exact hQ0 h'.symm
        · exact hQ0 (neg_eq_zero.mp h'.symm)
      obtain ⟨x', y', h', hsmul, hx'⟩ := smul_x_eq W hpos h hGx
      have hx'c : x' = c := by
        rw [hsmul] at hP'
        rcases hP' with h'' | h''
        · rw [hQdef] at h''
          exact (Point.some.inj h'').1
        · rw [hnegQ] at h''
          exact (Point.some.inj h'').1
      have hpx : p.eval x = 0 := by
        rw [hpdef, eval_sub, eval_mul, eval_C, sub_eq_zero, ← hx'c]
        exact hx'.symm
      rw [Finset.mem_coe, hmemR2]
      exact ⟨hpx, h.1⟩
  have hinj : Set.InjOn (coords W)
      {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q} := by
    rintro P₁ hP₁ P₂ hP₂ hco
    rcases P₁ with _ | ⟨x₁, y₁, h₁⟩
    · exact absurd Point.zero_def.symm (hPne0 _ hP₁)
    · rcases P₂ with _ | ⟨x₂, y₂, h₂⟩
      · exact absurd Point.zero_def.symm (hPne0 _ hP₂)
      · simp only [coords] at hco
        obtain ⟨hx, hy⟩ := Prod.ext_iff.mp hco
        subst hx
        subst hy
        rfl
  have hsurj : Set.SurjOn (coords W)
      {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q} ↑R2fin := by
    rintro z hz
    rw [Finset.mem_coe, hmemR2] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨x, y⟩ := z
    have h : (W.baseChange K).toAffine.Nonsingular x y :=
      WeierstrassCurve.Affine.equation_iff_nonsingular.mp hz2
    have hGx : G.eval x ≠ 0 := key_G x hz1
    obtain ⟨x', y', h', hsmul, hx'⟩ := smul_x_eq W hpos h hGx
    have hx'c : x' = c := by
      have hFc := key_F x hz1
      rw [hFc] at hx'
      exact mul_right_cancel₀ hGx hx'
    subst hx'c
    have hy' := WeierstrassCurve.Affine.Y_eq_of_X_eq h'.1 hQns.1 rfl
    refine ⟨Point.some x y h, ?_, rfl⟩
    rcases hy' with rfl | rfl
    · exact Or.inl hsmul
    · refine Or.inr ?_
      rw [hnegQ]
      exact hsmul

  have hbij : Set.BijOn (coords W) {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q}
      ↑R2fin := ⟨hmaps, hinj, hsurj⟩
  calc Nat.card {P : (W.baseChange K).toAffine.Point // n • P = Q ∨ n • P = -Q}
      = Set.ncard {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q} :=
        Nat.card_coe_set_eq _
    _ = (coords W '' {P : (W.baseChange K).toAffine.Point | n • P = Q ∨ n • P = -Q}).ncard :=
        (hbij.injOn.ncard_image).symm
    _ = (↑R2fin : Set (K × K)).ncard := by rw [hbij.image_eq]
    _ = R2fin.card := Set.ncard_coe_finset _
    _ = 2 * n ^ 2 := hR2card

/-- FLT's `card_nTorsion_odd_fibers`: for odd `n` the `n`-torsion has exactly
`n²` elements. FLT's local `nTorsion` is replaced by `Submodule.torsionBy`. -/
theorem card_nTorsion_odd_fibers [W.IsElliptic] {n : ℕ} (hodd : Odd n)
    (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) = n ^ 2 := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨Q, hQ⟩ := exists_double_fiber_card W hodd hn
  by_cases hQQ : Q = -Q
  · exfalso
    simp only [← hQQ, or_self] at hQ
    rw [card_smul_fiber W hn Q] at hQ
    have hfin : Finite (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [hQ]
      exact mul_ne_zero two_ne_zero (pow_ne_zero 2 hn0)
    have hdvd : 2 ∣ Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) := by
      rw [hQ]; exact dvd_mul_right 2 _
    have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' 2 hdvd
    have hcoe : addOrderOf ((g : (W.baseChange K).toAffine.Point)) = 2 :=
      (AddSubgroup.addOrderOf_coe
        (H := (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n).toAddSubgroup)
        g).trans hg
    have hgn : n • (g : (W.baseChange K).toAffine.Point) = 0 := g.2
    have hdvdn : addOrderOf (g : (W.baseChange K).toAffine.Point) ∣ n :=
      addOrderOf_dvd_of_nsmul_eq_zero hgn
    rw [hcoe] at hdvdn
    have hodd' := Nat.odd_iff.mp hodd
    omega
  · have hdisj : Disjoint (fun P : (W.baseChange K).toAffine.Point => n • P = Q)
        (fun P : (W.baseChange K).toAffine.Point => n • P = -Q) := by
      rw [Pi.disjoint_iff]
      intro P
      rw [Prop.disjoint_iff]
      rintro ⟨h1, h2⟩
      exact hQQ (h1 ▸ h2)
    have e := subtypeOrEquiv (fun P : (W.baseChange K).toAffine.Point => n • P = Q)
      (fun P : (W.baseChange K).toAffine.Point => n • P = -Q) hdisj
    rw [Nat.card_congr e] at hQ
    have hfinsum : Finite ({P : (W.baseChange K).toAffine.Point // n • P = Q} ⊕
        {P : (W.baseChange K).toAffine.Point // n • P = -Q}) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [hQ]
      exact mul_ne_zero two_ne_zero (pow_ne_zero 2 hn0)
    have hfinQ : Finite {P : (W.baseChange K).toAffine.Point // n • P = Q} :=
      Finite.of_injective
        (Sum.inl : {P : (W.baseChange K).toAffine.Point // n • P = Q} →
          {P : (W.baseChange K).toAffine.Point // n • P = Q} ⊕
            {P : (W.baseChange K).toAffine.Point // n • P = -Q})
        Sum.inl_injective
    have hfinQ' : Finite {P : (W.baseChange K).toAffine.Point // n • P = -Q} :=
      Finite.of_injective
        (Sum.inr : {P : (W.baseChange K).toAffine.Point // n • P = -Q} →
          {P : (W.baseChange K).toAffine.Point // n • P = Q} ⊕
            {P : (W.baseChange K).toAffine.Point // n • P = -Q})
        Sum.inr_injective
    rw [Nat.card_sum, card_smul_fiber W hn Q, card_smul_fiber W hn (-Q),
      ← two_mul] at hQ
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hQ

omit [IsAlgClosed K] in
theorem mem_nTorsion_two_iff {x y : K} (h : (W.baseChange K).toAffine.Nonsingular x y) :
    (Point.some x y h : (W.baseChange K).toAffine.Point) ∈
      Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 2 ↔
      y = (W.baseChange K).toAffine.negY x y := by
  show 2 • (Point.some x y h : (W.baseChange K).toAffine.Point) = 0 ↔ _
  rw [two_nsmul, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq]
  simp

/-- FLT's `card_nTorsion_two`: the 2-torsion has 4 elements when `2 ≠ 0`. -/
theorem card_nTorsion_two [W.IsElliptic] (h2 : (2 : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 2) = 4 := by
  classical
  set E := W.baseChange K with hE
  have ha : E.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : K) ≠ 0
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have hd : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero_of_isElliptic (isUnit_iff_ne_zero.mpr h2)
  have hsplits : (E.twoTorsionPolynomial.toPoly.map (RingHom.id K)).Splits := by
    rw [Polynomial.map_id]; exact IsAlgClosed.splits _
  have hmap : Cubic.map (RingHom.id K) E.twoTorsionPolynomial = E.twoTorsionPolynomial := rfl
  have hcard3 : E.twoTorsionPolynomial.roots.toFinset.card = 3 := by
    have h := Cubic.card_roots_of_discr_ne_zero ha hsplits hd
    rwa [hmap] at h
  have hroot_iff : ∀ x : K, x ∈ E.twoTorsionPolynomial.roots ↔
      4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ = 0 :=
    fun x => Cubic.mem_roots_iff (Cubic.ne_zero_of_a_ne_zero ha) x
  set yy : K → K := fun x => -(E.a₁ * x + E.a₃) / 2 with hyy
  have hyneg : ∀ x : K, yy x = E.toAffine.negY x (yy x) := by
    intro x
    simp only [hyy, WeierstrassCurve.Affine.negY]
    field_simp
    ring
  have hEq : ∀ x : K, 4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ = 0 →
      E.toAffine.Equation x (yy x) := by
    intro x hx
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [hyy]
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hx
    field_simp
    linear_combination -hx
  have hEval : ∀ x y : K, E.toAffine.Equation x y → y = E.toAffine.negY x y →
      (4 * x ^ 3 + E.b₂ * x ^ 2 + 2 * E.b₄ * x + E.b₆ = 0 ∧ y = yy x) := by
    intro x y heq hy
    rw [WeierstrassCurve.Affine.equation_iff] at heq
    simp only [WeierstrassCurve.Affine.negY] at hy
    have hy2 : 2 * y + E.a₁ * x + E.a₃ = 0 := by linear_combination hy
    constructor
    · simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
      linear_combination (-4 : K) * heq + (2 * y + E.a₁ * x + E.a₃) * hy2
    · simp only [hyy]
      field_simp
      linear_combination hy2
  have hns : ∀ x ∈ E.twoTorsionPolynomial.roots.toFinset, E.toAffine.Nonsingular x (yy x) :=
    fun x hx =>
      WeierstrassCurve.Affine.equation_iff_nonsingular.mp
        (hEq x ((hroot_iff x).mp (Multiset.mem_toFinset.mp hx)))
  set T : Finset (W.baseChange K).toAffine.Point :=
    insert 0 ((E.twoTorsionPolynomial.roots.toFinset.attach).image
      fun p => Point.some p.1 (yy p.1) (hns p.1 p.2)) with hT
  have hsetEq : ((Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 2 :
      Submodule ℤ ((W.baseChange K).toAffine.Point)) : Set ((W.baseChange K).toAffine.Point)) = ↑T := by
    ext P
    rw [SetLike.mem_coe, Finset.mem_coe, hT, Finset.mem_insert, Finset.mem_image]
    cases P with
    | zero =>
      exact iff_of_true (Submodule.zero_mem _) (Or.inl rfl)
    | @some x y h =>
      rw [mem_nTorsion_two_iff]
      constructor
      · intro hy
        obtain ⟨hx0, hyx⟩ := hEval x y h.left hy
        refine Or.inr ⟨⟨x, Multiset.mem_toFinset.mpr ((hroot_iff x).mpr hx0)⟩,
          Finset.mem_attach _ _, ?_⟩
        simp [hyx.symm]
      · rintro (h0 | ⟨⟨x', hx'⟩, -, hPeq⟩)
        · exact absurd h0 (Point.some_ne_zero h)
        · rw [Point.some.injEq] at hPeq
          obtain ⟨hxx, hyy'⟩ := hPeq
          subst hxx
          rw [← hyy']
          exact hyneg x'
  have hcount : Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 2) =
      ((Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 2 :
        Set ((W.baseChange K).toAffine.Point))).ncard :=
    Nat.card_coe_set_eq _
  rw [hcount, hsetEq, Set.ncard_coe_finset]
  have h0T : (0 : (W.baseChange K).toAffine.Point) ∉
      (E.twoTorsionPolynomial.roots.toFinset.attach).image
        (fun p => Point.some p.1 (yy p.1) (hns p.1 p.2)) := by
    simp only [Finset.mem_image]
    rintro ⟨p, -, hp⟩
    exact Point.some_ne_zero _ hp
  rw [hT, Finset.card_insert_of_notMem h0T, Finset.card_image_of_injOn, Finset.card_attach,
    hcard3]
  intro p _ q _ hpq
  rw [Point.some.injEq] at hpq
  exact Subtype.ext hpq.left

omit [IsAlgClosed K] in
theorem card_nTorsion_one :
    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 1) = 1 := by
  have hbot : Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 1 = ⊥ := by
    ext P
    rw [Submodule.mem_bot]
    show 1 • P = 0 ↔ P = 0
    rw [one_nsmul]
  rw [hbot]
  exact AddSubgroup.card_bot

/-- FLT's `card_nTorsion_prime`. -/
theorem card_nTorsion_prime [W.IsElliptic] {p : ℕ} (hp : p.Prime) (hn : (p : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) p) = p ^ 2 := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num,
      card_nTorsion_two W (by exact_mod_cast hn)]
    norm_num
  · exact card_nTorsion_odd_fibers W hodd hn

/-- FLT's `card_nTorsion_prime_pow`. -/
theorem card_nTorsion_prime_pow [W.IsElliptic] {p : ℕ} (hp : p.Prime)
    (hn : (p : K) ≠ 0) (k : ℕ) :
    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) (p ^ k)) = p ^ (2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpk : ((p ^ k : ℕ) : K) ≠ 0 := by push_cast; exact pow_ne_zero _ hn
    have hpfin : Finite (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) p) := by
      refine Nat.finite_of_card_ne_zero ?_
      rw [card_nTorsion_prime W hp hn]
      exact pow_ne_zero 2 hp.pos.ne'
    have hft : Fintype (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) p) :=
      Fintype.ofFinite _
    have hfib : ∀ Q : (W.baseChange K).toAffine.Point,
        Nat.card {P : (W.baseChange K).toAffine.Point // p ^ k • P = Q} =
        Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) (p ^ k)) :=
      fun Q => card_smul_fiber W hpk Q
    have hfibfin : ∀ Q : Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) p,
        Finite {P : (W.baseChange K).toAffine.Point //
          p ^ k • P = (Q : (W.baseChange K).toAffine.Point)} := by
      intro Q
      refine Nat.finite_of_card_ne_zero ?_
      rw [hfib, ih]
      exact pow_ne_zero _ hp.pos.ne'
    have e : Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) (p ^ (k + 1)) ≃
        Σ Q : Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) p,
          {P : (W.baseChange K).toAffine.Point //
            p ^ k • P = (Q : (W.baseChange K).toAffine.Point)} := by
      refine ⟨fun P => ⟨⟨p ^ k • (P : (W.baseChange K).toAffine.Point), ?_⟩,
          ⟨(P : (W.baseChange K).toAffine.Point), rfl⟩⟩,
        fun x => ⟨x.2.1, ?_⟩, fun P => ?_, fun x => ?_⟩
      · show p • (p ^ k • (P : (W.baseChange K).toAffine.Point)) = 0
        rw [smul_smul, ← pow_succ']
        exact P.2
      · show p ^ (k + 1) • (x.2.1 : (W.baseChange K).toAffine.Point) = 0
        rw [pow_succ', ← smul_smul, x.2.2]
        exact x.1.2
      · exact Subtype.ext rfl
      · obtain ⟨⟨Qv, hQ⟩, ⟨P, hP⟩⟩ := x
        dsimp only at hP
        subst hP
        rfl
    rw [Nat.card_congr e, Nat.card_sigma]
    have hsum : ∀ Q : Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) p,
        Nat.card {P : (W.baseChange K).toAffine.Point //
          p ^ k • P = (Q : (W.baseChange K).toAffine.Point)} = p ^ (2 * k) :=
      fun Q => (hfib _).trans ih
    rw [Finset.sum_congr rfl (fun Q _ => hsum Q), Finset.sum_const, smul_eq_mul,
      Finset.card_univ, ← Nat.card_eq_fintype_card, card_nTorsion_prime W hp hn,
      ← pow_add]
    congr 1
    omega

end AlgClosed

section Coprime

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

/-- FLT's `card_nTorsion_mul_of_coprime`: the CRT decomposition of the torsion. -/
theorem card_nTorsion_mul_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) :
    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) (m * n)) =
      Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) m) *
        Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) := by
  set a : ℤ := Nat.gcdA m n with ha
  set b : ℤ := Nat.gcdB m n with hb
  have hBez : (m : ℤ) * a + (n : ℤ) * b = 1 := by
    have h := Nat.gcd_eq_gcd_ab m n
    rw [hmn.gcd_eq_one] at h
    exact_mod_cast h.symm
  have e : Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) (m * n) ≃
      Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) m ×
        Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n := by
    refine ⟨fun P => (⟨((n : ℤ) * b) • (P : (W.baseChange K).toAffine.Point), ?_⟩,
        ⟨((m : ℤ) * a) • (P : (W.baseChange K).toAffine.Point), ?_⟩),
      fun x => ⟨(x.1 : (W.baseChange K).toAffine.Point) +
        (x.2 : (W.baseChange K).toAffine.Point), ?_⟩,
      fun P => ?_, fun x => ?_⟩
    ·
      have hP : ((m : ℤ) * (n : ℤ)) • (P : (W.baseChange K).toAffine.Point) = 0 :=
        (Submodule.mem_torsionBy_iff ((m : ℤ) * (n : ℤ)) (P : (W.baseChange K).toAffine.Point)).mp P.2
      calc m • (((n : ℤ) * b) • (P : (W.baseChange K).toAffine.Point))
          = (m : ℤ) • (((n : ℤ) * b) • (P : (W.baseChange K).toAffine.Point)) := by
            rw [natCast_zsmul]
        _ = ((m : ℤ) * ((n : ℤ) * b)) • (P : (W.baseChange K).toAffine.Point) := by
            rw [smul_smul]
        _ = (b * ((m : ℤ) * (n : ℤ))) • (P : (W.baseChange K).toAffine.Point) := by
            rw [show (m : ℤ) * ((n : ℤ) * b) = b * ((m : ℤ) * (n : ℤ)) by ring]
        _ = b • (((m : ℤ) * (n : ℤ)) • (P : (W.baseChange K).toAffine.Point)) := by
            rw [smul_smul]
        _ = 0 := by rw [hP, smul_zero]
    ·
      have hP : ((m : ℤ) * (n : ℤ)) • (P : (W.baseChange K).toAffine.Point) = 0 :=
        (Submodule.mem_torsionBy_iff ((m : ℤ) * (n : ℤ)) (P : (W.baseChange K).toAffine.Point)).mp P.2
      calc n • (((m : ℤ) * a) • (P : (W.baseChange K).toAffine.Point))
          = (n : ℤ) • (((m : ℤ) * a) • (P : (W.baseChange K).toAffine.Point)) := by
            rw [natCast_zsmul]
        _ = ((n : ℤ) * ((m : ℤ) * a)) • (P : (W.baseChange K).toAffine.Point) := by
            rw [smul_smul]
        _ = (a * ((m : ℤ) * (n : ℤ))) • (P : (W.baseChange K).toAffine.Point) := by
            rw [show (n : ℤ) * ((m : ℤ) * a) = a * ((m : ℤ) * (n : ℤ)) by ring]
        _ = a • (((m : ℤ) * (n : ℤ)) • (P : (W.baseChange K).toAffine.Point)) := by
            rw [smul_smul]
        _ = 0 := by rw [hP, smul_zero]
    ·
      show (m * n) • ((x.1 : (W.baseChange K).toAffine.Point) +
        (x.2 : (W.baseChange K).toAffine.Point)) = 0
      have hx1 : m • (x.1 : (W.baseChange K).toAffine.Point) = 0 := x.1.2
      have hx2 : n • (x.2 : (W.baseChange K).toAffine.Point) = 0 := x.2.2
      rw [smul_add]
      have h1 : (m * n) • (x.1 : (W.baseChange K).toAffine.Point) = 0 := by
        rw [mul_comm, ← smul_smul, hx1, smul_zero]
      have h2 : (m * n) • (x.2 : (W.baseChange K).toAffine.Point) = 0 := by
        rw [← smul_smul, hx2, smul_zero]
      rw [h1, h2, add_zero]
    ·
      apply Subtype.ext
      show ((n : ℤ) * b) • (P : (W.baseChange K).toAffine.Point) +
        ((m : ℤ) * a) • (P : (W.baseChange K).toAffine.Point) =
        (P : (W.baseChange K).toAffine.Point)
      rw [← add_zsmul, show (n : ℤ) * b + (m : ℤ) * a = 1 by linarith [hBez], one_zsmul]
    ·
      have hm1 : (m : ℤ) • (x.1 : (W.baseChange K).toAffine.Point) = 0 := by
        rw [natCast_zsmul]; exact x.1.2
      have hn2 : (n : ℤ) • (x.2 : (W.baseChange K).toAffine.Point) = 0 := by
        rw [natCast_zsmul]; exact x.2.2
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · show ((n : ℤ) * b) • ((x.1 : (W.baseChange K).toAffine.Point) +
          (x.2 : (W.baseChange K).toAffine.Point)) =
          (x.1 : (W.baseChange K).toAffine.Point)
        rw [smul_add]
        have e2 : ((n : ℤ) * b) • (x.2 : (W.baseChange K).toAffine.Point) = 0 := by
          rw [show (n : ℤ) * b = b * (n : ℤ) by ring, ← smul_smul, hn2, smul_zero]
        have e1 : ((n : ℤ) * b) • (x.1 : (W.baseChange K).toAffine.Point) =
            (x.1 : (W.baseChange K).toAffine.Point) := by
          rw [show (n : ℤ) * b = 1 - (m : ℤ) * a by linarith [hBez], sub_smul, one_zsmul,
            show (m : ℤ) * a = a * (m : ℤ) by ring, ← smul_smul, hm1, smul_zero, sub_zero]
        rw [e1, e2, add_zero]
      · show ((m : ℤ) * a) • ((x.1 : (W.baseChange K).toAffine.Point) +
          (x.2 : (W.baseChange K).toAffine.Point)) =
          (x.2 : (W.baseChange K).toAffine.Point)
        rw [smul_add]
        have e1 : ((m : ℤ) * a) • (x.1 : (W.baseChange K).toAffine.Point) = 0 := by
          rw [show (m : ℤ) * a = a * (m : ℤ) by ring, ← smul_smul, hm1, smul_zero]
        have e2 : ((m : ℤ) * a) • (x.2 : (W.baseChange K).toAffine.Point) =
            (x.2 : (W.baseChange K).toAffine.Point) := by
          rw [show (m : ℤ) * a = 1 - (n : ℤ) * b by linarith [hBez], sub_smul, one_zsmul,
            show (n : ℤ) * b = b * (n : ℤ) by ring, ← smul_smul, hn2, smul_zero, sub_zero]
        rw [e1, e2, zero_add]
  rw [Nat.card_congr e, Nat.card_prod]

end Coprime

/-- FLT's `card_nTorsion`, and the port's main theorem: `#E[n] = n²` for `n`
invertible in `K`. Stated directly over mathlib's `Submodule.torsionBy`, so no
reconciliation with a local `nTorsion` is needed. -/
theorem card_nTorsion {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]
    [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) = n ^ 2 := by
  revert hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hn
    have hpK : (p : K) ≠ 0 := by
      intro h0
      apply hn
      push_cast
      rw [h0]
      exact zero_pow hk.ne'
    rw [show ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k by push_cast; ring,
      card_nTorsion_prime_pow W hp hpK k, ← pow_mul, Nat.mul_comm]
  | zero =>
    intro hn
    simp at hn
  | one =>
    intro _
    simp
  | coprime a b ha hb hab iha ihb =>
    intro hn
    have haK : (a : K) ≠ 0 := by
      intro h0; apply hn; push_cast; rw [h0, zero_mul]
    have hbK : (b : K) ≠ 0 := by
      intro h0; apply hn; push_cast; rw [h0, mul_zero]
    rw [show ((a * b : ℕ) : ℤ) = (a : ℤ) * (b : ℤ) by push_cast; ring,
      card_nTorsion_mul_of_coprime W hab, iha haK, ihb hbK, mul_pow]

/-- **The theorem.** Over an algebraically closed field `K`, the `n`-torsion of
an elliptic curve `E/K` has `n²` elements. This is
`WeierstrassCurve.card_torsion_of_isAlgClosed` (FLT's `solution`, pinned at
`aa2d8b3`), stated directly over mathlib's `Submodule.torsionBy`; since
`card_nTorsion` above already uses `Submodule.torsionBy`, no reconciliation
wrapper is needed. -/
theorem card_torsion_of_isAlgClosed {F K : Type*} [Field F] [Field K] [Algebra F K]
    [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ}
    (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W.baseChange K).toAffine.Point n) = n ^ 2 :=
  card_nTorsion W n hn

end FLTForHuman.Elliptic
