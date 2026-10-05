/-
The torsion of an elliptic curve over an algebraically closed field is `(Z/n)²`.

Ported from the pinned FLT `aa2d8b3`
`P2M/Sol/S_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed.lean` (the
char-free `nsmul`/`zsmul` surjectivity of the point group) and the 23-line wrapper
`P2M/Sol/S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean`
(the classification, applying the generic `AddCommGroup` lemma in
`FLTForHuman/Algebra/ZModTorsion.lean` to `W.card_torsion_of_isAlgClosed`).

The first half's helpers that `FLTForHuman/Elliptic/TorsionCard.lean` already
carries (`smul_x_eq`, `isCoprime_Φ_ΨSq`, `smul_eq_zero_of_ΨSq_eval_eq_zero`, …) are
reused, so this module adds only the char-free `nsmul_surjective_charfree` /
`exists_zsmul_eq` core, its two `preΨ'` companions, and the two headline
statements. Both headlines are the `Theorems/` wrappers' statements verbatim; the
pin's public `solution` is not exposed (SET-2 pattern). The char-free core is not
weakened: `exists_zsmul_eq` takes `{n : ℤ} (hn : n ≠ 0)` with no `[CharZero K]`.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean>
-/
import FLTForHuman.Algebra.ZModTorsion
import FLTForHuman.Elliptic.TorsionCard

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open scoped FLTForHuman.Elliptic
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open WeierstrassCurve.Affine.Point

namespace FLTForHuman.Elliptic

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve F)

section

omit [DecidableEq K] in
theorem ΨSq_odd_eq_sq {n : ℕ} (hodd : Odd n) :
    (W.baseChange K).ΨSq n = ((W.baseChange K).preΨ' n) ^ 2 := by
  rw [ΨSq_ofNat, ite_eq_right (Nat.not_even_iff_odd.mpr hodd), mul_one]

theorem smul_eq_zero_iff_preΨ'_eval [W.IsElliptic] {n : ℕ} (hodd : Odd n)
    (hn : 0 < n) {x y : K} (h : (W.baseChange K).toAffine.Nonsingular x y) :
    n • (Point.some x y h : W.toAffine⟮K⟯) = 0 ↔
      ((W.baseChange K).preΨ' n).eval x = 0 := by
  constructor
  · intro hsmul
    by_contra hne
    have hns : ((W.baseChange K).ΨSq n).eval x ≠ 0 := by
      rw [ΨSq_odd_eq_sq W hodd, eval_pow]
      exact pow_ne_zero 2 hne
    obtain ⟨x', y', h', heq, -⟩ := smul_x_eq W hn h hns
    rw [hsmul] at heq
    exact Point.some_ne_zero h' heq.symm
  · intro hz
    have hz' : ((W.baseChange K).ΨSq n).eval x = 0 := by
      rw [ΨSq_odd_eq_sq W hodd, eval_pow, hz]
      exact zero_pow two_ne_zero
    exact smul_eq_zero_of_ΨSq_eval_eq_zero W hn h hz'

theorem nsmul_surjective_charfree [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hpos : 0 < n) :
    Function.Surjective (fun P : W.toAffine⟮K⟯ => n • P) := by
  intro Q
  rcases Q with _ | ⟨xQ, yQ, hQ⟩
  · refine ⟨0, ?_⟩
    show n • (0 : W.toAffine⟮K⟯) = Point.zero
    rw [nsmul_zero]
    exact Point.zero_def
  set F' := (W.baseChange K).Φ n with hFdef
  set G := (W.baseChange K).ΨSq n with hGdef
  have hFdeg : F'.natDegree = n ^ 2 := by
    have h := WeierstrassCurve.natDegree_Φ (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hFdef, h]
  have hGdeg : G.natDegree ≤ n ^ 2 - 1 := by
    have h := WeierstrassCurve.natDegree_ΨSq_le (W.baseChange K) (n : ℤ)
    rw [Int.natAbs_natCast] at h
    rw [hGdef]; exact h
  have h1n : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hpos.ne')
  set p : K[X] := F' - C xQ * G with hpdef
  have hpdeg : p.natDegree = n ^ 2 := by
    rw [hpdef]
    rw [natDegree_sub_eq_left_of_natDegree_lt, hFdeg]
    refine lt_of_le_of_lt (natDegree_C_mul_le xQ G) ?_
    rw [hFdeg]
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
  · have hnegQ : -(Point.some x' yQ hQ : W.toAffine⟮K⟯) =
        Point.some x' ((W.baseChange K).toAffine.negY x' yQ)
          ((WeierstrassCurve.Affine.nonsingular_neg ..).mpr hQ) := Point.neg_some hQ
    have hprev : n • (Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) =
        -(Point.some x' yQ hQ) := by
      rw [hnegQ]
      exact hsmul
    have hsn : n • -(Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) =
        -(n • (Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯)) :=
      neg_nsmul (Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) n
    refine ⟨-(Point.some x₀ y₀ h₀), ?_⟩
    show n • -(Point.some x₀ y₀ h₀ : W.toAffine⟮K⟯) = Point.some x' yQ hQ
    rw [hsn, hprev, neg_neg]

theorem exists_zsmul_eq [IsAlgClosed K] [W.IsElliptic] {n : ℤ} (hn : n ≠ 0)
    (P : W.toAffine⟮K⟯) : ∃ Q : W.toAffine⟮K⟯, n • Q = P := by
  have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨Q, hQ⟩ := nsmul_surjective_charfree W (K := K) hpos P
  rcases Int.natAbs_eq n with h | h
  · exact ⟨Q, by rw [h, natCast_zsmul]; exact hQ⟩
  · exact ⟨-Q, by rw [h, neg_zsmul, zsmul_neg, neg_neg, natCast_zsmul]; exact hQ⟩

end

end FLTForHuman.Elliptic

namespace WeierstrassCurve.Affine.Point

open FLTForHuman.Elliptic

/-- **Char-free `zsmul` surjectivity.** Over an algebraically closed field every
point is divisible by every nonzero integer, with no characteristic hypothesis.
This is the pin `WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed`
verbatim. -/
theorem exists_zsmul_eq_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    [DecidableEq K] (E : WeierstrassCurve K) [E.IsElliptic] {n : ℤ} (hn : n ≠ 0)
    (P : E.toAffine.Point) : ∃ Q : E.toAffine.Point, n • Q = P :=
  FLTForHuman.Elliptic.exists_zsmul_eq (F := K) (K := K) E hn P

end WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

open FLTForHuman.Elliptic

/-- **The torsion classification for an elliptic curve over an algebraically
closed field.** If `n` is invertible in the algebraically closed field `K`, then
`E(K)[n] ≅ (Z/n)²`. The pin
`WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` verbatim;
the cardinality hypothesis is `W.card_torsion_of_isAlgClosed`. -/
theorem nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed
    {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ (W⁄K).Point n) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  refine AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq hn0 ?_
  intro d hd
  have hdK : (d : K) ≠ 0 := by
    obtain ⟨c, rfl⟩ := hd
    intro h; apply hn; push_cast; rw [h, zero_mul]
  exact FLTForHuman.Elliptic.card_torsion_of_isAlgClosed W hdK

end WeierstrassCurve
