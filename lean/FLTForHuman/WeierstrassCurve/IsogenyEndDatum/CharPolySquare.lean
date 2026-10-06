/-
SET-1 gateway 2: the number-theoretic consumer of gateway 1 — the trace/norm of a
non-integral endomorphism spans binary quadratic forms of negative discriminant.

Canonical sources: the pinned FLT `aa2d8b3`
`Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean`
(the statement authority for the headline) and
`P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean`
(the proof; its `Ws13S7` prelude is the statement authority for the helper
declarations the wrapper does not carry).  Statements are transcribed verbatim; only
the proof bodies are adapted to mathlib `v4.34.0`.

The module is the pin's own topological order (a valid one): the pure-algebra
prelude in `Ws13S7` (`mem_bot_addMonoidEnd_iff`, `dd_charPoly_eq`,
`dd_intLinComb_norm_pos_*`, `binaryQuadForm_pos_of_neg_disc`,
`linearIndependent_one_of_quadCharPoly_neg_disc`), the curve block
(`charZero_addMonoidEnd_point`, `intCast_addMonoidEnd_point_injective`,
`finrankAlong_pos`, `finrankAlong_datum_pos`,
`isogenyEndSubring_mul_left_cancel`), the dual-end-data block
(`sq_eq_intCast_nonneg_isSquare`, `dualEndData_disc_neg_of_notBot`,
`s7_exists_dualEndData_dual_mem_and_intLinComb_norm_pos`, `dd_norm_trace_unique`,
`s7_dualEndData_norm_eq_finrankAlong`) and the headline
`s7_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq`; the wrapper's headline
is the last declaration.

Assumes from lower modules: `IsogenyEndDatum/PointEndSubring.lean` (gateway 1 —
`exists_pointEnd_eq_of_mem_isogenyEndSubring` is consumed by
`isogenyEndSubring_mul_left_cancel`, `sq_eq_intCast_nonneg_isSquare`,
`s7_exists_dualEndData_dual_mem_and_intLinComb_norm_pos` and
`s7_exists_sq_lt_…`), `IsogenyEndDatum/DualEndData.lean` (`DualEndData`,
`exists_dualEndData_dual_mem_and_norm_eq_finrankAlong`, `DualEndData.intLinComb*`,
`dualEndData_intCast*`), `IsogenyEndDatum/Vocabulary.lean`,
`Elliptic/TorsionCardLight.lean` (the `card_torsionBy_eq_sq_of_isAlgClosed` count),
`Elliptic/TorsionZMod.lean` (`Point.exists_zsmul_eq_of_isAlgClosed`) and
`WeierstrassCurve/Isogeny/DualAPI.lean` (the `DualEndData` algebra).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_IsogenyEndDatum_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq.lean>
-/
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.PointEndSubring
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DualEndData
import FLTForHuman.Elliptic.TorsionCardLight
import FLTForHuman.Elliptic.TorsionZMod
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

namespace Ws13S7

set_option linter.unusedSectionVars false

open AddMonoid.End

/-! ## Pure algebra -/

section PureAlgebra

variable {A : Type*} [AddCommGroup A]

/-- The pin's `mem_bot_addMonoidEnd_iff`: a scalar endomorphism is an integer. -/
theorem mem_bot_addMonoidEnd_iff (φ : AddMonoid.End A) :
    φ ∈ (⊥ : Subring (AddMonoid.End A)) ↔ ∃ n : ℤ, ∀ x : A, φ x = n • x := by
  rw [Subring.mem_bot]
  refine ⟨fun ⟨n, hn⟩ => ⟨n, fun x => hn ▸ (AddMonoid.End.intCast_apply n x)⟩,
    fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
  exact AddMonoidHom.ext fun x => (AddMonoid.End.intCast_apply n x).trans (hn x).symm

/-- The pin's `dd_charPoly_eq`: the characteristic-polynomial relation, in
`φ * φ = trace * φ - norm` form. -/
theorem dd_charPoly_eq {φ : AddMonoid.End A} (D : DualEndData φ) :
    φ * φ = (D.trace : AddMonoid.End A) * φ - (D.norm : AddMonoid.End A) := by
  have h := D.charPoly
  rwa [sub_add, sub_eq_zero] at h

/-- The pin's `dd_intLinComb_norm_pos_of_disc_neg`. -/
theorem dd_intLinComb_norm_pos_of_disc_neg {φ : AddMonoid.End A} (D : DualEndData φ)
    (hdisc : D.trace ^ 2 < 4 * D.norm) {a b : ℤ} (hb : b ≠ 0) :
    0 < (D.intLinComb a b).norm := by
  rw [DualEndData.intLinComb_norm]
  have key : 4 * (a ^ 2 + D.trace * a * b + D.norm * b ^ 2)
      = (2 * a + D.trace * b) ^ 2 + (4 * D.norm - D.trace ^ 2) * b ^ 2 := by ring
  have hbsq : (0 : ℤ) < b ^ 2 := by positivity
  nlinarith [sq_nonneg (2 * a + D.trace * b)]

/-- The pin's `dd_intLinComb_norm_pos_of_b_eq_zero`. -/
theorem dd_intLinComb_norm_pos_of_b_eq_zero {φ : AddMonoid.End A} (D : DualEndData φ)
    {a : ℤ} (ha : a ≠ 0) :
    0 < (D.intLinComb a 0).norm := by
  rw [DualEndData.intLinComb_norm]
  have : a ^ 2 + D.trace * a * 0 + D.norm * 0 ^ 2 = a ^ 2 := by ring
  rw [this]; positivity

/-- The pin's `dd_intLinComb_norm_pos_of_disc_neg_of_ne_zero`. -/
theorem dd_intLinComb_norm_pos_of_disc_neg_of_ne_zero {φ : AddMonoid.End A}
    (D : DualEndData φ) (hdisc : D.trace ^ 2 < 4 * D.norm) {a b : ℤ}
    (hne : (a : AddMonoid.End A) + (b : AddMonoid.End A) * φ ≠ 0) :
    0 < (D.intLinComb a b).norm := by
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a ≠ 0 := by
      rintro rfl
      exact hne (by simp)
    exact dd_intLinComb_norm_pos_of_b_eq_zero D ha
  · exact dd_intLinComb_norm_pos_of_disc_neg D hdisc hb

/-- The pin's `binaryQuadForm_pos_of_neg_disc`: a binary quadratic form of negative
discriminant has no nontrivial zero. -/
theorem binaryQuadForm_pos_of_neg_disc {t n a b : ℤ} (hdisc : t ^ 2 < 4 * n)
    (hform : a ^ 2 + t * a * b + n * b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have hb : b = 0 := by nlinarith [sq_nonneg (2 * a + t * b), sq_nonneg b]
  subst hb
  have ha : a = 0 := by nlinarith [sq_nonneg a]
  exact ⟨ha, rfl⟩

/-- The pin's `linearIndependent_one_of_quadCharPoly_neg_disc`. -/
theorem linearIndependent_one_of_quadCharPoly_neg_disc
    (hinj : Function.Injective (Int.cast : ℤ → AddMonoid.End A))
    {φ : AddMonoid.End A} {t n : ℤ}
    (hquad : φ * φ = (t : AddMonoid.End A) * φ - (n : AddMonoid.End A))
    (hdisc : t ^ 2 < 4 * n) :
    ∀ a b : ℤ, (a : AddMonoid.End A) + (b : AddMonoid.End A) * φ = 0 → a = 0 ∧ b = 0 := by
  intro a b hrel
  have hpt : ∀ x : A, b • φ x = -(a • x) := by
    intro x
    have h : a • x + b • φ x = 0 := calc
      a • x + b • φ x
          = (a : AddMonoid.End A) x + (b : AddMonoid.End A) (φ x) := by
            rw [AddMonoid.End.intCast_apply, AddMonoid.End.intCast_apply]
        _ = ((a : AddMonoid.End A) + (b : AddMonoid.End A) * φ) x := rfl
        _ = (0 : AddMonoid.End A) x := DFunLike.congr_fun hrel x
        _ = 0 := rfl
    exact eq_neg_of_add_eq_zero_right h
  have hq : ∀ x : A, φ (φ x) = t • φ x - n • x := by
    intro x
    calc φ (φ x) = (φ * φ) x := rfl
      _ = ((t : AddMonoid.End A) * φ - (n : AddMonoid.End A)) x := DFunLike.congr_fun hquad x
      _ = (t : AddMonoid.End A) (φ x) - (n : AddMonoid.End A) x := rfl
      _ = t • φ x - n • x := by rw [AddMonoid.End.intCast_apply, AddMonoid.End.intCast_apply]
  have hkey : ∀ x : A, (a ^ 2 + t * a * b + n * b ^ 2) • x = 0 := by
    intro x
    have hb2 : (b * b) • φ (φ x) = (-(t * a * b) - n * (b * b)) • x := by
      rw [hq, smul_sub, ← mul_smul, show (b * b) * t = (t * b) * b from by ring, mul_smul,
        hpt, smul_neg, ← mul_smul, ← mul_smul, ← neg_smul, ← sub_smul]
      congr 1; ring
    have hb2' : (b * b) • φ (φ x) = (a * a) • x := by
      rw [mul_smul, hpt (φ x), smul_neg, ← mul_smul, mul_comm b a, mul_smul, hpt, smul_neg,
        neg_neg, ← mul_smul]
    rw [show a ^ 2 + t * a * b + n * b ^ 2 = a * a - (-(t * a * b) - n * (b * b)) from by ring,
      sub_smul, ← hb2, ← hb2', sub_self]
  have hcast : ((a ^ 2 + t * a * b + n * b ^ 2 : ℤ) : AddMonoid.End A) = 0 :=
    AddMonoidHom.ext fun x => (AddMonoid.End.intCast_apply _ x).trans (hkey x)
  have hint : a ^ 2 + t * a * b + n * b ^ 2 = 0 :=
    hinj (show ((a ^ 2 + t * a * b + n * b ^ 2 : ℤ) : AddMonoid.End A)
      = ((0 : ℤ) : AddMonoid.End A) by rw [Int.cast_zero]; exact hcast)
  exact binaryQuadForm_pos_of_neg_disc hdisc hint

end PureAlgebra

/-! ## The curve block -/

section Curve

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- The pin's `charZero_addMonoidEnd_point`: the endomorphism ring of the point group
has characteristic zero. -/
theorem charZero_addMonoidEnd_point : CharZero (AddMonoid.End W.Point) := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  have htop : ∀ k : ℕ, n ∣ k → Submodule.torsionBy ℤ W.Point (k : ℤ) = ⊤ := by
    rintro k ⟨c, rfl⟩
    refine eq_top_iff.mpr fun P _ => ?_
    rw [Submodule.mem_torsionBy_iff]
    have hP : (n : ℤ) • P = 0 := by
      have h := DFunLike.congr_fun hn P
      rw [AddMonoid.End.natCast_apply] at h
      rw [natCast_zsmul]; exact h
    rw [Nat.cast_mul, mul_comm, mul_zsmul, hP, zsmul_zero]
  have hcard : ∀ k : ℕ, n ∣ k → k ≠ 0 → Nat.card W.Point = k ^ 2 := by
    intro k hk hk0
    have h : Nat.card (Submodule.torsionBy ℤ W.Point (k : ℤ)) = k ^ 2 :=
      WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W (n := k)
        (Nat.cast_ne_zero.mpr hk0) two_ne_zero
    rw [htop k hk] at h
    rwa [Nat.card_congr (Submodule.topEquiv (R := ℤ) (M := W.Point)).toEquiv] at h
  have h1 := hcard n dvd_rfl hn0
  have h2 := hcard (2 * n) (dvd_mul_left n 2) (by omega)
  have h3 : n ^ 2 = (2 * n) ^ 2 := h1.symm.trans h2
  have h4 : 3 * n ^ 2 = 0 := by nlinarith
  have h5 : n = 0 := by
    have : n ^ 2 = 0 := by omega
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  exact hn0 h5

/-- The pin's `intCast_addMonoidEnd_point_injective`. -/
theorem intCast_addMonoidEnd_point_injective :
    Function.Injective (Int.cast : ℤ → AddMonoid.End W.Point) :=
  haveI := charZero_addMonoidEnd_point W
  Int.cast_injective

/-- The pin's `finrankAlong_pos`. -/
theorem finrankAlong_pos {K L L' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L'] (φ : L →ₐ[K] L') (hfin : FiniteAlong K φ) :
    0 < finrankAlong K φ := by
  letI := algebraAlong φ
  haveI hfin' : Module.Finite L L' := hfin
  exact (Module.finrank_pos_iff_of_free (R := L) (M := L')).mpr inferInstance

variable [GenusOnePlaceGate W] [AbelTheorem W] [GenusOnePlaceGate.IsCentred W]

/-- The pin's `finrankAlong_datum_pos`. -/
theorem finrankAlong_datum_pos (D : IsogenyEndDatum W) : 0 < finrankAlong F D.ι :=
  finrankAlong_pos D.ι D.hfin

/-- The pin's `isogenyEndSubring_mul_left_cancel`: `isogenyEndSubring` has no
zero divisors acting on the left. -/
theorem isogenyEndSubring_mul_left_cancel
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    {φ : AddMonoid.End W.Point} (hφS : φ ∈ isogenyEndSubring W hNs) (hφ0 : φ ≠ 0)
    {ψ : AddMonoid.End W.Point} (hzero : φ * ψ = 0) : ψ = 0 := by
  obtain ⟨D, rfl⟩ :=
    IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring hNs φ hφS hφ0
  obtain ⟨DD, -, hnorm⟩ :=
    IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong hNs D
  have hdeg : (0 : ℤ) < DD.norm := by
    rw [hnorm]; exact_mod_cast finrankAlong_datum_pos W D
  have hNψ : ((DD.norm : ℤ) : AddMonoid.End W.Point) * ψ = 0 := by
    rw [← DD.dual_mul, mul_assoc, hzero, mul_zero]
  refine AddMonoidHom.ext fun P => ?_
  obtain ⟨Q, rfl⟩ : ∃ Q : W.Point, DD.norm • Q = P :=
    WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed W (n := DD.norm) hdeg.ne' P
  have h := DFunLike.congr_fun hNψ Q
  change (DD.norm : AddMonoid.End W.Point) (ψ Q) = 0 at h
  rw [AddMonoid.End.intCast_apply] at h
  show ψ (DD.norm • Q) = 0
  rw [map_zsmul ψ DD.norm Q, h]

end Curve

/-! ## The dual-end-data block -/

section CurveD

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]
variable [GenusOnePlaceGate W] [AbelTheorem W] [GenusOnePlaceGate.IsCentred W]

/-- The pin's `sq_eq_intCast_nonneg_isSquare`. -/
theorem sq_eq_intCast_nonneg_isSquare
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    {ξ : AddMonoid.End W.Point} (hξS : ξ ∈ isogenyEndSubring W hNs)
    {d : ℤ} (hd_nn : 0 ≤ d)
    (hξsq : ξ * ξ = ((d : ℤ) : AddMonoid.End W.Point)) :
    ∃ e : ℤ, d = e ^ 2 := by
  rcases eq_or_ne ξ 0 with hξ0 | hξ0
  · have : ((d : ℤ) : AddMonoid.End W.Point) = ((0 : ℤ) : AddMonoid.End W.Point) := by
      rw [← hξsq, hξ0, mul_zero, Int.cast_zero]
    exact ⟨0, by simpa using intCast_addMonoidEnd_point_injective W this⟩
  · obtain ⟨Dξ, hDξ⟩ :=
      IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring hNs ξ hξS hξ0
    obtain ⟨DDξ, -, hnormξ⟩ :=
      IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong hNs Dξ
    have hnξ_pos : (0 : ℤ) < DDξ.norm := by
      rw [hnormξ]; exact_mod_cast finrankAlong_datum_pos W Dξ
    have htξ : ξ + DDξ.dual = ((DDξ.trace : ℤ) : AddMonoid.End W.Point) := by
      rw [← hDξ]; exact DDξ.add_dual
    have hmul : ξ * DDξ.dual = ((DDξ.norm : ℤ) : AddMonoid.End W.Point) := by
      rw [← hDξ]; exact DDξ.mul_dual

    have hlin : ξ * ((DDξ.trace : ℤ) : AddMonoid.End W.Point)
        = (((d + DDξ.norm) : ℤ) : AddMonoid.End W.Point) := by
      rw [← htξ, mul_add, hξsq, hmul, ← Int.cast_add]
    set c : ℤ := d + DDξ.norm with hc_def
    have hc_pos : 0 < c := by omega
    have hsq : DDξ.trace ^ 2 * d = c ^ 2 := by
      have L : ξ * ((DDξ.trace : ℤ) : AddMonoid.End W.Point)
          * (ξ * ((DDξ.trace : ℤ) : AddMonoid.End W.Point))
            = (((DDξ.trace ^ 2 * d : ℤ)) : AddMonoid.End W.Point) := by
        rw [mul_assoc, ← mul_assoc ((DDξ.trace : ℤ) : AddMonoid.End W.Point),
          (Int.cast_commute DDξ.trace ξ).eq, mul_assoc ξ, ← mul_assoc, hξsq,
          ← Int.cast_mul, ← Int.cast_mul]
        exact congrArg Int.cast (by ring)
      have key : (((DDξ.trace ^ 2 * d : ℤ)) : AddMonoid.End W.Point)
          = (((c ^ 2 : ℤ)) : AddMonoid.End W.Point) := by
        rw [← L, hlin, ← Int.cast_mul, sq]
      exact intCast_addMonoidEnd_point_injective W key
    have htξ_ne : DDξ.trace ≠ 0 := by
      intro h0; rw [h0, zero_pow (by omega), zero_mul] at hsq
      exact (pow_eq_zero_iff (n := 2) (by omega) |>.mp hsq.symm |> hc_pos.ne').elim
    obtain ⟨k, hk⟩ : DDξ.trace ∣ c :=
      (Int.pow_dvd_pow_iff (n := 2) (by omega)).mp ⟨d, hsq.symm⟩
    refine ⟨k, ?_⟩
    have : DDξ.trace ^ 2 * d = DDξ.trace ^ 2 * k ^ 2 := by rw [hsq, hk]; ring
    exact mul_left_cancel₀ (pow_ne_zero 2 htξ_ne) this

/-- The pin's `dualEndData_disc_neg_of_notBot`. -/
theorem dualEndData_disc_neg_of_notBot
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    {φ : AddMonoid.End W.Point} (hφS : φ ∈ isogenyEndSubring W hNs)
    (hbot : φ ∉ (⊥ : Subring (AddMonoid.End W.Point)))
    (DD : DualEndData φ) :
    DD.trace ^ 2 < 4 * DD.norm := by
  by_contra hcontra
  set t : ℤ := DD.trace with ht_def
  set n : ℤ := DD.norm with hn_def
  set d : ℤ := t ^ 2 - 4 * n with hd_def
  have hd_nn : 0 ≤ d := by
    rw [not_lt] at hcontra; omega
  set ξ : AddMonoid.End W.Point :=
    ((2 : ℤ) : AddMonoid.End W.Point) * φ
      - ((t : ℤ) : AddMonoid.End W.Point) with hξ_def
  have hξS : ξ ∈ isogenyEndSubring W hNs :=
    sub_mem (mul_mem (intCast_mem _ 2) hφS) (intCast_mem _ t)

  have hξsq : ξ * ξ = ((d : ℤ) : AddMonoid.End W.Point) := by
    have hφφ : φ * φ
        = ((t : ℤ) : AddMonoid.End W.Point) * φ - ((n : ℤ) : AddMonoid.End W.Point) := by
      have h := DD.charPoly
      rw [← ht_def, ← hn_def, sub_add, sub_eq_zero] at h; exact h
    rw [hξ_def, sub_mul, mul_sub, mul_sub,
      show ((2 : ℤ) : AddMonoid.End W.Point) * φ
        * (((2 : ℤ) : AddMonoid.End W.Point) * φ)
          = (((2 * 2 : ℤ)) : AddMonoid.End W.Point) * (φ * φ) by
        rw [mul_assoc, ← mul_assoc φ,
          ← (Int.cast_commute (2 : ℤ) φ).eq, mul_assoc,
          ← mul_assoc ((2 : ℤ) : AddMonoid.End W.Point), ← Int.cast_mul],
      show ((2 : ℤ) : AddMonoid.End W.Point) * φ
        * ((t : ℤ) : AddMonoid.End W.Point)
          = (((2 * t : ℤ)) : AddMonoid.End W.Point) * φ by
        rw [mul_assoc, ← (Int.cast_commute t φ).eq, ← mul_assoc, ← Int.cast_mul],
      show ((t : ℤ) : AddMonoid.End W.Point)
        * (((2 : ℤ) : AddMonoid.End W.Point) * φ)
          = (((t * 2 : ℤ)) : AddMonoid.End W.Point) * φ by
        rw [← mul_assoc, ← Int.cast_mul],
      hφφ, mul_sub,
      ← mul_assoc (((2 * 2 : ℤ)) : AddMonoid.End W.Point)
        ((t : ℤ) : AddMonoid.End W.Point),
      ← Int.cast_mul (2 * 2) t, ← Int.cast_mul t t,
      show ((2 * 2 : ℤ) : AddMonoid.End W.Point) * ((n : ℤ) : AddMonoid.End W.Point)
          = (((4 * n : ℤ)) : AddMonoid.End W.Point) by
        rw [← Int.cast_mul]; norm_num,
      show ((2 * 2 * t : ℤ) : AddMonoid.End W.Point)
        = ((2 * t : ℤ) : AddMonoid.End W.Point)
          + ((t * 2 : ℤ) : AddMonoid.End W.Point) by
        rw [← Int.cast_add]; congr 1; ring,
      add_mul, hd_def,
      show ((t ^ 2 - 4 * n : ℤ) : AddMonoid.End W.Point)
        = ((t * t : ℤ) : AddMonoid.End W.Point)
          - ((4 * n : ℤ) : AddMonoid.End W.Point) by
        rw [← Int.cast_sub]; congr 1; ring]
    abel

  obtain ⟨e, he⟩ := sq_eq_intCast_nonneg_isSquare W hNs hξS hd_nn hξsq

  have hfact : (ξ - ((e : ℤ) : AddMonoid.End W.Point))
      * (ξ + ((e : ℤ) : AddMonoid.End W.Point)) = 0 := by
    have expand : (ξ - ((e : ℤ) : AddMonoid.End W.Point))
        * (ξ + ((e : ℤ) : AddMonoid.End W.Point))
          = ξ * ξ - ((e : ℤ) : AddMonoid.End W.Point)
            * ((e : ℤ) : AddMonoid.End W.Point) := by
      rw [sub_mul, mul_add, mul_add, (Int.cast_commute e ξ).eq]
      abel
    rw [expand, hξsq, ← Int.cast_mul, ← Int.cast_sub, he, sq,
      sub_self, Int.cast_zero]
  have hξbot : ξ ∈ (⊥ : Subring (AddMonoid.End W.Point)) := by
    rcases eq_or_ne (ξ - ((e : ℤ) : AddMonoid.End W.Point)) 0 with h | h
    · exact Subring.mem_bot.mpr ⟨e, (sub_eq_zero.mp h).symm⟩
    · have h0 := isogenyEndSubring_mul_left_cancel W hNs
        (sub_mem hξS (intCast_mem _ e)) h hfact
      exact Subring.mem_bot.mpr ⟨-e, by
        rw [Int.cast_neg]; exact neg_eq_of_add_eq_zero_left h0⟩

  obtain ⟨s, hs⟩ := Subring.mem_bot.mp hξbot
  have h2φ : ((2 : ℤ) : AddMonoid.End W.Point) * φ
      = (((t + s : ℤ)) : AddMonoid.End W.Point) := by
    have : ((2 : ℤ) : AddMonoid.End W.Point) * φ
        = ((t : ℤ) : AddMonoid.End W.Point) + ξ := by rw [hξ_def]; abel
    rw [this, ← hs, ← Int.cast_add]

  have hs_sq : s ^ 2 = d := by
    have : (((s ^ 2 : ℤ)) : AddMonoid.End W.Point)
        = ((d : ℤ) : AddMonoid.End W.Point) := by
      rw [← hξsq, ← hs, sq, Int.cast_mul]
    exact intCast_addMonoidEnd_point_injective W this

  have hprod : (t + s) * (t - s) = 4 * n := by
    have : t ^ 2 - s ^ 2 = 4 * n := by rw [hs_sq, hd_def]; ring
    linarith [sq_sub_sq t s]
  have hts_even : 2 ∣ (t + s) := by
    by_contra hndvd
    have h1 : (t + s) % 2 = 1 := by omega
    have h2 : (t - s) % 2 = 1 := by omega
    have h3 : ((t + s) * (t - s)) % 2 = 1 := by
      rw [Int.mul_emod, h1, h2]; norm_num
    rw [hprod] at h3
    omega
  obtain ⟨m, hm⟩ := hts_even

  have hcancel : ((2 : ℤ) : AddMonoid.End W.Point)
      * (φ - ((m : ℤ) : AddMonoid.End W.Point)) = 0 := by
    rw [mul_sub, h2φ, ← Int.cast_mul, ← Int.cast_sub, hm, sub_self, Int.cast_zero]
  have h2ne : ((2 : ℤ) : AddMonoid.End W.Point) ≠ 0 := by
    intro h
    exact two_ne_zero
      (intCast_addMonoidEnd_point_injective W (h.trans Int.cast_zero.symm))
  have hφm : φ - ((m : ℤ) : AddMonoid.End W.Point) = 0 :=
    isogenyEndSubring_mul_left_cancel W hNs (intCast_mem _ 2) h2ne hcancel
  exact hbot (Subring.mem_bot.mpr ⟨m, (sub_eq_zero.mp hφm).symm⟩)

/-- The pin's `s7_exists_dualEndData_dual_mem_and_intLinComb_norm_pos`. -/
theorem s7_exists_dualEndData_dual_mem_and_intLinComb_norm_pos
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (φ : AddMonoid.End W.Point) (hφ : φ ∈ isogenyEndSubring W hNs) :
    ∃ D : AddMonoid.End.DualEndData φ, D.dual ∈ isogenyEndSubring W hNs ∧
      ∀ a b : ℤ, (a : AddMonoid.End W.Point) + (b : AddMonoid.End W.Point) * φ ≠ 0 →
        0 < (D.intLinComb a b).norm := by
  by_cases hbot : φ ∈ (⊥ : Subring (AddMonoid.End W.Point))
  · obtain ⟨m, rfl⟩ := Subring.mem_bot.mp hbot
    refine ⟨dualEndData_intCast m, intCast_mem _ m, fun a b hne => ?_⟩
    rw [DualEndData.intLinComb_norm, dualEndData_intCast_trace, dualEndData_intCast_norm]
    have hcast : (a : AddMonoid.End W.Point)
        + (b : AddMonoid.End W.Point) * ((m : ℤ) : AddMonoid.End W.Point)
          = ((a + b * m : ℤ) : AddMonoid.End W.Point) := by
      rw [Int.cast_add, Int.cast_mul]
    have habm : a + b * m ≠ 0 := by
      rintro habm
      exact hne (by rw [hcast, habm, Int.cast_zero])
    have hsq : a ^ 2 + 2 * m * a * b + m ^ 2 * b ^ 2 = (a + b * m) ^ 2 := by ring
    rw [hsq]; positivity
  · have hφ0 : φ ≠ 0 := by
      intro h; apply hbot; rw [h]; exact zero_mem _
    obtain ⟨D, rfl⟩ :=
      IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring hNs φ hφ hφ0
    obtain ⟨DD, hdual, -⟩ :=
      IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong hNs D
    have hdisc := dualEndData_disc_neg_of_notBot W hNs hφ hbot DD
    exact ⟨DD, hdual, fun a b hne =>
      dd_intLinComb_norm_pos_of_disc_neg_of_ne_zero DD hdisc hne⟩

/-- The pin's `dd_norm_trace_unique`: the trace and norm of a negative-discriminant
`DualEndData` are determined by `φ`. -/
theorem dd_norm_trace_unique {A : Type*} [AddCommGroup A]
    (hinj : Function.Injective (Int.cast : ℤ → AddMonoid.End A))
    {φ : AddMonoid.End A} (DD DD₀ : DualEndData φ)
    (hdisc : DD.trace ^ 2 < 4 * DD.norm) :
    DD.norm = DD₀.norm ∧ DD.trace = DD₀.trace := by
  have hcp := DD.charPoly
  have hcp₀ := DD₀.charPoly
  have e1 : φ * φ + (↑DD.norm : AddMonoid.End A) = ↑DD.trace * φ := by
    have h := hcp; rw [sub_add_eq_add_sub, sub_eq_zero] at h; exact h
  have e2 : φ * φ + (↑DD₀.norm : AddMonoid.End A) = ↑DD₀.trace * φ := by
    have h := hcp₀; rw [sub_add_eq_add_sub, sub_eq_zero] at h; exact h
  have hsub : (↑(DD.trace - DD₀.trace) : AddMonoid.End A) * φ
      = ↑(DD.norm - DD₀.norm) := by
    rw [Int.cast_sub, Int.cast_sub, sub_mul, ← e1, ← e2]
    abel
  set k : ℤ := DD.trace - DD₀.trace with hk_def
  set ℓ : ℤ := DD.norm - DD₀.norm with hℓ_def
  rcases eq_or_ne k 0 with hk | hk
  · rw [hk, Int.cast_zero, zero_mul] at hsub
    have hℓ0 : (↑ℓ : AddMonoid.End A) = ↑(0 : ℤ) := by
      rw [Int.cast_zero]; exact hsub.symm
    have hℓ : ℓ = 0 := hinj hℓ0
    refine ⟨?_, ?_⟩
    · rw [hℓ_def] at hℓ; linarith
    · rw [hk_def] at hk; linarith
  · exfalso
    have hcent : Commute (↑k : AddMonoid.End A) φ := Int.cast_commute k φ
    have hA : (↑k : AddMonoid.End A) ^ 2 * φ ^ 2 = (↑ℓ : AddMonoid.End A) ^ 2 := by
      rw [← hcent.mul_pow, hsub]
    have hB : (↑k : AddMonoid.End A) ^ 2 * (↑DD.trace * φ)
        = (↑DD.trace : AddMonoid.End A) * ↑k * ↑ℓ := by
      rw [sq, mul_assoc,
        ← mul_assoc (↑k : AddMonoid.End A) (↑DD.trace) φ,
        (Int.cast_commute k (↑DD.trace : AddMonoid.End A)).eq,
        mul_assoc (↑DD.trace : AddMonoid.End A), hsub, ← mul_assoc,
        (Int.cast_commute k (↑DD.trace : AddMonoid.End A)).eq]
    have hZ : ℓ ^ 2 - DD.trace * k * ℓ + k ^ 2 * DD.norm = 0 := by
      have h0 : (↑k : AddMonoid.End A) ^ 2
          * (φ * φ - ↑DD.trace * φ + ↑DD.norm) = 0 := by
        rw [hcp, mul_zero]
      rw [mul_add, mul_sub, ← sq, hA, hB] at h0
      have h1 : ((ℓ ^ 2 - DD.trace * k * ℓ + k ^ 2 * DD.norm : ℤ) : AddMonoid.End A)
          = ↑(0 : ℤ) := by
        rw [Int.cast_zero]; push_cast; exact h0
      exact hinj h1
    have hk2 : (0 : ℤ) < k ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * ℓ - DD.trace * k), hZ, hk2, hdisc]

/-- The pin's `s7_dualEndData_norm_eq_finrankAlong`. -/
theorem s7_dualEndData_norm_eq_finrankAlong
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (D : IsogenyEndDatum W) (DD : AddMonoid.End.DualEndData (D.pointEnd (hNs D)))
    (hdisc : DD.trace ^ 2 < 4 * DD.norm) :
    DD.norm = finrankAlong F D.ι := by
  obtain ⟨DD₀, -, hd⟩ :=
    IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong hNs D
  rw [← hd]
  exact (dd_norm_trace_unique (intCast_addMonoidEnd_point_injective W) DD DD₀ hdisc).1

/-- The pin's `s7_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq`. -/
theorem s7_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (D₀ : IsogenyEndDatum W)
    (hD₀ : ¬ ∃ m : ℤ, ∀ P : W.Point, D₀.pointEnd (hNs D₀) P = m • P) :
    ∃ t n : ℤ, t ^ 2 < 4 * n ∧
      ∀ a b : ℤ, b ≠ 0 → ∃ D : IsogenyEndDatum W,
        (finrankAlong F D.ι : ℤ) = a ^ 2 + t * a * b + n * b ^ 2 := by
  have hφS : D₀.pointEnd (hNs D₀) ∈ isogenyEndSubring W hNs :=
    IsogenyEndDatum.pointEnd_mem_isogenyEndSubring W hNs D₀
  have hφnb : D₀.pointEnd (hNs D₀) ∉ (⊥ : Subring (AddMonoid.End W.Point)) :=
    fun hmem => hD₀ ((mem_bot_addMonoidEnd_iff _).mp hmem)
  obtain ⟨DD, -, -⟩ :=
    IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong hNs D₀
  have hdisc : DD.trace ^ 2 < 4 * DD.norm :=
    dualEndData_disc_neg_of_notBot W hNs hφS hφnb DD
  refine ⟨DD.trace, DD.norm, hdisc, fun a b hb => ?_⟩
  have hψmem :
      (a : AddMonoid.End W.Point) + (b : AddMonoid.End W.Point) * D₀.pointEnd (hNs D₀)
        ∈ isogenyEndSubring W hNs :=
    add_mem (intCast_mem _ a) (mul_mem (intCast_mem _ b) hφS)
  have hlin := linearIndependent_one_of_quadCharPoly_neg_disc
    (intCast_addMonoidEnd_point_injective W) (dd_charPoly_eq DD) hdisc
  have hψne :
      (a : AddMonoid.End W.Point) + (b : AddMonoid.End W.Point) * D₀.pointEnd (hNs D₀) ≠ 0 :=
    fun heq => hb (hlin a b heq).2
  obtain ⟨D', hD'pt⟩ :=
    IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring hNs _ hψmem hψne
  have hdisc' : (DD.intLinComb a b).trace ^ 2 < 4 * (DD.intLinComb a b).norm :=
    DD.intLinComb_disc_neg hb hdisc
  have hcast : ∀ {φ ψ : AddMonoid.End W.Point} (h : φ = ψ) (E : AddMonoid.End.DualEndData ψ),
      (h ▸ E).norm = E.norm ∧ (h ▸ E).trace = E.trace := by
    intro φ ψ h E; subst h; exact ⟨rfl, rfl⟩
  have hnorm : (DD.intLinComb a b).norm = finrankAlong F D'.ι := by
    have h := s7_dualEndData_norm_eq_finrankAlong W hNs D' (hD'pt ▸ DD.intLinComb a b)
      (by rw [(hcast hD'pt _).1, (hcast hD'pt _).2]; exact hdisc')
    rwa [(hcast hD'pt _).1] at h
  refine ⟨D', ?_⟩
  rw [← hnorm, DualEndData.intLinComb_norm]

end CurveD

end Ws13S7

/-! ## The headline -/

namespace WeierstrassCurve

namespace Affine

namespace IsogenyEndDatum

/-- The pin's `WeierstrassCurve.Affine.IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq`
(the gateway-2 headline): the trace and norm of a non-integral endomorphism span
binary quadratic forms of negative discriminant. -/
theorem exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    [GenusOnePlaceGate.IsCentred W]
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (D₀ : IsogenyEndDatum W) (hD₀ : ¬ ∃ m : ℤ, ∀ P : W.Point, D₀.pointEnd (hNs D₀) P = m • P) :
    ∃ t n : ℤ, t ^ 2 < 4 * n ∧
      ∀ a b : ℤ, b ≠ 0 → ∃ D : IsogenyEndDatum W,
        (finrankAlong F D.ι : ℤ) = a ^ 2 + t * a * b + n * b ^ 2 :=
  Ws13S7.s7_exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq W hNs D₀ hD₀

end IsogenyEndDatum

end Affine

end WeierstrassCurve
