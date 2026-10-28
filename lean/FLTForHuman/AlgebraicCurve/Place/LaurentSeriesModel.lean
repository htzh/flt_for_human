/-
  The Laurent-series model at a degree-one place: the first of the three `localParam`
  leaves of the Deligne–Serre cone, and the Laurent expansion that every local
  computation uses. A degree-one place `w` has residue field `K` (`resEquiv`), so
  every integral element has a coefficient sequence (`resCoeff`, `remSeq`,
  `expCoeff`) and hence an expansion in a uniformiser `π`: `expPS` is a ring hom
  `w.toValuationSubring →+* PowerSeries K`, the induced map into `LaurentSeries K` is
  injective, so it extends to `F` by `IsFractionRing.lift`, and the resulting
  `K`-algebra map has order `w.ord` at every element. The headline sends a prescribed
  uniformiser `t` (any `t` with `w.ord t = 1`) to `X = HahnSeries.single 1 1`.

  Statements are transcribed verbatim from the pinned FLT proof
  (`anthropics/fermats-last-theorem`, `aa2d8b3`); only proof bodies are adapted to
  mathlib `v4.34.0`. All 27 of the pin's `private` declarations stay `private` — the
  engine `resEquiv`/`resCoeff`/`remSeq`/`expCoeff`/`expPS` with its lemmas, and the
  pin's own private statement of the headline, which the public theorem re-exports
  (the pin's `solution`).

  Role: tier 1. Two public headlines,
  `AlgebraicCurve.Place.exists_algHom_laurentSeries_of_deg_eq_one` and
  `AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries`.

  The second headline is the converse direction of the model, stated over the ramified
  Puiseux embedding: a `K`-algebra map `F →ₐ[K] LaurentSeries K` that is not order-trivial
  is, after rescaling by a positive integer `γ`, the order map of a place of `F`.  Its
  proof is the pin's `CD` block of `S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries`:
  the transport lemmas `hasRamBound_puiseuxRamEmb`/`order_puiseuxRamEmb`, the constant
  computations `laurentAlgebraMap_eq_C`/`hahnQAlgebraMap_eq_C`, the lift `liftToHahn`
  into `HahnSeries ℚ K` with its order law `order_liftToHahn`, and then
  `Place.exists_ord_mul_eq_order_of_hasRamBound` (`Place/ValueDictionary.lean`) applied to
  that lift.  The pin's downstream control `cd2_control` (which computes against
  `ModularCurve/XH`'s `laurentBaseChange`/`coeffEmb` and would invert the import
  direction) is deliberately not ported.  The pin's private statement of this headline
  stays `private`, in `LaurentSeriesModel` — Lean 4 refuses a public declaration that
  reuses the name of a private one in the same module, and the block's other private
  declarations already live there.

  spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one.lean
  spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Defs.HahnSeriesRamificationBound
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Place.ValueDictionary
import FLTForHuman.ModularCurve.Defs.Laurent
import Mathlib.RingTheory.PowerSeries.Trunc

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

namespace Place

namespace LaurentSeriesModel

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private def resEquiv (w : Place K F) (hw : w.deg = 1) : K ≃+* w.ResidueField :=
  RingEquiv.ofBijective (algebraMap K w.ResidueField)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hw)

private theorem resEquiv_apply (w : Place K F) (hw : w.deg = 1) (a : K) :
    resEquiv w hw a = algebraMap K w.ResidueField a := rfl

private theorem residue_algebraMap (w : Place K F) (a : K) :
    residue w.toValuationSubring (algebraMap K w.toValuationSubring a)
      = algebraMap K w.ResidueField a := by
  rw [IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField,
    IsLocalRing.ResidueField.algebraMap_eq]

private def resCoeff (w : Place K F) (hw : w.deg = 1) (y : w.toValuationSubring) : K :=
  (resEquiv w hw).symm (residue w.toValuationSubring y)

private theorem residue_sub_algebraMap_resCoeff (w : Place K F) (hw : w.deg = 1)
    (y : w.toValuationSubring) :
    residue w.toValuationSubring (y - algebraMap K w.toValuationSubring (resCoeff w hw y))
      = 0 := by
  rw [map_sub, residue_algebraMap,
    show algebraMap K w.ResidueField (resCoeff w hw y)
        = resEquiv w hw ((resEquiv w hw).symm (residue w.toValuationSubring y)) from rfl,
    RingEquiv.apply_symm_apply, sub_self]

private theorem exists_sub_resCoeff_eq_mul (w : Place K F) (hw : w.deg = 1)
    {π : w.toValuationSubring} (hπ : Irreducible π) (y : w.toValuationSubring) :
    ∃ z : w.toValuationSubring,
      y - algebraMap K w.toValuationSubring (resCoeff w hw y) = π * z := by
  have h := residue_sub_algebraMap_resCoeff w hw y
  rw [residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at h
  exact h

private def remSeq (w : Place K F) (hw : w.deg = 1) {π : w.toValuationSubring}
    (hπ : Irreducible π) (y : w.toValuationSubring) : ℕ → w.toValuationSubring
  | 0 => y
  | n + 1 => (exists_sub_resCoeff_eq_mul w hw hπ (remSeq w hw hπ y n)).choose

private theorem remSeq_spec (w : Place K F) (hw : w.deg = 1) {π : w.toValuationSubring}
    (hπ : Irreducible π) (y : w.toValuationSubring) (n : ℕ) :
    remSeq w hw hπ y n
        - algebraMap K w.toValuationSubring (resCoeff w hw (remSeq w hw hπ y n))
      = π * remSeq w hw hπ y (n + 1) :=
  (exists_sub_resCoeff_eq_mul w hw hπ (remSeq w hw hπ y n)).choose_spec

private def expCoeff (w : Place K F) (hw : w.deg = 1) {π : w.toValuationSubring}
    (hπ : Irreducible π) (y : w.toValuationSubring) (n : ℕ) : K :=
  resCoeff w hw (remSeq w hw hπ y n)

private theorem remSeq_sum (w : Place K F) (hw : w.deg = 1) {π : w.toValuationSubring}
    (hπ : Irreducible π) (y : w.toValuationSubring) (M : ℕ) :
    y = (∑ n ∈ Finset.range M,
          algebraMap K w.toValuationSubring (expCoeff w hw hπ y n) * π ^ n)
        + π ^ M * remSeq w hw hπ y M := by
  induction M with
  | zero => simp [remSeq]
  | succ M ih =>
      have h : remSeq w hw hπ y M
          = π * remSeq w hw hπ y (M + 1)
            + algebraMap K w.toValuationSubring (expCoeff w hw hπ y M) := by
        have hs := remSeq_spec w hw hπ y M
        rw [sub_eq_iff_eq_add] at hs
        exact hs
      conv_lhs => rw [ih]
      rw [Finset.sum_range_succ, add_assoc]
      congr 1
      rw [h]
      ring

private theorem remSeq_shift (w : Place K F) (hw : w.deg = 1) {π : w.toValuationSubring}
    (hπ : Irreducible π) (y : w.toValuationSubring) :
    ∀ n : ℕ, remSeq w hw hπ y (n + 1) = remSeq w hw hπ (remSeq w hw hπ y 1) n
  | 0 => rfl
  | n + 1 => by
      show (exists_sub_resCoeff_eq_mul w hw hπ (remSeq w hw hπ y (n + 1))).choose
        = remSeq w hw hπ (remSeq w hw hπ y 1) (n + 1)
      rw [remSeq_shift w hw hπ y n]
      rfl

private theorem expCoeff_eq_of_eq_sum (w : Place K F) (hw : w.deg = 1)
    {π : w.toValuationSubring} (hπ : Irreducible π) :
    ∀ (M : ℕ) (y : w.toValuationSubring) (b : ℕ → K) (r : w.toValuationSubring),
      y = (∑ n ∈ Finset.range M, algebraMap K w.toValuationSubring (b n) * π ^ n)
          + π ^ M * r →
      ∀ n < M, expCoeff w hw hπ y n = b n := by
  intro M
  induction M with
  | zero => intro y b r _ n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ M ih =>
      intro y b r h n hn
      have hπ0 : residue w.toValuationSubring π = 0 := by
        rw [residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact hπ.not_isUnit
      have hS : y = algebraMap K w.toValuationSubring (b 0)
          + π * ((∑ k ∈ Finset.range M,
              algebraMap K w.toValuationSubring (b (k + 1)) * π ^ k) + π ^ M * r) := by
        have hfac : (∑ k ∈ Finset.range M,
              algebraMap K w.toValuationSubring (b (k + 1)) * π ^ (k + 1))
            = π * ∑ k ∈ Finset.range M,
                algebraMap K w.toValuationSubring (b (k + 1)) * π ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
        rw [h, Finset.sum_range_succ', hfac]
        ring
      have hres : residue w.toValuationSubring y = algebraMap K w.ResidueField (b 0) := by
        rw [hS, map_add, map_mul, hπ0, zero_mul, add_zero, residue_algebraMap]
      have h0 : expCoeff w hw hπ y 0 = b 0 := by
        show (resEquiv w hw).symm (residue w.toValuationSubring y) = b 0
        rw [hres, ← resEquiv_apply w hw, RingEquiv.symm_apply_apply]
      have hspec : y - algebraMap K w.toValuationSubring (resCoeff w hw y)
          = π * remSeq w hw hπ y 1 := remSeq_spec w hw hπ y 0
      have h1 : remSeq w hw hπ y 1
          = (∑ k ∈ Finset.range M,
              algebraMap K w.toValuationSubring (b (k + 1)) * π ^ k) + π ^ M * r := by
        apply mul_left_cancel₀ hπ.ne_zero
        rw [← hspec, show resCoeff w hw y = expCoeff w hw hπ y 0 from rfl, h0]
        conv_lhs => rw [hS]
        ring
      rcases n with _ | k
      · exact h0
      · have hshift : expCoeff w hw hπ y (k + 1)
            = expCoeff w hw hπ (remSeq w hw hπ y 1) k := by
          show resCoeff w hw (remSeq w hw hπ y (k + 1))
            = resCoeff w hw (remSeq w hw hπ (remSeq w hw hπ y 1) k)
          rw [remSeq_shift]
        rw [hshift]
        exact ih (remSeq w hw hπ y 1) (fun j => b (j + 1)) r h1 k (by omega)

private theorem sum_single_coeff (w : Place K F) {π : w.toValuationSubring} (M j : ℕ)
    (hj : j < M) (a : K) :
    (∑ k ∈ Finset.range M,
        algebraMap K w.toValuationSubring (if k = j then a else 0) * π ^ k)
      = algebraMap K w.toValuationSubring a * π ^ j := by
  rw [Finset.sum_eq_single j]
  · rw [ite_eq_left rfl]
  · intro k _ hk
    rw [ite_eq_right hk, map_zero, zero_mul]
  · intro hj'
    exact absurd (Finset.mem_range.mpr hj) hj'

private def expPS (w : Place K F) (hw : w.deg = 1) {π : w.toValuationSubring}
    (hπ : Irreducible π) : w.toValuationSubring →+* PowerSeries K where
  toFun y := PowerSeries.mk (expCoeff w hw hπ y)
  map_one' := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    have hident : (1 : w.toValuationSubring)
        = (∑ k ∈ Finset.range (n + 1),
            algebraMap K w.toValuationSubring (if k = 0 then (1 : K) else 0) * π ^ k)
          + π ^ (n + 1) * 0 := by
      rw [mul_zero, add_zero, sum_single_coeff w (n + 1) 0 n.succ_pos 1, map_one, pow_zero,
        mul_one]
    exact expCoeff_eq_of_eq_sum w hw hπ (n + 1) 1
      (fun j => if j = 0 then (1 : K) else 0) 0 hident n n.lt_succ_self
  map_mul' y z := by
    ext n
    rw [PowerSeries.coeff_mk]
    have hprod : ∀ d < n + 1,
        (PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ y))
            * PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ z))).coeff d
          = PowerSeries.coeff d
              (PowerSeries.mk (expCoeff w hw hπ y) * PowerSeries.mk (expCoeff w hw hπ z)) := by
      intro d hd
      rw [Polynomial.coeff_mul, PowerSeries.coeff_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc, ite_eq_left (by omega),
        ite_eq_left (by omega)]
    obtain ⟨Q, hQ⟩ : ∃ Q : Polynomial K,
        PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ y))
            * PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ z))
          = PowerSeries.trunc (n + 1)
              (PowerSeries.mk (expCoeff w hw hπ y) * PowerSeries.mk (expCoeff w hw hπ z))
            + Polynomial.X ^ (n + 1) * Q := by
      have hdvd : Polynomial.X ^ (n + 1) ∣
          (PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ y))
              * PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ z))
            - PowerSeries.trunc (n + 1)
                (PowerSeries.mk (expCoeff w hw hπ y)
                  * PowerSeries.mk (expCoeff w hw hπ z))) := by
        rw [Polynomial.X_pow_dvd_iff]
        intro d hd
        rw [Polynomial.coeff_sub, hprod d hd, PowerSeries.coeff_trunc, ite_eq_left hd, sub_self]
      obtain ⟨Q, hQ⟩ := hdvd
      refine ⟨Q, ?_⟩
      rw [← hQ]
      ring
    have hyev : y = Polynomial.eval₂ (algebraMap K w.toValuationSubring) π
          (PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ y)))
        + π ^ (n + 1) * remSeq w hw hπ y (n + 1) := by
      rw [PowerSeries.eval₂_trunc_eq_sum_range]
      simp only [PowerSeries.coeff_mk]
      exact remSeq_sum w hw hπ y (n + 1)
    have hzev : z = Polynomial.eval₂ (algebraMap K w.toValuationSubring) π
          (PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ z)))
        + π ^ (n + 1) * remSeq w hw hπ z (n + 1) := by
      rw [PowerSeries.eval₂_trunc_eq_sum_range]
      simp only [PowerSeries.coeff_mk]
      exact remSeq_sum w hw hπ z (n + 1)
    have hAB : Polynomial.eval₂ (algebraMap K w.toValuationSubring) π
          (PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ y)))
        * Polynomial.eval₂ (algebraMap K w.toValuationSubring) π
            (PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ z)))
        = (∑ k ∈ Finset.range (n + 1),
            algebraMap K w.toValuationSubring
                (PowerSeries.coeff k
                  (PowerSeries.mk (expCoeff w hw hπ y)
                    * PowerSeries.mk (expCoeff w hw hπ z)))
              * π ^ k)
          + π ^ (n + 1) * Polynomial.eval₂ (algebraMap K w.toValuationSubring) π Q := by
      rw [← Polynomial.eval₂_mul, hQ, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_X_pow, PowerSeries.eval₂_trunc_eq_sum_range]
    set p := π ^ (n + 1)
    set A := Polynomial.eval₂ (algebraMap K w.toValuationSubring) π
      (PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ y)))
    set B := Polynomial.eval₂ (algebraMap K w.toValuationSubring) π
      (PowerSeries.trunc (n + 1) (PowerSeries.mk (expCoeff w hw hπ z)))
    set ry := remSeq w hw hπ y (n + 1)
    set rz := remSeq w hw hπ z (n + 1)
    set EQ := Polynomial.eval₂ (algebraMap K w.toValuationSubring) π Q
    have hident : y * z
        = (∑ k ∈ Finset.range (n + 1),
            algebraMap K w.toValuationSubring
                (PowerSeries.coeff k
                  (PowerSeries.mk (expCoeff w hw hπ y)
                    * PowerSeries.mk (expCoeff w hw hπ z)))
              * π ^ k)
          + p * (EQ + (A * rz + ry * B + p * (ry * rz))) := by
      conv_lhs => rw [hyev, hzev]
      rw [show (A + p * ry) * (B + p * rz)
          = A * B + p * (A * rz + ry * B + p * (ry * rz)) from by ring, hAB]
      ring
    exact expCoeff_eq_of_eq_sum w hw hπ (n + 1) (y * z)
      (fun j => PowerSeries.coeff j
        (PowerSeries.mk (expCoeff w hw hπ y) * PowerSeries.mk (expCoeff w hw hπ z)))
      (EQ + (A * rz + ry * B + p * (ry * rz))) hident n n.lt_succ_self
  map_zero' := by
    ext n
    rw [PowerSeries.coeff_mk, map_zero]
    have hident : (0 : w.toValuationSubring)
        = (∑ k ∈ Finset.range (n + 1),
            algebraMap K w.toValuationSubring ((0 : K)) * π ^ k)
          + π ^ (n + 1) * 0 := by
      simp
    exact expCoeff_eq_of_eq_sum w hw hπ (n + 1) 0 (fun _ => (0 : K)) 0 hident n
      n.lt_succ_self
  map_add' y z := by
    ext n
    rw [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    have hident : y + z
        = (∑ k ∈ Finset.range (n + 1),
            algebraMap K w.toValuationSubring
                (expCoeff w hw hπ y k + expCoeff w hw hπ z k) * π ^ k)
          + π ^ (n + 1) * (remSeq w hw hπ y (n + 1) + remSeq w hw hπ z (n + 1)) := by
      conv_lhs => rw [remSeq_sum w hw hπ y (n + 1), remSeq_sum w hw hπ z (n + 1)]
      simp only [map_add, add_mul, Finset.sum_add_distrib, mul_add]
      ring
    exact expCoeff_eq_of_eq_sum w hw hπ (n + 1) (y + z)
      (fun j => expCoeff w hw hπ y j + expCoeff w hw hπ z j)
      _ hident n n.lt_succ_self

private theorem coeff_expPS (w : Place K F) (hw : w.deg = 1) {π : w.toValuationSubring}
    (hπ : Irreducible π) (y : w.toValuationSubring) (n : ℕ) :
    PowerSeries.coeff n (expPS w hw hπ y) = expCoeff w hw hπ y n :=
  PowerSeries.coeff_mk n (expCoeff w hw hπ y)

private theorem expPS_algebraMap (w : Place K F) (hw : w.deg = 1) {π : w.toValuationSubring}
    (hπ : Irreducible π) (a : K) :
    expPS w hw hπ (algebraMap K w.toValuationSubring a) = PowerSeries.C a := by
  ext n
  rw [coeff_expPS, PowerSeries.coeff_C]
  have hident : algebraMap K w.toValuationSubring a
      = (∑ k ∈ Finset.range (n + 1),
          algebraMap K w.toValuationSubring (if k = 0 then a else 0) * π ^ k)
        + π ^ (n + 1) * 0 := by
    rw [mul_zero, add_zero, sum_single_coeff w (n + 1) 0 n.succ_pos a, pow_zero, mul_one]
  exact expCoeff_eq_of_eq_sum w hw hπ (n + 1) _ (fun j => if j = 0 then a else 0) 0 hident n
    n.lt_succ_self

private theorem expPS_self (w : Place K F) (hw : w.deg = 1) {π : w.toValuationSubring}
    (hπ : Irreducible π) : expPS w hw hπ π = PowerSeries.X := by
  ext n
  rw [coeff_expPS, PowerSeries.coeff_X]
  rcases n with _ | m
  · have hident : π = (∑ k ∈ Finset.range 1,
          algebraMap K w.toValuationSubring ((0 : K)) * π ^ k)
        + π ^ 1 * 1 := by
      simp
    exact expCoeff_eq_of_eq_sum w hw hπ 1 π (fun _ => (0 : K)) 1 hident 0 Nat.one_pos
  · have hident : π = (∑ k ∈ Finset.range (m + 2),
          algebraMap K w.toValuationSubring (if k = 1 then (1 : K) else 0) * π ^ k)
        + π ^ (m + 2) * 0 := by
      rw [mul_zero, add_zero, sum_single_coeff w (m + 2) 1 (by omega) 1, map_one, pow_one,
        one_mul]
    exact expCoeff_eq_of_eq_sum w hw hπ (m + 2) π (fun j => if j = 1 then (1 : K) else 0) 0
      hident (m + 1) (by omega)

private theorem ord_coe_nonneg (w : Place K F) {y : w.toValuationSubring} (hy : y ≠ 0) :
    0 ≤ w.ord (y : F) := by
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hyF : (y : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hy
  have hπ₀F : (π₀ : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ₀.ne_zero
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hyF hπ₀
  set n0 := w.ord (y : F) with hn0
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (-n0).toNat = m + 1 := ⟨(-n0).toNat - 1, by omega⟩
  have hmul : (y : F) * (π₀ : F) ^ ((-n0).toNat)
      = ((u : w.toValuationSubring) : F) := by
    rw [hu, mul_assoc, ← zpow_natCast ((π₀ : F)), ← zpow_add₀ hπ₀F,
      show n0 + (((-n0).toNat : ℕ) : ℤ) = 0 from by omega, zpow_zero, mul_one]
  have hOw : y * π₀ ^ (m + 1) = (u : w.toValuationSubring) := by
    apply Subtype.coe_injective
    push_cast
    rw [← hm]
    exact hmul
  have hunit : IsUnit π₀ :=
    isUnit_of_dvd_unit ⟨y * π₀ ^ m, by rw [← hOw]; ring⟩ u.isUnit
  exact hπ₀.not_isUnit hunit

private theorem exists_unit_mul_pow (w : Place K F) {y : w.toValuationSubring} (hy : y ≠ 0)
    {π : w.toValuationSubring} (hπ : Irreducible π) :
    ∃ u : w.toValuationSubringˣ,
      y = (u : w.toValuationSubring) * π ^ (w.ord (y : F)).toNat := by
  have hyF : (y : F) ≠ 0 := by simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hy
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hyF hπ
  set n0 := w.ord (y : F) with hn0
  have h0 : 0 ≤ n0 := by rw [hn0]; exact ord_coe_nonneg w hy
  refine ⟨u, Subtype.coe_injective ?_⟩
  push_cast
  rw [hu, ← zpow_natCast ((π : F)), Int.toNat_of_nonneg h0]

private theorem expCoeff_eq_zero_of_lt_ord (w : Place K F) (hw : w.deg = 1)
    {π : w.toValuationSubring} (hπ : Irreducible π) {y : w.toValuationSubring} (hy : y ≠ 0)
    {n : ℕ} (hn : (n : ℤ) < w.ord (y : F)) : expCoeff w hw hπ y n = 0 := by
  obtain ⟨u, hu⟩ := exists_unit_mul_pow w hy hπ
  have hident : y = (∑ k ∈ Finset.range ((w.ord (y : F)).toNat),
        algebraMap K w.toValuationSubring ((0 : K)) * π ^ k)
      + π ^ ((w.ord (y : F)).toNat) * (u : w.toValuationSubring) := by
    conv_lhs => rw [hu]
    simp [mul_comm]
  exact expCoeff_eq_of_eq_sum w hw hπ ((w.ord (y : F)).toNat) y (fun _ => (0 : K))
    (u : w.toValuationSubring) hident n (by omega)

private theorem expCoeff_ord_toNat_ne_zero (w : Place K F) (hw : w.deg = 1)
    {π : w.toValuationSubring} (hπ : Irreducible π) {y : w.toValuationSubring} (hy : y ≠ 0) :
    expCoeff w hw hπ y ((w.ord (y : F)).toNat) ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_unit_mul_pow w hy hπ
  have hrem : remSeq w hw hπ y ((w.ord (y : F)).toNat) = (u : w.toValuationSubring) := by
    have hsum := remSeq_sum w hw hπ y ((w.ord (y : F)).toNat)
    have hz : ∀ k ∈ Finset.range ((w.ord (y : F)).toNat),
        algebraMap K w.toValuationSubring (expCoeff w hw hπ y k) * π ^ k = 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [expCoeff_eq_zero_of_lt_ord w hw hπ hy (by
        have := ord_coe_nonneg w hy
        omega), map_zero, zero_mul]
    rw [Finset.sum_eq_zero hz, zero_add] at hsum
    apply mul_left_cancel₀ (pow_ne_zero ((w.ord (y : F)).toNat) hπ.ne_zero)
    rw [← hsum]
    conv_lhs => rw [hu]
    exact mul_comm _ _
  show resCoeff w hw (remSeq w hw hπ y ((w.ord (y : F)).toNat)) ≠ 0
  rw [hrem]
  have hres : residue w.toValuationSubring (u : w.toValuationSubring) ≠ 0 :=
    (residue_ne_zero_iff_isUnit _).mpr u.isUnit
  intro h0
  apply hres
  have h0' : (resEquiv w hw).symm
      (residue w.toValuationSubring (u : w.toValuationSubring)) = 0 := h0
  have h := congrArg (resEquiv w hw) h0'
  rwa [RingEquiv.apply_symm_apply, map_zero] at h

private theorem ofPowerSeries_expPS_ne_zero (w : Place K F) (hw : w.deg = 1)
    {π : w.toValuationSubring} (hπ : Irreducible π) {y : w.toValuationSubring} (hy : y ≠ 0) :
    HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y) ≠ 0 := by
  have h : (HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y)).coeff
      (((w.ord (y : F)).toNat : ℤ)) ≠ 0 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_expPS]
    exact expCoeff_ord_toNat_ne_zero w hw hπ hy
  exact HahnSeries.ne_zero_of_coeff_ne_zero h

private theorem order_ofPowerSeries_expPS (w : Place K F) (hw : w.deg = 1)
    {π : w.toValuationSubring} (hπ : Irreducible π) {y : w.toValuationSubring} (hy : y ≠ 0) :
    (HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y)).order = w.ord (y : F) := by
  have hx0 := ofPowerSeries_expPS_ne_zero w hw hπ hy
  have hcoeff : (HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y)).coeff
      ((((w.ord (y : F)).toNat : ℕ) : ℤ)) ≠ 0 := by
    rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_expPS]
    exact expCoeff_ord_toNat_ne_zero w hw hπ hy
  have hle : (HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y)).order
      ≤ (((w.ord (y : F)).toNat : ℕ) : ℤ) := HahnSeries.order_le_of_coeff_ne_zero hcoeff
  have hge : ¬ (HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y)).order
      < (((w.ord (y : F)).toNat : ℕ) : ℤ) := by
    intro hlt
    have horder : (HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y)).coeff
        (HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y)).order ≠ 0 :=
      HahnSeries.coeff_order_eq_zero.not.mpr hx0
    rcases lt_or_ge (HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y)).order 0 with hneg | hpos
    · apply horder
      rw [HahnSeries.ofPowerSeries_apply]
      refine HahnSeries.embDomain_of_notMem_range ?_
      rintro ⟨j, hj⟩
      have hj' : ((j : ℤ))
          = (HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y)).order := hj
      omega
    · obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hpos
      apply horder
      rw [hj, HahnSeries.ofPowerSeries_apply_coeff, coeff_expPS]
      refine expCoeff_eq_zero_of_lt_ord w hw hπ hy ?_
      have h0 := ord_coe_nonneg w hy
      omega
  rw [not_lt] at hge
  rw [le_antisymm hle hge, Int.toNat_of_nonneg (ord_coe_nonneg w hy)]

private theorem exists_irreducible_coe_of_ord_eq_one (w : Place K F) {t : F}
    (ht : w.ord t = 1) :
    ∃ tO : w.toValuationSubring, (tO : F) = t ∧ Irreducible tO := by
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht
    simp at ht
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow ht0 hπ₀
  rw [ht, zpow_one] at hu
  refine ⟨(u : w.toValuationSubring) * π₀, ?_, ?_⟩
  · push_cast
    exact hu.symm
  · exact Associated.irreducible ⟨u, mul_comm π₀ (u : w.toValuationSubring)⟩ hπ₀

private theorem exists_algHom_laurentSeries_of_irreducible (w : Place K F) (hw : w.deg = 1)
    {π : w.toValuationSubring} (hπ : Irreducible π) :
    ∃ φ : F →ₐ[K] LaurentSeries K,
      φ (π : F) = HahnSeries.single (1 : ℤ) (1 : K) ∧ ∀ x : F, (φ x).order = w.ord x := by

  have hinj : Function.Injective ((HahnSeries.ofPowerSeries ℤ K).comp (expPS w hw hπ)) :=
    (injective_iff_map_eq_zero _).2 fun y hy =>
      by_contra fun hy0 => ofPowerSeries_expPS_ne_zero w hw hπ hy0 hy
  let φ₀ : F →+* LaurentSeries K := IsFractionRing.lift hinj
  have hφ₀ : ∀ y : w.toValuationSubring,
      φ₀ (y : F) = HahnSeries.ofPowerSeries ℤ K (expPS w hw hπ y) :=
    fun y => IsFractionRing.lift_algebraMap hinj y

  have hcomm : ∀ c : K, φ₀ (algebraMap K F c) = algebraMap K (LaurentSeries K) c := by
    intro c
    rw [← w.coe_algebraMap c, hφ₀, expPS_algebraMap, HahnSeries.ofPowerSeries_C,
      ModularCurve.algebraMap_laurentSeries_eq_single]
    rfl
  refine ⟨{ φ₀ with commutes' := hcomm }, ?_, fun x => ?_⟩
  ·
    change φ₀ (π : F) = _
    rw [hφ₀, expPS_self, HahnSeries.ofPowerSeries_X]
  ·
    change (φ₀ x).order = w.ord x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hx hπ
    have hπ1 : φ₀ (π : F) = HahnSeries.single (1 : ℤ) (1 : K) := by
      rw [hφ₀, expPS_self, HahnSeries.ofPowerSeries_X]
    have hu0 : (u : w.toValuationSubring) ≠ 0 := u.ne_zero
    have hφu0 : φ₀ ((u : w.toValuationSubring) : F) ≠ 0 := by
      rw [hφ₀]
      exact ofPowerSeries_expPS_ne_zero w hw hπ hu0
    have hφu : (φ₀ ((u : w.toValuationSubring) : F)).order = 0 := by
      rw [hφ₀, order_ofPowerSeries_expPS w hw hπ hu0, w.ord_coe_unit]
    have h1 : φ₀ x = φ₀ ((u : w.toValuationSubring) : F)
        * HahnSeries.single (1 : ℤ) (1 : K) ^ w.ord x := by
      rw [congrArg φ₀ hu, map_mul, map_zpow₀, hπ1]
    rw [h1, HahnSeries.order_mul hφu0
        (zpow_ne_zero _ (HahnSeries.single_ne_zero one_ne_zero)),
      hφu, zero_add, ← RatFunc.single_zpow, HahnSeries.order_single one_ne_zero]

private theorem exists_algHom_laurentSeries_of_deg_eq_one (w : Place K F) (hw : w.deg = 1)
    (t : F) (ht : w.ord t = 1) :
    ∃ φ : F →ₐ[K] LaurentSeries K,
      φ t = HahnSeries.single (1 : ℤ) (1 : K) ∧ ∀ x : F, (φ x).order = w.ord x := by
  obtain ⟨π, rfl, hπ⟩ := exists_irreducible_coe_of_ord_eq_one w ht
  exact exists_algHom_laurentSeries_of_irreducible w hw hπ

private theorem exists_algHom_laurentSeries_order_eq_ord (w : Place K F) (hw : w.deg = 1) :
    ∃ φ : F →ₐ[K] LaurentSeries K, ∀ x : F, (φ x).order = w.ord x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨φ, -, hφ⟩ := exists_algHom_laurentSeries_of_irreducible w hw hπ
  exact ⟨φ, hφ⟩

end LaurentSeriesModel

end Place

end AlgebraicCurve

namespace AlgebraicCurve

-- pin: AlgebraicCurve.Place.exists_algHom_laurentSeries_of_deg_eq_one (Theorems/Thm_AlgebraicCurve_Place_exists_algHom_laurentSeries_of_deg_eq_one.lean:7)
theorem Place.exists_algHom_laurentSeries_of_deg_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F) (hw : w.deg = 1)
    (t : F) (ht : w.ord t = 1) :
    ∃ φ : F →ₐ[K] LaurentSeries K,
      φ t = HahnSeries.single (1 : ℤ) (1 : K) ∧ ∀ x : F, (φ x).order = w.ord x :=
  Place.LaurentSeriesModel.exists_algHom_laurentSeries_of_deg_eq_one w hw t ht

end AlgebraicCurve

/- The `K`-algebra structure on `HahnSeries ℚ K` is a diamond in `Mathlib`: both
`HahnSeries.instAlgebra` (`C` of the base constants) and `HahnSeries.powerSeriesAlgebra`
(through `PowerSeries`) apply, and which of them instance resolution picks depends on the
module's import order. `Place.exists_ord_mul_eq_order_of_hasRamBound`
(`Place/ValueDictionary.lean`) is stated with `HahnSeries.instAlgebra`, so the block below
pins that instance locally; this also makes the two constant lemmas below the
`instAlgebra` form of `HahnSeries.C_eq_algebraMap`. The attribute is `local`, so it ends
with this file and no importer sees it. -/
attribute [local instance 2000] HahnSeries.instAlgebra

namespace AlgebraicCurve

namespace Place

namespace LaurentSeriesModel

section Transport

variable {K : Type*} [Field K]

/-- The Puiseux embedding of a Laurent series over `ℤ` into `HahnSeries ℚ K` lands in
the series ramified of denominator `e`: every support point of the image is `k / e`. -/
theorem hasRamBound_puiseuxRamEmb {e : ℕ} (he : 0 < e) (x : LaurentSeries K) :
    HahnSeries.HasRamBound e (HahnSeries.puiseuxRamEmb he x) := by
  intro q hq
  have hq' : q ∈ ⇑(HahnSeries.ramScale e) '' x.support := by
    simpa [HahnSeries.puiseuxRamEmb, HahnSeries.embDomainRingHom] using
      HahnSeries.support_embDomain_subset hq
  obtain ⟨k, -, rfl⟩ := hq'
  exact ⟨k, rfl⟩

/-- The order of a Puiseux-embedded Laurent series is the rescaled order of the
series: the exponents are divided by `e`. -/
theorem order_puiseuxRamEmb {e : ℕ} (he : 0 < e) (x : LaurentSeries K) :
    (HahnSeries.puiseuxRamEmb he x).order = HahnSeries.ramScale e x.order := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : HahnSeries.puiseuxRamEmb (K := K) he x ≠ 0 := by
      intro h0
      exact hx ((HahnSeries.puiseuxRamEmb (K := K) he).injective (by rw [h0, map_zero]))
    have h2 : (HahnSeries.puiseuxRamEmb (K := K) he x).orderTop
        = WithTop.map (⇑(HahnSeries.ramScale e)) x.orderTop :=
      HahnSeries.orderTop_embDomain
    have h1 := HahnSeries.order_eq_orderTop_of_ne_zero hx'
    rw [h2, ← HahnSeries.order_eq_orderTop_of_ne_zero hx, WithTop.map_coe] at h1
    exact_mod_cast h1

/-- The constants of `LaurentSeries K` are the constant Hahn series. -/
theorem laurentAlgebraMap_eq_C (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  rw [HahnSeries.C_eq_algebraMap]

/-- The constants of `HahnSeries ℚ K` are the constant Hahn series. -/
theorem hahnQAlgebraMap_eq_C (c : K) :
    algebraMap K (HahnSeries ℚ K) c = HahnSeries.C c := by
  rw [HahnSeries.C_eq_algebraMap]

end Transport

section Lift

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

/-- Transporting a `K`-algebra map into `LaurentSeries K` along the Puiseux embedding
gives a `K`-algebra map into `HahnSeries ℚ K`; its values are ramified of denominator
`1` and its order is the order of the original map. -/
def liftToHahn (ι : F →ₐ[K] LaurentSeries K) : F →ₐ[K] HahnSeries ℚ K where
  toRingHom := (HahnSeries.puiseuxRamEmb one_pos).comp ι.toRingHom
  commutes' := by
    intro c
    show HahnSeries.puiseuxRamEmb one_pos (ι (algebraMap K F c))
        = algebraMap K (HahnSeries ℚ K) c
    rw [ι.commutes c, laurentAlgebraMap_eq_C, hahnQAlgebraMap_eq_C]
    exact HahnSeries.embDomainRingHom_C

/-- The order of a lifted map is the order of the original map, the ramification
denominator being `1`. -/
theorem order_liftToHahn (ι : F →ₐ[K] LaurentSeries K) (x : F) :
    (liftToHahn ι x).order = ((ι x).order : ℚ) := by
  rw [show liftToHahn ι x = HahnSeries.puiseuxRamEmb one_pos (ι x) from rfl,
    order_puiseuxRamEmb one_pos, HahnSeries.ramScale_apply]
  simp

end Lift

/-- **A non-trivial `K`-algebra map into `LaurentSeries K` is a rescaled order map.**
The pin's private form of the headline: if `ι : F →ₐ[K] LaurentSeries K` is not
order-trivial, there are a place `w` of `F` and a positive integer `γ` with
`w.ord x * γ = (ι x).order` for all `x`.  The lift `liftToHahn ι` into `HahnSeries ℚ K`
is ramified of denominator `1` and has the same order, so
`Place.exists_ord_mul_eq_order_of_hasRamBound` applies to it; the scaling `γ` is the
order of `ι` at a uniformiser. -/
private theorem exists_ord_mul_eq_order_of_algHom_laurentSeries
    (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F]
    (ι : F →ₐ[K] LaurentSeries K) (h : ∃ x : F, (ι x).order ≠ 0) :
    ∃ (w : Place K F) (γ : ℕ), 0 < γ ∧ ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order := by
  obtain ⟨x₀, hx₀⟩ := h
  have hnt : ∃ x : F, ((liftToHahn ι) x).order ≠ 0 :=
    ⟨x₀, by rw [order_liftToHahn]; exact_mod_cast hx₀⟩
  have hRB : ∀ x : F, HahnSeries.HasRamBound 1 ((liftToHahn ι) x) :=
    fun x => hasRamBound_puiseuxRamEmb one_pos (ι x)
  obtain ⟨w, g, hg, hgw⟩ :=
    Place.exists_ord_mul_eq_order_of_hasRamBound (liftToHahn ι) one_pos hRB hnt
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have hordπ : w.ord (π : F) = 1 := w.ord_coe_irreducible hπ
  have hgval : g = ((ι (π : F)).order : ℚ) := by
    have h1 := hgw (π : F)
    rw [hordπ, order_liftToHahn] at h1
    simpa using h1
  have hpos : 0 < (ι (π : F)).order := by
    rw [hgval] at hg
    exact_mod_cast hg
  refine ⟨w, ((ι (π : F)).order).toNat, by omega, fun x => ?_⟩
  have h1 := hgw x
  rw [hgval, order_liftToHahn] at h1
  have h2 : w.ord x * (ι (π : F)).order = (ι x).order := by exact_mod_cast h1
  rw [Int.toNat_of_nonneg hpos.le]
  exact h2

end LaurentSeriesModel

/-- **A non-trivial `K`-algebra map into `LaurentSeries K` is a rescaled order map.**
Statement from
`Theorems/Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries.lean`;
the public wrapper of the pin's `solution`, around the private form above. -/
theorem exists_ord_mul_eq_order_of_algHom_laurentSeries (K : Type*) [Field K] {F : Type*}
    [Field F] [Algebra K F] (ι : F →ₐ[K] LaurentSeries K)
    (h : ∃ x : F, (ι x).order ≠ 0) :
    ∃ (w : Place K F) (γ : ℕ), 0 < γ ∧ ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order :=
  LaurentSeriesModel.exists_ord_mul_eq_order_of_algHom_laurentSeries (F := F) K ι h

end Place

end AlgebraicCurve
