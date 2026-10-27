/-
The degree identity `deg (x)_∞ = [F : K(x)]` for `x` transcendental over `K`: the pole
divisor `D` of `x`, given pointwise by `D v = max 0 (-(ord_v x))`, has degree the degree
of the field extension `[F : K(x)]`.

The two inequalities are Riemann–Roch counts.  For `[F : K(x)] ≤ deg D` one takes a
`K[x]`-integral basis `u` of `F` over `K(x)`: at a place where `x` is integral so are the
`u i`, and at the finitely many poles of `x` their orders are bounded by a constant `c`,
so the products `x ^ j * u i` (`0 ≤ j ≤ m - c`) are `K`-linearly independent elements of
`L(m D)` and number `n (m - c + 1)`; Riemann's inequality `ℓ(m D) ≤ m deg D + ℓ(0)` then
forces `n ≤ deg D`.  For `deg D ≤ [F : K(x)]` one counts residues: at each `v` in the
support of `D` a `K`-basis of the residue field `κ(v)` is lifted to elements regular
everywhere on the support, weak approximation supplies an element which is `1` at `v` and
`0` at the other places of the support, and the products `z k * t v ^ (-(a + 1))` for
`a < D v` are `K(x)`-linearly independent; their number is `deg D` and exceeds the
dimension `[F : K(x)]` otherwise.

Statements are transcribed verbatim from the pinned FLT (`aa2d8b3`); the proofs are
adapted from the three `P2M/Sol/S_` files named below.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord.lean

spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.Place.Approximation
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero IsLocalRing Polynomial
open scoped IntermediateField

-- The `letI`/`haveI` instance walls in the place sections are load-bearing — they
-- register the `algebraAlong`/`isScalarTower_along` instances the following tactic needs —
-- so the style linter's `let`/`have` suggestion does not apply; cf. `Genus/Index.lean`.
set_option linter.style.haveILetI false

namespace AlgebraicCurve

namespace Divisor

set_option linter.style.haveILetI false in
/-- Riemann–Roch in the form of a count: `[F : K(x)] ≤ deg (x)_∞`. -/
theorem finrank_adjoin_le_degree_of_eq_max_neg_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) ≤ Divisor.degree D := by
  classical

  set E : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hE
  set n : ℕ := Module.finrank E F with hn

  have hxE_mem : x ∈ E := IntermediateField.mem_adjoin_simple_self K x
  set xE : E := ⟨x, hxE_mem⟩ with hxE
  have hxE_coe : (xE : F) = x := rfl

  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have hxE0 : xE ≠ 0 := fun h => hx0 (by rw [← hxE_coe, h]; rfl)

  have hxE_trans : Transcendental K xE := by
    intro halg
    exact hx halg.algebraMap

  set A : Subalgebra K E := Algebra.adjoin K ({xE} : Set E) with hA
  have hA_dom : IsDomain A := inferInstance

  haveI hfrac : IsFractionRing A E := by

    refine IsFractionRing.of_field A E fun z => ?_

    obtain ⟨r, s, hzrs⟩ :=
      (IntermediateField.mem_adjoin_simple_iff K (x := (z : F))).mp z.2

    have hrA : Polynomial.aeval xE r ∈ A := by
      rw [hA, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨r, rfl⟩
    have hsA : Polynomial.aeval xE s ∈ A := by
      rw [hA, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨s, rfl⟩
    refine ⟨⟨_, hrA⟩, ⟨_, hsA⟩, ?_⟩

    apply Subtype.ext
    have hcoeR : ((Polynomial.aeval xE r : E) : F) = Polynomial.aeval x r := by
      have : xE = IntermediateField.AdjoinSimple.gen K x := rfl
      rw [this]; exact IntermediateField.AdjoinSimple.coe_aeval_gen_apply (F := K) (α := x) (f := r)
    have hcoeS : ((Polynomial.aeval xE s : E) : F) = Polynomial.aeval x s := by
      have : xE = IntermediateField.AdjoinSimple.gen K x := rfl
      rw [this]; exact IntermediateField.AdjoinSimple.coe_aeval_gen_apply (F := K) (α := x) (f := s)
    show (z : F) = ((algebraMap A E ⟨_, hrA⟩ / algebraMap A E ⟨_, hsA⟩ : E) : F)
    rw [show algebraMap A E ⟨_, hrA⟩ = Polynomial.aeval xE r from rfl,
        show algebraMap A E ⟨_, hsA⟩ = Polynomial.aeval xE s from rfl,
        IntermediateField.coe_div, hcoeR, hcoeS, hzrs]

  obtain ⟨s, b, hint⟩ := FiniteDimensional.exists_is_basis_integral A E F

  have hcard : Fintype.card s = n := (Module.finrank_eq_card_basis b).symm
  let e : Fin n ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  set u : Fin n → F := fun i => b (e i) with hu
  have hu_indep : LinearIndependent E u := (b.linearIndependent.comp e (e.injective))
  have hu_int : ∀ i, IsIntegral A (u i) := fun i => hint (e i)

  have hu_intF : ∀ i, IsIntegral (Algebra.adjoin K ({x} : Set F)) (u i) := by
    intro i

    have hrange : ∀ a : A, algebraMap A F a ∈ Algebra.adjoin K ({x} : Set F) := by
      intro a
      have hmap : (Algebra.adjoin K ({xE} : Set E)).map (IsScalarTower.toAlgHom K E F)
          = Algebra.adjoin K ({x} : Set F) := by
        rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
      have ha : algebraMap A F a = (IsScalarTower.toAlgHom K E F) (a : E) := rfl
      rw [ha, ← hmap]
      exact ⟨(a : E), hA ▸ a.2, rfl⟩
    let φ : A →+* Algebra.adjoin K ({x} : Set F) :=
      (algebraMap A F).codRestrict _ hrange
    have hcomp : (algebraMap (Algebra.adjoin K ({x} : Set F)) F).comp φ = algebraMap A F := by
      ext a; rfl
    exact (hu_int i).map_of_comp_eq φ (RingHom.id F) (by rw [RingHom.id_comp, hcomp])

  have hu_reg : ∀ i, ∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord (u i) := by
    intro i v hvx
    have hxmem : x ∈ v.toValuationSubring := v.mem_of_ord_nonneg hx0 hvx
    exact v.ord_nonneg_of_mem
      (v.mem_toValuationSubring_of_isIntegral_adjoin hxmem (hu_intF i))

  have hDeff : (0 : Divisor K F) ≤ D := by
    intro v; rw [hD]; exact le_max_left 0 _
  have hDeff' : ∀ m : ℕ, (0 : Divisor K F) ≤ m • D := fun m => nsmul_nonneg hDeff m

  have hDsupp : ∀ v ∈ D.support, (1 : ℤ) ≤ D v := by
    intro v hv
    have hne : D v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have hge : 0 ≤ D v := hDeff v
    omega
  obtain ⟨c, hc⟩ : ∃ c : ℕ, ∀ i, u i ∈ LSpace (c • D) := by
    refine ⟨(Finset.univ : Finset (Fin n)).sup fun i =>
      D.support.sup fun v => (-(v.ord (u i))).toNat, fun i => ?_⟩
    set c := (Finset.univ : Finset (Fin n)).sup fun i =>
      D.support.sup fun v => (-(v.ord (u i))).toNat
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (u i) 0 with h0 | h0
    · exact Or.inl h0
    refine Or.inr fun v => ?_
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
    rcases le_or_gt 0 (v.ord x) with hvx | hvx
    ·
      have hDv0 : D v = 0 := by rw [hD]; exact max_eq_left (by omega)
      rw [hDv0, mul_zero, neg_zero]
      exact hu_reg i v hvx
    ·
      have hvsupp : v ∈ D.support := Finsupp.mem_support_iff.mpr (by rw [hD]; omega)
      have hDv1 : (1 : ℤ) ≤ D v := hDsupp v hvsupp
      have hcle : (-(v.ord (u i))).toNat ≤ c := by
        refine le_trans ?_ (Finset.le_sup (f := fun i => D.support.sup fun v => (-(v.ord (u i))).toNat) (Finset.mem_univ i))
        exact Finset.le_sup (f := fun w => (-(w.ord (u i))).toNat) hvsupp
      have hcge : -(c : ℤ) ≤ v.ord (u i) := by
        have := Int.toNat_le.mp hcle
        omega
      nlinarith [Int.natCast_nonneg c, hDv1]

  have hx_li : LinearIndependent K (fun j : ℕ => xE ^ j) :=
    linearIndependent_pow_of_transcendental (K := K) (A := E) hxE_trans
  have hli : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * u p.2) := by
    have := linearIndependent_pow_mul (K := K) (E := E) (F := F) hx_li hu_indep
    simpa only [show algebraMap E F xE = x from hxE_coe] using this

  have hmem : ∀ m, c ≤ m → ∀ (j : ℕ) (i : Fin n), j ≤ m - c → x ^ j * u i ∈ LSpace (m • D) := by
    intro m hm j i hj
    rw [mem_lSpace_iff_ord]
    rcases eq_or_ne (x ^ j * u i) 0 with h0 | h0
    · exact Or.inl h0
    refine Or.inr fun v => ?_
    have hui0 : u i ≠ 0 := fun h => h0 (by rw [h, mul_zero])
    have hxj0 : (x : F) ^ j ≠ 0 := pow_ne_zero j hx0
    rw [v.ord_mul hxj0 hui0, show ((x : F) ^ j) = x ^ (j : ℤ) from (zpow_natCast x j).symm,
      v.ord_zpow]
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
    have huiL := (mem_lSpace_iff_ord.mp (hc i)).resolve_left hui0 v
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul] at huiL

    rcases le_or_gt 0 (v.ord x) with hvx | hvx
    · have hDv0 : D v = 0 := by rw [hD]; exact max_eq_left (by omega)
      rw [hDv0, mul_zero, neg_zero]
      exact add_nonneg (mul_nonneg (Int.natCast_nonneg j) hvx) (hu_reg i v hvx)
    · have hDv : D v = -v.ord x := by rw [hD]; exact max_eq_right (by omega)

      have hjc : (j : ℤ) + c ≤ m := by omega
      have hDvpos : 0 ≤ D v := hDeff v
      have hmj : (m : ℤ) - j ≥ c := by omega
      nlinarith [huiL, mul_le_mul_of_nonneg_right hjc hDvpos, hDv]

  have hlow : ∀ m, c ≤ m → (n : ℤ) * (m - c + 1) ≤ ell (m • D) := by
    intro m hm
    haveI : FiniteDimensional K (LSpace (m • D)) := finiteDimensional_lSpace (m • D)

    set ι := Fin (m - c + 1) × Fin n
    have hli' : LinearIndependent K (fun p : ι => (⟨x ^ (p.1 : ℕ) * u p.2,
        hmem m hm p.1 p.2 (by omega)⟩ : LSpace (m • D))) := by
      have hinj : Function.Injective
          (fun p : ι => ((p.1 : ℕ), p.2) : ι → ℕ × Fin n) := by
        intro p q hpq; simp only [Prod.mk.injEq, Fin.val_inj] at hpq
        exact Prod.ext hpq.1 hpq.2
      have hcomp := hli.comp _ hinj
      rw [LinearIndependent] at hcomp ⊢

      have hker := hcomp

      refine LinearIndependent.of_comp (LSpace (m • D)).subtype ?_
      exact hcomp
    have hcard : Fintype.card ι = (m - c + 1) * n := by
      simp [ι, Fintype.card_prod, Fintype.card_fin]
    calc (n : ℤ) * (m - c + 1)
        = ((m - c + 1) * n : ℕ) := by push_cast [Nat.cast_sub hm]; ring
      _ = (Fintype.card ι : ℤ) := by rw [hcard]
      _ ≤ (Module.finrank K (LSpace (m • D)) : ℤ) := by
          exact_mod_cast hli'.fintype_card_le_finrank
      _ = ell (m • D) := rfl

  have hhigh : ∀ m : ℕ, (ell (m • D) : ℤ) ≤ m * Divisor.degree D + ell (0 : Divisor K F) := by
    intro m
    have := ell_le_degree_add_ellZero (hDeff' m)
    rwa [Divisor.degree.map_nsmul, nsmul_eq_mul] at this

  by_contra hlt
  push Not at hlt
  have hngt : (Divisor.degree D : ℤ) + 1 ≤ n := by omega

  set m := c + n * c + ell (0 : Divisor K F) + 1 with hmdef
  have hm_ge_c : c ≤ m := by omega
  have hcombine := le_trans (hlow m hm_ge_c) (hhigh m)

  have hdeg_le : Divisor.degree D ≤ (n : ℤ) - 1 := by omega
  have hmZ : (m : ℤ) = c + n * c + ell (0 : Divisor K F) + 1 := by
    simp only [hmdef]; push_cast; ring
  have hmdd : (m : ℤ) * Divisor.degree D ≤ m * (n - 1) :=
    mul_le_mul_of_nonneg_left hdeg_le (Int.natCast_nonneg m)
  have hstep : (n : ℤ) * m - n * c + n ≤ m * n - m + ell (0 : Divisor K F) := by
    have := le_trans hcombine (by linarith [hmdd])
    nlinarith [this]
  have hcontra : (m : ℤ) ≤ n * c - n + ell (0 : Divisor K F) := by linarith
  linarith [hmZ, Int.natCast_nonneg c, Int.natCast_nonneg n, Int.natCast_nonneg (ell (0 : Divisor K F))]

set_option linter.style.haveILetI false in
/-- Riemann's inequality in the other direction: `deg (x)_∞ ≤ [F : K(x)]`. -/
theorem degree_le_finrank_adjoin_of_eq_max_neg_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D ≤ (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) := by
  classical
  set E : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hE
  set n : ℕ := Module.finrank E F with hn
  have hx0 : x ≠ 0 := fun h => hx (h ▸ isAlgebraic_zero)
  have hxE_mem : x ∈ E := IntermediateField.mem_adjoin_simple_self K x
  set xE : E := ⟨x, hxE_mem⟩ with hxE_def
  have hxE0 : xE ≠ 0 := fun h => hx0 (by rw [← show ((xE:F)=x) from rfl, h]; rfl)
  set S : Finset (Place K F) := D.support with hS
  have hSpole : ∀ v ∈ S, v.ord x < 0 := by
    intro v hv; have := Finsupp.mem_support_iff.mp hv; rw [hD] at this; omega
  have hDv : ∀ v ∈ S, D v = -v.ord x := by
    intro v hv; rw [hD]; exact max_eq_right (by linarith [hSpole v hv])
  have hDvpos : ∀ v ∈ S, 1 ≤ D v := by
    intro v hv; have := hSpole v hv; rw [hDv v hv]; omega
  have hdegD : Divisor.degree D = ∑ v ∈ S, D v * (v.deg : ℤ) := by
    rw [Divisor.degree_eq_sum_support, hS]

  have hmem_max : ∀ (v : Place K F) (f : F) (hf : f ∈ v.toValuationSubring),
      0 < v.ord f → (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    intro v f hf hord
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hval := (v.adicValuation_coe_eq_one_iff ⟨f, hf⟩).mpr hu
    simp only [Place.ord, hval, WithZero.log_one, neg_zero] at hord
    exact lt_irrefl 0 hord

  have hunit_iff : ∀ (v : Place K F) (a : v.toValuationSubring),
      IsUnit a ↔ IsLocalRing.residue _ a ≠ 0 := by
    intro v a
    rw [ne_eq, ← not_iff_not, not_not, ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal]
    exact Ideal.Quotient.eq_zero_iff_mem.symm

  have hres_K : ∀ (v : Place K F) (c : K),
      IsLocalRing.residue _ (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring)
        = algebraMap K v.ResidueField c := fun v c => v.residue_algebraMap c

  have hord_K : ∀ (v : Place K F) (c : K), c ≠ 0 → v.ord (algebraMap K F c) = 0 :=
    fun v c _ => v.ord_algebraMap c

  have hkey : ∀ v ∈ S, ∀ p : K[X], p ≠ 0 →
      ∃ h : aeval x p * x ^ (-(p.natDegree : ℤ)) ∈ v.toValuationSubring,
        IsUnit (⟨_, h⟩ : v.toValuationSubring) ∧
        IsLocalRing.residue _ ⟨_, h⟩ = algebraMap K v.ResidueField p.leadingCoeff := by
    intro v hv p hp
    set d := p.natDegree with hd
    have hld : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp

    have hexpand : aeval x p * x ^ (-(d:ℤ)) =
        algebraMap K F p.leadingCoeff +
        ∑ i ∈ Finset.range d, algebraMap K F (p.coeff i) * x ^ ((i:ℤ) - d) := by
      rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
          show p.coeff d = p.leadingCoeff from rfl, add_mul, Finset.sum_mul,
          add_comm]
      congr 1
      · rw [Algebra.smul_def, mul_assoc, ← zpow_natCast x d, ← zpow_add₀ hx0,
            add_neg_cancel, zpow_zero, mul_one]
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [Algebra.smul_def, mul_assoc, ← zpow_natCast x i, ← zpow_add₀ hx0]
        ring_nf

    have hterm_mem : ∀ i ∈ Finset.range d,
        algebraMap K F (p.coeff i) * x ^ ((i:ℤ) - d) ∈ v.toValuationSubring := by
      intro i hi
      rcases eq_or_ne (p.coeff i) 0 with hci | hci
      · simp [hci]
      · refine v.mem_of_ord_nonneg
          (mul_ne_zero ((map_ne_zero_iff _ (algebraMap K F).injective).mpr hci)
            (zpow_ne_zero _ hx0)) ?_
        rw [v.ord_mul ((map_ne_zero_iff _ (algebraMap K F).injective).mpr hci)
              (zpow_ne_zero _ hx0), hord_K v _ hci, zero_add, v.ord_zpow]
        have hlt : (i:ℤ) - d < 0 := by have := Finset.mem_range.mp hi; omega
        exact le_of_lt (mul_pos_of_neg_of_neg hlt (hSpole v hv))
    have hterm_max : ∀ (i : ℕ) (hi : i ∈ Finset.range d),
        (⟨_, hterm_mem i hi⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
      intro i hi
      rcases eq_or_ne (p.coeff i) 0 with hci | hci
      · have : (⟨_, hterm_mem i hi⟩ : v.toValuationSubring) = 0 := by
          refine Subtype.ext ?_; simp [hci]
        rw [this]; exact Ideal.zero_mem _
      · refine hmem_max v _ _ ?_
        rw [v.ord_mul ((map_ne_zero_iff _ (algebraMap K F).injective).mpr hci)
              (zpow_ne_zero _ hx0), hord_K v _ hci, zero_add, v.ord_zpow]
        have hlt : (i:ℤ) - d < 0 := by have := Finset.mem_range.mp hi; omega
        exact mul_pos_of_neg_of_neg hlt (hSpole v hv)
    set r : F := ∑ i ∈ Finset.range d, algebraMap K F (p.coeff i) * x ^ ((i:ℤ) - d) with hrdef
    have hrmem : r ∈ v.toValuationSubring := sum_mem hterm_mem
    have hrmax : (⟨r, hrmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
      have : (⟨r, hrmem⟩ : v.toValuationSubring)
          = ∑ i ∈ (Finset.range d).attach, ⟨_, hterm_mem i.1 i.2⟩ := by
        refine Subtype.ext ?_
        push_cast
        rw [Finset.sum_attach (Finset.range d)
          (fun i => algebraMap K F (p.coeff i) * x ^ ((i:ℤ) - d))]
      rw [this]
      exact Ideal.sum_mem _ fun i _ => hterm_max i.1 i.2
    have hcmem : algebraMap K F p.leadingCoeff ∈ v.toValuationSubring := v.algebraMap_mem' _
    have hsummem : aeval x p * x ^ (-(d:ℤ)) ∈ v.toValuationSubring := by
      rw [hexpand]; exact add_mem hcmem hrmem
    have hsplit : (⟨_, hsummem⟩ : v.toValuationSubring)
        = ⟨algebraMap K F p.leadingCoeff, hcmem⟩ + ⟨r, hrmem⟩ :=
      Subtype.ext hexpand
    have hres_eq : IsLocalRing.residue _ (⟨_, hsummem⟩ : v.toValuationSubring)
        = algebraMap K v.ResidueField p.leadingCoeff := by
      rw [hsplit, map_add, hres_K]
      have : IsLocalRing.residue _ (⟨r, hrmem⟩ : v.toValuationSubring) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).mpr hrmax
      rw [this, add_zero]
    exact ⟨hsummem,
      (hunit_iff v _).mpr (hres_eq ▸
        (map_ne_zero_iff _ (algebraMap K v.ResidueField).injective).mpr hld),
      hres_eq⟩

  have haeval_ne_zero : ∀ p : K[X], p ≠ 0 → aeval x p ≠ 0 :=
    fun p hp h => hx ⟨p, hp, h⟩
  have hord_aeval : ∀ v ∈ S, ∀ p : K[X], p ≠ 0 →
      v.ord (aeval x p) = (p.natDegree : ℤ) * v.ord x := by
    intro v hv p hp
    obtain ⟨hmem, hunit, _⟩ := hkey v hv p hp
    have hordu : v.ord (aeval x p * x ^ (-(p.natDegree:ℤ))) = 0 := by
      have := (v.adicValuation_coe_eq_one_iff ⟨_, hmem⟩).mpr hunit
      simp only [Place.ord, this, WithZero.log_one, neg_zero]
    rw [v.ord_mul (haeval_ne_zero p hp) (zpow_ne_zero _ hx0), v.ord_zpow] at hordu
    linarith

  have hord_E : ∀ g : E, (g:F) ≠ 0 → ∃ q : ℤ, ∀ v ∈ S, v.ord (g:F) = q * D v := by
    intro g hg0
    obtain ⟨r, s, hgrs⟩ := (IntermediateField.mem_adjoin_simple_iff K (x := (g:F))).mp g.2
    have hs0 : s ≠ 0 := by
      rintro rfl; simp only [map_zero, div_zero] at hgrs; exact hg0 hgrs
    have hr0 : r ≠ 0 := by
      rintro rfl; simp only [map_zero, zero_div] at hgrs; exact hg0 hgrs
    refine ⟨-(r.natDegree - s.natDegree), fun v hv => ?_⟩
    rw [hgrs, div_eq_mul_inv,
        v.ord_mul (haeval_ne_zero r hr0) (inv_ne_zero (haeval_ne_zero s hs0)),
        v.ord_inv, hord_aeval v hv r hr0, hord_aeval v hv s hs0, hDv v hv]
    ring

  have hres_E : ∀ v ∈ S, ∀ g : E, (g:F) ≠ 0 → v.ord (g:F) = 0 →
      ∃ c : K, c ≠ 0 ∧ ∀ hmem : (g:F) ∈ v.toValuationSubring,
        IsLocalRing.residue _ (⟨(g:F), hmem⟩ : v.toValuationSubring) = algebraMap K v.ResidueField c := by
    intro v hv g hg0 hord0
    obtain ⟨r, s, hgrs⟩ := (IntermediateField.mem_adjoin_simple_iff K (x := (g:F))).mp g.2
    have hs0 : s ≠ 0 := by rintro rfl; simp only [map_zero, div_zero] at hgrs; exact hg0 hgrs
    have hr0 : r ≠ 0 := by rintro rfl; simp only [map_zero, zero_div] at hgrs; exact hg0 hgrs
    have hdeg : (r.natDegree : ℤ) = s.natDegree := by
      have := hord_aeval v hv r hr0; have hs := hord_aeval v hv s hs0
      have h1 : v.ord (g:F) = (r.natDegree - s.natDegree : ℤ) * v.ord x := by
        rw [hgrs, div_eq_mul_inv, v.ord_mul (haeval_ne_zero r hr0)
            (inv_ne_zero (haeval_ne_zero s hs0)), v.ord_inv, this, hs]; ring
      rw [hord0] at h1
      have hvx := hSpole v hv
      have : (r.natDegree : ℤ) - s.natDegree = 0 := by
        by_contra hne
        exact absurd h1 (mul_ne_zero hne (ne_of_lt hvx)).symm
      linarith
    obtain ⟨hmr, hur, hresr⟩ := hkey v hv r hr0
    obtain ⟨hms, hus, hress⟩ := hkey v hv s hs0
    refine ⟨r.leadingCoeff / s.leadingCoeff,
      div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hr0) (Polynomial.leadingCoeff_ne_zero.mpr hs0),
      fun hmem => ?_⟩

    have hgval : (⟨(g:F), hmem⟩ : v.toValuationSubring) * ⟨_, hms⟩ = ⟨_, hmr⟩ := by
      refine Subtype.ext ?_
      show (g:F) * (aeval x s * x ^ (-(s.natDegree:ℤ))) = aeval x r * x ^ (-(r.natDegree:ℤ))
      rw [hgrs, div_mul_eq_mul_div, mul_div_assoc,
          mul_div_cancel_left₀ _ (haeval_ne_zero s hs0),
          show (r.natDegree:ℤ) = s.natDegree from hdeg]
    have hres_mul := congrArg (IsLocalRing.residue v.toValuationSubring) hgval
    rw [map_mul, hress, hresr] at hres_mul
    rw [map_div₀]
    exact (div_eq_of_eq_mul
      ((map_ne_zero_iff _ (algebraMap K v.ResidueField).injective).mpr
        (Polynomial.leadingCoeff_ne_zero.mpr hs0)) hres_mul.symm).symm

  have hex_t : ∀ v ∈ S, ∃ t : F, t ≠ 0 ∧ v.ord t = 1 ∧ ∀ v' ∈ S, v' ≠ v → v'.ord t = 0 := by
    intro v hv
    obtain ⟨t, ht0, htord⟩ := Place.exists_forall_ord_eq S (fun w => if w = v then 1 else 0)
    exact ⟨t, ht0, by simpa using htord v hv, fun v' hv' hne => by simpa [hne] using htord v' hv'⟩
  choose! t ht0 htv htv' using hex_t

  haveI hfinres : ∀ v : Place K F, Module.Finite K v.ResidueField := IsCurveOver.finiteResidue
  have hex_z : ∀ (v : Place K F) (hv : v ∈ S),
      ∃ (z : Fin v.deg → F) (hreg : ∀ k, ∀ v' ∈ S, z k ∈ v'.toValuationSubring),
      (∀ k, IsUnit (⟨z k, hreg k v hv⟩ : v.toValuationSubring)) ∧
      LinearIndependent K (fun k => IsLocalRing.residue _
        (⟨z k, hreg k v hv⟩ : v.toValuationSubring)) := by
    intro v hv
    haveI := hfinres v
    let bκ : Module.Basis (Fin v.deg) K v.ResidueField := Module.finBasis K v.ResidueField
    choose z₀ hz₀ using fun k =>
      Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal v.toValuationSubring) (bκ k)
    have hz₀' : ∀ k, IsLocalRing.residue _ (z₀ k) = bκ k := hz₀

    set zF : Fin v.deg → F := fun k => (z₀ k : F) with hzF
    have hzF_v : ∀ k, zF k ∈ v.toValuationSubring := fun k => (z₀ k).2
    have hzF_z₀ : ∀ k, (⟨zF k, hzF_v k⟩ : v.toValuationSubring) = z₀ k := fun k => rfl

    set N : ℕ := (Finset.univ : Finset (Fin v.deg)).sup fun k =>
      S.sup fun v' => (-(v'.ord (zF k))).toNat with hN
    obtain ⟨c, hc0, hcord⟩ := Place.exists_forall_ord_eq S
      (fun w => if w = v then 0 else (N : ℤ))
    have hcmem : ∀ v' ∈ S, c ∈ v'.toValuationSubring := by
      intro v' hv'
      refine v'.mem_of_ord_nonneg hc0 ?_
      rw [hcord v' hv']; split_ifs <;> positivity
    set cv : v.toValuationSubring := ⟨c, hcmem v hv⟩ with hcvdef
    have hcunit : IsUnit cv := by
      rw [← v.adicValuation_coe_eq_one_iff,
          show v.adicValuation (cv:F) = WithZero.exp (-(v.ord c)) from by
            rw [Place.ord, neg_neg, WithZero.exp_log (v.adicValuation_ne_zero hc0)],
          hcord v hv, ite_eq_left rfl, neg_zero, WithZero.exp_zero]
    have hresc_ne : IsLocalRing.residue _ cv ≠ 0 := (hunit_iff v _).mp hcunit
    have hreg : ∀ k, ∀ v' ∈ S, c * zF k ∈ v'.toValuationSubring := by
      intro k v' hv'
      rcases eq_or_ne (zF k) 0 with hz0 | hz0
      · simp [hz0]
      refine v'.mem_of_ord_nonneg (mul_ne_zero hc0 hz0) ?_
      rw [v'.ord_mul hc0 hz0, hcord v' hv']
      split_ifs with heq
      · rw [zero_add, heq]; exact v.ord_nonneg_of_mem (hzF_v k)
      · have hle : (-(v'.ord (zF k))).toNat ≤ N := by
          refine le_trans ?_ (Finset.le_sup (f := fun k => S.sup fun v' =>
            (-(v'.ord (zF k))).toNat) (Finset.mem_univ k))
          exact Finset.le_sup (f := fun w => (-(w.ord (zF k))).toNat) hv'
        omega
    refine ⟨fun k => c * zF k, hreg, ?_, ?_⟩
    · intro k
      rw [hunit_iff,
          show (⟨c * zF k, hreg k v hv⟩ : v.toValuationSubring) = cv * z₀ k from Subtype.ext rfl,
          map_mul, hz₀']
      exact mul_ne_zero hresc_ne (bκ.ne_zero k)
    · have heq : (fun k => IsLocalRing.residue _ (⟨c * zF k, hreg k v hv⟩ : v.toValuationSubring))
          = (LinearMap.mulLeft K (IsLocalRing.residue _ cv)) ∘ bκ := by
        funext k
        rw [show (⟨c * zF k, hreg k v hv⟩ : v.toValuationSubring) = cv * z₀ k from Subtype.ext rfl,
            map_mul, hz₀']
        rfl
      rw [heq]
      exact bκ.linearIndependent.map' (LinearMap.mulLeft K (IsLocalRing.residue _ cv))
        (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hresc_ne))
  choose z hz_reg hz_unit hz_li using hex_z

  let ι := (v : S) × Fin (D v.1).toNat × Fin v.1.deg
  let T : ι → F := fun i => z i.1.1 i.1.2 i.2.2 * (t i.1.1) ^ (-((i.2.1:ℤ)+1))
  have hz_ne0 : ∀ (v : Place K F) (hv : v ∈ S) (k : Fin v.deg), z v hv k ≠ 0 := by
    intro v hv k h
    have := (hz_unit v hv k)
    rw [show (⟨z v hv k, hz_reg v hv k v hv⟩ : v.toValuationSubring) = 0 from
      Subtype.ext (by simp [h])] at this
    exact not_isUnit_zero this
  have hT_ne0 : ∀ i : ι, T i ≠ 0 := fun i =>
    mul_ne_zero (hz_ne0 i.1.1 i.1.2 i.2.2) (zpow_ne_zero _ (ht0 i.1.1 i.1.2))
  have hz_ord0 : ∀ (v : Place K F) (hv : v ∈ S) (k : Fin v.deg), v.ord (z v hv k) = 0 := by
    intro v hv k
    have := (v.adicValuation_coe_eq_one_iff _).mpr (hz_unit v hv k)
    simp only [Place.ord, this, WithZero.log_one, neg_zero]
  have hT_ord_own : ∀ i : ι, i.1.1.ord (T i) = -((i.2.1:ℤ)+1) := by
    intro i
    simp only [T]
    rw [i.1.1.ord_mul (hz_ne0 _ _ _) (zpow_ne_zero _ (ht0 _ i.1.2)),
        hz_ord0, zero_add, i.1.1.ord_zpow, htv i.1.1 i.1.2, mul_one]
  have hT_ord_other : ∀ (i : ι) (v' : Place K F) (hv' : v' ∈ S), v' ≠ i.1.1 →
      0 ≤ v'.ord (T i) := by
    intro i v' hv' hne
    simp only [T]
    rw [v'.ord_mul (hz_ne0 _ _ _) (zpow_ne_zero _ (ht0 _ i.1.2)),
        v'.ord_zpow, htv' i.1.1 i.1.2 v' hv' hne, mul_zero, add_zero]
    exact Place.ord_nonneg_of_mem v' (hz_reg _ _ _ v' hv')

  have hTli : LinearIndependent E T := by
    rw [Fintype.linearIndependent_iff]
    intro φ hsum
    by_contra hex
    push Not at hex
    obtain ⟨i₁, hφi₁⟩ := hex
    set supp := (Finset.univ : Finset ι).filter (fun i => φ i ≠ 0) with hsupp
    have hi₁supp : i₁ ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hφi₁⟩
    have hsupp_ne : supp.Nonempty := ⟨i₁, hi₁supp⟩
    have hφne : ∀ i ∈ supp, ((φ i : E) : F) ≠ 0 := fun i hi =>
      (map_ne_zero_iff _ (algebraMap E F).injective).mpr (Finset.mem_filter.mp hi).2
    have hsumF : ∑ i, ((φ i : E) : F) * T i = 0 := by
      rw [show (∑ i, ((φ i : E) : F) * T i) = ∑ i, (φ i) • T i from
        Finset.sum_congr rfl fun i _ => (Algebra.smul_def (φ i) (T i)).symm]
      exact hsum
    have hq : ∀ i ∈ supp, ∃ q : ℤ, ∀ v ∈ S, v.ord ((φ i : E) : F) = q * D v :=
      fun i hi => hord_E (φ i) (hφne i hi)
    choose q hq using hq
    obtain ⟨i₂, hi₂, hq₂min⟩ := Finset.exists_min_image supp
      (fun i => if hi : i ∈ supp then q i hi else 0) hsupp_ne
    set q₂ := q i₂ hi₂ with hq₂def
    have hq₂le : ∀ (i) (hi : i ∈ supp), q₂ ≤ q i hi := by
      intro i hi; have := hq₂min i hi; rwa [dite_eq_left hi₂, dite_eq_left hi] at this
    set v₀ := i₂.1.1 with hv₀def
    have hv₀ : v₀ ∈ S := i₂.1.2
    have hψord : ∀ (i) (hi : i ∈ supp), ∀ v ∈ S,
        v.ord (x ^ q₂ * ((φ i : E) : F)) = (q i hi - q₂) * D v := by
      intro i hi v hv
      rw [v.ord_mul (zpow_ne_zero _ hx0) (hφne i hi), v.ord_zpow, hq i hi v hv, hDv v hv]
      ring
    have hψord_nn : ∀ (i) (hi : i ∈ supp), ∀ v ∈ S,
        0 ≤ v.ord (x ^ q₂ * ((φ i : E) : F)) := by
      intro i hi v hv
      rw [hψord i hi v hv]
      exact mul_nonneg (by linarith [hq₂le i hi]) (by linarith [hDvpos v hv])
    have hψT_sum : ∑ i, x ^ q₂ * ((φ i : E) : F) * T i = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hsumF, mul_zero]
    have hψT_ord_ge0_other : ∀ (i) (hi : i ∈ supp), i.1.1 ≠ v₀ →
        0 ≤ v₀.ord (x ^ q₂ * ((φ i : E) : F) * T i) := by
      intro i hi hne
      rw [v₀.ord_mul (mul_ne_zero (zpow_ne_zero _ hx0) (hφne i hi)) (hT_ne0 i)]
      exact add_nonneg (hψord_nn i hi v₀ hv₀) (hT_ord_other i v₀ hv₀ (Ne.symm hne))
    obtain ⟨i₃, hi₃, hmmin⟩ := Finset.exists_min_image supp
      (fun i => if hi : i ∈ supp then v₀.ord (x ^ q₂ * ((φ i : E) : F) * T i) else 0) hsupp_ne
    set m := v₀.ord (x ^ q₂ * ((φ i₃ : E) : F) * T i₃) with hmdef
    have hmle : ∀ (i) (hi : i ∈ supp), m ≤ v₀.ord (x ^ q₂ * ((φ i : E) : F) * T i) := by
      intro i hi; have := hmmin i hi; rwa [dite_eq_left hi₃, dite_eq_left hi] at this
    have hm_neg : m < 0 := by
      have h2 := hmle i₂ hi₂
      rw [v₀.ord_mul (mul_ne_zero (zpow_ne_zero _ hx0) (hφne i₂ hi₂)) (hT_ne0 i₂),
          hψord i₂ hi₂ v₀ hv₀, show q i₂ hi₂ - q₂ = 0 from by rw [hq₂def]; ring,
          zero_mul, zero_add, show v₀.ord (T i₂) = -((i₂.2.1:ℤ)+1) from hT_ord_own i₂] at h2
      linarith [Int.natCast_nonneg i₂.2.1.1]
    have hi₃v₀ : i₃.1.1 = v₀ := by
      by_contra hne
      exact absurd (hψT_ord_ge0_other i₃ hi₃ hne) (by linarith)

    clear_value v₀
    subst hi₃v₀
    set vv := i₃.1.1 with hvvdef
    set a₃ : ℤ := (i₃.2.1 : ℤ) with ha₃def
    have ha₃lt : a₃ < D vv := by
      have h1 : (i₃.2.1 : ℕ) < (D vv).toNat := i₃.2.1.2
      have h2 := hDvpos vv hv₀; omega
    set Q := q i₃ hi₃ - q₂ with hQdef
    have hQnn : 0 ≤ Q := by have := hq₂le i₃ hi₃; omega
    have hmeq : m = Q * D vv - (a₃ + 1) := by
      rw [hmdef, vv.ord_mul (mul_ne_zero (zpow_ne_zero _ hx0) (hφne i₃ hi₃)) (hT_ne0 i₃),
          hψord i₃ hi₃ vv hv₀, ← hQdef, hT_ord_own i₃]; ring
    have hmin_char : ∀ (i) (hi : i ∈ supp), i.1.1 = vv →
        vv.ord (x ^ q₂ * ((φ i : E) : F) * T i) = m →
        (i.2.1:ℤ) = a₃ ∧ q i hi - q₂ = Q := by
      intro i hi hiv heq
      have hai_lt : (i.2.1:ℤ) < D vv := by
        have h1 : (i.2.1 : ℕ) < (D i.1.1).toNat := i.2.1.2
        have h3 : D i.1.1 = D vv := by rw [hiv]
        have h2 := hDvpos vv hv₀; omega
      have heq2 : (q i hi - q₂) * D vv - ((i.2.1:ℤ)+1) = m := by
        rw [← heq, vv.ord_mul (mul_ne_zero (zpow_ne_zero _ hx0) (hφne i hi)) (hT_ne0 i),
            hψord i hi vv hv₀, show vv.ord (T i) = -((i.2.1:ℤ)+1) from hiv ▸ hT_ord_own i]
        ring
      rw [hmeq] at heq2
      have hD1 := hDvpos vv hv₀
      have hdiff : ((q i hi - q₂) - Q) * D vv = (i.2.1:ℤ) - a₃ := by linarith
      have hbnd1 : -(D vv) < (i.2.1:ℤ) - a₃ := by
        linarith [Int.natCast_nonneg i.2.1.1, ha₃lt]
      have hbnd2 : (i.2.1:ℤ) - a₃ < D vv := by
        linarith [hai_lt, Int.natCast_nonneg i₃.2.1.1]
      have hzero : (q i hi - q₂) - Q = 0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · nlinarith
        · nlinarith
      have hieq : (i.2.1:ℤ) = a₃ := by
        have h00 := hdiff; rw [hzero, zero_mul] at h00; linarith
      exact ⟨hieq, by linarith [hzero]⟩
    set μ := x ^ Q * (t vv) ^ (a₃ + 1) with hμdef
    have hμne : μ ≠ 0 := mul_ne_zero (zpow_ne_zero _ hx0) (zpow_ne_zero _ (ht0 vv hv₀))
    have hμord : vv.ord μ = -m := by
      rw [hμdef, vv.ord_mul (zpow_ne_zero _ hx0) (zpow_ne_zero _ (ht0 vv hv₀)),
          vv.ord_zpow, vv.ord_zpow, htv vv hv₀, mul_one, hmeq, hDv vv hv₀]
      ring
    have hμψT_mem : ∀ i, μ * (x ^ q₂ * ((φ i : E) : F) * T i) ∈ vv.toValuationSubring := by
      intro i
      by_cases hi : i ∈ supp
      · refine vv.mem_of_ord_nonneg (mul_ne_zero hμne
          (mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hx0) (hφne i hi)) (hT_ne0 i))) ?_
        rw [vv.ord_mul hμne (mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hx0) (hφne i hi))
              (hT_ne0 i)), hμord]
        linarith [hmle i hi]
      · have : φ i = 0 := by
          by_contra h; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        simp [this]
    have hsum_O : (∑ i, (⟨_, hμψT_mem i⟩ : vv.toValuationSubring)) = 0 := by
      refine Subtype.ext ?_
      simp only [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
      simp only [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hsumF, mul_zero, mul_zero]
    have hres_sum : ∑ i, IsLocalRing.residue _ (⟨_, hμψT_mem i⟩ : vv.toValuationSubring) = 0 := by
      rw [← map_sum, hsum_O, map_zero]

    have hres_zero : ∀ i, ¬(i ∈ supp ∧ vv.ord (x ^ q₂ * ((φ i : E) : F) * T i) = m) →
        IsLocalRing.residue _ (⟨_, hμψT_mem i⟩ : vv.toValuationSubring) = 0 := by
      intro i hnot
      by_cases hi : i ∈ supp
      · refine (Ideal.Quotient.eq_zero_iff_mem).mpr (hmem_max vv _ _ ?_)
        rw [vv.ord_mul hμne
            (mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hx0) (hφne i hi)) (hT_ne0 i)), hμord]
        have hgt : m < vv.ord (x ^ q₂ * ((φ i : E) : F) * T i) :=
          lt_of_le_of_ne (hmle i hi) (fun heq => hnot ⟨hi, heq.symm⟩)
        linarith
      · have hφ0 : φ i = 0 := by
          by_contra h; exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        rw [show (⟨_, hμψT_mem i⟩ : vv.toValuationSubring) = 0 from
          Subtype.ext (by simp [hφ0]), map_zero]

    let j : Fin vv.deg → ι := fun k => ⟨i₃.1, i₃.2.1, k⟩

    have hreindex : ∑ i, IsLocalRing.residue _ (⟨_, hμψT_mem i⟩ : vv.toValuationSubring)
        = ∑ k, IsLocalRing.residue _ (⟨_, hμψT_mem (j k)⟩ : vv.toValuationSubring) := by
      rw [Fintype.sum_sigma]
      have hside1 : ∀ w : ↥S, w ≠ i₃.1 →
          ∑ p, IsLocalRing.residue _ (⟨_, hμψT_mem ⟨w,p⟩⟩ : vv.toValuationSubring) = 0 := by
        intro w hw
        refine Finset.sum_eq_zero fun p _ => hres_zero ⟨w, p⟩ ?_
        rintro ⟨hisupp, heq⟩
        have : (⟨w,p⟩ : ι).1.1 = vv := by
          by_contra hne
          exact absurd (hψT_ord_ge0_other ⟨w,p⟩ hisupp hne) (heq ▸ hm_neg).not_ge
        exact hw (Subtype.ext this)
      rw [Fintype.sum_eq_single i₃.1 hside1, Fintype.sum_prod_type]
      have hside2 : ∀ a : Fin (D i₃.1.1).toNat, a ≠ i₃.2.1 →
          ∑ k, IsLocalRing.residue _ (⟨_, hμψT_mem ⟨i₃.1, a, k⟩⟩ : vv.toValuationSubring) = 0 := by
        intro a ha
        refine Finset.sum_eq_zero fun k _ => hres_zero ⟨i₃.1, a, k⟩ ?_
        rintro ⟨hisupp, heq⟩
        obtain ⟨hai, _⟩ := hmin_char ⟨i₃.1, a, k⟩ hisupp rfl heq
        refine ha (Fin.ext ?_)
        have hai' : (a : ℤ) = (i₃.2.1 : ℤ) := by simpa [ha₃def] using hai
        exact_mod_cast hai'
      rw [Fintype.sum_eq_single i₃.2.1 hside2]
    rw [hreindex] at hres_sum

    have hjkvv : ∀ k, (j k).1.1 = vv := fun k => rfl
    have hjk_T : ∀ k, T (j k) = z vv i₃.1.2 k * (t vv) ^ (-(a₃+1)) := fun k => rfl

    have hjk_simp : ∀ k (hjk : j k ∈ supp)
        (heq : vv.ord (x ^ q₂ * ((φ (j k) : E) : F) * T (j k)) = m),
        μ * (x ^ q₂ * ((φ (j k) : E) : F) * T (j k))
          = (x ^ (q (j k) hjk) * ((φ (j k) : E) : F)) * z vv i₃.1.2 k := by
      intro k hjk heq
      obtain ⟨_, hqeq⟩ := hmin_char (j k) hjk rfl heq
      have hqjk : q (j k) hjk = q₂ + Q := by linarith
      simp only [hμdef, hjk_T, hqjk]
      have hxcan : x ^ Q * x ^ q₂ = x ^ (q₂ + Q) := by rw [← zpow_add₀ hx0]; ring_nf
      have htcan : (t vv) ^ (a₃+1) * (t vv) ^ (-(a₃+1)) = 1 := by
        rw [← zpow_add₀ (ht0 vv hv₀), add_neg_cancel, zpow_zero]
      calc x ^ Q * (t vv)^(a₃+1) * (x^q₂ * ((φ (j k):E):F) * (z vv i₃.1.2 k * (t vv)^(-(a₃+1))))
          = (x^Q * x^q₂) * ((φ (j k):E):F) * z vv i₃.1.2 k *
            ((t vv)^(a₃+1) * (t vv)^(-(a₃+1))) := by ring
        _ = x^(q₂+Q) * ((φ (j k):E):F) * z vv i₃.1.2 k := by rw [hxcan, htcan, mul_one]

    have hxEpow : ∀ (r : ℤ), ((xE ^ r : E) : F) = x ^ r := fun r => by
      rw [show ((xE ^ r : E) : F) = E.val (xE ^ r) from rfl, map_zpow₀]; rfl
    have hEgk : ∀ k (hjk : j k ∈ supp),
        ((xE ^ (q (j k) hjk) * φ (j k) : E) : F) = x ^ (q (j k) hjk) * ((φ (j k) : E) : F) := by
      intro k hjk; push_cast; rw [hxEpow]
    have hEgk_ne0 : ∀ k (hjk : j k ∈ supp), ((xE ^ (q (j k) hjk) * φ (j k) : E) : F) ≠ 0 := by
      intro k hjk; rw [hEgk]; exact mul_ne_zero (zpow_ne_zero _ hx0) (hφne (j k) hjk)
    have hEgk_ord0 : ∀ k (hjk : j k ∈ supp),
        vv.ord ((xE ^ (q (j k) hjk) * φ (j k) : E) : F) = 0 := by
      intro k hjk
      rw [hEgk, vv.ord_mul (zpow_ne_zero _ hx0) (hφne (j k) hjk), vv.ord_zpow,
          hq (j k) hjk vv hv₀, hDv vv hv₀]; ring
    let γ : Fin vv.deg → K := fun k =>
      if hjk : j k ∈ supp ∧ vv.ord (x ^ q₂ * ((φ (j k) : E) : F) * T (j k)) = m
      then Classical.choose (hres_E vv hv₀ _ (hEgk_ne0 k hjk.1) (hEgk_ord0 k hjk.1))
      else 0
    have hγ_res : ∀ k, IsLocalRing.residue _ (⟨_, hμψT_mem (j k)⟩ : vv.toValuationSubring)
        = γ k • IsLocalRing.residue _
          (⟨z vv i₃.1.2 k, hz_reg vv i₃.1.2 k vv hv₀⟩ : vv.toValuationSubring) := by
      intro k
      by_cases hjk : j k ∈ supp ∧ vv.ord (x ^ q₂ * ((φ (j k) : E) : F) * T (j k)) = m
      · have hgmem : ((xE ^ (q (j k) hjk.1) * φ (j k) : E) : F) ∈ vv.toValuationSubring :=
          vv.mem_of_ord_nonneg (hEgk_ne0 k hjk.1) (hEgk_ord0 k hjk.1).ge
        have hsplit : (⟨_, hμψT_mem (j k)⟩ : vv.toValuationSubring)
            = ⟨_, hgmem⟩ * ⟨z vv i₃.1.2 k, hz_reg vv i₃.1.2 k vv hv₀⟩ := by
          refine Subtype.ext ?_
          show μ * (x ^ q₂ * ((φ (j k):E):F) * T (j k))
            = ((xE ^ (q (j k) hjk.1) * φ (j k) : E) : F) * z vv i₃.1.2 k
          rw [hjk_simp k hjk.1 hjk.2, hEgk k hjk.1]
        rw [hsplit, map_mul]
        simp only [γ, dite_eq_left hjk, Algebra.smul_def]
        congr 1
        exact (Classical.choose_spec
          (hres_E vv hv₀ _ (hEgk_ne0 k hjk.1) (hEgk_ord0 k hjk.1))).2 hgmem
      · rw [hres_zero (j k) hjk]; simp only [γ, dite_eq_right hjk, zero_smul]
    rw [show (∑ k, IsLocalRing.residue _ (⟨_, hμψT_mem (j k)⟩ : vv.toValuationSubring))
        = ∑ k, γ k • IsLocalRing.residue _
            (⟨z vv i₃.1.2 k, hz_reg vv i₃.1.2 k vv hv₀⟩ : vv.toValuationSubring) from
      Finset.sum_congr rfl fun k _ => hγ_res k] at hres_sum
    have hγk0 := Fintype.linearIndependent_iff.mp (hz_li vv i₃.1.2) γ hres_sum i₃.2.2
    have hji₃ : j i₃.2.2 = i₃ := rfl
    have hi₃cond : j i₃.2.2 ∈ supp ∧
        vv.ord (x ^ q₂ * ((φ (j i₃.2.2) : E) : F) * T (j i₃.2.2)) = m := by
      rw [hji₃]; exact ⟨hi₃, hmdef.symm⟩
    simp only [γ, dite_eq_left hi₃cond] at hγk0
    exact (Classical.choose_spec
      (hres_E vv hv₀ _ (hEgk_ne0 i₃.2.2 hi₃cond.1) (hEgk_ord0 i₃.2.2 hi₃cond.1))).1 hγk0

  have hcard : (Fintype.card ι : ℤ) = Divisor.degree D := by
    simp only [ι, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    rw [hdegD, ← Finset.sum_attach S (fun v => D v * (v.deg : ℤ))]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Int.toNat_of_nonneg (by linarith [hDvpos v.1 v.2])]
  calc Divisor.degree D = (Fintype.card ι : ℤ) := hcard.symm
    _ ≤ (n : ℤ) := by exact_mod_cast hTli.fintype_card_le_finrank

/-- The degree identity: `deg (x)_∞ = [F : K(x)]`. -/
theorem degree_eq_finrank_adjoin_of_eq_max_neg_ord
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) :=
  le_antisymm
    (degree_le_finrank_adjoin_of_eq_max_neg_ord x hx D hD)
    (finrank_adjoin_le_degree_of_eq_max_neg_ord x hx D hD)

end Divisor

end AlgebraicCurve
