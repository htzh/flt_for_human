/-
The degree identity `deg (x)_∞ = [F : K(x)]` for `x` transcendental over `K`: the
pole divisor `D` of `x`, given pointwise by `D v = max 0 (-(ord_v x))`, has degree
the degree of the field extension `[F : K(x)]`.

The two inequalities are Riemann–Roch counts.  For `[F : K(x)] ≤ deg D` one takes a
`K[x]`-integral basis `u` of `F` over `K(x)`: at a place where `x` is integral so are
the `u i`, and at the finitely many poles of `x` their orders are bounded by a
constant `c`, so the products `x ^ j * u i` (`0 ≤ j ≤ m - c`) are `K`-linearly
independent elements of `L(m D)` and number `n (m - c + 1)`; Riemann's inequality
`ℓ(m D) ≤ m deg D + ℓ(0)` then forces `n ≤ deg D`.  For `deg D ≤ [F : K(x)]` one
counts residues: at each `v` in the support of `D` a `K`-basis of the residue field
`κ(v)` is lifted to elements regular everywhere on the support, weak approximation
(`Place.exists_forall_ord_eq`) supplies an element which is `1` at `v` and `0` at the
other places of the support, and the products `z k * t v ^ (-(a + 1))` for
`a < D v` are `K(x)`-linearly independent; their number is `deg D` and exceeds the
dimension `[F : K(x)]` otherwise.

Statements are transcribed verbatim from the pinned FLT
(`anthropics/fermats-last-theorem`, `aa2d8b3`) `Theorems/` wrappers; the proofs are
adapted from the three `P2M/Sol/S_` files named below.  From the port, the independence
steps are `AlgebraicCurve.linearIndependent_pow_of_transcendental` and
`AlgebraicCurve.linearIndependent_pow_mul` (`Genus/Stichtenoth.lean`), Riemann's count is
`AlgebraicCurve.ell_le_degree_add_ellZero` and the finite-dimensionality of `L` is
`AlgebraicCurve.finiteDimensional_lSpace` (`Genus/Index.lean`), the `L`-space interface is
`Defs/AdelicIndex.lean`, and weak approximation is
`AlgebraicCurve.Place.exists_forall_ord_eq` (`Place/Approximation.lean`).

* `Theorems/Thm_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord.lean`
* `Theorems/Thm_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord.lean`
* `Theorems/Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord.lean`
* `P2M/Sol/S_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord.lean` (230 lines)
* `P2M/Sol/S_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord.lean` (546 lines)
* `P2M/Sol/S_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord.lean` (21 lines)

The module's second subject is the local form of that identity at a place: the
different is effective, `ord_v f - 1 ≤ ord_v (df)` when `df ≠ 0`, over a perfect base
field. The pin proves it by choosing a uniformiser `t`, writing `f = u t^m` with `u` a
unit and expanding `d(u t^m) = (u m t^(m-1) + t^m c_u) dt`; the first summand then has
order `m - 1` and the second at least `m`, so the minimum (`min_ord_le_ord_add`) is
`m - 1`. The coefficient bookkeeping is the port's `Place.diffCoeff` API
(`Differential/Coefficient.lean`): existence, uniqueness and integrality against a
uniformiser are `diffCoeff_smul_D_of_ord_eq_one`, `diffCoeff_smul_D_eq_of_ord_eq_one`
and `ord_diffCoeff_D_nonneg_of_perfectField`; `v.ordDiff` is the pin's `ordDiff`, whose
order laws are imported rather than re-proved.

spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_finrank_adjoin_le_degree_of_eq_max_neg_ord.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_degree_le_finrank_adjoin_of_eq_max_neg_ord.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.Canonical.PolarDifferentials
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.Place.Approximation
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import FLTForHuman.AlgebraicCurve.WeilExchange.Bifibre
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

noncomputable section

open Module IsDedekindDomain WithZero IsLocalRing Polynomial
open scoped IntermediateField

-- The `letI`/`haveI` instance walls in the place sections below are load-bearing — they
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

/-! ### The different is effective: `ord f - 1 ≤ ordDiff (df)`

After FLT's
`P2M/Sol/S_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField.lean` (181 ln,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField.lean>).
The private helpers are the pin's (`ordDiff_smul_impl`, `H2_pos`, `H2_impl`), renamed
for their content; the three imported `diffCoeff` theorems are not re-proved. -/

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Multiplying a differential by `g` adds `ord g` to its order (the pin's private
`ordDiff_smul_impl`). -/
private theorem ordDiff_smul_impl [PerfectField K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {g : F} (hg : g ≠ 0) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.ordDiff (g • ω) = v.ord g + v.ordDiff ω := by
  have ht : v.ord v.uniformizer_alt = 1 :=
    v.ord_uniformizer_alt ⟨v.uniformizer, v.ord_uniformizer⟩
  have hrep : diffCoeff v.uniformizer_alt ω • KaehlerDifferential.D K F v.uniformizer_alt = ω :=
    v.diffCoeff_smul_D_of_ord_eq_one x ht ω
  have hgo : g • ω =
      (g * diffCoeff v.uniformizer_alt ω) • KaehlerDifferential.D K F v.uniformizer_alt := by
    conv_lhs => rw [← hrep]
    rw [smul_smul]
  have hco : diffCoeff v.uniformizer_alt (g • ω) = g * diffCoeff v.uniformizer_alt ω := by
    rw [hgo]
    exact v.diffCoeff_smul_D_eq_of_ord_eq_one x ht _
  have hc0 : diffCoeff v.uniformizer_alt ω ≠ 0 := by
    intro h0
    apply hω
    rw [← hrep, h0, zero_smul]
  rw [ordDiff_def, ordDiff_def, hco, v.ord_mul hg hc0]

/-- The case `0 ≤ ord f`: write `f = u t^m` at the uniformiser `t` and read the order of
the coefficient of `df` off its two summands (the pin's private `H2_pos`). -/
private theorem ord_sub_one_le_ordDiff_D_of_ord_nonneg [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {f : F} (hD : KaehlerDifferential.D K F f ≠ 0) (hn : 0 ≤ v.ord f) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) := by
  have ht : v.ord v.uniformizer_alt = 1 :=
    v.ord_uniformizer_alt ⟨v.uniformizer, v.ord_uniformizer⟩
  set t := v.uniformizer_alt with htdef
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, v.ord_zero] at ht
    omega
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD
    exact hD rfl
  set m : ℕ := (v.ord f).toNat with hmdef
  have hm : (m : ℤ) = v.ord f := Int.toNat_of_nonneg hn
  have htm0 : t ^ m ≠ 0 := pow_ne_zero m ht0
  set u : F := f * (t ^ m)⁻¹ with hudef
  have hu0 : u ≠ 0 := mul_ne_zero hf0 (inv_ne_zero htm0)
  have hordu : v.ord u = 0 := by
    rw [hudef, v.ord_mul hf0 (inv_ne_zero htm0), v.ord_inv, v.ord_pow, ht, hm]
    ring
  have hfeq : f = u * t ^ m := by
    rw [hudef, mul_assoc, inv_mul_cancel₀ htm0, mul_one]

  set cu : F := diffCoeff t (KaehlerDifferential.D K F u) with hcudef
  have hcu_nonneg : 0 ≤ v.ord cu :=
    v.ord_diffCoeff_D_nonneg_of_perfectField x ht (le_of_eq hordu.symm)
  have hrepu : cu • KaehlerDifferential.D K F t = KaehlerDifferential.D K F u :=
    v.diffCoeff_smul_D_of_ord_eq_one x ht _
  have hDtm : KaehlerDifferential.D K F (t ^ m) =
      ((m : F) * t ^ (m - 1)) • KaehlerDifferential.D K F t := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F m, smul_smul]
  have hdecomp : KaehlerDifferential.D K F f =
      (u * ((m : F) * t ^ (m - 1)) + t ^ m * cu) • KaehlerDifferential.D K F t := by
    conv_lhs => rw [hfeq]
    rw [Derivation.leibniz, hDtm, ← hrepu, smul_smul, smul_smul, add_smul]
  have hcoeff : diffCoeff t (KaehlerDifferential.D K F f) =
      u * ((m : F) * t ^ (m - 1)) + t ^ m * cu := by
    rw [hdecomp]
    exact v.diffCoeff_smul_D_eq_of_ord_eq_one x ht _
  have hsum0 : u * ((m : F) * t ^ (m - 1)) + t ^ m * cu ≠ 0 := by
    intro h0
    apply hD
    rw [hdecomp, h0, zero_smul]
  rw [ordDiff_def, ← htdef, hcoeff]
  rcases eq_or_ne (u * ((m : F) * t ^ (m - 1))) 0 with ha | ha
  ·
    rw [ha, zero_add] at hsum0 ⊢
    have hcu0 : cu ≠ 0 := fun h => hsum0 (by rw [h, mul_zero])
    rw [v.ord_mul htm0 hcu0, v.ord_pow, ht]
    omega
  · have hmF : (m : F) ≠ 0 := by
      intro h
      exact ha (by rw [h, zero_mul, mul_zero])
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exact absurd (by rw [h, Nat.cast_zero] : (m : F) = 0) hmF
      · exact h
    have hordm : v.ord ((m : F)) = 0 := by
      have hcast : ((m : F)) = algebraMap K F ((m : K)) := by
        rw [map_natCast]
      rw [hcast, v.ord_algebraMap]
    have horda : v.ord (u * ((m : F) * t ^ (m - 1))) = (m : ℤ) - 1 := by
      have h1 : (m : F) * t ^ (m - 1) ≠ 0 := mul_ne_zero hmF (pow_ne_zero _ ht0)
      rw [v.ord_mul hu0 h1, v.ord_mul hmF (pow_ne_zero _ ht0), v.ord_pow, ht, hordu, hordm]
      have : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by
        omega
      rw [this]
      ring
    rcases eq_or_ne cu 0 with hcu0 | hcu0
    ·
      rw [hcu0, mul_zero, add_zero, horda]
      omega
    · have hordb : v.ord (t ^ m * cu) = (m : ℤ) + v.ord cu := by
        rw [v.ord_mul htm0 hcu0, v.ord_pow, ht]
        ring
      have hmin := v.min_ord_le_ord_add
        (f := u * ((m : F) * t ^ (m - 1))) (g := t ^ m * cu) hsum0
      rw [horda, hordb] at hmin
      have : min ((m : ℤ) - 1) ((m : ℤ) + v.ord cu) = (m : ℤ) - 1 := by
        omega
      rw [this] at hmin
      omega

/-- The case `ord f < 0`: apply the previous case to `f⁻¹`, whose differential is
`-f⁻¹ ^ 2 • df`, and use `ordDiff_smul_impl` (the pin's private `H2_impl`). -/
private theorem ord_sub_one_le_ordDiff_D_aux [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F)
    {f : F} (hD : KaehlerDifferential.D K F f ≠ 0) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) := by
  rcases le_or_gt 0 (v.ord f) with hn | hn
  · exact v.ord_sub_one_le_ordDiff_D_of_ord_nonneg x hD hn
  ·
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [map_zero] at hD
      exact hD rfl
    have hDinv : KaehlerDifferential.D K F f⁻¹ ≠ 0 := by
      intro h0
      apply hD
      have hleib := Derivation.leibniz_inv (KaehlerDifferential.D K F) f
      rw [h0] at hleib
      have hne : (-f⁻¹ ^ 2 : F) ≠ 0 := by
        simpa using hf0
      rcases smul_eq_zero.mp hleib.symm with h | h
      · exact absurd h hne
      · exact h
    have hpos := v.ord_sub_one_le_ordDiff_D_of_ord_nonneg x hDinv (by rw [v.ord_inv]; omega)
    have hleib := Derivation.leibniz_inv (KaehlerDifferential.D K F) f
    have hsmul : v.ordDiff (KaehlerDifferential.D K F f⁻¹) =
        v.ord (-f⁻¹ ^ 2) + v.ordDiff (KaehlerDifferential.D K F f) := by
      rw [hleib]
      exact v.ordDiff_smul_impl x (by simpa using hf0) hD
    have hordneg : v.ord (-f⁻¹ ^ 2 : F) = -2 * v.ord f := by
      have hneg1 : (-f⁻¹ ^ 2 : F) = algebraMap K F (-1) * f⁻¹ ^ 2 := by
        rw [map_neg, map_one]
        ring
      have h2 : (f⁻¹ ^ 2 : F) ≠ 0 := by
        simpa using hf0
      have hneg1ne : algebraMap K F (-1) ≠ 0 := by
        rw [map_neg, map_one]
        exact neg_ne_zero.mpr one_ne_zero
      rw [hneg1, v.ord_mul hneg1ne h2,
        v.ord_algebraMap, ← zpow_natCast (f⁻¹) 2, v.ord_zpow, v.ord_inv]
      ring
    rw [v.ord_inv] at hpos
    rw [hsmul, hordneg] at hpos
    omega

/-- **The different is effective at a place, over a perfect base field.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_Place_ord_sub_one_le_ordDiff_D_of_perfectField.lean`. -/
theorem ord_sub_one_le_ordDiff_D_of_perfectField {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (v : AlgebraicCurve.Place K F) {f : F}
    (hD : KaehlerDifferential.D K F f ≠ 0) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) :=
  v.ord_sub_one_le_ordDiff_D_aux x hD

/-! ## The Galois orbit/stabiliser dictionary over a fixed value

The pin's `Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois` (778 ln,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_restrictAlong_eq_natCard_algHom_of_isGalois.lean>)
and the engine it stands on: the place `basePlace c` below `K⟮t⟯` for transcendental
`t`, the restriction of a place along an integral map, and the Galois action on the
places of `M` over `K⟮t⟯`.  The engine's `mem_of_ord_nonneg` is the port's public
`Place.mem_of_ord_nonneg` (`Defs/PushPull.lean`), and the pin's bridge
`ordDiff_eq_ordDifferential` is not needed here.  `restrictAlong_comp` and
`finiteAlong_of_finiteDimensional_adjoin` are the pin's shared factoring block, written
once here; its third member, `isIntegral_of_finiteAlong`, is dead in this proof (the
headline takes integrality as the `hint` hypothesis), and the port already carries the
lemma publicly in `ModularCurve/X1/Inputs.lean`, so it is not restated.  The pin's
`Place.restrictAlong_surjective` is imported from `WeilExchange/Bifibre.lean` (its
home, beside `Place.exists_restrict_eq`), not re-proved here.

The pin's `letI`/`haveI` walls are load-bearing — they register the
`algebraAlong`/`isScalarTower_along` instances the following tactic needs — so the
style linter's `let`/`have` suggestion does not apply; cf. `Genus/Index.lean`. -/
section Engine

private theorem ord_eq_one_of_valuation_eq {K F : Type*} [Field K] [Field F] [Algebra K F]
    (w : Place K F) {v' : Valuation F ℤᵐ⁰}
    (hv' : v'.valuationSubring = w.toValuationSubring) {x : F} (hx : v' x = exp (-1 : ℤ)) :
    w.ord x = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero] at hx
    exact WithZero.exp_ne_zero hx.symm
  rw [w.ord_eq_neg_log_of_valuationSubring_eq v' hv' hx hx0, hx, WithZero.log_exp]
  ring

section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

scoped instance instIsPrincipalIdealRingAdjoinSingleton (t : F) :
    IsPrincipalIdealRing (Algebra.adjoin K ({t} : Set F)) := by
  have hmem : ∀ p : Polynomial K, Polynomial.aeval t p ∈ Algebra.adjoin K ({t} : Set F) := by
    intro p
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  refine IsPrincipalIdealRing.of_surjective
    ((Polynomial.aeval t).codRestrict (Algebra.adjoin K ({t} : Set F)) hmem) ?_
  rintro ⟨a, ha⟩
  obtain ⟨p, hp⟩ : ∃ p : Polynomial K, Polynomial.aeval t p = a := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    exact (AlgHom.mem_range _).mp ha
  exact ⟨p, Subtype.ext hp⟩

end

private def linGen {K F : Type*} [Field K] [Field F] [Algebra K F] (t : F) (c : K) :
    Algebra.adjoin K ({t} : Set F) :=
  ⟨t, Algebra.self_mem_adjoin_singleton K t⟩ - algebraMap K _ c

private theorem coe_linGen {K F : Type*} [Field K] [Field F] [Algebra K F] (t : F) (c : K) :
    ((linGen t c : Algebra.adjoin K ({t} : Set F)) : F) = t - algebraMap K F c := by
  simp [linGen]

section Transcendental

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
  (t : F) (htr : Transcendental K t)

include htr in
private theorem linGen_ne_zero (c : K) : linGen t c ≠ 0 := by
  intro h
  have h' := congrArg (fun a : Algebra.adjoin K ({t} : Set F) => (a : F)) h
  simp only [coe_linGen, ZeroMemClass.coe_zero, sub_eq_zero] at h'
  exact htr (by rw [h']; exact isAlgebraic_algebraMap c)

private def polyEquiv : Polynomial K ≃ₐ[K] Algebra.adjoin K ({t} : Set F) :=
  (AlgEquiv.ofInjective (Polynomial.aeval t) (transcendental_iff_injective.mp htr)).trans
    (Subalgebra.equivOfEq _ _ (by rw [Algebra.adjoin_singleton_eq_range_aeval]))

private theorem polyEquiv_X_sub_C (c : K) :
    polyEquiv t htr (Polynomial.X - Polynomial.C c) = linGen t c := by
  apply Subtype.ext
  rw [coe_linGen]
  simp [polyEquiv, Subalgebra.equivOfEq_apply, AlgEquiv.ofInjective_apply]

include htr in

private theorem prime_linGen (c : K) : Prime (linGen t c) := by
  rw [← polyEquiv_X_sub_C t htr c, MulEquiv.prime_iff]
  exact Polynomial.prime_X_sub_C c

private def linPrime (c : K) : HeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) :=
  ⟨Ideal.span {linGen t c}, (Ideal.span_singleton_prime (linGen_ne_zero t htr c)).mpr
    (prime_linGen t htr c), by
      rw [ne_eq, Ideal.span_singleton_eq_bot]
      exact linGen_ne_zero t htr c⟩

open scoped IntermediateField.algebraAdjoinAdjoin

private def basePlace (c : K) : Place K (IntermediateField.adjoin K ({t} : Set F)) :=
  Place.ofHeightOneSpectrum (K := K) (linPrime t htr c)

private theorem algebraMap_linGen (c : K) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F))
        (linGen t c) =
      IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c := by
  apply Subtype.ext
  rw [IntermediateField.algebraAdjoinAdjoin.coe_algebraMap, coe_linGen]
  simp

private theorem ord_basePlace (c : K) :
    (basePlace t htr c).ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) = 1 := by
  rw [← algebraMap_linGen]
  refine ord_eq_one_of_valuation_eq (basePlace t htr c)
    (v' := (linPrime t htr c).valuation (IntermediateField.adjoin K ({t} : Set F))) rfl ?_
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (linPrime t htr c).intValuation_singleton (linGen_ne_zero t htr c) rfl

private theorem forall_algebraMap_mem (v : Place K (IntermediateField.adjoin K ({t} : Set F)))
    (ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring)
    (r : Algebra.adjoin K ({t} : Set F)) :
    algebraMap (Algebra.adjoin K ({t} : Set F)) (IntermediateField.adjoin K ({t} : Set F)) r ∈
      v.toValuationSubring := by
  obtain ⟨x, hx⟩ := r
  show (⟨x, IntermediateField.algebra_adjoin_le_adjoin K _ hx⟩ :
      IntermediateField.adjoin K ({t} : Set F)) ∈ v.toValuationSubring
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    have hy' : y = t := Set.mem_singleton_iff.mp hy
    subst hy'
    exact ht
  | algebraMap a => exact v.algebraMap_mem' a
  | add y z hy hz ihy ihz => exact add_mem ihy ihz
  | mul y z hy hz ihy ihz => exact mul_mem ihy ihz

include htr in

private theorem eq_basePlace_of_ord_pos
    (v : Place K (IntermediateField.adjoin K ({t} : Set F))) (c : K)
    (hv : 0 < v.ord (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c)) :
    v = basePlace t htr c := by
  have ht : IntermediateField.AdjoinSimple.gen K t ∈ v.toValuationSubring :=
    mem_of_ord_sub_algebraMap_pos v (IntermediateField.AdjoinSimple.gen K t) c hv
  have hw := forall_algebraMap_mem t v ht
  have hmem : linGen t c ∈ Place.center (Algebra.adjoin K ({t} : Set F)) v hw := by
    rw [Place.mem_center_iff_ord_pos v hw (linGen_ne_zero t htr c), algebraMap_linGen]
    exact hv
  have hcenter : Place.center (Algebra.adjoin K ({t} : Set F)) v hw = Ideal.span {linGen t c} := by
    haveI : (Ideal.span {linGen t c}).IsPrime := (linPrime t htr c).isPrime
    have hmax : (Ideal.span {linGen t c}).IsMaximal :=
      IsPrime.to_maximal_ideal (linPrime t htr c).ne_bot
    exact (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance)
      ((Ideal.span_singleton_le_iff_mem _).mpr hmem)).symm
  have hc : Place.centerHeightOneSpectrum (Algebra.adjoin K ({t} : Set F)) v hw =
      linPrime t htr c := HeightOneSpectrum.ext hcenter
  apply Place.ext
  rw [v.toValuationSubring_eq_of_forall_mem hw, hc,
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rfl

include htr in

private theorem restrict_eq_basePlace
    [Algebra.IsIntegral (IntermediateField.adjoin K ({t} : Set F)) F]
    (w : Place K F) (c : K) (hw : 0 < w.ord (t - algebraMap K F c)) :
    w.restrict (IntermediateField.adjoin K ({t} : Set F)) = basePlace t htr c ∧
    (w.restrict (IntermediateField.adjoin K ({t} : Set F))).ord
      (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) = 1 := by
  have hgen : algebraMap (IntermediateField.adjoin K ({t} : Set F)) F
      (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) = t - algebraMap K F c := by
    rw [map_sub, IntermediateField.AdjoinSimple.algebraMap_gen K t, ← IsScalarTower.algebraMap_apply]
  have h := Place.ord_restrict (F := IntermediateField.adjoin K ({t} : Set F)) w
    (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c)
  rw [hgen] at h
  have hpos : 0 < (w.restrict (IntermediateField.adjoin K ({t} : Set F))).ord
      (IntermediateField.AdjoinSimple.gen K t - algebraMap K _ c) := by
    rw [h] at hw
    exact (pos_iff_pos_of_mul_pos hw).mp
      (by exact_mod_cast w.ramificationIndex_pos (F := IntermediateField.adjoin K ({t} : Set F)))
  have heq := eq_basePlace_of_ord_pos t htr (w.restrict (IntermediateField.adjoin K ({t} : Set F))) c
    hpos
  refine ⟨heq, ?_⟩
  have h1 := ord_basePlace t htr c
  rw [← heq] at h1
  exact h1

end Transcendental

private theorem deg_eq_one_of_isAlgClosed {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] (v : Place K F) (hv : v.deg ≠ 0) : v.deg = 1 := by
  haveI : Module.Finite K v.ResidueField := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hv)
  have e : K ≃ₗ[K] v.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap K v.ResidueField)
      (IsAlgClosed.algebraMap_bijective_of_isIntegral)
  unfold Place.deg
  rw [← e.finrank_eq, Module.finrank_self]

end Engine

section Along

variable {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M]
  (ι : F →ₐ[K] M) (y : F)

private def adjoinEquivAlong :
    IntermediateField.adjoin K ({y} : Set F) ≃ₐ[K] IntermediateField.adjoin K ({ι y} : Set M) :=
  (IntermediateField.equivMap (IntermediateField.adjoin K ({y} : Set F)) ι).trans
    (IntermediateField.equivOfEq (by rw [IntermediateField.adjoin_map, Set.image_singleton]))

private theorem coe_adjoinEquivAlong (r : IntermediateField.adjoin K ({y} : Set F)) :
    ((adjoinEquivAlong ι y r : IntermediateField.adjoin K ({ι y} : Set M)) : M) = ι r := rfl

private theorem finiteAlong_of_finiteDimensional_adjoin
    [h : FiniteDimensional (IntermediateField.adjoin K ({ι y} : Set M)) M] :
    FiniteAlong K ι := by
  letI := algebraAlong ι
  set R' := IntermediateField.adjoin K ({ι y} : Set M)
  obtain ⟨S, hS⟩ := h.fg_top
  refine ⟨⟨S, ?_⟩⟩
  rw [eq_top_iff]
  rintro b -
  have hb : b ∈ Submodule.span R' (S : Set M) := by rw [hS]; exact Submodule.mem_top
  induction hb using Submodule.span_induction with
  | mem b hb => exact Submodule.subset_span hb
  | zero => exact zero_mem _
  | add b b' _ _ ih ih' => exact add_mem ih ih'
  | smul r' b _ ih =>
    have hc : (r' : M) = ι ((adjoinEquivAlong ι y).symm r' :
        IntermediateField.adjoin K ({y} : Set F)) := by
      rw [← coe_adjoinEquivAlong ι y, AlgEquiv.apply_symm_apply]
    have hr : r' • b =
        (((adjoinEquivAlong ι y).symm r' : IntermediateField.adjoin K ({y} : Set F)) : F) • b := by
      change (r' : M) * b = ι _ * b
      rw [hc]
    rw [hr]
    exact Submodule.smul_mem _ _ ih

private theorem separableAlong_of_isSeparable_adjoin
    [Algebra.IsSeparable (IntermediateField.adjoin K ({ι y} : Set M)) M] :
    SeparableAlong K ι := by
  letI := algebraAlong ι
  set R := IntermediateField.adjoin K ({y} : Set F)
  set R' := IntermediateField.adjoin K ({ι y} : Set M)
  refine ⟨fun b => ?_⟩
  have hs : (minpoly R' b).Separable := Algebra.IsSeparable.isSeparable R' b
  set e := adjoinEquivAlong ι y
  set φ : R' →+* F := (algebraMap R F).comp (e.symm : R' →+* R) with hφ
  have hcomp : (algebraMap F M).comp φ = algebraMap R' M := by
    ext r'
    change ι (algebraMap R F (e.symm r')) = (r' : M)
    rw [show algebraMap R F (e.symm r') = ((e.symm r' : R) : F) from rfl, ← coe_adjoinEquivAlong ι y,
      AlgEquiv.apply_symm_apply]
  have hq : ((minpoly R' b).map φ).Separable := hs.map
  have hqb : Polynomial.aeval b ((minpoly R' b).map φ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
    exact minpoly.aeval R' b
  exact hq.of_dvd (minpoly.dvd F b hqb)

private theorem normalAlong_of_normal_adjoin
    [Normal (IntermediateField.adjoin K ({ι y} : Set M)) M] :
    @Normal F M _ _ (algebraAlong ι) := by
  letI := algebraAlong ι
  set R := IntermediateField.adjoin K ({y} : Set F)
  set R' := IntermediateField.adjoin K ({ι y} : Set M)
  set e := adjoinEquivAlong ι y
  set φ : R' →+* F := (algebraMap R F).comp (e.symm : R' →+* R) with hφ
  have hcomp : (algebraMap F M).comp φ = algebraMap R' M := by
    ext r'
    change ι (algebraMap R F (e.symm r')) = (r' : M)
    rw [show algebraMap R F (e.symm r') = ((e.symm r' : R) : F) from rfl, ← coe_adjoinEquivAlong ι y,
      AlgEquiv.apply_symm_apply]
  refine normal_iff.mpr fun b => ?_
  have hint : IsIntegral R' b := Normal.isIntegral inferInstance b
  have hsplit : ((minpoly R' b).map (algebraMap R' M)).Splits :=
    Normal.splits inferInstance b
  have hqb : Polynomial.aeval b ((minpoly R' b).map φ) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp, ← Polynomial.aeval_def]
    exact minpoly.aeval R' b
  have hintF : IsIntegral F b := ⟨(minpoly R' b).map φ, (minpoly.monic hint).map φ, by
    rw [← Polynomial.aeval_def]; exact hqb⟩
  refine ⟨hintF, ?_⟩
  have hdvd : minpoly F b ∣ (minpoly R' b).map φ := minpoly.dvd F b hqb
  have hsplit' : (((minpoly R' b).map φ).map (algebraMap F M)).Splits := by
    rw [Polynomial.map_map, hcomp]
    exact hsplit
  exact Polynomial.Splits.of_dvd hsplit' (Polynomial.map_ne_zero
    (Polynomial.map_monic_ne_zero (minpoly.monic hint))) (Polynomial.map_dvd _ hdvd)

end Along

section Galois

variable (K E M : Type*) [Field K] [Field E] [Field M]
  [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]

private def toSemilinear : (M ≃ₐ[E] M) →* SemilinearAut K M where
  toFun σ := SemilinearAut.ofAlgAut (σ.restrictScalars K)
  map_one' := by ext <;> rfl
  map_mul' _ _ := by ext <;> rfl

@[reducible] private def placeAction : MulAction (M ≃ₐ[E] M) (Place K M) :=
  MulAction.compHom _ (toSemilinear K E M)

attribute [local instance] placeAction

variable {K E M}

private theorem smul_place_def (σ : M ≃ₐ[E] M) (W : Place K M) :
    σ • W = SemilinearAut.ofAlgAut (σ.restrictScalars K) • W := rfl

private theorem mem_smul_place_iff (σ : M ≃ₐ[E] M) (W : Place K M) (y : M) :
    y ∈ (σ • W).toValuationSubring ↔ σ.symm y ∈ W.toValuationSubring := by
  rw [smul_place_def, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, SemilinearAut.ofAlgAut_smul]
  rfl

variable [FiniteDimensional E M] [IsGalois E M]

private theorem mem_fiberOver_iff_mem_orbit (P W : Place K M) :
    W ∈ (P.restrict E).fiberOver M ↔ W ∈ MulAction.orbit (M ≃ₐ[E] M) P := by
  rw [Place.mem_fiberOver, MulAction.mem_orbit_iff]
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq (K := K) (F' := E) P W h
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, rfl⟩
    exact Place.restrict_ofAlgAut_smul σ P

private theorem card_stabilizer_mul_card_fiberOver (P : Place K M) :
    Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) P) * ((P.restrict E).fiberOver M).card =
      Module.finrank E M := by
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer (M ≃ₐ[E] M) P)
  rw [MulAction.index_stabilizer, IsGalois.card_aut_eq_finrank] at h1
  have h2 : (MulAction.orbit (M ≃ₐ[E] M) P).ncard = ((P.restrict E).fiberOver M).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext W
    rw [Finset.mem_coe, mem_fiberOver_iff_mem_orbit]
  rw [h2] at h1
  exact h1

omit [FiniteDimensional E M] [IsGalois E M] in

private theorem inertiaDeg_eq_one_of_deg_eq_one {F' : Type*} [Field F'] [Algebra K F']
    [Algebra F' M] [IsScalarTower K F' M] [Algebra.IsIntegral F' M] (W : Place K M)
    (hW : W.deg = 1) : W.inertiaDeg F' = 1 := by
  have h := W.deg_restrict_mul_inertiaDeg (F := F')
  rw [hW] at h
  exact Nat.eq_one_of_mul_eq_one_left h

private theorem card_stabilizer_eq (P : Place K M) (hdeg : P.deg = 1) :
    Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) P) = P.ramificationIndex E := by
  have h1 := card_stabilizer_mul_card_fiberOver (K := K) (E := E) P
  have h2 := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (K := K)
    (P.restrict E) P rfl
  rw [inertiaDeg_eq_one_of_deg_eq_one P hdeg, mul_one] at h2
  have hpos : 0 < ((P.restrict E).fiberOver M).card :=
    Finset.card_pos.mpr ⟨P, Place.restrict_mem_fiberOver P⟩
  have : Nat.card (MulAction.stabilizer (M ≃ₐ[E] M) P) * ((P.restrict E).fiberOver M).card =
      P.ramificationIndex E * ((P.restrict E).fiberOver M).card := by
    rw [h1, mul_comm, h2]
  exact Nat.eq_of_mul_eq_mul_right hpos this

end Galois

section AlongPsi

variable {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M]
  (x : F) (t : M)

private def adjoinEquivNorm (ψ : F →ₐ[K] M) (hψ : ψ x = t) : K⟮x⟯ ≃ₐ[K] K⟮t⟯ :=
  (adjoinEquivAlong ψ x).trans (IntermediateField.equivOfEq (by rw [hψ]))

private theorem coe_adjoinEquivNorm (ψ : F →ₐ[K] M) (hψ : ψ x = t) (r : K⟮x⟯) :
    ((adjoinEquivNorm x t ψ hψ r : K⟮t⟯) : M) = ψ r := rfl

private def baseHom (ψ : F →ₐ[K] M) (hψ : ψ x = t) : K⟮t⟯ →+* F :=
  (algebraMap K⟮x⟯ F).comp ((adjoinEquivNorm x t ψ hψ).symm : K⟮t⟯ →+* K⟮x⟯)

private theorem psi_baseHom (ψ : F →ₐ[K] M) (hψ : ψ x = t) (r : K⟮t⟯) :
    ψ (baseHom x t ψ hψ r) = r := by
  show ψ (((adjoinEquivNorm x t ψ hψ).symm r : K⟮x⟯) : F) = r
  rw [← coe_adjoinEquivNorm x t ψ hψ, AlgEquiv.apply_symm_apply]

private theorem baseHom_mem (ψ : F →ₐ[K] M) (hψ : ψ x = t) (r : K⟮t⟯) :
    baseHom x t ψ hψ r ∈ K⟮x⟯ :=
  ((adjoinEquivNorm x t ψ hψ).symm r).2

private theorem apply_eq_of_mem_adjoin (ψ ψ' : F →ₐ[K] M) (hψ : ψ x = t) (hψ' : ψ' x = t) {f : F}
    (hf : f ∈ K⟮x⟯) : ψ f = ψ' f := by
  have h : ψ.comp (K⟮x⟯.val) = ψ'.comp (K⟮x⟯.val) := by
    refine IntermediateField.adjoin_algHom_ext K fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show ψ y = ψ' y
    rw [hψ, hψ']
  exact congrArg (fun φ : K⟮x⟯ →ₐ[K] M => φ ⟨f, hf⟩) h

private theorem psi'_baseHom (ψ ψ' : F →ₐ[K] M) (hψ : ψ x = t) (hψ' : ψ' x = t) (r : K⟮t⟯) :
    ψ' (baseHom x t ψ hψ r) = r := by
  rw [← apply_eq_of_mem_adjoin x t ψ ψ' hψ hψ' (baseHom_mem x t ψ hψ r)]
  exact psi_baseHom x t ψ hψ r

private theorem exists_algEquiv_comp_eq [Normal K⟮t⟯ M] (ψ ψ' : F →ₐ[K] M) (hψ : ψ x = t)
    (hψ' : ψ' x = t) : ∃ τ : M ≃ₐ[K⟮t⟯] M, ∀ f, τ (ψ f) = ψ' f := by
  letI : Algebra K⟮t⟯ F := (baseHom x t ψ hψ).toAlgebra
  letI : Algebra F M := algebraAlong ψ
  haveI : IsScalarTower K⟮t⟯ F M := IsScalarTower.of_algebraMap_eq fun r =>
    (psi_baseHom x t ψ hψ r).symm
  let ϕ : F →ₐ[K⟮t⟯] M :=
    { (ψ' : F →+* M) with
      commutes' := fun r => by
        show ψ' (baseHom x t ψ hψ r) = (r : M)
        exact psi'_baseHom x t ψ ψ' hψ hψ' r }
  have hϕ : ∀ f, ϕ f = ψ' f := fun f => rfl
  let τh : M →ₐ[K⟮t⟯] M := ϕ.liftNormal M
  haveI : Algebra.IsAlgebraic K⟮t⟯ M := Algebra.IsIntegral.isAlgebraic
  refine ⟨AlgEquiv.ofBijective τh (Algebra.IsAlgebraic.algHom_bijective τh), fun f => ?_⟩
  show τh (algebraMap F M f) = ψ' f
  rw [AlgHom.liftNormal_commutes]
  exact hϕ f

attribute [local instance] placeAction

private theorem restrictAlong_comp (ψ : F →ₐ[K] M) (τ : M ≃ₐ[K⟮t⟯] M)
    (h₁ : (((τ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ).toRingHom.IsIntegral)
    (h₂ : ψ.toRingHom.IsIntegral) (W : Place K M) :
    W.restrictAlong (((τ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ) h₁ =
      (τ⁻¹ • W).restrictAlong ψ h₂ := by
  apply Place.ext
  ext f
  show (τ (ψ f) ∈ W.toValuationSubring) ↔ ψ f ∈ (τ⁻¹ • W).toValuationSubring
  rw [mem_smul_place_iff]
  rfl

private theorem finiteAlong_norm [FiniteDimensional K⟮t⟯ M] (ψ : F →ₐ[K] M) (hψ : ψ x = t) :
    FiniteAlong K ψ := by
  haveI : FiniteDimensional K⟮ψ x⟯ M := by rw [hψ]; infer_instance
  exact finiteAlong_of_finiteDimensional_adjoin ψ x

private theorem separableAlong_norm [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M]
    (ψ : F →ₐ[K] M) (hψ : ψ x = t) : SeparableAlong K ψ := by
  haveI : IsGalois K⟮ψ x⟯ M := by rw [hψ]; infer_instance
  exact separableAlong_of_isSeparable_adjoin ψ x

private theorem isGalois_along [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M] (ψ : F →ₐ[K] M)
    (hψ : ψ x = t) : @IsGalois F _ M _ (algebraAlong ψ) := by
  letI := algebraAlong ψ
  haveI : IsGalois K⟮ψ x⟯ M := by rw [hψ]; infer_instance
  haveI : Algebra.IsSeparable F M := separableAlong_of_isSeparable_adjoin ψ x
  haveI : Normal F M := normalAlong_of_normal_adjoin ψ x
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

end AlongPsi

section Main

variable {K : Type*} [Field K] [IsAlgClosed K] {F M : Type*} [Field F] [Field M] [Algebra K F]
  [Algebra K M] (x : F) (t : M) (j₀ : K) (ι : F →ₐ[K] M) (hι : ι x = t)
  [FiniteDimensional K⟮t⟯ M] [IsGalois K⟮t⟯ M]
  (hint : ∀ ψ : F →ₐ[K] M, ψ x = t → ψ.toRingHom.IsIntegral)
  (W₀ : Place K M) (hW₀ : 0 < W₀.ord (t - algebraMap K M j₀))

attribute [local instance] placeAction

omit [IsAlgClosed K] [FiniteDimensional (↥K⟮t⟯) M] [IsGalois (↥K⟮t⟯) M] in
private theorem algebraMap_gen_sub :
    algebraMap K⟮t⟯ M (IntermediateField.AdjoinSimple.gen K t - algebraMap K K⟮t⟯ j₀) =
      t - algebraMap K M j₀ := by
  rw [map_sub, IntermediateField.AdjoinSimple.algebraMap_gen K t, ← IsScalarTower.algebraMap_apply]

include hW₀ in

omit [FiniteDimensional (↥K⟮t⟯) M] [IsGalois (↥K⟮t⟯) M] in
private theorem transcendental_t : Transcendental K t := by
  intro halg
  obtain ⟨c, hc⟩ : t ∈ (algebraMap K M).range := by
    have h1 := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)
    exact minpoly.mem_range_of_degree_eq_one K t h1
  rw [← hc, ← map_sub, Place.ord_algebraMap] at hW₀
  exact lt_irrefl _ hW₀

omit [IsAlgClosed K] [FiniteDimensional (↥K⟮t⟯) M] [IsGalois (↥K⟮t⟯) M] in
private theorem psi_sub (ψ : F →ₐ[K] M) (hψ : ψ x = t) :
    ψ (x - algebraMap K F j₀) = t - algebraMap K M j₀ := by
  rw [map_sub, hψ, ψ.commutes]

include hW₀ in

private theorem ord_eq_card_stabilizer :
    W₀.ord (t - algebraMap K M j₀) = Nat.card (MulAction.stabilizer (M ≃ₐ[K⟮t⟯] M) W₀) := by
  have htr := transcendental_t t j₀ W₀ hW₀
  have h := Place.ord_restrict (F := K⟮t⟯) W₀
    (IntermediateField.AdjoinSimple.gen K t - algebraMap K K⟮t⟯ j₀)
  rw [algebraMap_gen_sub] at h
  obtain ⟨-, h1⟩ := restrict_eq_basePlace (F := M) t htr W₀ j₀ hW₀
  rw [h1, mul_one] at h
  rw [h]
  have hdeg : W₀.deg = 1 := Place.deg_eq_one_of_isAlgClosed W₀
    (Place.deg_ne_zero_of_finiteDimensional_adjoin t htr W₀)
  exact_mod_cast (card_stabilizer_eq (K := K) (E := K⟮t⟯) W₀ hdeg).symm

include hW₀ in

omit [IsAlgClosed K] [FiniteDimensional (↥K⟮t⟯) M] [IsGalois (↥K⟮t⟯) M] in
private theorem ord_restrictAlong_pos (ψ : F →ₐ[K] M) (hψ : ψ x = t)
    (h : ψ.toRingHom.IsIntegral) :
    0 < (W₀.restrictAlong ψ h).ord (x - algebraMap K F j₀) := by
  have hf := Place.ord_restrictAlong ψ h W₀ (x - algebraMap K F j₀)
  rw [psi_sub x t j₀ ψ hψ] at hf
  rw [hf] at hW₀
  exact pos_of_mul_pos_right hW₀ (by exact_mod_cast Nat.zero_le _)

include hW₀ in

private theorem exists_smul_eq_of_ord_pos (W : Place K M) (hW : 0 < W.ord (t - algebraMap K M j₀)) :
    ∃ σ : M ≃ₐ[K⟮t⟯] M, σ • W₀ = W := by
  have htr := transcendental_t t j₀ W₀ hW₀
  obtain ⟨h0, -⟩ := restrict_eq_basePlace (F := M) t htr W₀ j₀ hW₀
  obtain ⟨h1, -⟩ := restrict_eq_basePlace (F := M) t htr W j₀ hW
  exact Place.exists_algEquiv_smul_eq_of_restrict_eq (K := K) (F' := K⟮t⟯) W₀ W (h1.trans h0.symm)

omit [IsAlgClosed K] [FiniteDimensional (↥K⟮t⟯) M] [IsGalois (↥K⟮t⟯) M] in
private theorem inv_comp_apply (σ : M ≃ₐ[K⟮t⟯] M) (hι : ι x = t) :
    (((σ⁻¹ : M ≃ₐ[K⟮t⟯] M) : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ι x = t := by
  show σ⁻¹ (ι x) = t
  rw [hι]
  exact σ⁻¹.commutes (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)

include hι hW₀ in

private theorem exists_restrictAlong_eq (w : Place K F) (hw : 0 < w.ord (x - algebraMap K F j₀)) :
    ∃ (ψ : F →ₐ[K] M) (hψ : ψ x = t), W₀.restrictAlong ψ (hint ψ hψ) = w := by
  obtain ⟨W, hWw⟩ := Place.restrictAlong_surjective ι (hint ι hι) (finiteAlong_norm x t ι hι)
    (separableAlong_norm x t ι hι) w
  dsimp only at hWw

  have hW : 0 < W.ord (t - algebraMap K M j₀) := by
    have hf := Place.ord_restrictAlong ι (hint ι hι) W (x - algebraMap K F j₀)
    rw [psi_sub x t j₀ ι hι, hWw] at hf
    rw [hf]
    letI := algebraAlong ι
    haveI := isScalarTower_along (K := K) ι
    haveI := isIntegral_along (K := K) ι (hint ι hι)
    have he : 0 < Place.ramificationIndexAlong ι W := W.ramificationIndex_pos (F := F)
    exact mul_pos (by exact_mod_cast he) hw
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_ord_pos t j₀ W₀ hW₀ W hW
  refine ⟨(((σ⁻¹ : M ≃ₐ[K⟮t⟯] M) : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ι,
    inv_comp_apply x t ι σ hι, ?_⟩
  rw [restrictAlong_comp t ι σ⁻¹ _ (hint ι hι) W₀, inv_inv, hσ, hWw]

private def toGal (ψ : F →ₐ[K] M) (hψ : ψ x = t) (u : M ≃+* M) (hu : ∀ f, u (ψ f) = ψ f) :
    M ≃ₐ[K⟮t⟯] M :=
  AlgEquiv.ofRingEquiv (f := u) fun r => by
    show u (r : M) = r
    rw [← psi_baseHom x t ψ hψ r]
    exact hu _

omit [IsAlgClosed K] [FiniteDimensional (↥K⟮t⟯) M] [IsGalois (↥K⟮t⟯) M] in
private theorem toGal_apply (ψ : F →ₐ[K] M) (hψ : ψ x = t) (u : M ≃+* M)
    (hu : ∀ f, u (ψ f) = ψ f) (y : M) : toGal x t ψ hψ u hu y = u y := rfl

omit [IsAlgClosed K] in
private theorem restrictAlong_eq_iff (ψ ψ' : F →ₐ[K] M) (hψ : ψ x = t) (hψ' : ψ' x = t) :
    W₀.restrictAlong ψ (hint ψ hψ) = W₀.restrictAlong ψ' (hint ψ' hψ') ↔
      ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
        ψ' = ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ := by
  constructor
  · intro h
    obtain ⟨τ, hτ⟩ := exists_algEquiv_comp_eq x t ψ ψ' hψ hψ'
    have hψ'eq : ψ' = ((τ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ :=
      AlgHom.ext fun f => (hτ f).symm
    subst hψ'eq
    rw [restrictAlong_comp t ψ τ _ (hint ψ hψ) W₀] at h

    letI := algebraAlong ψ
    haveI := isScalarTower_along (K := K) ψ
    haveI : Module.Finite F M := finiteAlong_norm x t ψ hψ
    haveI : IsGalois F M := isGalois_along x t ψ hψ
    obtain ⟨u, hu⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq (K := K) (F' := F) W₀ (τ⁻¹ • W₀)
      h.symm
    have huc : ∀ f, (u : M ≃+* M) (ψ f) = ψ f := fun f => u.commutes f
    let uk : M ≃ₐ[K⟮t⟯] M := toGal x t ψ hψ (u : M ≃+* M) huc
    have huk : uk • W₀ = τ⁻¹ • W₀ := by
      rw [smul_place_def, show uk.restrictScalars K = u.restrictScalars K from
        AlgEquiv.ext fun _ => rfl]
      exact hu
    refine ⟨τ * uk, ?_, ?_⟩
    · show (τ * uk) • W₀ = W₀
      rw [mul_smul, huk, smul_inv_smul]
    · ext f
      show τ (ψ f) = (τ * uk) (ψ f)
      rw [AlgEquiv.mul_apply, toGal_apply]
      exact congrArg τ (huc f).symm
  · rintro ⟨σ, hσ, rfl⟩
    rw [restrictAlong_comp t ψ σ _ (hint ψ hψ) W₀]
    have hσ' : σ⁻¹ • W₀ = W₀ := by
      rw [inv_smul_eq_iff]
      exact hσ.symm
    rw [hσ']

private abbrev Emb : Type _ := {ψ : F →ₐ[K] M // ψ x = t}

@[reducible] private def embAction : MulAction (M ≃ₐ[K⟮t⟯] M) (Emb x t (K := K)) where
  smul σ ψ := ⟨((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ.1, by
    show σ (ψ.1 x) = t
    rw [ψ.2]
    exact σ.commutes (⟨t, IntermediateField.mem_adjoin_simple_self K t⟩ : K⟮t⟯)⟩
  one_smul ψ := Subtype.ext (AlgHom.ext fun _ => rfl)
  mul_smul σ τ ψ := Subtype.ext (AlgHom.ext fun _ => rfl)

attribute [local instance] embAction

omit [IsAlgClosed K] in
private theorem setOf_sameClass_eq_orbit (ψ : Emb x t (K := K)) :
    {ψ' : Emb x t (K := K) | W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) =
        W₀.restrictAlong ψ.1 (hint ψ.1 ψ.2)} =
      MulAction.orbit (MulAction.stabilizer (M ≃ₐ[K⟮t⟯] M) W₀) ψ := by
  ext ψ'
  rw [Set.mem_ofPred_eq, MulAction.mem_orbit_iff, eq_comm,
    restrictAlong_eq_iff x t hint W₀ ψ.1 ψ'.1 ψ.2 ψ'.2]
  constructor
  · rintro ⟨σ, hσ, h⟩
    exact ⟨⟨σ, hσ⟩, Subtype.ext h.symm⟩
  · rintro ⟨⟨σ, hσ⟩, h⟩
    exact ⟨σ, hσ, (congrArg Subtype.val h).symm⟩

include hW₀ in

private theorem card_stabilizer_emb (ψ : Emb x t (K := K)) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer (M ≃ₐ[K⟮t⟯] M) W₀) ψ) =
      Place.ramificationIndexAlong ψ.1 W₀ := by
  letI := algebraAlong ψ.1
  haveI := isScalarTower_along (K := K) ψ.1
  haveI : Module.Finite F M := finiteAlong_norm x t ψ.1 ψ.2
  haveI : IsGalois F M := isGalois_along x t ψ.1 ψ.2
  have hdeg : W₀.deg = 1 := Place.deg_eq_one_of_isAlgClosed W₀
    (Place.deg_ne_zero_of_finiteDimensional_adjoin t (transcendental_t t j₀ W₀ hW₀) W₀)
  rw [show Place.ramificationIndexAlong ψ.1 W₀ = W₀.ramificationIndex F from rfl,
    ← card_stabilizer_eq (K := K) (E := F) W₀ hdeg]

  have fwd_comm : ∀ d : MulAction.stabilizer (MulAction.stabilizer (M ≃ₐ[K⟮t⟯] M) W₀) ψ,
      ∀ f, ((d.1.1 : M ≃ₐ[K⟮t⟯] M) : M ≃+* M) (ψ.1 f) = ψ.1 f := by
    intro d f
    have h := congrArg (fun e : Emb x t (K := K) => e.1 f) (MulAction.mem_stabilizer_iff.mp d.2)
    exact h
  let fwd : MulAction.stabilizer (MulAction.stabilizer (M ≃ₐ[K⟮t⟯] M) W₀) ψ →
      MulAction.stabilizer (M ≃ₐ[F] M) W₀ := fun d =>
    ⟨AlgEquiv.ofRingEquiv (f := ((d.1.1 : M ≃ₐ[K⟮t⟯] M) : M ≃+* M)) (fwd_comm d), by
      rw [MulAction.mem_stabilizer_iff, smul_place_def,
        show (AlgEquiv.ofRingEquiv (fwd_comm d) : M ≃ₐ[F] M).restrictScalars K =
          (d.1.1 : M ≃ₐ[K⟮t⟯] M).restrictScalars K from AlgEquiv.ext fun _ => rfl]
      exact MulAction.mem_stabilizer_iff.mp d.1.2⟩
  let bwd : MulAction.stabilizer (M ≃ₐ[F] M) W₀ →
      MulAction.stabilizer (MulAction.stabilizer (M ≃ₐ[K⟮t⟯] M) W₀) ψ := fun u =>
    ⟨⟨toGal x t ψ.1 ψ.2 (u.1 : M ≃+* M) (fun f => u.1.commutes f), by
      rw [MulAction.mem_stabilizer_iff, smul_place_def,
        show (toGal x t ψ.1 ψ.2 (u.1 : M ≃+* M) (fun f => u.1.commutes f)).restrictScalars K =
          u.1.restrictScalars K from AlgEquiv.ext fun _ => rfl]
      exact MulAction.mem_stabilizer_iff.mp u.2⟩, by
      rw [MulAction.mem_stabilizer_iff]
      exact Subtype.ext (AlgHom.ext fun f => u.1.commutes f)⟩
  exact Nat.card_congr
    { toFun := fwd
      invFun := bwd
      left_inv := fun d => Subtype.ext (Subtype.ext (AlgEquiv.ext fun _ => rfl))
      right_inv := fun u => Subtype.ext (AlgEquiv.ext fun _ => rfl) }

include hW₀ in

private theorem ord_restrictAlong_eq_card (ψ : F →ₐ[K] M) (hψ : ψ x = t) :
    (W₀.restrictAlong ψ (hint ψ hψ)).ord (x - algebraMap K F j₀) =
      Nat.card {ψ' : Emb x t (K := K) //
        W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)} := by
  set D := MulAction.stabilizer (M ≃ₐ[K⟮t⟯] M) W₀ with hD
  let ψe : Emb x t (K := K) := ⟨ψ, hψ⟩

  have h1 := Subgroup.card_mul_index (MulAction.stabilizer D ψe)
  rw [MulAction.index_stabilizer] at h1

  have h2 : (MulAction.orbit D ψe).ncard = Nat.card {ψ' : Emb x t (K := K) //
      W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)} := by
    rw [← setOf_sameClass_eq_orbit x t hint W₀ ψe, ← Nat.card_coe_set_eq]
    rfl

  have h3 := card_stabilizer_emb x t j₀ W₀ hW₀ ψe

  have h4 := ord_eq_card_stabilizer t j₀ W₀ hW₀
  have h5 := Place.ord_restrictAlong ψ (hint ψ hψ) W₀ (x - algebraMap K F j₀)
  rw [psi_sub x t j₀ ψ hψ] at h5
  rw [h2, h3] at h1

  have he : 0 < Place.ramificationIndexAlong ψ W₀ := by
    letI := algebraAlong ψ
    haveI := isScalarTower_along (K := K) ψ
    haveI := isIntegral_along (K := K) ψ (hint ψ hψ)
    exact W₀.ramificationIndex_pos (F := F)
  have h6 : (Place.ramificationIndexAlong ψ W₀ : ℤ) * (W₀.restrictAlong ψ (hint ψ hψ)).ord
      (x - algebraMap K F j₀) = (Place.ramificationIndexAlong ψ W₀ : ℤ) *
        Nat.card {ψ' : Emb x t (K := K) //
          W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)} := by
    rw [← h5, h4, ← hD, ← h1]
    push_cast
    ring
  exact mul_left_cancel₀ (by exact_mod_cast he.ne') h6

end Main

universe u v in
/-- The Galois orbit/stabiliser dictionary at a place. -/
theorem ord_restrictAlong_eq_natCard_algHom_of_isGalois
    (K : Type u) [Field K] [IsAlgClosed K]
    {F M : Type v} [Field F] [Field M] [Algebra K F] [Algebra K M]
    (x : F) (t : M) (j₀ : K) (ι : F →ₐ[K] M) (hι : ι x = t)
    (hfin : FiniteDimensional K⟮t⟯ M) (hgal : IsGalois K⟮t⟯ M)
    (hint : ∀ ψ : F →ₐ[K] M, ψ x = t → ψ.toRingHom.IsIntegral)
    (W₀ : Place K M) (hW₀ : 0 < W₀.ord (t - algebraMap K M j₀)) :
    (W₀.ord (t - algebraMap K M j₀) =
        Nat.card {σ : M ≃ₐ[K⟮t⟯] M // SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀}) ∧
    (∀ (ψ : F →ₐ[K] M) (hψ : ψ x = t),
        0 < (W₀.restrictAlong ψ (hint ψ hψ)).ord (x - algebraMap K F j₀)) ∧
    (∀ w : Place K F, 0 < w.ord (x - algebraMap K F j₀) →
        ∃ (ψ : F →ₐ[K] M) (hψ : ψ x = t), W₀.restrictAlong ψ (hint ψ hψ) = w) ∧
    (∀ (ψ ψ' : F →ₐ[K] M) (hψ : ψ x = t) (hψ' : ψ' x = t),
        W₀.restrictAlong ψ (hint ψ hψ) = W₀.restrictAlong ψ' (hint ψ' hψ') ↔
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ψ' = ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ) ∧
    (∀ (ψ : F →ₐ[K] M) (hψ : ψ x = t),
        (W₀.restrictAlong ψ (hint ψ hψ)).ord (x - algebraMap K F j₀) =
          Nat.card {ψ' : {ψ' : F →ₐ[K] M // ψ' x = t} //
            W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)}) := by
  haveI := hfin
  haveI := hgal
  refine ⟨?_, fun ψ hψ => ord_restrictAlong_pos x t j₀ W₀ hW₀ ψ hψ (hint ψ hψ),
    fun w hw => exists_restrictAlong_eq x t j₀ ι hι hint W₀ hW₀ w hw,
    fun ψ ψ' hψ hψ' => restrictAlong_eq_iff x t hint W₀ ψ ψ' hψ hψ',
    fun ψ hψ => ord_restrictAlong_eq_card x t j₀ hint W₀ hW₀ ψ hψ⟩
  rw [ord_eq_card_stabilizer t j₀ W₀ hW₀]
  congr 1


end Place


/-! ## The Hurwitz line bound for the different

The pin's `sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable` (418 ln,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean>):
the sum of `ordDiff` over the regular places of an `x`, plus the ramification
correction `-ord x - 1` over its poles, is at most `2g - 2 + 2[F : k(x)]`.  The
counting lemma `sum_bound` is the pin's; the pole count runs through the port's
`RationalFunctionField.transcendenceTower`, whose two facts the pin proves
(`poleDivisor_apply`, `degree_poleDivisor_eq_finrank`) are re-derived locally because
`Genus/Stichtenoth.lean` keeps them `private`.  The pin's `with_ratFunc` transports the
`RatFunc` tower to `k⟮x⟯`, and its `riemannRoch_and_constantsAreBase_pkg` /
`genus_eq_genusFF_pkg` / `degree_canonical_pkg` are the port's
`riemannRoch_and_constantsAreBase`, `genus_eq_genusFF` and
`degree_canonicalDivisor_eq_of_riemannRoch`, applied in place. -/

section HurwitzLineBound

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]

/-- The `RatFunc` transport: every instance the `RatFunc`-tower formulation needs can be
transported along `RatFunc k ≃ₐ[k] k⟮x⟯`. -/
private theorem with_ratFunc (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional k⟮x⟯ F) (hsep : Algebra.IsSeparable k⟮x⟯ F) {P : Prop}
    (h : ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F],
      algebraMap (RatFunc k) F RatFunc.X = x →
      Module.finrank (RatFunc k) F = Module.finrank k⟮x⟯ F → P) : P := by
  haveI := hfin
  haveI := hsep
  let e : RatFunc k ≃ₐ[k] k⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  letI : Algebra (RatFunc k) F := ((algebraMap k⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc k) F) (e.symm.toRingEquiv : k⟮x⟯ →+* RatFunc k)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap k⟮x⟯ F) := by
    ext y
    show algebraMap k⟮x⟯ F (e (e.symm y)) = algebraMap k⟮x⟯ F y
    rw [e.apply_symm_apply]
  haveI : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap k F a = algebraMap k⟮x⟯ F (e (algebraMap k (RatFunc k) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  haveI hfd : FiniteDimensional (RatFunc k) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  haveI : Algebra.IsSeparable (RatFunc k) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have hX : algebraMap (RatFunc k) F RatFunc.X = x := by
    show algebraMap k⟮x⟯ F (e RatFunc.X) = x
    exact RatFunc.algEquivOfTranscendental_X x hx
  have hn : Module.finrank (RatFunc k) F = Module.finrank k⟮x⟯ F :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl F) (by ext y; rfl)
  exact h hX hn

section Poles

variable [DecidableEq (RatFunc k)]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
  [HasPrincipalDivisors k F]

omit [DecidableEq (RatFunc k)] [FiniteDimensional (RatFunc k) F] in

private theorem poleDivisor_apply
    (T : TranscendenceTower k (RatFunc k) F) (w : Place k F) :
    T.poleDivisor w = (w.ramificationIndex (RatFunc k) : ℤ) *
      (Finsupp.single T.v 1) (w.restrict (RatFunc k)) :=
  Divisor.pullback_apply (Finsupp.single T.v 1) w

omit [DecidableEq (RatFunc k)] in
private theorem degree_poleDivisor_eq_finrank
    (T : TranscendenceTower k (RatFunc k) F) :
    Divisor.degree T.poleDivisor = (Module.finrank (RatFunc k) F : ℤ) := by
  rw [TranscendenceTower.poleDivisor, Divisor.degree_pullback, Divisor.degree_single, T.hvdeg]
  push_cast
  ring

omit [FiniteDimensional (RatFunc k) F] in

private theorem towerX_poleDivisor_apply (w : Place k F) :
    (RationalFunctionField.transcendenceTower k F).poleDivisor w =
      if w.ord (algebraMap (RatFunc k) F RatFunc.X) < 0 then
        -w.ord (algebraMap (RatFunc k) F RatFunc.X) else 0 := by
  have happ := poleDivisor_apply (RationalFunctionField.transcendenceTower k F) w
  have hres := w.ord_restrict (F := RatFunc k) (RatFunc.X : RatFunc k)
  have hv : (RationalFunctionField.transcendenceTower k F).v = RationalFunctionField.placeInfty k := rfl
  rw [hv] at happ
  by_cases hw : w.restrict (RatFunc k) = RationalFunctionField.placeInfty k
  · rw [hw, RationalFunctionField.ord_placeInfty_X, mul_neg, mul_one] at hres
    have hepos : 0 < Place.ramificationIndex (F := RatFunc k) w := w.ramificationIndex_pos
    rw [happ, hw, Finsupp.single_eq_same, mul_one, hres, neg_neg, ite_eq_left]
    rw [neg_lt_zero]
    exact_mod_cast hepos
  · have hnn := RationalFunctionField.ord_X_nonneg_of_ne_placeInfty k hw
    have h0 : 0 ≤ w.ord (algebraMap (RatFunc k) F RatFunc.X) := by
      rw [hres]; positivity
    rw [happ, Finsupp.single_eq_of_ne hw, mul_zero, ite_eq_right (not_lt.mpr h0)]

private theorem sum_poles_eq_finrank (hdeg1 : ∀ w : Place k F, w.deg = 1) :
    ∃ P : Finset (Place k F),
      (∀ w, w ∈ P ↔ w.ord (algebraMap (RatFunc k) F RatFunc.X) < 0) ∧
      ∑ w ∈ P, (-w.ord (algebraMap (RatFunc k) F RatFunc.X)) =
        (Module.finrank (RatFunc k) F : ℤ) := by
  have hD := towerX_poleDivisor_apply (k := k) (F := F)
  refine ⟨(RationalFunctionField.transcendenceTower k F).poleDivisor.support, fun w => ?_, ?_⟩
  · rw [Finsupp.mem_support_iff, hD]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => by omega⟩
    · exact ⟨fun h0 => absurd rfl h0, fun h' => absurd h' h⟩
  · rw [← degree_poleDivisor_eq_finrank (RationalFunctionField.transcendenceTower k F), Divisor.degree_eq_sum_support]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hdeg1, Nat.cast_one, mul_one, hD]
    rw [Finsupp.mem_support_iff, hD] at hw
    split_ifs at hw ⊢ with h
    · rfl
    · exact absurd rfl hw

end Poles

private theorem sum_bound {ι : Type*} [DecidableEq ι] (f m : ι → ℤ)
    (S : Finset ι) (hS : ∀ P, P ∉ S → f P = 0) (C : ℤ) (hC : ∑ P ∈ S, f P = C)
    (Poles : Finset ι) (hPoles : ∀ P, P ∈ Poles ↔ m P < 0) (n : ℤ)
    (hn : ∑ P ∈ Poles, (-m P) = n)
    (hreg : ∀ P, 0 ≤ m P → 0 ≤ f P) (hpole : ∀ P, m P - 1 ≤ f P)
    (T : Finset ι) (hT : ∀ P ∈ T, 0 ≤ m P) (Tinf : Finset ι) (hTinf : ∀ P ∈ Tinf, m P < 0) :
    ∑ P ∈ T, f P + ∑ P ∈ Tinf, (-m P - 1) ≤ C + 2 * n := by
  set U : Finset ι := S ∪ T ∪ Poles with hU
  have hSU : S ⊆ U := Finset.subset_union_left.trans Finset.subset_union_left
  have hTU : T ⊆ U := Finset.subset_union_right.trans Finset.subset_union_left
  have hPU : Poles ⊆ U \ T := by
    intro P hP
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_union_right _ hP, fun hPT => ?_⟩
    have h1 := (hPoles P).mp hP
    have h2 := hT P hPT
    omega

  have hUsum : ∑ P ∈ U, f P = C := by
    rw [← hC]; exact (Finset.sum_subset hSU fun P _ hPS => hS P hPS).symm

  have hsplit : ∑ P ∈ U \ T, f P + ∑ P ∈ T, f P = ∑ P ∈ U, f P := Finset.sum_sdiff hTU

  let g : ι → ℤ := fun P => if m P < 0 then m P - 1 else 0
  have hfg : ∀ P, g P ≤ f P := fun P => by
    show (if m P < 0 then m P - 1 else 0) ≤ f P
    split_ifs with h
    · exact hpole P
    · exact hreg P (not_lt.mp h)
  have hg1 : ∑ P ∈ U \ T, g P ≤ ∑ P ∈ U \ T, f P := Finset.sum_le_sum fun P _ => hfg P
  have hg2 : ∑ P ∈ Poles, g P = ∑ P ∈ U \ T, g P := by
    refine Finset.sum_subset hPU fun P _ hP => ?_
    show (if m P < 0 then m P - 1 else 0) = 0
    rw [ite_eq_right (fun h => hP ((hPoles P).mpr h))]
  have hg3 : ∑ P ∈ Poles, g P = ∑ P ∈ Poles, (m P - 1) :=
    Finset.sum_congr rfl fun P hP => ite_eq_left ((hPoles P).mp hP)

  have hcard : ∑ P ∈ Poles, (1 : ℤ) = Poles.card := by simp
  have hsum1 : ∑ P ∈ Poles, (m P - 1) = -n - Poles.card := by
    rw [Finset.sum_sub_distrib, hcard, ← hn, Finset.sum_neg_distrib, neg_neg]
  have hsum2 : ∑ P ∈ Poles, (-m P - 1) = n - Poles.card := by
    rw [Finset.sum_sub_distrib, hcard, hn]

  have hTP : Tinf ⊆ Poles := fun P hP => (hPoles P).mpr (hTinf P hP)
  have hinf : ∑ P ∈ Tinf, (-m P - 1) ≤ ∑ P ∈ Poles, (-m P - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hTP fun P hP _ => by
      have := (hPoles P).mp hP
      omega

  have hTle : ∑ P ∈ T, f P ≤ C + n + Poles.card := by
    have := hg1; rw [← hg2, hg3, hsum1] at this
    linarith
  linarith

/-- **The Hurwitz line bound**: the different contributes at most `2g - 2 + 2[F : k(x)]`.
Statement from
`Theorems/Thm_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean`. -/
theorem sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (hT : ∀ P ∈ T, 0 ≤ P.ord x)
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  classical
  haveI hC : IsCurveOver k F :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable k F x hx hfin hsep
  haveI hEss : Algebra.EssFiniteType k F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hfin
  haveI hK : HasCanonicalDivisor (K := k) (F := F) := hasCanonicalDivisor_of_isCurveOver
  haveI hG : ∀ v : Place k F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  haveI hsepI : Algebra.IsSeparable k⟮x⟯ F := hsep

  have hω : KaehlerDifferential.D k F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental k x hx
  have hrr := riemannRoch_and_constantsAreBase (K := k) (F := F)
  have hSG : StichtenothGenusExists k F :=
    stichtenothGenusExists_of_isCurveOver (K := k) (F := F) hrr.2
  have wda : WeilDualityAdelic k F :=
    weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists hrr.1 hSG
  have hgenus : genus k F = genusFF k F := genus_eq_genusFF hrr.1 wda hrr.2
  have hWapp : ∀ P : Place k F, canonicalDivisorOf hω P = P.ordDiff ((KaehlerDifferential.D k F x)) := fun P => by
    rw [canonicalDivisorOf_apply]
    rfl
  have hWdeg : (canonicalDivisorOf hω).degree = 2 * (genusFF k F : ℤ) - 2 := by
    rw [← hgenus]
    exact degree_canonicalDivisor_eq_of_riemannRoch hrr.1 hrr.2 hω
  have hdeg1 : ∀ P : Place k F, P.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have hS : ∀ P, P ∉ (canonicalDivisorOf hω).support → P.ordDiff ((KaehlerDifferential.D k F x)) = 0 := fun P hP => by
    rw [← hWapp]; exact Finsupp.notMem_support_iff.mp hP
  have hsumW : ∑ P ∈ (canonicalDivisorOf hω).support, P.ordDiff ((KaehlerDifferential.D k F x)) =
      2 * (genusFF k F : ℤ) - 2 := by
    rw [← hWdeg, Divisor.degree_eq_sum_support]
    exact (Finset.sum_congr rfl fun P _ => by rw [hWapp, hdeg1, Nat.cast_one, mul_one]).symm

  obtain ⟨Poles, hPoles, hn⟩ : ∃ Poles : Finset (Place k F), (∀ w, w ∈ Poles ↔ w.ord x < 0) ∧
      ∑ w ∈ Poles, (-w.ord x) = (Module.finrank k⟮x⟯ F : ℤ) := by
    refine with_ratFunc x hx hfin hsep ?_
    intro _ _ _ _ hX hnn
    have h := sum_poles_eq_finrank hdeg1
    rw [hX, hnn] at h
    exact h

  have hreg : ∀ P : Place k F, 0 ≤ P.ord x → 0 ≤ P.ordDiff ((KaehlerDifferential.D k F x)) := fun P hP => by
    rw [Place.ordDiff_def]
    exact Place.ord_diffCoeff_D_nonneg_of_perfectField x P
      (P.ord_uniformizer_alt P.exists_ord_eq_one) hP
  have hpole : ∀ P : Place k F, P.ord x - 1 ≤ P.ordDiff ((KaehlerDifferential.D k F x)) := fun P =>
    Place.ord_sub_one_le_ordDiff_D_of_perfectField x P hω
  exact sum_bound (fun P : Place k F => P.ordDiff (KaehlerDifferential.D k F x)) (fun P => P.ord x)
    (canonicalDivisorOf hω).support hS _ hsumW Poles hPoles _ hn hreg hpole T hT Tinf hTinf

end HurwitzLineBound

/-! ## The logarithmic Hurwitz line bound

The pin's `sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable` (76 ln,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean>):
replacing the `ordDiff` summands of the bound above by `ord (x - a) - 1` costs nothing, since
`Place.ord_sub_one_le_ordDiff_D_of_perfectField` bounds each summand from above and a
translation of `x` does not change its differential.  The two helpers are the pin's
`HurwitzRamificationOverLine` lemmas; the summed bound
`sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable` and the local bound are this module's own
public declarations, applied in place. -/

section HurwitzLogBound

variable {k : Type*} [Field k] {F : Type*} [Field F] [Algebra k F]

/-- A place at which `x - a` has positive order is a place where `x` is integral. -/
private theorem ord_nonneg_of_ord_sub_algebraMap_pos (P : Place k F) (x : F) (a : k)
    (h : 0 < P.ord (x - algebraMap k F a)) : 0 ≤ P.ord x := by
  have h1 : P.adicValuation (x - algebraMap k F a) ≤ 1 :=
    P.adicValuation_le_one_iff.mpr (Or.inr h.le)
  have h2 : P.adicValuation (algebraMap k F a) ≤ 1 := P.adicValuation_algebraMap_le_one a
  have h3 : P.adicValuation x ≤ 1 := by
    have hx : x = (x - algebraMap k F a) + algebraMap k F a := by ring
    rw [hx]
    exact Valuation.map_add_le _ h1 h2
  rcases P.adicValuation_le_one_iff.mp h3 with hx0 | hx0
  · simp [hx0]
  · exact hx0

/-- Translating `x` does not change its differential. -/
private theorem D_sub_algebraMap (x : F) (a : k) :
    KaehlerDifferential.D k F (x - algebraMap k F a) = KaehlerDifferential.D k F x := by
  rw [map_sub, Derivation.map_algebraMap, sub_zero]

/-- **The logarithmic Hurwitz line bound**: the sum of `ord (x - a) - 1` over the places
where `x - a` has positive order, plus the pole correction `-ord x - 1`, is at most
`2g - 2 + 2[F : k(x)]`.  Statement from
`Theorems/Thm_AlgebraicCurve_sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable.lean`. -/
theorem sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (a : Place k F → k)
    (hT : ∀ P ∈ T, 0 < P.ord (x - algebraMap k F (a P)))
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, (P.ord (x - algebraMap k F (a P)) - 1) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  haveI := hfin
  haveI := hsep
  have hmain :=
    sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable k x hx hfin hsep T
      (fun P hP => ord_nonneg_of_ord_sub_algebraMap_pos P x (a P) (hT P hP)) Tinf hTinf
  have hDx : KaehlerDifferential.D k F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental k x hx
  have hloc : ∀ P ∈ T,
      P.ord (x - algebraMap k F (a P)) - 1 ≤ P.ordDiff (KaehlerDifferential.D k F x) := by
    intro P hP
    have hD : KaehlerDifferential.D k F (x - algebraMap k F (a P)) ≠ 0 := by
      rwa [D_sub_algebraMap]
    have h := Place.ord_sub_one_le_ordDiff_D_of_perfectField x P hD
    rwa [D_sub_algebraMap] at h
  have hsum :
      ∑ P ∈ T, (P.ord (x - algebraMap k F (a P)) - 1) ≤
        ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) :=
    Finset.sum_le_sum hloc
  linarith

end HurwitzLogBound

end AlgebraicCurve
