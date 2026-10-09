/-
  The leading coefficient of the transported modular polynomial `Φ_N`.

  Row 1 of subject B: for `N` not a square, the leading coefficient of
  `data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X` — the `Y`-leading
  coefficient of the modular polynomial evaluated at `X = j` — is a unit of `ℤ`.
  Equivalently it is `±1`; the `2N`-th power of that integer is `1`, and `2N > 0`.

  The proof is the pin's: it transports the datum to the cyclotomic field
  `K = ℚ(ζ_N)`, where `minpoly_jqN_map_eq_prod_slots` factors
  `Φ.map (coeffEmb ∘ qExpand ℚ N)` into the `N.divisors`-indexed product over the
  slot family. Every slot factor `TS K N 1 - TS K (a*a) (ζ ^ (b*a))` is nonzero
  with leading coefficient in the `2N`-torsion of `Kˣ` (`w1_slot_factor`), and both
  properties survive the product (`w1_prod_ne_zero_leadingCoeff`), so the leading
  coefficient of `f W` — where `f = coeffEmb K ∘ qExpand ℚ N` and
  `W = evalAtJ D` — is a `2N`-th root of unity in `K`. Injectivity of `ℚ → K`
  pulls the `ℚ`-statement back, and `exact_mod_cast` clears the denominators.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.lean`
  (724 lines). The public statement is the `Theorems/` wrapper verbatim. The
  pin's public prelude (`TS`, its coefficient lemmas, `qTwistEquiv`, the conjugate
  family, `phiAtSeed`, the at-slot roots) is already in the port and is imported.

  ## Reuse

  Imports `Defs/TS`, `Defs/PhiAtSlot`, `Defs/Cyclotomic`, `ModularPolynomialIrreducible`
  (`aeval_jqN_toAdjoin`), `FunctionFieldGeneration/SlotProduct`
  (`minpoly_jqN_map_eq_prod_slots`) and `FunctionFieldGeneration/Capstone`
  (`finrank_adjoin_jqN_eq_dedekindPsi`, `modularFunctionField_eq_full`).

  ## Local `private` re-derivations

  The pin's ten new `W1` helpers, all `private` at the pin too (so no promotion is
  available or authorised): `w1_order_eq`, `w1_order_TS`,
  `w1_order_sub_left`/`w1_order_sub_right`, `w1_prod_ne_zero_leadingCoeff`,
  `w1_slot_factor`, `w1_natDegree_toAdjoin`, `w1_toAdjoin_eq_minpoly`,
  `w1_diag_lc_pow`, and the headline's pin-`private` body. The pin's private
  `w1_evalAtJGen_injective` is dropped — it has no consumer anywhere (the public
  `evalAtJGen_injective` is imported from `ModularPolynomialIrreducible.lean`).
-/
import FLTForHuman.ModularCurve.ModularPolynomialIrreducible
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

/-! ## The U2 kit: Hahn-series order and the slot factor -/

/-- `order`/`leadingCoeff` of a series from its lowest nonzero coefficient. -/
private theorem w1_order_eq {K : Type*} [Field K] {x : LaurentSeries K} {a : ℤ}
    (hne : x.coeff a ≠ 0) (hlow : ∀ k, k < a → x.coeff k = 0) :
    x.order = a ∧ x.leadingCoeff = x.coeff a := by
  have hx0 : x ≠ 0 := fun h0 => hne (by simp [h0])
  have h1 : x.order = a := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hne) (not_lt.mp fun hlt => ?_)
    exact hx0 (HahnSeries.coeff_order_eq_zero.mp (hlow _ hlt))
  exact ⟨h1, by rw [HahnSeries.leadingCoeff_eq, h1]⟩

/-- `TS K e u` has order `-e` and leading coefficient `u⁻¹`. -/
private theorem w1_order_TS {K : Type*} [Field K] [Algebra ℚ K] (e : ℕ) [NeZero e] (u : Kˣ) :
    (TS K e u).order = -(e : ℤ) ∧ (TS K e u).leadingCoeff = ((u⁻¹ : Kˣ) : K) := by
  have h := w1_order_eq (x := TS K e u) (a := -(e : ℤ))
    (by rw [TS_coeff_neg]; exact Units.ne_zero _) (fun k hk => TS_coeff_of_lt (K := K) e u hk)
  exact ⟨h.1, by rw [h.2, TS_coeff_neg]⟩

/-- Subtracting a series of strictly larger order leaves the leading term. -/
private theorem w1_order_sub_right {K : Type*} [Field K] {x y : LaurentSeries K}
    (h : y.order < x.order) (hy : y ≠ 0) :
    (x - y).order = y.order ∧ (x - y).leadingCoeff = -y.leadingCoeff := by
  have hat : (x - y).coeff y.order = -y.leadingCoeff := by
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_eq_zero_of_lt_order h, zero_sub,
      HahnSeries.leadingCoeff_eq]
  have h' := w1_order_eq (x := x - y) (a := y.order)
    (by rw [hat, neg_ne_zero]; exact fun h0 => hy (HahnSeries.leadingCoeff_eq_zero.mp h0))
    (fun k hk => by
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_eq_zero_of_lt_order (hk.trans h),
        HahnSeries.coeff_eq_zero_of_lt_order hk, sub_zero])
  exact ⟨h'.1, by rw [h'.2, hat]⟩

/-- The mirror of `w1_order_sub_right`: subtracting a strictly smaller order. -/
private theorem w1_order_sub_left {K : Type*} [Field K] {x y : LaurentSeries K}
    (h : x.order < y.order) (hx : x ≠ 0) :
    (x - y).order = x.order ∧ (x - y).leadingCoeff = x.leadingCoeff := by
  have hat : (x - y).coeff x.order = x.leadingCoeff := by
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_eq_zero_of_lt_order h, sub_zero,
      HahnSeries.leadingCoeff_eq]
  have h' := w1_order_eq (x := x - y) (a := x.order)
    (by rw [hat]; exact fun h0 => hx (HahnSeries.leadingCoeff_eq_zero.mp h0))
    (fun k hk => by
      rw [HahnSeries.coeff_sub, HahnSeries.coeff_eq_zero_of_lt_order hk,
        HahnSeries.coeff_eq_zero_of_lt_order (hk.trans h), sub_zero])
  exact ⟨h'.1, by rw [h'.2, hat]⟩

/-- A product of nonzero series over a finset is nonzero, and its leading
coefficient is the product of the leading coefficients. -/
private theorem w1_prod_ne_zero_leadingCoeff {K : Type*} [Field K] {α : Type*} (s : Finset α)
    (F : α → LaurentSeries K) (h : ∀ i ∈ s, F i ≠ 0) :
    (∏ i ∈ s, F i) ≠ 0 ∧ (∏ i ∈ s, F i).leadingCoeff = ∏ i ∈ s, (F i).leadingCoeff := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h0, hlc⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha0 : F a ≠ 0 := h a (Finset.mem_insert_self a s)
    have hne : (F a).leadingCoeff * (∏ i ∈ s, F i).leadingCoeff ≠ 0 :=
      mul_ne_zero (fun hz => ha0 (HahnSeries.leadingCoeff_eq_zero.mp hz))
        (fun hz => h0 (HahnSeries.leadingCoeff_eq_zero.mp hz))
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ⟨mul_ne_zero ha0 h0,
      by rw [HahnSeries.leadingCoeff_mul_of_ne_zero hne, hlc]⟩

/-- The slot factor is nonzero and its leading coefficient is a `2N`-th root of
unity. This is the arithmetic heart of the row. -/
private theorem w1_slot_factor {K : Type*} [Field K] [Algebra ℚ K] (N a b : ℕ) [NeZero N]
    [NeZero a] (hN : ¬ IsSquare N) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N) :
    (TS K N 1 - TS K (a * a) (ζ ^ (b * a))) ≠ 0 ∧
      (TS K N 1 - TS K (a * a) (ζ ^ (b * a))).leadingCoeff ^ (2 * N) = 1 := by
  have hne : a * a ≠ N := fun h => hN ⟨a, h.symm⟩
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  ·
    obtain ⟨hoN, hlN⟩ := w1_order_TS (K := K) N 1
    obtain ⟨hoa, _⟩ := w1_order_TS (K := K) (a * a) (ζ ^ (b * a))
    have hord : (TS K N 1).order < (TS K (a * a) (ζ ^ (b * a))).order := by
      rw [hoN, hoa]
      push_cast
      omega
    obtain ⟨_, hlc⟩ := w1_order_sub_left hord (TS_ne_zero (K := K) N 1)
    have hlc1 : (TS K N 1 - TS K (a * a) (ζ ^ (b * a))).leadingCoeff = 1 := by
      rw [hlc, hlN, inv_one, Units.val_one]
    refine ⟨fun h0 => one_ne_zero (α := K) ?_, by rw [hlc1, one_pow]⟩
    rw [← hlc1, h0, HahnSeries.leadingCoeff_eq_zero.mpr rfl]
  ·
    obtain ⟨hoN, _⟩ := w1_order_TS (K := K) N 1
    obtain ⟨hoa, hla⟩ := w1_order_TS (K := K) (a * a) (ζ ^ (b * a))
    have hord : (TS K (a * a) (ζ ^ (b * a))).order < (TS K N 1).order := by
      rw [hoN, hoa]
      push_cast
      omega
    obtain ⟨_, hlc⟩ := w1_order_sub_right hord (TS_ne_zero (K := K) (a * a) (ζ ^ (b * a)))
    have hlcv : (TS K N 1 - TS K (a * a) (ζ ^ (b * a))).leadingCoeff =
        -((ζ : K) ^ (b * a))⁻¹ := by
      rw [hlc, hla, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have hvne : -((ζ : K) ^ (b * a))⁻¹ ≠ 0 := by
      rw [neg_ne_zero]
      exact inv_ne_zero (pow_ne_zero _ (Units.ne_zero ζ))
    refine ⟨fun h0 => hvne ?_, ?_⟩
    · rw [← hlcv, h0, HahnSeries.leadingCoeff_eq_zero.mpr rfl]
    · have hzN : (ζ : K) ^ N = 1 := hζ.pow_eq_one
      have hv : (((ζ : K) ^ (b * a)) ^ (2 * N) : K) = 1 := by
        rw [← pow_mul, show b * a * (2 * N) = N * (2 * (b * a)) by ring, pow_mul, hzN, one_pow]
      have heven : Even (2 * N) := ⟨N, by ring⟩
      rw [hlcv, heven.neg_pow, inv_pow, hv, inv_one]

/-! ## Transporting the datum to the cyclotomic field -/

/-- The `Y`-degree of the transported datum is `ψ(N)`. -/
private theorem w1_natDegree_toAdjoin {N : ℕ} [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin.natDegree = dedekindPsi N := by
  rw [ModularPolynomialData.toAdjoin, data.monic.natDegree_map, data.natDegree_eq]

/-- `data.toAdjoin` is the minimal polynomial of `j(q ^ N)`. -/
private theorem w1_toAdjoin_eq_minpoly (N : ℕ) [NeZero N] (data : ModularPolynomialData N) :
    data.toAdjoin = minpoly ℚ⟮jq⟯ (jqN N) := by
  have hint : IsIntegral ℚ⟮jq⟯ (jqN N) := ⟨data.toAdjoin, data.toAdjoin_monic, by
    simpa [Polynomial.aeval_def] using aeval_jqN_toAdjoin data⟩
  have hdeg : (minpoly ℚ⟮jq⟯ (jqN N)).natDegree = dedekindPsi N := by
    rw [← IntermediateField.adjoin.finrank hint]
    exact finrank_adjoin_jqN_eq_dedekindPsi N
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) data.toAdjoin_monic
    (minpoly.dvd _ _ (aeval_jqN_toAdjoin data)) ?_
  rw [hdeg, w1_natDegree_toAdjoin]

/-- The `2N`-th power of the `Y`-leading coefficient of `Φ(j, Y)` is `1`: push the
datum to `ℚ(ζ_N)`, factor it into its nonzero slot factors, and read the leading
coefficient of the product off `w1_slot_factor`. -/
private theorem w1_diag_lc_pow (N : ℕ) [NeZero N] (hN : ¬ IsSquare N)
    (data : ModularPolynomialData N) :
    (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff ^ (2 * N) = 1 := by
  classical
  set D : Polynomial ℤ := data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X with hD
  set K := CyclotomicField N ℚ with hK
  set ζ : Kˣ := cycUnit N with hζdef
  have hζ := cycUnit_spec N
  set f : LaurentSeries ℚ →+* LaurentSeries K := (coeffEmb K).comp (qExpand ℚ N) with hf
  set W : LaurentSeries ℚ := evalAtJ D with hW

  have hcensus := minpoly_jqN_map_eq_prod_slots (K := K) N ζ hζ
    (fun d _ _ => ⟨finrank_adjoin_jqN_eq_dedekindPsi d, modularFunctionField_eq_full d⟩)

  have hhom : ((((coeffEmb K).comp (qExpand ℚ N)).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))).comp evalAtJGen) = f.comp evalAtJ := by
    rw [RingHom.comp_assoc, algebraMap_comp_evalAtJGen, hf]
  have hmaps : data.Φ.map (f.comp evalAtJ) =
      ∏ a ∈ N.divisors, ∏ b ∈ (Finset.range (N / a)).filter
        (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
        (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))) := by
    rw [← hcensus, ← w1_toAdjoin_eq_minpoly N data, ModularPolynomialData.toAdjoin,
      Polynomial.map_map, hhom]

  have hfjq : f jq = TS K N 1 := iota_jq N
  have hfact : f W = ∏ a ∈ N.divisors, ∏ b ∈ (Finset.range (N / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
      (TS K N 1 - (if h : a = 0 then 0 else
        letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)))) := by
    have h1 : f W = (data.Φ.map (f.comp evalAtJ)).eval (f jq) := by
      rw [hW, ← RingHom.comp_apply, hD, Polynomial.hom_eval₂, RingHom.comp_id,
        Polynomial.eval₂_eq_eval_map, RingHom.comp_apply, evalAtJ_X]
    rw [h1, hmaps, Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Polynomial.eval_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hfjq]

  have hinner : ∀ a ∈ N.divisors,
      (∏ b ∈ (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
        (TS K N 1 - (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))))) ≠ 0 ∧
      ((∏ b ∈ (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1),
        (TS K N 1 - (if h : a = 0 then 0 else
          letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))))).leadingCoeff)
        ^ (2 * N) = 1 := by
    intro a ha
    have ha0 : a ≠ 0 := (Nat.pos_of_mem_divisors ha).ne'
    have haNe : NeZero a := ⟨ha0⟩
    have hdval : ∀ b : ℕ, (if h : a = 0 then (0 : LaurentSeries K) else
        letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))) =
        TS K (a * a) (ζ ^ (b * a)) := fun b => by rw [dite_eq_right ha0]; rfl
    simp only [hdval]
    obtain ⟨hne, hlc⟩ := w1_prod_ne_zero_leadingCoeff (K := K)
      ((Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1))
      (fun b => TS K N 1 - TS K (a * a) (ζ ^ (b * a)))
      (fun b _ => (w1_slot_factor N a b hN ζ hζ).1)
    refine ⟨hne, ?_⟩
    rw [hlc, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun b _ => (w1_slot_factor N a b hN ζ hζ).2

  obtain ⟨houter_ne, houter_lc⟩ := w1_prod_ne_zero_leadingCoeff (K := K) N.divisors _
    (fun a ha => (hinner a ha).1)
  have hfW_ne : f W ≠ 0 := by rw [hfact]; exact houter_ne
  have hfW_pow : (f W).leadingCoeff ^ (2 * N) = 1 := by
    rw [hfact, houter_lc, ← Finset.prod_pow]
    exact Finset.prod_eq_one fun a ha => (hinner a ha).2

  have hW_ne : W ≠ 0 := fun h0 => hfW_ne (by rw [h0, map_zero])
  have hD0 : D ≠ 0 := fun h0 => hW_ne (by rw [hW, h0, map_zero])
  have hEJ : evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) jq := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp [evalAtJ, Polynomial.coe_eval₂RingHom]
  have hsum : evalAtJ D = ∑ i ∈ Finset.range (D.natDegree + 1), (D.coeff i) • jq ^ i := by
    rw [hEJ]
    show Polynomial.eval₂ (Int.castRingHom (LaurentSeries ℚ)) jq D = _
    rw [Polynomial.eval₂_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => (zsmul_eq_mul _ _).symm
  have hWcoeff : ∀ m : ℤ, W.coeff m =
      ∑ i ∈ Finset.range (D.natDegree + 1), (D.coeff i) • (jq ^ i).coeff m := by
    intro m
    rw [hW, hsum, HahnSeries.coeff_sum]
    exact Finset.sum_congr rfl fun i _ => HahnSeries.coeff_smul
  have hlow : ∀ m : ℤ, m < -(D.natDegree : ℤ) → W.coeff m = 0 := by
    intro m hm
    rw [hWcoeff]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [coeff_jq_pow_of_lt, smul_zero]
    have : i ≤ D.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    omega
  have htop : W.coeff (-(D.natDegree : ℤ)) = (D.leadingCoeff : ℚ) := by
    rw [hWcoeff]
    rw [Finset.sum_eq_single D.natDegree]
    · rw [coeff_jq_pow_self, Polynomial.leadingCoeff]
      rw [zsmul_eq_mul, mul_one]
    · intro i hi hne
      have hilt : i < D.natDegree :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      rw [coeff_jq_pow_of_lt (by omega), smul_zero]
    · intro h
      exact absurd (Finset.mem_range.mpr D.natDegree.lt_succ_self) h

  have hPcoeff : ∀ m : ℤ, (f W).coeff ((N : ℤ) * m) = algebraMap ℚ K (W.coeff m) := by
    intro m
    rw [hf, RingHom.comp_apply, coeffEmb_coeff, qExpand_coeff_mul]
  have hPnd : ∀ k : ℤ, ¬ (N : ℤ) ∣ k → (f W).coeff k = 0 := by
    intro k hk
    rw [hf, RingHom.comp_apply, coeffEmb_coeff, qExpand_coeff_of_not_dvd N W hk, map_zero]
  have hcoeff_at : (f W).coeff ((N : ℤ) * (-(D.natDegree : ℤ))) =
      algebraMap ℚ K ((D.leadingCoeff : ℚ)) := by
    rw [hPcoeff, htop]
  have hlcD : (f W).leadingCoeff = algebraMap ℚ K ((D.leadingCoeff : ℚ)) := by
    have hne_at : (f W).coeff ((N : ℤ) * (-(D.natDegree : ℤ))) ≠ 0 := by
      rw [hcoeff_at]
      intro h0
      have : (D.leadingCoeff : ℚ) = 0 := (algebraMap ℚ K).injective (by rw [h0, map_zero])
      exact Polynomial.leadingCoeff_ne_zero.mpr hD0 (by exact_mod_cast this)
    have hbelow : ∀ k : ℤ, k < (N : ℤ) * (-(D.natDegree : ℤ)) → (f W).coeff k = 0 := by
      intro k hk
      by_cases hdvd : (N : ℤ) ∣ k
      · obtain ⟨m, rfl⟩ := hdvd
        rw [hPcoeff]
        have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
        rw [hlow m (lt_of_mul_lt_mul_left hk hNpos.le), map_zero]
      · exact hPnd _ hdvd
    obtain ⟨_, hlc_eq⟩ := w1_order_eq hne_at hbelow
    rw [hlc_eq, hcoeff_at]

  have hQpow : ((D.leadingCoeff : ℚ)) ^ (2 * N) = 1 := by
    refine (algebraMap ℚ K).injective ?_
    rw [map_pow, map_one, ← hlcD]
    exact hfW_pow
  exact_mod_cast hQpow

namespace ModularPolynomialData

/-- For `N` not a square, the `Y`-leading coefficient of `Φ(j, Y)` is a unit of
`ℤ`. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag_of_not_isSquare.lean`. -/
theorem isUnit_leadingCoeff_diag_of_not_isSquare (N : ℕ) [NeZero N] (hN : ¬ IsSquare N)
    (data : ModularCurve.ModularPolynomialData N) :
    IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff := by
  have h := w1_diag_lc_pow N hN data
  have h1 : (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff.natAbs
      ^ (2 * N) = 1 := by
    have h' := congrArg Int.natAbs h
    rwa [Int.natAbs_pow] at h'
  have h2 : (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff.natAbs = 1 := by
    rcases Nat.pow_eq_one.mp h1 with h' | h'
    · exact h'
    · have := NeZero.ne N
      omega
  exact Int.isUnit_iff.mpr ((Int.natAbs_eq_iff.mp h2).imp id (by simp))

end ModularPolynomialData

end ModularCurve

end

#print axioms ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare
