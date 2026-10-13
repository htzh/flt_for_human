/-
  The public coefficient and convergence theorems of the universal Tate curve under
  `Γ₀(ℓ)`-slot substitution: the convergence criterion `tsum_of_coeff_lt_eq_zero`
  and the Lambert identity `tsum_lambertTerm_eq`, the `single`-series closed forms,
  the injectivity of the generic slot substitution, the coefficient formulas
  `coeff_slotSubst_tateUnivX`/`_tateUnivY`, the `tateBase` equation, and the
  toric-point coefficients.

  These are the port's tier-1 surface over the tier-3 engine
  (`TateSlots/Convergence.lean`, `TateSlots/SlotCoeff.lean`). Each statement is
  the pin's `Theorems/Thm_ModularCurve_<name>.lean` wrapper verbatim — that
  wrapper, not the `S_` file's section-implicit `solution`, is the checker's
  statement authority — and each proof is the one-line application of the
  engine's kernel `ModularCurve.TateSlots.<name>`.

  The pin writes the same shape inside each `S_` file: a `private` kernel and a
  public `solution` forwarding to it. The port promotes the kernel to public in
  the engine (the fourteen `S_` files are near-identical copies of one
  development; see TOPIC-tate-slots-weight-four.md) and keeps the public
  statement here, at the pin's wrapper name.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_tsum_lambertTerm_eq.lean
  (and the thirteen sibling wrappers `Theorems/Thm_ModularCurve_<name>.lean`).
-/
import FLTForHuman.ModularCurve.TateSlots.Convergence
import FLTForHuman.ModularCurve.TateSlots.SlotCoeff

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve

-- pin: tsum_lambertTerm_eq (Theorems/Thm_ModularCurve_tsum_lambertTerm_eq.lean)
theorem tsum_lambertTerm_eq (K : Type*) [Field K] (p : ℕ) [NeZero p] (c : ℕ → ℕ) :
    ∑' n : ℕ, ((c n : ℕ) : LaurentSeries K) *
        ((HahnSeries.single (p : ℤ) (1 : K)) ^ n / (1 - (HahnSeries.single (p : ℤ) (1 : K)) ^ n)) =
      qExpand K p (laurentOfInt K (PowerSeries.mk fun m => ∑ d ∈ m.divisors, (c d : ℤ))) :=
  TateSlots.tsum_lambertTerm_eq K p c

-- pin: single_div_one_sub_sq (Theorems/Thm_ModularCurve_single_div_one_sub_sq.lean)
theorem single_div_one_sub_sq (K : Type*) [Field K] (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 2 =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => if j ∣ n then ((n / j : ℕ) : K) * c ^ (n / j) else 0) :=
  TateSlots.single_div_one_sub_sq K j hj c

-- pin: single_sq_div_one_sub_cube (Theorems/Thm_ModularCurve_single_sq_div_one_sub_cube.lean)
theorem single_sq_div_one_sub_cube (K : Type*) [Field K] (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c ^ 2 / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 3 =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => if j ∣ n then (((n / j).choose 2 : ℕ) : K) * c ^ (n / j) else 0) :=
  TateSlots.single_sq_div_one_sub_cube K j hj c

-- pin: slotSubst_gen_injective (Theorems/Thm_ModularCurve_slotSubst_gen_injective.lean)
theorem slotSubst_gen_injective : Function.Injective (slotSubst (LaurentSeries ℚ) 2
      (Units.mk0 (HahnSeries.single (1 : ℤ) (1 : ℚ)) (HahnSeries.single_ne_zero one_ne_zero)) 1) :=
  TateSlots.slotSubst_gen_injective

-- pin: coeff_slotSubst_tateUnivX (Theorems/Thm_ModularCurve_coeff_slotSubst_tateUnivX.lean)
theorem coeff_slotSubst_tateUnivX {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) : PowerSeries.coeff n (slotSubst K p c j tateUnivX) = (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0) + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (e : K) * ((if n = p * M + j * e then (c : K) ^ e else 0) + (if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0) - (if n = p * M then 2 else 0)) :=
  TateSlots.coeff_slotSubst_tateUnivX p c j hj hjp n

-- pin: coeff_slotSubst_tateUnivY (Theorems/Thm_ModularCurve_coeff_slotSubst_tateUnivY.lean)
theorem coeff_slotSubst_tateUnivY {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) : PowerSeries.coeff n (slotSubst K p c j tateUnivY) = (if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0) + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, ((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0) - (if n + j * e = p * M then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0) + (if n = p * M then (e : K) else 0)) :=
  TateSlots.coeff_slotSubst_tateUnivY p c j hj hjp n

-- pin: equation_tateBase_iff (Theorems/Thm_ModularCurve_equation_tateBase_iff.lean)
theorem equation_tateBase_iff (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (x y : LaurentSeries K) : (tateBase K p).toAffine.Equation x y ↔ y ^ 2 + x * y = x ^ 3 + qExpand K p (laurentOfInt K tateA4) * x + qExpand K p (laurentOfInt K tateA6) :=
  TateSlots.equation_tateBase_iff K p x y

-- pin: toricPoint_fst_coeff_mul (Theorems/Thm_ModularCurve_toricPoint_fst_coeff_mul.lean)
theorem toricPoint_fst_coeff_mul (K : Type*) [Field K] (p : ℕ) (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) : (toricPoint K p c).1.coeff ((p * M : ℕ) : ℤ) = ∑ e ∈ M.divisors, (e : K) * (c ^ e + c⁻¹ ^ e - 2) :=
  TateSlots.toricPoint_fst_coeff_mul K p hp c hM

-- pin: toricPoint_fst_coeff_of_not_dvd (Theorems/Thm_ModularCurve_toricPoint_fst_coeff_of_not_dvd.lean)
theorem toricPoint_fst_coeff_of_not_dvd (K : Type*) [Field K] (p : ℕ) (c : K) {m : ℕ} (hpm : ¬ p ∣ m) : (toricPoint K p c).1.coeff (m : ℤ) = 0 :=
  TateSlots.toricPoint_fst_coeff_of_not_dvd K p c hpm

-- pin: toricPoint_fst_coeff_zero (Theorems/Thm_ModularCurve_toricPoint_fst_coeff_zero.lean)
theorem toricPoint_fst_coeff_zero (K : Type*) [Field K] (p : ℕ) (c : K) : (toricPoint K p c).1.coeff 0 = c / (1 - c) ^ 2 :=
  TateSlots.toricPoint_fst_coeff_zero K p c

-- pin: toricPoint_snd_coeff_mul_eq_sum_divisors (Theorems/Thm_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.lean)
theorem toricPoint_snd_coeff_mul_eq_sum_divisors (K : Type*) [Field K] (p : ℕ) (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) : (toricPoint K p c).2.coeff ((p * M : ℕ) : ℤ) = ∑ e ∈ M.divisors, (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K)) :=
  TateSlots.toricPoint_snd_coeff_mul_eq_sum_divisors K p hp c hM

-- pin: toricPoint_snd_coeff_of_not_dvd (Theorems/Thm_ModularCurve_toricPoint_snd_coeff_of_not_dvd.lean)
theorem toricPoint_snd_coeff_of_not_dvd (K : Type*) [Field K] (p : ℕ) (c : K) {m : ℕ} (hpm : ¬ p ∣ m) : (toricPoint K p c).2.coeff (m : ℤ) = 0 :=
  TateSlots.toricPoint_snd_coeff_of_not_dvd K p c hpm

-- pin: toricPoint_snd_coeff_zero (Theorems/Thm_ModularCurve_toricPoint_snd_coeff_zero.lean)
theorem toricPoint_snd_coeff_zero (K : Type*) [Field K] (p : ℕ) (c : K) : (toricPoint K p c).2.coeff 0 = c ^ 2 / (1 - c) ^ 3 :=
  TateSlots.toricPoint_snd_coeff_zero K p c

-- pin: tsum_of_coeff_lt_eq_zero (Theorems/Thm_ModularCurve_tsum_of_coeff_lt_eq_zero.lean)
theorem tsum_of_coeff_lt_eq_zero {K : Type*} [Field K] {δ : ℕ} (hδ : 0 < δ) (f : ℕ → LaurentSeries K) (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0) (g : LaurentSeries K) (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) : ∑' N, f N = g :=
  TateSlots.tsum_of_coeff_lt_eq_zero hδ f hf g hg

end ModularCurve

end
