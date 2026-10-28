/-
  The public coefficient and convergence theorems of the universal Tate curve under
  `Γ₀(ℓ)`-slot substitution: the convergence criterion `tsum_of_coeff_lt_eq_zero`
  and the Lambert identity `tsum_lambertTerm_eq`, the `single`-series closed forms,
  the injectivity of the generic slot substitution, the coefficient formulas
  `coeff_slotSubst_tateUnivX`/`_tateUnivY`, the `tateBase` equation, the
  toric-point coefficients, and the unit twist of a non-toric point.

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

  One row goes further than that template. `qTwist_nonToricPoint_of_pow_eq_one`
  (`S_` file: 185 lines of proof, not a kernel application) says that the unit
  twist `qTwist ζ` — the coefficient rescaling `q ↦ ζ q` of
  `ModularCurve/Defs/Twist.lean` — carries the non-toric point
  `nonToricPoint K M c j` to `nonToricPoint K M (c * ζ ^ j) j` when `ζ ^ M = 1`:
  the twist moves `c` to `c * ζ ^ j` and the second slot's `ζ⁻ʲ` is `ζ ^ (M - j)`
  because `ζ ^ M = 1`. Its proof is the pin's, over the ported `qTwistFun` and the
  coefficient formulas above; the facts it needs stay `private` in this file,
  below, so the public surface gains exactly the wrapper's statement.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_tsum_lambertTerm_eq.lean
  (and the thirteen sibling wrappers `Theorems/Thm_ModularCurve_<name>.lean`).
spec-pin: Theorems/Thm_ModularCurve_tsum_lambertTerm_eq.lean
spec-pin: Theorems/Thm_ModularCurve_single_div_one_sub_sq.lean
spec-pin: Theorems/Thm_ModularCurve_single_sq_div_one_sub_cube.lean
spec-pin: Theorems/Thm_ModularCurve_slotSubst_gen_injective.lean
spec-pin: Theorems/Thm_ModularCurve_coeff_slotSubst_tateUnivX.lean
spec-pin: Theorems/Thm_ModularCurve_coeff_slotSubst_tateUnivY.lean
spec-pin: Theorems/Thm_ModularCurve_equation_tateBase_iff.lean
spec-pin: Theorems/Thm_ModularCurve_toricPoint_fst_coeff_mul.lean
spec-pin: Theorems/Thm_ModularCurve_toricPoint_fst_coeff_of_not_dvd.lean
spec-pin: Theorems/Thm_ModularCurve_toricPoint_fst_coeff_zero.lean
spec-pin: Theorems/Thm_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.lean
spec-pin: Theorems/Thm_ModularCurve_toricPoint_snd_coeff_of_not_dvd.lean
spec-pin: Theorems/Thm_ModularCurve_toricPoint_snd_coeff_zero.lean
spec-pin: Theorems/Thm_ModularCurve_tsum_of_coeff_lt_eq_zero.lean
spec-pin: Theorems/Thm_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one.lean
spec-pin: P2M/Sol/S_ModularCurve_tsum_lambertTerm_eq.lean
spec-pin: P2M/Sol/S_ModularCurve_single_div_one_sub_sq.lean
spec-pin: P2M/Sol/S_ModularCurve_single_sq_div_one_sub_cube.lean
spec-pin: P2M/Sol/S_ModularCurve_slotSubst_gen_injective.lean
spec-pin: P2M/Sol/S_ModularCurve_coeff_slotSubst_tateUnivX.lean
spec-pin: P2M/Sol/S_ModularCurve_coeff_slotSubst_tateUnivY.lean
spec-pin: P2M/Sol/S_ModularCurve_equation_tateBase_iff.lean
spec-pin: P2M/Sol/S_ModularCurve_toricPoint_fst_coeff_mul.lean
spec-pin: P2M/Sol/S_ModularCurve_toricPoint_fst_coeff_of_not_dvd.lean
spec-pin: P2M/Sol/S_ModularCurve_toricPoint_fst_coeff_zero.lean
spec-pin: P2M/Sol/S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.lean
spec-pin: P2M/Sol/S_ModularCurve_toricPoint_snd_coeff_of_not_dvd.lean
spec-pin: P2M/Sol/S_ModularCurve_toricPoint_snd_coeff_zero.lean
spec-pin: P2M/Sol/S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean
spec-pin: P2M/Sol/S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one.lean
-/
import FLTForHuman.ModularCurve.TateSlots.Convergence
import FLTForHuman.ModularCurve.TateSlots.SlotCoeff
import FLTForHuman.ModularCurve.Defs.Twist

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

/-! ### The unit twist on non-toric points

`qTwist ζ` rescales the coefficient of `q ^ n` by `ζ ^ n`. Pushed through the
slot substitution it acts on the slots: the twist of a non-toric point is the
non-toric point whose `c` is twisted to `c * ζ ^ j`. The facts below are the
pin's `S_`-file proof (`qTwist_ofPowerSeries`, `zeta_pow_*`, `val_*_pow_pow`,
`term_twist`, `head_twist`, `rescale_slotSubst_tateUniv{X,Y}`) read as
mathematics: they are this row's engine, so they stay `private` and the public
surface gains only the wrapper's statement. -/

private theorem qTwistFun_ofPowerSeries {K : Type*} [CommRing K] (u : Kˣ) (f : PowerSeries K) :
    qTwist u (HahnSeries.ofPowerSeries ℤ K f) =
      HahnSeries.ofPowerSeries ℤ K (PowerSeries.rescale (u : K) f) := by
  ext k
  rw [qTwist_coeff]
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_rescale, zpow_natCast, Units.val_pow_eq_pow_val]
  · have h0 : ∀ g : PowerSeries K, (HahnSeries.ofPowerSeries ℤ K g).coeff k = 0 := by
      intro g
      rw [HahnSeries.ofPowerSeries_apply]
      refine HahnSeries.embDomain_of_notMem_range ?_
      rintro ⟨n, hn⟩
      have hn' : (n : ℤ) = k := hn
      omega
    rw [h0, h0, mul_zero]

private theorem zeta_pow_of_eq {K : Type*} [CommRing K] {M : ℕ} (ζ : Kˣ) (hζ : ζ ^ M = 1)
    {n m t : ℕ} (h : n = M * m + t) : (ζ : K) ^ n = (ζ : K) ^ t := by
  have h' : ζ ^ n = ζ ^ t := by rw [h, pow_add, pow_mul, hζ, one_pow, one_mul]
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h']

private theorem zeta_pow_mul_of_add_eq {K : Type*} [CommRing K] {M : ℕ} (ζ : Kˣ)
    (hζ : ζ ^ M = 1) {n m t : ℕ} (h : n + t = M * m) : (ζ : K) ^ n * (ζ : K) ^ t = 1 := by
  have h' : ζ ^ n * ζ ^ t = 1 := by rw [← pow_add, h, pow_mul, hζ, one_pow]
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, h',
    Units.val_one]

private theorem val_mul_pow_pow {K : Type*} [CommRing K] (c ζ : Kˣ) (j e : ℕ) :
    ((c * ζ ^ j : Kˣ) : K) ^ e = (c : K) ^ e * (ζ : K) ^ (j * e) := by
  rw [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]

private theorem val_inv_mul_pow_pow {K : Type*} [CommRing K] (c ζ : Kˣ) (j e : ℕ) :
    (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e * (ζ : K) ^ (j * e) = ((c⁻¹ : Kˣ) : K) ^ e := by
  have h : ((c * ζ ^ j)⁻¹ : Kˣ) ^ e * ζ ^ (j * e) = c⁻¹ ^ e := by
    rw [mul_inv, mul_pow, inv_pow (ζ ^ j), ← pow_mul, mul_assoc, inv_mul_cancel, mul_one]
  have h' := congrArg Units.val h
  rwa [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val] at h'

/-- `ζ ^ n` distributes over the three indicators of a slot coefficient, using
`ζ ^ n = ζ ^ (j * e)` on the positive side and `ζ ^ n * ζ ^ (j * e) = 1` on the
inverse side. -/
private theorem term_twist {K : Type*} [CommRing K] (M : ℕ) (ζ : Kˣ) (hζ : ζ ^ M = 1) (c : Kˣ)
    (j n m e : ℕ) (α β γ : K) :
    (ζ : K) ^ n * (α * (if n = M * m + j * e then (c : K) ^ e else 0) +
        β * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) +
        γ * (if n = M * m then 1 else 0)) =
      α * (if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e else 0) +
        β * (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) +
        γ * (if n = M * m then 1 else 0) := by
  have S1 : (ζ : K) ^ n * (if n = M * m + j * e then (c : K) ^ e else 0) =
      (if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e else 0) := by
    by_cases h : n = M * m + j * e
    · rw [ite_eq_left h, ite_eq_left h, val_mul_pow_pow, zeta_pow_of_eq ζ hζ h]
      ring
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  have S2 : (ζ : K) ^ n * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) =
      (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) := by
    by_cases h : n + j * e = M * m
    · rw [ite_eq_left h, ite_eq_left h, ← val_inv_mul_pow_pow c ζ j e, ← mul_assoc,
        mul_comm ((ζ : K) ^ n), mul_assoc
      ]
      rw [zeta_pow_mul_of_add_eq ζ hζ h, mul_one]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  have S3 : (ζ : K) ^ n * (if n = M * m then (1 : K) else 0) =
      (if n = M * m then 1 else 0) := by
    by_cases h : n = M * m
    · rw [ite_eq_left h,
        zeta_pow_of_eq ζ hζ (t := 0) (m := m) (n := n) (by omega), pow_zero, mul_one]
    · rw [ite_eq_right h, mul_zero]
  calc (ζ : K) ^ n * (α * (if n = M * m + j * e then (c : K) ^ e else 0) +
        β * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) +
        γ * (if n = M * m then 1 else 0))
      = α * ((ζ : K) ^ n * (if n = M * m + j * e then (c : K) ^ e else 0)) +
        β * ((ζ : K) ^ n * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0)) +
        γ * ((ζ : K) ^ n * (if n = M * m then 1 else 0)) := by ring
    _ = _ := by rw [S1, S2, S3]

/-- The head term of a slot coefficient twists by `ζ ^ (j * (n / j)) = ζ ^ n`. -/
private theorem head_twist {K : Type*} [CommRing K] (ζ c : Kˣ) (j n : ℕ) (hj : 0 < j)
    (δ : ℕ → K) :
    (ζ : K) ^ n * (if j ∣ n then δ (n / j) * (c : K) ^ (n / j) else 0) =
      (if j ∣ n then δ (n / j) * ((c * ζ ^ j : Kˣ) : K) ^ (n / j) else 0) := by
  split_ifs with hjn
  · obtain ⟨d, rfl⟩ := hjn
    rw [Nat.mul_div_cancel_left d hj, val_mul_pow_pow]
    ring
  · rw [mul_zero]

private theorem rescale_slotSubst_tateUnivX {K : Type*} [CommRing K] (M : ℕ) (ζ : Kˣ)
    (hζ : ζ ^ M = 1) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    PowerSeries.rescale (ζ : K) (slotSubst K M c j tateUnivX) =
      slotSubst K M (c * ζ ^ j) j tateUnivX := by
  ext n
  rw [PowerSeries.coeff_rescale, coeff_slotSubst_tateUnivX M c j hj hjM n,
    coeff_slotSubst_tateUnivX M (c * ζ ^ j) j hj hjM n, mul_add, Finset.mul_sum]
  congr 1
  · exact head_twist ζ c j n hj fun d => (d : K)
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have htw := term_twist M ζ hζ c j n m e (e : K) (e : K) (-(2 * (e : K)))
    have hl : (e : K) * ((if n = M * m + j * e then (c : K) ^ e else 0) +
        (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) -
        (if n = M * m then 2 else 0)) =
        (e : K) * (if n = M * m + j * e then (c : K) ^ e else 0) +
        (e : K) * (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) +
        (-(2 * (e : K))) * (if n = M * m then 1 else 0) := by
      split_ifs <;> ring
    have hr : (e : K) * ((if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e else 0) +
        (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) -
        (if n = M * m then 2 else 0)) =
        (e : K) * (if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e else 0) +
        (e : K) * (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) +
        (-(2 * (e : K))) * (if n = M * m then 1 else 0) := by
      split_ifs <;> ring
    rw [hl, hr, htw]

private theorem rescale_slotSubst_tateUnivY {K : Type*} [CommRing K] (M : ℕ) (ζ : Kˣ)
    (hζ : ζ ^ M = 1) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    PowerSeries.rescale (ζ : K) (slotSubst K M c j tateUnivY) =
      slotSubst K M (c * ζ ^ j) j tateUnivY := by
  ext n
  rw [PowerSeries.coeff_rescale, coeff_slotSubst_tateUnivY M c j hj hjM n,
    coeff_slotSubst_tateUnivY M (c * ζ ^ j) j hj hjM n, mul_add, Finset.mul_sum]
  congr 1
  · exact head_twist ζ c j n hj fun d => ((d.choose 2 : ℕ) : K)
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have htw := term_twist M ζ hζ c j n m e (((e.choose 2 : ℕ)) : K)
      (-((((e + 1).choose 2 : ℕ)) : K)) (e : K)
    have hl : ((if n = M * m + j * e then (((e.choose 2 : ℕ)) : K) * (c : K) ^ e else 0) -
        (if n + j * e = M * m then ((((e + 1).choose 2 : ℕ)) : K) * ((c⁻¹ : Kˣ) : K) ^ e
          else 0) +
        (if n = M * m then (e : K) else 0)) =
        (((e.choose 2 : ℕ)) : K) * (if n = M * m + j * e then (c : K) ^ e else 0) +
        (-((((e + 1).choose 2 : ℕ)) : K)) *
          (if n + j * e = M * m then ((c⁻¹ : Kˣ) : K) ^ e else 0) +
        (e : K) * (if n = M * m then 1 else 0) := by
      split_ifs <;> ring
    have hr : ((if n = M * m + j * e then
          (((e.choose 2 : ℕ)) : K) * ((c * ζ ^ j : Kˣ) : K) ^ e else 0) -
        (if n + j * e = M * m then
          ((((e + 1).choose 2 : ℕ)) : K) * (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) +
        (if n = M * m then (e : K) else 0)) =
        (((e.choose 2 : ℕ)) : K) * (if n = M * m + j * e then ((c * ζ ^ j : Kˣ) : K) ^ e
          else 0) +
        (-((((e + 1).choose 2 : ℕ)) : K)) *
          (if n + j * e = M * m then (((c * ζ ^ j)⁻¹ : Kˣ) : K) ^ e else 0) +
        (e : K) * (if n = M * m then 1 else 0) := by
      split_ifs <;> ring
    rw [hl, hr, htw]

universe u in
-- pin: qTwist_nonToricPoint_of_pow_eq_one (Theorems/Thm_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one.lean)
theorem qTwist_nonToricPoint_of_pow_eq_one (K : Type u) [CommRing K] (M : ℕ) [NeZero M] (ζ : Kˣ)
    (hζ : ζ ^ M = 1) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    (qTwist ζ (nonToricPoint K M c j).1, qTwist ζ (nonToricPoint K M c j).2) =
      nonToricPoint K M (c * ζ ^ j) j := by
  rw [nonToricPoint, nonToricPoint, Prod.mk.injEq]
  dsimp only
  constructor
  · rw [qTwistFun_ofPowerSeries, rescale_slotSubst_tateUnivX M ζ hζ c j hj hjM]
  · rw [qTwistFun_ofPowerSeries, rescale_slotSubst_tateUnivY M ζ hζ c j hj hjM]

end ModularCurve

end
