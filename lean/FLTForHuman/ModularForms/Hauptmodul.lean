/-
  T7 — the Hauptmodul form of R1: a pole-bounded, realized, `SL₂(ℤ)`-invariant
  Laurent series is a polynomial in `jq`.

  This completes R1 (the level-one q-expansion principle). It combines the two
  earlier topics: T5's kernel `coeff_eq_zero_of_hasSum_of_slash_invariant` is
  applied to the holomorphic remainder, and T6's
  `hasSum_jq_qParam`/`E4_cube_div_discriminant_smul` realize the polynomials in
  `jq` used to kill the pole. The headline is stated verbatim from its `Theorems/`
  wrapper.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:

  - `P2M/Sol/S_ModularCurve_hasSum_qParam_mul.lean` (80) — products of
    power-series `q`-expansions on `ℍ` (the Cauchy product);
  - `P2M/Sol/S_ModularCurve_hasSum_qParam_mul_laurent.lean` (84) — the Laurent
    case, via `single_mul`, the order split and `powerSeriesPart`;
  - `P2M/Sol/S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean` (84) —
    pole killing: the triangularity of `j`'s powers;
  - `P2M/Sol/S_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean`
    (214) — `RealL`, its closure, `realL_aeval_jq`, and the headline.

  ## The mathlib-first audit: this is the glue topic

  Unlike T5 and T6 there is almost nothing for mathlib to replace. The audit
  found **no** public mathlib statement for `RealL` or its closure (mathlib has
  `UpperHalfPlane.cuspFunction_mul` for the *cusp function*, not the pointwise
  `HasSum` predicate), for `coeff_prod_X_sub_C`, for `realL_aeval_jq`, for the
  pole-killing lemma, or for the headline. What mathlib supplies is the
  Cauchy-product **core** inside `hasSum_qParam_mul` (the
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` /
  `summable_norm_sum_mul_antidiagonal_of_summable_norm` pair), the
  `HahnSeries`/`PowerSeries` order-and-coefficient API used by the Laurent and
  pole-killing blocks, `Periodic.norm_qParam_lt_one`, and — through T5/T6 — the
  kernel and the `jq` realization. Everything else is ported.

  So the audit's value here is negative information: do not hunt for mathlib
  analogues, budget the port as a port. The prediction was 1:1 against the
  ~462-line pin.

  ## The exported API

  FLT *duplicates* the `RealL` block: the same predicate and closure are defined
  again in T8's pin file,
  `S_ModularCurve_PhiGen_PhiGenDescends_hasSum_cosetPoly_coeff.lean`. The port
  defines it once, here, and exports it — `RealL` with its closure and the two
  `hasSum_qParam_mul{,_laurent}` lemmas are the interface T8 imports rather than
  copies (porting-playbook.md §2, "deduplicate at the source"). Everything else
  in this module — the pole-killing block, `realL_aeval_jq`, the `jt`/`jqC` glue,
  and `mem_adjoin_jq_of_realL_invariant` — is private.

  ## Assumptions

  `HasSum`, `PowerSeries`, `HahnSeries`, `LaurentSeries`, `Polynomial` and
  `Periodic.norm_qParam_lt_one` are mathlib's; `jq`, `coeff_jq_pow_self`,
  `coeff_jq_pow_of_lt`, `PoleOrderLE`, `coeffMap`, `algebraMap_apply_eq_single`
  and `algebraMap_laurentSeries_eq_single` are the port's (`Defs/`). The kernel
  is T5's (`QExpansionPrinciple.lean`); the `jq` realization is T6's
  (`JqAnalyticModel.lean`). Names are FLT's verbatim.

  T9 promoted this module's two private triangularity lemmas — `coeff_aeval_jq_neg`
  and `poleOrderLE_aeval_jq` — to `Defs/Jq.lean` and `Defs/PhiGen.lean`
  respectively (they were unused here), so the cone's remaining topics no longer
  repeat FLT's nine private copies.
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.RingTheory.LaurentSeries
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularForms.QExpansionPrinciple
import FLTForHuman.ModularForms.JqAnalyticModel

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups

local notation "𝕢" => Function.Periodic.qParam

namespace ModularCurve

/-! ## Products of `q`-expansions on `ℍ`

The Cauchy-product core is mathlib's; the wrapper turns a `HasSum` on `ℍ` into
absolute summability at a point of the disc. -/

/-- Absolute summability at a point of the disc, from a `HasSum` on `ℍ`: the
comparison radius `r` with `‖q‖ < r < 1` is reached by a point of `ℍ`. -/
private theorem summable_norm_of_hasSum_qParam {h : ℝ} (hh : 0 < h) {a : ℕ → ℂ} {F : ℍ → ℂ}
    (hA : ∀ τ : ℍ, HasSum (fun m : ℕ => a m * 𝕢 h (τ : ℂ) ^ m) (F τ)) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ => ‖a m * q ^ m‖) := by
  obtain ⟨r, hqr, hr1⟩ := exists_between hq
  have hr0 : 0 < r := (norm_nonneg q).trans_lt hqr
  have hr1' : ‖(r : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have hrne : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0.ne'
  let τ' : ℍ := ⟨Periodic.invQParam h r, Periodic.im_invQParam_pos_of_norm_lt_one hh hr1' hrne⟩
  have hq' : 𝕢 h (τ' : ℂ) = r := Periodic.qParam_right_inv hh.ne' hrne
  have hs : Summable (fun m : ℕ => a m * (r : ℂ) ^ m) := by
    have := (hA τ').summable
    rwa [hq'] at this
  have hev : ∀ᶠ m : ℕ in cofinite, ‖a m * (r : ℂ) ^ m‖ < 1 :=
    NormedAddGroup.tendsto_nhds_zero.mp hs.tendsto_cofinite_zero 1 one_pos
  refine Summable.of_norm_bounded_eventually (g := fun m : ℕ => (‖q‖ / r) ^ m)
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hr0).mpr hqr)) ?_
  filter_upwards [hev] with m hm
  rw [norm_norm, norm_mul, norm_pow, div_pow, le_div_iff₀ (pow_pos hr0 m)]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr0.le] at hm
  calc ‖a m‖ * ‖q‖ ^ m * r ^ m = (‖a m‖ * r ^ m) * ‖q‖ ^ m := by ring
    _ ≤ 1 * ‖q‖ ^ m := by gcongr
    _ = ‖q‖ ^ m := one_mul _

/-- The Cauchy product of two `q`-expansions on `ℍ` (power-series case), stated
verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_hasSum_qParam_mul.lean`. -/
theorem hasSum_qParam_mul (h : ℝ) (hh : 0 < h) (A B : PowerSeries ℂ)
    (F G : UpperHalfPlane → ℂ)
    (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ =>
      PowerSeries.coeff m A * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ))
    (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ =>
      PowerSeries.coeff m B * Function.Periodic.qParam h (τ : ℂ) ^ m) (G τ))
    (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => PowerSeries.coeff m (A * B) * Function.Periodic.qParam h (τ : ℂ) ^ m)
      (F τ * G τ) := by
  set q : ℂ := 𝕢 h (τ : ℂ) with hqdef
  have hq : ‖q‖ < 1 := Periodic.norm_qParam_lt_one hh τ.im_pos
  have hsA := summable_norm_of_hasSum_qParam hh hA hq
  have hsB := summable_norm_of_hasSum_qParam hh hB hq
  have key := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsA hsB
  have hsum : Summable (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff kl.1 A * q ^ kl.1) * (PowerSeries.coeff kl.2 B * q ^ kl.2)) :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hsA hsB).of_norm
  have H : HasSum (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      (PowerSeries.coeff kl.1 A * q ^ kl.1) * (PowerSeries.coeff kl.2 B * q ^ kl.2)) (F τ * G τ) := by
    rw [← (hA τ).tsum_eq, ← (hB τ).tsum_eq, ← hqdef, key]
    exact hsum.hasSum
  have hfg : (fun m : ℕ => PowerSeries.coeff m (A * B) * q ^ m) =
      (fun n : ℕ => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
        (PowerSeries.coeff kl.1 A * q ^ kl.1) * (PowerSeries.coeff kl.2 B * q ^ kl.2)) := by
    funext n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
    rw [← hkl, pow_add]
    ring
  rw [hfg]
  exact H

/-! ## The Laurent case

`hasSum_single_mul_coe_iff` moves a power-series `HasSum` to the shifted Laurent
`HasSum`, and `powerSeriesPart`/`order` reduce the Laurent product to the
power-series one. -/

private theorem hasSum_single_mul_coe_iff (k : ℤ) (P : PowerSeries ℂ) {q : ℂ} (hq : q ≠ 0)
    (t : ℂ) :
    HasSum (fun m : ℤ => (HahnSeries.single k (1 : ℂ) * (P : LaurentSeries ℂ)).coeff m * q ^ m)
        (t * q ^ k) ↔
      HasSum (fun n : ℕ => PowerSeries.coeff n P * q ^ n) t := by
  have hinj : Function.Injective (fun n : ℕ => (n : ℤ) + k) := fun a b hab => by simpa using hab
  rw [← hinj.hasSum_iff]
  · have hfg : (fun m : ℤ =>
        (HahnSeries.single k (1 : ℂ) * (P : LaurentSeries ℂ)).coeff m * q ^ m) ∘
        (fun n : ℕ => (n : ℤ) + k) = fun n : ℕ => (PowerSeries.coeff n P * q ^ n) * q ^ k := by
      funext n
      simp only [Function.comp_apply]
      rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.coeff_coe_powerSeries, zpow_add₀ hq,
        zpow_natCast]
      ring
    rw [hfg]
    exact hasSum_mul_right_iff (zpow_ne_zero k hq)
  · intro m hm
    have hmk : m - k < 0 := by
      by_contra hge
      push Not at hge
      exact hm ⟨(m - k).toNat, by simp only; omega⟩
    rw [← sub_add_cancel m k, HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe,
      ite_eq_left hmk, zero_mul]

/-- The Cauchy product of two Laurent `q`-expansions on `ℍ`, stated verbatim from
the pin wrapper `Theorems/Thm_ModularCurve_hasSum_qParam_mul_laurent.lean`. -/
theorem hasSum_qParam_mul_laurent (h : ℝ) (hh : 0 < h) (A B : LaurentSeries ℂ)
    (F G : UpperHalfPlane → ℂ)
    (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ =>
      A.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ))
    (hB : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ =>
      B.coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m) (G τ)) (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => (A * B).coeff m * Function.Periodic.qParam h (τ : ℂ) ^ m)
      (F τ * G τ) := by
  have hq0 : ∀ τ : ℍ, 𝕢 h (τ : ℂ) ≠ 0 := fun τ => Periodic.qParam_ne_zero _
  set F' : ℍ → ℂ := fun τ => F τ * (𝕢 h (τ : ℂ) ^ A.order)⁻¹ with hF'
  set G' : ℍ → ℂ := fun τ => G τ * (𝕢 h (τ : ℂ) ^ B.order)⁻¹ with hG'
  have hA' : ∀ τ : ℍ, HasSum (fun n : ℕ => PowerSeries.coeff n A.powerSeriesPart * 𝕢 h (τ : ℂ) ^ n)
      (F' τ) := by
    intro τ
    rw [← hasSum_single_mul_coe_iff A.order A.powerSeriesPart (hq0 τ), A.single_order_mul_powerSeriesPart,
      hF', inv_mul_cancel_right₀ (zpow_ne_zero _ (hq0 τ))]
    exact hA τ
  have hB' : ∀ τ : ℍ, HasSum (fun n : ℕ => PowerSeries.coeff n B.powerSeriesPart * 𝕢 h (τ : ℂ) ^ n)
      (G' τ) := by
    intro τ
    rw [← hasSum_single_mul_coe_iff B.order B.powerSeriesPart (hq0 τ), B.single_order_mul_powerSeriesPart,
      hG', inv_mul_cancel_right₀ (zpow_ne_zero _ (hq0 τ))]
    exact hB τ
  have H := hasSum_qParam_mul h hh A.powerSeriesPart B.powerSeriesPart F' G' hA' hB' τ
  have hAB : HahnSeries.single (A.order + B.order) (1 : ℂ) *
      ((A.powerSeriesPart * B.powerSeriesPart : PowerSeries ℂ) : LaurentSeries ℂ) = A * B := by
    conv_rhs => rw [← A.single_order_mul_powerSeriesPart, ← B.single_order_mul_powerSeriesPart]
    rw [PowerSeries.coe_mul, ← one_mul (1 : ℂ), ← HahnSeries.single_mul_single, one_mul]
    ring
  have hFG : F τ * G τ = F' τ * G' τ * 𝕢 h (τ : ℂ) ^ (A.order + B.order) := by
    have hqτ := hq0 τ
    simp only [hF', hG']
    rw [zpow_add₀ hqτ]
    field_simp
  rw [← hAB, hFG]
  exact (hasSum_single_mul_coe_iff _ _ (hq0 τ) _).mpr H

/-! ## `RealL`: realization of a Laurent series by a function on `ℍ`

The T8 interface. FLT duplicates this block in its T8 file; the port keeps one
copy, public, here. -/

/-- `A` is realized by `F` on `ℍ` at period `h`: for every `τ`, the Laurent
series `∑ A.coeff m · q(τ)^m` converges to `F τ`. The general period `h` is
needed by T8's Hecke translates; the headline uses `h = 1`. -/
def RealL (h : ℝ) (A : LaurentSeries ℂ) (F : ℍ → ℂ) : Prop :=
  ∀ τ : ℍ, HasSum (fun m : ℤ => A.coeff m * 𝕢 h (τ : ℂ) ^ m) (F τ)

namespace RealL

variable {h : ℝ} {A B : LaurentSeries ℂ} {F G : ℍ → ℂ}

lemma add (hA : RealL h A F) (hB : RealL h B G) : RealL h (A + B) (F + G) := fun τ => by
  simpa [add_mul] using (hA τ).add (hB τ)

lemma neg (hA : RealL h A F) : RealL h (-A) (-F) := fun τ => by
  simpa [neg_mul] using (hA τ).neg

lemma sub (hA : RealL h A F) (hB : RealL h B G) : RealL h (A - B) (F - G) := fun τ => by
  simpa [sub_mul] using (hA τ).sub (hB τ)

lemma mul (hh : 0 < h) (hA : RealL h A F) (hB : RealL h B G) : RealL h (A * B) (F * G) := fun τ =>
  hasSum_qParam_mul_laurent h hh A B F G hA hB τ

lemma single (h : ℝ) (a : ℂ) (n : ℤ) :
    RealL h (HahnSeries.single n a) (fun τ => a * 𝕢 h (τ : ℂ) ^ n) := fun τ => by
  refine (hasSum_ite_eq n (a * 𝕢 h (τ : ℂ) ^ n)).congr_fun fun m => ?_
  by_cases hm : m = n
  · subst hm; simp
  · simp [HahnSeries.coeff_single_of_ne hm, hm]

lemma C (h : ℝ) (a : ℂ) : RealL h (HahnSeries.C a) (fun _ => a) := by
  simpa using single h a 0

lemma one (h : ℝ) : RealL h 1 1 := by
  have h__af := C h 1
  simp at h__af
  exact h__af

lemma zero (h : ℝ) : RealL h 0 0 := fun τ => by simp [hasSum_zero]

lemma congr {A' : LaurentSeries ℂ} {F' : ℍ → ℂ} (hA : RealL h A F) (h1 : A = A')
    (h2 : ∀ τ, F τ = F' τ) : RealL h A' F' := fun τ => by rw [← h1, ← h2]; exact hA τ

lemma prod (hh : 0 < h) {ι : Type} (s : Finset ι) {A : ι → LaurentSeries ℂ} {F : ι → ℍ → ℂ}
    (hAF : ∀ i ∈ s, RealL h (A i) (F i)) : RealL h (∏ i ∈ s, A i) (fun τ => ∏ i ∈ s, F i τ) := by
  classical
  induction s using Finset.induction_on with
  | empty => (have h__af := one h; simp at h__af ⊢; exact h__af)
  | insert a s ha ih =>
    have h1 := (hAF a (Finset.mem_insert_self a s)).mul hh
      (ih fun i hi => hAF i (Finset.mem_insert_of_mem hi))
    refine h1.congr (Finset.prod_insert ha).symm fun τ => ?_
    simp [Finset.prod_insert ha]

lemma coeff_prod_X_sub_C (hh : 0 < h) {ι : Type} (s : Finset ι) {a : ι → LaurentSeries ℂ}
    {α : ι → ℍ → ℂ} (haα : ∀ i ∈ s, RealL h (a i) (α i)) (k : ℕ) :
    RealL h ((∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))).coeff k)
      (fun τ => (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))).coeff k) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Polynomial.coeff_one]
    by_cases hk : k = 0
    · subst hk; (have h__af := one h; simp at h__af ⊢; exact h__af)
    · have h__af := zero h
      simp [hk] at h__af ⊢
      exact h__af
  | insert b s hb ih =>
    have ih' := fun k => ih (fun i hi => haα i (Finset.mem_insert_of_mem hi)) k
    have hb' := haα b (Finset.mem_insert_self b s)
    have hA : (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (a i))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i))) * (Polynomial.X - Polynomial.C (a b)) :=
      (Finset.prod_insert hb).trans (mul_comm (G := Polynomial (LaurentSeries ℂ)) _ _)
    have hfun : ∀ τ : ℍ, (∏ i ∈ insert b s, (Polynomial.X - Polynomial.C (α i τ))) =
        (∏ i ∈ s, (Polynomial.X - Polynomial.C (α i τ))) * (Polynomial.X - Polynomial.C (α b τ)) :=
      fun τ => (Finset.prod_insert hb).trans (mul_comm (G := Polynomial ℂ) _ _)
    cases k with
    | zero =>
      refine ((ih' 0).mul hh hb').neg.congr ?_ fun τ => ?_
      · rw [hA, Polynomial.mul_coeff_zero, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
          Polynomial.coeff_C_zero, zero_sub]
        exact (mul_neg (α := LaurentSeries ℂ) _ _).symm
      · simp only [hfun τ, Polynomial.mul_coeff_zero, Pi.neg_apply, Pi.mul_apply, Polynomial.coeff_sub,
          Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
    | succ k =>
      refine ((ih' k).sub ((ih' (k + 1)).mul hh hb')).congr ?_ fun τ => ?_
      · rw [hA, Polynomial.coeff_mul_X_sub_C]
      · simp only [hfun τ, Polynomial.coeff_mul_X_sub_C, Pi.sub_apply, Pi.mul_apply]

end RealL

/-! ## Pole killing (private)

The triangularity of `j`'s powers: `jq = q⁻¹(1 + ⋯)`, so subtracting a suitable
multiple of `jq^(n+1)` kills the `q^{-(n+1)}` coefficient without disturbing
higher exponents. -/

private theorem poleOrderLE_iff_le_order {f : LaurentSeries ℚ} (hf : f ≠ 0) {n : ℕ} :
    PoleOrderLE f n ↔ -(n : ℤ) ≤ f.order :=
  (HahnSeries.le_order_iff_forall hf).symm

private theorem exists_poleOrderLE (f : LaurentSeries ℚ) : ∃ n : ℕ, PoleOrderLE f n :=
  ⟨(-f.order).toNat, fun _ hk => HahnSeries.coeff_eq_zero_of_lt_order (by omega)⟩

private theorem poleOrderLE_sub_aeval_jq_succ {f : LaurentSeries ℚ} {n : ℕ}
    (hf : PoleOrderLE f (n + 1)) :
    PoleOrderLE
      (f - Polynomial.aeval jq
        (Polynomial.C (f.coeff (-(n + 1 : ℕ) : ℤ)) * Polynomial.X ^ (n + 1))) n := by
  intro k hk
  rw [HahnSeries.coeff_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
    algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul]
  rcases (show k ≤ -((n + 1 : ℕ) : ℤ) by omega).eq_or_lt with heq | hlt
  · rw [heq, coeff_jq_pow_self, mul_one, sub_self]
  · rw [hf k hlt, coeff_jq_pow_of_lt hlt, mul_zero, sub_zero]

private theorem exists_aeval_jq_sub_holomorphicAtInfty (n : ℕ) :
    ∀ f : LaurentSeries ℚ, PoleOrderLE f n →
      ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ PoleOrderLE (f - Polynomial.aeval jq P) 0 := by
  induction n with
  | zero =>
    intro f hf
    exact ⟨0, by simp, by simpa using hf⟩
  | succ n ih =>
    intro f hf
    obtain ⟨Q, hQdeg, hQ⟩ := ih _ (poleOrderLE_sub_aeval_jq_succ hf)
    refine ⟨Polynomial.C (f.coeff (-(n + 1 : ℕ) : ℤ)) * Polynomial.X ^ (n + 1) + Q, ?_, ?_⟩
    · refine le_trans (Polynomial.natDegree_add_le _ _)
        (max_le (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_)
      omega
    · intro k hk
      rw [map_add, sub_add_eq_sub_sub]
      exact hQ k hk

/-! ## The `jq` realization glue (private) -/

private def jt (τ : ℍ) : ℂ := ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

private abbrev castC : ℚ →+* ℂ := Rat.castHom ℂ

private def jqC : LaurentSeries ℂ := coeffMap castC jq

private lemma jqC_coeff (m : ℤ) : jqC.coeff m = ((jq.coeff m : ℚ) : ℂ) := rfl

private lemma realL_jqC : RealL 1 jqC jt := fun τ => hasSum_jq_qParam τ

private lemma jt_smul (γ : SL(2, ℤ)) (τ : ℍ) : jt (γ • τ) = jt τ :=
  E4_cube_div_discriminant_smul γ τ

private lemma realL_aeval_jq (P : Polynomial ℚ) :
    RealL 1 (coeffMap castC (Polynomial.aeval jq P)) (fun τ => (P.map castC).eval (jt τ)) := by
  induction P using Polynomial.induction_on with
  | C a =>
    refine (RealL.C 1 (a : ℂ)).congr ?_ fun τ => ?_
    · rw [Polynomial.aeval_C, algebraMap_laurentSeries_eq_single, coeffMap_single]
      rfl
    · simp
  | add P Q hP hQ =>
    refine (hP.add hQ).congr ?_ fun τ => ?_
    · rw [map_add, map_add]
    · simp
  | monomial n a ih =>
    refine (ih.mul one_pos realL_jqC).congr ?_ fun τ => ?_
    · rw [jqC, ← map_mul]
      congr 1
      symm
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    · simp [pow_succ, mul_assoc]

/-! ## The Hauptmodul form -/

private theorem mem_adjoin_jq_of_realL_invariant (f : LaurentSeries ℚ) (F : ℍ → ℂ)
    (hF : ∀ τ : ℍ, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ), F (γ • τ) = F τ) : f ∈ Algebra.adjoin ℚ {jq} := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, PoleOrderLE f n := by
    by_cases hf0 : f = 0
    · exact ⟨0, fun m _ => by simp [hf0]⟩
    refine ⟨(-f.order).toNat, fun m hm => HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hm ?_)⟩
    have := Int.self_le_toNat (-f.order)
    omega
  obtain ⟨P, -, he⟩ := exists_aeval_jq_sub_holomorphicAtInfty n f hn
  set e : LaurentSeries ℚ := f - Polynomial.aeval jq P with he_def
  have he0 : ∀ m : ℤ, m < 0 → e.coeff m = 0 := fun m hm => he m (by simpa using hm)
  have hfR : RealL 1 (coeffMap castC f) F := hF
  have hE : RealL 1 (coeffMap castC e) (F - fun τ => (P.map castC).eval (jt τ)) := by
    rw [he_def, map_sub]
    exact hfR.sub (realL_aeval_jq P)
  have hEinv : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
      (F - fun τ => (P.map castC).eval (jt τ)) (γ • τ) =
        (F - fun τ => (P.map castC).eval (jt τ)) τ := by
    intro γ τ
    simp only [Pi.sub_apply, hinv γ τ, jt_smul γ τ]
  have hEN : ∀ τ : ℍ, HasSum (fun n : ℕ => ((e.coeff n : ℚ) : ℂ) * 𝕢 1 (τ : ℂ) ^ n)
      ((F - fun τ => (P.map castC).eval (jt τ)) τ) := by
    intro τ
    have h := hE τ
    rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff] at h
    · exact h
    · intro m hm
      have hm' : m < 0 := by
        by_contra hge
        push Not at hge
        exact hm ⟨m.toNat, Int.toNat_of_nonneg hge⟩
      rw [coeffMap_coeff, he0 m hm', map_zero, zero_mul]
  have hvan : ∀ n : ℕ, n ≠ 0 → e.coeff n = 0 := fun n hn => by
    have := coeff_eq_zero_of_hasSum_of_slash_invariant hEN hEinv hn
    exact_mod_cast this
  have heconst : e = HahnSeries.single 0 (e.coeff 0) := by
    ext m
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · rw [he0 m hm, HahnSeries.coeff_single_of_ne hm.ne]
    · rw [HahnSeries.coeff_single_same]
    · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm.le
      rw [HahnSeries.coeff_single_of_ne (by exact_mod_cast hm.ne')]
      exact hvan n (by exact_mod_cast hm.ne')
  have hck : f = algebraMap ℚ (LaurentSeries ℚ) (e.coeff 0) + Polynomial.aeval jq P := by
    rw [algebraMap_laurentSeries_eq_single, ← heconst, he_def, sub_add_cancel]
  rw [hck]
  exact Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Polynomial.aeval_mem_adjoin_singleton ℚ jq)

/-- R1 in Hauptmodul form: a Laurent series realized by an `SL₂(ℤ)`-invariant
`F : ℍ → ℂ` lies in `ℚ[jq]`. This is the completion of R1 and the form the
Φ_p splitting cone consumes.

Stated verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_mem_adjoin_jq_of_hasSum_of_slash_invariant.lean`. -/
theorem mem_adjoin_jq_of_hasSum_of_slash_invariant (f : LaurentSeries ℚ)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => ((f.coeff m : ℚ) : ℂ) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ))
    (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ) :
    f ∈ Algebra.adjoin ℚ {jq} :=
  mem_adjoin_jq_of_realL_invariant f F hF hinv

end ModularCurve

end
