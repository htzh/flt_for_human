/-
  T12 — the coefficients of `jq` are positive.

  `one_le_coeff_jq : ∀ n, (1 : ℚ) ≤ jq.coeff (n : ℤ)` — every regular coefficient
  of `j = q⁻¹ + 744 + 196884 q + ⋯` is at least `1`. The route is the eta product,
  not analysis: `jq = q⁻¹ · jNum` with `jNum = E₄³ · Δ⁻¹`, `E₄³` has nonnegative
  coefficients and constant term `1`, and `Δ⁻¹ = ∏ (1 - q^d)^{-24}` has all
  coefficients `≥ 1` (the coefficient of `q^n` counts `24`-coloured partitions of
  `n`, and the all-`1`s partition contributes `1`). Multiplying a series with
  constant term `1` and nonnegative coefficients by one with all coefficients
  `≥ 1` keeps all coefficients `≥ 1` (the `(0, n)` term of the Cauchy sum).

  This is the coefficient positivity the 895 block threads as `hpos`; its
  consumers use it only at `n = ℓ`, but the exported statement is for all `n`.

  ## The mathlib substitution (work order §3.1.9)

  FLT's 386 lines hand-build the truncation machinery. Two pieces are replaced by
  public mathlib `v4.34.0` lemmas:

  * `PowerSeries.coeff_mul_prod_one_sub_of_lt_order` gives the finite eta product's
    low coefficients in one step, replacing the pin's 40-line induction
    `coeff_prod_one_sub_X_pow_eq_coeff_one`;
  * `PowerSeries.expand` + `PowerSeries.mk_one_mul_one_sub_eq_one` invert
    `1 - q ^ d` in one step, replacing the pin's 45-line `geomSeries` block.

  The eta-truncation comparison `coeff_etaProd_eq_coeff_partialProd` (the pin's
  `Tendsto`-to-a-discrete-limit argument) and the truncation-stable inverse
  comparison `coeff_inv_congr` have no mathlib replacement and are ported. The
  measured outcome is in the log §12.3.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_one_le_coeff_jq.lean` (386 lines). The public statement
  is verbatim from `Theorems/Thm_ModularCurve_one_le_coeff_jq.lean`; the one-line
  `coeff_jq_ne_zero` is the pin's own public corollary.

  ## Assumptions

  `eisenstein4`, `etaProd`, `dedekindEtaUnit{,_inv}`, `jNum`, `jNumQ`, `jq` are the
  port's `Defs/Jq`; `PowerSeries`/`Finset` and the order/expand lemmas are
  mathlib's.
-/
import FLTForHuman.ModularCurve.Defs.Jq
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open PowerSeries Finset

namespace ModularCurve

/-! ## The finite eta product -/

/-- The low coefficients of a finite product `∏ (1 - q ^ (e i))` in which every
`e i > n`: it is `1` at `0` and vanishes below `n`. Mathlib's
`coeff_mul_prod_one_sub_of_lt_order` supplies the whole computation (the pin proves
it by a 40-line induction). -/
private theorem coeff_prod_one_sub_X_pow_eq_coeff_one {R : Type*} [CommRing R] [Nontrivial R]
    {ι : Type*} {n : ℕ} (s : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ s, n < e i) :
    ∀ m ≤ n, PowerSeries.coeff m (∏ i ∈ s, ((1 : PowerSeries R) - X ^ e i)) =
      if m = 0 then 1 else 0 := by
  intro m hm
  have h := PowerSeries.coeff_mul_prod_one_sub_of_lt_order m s (1 : PowerSeries R)
    (fun i => X ^ e i) (fun i hi => by
      rw [PowerSeries.order_X_pow]
      exact_mod_cast lt_of_le_of_lt hm (he i hi))
  simpa only [one_mul, PowerSeries.coeff_one] using h

/-- The `n`-th coefficient of `∏_{i < k+1} (1 - q ^ (i+1))` is independent of `k`
once `n ≤ k`. -/
private theorem coeff_prod_one_sub_pow_le {R : Type*} [CommRing R] [Nontrivial R]
    (k n : ℕ) (h : n ≤ k) :
    PowerSeries.coeff n
        (∏ i ∈ Finset.range (k + 1), ((1 : PowerSeries R) - X ^ (i + 1))) =
      PowerSeries.coeff n
        (∏ i ∈ Finset.range (n + 1), ((1 : PowerSeries R) - X ^ (i + 1))) := by
  classical
  have hsplit :
      (∏ i ∈ Finset.range (k + 1), ((1 : PowerSeries R) - X ^ (i + 1))) =
        (∏ i ∈ Finset.range (n + 1), ((1 : PowerSeries R) - X ^ (i + 1))) *
          ∏ i ∈ Finset.Ico (n + 1) (k + 1), ((1 : PowerSeries R) - X ^ (i + 1)) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.prod_Ico_consecutive _ (Nat.zero_le _) (Nat.succ_le_succ h)]
  rw [hsplit, PowerSeries.coeff_mul]
  have htail : ∀ m ≤ n,
      PowerSeries.coeff m
          (∏ i ∈ Finset.Ico (n + 1) (k + 1), ((1 : PowerSeries R) - X ^ (i + 1))) =
        if m = 0 then 1 else 0 := by
    refine coeff_prod_one_sub_X_pow_eq_coeff_one _ _ ?_
    intro i hi
    have : n + 1 ≤ i := (Finset.mem_Ico.mp hi).1
    omega
  rw [Finset.sum_eq_single_of_mem (n, 0) (by simp)]
  · rw [htail 0 (Nat.zero_le n), ite_eq_left rfl, mul_one]
  · rintro ⟨b₁, b₂⟩ hb hne
    have hb' : b₁ + b₂ = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hb₂ : b₂ ≤ n := Finset.HasAntidiagonal.antidiagonal.snd_le hb
    have : b₂ ≠ 0 := by
      rintro rfl
      exact hne (by simp [← hb'])
    rw [htail b₂ hb₂, ite_eq_right this, mul_zero]

/-- `etaProd`'s `n`-th coefficient is that of the finite product through `n + 1`:
the topological product's coefficient is eventually stable (the pin's
`Tendsto`-to-a-discrete-limit argument; no mathlib replacement). -/
private theorem coeff_etaProd_eq_coeff_partialProd (n : ℕ) :
    PowerSeries.coeff n etaProd =
      PowerSeries.coeff n
        (∏ i ∈ Finset.range (n + 1), (1 - X ^ (i + 1) : PowerSeries ℤ)) := by
  classical
  have hconv : Filter.Tendsto
      (fun s : Finset ℕ =>
        PowerSeries.coeff n (∏ i ∈ s, (1 - X ^ (i + 1) : PowerSeries ℤ)))
      Filter.atTop (nhds (PowerSeries.coeff n etaProd)) := by
    have h0 : Filter.Tendsto
        (fun s : Finset ℕ => ∏ i ∈ s, (1 - X ^ (i + 1) : PowerSeries ℤ))
        Filter.atTop (nhds etaProd) :=
      (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd
    exact (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto _ _ _ _).mp h0 n
  rw [show nhds (PowerSeries.coeff n etaProd) = pure (PowerSeries.coeff n etaProd) from
      congrFun (nhds_discrete ℤ) _,
    Filter.tendsto_pure] at hconv
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp hconv
  rw [← ht₀ (t₀ ∪ Finset.range (n + 1)) Finset.subset_union_left]
  rw [show t₀ ∪ Finset.range (n + 1)
        = Finset.range (n + 1) ∪ (t₀ \ Finset.range (n + 1)) by
      rw [Finset.union_sdiff_self_eq_union, Finset.union_comm],
    Finset.prod_union Finset.disjoint_sdiff, PowerSeries.coeff_mul]
  have htail : ∀ m ≤ n,
      PowerSeries.coeff m
          (∏ i ∈ t₀ \ Finset.range (n + 1), (1 - X ^ (i + 1) : PowerSeries ℤ)) =
        if m = 0 then 1 else 0 := by
    refine coeff_prod_one_sub_X_pow_eq_coeff_one _ _ (fun i hi => ?_)
    have hi' : ¬ i < n + 1 := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_range.mpr h)
    omega
  rw [Finset.sum_eq_single_of_mem (n, 0) (by simp)]
  · rw [htail 0 (Nat.zero_le n), ite_eq_left rfl, mul_one]
  · rintro ⟨b₁, b₂⟩ hb hne
    have hb' : b₁ + b₂ = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hb₂ : b₂ ≤ n := Finset.HasAntidiagonal.antidiagonal.snd_le hb
    have h2 : b₂ ≠ 0 := by
      rintro rfl
      exact hne (by simp [← hb'])
    rw [htail b₂ hb₂, ite_eq_right h2, mul_zero]

/-- `jq.coeff (n - 1)` is `jNum.coeff n`, as rationals: `jq = q⁻¹ · jNum`. -/
private theorem coeff_jq_eq_coeff_jNum (n : ℕ) :
    jq.coeff ((n : ℤ) - 1) = ((PowerSeries.coeff n jNum : ℤ) : ℚ) := by
  rw [jq, HahnSeries.coeff_single_mul, one_mul,
    show ((n : ℤ) - 1 - (-1) : ℤ) = ((n : ℕ) : ℤ) by ring,
    HahnSeries.ofPowerSeries_apply_coeff, jNumQ, PowerSeries.coeff_map]
  simp

/-! ## The geometric factor `(1 - q ^ d)⁻¹`

`geomSeries d := expand d (mk 1)` has coefficients `1` on the multiples of `d` and
`0` elsewhere, and inverts `1 - q ^ d` in one step. This replaces the pin's
45-line `geomSeries` block; `expand` and `mk_one_mul_one_sub_eq_one` are mathlib's.
The pin's `geomSeries` was defined by `mk (if d ∣ k then 1 else 0)`; the port's
`expand` form is the same series and its two algebraic facts are mathlib's. -/

/-- `(1 - q ^ d)⁻¹`, as `expand d` of the geometric series `∑ q ^ k`. -/
private noncomputable def geomSeries (d : ℕ) (hd : d ≠ 0) : PowerSeries ℤ :=
  PowerSeries.expand d hd (PowerSeries.mk 1)

@[simp]
private theorem coeff_geomSeries (d : ℕ) (hd : d ≠ 0) (k : ℕ) :
    PowerSeries.coeff k (geomSeries d hd) = if d ∣ k then 1 else 0 := by
  rw [geomSeries, PowerSeries.coeff_expand]
  by_cases h : d ∣ k
  · rw [ite_eq_left h, ite_eq_left h]; simp
  · rw [ite_eq_right h, ite_eq_right h]

private theorem coeff_geomSeries_nonneg (d : ℕ) (hd : d ≠ 0) (k : ℕ) :
    0 ≤ PowerSeries.coeff k (geomSeries d hd) := by
  rw [coeff_geomSeries]
  split <;> norm_num

private theorem coeff_geomSeries_one (k : ℕ) :
    PowerSeries.coeff k (geomSeries 1 one_ne_zero) = 1 := by
  rw [coeff_geomSeries, ite_eq_left (one_dvd k)]

private theorem one_sub_X_pow_mul_geomSeries {d : ℕ} (hd : d ≠ 0) :
    ((1 : PowerSeries ℤ) - X ^ d) * geomSeries d hd = 1 := by
  have h : (1 : PowerSeries ℤ) - X ^ d = PowerSeries.expand d hd (1 - X) := by
    rw [map_sub, map_one, PowerSeries.expand_X]
  rw [h, geomSeries, ← map_mul,
    show (1 - X : PowerSeries ℤ) * PowerSeries.mk 1
        = PowerSeries.mk 1 * (1 - X) from mul_comm _ _,
    PowerSeries.mk_one_mul_one_sub_eq_one, map_one]

/-! ## Positivity of products and powers -/

private theorem coeff_mul_nonneg {f g : PowerSeries ℤ}
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (hg : ∀ k, 0 ≤ PowerSeries.coeff k g) (n : ℕ) :
    0 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hf p.1) (hg p.2)

private theorem coeff_prod_nonneg {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℤ)
    (hf : ∀ i ∈ s, ∀ k, 0 ≤ PowerSeries.coeff k (f i)) :
    ∀ n, 0 ≤ PowerSeries.coeff n (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro n
    rw [Finset.prod_empty, PowerSeries.coeff_one]
    split <;> norm_num
  | @insert a s ha ih =>
    intro n
    rw [Finset.prod_insert ha]
    exact coeff_mul_nonneg (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))) n

private theorem coeff_pow_nonneg {f : PowerSeries ℤ}
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (m : ℕ) :
    ∀ n, 0 ≤ PowerSeries.coeff n (f ^ m) := by
  induction m with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split <;> norm_num
  | succ m ih =>
    intro n
    rw [pow_succ]
    exact coeff_mul_nonneg ih hf n

/-- A series with constant term `1` and nonnegative coefficients times one with all
coefficients `≥ 1` has all coefficients `≥ 1` (the `(0, n)` term of the Cauchy
sum). -/
private theorem one_le_coeff_mul_of_nonneg {f g : PowerSeries ℤ}
    (hf : ∀ k, 0 ≤ PowerSeries.coeff k f) (hf0 : PowerSeries.constantCoeff f = 1)
    (hg : ∀ k, 1 ≤ PowerSeries.coeff k g) (n : ℕ) :
    1 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  have hmem : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  have hterm : (1 : ℤ) ≤ PowerSeries.coeff (0 : ℕ) f * PowerSeries.coeff n g := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff, hf0, one_mul]
    exact hg n
  calc (1 : ℤ) ≤ PowerSeries.coeff (0 : ℕ) f * PowerSeries.coeff n g := hterm
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g :=
        Finset.single_le_sum
          (fun p _ => mul_nonneg (hf p.1) (le_trans zero_le_one (hg p.2))) hmem

private theorem one_le_coeff_mul {f g : PowerSeries ℤ}
    (hf : ∀ k, 1 ≤ PowerSeries.coeff k f) (hg : ∀ k, 1 ≤ PowerSeries.coeff k g) (n : ℕ) :
    1 ≤ PowerSeries.coeff n (f * g) := by
  rw [PowerSeries.coeff_mul]
  have hmem : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  calc (1 : ℤ) = 1 * 1 := (one_mul 1).symm
    _ ≤ PowerSeries.coeff (0 : ℕ) f * PowerSeries.coeff n g :=
        mul_le_mul (hf 0) (hg n) zero_le_one (le_trans zero_le_one (hf 0))
    _ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g :=
        Finset.single_le_sum
          (fun p _ => mul_nonneg (le_trans zero_le_one (hf p.1))
            (le_trans zero_le_one (hg p.2))) hmem

private theorem one_le_coeff_pow {f : PowerSeries ℤ}
    (hf : ∀ k, 1 ≤ PowerSeries.coeff k f) (m : ℕ) :
    ∀ n, 1 ≤ PowerSeries.coeff n (f ^ (m + 1)) := by
  induction m with
  | zero => intro n; simpa using hf n
  | succ m ih => intro n; rw [pow_succ]; exact one_le_coeff_mul ih hf n

/-! ## Truncation-stable comparisons

The three lemmas below are local (the audit found no mathlib replacement):
`coeff_mul_congr` and `coeff_pow_congr` compare coefficients below the truncation
order, and `coeff_inv_congr` is the truncation-stable inverse comparison. -/

private theorem coeff_mul_congr {A C g : PowerSeries ℤ} {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k C) :
    ∀ k ≤ n, PowerSeries.coeff k (A * g) = PowerSeries.coeff k (C * g) := by
  intro k hk
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have h1 : p.1 ≤ k := Finset.HasAntidiagonal.antidiagonal.fst_le hp
  rw [h p.1 (le_trans h1 hk)]

private theorem coeff_pow_congr {A C : PowerSeries ℤ} {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k C) (m : ℕ) :
    ∀ k ≤ n, PowerSeries.coeff k (A ^ m) = PowerSeries.coeff k (C ^ m) := by
  induction m with
  | zero => intro k _; rfl
  | succ m ih =>
    intro k hk
    rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have h1 : p.1 ≤ k := Finset.HasAntidiagonal.antidiagonal.fst_le hp
    have h2 : p.2 ≤ k := Finset.HasAntidiagonal.antidiagonal.snd_le hp
    rw [ih p.1 (le_trans h1 hk), h p.2 (le_trans h2 hk)]

private theorem coeff_inv_congr {A B C D : PowerSeries ℤ}
    (hAB : A * B = 1) (hCD : C * D = 1) {n : ℕ}
    (h : ∀ k ≤ n, PowerSeries.coeff k A = PowerSeries.coeff k C) :
    ∀ k ≤ n, PowerSeries.coeff k B = PowerSeries.coeff k D := by
  intro k hk

  have hCB : ∀ m ≤ n, PowerSeries.coeff m (C * B) =
      PowerSeries.coeff m (1 : PowerSeries ℤ) := by
    intro m hm
    rw [← hAB]
    exact (coeff_mul_congr (fun k hk => (h k hk).symm) m hm)

  have key : B = D * (C * B) := by
    rw [← mul_assoc, mul_comm D C, hCD, one_mul]
  rw [key, PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single_of_mem (k, 0) (by simp)]
  · rw [hCB 0 (Nat.zero_le n), PowerSeries.coeff_one, ite_eq_left rfl, mul_one]
  · rintro ⟨b₁, b₂⟩ hb hne
    have hb' : b₁ + b₂ = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hb
    have hb₂ : b₂ ≤ k := Finset.HasAntidiagonal.antidiagonal.snd_le hb
    have h2 : b₂ ≠ 0 := by
      rintro rfl
      exact hne (by simp [← hb'])
    rw [hCB b₂ (le_trans hb₂ hk), PowerSeries.coeff_one, ite_eq_right h2, mul_zero]

/-! ## The truncated `eta` and `Δ⁻¹` -/

private abbrev partialEta (N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, ((1 : PowerSeries ℤ) - X ^ (i + 1))

private abbrev partialGeom (N : ℕ) : PowerSeries ℤ :=
  ∏ i ∈ Finset.range N, geomSeries (i + 1) (Nat.succ_ne_zero i)

private theorem partialEta_mul_partialGeom (N : ℕ) :
    partialEta N * partialGeom N = 1 := by
  rw [← Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl
    (fun i _ => one_sub_X_pow_mul_geomSeries (Nat.succ_ne_zero i))]
  exact Finset.prod_const_one

private theorem coeff_etaProd_eq_coeff_partialEta {k n : ℕ} (hk : k ≤ n) :
    PowerSeries.coeff k etaProd = PowerSeries.coeff k (partialEta (n + 1)) := by
  rw [coeff_etaProd_eq_coeff_partialProd k]
  exact (coeff_prod_one_sub_pow_le n k hk).symm

private theorem coeff_dedekindEtaUnitInv_eq_coeff_partialGeom_pow (n : ℕ) :
    ∀ k ≤ n, PowerSeries.coeff k dedekindEtaUnitInv =
      PowerSeries.coeff k (partialGeom (n + 1) ^ 24) := by

  have hunits : ∀ k ≤ n, PowerSeries.coeff k dedekindEtaUnit =
      PowerSeries.coeff k (partialEta (n + 1) ^ 24) := by
    intro k hk
    rw [dedekindEtaUnit]
    exact coeff_pow_congr (fun k hk => coeff_etaProd_eq_coeff_partialEta hk) 24 k hk

  have hinv : partialEta (n + 1) ^ 24 * partialGeom (n + 1) ^ 24 = 1 := by
    rw [← mul_pow, partialEta_mul_partialGeom, one_pow]
  exact coeff_inv_congr dedekindEtaUnit_mul_inv hinv hunits

private theorem one_le_coeff_partialGeom_pow (n k : ℕ) :
    1 ≤ PowerSeries.coeff k (partialGeom (n + 1) ^ 24) := by

  have hsplit : partialGeom (n + 1) =
      (∏ i ∈ Finset.range n, geomSeries (i + 2) (Nat.succ_ne_zero (i + 1))) *
        geomSeries 1 one_ne_zero :=
    Finset.prod_range_succ' (fun i => geomSeries (i + 1) (Nat.succ_ne_zero i)) n
  rw [hsplit, mul_pow]

  have htail_nonneg : ∀ j, 0 ≤ PowerSeries.coeff j
      ((∏ i ∈ Finset.range n, geomSeries (i + 2) (Nat.succ_ne_zero (i + 1))) ^ 24) :=
    coeff_pow_nonneg
      (coeff_prod_nonneg _ _
        (fun i _ k => coeff_geomSeries_nonneg (i + 2) (Nat.succ_ne_zero (i + 1)) k)) 24
  have htail_cc : PowerSeries.constantCoeff
      ((∏ i ∈ Finset.range n, geomSeries (i + 2) (Nat.succ_ne_zero (i + 1))) ^ 24) = 1 := by
    rw [map_pow, map_prod]
    simp only [show ∀ i, PowerSeries.constantCoeff
      (geomSeries (i + 1) (Nat.succ_ne_zero i)) = 1 from fun i => by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_geomSeries,
          ite_eq_left (dvd_zero _)], Finset.prod_const_one, one_pow]

  have hhead : ∀ j, 1 ≤ PowerSeries.coeff j (geomSeries 1 one_ne_zero ^ 24) :=
    one_le_coeff_pow (fun j => le_of_eq (coeff_geomSeries_one j).symm) 23
  exact one_le_coeff_mul_of_nonneg htail_nonneg htail_cc hhead k

private theorem one_le_coeff_dedekindEtaUnitInv (n : ℕ) :
    1 ≤ PowerSeries.coeff n dedekindEtaUnitInv := by
  rw [coeff_dedekindEtaUnitInv_eq_coeff_partialGeom_pow n n le_rfl]
  exact one_le_coeff_partialGeom_pow n n

private theorem coeff_eisenstein4_nonneg (n : ℕ) :
    0 ≤ PowerSeries.coeff n eisenstein4 := by
  rw [eisenstein4, PowerSeries.coeff_mk]
  split
  · norm_num
  · refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun d _ => ?_)
    exact pow_nonneg (Int.natCast_nonneg d) 3

private theorem one_le_coeff_jNum (n : ℕ) : 1 ≤ PowerSeries.coeff n jNum := by
  rw [jNum]
  exact one_le_coeff_mul_of_nonneg (coeff_pow_nonneg coeff_eisenstein4_nonneg 3)
    (by rw [map_pow, constantCoeff_eisenstein4, one_pow])
    one_le_coeff_dedekindEtaUnitInv n

/-! ## The exported statements -/

/-- Every regular coefficient of `j(q)` is at least `1`. Verbatim from the pin
wrapper `Theorems/Thm_ModularCurve_one_le_coeff_jq.lean`. -/
theorem one_le_coeff_jq (n : ℕ) : (1 : ℚ) ≤ jq.coeff (n : ℤ) := by
  have h : ((n : ℤ)) = ((n + 1 : ℕ) : ℤ) - 1 := by push_cast; ring
  rw [h, coeff_jq_eq_coeff_jNum]
  exact_mod_cast one_le_coeff_jNum (n + 1)

/-- No regular coefficient of `j(q)` vanishes. -/
theorem coeff_jq_ne_zero (n : ℕ) : jq.coeff (n : ℤ) ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_coeff_jq n))

end ModularCurve

end

#print axioms ModularCurve.one_le_coeff_jq
#print axioms ModularCurve.coeff_jq_ne_zero
