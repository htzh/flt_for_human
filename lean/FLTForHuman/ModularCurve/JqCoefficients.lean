/-
  The low coefficients of `jq`: `j(q) = q⁻¹ + 744 + 196884 q + ⋯`.

  This is the first *proof* module of the `functionFieldGeneration` effort: it closes
  the two `jq.coeff` claims that sat in Zone C of `spec/ModularCurveConsumer.lean`
  since Layer 0.

  Source of the *statement* — `base/004-the-j-invariant.md` (and the consumer's
  Zone C): the regular coefficients of `j` are `744` at `q ^ 0` and `196884` at
  `q ^ 1`. FLT has no declaration for these two facts — `hasSum_jq_qParam` is a
  different statement, reached a different way — so there is no FLT name to keep.
  The names follow the port's own convention in `Defs/Jq.lean`, next to
  `coeff_jq_neg_one` and `coeff_jq_of_lt`.

  The *proof* is a deliberate divergence from FLT's route. FLT reaches the
  coefficients of `η` through `S_ModularCurve_StarBank_deltaNorm.lean`
  (`rescale_tprod_one_sub_X_pow`, `expand_tprod_one_sub_X_pow`) and the modular-form
  q-expansion cluster (44 nodes, ~11k lines) inside the deferred `Φ_p` subtree.
  Here we use mathlib's pentagonal number theorem instead: `Defs/Jq.lean` defines
  `etaProd` as exactly `∏' n, (1 - X ^ (n + 1))`, and mathlib's
  `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` identifies that product with
  `pentagonalSeries`, whose coefficients are given by
  `coeff_pentagonalSeries_pentagonal` / `coeff_pentagonalSeries_eq_zero`. The
  computation is then finite and low-order:

      E₄³  = 1 + 720 q + 179280 q² + ⋯
      η²⁴  = 1 - 24 q +   252 q² + ⋯
      Δ⁻¹  = 1 + 24 q +   324 q² + ⋯
      jNum = 1 + 744 q + 196884 q² + ⋯

  Nothing of the modular-form cluster is ported. `PowerSeries`, `HahnSeries`,
  `pentagonalSeries` and `Finset.Nat.sum_antidiagonal_eq_sum_range_succ` are
  mathlib's; the two exported theorems are ours.

  Assumes `eisenstein4`, `etaProd`, `dedekindEtaUnit{,_inv}`, `jNum`, `jNumQ`, `jq`
  and their constant-term/`invOfUnit` lemmas from `Defs/Jq.lean`.

  ## The low coefficients up to order six, and `etaProd ^ a`

  The three FLT rows that continue this computation are appended below, at their
  wrapper statements:

  * `coeff_jNum_le_six` — `jNum`'s coefficients `0`–`6` (`Theorems/…coeff_jNum_le_six`),
    the same `LowCoeffs`/`conv` list algebra on one more order, and to order six
    instead of two.
  * `hasSum_coeff_etaProd_pow` — the analytic form: for `‖q‖ < 1`, the `q`-series of
    `etaProd ^ a` sums to `(∏' n, (1 - q ^ (n + 1))) ^ a` (`Theorems/…hasSum_coeff_etaProd_pow`),
    by dominated convergence over the partial products, with the geometric-exponential
    bound `|coeff m (f N ^ a)| ≤ exp(∑' n, r ^ (n + 1)) ^ a` for `‖q‖ < r < 1`.
  * `eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero` — a polynomial killed by
    `evalAtJ` on the coefficient window `[-n, 0]` is zero
    (`Theorems/…eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero`), read off the
    `q ^ (-natDegree)` coefficient.

  spec-pin: Theorems/Thm_ModularCurve_coeff_jNum_le_six.lean
  spec-pin: P2M/Sol/S_ModularCurve_coeff_jNum_le_six.lean
  spec-pin: Theorems/Thm_ModularCurve_hasSum_coeff_etaProd_pow.lean
  spec-pin: P2M/Sol/S_ModularCurve_hasSum_coeff_etaProd_pow.lean
  spec-pin: Theorems/Thm_ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero.lean
  spec-pin: P2M/Sol/S_ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero.lean
-/
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.NumberTheory.ModularForms.DedekindEta
import Mathlib.Analysis.Normed.Group.Tannery
import FLTForHuman.ModularCurve.Defs.Jq

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

/-! ## `etaProd` is mathlib's pentagonal product

`Defs/Jq.lean` defines `etaProd` as a topological product; mathlib proves the same
product equals `pentagonalSeries`, whose coefficients are explicit. The next three
constants are all the `η` data the computation needs: `1`, `-1`, `-1`. -/

private theorem etaProd_eq_pentagonalSeries : etaProd = PowerSeries.pentagonalSeries ℤ := by
  rw [etaProd]
  exact PowerSeries.WithPiTopology.tprod_one_sub_X_pow ℤ

private theorem coeff_etaProd_one : etaProd.coeff 1 = -1 := by
  rw [etaProd_eq_pentagonalSeries]
  have h := PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℤ) 1
  norm_num [pentagonal] at h
  exact h

private theorem coeff_etaProd_two : etaProd.coeff 2 = -1 := by
  rw [etaProd_eq_pentagonalSeries]
  have h := PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℤ) (-1)
  norm_num [pentagonal] at h
  exact h

/-! ## Low-order coefficient algebra

`PowerSeries.coeff_mul` is a `Finset` sum over `antidiagonal n`; for `n = 2` it is
the three-term formula below (mathlib rewrites the antidiagonal as `range 3` via
`Finset.Nat.sum_antidiagonal_eq_sum_range_succ`). `coeff_two_pow` is the resulting
closed form for the second coefficient of a power, by induction on the exponent,
using mathlib's `coeff_one_pow` for the first coefficient. -/

private theorem coeff_two_mul (φ ψ : PowerSeries ℤ) :
    (φ * ψ).coeff 2 =
      φ.coeff 0 * ψ.coeff 2 + φ.coeff 1 * ψ.coeff 1 + φ.coeff 2 * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (PowerSeries.coeff i) φ * (PowerSeries.coeff j) ψ) 2]
  norm_num [Finset.sum_range_succ]

private theorem coeff_two_pow (φ : PowerSeries ℤ) (h0 : constantCoeff φ = 1) (n : ℕ) :
    (φ ^ n).coeff 2 =
      (n.choose 2 : ℤ) * (φ.coeff 1) ^ 2 + (n : ℤ) * φ.coeff 2 := by
  have h0' : φ.coeff 0 = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact h0
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow0 : (φ ^ n).coeff 0 = 1 := by
        rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, h0, one_pow]
      rw [pow_succ, coeff_two_mul, ih, PowerSeries.coeff_one_pow, hpow0, h0', h0]
      simp only [mul_one, one_mul]
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      ring

/-! ## The numerator `jNum = E₄ ^ 3 · Δ⁻¹` -/

private theorem coeff_eisenstein4_one : eisenstein4.coeff 1 = 240 := by
  rw [eisenstein4, PowerSeries.coeff_mk, ite_eq_right (by norm_num : ¬ (1 : ℕ) = 0),
    Nat.divisors_one]
  norm_num

private theorem coeff_eisenstein4_two : eisenstein4.coeff 2 = 2160 := by
  rw [eisenstein4, PowerSeries.coeff_mk, ite_eq_right (by norm_num : ¬ (2 : ℕ) = 0)]
  decide

private theorem coeff_dedekindEtaUnit_zero : dedekindEtaUnit.coeff 0 = 1 := by
  rw [dedekindEtaUnit, PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_etaProd,
    one_pow]

private theorem coeff_dedekindEtaUnit_one : dedekindEtaUnit.coeff 1 = -24 := by
  rw [dedekindEtaUnit, PowerSeries.coeff_one_pow, coeff_etaProd_one, constantCoeff_etaProd]
  norm_num

private theorem coeff_dedekindEtaUnit_two : dedekindEtaUnit.coeff 2 = 252 := by
  rw [dedekindEtaUnit, coeff_two_pow _ constantCoeff_etaProd, coeff_etaProd_one, coeff_etaProd_two]
  decide

/-- `Δ⁻¹`'s coefficients come from `Δ * Δ⁻¹ = 1` rather than from
`PowerSeries.coeff_invOfUnit`'s recursion: multiply out and solve. -/
private theorem coeff_dedekindEtaUnitInv_zero : dedekindEtaUnitInv.coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  exact constantCoeff_dedekindEtaUnitInv

private theorem coeff_dedekindEtaUnitInv_one : dedekindEtaUnitInv.coeff 1 = 24 := by
  have h := congrArg (PowerSeries.coeff 1) dedekindEtaUnit_mul_inv
  rw [PowerSeries.coeff_one_mul, PowerSeries.coeff_one, coeff_dedekindEtaUnit_one,
    constantCoeff_dedekindEtaUnit, constantCoeff_dedekindEtaUnitInv] at h
  norm_num at h
  linarith

private theorem coeff_dedekindEtaUnitInv_two : dedekindEtaUnitInv.coeff 2 = 324 := by
  have h := congrArg (PowerSeries.coeff 2) dedekindEtaUnit_mul_inv
  rw [coeff_two_mul, PowerSeries.coeff_one, coeff_dedekindEtaUnit_zero,
    coeff_dedekindEtaUnit_one, coeff_dedekindEtaUnit_two, coeff_dedekindEtaUnitInv_zero,
    coeff_dedekindEtaUnitInv_one] at h
  norm_num at h
  linarith

private theorem coeff_eisenstein4Pow3_zero : (eisenstein4 ^ 3).coeff 0 = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_eisenstein4, one_pow]

private theorem coeff_eisenstein4Pow3_one : (eisenstein4 ^ 3).coeff 1 = 720 := by
  rw [PowerSeries.coeff_one_pow, coeff_eisenstein4_one, constantCoeff_eisenstein4]
  norm_num

private theorem coeff_eisenstein4Pow3_two : (eisenstein4 ^ 3).coeff 2 = 179280 := by
  rw [coeff_two_pow _ constantCoeff_eisenstein4, coeff_eisenstein4_one, coeff_eisenstein4_two]
  decide

private theorem constantCoeff_eisenstein4Pow3 : constantCoeff (eisenstein4 ^ 3) = 1 := by
  rw [map_pow, constantCoeff_eisenstein4, one_pow]

private theorem coeff_jNum_one : jNum.coeff 1 = 744 := by
  rw [jNum, PowerSeries.coeff_one_mul, coeff_eisenstein4Pow3_one, constantCoeff_dedekindEtaUnitInv,
    coeff_dedekindEtaUnitInv_one, constantCoeff_eisenstein4Pow3]
  norm_num

private theorem coeff_jNum_two : jNum.coeff 2 = 196884 := by
  rw [jNum, coeff_two_mul, coeff_eisenstein4Pow3_zero, coeff_eisenstein4Pow3_one,
    coeff_eisenstein4Pow3_two, coeff_dedekindEtaUnitInv_zero, coeff_dedekindEtaUnitInv_one,
    coeff_dedekindEtaUnitInv_two]
  norm_num

/-! ## Push to `ℚ` and read off the coefficients of `jq` -/

private theorem coeff_jNumQ_one : jNumQ.coeff 1 = 744 := by
  rw [jNumQ, PowerSeries.coeff_map, coeff_jNum_one]
  norm_num

private theorem coeff_jNumQ_two : jNumQ.coeff 2 = 196884 := by
  rw [jNumQ, PowerSeries.coeff_map, coeff_jNum_two]
  norm_num

/-- The constant coefficient of the `j`-invariant, `j(q) = q⁻¹ + 744 + ⋯`:
`744`. The statement is base/004's; the proof is mathlib's pentagonal route. -/
theorem coeff_jq_zero : jq.coeff 0 = 744 := by
  rw [jq, HahnSeries.coeff_single_mul, one_mul]
  rw [show (0 : ℤ) - -1 = ((1 : ℕ) : ℤ) by norm_num]
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  exact coeff_jNumQ_one

/-- The `q`-coefficient of the `j`-invariant, `j(q) = q⁻¹ + 744 + 196884 q + ⋯`:
`196884`. The statement is base/004's; the proof is mathlib's pentagonal route. -/
theorem coeff_jq_one : jq.coeff 1 = 196884 := by
  rw [jq, HahnSeries.coeff_single_mul, one_mul]
  rw [show (1 : ℤ) - -1 = ((2 : ℕ) : ℤ) by norm_num]
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  exact coeff_jNumQ_two

/-! ## The coefficient window `[-n, 0]` of `evalAtJ`

`evalAtJ P` is `P` evaluated at `q⁻¹ + 744 + ⋯`, so its `q ^ (-d)` coefficient is the
`d`-th coefficient of `P` as soon as `d ≥ P.natDegree`. A polynomial whose evaluation
vanishes on the whole window `[-n, 0]` therefore has a zero leading coefficient: it
is the zero polynomial. This is the pin's `coeff_evalAtJ_neg_natDegree` route, read
here through the port's `coeff_aeval_jq_neg`. -/

theorem coeff_evalAtJ_neg_natDegree (P : Polynomial ℤ) (d : ℕ) (hd : P.natDegree ≤ d) :
    (evalAtJ P).coeff (-(d : ℤ)) = (P.coeff d : ℚ) := by
  rw [evalAtJ_eq_aeval_map]
  have h := coeff_aeval_jq_neg (P.map (Int.castRingHom ℚ))
    (le_trans Polynomial.natDegree_map_le hd)
  rw [Polynomial.coeff_map] at h
  exact h

theorem eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero (P : Polynomial ℤ) (n : ℕ)
    (hP : P.natDegree ≤ n) (h : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ 0 → (evalAtJ P).coeff m = 0) :
    P = 0 := by
  by_contra hne
  have hlc : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have := coeff_evalAtJ_neg_natDegree P P.natDegree le_rfl
  rw [h _ (by omega) (by omega)] at this
  exact hlc (by exact_mod_cast this.symm)

/-! ## The `LowCoeffs` list algebra

The pin's route to `jNum`'s first coefficients: a power series is pinned down to
order `L.length` by a list `L`, and `conv` is the list convolution that multiplies
two such pins down. `LowCoeffs.invOfUnit` converts a pin on `u` and a convolution
identity into a pin on `u.invOfUnit 1`, which is what makes `Δ⁻¹`'s coefficients
computable by hand. -/

open scoped PowerSeries

namespace JCoeff

variable {R : Type*} [CommRing R]

def LowCoeffs (f : R⟦X⟧) (L : List R) : Prop :=
  ∀ i : ℕ, i < L.length → coeff i f = L.getD i 0

def conv (L M : List R) : List R :=
  (List.range (min L.length M.length)).map
    fun k => ((List.range (k + 1)).map fun i => L.getD i 0 * M.getD (k - i) 0).sum

theorem length_conv (L M : List R) : (conv L M).length = min L.length M.length := by
  simp [conv]

theorem finset_sum_range_eq_list_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp

theorem getD_conv (L M : List R) {k : ℕ} (hk : k < min L.length M.length) :
    (conv L M).getD k 0 = ∑ i ∈ Finset.range (k + 1), L.getD i 0 * M.getD (k - i) 0 := by
  rw [conv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  simp [finset_sum_range_eq_list_sum]

theorem LowCoeffs.mul {f g : R⟦X⟧} {L M : List R} (hf : LowCoeffs f L) (hg : LowCoeffs g M) :
    LowCoeffs (f * g) (conv L M) := by
  intro k hk
  rw [length_conv] at hk
  rw [getD_conv L M hk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hf i (by omega), hg (k - i) (by omega)]

theorem LowCoeffs.congr {f : R⟦X⟧} {L M : List R} (hf : LowCoeffs f L) (h : L = M) :
    LowCoeffs f M :=
  h ▸ hf

theorem LowCoeffs.one (n : ℕ) : LowCoeffs (1 : R⟦X⟧) (1 :: List.replicate n 0) := by
  intro i hi
  rcases i with _ | i
  · simp
  · simp only [List.length_cons, List.length_replicate] at hi
    rw [PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero i), List.getD_eq_getElem?_getD]
    simp [show i < n by omega]

theorem LowCoeffs.one_sub_X_pow (m n : ℕ) (hm : 0 < m) :
    LowCoeffs (1 - X ^ m : R⟦X⟧)
      ((List.range n).map fun i => if i = 0 then 1 else if i = m then -1 else 0) := by
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, map_sub, PowerSeries.coeff_one,
    PowerSeries.coeff_X_pow]
  by_cases h0 : i = 0
  · subst h0; simp [hm.ne]
  · simp [h0]
    split_ifs <;> simp

theorem LowCoeffs.X_pow_dvd_sub {f g : R⟦X⟧} {L : List R} (hf : LowCoeffs f L)
    (hg : LowCoeffs g L) : (X : R⟦X⟧) ^ L.length ∣ f - g := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, hf m hm, hg m hm, sub_self]

theorem LowCoeffs.invOfUnit {u : R⟦X⟧} {L V : List R} (hu : LowCoeffs u L)
    (hV : V.length = L.length) (hc : constantCoeff u = 1)
    (hconv : conv L V = 1 :: List.replicate (L.length - 1) 0) (hpos : 0 < L.length) :
    LowCoeffs (u.invOfUnit 1) V := by
  set w := u.invOfUnit 1 with hw
  have huw : u * w = 1 := PowerSeries.mul_invOfUnit u 1 (by rw [hc]; rfl)

  set Vp : R⟦X⟧ := PowerSeries.mk fun i => V.getD i 0 with hVp
  have hVpL : LowCoeffs Vp V := fun i _ => by simp [hVp, PowerSeries.coeff_mk]
  have h1 : LowCoeffs (u * Vp) (1 :: List.replicate (L.length - 1) 0) :=
    (hu.mul hVpL).congr (by rw [hconv])
  have h1' : LowCoeffs (1 : R⟦X⟧) (1 :: List.replicate (L.length - 1) 0) := LowCoeffs.one _
  have hdvd : (X : R⟦X⟧) ^ L.length ∣ u * Vp - 1 := by
    have := h1.X_pow_dvd_sub h1'
    simpa [Nat.sub_add_cancel hpos] using this
  have hdvd' : (X : R⟦X⟧) ^ L.length ∣ Vp - w := by
    have : Vp - w = w * (u * Vp - 1) := by
      calc Vp - w = (u * w) * Vp - w * 1 := by rw [huw, one_mul, mul_one]
        _ = w * (u * Vp - 1) := by ring
    rw [this]
    exact Dvd.dvd.mul_left hdvd w
  rw [PowerSeries.X_pow_dvd_iff] at hdvd'
  intro i hi
  have := hdvd' i (by omega)
  rw [map_sub, sub_eq_zero] at this
  rw [← this]
  exact hVpL i hi

theorem LowCoeffs.pow_succ {f : R⟦X⟧} {L M : List R} {n : ℕ} (hn : LowCoeffs (f ^ n) M)
    (hf : LowCoeffs f L) : LowCoeffs (f ^ (n + 1)) (conv M L) := by
  rw [_root_.pow_succ]; exact hn.mul hf

end JCoeff

open JCoeff

section Eta

theorem coeff_prod_one_sub_X_pow_of_le (T : Finset ℕ) (K : ℕ) (hT : ∀ b ∈ T, K ≤ b) (k : ℕ)
    (hk : k ≤ K) :
    coeff k (∏ b ∈ T, (1 - (X : ℤ⟦X⟧) ^ (b + 1))) = coeff k (1 : ℤ⟦X⟧) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, sub_mul, one_mul, map_sub,
      ih (fun b hb => hT b (Finset.mem_insert_of_mem hb))]
    have : coeff k ((X : ℤ⟦X⟧) ^ (a + 1) * ∏ b ∈ T, (1 - (X : ℤ⟦X⟧) ^ (b + 1))) = 0 := by
      rw [PowerSeries.coeff_X_pow_mul']
      have : ¬ a + 1 ≤ k := by have := hT a (Finset.mem_insert_self a T); omega
      rw [ite_eq_right this]
    rw [this, sub_zero]

theorem coeff_etaProd_eq_coeff_prod_range (K k : ℕ) (hk : k ≤ K) :
    coeff k etaProd = coeff k (∏ n ∈ Finset.range K, (1 - (X : ℤ⟦X⟧) ^ (n + 1))) := by
  classical
  have hmul := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have hprod : HasProd (fun n => 1 - (X : ℤ⟦X⟧) ^ (n + 1)) etaProd := hmul.hasProd

  have hlim : Filter.Tendsto
      (fun s : Finset ℕ => coeff k (∏ b ∈ s, (1 - (X : ℤ⟦X⟧) ^ (b + 1))))
      Filter.atTop (nhds (coeff k etaProd)) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℤ k).tendsto _).comp hprod

  have hev : ∀ᶠ s : Finset ℕ in Filter.atTop,
      coeff k (∏ b ∈ s, (1 - (X : ℤ⟦X⟧) ^ (b + 1)))
        = coeff k (∏ n ∈ Finset.range K, (1 - (X : ℤ⟦X⟧) ^ (n + 1))) := by
    rw [Filter.eventually_atTop]
    refine ⟨Finset.range K, fun s hs => ?_⟩
    rw [← Finset.prod_sdiff hs, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.sum_eq_single 0]
    · rw [coeff_prod_one_sub_X_pow_of_le (s \ Finset.range K) K (fun b hb => by
          simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hb; exact hb.2) 0
          (Nat.zero_le _)]
      simp
    · intro i hi hi0
      rw [coeff_prod_one_sub_X_pow_of_le (s \ Finset.range K) K (fun b hb => by
          simp only [Finset.mem_sdiff, Finset.mem_range, not_lt] at hb; exact hb.2) i
          (by rw [Finset.mem_range] at hi; omega)]
      rw [PowerSeries.coeff_one, ite_eq_right hi0, zero_mul]
    · intro h; simp at h
  have hlim2 : Filter.Tendsto
      (fun s : Finset ℕ => coeff k (∏ b ∈ s, (1 - (X : ℤ⟦X⟧) ^ (b + 1))))
      Filter.atTop (nhds (coeff k (∏ n ∈ Finset.range K, (1 - (X : ℤ⟦X⟧) ^ (n + 1))))) :=
    tendsto_const_nhds.congr' (Filter.EventuallyEq.symm hev)
  exact tendsto_nhds_unique hlim hlim2

theorem lowCoeffs_etaProd : LowCoeffs etaProd [1, -1, -1, 0, 0, 1, 0] := by

  have hP : LowCoeffs (∏ n ∈ Finset.range 7, (1 - (X : ℤ⟦X⟧) ^ (n + 1)))
      [1, -1, -1, 0, 0, 1, 0] := by
    have f := fun m (hm : 0 < m) => LowCoeffs.one_sub_X_pow (R := ℤ) m 7 hm
    have h1 : LowCoeffs (∏ n ∈ Finset.range 1, (1 - (X : ℤ⟦X⟧) ^ (n + 1)))
        [1, -1, 0, 0, 0, 0, 0] := by
      rw [Finset.prod_range_one]; exact (f 1 (by norm_num)).congr (by decide)
    have h2 := (h1.mul (f 2 (by norm_num))).congr (M := [1, -1, -1, 1, 0, 0, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h2
    have h3 := (h2.mul (f 3 (by norm_num))).congr (M := [1, -1, -1, 0, 1, 1, -1]) (by decide)
    rw [← Finset.prod_range_succ] at h3
    have h4 := (h3.mul (f 4 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 2, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h4
    have h5 := (h4.mul (f 5 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 1, 1]) (by decide)
    rw [← Finset.prod_range_succ] at h5
    have h6 := (h5.mul (f 6 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 1, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h6
    have h7 := (h6.mul (f 7 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 1, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h7
    exact h7
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rw [coeff_etaProd_eq_coeff_prod_range 7 i (by omega)]
  exact hP i (by simpa using hi)

theorem lowCoeffs_dedekindEtaUnit :
    LowCoeffs dedekindEtaUnit [1, -24, 252, -1472, 4830, -6048, -16744] := by
  have e1 := lowCoeffs_etaProd
  have e2 := (e1.mul e1).congr (M := [1, -2, -1, 2, 1, 2, -2]) (by decide)
  have e4 := (e2.mul e2).congr (M := [1, -4, 2, 8, -5, -4, -10]) (by decide)
  have e8 := (e4.mul e4).congr (M := [1, -8, 20, 0, -70, 64, 56]) (by decide)
  have e16 := (e8.mul e8).congr (M := [1, -16, 104, -320, 260, 1248, -3712]) (by decide)
  have e24 := (e16.mul e8).congr (M := [1, -24, 252, -1472, 4830, -6048, -16744]) (by decide)
  have h24 : dedekindEtaUnit = ((((etaProd * etaProd) * (etaProd * etaProd)) *
        ((etaProd * etaProd) * (etaProd * etaProd))) *
      (((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd)))) *
      (((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd))) := by
    rw [dedekindEtaUnit]; ring
  rw [h24]
  exact e24

theorem lowCoeffs_dedekindEtaUnitInv :
    LowCoeffs dedekindEtaUnitInv [1, 24, 324, 3200, 25650, 176256, 1073720] := by
  refine lowCoeffs_dedekindEtaUnit.invOfUnit (by rfl) constantCoeff_dedekindEtaUnit
    (by decide) (by decide)

theorem lowCoeffs_eisenstein4 : LowCoeffs eisenstein4 [1, 240, 2160, 6720, 17520, 30240, 60480] := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  simp only [eisenstein4, PowerSeries.coeff_mk]
  interval_cases i <;> decide

theorem lowCoeffs_jNum :
    LowCoeffs jNum [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600] := by
  have h4 := lowCoeffs_eisenstein4
  have h42 := (h4.mul h4).congr (M := [1, 480, 61920, 1050240, 7926240, 37500480, 135480960])
    (by decide)
  have h43 := (h42.mul h4).congr
    (M := [1, 720, 179280, 16954560, 396974160, 4632858720, 34413301440]) (by decide)
  have hj := (h43.mul lowCoeffs_dedekindEtaUnitInv).congr
    (M := [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600]) (by decide)
  have : jNum = eisenstein4 * eisenstein4 * eisenstein4 * dedekindEtaUnitInv := by
    rw [jNum]; ring
  rw [this]; exact hj

end Eta

/-- The pin's `coeff_jNum_le_six` (`Theorems/Thm_ModularCurve_coeff_jNum_le_six.lean`):
the numerator of `j` starts `1 + 744 q + 196884 q² + ⋯`, up to order six. -/
theorem coeff_jNum_le_six :
    PowerSeries.coeff 0 jNum = 1 ∧ PowerSeries.coeff 1 jNum = 744 ∧
      PowerSeries.coeff 2 jNum = 196884 ∧ PowerSeries.coeff 3 jNum = 21493760 ∧
      PowerSeries.coeff 4 jNum = 864299970 ∧ PowerSeries.coeff 5 jNum = 20245856256 ∧
      PowerSeries.coeff 6 jNum = 333202640600 := by
  have h := lowCoeffs_jNum
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide)⟩

open Filter

open scoped Topology

/-! ## `etaProd ^ a` as a `q`-series, and the pentagonal bound

The coefficient `m` of `etaProd ^ a` depends only on the partial product over
`n < m + 1` (the tail starts in degree `m + 1`), and the partial products converge
to `etaProd` in the `WithPiTopology`, so `coeff m (etaProd ^ a)` is the coefficient of
the finite product `f (m + 1) ^ a`. Bounding `p N ^ a` by the real polynomial
`P N ^ a` turns that into absolute convergence on `‖q‖ < 1`, and dominated
convergence gives the `HasSum` of the statement. -/

namespace EtaQSeries

def f (N : ℕ) : PowerSeries ℤ :=
  ∏ n ∈ Finset.range N, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))

def Cong (m : ℕ) (G : PowerSeries ℤ) : Prop := (PowerSeries.X : PowerSeries ℤ) ^ (m + 1) ∣ G - 1

theorem Cong.mul {m : ℕ} {G H : PowerSeries ℤ} (hG : Cong m G) (hH : Cong m H) : Cong m (G * H) := by
  have : G * H - 1 = (G - 1) * H + (H - 1) := by ring
  rw [Cong, this]
  exact dvd_add (hG.mul_right _) hH

theorem Cong.one (m : ℕ) : Cong m 1 := by simp [Cong]

theorem Cong.pow {m : ℕ} {G : PowerSeries ℤ} (hG : Cong m G) (a : ℕ) : Cong m (G ^ a) := by
  induction a with
  | zero => simpa using Cong.one m
  | succ a ih => rw [pow_succ]; exact ih.mul hG

theorem Cong.prod {m : ℕ} {ι : Type*} (s : Finset ι) {g : ι → PowerSeries ℤ}
    (hg : ∀ i ∈ s, Cong m (g i)) : Cong m (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Cong.one m
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (hg i (Finset.mem_insert_self i s)).mul (ih fun j hj => hg j (Finset.mem_insert_of_mem hj))

theorem Cong.one_sub_X_pow {m n : ℕ} (hn : m + 1 ≤ n + 1) : Cong m (1 - PowerSeries.X ^ (n + 1)) := by
  rw [Cong, sub_sub_cancel_left, dvd_neg]
  exact pow_dvd_pow _ hn

theorem coeff_mul_of_cong {m : ℕ} {G : PowerSeries ℤ} (hG : Cong m G) (H : PowerSeries ℤ) :
    PowerSeries.coeff m (H * G) = PowerSeries.coeff m H := by
  obtain ⟨K, hK⟩ := hG
  have : G = 1 + PowerSeries.X ^ (m + 1) * K := by rw [← hK]; ring
  rw [this, mul_add, mul_one, map_add, ← mul_assoc, mul_comm H, mul_assoc,
    PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega), add_zero]

theorem coeff_prod_pow_eq (a m : ℕ) (s : Finset ℕ) (hs : Finset.range (m + 1) ⊆ s) :
    PowerSeries.coeff m ((∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) ^ a) =
      PowerSeries.coeff m (f (m + 1) ^ a) := by
  rw [← Finset.prod_sdiff hs, mul_pow, mul_comm, f]
  apply coeff_mul_of_cong
  apply Cong.pow
  apply Cong.prod
  intro n hn
  rw [Finset.mem_sdiff, Finset.mem_range, not_lt] at hn
  exact Cong.one_sub_X_pow (by omega)

theorem coeff_etaProd_pow (a m : ℕ) :
    PowerSeries.coeff m (etaProd ^ a) = PowerSeries.coeff m (f (m + 1) ^ a) := by
  have hmult := PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ
  have h1 : Tendsto (fun s : Finset ℕ => ∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1)))
      atTop (𝓝 etaProd) := hmult.hasProd
  have h2 : Tendsto (fun s : Finset ℕ =>
      PowerSeries.coeff m ((∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) ^ a)) atTop
      (𝓝 (PowerSeries.coeff m (etaProd ^ a))) :=
    ((PowerSeries.WithPiTopology.continuous_coeff ℤ m).tendsto _).comp (h1.pow a)
  have h3 : Tendsto (fun s : Finset ℕ =>
      PowerSeries.coeff m ((∏ n ∈ s, ((1 : PowerSeries ℤ) - PowerSeries.X ^ (n + 1))) ^ a)) atTop
      (𝓝 (PowerSeries.coeff m (f (m + 1) ^ a))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (Finset.range (m + 1))] with s hs
    exact (coeff_prod_pow_eq a m s hs).symm
  exact tendsto_nhds_unique h2 h3

theorem coeff_etaProd_pow_eq_coeff_f (a m N : ℕ) (hN : m < N) :
    PowerSeries.coeff m (etaProd ^ a) = PowerSeries.coeff m (f N ^ a) := by
  rw [coeff_etaProd_pow]
  exact (coeff_prod_pow_eq a m (Finset.range N) (Finset.range_subset_range.mpr hN)).symm

def p (N : ℕ) : Polynomial ℤ :=
  ∏ n ∈ Finset.range N, ((1 : Polynomial ℤ) - Polynomial.X ^ (n + 1))

theorem coe_p (N : ℕ) : ((p N : Polynomial ℤ) : PowerSeries ℤ) = f N := by
  rw [p, f, ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl (fun n _ => ?_)
  rw [map_sub, map_one, map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem coeff_f_pow (a N m : ℕ) : PowerSeries.coeff m (f N ^ a) = (p N ^ a).coeff m := by
  rw [← Polynomial.coeff_coe, Polynomial.coe_pow, coe_p]

theorem eval₂_p_pow (a N : ℕ) (q : ℂ) :
    (p N ^ a).eval₂ (Int.castRingHom ℂ) q = (∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ a := by
  rw [Polynomial.eval₂_pow, p, Polynomial.eval₂_finsetProd]
  simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow]

theorem hasSum_partial (a N : ℕ) (q : ℂ) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (f N ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ a) := by
  rw [← eval₂_p_pow, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  simp_rw [coeff_f_pow]
  apply hasSum_sum_of_ne_finset_zero
  intro m hm
  rw [Polynomial.notMem_support_iff.mp hm, Int.cast_zero, zero_mul]

def Maj (φ : Polynomial ℤ) (Φ : Polynomial ℝ) : Prop := ∀ m, |((φ.coeff m : ℤ) : ℝ)| ≤ Φ.coeff m

theorem Maj.nonneg {φ : Polynomial ℤ} {Φ : Polynomial ℝ} (h : Maj φ Φ) (m : ℕ) : 0 ≤ Φ.coeff m :=
  (abs_nonneg _).trans (h m)

theorem Maj.mul {φ ψ : Polynomial ℤ} {Φ Ψ : Polynomial ℝ} (hφ : Maj φ Φ) (hψ : Maj ψ Ψ) :
    Maj (φ * ψ) (Φ * Ψ) := by
  intro m
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul, Int.cast_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [Int.cast_mul, abs_mul]
  exact mul_le_mul (hφ _) (hψ _) (abs_nonneg _) (hφ.nonneg _)

theorem Maj.one : Maj 1 1 := by
  intro m
  rw [Polynomial.coeff_one, Polynomial.coeff_one]
  split_ifs <;> simp

theorem Maj.pow {φ : Polynomial ℤ} {Φ : Polynomial ℝ} (h : Maj φ Φ) (a : ℕ) : Maj (φ ^ a) (Φ ^ a) := by
  induction a with
  | zero => simpa using Maj.one
  | succ a ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem Maj.prod {ι : Type*} (s : Finset ι) {φ : ι → Polynomial ℤ} {Φ : ι → Polynomial ℝ}
    (h : ∀ i ∈ s, Maj (φ i) (Φ i)) : Maj (∏ i ∈ s, φ i) (∏ i ∈ s, Φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Maj.one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem Maj.one_sub_X_pow (k : ℕ) : Maj (1 - Polynomial.X ^ k) (1 + Polynomial.X ^ k) := by
  intro m
  simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X_pow, Int.cast_sub]
  refine (abs_sub _ _).trans ?_
  split_ifs <;> simp

def P (N : ℕ) : Polynomial ℝ := ∏ n ∈ Finset.range N, ((1 : Polynomial ℝ) + Polynomial.X ^ (n + 1))

theorem maj_p_pow (a N : ℕ) : Maj (p N ^ a) (P N ^ a) :=
  (Maj.prod (Finset.range N) fun n _ => Maj.one_sub_X_pow (n + 1)).pow a

theorem eval_P_pow (a N : ℕ) (r : ℝ) : (P N ^ a).eval r = (∏ n ∈ Finset.range N, (1 + r ^ (n + 1))) ^ a := by
  rw [Polynomial.eval_pow, P, Polynomial.eval_prod]
  simp

theorem coeff_mul_pow_le_eval {Φ : Polynomial ℝ} (hΦ : ∀ m, 0 ≤ Φ.coeff m) {r : ℝ} (hr : 0 ≤ r)
    (m : ℕ) : Φ.coeff m * r ^ m ≤ Φ.eval r := by
  rw [Polynomial.eval_eq_sum_range' (n := max (Φ.natDegree + 1) (m + 1))
    (lt_max_of_lt_left (Nat.lt_succ_self _))]
  refine Finset.single_le_sum (f := fun i => Φ.coeff i * r ^ i)
    (fun i _ => mul_nonneg (hΦ i) (pow_nonneg hr i))
    (Finset.mem_range.mpr (lt_max_of_lt_right (Nat.lt_succ_self m)))

theorem prod_one_add_le_exp {N : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∏ n ∈ Finset.range N, (1 + r ^ (n + 1)) ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) := by
  have hsum : Summable (fun n : ℕ => r ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
  calc ∏ n ∈ Finset.range N, (1 + r ^ (n + 1)) ≤ ∏ n ∈ Finset.range N, Real.exp (r ^ (n + 1)) :=
        Finset.prod_le_prod₀ (fun n _ => by positivity) (fun n _ => by
          have := Real.add_one_le_exp (r ^ (n + 1)); linarith)
    _ = Real.exp (∑ n ∈ Finset.range N, r ^ (n + 1)) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) :=
        Real.exp_le_exp.mpr (hsum.sum_le_tsum _ (fun n _ => pow_nonneg hr0 _))

theorem norm_coeff_f_pow_mul_le (a N m : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * r ^ m ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) ^ a := by
  have hmaj := maj_p_pow a N
  calc |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * r ^ m ≤ (P N ^ a).coeff m * r ^ m := by
        rw [coeff_f_pow]; exact mul_le_mul_of_nonneg_right (hmaj m) (pow_nonneg hr0 m)
    _ ≤ (P N ^ a).eval r := coeff_mul_pow_le_eval hmaj.nonneg hr0 m
    _ = (∏ n ∈ Finset.range N, (1 + r ^ (n + 1))) ^ a := eval_P_pow a N r
    _ ≤ Real.exp (∑' n : ℕ, r ^ (n + 1)) ^ a :=
        pow_le_pow_left₀ (Finset.prod_nonneg fun n _ => by positivity) (prod_one_add_le_exp hr0 hr1) a

end EtaQSeries

open EtaQSeries

/-- The pin's `hasSum_coeff_etaProd_pow`
(`Theorems/Thm_ModularCurve_hasSum_coeff_etaProd_pow.lean`): on the open unit disc, the
`q`-series of `etaProd ^ a` sums to `(∏' n, (1 - q ^ (n + 1))) ^ a`. This is the pin's
`EtaQSeries.main`, stated once, at the wrapper's name. -/
theorem hasSum_coeff_etaProd_pow (a : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m)
      ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a) := by
  set r : ℝ := (‖q‖ + 1) / 2 with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hqr : ‖q‖ < r := by rw [hr]; linarith
  have hr1 : r < 1 := by rw [hr]; linarith
  have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg q) hqr
  set ρ : ℝ := ‖q‖ / r with hρ
  have hρ0 : 0 ≤ ρ := div_nonneg (norm_nonneg q) hr0
  have hρ1 : ρ < 1 := (div_lt_one hrpos).mpr hqr
  set C : ℝ := Real.exp (∑' n : ℕ, r ^ (n + 1)) ^ a with hC

  let F : ℕ → ℕ → ℂ := fun N m => ((PowerSeries.coeff m (f N ^ a) : ℤ) : ℂ) * q ^ m
  let g : ℕ → ℂ := fun m => ((PowerSeries.coeff m (etaProd ^ a) : ℤ) : ℂ) * q ^ m
  have hbound : ∀ N m, ‖F N m‖ ≤ C * ρ ^ m := by
    intro N m
    have h1 := norm_coeff_f_pow_mul_le a N m hr0 hr1
    have hqm : ‖q‖ ^ m = r ^ m * ρ ^ m := by
      rw [← mul_pow, hρ, mul_div_cancel₀ _ hrpos.ne']
    calc ‖F N m‖ = |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * ‖q‖ ^ m := by
          simp only [F, norm_mul, norm_pow, Complex.norm_intCast]
      _ = |((PowerSeries.coeff m (f N ^ a) : ℤ) : ℝ)| * r ^ m * ρ ^ m := by rw [hqm, mul_assoc]
      _ ≤ C * ρ ^ m := mul_le_mul_of_nonneg_right h1 (pow_nonneg hρ0 m)
  have hsumm : Summable (fun m : ℕ => C * ρ ^ m) :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left C
  have hlim : ∀ m, Tendsto (fun N => F N m) atTop (𝓝 (g m)) := by
    intro m
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop m] with N hN
    simp only [F, g, coeff_etaProd_pow_eq_coeff_f a m N hN]

  have hT : Tendsto (fun N => ∑' m, F N m) atTop (𝓝 (∑' m, g m)) :=
    tendsto_tsum_of_dominated_convergence hsumm hlim (Eventually.of_forall hbound)

  have hP : ∀ N, ∑' m, F N m = (∏ n ∈ Finset.range N, (1 - q ^ (n + 1))) ^ a :=
    fun N => (hasSum_partial a N q).tsum_eq
  have hA : Tendsto (fun N => ∑' m, F N m) atTop (𝓝 ((∏' n : ℕ, (1 - q ^ (n + 1))) ^ a)) := by
    simp_rw [hP]
    exact ((ModularForm.multipliable_one_sub_pow hq).hasProd.tendsto_prod_nat).pow a
  have heq : ∑' m, g m = (∏' n : ℕ, (1 - q ^ (n + 1))) ^ a := tendsto_nhds_unique hT hA

  have hg : Summable g := by
    refine Summable.of_norm_bounded hsumm (fun m => ?_)
    have := hbound (m + 1) m
    simpa only [F, g, coeff_etaProd_pow_eq_coeff_f a m (m + 1) (Nat.lt_succ_self m)] using this
  rw [← heq]
  exact hg.hasSum

end ModularCurve

end
