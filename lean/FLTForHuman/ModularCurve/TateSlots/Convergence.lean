/-
  The valued platform and the `W4B` convergence / geometric-series layer of the
  Tate-slot weight-4 engine: the rank-one discrete valuation on `LaurentSeries K`
  (`rankOneLaurent`, `w4bNormed`, `tateQ`), the convergence criterion
  `tsum_of_coeff_lt_eq_zero` with its `hasSum` / `summable` forms, the geometric
  series `geomPS` / `Qp` / `coeff_Qp_pow_div_one_sub`, and the Lambert term
  `lambertTerm` with `tsum_lambertTerm_eq`.

  FLT provenance, pinned `aa2d8b3`: the shared development carried by the
  fourteen `P2M/Sol/S_ModularCurve_*.lean` files; the representative
  transcription source is
  `P2M/Sol/S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean` (1,649 lines), sections
  `Seam` (286–298), `Kit` (300–378), `Platform` (380–421), `W4B` (430–483),
  `W4B.B2.GeomPS` (489–525), `W4B.B2.GeomLS` (528–604), `W4B.B2.Lambert`
  (607–733).
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean

  Transcribed whole (playbook §2.3); the pin's `p2m_export` / `p2m_open` /
  `p2m_reactivate` lines are dropped, together with the outer
  `P2MW.S_ModularCurve_tsum_of_coeff_lt_eq_zero` frame — `Defs/TateSlots.lean`
  already provides the definitions in `ModularCurve`. The two headline kernels
  are promoted to public
  `ModularCurve.TateSlots.{tsum_of_coeff_lt_eq_zero,tsum_lambertTerm_eq}` with the
  binders of their `Theorems/` wrappers. The pin's duplicate
  `ofPowerSeries_coeff_neg` / `ofPowerSeries_coeff_int` is written once here (in
  the `W4B.B2.GeomLS` block), per the work order §3.4.
-/
import FLTForHuman.ModularCurve.Defs.TateSlots
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve

section Seam

variable (K : Type*) [Field K]

-- pin: isRankOneDiscrete_valued (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:290)
theorem isRankOneDiscrete_valued :
    (Valued.v : Valuation (LaurentSeries K) (WithZero (Multiplicative ℤ))).IsRankOneDiscrete :=
  (Valuation.IsRankOneDiscrete.mk' _ : ((PowerSeries.idealX K).valuation (LaurentSeries K)).IsRankOneDiscrete)

-- pin: rankOneLaurent (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:294)
abbrev rankOneLaurent : (Valued.v : Valuation (LaurentSeries K) (WithZero (Multiplicative ℤ))).RankOne :=
  haveI := isRankOneDiscrete_valued K
  Valuation.IsRankOneDiscrete.rankOne _ (e := (2 : NNReal)) (by norm_num)

end Seam

section Kit

variable (K : Type*) [Field K]

-- pin: w4bNormed (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:304)
abbrev w4bNormed : NontriviallyNormedField (LaurentSeries K) :=
  @Valued.toNontriviallyNormedField (LaurentSeries K) _ (WithZero (Multiplicative ℤ)) _ _ (rankOneLaurent K)

-- pin: tateQ (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:307)
def tateQ (p : ℕ) : LaurentSeries K := HahnSeries.single (p : ℤ) (1 : K)

variable {K}

-- pin: valued_single_zero_of_ne_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:311)
theorem valued_single_zero_of_ne_zero {c : K} (hc : c ≠ 0) :
    Valued.v (HahnSeries.single (0 : ℤ) c : LaurentSeries K) = 1 := by
  have hle : ∀ {d : K}, Valued.v (HahnSeries.single (0 : ℤ) d : LaurentSeries K) ≤ 1 := by
    intro d
    have h := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K (D := 0)
      (f := (HahnSeries.single (0 : ℤ) d : LaurentSeries K))).mpr
      (fun n hn => HahnSeries.coeff_single_of_ne hn.ne)
    simpa using h
  have hmul : (HahnSeries.single (0 : ℤ) c : LaurentSeries K) * HahnSeries.single (0 : ℤ) c⁻¹ = 1 := by
    rw [HahnSeries.single_mul_single, add_zero, mul_inv_cancel₀ hc]
    rfl
  have h1 : Valued.v (HahnSeries.single (0 : ℤ) c : LaurentSeries K) *
      Valued.v (HahnSeries.single (0 : ℤ) c⁻¹ : LaurentSeries K) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have : Valued.v (HahnSeries.single (0 : ℤ) c : LaurentSeries K) *
      Valued.v (HahnSeries.single (0 : ℤ) c⁻¹ : LaurentSeries K) < 1 :=
    calc _ ≤ Valued.v (HahnSeries.single (0 : ℤ) c : LaurentSeries K) * 1 := mul_le_mul_right hle _
      _ = _ := mul_one _
      _ < 1 := hlt
  exact absurd h1 this.ne

-- pin: valued_single_of_ne_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:335)
theorem valued_single_of_ne_zero (n : ℤ) {c : K} (hc : c ≠ 0) :
    Valued.v (HahnSeries.single n c : LaurentSeries K) = WithZero.exp (-n) := by
  have h : (HahnSeries.single n c : LaurentSeries K) =
      HahnSeries.single n (1 : K) * HahnSeries.single (0 : ℤ) c := by
    rw [HahnSeries.single_mul_single, add_zero, one_mul]
  rw [h, map_mul, LaurentSeries.valuation_single_zpow, valued_single_zero_of_ne_zero hc, mul_one]

-- pin: tateQ_ne_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:342)
theorem tateQ_ne_zero (p : ℕ) : tateQ K p ≠ 0 := HahnSeries.single_ne_zero one_ne_zero

-- pin: valued_tateQ (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:344)
theorem valued_tateQ (p : ℕ) : Valued.v (tateQ K p) = WithZero.exp (-(p : ℤ)) :=
  LaurentSeries.valuation_single_zpow K (p : ℤ)

-- pin: valued_tateQ_zpow_mul_single (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:347)
theorem valued_tateQ_zpow_mul_single (p : ℕ) (n j : ℤ) {c : K} (hc : c ≠ 0) :
    Valued.v (tateQ K p ^ n * HahnSeries.single j c) = WithZero.exp (-((p : ℤ) * n + j)) := by
  rw [map_mul, map_zpow₀, valued_tateQ, valued_single_of_ne_zero j hc, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  congr 1
  simp only [smul_eq_mul]
  ring

-- pin: tateQ_zpow_mul_single_ne_one_of_pos (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:354)
theorem tateQ_zpow_mul_single_ne_one_of_pos {p j : ℕ} (hj : 0 < j) (hjp : j < p) {c : K} (hc : c ≠ 0)
    (n : ℤ) : tateQ K p ^ n * HahnSeries.single (j : ℤ) c ≠ 1 := by
  intro h
  have hv := valued_tateQ_zpow_mul_single p n (j : ℤ) hc
  rw [h, map_one, eq_comm, WithZero.exp_eq_one, neg_eq_zero] at hv
  rcases le_or_gt 0 n with hn | hn
  · have : (0 : ℤ) ≤ (p : ℤ) * n := mul_nonneg (by positivity) hn
    omega
  · have : (p : ℤ) * n ≤ -(p : ℤ) := by nlinarith
    omega

-- pin: tateQ_zpow_mul_single_zero_ne_one (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:365)
theorem tateQ_zpow_mul_single_zero_ne_one {p : ℕ} [NeZero p] {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (n : ℤ) :
    tateQ K p ^ n * HahnSeries.single (0 : ℤ) c ≠ 1 := by
  intro h
  have hv := valued_tateQ_zpow_mul_single p n 0 hc0
  rw [h, map_one, eq_comm, WithZero.exp_eq_one, neg_eq_zero, add_zero, mul_eq_zero] at hv
  rcases hv with hp | hn
  · exact (NeZero.ne p) (by exact_mod_cast hp)
  · subst hn
    rw [zpow_zero, one_mul] at h
    apply hc1
    have := congrArg (fun f : LaurentSeries K => f.coeff (0 : ℤ)) h
    simpa using this

end Kit

section Platform

attribute [local instance] rankOneLaurent w4bNormed

variable {K : Type*} [Field K]

example : IsUltrametricDist (LaurentSeries K) := inferInstance
example : CompleteSpace (LaurentSeries K) := inferInstance
example : (w4bNormed K).toField = (inferInstance : Field (LaurentSeries K)) := rfl

-- pin: charZero_laurentSeries (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:390)
theorem charZero_laurentSeries [CharZero K] : CharZero (LaurentSeries K) :=
  charZero_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective

-- pin: nnnorm_lt_one_iff_valued (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:393)
theorem nnnorm_lt_one_iff_valued (x : LaurentSeries K) : ‖x‖₊ < 1 ↔ Valued.v x < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
  exact Valued.toNormedField.norm_lt_one_iff

-- pin: exp_neg_lt_one (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:397)
theorem exp_neg_lt_one {m : ℤ} (hm : 0 < m) : WithZero.exp (-m) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

-- pin: nnnorm_tateQ_lt_one (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:401)
theorem nnnorm_tateQ_lt_one (p : ℕ) [NeZero p] : ‖tateQ K p‖₊ < 1 := by
  rw [nnnorm_lt_one_iff_valued, valued_tateQ]
  exact exp_neg_lt_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p))

-- pin: nnnorm_tateQ_mul_single_lt_one (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:405)
theorem nnnorm_tateQ_mul_single_lt_one (p : ℕ) [NeZero p] (j : ℕ) {c : K} (hc : c ≠ 0) :
    ‖tateQ K p * HahnSeries.single (j : ℤ) c‖₊ < 1 := by
  rw [nnnorm_lt_one_iff_valued]
  have := valued_tateQ_zpow_mul_single (K := K) p 1 (j : ℤ) hc
  rw [zpow_one] at this
  rw [this]
  exact exp_neg_lt_one (by have := Nat.pos_of_ne_zero (NeZero.ne p); omega)

-- pin: nnnorm_tateQ_mul_single_inv_lt_one (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:413)
theorem nnnorm_tateQ_mul_single_inv_lt_one (p : ℕ) [NeZero p] {j : ℕ} (hjp : j < p) {c : K} (hc : c ≠ 0) :
    ‖tateQ K p * (HahnSeries.single (j : ℤ) c)⁻¹‖₊ < 1 := by
  rw [nnnorm_lt_one_iff_valued, HahnSeries.inv_single]
  have := valued_tateQ_zpow_mul_single (K := K) p 1 (-(j : ℤ)) (inv_ne_zero hc)
  rw [zpow_one] at this
  rw [this]
  exact exp_neg_lt_one (by omega)

end Platform

open WithZero Filter Finset Topology

namespace W4B

variable {K : Type*} [Field K]

-- pin: hasSum_of_coeff_lt_eq_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:434)
theorem hasSum_of_coeff_lt_eq_zero {δ : ℕ} (hδ : 0 < δ)
    (f : ℕ → LaurentSeries K)
    (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0)
    (g : LaurentSeries K)
    (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) :
    HasSum f g := by
  have key : ∀ (k : ℕ) (s : Finset ℕ), Finset.range (k + 1) ⊆ s →
      Valued.v ((∑ N ∈ s, f N) - g) ≤ exp (-(k : ℤ)) := by
    intro k s hs
    refine (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).mpr fun m hm => ?_
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_sum, hg m, sub_eq_zero]
    have hmk : m.toNat ≤ k := by omega
    refine (Finset.sum_subset (fun N hN => hs ?_) (fun N _ hN => hf N m ?_)).symm
    · rw [Finset.mem_range] at hN ⊢
      exact hN.trans_le (Nat.add_le_add_right ((Nat.div_le_self _ _).trans hmk) 1)
    · rw [Finset.mem_range, not_lt] at hN
      have h3 : m.toNat < N * δ := (Nat.div_lt_iff_lt_mul hδ).mp (Nat.lt_of_succ_le hN)
      calc (m : ℤ) ≤ (m.toNat : ℤ) := Int.self_le_toNat m
        _ < ((N * δ : ℕ) : ℤ) := by exact_mod_cast h3
        _ = (N : ℤ) * (δ : ℤ) := by push_cast; ring
  show Tendsto (fun s : Finset ℕ => ∑ N ∈ s, f N) atTop (𝓝 g)
  rw [← tendsto_sub_nhds_zero_iff,
    (Valued.hasBasis_nhds_zero (LaurentSeries K) ℤᵐ⁰).tendsto_right_iff]
  intro γ _
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 := by
    simp
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt hγ0
  refine Filter.eventually_atTop.mpr ⟨Finset.range (k + 1), fun s hs => ?_⟩
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
  exact (key k s hs).trans_lt hk

-- pin: summable_of_coeff_lt_eq_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:465)
theorem summable_of_coeff_lt_eq_zero {δ : ℕ} (hδ : 0 < δ)
    (f : ℕ → LaurentSeries K)
    (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0)
    (g : LaurentSeries K)
    (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) :
    Summable f :=
  ⟨g, hasSum_of_coeff_lt_eq_zero hδ f hf g hg⟩

end W4B

namespace W4B

namespace B2

section GeomPS

variable (K : Type*) [CommRing K]

-- pin: geomPS (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:492)
def geomPS (d : ℕ) : PowerSeries K := PowerSeries.mk fun m => if d ∣ m then 1 else 0

-- pin: coeff_geomPS (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:494)
theorem coeff_geomPS (d m : ℕ) : PowerSeries.coeff m (geomPS K d) = if d ∣ m then 1 else 0 :=
  PowerSeries.coeff_mk m _

-- pin: dvd_sub_iff_of_le (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:497)
private theorem dvd_sub_iff_of_le {d m : ℕ} (h : d ≤ m) : d ∣ (m - d) ↔ d ∣ m := by
  constructor
  · intro hd; have := hd.add (dvd_refl d); rwa [Nat.sub_add_cancel h] at this
  · intro hd; exact Nat.dvd_sub hd (dvd_refl d)

-- pin: one_sub_X_pow_mul_geomPS (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:502)
theorem one_sub_X_pow_mul_geomPS (d : ℕ) (hd : 0 < d) :
    (1 - (PowerSeries.X : PowerSeries K) ^ d) * geomPS K d = 1 := by
  ext m
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_geomPS, coeff_geomPS,
    PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hd.not_ge]
  · rw [ite_eq_right hm.ne']
    rcases le_or_gt d m with hdm | hdm
    · simp only [ite_eq_left hdm, dvd_sub_iff_of_le hdm]
      split_ifs <;> ring
    · rw [ite_eq_right hdm.not_ge, ite_eq_right (fun h => hdm.not_ge (Nat.le_of_dvd hm h))]
      ring

-- pin: coeff_X_pow_mul_geomPS (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:516)
theorem coeff_X_pow_mul_geomPS (d : ℕ) (m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.X : PowerSeries K) ^ d * geomPS K d)
      = if d ∣ m ∧ d ≤ m then 1 else 0 := by
  rw [coeff_X_pow_mul', coeff_geomPS]
  rcases le_or_gt d m with hdm | hdm
  · rw [ite_eq_left hdm]
    simp only [dvd_sub_iff_of_le hdm, hdm, and_true]
  · rw [ite_eq_right hdm.not_ge, ite_eq_right (fun h => hdm.not_ge h.2)]

end GeomPS

section GeomLS

variable (K : Type*) [Field K]

-- pin: Qp (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:531)
abbrev Qp (p : ℕ) : LaurentSeries K := HahnSeries.single (p : ℤ) (1 : K)

-- pin: Qp_pow_eq_ofPowerSeries (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:533)
theorem Qp_pow_eq_ofPowerSeries (p n : ℕ) :
    (Qp K p) ^ n = HahnSeries.ofPowerSeries ℤ K ((PowerSeries.X) ^ (p * n)) := by
  rw [HahnSeries.ofPowerSeries_X_pow, Qp]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, HahnSeries.single_mul_single, one_mul]
    push_cast; ring_nf

-- pin: one_sub_Qp_pow_ne_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:542)
theorem one_sub_Qp_pow_ne_zero (p n : ℕ) (hpn : 0 < p * n) :
    (1 : LaurentSeries K) - (Qp K p) ^ n ≠ 0 := by
  intro h
  have hc : ((1 : LaurentSeries K) - (Qp K p) ^ n).coeff 0 = 0 := by rw [h]; rfl
  rw [Qp_pow_eq_ofPowerSeries, HahnSeries.ofPowerSeries_X_pow, HahnSeries.coeff_sub,
    HahnSeries.coeff_one, ite_eq_left rfl, HahnSeries.coeff_single,
    ite_eq_right (by exact_mod_cast hpn.ne), sub_zero] at hc
  exact one_ne_zero hc

-- pin: Qp_pow_div_one_sub_eq (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:551)
theorem Qp_pow_div_one_sub_eq (p n : ℕ) (hpn : 0 < p * n) :
    (Qp K p) ^ n / (1 - (Qp K p) ^ n)
      = HahnSeries.ofPowerSeries ℤ K ((PowerSeries.X) ^ (p * n) * geomPS K (p * n)) := by
  rw [div_eq_iff (one_sub_Qp_pow_ne_zero K p n hpn), Qp_pow_eq_ofPowerSeries,
    show (1 : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K 1 from (map_one _).symm,
    ← map_sub, ← map_mul]
  congr 1
  rw [mul_assoc, mul_comm (geomPS K (p * n)), one_sub_X_pow_mul_geomPS K (p * n) hpn, mul_one]

-- pin: ofPowerSeries_coeff_neg (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:560)
theorem ofPowerSeries_coeff_neg (f : PowerSeries K) (m : ℤ) (hm : m < 0) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff m = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨n, hn⟩
  have : (n : ℤ) = m := hn
  omega

-- pin: ofPowerSeries_coeff_int (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:568)
theorem ofPowerSeries_coeff_int (f : PowerSeries K) (m : ℤ) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff m
      = if 0 ≤ m then PowerSeries.coeff m.toNat f else 0 := by
  split_ifs with h
  · conv_lhs => rw [show m = ((m.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm]
    exact HahnSeries.ofPowerSeries_apply_coeff f m.toNat
  · exact ofPowerSeries_coeff_neg K f m (not_le.mp h)

-- pin: coeff_Qp_pow_div_one_sub (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:576)
theorem coeff_Qp_pow_div_one_sub (p n : ℕ) [NeZero p] (hn : 0 < n) (m : ℤ) :
    ((Qp K p) ^ n / (1 - (Qp K p) ^ n)).coeff m
      = if ((p * n : ℤ) ∣ m ∧ (p * n : ℤ) ≤ m) then 1 else 0 := by
  have hpn : 0 < p * n := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne p)) hn
  rw [Qp_pow_div_one_sub_eq K p n hpn, ofPowerSeries_coeff_int, coeff_X_pow_mul_geomPS]
  rcases lt_or_ge m 0 with hm | hm
  · rw [ite_eq_right (not_le.mpr hm), ite_eq_right]
    rintro ⟨-, h⟩
    exact absurd (h.trans hm.le) (by exact_mod_cast hpn.not_ge)
  · rw [ite_eq_left hm]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨⟨k, hk⟩, h2⟩
      refine ⟨⟨(k : ℤ), ?_⟩, by omega⟩
      have : m = ((p * n * k : ℕ) : ℤ) := by rw [← hk, Int.toNat_of_nonneg hm]
      push_cast at this; linarith
    · rintro ⟨⟨k, hk⟩, h2⟩
      have hk0 : 0 ≤ k := by
        rcases lt_or_ge k 0 with hk0 | hk0
        · exfalso
          have : m < 0 := hk ▸ mul_neg_of_pos_of_neg (by exact_mod_cast hpn) hk0
          omega
        · exact hk0
      refine ⟨⟨k.toNat, ?_⟩, by omega⟩
      have : m = ((p * n * k.toNat : ℕ) : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg hk0]; linarith
      omega

end GeomLS

section Lambert

variable (K : Type*) [Field K]

-- pin: lambertTerm (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:610)
def lambertTerm (p : ℕ) (c : ℕ → ℕ) (n : ℕ) : LaurentSeries K :=
  (c n : LaurentSeries K) * ((Qp K p) ^ n / (1 - (Qp K p) ^ n))

-- pin: lambertTerm_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:613)
theorem lambertTerm_zero (p : ℕ) (c : ℕ → ℕ) : lambertTerm K p c 0 = 0 := by
  simp [lambertTerm]

-- pin: coeff_lambertTerm (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:616)
theorem coeff_lambertTerm (p : ℕ) [NeZero p] (c : ℕ → ℕ) (n : ℕ) (hn : 0 < n) (m : ℤ) :
    (lambertTerm K p c n).coeff m
      = if ((p * n : ℤ) ∣ m ∧ (p * n : ℤ) ≤ m) then (c n : K) else 0 := by
  rw [lambertTerm, ← HahnSeries.single_zero_natCast, HahnSeries.coeff_single_zero_mul,
    coeff_Qp_pow_div_one_sub K p n hn m]
  split_ifs <;> simp

-- pin: coeff_lambertTerm_eq_zero_of_lt (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:623)
theorem coeff_lambertTerm_eq_zero_of_lt (p : ℕ) [NeZero p] (c : ℕ → ℕ) (n : ℕ) (m : ℤ)
    (hm : m < (n : ℤ) * (p : ℤ)) : (lambertTerm K p c n).coeff m = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [lambertTerm_zero]; rfl
  · rw [coeff_lambertTerm K p c n hn m, ite_eq_right]
    rintro ⟨-, h2⟩
    have hc : (n : ℤ) * (p : ℤ) = ((p * n : ℕ) : ℤ) := by push_cast; ring
    omega

-- pin: coeff_qExpand_laurentOfInt (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:632)
theorem coeff_qExpand_laurentOfInt (p : ℕ) [NeZero p] (φ : PowerSeries ℤ) (m : ℤ) :
    (qExpand K p (laurentOfInt K φ)).coeff m
      = if ((p : ℤ) ∣ m ∧ 0 ≤ m) then ((PowerSeries.coeff (m.toNat / p) φ : ℤ) : K) else 0 := by
  by_cases hdvd : (p : ℤ) ∣ m
  · obtain ⟨k, hk⟩ := hdvd
    have hp : 0 < (p : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    rw [hk, qExpand_coeff_mul, laurentOfInt_apply, ofPowerSeries_coeff_int, PowerSeries.coeff_map]
    congr 1
    · refine propext ⟨fun hk0 => ⟨⟨k, rfl⟩, by positivity⟩, fun ⟨_, hm0⟩ => ?_⟩
      exact (mul_nonneg_iff_of_pos_left hp).mp hm0
    · have hk' : ((p : ℤ) * k).toNat = p * k.toNat := by
        rcases le_or_gt 0 k with h | h
        · have heq : (p : ℤ) * k = ((p * k.toNat : ℕ) : ℤ) := by
            push_cast; rw [Int.toNat_of_nonneg h]
          omega
        · have hneg : (p : ℤ) * k < 0 := mul_neg_of_pos_of_neg hp h
          simp [Int.toNat_of_nonpos hneg.le, Int.toNat_of_nonpos h.le]
      rw [hk', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne p))]
      rfl
  · rw [qExpand_coeff_of_not_dvd _ _ hdvd, ite_eq_right (fun h => hdvd h.1)]

-- pin: range_dvd_sum_eq_divisors_sum (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:653)
theorem range_dvd_sum_eq_divisors_sum (k : ℕ) (c : ℕ → ℕ) :
    (∑ N ∈ Finset.range (k + 1), if (N ∣ k ∧ 1 ≤ N) then (c N : K) else 0)
      = ∑ d ∈ k.divisors, (c d : K) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext N
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨_, hd, h1⟩; exact ⟨hd, fun hk0 => by omega⟩
  · rintro ⟨hd, hk0⟩
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (fun h => hk0 (zero_dvd_iff.mp (h ▸ hd)))
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hd), hd, hN1⟩

end Lambert

end B2

end W4B

namespace TateSlots

-- pin: W4B.tsum_of_coeff_lt_eq_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:475)
theorem tsum_of_coeff_lt_eq_zero {K : Type*} [Field K] {δ : ℕ} (hδ : 0 < δ)
    (f : ℕ → LaurentSeries K)
    (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0)
    (g : LaurentSeries K)
    (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) :
    ∑' N, f N = g :=
  (W4B.hasSum_of_coeff_lt_eq_zero hδ f hf g hg).tsum_eq

-- pin: W4B.B2.tsum_lambertTerm_eq (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:666)
theorem tsum_lambertTerm_eq (K : Type*) [Field K] (p : ℕ) [NeZero p] (c : ℕ → ℕ) :
    ∑' n : ℕ, ((c n : ℕ) : LaurentSeries K) *
        ((HahnSeries.single (p : ℤ) (1 : K)) ^ n / (1 - (HahnSeries.single (p : ℤ) (1 : K)) ^ n)) =
      qExpand K p (laurentOfInt K (PowerSeries.mk fun m => ∑ d ∈ m.divisors, (c d : ℤ))) := by
  change ∑' n, W4B.B2.lambertTerm K p c n
      = qExpand K p (laurentOfInt K (PowerSeries.mk fun m => ∑ d ∈ m.divisors, (c d : ℤ)))
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  refine tsum_of_coeff_lt_eq_zero (K := K) hp _ (W4B.B2.coeff_lambertTerm_eq_zero_of_lt K p c) _ ?_
  intro m
  rw [W4B.B2.coeff_qExpand_laurentOfInt, PowerSeries.coeff_mk]
  rcases lt_or_ge m 0 with hm | hm
  · rw [ite_eq_right (fun h => absurd h.2 (not_le.mpr hm))]
    simp only [Int.toNat_of_nonpos hm.le, Nat.zero_div, zero_add, Finset.range_one,
      Finset.sum_singleton, W4B.B2.lambertTerm_zero, HahnSeries.coeff_zero]
  · push_cast
    have step : ∀ N ∈ Finset.range (m.toNat / p + 1),
        (W4B.B2.lambertTerm K p c N).coeff m
          = if (N ∣ m.toNat / p ∧ 1 ≤ N ∧ (p : ℤ) ∣ m) then (c N : K) else 0 := by
      intro N hN
      rcases Nat.eq_zero_or_pos N with rfl | hN1
      · simp [W4B.B2.lambertTerm_zero]
      · rw [W4B.B2.coeff_lambertTerm K p c N hN1]
        refine if_congr ?_ rfl rfl
        constructor
        · rintro ⟨⟨k, hk⟩, h2⟩
          have hk0 : 0 ≤ k := by
            by_contra h; push Not at h
            have hneg : m < 0 := hk ▸ mul_neg_of_pos_of_neg
              (mul_pos (by exact_mod_cast hp) (by exact_mod_cast hN1)) h
            omega
          have hmN : m.toNat = p * N * k.toNat := by
            have heq : m = ((p * N * k.toNat : ℕ) : ℤ) := by
              push_cast; rw [Int.toNat_of_nonneg hk0]; linarith
            omega
          refine ⟨⟨k.toNat, ?_⟩, hN1, ⟨(N : ℤ) * k, by rw [hk]; ring⟩⟩
          rw [hmN, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp]
        · rintro ⟨⟨k, hk⟩, -, ⟨k', hk'⟩⟩
          have hk'0 : 0 ≤ k' := by
            by_contra h; push Not at h
            have : m < 0 := hk' ▸ mul_neg_of_pos_of_neg (by exact_mod_cast hp) h
            omega
          have hpd : p ∣ m.toNat := ⟨k'.toNat, by
            have heq : m = ((p * k'.toNat : ℕ) : ℤ) := by
              push_cast; rw [Int.toNat_of_nonneg hk'0]; linarith
            omega⟩
          have hkm : m.toNat = p * (N * k) := by
            rw [← Nat.div_mul_cancel hpd, hk, Nat.mul_comm]
          refine ⟨⟨(k : ℤ), ?_⟩, ?_⟩
          · have heq : m = ((p * N * k : ℕ) : ℤ) := by
              rw [← Int.toNat_of_nonneg hm, hkm]; push_cast; ring
            push_cast at heq ⊢; linarith
          · have hk1 : 1 ≤ k := by
              rcases Nat.eq_zero_or_pos k with rfl | h
              · exfalso
                simp only [mul_zero] at hkm
                rw [Finset.mem_range] at hN
                omega
              · exact h
            have hle : (p * N : ℤ) ≤ ((p * (N * k) : ℕ) : ℤ) := by
              push_cast; nlinarith
            rw [← hkm, Int.toNat_of_nonneg hm] at hle
            linarith
    rw [Finset.sum_congr rfl step]
    by_cases hdvd : (p : ℤ) ∣ m
    · rw [ite_eq_left ⟨hdvd, hm⟩]
      simp only [hdvd, and_true]
      exact (W4B.B2.range_dvd_sum_eq_divisors_sum K (m.toNat / p) c).symm
    · rw [ite_eq_right (fun h => hdvd h.1)]
      exact (Finset.sum_eq_zero fun N _ => ite_eq_right (fun h => hdvd h.2.2)).symm

end TateSlots

end ModularCurve

end
