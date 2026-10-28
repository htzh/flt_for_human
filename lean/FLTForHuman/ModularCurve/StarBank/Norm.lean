/-
  The `StarBank` norm leaves: the `σ`-norm of `Δ`, the total-ramification closure
  of the star datum, and the one-point case.

  ## What this module states

  Three headlines of the pin's `StarBank` subject, over the diamond/star action of
  the `p`-th cyclotomic twists on `j(q) = q⁻¹ + 196744 + ⋯` and on
  `Δ = q · η(q)^24`:

  * `StarBank.deltaNorm` — the product of `Δ` over the `p` twists of `q`, times
    `qExpand (p * p) Δ`, is the `p`-th root of unity `∏ b ∈ range p, ζ ^ b` times
    `qExpand p Δ ^ (p + 1)`. The pin proves it first for the `η`-power (a
    topological-product computation, `etaNorm_powerSeries`) and then moves the
    `q`-shift through `qTwist`/`qExpand`.
  * `StarBank.closure` — over an algebraically closed field, for a `G` with
    `aeval (jqModC K) G · Δ ^ M = 1` (a star datum), the four hypotheses
    (`hstar`, `hR`, `hpress`, `hnorm`) force `G.comp R ∣ C c · G ^ (p + 1)` for
    some `c ≠ 0`: the star polynomial's iterate divides.
  * `StarBank.onePoint` — the one-point case: if `C c · (X - C β₀) ^ M` annihilates
    `Δ` under `aeval (jqModC K)`, then `(jqModC K - C β₀) · Δ` is a constant.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:

  * `P2M/Sol/S_ModularCurve_StarBank_deltaNorm.lean` (471 lines) and
    `Theorems/Thm_ModularCurve_StarBank_deltaNorm.lean`;
  * `P2M/Sol/S_ModularCurve_StarBank_closure.lean` (304 lines) and
    `Theorems/Thm_ModularCurve_StarBank_closure.lean`;
  * `P2M/Sol/S_ModularCurve_StarBank_onePoint.lean` (220 lines) and
    `Theorems/Thm_ModularCurve_StarBank_onePoint.lean`.

  The pin declares each headline `private` in its `S_` file and restates it in the
  public `Theorems/` wrapper (whose statement the checker diffs). This module
  states each **once**, public, at the wrapper's name, with the wrapper's
  statement — the precedent is `ModularPolynomialStarBank.lean`'s `delta_pow_ne`.

  ## Reuse

  The `W1` prelude the pin's `S_` files carry is transcribed here once per lemma a
  row needs, at the pin's names, in the pin's `ModularCurve.W1` namespace; where the
  port already holds a lemma the pin's prelude re-derives `private` in every
  solution file, the port's public home is used and nothing is restated:

  * `jqModC_pow`, `coeff_jqModC_pow_self`, `coeff_jqModC_pow_of_lt` are
    `Defs/JqCoeff.lean`'s (the trio's one home, pin headlines, public there).
  * `algebraMap_laurentSeries_eq_single` is `Defs/Laurent.lean`'s; the `W1`
    `algebraMap_eq_C` (the `HahnSeries.C` spelling the pin's proofs rewrite with)
    is a two-line adapter on it and stays `private`.
  * `coeff_one_mul`, `coeff_one_pow_of_constantCoeff` and `coeff_one_etaProd` of
    the `deltaNorm` prelude feed only the pin's anonymous `example` falsifier
    (its lines 437–452), not the headline: dropped, as the pin's other `example`
    probes are (`ModularPolynomialStarBank.lean` records the same decision for
    `press` and `delta_pow_ne`). `coeff_one_etaProd` is not needed by any row of
    this order, and is not promoted.
  * The pin's three `example` probes (`closure:270`, `onePoint:190`, `onePoint:198`)
    are node-local regression checks of imported lemmas, consumed by nothing:
    dropped.

  ## Assumptions

  `Defs/Twist.lean`'s `qTwist`/`qTwist_coeff`/`qTwist_single`/`qTwist_one_apply`;
  `Defs/Laurent.lean`'s `qExpand`/`qExpand_coeff_mul`/`qExpand_coeff_of_not_dvd`/
  `qExpand_single`/`qExpand_C`/`qExpand_injective`/`qExpand_qExpand`/
  `algebraMap_laurentSeries_eq_single`; `Defs/Jq.lean`'s `etaProd`/`jNum`/
  `constantCoeff_jNum`/`ofPowerSeries_coeff_of_neg`; `Defs/JqCoeff.lean`'s
  `jqModC`/`jqNModC`/`jqModC_pow`/`coeff_jqModC_pow_self`/`coeff_jqModC_pow_of_lt`;
  mathlib's `PowerSeries.WithPiTopology` (`multipliable_one_sub_X_pow`,
  `multipliable_one_add_of_tendsto_order_atTop_nhds_top`, `continuous_coeff`,
  `tendsto_iff_coeff_tendsto`), `PowerSeries.expand`/`rescale`,
  `IsPrimitiveRoot.pow_sub_pow_eq_prod_sub_mul`, the `tprod` API, and the
  `HahnSeries` order/leading-coefficient API.

  spec-pin: Theorems/Thm_ModularCurve_StarBank_deltaNorm.lean
  spec-pin: P2M/Sol/S_ModularCurve_StarBank_deltaNorm.lean
  spec-pin: Theorems/Thm_ModularCurve_StarBank_closure.lean
  spec-pin: P2M/Sol/S_ModularCurve_StarBank_closure.lean
  spec-pin: Theorems/Thm_ModularCurve_StarBank_onePoint.lean
  spec-pin: P2M/Sol/S_ModularCurve_StarBank_onePoint.lean
-/
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Defs.Twist
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

noncomputable section

open scoped PowerSeries.WithPiTopology

namespace ModularCurve

namespace W1

/-! ### `qTwist` and `qExpand` on the `q`-series of a power series -/

theorem qTwist_ofPowerSeries {R : Type*} [CommRing R] (u : Rˣ) (f : PowerSeries R) :
    qTwist u (HahnSeries.ofPowerSeries ℤ R f) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.rescale (u : R) f) := by
  ext k
  rw [qTwist_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_rescale, zpow_natCast, Units.val_pow_eq_pow_val]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, mul_zero]

theorem qExpand_ofPowerSeries {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (f : PowerSeries R) :
    qExpand R N (HahnSeries.ofPowerSeries ℤ R f) =
      HahnSeries.ofPowerSeries ℤ R (PowerSeries.expand N (NeZero.ne N) f) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul]
    rcases le_or_gt 0 m with hm | hm
    · lift m to ℕ using hm
      rw [HahnSeries.ofPowerSeries_apply_coeff,
        show ((N : ℤ) * ((m : ℕ) : ℤ) : ℤ) = ((N * m : ℕ) : ℤ) by push_cast; ring,
        HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_expand_mul]
    · have hneg : (N : ℤ) * m < 0 :=
        mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)) hm
      rw [ofPowerSeries_coeff_of_neg _ hm, ofPowerSeries_coeff_of_neg _ hneg]
  · rw [qExpand_coeff_of_not_dvd N _ hk]
    rcases le_or_gt 0 k with hk0 | hk0
    · lift k to ℕ using hk0
      rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_expand_of_not_dvd]
      exact fun h => hk (Int.natCast_dvd_natCast.2 h)
    · rw [ofPowerSeries_coeff_of_neg _ hk0]

/-! ### Continuity of the power-series operations in the product topology -/

theorem continuous_of_coeff {R S : Type*} [Semiring R] [Semiring S] [TopologicalSpace R]
    [TopologicalSpace S] (g : PowerSeries R → PowerSeries S)
    (h : ∀ d, Continuous fun φ => PowerSeries.coeff d (g φ)) : Continuous g :=
  continuous_iff_continuousAt.2 fun φ =>
    (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto S g (nhds φ) (g φ)).2 fun d =>
      (h d).continuousAt

theorem continuous_map {R S : Type*} [Semiring R] [Semiring S] [TopologicalSpace R]
    [TopologicalSpace S] (f : R →+* S) (hf : Continuous f) :
    Continuous (PowerSeries.map f : PowerSeries R → PowerSeries S) :=
  continuous_of_coeff _ fun d => by
    simp only [PowerSeries.coeff_map]
    exact hf.comp (PowerSeries.WithPiTopology.continuous_coeff R d)

theorem continuous_rescale {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    (a : R) : Continuous (PowerSeries.rescale a : PowerSeries R → PowerSeries R) :=
  continuous_of_coeff _ fun d => by
    simp only [PowerSeries.coeff_rescale]
    exact (continuous_of_discreteTopology (f := fun x : R => a ^ d * x)).comp
      (PowerSeries.WithPiTopology.continuous_coeff R d)

theorem continuous_expand {R : Type*} [CommRing R] [TopologicalSpace R] (N : ℕ) (hN : N ≠ 0) :
    Continuous (PowerSeries.expand N hN : PowerSeries R → PowerSeries R) :=
  continuous_of_coeff _ fun d => by
    simp only [PowerSeries.coeff_expand]
    split_ifs
    · exact PowerSeries.WithPiTopology.continuous_coeff R _
    · exact continuous_const

/-! ### Multipliability of the truncations -/

theorem multipliable_of_X_pow_dvd {R : Type*} [CommRing R] [TopologicalSpace R]
    (u : ℕ → PowerSeries R) (h : ∀ n, (PowerSeries.X : PowerSeries R) ^ (n + 1) ∣ u n - 1) :
    Multipliable u := by
  have hu : u = fun n => 1 + (u n - 1) := funext fun n => by ring
  rw [hu]
  apply PowerSeries.WithPiTopology.multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n => Filter.eventually_atTop.mpr ⟨n, ?_⟩
  intro m hm
  have hle : ((m + 1 : ℕ) : ℕ∞) ≤ (u m - 1).order :=
    PowerSeries.nat_le_order _ _ fun i hi => PowerSeries.X_pow_dvd_iff.1 (h m) i hi
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_of_le hm) hle

/-! ### The `η`-product as a topological product, rescaled and expanded -/

theorem map_etaProd_eq_tprod (K : Type*) [CommRing K] [TopologicalSpace K] [T2Space K] :
    PowerSeries.map (Int.castRingHom K) etaProd =
      ∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1)) := by
  rw [etaProd, (PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod
    (PowerSeries.map (Int.castRingHom K)) (continuous_map _ continuous_of_discreteTopology)]
  exact tprod_congr fun n => by rw [map_sub, map_one, map_pow, PowerSeries.map_X]

theorem rescale_tprod_one_sub_X_pow {K : Type*} [CommRing K] [TopologicalSpace K]
    [DiscreteTopology K] (a : K) :
    PowerSeries.rescale a (∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1))) =
      ∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.C (a ^ (n + 1)) * PowerSeries.X ^ (n + 1)) := by
  rw [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow K).map_tprod (PowerSeries.rescale a)
    (continuous_rescale a)]
  exact tprod_congr fun n => by
    rw [map_sub, map_one, map_pow, PowerSeries.rescale_X, mul_pow, ← map_pow]

theorem expand_tprod_one_sub_X_pow {K : Type*} [CommRing K] [TopologicalSpace K] [T2Space K]
    (N : ℕ) (hN : N ≠ 0) :
    PowerSeries.expand N hN (∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1))) =
      ∏' n : ℕ, ((1 : PowerSeries K) - PowerSeries.X ^ (N * (n + 1))) := by
  rw [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow K).map_tprod (PowerSeries.expand N hN)
    (continuous_expand N hN)]
  exact tprod_congr fun n => by rw [map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul]

/-! ### The finite products over the `p`-th roots of unity -/

theorem prod_one_sub_root_mul {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {μ : K}
    (hμ : IsPrimitiveRoot μ p) (Y : PowerSeries K) :
    ∏ b ∈ Finset.range p, ((1 : PowerSeries K) - PowerSeries.C (μ ^ b) * Y) = 1 - Y ^ p := by
  classical
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (PowerSeries.C : K → PowerSeries K) := fun a b hab => by
    simpa using congrArg PowerSeries.constantCoeff hab
  have hμ' : IsPrimitiveRoot (PowerSeries.C μ) p := hμ.map_of_injective hinj
  have h := hμ'.pow_sub_pow_eq_prod_sub_mul 1 Y hp.pos
  rw [one_pow] at h
  rw [h]
  have hset : Polynomial.nthRootsFinset p (1 : PowerSeries K) =
      (Finset.range p).image fun b => PowerSeries.C μ ^ b := by
    ext x
    rw [Polynomial.mem_nthRootsFinset hp.pos, Finset.mem_image]
    constructor
    · intro hx
      obtain ⟨i, hi, rfl⟩ := hμ'.eq_pow_of_pow_eq_one hx
      exact ⟨i, Finset.mem_range.2 hi, rfl⟩
    · rintro ⟨i, -, rfl⟩
      rw [← pow_mul, mul_comm, pow_mul, hμ'.pow_eq_one, one_pow]
  rw [hset, Finset.prod_image fun i hi j hj hij =>
    hμ'.pow_inj (Finset.mem_range.1 hi) (Finset.mem_range.1 hj) hij]
  exact Finset.prod_congr rfl fun b _ => by rw [map_pow]

theorem prod_twist_factor {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (m : ℕ) :
    ∏ b ∈ Finset.range p,
        ((1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ m) * PowerSeries.X ^ m) =
      if p ∣ m then ((1 : PowerSeries K) - PowerSeries.X ^ m) ^ p
      else (1 : PowerSeries K) - PowerSeries.X ^ (p * m) := by
  have hp : p.Prime := Fact.out
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    rw [Finset.prod_congr rfl fun b _ => show
        (1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ (p * k)) * PowerSeries.X ^ (p * k) =
          1 - PowerSeries.X ^ (p * k) by
      rw [← pow_mul, mul_left_comm b p k, pow_mul, hζ.pow_eq_one, one_pow, map_one, one_mul],
      Finset.prod_const, Finset.card_range]
  · have hμ : IsPrimitiveRoot (ζ ^ m) p :=
      hζ.pow_of_coprime m (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hd))
    rw [Finset.prod_congr rfl fun b _ => show
        (1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ m) * PowerSeries.X ^ m =
          1 - PowerSeries.C ((ζ ^ m) ^ b) * PowerSeries.X ^ m by rw [← pow_mul, mul_comm b m, pow_mul],
      prod_one_sub_root_mul hμ, ← pow_mul, mul_comm m p]

/-! ### The regrouping of the Euler-type infinite products -/

/-- The truncations `1 - X ^ (k (n + 1))`. -/
def uFam (K : Type*) [CommRing K] (k n : ℕ) : PowerSeries K := 1 - PowerSeries.X ^ (k * (n + 1))

/-- The part of `uFam K p` at the indices `p ∤ n + 1`. -/
def hFam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then 1 else 1 - PowerSeries.X ^ (p * (n + 1))

/-- The part of `uFam K p` at the indices `p ∣ n + 1`, in `p`-th power form. -/
def gFam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then (1 - PowerSeries.X ^ (n + 1)) ^ p else 1

/-- The same support as `gFam`, but with the expanded factor. -/
def g'Fam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then 1 - PowerSeries.X ^ (p * (n + 1)) else 1

/-- The `η (p q) ^ 24`-type family: `uFam K p`'s factor where `p ∣ n + 1`, `gFam`'s
elsewhere. -/
def cFam (K : Type*) [CommRing K] (p n : ℕ) : PowerSeries K :=
  if p ∣ n + 1 then (1 - PowerSeries.X ^ (n + 1)) ^ p else 1 - PowerSeries.X ^ (p * (n + 1))

theorem cFam_eq (K : Type*) [CommRing K] (p n : ℕ) : cFam K p n = hFam K p n * gFam K p n := by
  unfold cFam hFam gFam
  split_ifs <;> ring

theorem uFam_eq (K : Type*) [CommRing K] (p n : ℕ) : uFam K p n = hFam K p n * g'Fam K p n := by
  unfold uFam hFam g'Fam
  split_ifs <;> ring

theorem one_le_index {p : ℕ} (hp : 0 < p) (m : ℕ) : 1 ≤ p * (m + 1) :=
  Nat.one_le_iff_ne_zero.2 (mul_ne_zero hp.ne' (Nat.succ_ne_zero m))

theorem index_injective {p : ℕ} (hp : 0 < p) : Function.Injective fun m : ℕ => p * (m + 1) - 1 := by
  intro a b hab
  have h := (tsub_left_inj (one_le_index hp a) (one_le_index hp b)).1 hab
  have h' := Nat.eq_of_mul_eq_mul_left hp h
  omega

theorem mulSupport_subset_range {K : Type*} [CommRing K] {p : ℕ} (F : ℕ → PowerSeries K)
    (hF : ∀ n, ¬ p ∣ n + 1 → F n = 1) :
    Function.mulSupport F ⊆ Set.range fun m : ℕ => p * (m + 1) - 1 := by
  intro n hn
  rw [Function.mem_mulSupport] at hn
  by_cases hd : p ∣ n + 1
  · obtain ⟨k, hk⟩ := hd
    cases k with
    | zero => simp at hk
    | succ m => exact ⟨m, (Nat.eq_sub_of_add_eq hk).symm⟩
  · exact absurd (hF n hd) hn

section Multipliable

variable (K : Type*) [CommRing K] [TopologicalSpace K]

theorem multipliable_uFam {k : ℕ} (hk : 0 < k) : Multipliable (uFam K k) :=
  multipliable_of_X_pow_dvd _ fun n => by
    rw [uFam, sub_sub_cancel_left, dvd_neg]
    exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hk)

theorem multipliable_hFam {p : ℕ} (hp : 0 < p) : Multipliable (hFam K p) :=
  multipliable_of_X_pow_dvd _ fun n => by
    unfold hFam
    split_ifs
    · simp
    · rw [sub_sub_cancel_left, dvd_neg]
      exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hp)

theorem multipliable_gFam (p : ℕ) : Multipliable (gFam K p) :=
  multipliable_of_X_pow_dvd _ fun n => by
    unfold gFam
    split_ifs
    · have h1 : (PowerSeries.X : PowerSeries K) ^ (n + 1) ∣ (1 - PowerSeries.X ^ (n + 1)) - 1 :=
        ⟨-1, by ring⟩
      have h2 := sub_dvd_pow_sub_pow ((1 : PowerSeries K) - PowerSeries.X ^ (n + 1)) 1 p
      rw [one_pow] at h2
      exact h1.trans h2
    · simp

theorem multipliable_g'Fam {p : ℕ} (hp : 0 < p) : Multipliable (g'Fam K p) :=
  multipliable_of_X_pow_dvd _ fun n => by
    unfold g'Fam
    split_ifs
    · rw [sub_sub_cancel_left, dvd_neg]
      exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hp)
    · simp

end Multipliable

section Topological

variable (K : Type*) [CommRing K] [TopologicalSpace K] [DiscreteTopology K]

theorem tprod_gFam {p : ℕ} (hp : 0 < p) : ∏' n, gFam K p n = (∏' n, uFam K p n) ^ p := by
  have hsupp := mulSupport_subset_range (gFam K p) fun n hd => by
    unfold gFam; rw [ite_eq_right hd]
  rw [← (index_injective hp).tprod_eq hsupp, ← (multipliable_uFam K hp).tprod_pow]
  exact tprod_congr fun m => by
    show gFam K p (p * (m + 1) - 1) = uFam K p m ^ p
    unfold gFam uFam
    rw [Nat.sub_add_cancel (one_le_index hp m), ite_eq_left (dvd_mul_right p (m + 1))]

omit [DiscreteTopology K] in
theorem tprod_g'Fam {p : ℕ} (hp : 0 < p) : ∏' n, g'Fam K p n = ∏' n, uFam K (p * p) n := by
  have hsupp := mulSupport_subset_range (g'Fam K p) fun n hd => by
    unfold g'Fam; rw [ite_eq_right hd]
  rw [← (index_injective hp).tprod_eq hsupp]
  exact tprod_congr fun m => by
    show g'Fam K p (p * (m + 1) - 1) = uFam K (p * p) m
    unfold g'Fam uFam
    rw [Nat.sub_add_cancel (one_le_index hp m), ite_eq_left (dvd_mul_right p (m + 1)), mul_assoc]

theorem regroup {p : ℕ} (hp : 0 < p) :
    (∏' n, cFam K p n) * (∏' n, uFam K (p * p) n) = (∏' n, uFam K p n) ^ (p + 1) := by
  have hc : ∏' n, cFam K p n = (∏' n, hFam K p n) * ∏' n, gFam K p n := by
    rw [← (multipliable_hFam K hp).tprod_mul (multipliable_gFam K p)]
    exact tprod_congr fun n => cFam_eq K p n
  have hu : ∏' n, uFam K p n = (∏' n, hFam K p n) * ∏' n, g'Fam K p n := by
    rw [← (multipliable_hFam K hp).tprod_mul (multipliable_g'Fam K hp)]
    exact tprod_congr fun n => uFam_eq K p n
  rw [hc, tprod_gFam K hp, ← tprod_g'Fam K hp]
  calc (∏' n, hFam K p n) * (∏' n, uFam K p n) ^ p * ∏' n, g'Fam K p n
      = (∏' n, uFam K p n) ^ p * ((∏' n, hFam K p n) * ∏' n, g'Fam K p n) := by ring
    _ = (∏' n, uFam K p n) ^ (p + 1) := by rw [← hu, pow_succ]

end Topological

/-- The `η`-norm identity at the level of power series: the product of the `p`
rescales of `η` times the `p * p`-expansion of `η` is the `p + 1`-st power of the
`p`-expansion, in `PowerSeries K`. Transcribed from the pin's
`S_ModularCurve_StarBank_deltaNorm.lean:285`. -/
theorem etaNorm_powerSeries {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    (∏ b ∈ Finset.range p,
        PowerSeries.rescale (ζ ^ b) (PowerSeries.map (Int.castRingHom K) etaProd)) *
      PowerSeries.expand (p * p) (mul_ne_zero (NeZero.ne p) (NeZero.ne p))
        (PowerSeries.map (Int.castRingHom K) etaProd) =
    PowerSeries.expand p (NeZero.ne p) (PowerSeries.map (Int.castRingHom K) etaProd) ^ (p + 1) := by
  let : TopologicalSpace K := ⊥
  have : DiscreteTopology K := ⟨rfl⟩
  have hp : p.Prime := Fact.out
  have hmult : ∀ b ∈ Finset.range p, Multipliable fun n : ℕ =>
      (1 : PowerSeries K) - PowerSeries.C ((ζ ^ b) ^ (n + 1)) * PowerSeries.X ^ (n + 1) :=
    fun b _ => multipliable_of_X_pow_dvd _ fun n => ⟨-PowerSeries.C ((ζ ^ b) ^ (n + 1)), by ring⟩
  rw [map_etaProd_eq_tprod K, expand_tprod_one_sub_X_pow, expand_tprod_one_sub_X_pow,
    Finset.prod_congr rfl fun b _ => rescale_tprod_one_sub_X_pow (ζ ^ b),
    ← Multipliable.tprod_finsetProd hmult, tprod_congr fun n => prod_twist_factor hζ (n + 1)]
  exact regroup K hp.pos

end W1

namespace StarBank

/-- The `η`-norm identity in Laurent-series form: the `q`-shifts are pulled out of
`qTwist`/`qExpand`. The pin's `S_` file states it `private` (its line 308). -/
private theorem etaNorm {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (∏ b ∈ Finset.range p,
        qTwist (ζ ^ b) (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd))) *
      qExpand K (p * p) (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)) =
    qExpand K p (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)) ^
      (p + 1) := by
  rw [W1.qExpand_ofPowerSeries, W1.qExpand_ofPowerSeries,
    Finset.prod_congr rfl fun b _ => W1.qTwist_ofPowerSeries (ζ ^ b) _,
    ← map_prod, ← map_mul, ← map_pow]
  simp only [Units.val_pow_eq_pow_val]
  exact congrArg _ (W1.etaNorm_powerSeries hζ)

end StarBank

namespace W1

/-- A product of `p` single terms is the single term at the sum of the exponents. -/
theorem prod_single_one {K : Type*} [CommRing K] (s : Finset ℕ) (x : ℕ → K) :
    ∏ b ∈ s, HahnSeries.single (1 : ℤ) (x b) = HahnSeries.single (s.card : ℤ) (∏ b ∈ s, x b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, HahnSeries.single_mul_single,
      Finset.card_insert_of_notMem ha, Nat.cast_succ, add_comm (1 : ℤ)]

/-- The bookkeeping that turns `∏ b, qTwist (ζ ^ b) Δ` into `C ε · Δ ^ (p + 1)`: the
`q`-shifts `single p ε` and `single (p * p) 1` combine into `C ε · single p 1 ^ (p + 1)`. -/
theorem delta_bookkeeping {K : Type*} [Field K] (p : ℕ) (ε : K) (PT V1 V2 : LaurentSeries K)
    (hN : PT * V2 = V1 ^ (p + 1)) :
    HahnSeries.single (p : ℤ) ε * PT ^ 24 * (HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K) * V2 ^ 24) =
      HahnSeries.C ε * (HahnSeries.single (p : ℤ) (1 : K) * V1 ^ 24) ^ (p + 1) := by
  have hs : HahnSeries.single (p : ℤ) ε * HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K) =
      HahnSeries.C ε * HahnSeries.single (p : ℤ) (1 : K) ^ (p + 1) := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_pow, HahnSeries.C_apply,
      HahnSeries.single_mul_single, mul_one, one_pow, mul_one,
      show (0 : ℤ) + (p + 1) • ((p : ℕ) : ℤ) = ((p : ℕ) : ℤ) + ((p * p : ℕ) : ℤ) by
        rw [nsmul_eq_mul]; push_cast; ring]
  calc HahnSeries.single (p : ℤ) ε * PT ^ 24 *
        (HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K) * V2 ^ 24)
      = (HahnSeries.single (p : ℤ) ε * HahnSeries.single ((p * p : ℕ) : ℤ) (1 : K)) *
          (PT * V2) ^ 24 := by ring
    _ = HahnSeries.C ε * (HahnSeries.single (p : ℤ) (1 : K) * V1 ^ 24) ^ (p + 1) := by
        rw [hN, hs]; ring

end W1

namespace StarBank

/-- **The `σ`-norm of `Δ`**: the product of `Δ = q · η ^ 24` over the `p` cyclotomic
twists, times the `p * p`-expansion of `Δ`, is the `p`-th root of unity
`∏ b ∈ range p, ζ ^ b` times the `(p + 1)`-st power of the `p`-expansion of `Δ`.
Verbatim from `Theorems/Thm_ModularCurve_StarBank_deltaNorm.lean:7`. -/
theorem deltaNorm {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) :
    (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1) := by
  have hN := etaNorm p ζ hζ
  have hT : ∀ b ∈ Finset.range p,
      qTwist (ζ ^ b) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
        HahnSeries.single (1 : ℤ) ((ζ ^ b : Kˣ) : K) *
          qTwist (ζ ^ b)
            (HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd)) ^ 24 :=
    fun b _ => by rw [map_mul, map_pow, qTwist_single, zpow_one, mul_one]
  rw [Finset.prod_congr rfl hT, Finset.prod_mul_distrib, Finset.prod_pow,
    W1.prod_single_one, Finset.card_range, ← Units.coe_prod, map_mul, map_pow,
    qExpand_single, mul_one, map_mul, map_pow, qExpand_single, mul_one]
  exact W1.delta_bookkeeping p _ _ _ _ hN

end StarBank

namespace W1

/-! ### The `j`-series algebra: `aeval (jqModC K)` of a polynomial -/

section Kit

variable (K : Type*) [Field K]

/-- The scalar `c` as `c q ^ 0`, in the `HahnSeries.C` spelling the pin's proofs
rewrite with (the port's `algebraMap_laurentSeries_eq_single` is the same fact). -/
theorem algebraMap_eq_C (c : K) : algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]

theorem aeval_jqModC_eq_sum (P : Polynomial K) :
    Polynomial.aeval (jqModC K) P =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        algebraMap K (LaurentSeries K) (P.coeff i) * jqModC K ^ i := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]

theorem coeff_aeval_jqModC (P : Polynomial K) (m : ℤ) :
    (Polynomial.aeval (jqModC K) P).coeff m =
      ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (jqModC K ^ i).coeff m := by
  rw [aeval_jqModC_eq_sum, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [algebraMap_eq_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

theorem coeff_aeval_jqModC_neg_natDegree (P : Polynomial K) :
    (Polynomial.aeval (jqModC K) P).coeff (-(P.natDegree : ℤ)) = P.leadingCoeff := by
  rw [coeff_aeval_jqModC, Finset.sum_range_succ, coeff_jqModC_pow_self, mul_one,
    Finset.sum_eq_zero fun i hi => ?_, zero_add, Polynomial.leadingCoeff]
  rw [coeff_jqModC_pow_of_lt K (by have := Finset.mem_range.1 hi; omega), mul_zero]

/-- `aeval (jqModC K)` is injective: a nonzero polynomial has a nonzero top
coefficient, which `polynomial in j` reads at `q ^ (-natDegree)`. -/
theorem aeval_jqModC_injective :
    Function.Injective (Polynomial.aeval (jqModC K) : Polynomial K → LaurentSeries K) := by
  intro P Q h
  by_contra hne
  have h0 : Polynomial.aeval (jqModC K) (P - Q) = 0 := by rw [map_sub, h, sub_self]
  have hlc := coeff_aeval_jqModC_neg_natDegree K (P - Q)
  rw [h0, HahnSeries.coeff_zero] at hlc
  exact hne (sub_eq_zero.1 (Polynomial.leadingCoeff_eq_zero.1 hlc.symm))

theorem qTwist_C (u : Kˣ) (c : K) : qTwist u (HahnSeries.C c) = HahnSeries.C c := by
  rw [HahnSeries.C_apply, qTwist_single, zpow_zero, Units.val_one, one_mul]

theorem qTwist_aeval (u : Kˣ) (x : LaurentSeries K) (P : Polynomial K) :
    qTwist u (Polynomial.aeval x P) = Polynomial.aeval (qTwist u x) P := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext fun c => by rw [RingHom.comp_apply, algebraMap_eq_C, qTwist_C]

theorem qExpand_aeval (N : ℕ) [NeZero N] (x : LaurentSeries K) (P : Polynomial K) :
    qExpand K N (Polynomial.aeval x P) = Polynomial.aeval (qExpand K N x) P := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext fun c => by rw [RingHom.comp_apply, algebraMap_eq_C, qExpand_C]

theorem prod_map_sub_comm (s : Multiset K) (x : LaurentSeries K) :
    (s.map fun α => x - algebraMap K (LaurentSeries K) α).prod =
      (-1) ^ Multiset.card s * (s.map fun α => algebraMap K (LaurentSeries K) α - x).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ih,
      Multiset.card_cons, pow_succ]
    ring

variable [IsAlgClosed K]

/-- Over an algebraically closed field, `aeval x G` factors through the roots of
`G` and the leading coefficient: `aeval x G = G.leadingCoeff · ∏ (α - x)`. -/
theorem aeval_eq_prod_roots (G : Polynomial K) (x : LaurentSeries K) :
    Polynomial.aeval x G =
      algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots *
        (G.roots.map fun α => algebraMap K (LaurentSeries K) α - x).prod := by
  conv_lhs => rw [(IsAlgClosed.splits G).eq_prod_roots]
  rw [map_mul, Polynomial.aeval_C, map_multiset_prod, Multiset.map_map, mul_assoc,
    ← prod_map_sub_comm]
  congr 2
  exact Multiset.map_congr rfl fun α _ => by
    simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

end Kit

end W1

namespace StarBank

local notation "𝓓[" K "]" =>
  (HahnSeries.single (1 : ℤ) (1 : K) *
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)

open ModularCurve.W1 in
/-- **The closure of the star datum**: over an algebraically closed field, if `G`
annihilates `Δ ^ M` at `jqModC K` (`hstar`), `R` realises `jqNModC K p` (`hR`) and
presses it into the `p` twists of `jqModC K` (`hpress`), and the norm of `Δ` is the
`p`-th root of unity (`hnorm`), then `G.comp R` divides `C c · G ^ (p + 1)` with
`c ≠ 0`. Verbatim from `Theorems/Thm_ModularCurve_StarBank_closure.lean:7`. -/
theorem closure {K : Type*} [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime]
    (ζ : Kˣ) {M : ℕ} {G R : Polynomial K}
    (hstar : Polynomial.aeval (jqModC K) G *
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1)
    (hR : Polynomial.aeval (jqModC K) R = jqNModC K p)
    (hpress : R.map (algebraMap K (LaurentSeries K)) - Polynomial.C (jqNModC K p) =
        ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))))
    (hnorm : (∏ b ∈ Finset.range p, qTwist (ζ ^ b)
        (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24)) *
      qExpand K (p * p) (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) =
    HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
      qExpand K p (HahnSeries.single (1 : ℤ) (1 : K) *
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^
        (p + 1)) :
    ∃ c : K, c ≠ 0 ∧ G.comp R ∣ Polynomial.C c * G ^ (p + 1) := by

  have hjp : jqNModC K p = qExpand K p (jqModC K) := rfl

  have F2 : ∀ α : K, algebraMap K (LaurentSeries K) (R.eval α) - jqNModC K p =
      ∏ b ∈ Finset.range p, (algebraMap K (LaurentSeries K) α - qTwist (ζ ^ b) (jqModC K)) := by
    intro α
    have h := congrArg (Polynomial.eval (algebraMap K (LaurentSeries K) α)) hpress
    rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      Polynomial.eval_prod] at h
    simpa only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using h

  have F3 : Polynomial.aeval (jqNModC K p)
      ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) =
      ∏ b ∈ Finset.range p, (G.roots.map fun α =>
        algebraMap K (LaurentSeries K) α - qTwist (ζ ^ b) (jqModC K)).prod := by
    rw [map_multiset_prod, Multiset.map_map]
    have h1 : (G.roots.map ((Polynomial.aeval (jqNModC K p)) ∘ fun α =>
        Polynomial.C (R.eval α) - Polynomial.X)) =
        G.roots.map fun α => ∏ b ∈ Finset.range p,
          (algebraMap K (LaurentSeries K) α - qTwist (ζ ^ b) (jqModC K)) := by
      refine Multiset.map_congr rfl fun α _ => ?_
      rw [Function.comp_apply, map_sub, Polynomial.aeval_C, Polynomial.aeval_X]
      exact F2 α
    rw [h1]
    simp only [Finset.prod_eq_multiset_prod]
    exact Multiset.prod_map_prod_map _ _

  have F4 : ∏ b ∈ Finset.range p, Polynomial.aeval (qTwist (ζ ^ b) (jqModC K)) G =
      (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        Polynomial.aeval (jqNModC K p)
          ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) := by
    rw [F3, Finset.prod_congr rfl fun b _ => aeval_eq_prod_roots K G (qTwist (ζ ^ b) (jqModC K)),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

  have F5 : (∏ b ∈ Finset.range p, Polynomial.aeval (qTwist (ζ ^ b) (jqModC K)) G) *
      (∏ b ∈ Finset.range p, qTwist (ζ ^ b) 𝓓[K]) ^ M = 1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun b _ => ?_
    have h := congrArg (qTwist (ζ ^ b)) hstar
    rwa [map_mul, map_pow, (qTwist (ζ ^ b)).map_one, qTwist_aeval] at h

  have F6 : Polynomial.aeval (jqNModC K p) G * qExpand K p 𝓓[K] ^ M = 1 := by
    have h := congrArg (qExpand K p) hstar
    rwa [map_mul, map_pow, (qExpand K p).map_one, qExpand_aeval] at h
  have F7 : Polynomial.aeval (qExpand K (p * p) (jqModC K)) G * qExpand K (p * p) 𝓓[K] ^ M = 1 := by
    have h := congrArg (qExpand K (p * p)) hstar
    rwa [map_mul, map_pow, (qExpand K (p * p)).map_one, qExpand_aeval] at h

  have F54 : (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
      Polynomial.aeval (jqNModC K p)
        ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
      (∏ b ∈ Finset.range p, qTwist (ζ ^ b) 𝓓[K]) ^ M = 1 := by
    rw [← F4]; exact F5

  have key : Polynomial.aeval (jqNModC K p) G ^ (p + 1) =
      (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M *
        Polynomial.aeval (jqNModC K p)
          ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
        Polynomial.aeval (qExpand K (p * p) (jqModC K)) G := by
    calc Polynomial.aeval (jqNModC K p) G ^ (p + 1)
        = Polynomial.aeval (jqNModC K p) G ^ (p + 1) *
            (Polynomial.aeval (qExpand K (p * p) (jqModC K)) G * qExpand K (p * p) 𝓓[K] ^ M) *
            ((algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
              Polynomial.aeval (jqNModC K p)
                ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
              (∏ b ∈ Finset.range p, qTwist (ζ ^ b) 𝓓[K]) ^ M) := by
          rw [F7, F54, mul_one, mul_one]
      _ = (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
            Polynomial.aeval (jqNModC K p)
              ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
            Polynomial.aeval (qExpand K (p * p) (jqModC K)) G *
            Polynomial.aeval (jqNModC K p) G ^ (p + 1) *
            ((∏ b ∈ Finset.range p, qTwist (ζ ^ b) 𝓓[K]) * qExpand K (p * p) 𝓓[K]) ^ M := by
          ring
      _ = (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
            Polynomial.aeval (jqNModC K p)
              ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
            Polynomial.aeval (qExpand K (p * p) (jqModC K)) G *
            Polynomial.aeval (jqNModC K p) G ^ (p + 1) *
            (HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) *
              qExpand K p 𝓓[K] ^ (p + 1)) ^ M := by
          rw [hnorm]
      _ = (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
            HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M *
            Polynomial.aeval (jqNModC K p)
              ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
            Polynomial.aeval (qExpand K (p * p) (jqModC K)) G *
            (Polynomial.aeval (jqNModC K p) G * qExpand K p 𝓓[K] ^ M) ^ (p + 1) := by
          ring
      _ = (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
            HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M *
            Polynomial.aeval (jqNModC K p)
              ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
            Polynomial.aeval (qExpand K (p * p) (jqModC K)) G := by
          rw [F6, one_pow, mul_one]

  have hκL : algebraMap K (LaurentSeries K)
      ((G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M) =
      (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M := by
    rw [map_mul, map_pow, map_pow, map_mul, map_pow, map_neg, map_one,
      algebraMap_eq_C K (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K))]
  have hP1 : qExpand K p (Polynomial.aeval (jqModC K) (G ^ (p + 1))) =
      Polynomial.aeval (jqNModC K p) G ^ (p + 1) := by
    rw [map_pow, map_pow, qExpand_aeval, ← hjp]
  have hP2 : qExpand K p (Polynomial.aeval (jqModC K)
      (Polynomial.C ((G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
          (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M) *
        (G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod * G.comp R)) =
      (algebraMap K (LaurentSeries K) G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
        HahnSeries.C (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M *
        Polynomial.aeval (jqNModC K p)
          ((G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod) *
        Polynomial.aeval (qExpand K (p * p) (jqModC K)) G := by
    rw [map_mul, map_mul, map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_comp, hR, hjp,
      ← qExpand_aeval, qExpand_qExpand,
      algebraMap_eq_C, qExpand_C, ← algebraMap_eq_C, hκL, qExpand_aeval, qExpand_aeval]
  have hpoly : G ^ (p + 1) =
      Polynomial.C ((G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
          (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M) *
        (G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod * G.comp R :=
    aeval_jqModC_injective K (qExpand_injective (R := K) (N := p) (hP1.trans (key.trans hP2.symm)))
  exact ⟨1, one_ne_zero, Polynomial.C ((G.leadingCoeff * (-1) ^ Multiset.card G.roots) ^ p *
      (((∏ b ∈ Finset.range p, ζ ^ b : Kˣ) : K)) ^ M) *
    (G.roots.map fun α => Polynomial.C (R.eval α) - Polynomial.X).prod,
    by rw [map_one, one_mul, hpoly]; ring⟩

end StarBank

namespace W1

/-! ### The one-point kit: `HahnSeries` order, leading coefficient and constants -/

section OnePointKit

variable {K : Type*} [Field K]

/-- The leading coefficient of a power of a Laurent series is the power of the
leading coefficient. -/
theorem leadingCoeff_laurent_pow (x : LaurentSeries K) (n : ℕ) :
    (x ^ n).leadingCoeff = x.leadingCoeff ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, HahnSeries.leadingCoeff_eq, HahnSeries.order_one,
      ← HahnSeries.single_zero_one, HahnSeries.coeff_single, ite_eq_left rfl]
  | succ n ih =>
    rw [pow_succ, pow_succ, HahnSeries.leadingCoeff_mul, ih]

/-- The order of a power of a nonzero Laurent series is the multiple of the order. -/
theorem order_laurent_pow {x : LaurentSeries K} (hx : x ≠ 0) (n : ℕ) :
    (x ^ n).order = n • x.order := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul, HahnSeries.order_one]
  | succ n ih =>
    have hlc : (x ^ n).leadingCoeff * x.leadingCoeff ≠ 0 := by
      rw [leadingCoeff_laurent_pow]
      exact mul_ne_zero (pow_ne_zero _ (HahnSeries.leadingCoeff_ne_zero.mpr hx))
        (HahnSeries.leadingCoeff_ne_zero.mpr hx)
    rw [pow_succ, HahnSeries.order_mul_of_ne_zero hlc, ih, succ_nsmul]

/-- The coefficients of a constant multiple. -/
theorem coeff_C_mul (c : K) (y : LaurentSeries K) (g : ℤ) :
    (HahnSeries.C c * y).coeff g = c * y.coeff g := by
  rw [show (HahnSeries.C c : LaurentSeries K) = HahnSeries.single 0 c from rfl,
    HahnSeries.coeff_single_mul, sub_zero]

/-- A constant has no coefficient off `q ^ 0`. -/
theorem coeff_C_of_ne (c : K) {g : ℤ} (hg : g ≠ 0) :
    (HahnSeries.C c : LaurentSeries K).coeff g = 0 := by
  rw [show (HahnSeries.C c : LaurentSeries K) = HahnSeries.single 0 c from rfl,
    HahnSeries.coeff_single, ite_eq_right hg]

/-- **The one-point extraction**: if the `M`-th power of a Laurent series is a
nonzero constant (`M` invertible in `K`), the series is a nonzero constant. The
proof reads the order off `order_laurent_pow` and then kills the first-order term
of `(C γ + y) ^ M`. Verbatim from the pin's
`S_ModularCurve_StarBank_onePoint.lean:57`. -/
theorem eq_C_of_pow_eq_C {x : LaurentSeries K} {γ₀ : K} {M : ℕ}
    (hM : (M : K) ≠ 0) (hγ₀ : γ₀ ≠ 0) (hx : x ^ M = HahnSeries.C γ₀) :
    ∃ γ : K, γ ≠ 0 ∧ x = HahnSeries.C γ := by
  have hM0 : M ≠ 0 := fun h => hM (by rw [h, Nat.cast_zero])
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, zero_pow hM0] at hx
    apply hγ₀
    have h1 := congrArg (fun z : LaurentSeries K => z.coeff 0) hx.symm
    rw [show (HahnSeries.C γ₀ : LaurentSeries K) = HahnSeries.single 0 γ₀ from rfl,
      HahnSeries.coeff_single, ite_eq_left rfl] at h1
    exact h1.trans rfl

  have horder : x.order = 0 := by
    have h2 := order_laurent_pow hx0 M
    rw [hx, HahnSeries.order_C] at h2
    have h3 : (M : ℤ) * x.order = 0 := by rw [← nsmul_eq_mul]; exact h2.symm
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (Int.natCast_ne_zero.mpr hM0)
    · exact h4
  set γ : K := x.coeff 0 with hγdef
  have hγ : γ ≠ 0 := by
    rw [hγdef, ← horder]
    exact fun h => hx0 (HahnSeries.coeff_order_eq_zero.mp h)
  refine ⟨γ, hγ, ?_⟩
  by_contra hne
  have hy0 : x - HahnSeries.C γ ≠ 0 := fun h => hne (by rwa [sub_eq_zero] at h)
  set y : LaurentSeries K := x - HahnSeries.C γ with hydef
  set r : ℤ := y.order with hrdef
  have hyr : y.coeff r ≠ 0 := fun h => hy0 (HahnSeries.coeff_order_eq_zero.mp h)

  have hylow : ∀ k : ℤ, k ≤ 0 → y.coeff k = 0 := by
    intro k hk
    rcases lt_or_eq_of_le hk with hk0 | hk0
    · rw [hydef, HahnSeries.coeff_sub,
        HahnSeries.coeff_eq_zero_of_lt_order (by rw [horder]; exact hk0),
        coeff_C_of_ne γ (ne_of_lt hk0), sub_zero]
    · rw [hydef, HahnSeries.coeff_sub, hk0,
        show (HahnSeries.C γ : LaurentSeries K) = HahnSeries.single 0 γ from rfl,
        HahnSeries.coeff_single, ite_eq_left rfl, ← hγdef, sub_self]
  have hr1 : 1 ≤ r := by
    by_contra hr0
    exact hyr (hylow r (by omega))
  have hrne : r ≠ 0 := by omega

  have hxsplit : x = HahnSeries.C γ + y := by rw [hydef]; ring
  have hch : M.choose (M - 1) = M := by
    have h3 := Nat.choose_symm (show M - 1 ≤ M by omega)
    rw [show M - (M - 1) = 1 from by omega] at h3
    rw [← h3, Nat.choose_one_right]
  have hcoeffM : (x ^ M).coeff r = γ ^ (M - 1) * (M : K) * y.coeff r := by
    rw [hxsplit, add_pow, HahnSeries.coeff_sum]
    rw [Finset.sum_eq_single_of_mem (M - 1) (Finset.mem_range.mpr (by omega))
      (fun b hb hbne => ?_)]
    ·
      have h1 : M - (M - 1) = 1 := by omega
      have hC : (HahnSeries.C γ : LaurentSeries K) ^ (M - 1) * y ^ (M - (M - 1))
            * ((M.choose (M - 1) : ℕ) : LaurentSeries K)
          = HahnSeries.C (γ ^ (M - 1) * (M : K)) * y := by
        rw [h1, pow_one, hch, ← map_pow, ← map_natCast (HahnSeries.C (Γ := ℤ) (R := K)) M,
          mul_right_comm, ← map_mul]
      rw [hC, coeff_C_mul]
    ·
      have hbM : b ≤ M := by
        have := Finset.mem_range.mp hb
        omega
      rcases eq_or_ne b M with hbeq | hbM'
      ·
        subst hbeq
        rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one,
          ← map_pow, coeff_C_of_ne _ hrne]
      ·
        have hb2 : 2 ≤ M - b := by omega
        have hCb : (HahnSeries.C γ : LaurentSeries K) ^ b * y ^ (M - b)
              * ((M.choose b : ℕ) : LaurentSeries K)
            = HahnSeries.C (γ ^ b * (M.choose b : K)) * y ^ (M - b) := by
          rw [← map_pow, ← map_natCast (HahnSeries.C (Γ := ℤ) (R := K)) (M.choose b),
            mul_right_comm, ← map_mul]
        have hyb : (y ^ (M - b)).coeff r = 0 := by
          apply HahnSeries.coeff_eq_zero_of_lt_order
          rw [order_laurent_pow hy0, nsmul_eq_mul]
          have h2b : (2 : ℤ) ≤ ((M - b : ℕ) : ℤ) := by exact_mod_cast hb2
          nlinarith
        rw [hCb, coeff_C_mul, hyb, mul_zero]
  rw [hx] at hcoeffM
  rw [coeff_C_of_ne _ hrne] at hcoeffM
  exact absurd hcoeffM.symm
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hγ) hM) hyr)

end OnePointKit

end W1

namespace StarBank

/-- **The one-point case**: if `C c · (X - C β₀) ^ M` annihilates `Δ ^ M` at
`jqModC K` (`hstar`, with `M` invertible and `c ≠ 0`), then `(jqModC K - C β₀) · Δ`
is a nonzero constant. Verbatim from
`Theorems/Thm_ModularCurve_StarBank_onePoint.lean:6`. -/
theorem onePoint {K : Type*} [Field K] {M : ℕ}
    (hM : (M : K) ≠ 0) {c : K} (hc : c ≠ 0) {β₀ : K}
    (hstar : Polynomial.aeval (ModularCurve.jqModC K)
          (Polynomial.C c * (Polynomial.X - Polynomial.C β₀) ^ M)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24) ^ M
        = 1) :
    ∃ γ : K, γ ≠ 0 ∧
      (ModularCurve.jqModC K - HahnSeries.C β₀)
        * (HahnSeries.single (1 : ℤ) 1
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24)
        = HahnSeries.C γ := by
  set D : LaurentSeries K := HahnSeries.single (1 : ℤ) 1
    * HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) ModularCurve.etaProd) ^ 24 with hD

  have haeval : Polynomial.aeval (jqModC K) (Polynomial.C c * (Polynomial.X - Polynomial.C β₀) ^ M)
      = HahnSeries.C c * (jqModC K - HahnSeries.C β₀) ^ M := by
    rw [map_mul, map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C,
      ModularCurve.algebraMap_laurentSeries_eq_single K c,
      ModularCurve.algebraMap_laurentSeries_eq_single K β₀]
    rfl
  rw [haeval] at hstar

  have hgroup : HahnSeries.C c * ((jqModC K - HahnSeries.C β₀) * D) ^ M = 1 := by
    rw [mul_pow, ← mul_assoc]
    exact hstar

  have hpow : ((jqModC K - HahnSeries.C β₀) * D) ^ M = HahnSeries.C c⁻¹ := by
    have h2 := congrArg (fun z : LaurentSeries K => HahnSeries.C c⁻¹ * z) hgroup
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul, mul_one] at h2
    exact h2
  obtain ⟨γ, hγ, hxC⟩ := ModularCurve.W1.eq_C_of_pow_eq_C hM (inv_ne_zero hc) hpow
  exact ⟨γ, hγ, hxC⟩

end StarBank

end ModularCurve
