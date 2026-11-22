/-
  The convergence and `q`-multiplication identities of the Tate curve's point series.

  Seven identities of the `q`-series layer of the Tate curve:

  * `hasSum_xfun`, `hasSum_yfun`: the two rational functions `xfun w = w / (1 - w)²` and
    `yfun w = w² / (1 - w)³` are the sums of their geometric-type expansions in `w`;
  * `nodal_xfun_yfun`: `yfun² + xfun · yfun = xfun³` — the two series lie on the nodal cubic
    `y² + xy = x³`;
  * `pointX_q_mul`, `pointY_q_mul`: the point coordinates are invariant under `u ↦ q * u`, which is
    the Tate curve's own `q`-periodicity;
  * `tsum_succ_prod_eq_tsum_divisors`: the double `tsum` over `ℕ × ℕ` collapses to a single `tsum`
    over the divisor sums (`N + 1`'s divisors), the Lambert-type regrouping the `coeffSum` layer
    uses;
  * `exists_zpow_mul_mem_annulus`: every `u ≠ 0` is carried into the norm-`< 1` annulus
    (`‖q * (q ^ n * u)‖ < 1` and the same for the inverse) by a power of `q`.

  Transcribed from the seven pins below (pinned `aa2d8b3`, 157 + 69 + 22 + 19 + 19 + 17 + 17 lines),
  whose names and statements are the pins' (no shared engine).

  Assumes `TateCurve/QSeries.lean` and `TateCurve/PointSeries.lean` (`xfun`, `yfun`, `pointX`,
  `pointY`, the term series and their summability).

  Engine notes (the pin's `private` rows, 21 pin rows in all: 7 public + 14 private):

  * the `ℕ × ℕ` regrouping is `section GeneralRegrouping` (pin `S_TateCurve_tsum_succ_prod_eq_tsum_divisors`,
    nine private rows); the pin's private `tsum_succ_prod_main` is kept as the pin has it, so its
    statement is the headline's — the pin's own pair, recorded here per the `dedup` gate;
  * the annulus pin's private engine is `nnnorm_lt_one_iff_norm` + `exists_zpow_mul_norm_Ioc`. The
    pin's *third* private row, `exists_zpow_mul_mem_annulus`, states exactly the headline; since the
    published name is the headline's, Lean forbids keeping both (a `private` and a public
    `TateCurve.exists_zpow_mul_mem_annulus` collide: "a private declaration … has already been
    declared"), so that row is folded into the headline — its body is transcribed verbatim there;
  * `tsum_comp_add_one'` is stated identically in the two `q`-multiplication pins and is written once
    (`private`, in the `q`-multiplication section), hence 2 pin rows → 1 port row.

  Two pin declarations carry no `set_option` and the port adds none. The pin's
  `norm_le_of_le_geometric` auto-includes the section's `[CompleteSpace K]`, which it does not use
  (the pin's file has no `linter.unusedSectionVars` line to transcribe, and the port's rule for a
  dead binder is to drop it, not to excuse it); the port writes `omit [CompleteSpace K] in` there,
  the tree's standing cure for that warning. Two mathlib modules are added to the scaffold's import
  list because the `tsum` engine needs them: `InfiniteSum.Constructions`
  (`Summable.tsum_sigma`) and `InfiniteSum.Real` (`summable_sigma_of_nonneg`).

  Gates measured on landing:

  * heartbeat probe pair (measured, **never installed** — FR-0225): silent at
    `-DmaxHeartbeats=2000`, fails at `1500` (`(deterministic) timeout at whnf`, on
    `nodal_xfun_yfun`), so the module's natural cost is 1.5–2 k heartbeats — under 1 % of the
    200 000 edit-loop cap. No `set_option maxHeartbeats` here, ever;
  * `move_dead --dry-run` (gate 6): 2 declarations / 22 lines, and both are the pin's own dead
    `private` companions — `summable_pairTerm` and `summable_succ_prod` (the pin states them and
    never calls them either: `summable_pairTerm`'s only caller is `summable_succ_prod`). Kept in
    place and recorded here per the escape clause; never deleted on the port's own;
  * `dedup --within --module SeriesIdentities` (all three tiers, `--min-cost 0`): 0 clusters.

  spec-pin: P2M/Sol/S_TateCurve_tsum_succ_prod_eq_tsum_divisors.lean
  spec-pin: P2M/Sol/S_TateCurve_exists_zpow_mul_mem_annulus.lean
  spec-pin: P2M/Sol/S_TateCurve_nodal_xfun_yfun.lean
  spec-pin: P2M/Sol/S_TateCurve_pointX_q_mul.lean
  spec-pin: P2M/Sol/S_TateCurve_pointY_q_mul.lean
  spec-pin: P2M/Sol/S_TateCurve_hasSum_xfun.lean
  spec-pin: P2M/Sol/S_TateCurve_hasSum_yfun.lean
-/
import FLTForHuman.TateCurve.PointSeries
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

noncomputable section

open TateCurve
open scoped NNReal

namespace TateCurve

/-! ### The geometric-series expansions of `xfun` and `yfun` -/

theorem hasSum_xfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun m : ℕ => ((m + 1 : ℕ) : K) * w ^ (m + 1)) (xfun w) := by
  have hw' : ‖w‖ < 1 := hw
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hw').mul_left w
  have hfun : (fun m : ℕ => w * (((m + 1).choose 1 : ℕ) * w ^ m))
      = fun m : ℕ => ((m + 1 : ℕ) : K) * w ^ (m + 1) := by
    funext m; rw [Nat.choose_one_right]; ring
  have hval : w * (1 / (1 - w) ^ 2) = xfun w := by rw [xfun]; ring
  rw [hfun, hval] at h
  exact h

theorem hasSum_yfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2)) (yfun w) := by
  have hw' : ‖w‖ < 1 := hw
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hw').mul_left (w ^ 2)
  have hfun : (fun m : ℕ => w ^ 2 * (((m + 2).choose 2 : ℕ) * w ^ m))
      = fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2) := by
    funext m; ring
  have hval : w ^ 2 * (1 / (1 - w) ^ 3) = yfun w := by rw [yfun]; ring
  rw [hfun, hval] at h
  exact h

theorem nodal_xfun_yfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw1 : w ≠ 1) :
    yfun w ^ 2 + xfun w * yfun w = xfun w ^ 3 := by
  have h1 : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have e2 : xfun w * ((1 : K) - w) ^ 2 = w := by
    rw [xfun, div_mul_cancel₀ _ (pow_ne_zero 2 h1)]
  have e3 : yfun w * ((1 : K) - w) ^ 3 = w ^ 2 := by
    rw [yfun, div_mul_cancel₀ _ (pow_ne_zero 3 h1)]
  apply mul_right_cancel₀ (pow_ne_zero 6 h1)
  calc (yfun w ^ 2 + xfun w * yfun w) * ((1 : K) - w) ^ 6
      = (yfun w * ((1 : K) - w) ^ 3) ^ 2
        + (xfun w * ((1 : K) - w) ^ 2) * (yfun w * ((1 : K) - w) ^ 3) * ((1 : K) - w) := by ring
    _ = (w ^ 2) ^ 2 + w * w ^ 2 * ((1 : K) - w) := by rw [e2, e3]
    _ = w ^ 3 := by ring
    _ = (xfun w * ((1 : K) - w) ^ 2) ^ 3 := by rw [e2]
    _ = xfun w ^ 3 * ((1 : K) - w) ^ 6 := by ring

/-! ### The `q`-periodicity of the point coordinates -/

section QMul

private theorem tsum_comp_add_one' {α : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] [CompleteSpace α] [T2Space α] (f : ℤ → α) :
    ∑' n : ℤ, f (n + 1) = ∑' n : ℤ, f n :=
  (Equiv.addRight (1 : ℤ)).tsum_eq f

theorem pointX_q_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q u : K} (hq0 : q ≠ 0) : pointX q (q * u) = pointX q u := by
  have hterm : ∀ n : ℤ, xTerm q (q * u) n = xTerm q u (n + 1) := fun n => by
    rw [xTerm, xTerm, show q ^ n * (q * u) = q ^ (n + 1) * u by rw [zpow_add_one₀ hq0]; ring]
  rw [pointX, pointX]
  congr 1
  calc ∑' n : ℤ, xTerm q (q * u) n = ∑' n : ℤ, xTerm q u (n + 1) := tsum_congr hterm
    _ = ∑' n : ℤ, xTerm q u n := tsum_comp_add_one' _

theorem pointY_q_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q u : K} (hq0 : q ≠ 0) : pointY q (q * u) = pointY q u := by
  have hterm : ∀ n : ℤ, yTerm q (q * u) n = yTerm q u (n + 1) := fun n => by
    rw [yTerm, yTerm, show q ^ n * (q * u) = q ^ (n + 1) * u by rw [zpow_add_one₀ hq0]; ring]
  rw [pointY, pointY]
  congr 1
  calc ∑' n : ℤ, yTerm q (q * u) n = ∑' n : ℤ, yTerm q u (n + 1) := tsum_congr hterm
    _ = ∑' n : ℤ, yTerm q u n := tsum_comp_add_one' _

end QMul

/-! ### The Lambert-type regrouping over `ℕ × ℕ` -/

section GeneralRegrouping

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable {h : ℕ → K} {C : ℝ} {r : K}

private def pairTerm (h : ℕ → K) (r : K) (c : ℕ+ × ℕ+) : K :=
  h (c.2 : ℕ) * r ^ ((c.1 : ℕ) * (c.2 : ℕ))

private def sigmaTerm' (h : ℕ → K) (r : K)
    (x : (n : ℕ+) × {p // p ∈ (n : ℕ).divisorsAntidiagonal}) : K :=
  h x.2.1.2 * r ^ (x.2.1.1 * x.2.1.2)

omit [CompleteSpace K] in
private theorem norm_le_of_le_geometric (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m)
    {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) :
    ‖h p.2 * r ^ (p.1 * p.2)‖ ≤ C ^ n * ‖r‖ ^ n := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC1
  obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hp2mem : p.2 ∈ n.divisors := Nat.snd_mem_divisors_of_mem_antidiagonal hp
  have hp2pos : 0 < p.2 := Nat.pos_of_mem_divisors hp2mem
  have hp2le : p.2 ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hp2mem)
  rw [norm_mul, norm_pow, hmul]
  exact mul_le_mul ((hh p.2 hp2pos).trans (pow_le_pow_right₀ hC1 hp2le)) le_rfl
    (pow_nonneg (norm_nonneg r) n) (pow_nonneg hC0 n)

private theorem summable_sigmaTerm' (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable (sigmaTerm' h r) := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC1
  have hs0 : (0 : ℝ) ≤ C * ‖r‖ := mul_nonneg hC0 (norm_nonneg r)
  have hs1 : C * ‖r‖ < 1 := by rwa [mul_comm] at hrC

  have hgeom : Summable fun n : ℕ => (n : ℝ) * (C * ‖r‖) ^ n := by
    have habs : ‖(C * ‖r‖ : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hs0]
    have := summable_pow_mul_geometric_of_norm_lt_one 1 habs
    simpa using this
  have hgeomP : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) * (C * ‖r‖) ^ (n : ℕ) :=
    hgeom.comp_injective PNat.coe_injective
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun a => norm_nonneg _)]
  refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun x => norm_nonneg _)
    (fun n => ?_) hgeomP
  rw [tsum_fintype]
  calc ∑ x : {p // p ∈ ((n : ℕ)).divisorsAntidiagonal}, ‖sigmaTerm' h r ⟨n, x⟩‖
      = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, ‖h p.2 * r ^ (p.1 * p.2)‖ := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal fun p => ‖h p.2 * r ^ (p.1 * p.2)‖
    _ ≤ ∑ _p ∈ ((n : ℕ)).divisorsAntidiagonal, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) :=
        Finset.sum_le_sum fun p hp => norm_le_of_le_geometric hC1 hh hp
    _ = ∑ _d ∈ ((n : ℕ)).divisors, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) := by
        rw [Nat.sum_divisorsAntidiagonal' (f := fun _ _ => C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ))]
    _ = (((n : ℕ)).divisors.card : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n : ℕ) : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (pow_nonneg hC0 _) (pow_nonneg (norm_nonneg r) _))
        exact_mod_cast Nat.card_divisors_le_self (n : ℕ)
    _ = ((n : ℕ) : ℝ) * (C * ‖r‖) ^ (n : ℕ) := by rw [mul_pow]

private theorem summable_pairTerm (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable (pairTerm h r) := by
  have hcomp : Summable (pairTerm h r ∘ ⇑sigmaAntidiagonalEquivProd) := by
    have hfun : pairTerm h r ∘ ⇑sigmaAntidiagonalEquivProd = sigmaTerm' h r := by
      funext x
      obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
      rfl
    rw [hfun]
    exact summable_sigmaTerm' hC1 hh hrC
  exact (Equiv.summable_iff sigmaAntidiagonalEquivProd).mp hcomp

private theorem tsum_pairTerm_eq_tsum_divisors (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    ∑' c : ℕ+ × ℕ+, pairTerm h r c
      = ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
  have haux := summable_sigmaTerm' (r := r) hC1 hh hrC

  have htrans : ∑' c : ℕ+ × ℕ+, pairTerm h r c
      = ∑' x : (n : ℕ+) × {p // p ∈ (n : ℕ).divisorsAntidiagonal}, sigmaTerm' h r x := by
    rw [← Equiv.tsum_eq sigmaAntidiagonalEquivProd (pairTerm h r)]
    refine tsum_congr fun x => ?_
    obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
    rfl
  rw [htrans, Summable.tsum_sigma haux]
  refine tsum_congr fun n => ?_

  rw [tsum_fintype]
  calc ∑ x : {p // p ∈ ((n : ℕ)).divisorsAntidiagonal}, sigmaTerm' h r ⟨n, x⟩
      = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2 * r ^ (p.1 * p.2) := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal fun p => h p.2 * r ^ (p.1 * p.2)
    _ = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2 * r ^ (n : ℕ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = (∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2) * r ^ (n : ℕ) := by
        rw [Finset.sum_mul]
    _ = (∑ d ∈ ((n : ℕ)).divisors, h d) * r ^ (n : ℕ) := by
        rw [Nat.sum_divisorsAntidiagonal' (f := fun _ d => h d)]

private def succEquivPNat : ℕ ≃ ℕ+ where
  toFun n := n.succPNat
  invFun n := n.natPred
  left_inv n := Nat.natPred_succPNat n
  right_inv n := PNat.succPNat_natPred n

private theorem tsum_succ_prod_main (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) := by
  have hL : ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' c : ℕ+ × ℕ+, pairTerm h r c := by
    rw [← Equiv.tsum_eq (Equiv.prodCongr succEquivPNat succEquivPNat) (pairTerm h r)]
    refine tsum_congr fun p => ?_
    obtain ⟨a, b⟩ := p
    rfl
  have hR : ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1)
      = ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
    rw [← Equiv.tsum_eq succEquivPNat
      (fun n : ℕ+ => (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ))]
    exact tsum_congr fun N => rfl
  rw [hL, hR]
  exact tsum_pairTerm_eq_tsum_divisors hC1 hh hrC

private theorem summable_succ_prod (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable fun p : ℕ × ℕ => h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) := by
  have hsum := summable_pairTerm (r := r) hC1 hh hrC
  have hcomp : Summable (pairTerm h r ∘ ⇑(Equiv.prodCongr succEquivPNat succEquivPNat)) :=
    (Equiv.summable_iff (Equiv.prodCongr succEquivPNat succEquivPNat)).mpr hsum
  refine hcomp.congr fun p => ?_
  obtain ⟨a, b⟩ := p
  rfl

end GeneralRegrouping

theorem tsum_succ_prod_eq_tsum_divisors {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m)
    (hrC : ‖r‖ * C < 1) :
    ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) =
      ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) :=
  tsum_succ_prod_main hC1 hh hrC

/-! ### Carrying `u` into the norm-`< 1` annulus -/

section Annulus

variable {K : Type*} [NontriviallyNormedField K] {q u : K}

private theorem nnnorm_lt_one_iff_norm {x : K} : ‖x‖₊ < 1 ↔ ‖x‖ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

private theorem exists_zpow_mul_norm_Ioc (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hu0 : u ≠ 0) :
    ∃ n : ℤ, ‖q‖ < ‖q ^ n * u‖ ∧ ‖q ^ n * u‖ ≤ 1 := by
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu_pos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hq_ne : (‖q‖ : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hy : (1 : ℝ) < ‖q‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hq_pos, hq⟩
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu_pos hy
  have hqk_pos : (0 : ℝ) < ‖q‖ ^ (n + 1 : ℤ) := zpow_pos hq_pos _

  have hcancel : ∀ m : ℤ, ‖q‖⁻¹ ^ m * ‖q‖ ^ m = 1 := fun m => by
    rw [← mul_zpow, inv_mul_cancel₀ hq_ne, one_zpow]
  refine ⟨n + 1, ?_, ?_⟩
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n = ‖q‖ := by
      rw [zpow_add₀ hq_ne, zpow_one]
      calc ‖q‖ ^ n * ‖q‖ * ‖q‖⁻¹ ^ n
          = ‖q‖⁻¹ ^ n * (‖q‖ ^ n * ‖q‖) := mul_comm _ _
        _ = ‖q‖⁻¹ ^ n * ‖q‖ ^ n * ‖q‖ := (mul_assoc _ _ _).symm
        _ = 1 * ‖q‖ := by rw [hcancel n]
        _ = ‖q‖ := one_mul _
    have hlt : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ :=
      mul_lt_mul_of_pos_left hn1 hqk_pos
    rw [norm_mul, norm_zpow]
    calc ‖q‖ = ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n := hkey.symm
      _ < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ := hlt
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) = 1 := by
      calc ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1)
          = ‖q‖⁻¹ ^ (n + 1) * ‖q‖ ^ (n + 1) := mul_comm _ _
        _ = 1 := hcancel (n + 1)
    have hle : ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hn2 hqk_pos.le
    rw [norm_mul, norm_zpow]
    calc ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) := hle
      _ = 1 := hkey

end Annulus

theorem exists_zpow_mul_mem_annulus {K : Type*} [NontriviallyNormedField K] {q u : K}
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    ∃ n : ℤ, ‖q * (q ^ n * u)‖₊ < 1 ∧ ‖q * (q ^ n * u)⁻¹‖₊ < 1 := by
  have hqR : ‖q‖ < 1 := nnnorm_lt_one_iff_norm.mp hq
  obtain ⟨n, h1, h2⟩ := exists_zpow_mul_norm_Ioc hq0 hqR hu0
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hv_pos : (0 : ℝ) < ‖q ^ n * u‖ := lt_trans hq_pos h1
  refine ⟨n, nnnorm_lt_one_iff_norm.mpr ?_, nnnorm_lt_one_iff_norm.mpr ?_⟩
  · rw [norm_mul]
    calc ‖q‖ * ‖q ^ n * u‖ ≤ ‖q‖ * 1 := mul_le_mul_of_nonneg_left h2 hq_pos.le
      _ = ‖q‖ := mul_one _
      _ < 1 := hqR
  · rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hv_pos]
    exact h1

end TateCurve
