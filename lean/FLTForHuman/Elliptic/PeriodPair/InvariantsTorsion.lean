/-
  Three `℘`-of-a-period-pair results: the lattice is determined by `(g₂, g₃)`, the
  torsion values of `℘` form a level-`N` modular form with a controlled behaviour at
  the cusp, and the level-`1`-style package at `Γ₁(N)`.

  1. `PeriodPair.lattice_eq_of_g2_eq_of_g3_eq`: `L.g₂ = L'.g₂ → L.g₃ = L'.g₃ →
     L.lattice = L'.lattice` — two period lattices with the same invariants coincide.
     The proof compares `℘` near `0` (where `℘[L] z - z⁻²` is analytic), uses the
     ODE `℘'² = 4℘³ - g₂℘ - g₃` twice to show the difference vanishes to infinite
     order at `0` and hence identically on the connected complement of the two
     lattices, and then that a `℘`-equality off the lattices forces
     `L.lattice ≤ L'.lattice` by comparing pole orders.

  2. `PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty`: for a
     family `L` with `(L τ).ω₁ = τ`, `(L τ).ω₂ = 1`, the functions
     `W b τ = ℘[L τ] ((b₀ τ + b₁)/N)` are a `Γ(N)`-modular form of weight `2`, they
     slash by `γ ∈ SL(2, ℤ)` to `W (b ᵥ* γ)`, and at the cusp they tend to
     `-π²/3 + π²/sin²(π b₁/N)` when `b₀ = 0` and to `-π²/3` otherwise. The engine is
     the `q`-expansion package `WLight.weierstrassP_qExpansion_package` (the pin's
     `WLight` node, homed in `ModularForms/WeightOne/LevelOneHauptmodul.lean`), which
     expands `℘` in the `N`-torsion argument as `(2πi)²` times a principal part
     `ζ^a q^a/(1-ζ^a q^a)²`, the constant `1/12`, and an absolutely convergent double
     series over `ℕ+ × ℕ+`; the limit is then termwise.

  3. `PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff`:
     a single family `W : ZMod M → ModularForm Γ₁(M) 2` which (a) is
     `12 (2πi)⁻² ℘` at the torsion point `t/M` for any normalized `L`, (b) slashes by
     `γ ∈ Γ₀(M)` to `W (t * γ₁₁)`, and (c) whose `q`-expansion coefficients are the
     divisor sums `12 ∑_{d ∣ n} d (ζ^{td} + ζ^{-td} - 2)` (with the `n = 0` constant
     term), the classical `℘`-`q`-expansion at `Γ₁`.

  The port of the pin leaves `PeriodPair.lattice_eq_of_g2_eq_of_g3_eq` (234 pin
  lines), `PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty` (558)
  and `PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff`
  (319), statements from their `Theorems/` wrappers and proofs from the matching
  `P2M/Sol/S_…` files (pinned `aa2d8b3`). The pin's inner namespaces
  `PeriodPair.LatticeFromInvariants`, `EIS2K1` and `WPGamma1` are kept verbatim; only
  the `P2MW.S_<stem>` prefixes are dropped, and the `solution` wrappers are not ported
  (their statements are the three headlines below; the gamma1 headline's proof is
  `WPGamma1.main M`, the torsion headline's body is `EIS2K1.main hL a`, and the
  lattice headline's body the `LatticeFromInvariants` argument). Node 3's proof
  consumes node 2's headline (its `K1` is the `∃ F, ⇑F = Wraw _ ![0,t]` and slash
  halves of it), so the two are homed together; node 1 is independent and could be
  read separately.

  Assumes: mathlib `v4.34.0` plus the port's `WLight.weierstrassP_qExpansion_package`
  (`ModularForms/WeightOne/LevelOneHauptmodul.lean`, the pin's `WLight` node) — nothing
  else from earlier modules of the port. The pin's `import Mathlib` is replaced by the
  modules the proofs name.
  Mathlib-first check (2026-10-20): `rg "lattice_eq_of_g2_eq|lattice_eq_of_.*g2"
  Mathlib/` and `rg "weierstrassP_torsion|qExpansion_coeff.*weierstrassP" Mathlib/` are
  empty; mathlib's `Analysis/SpecialFunctions/Elliptic/Weierstrass.lean` has `g₂`/`g₃`,
  `weierstrassP`, `derivWeierstrassP_sq` and the `PeriodPair` API but no
  invariants-determine-the-lattice theorem and no modular-form statement about `℘` at
  torsion points, so all three are supplements.

  spec-pin: Theorems/Thm_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq.lean
  spec-pin: P2M/Sol/S_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq.lean
  spec-pin: Theorems/Thm_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty.lean
  spec-pin: P2M/Sol/S_PeriodPair_weierstrassP_torsion_modularForm_slash_tendsto_atImInfty.lean
  spec-pin: Theorems/Thm_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff.lean
  spec-pin: P2M/Sol/S_PeriodPair_exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff.lean
-/

import FLTForHuman.ModularForms.WeightOne.LevelOneHauptmodul
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open Complex Filter Topology
open scoped PeriodPair

namespace PeriodPair
namespace LatticeFromInvariants

lemma weierstrassP_eq_except (L : PeriodPair) (z : ℂ) :
    ℘[L] z = (L.weierstrassPExcept 0) z + 1 / z ^ 2 := by
  have h := L.weierstrassPExcept_add ⟨0, zero_mem _⟩ z
  simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at h
  exact h.symm

lemma derivWeierstrassP_eq_except (L : PeriodPair) (z : ℂ) :
    ℘'[L] z = (L.derivWeierstrassPExcept 0) z - 2 / z ^ 3 := by
  have h := L.derivWeierstrassPExcept_sub ⟨0, zero_mem _⟩ z
  simp only [sub_zero] at h
  exact h.symm

lemma ode_except (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    (z ^ 3 * (L.derivWeierstrassPExcept 0) z - 2) ^ 2 -
      (4 * (z ^ 2 * (L.weierstrassPExcept 0) z + 1) ^ 3
        - L.g₂ * z ^ 4 * (z ^ 2 * (L.weierstrassPExcept 0) z + 1)
        - L.g₃ * z ^ 6) = 0 := by
  have hz0 : z ≠ 0 := fun h => hz (h ▸ zero_mem _)
  have hODE := L.derivWeierstrassP_sq z hz
  rw [weierstrassP_eq_except L z, derivWeierstrassP_eq_except L z] at hODE
  have key : (z ^ 3 * (L.derivWeierstrassPExcept 0) z - 2) ^ 2 -
      (4 * (z ^ 2 * (L.weierstrassPExcept 0) z + 1) ^ 3
        - L.g₂ * z ^ 4 * (z ^ 2 * (L.weierstrassPExcept 0) z + 1)
        - L.g₃ * z ^ 6) =
      z ^ 6 * (((L.derivWeierstrassPExcept 0) z - 2 / z ^ 3) ^ 2 -
        (4 * ((L.weierstrassPExcept 0) z + 1 / z ^ 2) ^ 3
          - L.g₂ * ((L.weierstrassPExcept 0) z + 1 / z ^ 2) - L.g₃)) := by
    field_simp
  rw [key, hODE, sub_self, mul_zero]

lemma eventuallyEq_zero (L L' : PeriodPair) (h₂ : L.g₂ = L'.g₂) (h₃ : L.g₃ = L'.g₃) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), ℘[L] z = ℘[L'] z := by
  have hP₁ : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 := L.analyticAt_weierstrassPExcept 0
  have hP₂ : AnalyticAt ℂ (L'.weierstrassPExcept 0) 0 := L'.analyticAt_weierstrassPExcept 0
  have hQ₁ : AnalyticAt ℂ (L.derivWeierstrassPExcept 0) 0 :=
    L.analyticAt_derivWeierstrassPExcept 0
  have hQ₂ : AnalyticAt ℂ (L'.derivWeierstrassPExcept 0) 0 :=
    L'.analyticAt_derivWeierstrassPExcept 0
  have hdP₁ : ∀ᶠ z in 𝓝 (0 : ℂ),
      deriv (L.weierstrassPExcept 0) z = (L.derivWeierstrassPExcept 0) z :=
    Filter.eventually_of_mem (L.compl_lattice_sdiff_singleton_mem_nhds 0)
      (L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0)
  have hdP₂ : ∀ᶠ z in 𝓝 (0 : ℂ),
      deriv (L'.weierstrassPExcept 0) z = (L'.derivWeierstrassPExcept 0) z :=
    Filter.eventually_of_mem (L'.compl_lattice_sdiff_singleton_mem_nhds 0)
      (L'.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0)

  suffices hD0 : ∀ᶠ z in 𝓝 (0 : ℂ),
      ((L.weierstrassPExcept 0) - (L'.weierstrassPExcept 0)) z = 0 by
    refine mem_nhdsWithin_of_mem_nhds ?_
    filter_upwards [hD0] with z hz
    rw [Pi.sub_apply, sub_eq_zero] at hz
    show ℘[L] z = ℘[L'] z
    rw [weierstrassP_eq_except L, weierstrassP_eq_except L', hz]
  by_contra hD0
  obtain ⟨m, E, hE, hE0, hDE⟩ :=
    (hP₁.sub hP₂).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hD0
  have hDE' : ∀ᶠ z in 𝓝 (0 : ℂ),
      ((L.weierstrassPExcept 0) - (L'.weierstrassPExcept 0)) z = z ^ m * E z := by
    filter_upwards [hDE] with z hz
    rw [hz, sub_zero, smul_eq_mul]

  have hderiv : ∀ᶠ z in 𝓝 (0 : ℂ),
      (L.derivWeierstrassPExcept 0) z - (L'.derivWeierstrassPExcept 0) z =
        (m : ℂ) * z ^ (m - 1) * E z + z ^ m * deriv E z := by
    have h1 : deriv ((L.weierstrassPExcept 0) - (L'.weierstrassPExcept 0)) =ᶠ[𝓝 0]
        deriv (fun z => z ^ m * E z) :=
      Filter.EventuallyEq.deriv hDE'
    filter_upwards [h1, hP₁.eventually_analyticAt, hP₂.eventually_analyticAt,
      hE.eventually_analyticAt, hdP₁, hdP₂] with z hz h1z h2z hEz hd1 hd2
    have lhs : deriv ((L.weierstrassPExcept 0) - (L'.weierstrassPExcept 0)) z =
        deriv (L.weierstrassPExcept 0) z - deriv (L'.weierstrassPExcept 0) z :=
      deriv_sub h1z.differentiableAt h2z.differentiableAt
    have rhs : deriv (fun z => z ^ m * E z) z =
        (m : ℂ) * z ^ (m - 1) * E z + z ^ m * deriv E z :=
      ((hasDerivAt_pow m z).mul hEz.differentiableAt.hasDerivAt).deriv
    rw [← hd1, ← hd2, ← lhs, hz, rhs]

  have key : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ((m : ℂ) * E z + z * deriv E z) *
          ((z ^ 3 * (L.derivWeierstrassPExcept 0) z - 2) +
            (z ^ 3 * (L'.derivWeierstrassPExcept 0) z - 2)) =
        E z * (4 * ((z ^ 2 * (L.weierstrassPExcept 0) z + 1) ^ 2 +
          (z ^ 2 * (L.weierstrassPExcept 0) z + 1) *
            (z ^ 2 * (L'.weierstrassPExcept 0) z + 1) +
            (z ^ 2 * (L'.weierstrassPExcept 0) z + 1) ^ 2) - L.g₂ * z ^ 4) := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
      mem_nhdsWithin_of_mem_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds 0),
      mem_nhdsWithin_of_mem_nhds hDE', mem_nhdsWithin_of_mem_nhds hderiv,
      self_mem_nhdsWithin] with z hz1 hz2 hz3 hz4 hz0
    have hz0' : z ≠ 0 := hz0
    simp only [Set.mem_compl_iff, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff,
      not_and, not_not] at hz1 hz2
    have hzL : z ∉ L.lattice := fun h => hz0' (hz1 h)
    have hzL' : z ∉ L'.lattice := fun h => hz0' (hz2 h)
    have H1 := ode_except L hzL
    have H2 := ode_except L' hzL'
    rw [← h₂, ← h₃] at H2
    have H3 : (L.weierstrassPExcept 0) z - (L'.weierstrassPExcept 0) z = z ^ m * E z :=
      hz3
    have H4 : z * ((L.derivWeierstrassPExcept 0) z - (L'.derivWeierstrassPExcept 0) z) =
        (m : ℂ) * z ^ m * E z + z ^ (m + 1) * deriv E z := by
      rw [hz4]
      rcases m.eq_zero_or_pos with hm | hm
      · subst hm; simp
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
        simp only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_one]
        ring
    apply mul_left_cancel₀ (pow_ne_zero (m + 2) hz0')
    linear_combination H1 - H2
      - z ^ 2 * ((z ^ 3 * (L.derivWeierstrassPExcept 0) z - 2) +
          (z ^ 3 * (L'.derivWeierstrassPExcept 0) z - 2)) * H4
      + z ^ 2 * (4 * ((z ^ 2 * (L.weierstrassPExcept 0) z + 1) ^ 2 +
          (z ^ 2 * (L.weierstrassPExcept 0) z + 1) *
            (z ^ 2 * (L'.weierstrassPExcept 0) z + 1) +
            (z ^ 2 * (L'.weierstrassPExcept 0) z + 1) ^ 2) - L.g₂ * z ^ 4) * H3

  have hEc : ContinuousAt E 0 := hE.continuousAt
  have hE'c : ContinuousAt (deriv E) 0 := hE.deriv.continuousAt
  have hP₁c := hP₁.continuousAt
  have hP₂c := hP₂.continuousAt
  have hQ₁c := hQ₁.continuousAt
  have hQ₂c := hQ₂.continuousAt
  have hcont1 : ContinuousAt (fun z : ℂ => ((m : ℂ) * E z + z * deriv E z) *
      ((z ^ 3 * (L.derivWeierstrassPExcept 0) z - 2) +
        (z ^ 3 * (L'.derivWeierstrassPExcept 0) z - 2))) 0 := by
    fun_prop
  have hcont2 : ContinuousAt (fun z : ℂ => E z *
      (4 * ((z ^ 2 * (L.weierstrassPExcept 0) z + 1) ^ 2 +
      (z ^ 2 * (L.weierstrassPExcept 0) z + 1) * (z ^ 2 * (L'.weierstrassPExcept 0) z + 1) +
        (z ^ 2 * (L'.weierstrassPExcept 0) z + 1) ^ 2) - L.g₂ * z ^ 4)) 0 := by
    fun_prop
  have hlim := tendsto_nhds_unique_of_eventuallyEq hcont1.continuousWithinAt.tendsto
    hcont2.continuousWithinAt.tendsto key
  have hlim' : ((m : ℂ) * E 0 + 0 * deriv E 0) *
      (((0 : ℂ) ^ 3 * (L.derivWeierstrassPExcept 0) 0 - 2) +
        ((0 : ℂ) ^ 3 * (L'.derivWeierstrassPExcept 0) 0 - 2)) =
      E 0 * (4 * (((0 : ℂ) ^ 2 * (L.weierstrassPExcept 0) 0 + 1) ^ 2 +
        ((0 : ℂ) ^ 2 * (L.weierstrassPExcept 0) 0 + 1) *
          ((0 : ℂ) ^ 2 * (L'.weierstrassPExcept 0) 0 + 1) +
          ((0 : ℂ) ^ 2 * (L'.weierstrassPExcept 0) 0 + 1) ^ 2) - L.g₂ * (0 : ℂ) ^ 4) := hlim
  have hm : (4 * (m : ℂ) + 12) ≠ 0 := by
    have : (4 * (m : ℂ) + 12) = ((4 * m + 12 : ℕ) : ℂ) := by push_cast; ring
    rw [this, Nat.cast_ne_zero]; omega
  apply hE0
  have h : E 0 * (4 * (m : ℂ) + 12) = 0 := by linear_combination -hlim'
  exact (mul_eq_zero.mp h).resolve_right hm

lemma lattice_le_of_eqOn (L L' : PeriodPair)
    (heq : Set.EqOn ℘[L] ℘[L'] ((L.lattice : Set ℂ) ∪ L'.lattice)ᶜ) :
    L.lattice ≤ L'.lattice := by
  intro x hx
  by_contra hx'
  have hU : ((L.lattice : Set ℂ) ∪ L'.lattice)ᶜ ∈ 𝓝[≠] x := by
    have h1 : ((L.lattice : Set ℂ) \ {x})ᶜ ∈ 𝓝[≠] x :=
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds x)
    have h2 : (L'.lattice : Set ℂ)ᶜ ∈ 𝓝[≠] x :=
      mem_nhdsWithin_of_mem_nhds (L'.isClosed_lattice.isOpen_compl.mem_nhds hx')
    filter_upwards [h1, h2, self_mem_nhdsWithin] with z hz1 hz2 hz3
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
      Set.mem_union, not_or] at hz1 hz2 hz3 ⊢
    exact ⟨fun h => hz1 ⟨h, hz3⟩, hz2⟩
  have hfeq : ℘[L] =ᶠ[𝓝[≠] x] ℘[L'] := Filter.eventually_of_mem hU heq
  have h₁ := L.order_weierstrassP x hx
  have h₂ := (L'.analyticOnNhd_weierstrassP x hx').meromorphicOrderAt_nonneg
  rw [← meromorphicOrderAt_congr hfeq, h₁] at h₂
  exact absurd h₂ (by decide)

lemma isPreconnected_compl_union (L L' : PeriodPair) :
    IsPreconnected ((L.lattice : Set ℂ) ∪ L'.lattice)ᶜ := by
  refine (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) ?_).isPreconnected
  refine Set.Countable.union ?_ ?_
  · exact Set.countable_coe_iff.mp (countable_of_Lindelof_of_discrete (X := L.lattice))
  · exact Set.countable_coe_iff.mp (countable_of_Lindelof_of_discrete (X := L'.lattice))

lemma eqOn_of_eventuallyEq_zero (L L' : PeriodPair)
    (h0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ℘[L] z = ℘[L'] z) :
    Set.EqOn ℘[L] ℘[L'] ((L.lattice : Set ℂ) ∪ L'.lattice)ᶜ := by
  set U : Set ℂ := ((L.lattice : Set ℂ) ∪ L'.lattice)ᶜ with hU
  have hUmem : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ U := by
    have h1 : ((L.lattice : Set ℂ) \ {0})ᶜ ∈ 𝓝[≠] (0 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0)
    have h2 : ((L'.lattice : Set ℂ) \ {0})ᶜ ∈ 𝓝[≠] (0 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (L'.compl_lattice_sdiff_singleton_mem_nhds 0)
    filter_upwards [h1, h2, self_mem_nhdsWithin] with z hz1 hz2 hz3
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe,
      Set.mem_union, not_or, hU] at hz1 hz2 hz3 ⊢
    exact ⟨fun h => hz1 ⟨h, hz3⟩, fun h => hz2 ⟨h, hz3⟩⟩

  have hboth : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ∀ᶠ w in 𝓝 z, w ∈ U ∧ ℘[L] w = ℘[L'] w := by
    have h := (hUmem.and h0)
    rw [eventually_nhdsWithin_iff] at h ⊢
    filter_upwards [h.eventually_nhds] with z hz hz0
    have hne : ∀ᶠ w in 𝓝 z, w ≠ (0 : ℂ) := isOpen_ne.mem_nhds hz0
    filter_upwards [hz, hne] with w hw hwne
    exact hw hwne
  obtain ⟨z₀, hz₀⟩ := hboth.exists
  have hz₀U : z₀ ∈ U := (hz₀.self_of_nhds).1
  have hfg : ℘[L] =ᶠ[𝓝 z₀] ℘[L'] := hz₀.mono fun w hw => hw.2
  have hf : AnalyticOnNhd ℂ ℘[L] U :=
    L.analyticOnNhd_weierstrassP.mono (Set.compl_subset_compl.2 Set.subset_union_left)
  have hg : AnalyticOnNhd ℂ ℘[L'] U :=
    L'.analyticOnNhd_weierstrassP.mono (Set.compl_subset_compl.2 Set.subset_union_right)
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (isPreconnected_compl_union L L') hz₀U hfg

end PeriodPair.LatticeFromInvariants

end

open PeriodPair.LatticeFromInvariants in

theorem PeriodPair.lattice_eq_of_g2_eq_of_g3_eq (L L' : PeriodPair)
    (h₂ : L.g₂ = L'.g₂) (h₃ : L.g₃ = L'.g₃) : L.lattice = L'.lattice := by
  have heq := eqOn_of_eventuallyEq_zero L L' (eventuallyEq_zero L L' h₂ h₃)
  refine le_antisymm (lattice_le_of_eqOn L L' heq) (lattice_le_of_eqOn L' L ?_)
  rw [Set.union_comm]
  exact heq.symm

open scoped MatrixGroups CongruenceSubgroup ModularForm Topology Manifold Matrix Real
open UpperHalfPlane hiding I
open Complex Filter

noncomputable section

namespace EIS2K1

variable (L : ℍ → PeriodPair) {N : ℕ}

def W (N : ℕ) (b : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (L τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / N)

abbrev redN (N : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod N) :=
  ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))

lemma redN_apply (γ : SL(2, ℤ)) (i j : Fin 2) : redN N γ i j = ((γ i j : ℤ) : ZMod N) := rfl

section Lattice

variable {L} (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
include hL

omit hL in

lemma weierstrassP_congr {L₁ L₂ : PeriodPair} (h : L₁.lattice = L₂.lattice) : L₁.weierstrassP = L₂.weierstrassP := by
  funext z
  simp only [PeriodPair.weierstrassP]
  rw [h]

omit hL in
lemma indep_of_im_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0) (γ : SL(2, ℤ)) :
    LinearIndependent ℝ ![((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ), ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
    rw [γ.prop] at this
    linarith

  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.smul_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero, smul_eq_mul, Complex.zero_im, Complex.add_re, Complex.smul_re, Complex.mul_re,
    sub_zero, Complex.zero_re] at him hre
  have h1 : (s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ)) * τ.im = 0 := by
    have : s * ((γ 0 0 : ℤ) * τ.im) + t * ((γ 1 0 : ℤ) * τ.im) = 0 := by exact_mod_cast him
    linarith
  have hA : s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hτ
  have hB : s * (γ 0 1 : ℤ) + t * (γ 1 1 : ℤ) = 0 := by
    have : s * ((γ 0 0 : ℤ) * τ.re + (γ 0 1 : ℤ)) + t * ((γ 1 0 : ℤ) * τ.re + (γ 1 1 : ℤ)) = 0 := by
      exact_mod_cast hre
    have h2 : (s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ)) * τ.re + (s * (γ 0 1 : ℤ) + t * (γ 1 1 : ℤ)) = 0 := by
      linarith
    rwa [hA, zero_mul, zero_add] at h2
  have hd : ((γ 0 0 : ℤ) : ℝ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hdet
  constructor
  · have : s = (s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ)) * (γ 1 1 : ℤ) - (s * (γ 0 1 : ℤ) + t * (γ 1 1 : ℤ)) * (γ 1 0 : ℤ) := by
      linear_combination (-s) * hd
    rw [this, hA, hB]; ring
  · have : t = -(s * (γ 0 0 : ℤ) + t * (γ 1 0 : ℤ)) * (γ 0 1 : ℤ) + (s * (γ 0 1 : ℤ) + t * (γ 1 1 : ℤ)) * (γ 0 0 : ℤ) := by
      linear_combination (-t) * hd
    rw [this, hA, hB]; ring

omit hL in

def pairγ (γ : SL(2, ℤ)) (τ : ℍ) : PeriodPair :=
  ⟨((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ), ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ), indep_of_im_ne_zero τ.im_ne_zero γ⟩

lemma lattice_L (τ : ℍ) : (L τ).lattice = Submodule.span ℤ {(τ : ℂ), 1} := by
  rw [PeriodPair.lattice, (hL τ).1, (hL τ).2]

lemma lattice_pairγ (γ : SL(2, ℤ)) (τ : ℍ) : (pairγ γ τ).lattice = (L τ).lattice := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.det_fin_two (γ : Matrix (Fin 2) (Fin 2) ℤ)
    rw [γ.prop] at this
    linarith
  rw [lattice_L hL, PeriodPair.lattice]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · rw [pairγ, SetLike.mem_coe, Submodule.mem_span_pair]
      exact ⟨γ 0 0, γ 0 1, by simp [zsmul_eq_mul]⟩
    · rw [pairγ, SetLike.mem_coe, Submodule.mem_span_pair]
      exact ⟨γ 1 0, γ 1 1, by simp [zsmul_eq_mul]⟩
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, Submodule.mem_span_pair]
      refine ⟨γ 1 1, -(γ 0 1), ?_⟩
      simp only [pairγ, zsmul_eq_mul, Int.cast_neg]
      have hd : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hdet
      linear_combination (τ : ℂ) * hd
    · rw [SetLike.mem_coe, Submodule.mem_span_pair]
      refine ⟨-(γ 1 0), γ 0 0, ?_⟩
      simp only [pairγ, zsmul_eq_mul, Int.cast_neg]
      have hd : ((γ 0 0 : ℤ) : ℂ) * (γ 1 1 : ℤ) - (γ 0 1 : ℤ) * (γ 1 0 : ℤ) = 1 := by exact_mod_cast hdet
      linear_combination hd

lemma weierstrassP_add_int (τ : ℍ) (z : ℂ) (m n : ℤ) :
    (L τ).weierstrassP (z + ((m : ℂ) * τ + n)) = (L τ).weierstrassP z := by
  have hmem : ((m : ℂ) * τ + n) ∈ (L τ).lattice := by
    rw [PeriodPair.mem_lattice]
    exact ⟨m, n, by rw [(hL τ).1, (hL τ).2, mul_one]⟩
  exact (L τ).weierstrassP_add_coe z ⟨_, hmem⟩

end Lattice

section Slash

variable {L} (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) [NeZero N]
include hL

lemma W_smul (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) (τ : ℍ) :
    W L N a (γ • τ) = (((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ)) ^ 2 *
      (L τ).weierstrassP
        (((((a 0).val * γ 0 0 + (a 1).val * γ 1 0 : ℤ) : ℂ) * τ + ((a 0).val * γ 0 1 + (a 1).val * γ 1 1 : ℤ)) / N) := by
  obtain ⟨-, -, -, -, h4⟩ := WLight.weierstrassP_qExpansion_package
  set de : ℂ := ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ) with hde
  set nu : ℂ := ((γ 0 0 : ℤ) : ℂ) * τ + (γ 0 1 : ℤ) with hnu
  have hde0 : de ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero γ τ
    simpa [denom, hde] using this
  have hcoe : ((γ • τ : ℍ) : ℂ) = nu / de := by
    simp [UpperHalfPlane.specialLinearGroup_apply, hnu, hde]

  have h1 : (L (γ • τ)).ω₁ = de⁻¹ * (pairγ γ τ).ω₁ := by
    rw [(hL _).1, hcoe]; simp only [pairγ]; rw [div_eq_inv_mul]
  have h2 : (L (γ • τ)).ω₂ = de⁻¹ * (pairγ γ τ).ω₂ := by
    rw [(hL _).2]; simp only [pairγ]; rw [← hde, inv_mul_cancel₀ hde0]
  set z : ℂ := ((((a 0).val * γ 0 0 + (a 1).val * γ 1 0 : ℤ) : ℂ) * τ +
      ((a 0).val * γ 0 1 + (a 1).val * γ 1 1 : ℤ)) / N with hz
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have harg : ((((a 0).val : ℂ) * ((γ • τ : ℍ) : ℂ) + (a 1).val) / N) = de⁻¹ * z := by
    rw [hcoe, hz]
    field_simp
    rw [hnu, hde]
    push_cast
    ring
  rw [W, harg, h4 (pairγ γ τ) (L (γ • τ)) de⁻¹ h1 h2 z, inv_inv, weierstrassP_congr (lattice_pairγ hL γ τ)]

theorem W_slash (a : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : W L N a ∣[(2 : ℤ)] γ = W L N (a ᵥ* redN N γ) := by
  funext τ
  rw [ModularForm.SL_slash_apply, W_smul hL a γ τ]
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) τ
      = ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ) := by
    simp [denom]
  have hde0 : ((γ 1 0 : ℤ) : ℂ) * τ + (γ 1 1 : ℤ) ≠ 0 := by
    rw [← hden]; exact UpperHalfPlane.denom_ne_zero _ τ
  rw [hden, mul_comm, ← mul_assoc, show (-(2 : ℤ)) = -((2 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast,
    inv_mul_cancel₀ (pow_ne_zero 2 hde0), one_mul]

  set A : ℤ := (a 0).val * γ 0 0 + (a 1).val * γ 1 0 with hA
  set B : ℤ := (a 0).val * γ 0 1 + (a 1).val * γ 1 1 with hB
  have hA' : (((a ᵥ* redN N γ) 0).val : ZMod N) = (A : ZMod N) := by
    rw [ZMod.natCast_zmod_val]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hA]
  have hB' : (((a ᵥ* redN N γ) 1).val : ZMod N) = (B : ZMod N) := by
    rw [ZMod.natCast_zmod_val]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hB]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (((a ᵥ* redN N γ) 0).val : ℤ) = A + N * m := by
    have : ((((((a ᵥ* redN N γ) 0).val : ℤ) - A : ℤ)) : ZMod N) = 0 := by
      push_cast; rw [hA', sub_self]
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    exact ⟨m, by linarith⟩
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (((a ᵥ* redN N γ) 1).val : ℤ) = B + N * n := by
    have : ((((((a ᵥ* redN N γ) 1).val : ℤ) - B : ℤ)) : ZMod N) = 0 := by
      push_cast; rw [hB', sub_self]
    obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
    exact ⟨n, by linarith⟩
  rw [W]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hval0 : (((a ᵥ* redN N γ) 0).val : ℂ) = ((A + N * m : ℤ) : ℂ) := by rw [← hm]; norm_cast
  have hval1 : (((a ᵥ* redN N γ) 1).val : ℂ) = ((B + N * n : ℤ) : ℂ) := by rw [← hn]; norm_cast
  rw [hval0, hval1]
  have : (((A + N * m : ℤ) : ℂ) * (τ : ℂ) + ((B + N * n : ℤ) : ℂ)) / N
      = (((A : ℂ)) * τ + B) / N + ((m : ℂ) * τ + n) := by
    push_cast; field_simp; ring
  rw [this, weierstrassP_add_int hL]

end Slash

section Limit

variable [NeZero N]

def qN (N : ℕ) (τ : ℍ) : ℂ := cexp (2 * π * I * (τ : ℂ) / N)
omit [NeZero N] in

lemma norm_qN (τ : ℍ) : ‖qN N τ‖ = Real.exp (-(2 * π * τ.im / N)) := by
  rw [qN, Complex.norm_exp]
  congr 1
  have : (2 * π * I * (τ : ℂ) / N) = ((-(2 * π * τ.im / N) : ℝ) : ℂ) + ((2 * π * τ.re / N : ℝ) : ℂ) * I := by
    have hτ : (τ : ℂ) = ((τ.re : ℝ) : ℂ) + ((τ.im : ℝ) : ℂ) * I := (Complex.re_add_im (τ : ℂ)).symm
    rw [hτ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]

lemma tendsto_qN : Tendsto (qN N) atImInfty (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_qN]
  have hc : 0 < 2 * π / (N : ℝ) := by
    have := NeZero.pos N
    positivity
  have h1 : Tendsto (fun τ : ℍ => -(2 * π * τ.im / N)) atImInfty atBot := by
    have h2 : Tendsto (fun τ : ℍ => (2 * π / N) * τ.im) atImInfty atTop := by
      rw [atImInfty]
      exact (tendsto_comap).const_mul_atTop hc
    have := tendsto_neg_atTop_atBot.comp h2
    refine this.congr fun τ => ?_
    simp only [Function.comp_apply]; ring
  exact Real.tendsto_exp_atBot.comp h1

def ρ (N : ℕ) : ℝ := Real.exp (-(2 * π / N))
omit [NeZero N] in

lemma ρ_pos : 0 < ρ N := Real.exp_pos _

lemma ρ_lt_one : ρ N < 1 := by
  have := NeZero.pos N
  have h : -(2 * π / (N : ℝ)) < 0 := by
    have : 0 < 2 * π / (N : ℝ) := by positivity
    linarith
  calc ρ N < Real.exp 0 := Real.exp_lt_exp.mpr h
    _ = 1 := Real.exp_zero

lemma norm_qN_le {τ : ℍ} (hτ : 1 ≤ τ.im) : ‖qN N τ‖ ≤ ρ N := by
  rw [norm_qN, ρ, Real.exp_le_exp, neg_le_neg_iff]
  have := NeZero.pos N
  have h : 2 * π / (N : ℝ) * 1 ≤ 2 * π / N * τ.im := mul_le_mul_of_nonneg_left hτ (by positivity)
  calc 2 * π / (N : ℝ) = 2 * π / N * 1 := by ring
    _ ≤ 2 * π / N * τ.im := h
    _ = 2 * π * τ.im / N := by ring

def ζ (N : ℕ) : ℂ := cexp (2 * π * I / N)
omit [NeZero N] in

lemma norm_ζ : ‖ζ N‖ = 1 := by
  rw [ζ, show (2 * π * I / N : ℂ) = ((2 * π / N : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

omit [NeZero N] in
lemma norm_ζ_pow (k : ℕ) : ‖ζ N ^ k‖ = 1 := by rw [norm_pow, norm_ζ, one_pow]

omit [NeZero N] in
lemma norm_ζ_inv_pow (k : ℕ) : ‖(ζ N)⁻¹ ^ k‖ = 1 := by rw [norm_pow, norm_inv, norm_ζ, inv_one, one_pow]

def term (N a₁ a₂ : ℕ) (p : ℕ+ × ℕ+) (τ : ℍ) : ℂ :=
  ((p.2 : ℕ) : ℂ) *
    (ζ N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
      2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ)))

def bound (N : ℕ) (p : ℕ+ × ℕ+) : ℝ := (4 * ρ N ^ ((p.1 : ℕ) - 1)) * (((p.2 : ℕ) : ℝ) * ρ N ^ (p.2 : ℕ))

lemma summable_bound : Summable (bound N) := by
  have hρ := ρ_lt_one (N := N)
  have hρ0 := (ρ_pos (N := N)).le
  have h1 : Summable fun p : ℕ+ => 4 * ρ N ^ ((p : ℕ) - 1) := by
    have hg : Summable fun n : ℕ => ρ N ^ n := summable_geometric_of_lt_one hρ0 hρ
    have : Summable fun p : ℕ+ => ρ N ^ ((p : ℕ) - 1) := by
      have := hg.comp_injective (i := fun p : ℕ+ => (p : ℕ) - 1) (fun p q h => by
        have hp := p.pos; have hq := q.pos
        exact PNat.eq (by simp only at h; omega))
      exact this
    exact this.mul_left 4
  have h2 : Summable fun p : ℕ+ => ((p : ℕ) : ℝ) * ρ N ^ (p : ℕ) := by
    have hg : Summable fun n : ℕ => (n : ℝ) ^ 1 * ρ N ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ)
    have := hg.comp_injective PNat.coe_injective
    simp at this
    exact this
  exact h1.mul_of_nonneg h2 (fun p => by positivity) (fun p => by positivity)

lemma exp_le (a₁ : ℕ) (ha₁ : a₁ < N) (p : ℕ+ × ℕ+) :
    (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ ((p.1 : ℕ) * N - a₁) * (p.2 : ℕ) ∧
    (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ ((p.1 : ℕ) * N + a₁) * (p.2 : ℕ) ∧
    (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ (p.1 : ℕ) * N * (p.2 : ℕ) := by
  have hp1 := p.1.pos
  have hp2 := p.2.pos
  set x : ℕ := (p.1 : ℕ) with hx
  set y : ℕ := (p.2 : ℕ) with hy
  have hxy : x - 1 + y ≤ x * y := by
    have : (x - 1) * 1 ≤ (x - 1) * y := Nat.mul_le_mul_left _ hp2
    have h' : x * y = (x - 1) * y + y := by
      rcases x with _ | x
      · omega
      · simp [Nat.succ_mul]
    omega
  have hxN : x ≤ x * N - a₁ := by
    have : x * N ≥ x + a₁ := by
      have hN1 : 1 + a₁ ≤ N := by omega
      calc x + a₁ ≤ x + x * a₁ := by nlinarith
        _ = x * (1 + a₁) := by ring
        _ ≤ x * N := Nat.mul_le_mul_left _ hN1
    omega
  refine ⟨le_trans hxy (Nat.mul_le_mul_right _ hxN), le_trans hxy (Nat.mul_le_mul_right _ ?_),
    le_trans hxy (Nat.mul_le_mul_right _ ?_)⟩
  · have := NeZero.pos N; nlinarith
  · have := NeZero.pos N; nlinarith

lemma norm_term_le (a₁ a₂ : ℕ) (ha₁ : a₁ < N) (p : ℕ+ × ℕ+) {τ : ℍ} (hτ : 1 ≤ τ.im) :
    ‖term N a₁ a₂ p τ‖ ≤ bound N p := by
  have hρ1 := (ρ_lt_one (N := N)).le
  have hρ0 := (ρ_pos (N := N)).le
  have hq : ‖qN N τ‖ ≤ ρ N := norm_qN_le hτ
  have hq0 : 0 ≤ ‖qN N τ‖ := norm_nonneg _
  obtain ⟨e1, e2, e3⟩ := exp_le a₁ ha₁ p (N := N)

  have hpow : ∀ e : ℕ, (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ e → ‖qN N τ ^ e‖ ≤ ρ N ^ ((p.1 : ℕ) - 1 + (p.2 : ℕ)) := by
    intro e he
    rw [norm_pow]
    calc ‖qN N τ‖ ^ e ≤ ρ N ^ e := pow_le_pow_left₀ hq0 hq e
      _ ≤ ρ N ^ ((p.1 : ℕ) - 1 + (p.2 : ℕ)) := pow_le_pow_of_le_one hρ0 hρ1 he
  set R : ℝ := ρ N ^ ((p.1 : ℕ) - 1 + (p.2 : ℕ)) with hR
  have hA : ‖ζ N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ))‖ ≤ R := by
    rw [norm_mul, norm_ζ_pow, one_mul]; exact hpow _ e2
  have hB : ‖(ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ))‖ ≤ R := by
    rw [norm_mul, norm_ζ_inv_pow, one_mul]; exact hpow _ e1
  have hC : ‖2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ))‖ ≤ 2 * R := by
    rw [norm_mul, Complex.norm_two]; exact mul_le_mul_of_nonneg_left (hpow _ e3) zero_le_two
  rw [term, norm_mul, Complex.norm_natCast]
  have hsum : ‖ζ N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
      (ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
      2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ))‖ ≤ 4 * R := by
    calc _ ≤ ‖ζ N ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
          (ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ)) * qN N τ ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ))‖ +
          ‖2 * qN N τ ^ ((p.1 : ℕ) * N * (p.2 : ℕ))‖ := norm_sub_le _ _
      _ ≤ (R + R) + 2 * R := add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hC
      _ = 4 * R := by ring
  calc ((p.2 : ℕ) : ℝ) * _ ≤ ((p.2 : ℕ) : ℝ) * (4 * R) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = bound N p := by rw [bound, hR, pow_add]; ring

lemma tendsto_term (a₁ a₂ : ℕ) (ha₁ : a₁ < N) (p : ℕ+ × ℕ+) :
    Tendsto (fun τ => term N a₁ a₂ p τ) atImInfty (𝓝 0) := by
  obtain ⟨e1, e2, e3⟩ := exp_le a₁ ha₁ p (N := N)
  have hpos : 0 < (p.1 : ℕ) - 1 + (p.2 : ℕ) := by have := p.2.pos; omega
  have hq : ∀ e : ℕ, (p.1 : ℕ) - 1 + (p.2 : ℕ) ≤ e → Tendsto (fun τ => qN N τ ^ e) atImInfty (𝓝 0) := by
    intro e he
    have := (tendsto_qN (N := N)).pow e
    rwa [zero_pow (by omega)] at this
  have h := ((((hq _ e2).const_mul (ζ N ^ (a₂ * (p.2 : ℕ)))).add ((hq _ e1).const_mul ((ζ N)⁻¹ ^ (a₂ * (p.2 : ℕ))))).sub
    ((hq _ e3).const_mul 2)).const_mul (((p.2 : ℕ) : ℂ))
  simp only [mul_zero, add_zero, sub_zero] at h
  exact h

lemma tendsto_tsum_term (a₁ a₂ : ℕ) (ha₁ : a₁ < N) :
    Tendsto (fun τ => ∑' p : ℕ+ × ℕ+, term N a₁ a₂ p τ) atImInfty (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty) (f := fun τ p => term N a₁ a₂ p τ)
    (g := fun _ => (0 : ℂ)) (bound := bound N) summable_bound (fun p => tendsto_term a₁ a₂ ha₁ p) ?_
  · simpa using h
  · have hev : ∀ᶠ τ : ℍ in atImInfty, (1 : ℝ) ≤ τ.im := (atImInfty_mem _).mpr ⟨1, fun _ h => h⟩
    filter_upwards [hev] with τ hτ p
    exact norm_term_le a₁ a₂ ha₁ p hτ

lemma tendsto_A (a₁ a₂ : ℕ) :
    Tendsto (fun τ => ζ N ^ a₂ * qN N τ ^ a₁ / (1 - ζ N ^ a₂ * qN N τ ^ a₁) ^ 2) atImInfty
      (𝓝 (if a₁ = 0 then ζ N ^ a₂ / (1 - ζ N ^ a₂) ^ 2 else 0)) := by
  by_cases ha : a₁ = 0
  · subst ha
    simp only [pow_zero, mul_one, ite_true]
    exact tendsto_const_nhds
  · rw [ite_eq_right ha]
    have hq : Tendsto (fun τ => ζ N ^ a₂ * qN N τ ^ a₁) atImInfty (𝓝 0) := by
      have := ((tendsto_qN (N := N)).pow a₁).const_mul (ζ N ^ a₂)
      rwa [zero_pow ha, mul_zero] at this
    have hden : Tendsto (fun τ => (1 - ζ N ^ a₂ * qN N τ ^ a₁) ^ 2) atImInfty (𝓝 1) := by
      have := ((tendsto_const_nhds (x := (1 : ℂ))).sub hq).pow 2
      simpa using this
    have := hq.div hden one_ne_zero
    simp at this
    exact this

lemma csc_identity (θ : ℂ) (hs : Complex.sin θ ≠ 0) :
    (2 * π * I) ^ 2 * (cexp (2 * (θ * I)) / (1 - cexp (2 * (θ * I))) ^ 2) = (π : ℂ) ^ 2 / Complex.sin θ ^ 2 := by
  set u : ℂ := cexp (θ * I) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hsin : Complex.sin θ = (u⁻¹ - u) * I / 2 := by
    have := Complex.two_sin θ
    rw [show -θ * I = -(θ * I) by ring, Complex.exp_neg, ← hu] at this
    linear_combination this / 2
  have h2 : cexp (2 * (θ * I)) = u ^ 2 := by rw [hu, ← Complex.exp_nat_mul]; norm_num
  have hden : 1 - u ^ 2 ≠ 0 := by
    intro h
    apply hs
    rw [hsin]
    have : u⁻¹ - u = u⁻¹ * (1 - u ^ 2) := by field_simp
    rw [this, h]; simp
  have hsub : u⁻¹ - u ≠ 0 := by
    intro h
    apply hden
    have : u⁻¹ = u := sub_eq_zero.mp h
    have h' : u * u⁻¹ = u * u := by rw [this]
    rw [mul_inv_cancel₀ hu0] at h'
    linear_combination h'
  have hsin2 : Complex.sin θ ^ 2 = -(u⁻¹ - u) ^ 2 / 4 := by
    rw [hsin, div_pow, mul_pow, Complex.I_sq]; ring
  have hI2 : (2 * π * I) ^ 2 = -4 * (π : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]; ring
  rw [h2, hI2, hsin2]
  field_simp

lemma sin_ne_zero {t : ℕ} (ht0 : t ≠ 0) (htN : t < N) : Complex.sin (π * t / N) ≠ 0 := by
  intro h
  rw [Complex.sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (t : ℂ) = (k : ℂ) * N := by
    have h0 : (π : ℂ) * t = k * π * N := (div_eq_iff hN).mp hk
    exact mul_left_cancel₀ hpi (by rw [h0]; ring)
  have h2 : (t : ℤ) = k * N := by exact_mod_cast h1
  have hk0 : 0 < k := by
    by_contra hle
    push Not at hle
    have : (t : ℤ) ≤ 0 := by rw [h2]; exact mul_nonpos_of_nonpos_of_nonneg hle (by positivity)
    omega
  have : (N : ℤ) ≤ t := by rw [h2]; nlinarith
  omega

variable {L} (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
include hL

theorem tendsto_W (a : Fin 2 → ZMod N) (ha : a ≠ 0) :
    Tendsto (W L N a) atImInfty
      (𝓝 (-((π : ℂ) ^ 2 / 3) + if a 0 = 0 then (π : ℂ) ^ 2 / Complex.sin (π * (a 1).val / N) ^ 2 else 0)) := by
  obtain ⟨-, -, -, h23, -⟩ := WLight.weierstrassP_qExpansion_package
  set a₁ : ℕ := (a 0).val with ha₁
  set a₂ : ℕ := (a 1).val with ha₂
  have ha₁N : a₁ < N := ZMod.val_lt _
  have ha₂N : a₂ < N := ZMod.val_lt _
  have hne : a₁ ≠ 0 ∨ a₂ ≠ 0 := by
    by_contra h
    push Not at h
    apply ha
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp h.1
    · exact (ZMod.val_eq_zero _).mp h.2
  obtain ⟨hexp, -⟩ := h23 L hL N a₁ a₂ ha₁N ha₂N hne

  have hW : W L N a = fun τ => (2 * π * I) ^ 2 *
      (ζ N ^ a₂ * qN N τ ^ a₁ / (1 - ζ N ^ a₂ * qN N τ ^ a₁) ^ 2 + 1 / 12 + ∑' p : ℕ+ × ℕ+, term N a₁ a₂ p τ) := by
    funext τ
    rw [W, ← ha₁, ← ha₂, hexp τ]
    rfl
  rw [hW]
  have hlim := (((tendsto_A a₁ a₂ (N := N)).add (tendsto_const_nhds (x := (1 / 12 : ℂ)))).add
    (tendsto_tsum_term a₁ a₂ ha₁N)).const_mul ((2 * π * I) ^ 2)
  refine hlim.congr' (Eventually.of_forall fun τ => rfl) |>.trans ?_

  apply le_of_eq
  congr 1
  rw [add_zero]
  have hval0 : a 0 = 0 ↔ a₁ = 0 := (ZMod.val_eq_zero (a 0)).symm
  by_cases h0 : a₁ = 0
  · rw [ite_eq_left h0, ite_eq_left (hval0.mpr h0)]
    have ha₂0 : a₂ ≠ 0 := hne.resolve_left (not_not.mpr h0)
    have hs := sin_ne_zero (N := N) ha₂0 ha₂N
    have hζ : ζ N ^ a₂ = cexp (2 * ((π * a₂ / N) * I)) := by
      rw [ζ, ← Complex.exp_nat_mul]
      congr 1
      ring
    rw [mul_add, hζ, csc_identity _ hs]
    have hI : (2 * π * I) ^ 2 = -4 * (π : ℂ) ^ 2 := by
      rw [mul_pow, Complex.I_sq]; ring
    rw [hI]
    ring
  · rw [ite_eq_right h0, ite_eq_right (fun h => h0 (hval0.mp h))]
    rw [mul_pow, Complex.I_sq]
    ring

end Limit

section MF

variable {L} (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) [NeZero N]
include hL

set_option linter.unusedSectionVars false in
lemma W_zero : W L N 0 = 0 := by
  funext τ
  simp [W, PeriodPair.weierstrassP_zero]

lemma mdifferentiable_W (a : Fin 2 → ZMod N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (W L N a) := by
  by_cases ha : a = 0
  · subst ha
    rw [W_zero hL]
    exact mdifferentiable_const
  · obtain ⟨-, -, -, h23, -⟩ := WLight.weierstrassP_qExpansion_package
    have hne : (a 0).val ≠ 0 ∨ (a 1).val ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      funext i
      fin_cases i
      · exact (ZMod.val_eq_zero _).mp h.1
      · exact (ZMod.val_eq_zero _).mp h.2
    exact (h23 L hL N (a 0).val (a 1).val (ZMod.val_lt _) (ZMod.val_lt _) hne).2

lemma isBoundedAtImInfty_W (a : Fin 2 → ZMod N) : IsBoundedAtImInfty (W L N a) := by
  by_cases ha : a = 0
  · subst ha
    rw [W_zero hL]
    exact UpperHalfPlane.zero_form_isBoundedAtImInfty
  · exact (tendsto_W hL a ha).isBigO_one ℝ

def sif (a : Fin 2 → ZMod N) : SlashInvariantForm Γ(N) 2 where
  toFun := W L N a
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Γ(N)), rfl⟩ := hA
    have h := W_slash hL a A
    have hred : redN N A = 1 := by
      rw [redN, CongruenceSubgroup.Gamma_mem'.mp hA]; rfl
    rw [hred, Matrix.vecMul_one] at h
    simpa [Matrix.SpecialLinearGroup.mapGL, ← ModularForm.SL_slash] using h

def mf (a : Fin 2 → ZMod N) : ModularForm Γ(N) 2 where
  toFun := W L N a
  slash_action_eq' := (sif hL a).slash_action_eq'
  holo' := mdifferentiable_W hL a
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    show IsBoundedAtImInfty (W L N a ∣[(2 : ℤ)] γ)
    rw [W_slash hL]
    exact isBoundedAtImInfty_W hL _

theorem main (a : Fin 2 → ZMod N) :
    (∃ F : ModularForm Γ(N) 2, ⇑F = W L N a) ∧
    (∀ γ : SL(2, ℤ), W L N a ∣[(2 : ℤ)] γ = W L N (a ᵥ* redN N γ)) ∧
    (a ≠ 0 → Tendsto (W L N a) atImInfty
      (𝓝 (-((π : ℂ) ^ 2 / 3) + if a 0 = 0 then (π : ℂ) ^ 2 / Complex.sin (π * (a 1).val / N) ^ 2 else 0))) :=
  ⟨⟨mf hL a, rfl⟩, W_slash hL a, tendsto_W hL a⟩

end MF

end EIS2K1

end

theorem PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty
    (L : UpperHalfPlane → PeriodPair) (hL : ∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N) :
    let W : (Fin 2 → ZMod N) → UpperHalfPlane → ℂ :=
      fun b τ => (L τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / N)
    (∃ F : ModularForm (CongruenceSubgroup.Gamma N) 2, ⇑F = W a) ∧
    (∀ γ : SL(2, ℤ), W a ∣[(2 : ℤ)] γ = W (a ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)))) ∧
    (a ≠ 0 → Filter.Tendsto (W a) UpperHalfPlane.atImInfty
      (𝓝 (-((π : ℂ) ^ 2 / 3) + if a 0 = 0 then (π : ℂ) ^ 2 / Complex.sin (π * (a 1).val / N) ^ 2 else 0))) :=
  EIS2K1.main hL a

noncomputable section

open UpperHalfPlane hiding I
open Complex Filter Function ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm Topology Manifold Matrix Real

namespace WPGamma1

theorem indep (τ : ℍ) : LinearIndependent ℝ ![(τ : ℂ), 1] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp only [Complex.add_im, Complex.smul_im, Complex.one_im, smul_eq_mul, mul_zero, add_zero,
    Complex.zero_im, Complex.add_re, Complex.smul_re, Complex.one_re, mul_one, Complex.zero_re] at him hre
  have hs : s = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h τ.im_ne_zero
  subst hs
  simp only [zero_mul, zero_add] at hre
  exact ⟨rfl, hre⟩

def L (τ : ℍ) : PeriodPair := ⟨τ, 1, indep τ⟩

theorem hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1 := fun _ => ⟨rfl, rfl⟩

theorem weierstrassP_eq_of_hL (L' : ℍ → PeriodPair)
    (hL' : ∀ τ : ℍ, (L' τ).ω₁ = (τ : ℂ) ∧ (L' τ).ω₂ = 1) (τ : ℍ) :
    (L' τ).weierstrassP = (L τ).weierstrassP := by
  have h : (L' τ).lattice = (L τ).lattice := by
    rw [PeriodPair.lattice, PeriodPair.lattice, (hL' τ).1, (hL' τ).2, (hL τ).1, (hL τ).2]
  funext z
  simp only [PeriodPair.weierstrassP]
  rw [h]

variable (M : ℕ) [NeZero M]

local notation "Γ₁ᴳ" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def Wraw (b : Fin 2 → ZMod M) (τ : ℍ) : ℂ :=
  (L τ).weierstrassP ((((b 0).val : ℂ) * (τ : ℂ) + (b 1).val) / M)

def cst : ℂ := 12 * ((2 * π * I) ^ 2)⁻¹

def Wfun (t : ZMod M) (τ : ℍ) : ℂ := cst * (L τ).weierstrassP ((t.val : ℂ) / M)

theorem Wfun_eq (t : ZMod M) : Wfun M t = cst • Wraw M ![0, t] := by
  funext τ
  simp [Wfun, Wraw, Pi.smul_apply, smul_eq_mul]

abbrev redN (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) (ZMod M) :=
  ((γ : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M))
omit [NeZero M] in

theorem redN_apply (γ : SL(2, ℤ)) (i j : Fin 2) : redN M γ i j = ((γ i j : ℤ) : ZMod M) := rfl

theorem K1 (t : ZMod M) :
    (∃ F : ModularForm Γ(M) 2, ⇑F = Wraw M ![0, t]) ∧
    (∀ γ : SL(2, ℤ), Wraw M ![0, t] ∣[(2 : ℤ)] γ = Wraw M (![0, t] ᵥ* redN M γ)) := by
  obtain ⟨h1, h2, -⟩ :=
    PeriodPair.weierstrassP_torsion_modularForm_slash_tendsto_atImInfty L hL M ![0, t]
  exact ⟨h1, h2⟩
omit [NeZero M] in

theorem vecMul_redN (t : ZMod M) (γ : SL(2, ℤ)) :
    (![0, t] ᵥ* redN M γ : Fin 2 → ZMod M) =
      ![t * ((γ 1 0 : ℤ) : ZMod M), t * ((γ 1 1 : ℤ) : ZMod M)] := by
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem Wfun_slash (t : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    Wfun M t ∣[(2 : ℤ)] γ = Wfun M (t * ((γ 1 1 : ℤ) : ZMod M)) := by
  have h10 : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
  rw [Wfun_eq, Wfun_eq, ModularForm.SL_smul_slash, (K1 M t).2 γ, vecMul_redN, h10, mul_zero]

theorem Wfun_slash_of_mem_Gamma1 (t : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 M) :
    Wfun M t ∣[(2 : ℤ)] γ = Wfun M t := by
  have h := (Gamma1_mem M γ).mp hγ
  rw [Wfun_slash M t γ (Gamma1_in_Gamma0 M hγ), h.2.1, mul_one]

def FΓ (t : ZMod M) : ModularForm Γ(M) 2 := cst • (K1 M t).1.choose

theorem coe_FΓ (t : ZMod M) : (⇑(FΓ M t) : ℍ → ℂ) = Wfun M t := by
  rw [FΓ, FunLike.coe_smul, (K1 M t).1.choose_spec, Wfun_eq]

def Wform (t : ZMod M) : ModularForm Γ₁ᴳ 2 where
  toFun := Wfun M t
  slash_action_eq' A hA := by
    obtain ⟨γ, hγ, rfl⟩ := hA
    have := Wfun_slash_of_mem_Gamma1 M t γ hγ
    rwa [ModularForm.SL_slash] at this
  holo' := by
    change MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Wfun M t)
    rw [← coe_FΓ M t]
    exact (FΓ M t).holo'
  bdd_at_cusps' {cu} hcu := by
    have hcu' : IsCusp cu Γ(M) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hcu ⊢
      exact hcu
    change cu.IsBoundedAt (Wfun M t) (2 : ℤ)
    rw [← coe_FΓ M t]
    exact (FΓ M t).bdd_at_cusps' hcu'

theorem coe_Wform (t : ZMod M) : (⇑(Wform M t) : ℍ → ℂ) = Wfun M t := rfl

theorem Wform_apply (t : ZMod M) (τ : ℍ) :
    Wform M t τ = 12 * ((2 * π * I) ^ 2)⁻¹ * (L τ).weierstrassP ((t.val : ℂ) / M) := rfl

section QExp

def ζ : ℂ := cexp (2 * π * I / M)

def chi (t : ZMod M) (d : ℕ) : ℂ := ζ M ^ (t.val * d) + (ζ M)⁻¹ ^ (t.val * d) - 2
omit [NeZero M] in

theorem norm_ζ : ‖ζ M‖ = 1 := by
  rw [ζ, show (2 * π * I / M : ℂ) = ((2 * π / M : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

omit [NeZero M] in
theorem norm_chi_le (t : ZMod M) (d : ℕ) : ‖chi M t d‖ ≤ 4 := by
  rw [chi]
  calc ‖ζ M ^ (t.val * d) + (ζ M)⁻¹ ^ (t.val * d) - 2‖
        ≤ ‖ζ M ^ (t.val * d) + (ζ M)⁻¹ ^ (t.val * d)‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖ζ M ^ (t.val * d)‖ + ‖(ζ M)⁻¹ ^ (t.val * d)‖) + ‖(2 : ℂ)‖ :=
        add_le_add (norm_add_le _ _) le_rfl
    _ = 4 := by
        rw [norm_pow, norm_pow, norm_inv, norm_ζ, inv_one, one_pow, Complex.norm_two]; norm_num

def acoef (t : ZMod M) (n : ℕ) : ℂ := ∑ d ∈ n.divisors, (d : ℂ) * chi M t d

def wc (t : ZMod M) (n : ℕ) : ℂ :=
  if n = 0 then 1 + 12 * ζ M ^ t.val / (1 - ζ M ^ t.val) ^ 2
  else 12 * ((∑ d ∈ n.divisors, (d : ℂ) * (ζ M ^ (t.val * d) + (ζ M)⁻¹ ^ (t.val * d))) -
    2 * ∑ d ∈ n.divisors, (d : ℂ))
omit [NeZero M] in

theorem wc_of_ne_zero (t : ZMod M) {n : ℕ} (hn : n ≠ 0) : wc M t n = 12 * acoef M t n := by
  rw [wc, ite_eq_right hn, acoef]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [chi]; ring

def qq (τ : ℍ) : ℂ := cexp (2 * π * I * (τ : ℂ))

theorem norm_qq_lt_one (τ : ℍ) : ‖qq τ‖ < 1 := norm_exp_two_pi_I_lt_one τ

theorem qParam_one (τ : ℍ) : Periodic.qParam 1 (τ : ℂ) = qq τ := by
  simp [Periodic.qParam, qq]

theorem qM_pow (τ : ℍ) : cexp (2 * π * I * (τ : ℂ) / M) ^ M = qq τ := by
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [qq, ← Complex.exp_nat_mul]
  congr 1
  field_simp

def term (t : ZMod M) (τ : ℍ) (p : ℕ+ × ℕ+) : ℂ :=
  ((p.2 : ℕ) : ℂ) * chi M t (p.2 : ℕ) * qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ))

omit [NeZero M] in
theorem summable_term (t : ZMod M) (τ : ℍ) : Summable (term M t τ) := by
  have hs : Summable fun c : ℕ+ × ℕ+ => ((c.2 : ℕ) : ℂ) ^ 1 * qq τ ^ ((c.1 : ℕ) * (c.2 : ℕ)) :=
    summable_prod_mul_pow 1 (norm_qq_lt_one τ)
  refine Summable.of_norm_bounded (g := fun c : ℕ+ × ℕ+ =>
    4 * ‖((c.2 : ℕ) : ℂ) ^ 1 * qq τ ^ ((c.1 : ℕ) * (c.2 : ℕ))‖) (hs.norm.mul_left 4) fun p => ?_
  simp only [pow_one]
  rw [term, norm_mul, norm_mul, norm_mul]
  calc ‖((p.2 : ℕ) : ℂ)‖ * ‖chi M t (p.2 : ℕ)‖ * ‖qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ))‖
        ≤ ‖((p.2 : ℕ) : ℂ)‖ * 4 * ‖qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ))‖ := by
          gcongr
          exact norm_chi_le M t _
    _ = 4 * (‖((p.2 : ℕ) : ℂ)‖ * ‖qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ))‖) := by ring

theorem Wfun_eq_tsum (t : ZMod M) (ht : t ≠ 0) (τ : ℍ) :
    Wfun M t τ = (1 + 12 * ζ M ^ t.val / (1 - ζ M ^ t.val) ^ 2) + 12 * ∑' p : ℕ+ × ℕ+, term M t τ p := by
  obtain ⟨-, -, -, h23, -⟩ := WLight.weierstrassP_qExpansion_package
  have htv : t.val ≠ 0 := fun h => ht ((ZMod.val_eq_zero t).mp h)
  obtain ⟨hexp, -⟩ := h23 L hL M 0 t.val (NeZero.pos M) (ZMod.val_lt t) (Or.inr htv)
  have h := hexp τ
  simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, mul_one, add_zero, Nat.sub_zero] at h
  have hI : (2 * π * I : ℂ) ^ 2 ≠ 0 := by
    apply pow_ne_zero
    simp [Real.pi_ne_zero, Complex.I_ne_zero]

  have hterm : (fun p : ℕ+ × ℕ+ => ((p.2 : ℕ) : ℂ) *
      (cexp (2 * π * I / M) ^ (t.val * (p.2 : ℕ)) * cexp (2 * π * I * (τ : ℂ) / M) ^ ((p.1 : ℕ) * M * (p.2 : ℕ)) +
        (cexp (2 * π * I / M))⁻¹ ^ (t.val * (p.2 : ℕ)) * cexp (2 * π * I * (τ : ℂ) / M) ^ ((p.1 : ℕ) * M * (p.2 : ℕ)) -
        2 * cexp (2 * π * I * (τ : ℂ) / M) ^ ((p.1 : ℕ) * M * (p.2 : ℕ)))) = term M t τ := by
    funext p
    have hq : cexp (2 * π * I * (τ : ℂ) / M) ^ ((p.1 : ℕ) * M * (p.2 : ℕ)) = qq τ ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
      rw [show (p.1 : ℕ) * M * (p.2 : ℕ) = M * ((p.1 : ℕ) * (p.2 : ℕ)) by ring, pow_mul, qM_pow]
    rw [hq, term, chi, ζ]
    ring
  rw [Wfun, h, hterm, cst, ζ]
  field_simp
  ring

omit [NeZero M] in
theorem hasSum_acoef (t : ZMod M) (τ : ℍ) :
    HasSum (fun n : ℕ+ => acoef M t n * qq τ ^ (n : ℕ)) (∑' p : ℕ+ × ℕ+, term M t τ p) := by
  have h0 : HasSum (term M t τ) (∑' p : ℕ+ × ℕ+, term M t τ p) := (summable_term M t τ).hasSum
  have h1 : HasSum (term M t τ ∘ sigmaAntidiagonalEquivProd) (∑' p : ℕ+ × ℕ+, term M t τ p) :=
    (Equiv.hasSum_iff sigmaAntidiagonalEquivProd).mpr h0
  refine h1.sigma fun n => ?_

  have hfin : ∑ c : ((n : ℕ).divisorsAntidiagonal : Set (ℕ × ℕ)),
      (term M t τ ∘ sigmaAntidiagonalEquivProd) ⟨n, c⟩ = acoef M t n * qq τ ^ (n : ℕ) := by
    have e1 : ∀ c : ((n : ℕ).divisorsAntidiagonal : Set (ℕ × ℕ)),
        (term M t τ ∘ sigmaAntidiagonalEquivProd) ⟨n, c⟩ =
          ((c.1.2 : ℕ) : ℂ) * chi M t c.1.2 * qq τ ^ (c.1.1 * c.1.2) := by
      intro c
      rfl
    simp_rw [e1]
    rw [show (∑ c : ((n : ℕ).divisorsAntidiagonal : Set (ℕ × ℕ)),
        ((c.1.2 : ℕ) : ℂ) * chi M t c.1.2 * qq τ ^ (c.1.1 * c.1.2)) =
        ∑ c ∈ ((n : ℕ).divisorsAntidiagonal).attach,
          ((c.1.2 : ℕ) : ℂ) * chi M t c.1.2 * qq τ ^ (c.1.1 * c.1.2) from rfl]
    rw [Finset.sum_attach ((n : ℕ).divisorsAntidiagonal)
      (fun c : ℕ × ℕ => ((c.2 : ℕ) : ℂ) * chi M t c.2 * qq τ ^ (c.1 * c.2))]
    have e2 : ∀ c ∈ (n : ℕ).divisorsAntidiagonal,
        ((c.2 : ℕ) : ℂ) * chi M t c.2 * qq τ ^ (c.1 * c.2) = ((c.2 : ℕ) : ℂ) * chi M t c.2 * qq τ ^ (n : ℕ) := by
      intro c hc
      rw [(Nat.mem_divisorsAntidiagonal.mp hc).1]
    rw [Finset.sum_congr rfl e2, Nat.sum_divisorsAntidiagonal' (fun _ j => ((j : ℕ) : ℂ) * chi M t j * qq τ ^ (n : ℕ)),
      acoef, Finset.sum_mul]
  rw [← hfin]
  exact hasSum_fintype _

theorem hasSum_wc (t : ZMod M) (ht : t ≠ 0) (τ : ℍ) :
    HasSum (fun n : ℕ => wc M t n • Periodic.qParam 1 (τ : ℂ) ^ n) (Wform M t τ) := by
  rw [coe_Wform, Wfun_eq_tsum M t ht τ]
  set A : ℂ := 1 + 12 * ζ M ^ t.val / (1 - ζ M ^ t.val) ^ 2 with hA
  set T : ℂ := ∑' p : ℕ+ × ℕ+, term M t τ p with hT

  set G : ℕ → ℂ := fun n => if n = 0 then 0 else 12 * (acoef M t n * qq τ ^ n) with hG
  have hG1 : HasSum G (12 * T) := by
    have h := (hasSum_acoef M t τ).mul_left 12
    have hzero : ∀ x ∉ Set.range (PNat.val), G x = 0 := by
      intro x hx
      have : x = 0 := by
        by_contra hx0
        exact hx ⟨⟨x, Nat.pos_of_ne_zero hx0⟩, rfl⟩
      rw [hG, this]; simp
    rw [← PNat.coe_injective.hasSum_iff hzero]
    refine h.congr_fun fun n => ?_
    simp [hG, n.ne_zero]
  have hG0 : HasSum (fun n : ℕ => if n = 0 then A else 0) A := hasSum_ite_eq 0 A
  have hsum := hG0.add hG1
  refine hsum.congr_fun fun n => ?_
  rw [qParam_one]
  by_cases hn : n = 0
  · subst hn
    simp [hG, wc, hA]
  · simp only [hG, ite_eq_right hn, wc_of_ne_zero M t hn, zero_add, smul_eq_mul]
    ring
omit [NeZero M] in

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  refine (Gamma1_mem M _).mpr ⟨?_, ?_, ?_⟩ <;> simp [ModularGroup.T]

omit [NeZero M] in
theorem one_mem_strictPeriods : (1 : ℝ) ∈ (Γ₁ᴳ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem qExpansion_Wform_coeff (t : ZMod M) (ht : t ≠ 0) (n : ℕ) :
    (qExpansion 1 (Wform M t)).coeff n = wc M t n :=
  (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods M)
    (f := Wform M t) (hasSum_wc M t ht) n).symm

end QExp

theorem main :
    ∃ W : ZMod M → ModularForm Γ₁ᴳ 2,
      (∀ (L' : ℍ → PeriodPair), (∀ τ : ℍ, (L' τ).ω₁ = (τ : ℂ) ∧ (L' τ).ω₂ = 1) →
        ∀ (t : ZMod M) (τ : ℍ),
          W t τ = 12 * ((2 * π * I) ^ 2)⁻¹ * (L' τ).weierstrassP ((t.val : ℂ) / M)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ Gamma0 M →
        (⇑(W t) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(W (t * ((γ 1 1 : ℤ) : ZMod M)))) ∧
      ∀ t : ZMod M, t ≠ 0 → ∀ n : ℕ,
        (qExpansion 1 (W t)).coeff n =
          if n = 0 then
            1 + 12 * cexp (2 * π * I / M) ^ t.val / (1 - cexp (2 * π * I / M) ^ t.val) ^ 2
          else
            12 * ((∑ d ∈ n.divisors, (d : ℂ) *
                (cexp (2 * π * I / M) ^ (t.val * d) + (cexp (2 * π * I / M))⁻¹ ^ (t.val * d))) -
              2 * ∑ d ∈ n.divisors, (d : ℂ)) := by
  refine ⟨Wform M, fun L' hL' t τ => ?_, fun t γ hγ => Wfun_slash M t γ hγ,
    fun t ht n => qExpansion_Wform_coeff M t ht n⟩
  rw [Wform_apply, weierstrassP_eq_of_hL L' hL' τ]

end WPGamma1

end

open scoped MatrixGroups ModularForm Real in

theorem PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff (M : ℕ) [NeZero M] :
    ∃ W : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2,
      (∀ (L : UpperHalfPlane → PeriodPair),
        (∀ τ : UpperHalfPlane, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) →
        ∀ (t : ZMod M) (τ : UpperHalfPlane),
          W t τ = 12 * ((2 * π * Complex.I) ^ 2)⁻¹ * (L τ).weierstrassP ((t.val : ℂ) / M)) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(W t) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(W (t * ((γ 1 1 : ℤ) : ZMod M)))) ∧
      ∀ t : ZMod M, t ≠ 0 → ∀ n : ℕ,
        (UpperHalfPlane.qExpansion 1 (W t)).coeff n =
          if n = 0 then
            1 + 12 * Complex.exp (2 * π * Complex.I / M) ^ t.val /
              (1 - Complex.exp (2 * π * Complex.I / M) ^ t.val) ^ 2
          else
            12 * ((∑ d ∈ n.divisors, (d : ℂ) *
                (Complex.exp (2 * π * Complex.I / M) ^ (t.val * d) +
                  (Complex.exp (2 * π * Complex.I / M))⁻¹ ^ (t.val * d))) -
              2 * ∑ d ∈ n.divisors, (d : ℂ)) :=
  WPGamma1.main M
