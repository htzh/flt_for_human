/-
  Squarefree values of the quadratic polynomial `x² + D` and of the positive
  definite binary quadratic forms `a² + t a b + n b²`:

      `∀ D ≥ 1, ∃ c ≥ 1, Squarefree (c² + D)`

      `t² < 4n → ∃ a b, b ≠ 0 ∧ Squarefree ((a² + t a b + n b²).toNat) ∧
        2 ≤ (a² + t a b + n b²).toNat`

  The port of the pin leaves

      `Nat.exists_squarefree_sq_add` (305 pin lines) and
      `Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul` (22),

  statements from their `Theorems/` wrappers and proofs from the matching
  `P2M/Sol/S_…` files. The pin's inner namespaces `K2Seam3.SqfreeSieve`, its
  `section Sieve`, its two `scoped` `Fact` instances and its abbreviations are
  kept verbatim; only the generated `kw_` prefixes are stripped to the port names
  (`kw_psq_dvd_of_not_dvd` → `psq_dvd_of_not_dvd`, `KwExistsSqfreeSqAdd` →
  `ExistsSqfreeSqAdd`), which is the checker's `kw_` normalisation on both sides
  and the port's residual-`kw` name guard.

  The mathematics. The sieve proves `KwExistsSqfreeSqAdd` by contradiction: for
  `f k = (2Dk + D + 1)² + D`, non-squarefree `f k` for all `k < K` puts each `k`
  in the set of roots of `f` modulo `p²` for some prime `p < P = 3DK` with
  `p ≥ 3`, `p ∤ D`. Nothing is `4` modulo `4` (`four_not_dvd_f`), a prime divisor
  of `D` never divides `f` (`primeDvdD_not_dvd_f`), and each such prime
  contributes at most `2 (K/p² + 1)` roots — `p² ∣ x² + D` and `p² ∣ y² + D` force
  `p² ∣ (x - y)` or `p² ∣ (x + y)` (`sqAdd_pm_congr`), so the residues `x mod p²`
  are at most two cosets (`perPrime_count`). Summing over `S ⊆ (2, P]` with
  `∑ p⁻² ≤ 4/9` (`sum_Ioc_inv_sq_le_sub`), against `|S| < K/18` from Chebyshev's
  `π(x) ≤ (log 4 + 1) x / log x`, gives `K < K`. The `Int` corollary instantiates
  `D = 4n - t²` at `c - t` and `b = 2`.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  spec-pin: Theorems/Thm_Nat_exists_squarefree_sq_add.lean
  spec-pin: P2M/Sol/S_Nat_exists_squarefree_sq_add.lean
  spec-pin: Theorems/Thm_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul.lean
  spec-pin: P2M/Sol/S_Int_exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul.lean
  Drift against `v4.34.0` — statements untouched; the pin's `kw_` names are rewritten
  only because `norm` erases the prefix on both sides and the port's name guard rejects
  a residual `kw`.

  * port:86, 92, 105, 131, 210, 220, 231 — `KwExistsSqfreeSqAdd` →
    `ExistsSqfreeSqAdd`, `kw_psq_dvd_of_not_dvd` → `psq_dvd_of_not_dvd`,
    `kw_sqAdd_pm_congr` → `sqAdd_pm_congr`, `kw_perPrime_count` → `perPrime_count`,
    `kw_four_not_dvd_f` → `four_not_dvd_f`, `kw_primeDvdD_not_dvd_f` →
    `primeDvdD_not_dvd_f`, `kw_existsSqfreeSqAdd_proved` →
    `existsSqfreeSqAdd_proved`.
  * port:74 — the pin's `p2m_open "Finset Nat Finset.Nat Real Filter"` is written
    `open Finset Nat Finset.Nat Real Filter`; its `p2m_reactivate` lines are dropped.
  * port:222 — `haveI := Fact.mk hp` → `have := Fact.mk hp`
    (`linter.style.haveILetI`, Lean's own suggestion; `Fact` is `Prop`-valued, so the
    instance is still found).
  * port:371–373 — the pin's `end K2Seam3.SqfreeSieve` is written as two bare `end`s:
    the checker's namespace tracker closes one scope per `end`, and the one-line form
    de-nests the two headlines into `K2Seam3` (`K2Seam3.Nat.exists_squarefree_sq_add`).
  * the pin's `set_option linter.unusedSectionVars false` was not needed and is not
    carried.

-/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Finset Nat Finset.Nat Real Filter

noncomputable section

namespace K2Seam3
namespace SqfreeSieve

scoped instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by norm_num⟩
scoped instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The pin's abbreviation for the statement of the node: every `D ≥ 1` is a
squarefree value of `x² + D` at some `x ≥ 1`. -/
abbrev ExistsSqfreeSqAdd : Prop :=
  ∀ D : ℕ, 1 ≤ D → ∃ c : ℕ, 1 ≤ c ∧ Squarefree (c ^ 2 + D)

section Sieve

/-- If `p ∤ a` and `p² ∣ a b` then `p² ∣ b`. -/
lemma psq_dvd_of_not_dvd {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : ¬ (p : ℤ) ∣ a) (hab : (p : ℤ)^2 ∣ a * b) : (p : ℤ)^2 ∣ b := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpb : (p : ℤ) ∣ b :=
    (hpZ.dvd_mul.mp (dvd_trans ⟨(p : ℤ), (sq (p : ℤ))⟩ hab)).resolve_left ha
  obtain ⟨c, rfl⟩ := hpb
  rw [show a * ((p : ℤ) * c) = (p : ℤ) * (a * c) by ring, sq] at hab
  have hpac := (mul_dvd_mul_iff_left (a := (p : ℤ))
    (by exact_mod_cast hp.ne_zero)).mp hab
  obtain ⟨d, rfl⟩ := (hpZ.dvd_mul.mp hpac).resolve_left ha
  exact ⟨d, by ring⟩

/-- Two roots of `x² + D` modulo `p²` (`p` odd, `p ∤ D`) are congruent up to sign. -/
lemma sqAdd_pm_congr {p D : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpD : ¬ p ∣ D)
    {x y : ℤ} (hx : (p : ℤ)^2 ∣ x^2 + D) (hy : (p : ℤ)^2 ∣ y^2 + D) :
    (p : ℤ)^2 ∣ (x - y) ∨ (p : ℤ)^2 ∣ (x + y) := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdiff : (p : ℤ)^2 ∣ (x - y) * (x + y) := by
    have h := dvd_sub hx hy
    have heq : x^2 + (D : ℤ) - (y^2 + D) = (x - y) * (x + y) := by ring
    rwa [heq] at h
  have hnx : ¬ (p : ℤ) ∣ x := fun hd => hpD <| by
    have hpxD : (p : ℤ) ∣ x^2 + D := dvd_trans ⟨(p : ℤ), (sq (p : ℤ))⟩ hx
    have hpD' : (p : ℤ) ∣ (D : ℤ) := by
      have := dvd_sub hpxD (dvd_pow hd two_ne_zero); simpa using this
    exact_mod_cast hpD'
  by_cases hxmy : (p : ℤ) ∣ (x - y)
  · by_cases hxpy : (p : ℤ) ∣ (x + y)
    · exfalso
      have h2x : (p : ℤ) ∣ 2 * x := by
        have := dvd_add hxmy hxpy; simpa [two_mul] using this
      rcases hpZ.dvd_mul.mp h2x with h2 | hx'
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by exact_mod_cast h2))
      · exact hnx hx'
    · exact Or.inl (psq_dvd_of_not_dvd hp hxpy (by rwa [mul_comm] at hdiff))
  · exact Or.inr (psq_dvd_of_not_dvd hp hxmy hdiff)

/-- Each prime `p ≥ 3` not dividing `D` is a root of `f` modulo `p²` for at most
`2 (K/p² + 1)` values of `k < K`. -/
lemma perPrime_count {D K p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hpD : ¬ p ∣ D) :
    ((Finset.range K).filter (fun k => p^2 ∣ (2*D*k + D + 1)^2 + D)).card
      ≤ 2 * (K / p^2 + 1) := by
  classical
  set c : ℕ → ℤ := fun k => (2*D*k + D + 1 : ℤ) with hc_def
  set Bad := (Finset.range K).filter (fun k => p^2 ∣ (2*D*k + D + 1)^2 + D) with hBad_def
  rcases Bad.eq_empty_or_nonempty with hemp | ⟨k₀, hk₀⟩
  · rw [hemp]; simp
  have hp2pos : 0 < p^2 := by positivity
  have hp2 : p ≠ 2 := by omega
  have hp2D : ¬ (p : ℤ) ∣ (2 * D : ℤ) := fun h => by
    rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp h with h2 | hd
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (by exact_mod_cast h2))
    · exact hpD (by exact_mod_cast hd)
  have hceq : ∀ k, (c k)^2 + (D:ℤ) = (((2*D*k + D + 1)^2 + D : ℕ) : ℤ) := fun k => by
    simp only [c]; push_cast; ring
  have hfc : ∀ k, p^2 ∣ (2*D*k + D + 1)^2 + D ↔ (p:ℤ)^2 ∣ (c k)^2 + D := fun k => by
    rw [hceq, show ((p:ℤ)^2) = ((p^2:ℕ):ℤ) by push_cast; ring]
    exact Int.natCast_dvd_natCast.symm
  have hk₀' : (p:ℤ)^2 ∣ (c k₀)^2 + D := (hfc k₀).mp (Finset.mem_filter.mp hk₀).2
  let g : ℕ → Bool × ℕ := fun k => (decide ((p:ℤ)^2 ∣ c k - c k₀), k / p^2)
  have hinj : Set.InjOn g Bad := by
    intro a haB b hbB hab
    simp only [g, Prod.mk.injEq, decide_eq_decide] at hab
    obtain ⟨hd, hq⟩ := hab
    have ha' := (hfc a).mp (Finset.mem_filter.mp haB).2
    have hb' := (hfc b).mp (Finset.mem_filter.mp hbB).2
    have hda := sqAdd_pm_congr hp hp2 hpD ha' hk₀'
    have hdb := sqAdd_pm_congr hp hp2 hpD hb' hk₀'
    have hcab : (p:ℤ)^2 ∣ c a - c b := by
      by_cases hca : (p:ℤ)^2 ∣ c a - c k₀
      · have hcb : (p:ℤ)^2 ∣ c b - c k₀ := hd.mp hca
        have := dvd_sub hca hcb; simpa using this
      · have hca' : (p:ℤ)^2 ∣ c a + c k₀ := hda.resolve_left hca
        have hcb' : (p:ℤ)^2 ∣ c b + c k₀ := hdb.resolve_left (fun h => hca (hd.mpr h))
        have := dvd_sub hca' hcb'; simpa using this
    have hcabeq : c a - c b = (2*D : ℤ) * ((a:ℤ) - b) := by
      simp only [c]; ring
    rw [hcabeq] at hcab
    have hkab : (p:ℤ)^2 ∣ ((a:ℤ) - b) := psq_dvd_of_not_dvd hp hp2D hcab

    have h1 := Nat.div_add_mod a (p^2)
    have h2 := Nat.div_add_mod b (p^2)
    have heq : (a:ℤ) - b = ((a % p^2 : ℕ) : ℤ) - ((b % p^2 : ℕ) : ℤ) := by
      set Q : ℕ := p^2 * (a / p^2) with hQ
      have hQb : p^2 * (b / p^2) = Q := by rw [hQ, hq]
      have hZ1 : (a:ℤ) = (Q:ℤ) + ((a % p^2 : ℕ):ℤ) := by exact_mod_cast h1.symm
      have hZ2 : (b:ℤ) = (Q:ℤ) + ((b % p^2 : ℕ):ℤ) := by
        rw [← hQb] at hQ ⊢; exact_mod_cast h2.symm
      linarith
    rw [heq] at hkab
    obtain ⟨m, hm⟩ := hkab
    have ha' : ((a % p^2 : ℕ):ℤ) < ((p^2:ℕ):ℤ) := by exact_mod_cast Nat.mod_lt a hp2pos
    have hb' : ((b % p^2 : ℕ):ℤ) < ((p^2:ℕ):ℤ) := by exact_mod_cast Nat.mod_lt b hp2pos
    have ha0 : (0:ℤ) ≤ ((a % p^2 : ℕ):ℤ) := Int.natCast_nonneg _
    have hb0 : (0:ℤ) ≤ ((b % p^2 : ℕ):ℤ) := Int.natCast_nonneg _
    have hpc : ((p^2:ℕ):ℤ) = (p:ℤ)^2 := by push_cast; ring
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with hneg | h0 | hpos
      · exfalso; nlinarith [hm, hpc]
      · exact h0
      · exfalso; nlinarith [hm, hpc]
    have hmodeq : a % p^2 = b % p^2 := by
      have : ((a % p^2 : ℕ):ℤ) = ((b % p^2 : ℕ):ℤ) := by rw [hm0, mul_zero] at hm; linarith
      exact_mod_cast this
    omega
  calc Bad.card
      ≤ ((Finset.univ : Finset Bool) ×ˢ Finset.range (K / p^2 + 1)).card := by
        apply Finset.card_le_card_of_injOn g ?_ hinj
        intro k hk
        have hkK : k < K := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
        have hdiv : k / p^2 ≤ K / p^2 := Nat.div_le_div_right (le_of_lt hkK)
        refine Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩
        simp only [g, Finset.mem_range]; omega
    _ = 2 * (K / p^2 + 1) := by
        rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool]

/-- `f k = (2Dk + D + 1)² + D` is never divisible by `4`. -/
lemma four_not_dvd_f (D k : ℕ) : ¬ (4 : ℕ) ∣ ((2*D*k + D + 1)^2 + D) := by
  have hexp : (2*D*k + D + 1)^2 + D = 4*(D^2*k^2 + D^2*k + D*k) + (D^2 + 3*D + 1) := by ring
  intro h; rw [hexp] at h
  have h4 : (4 : ℕ) ∣ (D^2 + 3*D + 1) := (Nat.dvd_add_right ⟨_, rfl⟩).mp h
  have hZ : ((D:ZMod 4)^2 + 3*(D:ZMod 4) + 1 : ZMod 4) = 0 := by
    have := (ZMod.natCast_eq_zero_iff (D^2 + 3*D + 1) 4).mpr h4
    push_cast at this; linear_combination this
  exact (by decide : ∀ d : ZMod 4, d^2 + 3*d + 1 ≠ 0) _ hZ

/-- A prime divisor of `D` never divides `f k`. -/
lemma primeDvdD_not_dvd_f {D p : ℕ} (k : ℕ) (hp : p.Prime) (hpD : p ∣ D) :
    ¬ p ∣ ((2*D*k + D + 1)^2 + D) := by
  have := Fact.mk hp
  intro h
  have hZ : (((2*D*k + D + 1)^2 + D : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
  have hDZ : ((D : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hpD
  push_cast at hZ
  rw [hDZ] at hZ; ring_nf at hZ
  exact one_ne_zero hZ

/-- The sieve: `ExistsSqfreeSqAdd` is proved. -/
theorem existsSqfreeSqAdd_proved : ExistsSqfreeSqAdd := by
  intro D hD
  set f : ℕ → ℕ := fun k => (2*D*k + D + 1)^2 + D with hf_def
  suffices h : ∃ k, Squarefree (f k) by
    obtain ⟨k, hk⟩ := h; exact ⟨2*D*k + D + 1, by omega, hk⟩
  by_contra hcon; push Not at hcon

  obtain ⟨N₀, hN₀⟩ :=
    eventually_atTop.mp (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)

  have htend : Tendsto (fun K : ℕ => (3 * D * K : ℝ)) atTop atTop := by
    refine (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0:ℝ) < 3*D)).congr ?_
    intro K; ring
  obtain ⟨K, hKlog, hKN, hK1⟩ :
      ∃ K : ℕ, 54 * D * (Real.log 4 + 1) < Real.log (3 * D * K)
        ∧ max N₀ 3 ≤ (3 * D * K : ℝ) ∧ 1 ≤ K :=
    (((Real.tendsto_log_atTop.comp htend).eventually_gt_atTop _).and
      ((htend.eventually_ge_atTop (max N₀ 3)).and (eventually_ge_atTop 1))).exists
  set P := 3 * D * K with hP_def
  have hPR : (P : ℝ) = 3 * (D : ℝ) * K := by rw [hP_def]; push_cast; ring
  have hP3 : (3 : ℝ) ≤ (P : ℝ) := by rw [hPR]; exact le_trans (le_max_right _ _) hKN
  have hPN₀ : N₀ ≤ (P : ℝ) := by rw [hPR]; exact le_trans (le_max_left _ _) hKN
  have hPnat3 : 3 ≤ P := by exact_mod_cast hP3
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  rw [← hPR] at hKlog

  set S := (Finset.range P).filter (fun p => p.Prime ∧ 3 ≤ p ∧ ¬ p ∣ D) with hS_def

  have hcov : Finset.range K ⊆ S.biUnion fun p => (Finset.range K).filter (p^2 ∣ f ·) := by
    intro k hkK
    have hns := hcon k
    rw [Nat.squarefree_iff_prime_squarefree] at hns; push Not at hns
    obtain ⟨p, hp, hdvd⟩ := hns
    rw [← sq] at hdvd
    have hp3 : 3 ≤ p := by
      by_contra h3
      interval_cases p
      · exact absurd hp (by decide)
      · exact absurd hp (by decide)
      · exact four_not_dvd_f D k (by simpa using hdvd)
    have hpnD : ¬ p ∣ D := fun hpD =>
      primeDvdD_not_dvd_f k hp hpD (dvd_trans (dvd_pow_self p two_ne_zero) hdvd)
    have hpP : p < P := by
      have hfpos : 0 < f k := by simp only [hf_def]; positivity
      have hple : p^2 ≤ f k := Nat.le_of_dvd hfpos hdvd
      have hkK' : k + 1 ≤ K := Finset.mem_range.mp hkK
      have hck : 2*D*k + D + 2 ≤ P := by nlinarith
      have hfk : f k < P^2 := by
        simp only [hf_def]
        calc (2*D*k+D+1)^2 + D
            < (2*D*k+D+1)^2 + (2*(2*D*k+D+1) + 1) := by omega
          _ = (2*D*k+D+2)^2 := by ring
          _ ≤ P^2 := Nat.pow_le_pow_left hck 2
      nlinarith [hp.two_le]
    exact Finset.mem_biUnion.mpr ⟨p,
      by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨hpP, hp, hp3, hpnD⟩,
      Finset.mem_filter.mpr ⟨hkK, hdvd⟩⟩

  have hKle : (K : ℝ) ≤ ∑ p ∈ S, (((Finset.range K).filter (p^2 ∣ f ·)).card : ℝ) := by
    have h1 : K ≤ ∑ p ∈ S, ((Finset.range K).filter (p^2 ∣ f ·)).card :=
      calc K = (Finset.range K).card := (Finset.card_range K).symm
        _ ≤ (S.biUnion fun p => (Finset.range K).filter (p^2 ∣ f ·)).card :=
            Finset.card_le_card hcov
        _ ≤ _ := Finset.card_biUnion_le
    exact_mod_cast h1

  have hper : ∀ p ∈ S, (((Finset.range K).filter (p^2 ∣ f ·)).card : ℝ)
      ≤ 2 * K * ((p:ℝ)^2)⁻¹ + 2 := by
    intro p hpS
    simp only [S, Finset.mem_filter, Finset.mem_range] at hpS
    obtain ⟨_, hp, hp3, hpnD⟩ := hpS
    have hNat : ((Finset.range K).filter (p^2 ∣ f ·)).card ≤ 2 * (K / p^2 + 1) := by
      simp only [hf_def]; exact perPrime_count hp hp3 hpnD
    calc (((Finset.range K).filter (p^2 ∣ f ·)).card : ℝ)
        ≤ (2 * (K / p^2 + 1) : ℕ) := by exact_mod_cast hNat
      _ = 2 * ((K / p^2 : ℕ) : ℝ) + 2 := by push_cast; ring
      _ ≤ 2 * ((K : ℝ) / (p^2 : ℕ)) + 2 := by
          gcongr; exact Nat.cast_div_le
      _ = 2 * K * ((p:ℝ)^2)⁻¹ + 2 := by push_cast; ring

  have hSsub : S ⊆ Finset.Ioc 2 P := by
    intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_range] at hp
    simp only [Finset.mem_Ioc]; omega
  have hsumInv : ∑ p ∈ S, ((p:ℝ)^2)⁻¹ ≤ 4/9 := by
    calc ∑ p ∈ S, ((p:ℝ)^2)⁻¹
        ≤ ∑ p ∈ Finset.Ioc 2 P, ((p:ℝ)^2)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
          intros; positivity
      _ = ((3:ℝ)^2)⁻¹ + ∑ p ∈ Finset.Ioc 3 P, ((p:ℝ)^2)⁻¹ := by
          rw [show Finset.Ioc 2 P = insert 3 (Finset.Ioc 3 P) by
            ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega]
          rw [Finset.sum_insert (by simp)]; norm_num
      _ ≤ 1/9 + ((3:ℝ)⁻¹ - (P:ℝ)⁻¹) := by
          gcongr
          · norm_num
          · exact sum_Ioc_inv_sq_le_sub (by norm_num) hPnat3
      _ ≤ 4/9 := by
          have hPinv : 0 ≤ (P:ℝ)⁻¹ := by positivity
          linarith

  have hScard : (S.card : ℝ) < K / 18 := by
    have hSle : S.card ≤ P.primeCounting := by
      calc S.card ≤ ((Finset.range P).filter Nat.Prime).card := by
            apply Finset.card_le_card; intro p hp
            simp only [S, Finset.mem_filter, Finset.mem_range] at hp ⊢
            exact ⟨hp.1, hp.2.1⟩
        _ = P.primesBelow.card := by rfl
        _ = P.primeCounting' := Nat.primesBelow_card_eq_primeCounting' P
        _ = (P - 1).primeCounting := (Nat.primeCounting_sub_one P).symm
        _ ≤ P.primeCounting := Nat.monotone_primeCounting (Nat.sub_le P 1)
    have hπ : (P.primeCounting : ℝ) ≤ (Real.log 4 + 1) * P / Real.log P := by
      have := hN₀ (P : ℝ) hPN₀
      simpa using this
    calc (S.card : ℝ) ≤ P.primeCounting := by exact_mod_cast hSle
      _ ≤ (Real.log 4 + 1) * P / Real.log P := hπ
      _ < K / 18 := by
          rw [div_lt_div_iff₀ hlogP (by norm_num : (0:ℝ) < 18)]
          have hl4 : 0 < Real.log 4 + 1 := by positivity
          have hPpos : (0:ℝ) < (P:ℝ) := by linarith

          have hkey : (Real.log 4 + 1) * (P:ℝ) * 18 = (K:ℝ) * (54 * D * (Real.log 4 + 1)) := by
            rw [hPR]; ring
          nlinarith [hKlog, hkey, mul_pos (show (0:ℝ) < K by positivity)
            (sub_pos.mpr hKlog)]

  have hcontra : (K : ℝ) < K := by
    calc (K : ℝ)
        ≤ ∑ p ∈ S, (((Finset.range K).filter (p^2 ∣ f ·)).card : ℝ) := hKle
      _ ≤ ∑ p ∈ S, (2 * K * ((p:ℝ)^2)⁻¹ + 2) := Finset.sum_le_sum hper
      _ = 2 * K * ∑ p ∈ S, ((p:ℝ)^2)⁻¹ + 2 * S.card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ 2 * K * (4/9) + 2 * S.card := by gcongr
      _ < 2 * K * (4/9) + 2 * (K / 18) := by linarith [hScard]
      _ = K := by ring
  exact absurd hcontra (lt_irrefl _)

end Sieve

end SqfreeSieve

end K2Seam3

namespace Nat

/-- Every `D ≥ 1` is a squarefree value of `x² + D` at some `x ≥ 1`. -/
theorem exists_squarefree_sq_add (D : ℕ) (hD : 1 ≤ D) :
    ∃ c : ℕ, 1 ≤ c ∧ Squarefree (c ^ 2 + D) :=
  K2Seam3.SqfreeSieve.existsSqfreeSqAdd_proved D hD

end Nat

namespace Int

/-- Every positive definite binary quadratic form `a² + t a b + n b²` (`t² < 4n`)
represents a squarefree integer at least `2`. -/
theorem exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul (t n : ℤ) (h : t ^ 2 < 4 * n) :
    ∃ a b : ℤ, b ≠ 0 ∧ Squarefree (a ^ 2 + t * a * b + n * b ^ 2).toNat ∧
      2 ≤ (a ^ 2 + t * a * b + n * b ^ 2).toNat := by
  set D : ℕ := (4 * n - t ^ 2).toNat with hD_def
  have hD1 : 1 ≤ D := by
    have : (1 : ℤ) ≤ 4 * n - t ^ 2 := by omega
    omega
  have hDcast : ((D : ℤ)) = 4 * n - t ^ 2 := by
    rw [hD_def]; exact Int.toNat_of_nonneg (by omega)
  obtain ⟨c, hc1, hsf⟩ := Nat.exists_squarefree_sq_add D hD1
  have hid : ((c : ℤ) - t) ^ 2 + t * ((c : ℤ) - t) * 2 + n * 2 ^ 2 = ((c ^ 2 + D : ℕ) : ℤ) := by
    push_cast [hDcast]; ring
  refine ⟨(c : ℤ) - t, 2, two_ne_zero, ?_, ?_⟩
  · rw [hid, Int.toNat_natCast]; exact hsf
  · rw [hid, Int.toNat_natCast]; nlinarith [sq_nonneg c]

end Int

end
