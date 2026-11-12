/-
  The Casimir trichotomy, and the growth of the solutions of the `GL₂(ℂ)` Whittaker system in each of
  its three regimes.

  For an `n`-step `SU(2)`-string of components `f p` (`p ≤ n`) satisfying the two Casimir relations of
  the torus system, the local behaviour near `y = 0` is governed by the Casimir eigenvalue `λ` against
  the string's weight set: `λ > 0` (the principal series, where the system's solutions are uniformly
  bounded), `λ` real and non-positive (the complementary and discrete cases, where the growth is
  controlled by the exponent the system forces), and the equality case `λ ≠ λ'` with `Re λ = Re λ'`
  (the degenerate regime, where the string's length `n` and parity decide). Each of the three is a
  bound `‖f p y‖ = O(y ^ δ)` on `(0, 1]`; the trichotomy itself is the statement that a non-empty
  weight set forces one of the three regimes.

  These are the local input of the `diagOne` Whittaker coefficient bounds: they turn the Casimir
  eigenvalue of a cusp constituent into the growth exponent of the string.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet.lean` (139 lines),
  `…_norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq.lean` (377),
  `…_exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded.lean` (508) and
  `…_exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos.lean` (499), with the statements
  from their wrappers `Theorems/Thm_LanglandsTunnell_*.lean`.

  spec-pin: Theorems/Thm_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet.lean
  spec-pin: Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq.lean
  spec-pin: Theorems/Thm_LanglandsTunnell_exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded.lean
  spec-pin: Theorems/Thm_LanglandsTunnell_exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos.lean
-/
import FLTForHuman.LanglandsTunnell.ODENearZeroBounds
import FLTForHuman.LanglandsTunnell.WhittakerODENearZero
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Group.Even
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

open scoped Real

noncomputable section

namespace LanglandsTunnell

namespace UnitClass17

private theorem main (lam : ℝ) (S : Set ℤ) (hS : S.Nonempty)
    (hminus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n - 2))
    (hplus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n + 2))
    (clminus : ∀ n ∈ S, 0 < 4 * lam + n * (n - 2) → n - 2 ∈ S)
    (clplus : ∀ n ∈ S, 0 < 4 * lam + n * (n + 2) → n + 2 ∈ S) :
    0 < lam ∨
      (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ∀ n ∈ S, (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨
      (lam = 0 ∧ (0 : ℤ) ∈ S) := by
  classical
  by_cases hpos : 0 < lam
  · exact Or.inl hpos
  push Not at hpos
  by_cases h0 : (0 : ℤ) ∈ S
  · refine Or.inr (Or.inr ⟨?_, h0⟩)
    have := hminus 0 h0
    push_cast at this
    linarith

  have h1 : (1 : ℤ) ∉ S := by
    intro h; have := hminus 1 h; push_cast at this; linarith
  have h1' : (-1 : ℤ) ∉ S := by
    intro h; have := hplus (-1) h; push_cast at this; linarith

  have hex : ∃ k : ℕ, ∃ n ∈ S, n.natAbs = k := by
    obtain ⟨n, hn⟩ := hS; exact ⟨n.natAbs, n, hn, rfl⟩
  set k₀ := Nat.find hex with hk₀
  obtain ⟨n₀, hn₀S, hn₀⟩ := Nat.find_spec hex
  have hmin : ∀ m ∈ S, k₀ ≤ m.natAbs := by
    intro m hm
    by_contra hlt
    push Not at hlt
    exact Nat.find_min hex hlt ⟨m, hm, rfl⟩
  rw [← hk₀] at hn₀
  have hk2 : 2 ≤ k₀ := by
    by_contra hlt
    push Not at hlt
    interval_cases k₀
    · have : n₀ = 0 := Int.natAbs_eq_zero.mp hn₀
      exact h0 (this ▸ hn₀S)
    · rcases Int.natAbs_eq_iff.mp hn₀ with h | h
      · exact h1 (by simpa [h] using hn₀S)
      · exact h1' (by simpa [h] using hn₀S)

  have hkey : 4 * lam + (k₀ : ℝ) * ((k₀ : ℝ) - 2) = 0 := by
    rcases Int.natAbs_eq_iff.mp hn₀ with h | h
    ·
      have hge := hminus n₀ hn₀S
      rw [h] at hge; push_cast at hge
      by_contra hne
      have hposE : 0 < 4 * lam + (n₀ : ℝ) * ((n₀ : ℝ) - 2) := by
        rw [h]; push_cast; exact lt_of_le_of_ne hge (Ne.symm hne)
      have hmem := clminus n₀ hn₀S (by exact_mod_cast hposE)
      have := hmin _ hmem
      rw [h] at this
      omega
    ·
      have hge := hplus n₀ hn₀S
      rw [h] at hge; push_cast at hge
      by_contra hne
      have hne' : 4 * lam + (-(k₀ : ℝ)) * (-(k₀ : ℝ) + 2) ≠ 0 := by
        intro h'; apply hne; linarith
      have hposE : 0 < 4 * lam + (n₀ : ℝ) * ((n₀ : ℝ) + 2) := by
        rw [h]; push_cast; exact lt_of_le_of_ne hge (Ne.symm hne')
      have hmem := clplus n₀ hn₀S (by exact_mod_cast hposE)
      have := hmin _ hmem
      rw [h] at this
      omega
  refine Or.inr (Or.inl ⟨k₀, hk2, by linarith [hkey], fun m hm => ⟨?_, ?_⟩⟩)
  · have := hmin m hm
    rw [← Int.natCast_natAbs]
    exact_mod_cast this
  ·
    have hE : ∀ m : ℤ, 4 * lam + (m : ℝ) * ((m : ℝ) - 2) = ((m * (m - 2) - (k₀ : ℤ) * ((k₀ : ℤ) - 2) : ℤ) : ℝ) := by
      intro m; push_cast; linarith [hkey]
    have hE' : ∀ m : ℤ, 4 * lam + (m : ℝ) * ((m : ℝ) + 2) = ((m * (m + 2) - (k₀ : ℤ) * ((k₀ : ℤ) - 2) : ℤ) : ℝ) := by
      intro m; push_cast; linarith [hkey]
    suffices H : ∀ d : ℕ, ∀ m ∈ S, m.natAbs = k₀ + d → (m - k₀) % 2 = 0 by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hmin m hm)
      exact H d m hm hd
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro m hm hd
      rcases Nat.lt_or_ge d 2 with hd2 | hd2
      · interval_cases d
        ·
          rcases Int.natAbs_eq_iff.mp hd with h | h <;> (rw [h]; push_cast; omega)
        ·
          exfalso
          rcases Int.natAbs_eq_iff.mp hd with h | h
          · have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) - 2) := by
              rw [hE]; exact_mod_cast (by rw [h]; push_cast; nlinarith : (0 : ℤ) < m * (m - 2) - k₀ * (k₀ - 2))
            have hmem := clminus m hm hp
            have := hmin _ hmem
            rw [h] at this; push_cast at this; omega
          · have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) + 2) := by
              rw [hE']; exact_mod_cast (by rw [h]; push_cast; nlinarith : (0 : ℤ) < m * (m + 2) - k₀ * (k₀ - 2))
            have hmem := clplus m hm hp
            have := hmin _ hmem
            rw [h] at this; push_cast at this; omega
      ·
        rcases Int.natAbs_eq_iff.mp hd with h | h
        · have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) - 2) := by
            rw [hE]; exact_mod_cast (by rw [h]; push_cast; nlinarith : (0 : ℤ) < m * (m - 2) - k₀ * (k₀ - 2))
          have hmem := clminus m hm hp
          have hd' : (m - 2).natAbs = k₀ + (d - 2) := by rw [h]; push_cast; omega
          have := IH (d - 2) (by omega) (m - 2) hmem hd'
          omega
        · have hp : 0 < 4 * lam + (m : ℝ) * ((m : ℝ) + 2) := by
            rw [hE']; exact_mod_cast (by rw [h]; push_cast; nlinarith : (0 : ℤ) < m * (m + 2) - k₀ * (k₀ - 2))
          have hmem := clplus m hm hp
          have hd' : (m + 2).natAbs = k₀ + (d - 2) := by rw [h]; push_cast; omega
          have := IH (d - 2) (by omega) (m + 2) hmem hd'
          omega

end UnitClass17

theorem casimir_pos_or_discrete_or_zero_of_weightSet
    (lam : ℝ) (S : Set ℤ) (hS : S.Nonempty)
    (hminus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n - 2))
    (hplus : ∀ n ∈ S, 0 ≤ 4 * lam + n * (n + 2))
    (clminus : ∀ n ∈ S, 0 < 4 * lam + n * (n - 2) → n - 2 ∈ S)
    (clplus : ∀ n ∈ S, 0 < 4 * lam + n * (n + 2) → n + 2 ∈ S) :
    0 < lam ∨
      (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ∀ n ∈ S, (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨
      (lam = 0 ∧ (0 : ℤ) ∈ S) := by
  exact UnitClass17.main lam S hS hminus hplus clminus clplus

open scoped Real

namespace AlphaAux

open Finset

noncomputable def qR (n i : ℕ) : ℝ := (n : ℝ) - 2 * (i : ℝ)

noncomputable def G (n : ℕ) (f : ℕ → ℝ → ℂ) (i : ℕ) : ℝ → ℂ :=
  if 2 * i = n ∨ n < i then (fun _ => 0) else f i

noncomputable def aC (n : ℕ) (lam lam' : ℂ) (i : ℕ) : ℂ :=
  if 2 * i = n then 1 else 1 - 2 * (lam - lam') / (qR n i : ℂ)

noncomputable def uC (n : ℕ) (κ : ℂ) (i : ℕ) : ℂ := -(4 * (Real.pi : ℂ) * Complex.I * κ) / (qR n i : ℂ)

noncomputable def vC (n : ℕ) (κ : ℂ) (i : ℕ) : ℂ :=
  -(4 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((i : ℂ) * ((n : ℂ) + 1 - (i : ℂ)))) / (qR n i : ℂ)

noncomputable def αC (κ lam lam' : ℂ) : ℂ := -(2 * (Real.pi : ℂ) * Complex.I * κ) / (lam - lam')

noncomputable def βC (n : ℕ) (κ lam lam' : ℂ) (i : ℕ) : ℂ :=
  -(2 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((i : ℂ) * ((n : ℂ) + 1 - (i : ℂ)))) / (lam - lam')

noncomputable def δ (j t : ℕ) : ℂ := if j = t then 1 else 0

noncomputable def χ (n t : ℕ) : ℂ := if 2 * t = n then 1 else 0

noncomputable def Bn (n : ℕ) (κ lam lam' : ℂ) (y : ℝ) (i j : ℕ) : ℂ :=
  if 2 * i = n then 0 else
    (y : ℂ) * (uC n κ i * δ j (i + 1) + vC n κ i * δ j (i - 1)) +
    (y : ℂ) ^ 2 *
      (χ n (i + 1) * uC n κ i * (αC κ lam lam' * δ j (i + 2) + βC n κ lam lam' (i + 1) * δ j i) +
        χ n (i - 1) * vC n κ i * (αC κ lam lam' * δ j (i - 1 + 1) + βC n κ lam lam' (i - 1) * δ j (i - 1 - 1)))

theorem norm_δ_le (j t : ℕ) : ‖δ j t‖ ≤ 1 := by
  
  unfold δ; split_ifs <;> simp

theorem norm_χ_le (n t : ℕ) : ‖χ n t‖ ≤ 1 := by
  
  unfold χ; split_ifs <;> simp

theorem G_of_lt (n : ℕ) (f : ℕ → ℝ → ℂ) (i : ℕ) (h : n < i) : G n f i = fun _ => 0 := by
  
  unfold G; rw [ite_eq_left (Or.inr h)]

theorem G_of_mid (n : ℕ) (f : ℕ → ℝ → ℂ) (i : ℕ) (h : 2 * i = n) : G n f i = fun _ => 0 := by
  
  unfold G; rw [ite_eq_left (Or.inl h)]

theorem G_of_ne (n : ℕ) (f : ℕ → ℝ → ℂ) (i : ℕ) (h : ¬ 2 * i = n) (hi : i ≤ n) : G n f i = f i := by
  
  unfold G; rw [ite_eq_right (by omega)]

theorem sum_delta (n : ℕ) (f : ℕ → ℝ → ℂ) (t : ℕ) (y : ℝ) :
    ∑ j ∈ range (n + 1), δ j t * G n f j y = G n f t y := by
  
  simp only [δ, boole_mul, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [G_of_lt n f t (by omega)]

theorem rowsum (n : ℕ) (κ lam lam' : ℂ) (f : ℕ → ℝ → ℂ) (y : ℝ) (i : ℕ) (h : ¬ 2 * i = n) :
    ∑ j ∈ range (n + 1), Bn n κ lam lam' y i j * G n f j y =
      (y : ℂ) * (uC n κ i * G n f (i + 1) y + vC n κ i * G n f (i - 1) y) +
      (y : ℂ) ^ 2 *
        (χ n (i + 1) * uC n κ i * (αC κ lam lam' * G n f (i + 2) y + βC n κ lam lam' (i + 1) * G n f i y) +
          χ n (i - 1) * vC n κ i *
            (αC κ lam lam' * G n f (i - 1 + 1) y + βC n κ lam lam' (i - 1) * G n f (i - 1 - 1) y)) := by
  
  simp only [Bn, ite_eq_right h, add_mul, mul_add, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, sum_delta]

theorem rowsum_mid (n : ℕ) (κ lam lam' : ℂ) (f : ℕ → ℝ → ℂ) (y : ℝ) (i : ℕ) (h : 2 * i = n) :
    ∑ j ∈ range (n + 1), Bn n κ lam lam' y i j * G n f j y = 0 := by
  
  simp [Bn, h]

theorem sysN (n : ℕ) (Gf : ℕ → ℝ → ℂ) (a : ℕ → ℂ) (B : ℝ → ℕ → ℕ → ℂ) (c : ℝ)
    (ha : ∀ i, i ≤ n → 1 ≤ (a i).re)
    (hB : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i j, i ≤ n → j ≤ n → ‖B y i j‖ ≤ c * y)
    (hG : ∀ i, i ≤ n → DifferentiableOn ℝ (Gf i) (Set.Ioi 0))
    (hrow : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, i ≤ n →
      (y : ℂ) * deriv (Gf i) y = a i * Gf i y + ∑ j ∈ range (n + 1), B y i j * Gf j y) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, i ≤ n → ‖Gf i y‖ ≤ C * y ^ (1 - ε) := by
  
  intro ε hε
  obtain ⟨C, hC⟩ := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_system_of_diag (n + 1)
    (fun i => a i) 1 c 1 one_pos (fun i => ha i (Nat.lt_succ_iff.mp i.isLt)) (fun y i j => B y i j)
    (fun y hy hy1 i j => by
      simpa using hB y hy hy1 i j (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt))
    (fun i => Gf i) (fun i => hG i (Nat.lt_succ_iff.mp i.isLt))
    (fun y hy hy1 i => by
      rw [Fin.sum_univ_eq_sum_range (fun j => B y i j * Gf j y) (n + 1)]
      exact hrow y hy hy1 i (Nat.lt_succ_iff.mp i.isLt)) ε hε
  exact ⟨C, fun y hy hy1 i hi => hC y hy hy1 ⟨i, Nat.lt_succ_iff.mpr hi⟩⟩

end AlphaAux

namespace AlphaAux

open Finset

def HSys (n : ℕ) (κ lam lam' : ℂ) (f : ℕ → ℝ → ℂ) : Prop :=
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0)

variable {n : ℕ} {κ lam lam' : ℂ} {f : ℕ → ℝ → ℂ}

theorem hstar (hsys : HSys n κ lam lam' f) (i : ℕ) (hi : i ≤ n) (y : ℝ) (hy : 0 < y) :
    2 * ((n : ℂ) - 2 * (i : ℂ)) * (y : ℂ) * deriv (f i) y +
        (4 * (lam - lam') - 2 * ((n : ℂ) - 2 * (i : ℂ))) * f i y +
      8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) *
        (κ * f (i + 1) y + (starRingEnd ℂ) κ * ((i : ℂ) * ((n : ℂ) + 1 - (i : ℂ))) * f (i - 1) y) = 0 := by
  
  obtain ⟨E1, E2⟩ := (hsys ⟨i, Nat.lt_succ_iff.mpr hi⟩).2.2 y hy
  dsimp only at E1 E2
  linear_combination E1 - E2

theorem qR_cast (n i : ℕ) : ((qR n i : ℝ) : ℂ) = (n : ℂ) - 2 * (i : ℂ) := by
  
  simp [qR]

theorem q_ne_zero (i : ℕ) (h : ¬ 2 * i = n) : (n : ℂ) - 2 * (i : ℂ) ≠ 0 := by
  
  have h' : ((n : ℤ) - 2 * (i : ℤ)) ≠ 0 := by omega
  have h'' : (((n : ℤ) - 2 * (i : ℤ) : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr h'
  push_cast at h''
  exact h''

theorem rel (hsys : HSys n κ lam lam' f) (i : ℕ) (hi : i ≤ n) (h : ¬ 2 * i = n) (y : ℝ) (hy : 0 < y) :
    (y : ℂ) * deriv (f i) y =
      aC n lam lam' i * f i y + (y : ℂ) * (uC n κ i * f (i + 1) y + vC n κ i * f (i - 1) y) := by
  
  have H := hstar hsys i hi y hy
  have hq0 := q_ne_zero (n := n) i h
  have hinv : ((n : ℂ) - 2 * (i : ℂ)) * ((n : ℂ) - 2 * (i : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hq0
  rw [aC, ite_eq_right h, uC, vC, qR_cast]
  linear_combination ((2 : ℂ)⁻¹ * ((n : ℂ) - 2 * (i : ℂ))⁻¹) * H + (f i y - (y : ℂ) * deriv (f i) y) * hinv

theorem alg (hne : lam ≠ lam' ∨ Odd n) (hsys : HSys n κ lam lam' f) (j : ℕ) (hj : j ≤ n) (h : 2 * j = n)
    (y : ℝ) (hy : 0 < y) :
    f j y = (y : ℂ) * (αC κ lam lam' * f (j + 1) y + βC n κ lam lam' j * f (j - 1) y) := by
  
  have H := hstar hsys j hj y hy
  have hd : lam ≠ lam' := hne.resolve_right (by rintro ⟨k, hk⟩; omega)
  have hd' : lam - lam' ≠ 0 := sub_ne_zero.mpr hd
  have hdinv : (lam - lam') * (lam - lam')⁻¹ = 1 := mul_inv_cancel₀ hd'
  have hq : (n : ℂ) - 2 * (j : ℂ) = 0 := by
    have : (n : ℂ) = ((2 * j : ℕ) : ℂ) := by rw [h]
    rw [this]; push_cast; ring
  rw [αC, βC]
  linear_combination (4 : ℂ)⁻¹ * (lam - lam')⁻¹ * H - f j y * hdinv -
    (2 : ℂ)⁻¹ * (lam - lam')⁻¹ * ((y : ℂ) * deriv (f j) y - f j y) * hq

theorem f_eq (hne : lam ≠ lam' ∨ Odd n) (hfn : ∀ y : ℝ, f (n + 1) y = 0) (hsys : HSys n κ lam lam' f)
    (j : ℕ) (hj : j ≤ n + 1) (y : ℝ) (hy : 0 < y) :
    f j y = G n f j y +
      χ n j * ((y : ℂ) * (αC κ lam lam' * G n f (j + 1) y + βC n κ lam lam' j * G n f (j - 1) y)) := by
  
  by_cases hm : 2 * j = n
  · have hjn : j ≤ n := by omega
    have A := alg hne hsys j hjn hm y hy
    have h1 : f (j + 1) y = G n f (j + 1) y := by
      by_cases hj1 : n < j + 1
      · rw [G_of_lt n f (j + 1) hj1]
        have e : j + 1 = n + 1 := by omega
        rw [e, hfn]
      · rw [G_of_ne n f (j + 1) (by omega) (by omega)]
    have h2 : βC n κ lam lam' j * f (j - 1) y = βC n κ lam lam' j * G n f (j - 1) y := by
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; simp [βC]
      · rw [G_of_ne n f (j - 1) (by omega) (by omega)]
    rw [G_of_mid n f j hm, χ, ite_eq_left hm, one_mul, A, h1, mul_add, h2]
    ring
  · rw [χ, ite_eq_right hm, zero_mul, add_zero]
    by_cases hjn : n < j
    · have e : j = n + 1 := by omega
      subst e
      rw [G_of_lt n f (n + 1) hjn, hfn]
    · rw [G_of_ne n f j hm (by omega)]

theorem row (hne : lam ≠ lam' ∨ Odd n) (hfn : ∀ y : ℝ, f (n + 1) y = 0) (hsys : HSys n κ lam lam' f)
    (y : ℝ) (hy : 0 < y) (i : ℕ) (hi : i ≤ n) :
    (y : ℂ) * deriv (G n f i) y =
      aC n lam lam' i * G n f i y + ∑ j ∈ range (n + 1), Bn n κ lam lam' y i j * G n f j y := by
  
  by_cases hm : 2 * i = n
  · rw [rowsum_mid n κ lam lam' f y i hm, G_of_mid n f i hm]
    simp
  · rw [rowsum n κ lam lam' f y i hm]
    have hGi : G n f i = f i := G_of_ne n f i hm hi
    have R := rel hsys i hi hm y hy
    have E1 := f_eq hne hfn hsys (i + 1) (by omega) y hy
    have E2 := f_eq hne hfn hsys (i - 1) (by omega) y hy
    have e1 : i + 1 + 1 = i + 2 := by omega
    rw [Nat.add_sub_cancel, e1] at E1
    rw [hGi, R, E1, E2, hGi]
    ring

theorem G_differentiableOn (hsys : HSys n κ lam lam' f) (i : ℕ) :
    DifferentiableOn ℝ (G n f i) (Set.Ioi 0) := by
  
  unfold G
  split_ifs with h
  · exact differentiableOn_const 0
  · exact (hsys ⟨i, by omega⟩).1

theorem aC_re (hre : lam.re = lam'.re) (i : ℕ) : 1 ≤ (aC n lam lam' i).re := by
  
  unfold aC
  split_ifs with h
  · simp
  · have h2 : (2 * (lam - lam')).re = 0 := by simp [Complex.mul_re, hre]
    rw [Complex.sub_re, Complex.one_re, Complex.div_ofReal_re, h2, zero_div, sub_zero]

theorem norm_mul_le_of_norm_le_one_right (a d : ℂ) (h : ‖d‖ ≤ 1) : ‖a * d‖ ≤ ‖a‖ := by
  
  rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) h

theorem norm_mul_le_of_norm_le_one_left (x a : ℂ) (h : ‖x‖ ≤ 1) : ‖x * a‖ ≤ ‖a‖ := by
  
  rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) h

theorem norm_block_le (x u α β d1 d2 : ℂ) (hx : ‖x‖ ≤ 1) (h1 : ‖d1‖ ≤ 1) (h2 : ‖d2‖ ≤ 1) :
    ‖x * u * (α * d1 + β * d2)‖ ≤ ‖u‖ * (‖α‖ + ‖β‖) := by
  
  have e3 : ‖α * d1 + β * d2‖ ≤ ‖α‖ + ‖β‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_mul_le_of_norm_le_one_right α d1 h1)
      (norm_mul_le_of_norm_le_one_right β d2 h2))
  have e4 : ‖x * u‖ ≤ ‖u‖ := norm_mul_le_of_norm_le_one_left x u hx
  rw [norm_mul]
  exact mul_le_mul e4 e3 (norm_nonneg _) (norm_nonneg _)

noncomputable def K (n : ℕ) (κ lam lam' : ℂ) (i : ℕ) : ℝ :=
  ‖uC n κ i‖ + ‖vC n κ i‖ +
    (‖uC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i + 1)‖) +
      ‖vC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i - 1)‖))

theorem K_nonneg (i : ℕ) : 0 ≤ K n κ lam lam' i := by
  
  unfold K; positivity

noncomputable def Kc (n : ℕ) (κ lam lam' : ℂ) : ℝ := ∑ i ∈ range (n + 1), K n κ lam lam' i

theorem Kc_nonneg : 0 ≤ Kc n κ lam lam' := Finset.sum_nonneg fun i _ => K_nonneg i

theorem norm_Bn_le (y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) (i j : ℕ) (hi : i ≤ n) :
    ‖Bn n κ lam lam' y i j‖ ≤ Kc n κ lam lam' * y := by
  
  have hK : K n κ lam lam' i ≤ Kc n κ lam lam' :=
    Finset.single_le_sum (f := K n κ lam lam') (fun k _ => K_nonneg k) (mem_range.mpr (by omega))
  have hny : ‖(y : ℂ)‖ = y := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  unfold Bn
  split_ifs with hm
  · rw [norm_zero]; exact mul_nonneg Kc_nonneg hy.le
  · have hA : ‖uC n κ i * δ j (i + 1) + vC n κ i * δ j (i - 1)‖ ≤ ‖uC n κ i‖ + ‖vC n κ i‖ :=
      (norm_add_le _ _).trans (add_le_add
        (norm_mul_le_of_norm_le_one_right _ _ (norm_δ_le _ _))
        (norm_mul_le_of_norm_le_one_right _ _ (norm_δ_le _ _)))
    have hB :
        ‖χ n (i + 1) * uC n κ i * (αC κ lam lam' * δ j (i + 2) + βC n κ lam lam' (i + 1) * δ j i) +
            χ n (i - 1) * vC n κ i *
              (αC κ lam lam' * δ j (i - 1 + 1) + βC n κ lam lam' (i - 1) * δ j (i - 1 - 1))‖ ≤
          ‖uC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i + 1)‖) +
            ‖vC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i - 1)‖) :=
      (norm_add_le _ _).trans (add_le_add
        (norm_block_le _ _ _ _ _ _ (norm_χ_le _ _) (norm_δ_le _ _) (norm_δ_le _ _))
        (norm_block_le _ _ _ _ _ _ (norm_χ_le _ _) (norm_δ_le _ _) (norm_δ_le _ _)))
    have hy2 : y ^ 2 ≤ y := pow_le_of_le_one hy.le hy1 two_ne_zero
    calc _ ≤ ‖(y : ℂ) * (uC n κ i * δ j (i + 1) + vC n κ i * δ j (i - 1))‖ +
            ‖(y : ℂ) ^ 2 *
              (χ n (i + 1) * uC n κ i * (αC κ lam lam' * δ j (i + 2) + βC n κ lam lam' (i + 1) * δ j i) +
                χ n (i - 1) * vC n κ i *
                  (αC κ lam lam' * δ j (i - 1 + 1) + βC n κ lam lam' (i - 1) * δ j (i - 1 - 1)))‖ :=
          norm_add_le _ _
      _ ≤ y * (‖uC n κ i‖ + ‖vC n κ i‖) +
            y ^ 2 * (‖uC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i + 1)‖) +
              ‖vC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i - 1)‖)) := by
          rw [norm_mul, norm_mul, norm_pow, hny]
          exact add_le_add (mul_le_mul_of_nonneg_left hA hy.le) (mul_le_mul_of_nonneg_left hB (sq_nonneg y))
      _ ≤ y * (‖uC n κ i‖ + ‖vC n κ i‖) +
            y * (‖uC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i + 1)‖) +
              ‖vC n κ i‖ * (‖αC κ lam lam'‖ + ‖βC n κ lam lam' (i - 1)‖)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right hy2 (by positivity))
      _ = K n κ lam lam' i * y := by rw [K]; ring
      _ ≤ Kc n κ lam lam' * y := mul_le_mul_of_nonneg_right hK hy.le

end AlphaAux

namespace AlphaAux

open Finset

variable {n : ℕ} {κ lam lam' : ℂ} {f : ℕ → ℝ → ℂ}

theorem main (hne : lam ≠ lam' ∨ Odd n) (hre : lam.re = lam'.re) (hfn : ∀ y : ℝ, f (n + 1) y = 0)
    (hsys : HSys n κ lam lam' f) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ (1 - ε) := by
  
  intro ε hε
  obtain ⟨C, hC⟩ := sysN n (G n f) (aC n lam lam') (Bn n κ lam lam') (Kc n κ lam lam')
    (fun i _ => aC_re hre i) (fun y hy hy1 i j hi _ => norm_Bn_le y hy hy1 i j hi)
    (fun i _ => G_differentiableOn hsys i) (fun y hy _ i hi => row hne hfn hsys y hy i hi) ε hε
  have hC0 : 0 ≤ C := by
    have h := hC 1 one_pos le_rfl 0 (Nat.zero_le _)
    rw [Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hCall : ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ i, ‖G n f i y‖ ≤ C * y ^ (1 - ε) := by
    intro y hy hy1 i
    by_cases hi : i ≤ n
    · exact hC y hy hy1 i hi
    · rw [G_of_lt n f i (by omega), norm_zero]
      exact mul_nonneg hC0 (Real.rpow_nonneg hy.le _)
  set S := ∑ i ∈ range (n + 1), ‖βC n κ lam lam' i‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C * (1 + ‖αC κ lam lam'‖ + S), ?_⟩
  intro p y hy hy1
  have hp : (p : ℕ) ≤ n := Nat.lt_succ_iff.mp p.isLt
  have E := f_eq hne hfn hsys p (by omega) y hy
  have hβ : ‖βC n κ lam lam' p‖ ≤ S :=
    Finset.single_le_sum (f := fun i => ‖βC n κ lam lam' i‖) (fun _ _ => norm_nonneg _) (mem_range.mpr p.isLt)
  set s := y ^ (1 - ε) with hs
  have hs0 : 0 ≤ s := Real.rpow_nonneg hy.le _
  have hny : ‖(y : ℂ)‖ = y := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have h1 := hCall y hy hy1 p
  have h2 := hCall y hy hy1 (p + 1)
  have h3 := hCall y hy hy1 (p - 1)
  have hin : ‖αC κ lam lam' * G n f (p + 1) y + βC n κ lam lam' p * G n f (p - 1) y‖ ≤
      (‖αC κ lam lam'‖ + S) * (C * s) := by
    calc _ ≤ ‖αC κ lam lam' * G n f (p + 1) y‖ + ‖βC n κ lam lam' p * G n f (p - 1) y‖ := norm_add_le _ _
      _ = ‖αC κ lam lam'‖ * ‖G n f (p + 1) y‖ + ‖βC n κ lam lam' p‖ * ‖G n f (p - 1) y‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ ‖αC κ lam lam'‖ * (C * s) + S * (C * s) :=
          add_le_add (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)) (mul_le_mul hβ h3 (norm_nonneg _) hS0)
      _ = (‖αC κ lam lam'‖ + S) * (C * s) := by ring
  have hcorr : ‖χ n p * ((y : ℂ) * (αC κ lam lam' * G n f (p + 1) y + βC n κ lam lam' p * G n f (p - 1) y))‖ ≤
      (‖αC κ lam lam'‖ + S) * (C * s) := by
    rw [norm_mul, norm_mul, hny]
    calc _ ≤ 1 * (1 * ((‖αC κ lam lam'‖ + S) * (C * s))) :=
          mul_le_mul (norm_χ_le _ _) (mul_le_mul hy1 hin (norm_nonneg _) zero_le_one)
            (mul_nonneg hy.le (norm_nonneg _)) zero_le_one
      _ = _ := by ring
  rw [E]
  calc _ ≤ ‖G n f p y‖ +
        ‖χ n p * ((y : ℂ) * (αC κ lam lam' * G n f (p + 1) y + βC n κ lam lam' p * G n f (p - 1) y))‖ :=
        norm_add_le _ _
    _ ≤ C * s + (‖αC κ lam lam'‖ + S) * (C * s) := add_le_add h1 hcorr
    _ = C * (1 + ‖αC κ lam lam'‖ + S) * s := by ring

end AlphaAux

theorem norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (hne : lam ≠ lam' ∨ Odd n) (hre : lam.re = lam'.re) (f : ℕ → ℝ → ℂ)
    (hfn : ∀ y : ℝ, f (n + 1) y = 0)
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ (1 - ε) := by
  -- `hκ` is not needed by the bound, which is uniform in `κ`; the pin's statement carries it.
  have hκ₀ : κ ≠ 0 := hκ
  intro ε hε
  exact LanglandsTunnell.AlphaAux.main hne hre hfn hsys ε hε

open scoped Real

noncomputable section

namespace GammaP41

open Real Set

theorem bdd_Icc (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (a b : ℝ) (ha : 0 < a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Set.Icc a b, ‖f y‖ ≤ M := by
  
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le ha hy.1
  have hcont : ContinuousOn f (Set.Icc a b) := (hf.continuousOn).mono hsub
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hcont).isBounded.exists_norm_le
  exact ⟨max M 0, le_max_right _ _, fun y hy => (hM _ ⟨y, hy, rfl⟩).trans (le_max_left _ _)⟩

theorem extend_bound (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (L e C : ℝ) (he : 0 ≤ e)
    (hC : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ e) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ y : ℝ, 0 < y → y ≤ L → ‖f y‖ ≤ C' * y ^ e := by
  
  obtain ⟨M, hM0, hM⟩ := bdd_Icc f hf 1 L one_pos
  refine ⟨max C 0 + M, by positivity, fun y hy hyL => ?_⟩
  have hye : 0 ≤ y ^ e := (Real.rpow_pos_of_pos hy e).le
  rcases le_or_gt y 1 with h1 | h1
  · calc ‖f y‖ ≤ C * y ^ e := hC y hy h1
      _ ≤ max C 0 * y ^ e := by gcongr; exact le_max_left _ _
      _ ≤ (max C 0 + M) * y ^ e := by nlinarith
  · have h1e : 1 ≤ y ^ e := Real.one_le_rpow h1.le he
    calc ‖f y‖ ≤ M := hM y ⟨h1.le, hyL⟩
      _ ≤ M * y ^ e := le_mul_of_one_le_right hM0 h1e
      _ ≤ (max C 0 + M) * y ^ e := by nlinarith [le_max_right C 0]

theorem rpow_bound_mono {f : ℝ → ℂ} {C e e' : ℝ} (hee : e' ≤ e)
    (hC : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ e) :
    ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ max C 0 * y ^ e' := by
  
  intro y hy hy1
  calc ‖f y‖ ≤ C * y ^ e := hC y hy hy1
    _ ≤ max C 0 * y ^ e := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * y ^ e' := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hy hy1 hee) (le_max_right _ _)

theorem stepA (q : ℂ) (hq : q ≠ 0) (κ c : ℂ) (f fup fdn : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (Bup Bdn : ℝ) (hup : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖fup y‖ ≤ Bup) (hdn : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖fdn y‖ ≤ Bdn)
    (hrel : ∀ y : ℝ, 0 < y → 2 * q * ((y : ℂ) * deriv f y - f y) +
      8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * (κ * fup y + c * fdn y) = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f y‖ ≤ C * y ^ (1 - ε) := by
  
  set u : ℝ → ℂ := fun y => -(8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * (κ * fup y + c * fdn y)) / (2 * q) with hu
  have hfeq : ∀ y : ℝ, 0 < y → (y : ℂ) * deriv f y = 1 * f y + u y := by
    intro y hy
    have h := hrel y hy
    simp only [hu]
    field_simp
    linear_combination h
  set A : ℝ := 4 * Real.pi * (‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0) / ‖q‖ with hA
  have hub : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖u y‖ ≤ A * y ^ (1 : ℝ) := by
    intro y hy hy1
    rw [Real.rpow_one]
    have hq' : 0 < ‖q‖ := norm_pos_iff.mpr hq
    simp only [hu, norm_div, norm_neg, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, abs_of_pos hy]
    rw [div_le_iff₀ (by positivity), hA]
    have h1 : ‖κ * fup y + c * fdn y‖ ≤ ‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0 := by
      calc ‖κ * fup y + c * fdn y‖ ≤ ‖κ * fup y‖ + ‖c * fdn y‖ := norm_add_le _ _
        _ = ‖κ‖ * ‖fup y‖ + ‖c‖ * ‖fdn y‖ := by rw [norm_mul, norm_mul]
        _ ≤ ‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0 := by
            gcongr
            · exact (hup y hy hy1).trans (le_max_left _ _)
            · exact (hdn y hy hy1).trans (le_max_left _ _)
    calc 8 * Real.pi * y * ‖κ * fup y + c * fdn y‖ ≤ 8 * Real.pi * y * (‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0) := by gcongr
      _ = 4 * Real.pi * (‖κ‖ * max Bup 0 + ‖c‖ * max Bdn 0) / ‖q‖ * y * (2 * ‖q‖) := by field_simp; ring
  obtain ⟨C, hC⟩ := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing 1 1 A f u hf hub hfeq ε hε
  refine ⟨C, fun y hy hy1 => ?_⟩
  have := hC y hy hy1
  simpa using this

theorem rpow_m32_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (-(3 / 2 : ℝ) * (y ^ (-(3 / 2 : ℝ)) * y⁻¹)) y := by
  
  have h := Real.hasDerivAt_rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hy.ne')
  rw [Real.rpow_sub_one hy.ne', div_eq_mul_inv] at h
  exact h

theorem rescale (κ lam : ℂ) (hκ : κ ≠ 0) (νC : ℂ) (hν : νC ^ 2 = 1 - 4 * lam) (F R : ℝ → ℂ)
    (hF : DifferentiableOn ℝ F (Set.Ioi 0)) (hF' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0))
    (heq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - 3 * (y : ℂ) * deriv F y +
      (3 + 4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y = R y) :
    let c : ℝ := 2 * ‖κ‖
    let G : ℝ → ℂ := fun Y => ((((Y / c) ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F (Y / c)
    0 < c ∧ DifferentiableOn ℝ G (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv G) (Set.Ioi 0) ∧
    (∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv G) Y + (1 / 4 - νC ^ 2 - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * G Y =
        ((((Y / c) ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * R (Y / c)) ∧
    (∀ y : ℝ, 0 < y → G (c * y) = (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F y) ∧
    (∀ y : ℝ, 0 < y → ((c * y : ℝ) : ℂ) * deriv G (c * y) + (1 / 2 : ℂ) * G (c * y) =
        (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * ((y : ℂ) * deriv F y - F y)) ∧
    (∀ y : ℝ, 0 < y → ((c * y : ℝ) : ℂ) * deriv G (c * y) + (3 / 2 : ℂ) * G (c * y) =
        (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * ((y : ℂ) * deriv F y)) := by
  
  intro c G
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hc : 0 < c := by positivity
  set g : ℝ → ℂ := fun y => (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F y with hgdef
  set g1 : ℝ → ℂ := fun y => (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * (-(3 / 2 : ℂ) * (y : ℂ)⁻¹ * F y + deriv F y) with hg1def
  set g2 : ℝ → ℂ := fun y => (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) *
    ((15 / 4 : ℂ) * (y : ℂ)⁻¹ * (y : ℂ)⁻¹ * F y - 3 * (y : ℂ)⁻¹ * deriv F y + deriv (deriv F) y) with hg2def
  have hFd : ∀ y : ℝ, 0 < y → HasDerivAt F (deriv F y) y :=
    fun y hy => (hF.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hFdd : ∀ y : ℝ, 0 < y → HasDerivAt (deriv F) (deriv (deriv F) y) y :=
    fun y hy => (hF'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hpwC : ∀ y : ℝ, 0 < y → HasDerivAt (fun x : ℝ => (((x ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ))
      (((-(3 / 2 : ℝ) * (y ^ (-(3 / 2 : ℝ)) * y⁻¹)) : ℝ) : ℂ) y :=
    fun y hy => (rpow_m32_hasDerivAt hy).ofReal_comp
  have hg1 : ∀ y : ℝ, 0 < y → HasDerivAt g (g1 y) y := by
    intro y hy
    have h := (hpwC y hy).mul (hFd y hy)
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    convert h using 1; try rfl
    simp only [hg1def]; push_cast; ring
  have hderiv_g : ∀ y : ℝ, 0 < y → deriv g y = g1 y := fun y hy => (hg1 y hy).deriv
  have hg2 : ∀ y : ℝ, 0 < y → HasDerivAt g1 (g2 y) y := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have hinv : HasDerivAt (fun x : ℝ => (x : ℂ)⁻¹) (-((y : ℂ) ^ 2)⁻¹) y := by
      have h1 := (hasDerivAt_inv hy.ne').ofReal_comp
      have hfun : (fun x : ℝ => (x : ℂ)⁻¹) = fun x : ℝ => (((x⁻¹ : ℝ)) : ℂ) := by funext x; push_cast; rfl
      rw [hfun]
      convert h1 using 1
      push_cast; ring
    have hin : HasDerivAt (fun x : ℝ => -(3 / 2 : ℂ) * (x : ℂ)⁻¹ * F x + deriv F x)
        (-(3 / 2 : ℂ) * (-((y : ℂ) ^ 2)⁻¹) * F y + -(3 / 2 : ℂ) * (y : ℂ)⁻¹ * deriv F y + deriv (deriv F) y) y := by
      have := ((hinv.const_mul (-(3 / 2 : ℂ))).mul (hFd y hy)).add (hFdd y hy)
      convert this using 1
    have h := (hpwC y hy).mul hin
    convert h using 1; try rfl
    simp only [hg2def]; push_cast; field_simp; ring
  have hg1d : ∀ y : ℝ, 0 < y → HasDerivAt (deriv g) (g2 y) y := by
    intro y hy
    refine (hg2 y hy).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    exact hderiv_g s hs
  have hGg : G = fun Y => g (Y / c) := rfl
  have hdiv : ∀ Y : ℝ, HasDerivAt (fun X : ℝ => X / c) (1 / c) Y := fun Y => by
    simpa using (hasDerivAt_id Y).div_const c
  have hG1 : ∀ Y : ℝ, 0 < Y → HasDerivAt G ((1 / c) • g1 (Y / c)) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    rw [hGg]; exact (hg1 _ hy).scomp Y (hdiv Y)
  have hderiv_G : ∀ Y : ℝ, 0 < Y → deriv G Y = (1 / c) • g1 (Y / c) := fun Y hY => (hG1 Y hY).deriv
  have hG2 : ∀ Y : ℝ, 0 < Y → HasDerivAt (deriv G) ((1 / c) • ((1 / c) • g2 (Y / c))) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    have h := ((hg2 _ hy).scomp Y (hdiv Y)).const_smul (1 / c)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hY] with s hs
    rw [hderiv_G s hs]; rfl
  have hGd : DifferentiableOn ℝ G (Set.Ioi 0) := fun Y hY => (hG1 Y hY).differentiableAt.differentiableWithinAt
  have hGd' : DifferentiableOn ℝ (deriv G) (Set.Ioi 0) := fun Y hY => (hG2 Y hY).differentiableAt.differentiableWithinAt
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcn : (c : ℂ) ^ 2 = 4 * ((‖κ‖ : ℝ) : ℂ) ^ 2 := by show ((2 * ‖κ‖ : ℝ) : ℂ) ^ 2 = _; push_cast; ring
  have hsum : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * g2 y + (-(3 / 4 : ℂ) + 4 * lam - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y =
      (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * R y := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have e := heq y hy
    have h2 : (y : ℂ) ^ 2 * g2 y = (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) *
        ((15 / 4 : ℂ) * F y - 3 * (y : ℂ) * deriv F y + (y : ℂ) ^ 2 * deriv (deriv F) y) := by
      simp only [hg2def]; field_simp
    rw [h2]
    simp only [hgdef]
    linear_combination (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * e +
      (-(4 : ℂ) * (π : ℂ) ^ 2 * (y : ℂ) ^ 2 * (((y ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F y) * hcn
  refine ⟨hc, hGd, hGd', fun Y hY => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have hy : 0 < Y / c := div_pos hY hc
    rw [(hG2 Y hY).deriv]
    have hYy : (Y : ℂ) = (c : ℂ) * ((Y / c : ℝ) : ℂ) := by push_cast; field_simp
    have h3 : (Y : ℂ) ^ 2 * ((1 / c) • ((1 / c) • g2 (Y / c))) = (((Y / c : ℝ)) : ℂ) ^ 2 * g2 (Y / c) := by
      rw [hYy]; simp only [Complex.real_smul]; push_cast; field_simp
    have hGY : G Y = g (Y / c) := rfl
    rw [h3, hGY, hYy, hν]
    linear_combination hsum (Y / c) hy
  · show g (c * y / c) = _
    rw [mul_div_cancel_left₀ _ hc.ne']
  · rw [hderiv_G _ (by positivity)]
    show ((c * y : ℝ) : ℂ) * ((1 / c) • g1 (c * y / c)) + (1 / 2 : ℂ) * g (c * y / c) = _
    rw [mul_div_cancel_left₀ _ hc.ne']
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    simp only [hgdef, hg1def, Complex.real_smul]
    push_cast
    field_simp
    ring
  · rw [hderiv_G _ (by positivity)]
    show ((c * y : ℝ) : ℂ) * ((1 / c) • g1 (c * y / c)) + (3 / 2 : ℂ) * g (c * y / c) = _
    rw [mul_div_cancel_left₀ _ hc.ne']
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    simp only [hgdef, hg1def, Complex.real_smul]
    push_cast
    field_simp
    ring

theorem stepB (κ lam : ℂ) (hκ : κ ≠ 0) (ν : ℝ) (hν1 : 1 ≤ ν) (hνC : ((ν : ℝ) : ℂ) ^ 2 = 1 - 4 * lam)
    (F F₂ : ℝ → ℂ) (c₁ : ℂ)
    (hFd : DifferentiableOn ℝ F (Set.Ioi 0)) (hFd' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0))
    (hF₂d : DifferentiableOn ℝ F₂ (Set.Ioi 0))
    (heqF : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - 3 * (y : ℂ) * deriv F y +
      (3 + 4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y =
        8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * c₁ * (y : ℂ) * F₂ y)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F y‖ ≤ C * y ^ (1 - ε))
    (CF₂ : ℝ) (hCF₂ : ∀ y : ℝ, 0 < y → y ≤ 1 → ‖F₂ y‖ ≤ CF₂ * y ^ (1 - 1 / 8 : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y → 2 * ‖κ‖ * y ≤ 1 →
      ‖(y : ℂ) * deriv F y - F y‖ ≤ K * y ^ (7 / 4 : ℝ) := by
  
  have hν0 : 0 ≤ ν := by linarith
  have hνre : ((ν : ℝ) : ℂ).re = ν := Complex.ofReal_re _
  set R : ℝ → ℂ := fun y => 8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * c₁ * (y : ℂ) * F₂ y with hRdef
  obtain ⟨hc, hGd, hGd', hGeq, hGval, hGkill, hGder⟩ := rescale κ lam hκ ((ν : ℝ) : ℂ) hνC F R hFd hFd' heqF
  set c : ℝ := 2 * ‖κ‖ with hcdef
  set G : ℝ → ℂ := fun Y => ((((Y / c) ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * F (Y / c) with hGdef
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  obtain ⟨CF, hCF⟩ := hA (1 / 8) (by norm_num)
  obtain ⟨CF', hCF'0, hCF'⟩ := extend_bound F hFd (1 / c) (1 - 1 / 8) CF (by norm_num) hCF
  obtain ⟨CF₂', hCF₂'0, hCF₂'⟩ := extend_bound F₂ hF₂d (1 / c) (1 - 1 / 8) CF₂ (by norm_num) hCF₂
  have hYy : ∀ Y : ℝ, 0 < Y → Y ≤ 1 → 0 < Y / c ∧ Y / c ≤ 1 / c := fun Y hY hY1 =>
    ⟨div_pos hY hc, div_le_div_of_nonneg_right hY1 hc.le⟩
  have hpowsplit : ∀ (Y e : ℝ), 0 < Y → (Y / c) ^ e = c ^ (-e) * Y ^ e := by
    intro Y e hY
    rw [Real.div_rpow hY.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv, mul_comm]

  have hGapOf : ∀ (ε Cε : ℝ), (∀ y : ℝ, 0 < y → y ≤ 1 / c → ‖F y‖ ≤ Cε * y ^ (1 - ε)) →
      ∀ Y : ℝ, 0 < Y → Y ≤ 1 → ‖G Y‖ ≤ (Cε * c ^ (-(-(1 / 2) - ε))) * Y ^ (-(1 / 2) - ε) := by
    intro ε Cε hCε Y hY hY1
    obtain ⟨hy, hyc⟩ := hYy Y hY hY1
    simp only [hGdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _)]
    calc (Y / c) ^ (-(3 / 2 : ℝ)) * ‖F (Y / c)‖ ≤ (Y / c) ^ (-(3 / 2 : ℝ)) * (Cε * (Y / c) ^ (1 - ε)) := by
          gcongr; exact hCε _ hy hyc
      _ = Cε * ((Y / c) ^ (-(3 / 2 : ℝ)) * (Y / c) ^ (1 - ε)) := by ring
      _ = Cε * (Y / c) ^ (-(1 / 2) - ε) := by rw [← Real.rpow_add hy]; ring_nf
      _ = (Cε * c ^ (-(-(1 / 2) - ε))) * Y ^ (-(1 / 2) - ε) := by rw [hpowsplit Y _ hY]; ring

  set AG : ℝ := 8 * Real.pi * ‖κ‖ * ‖c₁‖ * CF₂' * c ^ (-(3 / 8) : ℝ) with hAG
  have hHb : ∀ Y : ℝ, 0 < Y → Y ≤ 1 → ‖((((Y / c) ^ (-(3 / 2 : ℝ)) : ℝ)) : ℂ) * R (Y / c)‖ ≤ AG * Y ^ (3 / 8 : ℝ) := by
    intro Y hY hY1
    obtain ⟨hy, hyc⟩ := hYy Y hY hY1
    simp only [hRdef]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _)]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_conj, abs_of_pos hy]
    calc (Y / c) ^ (-(3 / 2 : ℝ)) * (8 * Real.pi * ‖κ‖ * ‖c₁‖ * (Y / c) * ‖F₂ (Y / c)‖)
        ≤ (Y / c) ^ (-(3 / 2 : ℝ)) * (8 * Real.pi * ‖κ‖ * ‖c₁‖ * (Y / c) * (CF₂' * (Y / c) ^ (1 - 1 / 8 : ℝ))) := by
          gcongr; exact hCF₂' _ hy hyc
      _ = 8 * Real.pi * ‖κ‖ * ‖c₁‖ * CF₂' * ((Y / c) ^ (-(3 / 2 : ℝ)) * (Y / c) ^ (1 : ℝ) * (Y / c) ^ (1 - 1 / 8 : ℝ)) := by
          rw [Real.rpow_one]; ring
      _ = 8 * Real.pi * ‖κ‖ * ‖c₁‖ * CF₂' * (Y / c) ^ (3 / 8 : ℝ) := by
          rw [← Real.rpow_add hy, ← Real.rpow_add hy]; norm_num
      _ = AG * Y ^ (3 / 8 : ℝ) := by rw [hpowsplit Y _ hY, hAG]; ring

  have hback : ∀ (C : ℝ) (y : ℝ), 0 < y →
      ‖((c * y : ℝ) : ℂ) * deriv G (c * y) + (1 / 2 : ℂ) * G (c * y)‖ ≤ C * (c * y) ^ (1 / 4 : ℝ) →
      ‖(y : ℂ) * deriv F y - F y‖ ≤ max C 0 * c ^ (1 / 4 : ℝ) * y ^ (7 / 4 : ℝ) := by
    intro C y hy h
    rw [hGkill y hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy _),
      Real.mul_rpow hc.le hy.le] at h
    have hpos := Real.rpow_pos_of_pos hy (3 / 2 : ℝ)
    have h2 := mul_le_mul_of_nonneg_left h hpos.le
    rw [← mul_assoc, ← Real.rpow_add hy, show (3 / 2 : ℝ) + -(3 / 2) = 0 by norm_num, Real.rpow_zero, one_mul] at h2
    calc ‖(y : ℂ) * deriv F y - F y‖ ≤ y ^ (3 / 2 : ℝ) * (C * (c ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ))) := h2
      _ ≤ y ^ (3 / 2 : ℝ) * (max C 0 * (c ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ))) := by
          gcongr; exact le_max_left _ _
      _ = max C 0 * c ^ (1 / 4 : ℝ) * (y ^ (3 / 2 : ℝ) * y ^ (1 / 4 : ℝ)) := by ring
      _ = max C 0 * c ^ (1 / 4 : ℝ) * y ^ (7 / 4 : ℝ) := by rw [← Real.rpow_add hy]; norm_num

  have hkill : ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 0 < y → c * y ≤ 1 →
      ‖(y : ℂ) * deriv F y - F y‖ ≤ K * y ^ (7 / 4 : ℝ) := by
    rcases eq_or_lt_of_le hν1 with h1 | h1
    ·
      have hGap := hGapOf (1 / 8) CF' hCF'
      have hGAP := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori ((ν : ℝ) : ℂ)
        (by rw [hνre]; exact hν0) (3 / 8) AG (-(1 / 2) - 1 / 8) _ G _ hGd hGd' hHb hGap hGeq
      obtain ⟨C, hC⟩ := hGAP.1 (1 / 8) (by norm_num)
      have hexp : min (min (1 / 2 + ((ν : ℝ) : ℂ).re) (3 / 8)) (-(1 / 2) - 1 / 8 + 2) - 1 / 8 = (1 / 4 : ℝ) := by
        rw [hνre, ← h1]; norm_num
      refine ⟨max C 0 * c ^ (1 / 4 : ℝ), by positivity, fun y hy hcy => hback C y hy ?_⟩
      have hY : 0 < c * y := by positivity
      have h := hC (c * y) hY hcy
      rw [hexp, show (1 / 2 : ℂ) - ((ν : ℝ) : ℂ) = -(1 / 2 : ℂ) by rw [← h1]; push_cast; norm_num] at h
      convert h using 2; ring
    ·
      set ε₀ : ℝ := min (1 / 8) ((ν - 1) / 2) with hε₀
      have hε₀pos : 0 < ε₀ := lt_min (by norm_num) (by linarith)
      have hε₀le : ε₀ ≤ 1 / 8 := min_le_left _ _
      have hε₀lt : ε₀ < ν - 1 := (min_le_right _ _).trans_lt (by linarith)
      obtain ⟨C0, hC0⟩ := hA ε₀ hε₀pos
      obtain ⟨C0', -, hC0'⟩ := extend_bound F hFd (1 / c) (1 - ε₀) C0 (by linarith) hC0
      have hGap := hGapOf ε₀ C0' hC0'
      have hGAP := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_bessel_ode_of_forcing_of_apriori ((ν : ℝ) : ℂ)
        (by rw [hνre]; exact hν0) (3 / 8) AG (-(1 / 2) - ε₀) _ G _ hGd hGd' hHb hGap hGeq
      have hr : 1 / 2 - ((ν : ℝ) : ℂ).re < -(1 / 2) - ε₀ := by rw [hνre]; linarith
      obtain ⟨C, hC⟩ := hGAP.2 hr (1 / 8) (by norm_num)
      have hexp : min (1 / 2 + ((ν : ℝ) : ℂ).re) (3 / 8) - 1 / 8 = (1 / 4 : ℝ) := by
        rw [hνre, min_eq_right (by linarith)]; norm_num
      refine ⟨max (C + C) 0 * c ^ (1 / 4 : ℝ), by positivity, fun y hy hcy => hback (C + C) y hy ?_⟩
      have hY : 0 < c * y := by positivity
      obtain ⟨hG0, hG1⟩ := hC (c * y) hY hcy
      rw [hexp] at hG0 hG1
      calc ‖((c * y : ℝ) : ℂ) * deriv G (c * y) + (1 / 2 : ℂ) * G (c * y)‖
          ≤ ‖((c * y : ℝ) : ℂ) * deriv G (c * y)‖ + ‖(1 / 2 : ℂ) * G (c * y)‖ := norm_add_le _ _
        _ ≤ C * (c * y) ^ (1 / 4 : ℝ) + 1 / 2 * (C * (c * y) ^ (1 / 4 : ℝ)) := by
            rw [norm_mul (1 / 2 : ℂ), show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
            have h2 : 1 / 2 * ‖G (c * y)‖ ≤ 1 / 2 * (C * (c * y) ^ (1 / 4 : ℝ)) := by linarith [hG0]
            linarith [hG1, h2]
        _ ≤ (C + C) * (c * y) ^ (1 / 4 : ℝ) := by
            have : 0 ≤ C * (c * y) ^ (1 / 4 : ℝ) := le_trans (norm_nonneg _) hG0
            nlinarith
  obtain ⟨K, hK0, hK⟩ := hkill
  exact ⟨K, hK0, fun y hy hcy => hK y hy hcy⟩

end GammaP41

end

open GammaP41

theorem exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded
    (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) (κ lam lam' : ℂ) (hκ : κ ≠ 0)
    (hU : lam' = lam) (hre : lam.im = 0) (hneg : lam.re ≤ 0)
    (f : ℕ → ℝ → ℂ) (hfN : ∀ y : ℝ, f (n + 1) y = 0)
    (hbdd : ∀ p : Fin (n + 1), ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ B)
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ δ := by
  
  simp only [hU] at hsys

  have hlam : lam = ((lam.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hre]
  set ν : ℝ := Real.sqrt (1 - 4 * lam.re) with hνdef
  have hν1 : 1 ≤ ν := by
    rw [hνdef]
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (1 - 4 * lam.re) := Real.sqrt_le_sqrt (by linarith)
  have hν0 : 0 ≤ ν := by linarith
  have hνsq : ν ^ 2 = 1 - 4 * lam.re := Real.sq_sqrt (by linarith)
  have hνC : ((ν : ℝ) : ℂ) ^ 2 = 1 - 4 * lam := by
    rw [hlam]; exact_mod_cast hνsq
  have hνre : ((ν : ℝ) : ℂ).re = ν := Complex.ofReal_re _

  choose B hB using hbdd
  have hbN : ∀ m : ℕ, m ≤ n + 1 → ∃ Bm : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f m y‖ ≤ Bm := by
    intro m hm
    rcases Nat.lt_or_ge m (n + 1) with h | h
    · exact ⟨B ⟨m, h⟩, hB ⟨m, h⟩⟩
    · have : m = n + 1 := le_antisymm hm h
      exact ⟨0, fun y _ _ => by rw [this, hfN]; simp⟩

  have hrel : ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y →
      2 * ((n : ℂ) - 2 * (p : ℕ)) * ((y : ℂ) * deriv (f p) y - f p y) +
        8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) *
          (κ * f ((p : ℕ) + 1) y + ((starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ)))) * f ((p : ℕ) - 1) y) = 0 := by
    intro p y hy
    have h1 := ((hsys p).2.2 y hy).1
    have h2 := ((hsys p).2.2 y hy).2
    linear_combination h1 - h2

  have hA : ∀ p : Fin (n + 1), ((n : ℂ) - 2 * (p : ℕ)) ≠ 0 → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ (1 - ε) := by
    intro p hq ε hε
    obtain ⟨Bup, hup⟩ := hbN ((p : ℕ) + 1) (by have := p.isLt; omega)
    obtain ⟨Bdn, hdn⟩ := hbN ((p : ℕ) - 1) (by have := p.isLt; omega)
    exact stepA _ hq κ ((starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ)))) (f p) (f ((p : ℕ) + 1)) (f ((p : ℕ) - 1))
      (hsys p).1 Bup Bdn hup hdn (hrel p) ε hε

  obtain ⟨m, hm⟩ := hn
  have hm1 : 1 ≤ m := by omega
  have hmn : m - 1 < n + 1 := by omega
  set p₁ : Fin (n + 1) := ⟨m - 1, hmn⟩ with hp₁
  have hp₁v : ((p₁ : ℕ) : ℂ) = (m : ℂ) - 1 := by
    rw [show (p₁ : ℕ) = m - 1 from rfl]; push_cast [Nat.cast_sub hm1]; ring
  have hnm : (n : ℂ) = (m : ℂ) + (m : ℂ) := by exact_mod_cast hm
  have hq₁ : ((n : ℂ) - 2 * ((p₁ : ℕ) : ℂ)) = 2 := by rw [hp₁v, hnm]; ring
  have hq₁' : ((n : ℂ) - 2 * ((p₁ : ℕ) : ℂ)) ≠ 0 := by rw [hq₁]; norm_num
  have hm2n : m - 1 - 1 < n + 1 := by omega
  set p₂ : Fin (n + 1) := ⟨m - 1 - 1, hm2n⟩ with hp₂
  have hq₂' : ((n : ℂ) - 2 * ((p₂ : ℕ) : ℂ)) ≠ 0 := by
    rw [show (p₂ : ℕ) = m - 1 - 1 from rfl, hnm]
    rcases Nat.lt_or_ge m 2 with h | h
    · have h1 : m = 1 := by omega
      subst h1; norm_num
    · rw [Nat.cast_sub (by omega : 1 ≤ m - 1), Nat.cast_sub hm1]
      push_cast
      intro h0
      have h4 : (4 : ℂ) = 0 := by linear_combination h0
      norm_num at h4

  set F : ℝ → ℂ := f (m - 1) with hFdef
  set F₂ : ℝ → ℂ := f (m - 1 - 1) with hF₂def
  have hFd : DifferentiableOn ℝ F (Set.Ioi 0) := (hsys p₁).1
  have hFd' : DifferentiableOn ℝ (deriv F) (Set.Ioi 0) := (hsys p₁).2.1
  have hF₂d : DifferentiableOn ℝ F₂ (Set.Ioi 0) := (hsys p₂).1
  obtain ⟨CF, hCF⟩ := hA p₁ hq₁' (1 / 8) (by norm_num)
  obtain ⟨CF₂, hCF₂⟩ := hA p₂ hq₂' (1 / 8) (by norm_num)

  set c₁ : ℂ := ((p₁ : ℕ) : ℂ) * ((n : ℂ) + 1 - ((p₁ : ℕ) : ℂ)) with hc₁
  have heqF : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv F) y - 3 * (y : ℂ) * deriv F y +
      (3 + 4 * lam - 16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 * (y : ℂ) ^ 2) * F y =
        8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * c₁ * (y : ℂ) * F₂ y := by
    intro y hy
    have h2 := ((hsys p₁).2.2 y hy).2
    rw [hq₁] at h2
    have hF1 : f ((p₁ : ℕ)) = F := rfl
    have hF2 : f ((p₁ : ℕ) - 1) = F₂ := rfl
    rw [hF1, hF2] at h2
    simp only [hc₁]
    push_cast at h2 ⊢
    linear_combination h2

  obtain ⟨K, hK0, hK⟩ := stepB κ lam hκ ν hν1 hνC F F₂ c₁ hFd hFd' hF₂d heqF (hA p₁ hq₁') (max CF₂ 0)
    (rpow_bound_mono le_rfl hCF₂)
  set c : ℝ := 2 * ‖κ‖ with hcdef
  have hκn : 0 < ‖κ‖ := norm_pos_iff.mpr hκ
  have hc : 0 < c := by positivity

  have hm_eq : (p₁ : ℕ) + 1 = m := by show m - 1 + 1 = m; omega
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set K₀ : ℝ := (4 * K + 8 * Real.pi * ‖κ‖ * ‖c₁‖ * max CF₂ 0) / (8 * Real.pi * ‖κ‖) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  have hnear : ∀ y : ℝ, 0 < y → y ≤ 1 → c * y ≤ 1 → ‖f m y‖ ≤ K₀ * y ^ (3 / 4 : ℝ) := by
    intro y hy hy1 hcy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have e := hrel p₁ y hy
    rw [hq₁, hm_eq] at e
    have hF1 : f ((p₁ : ℕ)) = F := rfl
    have hF2 : f ((p₁ : ℕ) - 1) = F₂ := rfl
    rw [hF1, hF2] at e
    have hfm : f m y = -(4 * ((y : ℂ) * deriv F y - F y) + 8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * ((starRingEnd ℂ) κ * c₁ * F₂ y)) /
        (8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ)) := by
      field_simp
      linear_combination e
    rw [hfm, norm_div, norm_neg]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hy]
    rw [div_le_iff₀ (by positivity)]
    have hA1 : ‖4 * ((y : ℂ) * deriv F y - F y) + 8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * ((starRingEnd ℂ) κ * c₁ * F₂ y)‖ ≤
        4 * (K * y ^ (7 / 4 : ℝ)) + 8 * Real.pi * y * (‖κ‖ * ‖c₁‖ * (max CF₂ 0 * y ^ (3 / 4 : ℝ))) := by
      calc _ ≤ ‖4 * ((y : ℂ) * deriv F y - F y)‖ + ‖8 * (Real.pi : ℂ) * Complex.I * (y : ℂ) * ((starRingEnd ℂ) κ * c₁ * F₂ y)‖ :=
            norm_add_le _ _
        _ = 4 * ‖(y : ℂ) * deriv F y - F y‖ + 8 * Real.pi * y * (‖κ‖ * ‖c₁‖ * ‖F₂ y‖) := by
            simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
              abs_of_pos Real.pi_pos, abs_of_pos hy, Complex.norm_conj]
        _ ≤ 4 * (K * y ^ (7 / 4 : ℝ)) + 8 * Real.pi * y * (‖κ‖ * ‖c₁‖ * (max CF₂ 0 * y ^ (3 / 4 : ℝ))) := by
            gcongr
            · exact hK y hy hcy
            · exact rpow_bound_mono (by norm_num : (3 / 4 : ℝ) ≤ 1 - 1 / 8) hCF₂ y hy hy1
    refine hA1.trans (le_of_eq ?_)
    have e74 : y ^ (7 / 4 : ℝ) = y ^ (3 / 4 : ℝ) * y := by
      rw [show (7 / 4 : ℝ) = 3 / 4 + 1 by norm_num, Real.rpow_add hy, Real.rpow_one]
    rw [e74, hK₀]
    field_simp

  have hall : ∀ p : Fin (n + 1), ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ Cp * y ^ (3 / 4 : ℝ) := by
    intro p
    by_cases hpm : (p : ℕ) = m
    ·
      obtain ⟨M, hM0, hM⟩ := bdd_Icc (f m) (by have := (hsys p).1; rwa [hpm] at this) (1 / c) 1 (by positivity)
      refine ⟨K₀ + M * c ^ (3 / 4 : ℝ), by positivity, fun y hy hy1 => ?_⟩
      rw [hpm]
      have hy34 : 0 ≤ y ^ (3 / 4 : ℝ) := (Real.rpow_pos_of_pos hy _).le
      rcases le_or_gt (c * y) 1 with hcy | hcy
      · calc ‖f m y‖ ≤ K₀ * y ^ (3 / 4 : ℝ) := hnear y hy hy1 hcy
          _ ≤ (K₀ + M * c ^ (3 / 4 : ℝ)) * y ^ (3 / 4 : ℝ) := by
              rw [add_mul]; linarith [mul_nonneg (mul_nonneg hM0 (Real.rpow_nonneg hc.le (3 / 4 : ℝ))) hy34]
      · have hyc' : 1 / c ≤ y := by rw [div_le_iff₀ hc, mul_comm]; exact hcy.le
        have h1 : 1 ≤ (c * y) ^ (3 / 4 : ℝ) := Real.one_le_rpow hcy.le (by norm_num)
        rw [Real.mul_rpow hc.le hy.le] at h1
        calc ‖f m y‖ ≤ M := hM y ⟨hyc', hy1⟩
          _ ≤ M * (c ^ (3 / 4 : ℝ) * y ^ (3 / 4 : ℝ)) := le_mul_of_one_le_right hM0 h1
          _ ≤ (K₀ + M * c ^ (3 / 4 : ℝ)) * y ^ (3 / 4 : ℝ) := by nlinarith
    · have hq : ((n : ℂ) - 2 * ((p : ℕ) : ℂ)) ≠ 0 := by
        rw [hnm]
        intro h0
        have : ((m : ℂ)) = ((p : ℕ) : ℂ) := by linear_combination h0 / 2
        exact hpm (by exact_mod_cast this.symm)
      obtain ⟨C, hC⟩ := hA p hq (1 / 4) (by norm_num)
      exact ⟨max C 0, le_max_right _ _, rpow_bound_mono (by norm_num : (3 / 4 : ℝ) ≤ 1 - 1 / 4) hC⟩
  choose Cp hCp using hall
  refine ⟨3 / 4, by norm_num, ∑ p : Fin (n + 1), Cp p, fun p y hy hy1 => ?_⟩
  calc ‖f p y‖ ≤ Cp p * y ^ (3 / 4 : ℝ) := (hCp p).2 y hy hy1
    _ ≤ (∑ q : Fin (n + 1), Cp q) * y ^ (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => (hCp q).1) (Finset.mem_univ p))
          (Real.rpow_pos_of_pos hy _).le

open scoped Real

namespace RoadBeta40

theorem bessel_normal_form (a m : ℝ) (hma : a = -2 * m) (b νsq : ℂ) (hν : νsq = (((m + 1 / 2) ^ 2 : ℝ) : ℂ) - b)
    (c : ℝ) (hc : 0 < c) (f F : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (heq : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv f) y + (a : ℂ) * (y : ℂ) * deriv f y +
      (b - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = F y) :
    DifferentiableOn ℝ (fun Y : ℝ => (((Y / c) ^ (-m) : ℝ) : ℂ) * f (Y / c)) (Set.Ioi 0) ∧
    DifferentiableOn ℝ (deriv (fun Y : ℝ => (((Y / c) ^ (-m) : ℝ) : ℂ) * f (Y / c))) (Set.Ioi 0) ∧
    ∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv (fun Y : ℝ => (((Y / c) ^ (-m) : ℝ) : ℂ) * f (Y / c))) Y +
        (1 / 4 - νsq - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * ((((Y / c) ^ (-m) : ℝ) : ℂ) * f (Y / c)) =
      (((Y / c) ^ (-m) : ℝ) : ℂ) * F (Y / c) := by
  

  set P : ℝ → ℂ := fun y => (((y ^ (-m)) : ℝ) : ℂ) with hPdef
  have hP : ∀ y : ℝ, 0 < y → HasDerivAt P (-(m : ℂ) * (y : ℂ)⁻¹ * P y) y := by
    intro y hy
    have h := Real.hasDerivAt_rpow_const (p := -m) (Or.inl hy.ne')
    rw [Real.rpow_sub_one hy.ne'] at h
    have h2 : HasDerivAt P (((-m * (y ^ (-m) / y) : ℝ) : ℂ)) y := by
      rw [hPdef]
      exact HasDerivAt.ofReal_comp h
    convert h2 using 1
    rw [hPdef]; push_cast; ring
  have hfd : ∀ y : ℝ, 0 < y → HasDerivAt f (deriv f y) y := fun y hy =>
    ((hf y hy).differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hfdd : ∀ y : ℝ, 0 < y → HasDerivAt (deriv f) (deriv (deriv f) y) y := fun y hy =>
    ((hf' y hy).differentiableAt (Ioi_mem_nhds hy)).hasDerivAt

  set g : ℝ → ℂ := fun y => P y * f y with hgdef
  set g1 : ℝ → ℂ := fun y => -(m : ℂ) * (y : ℂ)⁻¹ * P y * f y + P y * deriv f y with hg1def
  have hg1 : ∀ y : ℝ, 0 < y → HasDerivAt g (g1 y) y := by
    intro y hy
    have h := (hP y hy).mul (hfd y hy)
    convert h using 1
  have hderiv_g : ∀ y : ℝ, 0 < y → deriv g y = g1 y := fun y hy => (hg1 y hy).deriv

  have hinv : ∀ y : ℝ, 0 < y → HasDerivAt (fun x : ℝ => (x : ℂ)⁻¹) (-((y : ℂ) ^ 2)⁻¹) y := by
    intro y hy
    have h := (hasDerivAt_inv hy.ne').ofReal_comp
    have hfun : (fun x : ℝ => (((x⁻¹ : ℝ)) : ℂ)) = fun x : ℝ => (x : ℂ)⁻¹ := by funext x; push_cast; rfl
    rw [hfun] at h
    convert h using 1
    push_cast; ring
  set g2 : ℝ → ℂ := fun y =>
    (-(m : ℂ) * (-((y : ℂ) ^ 2)⁻¹) * P y + -(m : ℂ) * (y : ℂ)⁻¹ * (-(m : ℂ) * (y : ℂ)⁻¹ * P y)) * f y +
      (-(m : ℂ) * (y : ℂ)⁻¹ * P y) * deriv f y +
      ((-(m : ℂ) * (y : ℂ)⁻¹ * P y) * deriv f y + P y * deriv (deriv f) y) with hg2def
  have hg2 : ∀ y : ℝ, 0 < y → HasDerivAt g1 (g2 y) y := by
    intro y hy
    have hA : HasDerivAt (fun x : ℝ => -(m : ℂ) * (x : ℂ)⁻¹ * P x)
        (-(m : ℂ) * (-((y : ℂ) ^ 2)⁻¹) * P y + -(m : ℂ) * (y : ℂ)⁻¹ * (-(m : ℂ) * (y : ℂ)⁻¹ * P y)) y := by
      have h := ((hinv y hy).const_mul (-(m : ℂ))).mul (hP y hy)
      convert h using 1
    have h := (hA.mul (hfd y hy)).add ((hP y hy).mul (hfdd y hy))
    convert h using 1
  have hg1d : ∀ y : ℝ, 0 < y → HasDerivAt (deriv g) (g2 y) y := by
    intro y hy
    refine (hg2 y hy).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hy] with s hs
    exact hderiv_g s hs

  have key : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * g2 y + (1 / 4 - νsq - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = P y * F y := by
    intro y hy
    have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    have e := heq y hy
    rw [hma] at e
    push_cast at e
    have h1 : (y : ℂ) * (y : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hyc
    have h2 : (y : ℂ) ^ 2 * ((y : ℂ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hyc)
    simp only [hg2def, hgdef, hν]
    push_cast
    linear_combination P y * e + ((m : ℂ) + (m : ℂ) ^ 2) * P y * f y * h2 +
      (-2 * (m : ℂ) * (y : ℂ) * P y * deriv f y) * h1

  have hGfun : (fun Y : ℝ => (((Y / c) ^ (-m) : ℝ) : ℂ) * f (Y / c)) = fun Y => g (Y / c) := by
    funext Y; rfl
  rw [hGfun]
  set G : ℝ → ℂ := fun Y => g (Y / c) with hGdef
  have hdiv : ∀ Y : ℝ, HasDerivAt (fun X : ℝ => X / c) (1 / c) Y := fun Y => by
    simpa using (hasDerivAt_id Y).div_const c
  have hG1 : ∀ Y : ℝ, 0 < Y → HasDerivAt G ((1 / c) • g1 (Y / c)) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    exact (hg1 _ hy).scomp Y (hdiv Y)
  have hderiv_G : ∀ Y : ℝ, 0 < Y → deriv G Y = (1 / c) • g1 (Y / c) := fun Y hY => (hG1 Y hY).deriv
  have hG2 : ∀ Y : ℝ, 0 < Y → HasDerivAt (deriv G) ((1 / c) • ((1 / c) • g2 (Y / c))) Y := by
    intro Y hY
    have hy : 0 < Y / c := div_pos hY hc
    have h := ((hg2 _ hy).scomp Y (hdiv Y)).const_smul (1 / c)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hY] with s hs
    rw [hderiv_G s hs]; rfl
  have hGd : DifferentiableOn ℝ G (Set.Ioi 0) := fun Y hY => (hG1 Y hY).differentiableAt.differentiableWithinAt
  have hGd' : DifferentiableOn ℝ (deriv G) (Set.Ioi 0) := fun Y hY => (hG2 Y hY).differentiableAt.differentiableWithinAt
  refine ⟨hGd, hGd', fun Y hY => ?_⟩
  have hy : 0 < Y / c := div_pos hY hc
  rw [(hG2 Y hY).deriv]
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have k := key (Y / c) hy
  show (Y : ℂ) ^ 2 * ((1 / c) • ((1 / c) • g2 (Y / c))) + (1 / 4 - νsq - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * g (Y / c) = P (Y / c) * F (Y / c)
  set y : ℝ := Y / c with hydef
  have hYy : (Y : ℂ) = (c : ℂ) * (y : ℂ) := by rw [hydef]; push_cast; rw [mul_div_cancel₀ _ hcc]
  rw [Complex.real_smul, Complex.real_smul, hYy]
  push_cast
  have hid : ((c : ℂ) * (y : ℂ)) ^ 2 * (1 / (c : ℂ) * (1 / (c : ℂ) * g2 y)) +
      (1 / 4 - νsq - 4 * (π : ℂ) ^ 2 * ((c : ℂ) * (y : ℂ)) ^ 2) * g y =
      (y : ℂ) ^ 2 * g2 y + (1 / 4 - νsq - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y := by
    field_simp
  calc ((c : ℂ) * (y : ℂ)) ^ 2 * (1 / (c : ℂ) * (1 / (c : ℂ) * g2 y)) +
        (1 / 4 - νsq - 4 * (π : ℂ) ^ 2 * ((c : ℂ) * (y : ℂ)) ^ 2) * g y
      = (y : ℂ) ^ 2 * g2 y + (1 / 4 - νsq - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y := hid
    _ = P y * F y := k

theorem abs_re_lt_one_of_sq (ν lam : ℂ) (hν : ν ^ 2 = 1 - 4 * lam) (hreal : lam.im = 0) (hpos : 0 < lam.re) :
    |ν.re| < 1 := by
  
  have hre : ν.re * ν.re - ν.im * ν.im = 1 - 4 * lam.re := by
    have h := congrArg Complex.re hν
    rw [sq, Complex.mul_re] at h
    rw [h]; simp
  have him : 2 * (ν.re * ν.im) = 0 := by
    have h := congrArg Complex.im hν
    rw [sq, Complex.mul_im] at h
    have h2 : (1 - 4 * lam).im = 0 := by simp [hreal]
    rw [h2] at h
    linarith [h]
  rcases mul_eq_zero.1 him with h2 | h
  · norm_num at h2
  rcases mul_eq_zero.1 h with h | h
  · rw [h, abs_zero]; exact one_pos
  · rw [h, mul_zero, sub_zero] at hre
    rw [abs_lt]
    constructor <;> nlinarith [hre, hpos]

theorem bound_on_Icc_rpow (f : ℝ → ℂ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 1 / c ≤ y → y ≤ 1 → ‖f y‖ ≤ M * y ^ δ := by
  
  have hsub : Set.Icc (1 / c) 1 ⊆ Set.Ioi 0 := fun y hy => lt_of_lt_of_le (by positivity) hy.1
  have hcont : ContinuousOn f (Set.Icc (1 / c) 1) := (hf.continuousOn).mono hsub
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hcont).isBounded.exists_norm_le
  refine ⟨max M 0 * c ^ δ, by positivity, fun y hy1 hy2 => ?_⟩
  have hy : 0 < y := lt_of_lt_of_le (by positivity) hy1
  have hfy : ‖f y‖ ≤ max M 0 := (hM _ ⟨y, ⟨hy1, hy2⟩, rfl⟩).trans (le_max_left _ _)
  have hcy : 1 ≤ c ^ δ * y ^ δ := by
    rw [← Real.mul_rpow hc.le hy.le]
    have h1 : 1 ≤ c * y := by
      have := mul_le_mul_of_nonneg_left hy1 hc.le
      rwa [mul_one_div, div_self hc.ne'] at this
    exact Real.one_le_rpow h1 hδ
  calc ‖f y‖ ≤ max M 0 * 1 := by rw [mul_one]; exact hfy
    _ ≤ max M 0 * (c ^ δ * y ^ δ) := mul_le_mul_of_nonneg_left hcy (le_max_right _ _)
    _ = max M 0 * c ^ δ * y ^ δ := by ring

theorem rpow_neg_mul_self {x : ℝ} (hx : 0 < x) (m : ℝ) : x ^ (-m) * x ^ m = 1 := by
  
  rw [← Real.rpow_add hx, neg_add_cancel, Real.rpow_zero]

theorem rpow_coupling {x : ℝ} (hx : 0 < x) (m : ℝ) : x ^ (-m) * x = x ^ (2 : ℕ) * x ^ (-(m + 1)) := by
  
  have h1 : x ^ (-m) * x = x ^ (-m + 1) := by rw [Real.rpow_add hx, Real.rpow_one]
  have h2 : x ^ (2 : ℕ) * x ^ (-(m + 1)) = x ^ (-m + 1) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]; norm_num; ring_nf
  rw [h1, h2]

end RoadBeta40

open RoadBeta40

theorem exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (hlam' : lam' = lam) (hreal : lam.im = 0) (hpos : 0 < lam.re) (f : ℕ → ℝ → ℂ)
    (hsys :
    ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f ((p : ℕ) - 1) y = 0))
    (hfn : ∀ y : ℝ, f (n + 1) y = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ δ := by
  
  classical
  subst lam'

  have hκn : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  set c : ℝ := 2 * ‖κ‖ with hcdef
  have hc : 0 < c := by rw [hcdef]; positivity
  have hc16 : (16 : ℂ) * (π : ℂ) ^ 2 * ((‖κ‖ : ℝ) : ℂ) ^ 2 = 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 := by
    rw [hcdef]; push_cast; ring
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq (1 - 4 * lam) two_pos
  have hr1 : |ν.re| < 1 := abs_re_lt_one_of_sq ν lam hν hreal hpos
  have hr0 : 0 ≤ |ν.re| := abs_nonneg _
  set ε : ℝ := (1 - |ν.re|) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set d : ℝ := 1 / 2 - |ν.re| - ε with hddef
  set δ : ℝ := (1 - |ν.re|) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hdδ : ∀ u : ℝ, 0 ≤ u → δ ≤ (u + 1) / 2 + d := by intro u hu; rw [hddef, hδdef, hεdef]; linarith

  have hmem : ∀ p : ℕ, p ≤ n →
      DifferentiableOn ℝ (f p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (f p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f (p + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (f p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (f p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * f p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              f (p - 1) y = 0) := by
    intro p hp
    exact hsys ⟨p, Nat.lt_succ_of_le hp⟩

  set mt : ℕ → ℝ := fun p => ((n : ℝ) - 2 * p + 1) / 2 with hmt
  set Gt : ℕ → ℝ → ℂ := fun p Y => (((Y / c) ^ (-(mt p)) : ℝ) : ℂ) * f p (Y / c) with hGt
  set Ft : ℕ → ℝ → ℂ := fun p y =>
    8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) * f (p - 1) y with hFt
  have hNFt : ∀ p : ℕ, p ≤ n →
      DifferentiableOn ℝ (Gt p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (Gt p)) (Set.Ioi 0) ∧
      ∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv (Gt p)) Y + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * Gt p Y =
        (((Y / c) ^ (-(mt p)) : ℝ) : ℂ) * Ft p (Y / c) := by
    intro p hp
    obtain ⟨hd, hd', heq⟩ := hmem p hp
    have heq' : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv (f p)) y +
        ((-((n : ℝ) - 2 * p + 1) : ℝ) : ℂ) * (y : ℂ) * deriv (f p) y +
        ((((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam) - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) *
          f p y = Ft p y := by
      intro y hy
      have e := (heq y hy).2
      rw [hFt]; simp only []
      push_cast at e ⊢
      linear_combination e + (y : ℂ) ^ 2 * f p y * hc16
    have h := bessel_normal_form (-((n : ℝ) - 2 * p + 1)) (mt p) (by rw [hmt]; ring)
      ((((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam)) (ν ^ 2)
      (by rw [hν, hmt]; push_cast; ring) c hc (f p) (Ft p) hd hd' heq'
    simpa only [hGt] using h

  set mb : ℕ → ℝ := fun p => (2 * p - (n : ℝ) + 1) / 2 with hmb
  set Gb : ℕ → ℝ → ℂ := fun p Y => (((Y / c) ^ (-(mb p)) : ℝ) : ℂ) * f p (Y / c) with hGb
  set Fb : ℕ → ℝ → ℂ := fun p y => -(8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * f (p + 1) y) with hFb
  have hNFb : ∀ p : ℕ, p ≤ n →
      DifferentiableOn ℝ (Gb p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (Gb p)) (Set.Ioi 0) ∧
      ∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv (Gb p)) Y + (1 / 4 - ν ^ 2 - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * Gb p Y =
        (((Y / c) ^ (-(mb p)) : ℝ) : ℂ) * Fb p (Y / c) := by
    intro p hp
    obtain ⟨hd, hd', heq⟩ := hmem p hp
    have heq' : ∀ y : ℝ, 0 < y → (y : ℂ) ^ 2 * deriv (deriv (f p)) y +
        ((((n : ℝ) - 2 * p - 1) : ℝ) : ℂ) * (y : ℂ) * deriv (f p) y +
        ((((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam) - 4 * (π : ℂ) ^ 2 * (c : ℂ) ^ 2 * (y : ℂ) ^ 2) *
          f p y = Fb p y := by
      intro y hy
      have e := (heq y hy).1
      rw [hFb]; simp only []
      push_cast at e ⊢
      linear_combination e + (y : ℂ) ^ 2 * f p y * hc16
    have h := bessel_normal_form ((n : ℝ) - 2 * p - 1) (mb p) (by rw [hmb]; ring)
      ((((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam)) (ν ^ 2)
      (by rw [hν, hmb]; push_cast; ring) c hc (f p) (Fb p) hd hd' heq'
    simpa only [hGb] using h

  have hnormpow : ∀ (x e : ℝ), 0 < x → ‖(((x ^ e : ℝ)) : ℂ)‖ = x ^ e := fun x e hx => by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)]

  have hfG : ∀ (m : ℝ) (p : ℕ) (Y : ℝ), 0 < Y →
      ‖f p (Y / c)‖ = (Y / c) ^ m * ‖(((Y / c) ^ (-m) : ℝ) : ℂ) * f p (Y / c)‖ := by
    intro m p Y hY
    have hy : 0 < Y / c := div_pos hY hc
    rw [norm_mul, hnormpow _ _ hy, ← mul_assoc, mul_comm ((Y / c) ^ m), rpow_neg_mul_self hy, one_mul]

  have hmin : min (1 / 2 - |ν.re|) (2 + d) - ε = d := by
    rw [min_eq_left (by rw [hddef]; linarith), hddef]

  have hT : ∀ p : ℕ, 2 * p ≤ n → ∃ C : ℝ, ∀ Y : ℝ, 0 < Y → Y ≤ 1 → ‖Gt p Y‖ ≤ C * Y ^ d := by
    intro p
    induction p with
    | zero =>
      intro _
      obtain ⟨hGd, hGd', hGeq⟩ := hNFt 0 (Nat.zero_le _)
      have hfeq : ∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv (Gt 0)) Y +
          (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((0 : ℝ) : ℂ) * (Y : ℂ) - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * Gt 0 Y = 0 := by
        intro Y hY
        have h := hGeq Y hY
        have h0 : Ft 0 (Y / c) = 0 := by rw [hFt]; simp
        rw [h0, mul_zero] at h
        push_cast
        linear_combination h
      exact (LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode ν 0 (Gt 0) hGd hGd' hfeq).2 ε hε
    | succ p ih =>
      intro hp
      obtain ⟨C, hC⟩ := ih (by omega)
      obtain ⟨hGd, hGd', hGeq⟩ := hNFt (p + 1) (by omega)
      have hC0 : 0 ≤ C := by
        have h := hC 1 one_pos le_rfl
        rw [Real.one_rpow, mul_one] at h
        exact (norm_nonneg _).trans h

      set A : ℝ := 8 * π * ‖κ‖ * ((p + 1 : ℕ) * ((n : ℝ) - p)) * (1 / c) ^ (2 : ℕ) * C with hA
      have hforc : ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
          ‖(((Y / c) ^ (-(mt (p + 1))) : ℝ) : ℂ) * Ft (p + 1) (Y / c)‖ ≤ A * Y ^ (2 + d) := by
        intro Y hY hY1
        have hy : 0 < Y / c := div_pos hY hc
        have hmm : mt p = mt (p + 1) + 1 := by rw [hmt]; push_cast; ring
        have hnp : ‖((n : ℂ) + 1 - ((p + 1 : ℕ) : ℂ))‖ = (n : ℝ) - p := by
          have : (n : ℂ) + 1 - ((p + 1 : ℕ) : ℂ) = (((n : ℝ) - p : ℝ) : ℂ) := by push_cast; ring
          rw [this, Complex.norm_real, Real.norm_of_nonneg (by
            have : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
            linarith)]
        have hval : (((Y / c) ^ (-(mt (p + 1))) : ℝ) : ℂ) * Ft (p + 1) (Y / c) =
            (8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * (((p + 1 : ℕ) : ℂ) * ((n : ℂ) + 1 - ((p + 1 : ℕ) : ℂ)))) *
              ((((Y / c) ^ (2 : ℕ) : ℝ)) : ℂ) * Gt p Y := by
          rw [hFt, hGt]; simp only [Nat.add_sub_cancel]
          rw [hmm]
          have hr := rpow_coupling hy (mt (p + 1))
          have hr' : (((Y / c) ^ (-(mt (p + 1))) : ℝ) : ℂ) * ((Y / c : ℝ) : ℂ) =
              ((((Y / c) ^ (2 : ℕ) : ℝ)) : ℂ) * (((Y / c) ^ (-(mt (p + 1) + 1)) : ℝ) : ℂ) := by
            exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hr
          linear_combination (8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ *
            (((p + 1 : ℕ) : ℂ) * ((n : ℂ) + 1 - ((p + 1 : ℕ) : ℂ))) * f p (Y / c)) * hr'
        rw [hval, norm_mul, norm_mul]
        have hn1 : ‖8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * (((p + 1 : ℕ) : ℂ) * ((n : ℂ) + 1 - ((p + 1 : ℕ) : ℂ)))‖ =
            8 * π * ‖κ‖ * ((p + 1 : ℕ) * ((n : ℝ) - p)) := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hnp, Complex.norm_conj, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_natCast]
          norm_num
        have hn2 : ‖((((Y / c) ^ (2 : ℕ) : ℝ)) : ℂ)‖ = (1 / c) ^ (2 : ℕ) * Y ^ (2 : ℕ) := by
          rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hy.le _), div_pow]; ring
        rw [hn1, hn2, hA]
        have hG := hC Y hY hY1
        have hY2 : Y ^ (2 : ℕ) * Y ^ d = Y ^ (2 + d) := by
          rw [← Real.rpow_natCast Y 2, ← Real.rpow_add hY]; norm_num
        calc 8 * π * ‖κ‖ * (↑(p + 1) * (↑n - ↑p)) * ((1 / c) ^ 2 * Y ^ 2) * ‖Gt p Y‖
            ≤ 8 * π * ‖κ‖ * (↑(p + 1) * (↑n - ↑p)) * ((1 / c) ^ 2 * Y ^ 2) * (C * Y ^ d) := by
              apply mul_le_mul_of_nonneg_left hG
              have : (0 : ℝ) ≤ (n : ℝ) - p := by
                have : (p : ℝ) ≤ n := by exact_mod_cast (by omega : p ≤ n)
                linarith
              positivity
          _ = 8 * π * ‖κ‖ * (↑(p + 1) * (↑n - ↑p)) * (1 / c) ^ 2 * C * (Y ^ (2 : ℕ) * Y ^ d) := by ring
          _ = _ := by rw [hY2]
      have hfeq : ∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv (Gt (p + 1))) Y +
          (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((0 : ℝ) : ℂ) * (Y : ℂ) - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * Gt (p + 1) Y =
            (((Y / c) ^ (-(mt (p + 1))) : ℝ) : ℂ) * Ft (p + 1) (Y / c) := by
        intro Y hY
        have h := hGeq Y hY
        push_cast
        linear_combination h
      obtain ⟨C', hC'⟩ := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing ν 0 (2 + d) A (Gt (p + 1))
        (fun Y => (((Y / c) ^ (-(mt (p + 1))) : ℝ) : ℂ) * Ft (p + 1) (Y / c)) hGd hGd' hforc hfeq ε hε
      refine ⟨C', fun Y hY hY1 => ?_⟩
      have h := hC' Y hY hY1
      rwa [hmin] at h

  have hB : ∀ j : ℕ, 2 * j ≤ n → ∃ C : ℝ, ∀ Y : ℝ, 0 < Y → Y ≤ 1 → ‖Gb (n - j) Y‖ ≤ C * Y ^ d := by
    intro j
    induction j with
    | zero =>
      intro _
      obtain ⟨hGd, hGd', hGeq⟩ := hNFb n le_rfl
      have hfeq : ∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv (Gb n)) Y +
          (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((0 : ℝ) : ℂ) * (Y : ℂ) - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * Gb n Y = 0 := by
        intro Y hY
        have h := hGeq Y hY
        have h0 : Fb n (Y / c) = 0 := by rw [hFb]; simp [hfn]
        rw [h0, mul_zero] at h
        push_cast
        linear_combination h
      simpa only [Nat.sub_zero] using
        (LanglandsTunnell.norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode ν 0 (Gb n) hGd hGd' hfeq).2 ε hε
    | succ j ih =>
      intro hj
      obtain ⟨C, hC⟩ := ih (by omega)
      have hjn : n - (j + 1) + 1 = n - j := by omega
      obtain ⟨hGd, hGd', hGeq⟩ := hNFb (n - (j + 1)) (Nat.sub_le _ _)
      have hC0 : 0 ≤ C := by
        have h := hC 1 one_pos le_rfl
        rw [Real.one_rpow, mul_one] at h
        exact (norm_nonneg _).trans h
      set A : ℝ := 8 * π * ‖κ‖ * (1 / c) ^ (2 : ℕ) * C with hA
      have hforc : ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
          ‖(((Y / c) ^ (-(mb (n - (j + 1)))) : ℝ) : ℂ) * Fb (n - (j + 1)) (Y / c)‖ ≤ A * Y ^ (2 + d) := by
        intro Y hY hY1
        have hy : 0 < Y / c := div_pos hY hc
        have hmm : mb (n - j) = mb (n - (j + 1)) + 1 := by
          rw [hmb]; simp only []
          rw [Nat.cast_sub (by omega : j ≤ n), Nat.cast_sub (by omega : j + 1 ≤ n)]; push_cast; ring
        have hval : (((Y / c) ^ (-(mb (n - (j + 1)))) : ℝ) : ℂ) * Fb (n - (j + 1)) (Y / c) =
            -(8 * (Real.pi : ℂ) * Complex.I * κ) * ((((Y / c) ^ (2 : ℕ) : ℝ)) : ℂ) * Gb (n - j) Y := by
          rw [hFb, hGb]; simp only []
          rw [hjn, hmm]
          have hr := rpow_coupling hy (mb (n - (j + 1)))
          have hr' : (((Y / c) ^ (-(mb (n - (j + 1)))) : ℝ) : ℂ) * ((Y / c : ℝ) : ℂ) =
              ((((Y / c) ^ (2 : ℕ) : ℝ)) : ℂ) * (((Y / c) ^ (-(mb (n - (j + 1)) + 1)) : ℝ) : ℂ) := by
            exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hr
          linear_combination (-(8 * (Real.pi : ℂ) * Complex.I * κ) * f (n - j) (Y / c)) * hr'
        rw [hval, norm_mul, norm_mul]
        have hn1 : ‖-(8 * (Real.pi : ℂ) * Complex.I * κ)‖ = 8 * π * ‖κ‖ := by
          rw [norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_of_nonneg Real.pi_pos.le]
          norm_num
        have hn2 : ‖((((Y / c) ^ (2 : ℕ) : ℝ)) : ℂ)‖ = (1 / c) ^ (2 : ℕ) * Y ^ (2 : ℕ) := by
          rw [Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hy.le _), div_pow]; ring
        rw [hn1, hn2, hA]
        have hG := hC Y hY hY1
        have hY2 : Y ^ (2 : ℕ) * Y ^ d = Y ^ (2 + d) := by
          rw [← Real.rpow_natCast Y 2, ← Real.rpow_add hY]; norm_num
        calc 8 * π * ‖κ‖ * ((1 / c) ^ 2 * Y ^ 2) * ‖Gb (n - j) Y‖
            ≤ 8 * π * ‖κ‖ * ((1 / c) ^ 2 * Y ^ 2) * (C * Y ^ d) := by
              apply mul_le_mul_of_nonneg_left hG; positivity
          _ = 8 * π * ‖κ‖ * (1 / c) ^ 2 * C * (Y ^ (2 : ℕ) * Y ^ d) := by ring
          _ = _ := by rw [hY2]
      have hfeq : ∀ Y : ℝ, 0 < Y → (Y : ℂ) ^ 2 * deriv (deriv (Gb (n - (j + 1)))) Y +
          (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((0 : ℝ) : ℂ) * (Y : ℂ) - 4 * (π : ℂ) ^ 2 * (Y : ℂ) ^ 2) * Gb (n - (j + 1)) Y =
            (((Y / c) ^ (-(mb (n - (j + 1)))) : ℝ) : ℂ) * Fb (n - (j + 1)) (Y / c) := by
        intro Y hY
        have h := hGeq Y hY
        push_cast
        linear_combination h
      obtain ⟨C', hC'⟩ := LanglandsTunnell.norm_le_mul_rpow_near_zero_of_whittaker_ode_of_forcing ν 0 (2 + d) A
        (Gb (n - (j + 1))) (fun Y => (((Y / c) ^ (-(mb (n - (j + 1)))) : ℝ) : ℂ) * Fb (n - (j + 1)) (Y / c)) hGd hGd' hforc hfeq ε hε
      refine ⟨C', fun Y hY hY1 => ?_⟩
      have h := hC' Y hY hY1
      rwa [hmin] at h

  have hmember : ∀ p : ℕ, p ≤ n → ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ δ := by
    intro p hp

    obtain ⟨m, hmδ, C, hC⟩ : ∃ m : ℝ, δ ≤ m + d ∧ ∃ C : ℝ, ∀ Y : ℝ, 0 < Y → Y ≤ 1 →
        ‖(((Y / c) ^ (-m) : ℝ) : ℂ) * f p (Y / c)‖ ≤ C * Y ^ d := by
      by_cases h2 : 2 * p ≤ n
      · obtain ⟨C, hC⟩ := hT p h2
        refine ⟨mt p, ?_, C, hC⟩
        have : mt p = (((n : ℝ) - 2 * p) + 1) / 2 := by rw [hmt]
        rw [this]
        have h2' : (2 * p : ℝ) ≤ n := by exact_mod_cast h2
        exact hdδ _ (by linarith)
      · have hj : 2 * (n - p) ≤ n := by omega
        obtain ⟨C, hC⟩ := hB (n - p) hj
        have hnp : n - (n - p) = p := by omega
        rw [hnp] at hC
        refine ⟨mb p, ?_, C, hC⟩
        have : mb p = ((2 * p - (n : ℝ)) + 1) / 2 := by rw [hmb]
        rw [this]
        have h2' : (n : ℝ) ≤ 2 * p := by exact_mod_cast (by omega : n ≤ 2 * p)
        exact hdδ _ (by linarith)
    have hC0 : 0 ≤ C := by
      have h := hC 1 one_pos le_rfl
      rw [Real.one_rpow, mul_one] at h
      exact (norm_nonneg _).trans h

    obtain ⟨M, hM0, hM⟩ := bound_on_Icc_rpow (f p) (hmem p hp).1 c δ hc hδ.le
    refine ⟨C * c ^ d + M, fun y hy hy1 => ?_⟩
    by_cases hyc : y ≤ 1 / c
    · have hY : 0 < c * y := mul_pos hc hy
      have hY1 : c * y ≤ 1 := by rwa [le_div_iff₀ hc, mul_comm] at hyc
      have h := hC (c * y) hY hY1
      rw [mul_div_cancel_left₀ _ hc.ne'] at h

      have hfy : ‖f p y‖ = y ^ m * ‖(((y ^ (-m)) : ℝ) : ℂ) * f p y‖ := by
        rw [norm_mul, hnormpow _ _ hy, ← mul_assoc, mul_comm (y ^ m), rpow_neg_mul_self hy, one_mul]
      rw [hfy]
      have hexp : y ^ m * (c * y) ^ d = c ^ d * y ^ (m + d) := by
        rw [Real.mul_rpow hc.le hy.le, Real.rpow_add hy]; ring
      have hmono : y ^ (m + d) ≤ y ^ δ := Real.rpow_le_rpow_of_exponent_ge hy hy1 hmδ
      calc y ^ m * ‖(((y ^ (-m)) : ℝ) : ℂ) * f p y‖ ≤ y ^ m * (C * (c * y) ^ d) :=
            mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hy.le _)
        _ = C * c ^ d * y ^ (m + d) := by rw [mul_comm C, ← mul_assoc, hexp]; ring
        _ ≤ C * c ^ d * y ^ δ := mul_le_mul_of_nonneg_left hmono (by positivity)
        _ ≤ (C * c ^ d + M) * y ^ δ := by rw [add_mul]; linarith [mul_nonneg hM0 (Real.rpow_nonneg hy.le δ)]
    · push Not at hyc
      calc ‖f p y‖ ≤ M * y ^ δ := hM y hyc.le hy1
        _ ≤ (C * c ^ d + M) * y ^ δ := by
            rw [add_mul]; linarith [mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hc.le d)) (Real.rpow_nonneg hy.le δ)]

  choose Cp hCp using hmember
  refine ⟨δ, hδ, ∑ p : Fin (n + 1), max (Cp p (Nat.le_of_lt_succ p.isLt)) 0, fun p y hy hy1 => ?_⟩
  have h := hCp p (Nat.le_of_lt_succ p.isLt) y hy hy1
  have hle : Cp p (Nat.le_of_lt_succ p.isLt) ≤ ∑ q : Fin (n + 1), max (Cp q (Nat.le_of_lt_succ q.isLt)) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun q : Fin (n + 1) => max (Cp q (Nat.le_of_lt_succ q.isLt)) 0)
      (fun q _ => le_max_right _ _) (Finset.mem_univ p))
  exact h.trans (mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hy.le _))

end LanglandsTunnell
