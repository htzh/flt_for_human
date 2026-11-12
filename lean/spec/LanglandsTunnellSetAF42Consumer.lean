/-
  Consumer zone for `FLTForHuman/LanglandsTunnell/TorusSystemGrowth.lean` (order AF42).

  A `spec/` probe, not a library module: it *consumes* the four headlines in composition, never by
  `#check`.

  The four headlines are one statement about one object: the growth near `y = 0` of an `n`-step
  `SU(2)`-string `f` solving the `GL₂(ℂ)` Whittaker system is decided by the Casimir eigenvalue `λ`
  against the string's weight set.

  * **T** `casimir_pos_or_discrete_or_zero_of_weightSet`: a non-empty weight set `S ⊆ ℤ` closed under
    `±2`, on which the two Casimir forms `4λ + n(n ∓ 2)` are non-negative, forces `λ > 0`, or
    `λ = k(k-2)/4` for some `k ≥ 2` with `S` above `|k|` and of the parity of `k`, or `λ = 0` with
    `0 ∈ S`.
  * **G** `exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded`: for even
    `n`, real `λ = λ' ≤ 0` and a string bounded on `(0, 1]`, the components obey `‖f p y‖ ≤ C · y ^ δ`
    with `δ > 0` — the complementary/discrete regime, where the exponent is `3/4`.
  * **R** `exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos`: for real `λ = λ' > 0` the
    same conclusion, with the Bessel normal form `y ↦ y ^ (-m)` supplying the exponent `δ = (1-|Re ν|)/2`
    from `ν ^ 2 = 1 - 4λ`.

  The two zones below read them off.

  * **Zone 1** is the trichotomy itself, on two weight sets at `λ = 0`. On `S = {0}` the closure
    clauses are vacuous and the conclusion lands in the **third** disjunct, `λ = 0 ∧ 0 ∈ S`; the
    first disjunct `0 < 0` is impossible and the discrete disjunct forces `k₀ ≤ |0| = 0` against
    `2 ≤ k₀`.

    The order's second reading, at the singleton `S = {2}`, **cannot be typed**: `clplus` at `n = 2`
    is `0 < 4 · 0 + 2 · 4 = 8`, so it demands `4 ∈ S`, and `clminus` at `n = 2` is `0 < 4λ + 0`, which
    for the `hminus`-allowed `λ ≥ 0` demands `0 ∈ S` unless `λ = 0`, while `hminus` at `n = 2` is
    `0 ≤ 4λ`. No `λ` satisfies the four hypotheses at `S = {2}`. The real set next to it is its
    `±2`-closure, `S = {n : ℤ | 2 ≤ n ∧ Even n}` (`evensAbove`), and there the conclusion lands in the
    **second**, discrete, disjunct — and forces `k₀ = 2`, since `k₀ ≤ |2|`. This substitution is the
    one deviation of the zone.

  * **Zone 2** feeds **G** and **R** at the same even `n = 2` and compares the two exponents. The
    order's data `λ = λ' = 0` cannot be typed on the **R** side either: **R** carries
    `hpos : 0 < lam.re`, unsatisfiable at `λ = 0`, and the two headlines' regimes are disjoint in
    `Re λ` by construction (`G` needs `Re λ ≤ 0`, `R` needs `0 < Re λ`) — that disjointness *is* the
    trichotomy. So **G** is read at `λ = λ' = 0` and **R** at `λ = λ' = 1` (`Re λ = 1 > 0`), at the
    same `n = 2`. The comparison is then the meet of the two exponents: both bounds transfer to
    `min δ_G δ_R > 0`, which is positive and carries the two strings simultaneously — the exponent of
    the weaker of the two, i.e. the one both headlines support at once.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF42Consumer.lean` and never enters the build.
-/
import FLTForHuman.LanglandsTunnell.TorusSystemGrowth

set_option autoImplicit false

open scoped Real

noncomputable section

namespace LanglandsTunnellSetAF42Consumer

/-! ### Zone 1: the trichotomy on `{0}` and on the `±2`-closure of `{2}` -/

/-- The `±2`-closure of the suggested singleton `{2}`: the even integers above `2`. `clplus` at
`n = 2` puts `4` in any admissible set, `clplus` again `6`, and so on; `clminus` is the same
downward. -/
def evensAbove : Set ℤ := {n : ℤ | 2 ≤ n ∧ Even n}

/-- **Zone 1a.** The trichotomy at `S = {0}`, `λ = 0`: the **third** disjunct, `λ = 0 ∧ 0 ∈ S`. The
four hypotheses hold — the closure clauses are vacuous because `4 · 0 + 0 · (0 ± 2) = 0` is never
positive — and of the three disjuncts only the third survives: `0 < 0` is impossible, and the discrete
disjunct's `k₀ ≤ |0|` contradicts `2 ≤ k₀`. -/
theorem trichotomy_at_zero :
    (0 : ℝ) = 0 ∧ (0 : ℤ) ∈ ({0} : Set ℤ) := by
  have hS : ({0} : Set ℤ).Nonempty := ⟨0, by simp⟩
  have hminus : ∀ n ∈ ({0} : Set ℤ), 0 ≤ 4 * (0 : ℝ) + n * (n - 2) := by
    intro n hn
    simp only [Set.mem_singleton_iff] at hn
    subst hn
    norm_num
  have hplus : ∀ n ∈ ({0} : Set ℤ), 0 ≤ 4 * (0 : ℝ) + n * (n + 2) := by
    intro n hn
    simp only [Set.mem_singleton_iff] at hn
    subst hn
    norm_num
  have clminus : ∀ n ∈ ({0} : Set ℤ), 0 < 4 * (0 : ℝ) + n * (n - 2) → n - 2 ∈ ({0} : Set ℤ) := by
    intro n hn h
    simp only [Set.mem_singleton_iff] at hn
    subst hn
    norm_num at h
  have clplus : ∀ n ∈ ({0} : Set ℤ), 0 < 4 * (0 : ℝ) + n * (n + 2) → n + 2 ∈ ({0} : Set ℤ) := by
    intro n hn h
    simp only [Set.mem_singleton_iff] at hn
    subst hn
    norm_num at h
  rcases LanglandsTunnell.casimir_pos_or_discrete_or_zero_of_weightSet 0 ({0} : Set ℤ) hS hminus
    hplus clminus clplus with h | ⟨k₀, hk2, -, hall⟩ | h
  · exact absurd h (lt_irrefl 0)
  · have hle : (k₀ : ℤ) ≤ 0 := by simpa using (hall 0 (by simp)).1
    omega
  · exact h

/-- **Zone 1b.** The trichotomy on `evensAbove`, the `±2`-closure of the order's `{2}`, at `λ = 0`:
the **second**, discrete, disjunct — with `k₀` forced to `2` by `k₀ ≤ |2|` — while the third disjunct
fails because `0 ∉ evensAbove`. The four hypotheses hold: `n ≥ 2` makes `n(n-2)` and `n(n+2)`
non-negative, `0 < n(n-2)` forces `n ≥ 4` and hence `n - 2 ≥ 2`, and `Even` is preserved by `±2`. -/
theorem trichotomy_on_evens :
    (∃ k₀ : ℕ, k₀ = 2 ∧ ∀ n ∈ evensAbove, (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∧
      (0 : ℤ) ∉ evensAbove := by
  have h2 : (2 : ℤ) ∈ evensAbove := ⟨le_rfl, ⟨1, by norm_num⟩⟩
  have hzero : (0 : ℤ) ∉ evensAbove := by
    intro h
    have := h.1
    omega
  have hS : evensAbove.Nonempty := ⟨2, h2⟩
  have hminus : ∀ n ∈ evensAbove, 0 ≤ 4 * (0 : ℝ) + n * (n - 2) := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 2) := by nlinarith
    simpa using this
  have hplus : ∀ n ∈ evensAbove, 0 ≤ 4 * (0 : ℝ) + n * (n + 2) := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 2) := by nlinarith
    simpa using this
  have clminus : ∀ n ∈ evensAbove, 0 < 4 * (0 : ℝ) + n * (n - 2) → n - 2 ∈ evensAbove := by
    intro n hn hpos
    have hn2 : 2 ≤ n := hn.1
    have hne : n ≠ 2 := by
      intro h
      rw [h] at hpos
      norm_num at hpos
    obtain ⟨r, hr⟩ := hn.2
    have hn4 : 4 ≤ n := by omega
    exact ⟨by omega, ⟨r - 1, by omega⟩⟩
  have clplus : ∀ n ∈ evensAbove, 0 < 4 * (0 : ℝ) + n * (n + 2) → n + 2 ∈ evensAbove := by
    intro n hn _
    have hn2 : 2 ≤ n := hn.1
    obtain ⟨r, hr⟩ := hn.2
    exact ⟨by omega, ⟨r + 1, by omega⟩⟩
  refine ⟨?_, hzero⟩
  rcases LanglandsTunnell.casimir_pos_or_discrete_or_zero_of_weightSet 0 evensAbove hS hminus hplus
    clminus clplus with h | ⟨k₀, hk2, -, hall⟩ | h
  · exact absurd h (lt_irrefl 0)
  · have hle : (k₀ : ℤ) ≤ 2 := by simpa using (hall 2 h2).1
    exact ⟨k₀, by omega, hall⟩
  · exact absurd h.2 hzero

/-! ### Zone 2: the two growth bounds at the same even `n = 2` -/

section growth

variable (κ : ℂ) (f g : ℕ → ℝ → ℂ)

variable (hfn : ∀ y : ℝ, f 3 y = 0) (hgn : ∀ y : ℝ, g 3 y = 0)
variable (hbdd : ∀ p : Fin 3, ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖f p y‖ ≤ B)

-- `f` solves the torus system at `λ = λ' = 0` — the complementary/discrete regime of **G**.
variable (hsysF : LanglandsTunnell.AlphaAux.HSys 2 κ 0 0 f)

-- `g` solves the same system at `λ = λ' = 1 > 0` — the principal-series regime of **R**.
variable (hsysG : LanglandsTunnell.AlphaAux.HSys 2 κ 1 1 g)

include hfn hgn hbdd hsysF hsysG in
/-- **Zone 2.** **G** at `n = 2`, `λ = λ' = 0` supplies an exponent `δ_G > 0`; **R** at the same
`n = 2`, `λ = λ' = 1` supplies `δ_R > 0`. On `(0, 1]` the `rpow` is decreasing in the exponent, so each
bound transfers to `min δ_G δ_R`, which is positive: the comparison of the two exponents is the meet,
and the weaker of the two exponents is the one that carries both strings. -/
theorem growth_exponents_meet (hκ : κ ≠ 0) :
    ∃ δG : ℝ, 0 < δG ∧ ∃ δR : ℝ, 0 < δR ∧ 0 < min δG δR ∧ ∃ C D : ℝ,
      (∀ (p : Fin 3) (y : ℝ), 0 < y → y ≤ 1 → ‖f p y‖ ≤ C * y ^ min δG δR) ∧
      (∀ (p : Fin 3) (y : ℝ), 0 < y → y ≤ 1 → ‖g p y‖ ≤ D * y ^ min δG δR) := by
  obtain ⟨δG, hδG, CG, hCG⟩ :=
    LanglandsTunnell.exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded
      2 (by norm_num) (by norm_num) κ 0 0 hκ rfl (by norm_num) (by norm_num) f hfn hbdd hsysF
  obtain ⟨δR, hδR, CR, hCR⟩ :=
    LanglandsTunnell.exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos
      2 κ 1 1 hκ rfl (by norm_num) (by norm_num) g hsysG hgn
  refine ⟨δG, hδG, δR, hδR, lt_min hδG hδR, max CG 0, max CR 0, ?_, ?_⟩
  · intro p y hy hy1
    calc ‖f p y‖ ≤ CG * y ^ δG := hCG p y hy hy1
      _ ≤ max CG 0 * y ^ δG := by
          gcongr
          exact le_max_left _ _
      _ ≤ max CG 0 * y ^ min δG δR :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hy hy1 (min_le_left δG δR)) (le_max_right _ _)
  · intro p y hy hy1
    calc ‖g p y‖ ≤ CR * y ^ δR := hCR p y hy hy1
      _ ≤ max CR 0 * y ^ δR := by
          gcongr
          exact le_max_left _ _
      _ ≤ max CR 0 * y ^ min δG δR :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hy hy1 (min_le_right δG δR)) (le_max_right _ _)

end growth

end LanglandsTunnellSetAF42Consumer
