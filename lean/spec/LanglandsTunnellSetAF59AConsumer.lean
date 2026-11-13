/-
  SET-AF59A consumer: the Whittaker system's string linear dependence, spent.

  **The row.** `FLTForHuman/LanglandsTunnell/WhittakerODELinearDependence.lean` (row P):
  `LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth`.  Two
  strings `f`, `g` of moderate growth whose every entry solves the coupled second-order Whittaker
  system of spectral data `(n, κ, lam, lam')` are linearly dependent over `ℂ`: one pair `(c₁, c₂)`
  annihilates *every* entry of *both* strings at once.

  **The readings.**  The row is spent at the place where the local theory stops caring about the
  individual string entries:

  * Zone A1 — the *derivative form*.  The dependence the row delivers is a pointwise relation
    `c₁ * f p y + c₂ * g p y = 0`.  The consumer asks for the relation together with its
    differentiated companion `c₁ * (f p)' y + c₂ * (g p)' y = 0`, i.e. the same pair `(c₁, c₂)`
    annihilates the jet `(f p, (f p)', g p, (g p)')` at every `y`, for every `p`.  That is the shape
    the ODE layer consumes: the two strings span a one-dimensional space of jets, not merely of
    values, so no Wronskian can separate them.
  * Zone A2 — the *Wronskian consequence*.  From the pair `(c₁, c₂)` the consumer reads off
    `f p y * (g p)' y - (f p)' y * g p y = 0` on `y > 0` for every `p`: the Wronskian of two
    moderate-growth solutions of the system vanishes identically.  This is what makes the solution
    space one-dimensional — the local `L`-factor is then well defined, which is the whole point of
    the row.
  * Zone A3 — the *executed instance*.  The row is also applied to concrete data: `n = 0`, `κ = 1`,
    `lam = lam' = 0` and the zero string `f = g = 0`, which solves every Whittaker system.  The
    headline then yields the pair `(1, 0)`, so the statement is not vacuous and the dependence it
    asserts is the trivial one.

  The statement-level data (`n`, `κ`, `lam`, `lam'`, `f`, `g`) cannot be instantiated apart from the
  zero string: they are the spectral data of an arbitrary pair of moderate-growth solutions, so they
  enter in hypothesis form in zones A1 and A2, which is the legitimate reading for this row.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.LanglandsTunnell.WhittakerODELinearDependence

set_option autoImplicit false

noncomputable section

open Filter Topology Set
open scoped Real NNReal

namespace LanglandsTunnell.SetAF59AConsumer

/-- **Zone A1, the derivative form.**  The headline's pair `(c₁, c₂)` annihilates the values *and*
the derivatives of every entry of both strings: the dependence is between jets, not just between
values. -/
theorem consumer_dependence_in_derivative_form
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (f g : ℕ → ℝ → ℂ)
    (hf : ∀ p : Fin (n + 1),
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
    (hg : ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (g p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (g p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (g p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (g p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * g p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * g ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (g p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (g p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * g p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              g ((p : ℕ) - 1) y = 0))
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f 0 y‖ ≤ C * y ^ N)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g 0 y‖ ≤ C * y ^ N) :
    ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ p : Fin (n + 1), ∀ y : ℝ, 0 < y →
      c.1 * f p y + c.2 * g p y = 0 ∧ c.1 * deriv (f p) y + c.2 * deriv (g p) y = 0 := by
  obtain ⟨c, hc, hdep⟩ :=
    LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth
      n κ lam lam' hκ f g hf hg hfgr hggr
  refine ⟨c, hc, fun p y hy => ⟨hdep p y hy, ?_⟩⟩
  have hmem : Set.Ioi (0 : ℝ) ∈ 𝓝 y := Ioi_mem_nhds hy
  have hF : DifferentiableAt ℝ (f p) y := (hf p).1.differentiableAt hmem
  have hG : DifferentiableAt ℝ (g p) y := (hg p).1.differentiableAt hmem
  have heq : (fun z => c.1 * f p z + c.2 * g p z) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hmem] with z hz
    exact hdep p z hz
  have h1 : deriv (fun z => c.1 * f p z + c.2 * g p z) y = 0 := by
    rw [heq.deriv_eq, deriv_const]
  have h2 : deriv (fun z => c.1 * f p z + c.2 * g p z) y =
      c.1 * deriv (f p) y + c.2 * deriv (g p) y :=
    ((hF.hasDerivAt.const_mul c.1).add (hG.hasDerivAt.const_mul c.2)).deriv
  rw [← h2, h1]

/-- **Zone A2, the Wronskian consequence.**  The Wronskian of the two strings vanishes identically:
the pair `(c₁, c₂)` makes the two jets proportional wherever `c₂ ≠ 0`, and kills both jets wherever
`c₂ = 0`; in either case `f * g' - f' * g = 0` on `y > 0`, entry by entry. -/
theorem consumer_wronskian_vanishes
    (n : ℕ) (κ lam lam' : ℂ) (hκ : κ ≠ 0) (f g : ℕ → ℝ → ℂ)
    (hf : ∀ p : Fin (n + 1),
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
    (hg : ∀ p : Fin (n + 1),
      DifferentiableOn ℝ (g p) (Set.Ioi 0) ∧ DifferentiableOn ℝ (deriv (g p)) (Set.Ioi 0) ∧
      ∀ y : ℝ, 0 < y →
        ((y : ℂ) ^ 2 * deriv (deriv (g p)) y + (((n : ℂ) - 2 * (p : ℕ)) - 1) * (y : ℂ) * deriv (g p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) - 4) / 4 + 4 * lam -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * g p y +
            8 * (Real.pi : ℂ) * Complex.I * κ * (y : ℂ) * g ((p : ℕ) + 1) y = 0) ∧
        ((y : ℂ) ^ 2 * deriv (deriv (g p)) y - (((n : ℂ) - 2 * (p : ℕ)) + 1) * (y : ℂ) * deriv (g p) y +
            (((n : ℂ) - 2 * (p : ℕ)) * (((n : ℂ) - 2 * (p : ℕ)) + 4) / 4 + 4 * lam' -
                16 * (Real.pi : ℂ) ^ 2 * ((‖κ‖ ^ 2 : ℝ) : ℂ) * (y : ℂ) ^ 2) * g p y -
            8 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) κ * ((p : ℕ) * ((n : ℂ) + 1 - (p : ℕ))) * (y : ℂ) *
              g ((p : ℕ) - 1) y = 0))
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f 0 y‖ ≤ C * y ^ N)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g 0 y‖ ≤ C * y ^ N) :
    ∀ p : Fin (n + 1), ∀ y : ℝ, 0 < y →
      f p y * deriv (g p) y - deriv (f p) y * g p y = 0 := by
  obtain ⟨c, hc, hder⟩ :=
    consumer_dependence_in_derivative_form n κ lam lam' hκ f g hf hg hfgr hggr
  intro p y hy
  obtain ⟨h1, h2⟩ := hder p y hy
  by_cases hc₂ : c.2 = 0
  · have h1' : c.1 * f p y = 0 := by
      simpa only [hc₂, zero_mul, add_zero] using h1
    have h2' : c.1 * deriv (f p) y = 0 := by
      simpa only [hc₂, zero_mul, add_zero] using h2
    have hc₁ : c.1 ≠ 0 := by
      intro h
      exact hc (Prod.ext h hc₂)
    have h : c.1 * (f p y * deriv (g p) y - deriv (f p) y * g p y) = 0 := by
      linear_combination deriv (g p) y * h1' - g p y * h2'
    exact (mul_eq_zero.mp h).resolve_left hc₁
  · have h : c.2 * (f p y * deriv (g p) y - deriv (f p) y * g p y) = 0 := by
      linear_combination f p y * h2 - deriv (f p) y * h1
    exact (mul_eq_zero.mp h).resolve_left hc₂

/-- **Zone A3, the executed instance.**  The headline applies to the zero string with `n = 0`,
`κ = 1`, `lam = lam' = 0` — the trivial moderate-growth solution of every Whittaker system — and
returns a nonzero pair; the dependence it asserts is therefore not vacuous. -/
theorem consumer_zero_string_witness :
    ∃ c : ℂ × ℂ, c ≠ 0 ∧
      ∀ p : Fin (0 + 1), ∀ y : ℝ, 0 < y →
        c.1 * (fun (_ : ℕ) (_ : ℝ) => (0 : ℂ)) p y + c.2 * (fun (_ : ℕ) (_ : ℝ) => (0 : ℂ)) p y = 0 := by
  have hz : deriv (fun _ : ℝ => (0 : ℂ)) = 0 := by
    funext y
    simp
  refine LanglandsTunnell.linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth
    0 1 0 0 one_ne_zero (fun _ _ => 0) (fun _ _ => 0) ?_ ?_ ⟨0, 0, ?_⟩ ⟨0, 0, ?_⟩
  · intro p
    refine ⟨?_, ?_, ?_⟩
    · exact differentiableOn_const (0 : ℂ)
    · rw [hz]
      exact differentiableOn_const (0 : ℂ)
    · intro y hy
      constructor <;> simp [hz]
  · intro p
    refine ⟨?_, ?_, ?_⟩
    · exact differentiableOn_const (0 : ℂ)
    · rw [hz]
      exact differentiableOn_const (0 : ℂ)
    · intro y hy
      constructor <;> simp [hz]
  · intro y hy
    simp
  · intro y hy
    simp

end LanglandsTunnell.SetAF59AConsumer
