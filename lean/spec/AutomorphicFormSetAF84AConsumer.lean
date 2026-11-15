/-
  SET-AF84A consumer: the finite Siegel cover, read as a *uniform* cover.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/Siegel/FiniteCover.lean` carries
  `exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet`: there are a finite set `T` of adelic
  matrices and thresholds `c > 0`, `u` such that for **every** window `d₁ ≤ d₂` with `d₂ > 0` the union of
  the translates `· * x` (`x ∈ T`) of `centreCutSiegelSet K c u d₁ d₂` covers `GL₂(𝔸_K)` modulo the centre
  (`CoversModCentre K D := ∀ g, ∃ γ z, globalPoints γ * g * centralScalar z ∈ D`).

  **The readings.** The row's quantifier order matters and is what makes it quantitative: `∃ T c u, ∀
  window, …`. The consumers of a cover care about the *other* two consequences, neither of which the row
  states outright:

  * Zone 1 — **uniformity across windows**: the same `T`, `c` and `u` serve two arbitrary valid windows
    at once, i.e. the quantifier swap `∀ window, ∃ T c u` — the form a proof wants when it has to choose a
    window *after* the cover has been fixed.
  * Zone 2 — **the cover is not vacuous**: every valid window's finite union is inhabited, which is the
    `CoversModCentre` unfolding composed with the fact that the set is a union of translates.
  * Zone 3 — **monotonicity**: `CoversModCentre` is monotone in the set
    (`SiegelCovering.CoversModCentre.mono`, already ported), so the row's cover transfers to any superset —
    the form the `L²` estimates use when they enlarge the window's set by a null set.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF84AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Siegel.FiniteCover

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped Classical

namespace AutomorphicFormSetAF84AConsumer

/-! ### Zone 1 — one finite set and one pair of thresholds serve every window -/

/-- **Zone 1.** The quantifier swap: there are `T`, `c`, `u` such that *any two* valid windows are covered
by the same translates of the same centre-cut Siegel set. -/
theorem exists_uniform_cover (K : Type) [Field K] [NumberField K] :
    ∃ T : Finset (AdelicGL2 (𝓞 K) K), ∃ c : ℝ, 0 < c ∧ ∃ u : ℝ,
      ∀ d₁ d₂ d₁' d₂' : ℝ, 0 < d₂ → d₁ ≤ d₂ → 0 < d₂' → d₁' ≤ d₂' →
        CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ∧
          CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁' d₂') := by
  obtain ⟨T, c, hc, u, h⟩ :=
    exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  exact ⟨T, c, hc, u, fun d₁ d₂ d₁' d₂' h₂ hle h₂' hle' => ⟨h d₁ d₂ h₂ hle, h d₁' d₂' h₂' hle'⟩⟩

/-! ### Zone 2 — the cover set is inhabited at every valid window -/

/-- **Zone 2.** Reading `CoversModCentre` out at `g = 1`: the finite union is nonempty, so the cover is not
vacuous. (The row's existential `T` is a *covering* set, not merely a formal one.) -/
theorem cover_nonempty (K : Type) [Field K] [NumberField K] :
    ∃ T : Finset (AdelicGL2 (𝓞 K) K), ∃ c : ℝ, 0 < c ∧ ∃ u : ℝ,
      ∀ d₁ d₂ : ℝ, 0 < d₂ → d₁ ≤ d₂ →
        (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂).Nonempty := by
  obtain ⟨T, c, hc, u, h⟩ :=
    exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
  refine ⟨T, c, hc, u, fun d₁ d₂ h₂ hle => ?_⟩
  obtain ⟨γ, z, hmem⟩ := h d₁ d₂ h₂ hle 1
  exact ⟨_, hmem⟩

/-! ### Zone 3 — the cover transfers to any superset -/

/-- **Zone 3.** `CoversModCentre` is monotone, so the row's cover of a finite union is a cover of any set
containing it — the reading the `L²` estimates spend when they enlarge the window. -/
theorem coversModCentre_of_cover_subset {K : Type} [Field K] [NumberField K]
    {D D' : Set (AdelicGL2 (𝓞 K) K)} (hDD' : D ⊆ D') (h : CoversModCentre K D) :
    CoversModCentre K D' :=
  CoversModCentre.mono hDD' h

end AutomorphicFormSetAF84AConsumer
