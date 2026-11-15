/-
  SET-AF80A consumer: the adelic-height Weyl mass, spent at `F = ℚ`.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/HeightWeylMass.lean` carries the pin's `solution`
  (`S_…:779–792`) as
  `AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow`:
  for a finite set `S₁` of finite places with nonempty open `U v`, and a nonempty open set `U₀` of
  infinite adeles, there are `m₀ > 0`, `m₁` with `m₀ ≤ (σ - 1/2) * ∫_{U₀ × ∏U} h_σ` and
  `(σ - 1/2) * ∫ h_σ ≤ m₁` eventually as `σ → 1/2⁺`, where `h_σ` is the `(σ + 1/2)`-power of the
  adelic height of the Weyl-unipotent transform `g ↦ w⁻¹ · u g`.

  **What is concrete here.** Everything the row leaves abstract:

  * `F = ℚ`, so `𝓞 ℚ` is `ℤ` and there is a single infinite place;
  * `S₁ = ∅`, `U = Set.univ` at every finite place, `U₀ = Set.univ`: the trivial covering;
  * the σ-algebra of `𝔸_ℚ` is the row's own `adeleBorel`, taken as a local instance so that
    `Measure (AdeleRing (𝓞 ℚ) ℚ)` and `adelicAddHaar (𝓞 ℚ) ℚ` live on the same space.

  **The readings.** The first three zones read the height identity `adelicHeight_wn` at the concrete
  point `x = 0` (the unipotent parameter `0`), and the last two read the headline:

  * Zone 1 — `wn ℚ 0 = (adelicWeyl (𝓞 ℚ) ℚ)⁻¹`: at `x = 0` the unipotent factor is `1`, so the
    mass point is the Weyl element itself.
  * Zone 2 — `adelicHeight_wn` at `x = 0`: every archimedean factor is `(1 + ‖0‖²)⁻¹ = 1` and every
    finite factor is `(max 1 ‖0‖²)⁻¹ = 1`, so the height of the Weyl element is `1`.
  * Zone 3 — the archimedean product of that identity, read on its own: at `F = ℚ` the product
    `∏ w, ((1 + ‖0‖²)⁻¹) ^ w.mult` is a product of ones.
  * Zone 4 — the headline at this data: the constants `m₀ > 0`, `m₁` and the eventual two-sided
    bound with the pin's `σ - 1/2` factor; then `m₀ > 0` and the lower half on its own.
  * Zone 5 — the lower bound read at an *explicit* shift: the eventual statement is consumed at a
    genuine `σ > 1/2`, so the factor `σ - 1/2` is a positive number.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF80AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.HeightWeylMass

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
  IsDedekindDomain.HeightOneSpectrum Topology Filter
open NumberField.AdelicHaar NumberField.AdelicHeight
open AutomorphicForm
open scoped NNReal ENNReal BigOperators

namespace AutomorphicFormSetAF80AConsumer

/-- The row's own `letI := adeleBorel (𝓞 ℚ) ℚ`, as a local instance: the σ-algebra of `𝔸_ℚ`. -/
local instance : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := adeleBorel (𝓞 ℚ) ℚ

/-! ### Zones 1–3 — the height identity `adelicHeight_wn` at the concrete point `x = 0` -/

/-- **Zone 1.** At unipotent parameter `x = 0` the mass point is the Weyl element itself. -/
theorem wn_zero : wn ℚ (0 : AdeleRing (𝓞 ℚ) ℚ) = (adelicWeyl (𝓞 ℚ) ℚ)⁻¹ := by
  rw [wn, unipotentGL2_zero, mul_one]

/-- **Zone 2.** `adelicHeight_wn` at `x = 0`: the Weyl element has height `1`. -/
theorem adelicHeight_wn_zero : adelicHeight ℚ (wn ℚ (0 : AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
  rw [adelicHeight_wn]
  have h1 : ∀ w : InfinitePlace ℚ, ((1 + ‖(0 : AdeleRing (𝓞 ℚ) ℚ).1 w‖ ^ 2)⁻¹) ^ w.mult = 1 := by
    intro w
    rw [zero_fst_apply, norm_zero]
    simp
  have h2 : ∀ v : HeightOneSpectrum (𝓞 ℚ), (max 1 ‖(0 : AdeleRing (𝓞 ℚ) ℚ).2 v‖ ^ 2)⁻¹ = 1 := by
    intro v
    rw [zero_snd_apply, norm_zero]
    norm_num
  rw [Finset.prod_eq_one fun w _ => h1 w, finprod_eq_one_of_forall_eq_one h2, mul_one]

/-- **Zone 3.** The archimedean product of the identity on its own: at `F = ℚ` every factor is the
`w.mult`-power of `(1 + ‖0‖²)⁻¹`, hence `1`. -/
theorem archHeight_factor_at_zero :
    (∏ w : InfinitePlace ℚ, ((1 + ‖(0 : AdeleRing (𝓞 ℚ) ℚ).1 w‖ ^ 2)⁻¹) ^ w.mult) = 1 := by
  refine Finset.prod_eq_one fun w _ => ?_
  rw [zero_fst_apply, norm_zero]
  simp

/-! ### Zone 4 — the headline at the trivial covering -/

/-- The mass the row *confines*: the `(σ + 1/2)`-power of the height of the Weyl-unipotent
transform, integrated over the trivial cylinder `U₀ × ∏_{v ∈ ∅} U v = ⊤`. -/
private abbrev massOn (σ : ℝ) : ℝ :=
  ∫ x in {x : AdeleRing (𝓞 ℚ) ℚ | x.1 ∈ (Set.univ : Set (InfiniteAdeleRing ℚ)) ∧
      ∀ v ∈ (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))), x.2 v ∈ (Set.univ : Set (v.adicCompletion ℚ))},
    adelicHeight ℚ ((adelicWeyl (𝓞 ℚ) ℚ)⁻¹ * unipotentGL2 x) ^ (σ + 1 / 2)
      ∂(adelicAddHaar (𝓞 ℚ) ℚ)

/-- The *total* mass the row's second half bounds. -/
private abbrev totalMass (σ : ℝ) : ℝ :=
  ∫ x, adelicHeight ℚ ((adelicWeyl (𝓞 ℚ) ℚ)⁻¹ * unipotentGL2 x) ^ (σ + 1 / 2)
    ∂(adelicAddHaar (𝓞 ℚ) ℚ)

/-- **Zone 4a.** The row at `F = ℚ`, `S₁ = ∅`, `U = U₀ = Set.univ`: the two constants and the
eventual two-sided bound with the pin's `σ - 1/2` factor. -/
theorem row :
    ∃ m₀ m₁ : ℝ, 0 < m₀ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
        m₀ ≤ (σ - 1 / 2) * massOn σ ∧ (σ - 1 / 2) * totalMass σ ≤ m₁ :=
  exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow ℚ ∅
    (fun _ => Set.univ) (fun _ _ => ⟨isOpen_univ, ⟨0, Set.mem_univ _⟩⟩) Set.univ
    ⟨isOpen_univ, ⟨0, Set.mem_univ _⟩⟩

/-- **Zone 4b.** The positive lower bound on its own: some `m₀ > 0` lies eventually below the
`(σ - 1/2)`-weighted confined mass. -/
theorem exists_pos_lower :
    ∃ m₀ : ℝ, 0 < m₀ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ), m₀ ≤ (σ - 1 / 2) * massOn σ := by
  obtain ⟨m₀, m₁, hm₀, h⟩ := row
  exact ⟨m₀, hm₀, h.mono fun σ hσ => hσ.1⟩

/-! ### Zone 5 — the lower bound at an explicit shift `σ > 1/2` -/

/-- **Zone 5.** The lower bound read at a concrete shift: the eventual statement of the row, which
is existential in `σ`, is instantiated at a genuine `σ` with `1/2 < σ`. -/
theorem lower_bound_at_shift :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∃ σ : ℝ, 1 / 2 < σ ∧ m₀ ≤ (σ - 1 / 2) * massOn σ := by
  obtain ⟨m₀, m₁, hm₀, h⟩ := row
  have h' : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ), 1 / 2 < σ ∧ m₀ ≤ (σ - 1 / 2) * massOn σ := by
    filter_upwards [self_mem_nhdsWithin, h] with σ hσ hb
    exact ⟨hσ, hb.1⟩
  obtain ⟨σ, hσ⟩ := h'.exists
  exact ⟨m₀, hm₀, σ, hσ.1, hσ.2⟩

/-- **Zone 5'.** Consequently the factor `σ - 1/2` at that shift is positive: the row's estimate is
a *genuine* lower bound on the mass, not the trivial one at the boundary point `1/2`. -/
theorem shift_factor_pos : ∃ σ : ℝ, 1 / 2 < σ ∧ 0 < σ - 1 / 2 := by
  obtain ⟨_, _, σ, hσ, _⟩ := lower_bound_at_shift
  exact ⟨σ, hσ, by linarith⟩

end AutomorphicFormSetAF80AConsumer
