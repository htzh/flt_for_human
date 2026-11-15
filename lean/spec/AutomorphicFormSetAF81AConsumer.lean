/-
  SET-AF81A consumer: the Weyl intertwining integral's eventual lower bound, read at the row's data.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/WeylIntertwiningIntegralBound.lean` carries the
  pin's `solution` (`S_…:398–421`) as
  `AutomorphicForm.exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family`:
  for a continuous family `φ ·` of induced sections that are archimedean-`K`-finite, `K_f`-smooth,
  nonnegative and real on the maximal compact and nonzero there, there is `δ > 0` with
  `δ ≤ ((σ - 1/2) * W(σ)).re` eventually as `σ → 1/2⁺`, where
  `W(σ) = ∫ x, φ(σ)(w⁻¹ · u(x)) ∂μ` is the Weyl intertwining integral of `φ σ`.

  **What is concrete here.** The row is a statement about a family that no formula in this file can
  produce, so the readings are of three kinds: the row is *applied* to the data (zone 1), the
  statement it produces is *unpacked* at a genuine shift (zone 2), and the three engine inputs the
  family conditions feed are *instantiated* at the trivial data (zones 3–5):

  * Zone 1 — the headline at the data: `∃ δ > 0`, `δ ≤ ((σ - 1/2) * W(σ)).re` eventually.
  * Zone 2 — the same read at an *explicit* `σ > 1/2`: the factor `σ - 1/2` is positive, so the
    bound is a genuine lower bound on `W(σ).re`, not the trivial one at the boundary `1/2`.
  * Zone 3 — `exists_cylinder` at `F = ℚ`, `S₂ = ∅`, `ψ ≡ 1`, `δ₀ = 0`: the local conditions it
    produces are nonempty open (`U₀` and every `U v`).
  * Zone 4 — `mem_Cpt` at `k = 1`: the identity lies in `Cpt = adelicMaximalCompact ∩ K_f`, the
    compact set the witness argument runs on.
  * Zone 5 — `eventually_norm_sub_lt` at that compact set: `φ σ → φ(1/2)` uniformly on `Cpt` as
    `σ → 1/2`, which is what turns the cylinder bound into the two-sided one.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF81AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwiningIntegralBound

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

namespace AutomorphicFormSetAF81AConsumer

/-- The row's own `letI := adeleBorel (𝓞 F) F`, as a local instance: the σ-algebra of `𝔸_F`. -/
local instance (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F

/-- The row's own `let α := …`: the modulus character of `𝔸_Fˣ`, as a monoid hom to `ℝˣ`. -/
private abbrev alpha (F : Type) [Field F] [NumberField F] : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

/-! ### Zone 1 — the headline at the row's data -/

/-- **Zone 1.** The row, applied to the family's data: the real part of `(σ - 1/2) * W(σ)` is
eventually bounded below by a positive constant. -/
theorem row
    (F : Type) [Field F] [NumberField F]
    (hα : ∀ t, 0 < ((alpha F t : ℝˣ) : ℝ))
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 (alpha F) hα s) (etaSnd 1 (alpha F) hα s) (φ s))
    (hφK : ∀ s, IsArchKFinite F (φ s))
    (hφf : ∀ s, IsKfSmooth F (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    (hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
    (hpos : ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0)
    (hex : ∃ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
        φ (1 / 2) k ≠ 0) :
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
        δ ≤ (((σ : ℂ) - 1 / 2) *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re :=
  exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family
    F hα φ hφ hφK hφf hφjc hφhol hpos hex

/-! ### Zone 2 — the row read at a genuine shift `σ > 1/2` -/

/-- **Zone 2.** The eventual statement of zone 1 is instantiated at a genuine `σ > 1/2`, where the
factor `σ - 1/2` is positive: the row is a lower bound on `W(σ).re` itself, not the trivial one at
the boundary point `1/2`. -/
theorem row_at_shift
    (F : Type) [Field F] [NumberField F]
    (hα : ∀ t, 0 < ((alpha F t : ℝˣ) : ℝ))
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 (alpha F) hα s) (etaSnd 1 (alpha F) hα s) (φ s))
    (hφK : ∀ s, IsArchKFinite F (φ s))
    (hφf : ∀ s, IsKfSmooth F (φ s))
    (hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
    (hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
    (hpos : ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0)
    (hex : ∃ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
        φ (1 / 2) k ≠ 0) :
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∃ δ σ : ℝ, 0 < δ ∧ 1 / 2 < σ ∧ 0 < σ - 1 / 2 ∧
      δ ≤ (((σ : ℂ) - 1 / 2) *
        weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re := by
  obtain ⟨δ, hδ, hev⟩ := row F hα φ hφ hφK hφf hφjc hφhol hpos hex
  have h' : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
      1 / 2 < σ ∧ δ ≤ (((σ : ℂ) - 1 / 2) *
        weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re := by
    filter_upwards [self_mem_nhdsWithin, hev] with σ hσ hb
    exact ⟨hσ, hb⟩
  obtain ⟨σ, hσ, hb⟩ := h'.exists
  exact ⟨δ, σ, hδ, hσ, by linarith, hb⟩

/-! ### Zone 3 — `exists_cylinder` at the trivial data -/

/-- **Zone 3.** The cylinder lemma at `F = ℚ`, `S₂ = ∅`, `ψ ≡ 1`, `δ₀ = 0`: the local conditions it
produces for the places of `S₂` are (vacuously) open and nonempty, and the archimedean one `U₀` is
open and nonempty. -/
theorem cylinder_trivial :
    ∃ U₀ : Set (InfiniteAdeleRing ℚ), IsOpen U₀ ∧ U₀.Nonempty := by
  obtain ⟨U, U₀, -, hU₀, hne, -⟩ :=
    exists_cylinder ℚ ∅ (fun _ => (1 : ℝ)) continuous_const (fun _ _ _ _ => rfl) 0 0 le_rfl
      (by norm_num)
  exact ⟨U₀, hU₀, hne⟩

/-! ### Zones 4–5 — the compact set and the uniform convergence on it -/

/-- **Zone 4.** The identity lies in the compact set `Cpt = adelicMaximalCompact ∩ K_f`. -/
theorem one_mem_Cpt (F : Type) [Field F] [NumberField F] :
    (1 : AdelicGL2 (𝓞 F) F) ∈ Cpt F :=
  mem_Cpt F (map_one _) (by rw [map_one]; exact one_mem _)

/-- **Zone 5.** `eventually_norm_sub_lt` on that compact set: `φ σ → φ(1/2)` uniformly on `Cpt` as
`σ → 1/2`. -/
theorem eventually_uniform_on_Cpt
    (F : Type) [Field F] [NumberField F]
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ σ : ℝ in 𝓝 (1 / 2 : ℝ),
      ∀ k ∈ Cpt F, ‖φ (σ : ℂ) k - φ (1 / 2) k‖ < ε :=
  eventually_norm_sub_lt F φ hjc (isCompact_Cpt F) ε hε

end AutomorphicFormSetAF81AConsumer
