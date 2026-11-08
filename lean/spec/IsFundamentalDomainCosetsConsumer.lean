/-
  Consumer specification for `FLTForHuman.MeasureTheory.IsFundamentalDomainCosets` (SET-AF21).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the two headlines of the module above, so that the module fails to
  elaborate here if its statements drift. It is deliberately **not part of any library** (nothing
  globs `spec/`), so it can never break a verified build. Run it by hand:

      cd lean
      lake env lean spec/IsFundamentalDomainCosetsConsumer.lean 2>&1 | grep -c error

  ZONE
  ----
  * `[one-translate]` — the cheapest non-degenerate instantiation of the first headline:
    `Γ₂ = Γ₁` (`hle = le_rfl`), `ι = Unit`, `R ≡ 1`. The coset hypothesis is then free
    (`(1)⁻¹ * γ = γ ∈ Γ`, uniquely at `()`), and the conclusion reads back that the union of the
    single translate `((1 : Γ) : G)⁻¹ • 𝓕` is a `Γ`-fundamental domain again — which is `𝓕`
    itself, since `(1 : G)⁻¹ • 𝓕 = 𝓕`. The last example instantiates the `E`-valued half of the
    second headline at `E = ℝ` on the same data.
-/
import FLTForHuman.MeasureTheory.IsFundamentalDomainCosets

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Pointwise ENNReal

namespace IsFundamentalDomainCosetsConsumer

/-! ## Zone `[one-translate]` — `Γ₂ = Γ₁`, `ι = Unit`, `R ≡ 1` -/

/-- At `Γ₂ = Γ₁` and `R ≡ 1` the coset hypothesis is free: `(1 : Γ)⁻¹ * γ = γ` lies in `Γ`, and
`Unit` gives uniqueness for nothing. -/
theorem cosetHyp {G : Type*} [Group G] (Γ : Subgroup G) :
    ∀ γ : Γ, ∃! i : Unit, (((fun _ : Unit => (1 : Γ)) i)⁻¹ * γ : G) ∈ Γ := by
  intro γ
  refine ⟨(), ?_, fun j _ => Subsingleton.elim j ()⟩
  show (((1 : Γ)⁻¹ * γ : Γ) : G) ∈ Γ
  exact ((1 : Γ)⁻¹ * γ).2

section OneTranslate

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  [MeasurableSpace G] [MeasurableSMul G X] (μ : Measure X) [SMulInvariantMeasure G X μ]
  (Γ : Subgroup G) [Countable Γ] (𝓕 : Set X) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)

/-- The first headline at `Γ₂ = Γ₁`: the union over the single representative `1` is a
`Γ`-fundamental domain. -/
example : IsFundamentalDomain Γ (⋃ _i : Unit, ((1 : Γ) : G)⁻¹ • 𝓕) μ :=
  IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives μ Γ Γ le_rfl 𝓕 h𝓕
    (fun _ => 1) (cosetHyp Γ)

/-- … and since `(1 : G)⁻¹ • 𝓕 = 𝓕`, that union is the domain we started from: one translate
recovers `𝓕` itself. -/
example : IsFundamentalDomain Γ 𝓕 μ := by
  simpa [Set.iUnion_const] using
    IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives μ Γ Γ le_rfl 𝓕 h𝓕
      (fun _ => 1) (cosetHyp Γ)

/-- The `E`-valued half of the second headline at the same data and `E = ℝ` — integrability,
a.e. summability and `∫ = ∫ ∑'` over the one translate. -/
example (h : X → ℝ) (hh : AEStronglyMeasurable h μ)
    (hfin : ∫⁻ x in 𝓕, ∑' _i : Unit, ‖h (((1 : Γ) : G)⁻¹ • x)‖ₑ ∂μ < ∞) :
    IntegrableOn h (⋃ _i : Unit, ((1 : Γ) : G)⁻¹ • 𝓕) μ ∧
      (∀ᵐ x ∂μ.restrict 𝓕, Summable fun _i : Unit => ‖h (((1 : Γ) : G)⁻¹ • x)‖) ∧
      ∫ x in ⋃ _i : Unit, ((1 : Γ) : G)⁻¹ • 𝓕, h x ∂μ
        = ∫ x in 𝓕, ∑' _i : Unit, h (((1 : Γ) : G)⁻¹ • x) ∂μ :=
  (IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
    μ Γ Γ le_rfl 𝓕 h𝓕 (fun _ => 1) (cosetHyp Γ)).2 h hh hfin

end OneTranslate

end IsFundamentalDomainCosetsConsumer

end
