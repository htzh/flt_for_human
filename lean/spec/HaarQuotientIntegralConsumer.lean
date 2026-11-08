/-
  Cross-module wire test for the Haar-quotient integral calculus (`AF21C`).

  A `spec/` probe, not a library module. One executed zone: the two headlines of
  `FLTForHuman/MeasureTheory/HaarQuotient.lean` instantiated at a **one-point quotient** —
  `H = ⊤`, `Γ = ⊥`, `S = T = Set.univ` — so that `⊤` acts transitively on `G`
  (`MulAction.orbitRel.Quotient ⊤ G` is a point) and the trivial subgroup's fundamental
  domain is the whole space. Every zone is a real composition — no `#check` — so deleting the
  module (or leaving a hole in it) breaks this file.

  The instantiation is the degenerate case in which the pin's whole computation must
  collapse: the `Γ`-sum has one term and the `T`-integral covers all of `H`, so the two
  sides of each identity are both `∫⁻ g, f g ∂μ` resp. `∫ g, f g ∂μ`, read through the
  one-point quotient.
-/
import FLTForHuman.MeasureTheory.HaarQuotient

open MeasureTheory
open scoped ENNReal Pointwise

namespace HaarQuotientIntegralConsumer

/-- `Set.univ` is a fundamental domain for any one-element group: the covering is `1`, and
there is no pair of distinct elements to be a.e. disjoint about. -/
private theorem isFundamentalDomain_univ_of_subsingleton
    {α : Type*} [MeasurableSpace α] {Γ : Type*} [Group Γ] [MulAction Γ α] [Subsingleton Γ]
    (μ : Measure α) : IsFundamentalDomain Γ (Set.univ : Set α) μ where
  nullMeasurableSet := MeasurableSet.univ.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun _ => ⟨1, Set.mem_univ _⟩
  aedisjoint a b hab := (hab (Subsingleton.elim a b)).elim

/-- `⊥` is a one-element subgroup of `⊤`, so `Γ.subgroupOf H` is one-element here too — the
only instance the trivial-`Γ` instantiation of the headlines needs that mathlib does not
already have. -/
private theorem subsingleton_bot_subgroupOf_top {G : Type*} [Group G] :
    Subsingleton ↥((⊥ : Subgroup G).subgroupOf (⊤ : Subgroup G)) :=
  ⟨fun a b => Subtype.ext (Subtype.ext (by
    rw [Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp a.2),
      Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp b.2)]))⟩

/-! ### Zone — the `ℝ≥0∞` row at a one-point quotient -/

/-- The pin's `setLIntegral_eq_lintegral_setLIntegral_mul_out` at `H = ⊤`, `Γ = ⊥`,
`S = T = Set.univ`: both sides are the full `μ`-integral of the `Γ`-invariant `f`, read
through the one-point quotient. -/
theorem setLIntegral_eq_lintegral_setLIntegral_mul_out_of_top
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (μH : Measure (⊤ : Subgroup G)) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f)
    (hfΓ : ∀ γ ∈ (⊥ : Subgroup G), ∀ g : G, f (γ * g) = f g) :
    ∫⁻ g in (Set.univ : Set G), f g ∂μ =
      ∫⁻ q : MulAction.orbitRel.Quotient (⊤ : Subgroup G) G,
        (∫⁻ x in (Set.univ : Set (⊤ : Subgroup G)),
          f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ (⊤ : Subgroup G) μH) := by
  have := subsingleton_bot_subgroupOf_top (G := G)
  exact HaarQuotient.setLIntegral_eq_lintegral_setLIntegral_mul_out μ (⊤ : Subgroup G)
    isClosed_univ μH (⊥ : Subgroup G) bot_le f hf hfΓ (Set.univ : Set G)
    (isFundamentalDomain_univ_of_subsingleton μ) (Set.univ : Set (⊤ : Subgroup G))
    (isFundamentalDomain_univ_of_subsingleton μH)

/-! ### Zone — the `ℂ` row at a one-point quotient, with its three conclusions -/

/-- The pin's `integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out`
at `H = ⊤`, `Γ = ⊥`, `S = T = Set.univ`: the a.e. integrability of the inner integral, the
integrability of the quotient integral, and the identity of the two integrals. -/
theorem integrable_and_integral_eq_of_top
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (μH : Measure (⊤ : Subgroup G)) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℂ) (hf : Measurable f)
    (hfΓ : ∀ γ ∈ (⊥ : Subgroup G), ∀ g : G, f (γ * g) = f g)
    (hfin : ∫⁻ g in (Set.univ : Set G), ‖f g‖ₑ ∂μ < ∞) :
    (∀ᵐ q ∂(HaarQuotient.measure μ (⊤ : Subgroup G) μH),
        IntegrableOn (fun x : (⊤ : Subgroup G) => f ((x : G) * q.out))
          (Set.univ : Set (⊤ : Subgroup G)) μH) ∧
      Integrable (fun q : MulAction.orbitRel.Quotient (⊤ : Subgroup G) G =>
        ∫ x in (Set.univ : Set (⊤ : Subgroup G)), f ((x : G) * q.out) ∂μH)
        (HaarQuotient.measure μ (⊤ : Subgroup G) μH) ∧
      ∫ g in (Set.univ : Set G), f g ∂μ =
        ∫ q : MulAction.orbitRel.Quotient (⊤ : Subgroup G) G,
          (∫ x in (Set.univ : Set (⊤ : Subgroup G)),
            f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ (⊤ : Subgroup G) μH) := by
  have := subsingleton_bot_subgroupOf_top (G := G)
  exact HaarQuotient.integrable_setIntegral_mul_out_and_setIntegral_eq_integral_setIntegral_mul_out
    μ (⊤ : Subgroup G) isClosed_univ μH (⊥ : Subgroup G) bot_le f hf hfΓ (Set.univ : Set G)
    (isFundamentalDomain_univ_of_subsingleton μ) (Set.univ : Set (⊤ : Subgroup G))
    (isFundamentalDomain_univ_of_subsingleton μH) hfin

end HaarQuotientIntegralConsumer
