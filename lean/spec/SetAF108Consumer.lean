import FLTForHuman.ModularCurve.ModularPolynomialFibreVelu
import FLTForHuman.ModularCurve.FunctionFieldGeneration.ModularPolynomialExistence
import FLTForHuman.TateCurve.SeriesIdentities

set_option autoImplicit false

noncomputable section

open Polynomial ModularCurve WeierstrassCurve TateCurve
open scoped NNReal

namespace SetAF108Consumer

/-! ## Zone 1 — the fibre polynomial's product form with the datum *eliminated* (order C)

Order C's row takes a `ModularPolynomialData ℓ` as a hypothesis: the fibre polynomial's `j`-value is the
product of the `ℓ + 1` Vélu quotients' `j`-invariants.  A consumer never wants the hypothesis — it wants
"the" fibre polynomial, which is a datum *chosen* by existence
(`ModularCurve.nonempty_modularPolynomialData`, `FunctionFieldGeneration/ModularPolynomialExistence.lean`,
a port row of the previous sets).  Composing the two removes the hypothesis from every call site: what
remains is the product formula for a datum that exists.

This is the cross-module composition of the set: order C's module (all of the `TDescent` engine and the
product formula) plus the existence row of the modular-polynomial generation module. -/

theorem exists_fibrePoly_j_eq_prod_veluQuotient_j
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    ∃ data : ModularPolynomialData ℓ,
      fibrePoly data.Φ W.j =
        ∏ i, (X - C (@WeierstrassCurve.j K _
          (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  obtain ⟨data⟩ := nonempty_modularPolynomialData ℓ
  exact ⟨data, data.fibrePoly_j_eq_prod_veluQuotient_j hℓ2 hℓK W hι Q hQ hQinj hΔ⟩

/-! ## Zone 2 — the normal forms are invariant under `u ↦ q ^ n * u` (orders E and H)

Order E's two normal forms write `pointX q u` (resp. `pointY q u`) as `xfun u` plus a `tsum`; order H's
`pointX_zpow_mul` / `pointY_zpow_mul` say the points are `q`-periodic in `u`.  Composed, they give the
normal form *at every `q`-translate of `u`* — the form in which the point-arithmetic layer consumes them
(it works with representatives of the `u`-coset modulo `q^ℤ`).  Two rows of two orders, one conclusion. -/

theorem pointX_normalForm_zpow_mul
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (n : ℤ) :
    pointX q (q ^ n * u) =
      ((xfun u + ∑' m : ℕ, (xfun (q ^ (m + 1) * u) + xfun (q ^ (m + 1) * u⁻¹) -
        2 * xfun (q ^ (m + 1))))) := by
  rw [pointX_zpow_mul hq0 n]
  exact pointX_normalForm hq0 hq hu0 hu

theorem pointY_normalForm_zpow_mul
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (n : ℤ) :
    pointY q (q ^ n * u) =
      ((yfun u + ∑' m : ℕ, (yfun (q ^ (m + 1) * u) - yfun (q ^ (m + 1) * u⁻¹) -
        xfun (q ^ (m + 1) * u⁻¹) + xfun (q ^ (m + 1))))) := by
  rw [pointY_zpow_mul hq0 n]
  exact pointY_normalForm hq0 hq hu0 hu

end SetAF108Consumer
