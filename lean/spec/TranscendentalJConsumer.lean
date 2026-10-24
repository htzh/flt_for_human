/-
  Cross-module wire test for the modular-equation-at-transcendental-`j` set.

  The set is the three statements in
  `FLTForHuman/ModularCurve/ModularPolynomialVelu.lean` (the forward root, the product
  form, the root-membership converse) together with their supports:

  * `WeierstrassCurve/IsogenyEndDatum/TranscendentalRigidity.lean` — the diagonal
    leading coefficient and the transcendental rigidity;
  * `WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` — equal quotient `j`'s
    force equal cyclic subgroups (the transcendental variant);
  * `WeierstrassCurve/Velu/SubfieldMembership.lean` — `j` stays in any subfield
    containing the coefficients (and the Vélu summing set);
  * `WeierstrassCurve/Velu/CyclicSubgroupCount.lean` — `ψ(n)` cyclic subgroups.

  A `spec/` probe, not a library module: it is outside every lake target and is run
  with `lake env lean`, so a green library build stays meaningful.  Deleting any of
  the five modules breaks it.

  Executed zones (each a real composition, no `#check`, no unfinished proof):

  * zone 1 — **the product form read at its factors**: for an odd prime `ℓ` and an
    injective family of `ℓ + 1` order-`ℓ` points, each quotient's `j` is a root of
    the fibre `Φ_ℓ(j(W), Y)`.  This consumes the product headline and, through it,
    the forward root and the transcendental distinctness;
  * zone 2 — **the product form fed to the converse**: the root produced in zone 1
    is handed to `mem_of_isRoot_map_j_of_transcendental_of_odd`, so it lies in any
    subfield containing the coefficients and the `ℓ`-torsion coordinates.  This is
    the composition the theory exists for — the product face and the membership face
    on one object — and it runs through the membership and count modules;
  * zone 3 — **the count at a prime**: the number of cyclic order-`ℓ` subgroups is
    `ψ(ℓ) = ℓ + 1`, composing the count module with `ModularCurve.dedekindPsi_prime`.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`; the two faces are
  `Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental.lean`
  and `…_mem_of_isRoot_map_j_of_transcendental_of_odd.lean`.
-/
import FLTForHuman.ModularCurve.ModularPolynomialVelu

set_option autoImplicit false
set_option linter.unusedVariables false
-- Each `haveI` here registers a local instance for typeclass search (ellipticity of a
-- quotient, `NeZero`, `CharZero`), not a proof step.
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine Polynomial ModularCurve

local notation "𝕂" => HahnSeries ℚ (AlgebraicClosure ℚ)

namespace TranscendentalJConsumer

variable [DecidableEq 𝕂]

/-- The quotient `j` attached to a point family, with the instance the quotient's
ellipticity needs. -/
private def jQuot {ℓ : ℕ} (W : WeierstrassCurve 𝕂) (Q : W.toAffine.Point) (n : ℕ)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0) : 𝕂 :=
  haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  (W.veluQuotient (W.oddOrderSummingSet Q n)).j

/-- **Zone 1.** The product form, read at one of its own factors: `j(W/⟨Q i⟩)` is a
root of `Φ_ℓ(j(W), Y)`. -/
theorem product_root
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (data : ModularCurve.ModularPolynomialData ℓ)
    (W : WeierstrassCurve 𝕂) [W.IsElliptic] (ht : Transcendental ℚ W.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    ∀ i, (fibrePoly data.Φ W.j).IsRoot (jQuot (ℓ := ℓ) W (Q i) (ℓ / 2) (hΔ i)) := by
  intro i
  rw [ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental
    (hℓ2 := hℓ2) (data := data) (W := W) (ht := ht) (hι := hι) (Q := Q) (hQ := hQ)
    (hQinj := hQinj) (hΔ := hΔ)]
  rw [Polynomial.IsRoot, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [jQuot])

/-- **Zone 2.** The product face and the membership face composed: the root of zone 1
lies in any subfield containing the coefficients and the coordinates of every
`ℓ`-torsion point. -/
theorem product_root_mem
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (data : ModularCurve.ModularPolynomialData ℓ)
    (W : WeierstrassCurve 𝕂) [W.IsElliptic] (ht : Transcendental ℚ W.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0)
    (L : Subfield 𝕂)
    (h₁ : W.a₁ ∈ L) (h₂ : W.a₂ ∈ L) (h₃ : W.a₃ ∈ L) (h₄ : W.a₄ ∈ L) (h₆ : W.a₆ ∈ L)
    (htors : ∀ (x y : 𝕂) (h : W.toAffine.Nonsingular x y),
      ℓ • (Point.some x y h : W.toAffine.Point) = 0 → x ∈ L ∧ y ∈ L) :
    ∀ i, jQuot (ℓ := ℓ) W (Q i) (ℓ / 2) (hΔ i) ∈ L := by
  have hℓP : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓP.ne_zero⟩
  have hℓodd : Odd ℓ := hℓP.odd_of_ne_two hℓ2
  intro i
  exact ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd
    (N := ℓ) hℓodd data W ht L h₁ h₂ h₃ h₄ h₆ htors _
    (product_root hℓ2 data W ht hι Q hQ hQinj hΔ i)

/-- **Zone 3.** The count at a prime: the cyclic order-`ℓ` subgroups are `ψ(ℓ) = ℓ + 1`
of them. -/
theorem count_prime
    {ℓ : ℕ} (hℓ : ℓ.Prime)
    (W : WeierstrassCurve 𝕂) [W.IsElliptic] :
    Nat.card {G : AddSubgroup (W⁄𝕂).Point // IsAddCyclic G ∧ Nat.card G = ℓ} = ℓ + 1 := by
  haveI : CharZero 𝕂 :=
    charZero_of_injective_ringHom (HahnSeries.C_injective (R := AlgebraicClosure ℚ) (Γ := ℚ))
  haveI : IsAlgClosed 𝕂 := HahnSeries.isAlgClosed_rat
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
    (F := 𝕂) (K := 𝕂) W (Nat.cast_ne_zero.mpr hℓ.ne_zero),
    ModularCurve.dedekindPsi_prime hℓ]

end TranscendentalJConsumer
