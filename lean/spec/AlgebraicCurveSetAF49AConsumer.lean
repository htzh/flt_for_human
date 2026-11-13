/-
  SET-AF49A consumer: the Kummer splitting step and the Gauss degree bound, read at the two sharpest
  non-degenerate instances.

  **The zone.** Two rows, hence two compositions, read off the two modules of the set:
  `FLTForHuman/AlgebraicCurve/RegularProlongationKummer.lean` and
  `FLTForHuman/AlgebraicCurve/RegularProlongationGaussDegree.lean`.

  Row A (`exists_prolongation_of_card_roots_eq`) splits a regular prolongation over `F` into `q`
  prolongations over the Kummer extension `F' = F(f^(1/q))`, with `q` distinct integer rings. Read at
  `q = 2` — the smallest prime, and the smallest family that is not a singleton — the conclusion's
  family is indexed by `Fin 2`, and its injectivity is *read*, not assumed: the consumer extracts the
  chosen family and turns the injectivity conjunct into the concrete inequality
  `(R' 0).integers ≠ (R' 1).integers`. The degree hypothesis `hdeg : finrank F F' = 2` is not
  typeable at `F' = F`, so it enters in hypothesis form, as does the splitting-field instance; the
  family itself is kept `private`, so the zone adds one concrete statement and no public carrier.

  Row A' (`minpoly_eq`) is the numerics behind that headline: over a splitting field of `X ^ 2 - C f`
  of degree `2`, every `α` with `α ^ 2 = algebraMap F F' f` has `minpoly F α = X ^ 2 - C f`. This is
  the irreducible-factor step at `q = 2`, discharged by the module's `irreducible_X_pow_sub_C`.

  Row B (`exists_monic_coeff_natDegree_le_of_forall_valuationSubring`) is the Gauss degree bound
  `natDegree (p.coeff j) ≤ (p.natDegree - j) * m`. Read at `m = 0` the right-hand side is `0`, so every
  coefficient of the certificate `p` is a *constant* polynomial: the consumer returns
  `∀ j, p.coeff j = C ((p.coeff j).coeff 0)` alongside the monic and annihilation conjuncts, with
  `h₁`-`h₃` as hypotheses. The substitution `m = 0` is recorded, not forced.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.AlgebraicCurve.RegularProlongationKummer
import FLTForHuman.AlgebraicCurve.RegularProlongationGaussDegree

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing Polynomial

namespace AlgebraicCurve.RegularProlongation

namespace AF49AConsumer

/-- The prolongation family of the Kummer headline at `q = 2`, kept `private`: the chosen `Fin 2`
family of prolongations of `F'` over `R`, over a splitting field of `X ^ 2 - C f` of degree `2`. -/
private noncomputable def kummerFamily
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (f : R.integers) (S : Finset Fbar)
    (hS : S.card = 2) (hSf : ∀ s ∈ S, s ^ 2 = R.residue f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ 2 - C (f : F))] (hdeg : Module.finrank F F' = 2) :
    Fin 2 → RegularProlongation A F' Fbar :=
  (exists_prolongation_of_card_roots_eq (q := 2) A R f S hS hSf F' hdeg).choose

/-- **Zone A.** The Kummer headline at `q = 2`: the family exists, its two integer rings are
distinct — the injectivity conjunct read at the two indices of `Fin 2` — and both prolong `R`. -/
theorem consumer_zoneA_kummer_two
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f : R.integers) (S : Finset Fbar) (hS : S.card = 2)
    (hSf : ∀ s ∈ S, s ^ 2 = R.residue f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ 2 - C (f : F))] (hdeg : Module.finrank F F' = 2) :
    ((kummerFamily R f S hS hSf F' hdeg 0).integers ≠
        (kummerFamily R f S hS hSf F' hdeg 1).integers) ∧
      (∀ i, (kummerFamily R f S hS hSf F' hdeg i).integers.comap (algebraMap F F')
        = R.integers) := by
  have hspec :=
    (exists_prolongation_of_card_roots_eq (q := 2) A R f S hS hSf F' hdeg).choose_spec
  refine ⟨?_, fun i => (hspec.2 i).1⟩
  intro heq
  exact absurd (hspec.1 heq) (by decide)

/-- **Zone A'.** The Kummer numerics at `q = 2`: in a splitting field of `X ^ 2 - C f` of degree
`2`, a square root `α` of `algebraMap F F' f` has minimal polynomial `X ^ 2 - C f`. -/
theorem consumer_zoneA'_minpoly_two
    {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
    {f : F} (hf0 : f ≠ 0) (hqF : (2 : F) ≠ 0)
    [IsSplittingField F F' (X ^ 2 - C f)] (hdeg : Module.finrank F F' = 2)
    {α : F'} (hα : α ^ 2 = algebraMap F F' f) :
    minpoly F α = X ^ 2 - C f :=
  KummerSplitting.minpoly_eq (q := 2) hf0 hqF F' hdeg hα

/-- **Zone B.** The Gauss degree bound at `m = 0`: the certificate is monic, annihilates `f` under the
chart evaluation at `x`, and each of its coefficients is a *constant* polynomial — the bound
`natDegree (p.coeff j) ≤ (p.natDegree - j) * 0` read at zero. -/
theorem consumer_zoneB_gauss_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (f : F)
    (h₁ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → (x : F) ∈ V → f ∈ V)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → (x : F) ∉ V →
      f * ((x : F) ^ 0)⁻¹ ∈ V)
    (h₃ : ∀ V : ValuationSubring F,
      (∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) → f ∈ V) :
    ∃ p : Polynomial (Polynomial A), p.Monic ∧
      (∀ j, (p.coeff j).natDegree = 0) ∧
      (∀ j, p.coeff j = Polynomial.C ((p.coeff j).coeff 0)) ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F)) f = 0 := by
  obtain ⟨p, hmon, hbound, hev⟩ :=
    exists_monic_coeff_natDegree_le_of_forall_valuationSubring A R x hx f 0 h₁ h₂ h₃
  have hconst : ∀ j, (p.coeff j).natDegree = 0 := fun j => Nat.le_zero.mp (by simpa using hbound j)
  exact ⟨p, hmon, hconst, fun j => Polynomial.eq_C_of_natDegree_eq_zero (hconst j), hev⟩

end AF49AConsumer

end AlgebraicCurve.RegularProlongation
