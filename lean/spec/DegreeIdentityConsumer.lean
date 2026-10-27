/-
  Cross-module wire test for the degree identity `deg (x)_∞ = [F : K(x)]`.

  The set is the degree identity and, beside it, the local different bounds that were
  split out of its module (`Genus/DegreeIdentity.lean` was 2,048 lines holding four
  subjects; it is now four modules, and this consumer binds all of them):

  * `AlgebraicCurve/Place/Approximation.lean` — weak approximation at finitely many
    places (`Place.exists_forall_ord_eq`);
  * `AlgebraicCurve/Genus/DegreeIdentity.lean` — the two Riemann–Roch counts
    (`Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord`,
    `Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord`) and their `le_antisymm`
    (`Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord`);
  * `AlgebraicCurve/Differential/Different.lean` — the different is effective
    (`Place.ord_sub_one_le_ordDiff_D_of_perfectField`);
  * `AlgebraicCurve/Place/OrbitCardinality.lean` — the Galois orbit/stabiliser dictionary
    (`Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois`);
  * `AlgebraicCurve/Genus/HurwitzBound.lean` — the two Hurwitz line bounds
    (`sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable`,
    `sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable`).

  A `spec/` probe, not a library module: it is outside every lake target and is run with
  `lake env lean`, so a green library build stays meaningful.  Deleting either module
  breaks it.

  Executed zones (each a real composition, no `#check`, no unfinished proof):

  * zone 1 — **the approximation at the orders of an indicator**: the element which is a
    uniformizer at one place of a finite set and a unit at all the others, which is what
    the upper bound consumes (`exists_ord_one_at_and_zero_elsewhere`);
  * zone 2 — **the identity applied at a hypothesis-form `IsCurveOver` package**, reading
    off both inequalities and the equality from the same hypotheses;
  * zone 3 — **the identity substituted into Riemann's inequality**: `ℓ(D) ≤ [F : K(x)] +
    ℓ(0)` for the pole divisor of `x`, composing the equality with the landed
    `AlgebraicCurve.ell_le_degree_add_ellZero` (`Genus/Index.lean`).

  Pin `anthropics/fermats-last-theorem@aa2d8b3`, the four `Theorems/Thm_AlgebraicCurve_*`
  wrappers the two modules carry.
-/
import FLTForHuman.AlgebraicCurve.Differential.Different
import FLTForHuman.AlgebraicCurve.Genus.DegreeIdentity
import FLTForHuman.AlgebraicCurve.Genus.HurwitzBound
import FLTForHuman.AlgebraicCurve.Place.Approximation
import FLTForHuman.AlgebraicCurve.Place.OrbitCardinality

set_option autoImplicit false

noncomputable section

open AlgebraicCurve
open scoped IntermediateField

namespace DegreeIdentityConsumer

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

omit [IsCurveOver K F] [FiniteDimensional K (LSpace (0 : Divisor K F))] in
/-- **Zone 1.** Weak approximation at the indicator of a place: an element which is a
uniformizer at `v` and a unit at every other place of `T`. -/
theorem exists_ord_one_at_and_zero_elsewhere {v : Place K F} (T : Finset (Place K F))
    (hv : v ∈ T) :
    ∃ t : F, t ≠ 0 ∧ v.ord t = 1 ∧ ∀ w ∈ T, w ≠ v → w.ord t = 0 := by
  classical
  obtain ⟨t, ht0, htord⟩ := Place.exists_forall_ord_eq T (fun w => if w = v then 1 else 0)
  exact ⟨t, ht0, by simpa using htord v hv, fun w hw hne => by simpa [hne] using htord w hw⟩

/-- **Zone 2.** The identity at a hypothesis-form curve package: both inequalities and the
equality, from the same hypotheses. -/
theorem degree_eq_and_inequalities
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) ≤ Divisor.degree D ∧
      Divisor.degree D ≤ (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) ∧
      Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) :=
  ⟨Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord x hx D hD,
    Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord x hx D hD,
    Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord x hx D hD⟩

/-- **Zone 3.** Riemann's inequality at the pole divisor of `x`, with the degree identity
substituted: `ℓ(D) ≤ [F : K(x)] + ℓ(0)`. -/
theorem ell_le_finrank_add_ellZero
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    (ell D : ℤ) ≤ (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ)
      + ell (0 : Divisor K F) := by
  have hDeff : ∀ v : Place K F, 0 ≤ D v := by
    intro v; rw [hD]; exact le_max_left 0 _
  have h := ell_le_degree_add_ellZero (K := K) (F := F) hDeff
  rwa [Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord x hx D hD] at h


/-- **Zone 4.** The three bounds split out of the degree-identity module, each applied:
the different is effective at a place, the order along a place is the orbit cardinality,
and the two Hurwitz line bounds. Deleting any of the three modules breaks this zone. -/
example {K F : Type*} [Field K] [Field F] [Algebra K F] [PerfectField K] {x : F}
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (v : Place K F) {f : F} (hD : KaehlerDifferential.D K F f ≠ 0) :
    v.ord f - 1 ≤ v.ordDiff (KaehlerDifferential.D K F f) :=
  Place.ord_sub_one_le_ordDiff_D_of_perfectField x v hD

example {K E M : Type*} [Field K] [IsAlgClosed K] [Field E] [Field M]
    [Algebra K E] [Algebra K M] [Algebra E M] [IsScalarTower K E M]
    [FiniteDimensional E M] [IsGalois E M]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (x : E) [FiniteDimensional (IntermediateField.adjoin K ({algebraMap E M x} : Set M)) M]
    (P : Place K M) (hx : (P.restrict E).ord x = 1)
    (a : ℕ) (ha : (p : ℤ) ^ a ∣ P.ord (algebraMap E M x)) :
    P.ord (algebraMap E M x) - 1 + ((p : ℤ) ^ a - 1) ≤
      P.ordDiff (KaehlerDifferential.D K M (algebraMap E M x)) :=
  Place.sub_one_add_pow_sub_one_le_ordDiff_D_of_isGalois p x P hx a ha

example (K : Type) [Field K] [IsAlgClosed K] {F M : Type} [Field F] [Field M]
    [Algebra K F] [Algebra K M]
    (x : F) (t : M) (j₀ : K) (ι : F →ₐ[K] M) (hι : ι x = t)
    (hfin : FiniteDimensional K⟮t⟯ M) (hgal : IsGalois K⟮t⟯ M)
    (hint : ∀ ψ : F →ₐ[K] M, ψ x = t → ψ.toRingHom.IsIntegral)
    (W₀ : Place K M) (hW₀ : 0 < W₀.ord (t - algebraMap K M j₀)) :
    (W₀.ord (t - algebraMap K M j₀) =
        Nat.card {σ : M ≃ₐ[K⟮t⟯] M //
          SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀}) ∧
    (∀ (ψ : F →ₐ[K] M) (hψ : ψ x = t),
        0 < (W₀.restrictAlong ψ (hint ψ hψ)).ord (x - algebraMap K F j₀)) ∧
    (∀ w : Place K F, 0 < w.ord (x - algebraMap K F j₀) →
        ∃ (ψ : F →ₐ[K] M) (hψ : ψ x = t), W₀.restrictAlong ψ (hint ψ hψ) = w) ∧
    (∀ (ψ ψ' : F →ₐ[K] M) (hψ : ψ x = t) (hψ' : ψ' x = t),
        W₀.restrictAlong ψ (hint ψ hψ) = W₀.restrictAlong ψ' (hint ψ' hψ') ↔
          ∃ σ : M ≃ₐ[K⟮t⟯] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W₀ = W₀ ∧
            ψ' = ((σ : M →ₐ[K⟮t⟯] M).restrictScalars K).comp ψ) ∧
    (∀ (ψ : F →ₐ[K] M) (hψ : ψ x = t),
        (W₀.restrictAlong ψ (hint ψ hψ)).ord (x - algebraMap K F j₀) =
          Nat.card {ψ' : {ψ' : F →ₐ[K] M // ψ' x = t} //
            W₀.restrictAlong ψ'.1 (hint ψ'.1 ψ'.2) = W₀.restrictAlong ψ (hint ψ hψ)}) :=
  Place.ord_restrictAlong_eq_natCard_algHom_of_isGalois K x t j₀ ι hι hfin hgal hint W₀ hW₀

example (k : Type) [Field k] [IsAlgClosed k] {F : Type} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T Tinf : Finset (Place k F)) (hT : ∀ P ∈ T, 0 ≤ P.ord x)
    (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) :=
  sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable k x hx hfin hsep T hT Tinf hTinf

example (k : Type) [Field k] [IsAlgClosed k] {F : Type} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (a : Place k F → k)
    (hT : ∀ P ∈ T, 0 < P.ord (x - algebraMap k F (a P)))
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, (P.ord (x - algebraMap k F (a P)) - 1) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) :=
  sum_ord_sub_one_le_two_mul_genusFF_of_isSeparable k x hx hfin hsep T a hT Tinf hTinf

end DegreeIdentityConsumer
