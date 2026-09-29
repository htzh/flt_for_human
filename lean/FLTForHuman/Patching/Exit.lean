/-
  The abstract patching exit: `R ≅ T` at a patching datum.

  `Algebra.PatchingDatum.bijective_and_free_of_surjective` — for a patching datum
  `P` over a discrete valuation ring `𝒪`, a compatible surjection `RtoT : R →ₐ[𝒪] T`
  of `𝒪`-algebras acting compatibly on the patched module `M` is bijective; `M` is
  free over both `R` and `T`; the annihilator of `M` over `R` is zero; and `T` is
  presented as a quotient of `𝒪[[X₁,…,X_r]]` by the ideal spanned by the `φ (Xᵢ)`
  of the level that `P` supplies.

  The statement is the pin's `Theorems/` wrapper verbatim
  (`Theorems/Thm_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean`,
  pinned `aa2d8b3`). The proof is the pin's four lines
  (`P2M/Sol/S_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean`), an
  assembly of already-ported lemmas:

  * `Algebra.PatchingDatum.nonempty_patchingLevel_bot` (SET 6,
    `FLTForHuman/Patching/PatchingConstruction.lean`) produces a patching level at
    the zero ideal;
  * `Algebra.PatchingLevel.free_and_ker_eq_span` (SET 4,
    `FLTForHuman/Patching/LevelDescent.lean`) extracts freeness, the vanishing
    annihilator, and the kernel identification from it;
  * `RingHom.bijective_of_surjective_of_smul_eq` and
    `Module.Free.of_surjective_of_smul_eq` (SET 4,
    `FLTForHuman/Algebra/FaithfulFreeness.lean`) turn the compatible surjection
    into a bijection and transport freeness;
  * the quotient presentation is the first isomorphism theorem for algebras,
    `Ideal.quotientEquivAlgOfEq` composed with
    `Ideal.quotientKerAlgEquivOfSurjective L.ψ_surjective`, followed by the
    `AlgEquiv` of the bijection.

  The mathematics is math/018 §5; the driver plan is studies/t-side-driver.md §1.
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import FLTForHuman.Patching.PatchingConstruction
import FLTForHuman.Patching.LevelDescent
import FLTForHuman.Algebra.FaithfulFreeness

set_option autoImplicit false

/-- **The abstract patching exit.** Stated verbatim from
`Theorems/Thm_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean`. -/
theorem Algebra.PatchingDatum.bijective_and_free_of_surjective
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    {ℓ r : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (P : Algebra.PatchingDatum 𝒪 ℓ r R M)
    {T : Type} [CommRing T] [Algebra 𝒪 T] [Module T M]
    (RtoT : R →ₐ[𝒪] T) (hsurj : Function.Surjective RtoT)
    (hcompat : ∀ (x : R) (m : M), RtoT x • m = x • m) :
    Function.Bijective RtoT ∧ Module.Free R M ∧ Module.Free T M ∧
      Module.annihilator R M = ⊥ ∧
      ∃ f : Fin r → MvPowerSeries (Fin r) 𝒪,
        Nonempty ((MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T) := by
  obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hℓ
  obtain ⟨hfree, hann, hker⟩ := L.free_and_ker_eq_span
  have hbij := (RtoT : R →+* T).bijective_of_surjective_of_smul_eq hcompat hsurj
  exact ⟨hbij, hfree, Module.Free.of_surjective_of_smul_eq (RtoT : R →+* T) hcompat hsurj, hann, _,
    ⟨((Ideal.quotientEquivAlgOfEq 𝒪 hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective L.ψ_surjective)).trans (AlgEquiv.ofBijective RtoT hbij)⟩⟩
