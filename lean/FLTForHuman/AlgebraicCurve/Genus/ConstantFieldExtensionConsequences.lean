/-
The `isAlgClosed`/transcendental consequences: the `ell(N·D)` growth and the degree
identity, after FLT's
`P2M/Sol/S_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental.lean` and
`P2M/Sol/S_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental.lean`
with their `Theorems/` wrappers.

Both rows are read off the same constant-field-extension setting as SET 6's
`Genus/ConstantFieldExtension.lean`: over an algebraically closed `K`, a transcendental
`x` with `[K⟮x⟯ : F]` finite gives `IsCurveOver K F` and `ConstantsAreBase K F`, and the
Stichtenoth genus bound is available.  The first row is the asymptotic
`ell(N • D) = N · deg D + 1 − g` for `D = (x)_∞`; the second is `deg (x)_∞ = [F : K⟮x⟯]`.

The home is a new module because neither `Genus/ConstantFieldExtension.lean` nor
`Genus/DegreeIdentity.lean` is above the other in the port's import order, and the second
row needs both (SET 7, §3).  The statements are the wrappers' and the proofs the pin's.

spec-pin: Theorems/Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental.lean
spec-pin: Theorems/Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental.lean
-/
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Genus.DegreeIdentity
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve

/-- **The `ell(N·D)` growth.**  Statement from
`Theorems/Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental.lean`;
proof after the pin's `S_` file: the constant-field-extension setting gives the curve and
the constants, the Stichtenoth genus bound gives `RiemannGenusReachedAt γ D₀`, and
`RiemannGenusReachedAt.eq_of_ge` turns the divisor inequality `n₀ • P ≤ N • D` into the
asymptotic. -/
theorem exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ell (0 : Divisor K F) = 1 ∧
    ∃ M : ℕ, 1 ≤ M ∧ ∀ N, M ≤ N →
      (ell (N • D) : ℤ) = N * Divisor.degree D + 1 - genusFF K F := by
  classical

  haveI hICO : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed_of_transcendental x hx
  haveI hEFT : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx inferInstance
  have hell0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one_of_constantsAreBase hC
  refine ⟨hell0, ?_⟩

  obtain ⟨hNon, hFD, γ, D₀, hRGA⟩ := stichtenothGenusExists_of_isCurveOver hC
  haveI : Nonempty (Place K F) := hNon
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := hFD

  have hidx0 : (indexOfSpecialty (0 : Divisor K F) : ℤ)
      = (ell (0 : Divisor K F) : ℤ) - (Divisor.degree (0 : Divisor K F) + 1 - γ) :=
    (indexOfSpecialty_eq_of_genusReached hRGA 0).2
  have hγ : γ = (genusFF K F : ℤ) := by
    have hgFF : indexOfSpecialty (0 : Divisor K F) = genusFF K F := by
      rw [indexOfSpecialty_eq_finrank_H1]; rfl
    have hdeg0 : Divisor.degree (0 : Divisor K F) = 0 := map_zero _
    rw [hgFF, hdeg0, hell0] at hidx0
    push_cast at hidx0
    linarith

  have hDnn : ∀ v, 0 ≤ D v := fun v ↦ by rw [hD v]; exact le_max_left 0 _
  have hDne : D ≠ 0 := by
    intro h0

    have hxmem : x ∈ LSpace (0 : Divisor K F) := by
      rw [mem_lSpace_iff_ord]
      right
      intro v
      have hDv0 : max 0 (-v.ord x) = 0 := by
        have := hD v; rw [h0] at this; exact this.symm
      have : -v.ord x ≤ 0 := max_eq_left_iff.mp hDv0
      simpa using neg_nonpos.mp this
    rw [hC] at hxmem
    obtain ⟨a, ha⟩ := hxmem
    exact hx (ha ▸ isAlgebraic_algebraMap a)

  obtain ⟨Q, hQ⟩ := Finsupp.support_nonempty_iff.mpr hDne
  have hDQ : 1 ≤ D Q := by
    have hne : D Q ≠ 0 := Finsupp.mem_support_iff.mp hQ
    have hnn := hDnn Q
    omega

  obtain ⟨n₀, hRGAQ⟩ :=
    exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists hRGA Q

  refine ⟨max 1 n₀, le_max_left _ _, fun N hN ↦ ?_⟩
  have hNn₀ : n₀ ≤ N := (le_max_right _ _).trans hN
  have hle : (n₀ : ℤ) • Finsupp.single Q (1 : ℤ) ≤ N • D := by
    intro v
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply,
      nsmul_eq_mul]
    split_ifs with h
    · subst h
      calc (n₀ : ℤ) * 1 = (n₀ : ℤ) := mul_one _
        _ ≤ (N : ℤ) := by exact_mod_cast hNn₀
        _ = (N : ℤ) * 1 := (mul_one _).symm
        _ ≤ (N : ℤ) * D Q := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hDQ) (Nat.cast_nonneg N)
    · calc (n₀ : ℤ) * 0 = 0 := mul_zero _
        _ ≤ (N : ℤ) * D v := mul_nonneg (Nat.cast_nonneg N) (hDnn v)
  have heq : Divisor.degree (N • D) - (ell (N • D) : ℤ) = γ - 1 :=
    hRGAQ.eq_of_ge hle
  have hdegNsmul : Divisor.degree (N • D) = (N : ℤ) * Divisor.degree D := by
    rw [AddMonoidHom.map_nsmul, nsmul_eq_mul]
  rw [hdegNsmul, hγ] at heq
  linarith

/-- **The degree identity.**  Statement from
`Theorems/Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental.lean`;
proof after the pin's `S_` file: derive the curve and the constants from the setting,
`ell 0 = 1` gives `LSpace 0` finite-dimensional, and
`Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord` is the degree identity. -/
theorem degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    Divisor.degree D = (Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F : ℤ) := by
  haveI : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hcab : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed_of_transcendental x hx
  have hℓ0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one_of_constantsAreBase hcab
  haveI : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    FiniteDimensional.of_finrank_eq_succ (n := 0) hℓ0
  exact Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord x hx D hD

end AlgebraicCurve
