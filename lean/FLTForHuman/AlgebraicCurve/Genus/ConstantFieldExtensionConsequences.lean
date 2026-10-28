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

Two further consequences of the same setting sit here, both read off the two engines
above: the **pole bound** (`exists_forall_mem_span_pow_mul_of_forall_ord_nonneg` and its
two helpers) says the pole-filtered part of `F` is spanned by the `x`-powers times one
`L`-space, using the `ell` growth and the one-step dimension count of
`Defs/AdelicIndex`; the **pole-sum form of the degree identity**
(`exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed`) writes the pole set as a finset
and its `-ord x` sum as the finrank, using `PrincipalDivisors/PoleDivisor` for the pole
divisor.

spec-pin: Theorems/Thm_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental.lean
spec-pin: Theorems/Thm_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental.lean
spec-pin: Theorems/Thm_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg.lean
spec-pin: Theorems/Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed.lean
-/
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Genus.DegreeIdentity
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.PoleDivisor
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

/-! ## The pole bound -/

/-- **Every `L`-space of a multiple of the pole divisor is finite-dimensional.**  Statement
from `Theorems/Thm_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg.lean`
(a helper of that `S_` file, public in the pin); proof after the pin's `S_` file: the curve
and finite-dimensionality of `L 0` come from the `ell` growth at `0`, and
`finiteDimensional_lSpace` gives the rest. -/
theorem fd_lSpace_nsmul_poleDivisor
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)) := by
  haveI : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hell0 : ell (0 : Divisor K F) = 1 :=
    (exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD).1
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) :=
    FiniteDimensional.of_finrank_eq_succ (n := 0) hell0
  exact fun M => finiteDimensional_lSpace (M • D)

/-- **The pole bound.**  Statement from
`Theorems/Thm_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg.lean`
(a helper of that `S_` file, public in the pin); proof after the pin's `S_` file: the
exponent is the supremum of `-ord h` over the pole divisor's support, and the case split
is on whether a place lies in that support. -/
theorem exists_mem_lSpace_nsmul_of_forall_ord_nonneg
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (h : F) (hh : ∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord h) :
    ∃ M : ℕ, h ∈ LSpace (M • D) := by
  rcases eq_or_ne h 0 with rfl | hh0
  · exact ⟨0, (LSpace _).zero_mem⟩
  refine ⟨D.support.sup (fun v => (-(v.ord h)).toNat), mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)⟩
  set M := D.support.sup (fun v => (-(v.ord h)).toNat) with hM
  simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul, neg_le]

  by_cases hv : v ∈ D.support
  · have hDv1 : (1:ℤ) ≤ D v := by
      have hne := Finsupp.mem_support_iff.mp hv
      have := hD v; omega
    have hMv : ((-(v.ord h)).toNat : ℤ) ≤ (M:ℤ) := by
      have h' := Finset.le_sup (f := fun w => (-(w.ord h)).toNat) hv
      exact_mod_cast h'
    calc -(v.ord h) ≤ ((-(v.ord h)).toNat : ℤ) := Int.self_le_toNat _
      _ ≤ (M:ℤ) := hMv
      _ = (M:ℤ) * 1 := (mul_one _).symm
      _ ≤ (M:ℤ) * D v := mul_le_mul_of_nonneg_left hDv1 (Nat.cast_nonneg M)
  · have hDv0 : D v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [hDv0, mul_zero]
    have hox : 0 ≤ v.ord x := by
      have := hD v; rw [hDv0] at this; omega
    exact neg_nonpos_of_nonneg (hh v hox)

/-- **The pole-bounded part is spanned by the `x`-powers times one `L`-space.**  Statement
from `Theorems/Thm_AlgebraicCurve_exists_forall_mem_span_pow_mul_of_forall_ord_nonneg.lean`;
proof after the pin's `S_` file: the `ell` growth gives `M₀` and `L(N • D)` for every `N`;
the one-step inclusion `lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq` and the
induction on `k` put every `L((M₁ + k) • D)` inside the span, and the pole bound puts `h`
in one of them. -/
theorem exists_forall_mem_span_pow_mul_of_forall_ord_nonneg
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ∃ M₁ : ℕ, ∀ h : F, (∀ v : Place K F, 0 ≤ v.ord x → 0 ≤ v.ord h) →
      h ∈ Submodule.span K {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} := by
  classical
  obtain ⟨_, M₀, hM₀1, hell⟩ :=
    exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental x hx D hD
  have hFD : ∀ M : ℕ, FiniteDimensional K ↥(LSpace (M • D)) :=
    fd_lSpace_nsmul_poleDivisor x hx D hD
  set M₁ := M₀ + 1
  refine ⟨M₁, fun h hh => ?_⟩
  set SP := Submodule.span K {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} with hSP

  have hD0 : (0 : Divisor K F) ≤ D := fun v => by rw [hD]; exact le_max_left _ _

  have hbase : (LSpace (M₁ • D) : Submodule K F) ≤ SP := fun y hy =>
    Submodule.subset_span ⟨0, y, hy, by rw [pow_zero, one_mul]⟩

  have hxSP : (SP.map (LinearMap.mulLeft K x) : Submodule K F) ≤ SP := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨j, y, hy, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨j+1, y, hy, ?_⟩
    rw [LinearMap.mulLeft_apply]; ring

  have hup : ∀ k, (LSpace ((M₁ + k) • D) : Submodule K F) ≤ SP := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ n ih =>
      have hdegD : (0:ℤ) ≤ Divisor.degree D := by
        simp only [Divisor.degree, Finsupp.liftAddHom_apply, AddMonoidHom.coe_mulRight,
          Finsupp.sum]
        exact Finset.sum_nonneg fun v _ => mul_nonneg (by simpa using hD0 v) (Nat.cast_nonneg _)
      have hstep := lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq
        x D hD hFD M₀ (Divisor.degree D).toNat (genusFF K F)
        (fun N hN => by rw [hell N hN, Int.toNat_of_nonneg hdegD])
        (M₁ + n) (by omega)
      refine hstep.trans (sup_le ih ?_)
      exact (Submodule.map_mono ih).trans hxSP

  have hall : ∀ m, (LSpace (m • D) : Submodule K F) ≤ SP := fun m => by
    refine (lSpace_mono ?_).trans (hup m)

    intro v
    have hDv : (0:ℤ) ≤ D v := by simpa using hD0 v
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
    have hmle : (m:ℤ) ≤ ((M₁+m:ℕ):ℤ) := by exact_mod_cast Nat.le_add_left m M₁
    exact mul_le_mul_of_nonneg_right hmle hDv

  obtain ⟨M, hMmem⟩ := exists_mem_lSpace_nsmul_of_forall_ord_nonneg x D hD h hh
  exact hall M hMmem

/-! ## The pole-set sum form of the degree identity -/

/-- **The pole set sums to the finrank.**  Statement from
`Theorems/Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed.lean`;
proof after the pin's `S_` file: the support of the pole divisor is the pole set, and
`Divisor.degree_eq_sum_support` against the degree identity turns the sum of `-ord x`
into the finrank. -/
theorem exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    ∃ S : Finset (Place k F), (∀ P, P ∈ S ↔ P.ord x < 0) ∧
      ∑ P ∈ S, (-P.ord x) = (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  classical
  haveI := hfin
  haveI : IsCurveOver k F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  obtain ⟨D, hD⟩ := exists_poleDivisor_of_transcendental x hx
  refine ⟨D.support, fun P => ?_, ?_⟩
  · rw [Finsupp.mem_support_iff, hD P]
    constructor
    · intro h; by_contra h'; exact h (max_eq_left (by omega))
    · intro h; rw [max_eq_right (by omega)]; omega
  · have hdeg := degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx D hD
    rw [Divisor.degree_eq_sum_support] at hdeg
    rw [← hdeg]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [IsCurveOver.deg_eq_one_of_isAlgClosed P, Nat.cast_one, mul_one, hD P]
    rw [Finsupp.mem_support_iff, hD P] at hP
    have : P.ord x < 0 := by by_contra h'; exact hP (max_eq_left (by omega))
    rw [max_eq_right (by omega)]

end AlgebraicCurve
