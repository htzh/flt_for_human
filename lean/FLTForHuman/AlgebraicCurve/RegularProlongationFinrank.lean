/-
  The residue map of a regular prolongation preserves the `finrank` of a span of
  integers. Along a regular prolongation `R` of a valuation subring `A` of `L`
  into a field extension `F`, with residue field extension `Fbar`, the residue map
  carries an `L`-span of `R`-integers onto a `ResidueField A`-span of the same
  dimension:

      Module.finrank (ResidueField A) (span of residues) = Module.finrank L V.

  It is the dimension-transport step behind residue-degree and genus
  computations.

  The port of the pin node

      `AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank`

  (`Theorems/Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.lean`,
  23 pin lines; proof in `P2M/Sol/S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.lean`,
  787 pin lines — see
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.lean
  for the comparable copy). The proof is carried in the pin's own seven phases as
  sections: `resIndep` (the independence of the coefficient reduction), `adapted`
  (an adapted basis of a subspace for a family of functionals), `frame` (the
  monomial frame `x ^ j * y i` and its independence), `covering` (clearing
  denominators so that a unit multiple of a finite-dimensional `V` lies in the
  span of a finite piece of the frame), `core` (the independence of residues
  adapted to a subspace), and `assembly` (the two `finrank` bounds). The pin's
  inner wrapper namespaces `P2MW.S_…` and `AJDFXA` are dropped; the token `AJDFXA`
  is a collision token with no mathematical meaning. The pin's `solution` — the
  private assembly twin of the headline — stays `private`, so the checker diffs
  the twenty-eight pin-public declarations and the headline.

  Assumes: `FLTForHuman/AlgebraicCurve/RegularProlongation.lean` (the pin's
  `Definitions/Def_AlgebraicCurve_RegularProlongation.lean`), and mathlib `v4.34.0`.

  spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.lean   -- comparable copy

  The four nodes of the `AlgebraicCurve` shelf's RP2 row (SET 5) are appended below: the
  residue side of a regular prolongation. Its engine (`constHom`, `coe_constHom`,
  `residue_constHom`, `residue_eq_zero_iff`, and the whole `resIndep`/`frame`/`covering`
  block) is declared above and imported, not restated; the pin repeats `constHom`,
  `coe_constHom` and `residue_constHom` in three of the four files.

  spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_eq_integers_of_forall_mem_adjoin_iff.lean
  spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_mul_min_ord_residue_le_of_monic.lean
  spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_transcendental_of_residue_transcendental.lean
  spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero.lean

  Drift against `v4.34.0`: proof-only, the statements are the pin's verbatim. The
  two `AJDFXA`-level namespace and `p2m_*` staging commands are dropped and
  `residue_eq_zero_iff` loses the pin's `_root_.` escape (it is stated plainly and
  publicly); every other declaration keeps the pin's name and statement.

-/

import FLTForHuman.AlgebraicCurve.RegularProlongation
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.GCongr

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

namespace RegularProlongation

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

/-- The constants of `L` as integers: the image of `A` under `L → F`, whose elements
land in `R.integers` by `algebraMap_mem_iff`. -/
def constHom (R : RegularProlongation A F Fbar) : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem coe_constHom (R : RegularProlongation A F Fbar) (a : A) :
    ((constHom R a : R.integers) : F) = algebraMap L F a := rfl

/-- The residue of a constant is the residue field's own image of the constant. -/
theorem residue_constHom (R : RegularProlongation A F Fbar) (a : A) :
    R.residue (constHom R a) = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) :=
  R.residue_algebraMap a

/-- An integer has residue zero exactly when it lies in the maximal ideal. -/
theorem residue_eq_zero_iff (R : RegularProlongation A F Fbar) (f : R.integers) :
    R.residue f = 0 ↔ f ∈ maximalIdeal R.integers := by
  change f ∈ RingHom.ker R.residue ↔ _
  rw [R.ker_residue]

/-- Multiplying by a normalizing constant of `L`: some index of maximal valuation
exists, and its inverse times any other coefficient lies in `A`. -/
theorem exists_normalizer {ι : Type*} (t : Finset ι) (g : ι → L) {i₀ : ι} (hi₀ : i₀ ∈ t)
    (hg : g i₀ ≠ 0) :
    ∃ i₁ ∈ t, g i₁ ≠ 0 ∧ (∀ i ∈ t, (g i₁)⁻¹ * g i ∈ A) ∧
      (∀ i ∈ t, A.valuation (g i) ≤ A.valuation (g i₁)) := by
  obtain ⟨i₁, hi₁t, hmax⟩ := t.exists_max_image (fun i => A.valuation (g i)) ⟨i₀, hi₀⟩
  have hg₁ : g i₁ ≠ 0 := by
    intro h0
    have h := hmax i₀ hi₀
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at h
    exact hg h
  have hv₁ : A.valuation (g i₁) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  refine ⟨i₁, hi₁t, hg₁, fun i hi => ?_, hmax⟩
  rw [← A.valuation_le_one_iff, map_mul, map_inv₀]
  calc (A.valuation (g i₁))⁻¹ * A.valuation (g i)
      ≤ (A.valuation (g i₁))⁻¹ * A.valuation (g i₁) := by gcongr; exact hmax i hi
    _ = 1 := inv_mul_cancel₀ hv₁

section resIndep

variable (R : RegularProlongation A F Fbar) {ι : Type*} (E : ι → R.integers)

/-- The underlying element of a constant combination of integers. -/
theorem coe_sum_constHom_mul (t : Finset ι) (a : ι → A) :
    ((∑ i ∈ t, constHom R (a i) * E i : R.integers) : F) = ∑ i ∈ t, (a i : L) • (E i : F) := by
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_constHom, Algebra.smul_def]

/-- The residue of a constant combination of integers. -/
theorem residue_sum_constHom_mul (t : Finset ι) (a : ι → A) :
    R.residue (∑ i ∈ t, constHom R (a i) * E i) =
      ∑ i ∈ t, IsLocalRing.residue A (a i) • R.residue (E i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, residue_constHom, Algebra.smul_def]

variable (hE : LinearIndependent (ResidueField A) (fun i => R.residue (E i)))
include hE

/-- The coefficients of a constant combination with vanishing residue vanish in the
residue field. -/
theorem residue_coeff_eq_zero (t : Finset ι) (a : ι → A)
    (h : R.residue (∑ i ∈ t, constHom R (a i) * E i) = 0) :
    ∀ i ∈ t, IsLocalRing.residue A (a i) = 0 := by
  rw [residue_sum_constHom_mul] at h
  exact linearIndependent_iff'.mp hE t (fun i => IsLocalRing.residue A (a i)) h

/-- An integral linear combination of residues-independent integers has all its
coefficients integral. -/
theorem mem_of_sum_smul_mem (t : Finset ι) (g : ι → L)
    (h : ∑ i ∈ t, g i • (E i : F) ∈ R.integers) : ∀ i ∈ t, g i ∈ A := by
  classical
  by_contra hne
  obtain ⟨i₀, hi₀t, hgi₀⟩ := not_forall₂.mp hne
  have hg0 : g i₀ ≠ 0 := by
    rintro h0
    exact hgi₀ (h0 ▸ zero_mem A)
  obtain ⟨i₁, hi₁t, hg₁, hcA, hmax⟩ := exists_normalizer (A := A) t g hi₀t hg0
  set c : L := (g i₁)⁻¹ with hc

  have hv₀ : 1 < A.valuation (g i₀) := by
    rw [← not_le, A.valuation_le_one_iff]; exact hgi₀
  have hv₁ : 1 < A.valuation (g i₁) := lt_of_lt_of_le hv₀ (hmax i₀ hi₀t)
  have hcv : A.valuation c < 1 := by
    rw [hc, map_inv₀]
    exact inv_lt_one_of_one_lt₀ hv₁
  have hcmem : c ∈ A := (A.valuation_le_one_iff c).mp hcv.le
  have hcres : IsLocalRing.residue A ⟨c, hcmem⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact hcv

  let a : ι → A := fun i => if hi : i ∈ t then ⟨c * g i, hcA i hi⟩ else 0
  have ha : ∀ i ∈ t, (a i : L) = c * g i := fun i hi => by simp [a, dite_eq_left hi]
  set X : R.integers := ∑ i ∈ t, constHom R (a i) * E i with hX
  have hXeq : X = constHom R ⟨c, hcmem⟩ * ⟨∑ i ∈ t, g i • (E i : F), h⟩ := by
    apply Subtype.ext
    rw [hX, coe_sum_constHom_mul]
    change _ = algebraMap L F c * ∑ i ∈ t, g i • (E i : F)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ha i hi, mul_smul, Algebra.smul_def]
  have hres : R.residue X = 0 := by
    rw [hXeq, map_mul, residue_constHom, hcres, map_zero, zero_mul]
  have hall := residue_coeff_eq_zero R E hE t a hres i₁ hi₁t
  have ha1 : a i₁ = 1 := Subtype.ext (by rw [ha i₁ hi₁t, hc, inv_mul_cancel₀ hg₁]; rfl)
  rw [ha1, map_one] at hall
  exact one_ne_zero hall

/-- An integral linear combination whose residue vanishes has all its coefficients
of valuation `< 1`. -/
theorem valuation_lt_one_of_sum_smul_mem (t : Finset ι) (g : ι → L)
    (h : ∑ i ∈ t, g i • (E i : F) ∈ R.integers) (h0 : R.residue ⟨_, h⟩ = 0) :
    ∀ i ∈ t, A.valuation (g i) < 1 := by
  classical
  have hA := mem_of_sum_smul_mem R E hE t g h
  let a : ι → A := fun i => if hi : i ∈ t then ⟨g i, hA i hi⟩ else 0
  have ha : ∀ i ∈ t, (a i : L) = g i := fun i hi => by simp [a, dite_eq_left hi]
  set X : R.integers := ∑ i ∈ t, constHom R (a i) * E i with hX
  have hXeq : X = ⟨∑ i ∈ t, g i • (E i : F), h⟩ := by
    apply Subtype.ext
    rw [hX, coe_sum_constHom_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [ha i hi]
  have hres : R.residue X = 0 := by rw [hXeq]; exact h0
  intro i hi
  have hz := residue_coeff_eq_zero R E hE t a hres i hi
  rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at hz
  rwa [ha i hi] at hz

/-- The elements themselves are independent over `L`. -/
theorem linearIndependent_coe : LinearIndependent L (fun i => (E i : F)) := by
  rw [linearIndependent_iff']
  intro t g hsum i hi
  have hmem : ∑ i ∈ t, g i • (E i : F) ∈ R.integers := by rw [hsum]; exact zero_mem _
  have h0 : R.residue ⟨_, hmem⟩ = 0 := by
    have : (⟨_, hmem⟩ : R.integers) = 0 := Subtype.ext hsum
    rw [this, map_zero]
  by_contra hgi

  have hsum' : ∑ j ∈ t, ((g i)⁻¹ * g j) • (E j : F) = 0 := by
    simp_rw [mul_smul, ← Finset.smul_sum, hsum, smul_zero]
  have hmem' : ∑ j ∈ t, ((g i)⁻¹ * g j) • (E j : F) ∈ R.integers := by
    rw [hsum']; exact zero_mem _
  have h0' : R.residue ⟨_, hmem'⟩ = 0 := by
    have : (⟨_, hmem'⟩ : R.integers) = 0 := Subtype.ext hsum'
    rw [this, map_zero]
  have hlt := valuation_lt_one_of_sum_smul_mem R E hE t (fun j => (g i)⁻¹ * g j) hmem' h0' i hi
  simp only [inv_mul_cancel₀ hgi, map_one, lt_self_iff_false] at hlt

end resIndep

section adapted

variable (A)

/-- An adapted basis: for a finite-dimensional `W` separated by a finite family of
`A`-valued functionals `ℓ`, there is a basis `b` of `W` and an injective choice `c` of
functionals, integral on `b`, with `ℓ (c a) (b a') = δ a a'`. -/
theorem exists_adapted {V : Type*} [AddCommGroup V] [Module L V] {J : Type*} [Fintype J]
    (ℓ : J → V →ₗ[L] L) :
    ∀ (d : ℕ) (W : Submodule L V), (∀ v ∈ W, (∀ j, ℓ j v = 0) → v = 0) →
      Module.finrank L W = d →
      ∃ (b : Fin d → V) (c : Fin d → J), Function.Injective c ∧ (∀ a, b a ∈ W) ∧
        (∀ a j, ℓ j (b a) ∈ A) ∧ (∀ a a', ℓ (c a) (b a') = if a = a' then 1 else 0) := by
  classical
  intro d
  induction d with
  | zero =>
    intro W _ _
    exact ⟨Fin.elim0, Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a,
      fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩
  | succ d ih =>
    intro W hinj hW
    have : Module.Finite L W := Module.finite_of_finrank_eq_succ hW

    have hWne : W ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hW
      exact Nat.succ_ne_zero d hW.symm
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hex : ∃ j, ℓ j w ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw0 (hinj w hwW hall)
    obtain ⟨j₁, hj₁⟩ := hex
    obtain ⟨j₀, -, hj₀, hcA, -⟩ :=
      exists_normalizer (A := A) Finset.univ (fun j => ℓ j w) (Finset.mem_univ j₁) hj₁

    set w' : V := (ℓ j₀ w)⁻¹ • w with hw'
    have hw'W : w' ∈ W := W.smul_mem _ hwW
    have hw'A : ∀ j, ℓ j w' ∈ A := fun j => by
      rw [hw', map_smul, smul_eq_mul]
      exact hcA j (Finset.mem_univ j)
    have hw'1 : ℓ j₀ w' = 1 := by
      rw [hw', map_smul, smul_eq_mul, inv_mul_cancel₀ hj₀]

    let φ : W →ₗ[L] L := (ℓ j₀).domRestrict W
    have hφsurj : Function.Surjective φ := by
      intro c
      refine ⟨⟨c • w', W.smul_mem _ hw'W⟩, ?_⟩
      simp [φ, hw'1]
    have hrange : Module.finrank L (LinearMap.range φ) = 1 := by
      rw [LinearMap.range_eq_top.mpr hφsurj, finrank_top, Module.finrank_self]
    have hsum := LinearMap.finrank_range_add_finrank_ker φ
    have hker : Module.finrank L (LinearMap.ker φ) = d := by
      rw [hrange, hW] at hsum
      omega
    set W' : Submodule L V := (LinearMap.ker φ).map W.subtype with hW'def
    have hW' : Module.finrank L W' = d := by
      rw [hW'def, Submodule.finrank_map_subtype_eq, hker]
    have hmemW' : ∀ v, v ∈ W' ↔ v ∈ W ∧ ℓ j₀ v = 0 := by
      intro v
      rw [hW'def, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hvW, hv0⟩
        exact ⟨⟨v, hvW⟩, hv0, rfl⟩
    have hinj' : ∀ v ∈ W', (∀ j, ℓ j v = 0) → v = 0 := fun v hv hall =>
      hinj v ((hmemW' v).mp hv).1 hall
    obtain ⟨b', c', hc'inj, hb'W', hb'A, hδ'⟩ := ih W' hinj' hW'
    have hb'W : ∀ a, b' a ∈ W := fun a => ((hmemW' _).mp (hb'W' a)).1
    have hb'0 : ∀ a, ℓ j₀ (b' a) = 0 := fun a => ((hmemW' _).mp (hb'W' a)).2
    have hc'ne : ∀ a, c' a ≠ j₀ := by
      intro a h
      have h1 := hδ' a a
      rw [ite_eq_left rfl, h, hb'0] at h1
      exact zero_ne_one h1

    set b₀ : V := w' - ∑ a, ℓ (c' a) w' • b' a with hb₀
    have hb₀W : b₀ ∈ W :=
      W.sub_mem hw'W (W.sum_mem fun a _ => W.smul_mem _ (hb'W a))
    have hℓb₀ : ∀ j, ℓ j b₀ = ℓ j w' - ∑ a, ℓ (c' a) w' * ℓ j (b' a) := by
      intro j
      rw [hb₀, map_sub, map_sum]
      simp_rw [map_smul, smul_eq_mul]
    refine ⟨Fin.cons b₀ b', Fin.cons j₀ c', ?_, ?_, ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, hc'inj⟩
      rintro ⟨a, ha⟩
      exact hc'ne a ha
    · intro a
      refine Fin.cases ?_ (fun a => ?_) a
      · simpa using hb₀W
      · simpa using hb'W a
    · intro a j
      refine Fin.cases ?_ (fun a => ?_) a
      · simp only [Fin.cons_zero]
        rw [hℓb₀]
        exact A.sub_mem (hw'A j)
          (A.toSubring.sum_mem fun a _ => A.toSubring.mul_mem (hw'A (c' a)) (hb'A a j))
      · simp only [Fin.cons_succ]
        exact hb'A a j
    · intro a a'
      refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun a' => ?_) a'
      · simp only [Fin.cons_zero]
        rw [hℓb₀, hw'1]
        simp [hb'0]
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hb'0, ite_eq_right (Fin.succ_ne_zero a').symm]
      · simp only [Fin.cons_zero, Fin.cons_succ]
        rw [hℓb₀, ite_eq_right (Fin.succ_ne_zero a)]
        simp_rw [hδ' a, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq Finset.univ a, ite_eq_left (Finset.mem_univ a), sub_self]
      · simp only [Fin.cons_succ]
        rw [hδ' a a']
        by_cases h : a = a'
        · subst h; simp
        · rw [ite_eq_right h, ite_eq_right (fun h' => h (Fin.succ_inj.mp h'))]

end adapted

/-- Polynomial evaluation is the linear combination of the powers along the
coefficient function. -/
theorem aeval_eq_linearCombination {K B : Type*} [CommRing K] [Ring B] [Algebra K B]
    (x : B) (p : Polynomial K) :
    Polynomial.aeval x p = Finsupp.linearCombination K (fun j : ℕ => x ^ j) p.toFinsupp.coeff := by
  rcases p with ⟨q⟩
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Polynomial.support_ofFinsupp, Polynomial.coeff_ofFinsupp, Finsupp.linearCombination_apply,
    Finsupp.sum, Algebra.smul_def]

/-- The powers of `x` are independent exactly when `x` is transcendental. -/
theorem linearIndependent_pow_iff_transcendental {K B : Type*} [Field K] [Ring B] [Algebra K B]
    (x : B) : LinearIndependent K (fun j : ℕ => x ^ j) ↔ Transcendental K x := by
  rw [linearIndependent_iff, transcendental_iff]
  constructor
  · intro h p hp
    have := h p.toFinsupp.coeff (by rw [← aeval_eq_linearCombination]; exact hp)
    exact Polynomial.toFinsupp_eq_zero.mp (AddMonoidAlgebra.coeff_eq_zero.mp this)
  · intro h l hl
    have := h ⟨.ofCoeff l⟩ (by rw [aeval_eq_linearCombination]; exact hl)
    exact AddMonoidAlgebra.ofCoeff_eq_zero.mp (Polynomial.ofFinsupp_eq_zero.mp this)

section frame

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

/-- The monomial frame `x ^ j * y i` of the covering. -/
def frame (p : ℕ × Fin n) : R.integers := x ^ p.1 * y p.2

@[scoped simp] theorem coe_frame (p : ℕ × Fin n) :
    ((frame R x y p : R.integers) : F) = (x : F) ^ p.1 * (y p.2 : F) := by
  simp [frame]

include hx in

/-- The residues of the powers of a transcendental integer are independent. -/
theorem linearIndependent_residue_pow :
    LinearIndependent (ResidueField A) (fun j : ℕ => R.residue (x ^ j)) := by
  have : (fun j : ℕ => R.residue (x ^ j)) = fun j => (R.residue x) ^ j := by
    funext j; rw [map_pow]
  rw [this]
  exact (linearIndependent_pow_iff_transcendental _).mpr hx

include hx hy in

/-- The residues of the frame are independent over the residue field. -/
theorem linearIndependent_residue_frame :
    LinearIndependent (ResidueField A) (fun p : ℕ × Fin n => R.residue (frame R x y p)) := by
  set k := ResidueField A
  set xb := R.residue x
  have hgen : LinearIndependent k
      (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) := by
    apply LinearIndependent.of_comp
      ((IntermediateField.adjoin k ({xb} : Set Fbar)).val.toLinearMap)
    have : ((IntermediateField.adjoin k ({xb} : Set Fbar)).val.toLinearMap : _ → Fbar) ∘
        (fun j : ℕ => (IntermediateField.AdjoinSimple.gen k xb) ^ j) = fun j : ℕ => xb ^ j := by
      funext j
      simp
    rw [this]
    exact (linearIndependent_pow_iff_transcendental _).mpr hx
  have h := linearIndependent_smul hgen hy
  have hfun : (fun p : ℕ × Fin n => R.residue (frame R x y p)) =
      fun p : ℕ × Fin n => xb ^ p.1 * R.residue (y p.2) := by
    funext p
    simp [frame, map_mul, map_pow, xb]
  rw [hfun]
  convert h using 1
  funext p
  simp [Algebra.smul_def]

include hx hy in

/-- The frame's elements are independent over `L`. -/
theorem linearIndependent_coe_frame :
    LinearIndependent L (fun p : ℕ × Fin n => (x : F) ^ p.1 * (y p.2 : F)) := by
  have h := linearIndependent_coe R (frame R x y) (linearIndependent_residue_frame R x hx y hy)
  have hfun : (fun p : ℕ × Fin n => ((frame R x y p : R.integers) : F)) =
      fun p : ℕ × Fin n => (x : F) ^ p.1 * (y p.2 : F) := by
    funext p; exact coe_frame R x y p
  rwa [hfun] at h

include hx hy in

/-- The `y i` are independent over the polynomial algebra `L[x]`. -/
theorem linearIndependent_adjoin :
    LinearIndependent (Algebra.adjoin L ({(x : F)} : Set F)) (fun i : Fin n => (y i : F)) := by
  have h2 := linearIndependent_coe_frame R x hx y hy
  rw [linearIndependent_iff']
  intro t g hsum
  have hg : ∀ i, ∃ p : Polynomial L, Polynomial.aeval (x : F) p = (g i : F) := fun i => by
    have h : (g i : F) ∈ (Polynomial.aeval (R := L) (x : F)).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (g i).2
    exact (AlgHom.mem_range _).1 h
  choose p hp using hg
  set N := t.sup (fun i => (p i).natDegree) + 1 with hN
  have hlt : ∀ i ∈ t, (p i).natDegree < N := fun i hi =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun i => (p i).natDegree) hi)
  have hzero := linearIndependent_iff'.mp h2 (Finset.range N ×ˢ t)
    (fun q => (p q.2).coeff q.1) ?_
  · intro i hi
    have hpi : p i = 0 := by
      ext j
      by_cases hj : j < N
      · exact hzero (j, i) (Finset.mk_mem_product (Finset.mem_range.mpr hj) hi)
      · rw [Polynomial.coeff_zero]
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_lt_of_le (hlt i hi) (not_lt.mp hj))
    apply Subtype.ext
    rw [← hp i, hpi, map_zero]
    rfl
  · rw [Finset.sum_product_right, ← hsum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Subalgebra.smul_def, ← hp i, Polynomial.aeval_eq_sum_range' (hlt i hi),
      Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_eq_mul]
    exact (smul_mul_assoc _ _ _).symm

include hx hy in
open scoped IntermediateField.algebraAdjoinAdjoin in

/-- The same independence over the intermediate field `L(x)`. -/
theorem linearIndependent_adjoinField :
    LinearIndependent (IntermediateField.adjoin L ({(x : F)} : Set F))
      (fun i : Fin n => (y i : F)) :=
  (LinearIndependent.iff_fractionRing (Algebra.adjoin L ({(x : F)} : Set F))
    (IntermediateField.adjoin L ({(x : F)} : Set F))).mp (linearIndependent_adjoin R x hx y hy)

include hx hy in

/-- Every element of `F` is a linear combination of the `y i` over `L(x)`. -/
theorem exists_repr_adjoinField
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n) (f : F) :
    ∃ r : Fin n → IntermediateField.adjoin L ({(x : F)} : Set F),
      f = ∑ i, (r i : F) * (y i : F) := by
  set E := IntermediateField.adjoin L ({(x : F)} : Set F)
  let B : Module.Basis (Fin n) E F :=
    basisOfLinearIndependentOfCardEqFinrank' _ (linearIndependent_adjoinField R x hx y hy)
      (by rw [Fintype.card_fin, hcard])
  refine ⟨fun i => B.repr f i, ?_⟩
  conv_lhs => rw [← B.sum_repr f]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_basisOfLinearIndependentOfCardEqFinrank', IntermediateField.smul_def, smul_eq_mul]

end frame

section covering

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

include hx in

/-- A polynomial value can be normalized by a unit of the integers: after rescaling
the constant, the value is a unit times `q(x)`. -/
theorem exists_normalize_aeval (q : Polynomial L) (hq : q ≠ 0) :
    ∃ U : R.integers, R.residue U ≠ 0 ∧ ∃ c : L, c ≠ 0 ∧
      (U : F) = algebraMap L F c⁻¹ * Polynomial.aeval (x : F) q := by
  classical
  set t := Finset.range (q.natDegree + 1) with ht
  have hi₀ : q.natDegree ∈ t := Finset.self_mem_range_succ _
  have hg : q.coeff q.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hq
  obtain ⟨j₁, hj₁t, hj₁, hcA, -⟩ := exists_normalizer (A := A) t (fun j => q.coeff j) hi₀ hg
  let a : ℕ → A := fun j => if hj : j ∈ t then ⟨(q.coeff j₁)⁻¹ * q.coeff j, hcA j hj⟩ else 0
  refine ⟨∑ j ∈ t, constHom R (a j) * x ^ j, ?_, q.coeff j₁, hj₁, ?_⟩
  · intro h0
    have hE := linearIndependent_residue_pow R x hx
    have h1 := residue_coeff_eq_zero R (fun j : ℕ => x ^ j) hE t a h0 j₁ hj₁t
    have ha1 : a j₁ = 1 := by
      apply Subtype.ext
      simp [a, dite_eq_left hj₁t, inv_mul_cancel₀ hj₁]
    rw [ha1, map_one] at h1
    exact one_ne_zero h1
  · rw [coe_sum_constHom_mul, Polynomial.aeval_eq_sum_range, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ∈ t := hj
    rw [Algebra.smul_def, Algebra.smul_def]
    simp only [a, dite_eq_left hj', map_mul]
    push_cast
    ring

include hx hy in

/-- A unit multiple of a finite-dimensional subspace lies in the span of a finite
piece of the frame. -/
theorem exists_unit_mul_mem_span
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n)
    (V : Submodule L F) [FiniteDimensional L V] :
    ∃ U : R.integers, R.residue U ≠ 0 ∧ ∃ T : Finset (ℕ × Fin n),
      ∀ v ∈ V, (U : F) * v ∈
        Submodule.span L (Set.range fun p : T => (x : F) ^ p.1.1 * (y p.1.2 : F)) := by
  classical
  let bV := Module.finBasis L V

  choose r hr using
    fun a : Fin (Module.finrank L V) => exists_repr_adjoinField R x hx y hy hcard ((bV a : V) : F)

  have hfrac : ∀ a i, ∃ PQ : Polynomial L × Polynomial L, Polynomial.aeval (x : F) PQ.2 ≠ 0 ∧
      (r a i : F) = Polynomial.aeval (x : F) PQ.1 / Polynomial.aeval (x : F) PQ.2 := by
    intro a i
    obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff L (r a i : F)).mp (r a i).2
    by_cases hQ : Polynomial.aeval (x : F) Q = 0
    · refine ⟨(0, 1), by simp, ?_⟩
      rw [hPQ, hQ, div_zero]
      simp
    · exact ⟨(P, Q), hQ, hPQ⟩
  choose PQ hQne hPQ using hfrac

  set q : Polynomial L := ∏ p : Fin (Module.finrank L V) × Fin n, (PQ p.1 p.2).2 with hqdef
  have haevalq : Polynomial.aeval (x : F) q =
      ∏ p : Fin (Module.finrank L V) × Fin n, Polynomial.aeval (x : F) (PQ p.1 p.2).2 := by
    rw [hqdef, map_prod]
  have hqx : Polynomial.aeval (x : F) q ≠ 0 := by
    rw [haevalq]
    exact Finset.prod_ne_zero_iff.mpr fun p _ => hQne p.1 p.2
  have hq0 : q ≠ 0 := by
    rintro h
    rw [h, map_zero] at hqx
    exact hqx rfl
  obtain ⟨U, hU, c, hc, hUq⟩ := exists_normalize_aeval R x hx q hq0

  obtain ⟨H, hH⟩ : ∃ H : Fin (Module.finrank L V) → Fin n → Polynomial L,
      ∀ a i, (U : F) * ((r a i : F) * (y i : F)) =
        Polynomial.aeval (x : F) (H a i) * (y i : F) := by
    refine ⟨fun a i => Polynomial.C c⁻¹ *
      ((∏ p ∈ Finset.univ.erase (a, i), (PQ p.1 p.2).2) * (PQ a i).1), fun a i => ?_⟩
    rw [hUq, hPQ a i, ← mul_assoc]
    congr 1
    simp only [map_mul, Polynomial.aeval_C, map_prod]
    rw [haevalq, ← Finset.mul_prod_erase Finset.univ
      (fun p : Fin (Module.finrank L V) × Fin n => Polynomial.aeval (x : F) (PQ p.1 p.2).2)
      (Finset.mem_univ (a, i))]
    have hQ := hQne a i
    field_simp
  have hN : ∃ N : ℕ, ∀ a i, (H a i).natDegree < N := by
    let g : Fin (Module.finrank L V) × Fin n → ℕ := fun p => (H p.1 p.2).natDegree
    refine ⟨Finset.univ.sup g + 1, fun a i => Nat.lt_succ_of_le ?_⟩
    exact Finset.le_sup (f := g) (Finset.mem_univ (a, i))
  obtain ⟨N, hlt⟩ := hN
  refine ⟨U, hU, Finset.range N ×ˢ Finset.univ, ?_⟩
  let S : Submodule L F := Submodule.span L
    (Set.range fun p : ↥(Finset.range N ×ˢ (Finset.univ : Finset (Fin n))) =>
      (x : F) ^ p.1.1 * (y p.1.2 : F))
  change ∀ v ∈ V, (U : F) * v ∈ S
  have hgen : ∀ j < N, ∀ i, (x : F) ^ j * (y i : F) ∈ S := by
    intro j hj i
    apply Submodule.subset_span
    exact ⟨⟨(j, i), Finset.mk_mem_product (Finset.mem_range.mpr hj) (Finset.mem_univ i)⟩, rfl⟩
  have hbasis : ∀ a, (U : F) * ((bV a : V) : F) ∈ S := by
    intro a
    rw [hr a, Finset.mul_sum]
    refine S.sum_mem fun i _ => ?_
    rw [hH a i, Polynomial.aeval_eq_sum_range' (hlt a i), Finset.sum_mul]
    refine S.sum_mem fun j hj => ?_
    rw [smul_mul_assoc]
    exact S.smul_mem _ (hgen j (Finset.mem_range.mp hj) i)
  intro v hv
  have hvsum : v = ∑ a, bV.repr ⟨v, hv⟩ a • ((bV a : V) : F) := by
    have h := congrArg (fun w : V => (w : F)) (bV.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  rw [hvsum, Finset.mul_sum]
  refine S.sum_mem fun a _ => ?_
  rw [mul_smul_comm]
  exact S.smul_mem _ (hbasis a)

end covering

section core

variable (R : RegularProlongation A F Fbar) {ι : Type*} [Fintype ι] (E : ι → R.integers)
  (hE : LinearIndependent (ResidueField A) (fun i => R.residue (E i)))

include hE in

/-- Inside the span of the `E i` there is a residue-independent family of integers
covering a subspace of dimension `d`. -/
theorem exists_residue_linearIndependent (W : Submodule L F)
    (hW : W ≤ Submodule.span L (Set.range fun i => (E i : F))) {d : ℕ}
    (hd : Module.finrank L W = d) :
    ∃ f : Fin d → R.integers, (∀ a, (f a : F) ∈ W) ∧
      LinearIndependent (ResidueField A) (fun a => R.residue (f a)) := by
  classical
  have hli := linearIndependent_coe R E hE

  let ℓ : ι → Submodule.span L (Set.range fun i => (E i : F)) →ₗ[L] L :=
    fun i => (Finsupp.lapply i).comp hli.repr
  have hexp : ∀ s : Submodule.span L (Set.range fun i => (E i : F)),
      (s : F) = ∑ i, ℓ i s • (E i : F) := by
    intro s
    have h := hli.linearCombination_repr s
    rw [Finsupp.linearCombination_apply] at h
    rw [Finsupp.sum_fintype _ _ (fun i => zero_smul L (E i : F))] at h
    exact h.symm

  let W₀ : Submodule L (Submodule.span L (Set.range fun i => (E i : F))) :=
    W.comap (Submodule.span L (Set.range fun i => (E i : F))).subtype
  have hW₀ : Module.finrank L W₀ = d := by
    rw [← hd]
    exact (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hinj : ∀ v ∈ W₀, (∀ i, ℓ i v = 0) → v = 0 := by
    intro v _ hv
    apply Subtype.ext
    rw [hexp v]
    simp [hv]
  obtain ⟨b, c, hcinj, hbW, hbA, hδ⟩ := exists_adapted A ℓ d W₀ hinj hW₀

  have hcoe : ∀ a, ((b a : _) : F) =
      ((∑ i, constHom R ⟨ℓ i (b a), hbA a i⟩ * E i : R.integers) : F) := by
    intro a
    rw [coe_sum_constHom_mul, hexp (b a)]
  have hbO : ∀ a, ((b a : _) : F) ∈ R.integers := fun a => by
    rw [hcoe a]
    exact Subtype.mem _
  refine ⟨fun a => ⟨(b a : F), hbO a⟩, fun a => hbW a, ?_⟩

  rw [Fintype.linearIndependent_iff]
  intro κ hκ a₀
  have hsurjres : Function.Surjective (IsLocalRing.residue A) := Ideal.Quotient.mk_surjective
  choose α hα using fun a => hsurjres (κ a)
  let sβ : Submodule.span L (Set.range fun i => (E i : F)) := ∑ a, (α a : L) • b a
  have hGeq : ∑ i, ℓ i sβ • (E i : F) =
      ((∑ a, constHom R (α a) * ⟨(b a : F), hbO a⟩ : R.integers) : F) := by
    rw [← hexp sβ, coe_sum_constHom_mul]
    simp [sβ]
  have hGmem : ∑ i, ℓ i sβ • (E i : F) ∈ R.integers := by
    rw [hGeq]
    exact Subtype.mem _
  have hG0 : R.residue ⟨_, hGmem⟩ = 0 := by
    have : (⟨_, hGmem⟩ : R.integers) = ∑ a, constHom R (α a) * ⟨(b a : F), hbO a⟩ :=
      Subtype.ext (hGeq)
    rw [this, residue_sum_constHom_mul]
    simp_rw [hα]
    exact hκ
  have hlt := valuation_lt_one_of_sum_smul_mem R E hE Finset.univ (fun i => ℓ i sβ) hGmem hG0
    (c a₀) (Finset.mem_univ _)
  have hcoord : ℓ (c a₀) sβ = α a₀ := by
    simp only [sβ, map_sum, map_smul, smul_eq_mul, hδ, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ a₀, ite_eq_left (Finset.mem_univ a₀)]
  simp only [hcoord] at hlt
  rw [← hα a₀]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr
    ((ValuationSubring.valuation_lt_one_iff A _).mpr hlt)

end core

section assembly

variable (R : RegularProlongation A F Fbar)

/-- A residue-independent family of integers in `V` has cardinal at most the
dimension of `V`. -/
theorem card_le_finrank (V : Submodule L F) [FiniteDimensional L V] {ι : Type*} [Fintype ι]
    (f : ι → R.integers) (hfV : ∀ i, (f i : F) ∈ V)
    (hind : LinearIndependent (ResidueField A) (fun i => R.residue (f i))) :
    Fintype.card ι ≤ Module.finrank L V := by
  have hli := linearIndependent_coe R f hind
  have hli' : LinearIndependent L (fun i => (⟨(f i : F), hfV i⟩ : V)) :=
    LinearIndependent.of_comp V.subtype hli
  exact hli'.fintype_card_le_finrank

/-- A residue of the span is the residue of an integer of `V`. -/
theorem mem_of_mem_span (V : Submodule L F) {h : Fbar}
    (hh : h ∈ Submodule.span (ResidueField A)
      {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) :
    ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h := by
  induction hh using Submodule.span_induction with
  | mem h hh => exact hh
  | zero => exact ⟨0, by simp, map_zero _⟩
  | add h₁ h₂ _ _ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁, rfl⟩ := ih₁
    obtain ⟨f₂, hf₂, rfl⟩ := ih₂
    exact ⟨f₁ + f₂, by simpa using V.add_mem hf₁ hf₂, map_add _ _ _⟩
  | smul κ h _ ih =>
    obtain ⟨f, hf, rfl⟩ := ih
    obtain ⟨α, hα⟩ := Ideal.Quotient.mk_surjective (I := maximalIdeal A) κ
    refine ⟨constHom R α * f, ?_, ?_⟩
    · have : ((constHom R α * f : R.integers) : F) = (α : L) • (f : F) := by
        simp [Algebra.smul_def]
      rw [this]
      exact V.smul_mem _ hf
    · have hα' : IsLocalRing.residue A α = κ := hα
      rw [map_mul, residue_constHom, hα', Algebra.smul_def]

/-- The residue map preserves the dimension of a span of integers. -/
theorem finrank_span_residue_eq_finrank' (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (ResidueField A)
        (Submodule.span (ResidueField A)
          {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) =
      Module.finrank L V := by
  classical
  have : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  have : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)

  let yb := Module.finBasis
    (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar
  choose y hy using fun i => R.residue_surjective (yb i)
  have hyind : LinearIndependent
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
      (fun i => R.residue (y i)) := by
    have : (fun i => R.residue (y i)) = yb := funext hy
    rw [this]
    exact yb.linearIndependent

  have hrank : Module.rank (ResidueField A)
      (Submodule.span (ResidueField A)
        {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) ≤ Module.finrank L V := by
    apply rank_le
    intro s hs
    have hmem := fun i : s => mem_of_mem_span R V (i : Submodule.span (ResidueField A) _).2
    choose f hfV hfres using hmem
    have hind : LinearIndependent (ResidueField A) (fun i : s => R.residue (f i)) := by
      have : (fun i : s => R.residue (f i)) =
          (Submodule.span (ResidueField A)
            {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}).subtype ∘
            (fun i : s => (i : Submodule.span (ResidueField A) _)) := by
        funext i
        simp [hfres]
      rw [this]
      exact hs.map' _ (Submodule.ker_subtype _)
    have h := card_le_finrank R V f hfV hind
    simpa using h
  have hfinS : Module.Finite (ResidueField A)
      (Submodule.span (ResidueField A)
        {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) := by
    rw [← Module.rank_lt_aleph0_iff]
    exact lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0)
  apply le_antisymm (Module.finrank_le_of_rank_le hrank)

  obtain ⟨U, hU, T, hT⟩ := exists_unit_mul_mem_span R x hx y hyind hdeg V
  have hUne : (U : F) ≠ 0 := by
    intro h
    apply hU
    rw [show U = 0 from Subtype.ext h, map_zero]
  let μ : F →ₗ[L] F := LinearMap.mulLeft L (U : F)
  have hμinj : Function.Injective μ := mul_right_injective₀ hUne
  have hWfin : Module.finrank L (V.map μ) = Module.finrank L V :=
    (Submodule.equivMapOfInjective μ hμinj V).finrank_eq.symm
  let ET : T → R.integers := fun p => frame R x y p.1
  have hET : LinearIndependent (ResidueField A) (fun p : T => R.residue (ET p)) :=
    (linearIndependent_residue_frame R x hx y hyind).comp _ Subtype.val_injective
  have hWle : V.map μ ≤ Submodule.span L (Set.range fun p : T => (ET p : F)) := by
    have hrange : (Set.range fun p : T => (ET p : F)) =
        Set.range fun p : T => (x : F) ^ p.1.1 * (y p.1.2 : F) := by
      congr 1
    rw [hrange]
    rintro _ ⟨v, hv, rfl⟩
    exact hT v hv
  obtain ⟨g, hgW, hgind⟩ := exists_residue_linearIndependent R ET hET (V.map μ) hWle hWfin

  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hU
  have hg'V : ∀ a, ((↑u⁻¹ * g a : R.integers) : F) ∈ V := by
    intro a
    obtain ⟨v, hv, hgv⟩ := hgW a
    have h1 : ((↑u⁻¹ * g a : R.integers) : F) = v := by
      have huinv : ((↑u⁻¹ : R.integers) : F) * (U : F) = 1 := by
        rw [← hu, ← Subring.coe_mul, Units.inv_mul]
        rfl
      rw [Subring.coe_mul, ← hgv]
      change ((↑u⁻¹ : R.integers) : F) * ((U : F) * v) = v
      rw [← mul_assoc, huinv, one_mul]
    rw [h1]
    exact hv
  have hg'ind : LinearIndependent (ResidueField A) (fun a => R.residue (↑u⁻¹ * g a)) := by
    have hru : R.residue ↑u⁻¹ ≠ 0 := R.residue_ne_zero_of_isUnit (Units.isUnit _)
    rw [Fintype.linearIndependent_iff] at hgind ⊢
    intro κ hκ
    apply hgind κ
    have : ∑ a, κ a • R.residue (↑u⁻¹ * g a) = R.residue ↑u⁻¹ * ∑ a, κ a • R.residue (g a) := by
      simp only [map_mul, Finset.mul_sum, mul_smul_comm]
    rw [this] at hκ
    exact (mul_eq_zero.mp hκ).resolve_left hru
  have hmemS : ∀ a, R.residue (↑u⁻¹ * g a) ∈ Submodule.span (ResidueField A)
      {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h} :=
    fun a => Submodule.subset_span ⟨_, hg'V a, rfl⟩
  have hind2 : LinearIndependent (ResidueField A)
      (fun a => (⟨R.residue (↑u⁻¹ * g a), hmemS a⟩ : Submodule.span (ResidueField A)
        {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h})) :=
    LinearIndependent.of_comp (Submodule.span (ResidueField A) _).subtype hg'ind
  have h := hind2.fintype_card_le_finrank
  simpa using h

end assembly

/-- The pin's private assembly twin of the headline: the primed working form at the
headline's own binders. -/
private theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) =
      Module.finrank L V :=
  finrank_span_residue_eq_finrank' R x hx hfin hdeg V

/-- Along a regular prolongation the residue map carries an `L`-span of integers
onto a `ResidueField A`-span of the same dimension: the residue preserves
`finrank`. -/
theorem finrank_span_residue_eq_finrank
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) =
      Module.finrank L V :=
  solution A R x hx hfin hdeg V

end RegularProlongation

/-! ## RP2 — the residue field of a regular prolongation -/

namespace RegularProlongation

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

/-! ### A transcendental residue -/

/-- An integer whose residue is transcendental over the residue field is transcendental
over `L`. -/
theorem transcendental_of_residue_transcendental
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x)) :
    Transcendental L (x : F) := by
  intro halg
  obtain ⟨q, hq0, hqx⟩ := halg
  have hsupp : q.support.Nonempty := Polynomial.support_nonempty.mpr hq0
  apply hx
  obtain ⟨j₀, hj₀, hj₀max⟩ := Finset.exists_max_image q.support
    (fun j => A.valuation (q.coeff j)) hsupp
  have hcj₀ : q.coeff j₀ ≠ 0 := Polynomial.mem_support_iff.mp hj₀
  set c : L := (q.coeff j₀)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hcj₀
  have hcoeff : ∀ j, c * q.coeff j ∈ A := by
    intro j
    by_cases hj : j ∈ q.support
    · have hv := hj₀max j hj
      rw [← A.valuation_le_one_iff, map_mul, hc, map_inv₀]
      have hvj₀ : A.valuation (q.coeff j₀) ≠ 0 := by
        simp only [ne_eq, map_eq_zero]; exact hcj₀
      calc (A.valuation (q.coeff j₀))⁻¹ * A.valuation (q.coeff j)
          ≤ (A.valuation (q.coeff j₀))⁻¹ * A.valuation (q.coeff j₀) :=
            mul_le_mul_right hv _
        _ = 1 := inv_mul_cancel₀ hvj₀
    · rw [Polynomial.notMem_support_iff.mp hj, mul_zero]
      exact A.zero_mem
  set q' : Polynomial A := q.support.sum
    (fun j => Polynomial.C ⟨c * q.coeff j, hcoeff j⟩ * Polynomial.X ^ j) with hq'
  have hq'map : q'.map A.subtype = c • q := by
    rw [hq']
    ext j
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Polynomial.coeff_smul,
      smul_eq_mul]
    rw [Finset.sum_ite_eq q.support j]
    by_cases hj : j ∈ q.support
    · simp [hj]
    · simp [hj, Polynomial.notMem_support_iff.mp hj]
  have hq'j₀ : q'.coeff j₀ = ⟨1, A.one_mem⟩ := by
    rw [hq']
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq q.support j₀, ite_eq_left hj₀]
    refine Subtype.ext ?_
    show c * q.coeff j₀ = 1
    rw [hc, inv_mul_cancel₀ hcj₀]
  set q'' : Polynomial (ResidueField A) := q'.map (IsLocalRing.residue A) with hq''
  refine ⟨q'', ?_, ?_⟩
  · intro hq''0
    have : q''.coeff j₀ = 0 := by rw [hq''0]; simp
    rw [hq'', Polynomial.coeff_map, hq'j₀] at this
    exact one_ne_zero (α := ResidueField ↥A)
      ((map_one (IsLocalRing.residue ↥A)).symm.trans this)
  · have heval0 : (Polynomial.aeval (x : F)) (q'.map A.subtype) = 0 := by
      rw [hq'map, map_smul, hqx, smul_zero]
    have hsub : R.integers.subtype.comp (constHom R) = (algebraMap L F).comp A.subtype := by
      ext a; rfl
    have hevO : (Polynomial.eval₂ (constHom R) x q' : R.integers) = 0 := by
      apply Subtype.ext
      show ((Polynomial.eval₂ (constHom R) x q' : R.integers) : F) = ((0 : R.integers) : F)
      have h1 : ((Polynomial.eval₂ (constHom R) x q' : R.integers) : F) =
          Polynomial.eval₂ ((algebraMap L F).comp A.subtype) (↑x) q' := by
        rw [← hsub]
        exact Polynomial.hom_eval₂ q' (constHom R) R.integers.subtype x
      rw [h1, ← Polynomial.eval₂_map]
      simpa [Polynomial.aeval_def] using heval0
    have hresφ : R.residue.comp (constHom R) =
        (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A) := by
      ext a
      exact R.residue_algebraMap a
    calc (Polynomial.aeval (R.residue x)) q''
        = Polynomial.eval₂ (algebraMap (ResidueField A) Fbar) (R.residue x)
            (q'.map (IsLocalRing.residue A)) := by rw [hq'', Polynomial.aeval_def]
      _ = Polynomial.eval₂ ((algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A))
            (R.residue x) q' := by rw [Polynomial.eval₂_map]
      _ = Polynomial.eval₂ (R.residue.comp (constHom R)) (R.residue x) q' := by rw [hresφ]
      _ = R.residue (Polynomial.eval₂ (constHom R) x q') :=
            (Polynomial.hom_eval₂ q' (constHom R) R.residue x).symm
      _ = R.residue 0 := by rw [hevO]
      _ = 0 := map_zero _

/-! ### A monic bivariate relation -/

open Polynomial in
/-- The residue of an `eval₂` at constants is the `eval₂` of the residues. -/
theorem residue_comp_eval₂_constHom (R : RegularProlongation A F Fbar) (f : R.integers) :
    (R.residue : R.integers →+* Fbar).comp (eval₂RingHom (constHom R) f) =
      (eval₂RingHom (algebraMap (ResidueField A) Fbar) (R.residue f)).comp
        (Polynomial.mapRingHom (IsLocalRing.residue A)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.coe_mapRingHom, Polynomial.map_C]
    exact residue_constHom R a
  · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.coe_mapRingHom, Polynomial.map_X]

open Polynomial in
/-- The subtype of an `eval₂` at constants is the pin's `eval₂` at the coefficient map. -/
theorem subtype_comp_eval₂_constHom (R : RegularProlongation A F Fbar) (f : R.integers) :
    (R.integers.subtype : R.integers →+* F).comp (eval₂RingHom (constHom R) f) =
      eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    exact coe_constHom R a
  · simp

/-- A monic bivariate relation between `f` and the residue variable `u` forces the
residue of `u` to be integral over the residue adjoin of the residue of `f`. -/
theorem isIntegral_adjoin_residue_of_exists_monic_bivariate_eval_eq_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (f u : R.integers)
    (hu : ∃ p : Polynomial (Polynomial A), p.Monic ∧
      p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) (u : F) = 0) :
    IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) {R.residue f}) (R.residue u) := by
  classical
  set k := IsLocalRing.ResidueField A
  obtain ⟨p, hmon, heq⟩ := hu
  let Φ : Polynomial A →+* R.integers := Polynomial.eval₂RingHom (constHom R) f
  have heqO : p.eval₂ Φ u = 0 := by
    have h := Polynomial.hom_eval₂ p Φ R.integers.subtype u
    rw [subtype_comp_eval₂_constHom] at h
    exact Subtype.ext (h.trans heq)
  let ψ : Polynomial k →+* Fbar := Polynomial.eval₂RingHom (algebraMap k Fbar) (R.residue f)
  have heqbar :
      (p.map (Polynomial.mapRingHom (IsLocalRing.residue A))).eval₂ ψ (R.residue u) = 0 := by
    have h2 := Polynomial.hom_eval₂ p Φ R.residue u
    rw [residue_comp_eval₂_constHom] at h2
    rw [Polynomial.eval₂_map, ← h2, heqO, map_zero]
  set S : Subalgebra k Fbar := Algebra.adjoin k {R.residue f}
  have hfS : R.residue f ∈ S := Algebra.self_mem_adjoin_singleton k (R.residue f)
  let η : Polynomial k →+* S := Polynomial.eval₂RingHom (algebraMap k S) ⟨R.residue f, hfS⟩
  have hψη : (algebraMap S Fbar).comp η = ψ := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [η, ψ]
    · simp [η, ψ]
  refine ⟨(p.map (Polynomial.mapRingHom (IsLocalRing.residue A))).map η,
    (hmon.map _).map η, ?_⟩
  rw [Polynomial.eval₂_map, hψη]
  exact heqbar

/-! ### The minimum-order/residue bound for monic polynomials -/

section eval₂Mem

variable {S : Type*} [CommSemiring S] {E : Type*} [Field E]

open Polynomial in
/-- A polynomial whose coefficients and whose value lie in a subring takes its value in
that subring. -/
theorem eval₂_mem (T : Subring E) (ρ : S →+* E) (hρ : ∀ a, ρ a ∈ T) {y : E} (hy : y ∈ T)
    (q : S[X]) : q.eval₂ ρ y ∈ T := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add]; exact T.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    exact T.mul_mem (hρ a) (T.pow_mem hy n)

open Polynomial in
/-- A scaled root of a monic polynomial is integral in a valuation subring that holds the
scaled coefficients. -/
theorem mul_mem_of_monic (O : ValuationSubring E) (P : E[X]) (hP : P.Monic) (s x : E)
    (hcoeff : ∀ i, P.coeff i * s ^ (P.natDegree - i) ∈ O) (hx : P.eval x = 0) :
    s * x ∈ O := by
  set Q : E[X] := P.scaleRoots s with hQ
  have hQmonic : Q.Monic := (Polynomial.monic_scaleRoots_iff s).mpr hP
  have hQroot : Q.eval (s * x) = 0 := by
    have h := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id E) (r := x) (s := s) (p := P) hx
    simpa using h
  have hsub : (↑Q.coeffs : Set E) ⊆ O.toSubring := by
    intro c hc
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp (Finset.mem_coe.mp hc)
    rw [hQ, Polynomial.coeff_scaleRoots]
    exact hcoeff n
  set Q' : (O.toSubring)[X] := Q.toSubring O.toSubring hsub with hQ'
  have hQ'monic : Q'.Monic := (Polynomial.monic_toSubring Q O.toSubring hsub).mpr hQmonic
  have hint : IsIntegral O (s * x) := by
    refine ⟨Q', hQ'monic, ?_⟩
    have hmap : Q'.map (algebraMap O E) = Q := Polynomial.map_toSubring Q O.toSubring hsub
    rw [← hmap, Polynomial.eval_map] at hQroot
    exact hQroot
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := E)).mp hint
  rw [← hy]
  exact y.2

end eval₂Mem

section Residue

variable {k : Type*} [Field k] {Fbar : Type*} [Field Fbar] [Algebra k Fbar]
variable {S : Type*} [CommRing S] (ρ : S →+* Fbar)
  (hρ : ∀ w : Place k Fbar, ∀ a, ρ a ∈ w.toValuationSubring)

include hρ in

open Polynomial in
/-- The minimum-order/residue bound: a monic polynomial with coefficient degrees bounded
by `(natDegree - j) * m` bounds the order of its root by `m` times the negative part of
the order of the evaluation point. -/
theorem mul_min_ord_le_ord (y x : Fbar) (m : ℕ) (p : Polynomial (Polynomial S)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (eval₂RingHom ρ y) x = 0) (w : Place k Fbar) :
    (m : ℤ) * min 0 (w.ord y) ≤ w.ord x := by
  set θ : Polynomial S →+* Fbar := Polynomial.eval₂RingHom ρ y with hθ
  set P : Fbar[X] := p.map θ with hP
  have hPmonic : P.Monic := hp.map θ
  have hPdeg : P.natDegree = p.natDegree := hp.natDegree_map θ
  have hProot : P.eval x = 0 := by rw [hP, Polynomial.eval_map]; exact hroot
  have hPcoeff : ∀ i, P.coeff i = (p.coeff i).eval₂ ρ y := fun i => by
    rw [hP, Polynomial.coeff_map, hθ]; rfl
  set O := w.toValuationSubring with hO
  by_cases hy : y ∈ O
  · have hmin : min 0 (w.ord y) = 0 := min_eq_left (Place.ord_nonneg_of_mem w hy)
    rw [hmin, mul_zero]
    have hxO : (1 : Fbar) * x ∈ O := by
      refine mul_mem_of_monic O P hPmonic 1 x (fun i => ?_) hProot
      rw [one_pow, mul_one, hPcoeff]
      exact eval₂_mem O.toSubring ρ (hρ w) hy _
    rw [one_mul] at hxO
    exact Place.ord_nonneg_of_mem w hxO
  · have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hordy : w.ord y < 0 := Place.ord_neg_of_not_mem w hy
    have hmin : min 0 (w.ord y) = w.ord y := min_eq_right hordy.le
    rw [hmin]
    set g : Fbar := y⁻¹ with hg
    have hgO : g ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    let _ : Invertible y := invertibleOfNonzero hy0
    have hinvOf : (⅟y : Fbar) = g := by rw [hg, invOf_eq_inv]
    have hcoeff : ∀ i, P.coeff i * (g ^ m) ^ (P.natDegree - i) ∈ O := by
      intro i
      rw [hPcoeff, hPdeg, ← pow_mul]
      set N := m * (p.natDegree - i) with hN
      have hqN : (p.coeff i).natDegree ≤ N := by
        rw [hN, mul_comm]; exact hdeg i
      have hrefl := Polynomial.eval₂_reflect_mul_pow ρ y N (p.coeff i) hqN
      rw [hinvOf] at hrefl
      have hyN : (y ^ N : Fbar) ≠ 0 := pow_ne_zero _ hy0
      have hkey : (p.coeff i).eval₂ ρ y * g ^ N =
          (Polynomial.reflect N (p.coeff i)).eval₂ ρ g := by
        rw [← hrefl, mul_assoc, ← mul_pow, hg, mul_inv_cancel₀ hy0, one_pow, mul_one]
      rw [hkey]
      exact eval₂_mem O.toSubring ρ (hρ w) hgO _
    have hxO : g ^ m * x ∈ O := mul_mem_of_monic O P hPmonic (g ^ m) x hcoeff hProot
    rcases eq_or_ne x 0 with rfl | hx0
    · simp only [Place.ord_zero]
      have : (m : ℤ) * w.ord y ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg m) hordy.le
      exact this
    · have h0 := Place.ord_nonneg_of_mem w hxO
      have hg0 : g ≠ 0 := inv_ne_zero hy0
      rw [w.ord_mul (pow_ne_zero _ hg0) hx0, ← zpow_natCast, w.ord_zpow, hg, w.ord_inv] at h0
      linarith

end Residue

/-- The subtype of the constants is the algebra map of `L`. -/
theorem subtype_comp_constHom (R : RegularProlongation A F Fbar) :
    R.integers.subtype.comp (constHom R) = (algebraMap L F).comp A.subtype := by
  ext a; rfl

/-- The constants of `A` read in the residue field `Fbar`. -/
def resConst (A : ValuationSubring L) (Fbar : Type*) [Field Fbar]
    [Algebra (ResidueField A) Fbar] : A →+* Fbar :=
  (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A)

/-- The residue of a constant is the constant of the residue field. -/
theorem residue_comp_constHom (R : RegularProlongation A F Fbar) :
    R.residue.comp (constHom R) = resConst A Fbar := by
  ext a; exact residue_constHom R a

/-- The constants of `A` lie in every place's valuation subring. -/
theorem resConst_mem (w : Place (ResidueField A) Fbar) (a : A) :
    resConst A Fbar a ∈ w.toValuationSubring :=
  w.algebraMap_mem' _

open Polynomial in
/-- A bivariate root relation over the integers reads, in the residue field, as a root
relation over the residue field of `A`. -/
theorem eval₂_residue_eq_zero (R : RegularProlongation A F Fbar) (f h : R.integers)
    (p : Polynomial (Polynomial A))
    (hroot : p.eval₂ (eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) (h : F) = 0) :
    p.eval₂ (eval₂RingHom (resConst A Fbar) (R.residue f)) (R.residue h) = 0 := by
  set ψ : Polynomial A →+* R.integers := Polynomial.eval₂RingHom (constHom R) f with hψ
  have hcoeψ : R.integers.subtype.comp ψ =
      Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [hψ]
    · simp [hψ]
  have hO : p.eval₂ ψ h = 0 := by
    apply R.integers.subtype_injective
    have := Polynomial.hom_eval₂ p ψ R.integers.subtype h
    rw [map_zero, this, hcoeψ]
    exact hroot
  have hres := congrArg R.residue hO
  rw [map_zero, Polynomial.hom_eval₂] at hres
  have hcomp : R.residue.comp ψ =
      Polynomial.eval₂RingHom (resConst A Fbar) (R.residue f) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [hψ, residue_constHom, resConst]
    · simp [hψ]
  rw [hcomp] at hres
  exact hres

open Polynomial in
/-- The minimum-order/residue bound at the prolongation's integers. -/
theorem mul_min_ord_residue_le (R : RegularProlongation A F Fbar) (f h : R.integers) (m : ℕ)
    (p : Polynomial (Polynomial A)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) (h : F) = 0)
    (w : Place (ResidueField A) Fbar) :
    (m : ℤ) * min 0 (w.ord (R.residue f)) ≤ w.ord (R.residue h) :=
  mul_min_ord_le_ord (resConst A Fbar) (resConst_mem) (R.residue f) (R.residue h) m p hp hdeg
    (eval₂_residue_eq_zero R f h p hroot) w

/-- The minimum-order/residue bound for monic polynomials: along a place of the residue
field, the order of the residue of `h` is at least `m` times the negative part of the
order of the residue of `f`. -/
theorem mul_min_ord_residue_le_of_monic
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (f h : R.integers) (m : ℕ)
    (p : Polynomial (Polynomial A)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (Polynomial.eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F))
      (h : F) = 0)
    (w : Place (IsLocalRing.ResidueField A) Fbar) :
    (m : ℤ) * min 0 (w.ord (R.residue f)) ≤ w.ord (R.residue h) :=
  mul_min_ord_residue_le R f h m p hp hdeg hroot w

/-! ### The integers of a regular prolongation are their behaviour on `L(x)` -/

section uniqueness

variable (R : RegularProlongation A F Fbar) (x : R.integers)
  (hx : Transcendental (ResidueField A) (R.residue x))
  {n : ℕ} (y : Fin n → R.integers)
  (hy : LinearIndependent (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
    (fun i => R.residue (y i)))

include hx hy in

/-- A unit multiple of a finite-dimensional subspace lies in the span of a finite piece of
the frame, and the unit itself lies in `L(x)`. -/
theorem exists_unit_mul_mem_span_adjoin
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n)
    (V : Submodule L F) [FiniteDimensional L V] :
    ∃ U : R.integers, R.residue U ≠ 0 ∧ (U : F) ∈ IntermediateField.adjoin L ({(x : F)} : Set F) ∧
      ∃ T : Finset (ℕ × Fin n), ∀ v ∈ V, (U : F) * v ∈
        Submodule.span L (Set.range fun p : T => (x : F) ^ p.1.1 * (y p.1.2 : F)) := by
  classical
  let bV := Module.finBasis L V
  choose r hr using
    fun a : Fin (Module.finrank L V) => exists_repr_adjoinField R x hx y hy hcard ((bV a : V) : F)
  have hfrac : ∀ a i, ∃ PQ : Polynomial L × Polynomial L, Polynomial.aeval (x : F) PQ.2 ≠ 0 ∧
      (r a i : F) = Polynomial.aeval (x : F) PQ.1 / Polynomial.aeval (x : F) PQ.2 := by
    intro a i
    obtain ⟨P, Q, hPQ⟩ := (IntermediateField.mem_adjoin_simple_iff L (r a i : F)).mp (r a i).2
    by_cases hQ : Polynomial.aeval (x : F) Q = 0
    · refine ⟨(0, 1), by simp, ?_⟩
      rw [hPQ, hQ, div_zero]
      simp
    · exact ⟨(P, Q), hQ, hPQ⟩
  choose PQ hQne hPQ using hfrac
  set q : Polynomial L := ∏ p : Fin (Module.finrank L V) × Fin n, (PQ p.1 p.2).2 with hqdef
  have haevalq : Polynomial.aeval (x : F) q =
      ∏ p : Fin (Module.finrank L V) × Fin n, Polynomial.aeval (x : F) (PQ p.1 p.2).2 := by
    rw [hqdef, map_prod]
  have hqx : Polynomial.aeval (x : F) q ≠ 0 := by
    rw [haevalq]
    exact Finset.prod_ne_zero_iff.mpr fun p _ => hQne p.1 p.2
  have hq0 : q ≠ 0 := by
    rintro h
    rw [h, map_zero] at hqx
    exact hqx rfl
  obtain ⟨U, hU, c, hc, hUq⟩ := exists_normalize_aeval R x hx q hq0
  obtain ⟨H, hH⟩ : ∃ H : Fin (Module.finrank L V) → Fin n → Polynomial L,
      ∀ a i, (U : F) * ((r a i : F) * (y i : F)) =
        Polynomial.aeval (x : F) (H a i) * (y i : F) := by
    refine ⟨fun a i => Polynomial.C c⁻¹ *
      ((∏ p ∈ Finset.univ.erase (a, i), (PQ p.1 p.2).2) * (PQ a i).1), fun a i => ?_⟩
    rw [hUq, hPQ a i, ← mul_assoc]
    congr 1
    simp only [map_mul, Polynomial.aeval_C, map_prod]
    rw [haevalq, ← Finset.mul_prod_erase Finset.univ
      (fun p : Fin (Module.finrank L V) × Fin n => Polynomial.aeval (x : F) (PQ p.1 p.2).2)
      (Finset.mem_univ (a, i))]
    have hQ := hQne a i
    field_simp
  have hN : ∃ N : ℕ, ∀ a i, (H a i).natDegree < N := by
    let g : Fin (Module.finrank L V) × Fin n → ℕ := fun p => (H p.1 p.2).natDegree
    refine ⟨Finset.univ.sup g + 1, fun a i => Nat.lt_succ_of_le ?_⟩
    exact Finset.le_sup (f := g) (Finset.mem_univ (a, i))
  obtain ⟨N, hlt⟩ := hN
  have hUmem : (U : F) ∈ IntermediateField.adjoin L ({(x : F)} : Set F) := by
    rw [hUq]
    refine mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    rw [Polynomial.aeval_eq_sum_range]
    refine sum_mem fun j _ => IntermediateField.smul_mem _ ?_
    exact pow_mem (IntermediateField.mem_adjoin_simple_self L (x : F)) _
  refine ⟨U, hU, hUmem, Finset.range N ×ˢ Finset.univ, ?_⟩
  let S : Submodule L F := Submodule.span L
    (Set.range fun p : ↥(Finset.range N ×ˢ (Finset.univ : Finset (Fin n))) =>
      (x : F) ^ p.1.1 * (y p.1.2 : F))
  change ∀ v ∈ V, (U : F) * v ∈ S
  have hgen : ∀ j < N, ∀ i, (x : F) ^ j * (y i : F) ∈ S := by
    intro j hj i
    apply Submodule.subset_span
    exact ⟨⟨(j, i), Finset.mk_mem_product (Finset.mem_range.mpr hj) (Finset.mem_univ i)⟩, rfl⟩
  have hbasis : ∀ a, (U : F) * ((bV a : V) : F) ∈ S := by
    intro a
    rw [hr a, Finset.mul_sum]
    refine S.sum_mem fun i _ => ?_
    rw [hH a i, Polynomial.aeval_eq_sum_range' (hlt a i), Finset.sum_mul]
    refine S.sum_mem fun j hj => ?_
    rw [smul_mul_assoc]
    exact S.smul_mem _ (hgen j (Finset.mem_range.mp hj) i)
  intro v hv
  have hvsum : v = ∑ a, bV.repr ⟨v, hv⟩ a • ((bV a : V) : F) := by
    have h := congrArg (fun w : V => (w : F)) (bV.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  rw [hvsum, Finset.mul_sum]
  refine S.sum_mem fun a _ => ?_
  rw [mul_smul_comm]
  exact S.smul_mem _ (hbasis a)

include hx hy in

/-- An integer is a combination of the `y i` whose coefficients are integers of `L(x)`. -/
theorem exists_repr_mem_inf
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n)
    (f : R.integers) :
    ∃ r : Fin n → F, (∀ i, r i ∈ R.integers ∧ r i ∈ IntermediateField.adjoin L ({(x : F)} : Set F)) ∧
      (f : F) = ∑ i, r i * (y i : F) := by
  classical
  set Lx := IntermediateField.adjoin L ({(x : F)} : Set F) with hLx
  obtain ⟨U, hU, hULx, T, hT⟩ :=
    exists_unit_mul_mem_span_adjoin R x hx y hy hcard (L ∙ (f : F))
  have hmem := hT (f : F) (Submodule.mem_span_singleton_self _)
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun L).mp hmem
  have hgO : ∑ p ∈ (Finset.univ : Finset T), g p • ((frame R x y p.1 : R.integers) : F) ∈
      R.integers := by
    have : ∑ p ∈ (Finset.univ : Finset T), g p • ((frame R x y p.1 : R.integers) : F) =
        (U : F) * (f : F) := by
      rw [← hg]
      exact Finset.sum_congr rfl fun p _ => by rw [coe_frame]
    rw [this]
    exact (U * f).2
  have hEind : LinearIndependent (ResidueField A)
      (fun p : T => R.residue (frame R x y p.1)) :=
    (linearIndependent_residue_frame R x hx y hy).comp _ Subtype.val_injective
  have hgA : ∀ p : T, g p ∈ A := fun p =>
    mem_of_sum_smul_mem R (fun p : T => frame R x y p.1) hEind Finset.univ g hgO p
      (Finset.mem_univ p)
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hU
  have huinv : ((↑u⁻¹ : R.integers) : F) * (U : F) = 1 := by
    rw [← hu, ← Subring.coe_mul, Units.inv_mul]; rfl
  have hU0 : (U : F) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at huinv; exact zero_ne_one huinv
  have huinv' : ((↑u⁻¹ : R.integers) : F) = (U : F)⁻¹ :=
    eq_inv_of_mul_eq_one_left huinv
  refine ⟨fun i => ∑ p ∈ Finset.univ.filter (fun p : T => p.1.2 = i),
      (U : F)⁻¹ * (algebraMap L F (g p) * (x : F) ^ p.1.1), fun i => ⟨?_, ?_⟩, ?_⟩
  · refine sum_mem fun p _ => mul_mem ?_ (mul_mem ?_ (pow_mem x.2 _))
    · rw [← huinv']; exact (↑u⁻¹ : R.integers).2
    · exact (R.algebraMap_mem_iff (g p)).mpr (hgA p)
  · refine sum_mem fun p _ => mul_mem (inv_mem hULx) (mul_mem (Lx.algebraMap_mem _) ?_)
    exact pow_mem (IntermediateField.mem_adjoin_simple_self L (x : F)) _
  · have hf : (f : F) = (U : F)⁻¹ * ((U : F) * (f : F)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hU0, one_mul]
    rw [hf, ← hg, Finset.mul_sum]
    simp_rw [Finset.sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : T => p.1.2) (t := Finset.univ)
      (fun p _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [← hp.2, Algebra.smul_def]
    ring

include hx hy in

/-- Agreement on `L(x)`: the integers of the prolongation lie in a valuation subring of
`F` that contains the integers of `L(x)`. -/
theorem integers_le_of_forall_mem
    [FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F]
    (hcard : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F = n)
    (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L ({(x : F)} : Set F) → e ∈ R.integers → e ∈ V) :
    R.integers ≤ V := by
  classical
  have hyV : ∀ i, (y i : F) ∈ V := by
    by_contra hne
    obtain ⟨i₁, hi₁⟩ := not_forall.mp hne
    obtain ⟨i₀, -, hmax⟩ :=
      Finset.univ.exists_max_image (fun i => V.valuation (y i : F)) ⟨i₁, Finset.mem_univ _⟩
    set w : F := (y i₀ : F) with hw
    have hw1 : 1 < V.valuation w := by
      have h1 : 1 < V.valuation (y i₁ : F) := by
        rw [← not_le, V.valuation_le_one_iff]; exact hi₁
      exact lt_of_lt_of_le h1 (hmax i₁ (Finset.mem_univ _))
    have hw0 : w ≠ 0 := by
      intro h0; rw [h0, map_zero] at hw1; exact not_lt_zero hw1
    have hvw0 : V.valuation w ≠ 0 := by rwa [ne_eq, map_eq_zero]
    have hquot : ∀ i, V.valuation ((y i : F) * w⁻¹) ≤ 1 := by
      intro i
      rw [map_mul, map_inv₀]
      calc V.valuation (y i : F) * (V.valuation w)⁻¹
          ≤ V.valuation w * (V.valuation w)⁻¹ := by
            gcongr; exact hmax i (Finset.mem_univ _)
        _ = 1 := mul_inv_cancel₀ hvw0
    have hwinv : V.valuation w⁻¹ < 1 := by
      rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hw1
    obtain ⟨r, hr, hsum⟩ := exists_repr_mem_inf R x hx y hy hcard (y i₀ * y i₀)
    have hrV : ∀ i, V.valuation (r i) ≤ 1 := fun i =>
      (V.valuation_le_one_iff _).mpr (hV _ (hr i).2 (hr i).1)
    have hone : (1 : F) = ∑ i, r i * ((y i : F) * w⁻¹) * w⁻¹ := by
      have h2 : w * w = ∑ i, r i * (y i : F) := by rw [hw]; exact_mod_cast hsum
      calc (1 : F) = (w * w) * w⁻¹ * w⁻¹ := by field_simp
        _ = ∑ i, r i * ((y i : F) * w⁻¹) * w⁻¹ := by
          rw [h2, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => by ring
    have hlt : V.valuation (∑ i, r i * ((y i : F) * w⁻¹) * w⁻¹) < 1 := by
      refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
      rw [map_mul, map_mul]
      calc V.valuation (r i) * V.valuation ((y i : F) * w⁻¹) * V.valuation w⁻¹
          ≤ 1 * 1 * V.valuation w⁻¹ := by
            gcongr
            · exact hrV i
            · exact hquot i
        _ = V.valuation w⁻¹ := by rw [one_mul, one_mul]
        _ < 1 := hwinv
    rw [← hone, map_one] at hlt
    exact lt_irrefl _ hlt
  intro f hf
  obtain ⟨r, hr, hsum⟩ := exists_repr_mem_inf R x hx y hy hcard ⟨f, hf⟩
  change f = _ at hsum
  rw [show f ∈ V ↔ (f : F) ∈ V from Iff.rfl, hsum]
  exact sum_mem fun i _ => mul_mem (hV _ (hr i).2 (hr i).1) (hyV i)

/-- A valuation subring that contains the integers and whose constants are integers is
contained in the integers. -/
theorem le_integers_of_integers_le (V : ValuationSubring F) (hOV : R.integers ≤ V)
    (hV : ∀ c : L, algebraMap L F c ∈ V → algebraMap L F c ∈ R.integers) :
    V ≤ R.integers := by
  intro f hfV
  by_contra hfO
  have hf0 : f ≠ 0 := by
    rintro rfl; exact hfO (zero_mem _)
  obtain ⟨c, hcf, hres⟩ := R.exists_smul_mem f hf0
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero hres
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : L) • f, hcf⟩ : R.integers) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  have hinvO : (c • f)⁻¹ ∈ R.integers := by
    have h1 : ((↑u⁻¹ : R.integers) : F) * (c • f) = 1 := by
      have := congrArg (fun z : R.integers => (z : F)) (Units.inv_mul u)
      simpa [hu] using this
    have : (c • f)⁻¹ = ((↑u⁻¹ : R.integers) : F) := (eq_inv_of_mul_eq_one_left h1).symm
    rw [this]; exact (↑u⁻¹ : R.integers).2
  have hcinv : algebraMap L F c⁻¹ = f * (c • f)⁻¹ := by
    rw [Algebra.smul_def, mul_inv, ← mul_assoc, mul_comm f, mul_assoc, mul_inv_cancel₀ hf0,
      mul_one, map_inv₀]
  have hcinvV : algebraMap L F c⁻¹ ∈ V := by
    rw [hcinv]; exact mul_mem hfV (hOV hinvO)
  have hcinvO := hV _ hcinvV
  apply hfO
  have : f = algebraMap L F c⁻¹ * (c • f) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  rw [this]
  exact mul_mem hcinvO hcf

end uniqueness

/-- The primed working form of the headline, at its own binders. -/
theorem eq_integers_of_forall_mem_adjoin_iff' (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) :
    V = R.integers := by
  have : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  have : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  let yb := Module.finBasis
    (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar
  choose y hy using fun i => R.residue_surjective (yb i)
  have hyind : LinearIndependent
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar))
      (fun i => R.residue (y i)) := by
    have : (fun i => R.residue (y i)) = yb := funext hy
    rw [this]; exact yb.linearIndependent
  have hOV : R.integers ≤ V :=
    integers_le_of_forall_mem R x hx y hyind hdeg V (fun e he heO => (hV e he).mpr heO)
  have hVO : V ≤ R.integers :=
    le_integers_of_integers_le R V hOV
      (fun c hc => (hV _ (IntermediateField.algebraMap_mem _ c)).mp hc)
  exact le_antisymm hVO hOV

/-- A valuation subring of `F` that agrees with the integers of the regular prolongation
on the field `L(x)` generated by a transcendental integer `x` **is** those integers. -/
theorem eq_integers_of_forall_mem_adjoin_iff
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : ValuationSubring F)
    (hV : ∀ e : F, e ∈ IntermediateField.adjoin L {(x : F)} → (e ∈ V ↔ e ∈ R.integers)) :
    V = R.integers :=
  eq_integers_of_forall_mem_adjoin_iff' R x hx hfin hdeg V hV

end RegularProlongation

end AlgebraicCurve

end
