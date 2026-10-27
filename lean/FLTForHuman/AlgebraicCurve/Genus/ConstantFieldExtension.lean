/-
The RR-level descent of the constant-field-extension wave: principality and torsion
descent of divisors along `K ⊆ K'`, `F ⊆ F' = K'·F`.  After FLT's
`P2M/Sol/S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension.lean` (402 ln)
and `P2M/Sol/S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.lean`
(878 ln), with their `Theorems/` wrappers:

* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension.lean>
* <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.lean>

**The mathematics.**  `isPrincipal_of_constantFieldExtension` decides principality
over the algebraically closed base: if `D'` on `F'` is principal and agrees with `D`
on the places of `F` (vanishing off them), then `D` is principal.  The pin's engine
`W7XK1a.isPrincipal_of_constantFieldExtension` lifts every place of `F` to `F'`,
writes the witnessing function `z` in the `K'`-digit expansion of
`exists_linearIndependent_repr`, bounds `D` by `P.ord` of the worst digit with
`ord_sum_le`, and closes on `degree_eq_sum` over the algebraically closed base.

`exists_torsion_descent_of_constantFieldExtension` descends an `n`-torsion class:
from `n·D' = div g'` it produces `D` on `F`, `g` on `F` with `n·D = div g`, and the
correction `h'` off the fibre.  The pin's engine `TorsionDescentDeriv.main` reduces
`D'` by a place `P₀` of negative order at a transcendental, uses Riemann–Roch
(`exists_reduced`: some `r` with `ell (c + r·P₀) = 1`) to put `φ = g'·fr^n` in the
`n`-fold multiple of an effective divisor `A`, shows `A`'s support lies over places of
`F` by producing — for a generic place — a derivation of `F'` over `K'` with
`δ t = 1` (`exists_derivation_apply_eq_one`) and applying
`exists_derivation_constantFieldExtension_map_mem` to the eigen-element estimate
`ord_le_ord_apply_of_eigen`, and finally applies the principality descent to
`n • R₀` over `n • B`.

**Home and visibility.**  `Genus/` is the RR home of the port and imports
`Differential/`, so this module takes the shared 192-line block
(`HorizDeriv.ord_sum_le`, `…exists_linearIndependent_repr`, `…isUnit_of_ord_eq_zero`,
`…ord_pos_of_mem_maximalIdeal`) from `Differential/ConstantFieldExtension.lean`
(P4) instead of repeating it; `W7XH.degree_eq_sum` comes from
`IsCurveOver/ConstantFieldExtensionSpan.lean`, the RR facts from `Genus/Index.lean`
and `Genus/Stichtenoth.lean`, and the alg-closed genus from
`RiemannRoch/Assembly.lean`.  The two public headlines are the pin's names; every
engine of the two pin files (`W7XK1a.…`, `TorsionDescentDeriv.…`) is `private` here,
because P6 imports only the two headlines.

Statements are transcribed textually from the pin.  The pin's global
`attribute [-instance]`/`[-simp]` walls are dropped; no statement changes.

spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_isPrincipal_of_constantFieldExtension.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_exists_torsion_descent_of_constantFieldExtension.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Differential.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Localization.FractionRing

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

/-! ## Principality descent

`AlgebraicCurve.Divisor.isPrincipal_of_constantFieldExtension` and its engine
`W7XK1a.isPrincipal_of_constantFieldExtension` (the pin's 402-line file). -/

namespace W7XK1a

section Main

variable (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F]
  [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F']
  [IsScalarTower K F F']

private theorem isPrincipal_of_constantFieldExtension [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (D : Divisor K F) (D' : Divisor K' F')
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        D' v' = 0)
    (hD' : D'.IsPrincipal) :
    D.IsPrincipal := by
  classical
  obtain ⟨z, hz0, hzD⟩ := hD'

  have hX := fun P : Place K F =>
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F K' F'
      hfg hfg' hgen P
  choose lift hlift_comap hlift_ord hlift_uniq using hX
  have hlift_inj : Function.Injective lift := by
    intro P Q h
    apply Place.ext
    rw [← hlift_comap P, ← hlift_comap Q, h]

  have hz_off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        z ∈ v'.toValuationSubring := by
    intro v' hv'
    apply Place.mem_vs_of_ord_nonneg
    rw [← hzD, hD'off v' hv']
  have hzspan := mem_span_range_algebraMap_of_constantFieldExtension K F K' F'
    hfg hfg' hgen z hz_off
  obtain ⟨n, β, u, hβ, hzu⟩ := HorizDeriv.exists_linearIndependent_repr K F K' F' hzspan

  obtain ⟨k₀, hk₀⟩ : ∃ k, u k ≠ 0 := by
    by_contra h
    push Not at h
    apply hz0
    rw [hzu]
    simp [h]

  have hle : ∀ P : Place K F, D P ≤ P.ord (u k₀) := by
    intro P
    have h := HorizDeriv.ord_sum_le P (lift P) (hlift_comap P) (hlift_ord P) Finset.univ β hβ u
      (Finset.mem_univ k₀) hk₀
    rwa [← hzu, ← hzD, hD'over _ _ (hlift_comap P)] at h

  have hdegD' : D'.degree = 0 := by
    obtain ⟨E', hE', hE'deg⟩ := HasPrincipalDivisors.exists_divisor (K := K') z hz0
    have : D' = E' := Finsupp.ext fun v' => by rw [hzD, hE']
    rw [this]
    exact hE'deg
  have hD'map : D' = Finsupp.mapDomain lift D := by
    ext v'
    by_cases hv' : ∃ P, lift P = v'
    · obtain ⟨P, rfl⟩ := hv'
      rw [Finsupp.mapDomain_apply_of_injective hlift_inj, hD'over _ _ (hlift_comap P)]
    · push Not at hv'
      rw [Finsupp.mapDomain_of_notMem_range D v' (fun ⟨P, hP⟩ => hv' P hP)]
      apply hD'off
      intro P hP
      exact hv' P (hlift_uniq P v' hP).symm
  have hdegD : D.degree = 0 := by
    have h1 : D'.degree = D.sum fun _ n => n := by
      rw [hD'map, W7XH.degree_eq_sum, Finsupp.sum_mapDomain_index_inj hlift_inj]
    rw [W7XH.degree_eq_sum, ← h1, hdegD']
  obtain ⟨E, hE, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (u k₀) hk₀

  have hG : ∀ v, 0 ≤ (E - D) v := fun v => by
    simp only [Finsupp.coe_sub, Pi.sub_apply, hE]
    linarith [hle v]
  have hGdeg : (E - D).degree = 0 := by rw [map_sub, hEdeg, hdegD, sub_zero]
  have hG0 : E - D = 0 := by
    rw [W7XH.degree_eq_sum, Finsupp.sum] at hGdeg
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hG v)).1 hGdeg
    ext v
    by_cases hv : v ∈ (E - D).support
    · exact h v hv
    · exact Finsupp.notMem_support_iff.1 hv
  refine ⟨u k₀, hk₀, fun v => ?_⟩
  have h := DFunLike.congr_fun hG0 v
  simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.coe_zero, Pi.zero_apply, hE] at h
  linarith

end Main

end W7XK1a

/-- **Principality descends along a constant-field extension.**  If `D'` on
`F' = K'·F` is principal and agrees with `D` over the places of `F`, and vanishes off
them, then `D` is principal.  The pin's
`AlgebraicCurve.Divisor.isPrincipal_of_constantFieldExtension` (402 ln). -/
theorem Divisor.isPrincipal_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (D : Divisor K F) (D' : Divisor K' F')
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        D' v' = 0)
    (hD' : D'.IsPrincipal) :
    D.IsPrincipal :=
  W7XK1a.isPrincipal_of_constantFieldExtension K F K' F' hfg hfg' hgen D D'
    hD'over hD'off hD'

/-! ## Torsion descent

`AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension` and the
pin's `TorsionDescentDeriv` engine (878 ln).  The engine block is the pin's own and
is `private` here: the `divOf` bookkeeping (`section General`), the
lying-over/generic-place vocabulary (`section Extension`), the existence of a
`K`-derivation with `δ t = 1` (`section DerivationExistence`), the local
valuation calculus (`section LocalCalc`), and `main`. -/

namespace TorsionDescentDeriv

section General

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

open Classical in
/-- The divisor of a function, chosen from `HasPrincipalDivisors`. -/
private noncomputable def divOf [HasPrincipalDivisors K F] (f : F) : Divisor K F :=
  if hf : f = 0 then 0 else (HasPrincipalDivisors.exists_divisor (K := K) f hf).choose

private theorem divOf_apply [HasPrincipalDivisors K F] {f : F} (hf : f ≠ 0) (v : Place K F) :
    divOf f v = v.ord f := by
  classical
  rw [divOf, dite_eq_right hf]
  exact (HasPrincipalDivisors.exists_divisor (K := K) f hf).choose_spec.1 v

private theorem divOf_zero [HasPrincipalDivisors K F] : divOf (K := K) (0 : F) = 0 := by
  classical
  rw [divOf, dite_eq_left rfl]

private theorem degree_divOf [HasPrincipalDivisors K F] (f : F) :
    Divisor.degree (divOf (K := K) f) = 0 := by
  classical
  by_cases hf : f = 0
  · subst hf
    simp [divOf_zero]
  · rw [divOf, dite_eq_right hf]
    exact (HasPrincipalDivisors.exists_divisor (K := K) f hf).choose_spec.2

private theorem isPrincipal_iff_eq_divOf [HasPrincipalDivisors K F] {D : Divisor K F} :
    D.IsPrincipal ↔ ∃ f : F, f ≠ 0 ∧ D = divOf f := by
  constructor
  · rintro ⟨f, hf, hD⟩
    exact ⟨f, hf, Finsupp.ext fun v => by rw [hD v, divOf_apply hf v]⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf, fun v => divOf_apply hf v⟩

private theorem divOf_mul [HasPrincipalDivisors K F] {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    divOf (K := K) (f * g) = divOf f + divOf g := by
  ext v
  rw [Finsupp.add_apply, divOf_apply (mul_ne_zero hf hg) v, divOf_apply hf v, divOf_apply hg v,
    Place.ord_mul _ hf hg]

private theorem divOf_inv [HasPrincipalDivisors K F] (f : F) :
    divOf (K := K) f⁻¹ = -divOf f := by
  classical
  by_cases hf : f = 0
  · subst hf
    simp [divOf_zero]
  ext v
  rw [Finsupp.neg_apply, divOf_apply (inv_ne_zero hf) v, divOf_apply hf v, Place.ord_inv]

private theorem divOf_pow [HasPrincipalDivisors K F] (f : F) (n : ℕ) :
    divOf (K := K) (f ^ n) = (n : ℤ) • divOf f := by
  classical
  by_cases hf : f = 0
  · subst hf
    cases n with
    | zero =>
      ext v
      simp only [pow_zero, Nat.cast_zero, zero_smul, Finsupp.coe_zero, Pi.zero_apply]
      rw [divOf_apply one_ne_zero v, Place.ord_one]
    | succ n => simp [divOf_zero]
  induction n with
  | zero =>
    ext v
    simp only [pow_zero, Nat.cast_zero, zero_smul, Finsupp.coe_zero, Pi.zero_apply]
    rw [divOf_apply one_ne_zero v, Place.ord_one]
  | succ n ih =>
    rw [pow_succ, divOf_mul (pow_ne_zero _ hf) hf, ih]
    simp [add_smul]

private theorem mem_lSpace_add_divOf_iff [HasPrincipalDivisors K F] {D : Divisor K F} {u : F}
    (hu : u ≠ 0) {y : F} :
    y ∈ LSpace (D + divOf u) ↔ y * u ∈ LSpace D := by
  rw [mem_lSpace_iff_ord, mem_lSpace_iff_ord]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  simp only [hy, mul_ne_zero hy hu, false_or, Finsupp.add_apply]
  constructor
  · intro h v
    have := h v
    rw [divOf_apply hu v] at this
    rw [Place.ord_mul _ hy hu]
    linarith
  · intro h v
    have := h v
    rw [Place.ord_mul _ hy hu] at this
    rw [divOf_apply hu v]
    linarith

private theorem divOf_add_mem_lSpace [HasPrincipalDivisors K F] {D : Divisor K F} {f : F}
    (hf0 : f ≠ 0) (hf : f ∈ LSpace D) :
    ∀ v : Place K F, 0 ≤ (D + divOf f : Divisor K F) v := by
  intro v
  have := ((mem_lSpace_iff_ord.mp hf).resolve_left hf0) v
  simp only [Finsupp.coe_add, Pi.add_apply, divOf_apply hf0 v]
  linarith

private theorem constantsAreBase_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ConstantsAreBase K F := by
  classical
  refine le_antisymm ?_ ?_
  · intro f hf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact zero_mem _
    have hord : ∀ v : Place K F, 0 ≤ v.ord f := by
      intro v
      have := ((mem_lSpace_iff_ord.mp hf).resolve_left hf0) v
      simpa using this
    have hzero : ∀ v : Place K F, v.ord f = 0 := by
      have hdeg := degree_divOf (K := K) f
      rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum] at hdeg
      have hnonneg : ∀ v ∈ (divOf (K := K) f).support,
          (0 : ℤ) ≤ (AddMonoidHom.mulRight (v.deg : ℤ)) (divOf (K := K) f v) := by
        intro v _
        simp only [AddMonoidHom.coe_mulRight, IsCurveOver.deg_eq_one_of_isAlgClosed v,
          Nat.cast_one, mul_one, divOf_apply hf0 v]
        exact hord v
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdeg
      intro v
      by_cases hv : v ∈ (divOf (K := K) f).support
      · have := hall v hv
        simpa [IsCurveOver.deg_eq_one_of_isAlgClosed v, divOf_apply hf0 v] using this
      · have : divOf (K := K) f v = 0 := Finsupp.notMem_support_iff.mp hv
        rwa [divOf_apply hf0 v] at this
    obtain ⟨c, hc⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hj hzero
    exact ⟨c, hc⟩
  · rintro _ ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c

set_option linter.style.haveILetI false in
private theorem exists_riemann_inequality [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  haveI : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hj hfd
  obtain ⟨γ, hγ⟩ :=
    exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) (constantsAreBase_of_isAlgClosed j hj)
  refine ⟨γ, fun D => ?_⟩
  have h := (hγ D).2
  have h0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

set_option linter.style.haveILetI false in
private theorem exists_reduced [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    (c : Divisor K F) (hc : Divisor.degree c = 0) (P : Place K F) :
    ∃ (r : ℕ) (f : F), f ≠ 0 ∧ f ∈ LSpace (c + (r : ℤ) • Finsupp.single P 1) ∧
      ∀ h ∈ LSpace (c + (r : ℤ) • Finsupp.single P 1), ∃ a : K, a • f = h := by
  classical
  obtain ⟨γ, hγ⟩ := exists_riemann_inequality (K := K) (F := F) j hj
  have hC := constantsAreBase_of_isAlgClosed (K := K) (F := F) j hj
  haveI := RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  let Dk : ℕ → Divisor K F := fun k => c + (k : ℤ) • Finsupp.single P 1
  have hdeg1 : P.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P
  have hdegk : ∀ k : ℕ, Divisor.degree (Dk k) = k := by
    intro k
    simp only [Dk, map_add, map_zsmul, hc, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one,
      smul_eq_mul, zero_add]
  have hex : ∃ k : ℕ, LSpace (Dk k) ≠ ⊥ := by
    refine ⟨γ.toNat, fun hbot => ?_⟩
    have h1 := hγ (Dk γ.toNat)
    have h2 : ell (Dk γ.toNat) = 0 := by
      rw [ell, hbot, finrank_bot]
    rw [hdegk, h2] at h1
    have := Int.self_le_toNat γ
    push_cast at h1
    linarith
  set r := Nat.find hex with hr_def
  have hr : LSpace (Dk r) ≠ ⊥ := Nat.find_spec hex
  obtain ⟨f, hfmem, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hr
  refine ⟨r, f, hf0, hfmem, ?_⟩
  have hprev : LSpace (Dk r - Finsupp.single P 1) = ⊥ := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · apply lSpace_eq_bot_of_degree_neg
      rw [map_sub, hdegk, h0, Divisor.degree_single, hdeg1]
      norm_num
    · have heq : Dk r - Finsupp.single P 1 = Dk (r - 1) := by
        simp only [Dk]
        rw [Nat.cast_sub hpos, sub_smul, Nat.cast_one, one_smul]
        abel
      rw [heq]
      by_contra hne
      exact Nat.find_min hex (Nat.sub_lt hpos one_pos) hne
  have hle : ell (Dk r) ≤ 1 := by
    have := ell_le_ell_sub_single_add_deg (Dk r) P
    have h0 : ell (Dk r - Finsupp.single P 1) = 0 := by
      rw [ell, hprev, finrank_bot]
    rw [h0, hdeg1, zero_add] at this
    exact this
  haveI : FiniteDimensional K (LSpace (Dk r)) := finiteDimensional_lSpace (Dk r)
  have hfne : (⟨f, hfmem⟩ : LSpace (Dk r)) ≠ 0 := by
    intro h
    apply hf0
    simpa using congrArg Subtype.val h
  have hone : Module.finrank K (LSpace (Dk r)) = 1 := by
    refine le_antisymm hle ?_
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨f, hfmem⟩, hfne⟩
  intro h hh
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨f, hfmem⟩ : LSpace (Dk r)) hfne).mp hone
    ⟨h, hh⟩
  exact ⟨a, by simpa using congrArg Subtype.val ha⟩

end General

section Extension

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra F F']

private def LiesOver (w' : Place K' F') (v : Place K F) : Prop :=
  w'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring

private def IsGeneric (K F : Type*) [Field K] [Field F] [Algebra K F] [Algebra F F']
    (w' : Place K' F') : Prop :=
  ∀ v : Place K F, ¬ LiesOver w' v

private def InMax (w : Place K' F') (y : F') : Prop := y = 0 ∨ 0 < w.ord y

section Tower

variable [Algebra K K'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

private theorem IsGeneric.comap_eq_top [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') :
    w'.toValuationSubring.comap (algebraMap F F') = ⊤ := by
  by_contra hne
  obtain ⟨v, hv⟩ := Place.exists_of_valuationSubring (K := K) x
    (w'.toValuationSubring.comap (algebraMap F F')) (fun a => by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply K K' F']
      exact w'.algebraMap_mem' _) hne
  exact hw v hv.symm

private theorem IsGeneric.algebraMap_mem [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') (y : F) :
    algebraMap F F' y ∈ w'.toValuationSubring := by
  rw [← ValuationSubring.mem_comap, hw.comap_eq_top x]
  exact ValuationSubring.mem_top _

private theorem IsGeneric.ord_algebraMap [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') (y : F) :
    w'.ord (algebraMap F F' y) = 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hy' : algebraMap F F' y ≠ 0 := by simpa using hy
  have hyi' : algebraMap F F' y⁻¹ ≠ 0 := by simpa using hy
  have h1 := (Place.mem_iff_ord_nonneg w' hy').mp (hw.algebraMap_mem x y)
  have h2 := (Place.mem_iff_ord_nonneg w' hyi').mp (hw.algebraMap_mem x y⁻¹)
  rw [map_inv₀, Place.ord_inv] at h2
  linarith

private theorem IsGeneric.exists_inMax_sub [CharZero K] [IsAlgClosed K'] [IsCurveOver K' F'] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') :
    ∃ t : K', InMax w' (algebraMap F F' x - algebraMap K' F' t) := by
  have hsurj : Function.Surjective (algebraMap K' w'.ResidueField) :=
    (Place.deg_eq_one_iff_surjective_algebraMap_residueField w').mp
      (IsCurveOver.deg_eq_one_of_isAlgClosed w')
  have hxmem : algebraMap F F' x ∈ w'.toValuationSubring := hw.algebraMap_mem x x
  obtain ⟨t, ht⟩ := hsurj (IsLocalRing.residue _ ⟨algebraMap F F' x, hxmem⟩)
  have htmem : algebraMap K' F' t ∈ w'.toValuationSubring := w'.algebraMap_mem' t
  refine ⟨t, (Place.mk_mem_maximalIdeal_iff w' (sub_mem hxmem htmem)).mp ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsub : (⟨algebraMap F F' x - algebraMap K' F' t, sub_mem hxmem htmem⟩ :
      w'.toValuationSubring) =
      ⟨algebraMap F F' x, hxmem⟩ - algebraMap K' w'.toValuationSubring t := by
    ext; simp [Place.coe_algebraMap]
  rw [hsub, map_sub, ← ht, sub_eq_zero, IsScalarTower.algebraMap_apply K' w'.toValuationSubring
    w'.ResidueField]
  rfl

private theorem IsGeneric.not_mem_range [CharZero K] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {w' : Place K' F'} (hw : IsGeneric K F w') {t : K'}
    (ht : InMax w' (algebraMap F F' x - algebraMap K' F' t)) :
    t ∉ Set.range (algebraMap K K') := by
  rintro ⟨c, rfl⟩
  have heq : algebraMap F F' x - algebraMap K' F' (algebraMap K K' c) =
      algebraMap F F' (x - algebraMap K F c) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [heq] at ht
  have hne : x - algebraMap K F c ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hx (h ▸ isAlgebraic_algebraMap c)
  rcases ht with h | h
  · exact hne ((map_eq_zero_iff _ (algebraMap F F').injective).mp h)
  · rw [hw.ord_algebraMap x] at h
    exact lt_irrefl _ h

end Tower

private theorem transcendental_of_not_mem_range [Algebra K K'] [IsAlgClosed K] {t : K'}
    (ht : t ∉ Set.range (algebraMap K K')) : Transcendental K t := by
  intro halg
  have hint : IsIntegral K t := halg.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  exact ht (minpoly.mem_range_of_degree_eq_one K t hdeg)

end Extension

section DerivationExistence

open scoped IntermediateField
open KaehlerDifferential MvPolynomial

set_option linter.style.haveILetI false in
private theorem exists_derivation_apply_eq_one (K K' : Type*) [Field K] [Field K'] [Algebra K K']
    [CharZero K] (t : K') (ht : Transcendental K t) :
    ∃ δ : Derivation K K' K', δ t = 1 := by
  classical

  have hind : AlgebraicIndepOn K id ({t} : Set K') :=
    (algebraicIndependent_singleton_iff (R := K) (x := fun i : ({t} : Set K') => (id (i : K')))
      ⟨t, Set.mem_singleton t⟩).mpr ht
  obtain ⟨B, htB, hB⟩ := exists_isTranscendenceBasis_superset hind
  set L : IntermediateField K K' := IntermediateField.adjoin K (Set.range ((↑) : B → K')) with hL
  haveI : Algebra.IsAlgebraic L K' := hB.isAlgebraic_field
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : Algebra.IsSeparable L K' := inferInstance

  let R := MvPolynomial B K
  let e : FractionRing R ≃ₐ[K] L := hB.1.aevalEquivField
  letI iRL : Algebra R L := (e.toAlgHom.toRingHom.comp (algebraMap R (FractionRing R))).toAlgebra
  letI iRK' : Algebra R K' := ((algebraMap L K').comp (algebraMap R L)).toAlgebra
  haveI : IsScalarTower R L K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgL : ∀ p : R, algebraMap R L p = e (algebraMap R (FractionRing R) p) := fun _ => rfl
  have halgK' : ∀ p : R, algebraMap R K' p = ((e (algebraMap R (FractionRing R) p) : L) : K') :=
    fun _ => rfl
  have halgK'' : ∀ p : R, algebraMap R K' p = MvPolynomial.aeval ((↑) : B → K') p := by
    intro p
    rw [halgK', AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  haveI : IsScalarTower K R K' := IsScalarTower.of_algebraMap_eq fun k => by
    rw [halgK'', MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
  haveI : IsScalarTower K R L := IsScalarTower.of_algebraMap_eq fun k => by
    apply Subtype.ext
    rw [show ((algebraMap K L k : L) : K') = algebraMap K K' k from rfl,
      show ((algebraMap R L (algebraMap K R k) : L) : K')
      = algebraMap R K' (algebraMap K R k) from rfl, halgK'', MvPolynomial.algebraMap_eq,
      MvPolynomial.aeval_C]

  let e' : FractionRing R ≃ₐ[R] L :=
    AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (fun p => rfl)
  haveI : IsFractionRing R L :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors R) e'
  haveI : Algebra.FormallyEtale R L :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := L) (nonZeroDivisors R)
  haveI : Algebra.FormallyEtale L K' := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale R K' := Algebra.FormallyEtale.comp R L K'

  let t₀ : B := ⟨t, htB (Set.mem_singleton t)⟩
  let D₁ : Derivation K R K' := (Algebra.linearMap R K').compDer (MvPolynomial.pderiv t₀)
  have hD₁ : ∀ p : R, D₁ p = algebraMap R K' (MvPolynomial.pderiv t₀ p) := fun _ => rfl

  have hBC := KaehlerDifferential.isBaseChange_of_formallyEtale K R K'
  let Φ : Ω[K'⁄K] →ₗ[K'] K' := hBC.lift D₁.liftKaehlerDifferential
  have hΦ : ∀ p : R, Φ (KaehlerDifferential.D K K' (algebraMap R K' p)) = D₁ p := by
    intro p
    rw [← KaehlerDifferential.map_D K K R K' p]
    show hBC.lift D₁.liftKaehlerDifferential _ = _
    rw [hBC.lift_eq, Derivation.liftKaehlerDifferential_comp_D]
  let δ : Derivation K K' K' := Φ.compDer (KaehlerDifferential.D K K')
  have hδalg : ∀ p : R, δ (algebraMap R K' p) = D₁ p := fun p => hΦ p
  refine ⟨δ, ?_⟩
  have hX : algebraMap R K' (MvPolynomial.X t₀) = t := by
    rw [halgK'', MvPolynomial.aeval_X]
  calc δ t = δ (algebraMap R K' (MvPolynomial.X t₀)) := by rw [hX]
    _ = D₁ (MvPolynomial.X t₀) := hδalg _
    _ = 1 := by rw [hD₁, MvPolynomial.pderiv_X_self, map_one]

end DerivationExistence

section LocalCalc

variable {R K F : Type*} [CommRing R] [Field K] [Field F] [Algebra K F] [Algebra R F]

private theorem leibniz_zpow (D : Derivation R F F) {a : F} (ha : a ≠ 0) (k : ℤ) :
    D (a ^ k) = (k : F) * a ^ (k - 1) * D a := by
  rcases k with n | n
  ·
    rw [Int.ofNat_eq_natCast, zpow_natCast, D.leibniz_pow, nsmul_eq_mul, smul_eq_mul,
      Int.cast_natCast]
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel, show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring, zpow_natCast]
      ring
  · rw [zpow_negSucc, D.leibniz_inv, D.leibniz_pow, Int.negSucc_sub_one, zpow_negSucc,
      Int.cast_negSucc, Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, smul_eq_mul]
    have hp : a ^ (n + 1) ≠ 0 := pow_ne_zero _ ha
    have hp' : a ^ (n + 1 + 1) ≠ 0 := pow_ne_zero _ ha
    field_simp
    push_cast
    ring

variable (w : Place K F)

private theorem ne_zero_of_ord_ne_zero {f : F} (hf : w.ord f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact hf (Place.ord_zero w)

private theorem mem_of_ord_eq_zero {u : F} (hu0 : u ≠ 0) (hu : w.ord u = 0) :
    u ∈ w.toValuationSubring :=
  (Place.mem_iff_ord_nonneg w hu0).mpr hu.ge

private theorem ord_nonneg_of_mem {f : F} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · exact (Place.mem_iff_ord_nonneg w hf0).mp hf

private theorem ord_intCast (k : ℤ) : w.ord (k : F) = 0 := by
  rw [show (k : F) = algebraMap K F (k : K) by rw [map_intCast]]
  exact Place.ord_algebraMap w _

private theorem ord_natCast (k : ℕ) : w.ord (k : F) = 0 := by
  rw [show (k : F) = algebraMap K F (k : K) by rw [map_natCast]]
  exact Place.ord_algebraMap w _

private theorem le_ord_add {a b : F} {m : ℤ} (ha : a = 0 ∨ m ≤ w.ord a) (hb : b = 0 ∨ m ≤ w.ord b)
    (hab : a + b ≠ 0) : m ≤ w.ord (a + b) := by
  rcases ha with rfl | ha
  · rw [zero_add] at hab ⊢
    exact hb.resolve_left hab
  rcases hb with rfl | hb
  · rw [add_zero]
    exact ha
  by_cases ha0 : a = 0
  · rw [ha0, zero_add] at hab ⊢; exact hb
  by_cases hb0 : b = 0
  · rw [hb0, add_zero]; exact ha
  exact (le_min ha hb).trans (Place.min_ord_le_ord_add w hab)

private theorem ord_sub_le_ord_apply (D : Derivation R F F)
    (hD : ∀ z ∈ w.toValuationSubring, D z ∈ w.toValuationSubring)
    {π : F} (hπ : w.ord π = 1) {c : ℤ} (hc : 0 ≤ c) (hπD : D π = 0 ∨ 1 - c ≤ w.ord (D π))
    {f : F} (hf : f ≠ 0) (hDf : D f ≠ 0) : w.ord f - c ≤ w.ord (D f) := by
  have hπ0 : π ≠ 0 := ne_zero_of_ord_ne_zero w (by rw [hπ]; exact one_ne_zero)
  set k : ℤ := w.ord f with hk
  have hπk : π ^ k ≠ 0 := zpow_ne_zero k hπ0
  have hπk1 : π ^ (k - 1) ≠ 0 := zpow_ne_zero _ hπ0
  set u : F := f * (π ^ k)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hf (inv_ne_zero hπk)
  have hordu : w.ord u = 0 := by
    rw [hu, Place.ord_mul _ hf (inv_ne_zero hπk), Place.ord_inv, Place.ord_zpow, hπ, mul_one, ← hk]
    ring
  have humem : u ∈ w.toValuationSubring := mem_of_ord_eq_zero w hu0 hordu
  have hDu : D u ∈ w.toValuationSubring := hD u humem
  have hfu : f = u * π ^ k := by
    rw [hu, inv_mul_cancel_right₀ hπk]

  have hDf_eq : D f = π ^ k * D u + u * ((k : F) * π ^ (k - 1) * D π) := by
    conv_lhs => rw [hfu]
    rw [D.leibniz, leibniz_zpow D hπ0 k, smul_eq_mul, smul_eq_mul, add_comm]

  have hT1 : π ^ k * D u = 0 ∨ k - c ≤ w.ord (π ^ k * D u) := by
    by_cases hDu0 : D u = 0
    · left; rw [hDu0, mul_zero]
    · right
      rw [Place.ord_mul _ hπk hDu0, Place.ord_zpow, hπ, mul_one]
      have := ord_nonneg_of_mem w hDu
      linarith
  have hT2 : u * ((k : F) * π ^ (k - 1) * D π) = 0 ∨
      k - c ≤ w.ord (u * ((k : F) * π ^ (k - 1) * D π)) := by
    by_cases hz : (k : F) * π ^ (k - 1) * D π = 0
    · left; rw [hz, mul_zero]
    · right
      have hDπ0 : D π ≠ 0 := fun h => hz (by rw [h, mul_zero])
      have hk0 : (k : F) ≠ 0 := fun h => hz (by rw [h, zero_mul, zero_mul])
      have hbound : 1 - c ≤ w.ord (D π) := hπD.resolve_left hDπ0
      rw [Place.ord_mul _ hu0 hz, Place.ord_mul _ (mul_ne_zero hk0 hπk1) hDπ0,
        Place.ord_mul _ hk0 hπk1, hordu, ord_intCast, Place.ord_zpow, hπ, mul_one]
      linarith
  rw [hDf_eq] at hDf ⊢
  exact le_ord_add w hT1 hT2 hDf

private theorem exists_ord_eq_one : ∃ π : F, w.ord π = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  exact ⟨π, w.ord_coe_irreducible hπ⟩

private theorem ord_le_ord_apply_of_eigen [CharZero F] (D : Derivation R F F)
    (hD : ∀ z ∈ w.toValuationSubring, D z ∈ w.toValuationSubring)
    {φ : F} (hφ0 : φ ≠ 0) (hφ : 0 < w.ord φ) {a : F} (ha : a ∈ w.toValuationSubring)
    (hDφ : D φ = a * φ)
    {z : F} (hz0 : z ≠ 0) (hz : 0 < w.ord z) (hDz : D z ≠ 0) : w.ord z ≤ w.ord (D z) := by

  set k : ℕ := (w.ord φ).toNat with hk
  set m : ℕ := (w.ord z).toNat with hm
  have hkz : (k : ℤ) = w.ord φ := Int.toNat_of_nonneg hφ.le
  have hmz : (m : ℤ) = w.ord z := Int.toNat_of_nonneg hz.le
  have hk1 : 1 ≤ k := by
    have : (1 : ℤ) ≤ k := by rw [hkz]; exact hφ
    exact_mod_cast this
  have hm1 : 1 ≤ m := by
    have : (1 : ℤ) ≤ m := by rw [hmz]; exact hz
    exact_mod_cast this
  have hφm : φ ^ m ≠ 0 := pow_ne_zero _ hφ0
  have hzk : z ^ k ≠ 0 := pow_ne_zero _ hz0

  set u : F := z ^ k * (φ ^ m)⁻¹ with hu
  have hu0 : u ≠ 0 := mul_ne_zero hzk (inv_ne_zero hφm)
  have hordu : w.ord u = 0 := by
    rw [hu, Place.ord_mul _ hzk (inv_ne_zero hφm), Place.ord_inv, ← zpow_natCast, ← zpow_natCast,
      Place.ord_zpow, Place.ord_zpow, ← hkz, ← hmz]
    ring
  have humem : u ∈ w.toValuationSubring := mem_of_ord_eq_zero w hu0 hordu
  have hDu : D u ∈ w.toValuationSubring := hD u humem
  have hzu : z ^ k = u * φ ^ m := by rw [hu, inv_mul_cancel_right₀ hφm]

  have hL : D (z ^ k) = (k : F) * z ^ (k - 1) * D z := by
    rw [D.leibniz_pow, nsmul_eq_mul, smul_eq_mul, mul_assoc]
  have hR : D (u * φ ^ m) = ((m : F) * a * u + D u) * φ ^ m := by
    rw [D.leibniz, D.leibniz_pow, hDφ, smul_eq_mul, smul_eq_mul, nsmul_eq_mul, smul_eq_mul]
    have hpow : φ ^ (m - 1) * φ = φ ^ m := by
      rw [← pow_succ, Nat.sub_add_cancel hm1]
    calc u * ((m : F) * (φ ^ (m - 1) * (a * φ))) + φ ^ m * D u
        = (m : F) * a * u * (φ ^ (m - 1) * φ) + D u * φ ^ m := by ring
      _ = ((m : F) * a * u + D u) * φ ^ m := by rw [hpow]; ring
  have hEq : (k : F) * z ^ (k - 1) * D z = ((m : F) * a * u + D u) * φ ^ m := by
    rw [← hL, ← hR, hzu]

  have hk0 : (k : F) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hzk1 : z ^ (k - 1) ≠ 0 := pow_ne_zero _ hz0
  have hLne : (k : F) * z ^ (k - 1) * D z ≠ 0 := mul_ne_zero (mul_ne_zero hk0 hzk1) hDz
  have hcoef : (m : F) * a * u + D u ≠ 0 := by
    intro h
    rw [h, zero_mul] at hEq
    exact hLne hEq
  have hcoef_mem : (m : F) * a * u + D u ∈ w.toValuationSubring :=
    add_mem (mul_mem (mul_mem (by
      rw [show ((m : ℕ) : F) = algebraMap K F (m : K) by rw [map_natCast]]
      exact w.algebraMap_mem' _) ha) humem) hDu
  have hcoef_ord : 0 ≤ w.ord ((m : F) * a * u + D u) := ord_nonneg_of_mem w hcoef_mem

  have hordL : w.ord ((k : F) * z ^ (k - 1) * D z) = ((k : ℤ) - 1) * w.ord z + w.ord (D z) := by
    rw [Place.ord_mul _ (mul_ne_zero hk0 hzk1) hDz, Place.ord_mul _ hk0 hzk1, ord_natCast,
      ← zpow_natCast, Place.ord_zpow, Nat.cast_sub hk1]
    push_cast
    ring
  have hordR : w.ord (((m : F) * a * u + D u) * φ ^ m) =
      w.ord ((m : F) * a * u + D u) + (m : ℤ) * w.ord φ := by
    rw [Place.ord_mul _ hcoef hφm, ← zpow_natCast, Place.ord_zpow]
  have key : ((k : ℤ) - 1) * w.ord z + w.ord (D z) =
      w.ord ((m : F) * a * u + D u) + (m : ℤ) * w.ord φ := by
    rw [← hordL, ← hordR, hEq]
  rw [← hkz, ← hmz] at key
  rw [← hmz]
  nlinarith [key, hcoef_ord, hk1, hm1]

end LocalCalc

section Main

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
  [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

set_option linter.style.haveILetI false in
private theorem main [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') := by
  classical
  obtain ⟨x, hx, hxfd⟩ := id hfg
  obtain ⟨x', hx', hxfd'⟩ := id hfg'
  haveI := hxfd
  haveI := hxfd'
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : CharZero F' := charZero_of_injective_algebraMap (algebraMap K' F').injective
  obtain ⟨g', hg'0, hg'⟩ := hD'
  have hnD' : (n : ℤ) • D' = divOf g' := by
    ext w
    rw [Finsupp.smul_apply, smul_eq_mul, hg' w, divOf_apply hg'0 w]

  have hlift := Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F K' F' hfg hfg' hgen
  choose lift hliftOver hliftOrd hliftUniq using hlift
  have hU : ∀ (v : Place K F) (w₁ w₂ : Place K' F'), LiesOver w₁ v → LiesOver w₂ v → w₁ = w₂ :=
    fun v w₁ w₂ h₁ h₂ => (hliftUniq v w₁ h₁).trans (hliftUniq v w₂ h₂).symm
  have hV : ∀ (w' : Place K' F') (v₁ v₂ : Place K F), LiesOver w' v₁ → LiesOver w' v₂ → v₁ = v₂ :=
    fun w' v₁ v₂ h₁ h₂ => Place.ext (h₁.symm.trans h₂)

  obtain ⟨P, -⟩ := Place.exists_ord_neg_of_transcendental x hx
  set P₀ : Place K' F' := lift P with hP₀def
  have hP₀ : LiesOver P₀ P := hliftOver P
  have hdegP₀ : P₀.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed P₀

  set d : ℤ := Divisor.degree D' with hd
  set c₀ : Divisor K' F' := D' - d • Finsupp.single P₀ 1 with hc₀
  have hc₀deg : Divisor.degree c₀ = 0 := by
    simp only [hc₀, map_sub, map_zsmul, Divisor.degree_single, hdegP₀, Nat.cast_one, mul_one,
      smul_eq_mul, hd]
    ring
  obtain ⟨r, fr, hfr0, hfrmem, hfruniq⟩ := exists_reduced (K := K') (F := F') x' hx' c₀ hc₀deg P₀
  set A : Divisor K' F' := c₀ + (r : ℤ) • Finsupp.single P₀ 1 + divOf fr with hA
  have hA0w : ∀ w : Place K' F', 0 ≤ A w := divOf_add_mem_lSpace hfr0 hfrmem

  set φ : F' := g' * fr ^ n with hφ
  have hφ0 : φ ≠ 0 := mul_ne_zero hg'0 (pow_ne_zero _ hfr0)
  have hφdiv : divOf φ = (n : ℤ) • A - ((n : ℤ) * ((r : ℤ) - d)) • Finsupp.single P₀ 1 := by
    rw [hφ, divOf_mul hg'0 (pow_ne_zero _ hfr0), divOf_pow, ← hnD']
    simp only [hA, hc₀]
    module
  have hordφ : ∀ w : Place K' F',
      w.ord φ = (n : ℤ) * A w - (n : ℤ) * ((r : ℤ) - d) * Finsupp.single P₀ (1 : ℤ) w := by
    intro w
    have := congrArg (fun E : Divisor K' F' => E w) hφdiv
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, divOf_apply hφ0 w] at this
    rw [this, mul_assoc]
  have hordφ_gen : ∀ w : Place K' F', IsGeneric K F w → w.ord φ = (n : ℤ) * A w := by
    intro w hw
    have hsP₀ : Finsupp.single P₀ (1 : ℤ) w = 0 := by
      rw [Finsupp.single_apply, ite_eq_right]
      rintro rfl
      exact hw P hP₀
    rw [hordφ, hsP₀, mul_zero, sub_zero]

  have hAsupp : ∀ w' ∈ A.support, ¬ IsGeneric K F w' := by
    intro w' hw' hgw

    obtain ⟨t, ht⟩ := hgw.exists_inMax_sub x
    have htK : t ∉ Set.range (algebraMap K K') := hgw.not_mem_range x hx ht
    have httr : Transcendental K t := transcendental_of_not_mem_range htK
    obtain ⟨δ, hδt⟩ := exists_derivation_apply_eq_one K K' t httr

    obtain ⟨Dd, hDF, hDE, hDreg⟩ :=
      exists_derivation_constantFieldExtension_map_mem K F K' F' hfg hfg' hgen δ

    set y : F' := Dd φ * φ⁻¹ with hy
    have hymem : y ∈ LSpace A := by
      rw [mem_lSpace_iff_ord]
      rcases eq_or_ne y 0 with hy0 | hy0
      · exact Or.inl hy0
      right
      intro w
      have hDφ0 : Dd φ ≠ 0 := by
        intro h; apply hy0; rw [hy, h, zero_mul]
      have hordy : w.ord y = w.ord (Dd φ) - w.ord φ := by
        rw [hy, Place.ord_mul _ hDφ0 (inv_ne_zero hφ0), Place.ord_inv]; ring
      by_cases hgen_w : IsGeneric K F w
      ·
        obtain ⟨π, hπ⟩ := exists_ord_eq_one w
        have hπ0 : π ≠ 0 := ne_zero_of_ord_ne_zero w (by rw [hπ]; exact one_ne_zero)
        have hπmem : π ∈ w.toValuationSubring :=
          (Place.mem_iff_ord_nonneg w hπ0).mpr (by rw [hπ]; exact zero_le_one)
        have hDπ : Dd π = 0 ∨ 1 - 1 ≤ w.ord (Dd π) := by
          by_cases h : Dd π = 0
          · exact Or.inl h
          · right
            rw [sub_self]
            exact ord_nonneg_of_mem w (hDreg w π hπmem)
        have h1 : w.ord φ - 1 ≤ w.ord (Dd φ) :=
          ord_sub_le_ord_apply w Dd (fun z hz => hDreg w z hz) hπ zero_le_one hDπ hφ0 hDφ0
        have hordφw : w.ord φ = (n : ℤ) * A w := hordφ_gen w hgen_w
        by_cases hAw : A w = 0
        · have hφmem : φ ∈ w.toValuationSubring :=
            (Place.mem_iff_ord_nonneg w hφ0).mpr (by rw [hordφw, hAw, mul_zero])
          have h2 := ord_nonneg_of_mem w (hDreg w φ hφmem)
          rw [hordy, hordφw, hAw]
          linarith
        · have hAw1 : 1 ≤ A w := by
            have := hA0w w
            omega
          rw [hordy]
          linarith
      ·
        simp only [IsGeneric, not_forall, not_not] at hgen_w
        obtain ⟨v, hv⟩ := hgen_w
        have hw : w = lift v := hU v w (lift v) hv (hliftOver v)
        obtain ⟨π₀, hπ₀⟩ := exists_ord_eq_one v
        have hπ : w.ord (algebraMap F F' π₀) = 1 := by rw [hw, hliftOrd, hπ₀]
        have hDπ : Dd (algebraMap F F' π₀) = 0 ∨ 1 - 0 ≤ w.ord (Dd (algebraMap F F' π₀)) :=
          Or.inl (hDF π₀)
        have h1 : w.ord φ - 0 ≤ w.ord (Dd φ) :=
          ord_sub_le_ord_apply w Dd (fun z hz => hDreg w z hz) hπ le_rfl hDπ hφ0 hDφ0
        have h2 := hA0w w
        rw [hordy]
        linarith

    have hyfr : y * fr ∈ LSpace (c₀ + (r : ℤ) • Finsupp.single P₀ 1) := by
      rw [hA] at hymem
      exact (mem_lSpace_add_divOf_iff hfr0).mp hymem
    obtain ⟨a, ha⟩ := hfruniq _ hyfr
    have hya : y = algebraMap K' F' a := by
      rw [Algebra.smul_def] at ha
      exact (mul_left_injective₀ hfr0 ha).symm
    have hDφ : Dd φ = algebraMap K' F' a * φ := by
      rw [← hya, hy, inv_mul_cancel_right₀ hφ0]

    have hAw' : 1 ≤ A w' := by
      have h1 := hA0w w'
      have h2 : A w' ≠ 0 := Finsupp.mem_support_iff.mp hw'
      omega
    have hn1 : (1 : ℤ) ≤ n := by
      have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      exact_mod_cast this
    have hφpos : 0 < w'.ord φ := by
      rw [hordφ_gen w' hgw]
      nlinarith

    have hDy₀ : Dd (algebraMap F F' x - algebraMap K' F' t) = -1 := by
      rw [map_sub, hDF, hDE, hδt, map_one, zero_sub]
    rcases ht with hy00 | hy0pos
    · rw [hy00, map_zero] at hDy₀
      norm_num at hDy₀
    · have hy0ne : algebraMap F F' x - algebraMap K' F' t ≠ 0 := by
        intro h
        rw [h, Place.ord_zero] at hy0pos
        exact lt_irrefl _ hy0pos
      have hDy₀ne : Dd (algebraMap F F' x - algebraMap K' F' t) ≠ 0 := by
        rw [hDy₀]; norm_num
      have key := ord_le_ord_apply_of_eigen w' Dd (fun z hz => hDreg w' z hz) hφ0 hφpos
        (w'.algebraMap_mem' a) hDφ hy0ne hy0pos hDy₀ne
      rw [hDy₀, show (-1 : F') = algebraMap K' F' (-1) by simp, Place.ord_algebraMap] at key
      exact absurd key (not_le.mpr hy0pos)

  set B : Divisor K' F' := A + (d - r) • Finsupp.single P₀ 1 with hB
  have hBsupp : ∀ w' ∈ B.support, ∃ v : Place K F, LiesOver w' v := by
    intro w' hw'
    rcases Finset.mem_union.mp (Finsupp.support_add hw') with h | h
    · have := hAsupp w' h
      simp only [IsGeneric, not_forall, not_not] at this
      exact this
    · have h2 := Finsupp.support_smul h
      rw [Finsupp.mem_support_single] at h2
      exact ⟨P, h2.1 ▸ hP₀⟩
  have hD'B : D' = B + divOf fr⁻¹ := by
    rw [divOf_inv]
    simp only [hB, hA, hc₀, sub_smul]
    abel
  let π : Place K' F' → Place K F := fun w' =>
    if h : ∃ v : Place K F, LiesOver w' v then h.choose else P
  have hπ : ∀ (w' : Place K' F') (v : Place K F), LiesOver w' v → π w' = v := by
    intro w' v h
    have hex : ∃ v : Place K F, LiesOver w' v := ⟨v, h⟩
    simp only [π, dite_eq_left hex]
    exact hV w' _ _ hex.choose_spec h
  set R₀ : Divisor K F := Finsupp.mapDomain π B with hR₀
  have hR₀v : ∀ v : Place K F, R₀ v = B (lift v) := by
    intro v
    have hS : ((B.support : Finset (Place K' F')) : Set (Place K' F')) ⊆
        {w' : Place K' F' | ∃ v : Place K F, LiesOver w' v} := fun w' hw' => hBsupp w' hw'
    have hinjOn : Set.InjOn π {w' : Place K' F' | ∃ v : Place K F, LiesOver w' v} := by
      rintro w₁ ⟨v₁, h₁⟩ w₂ ⟨v₂, h₂⟩ heq
      rw [hπ w₁ v₁ h₁, hπ w₂ v₂ h₂] at heq
      subst heq
      exact hU v₁ w₁ w₂ h₁ h₂
    have := Finsupp.mapDomain_apply' _ B hS hinjOn (a := lift v) ⟨v, hliftOver v⟩
    rwa [hπ (lift v) v (hliftOver v)] at this
  have hB0 : ∀ w' : Place K' F', (∀ v : Place K F, ¬ LiesOver w' v) → B w' = 0 := by
    intro w' hw'
    by_contra hne
    obtain ⟨v, hv⟩ := hBsupp w' (Finsupp.mem_support_iff.mpr hne)
    exact hw' v hv

  have hprin : ((n : ℤ) • R₀).IsPrincipal := by
    apply Divisor.isPrincipal_of_constantFieldExtension K F K' F' hfg hfg' hgen
      ((n : ℤ) • R₀) ((n : ℤ) • B)
    · intro w' v hw'v
      have hw : w' = lift v := hU v w' (lift v) hw'v (hliftOver v)
      simp only [Finsupp.smul_apply, smul_eq_mul]
      rw [hR₀v v, hw]
    · intro w' hw'
      simp only [Finsupp.smul_apply, smul_eq_mul, hB0 w' hw', mul_zero]
    · refine isPrincipal_iff_eq_divOf.mpr ⟨g' * fr ^ n, mul_ne_zero hg'0 (pow_ne_zero _ hfr0), ?_⟩
      rw [divOf_mul hg'0 (pow_ne_zero _ hfr0), divOf_pow, ← hnD']
      have : B = D' + divOf fr := by
        rw [hD'B, divOf_inv]
        abel
      rw [this, smul_add]
  obtain ⟨g, hg0, hg⟩ := hprin
  refine ⟨R₀, fr⁻¹, inv_ne_zero hfr0, ⟨g, hg0, fun v => ?_⟩, fun v v' hv' => ?_, fun v' hv' => ?_⟩
  · have := hg v
    simpa only [Finsupp.smul_apply, smul_eq_mul] using this
  · have hw : v' = lift v := hU v v' (lift v) hv' (hliftOver v)
    rw [hD'B, Finsupp.add_apply, divOf_apply (inv_ne_zero hfr0) v', hw, hR₀v v]
  · rw [hD'B, Finsupp.add_apply, divOf_apply (inv_ne_zero hfr0) v', hB0 v' hv', zero_add]

end Main

end TorsionDescentDeriv

/-- **Descent of an `n`-torsion divisor class along a constant-field extension.**  From
`n · D' = div g'` on `F' = K'·F` one gets `D` on `F`, `g` on `F` with `n · D = div g`,
and the correction `h'` that accounts for `D'` off the places of `F`.  The pin's
`AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension` (878 ln). -/
theorem Divisor.exists_torsion_descent_of_constantFieldExtension
    (K F K' F' : Type*) [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D' : Divisor K' F')
    (hD' : ∃ g' : F', g' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) * D' v' = v'.ord g') :
    ∃ (D : Divisor K F) (h' : F'), h' ≠ 0 ∧
      (∃ g : F, g ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) * D v = v.ord g) ∧
      (∀ (v : Place K F) (v' : Place K' F'),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          D' v' = D v + v'.ord h') ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          D' v' = v'.ord h') :=
  TorsionDescentDeriv.main (K := K) (F := F) (K' := K') (F' := F') hfg hfg' hgen n hn D' hD'

/-! ## The index of specialty of a lifted divisor

`AlgebraicCurve.exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed`,
after `P2M/Sol/S_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed.lean`
(99 ln) and its `Theorems/` wrapper.  The pin's engine `W7XChildE.constantsAreBase` is the
same `ConstantsAreBase` statement this module already proves privately for `isAlgClosed` at
`TorsionDescentDeriv.constantsAreBase_of_isAlgClosed`; rather than repeat the block, the
node below re-derives the pin's `hfg`-shaped binder from that same-file helper. -/

namespace W7XChildE

set_option linter.style.haveILetI false in
private theorem constantsAreBase {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ConstantsAreBase K F := by
  obtain ⟨x, hx, hxfin⟩ := hfg
  haveI := hxfin
  exact TorsionDescentDeriv.constantsAreBase_of_isAlgClosed (K := K) (F := F) x hx

end W7XChildE

set_option linter.unusedVariables false in
set_option linter.style.haveILetI false in
/-- **The index of specialty of a lifted divisor vanishes.**  Verbatim from
`Theorems/Thm_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed.lean`:
over algebraically closed `K, K'`, some divisor of `F`, pushed to `F'` along an
order-preserving injective `lift`, has index of specialty zero. -/
theorem exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift) :
    ∃ D : Divisor K F, indexOfSpecialty (K := K') (Finsupp.mapDomain lift D) = 0 := by
  classical

  obtain ⟨x, hxt, hxfd⟩ := id hfg
  obtain ⟨x', hxt', hxfd'⟩ := id hfg'
  haveI : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt hxfd
  haveI : Algebra.EssFiniteType K' F' :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt' hxfd'
  have hCAB : ConstantsAreBase K F := W7XChildE.constantsAreBase hfg
  have hCAB' : ConstantsAreBase K' F' := W7XChildE.constantsAreBase hfg'

  obtain ⟨hne, hfd0, γ, D₀, hD₀⟩ := stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hCAB
  obtain ⟨hne', hfd0', γ', D₀', hD₀'⟩ :=
    stichtenothGenusExists_of_isCurveOver (K := K') (F := F') hCAB'
  haveI := hne; haveI := hfd0; haveI := hne'; haveI := hfd0'

  obtain ⟨P₀⟩ := hne

  obtain ⟨n, hRGA⟩ :=
    exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists hD₀' (lift P₀)

  refine ⟨Finsupp.single P₀ (n : ℤ), ?_⟩
  have hmap : (Finsupp.mapDomain lift (Finsupp.single P₀ (n : ℤ)) : Divisor K' F')
      = (n : ℤ) • Finsupp.single (lift P₀) (1 : ℤ) := by
    rw [Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hmap]
  exact indexOfSpecialty_eq_zero_of_genusReached hRGA

/-! ## The order of the torsion of `Pic⁰`

`AlgebraicCurve.Pic0.natCard_torsion_eq_of_constantFieldExtension`, after
`P2M/Sol/S_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension.lean` (541 ln)
and its `Theorems/` wrapper: a constant-field extension `K ⊆ K'` preserves the order of
the `n`-torsion of `Pic⁰`, `#Pic⁰[n](K'·F) = #Pic⁰[n](F)` (the `p^{2g}` statement).

The pin's engine `W7XL2` is private here; the port takes its `ord` prelude
(`ord_eq_zero_of_mem_of_inv_mem`, `ord_algebraMap_base`) and
`linearIndependent_pow_of_transcendental` from the already-ported blocks
`Place/ConstantFieldExtension.lean`, `P1/EnginePrelude.lean` and
`IsCurveOver/ConstantFieldExtensionSpan.lean` instead of repeating them, as the pin's
`S_` files do. -/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Polynomial

open scoped IntermediateField

namespace W7XL2

private theorem linearIndependent_adjoin_simple_of_pow_mul {K' L : Type*} [Field K'] [Field L]
    [Algebra K' L] (x : L) {ι : Type*} (u : ι → L)
    (h : LinearIndependent K' fun p : ℕ × ι => x ^ p.1 * u p.2) :
    LinearIndependent (IntermediateField.adjoin K' ({x} : Set L)) u := by
  classical
  -- Clear denominators over `K'⟮x⟯`: every element of `K'⟮x⟯` is `p(x) / q(x)`.
  have key : ∀ l : K'⟮x⟯, ∃ p q : K'[X], aeval x q ≠ 0 ∧ (l : L) * aeval x q = aeval x p := by
    intro l
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K' (l : L)).mp l.2
    by_cases hs : aeval x s = 0
    · exact ⟨0, 1, by simp, by rw [hrs, hs, div_zero, zero_mul, map_zero]⟩
    · exact ⟨r, s, hs, by rw [hrs, div_mul_cancel₀ _ hs]⟩
  rw [linearIndependent_iff'] at h ⊢
  intro s g hg i hi
  choose p q hq hpq using fun j => key (g j)
  set Q : K'[X] := ∏ j ∈ s, q j with hQ
  have hQ0 : aeval x Q ≠ 0 := by
    rw [hQ, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j hj => hq j
  let P : ι → K'[X] := fun j => p j * ∏ k ∈ s.erase j, q k
  have hP : ∀ j ∈ s, ((g j : K'⟮x⟯) : L) * aeval x Q = aeval x (P j) := by
    intro j hj
    rw [hQ, ← Finset.mul_prod_erase s q hj, map_mul, ← mul_assoc, hpq j, ← map_mul]
  have hrelL : ∑ j ∈ s, ((g j : K'⟮x⟯) : L) * u j = 0 := by
    have := hg
    simpa [IntermediateField.smul_def, smul_eq_mul] using this
  have hrelQ : ∑ j ∈ s, aeval x (P j) * u j = 0 := by
    have := congrArg (fun z : L => z * aeval x Q) hrelL
    simp only [zero_mul, Finset.sum_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hP j hj]; ring
  set N : ℕ := (s.sup fun j => (P j).natDegree) + 1 with hN
  have hdeg : ∀ j ∈ s, (P j).natDegree < N := fun j hj =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (P j).natDegree) hj)
  have hkey := h (Finset.range N ×ˢ s) (fun q => (P q.2).coeff q.1) ?_
  swap
  · rw [← hrelQ, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [aeval_eq_sum_range' (hdeg j hj), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [smul_mul_assoc]
  have hPi : P i = 0 := by
    ext k
    by_cases hk : k < N
    · simpa using hkey (k, i) (Finset.mk_mem_product (Finset.mem_range.mpr hk) hi)
    · rw [coeff_zero]
      exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i hi) (not_lt.mp hk))
  have h1 := hP i hi
  rw [hPi, map_zero, mul_eq_zero] at h1
  rcases h1 with h2 | h2
  · exact Subtype.ext h2
  · exact absurd h2 hQ0

private theorem algebraMap_mem_adjoin_simple {K A K' B : Type*} [Field K] [Field A] [Field K'] [Field B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
    [Algebra K' B] [Algebra K K'] [IsScalarTower K K' B] (x : A)
    {e : A} (he : e ∈ IntermediateField.adjoin K ({x} : Set A)) :
    algebraMap A B e ∈ IntermediateField.adjoin K' ({algebraMap A B x} : Set B) := by
  have hle : (IntermediateField.adjoin K ({x} : Set A)).map (IsScalarTower.toAlgHom K A B) ≤
      (IntermediateField.adjoin K' ({algebraMap A B x} : Set B)).restrictScalars K := by
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact IntermediateField.mem_adjoin_simple_self K' (algebraMap A B x)
  exact hle ⟨e, he, rfl⟩

private theorem finiteDimensional_adjoin_simple_algebraMap {K A B : Type*} [Field K] [Field A] [Field B]
    [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [FiniteDimensional A B]
    (x : A) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set A)) A] :
    FiniteDimensional (IntermediateField.adjoin K ({algebraMap A B x} : Set B)) B := by
  set E := IntermediateField.adjoin K ({x} : Set A) with hE
  set E' := IntermediateField.adjoin K ({algebraMap A B x} : Set B) with hE'
  have hmap : ∀ e : E, algebraMap A B (e : A) ∈ E' := fun e =>
    algebraMap_mem_adjoin_simple (K' := K) x e.2
  let φ : E →+* E' := ((algebraMap A B).comp (algebraMap E A)).codRestrict E' hmap
  letI : Algebra E E' := φ.toAlgebra
  haveI : IsScalarTower E E' B := IsScalarTower.of_algebraMap_eq (fun e => rfl)
  haveI : Module.Finite E B := Module.Finite.trans A B
  exact Module.Finite.of_restrictScalars_finite E E' B

section KL

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

private theorem mem_range_of_pow_eq_algebraMap [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {n : ℕ} (hn : n ≠ 0) {y : F'} {g : F} (hy : y ^ n = algebraMap F F' g) :
    y ∈ (algebraMap F F').range := by
  classical
  obtain ⟨x, hx, hfin⟩ := hfg
  haveI := hfin
  set E : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hE
  have hyint : IsIntegral F y :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by rw [hy]; exact isIntegral_algebraMap)
  set S : IntermediateField F F' := IntermediateField.adjoin F ({y} : Set F') with hS
  haveI : FiniteDimensional F S := IntermediateField.adjoin.finiteDimensional hyint
  set x' : F' := algebraMap F F' x with hx'
  set E' : IntermediateField K' F' := IntermediateField.adjoin K' ({x'} : Set F') with hE'
  set m := Module.finrank E F with hm_def
  set d := Module.finrank F S with hd_def
  let bF := Module.finBasis E F
  let bS := Module.finBasis F S
  have hm : 0 < m := Module.finrank_pos
  haveI i2 : IsScalarTower K S F' := IsScalarTower.of_algebraMap_eq (fun k => rfl)

  let xE : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  have hxEt : Transcendental K xE := by
    have : Function.Injective (algebraMap E F) := (algebraMap E F).injective
    rw [← transcendental_algebraMap_iff this]
    exact hx
  have hpow : LinearIndependent K fun k : ℕ => xE ^ k := W7XH.linearIndependent_pow_of_transcendental hxEt
  have h1 : LinearIndependent K fun q : ℕ × Fin m => (xE ^ q.1 • bF q.2 : F) :=
    linearIndependent_smul hpow bF.linearIndependent
  have h2 : LinearIndependent F fun j : Fin d => ((bS j : S) : F') :=
    bS.linearIndependent.map' S.val.toLinearMap (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hfam' : LinearIndependent K fun q : (ℕ × Fin m) × Fin d =>
      (xE ^ q.1.1 • bF q.1.2 : F) • ((bS q.2 : S) : F') := by
    exact linearIndependent_smul (R := K) (S := F) (A := F') (ι := ℕ × Fin m) (ι' := Fin d)
      (b := fun q : ℕ × Fin m => (xE ^ q.1 • bF q.2 : F)) (c := fun j => ((bS j : S) : F')) h1 h2
  have hmem : ∀ q : (ℕ × Fin m) × Fin d,
      (xE ^ q.1.1 • bF q.1.2 : F) • ((bS q.2 : S) : F') ∈ S := fun q => by
    rw [Algebra.smul_def]
    exact S.mul_mem (S.algebraMap_mem _) (bS q.2).2
  let v : (ℕ × Fin m) × Fin d → S := fun q => ⟨_, hmem q⟩
  have hfam : LinearIndependent K v :=
    LinearIndependent.of_comp (IsScalarTower.toAlgHom K S F').toLinearMap hfam'

  have hfgS : ∃ z : S, Transcendental K z ∧
      FiniteDimensional (IntermediateField.adjoin K ({z} : Set S)) S :=
    ⟨algebraMap F S x, (transcendental_algebraMap_iff (algebraMap F S).injective).mpr hx,
      finiteDimensional_adjoin_simple_algebraMap x⟩
  have hgenS : IntermediateField.adjoin K' (Set.range (algebraMap S F')) = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨f, rfl⟩
    exact IntermediateField.subset_adjoin K' _
      ⟨algebraMap F S f, (IsScalarTower.algebraMap_apply F S F' f).symm⟩
  have hW := AlgebraicCurve.linearIndependent_of_constantFieldExtension K S K' F' hfgS hfg' hgenS
    hfam
  have hW' : LinearIndependent K' fun p : ℕ × (Fin m × Fin d) =>
      x' ^ p.1 * (algebraMap F F' (bF p.2.1) * (bS p.2.2 : F')) := by
    have := hW.comp _ (Equiv.prodAssoc ℕ (Fin m) (Fin d)).symm.injective
    convert this using 1
    funext p
    simp only [Function.comp_apply, Equiv.prodAssoc_symm_apply, hx',
      IntermediateField.algebraMap_apply, Algebra.smul_def, map_mul, map_pow, v]
    ring

  set u : Fin m × Fin d → F' := fun p => algebraMap F F' (bF p.1) * (bS p.2 : F') with hu_def
  have hu : LinearIndependent E' u := linearIndependent_adjoin_simple_of_pow_mul x' u hW'

  set b' : Fin m → F' := fun i => algebraMap F F' (bF i) with hb'
  set V : Submodule E' F' := Submodule.span E' (Set.range b') with hV_def
  have hEE' : ∀ e : E, algebraMap F F' (e : F) ∈ E' := fun e =>
    algebraMap_mem_adjoin_simple (K' := K') x e.2
  have hFV : ∀ f : F, algebraMap F F' f ∈ V := by
    intro f
    rw [← bF.sum_repr f, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap F F' (bF.repr f i • bF i) =
        (⟨algebraMap F F' (bF.repr f i : F), hEE' _⟩ : E') • b' i := by
      rw [IntermediateField.smul_def, IntermediateField.smul_def, smul_eq_mul, map_mul,
        smul_eq_mul]
    rw [this]
    exact V.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hVV : V * V ≤ V := by
    rw [hV_def, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    show b' i * b' j ∈ V
    rw [hb']; dsimp only; rw [← map_mul]; exact hFV _
  have h1V : (1 : F') ∈ V := by simpa using hFV 1
  let A : Subalgebra E' F' :=
    { carrier := V
      mul_mem' := fun ha hb => hVV (Submodule.mul_mem_mul ha hb)
      one_mem' := h1V
      add_mem' := fun ha hb => V.add_mem ha hb
      zero_mem' := V.zero_mem
      algebraMap_mem' := fun e' => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem _ h1V }
  have hAfg : (Subalgebra.toSubmodule A).FG := Submodule.fg_span (Set.finite_range b')
  have hinv : ∀ z ∈ A, z⁻¹ ∈ A := fun z hz =>
    A.inv_mem_of_algebraic (x := ⟨z, hz⟩) (IsIntegral.of_mem_of_fg A hAfg z hz).isAlgebraic
  let IF : IntermediateField K' F' := (A.restrictScalars K').toIntermediateField hinv
  have hIF : IF = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_le_iff]
    rintro _ ⟨f, rfl⟩
    exact hFV f
  have hVtop : V = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ IF := hIF ▸ IntermediateField.mem_top
    exact hz
  haveI : Module.Finite E' F' := ⟨hVtop ▸ Submodule.fg_span (Set.finite_range b')⟩
  have hle : Module.finrank E' F' ≤ m := by
    have := finrank_range_le_card (R := E') b'
    unfold Set.finrank at this
    rw [← hV_def, hVtop, finrank_top, Fintype.card_fin] at this
    exact this

  have hcard := hu.fintype_card_le_finrank
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  have hd1 : d = 1 := by
    have h3 : 0 < d := Module.finrank_pos
    have h1 : m * d ≤ m * 1 := by rw [mul_one]; exact hcard.trans hle
    have h2 : d ≤ 1 := Nat.le_of_mul_le_mul_left h1 hm
    omega
  have hyb : y ∈ (⊥ : IntermediateField F F') :=
    IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hd1
  rw [IntermediateField.mem_bot] at hyb
  obtain ⟨f, hf⟩ := hyb
  exact ⟨f, hf⟩

end KL

section Transfer

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

private theorem degree_eq_zero_of_forall_eq_ord {k L : Type*} [Field k] [Field L] [Algebra k L]
    [HasPrincipalDivisors k L] {f : L} (hf : f ≠ 0) {D : Divisor k L}
    (hD : ∀ v, D v = v.ord f) : Divisor.degree D = 0 := by
  obtain ⟨E, hE, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) f hf
  have : D = E := Finsupp.ext fun v => by rw [hD, hE]
  rw [this]
  exact hdeg

private theorem mk_zsmul' {k L : Type*} [Field k] [Field L] [Algebra k L] (n : ℤ)
    (D : Divisor.degZero (K := k) (F := L)) : Pic0.mk (n • D) = n • Pic0.mk D :=
  QuotientAddGroup.mk_zsmul _ D n

private theorem mk_eq_zero_iff' {k L : Type*} [Field k] [Field L] [Algebra k L]
    (D : Divisor.degZero (K := k) (F := L)) :
    Pic0.mk D = 0 ↔ (D : Divisor k L) ∈ (Divisor.principal : AddSubgroup (Divisor k L)) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

private theorem mk_eq_mk_iff' {k L : Type*} [Field k] [Field L] [Algebra k L]
    (D E : Divisor.degZero (K := k) (F := L)) :
    Pic0.mk D = Pic0.mk E ↔
      -(D : Divisor k L) + E ∈ (Divisor.principal : AddSubgroup (Divisor k L)) := by
  unfold Pic0.mk
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  exact Iff.rfl

private theorem natCast_mul_apply_eq_of_zsmul_mem_principal {k L : Type*} [Field k] [Field L]
    [Algebra k L] {n : ℕ} {D : Divisor.degZero (K := k) (F := L)}
    (h : ((n : ℤ) • D : Divisor.degZero (K := k) (F := L)) ∈
      (Divisor.principal : AddSubgroup (Divisor k L)).addSubgroupOf Divisor.degZero) :
    ∃ g : L, g ≠ 0 ∧ ∀ v : Place k L, (n : ℤ) * (D : Divisor k L) v = v.ord g := by
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨g, hg, hDg⟩ := h
  refine ⟨g, hg, fun v => ?_⟩
  rw [← hDg v, AddSubgroupClass.coe_zsmul, Finsupp.smul_apply, smul_eq_mul]

section Lift

variable [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
  (hfg : ∃ x : F, Transcendental K x ∧
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
  (hfg' : ∃ x : F', Transcendental K' x ∧
    FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
  (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)

private noncomputable def liftPlace (P : Place K F) : Place K' F' :=
  Classical.choose
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

private theorem liftPlace_spec (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
        P.toValuationSubring ∧
      (∀ f : F, (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F', Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
        Q' = liftPlace hfg hfg' hgen P :=
  Classical.choose_spec
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

private theorem liftPlace_comap (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
      P.toValuationSubring :=
  (liftPlace_spec hfg hfg' hgen P).1

private theorem ord_liftPlace (P : Place K F) (f : F) :
    (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f :=
  (liftPlace_spec hfg hfg' hgen P).2.1 f

private theorem eq_liftPlace {P : Place K F} {Q' : Place K' F'}
    (h : Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) :
    Q' = liftPlace hfg hfg' hgen P :=
  (liftPlace_spec hfg hfg' hgen P).2.2 Q' h

private theorem liftPlace_injective :
    Function.Injective (liftPlace (K := K) (F := F) (K' := K') (F' := F') hfg hfg' hgen) := by
  intro P Q h
  apply Place.ext
  rw [← liftPlace_comap hfg hfg' hgen P, h, liftPlace_comap]

private theorem ord_algebraMap_eq_zero_of_forall_ne (w : Place K' F')
    (hw : ∀ P : Place K F, w ≠ liftPlace hfg hfg' hgen P) (f : F) :
    w.ord (algebraMap F F' f) = 0 := by
  by_contra hne
  obtain ⟨x, hx, hfin⟩ := id hfg
  haveI := hfin
  have hwK : ∀ a : K, algebraMap F F' (algebraMap K F a) ∈ w.toValuationSubring := fun a => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K K' F']
    exact w.algebraMap_mem' _
  have hwx : ∃ y : F, algebraMap F F' y ∉ w.toValuationSubring := by
    by_contra hall
    push Not at hall
    exact hne (ConstantFieldPlaceLift.ord_eq_zero_of_mem_of_inv_mem w (hall f)
      (by rw [← map_inv₀]; exact hall _))
  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom
    (K := K) x (algebraMap F F') w.toValuationSubring hwK hwx
  exact hw v (eq_liftPlace hfg hfg' hgen hv.symm)

private noncomputable def conormDiv : Divisor K F →+ Divisor K' F' :=
  Finsupp.mapDomain.addMonoidHom (liftPlace hfg hfg' hgen)

private theorem conormDiv_apply_liftPlace (D : Divisor K F) (P : Place K F) :
    conormDiv hfg hfg' hgen D (liftPlace hfg hfg' hgen P) = D P :=
  Finsupp.mapDomain_apply_of_injective (liftPlace_injective hfg hfg' hgen) D P

private theorem conormDiv_apply_of_forall_ne (D : Divisor K F) (w : Place K' F')
    (hw : ∀ P : Place K F, w ≠ liftPlace hfg hfg' hgen P) : conormDiv hfg hfg' hgen D w = 0 :=
  Finsupp.mapDomain_of_notMem_range D w (by rintro ⟨P, rfl⟩; exact hw P rfl)

private theorem conormDiv_single (P : Place K F) (m : ℤ) :
    conormDiv hfg hfg' hgen (Finsupp.single P m) = Finsupp.single (liftPlace hfg hfg' hgen P) m :=
  Finsupp.mapDomain_single

private theorem conormDiv_mem_principal {D : Divisor K F}
    (hD : D ∈ (Divisor.principal : AddSubgroup (Divisor K F))) :
    conormDiv hfg hfg' hgen D ∈ (Divisor.principal : AddSubgroup (Divisor K' F')) := by
  obtain ⟨f, hf, hDf⟩ := hD
  refine ⟨algebraMap F F' f, (map_ne_zero (algebraMap F F')).mpr hf, fun w => ?_⟩
  by_cases hw : ∃ P, w = liftPlace hfg hfg' hgen P
  · obtain ⟨P, rfl⟩ := hw
    rw [conormDiv_apply_liftPlace, ord_liftPlace, hDf]
  · push Not at hw
    rw [conormDiv_apply_of_forall_ne hfg hfg' hgen D w hw,
      ord_algebraMap_eq_zero_of_forall_ne hfg hfg' hgen w hw]

variable [IsAlgClosed K'] [IsCurveOver K' F']

private theorem degree_conormDiv (D : Divisor K F) :
    Divisor.degree (conormDiv hfg hfg' hgen D) = Divisor.degree D := by
  refine Finsupp.induction D (by simp) fun P m D _ _ ih => ?_
  rw [map_add, map_add, map_add, ih, conormDiv_single, Divisor.degree_single,
    Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed,
    IsCurveOver.deg_eq_one_of_isAlgClosed]

private noncomputable def conormDegZero :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K') (F := F') :=
  ((conormDiv hfg hfg' hgen).domRestrict (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => show Divisor.degree (conormDiv hfg hfg' hgen (D : Divisor K F)) = 0 by
      rw [degree_conormDiv]; exact D.2)

private theorem coe_conormDegZero (D : Divisor.degZero (K := K) (F := F)) :
    (conormDegZero hfg hfg' hgen D : Divisor K' F') = conormDiv hfg hfg' hgen D := rfl

private noncomputable def Con : Pic0 K F →+ Pic0 K' F' :=
  QuotientAddGroup.map _ _ (conormDegZero hfg hfg' hgen) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact conormDiv_mem_principal hfg hfg' hgen hD)

private theorem Con_mk (D : Divisor.degZero (K := K) (F := F)) :
    Con hfg hfg' hgen (Pic0.mk D) = Pic0.mk (conormDegZero hfg hfg' hgen D) := rfl

private theorem Con_eq_zero_imp {n : ℕ} (hn : n ≠ 0) {c : Pic0 K F}
    (hc : c ∈ Pic0.torsion K F n) (h0 : Con hfg hfg' hgen c = 0) : c = 0 := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [Con_mk, mk_eq_zero_iff', coe_conormDegZero] at h0
  obtain ⟨f', hf', hDf'⟩ := h0
  rw [Pic0.mem_torsion, ← mk_zsmul', mk_eq_zero_iff', ← AddSubgroup.mem_addSubgroupOf] at hc
  obtain ⟨g, hg, hDg⟩ := natCast_mul_apply_eq_of_zsmul_mem_principal hc
  have hg' : algebraMap F F' g ≠ 0 := (map_ne_zero (algebraMap F F')).mpr hg

  set z : F' := f' ^ n * (algebraMap F F' g)⁻¹ with hz
  have hz0 : z ≠ 0 := mul_ne_zero (pow_ne_zero _ hf') (inv_ne_zero hg')
  have hzord : ∀ w : Place K' F', w.ord z = 0 := by
    intro w
    rw [hz, w.ord_mul (pow_ne_zero _ hf') (inv_ne_zero hg'), Place.ord_inv, ← zpow_natCast,
      Place.ord_zpow]
    by_cases hw : ∃ P, w = liftPlace hfg hfg' hgen P
    · obtain ⟨P, rfl⟩ := hw
      rw [ord_liftPlace, ← hDg P, ← hDf', conormDiv_apply_liftPlace]
      ring
    · push Not at hw
      rw [← hDf', conormDiv_apply_of_forall_ne hfg hfg' hgen _ w hw,
        ord_algebraMap_eq_zero_of_forall_ne hfg hfg' hgen w hw]
      ring
  obtain ⟨x', hx', hfin'⟩ := id hfg'
  haveI := hfin'
  obtain ⟨c, hc⟩ :=
    AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
      (K := K') x' hx' hzord
  have hc0 : c ≠ 0 := by rintro rfl; exact hz0 (by rw [← hc, map_zero])

  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c (Nat.pos_of_ne_zero hn)
  have hd0 : d ≠ 0 := by rintro rfl; exact hc0 (by rw [← hd, zero_pow hn])
  have hd0' : algebraMap K' F' d ≠ 0 := (map_ne_zero (algebraMap K' F')).mpr hd0

  set y : F' := f' * (algebraMap K' F' d)⁻¹ with hy_def
  have hy : y ^ n = algebraMap F F' g := by
    rw [hy_def, mul_pow, inv_pow, ← map_pow, hd, hc, hz, mul_inv, inv_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hf'), one_mul]
  obtain ⟨f, hf⟩ := mem_range_of_pow_eq_algebraMap hfg hfg' hgen hn hy
  have hfy : f' = algebraMap F F' f * algebraMap K' F' d := by
    rw [hf, hy_def, inv_mul_cancel_right₀ hd0']
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hfy
    exact hf' hfy

  refine (mk_eq_zero_iff' D).mpr ⟨f, hf0, fun P => ?_⟩
  rw [← ord_liftPlace hfg hfg' hgen P f, ← conormDiv_apply_liftPlace hfg hfg' hgen (D : Divisor K F) P,
    hDf', hfy, (liftPlace hfg hfg' hgen P).ord_mul ((map_ne_zero (algebraMap F F')).mpr hf0) hd0',
    Place.ord_algebraMap_base, add_zero]

private theorem exists_Con_eq {n : ℕ} (hn : n ≠ 0) {c' : Pic0 K' F'}
    (hc' : c' ∈ Pic0.torsion K' F' n) :
    ∃ c ∈ Pic0.torsion K F n, Con hfg hfg' hgen c = c' := by
  obtain ⟨D', rfl⟩ := Pic0.mk_surjective c'
  have hc'' := hc'
  rw [Pic0.mem_torsion, ← mk_zsmul', mk_eq_zero_iff', ← AddSubgroup.mem_addSubgroupOf] at hc''
  obtain ⟨g', hg', hDg'⟩ := natCast_mul_apply_eq_of_zsmul_mem_principal hc''
  obtain ⟨D, h', hh', ⟨g, hg, hDg⟩, hover, hoff⟩ :=
    AlgebraicCurve.Divisor.exists_torsion_descent_of_constantFieldExtension K F K' F' hfg hfg'
      hgen n hn (D' : Divisor K' F') ⟨g', hg', hDg'⟩
  have hDdeg : Divisor.degree D = 0 := by
    have h1 : Divisor.degree ((n : ℤ) • D) = 0 :=
      degree_eq_zero_of_forall_eq_ord hg fun v => by rw [Finsupp.smul_apply, smul_eq_mul, hDg]
    rw [map_zsmul, smul_eq_mul, mul_eq_zero] at h1
    exact h1.resolve_left (Int.natCast_ne_zero.mpr hn)
  refine ⟨Pic0.mk ⟨D, Divisor.mem_degZero.mpr hDdeg⟩, ?_, ?_⟩
  · rw [Pic0.mem_torsion, ← mk_zsmul', mk_eq_zero_iff']
    exact ⟨g, hg, fun v => by
      rw [AddSubgroupClass.coe_zsmul, Finsupp.smul_apply, smul_eq_mul]; exact hDg v⟩
  · rw [Con_mk, mk_eq_mk_iff', coe_conormDegZero]
    refine ⟨h', hh', fun w => ?_⟩
    rw [Finsupp.add_apply, Finsupp.neg_apply]
    by_cases hw : ∃ P, w = liftPlace hfg hfg' hgen P
    · obtain ⟨P, rfl⟩ := hw
      rw [conormDiv_apply_liftPlace, hover P _ (liftPlace_comap hfg hfg' hgen P)]
      ring
    · push Not at hw
      have hoffw := hoff w fun P hP => hw P (eq_liftPlace hfg hfg' hgen hP)
      rw [conormDiv_apply_of_forall_ne hfg hfg' hgen _ w hw, hoffw]
      ring

include hfg hfg' hgen in

private theorem natCard_torsion_eq {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Pic0.torsion K' F' n) = Nat.card (Pic0.torsion K F n) := by
  let t : Pic0.torsion K F n → Pic0.torsion K' F' n := fun c =>
    ⟨Con hfg hfg' hgen c, by
      rw [Pic0.mem_torsion, ← map_zsmul (Con hfg hfg' hgen), Pic0.mem_torsion.mp c.2, map_zero]⟩
  have hinj : Function.Injective t := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    have h' : Con hfg hfg' hgen a = Con hfg hfg' hgen b := congrArg Subtype.val h
    have hab : a - b ∈ Pic0.torsion K F n := (Pic0.torsion K F n).sub_mem ha hb
    have := Con_eq_zero_imp hfg hfg' hgen hn hab (by rw [map_sub, h', sub_self])
    exact Subtype.ext (sub_eq_zero.mp this)
  have hsurj : Function.Surjective t := by
    rintro ⟨c', hc'⟩
    obtain ⟨c, hc, hcc'⟩ := exists_Con_eq hfg hfg' hgen hn hc'
    exact ⟨⟨c, hc⟩, Subtype.ext hcc'⟩
  exact (Nat.card_congr (Equiv.ofBijective t ⟨hinj, hsurj⟩)).symm

end Lift

end Transfer

end W7XL2

set_option linter.style.haveILetI false in
/-- **The order of the `n`-torsion of `Pic⁰` is a constant-field-extension invariant.**
Verbatim from
`Theorems/Thm_AlgebraicCurve_Pic0_natCard_torsion_eq_of_constantFieldExtension.lean`; the
pin's `p^{2g}` statement `#Pic⁰[n](K'·F) = #Pic⁰[n](F)`. -/
theorem Pic0.natCard_torsion_eq_of_constantFieldExtension (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) :
    Nat.card (Pic0.torsion K' F' n) = Nat.card (Pic0.torsion K F n) :=
  W7XL2.natCard_torsion_eq hfg hfg' hgen hn

end AlgebraicCurve
