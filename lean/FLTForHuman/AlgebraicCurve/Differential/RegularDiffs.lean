/-
The regular differentials are already a `K`-subspace.

`IsRegularDiff K F ω` says `0 ≤ v.ordDiff ω` at every place, and `regularDiffs K F` is the
`K`-span of those `ω`. This module proves `ω ∈ regularDiffs K F ↔ IsRegularDiff K F ω`,
i.e. the pointwise condition is closed under `0`, `+` and scalar multiplication, so the
span adds nothing: the "regular" differentials are literally the submodule
`regularDiffs K F`. That identification is what lets the other form of the same statement
(the order of `diffCoeff` at a place being nonnegative) be used as a `Submodule` membership.

The prelude is the pin's, and it is the mathematics: `diffCoeff` is additive in `ω` at an
element of nonzero order, `ordDiff` obeys the ultrametric inequality through
`ord` of the coefficient, and the three closure cases. Each of the four ingredients the
proof uses was ported for its own sake — the coefficient laws (`diffCoeff_smul_D`, its
`_of_ord_ne_zero` sibling and the uniqueness form), `ordDiff_zero`, the multiplication law
`ordDiff_smul`, and `Place.min_ord_le_ord_add` — so this module is the span argument
itself and nothing else.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_mem_regularDiffs_iff.lean

The second half is the place/differential dictionary after a constant field extension:
`Place.ordDiff` and `Place.ordDifferential` are the two pin spellings of the order of a
differential, and a divisor whose support is `F`-integral has vanishing
order-differential along the extension.

spec-pin: Theorems/Thm_AlgebraicCurve_mem_regularDiffs_iff.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_mem_regularDiffs_iff.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Differential.Coefficient

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

-- The pin states this file's prelude in a section, so the binder block is the section's;
-- the same here, to keep the checked text identical (the check is textual).
section

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
  [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F]

include x in
/-- The coefficient is additive in the differential, at an element of nonzero order. -/
theorem diffCoeff_add (v : Place K F) {t : F} (ht : v.ord t ≠ 0) (ω₁ ω₂ : Ω[F⁄K]) :
    Place.diffCoeff t (ω₁ + ω₂) = Place.diffCoeff t ω₁ + Place.diffCoeff t ω₂ := by
  have h1 := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht ω₁
  have h2 := Place.diffCoeff_smul_D_of_ord_ne_zero x v ht ω₂
  conv_lhs => rw [← h1, ← h2, ← add_smul]
  exact Place.diffCoeff_smul_D_eq x v ht _

include x in
/-- `ordDiff` obeys the ultrametric inequality, through `ord` of the coefficient. -/
theorem min_ordDiff_le_ordDiff_add (v : Place K F) {ω₁ ω₂ : Ω[F⁄K]} (h₁₂ : ω₁ + ω₂ ≠ 0) :
    min (v.ordDiff ω₁) (v.ordDiff ω₂) ≤ v.ordDiff (ω₁ + ω₂) := by
  rcases eq_or_ne ω₁ 0 with rfl | h₁
  · rw [zero_add]; exact min_le_right _ _
  rcases eq_or_ne ω₂ 0 with rfl | h₂
  · rw [add_zero]; exact min_le_left _ _
  have hu : v.ord v.uniformizer_alt ≠ 0 := by
    rw [v.ord_uniformizer_alt ⟨v.uniformizer, v.ord_uniformizer⟩]; exact one_ne_zero
  have hcoe : ∀ ω : Ω[F⁄K], ω ≠ 0 → Place.diffCoeff v.uniformizer_alt ω ≠ 0 := by
    intro ω hω h0
    have := Place.diffCoeff_smul_D_of_ord_ne_zero x v hu ω
    rw [h0, zero_smul] at this
    exact hω this.symm
  simp only [Place.ordDiff_def]
  rw [diffCoeff_add x v hu]
  exact v.min_ord_le_ord_add (by rw [← diffCoeff_add x v hu]; exact hcoe _ h₁₂)

include x in
/-- The zero differential is regular. -/
theorem isRegularDiff_zero : IsRegularDiff K F (0 : Ω[F⁄K]) := fun v => by
  rw [Place.ordDiff_zero x v]

include x in
/-- Regular differentials are closed under addition. -/
theorem isRegularDiff_add {ω₁ ω₂ : Ω[F⁄K]} (h₁ : IsRegularDiff K F ω₁) (h₂ : IsRegularDiff K F ω₂) :
    IsRegularDiff K F (ω₁ + ω₂) := by
  intro v
  rcases eq_or_ne (ω₁ + ω₂) 0 with h12 | h12
  · rw [h12, Place.ordDiff_zero x v]
  · exact le_trans (le_min (h₁ v) (h₂ v)) (min_ordDiff_le_ordDiff_add x v h12)

include x in
/-- Regular differentials are closed under scalar multiplication. -/
theorem isRegularDiff_smul (c : K) {ω : Ω[F⁄K]} (h : IsRegularDiff K F ω) :
    IsRegularDiff K F (c • ω) := by
  intro v
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul]; exact isRegularDiff_zero x v
  rcases eq_or_ne ω 0 with rfl | hω
  · rw [smul_zero]; exact isRegularDiff_zero x v
  rw [← algebraMap_smul F c ω, Place.ordDiff_smul x v ((map_ne_zero _).mpr hc) hω,
    v.ord_algebraMap, zero_add]
  exact h v

end

/-- **The regular differentials form a `K`-subspace.** Verbatim from
`Theorems/Thm_AlgebraicCurve_mem_regularDiffs_iff.lean`: membership in the span is the
pointwise condition, the three closure cases supplying the span induction. -/
theorem mem_regularDiffs_iff {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K] (x : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] (ω : Ω[F⁄K]) :
    ω ∈ AlgebraicCurve.regularDiffs K F ↔ AlgebraicCurve.IsRegularDiff K F ω := by
  refine ⟨fun h => ?_, AlgebraicCurve.mem_regularDiffs_of_isRegularDiff⟩
  induction h using Submodule.span_induction with
  | mem ω hω => exact hω
  | zero => exact isRegularDiff_zero x
  | add ω₁ ω₂ _ _ h₁ h₂ => exact isRegularDiff_add x h₁ h₂
  | smul c ω _ h => exact isRegularDiff_smul x c h

/-! ## The two notions of the order of a differential

The pin's `Place.ordDiff` and `Place.ordDifferential` read the order of a differential
through two coefficients: the pin's `diffCoeff` against its `uniformizer_alt`, and
`differentialCoeff` against the port's single `uniformizer`.  The port keeps one
uniformiser (`Defs/CanonicalDivisor.lean`), so the two coefficients are the same
element definitionally and the bridge is `rfl`; the pin spends a
`dCoord`-decomposition on it. -/

/-- **`ordDiff` is `ordDifferential`.** Statement from
`Theorems/Thm_AlgebraicCurve_Place_ordDiff_eq_ordDifferential.lean`; the pin's proof
identifies the two coefficient functions, which is `rfl` in the port. -/
theorem Place.ordDiff_eq_ordDifferential {K F : Type*} [Field K] [Field F] [Algebra K F]
    [CharZero K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F]
    (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω :=
  rfl

/-! ## The order of `D x` along a constant field extension

The pin's `S_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem`
(517 ln): if `F' = K'·F` and a place `w` of `F'` contains the image of every element of
`F`, then the differential of a `K'`-transcendental element coming from `F` has nonzero
coefficient and order zero at `w`.  The engine is the pin's: the coefficient functional
`coeffDer w = differentialCoeff w ∘ D` is a derivation, it is regular on integral
elements (`differentialCoeff_D_mem`), and the order drops by exactly one on elements of
positive order (`coeffDer_of_one_le_ord`).  Then every `K'`-coefficient of an `F`-element
is divisible by `ord c + 1`, applied to the uniformiser of `w` — whose order is `1` and
which lies in `K'·F`.

Everything but the headline is private, as in the pin. -/

section OrdDifferentialD

open KaehlerDifferential IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem ord_eq_zero_of_isUnit (v : Place K F) {a : v.toValuationSubring}
    (ha : IsUnit a) : v.ord (a : F) = 0 := by
  obtain ⟨u, rfl⟩ := ha
  exact v.ord_coe_unit u

private theorem mem_maximalIdeal_of_not_isUnit (v : Place K F) {a : v.toValuationSubring}
    (ha : ¬IsUnit a) : a ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

private theorem not_isUnit_of_mem_maximalIdeal (v : Place K F) {a : v.toValuationSubring}
    (ha : a ∈ IsLocalRing.maximalIdeal v.toValuationSubring) : ¬IsUnit a := by
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha

private theorem one_le_ord_of_mem_of_inv_not_mem {v : Place K F} {f : F}
    (h1 : f ∈ v.toValuationSubring) (h2 : f⁻¹ ∉ v.toValuationSubring) : 1 ≤ v.ord f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact h2 (by simp)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ
  have h0 := Place.ord_nonneg_of_mem v h1
  by_contra hlt
  have hz : v.ord f = 0 := by omega
  apply h2
  have hmul : ((u : v.toValuationSubring) : F) *
      (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  rw [hu, hz, zpow_zero, mul_one, ← eq_inv_of_mul_eq_one_right hmul]
  exact SetLike.coe_mem _

private theorem mem_iff_ord_nonneg (v : Place K F) (f : F) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  refine ⟨Place.ord_nonneg_of_mem v, fun h => ?_⟩
  by_contra hmem
  have hinv : f⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem f).resolve_left hmem
  have := one_le_ord_of_mem_of_inv_not_mem hinv (by simpa using hmem)
  rw [v.ord_inv] at this
  omega

private theorem irreducible_uniformizerSubring (v : Place K F) :
    Irreducible v.uniformizerSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

private theorem mul_uniformizer_mem_maximalIdeal (v : Place K F) {d : F}
    (hd : d ∈ v.toValuationSubring) :
    (⟨d * v.uniformizer, mul_mem hd v.uniformizerSubring.2⟩ : v.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [(irreducible_uniformizerSubring v).maximalIdeal_eq, Ideal.mem_span_singleton']
  exact ⟨⟨d, hd⟩, Subtype.ext rfl⟩

set_option linter.style.haveILetI false in
private theorem isUnit_natCast [CharZero K] (v : Place K F) (n : ℕ) (hn : n ≠ 0) :
    IsUnit (⟨((n : ℕ) : F), natCast_mem v.toValuationSubring n⟩ : v.toValuationSubring) := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  have hne : ((n : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hinv_mem : ((n : ℕ) : F)⁻¹ ∈ v.toValuationSubring := by
    have h : ((n : ℕ) : F)⁻¹ = algebraMap K F ((n : K)⁻¹) := by
      rw [map_inv₀, map_natCast]
    rw [h]
    exact v.algebraMap_mem' _
  refine isUnit_iff_exists_inv.2 ⟨⟨((n : ℕ) : F)⁻¹, hinv_mem⟩, ?_⟩
  apply Subtype.ext
  rw [MulMemClass.coe_mul, OneMemClass.coe_one]
  exact mul_inv_cancel₀ hne

private theorem exists_unit_mul_zpow_uniformizer {w : Place K F} {f : F} (hf : f ≠ 0) :
    ∃ u : w.toValuationSubringˣ,
      f = ((u : w.toValuationSubring) : F) * w.uniformizer ^ (w.ord f) := by
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf (irreducible_uniformizerSubring w)
  exact ⟨u, hu⟩

end OrdDifferentialD

section Coeff

open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private noncomputable def coeffLin (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    Ω[F⁄K] →ₗ[F] F where
  toFun := w.differentialCoeff
  map_add' ω₁ ω₂ := w.differentialCoeff_unique
    (by rw [add_smul, w.differentialCoeff_smul_dCoord, w.differentialCoeff_smul_dCoord])
  map_smul' c ω := by
    simp only [RingHom.id_apply, smul_eq_mul]
    exact w.differentialCoeff_smul c ω

theorem coeffLin_apply (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (ω : Ω[F⁄K]) : coeffLin w ω = w.differentialCoeff ω := rfl

private noncomputable def coeffDer (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    Derivation K F F :=
  (coeffLin w).compDer (D K F)

theorem coeffDer_apply (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (f : F) : coeffDer w f = w.differentialCoeff (D K F f) := rfl

theorem coeffDer_uniformizer (w : Place K F) [w.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    coeffDer w w.uniformizer = 1 :=
  w.differentialCoeff_dCoord

theorem differentialCoeff_D_mem [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] [∀ w : Place K F, w.DCoordGenerates] (w : Place K F) {z : F}
    (hz : z ∈ w.toValuationSubring) :
    w.differentialCoeff (D K F z) ∈ w.toValuationSubring := by
  have hunit : ∀ u : F, u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (D K F u) ∈ w.toValuationSubring := by
    intro u hu0 hu
    rcases localUnitDerivativeRegular_of_isCurveOver w u hu0 hu with h | h
    · rw [h]; exact zero_mem _
    · exact (mem_iff_ord_nonneg w _).2 h
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [← coeffDer_apply, map_zero]; exact zero_mem _
  by_cases hzu : w.ord z = 0
  · exact hunit z hz0 hzu
  have h1 : 1 ≤ w.ord z := by have := Place.ord_nonneg_of_mem w hz; omega
  have hzmax : (⟨z, hz⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring :=
    mem_maximalIdeal_of_not_isUnit w fun hu => by
      have := ord_eq_zero_of_isUnit w hu; simp only at this; omega
  have hu : IsUnit (1 - (⟨z, hz⟩ : w.toValuationSubring)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hzmax
  have hu0 : (1 - z : F) ≠ 0 := by
    intro h
    apply hu.ne_zero
    exact Subtype.ext h
  have huord : w.ord (1 - z) = 0 := ord_eq_zero_of_isUnit w hu
  have key : w.differentialCoeff (D K F z) = -w.differentialCoeff (D K F (1 - z)) := by
    rw [← coeffDer_apply, ← coeffDer_apply, map_sub, Derivation.map_one_eq_zero, zero_sub,
      neg_neg]
  rw [key]
  exact neg_mem (hunit _ hu0 huord)

theorem coeffDer_of_one_le_ord [CharZero K] [PerfectField K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] [∀ w : Place K F, w.DCoordGenerates] (w : Place K F) {α : F} (hα0 : α ≠ 0)
    (hα : 1 ≤ w.ord α) :
    coeffDer w α ≠ 0 ∧ w.ord (coeffDer w α) = w.ord α - 1 := by
  obtain ⟨u, hu⟩ := exists_unit_mul_zpow_uniformizer (w := w) hα0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = w.ord α := ⟨(w.ord α).toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hαeq : α = ((u : w.toValuationSubring) : F) * w.uniformizer ^ (m + 1) := by
    rw [hu, ← hn, zpow_natCast]
  set d := coeffDer w ((u : w.toValuationSubring) : F) with hd_def
  have hd_mem : d ∈ w.toValuationSubring :=
    differentialCoeff_D_mem w (u : w.toValuationSubring).2
  set β : F := ((m + 1 : ℕ) : F) * ((u : w.toValuationSubring) : F) + d * w.uniformizer
    with hβ_def
  have hδ : coeffDer w α = w.uniformizer ^ m * β := by
    rw [hαeq, Derivation.leibniz, Derivation.leibniz_pow, coeffDer_uniformizer, hβ_def]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, mul_one]
    ring
  have hβ_mem : β ∈ w.toValuationSubring :=
    add_mem (mul_mem (natCast_mem _ _) (u : w.toValuationSubring).2)
      (mul_mem hd_mem w.uniformizerSubring.2)
  have hβ_unit : IsUnit (⟨β, hβ_mem⟩ : w.toValuationSubring) := by
    by_contra hnu
    have hmax := mem_maximalIdeal_of_not_isUnit w hnu
    have hprod := mul_uniformizer_mem_maximalIdeal w hd_mem
    have hnu_unit : IsUnit ((⟨((m + 1 : ℕ) : F), natCast_mem w.toValuationSubring _⟩ : w.toValuationSubring)
        * (u : w.toValuationSubring)) :=
      (isUnit_natCast w (m + 1) (Nat.succ_ne_zero m)).mul u.isUnit
    have heq : (⟨((m + 1 : ℕ) : F), natCast_mem w.toValuationSubring _⟩ : w.toValuationSubring)
        * (u : w.toValuationSubring)
        = ⟨β, hβ_mem⟩ - ⟨d * w.uniformizer, mul_mem hd_mem w.uniformizerSubring.2⟩ := by
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, hβ_def]
      ring
    refine not_isUnit_of_mem_maximalIdeal w ?_ hnu_unit
    rw [heq]
    exact sub_mem hmax hprod
  have hβ_ord' := ord_eq_zero_of_isUnit w hβ_unit
  have hβ_ord : w.ord β = 0 := by simpa only using hβ_ord'
  have hβ0 : β ≠ 0 := by
    intro h
    apply hβ_unit.ne_zero
    exact Subtype.ext h
  have hϖ0 : w.uniformizer ^ m ≠ 0 := pow_ne_zero _ w.uniformizer_ne_zero
  refine ⟨by rw [hδ]; exact mul_ne_zero hϖ0 hβ0, ?_⟩
  rw [hδ, w.ord_mul hϖ0 hβ0, hβ_ord, add_zero, ← zpow_natCast, w.ord_zpow, w.ord_uniformizer,
    mul_one, ← hn]
  push_cast
  ring

end Coeff

section BasisD

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

open KaehlerDifferential IntermediateField

/-- A differential with a transcendental generator is a one-element basis generated by
that differential: the pin's `exists_basis_D`, built here from the public
`span_D_eq_top_of_transcendental` and `D_ne_zero_of_transcendental` instead of the
`RatFunc`-tower basis of `Differential/ConstantFieldExtension.lean`. -/
private theorem exists_basis_D (K : Type*) (F : Type*) [Field K] [Field F] [Algebra K F]
    [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {t : F} (ht : Transcendental K t) :
    ∃ b : Module.Basis (Fin 1) F (Ω[F⁄K]), b 0 = D K F t := by
  obtain ⟨x₀, -, hx₀fin⟩ := hfg
  haveI := hx₀fin
  haveI hfin : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental (K := K) (F := F) x₀ ht
  haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({t} : Set F)) F :=
    Algebra.IsSeparable.of_integral _ F
  have hli : LinearIndependent F (fun _ : Fin 1 => D K F t) := by
    rw [linearIndependent_unique_iff]
    exact D_ne_zero_of_transcendental K t ht
  have hsp : Submodule.span F (Set.range (fun _ : Fin 1 => D K F t)) = ⊤ := by
    simpa using span_D_eq_top_of_transcendental K t ht
  exact ⟨Module.Basis.mk hli hsp.ge, Module.Basis.mk_apply hli hsp.ge 0⟩

/-- The pin's `D_ne_zero_of_transcendental`: `D t ≠ 0` for transcendental `t`, with the
finiteness hypothesis passed as an existential (the port's public form takes it as an
instance for the same `t`). -/
private theorem D_ne_zero_of_transcendental' (K : Type*) (F : Type*) [Field K] [Field F]
    [Algebra K F] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {t : F} (ht : Transcendental K t) : D K F t ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_basis_D K F hfg ht
  rw [← hb]
  exact b.ne_zero 0

end BasisD

section MainTheorem

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

open KaehlerDifferential IntermediateField

/-- **`D` of a `K'`-transcendental element of `F` has order `0`.** Statement from
`Theorems/Thm_AlgebraicCurve_Place_ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem.lean`;
proof after the pin's `S_` file. -/
theorem Place.ordDifferential_D_eq_zero_of_constantFieldExtension_of_forall_mem
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (w : Place K' F') (hw : ∀ f : F, algebraMap F F' f ∈ w.toValuationSubring)
    {x : F} (hx : Transcendental K' (algebraMap F F' x)) :
    w.differentialCoeff (KaehlerDifferential.D K' F' (algebraMap F F' x)) ≠ 0 ∧
      w.ordDifferential (KaehlerDifferential.D K' F' (algebraMap F F' x)) = 0 := by
  classical
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : Algebra.EssFiniteType K' F' := by
    obtain ⟨y, hy, hyfin⟩ := hfg'
    exact essFiniteType_of_transcendental_of_finiteDimensional hy hyfin
  haveI hDC' : ∀ w : Place K' F', w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  have hxK : Transcendental K x := fun halg =>
    hx ((halg.algHom (IsScalarTower.toAlgHom K F F')).tower_top K')
  set x' := algebraMap F F' x with hx'_def
  set c := w.differentialCoeff (D K' F' x') with hc_def
  have hcδ : coeffDer w x' = c := rfl
  have hDx' : D K' F' x' ≠ 0 := D_ne_zero_of_transcendental' K' F' hfg' hx
  have hc0 : c ≠ 0 := by
    intro h
    apply hDx'
    rw [← w.differentialCoeff_smul_dCoord (D K' F' x'), ← hc_def, h, zero_smul]
  refine ⟨hc0, ?_⟩
  show w.ord c = 0
  have hc_mem : c ∈ w.toValuationSubring := differentialCoeff_D_mem w (hw x)
  have hc_nonneg : 0 ≤ w.ord c := Place.ord_nonneg_of_mem w hc_mem
  obtain ⟨b, hb⟩ := exists_basis_D K F hfg hxK
  let d₀ : Derivation K F F := (b.coord 0).compDer (D K F)
  have hDf : ∀ f : F, D K F f = d₀ f • D K F x := fun f => by
    conv_lhs => rw [← b.sum_repr (D K F f)]
    rw [Fin.sum_univ_one, hb]
    rfl
  have hkey : ∀ f : F, coeffDer w (algebraMap F F' f) = algebraMap F F' (d₀ f) * c := by
    intro f
    have h1 : D K' F' (algebraMap F F' f) = algebraMap F F' (d₀ f) • D K' F' x' := by
      rw [← KaehlerDifferential.map_D K K' F F' f, hDf, map_smul,
        algebra_compatible_smul F' (d₀ f), KaehlerDifferential.map_D]
    rw [coeffDer_apply, h1, w.differentialCoeff_smul]
  set S : Subalgebra K' F' := Algebra.adjoin K' (Set.range (algebraMap F F')) with hS_def
  let Ow : Subalgebra K' F' :=
    { w.toValuationSubring.toSubring with
      algebraMap_mem' := fun r => w.algebraMap_mem' r }
  have hSO : S ≤ Ow := Algebra.adjoin_le (by rintro _ ⟨f, rfl⟩; exact hw f)
  have hSmem : ∀ z ∈ S, z ∈ w.toValuationSubring := fun z hz => hSO hz
  have hstab : ∀ z ∈ S, ∃ t ∈ S, coeffDer w z = t * c := by
    intro z hz
    refine Algebra.adjoin_induction (p := fun z _ => ∃ t ∈ S, coeffDer w z = t * c)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨f, rfl⟩
      exact ⟨algebraMap F F' (d₀ f), Algebra.subset_adjoin ⟨d₀ f, rfl⟩, hkey f⟩
    · intro r
      exact ⟨0, zero_mem _, by rw [Derivation.map_algebraMap, zero_mul]⟩
    · rintro a b - - ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
      exact ⟨ta + tb, add_mem hta htb, by rw [map_add, ha, hb, add_mul]⟩
    · rintro a b haS hbS ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
      refine ⟨a * tb + b * ta, add_mem (mul_mem haS htb) (mul_mem hbS hta), ?_⟩
      rw [Derivation.leibniz, ha, hb, smul_eq_mul, smul_eq_mul]
      ring
  by_contra hcne
  have hc1 : 1 ≤ w.ord c := by omega
  set k : ℤ := w.ord c + 1 with hk_def
  have hdiv : ∀ n : ℕ, ∀ z ∈ S, z ≠ 0 → w.ord z = n → k ∣ (n : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro z hzS hz0 hzn
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · exact dvd_zero k
      have hz1 : 1 ≤ w.ord z := by omega
      obtain ⟨hδ0, hδord⟩ := coeffDer_of_one_le_ord w hz0 hz1
      obtain ⟨t, htS, ht⟩ := hstab z hzS
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hδ0 (by rw [ht, zero_mul])
      have htord : w.ord t = n - k := by
        have h := hδord
        rw [ht, w.ord_mul ht0 hc0, hzn] at h
        omega
      have ht_nonneg : 0 ≤ w.ord t := Place.ord_nonneg_of_mem w (hSmem t htS)
      have hlt : (w.ord t).toNat < n := by omega
      have hih := ih _ hlt t htS ht0 (Int.toNat_of_nonneg ht_nonneg).symm
      rw [Int.toNat_of_nonneg ht_nonneg, htord] at hih
      simpa using hih
  have hdiv' : ∀ z ∈ S, z ≠ 0 → k ∣ w.ord z := fun z hzS hz0 => by
    have h0 : 0 ≤ w.ord z := Place.ord_nonneg_of_mem w (hSmem z hzS)
    have := hdiv (w.ord z).toNat z hzS hz0 (Int.toNat_of_nonneg h0).symm
    rwa [Int.toNat_of_nonneg h0] at this
  have hϖmem : w.uniformizer ∈ IntermediateField.adjoin K' (Set.range (algebraMap F F')) := by
    rw [hgen]; exact IntermediateField.mem_top
  rw [IntermediateField.mem_adjoin_iff_div] at hϖmem
  obtain ⟨r, hr, s, hs, hrs⟩ := hϖmem
  have hϖ0 := w.uniformizer_ne_zero
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hϖ0 (by rw [hrs, div_zero])
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hϖ0 (by rw [hrs, zero_div])
  have hord1 : w.ord r - w.ord s = 1 := by
    rw [← w.ord_uniformizer, hrs, div_eq_mul_inv, w.ord_mul hr0 (inv_ne_zero hs0), w.ord_inv]
    ring
  have hk1 : k ∣ 1 := by
    rw [← hord1]
    exact dvd_sub (hdiv' r hr hr0) (hdiv' s hs hs0)
  have hk2 : 2 ≤ k := by omega
  have := Int.eq_one_of_dvd_one (by omega) hk1
  omega

end MainTheorem

end AlgebraicCurve
