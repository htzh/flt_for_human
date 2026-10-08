/-
The Riemann–Roch assembly against the K ending, after FLT's
`P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean`
(6,257 ln) at pin `aa2d8b3`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean>).

The public headline is `AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`,
spelled verbatim from its `Theorems/` wrapper; `hRTK : ResidueTheoremK K F` stays a
hypothesis (row 6's `AlgebraicCurve.residueTheoremK_of_isAlgClosed` is the producer).
The proof is the pin's `solution`, reaching `ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed`
(pin 5931) and the `p0n25_wkc_*` `MirrorAssembly` block (pin 5971–6257).

The mathematics is the phase-1 Riemann–Roch engine under its phase-1 names
(`Defs/RiemannRochRows.lean` predicates and bridges, `Genus/Index.lean`,
`Genus/Stichtenoth.lean`, `RiemannRoch/Assembly.lean`) plus the K local-residue /
Weil-differential layer already public in `Defs/LocalResidue.lean`. The K-route chain
this file adds is adapter-shaped over those; the audit is
`topics/riemannRoch/AUDIT-mathlib-p3-7.md`.

Promotion debt: the pin-private `Place.exists_trace_residue_ne_zero` (pin 4863) lives
`private` in the frozen `Defs/WeilOfKaehler.lean`; re-provisioned `private` here.
-/
import FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluationAlgebra
import FLTForHuman.AlgebraicCurve.Defs.PoleDivisorPackage
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.Genus.Stichtenoth
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import FLTForHuman.AlgebraicCurve.LocalResidue.Instance
import FLTForHuman.AlgebraicCurve.ResidueTheorem.KFamily

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open KaehlerDifferential LinearMap
open WithZero IsDedekindDomain IsLocalRing Module
open scoped Classical

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-! ## The K-route chain over the phase-1 engine -/

namespace Place

/-- The pin's `private` helper `_root_.AlgebraicCurve.Place.ord_sub_evalAt_pos`
(pin 1973): a nonzero element of the valuation subring differs from its residue
value by something of positive order. -/
private theorem ord_sub_evalAt_pos (v : Place K F) (hrat : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring)
    (hne : f - algebraMap K F (v.evalAt f) ≠ 0) :
    0 < v.ord (f - algebraMap K F (v.evalAt f)) := by
  have hmem : f - algebraMap K F (v.evalAt f) ∈ v.toValuationSubring :=
    sub_mem hf (v.algebraMap_mem' _)
  rcases eq_or_ne (v.ord (f - algebraMap K F (v.evalAt f))) 0 with h0 | h0
  · exfalso
    refine v.evalAt_ne_zero hrat hne h0 ?_
    have hres : algebraMap K v.ResidueField
        (v.evalAt (f - algebraMap K F (v.evalAt f))) = 0 := by
      rw [v.algebraMap_evalAt hrat hmem]
      have hcoe : (⟨f - algebraMap K F (v.evalAt f), hmem⟩ : v.toValuationSubring)
          = ⟨f, hf⟩ - algebraMap K v.toValuationSubring (v.evalAt f) := by
        refine Subtype.ext ?_
        show f - algebraMap K F (v.evalAt f)
          = f - (algebraMap K v.toValuationSubring (v.evalAt f) : F)
        rw [Place.coe_algebraMap]
      rw [hcoe, map_sub, sub_eq_zero, ← v.algebraMap_evalAt hrat hf,
        IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
        IsLocalRing.ResidueField.algebraMap_eq]
    exact (map_eq_zero_iff _ (algebraMap K v.ResidueField).injective).mp hres
  · have hnonneg := v.ord_nonneg_of_mem hmem
    omega

end Place

section ConstantsAreBase

variable [HasPrincipalDivisors K F]

/-- The pin's `AlgebraicCurve.Place.eq_algebraMap_of_forall_ord_nonneg` (pin 2827):
a nonzero element of the function field whose order is nonnegative everywhere is a
constant. -/
theorem Place.eq_algebraMap_of_forall_ord_nonneg (v₀ : Place K F) (hrat : v₀.IsRational)
    (hdeg : v₀.deg ≠ 0) {g : F} (hg : g ≠ 0) (hord : ∀ v : Place K F, 0 ≤ v.ord g) :
    ∃ c : K, g = algebraMap K F c := by
  have hg₀ : g ∈ v₀.toValuationSubring := v₀.mem_of_ord_nonneg hg (hord v₀)
  refine ⟨v₀.evalAt g, ?_⟩
  by_contra hne
  set t : F := g - algebraMap K F (v₀.evalAt g) with ht
  have htne : t ≠ 0 := sub_ne_zero.mpr hne
  have hzero : 0 < v₀.ord t := v₀.ord_sub_evalAt_pos hrat hg₀ htne
  have hpole : ∀ v : Place K F, 0 ≤ v.ord t := fun v =>
    v.ord_nonneg_of_mem (sub_mem (v.mem_of_ord_nonneg hg (hord v)) (v.algebraMap_mem' _))
  obtain ⟨D, hD, hdeg0⟩ := HasPrincipalDivisors.exists_divisor (K := K) t htne
  have hDpos : 0 < D v₀ := by rw [hD v₀]; exact hzero
  have hDnonneg : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact hpole v
  have hmem : v₀ ∈ D.support := Finsupp.mem_support_iff.mpr hDpos.ne'
  have hpos : 0 < Divisor.degree D := by
    rw [Divisor.degree_eq_sum_support]
    calc (0 : ℤ) < D v₀ * (v₀.deg : ℤ) :=
          mul_pos hDpos (by exact_mod_cast Nat.pos_of_ne_zero hdeg)
      _ ≤ ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
          Finset.single_le_sum
            (fun v _ => mul_nonneg (hDnonneg v) (Int.natCast_nonneg _)) hmem
  omega

end ConstantsAreBase

section ConstantsAreBaseAdapters

/-- The pin's `AlgebraicCurve.constantsAreBase_of_exists_isRational` (pin 2865). -/
theorem constantsAreBase_of_exists_isRational [HasPrincipalDivisors K F]
    (v₀ : Place K F) (hrat : v₀.IsRational) (hdeg : v₀.deg ≠ 0) :
    ConstantsAreBase K F := by
  refine le_antisymm (fun f hf => ?_) (fun f ⟨c, hc⟩ => hc ▸ algebraMap_mem_lSpace_zero c)
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · have hord : ∀ v : Place K F, 0 ≤ v.ord f := by
      have h := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
      simpa using h
    obtain ⟨c, hc⟩ := Place.eq_algebraMap_of_forall_ord_nonneg v₀ hrat hdeg hf0 hord
    exact ⟨c, hc.symm⟩

/-- The pin's `AlgebraicCurve.constantsAreBase_of_deg_eq_one` (pin 2887). -/
theorem constantsAreBase_of_deg_eq_one [HasPrincipalDivisors K F]
    (v₀ : Place K F) (hdeg : v₀.deg = 1) :
    ConstantsAreBase K F :=
  constantsAreBase_of_exists_isRational v₀ ((Place.isRational_iff_deg_eq_one v₀).mpr hdeg)
    (hdeg ▸ one_ne_zero)

end ConstantsAreBaseAdapters

/-! ## Riemann-index / duality adapters -/

section WeilDualityAdelicRows

variable (K F)

/-- The pin's `AlgebraicCurve.weilDualityAdelic_of_residueRows` (pin 3262). -/
theorem weilDualityAdelic_of_residueRows (hΩℓ : WeilOmegaEllAgrees K F) :
    WeilDualityAdelic K F := by
  intro _ _ _ ω hω D
  rw [← finrank_omegaSpace_eq_indexOfSpecialty]
  exact hΩℓ hω D

end WeilDualityAdelicRows

/-- The pin's `AlgebraicCurve.riemannIndexFormula_of_genusReached` (pin 3592). -/
theorem riemannIndexFormula_of_genusReached
    (hg : ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
      RiemannGenusReached K F (genus K F)) :
    RiemannIndexFormula K F := by
  intro _ _ D
  obtain ⟨hne, hL0, D₀, hD₀⟩ := hg
  haveI := hne; haveI := hL0
  exact (indexOfSpecialty_eq_of_genusReached hD₀ D).2

/-- The pin's `AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula`
(pin 3747): Riemann's inequality from the index formula. -/
theorem degree_add_one_sub_genus_le_ell_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) (D : Divisor K F) :
    Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ) := by
  have hi := hRI D
  have hi0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

/-- The pin's `AlgebraicCurve.omegaSpace_finite_of_riemannIndexFormula` (pin 3755). -/
theorem omegaSpace_finite_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) {D : Divisor K F}
    (hpos : 0 < (ell D : ℤ) - Divisor.degree D - 1 + (genus K F : ℤ)) :
    Module.Finite K (omegaSpace (K := K) (F := F) D) := by
  have h0 : 0 < finrank K (adeleSpace K F ⧸ adeleBddPrincipal K F D) := by
    rw [← indexOfSpecialty_eq]
    have hi := hRI D
    have h0' : (0 : ℤ) < (indexOfSpecialty D : ℤ) := by linarith
    exact_mod_cast h0'
  haveI : Module.Finite K (adeleSpace K F ⧸ adeleBddPrincipal K F D) :=
    FiniteDimensional.of_finrank_pos h0
  exact Module.Finite.equiv (omegaSpaceEquivIndexDual D).symm

/-- The pin's `AlgebraicCurve.lSpace_finite_of_riemannIndexFormula` (pin 3770). -/
theorem lSpace_finite_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (hRI : RiemannIndexFormula K F) {D : Divisor K F}
    (hpos : 0 < Divisor.degree D + 1 - (genus K F : ℤ)) :
    Module.Finite K (LSpace (K := K) (F := F) D) := by
  have h0 : (0 : ℤ) < (ell D : ℤ) :=
    lt_of_lt_of_le hpos (degree_add_one_sub_genus_le_ell_of_riemannIndexFormula hRI D)
  exact FiniteDimensional.of_finrank_pos (by exact_mod_cast h0)

/-- The pin's `AlgebraicCurve.exists_weilSmul_eq_of_riemannIndexFormula` (pin 3779):
the rank-one statement, with `genus K F` in place of the Stichtenoth witness. -/
theorem exists_weilSmul_eq_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F)
    {φ μ : Module.Dual K (adeleSpace K F)} {W : Divisor K F}
    (hφ : φ ∈ omegaSpace W) (hμ : μ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :
    ∃ f : F, μ = weilSmul K F f φ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨P⟩ := ‹Nonempty (Place K F)›
  set n : ℕ := 3 * genus K F + 2 * (Divisor.degree W).natAbs + 4 with hn
  set D : Divisor K F := -Finsupp.single P (n : ℤ) with hD
  have hdegD : Divisor.degree D = -(n : ℤ) * (P.deg : ℤ) := by
    rw [hD, map_neg, Divisor.degree_single]; ring
  have hdegWD : Divisor.degree (W - D) = Divisor.degree W + (n : ℤ) * (P.deg : ℤ) := by
    rw [map_sub, hdegD]; ring
  have hPdeg1 : 1 ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
  have hg0 : (0 : ℤ) ≤ (genus K F : ℤ) := Int.natCast_nonneg _
  have habs0 : (0 : ℤ) ≤ |Divisor.degree W| := abs_nonneg _
  have habsW : -|Divisor.degree W| ≤ Divisor.degree W := neg_abs_le _
  have habsW' : Divisor.degree W ≤ |Divisor.degree W| := le_abs_self _
  have hn_ge : 3 * (genus K F : ℤ) + 2 * |Divisor.degree W| + 4 ≤ (n : ℤ) := by
    rw [hn]; push_cast [Int.natCast_natAbs]; ring_nf; omega
  have hndegP : (n : ℤ) ≤ (n : ℤ) * (P.deg : ℤ) := by nlinarith [Int.natCast_nonneg n]
  have hndegP_pos : 0 < (n : ℤ) * (P.deg : ℤ) := by nlinarith
  have hellD : ell D = 0 := ell_eq_zero_of_degree_neg (by rw [hdegD]; linarith)
  have hiD : (indexOfSpecialty D : ℤ) = (n : ℤ) * (P.deg : ℤ) - 1 + (genus K F : ℤ) := by
    have h := hRI D
    rw [hellD, hdegD] at h; push_cast at h; linarith
  have hlowerWD : Divisor.degree W + (n : ℤ) * (P.deg : ℤ) + 1 - (genus K F : ℤ)
      ≤ (ell (W - D) : ℤ) := by
    have h := degree_add_one_sub_genus_le_ell_of_riemannIndexFormula hRI (W - D)
    rw [hdegWD] at h; exact h
  have hiDpos : 0 < (ell D : ℤ) - Divisor.degree D - 1 + (genus K F : ℤ) := by
    rw [hellD, hdegD]; push_cast; nlinarith
  have hellWDpos : 0 < Divisor.degree (W - D) + 1 - (genus K F : ℤ) := by
    rw [hdegWD]; nlinarith
  haveI := omegaSpace_finite_of_riemannIndexFormula hRI hiDpos
  haveI := lSpace_finite_of_riemannIndexFormula hRI hellWDpos
  have hdbl : (2 * ell (W - D) : ℤ) ≤ (indexOfSpecialty D : ℤ) := by
    exact_mod_cast two_mul_ell_le_indexOfSpecialty W D hφ hμ hφ0 hcon
  rw [hiD] at hdbl
  nlinarith

/-- The pin's `AlgebraicCurve.weilDifferentialRankOne_of_riemannIndexFormula`
(pin 3833). -/
theorem weilDifferentialRankOne_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F) :
    WeilDifferentialRankOne K F := by
  intro φ hφmem hφ0 μ hμmem
  obtain ⟨W₁, hφW₁⟩ := mem_weilDifferentialModule_iff.mp hφmem
  obtain ⟨W₂, hμW₂⟩ := mem_weilDifferentialModule_iff.mp hμmem
  have hφW : φ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_left hφW₁
  have hμW : μ ∈ omegaSpace (W₁ ⊓ W₂) := omegaSpace_antitone inf_le_right hμW₂
  obtain ⟨f, hf⟩ := exists_weilSmul_eq_of_riemannIndexFormula hRI hφW hμW hφ0
  exact ⟨f, hf, fun f' hf' => weilSmul_left_injective hφ0 (hf'.symm.trans hf)⟩

section GenusIdentification

variable [IsCurveOver K F] [Nonempty (Place K F)]
  [FiniteDimensional K (LSpace (0 : Divisor K F))]

/-- The pin's `AlgebraicCurve.stichtenothGenus_nonneg` (pin 4031). -/
theorem stichtenothGenus_nonneg
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hC : ConstantsAreBase K F) : 0 ≤ γ := by
  have hi0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [_root_.map_zero, ell_zero_eq_one_of_constantsAreBase hC] at hi0
  have h0 : (0 : ℤ) ≤ (indexOfSpecialty (0 : Divisor K F) : ℤ) := Int.natCast_nonneg _
  push_cast at hi0; linarith

end GenusIdentification

section GenusDegreeDiv

variable [HasCanonicalDivisor (K := K) (F := F)] [Nontrivial Ω[F⁄K]]

/-- The pin's `AlgebraicCurve.genus_eq_degree_div` (pin 4042). -/
theorem genus_eq_degree_div :
    ∃ (ω₀ : Ω[F⁄K]) (hω₀ : ω₀ ≠ 0),
      genus K F = (Divisor.degree (canonicalDivisorOf hω₀) + 2).toNat / 2 := by
  have hne : ∃ ω : Ω[F⁄K], ω ≠ 0 := exists_ne 0
  refine ⟨hne.choose, hne.choose_spec, ?_⟩
  rw [genus, dif_pos hne]

end GenusDegreeDiv

/-! ## The residue pairing and the Kähler differential -/

/-- The pin's `AlgebraicCurve.mem_lSpace_of_weilSmul_mem_omegaSpace` (pin 4644). -/
theorem mem_lSpace_of_weilSmul_mem_omegaSpace [HasPrincipalDivisors K F]
    {W D : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W)
    {f : F} (hfφ : weilSmul K F f φ ∈ omegaSpace D) :
    f ∈ LSpace (W - D) := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact (LSpace (W - D)).zero_mem
  · obtain ⟨P, hPord, _⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
    have hPinv : ∀ v : Place K F, (-P) v = v.ord f⁻¹ := fun v => by
      rw [Finsupp.neg_apply, hPord, v.ord_inv]
    have hφshift : φ ∈ omegaSpace (D - P) := by
      have hinv : weilSmul K F f⁻¹ (weilSmul K F f φ) = φ := by
        rw [← LinearMap.comp_apply, ← weilSmul_mul, mul_inv_cancel₀ hf, weilSmul_one,
          LinearMap.id_apply]
      have h := weilSmul_mem_omegaSpace_add (inv_ne_zero hf) hPinv hfφ
      rwa [hinv, ← sub_eq_add_neg] at h
    have hle := hWmax (D - P) hφshift
    refine mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)
    have hlev := hle v
    rw [Finsupp.sub_apply, hPord v] at hlev
    rw [Finsupp.sub_apply]
    linarith

/-- The pin's `AlgebraicCurve.residuePairing_surjective` (pin 4682). -/
theorem residuePairing_surjective [HasPrincipalDivisors K F]
    (hRk1 : WeilDifferentialRankOne K F) (W D : Divisor K F)
    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)
    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) :
    Function.Surjective (residuePairing K F W D hφ) := by
  rintro ⟨μ, hμD⟩
  have hφmem : φ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule W hφ
  have hμmem : μ ∈ weilDifferentialModule K F := omegaSpace_le_weilDifferentialModule D hμD
  obtain ⟨f, hf, -⟩ := hRk1 hφmem hφ0 hμmem
  have hfL : f ∈ LSpace (W - D) :=
    mem_lSpace_of_weilSmul_mem_omegaSpace hWmax (hf ▸ hμD)
  exact ⟨⟨f, hfL⟩, Subtype.ext hf.symm⟩

/-- The pin's `AlgebraicCurve.residuePairingSurjective_of_weilDifferentialRankOne`
(pin 4709). -/
theorem residuePairingSurjective_of_weilDifferentialRankOne [HasPrincipalDivisors K F]
    (hRk1 : WeilDifferentialRankOne K F) : ResiduePairingSurjective K F := by
  intro _ W D φ hφ hφ0 hWmax
  exact residuePairing_surjective hRk1 W D hφ hφ0 hWmax

/-- The pin's `AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula`
(pin 4726). -/
theorem residuePairingSurjective_of_riemannIndexFormula
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F) : ResiduePairingSurjective K F :=
  residuePairingSurjective_of_weilDifferentialRankOne
    (weilDifferentialRankOne_of_riemannIndexFormula hRI)

section WeilOfKaehlerK

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates]

/-- The K twin of `weilOfKaehler_mem_omegaSpace_of_residueTheorem` (pin 4758). -/
theorem weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK [HasPrincipalDivisors K F]
    (hRT : ResidueTheoremK K F) (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    weilOfKaehlerK Rfam hω ∈ omegaSpace (canonicalDivisorOf hω) := by
  rw [omegaSpace, Submodule.mem_dualAnnihilator]
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Submodule.mem_sup.mp hα
  rw [map_add, weilOfKaehlerK_vanish_adeleBdd_canonical Rfam hω (Submodule.mem_comap.mp hβ)]
  obtain ⟨f, hf⟩ := Submodule.mem_comap.mp hγ
  have hγ' : γ = ⟨diagonalHom K F f, diagonal_mem_adeleSpace f⟩ := Subtype.ext hf.symm
  rw [hγ', hRT Rfam hω f, add_zero]

end WeilOfKaehlerK

namespace Place

/-- Re-provision of the pin's `private` `_root_.AlgebraicCurve.Place.exists_trace_residue_ne_zero`
(pin 4863); the identical declaration is `private` in the frozen
`Defs/WeilOfKaehler.lean:274` (promotion debt). -/
private theorem exists_trace_residue_ne_zero [HasSeparableResidue K F] (v : Place K F) :
    ∃ c : v.toValuationSubring,
      Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) ≠ 0 := by
  have htr := HasSeparableResidue.trace_ne_zero (K := K) (F := F) v
  rw [ne_eq, LinearMap.ext_iff, not_forall] at htr
  obtain ⟨x, hx⟩ := htr
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  exact ⟨c, by simpa using hx⟩

end Place

end AlgebraicCurve

/-! ## The `ModularCurve` assembly (pin 5931 and 5971–6257) -/

namespace ModularCurve

open AlgebraicCurve

section AlgClosedEngine

variable (K F : Type*) [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [DecidableEq (RatFunc K)]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsAlgClosed K] [IsCurveOver K F]

/-- The pin's `ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed` (pin 5931). -/
theorem p0n20_rr_constantsAreBase_of_isAlgClosed : ConstantsAreBase K F := by
  obtain ⟨v⟩ := RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  exact constantsAreBase_of_deg_eq_one v (IsCurveOver.deg_eq_one_of_isAlgClosed v)

end AlgClosedEngine

section CanonicalProbe

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]

/-- The pin's `p0n25_wkc_kaehlerResidueTermKFam_single_of_ne` (pin 5971). -/
theorem p0n25_wkc_kaehlerResidueTermKFam_single_of_ne
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK) (ω : Ω[F⁄K])
    {v : Place K F} (g : F) {w : Place K F} (hw : w ≠ v) :
    kaehlerResidueTermKFam Rfam ω (Pi.single v g) w = 0 := by
  rw [kaehlerResidueTermKFam_apply, Pi.single_eq_of_ne hw, zero_mul, _root_.map_zero,
    _root_.map_zero]

/-- The pin's `p0n25_wkc_localResidueData_res_mul_uniformizer_inv` (pin 5977). -/
theorem p0n25_wkc_localResidueData_res_mul_uniformizer_inv
    {v : Place K F} (R : v.LocalResidueData) (c : v.toValuationSubring) :
    R.res ((c : F) * v.uniformizer⁻¹) = IsLocalRing.residue _ c := by
  have hmul : v.uniformizer * ((c : F) * v.uniformizer⁻¹) = (c : F) := by
    rw [mul_comm (c : F), ← mul_assoc, mul_inv_cancel₀ v.uniformizer_ne_zero, one_mul]
  have hmem : v.uniformizer * ((c : F) * v.uniformizer⁻¹) ∈ v.toValuationSubring := by
    rw [hmul]; exact c.2
  rw [R.res_simplePole _ hmem]
  congr 1
  exact Subtype.ext hmul

variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]

/-- The pin's `p0n25_wkc_weilOfKaehlerK_single` (pin 5992). -/
theorem p0n25_wkc_weilOfKaehlerK_single
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (g : F) :
    weilOfKaehlerK Rfam hω (adeleSingle v g)
      = Algebra.trace K v.ResidueField ((Rfam v).res (g * v.differentialCoeff ω)) := by
  rw [weilOfKaehlerK_apply, adeleSingle_coe]
  refine (finsum_eq_single _ v
    fun w hw => p0n25_wkc_kaehlerResidueTermKFam_single_of_ne Rfam ω g hw).trans ?_
  rw [kaehlerResidueTermKFam_apply, Pi.single_eq_same]

/-- The pin's `p0n25_wkc_weilOfKaehlerK_simplePoleProbe` (pin 6002). -/
theorem p0n25_wkc_weilOfKaehlerK_simplePoleProbe
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (c : v.toValuationSubring) :
    weilOfKaehlerK Rfam hω (simplePoleProbe hω v c)
      = Algebra.trace K v.ResidueField (IsLocalRing.residue _ c) := by
  unfold simplePoleProbe
  rw [p0n25_wkc_weilOfKaehlerK_single Rfam hω,
    mul_assoc, inv_mul_cancel₀ (v.differentialCoeff_ne_zero hω), mul_one,
    p0n25_wkc_localResidueData_res_mul_uniformizer_inv (Rfam v).toLocalResidueData c]

end CanonicalProbe

section CanonicalNonvanishingMaximality

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable [Nontrivial Ω[F⁄K]]

/-- The pin's `p0n25_wkc_weilOfKaehlerK_ne_zero` (pin 6020). -/
theorem p0n25_wkc_weilOfKaehlerK_ne_zero [HasSeparableResidue K F] [Nonempty (Place K F)]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : weilOfKaehlerK Rfam hω ≠ 0 := by
  obtain ⟨v⟩ := ‹Nonempty (Place K F)›
  obtain ⟨c, hc⟩ := v.exists_trace_residue_ne_zero
  intro h
  apply hc
  rw [← p0n25_wkc_weilOfKaehlerK_simplePoleProbe Rfam hω v c, h, LinearMap.zero_apply]

/-- The pin's `p0n25_wkc_trace_eq_zero_of_weilOfKaehlerK_mem` (pin 6029). -/
theorem p0n25_wkc_trace_eq_zero_of_weilOfKaehlerK_mem
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : weilOfKaehlerK Rfam hω ∈ omegaSpace D)
    {v : Place K F} (hDv : canonicalDivisorOf hω v < D v) :
    (Algebra.trace K v.ResidueField : _ →ₗ[K] K) = 0 := by
  ext x
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective x
  rw [LinearMap.zero_apply, ← p0n25_wkc_weilOfKaehlerK_simplePoleProbe Rfam hω v c]
  exact omegaSpace_vanishBdd hD (simplePoleProbe_mem_adeleBdd hω v c hDv)

/-- The pin's `p0n25_wkc_weilOfKaehlerK_omegaSpace_le_canonical` (pin 6040). -/
theorem p0n25_wkc_weilOfKaehlerK_omegaSpace_le_canonical [HasSeparableResidue K F]
    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {D : Divisor K F}
    (hD : weilOfKaehlerK Rfam hω ∈ omegaSpace D) :
    D ≤ canonicalDivisorOf hω := by
  intro v
  rcases le_or_gt (D v) (canonicalDivisorOf hω v) with h | h
  · exact h
  · exact absurd (p0n25_wkc_trace_eq_zero_of_weilOfKaehlerK_mem Rfam hω hD h)
      (HasSeparableResidue.trace_ne_zero v)

end CanonicalNonvanishingMaximality

section CanonicalSupply

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
variable [Nontrivial Ω[F⁄K]]

/-- The pin's `p0n25_wkc_exists_weilMax_of_residueTheoremK` (pin 6059). -/
theorem p0n25_wkc_exists_weilMax_of_residueTheoremK
    [HasSeparableResidue K F] [Nonempty (Place K F)] [HasPrincipalDivisors K F]
    (hRTK : ResidueTheoremK K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    ∃ φ : Module.Dual K (adeleSpace K F), φ ≠ 0 ∧
      φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω :=
  ⟨weilOfKaehlerK (fun v => v.canonicalLocalResidueDataKOfExtend) hω,
    p0n25_wkc_weilOfKaehlerK_ne_zero _ hω,
    weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK hRTK _ hω,
    fun _ hD => p0n25_wkc_weilOfKaehlerK_omegaSpace_le_canonical _ hω hD⟩

end CanonicalSupply

section MirrorIdentification

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates]
variable [Nonempty (Place K F)] [FiniteDimensional K (LSpace (0 : Divisor K F))]

/-- The pin's `p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax`
(pin 6080). -/
theorem p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0)
    {φ : Module.Dual K (adeleSpace K F)} (hne : φ ≠ 0)
    (hmem : φ ∈ omegaSpace (canonicalDivisorOf hω))
    (hmax : ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (D : Divisor K F) :
    Module.finrank K (omegaSpace (K := K) (F := F) D) = ell (canonicalDivisorOf hω - D) := by
  have hinj := residuePairing_injective (canonicalDivisorOf hω) D hmem hne
  have hsurj := residuePairing_surjective_of_rankOne_max
    (weilDifferentialRankOne_of_genusReached h) hmem hne hmax D
  exact (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).finrank_eq.symm

/-- The pin's `p0n25_wkc_ell_canonicalDivisor_eq_gamma_of_weilMax` (pin 6093). -/
theorem p0n25_wkc_ell_canonicalDivisor_eq_gamma_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (ell (canonicalDivisorOf hω) : ℤ) = γ := by
  obtain ⟨φ, hne, hmem, hmax⟩ := hsup hω
  have hΩ0 := p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
    h hω hne hmem hmax 0
  rw [sub_zero] at hΩ0
  have hi0 := (indexOfSpecialty_eq_of_genusReached h 0).2
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, hΩ0, _root_.map_zero,
    ell_zero_eq_one_of_constantsAreBase hC] at hi0
  push_cast at hi0
  linarith

/-- The pin's `p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax` (pin 6110). -/
theorem p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * γ - 2 := by
  obtain ⟨φ, hne, hmem, hmax⟩ := hsup hω
  have hΩW := p0n25_wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
    h hω hne hmem hmax (canonicalDivisorOf hω)
  rw [sub_self] at hΩW
  have hiW := (indexOfSpecialty_eq_of_genusReached h (canonicalDivisorOf hω)).2
  rw [← finrank_omegaSpace_eq_indexOfSpecialty, hΩW,
    ell_zero_eq_one_of_constantsAreBase hC] at hiW
  have hℓW := p0n25_wkc_ell_canonicalDivisor_eq_gamma_of_weilMax h hsup hC hω
  push_cast at hiW
  linarith

/-- The pin's `p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax` (pin 6128). -/
theorem p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    γ = (genus K F : ℤ) := by
  obtain ⟨ω₀, hω₀, hgen⟩ := genus_eq_degree_div (K := K) (F := F)
  have hdeg := p0n25_wkc_degree_canonicalDivisor_eq_of_weilMax h hsup hC hω₀
  have hγ0 := stichtenothGenus_nonneg h hC
  rw [hgen, hdeg]
  have h2 : (2 * γ - 2 + 2).toNat / 2 = γ.toNat := by omega
  rw [h2]
  exact (Int.toNat_of_nonneg hγ0).symm

end MirrorIdentification

section MirrorAssembly

variable (K : Type*) [Field K] [DecidableEq (RatFunc K)]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
variable [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
variable [∀ v : Place K F, v.DCoordGenerates]

/-- The pin's `p0n25_wkc_riemannGenusReached_of_weilMax` (pin 6155). -/
theorem p0n25_wkc_riemannGenusReached_of_weilMax
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    RiemannGenusReached K F (genus K F) := by
  obtain ⟨hne, hL0, γ, D₀, hD₀⟩ := RationalFunctionField.stichtenothGenusExists K F hC
  haveI := hne
  haveI := hL0
  have hγeq := p0n25_wkc_stichtenothGenus_eq_genus_of_weilMax hD₀ hsup hC
  exact ⟨hne, hL0, D₀, hγeq ▸ hD₀⟩

/-- The pin's `p0n25_wkc_riemannIndexFormula_of_weilMax` (pin 6167). -/
theorem p0n25_wkc_riemannIndexFormula_of_weilMax
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    RiemannIndexFormula K F := by
  refine riemannIndexFormula_of_genusReached ?_
  intro _ _
  exact p0n25_wkc_riemannGenusReached_of_weilMax K F hsup hC

/-- The pin's `p0n25_wkc_weilOmegaEllAgrees_of_weilMax` (pin 6177). -/
theorem p0n25_wkc_weilOmegaEllAgrees_of_weilMax [Nonempty (Place K F)]
    (hRI : RiemannIndexFormula K F)
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω) :
    WeilOmegaEllAgrees K F := by
  have hSurj : ResiduePairingSurjective K F :=
    residuePairingSurjective_of_riemannIndexFormula hRI
  intro _ _ _ ω hω D
  obtain ⟨φ, hne, hmem, hmax⟩ := hsup hω
  have hinj := residuePairing_injective (canonicalDivisorOf hω) D hmem hne
  have hsurj := hSurj (canonicalDivisorOf hω) D hmem hne hmax
  exact_mod_cast (LinearEquiv.ofBijective
    (residuePairing K F (canonicalDivisorOf hω) D hmem) ⟨hinj, hsurj⟩).finrank_eq.symm

/-- The pin's `p0n25_wkc_functionFieldRiemannRoch_of_weilMax_of_constantsAreBase`
(pin 6192). -/
theorem p0n25_wkc_functionFieldRiemannRoch_of_weilMax_of_constantsAreBase
    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),
      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧
      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)
    (hC : ConstantsAreBase K F) :
    FunctionFieldRiemannRoch K F := by
  have hRI : RiemannIndexFormula K F :=
    p0n25_wkc_riemannIndexFormula_of_weilMax K F hsup hC
  haveI := RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  have hΩℓ : WeilOmegaEllAgrees K F :=
    p0n25_wkc_weilOmegaEllAgrees_of_weilMax K F hRI hsup
  have hWDA : WeilDualityAdelic K F := weilDualityAdelic_of_residueRows K F hΩℓ
  have hWD : WeilDuality K F := weilDuality_of_riemannIndex_of_adelic K F hRI hWDA
  intro _ _ _ ω hω D
  exact functionFieldRiemannRoch_of_riemann_and_duality K F hWD hω D

/-- The pin's `p0n25_wkc_functionFieldRiemannRoch_of_residueTheoremK` (pin 6208). -/
theorem p0n25_wkc_functionFieldRiemannRoch_of_residueTheoremK
    [HasSeparableResidue K F]
    (hRTK : ResidueTheoremK K F) (hC : ConstantsAreBase K F) :
    FunctionFieldRiemannRoch K F := by
  haveI := RationalFunctionField.nonempty_place_of_ratFunc_tower K F
  intro _ _ _ ω hω D
  exact p0n25_wkc_functionFieldRiemannRoch_of_weilMax_of_constantsAreBase K F
    (fun {ω'} hω' => p0n25_wkc_exists_weilMax_of_residueTheoremK hRTK hω') hC hω D

end MirrorAssembly

end ModularCurve

/-! ## The public headline -/

theorem AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F]
    (hRTK : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F := by
  intro _ _ _
  exact ModularCurve.p0n25_wkc_functionFieldRiemannRoch_of_residueTheoremK K F
    (hRTK := hRTK) (hC := ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed K F)

/-! ## The `ℙ¹` `genusFF` closure (ds-head rider)

The pin nodes the `genusFF_ratFunc_eq_zero_of_isAlgClosed` headline cites. They are
landed in this leaf module rather than `RiemannRoch/Assembly.lean`, their other
natural home: `Assembly` is a hub whose one-token edit cascades to 56 modules /
≈484 s, while nothing imports `RRAssembly`. See `topics/riemannRoch/ds-head-recon.md`
§10. -/

open AlgebraicCurve

theorem AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) := by
  have h0 := hRR hω 0
  rw [map_zero, ell_zero_eq_one_of_constantsAreBase hC, sub_zero] at h0
  push_cast at h0
  linarith

theorem AlgebraicCurve.genus_eq_genusFF
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hWDA : WeilDualityAdelic K F)
    (hC : ConstantsAreBase K F) :
    genus K F = genusFF K F := by
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄K])
  have h1 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (ell (canonicalDivisorOf hω - 0) : ℤ) :=
    hWDA hω 0
  rw [sub_zero] at h1
  have h2 : (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) :=
    ell_canonicalDivisor_eq_genus_of_riemannRoch hRR hC hω
  have h3 : indexOfSpecialty (0 : Divisor K F) = Module.finrank K (H1 (0 : Divisor K F)) :=
    indexOfSpecialty_eq_finrank_H1 0
  have h4 : (indexOfSpecialty (0 : Divisor K F) : ℤ) = (genusFF K F : ℤ) := by
    rw [genusFF, ← h3]
  have : (genus K F : ℤ) = (genusFF K F : ℤ) := by
    rw [← h4, h1, h2]
  exact_mod_cast this

theorem AlgebraicCurve.constantsAreBase_of_isAlgClosed (K F : Type*) [Field K] [Field F] [Algebra K F]
    [DecidableEq (RatFunc K)] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]
    [IsAlgClosed K] [IsCurveOver K F] :
    ConstantsAreBase K F :=
  ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed K F

theorem AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [HasLocalResidue K F] [∀ w : Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
    [∀ u : Place K (RatFunc K), u.FiniteResidue]
    [HasCanonicalLocalResidueKStar K F]
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [HasSeparableResidue K F] :
    FunctionFieldRiemannRoch K F :=
  functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
    (hRTK := residueTheoremK_of_isAlgClosed)

theorem AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [∀ w : Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
    [∀ u : Place K (RatFunc K), u.FiniteResidue]
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] :
    FunctionFieldRiemannRoch K F := by
  haveI : HasCanonicalLocalResidueKStar K F := instHasCanonicalLocalResidueKStar
  haveI : HasSeparableResidue K F := HasSeparableResidue.of_perfectField_of_isCurveOver
  intro _ _ _ ω hω D
  exact functionFieldRiemannRoch_of_isAlgClosed (K := K) (F := F) hω D

end
