/-
  Gauss prolongation of a regular prolongation: a polynomial over the base field
  whose value at an integral element lands back in the prolongation's integers has
  all its coefficients in the base valuation subring, and consequently the residue
  of an element of a purely transcendental simple extension `L(f)` which is
  integral for two prolongations along the same `f` lies in the residue field's own
  simple extension `ResidueField A (residue f)`.

  The port of the two pin leaves

      `AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers` and
      `GaussProlongation.residue_mem_adjoin_residue_of_mem_adjoin_integers`

  (`Theorems/Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers.lean`,
  `Theorems/Thm_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers.lean`,
  with proofs from the matching `P2M/Sol/S_…` files — 121 + 181 pin lines). The pin's
  inner namespaces are kept verbatim: `AlgebraicCurve.RegularProlongation` for the
  first node, `PsiSol` plus the `GaussProlongation` headline for the second; the
  pin's `solution` wrappers are not ported.

  The mathematics. `coeff_mem_of_aeval_mem_integers` picks the coefficient of
  maximal valuation: if some coefficient `c j₀` were outside `A`, then `s =
  (c j₀)⁻¹` is a nonunit, hence has residue `0`, and `s • c` is an integral
  polynomial `c'` with `c'.coeff j₀ = 1`; reducing `c'` at `R` gives a nonzero
  polynomial vanishing at the transcendental `R.residue x`, a contradiction.
  `residue_mem_adjoin_residue_of_mem_adjoin_integers` writes `w = r / s` in
  `L(f)`, clears denominators along `f` using `exists_smul_mem`, applies the
  coefficient bound to `c s` and `c r`, and reads the result off as
  `residue w · residue q = residue p` with `residue q ≠ 0`.

  Assumes: `FLTForHuman/AlgebraicCurve/RegularProlongation.lean` (the pin's
  `Definitions/Def_AlgebraicCurve_RegularProlongation.lean`), and mathlib `v4.34.0`.

  spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_coeff_mem_of_aeval_mem_integers.lean
  spec-pin: Theorems/Thm_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers.lean
  spec-pin: P2M/Sol/S_GaussProlongation_residue_mem_adjoin_residue_of_mem_adjoin_integers.lean
  Drift against `v4.34.0` — all four sites are proof-only; no statement moved.

  * port:141, 149, 152, 175 — the pin's bare `residue A` becomes
    `IsLocalRing.residue A`. The port homes `AlgebraicCurve.RegularProlongation`,
    whose field `residue` is a projection named `residue`; with `open AlgebraicCurve`
    that projection shadows `IsLocalRing.residue`, and `A : ValuationSubring L` no
    longer unifies with the structure's `integers`. (The pin's `S_` file has the same
    `open`s and the same theorem, so this is a v4.34 resolution change.)
  * port:114, 123, 248 — `Polynomial.finset_sum_coeff` → `Polynomial.finsetSum_coeff`
    (deprecated alias).
  * port:125 — `if_pos` → `ite_eq_left` (deprecated alias).

-/

import FLTForHuman.AlgebraicCurve.RegularProlongation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic

open AlgebraicCurve IsLocalRing Polynomial

set_option autoImplicit false

/-- If the value at an integral element `x` of a polynomial `c` over the base field
lies in the prolongation's integers and the residue of `x` is transcendental over
the residue field, then every coefficient of `c` lies in the base valuation
subring. -/
theorem AlgebraicCurve.RegularProlongation.coeff_mem_of_aeval_mem_integers
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (c : Polynomial L) (hc : Polynomial.aeval (x : F) c ∈ R.integers) (i : ℕ) :
    c.coeff i ∈ A := by
  classical

  by_cases hci : c.coeff i = 0
  · exact hci ▸ A.zero_mem
  have hi : i ∈ c.support := Polynomial.mem_support_iff.mpr hci

  obtain ⟨j₀, hj₀, hj₀max⟩ := Finset.exists_max_image c.support
    (fun j => A.valuation (c.coeff j)) ⟨i, hi⟩
  have hcj₀ : c.coeff j₀ ≠ 0 := Polynomial.mem_support_iff.mp hj₀

  suffices hAj₀ : c.coeff j₀ ∈ A by
    rw [← A.valuation_le_one_iff] at hAj₀ ⊢
    exact (hj₀max i hi).trans hAj₀
  by_contra hnA

  set s : L := (c.coeff j₀)⁻¹ with hs
  have hsnon : s ∈ A.nonunits := A.inv_mem_nonunits_iff.mpr (Or.inr hnA)
  have hsA : s ∈ A := (A.valuation_le_one_iff s).mp (A.mem_nonunits_iff.mp hsnon).le
  have hsres : IsLocalRing.residue A ⟨s, hsA⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr (A.coe_mem_nonunits_iff.mp hsnon)

  have hcoeff : ∀ j, s * c.coeff j ∈ A := by
    intro j
    by_cases hj : j ∈ c.support
    · have hv := hj₀max j hj
      rw [← A.valuation_le_one_iff, map_mul, hs, map_inv₀]
      have hvj₀ : A.valuation (c.coeff j₀) ≠ 0 := by
        simp only [ne_eq, map_eq_zero]; exact hcj₀
      calc (A.valuation (c.coeff j₀))⁻¹ * A.valuation (c.coeff j)
          ≤ (A.valuation (c.coeff j₀))⁻¹ * A.valuation (c.coeff j₀) :=
            mul_le_mul_right hv _
        _ = 1 := inv_mul_cancel₀ hvj₀
    · rw [Polynomial.notMem_support_iff.mp hj, mul_zero]; exact A.zero_mem

  set c' : Polynomial A := c.support.sum
    (fun j => Polynomial.C ⟨s * c.coeff j, hcoeff j⟩ * Polynomial.X ^ j) with hc'
  have hc'map : c'.map A.subtype = s • c := by
    rw [hc']; ext j
    simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero, Polynomial.coeff_smul, smul_eq_mul]
    rw [Finset.sum_ite_eq c.support j]
    by_cases hj : j ∈ c.support
    · simp [hj]
    · simp [hj, Polynomial.notMem_support_iff.mp hj]

  have hc'j₀ : c'.coeff j₀ = 1 := by
    rw [hc']
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq c.support j₀, ite_eq_left hj₀]
    exact Subtype.ext (show s * c.coeff j₀ = 1 from by rw [hs, inv_mul_cancel₀ hcj₀])

  set cbar : Polynomial (ResidueField A) := c'.map (IsLocalRing.residue A) with hcbar
  have hcbar0 : cbar ≠ 0 := by
    intro h0
    have : cbar.coeff j₀ = 0 := by rw [h0]; simp
    rw [hcbar, Polynomial.coeff_map, hc'j₀, map_one] at this
    exact one_ne_zero this

  let φ : A →+* R.integers :=
    { toFun := fun a => ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hresφ : R.residue.comp φ = (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A) := by
    ext a; exact R.residue_algebraMap a

  have hresEval : R.residue (Polynomial.eval₂ φ x c') =
      Polynomial.aeval (R.residue x) cbar := by
    calc R.residue (Polynomial.eval₂ φ x c')
        = Polynomial.eval₂ (R.residue.comp φ) (R.residue x) c' :=
          Polynomial.hom_eval₂ c' φ R.residue x
      _ = Polynomial.eval₂ ((algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A))
            (R.residue x) c' := by rw [hresφ]
      _ = Polynomial.eval₂ (algebraMap (ResidueField A) Fbar) (R.residue x)
            (c'.map (IsLocalRing.residue A)) := by rw [Polynomial.eval₂_map]
      _ = Polynomial.aeval (R.residue x) cbar := by rw [hcbar, Polynomial.aeval_def]
  have hne0 : R.residue (Polynomial.eval₂ φ x c') ≠ 0 := by
    rw [hresEval]
    exact fun h => hx ⟨cbar, hcbar0, h⟩

  have hfactor : (Polynomial.eval₂ φ x c' : R.integers) = φ ⟨s, hsA⟩ * ⟨_, hc⟩ := by
    apply Subtype.ext
    show ((Polynomial.eval₂ φ x c' : R.integers) : F) =
      algebraMap L F s * Polynomial.aeval (x : F) c
    have h1 : ((Polynomial.eval₂ φ x c' : R.integers) : F) =
        Polynomial.eval₂ ((algebraMap L F).comp A.subtype) (↑x) c' := by
      have hsub : R.integers.subtype.comp φ = (algebraMap L F).comp A.subtype := by
        ext a; rfl
      rw [← hsub]
      exact Polynomial.hom_eval₂ c' φ R.integers.subtype x
    rw [h1, ← Polynomial.eval₂_map, ← Polynomial.aeval_def, hc'map, map_smul,
      Algebra.smul_def]
  apply hne0
  rw [hfactor, map_mul]
  have hresφs : R.residue (φ ⟨s, hsA⟩) = 0 := by
    change (R.residue.comp φ) ⟨s, hsA⟩ = 0
    rw [hresφ]
    change algebraMap (ResidueField A) Fbar (IsLocalRing.residue A ⟨s, hsA⟩) = 0
    rw [hsres, map_zero]
  rw [hresφs, zero_mul]

noncomputable section

namespace PsiSol

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : RegularProlongation A F Fbar)
variable (f : F) (hf : f ∈ R.integers)

/-- The constants of `A` read inside the prolongation's integers. -/
def φ : A →+* R.integers where
  toFun a := ⟨algebraMap L F a, (R.algebraMap_mem_iff a).mpr a.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- `φ` followed by the residue map is the base residue map followed by the residue
field extension. -/
lemma residue_comp_φ :
    R.residue.comp (φ A R) = (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A) :=
  RingHom.ext fun a => R.residue_algebraMap a

/-- `φ` followed by the inclusion of the integers in `F` is the base field map. -/
lemma subtype_comp_φ : R.integers.subtype.comp (φ A R) = (algebraMap L F).comp A.subtype :=
  RingHom.ext fun _ => rfl

include hf in

/-- Evaluating an integral polynomial at `f` inside the integers, then mapping to `F`,
is the same as evaluating the mapped polynomial at `f`. -/
lemma coe_eval₂_φ (gA : Polynomial A) :
    ((Polynomial.eval₂ (φ A R) ⟨f, hf⟩ gA : R.integers) : F) = aeval f (gA.map A.subtype) := by
  calc ((Polynomial.eval₂ (φ A R) ⟨f, hf⟩ gA : R.integers) : F)
      = Polynomial.eval₂ (R.integers.subtype.comp (φ A R)) f gA :=
        Polynomial.hom_eval₂ gA (φ A R) R.integers.subtype ⟨f, hf⟩
    _ = Polynomial.eval₂ ((algebraMap L F).comp A.subtype) f gA := by rw [subtype_comp_φ]
    _ = Polynomial.eval₂ (algebraMap L F) f (gA.map A.subtype) :=
        (Polynomial.eval₂_map A.subtype (algebraMap L F) f).symm
    _ = aeval f (gA.map A.subtype) := (Polynomial.aeval_def _ _).symm

include hf in

/-- Evaluating an integral polynomial at `f` and then reducing is the same as
evaluating the reduced polynomial at the residue of `f`. -/
lemma residue_eval₂_φ (gA : Polynomial A) :
    R.residue (Polynomial.eval₂ (φ A R) ⟨f, hf⟩ gA) =
      aeval (R.residue ⟨f, hf⟩) (gA.map (IsLocalRing.residue A)) := by
  calc R.residue (Polynomial.eval₂ (φ A R) ⟨f, hf⟩ gA)
      = Polynomial.eval₂ (R.residue.comp (φ A R)) (R.residue ⟨f, hf⟩) gA :=
        Polynomial.hom_eval₂ gA (φ A R) R.residue ⟨f, hf⟩
    _ = Polynomial.eval₂ ((algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A))
          (R.residue ⟨f, hf⟩) gA := by rw [residue_comp_φ]
    _ = Polynomial.eval₂ (algebraMap (ResidueField A) Fbar) (R.residue ⟨f, hf⟩)
          (gA.map (IsLocalRing.residue A)) := (Polynomial.eval₂_map _ _ _).symm
    _ = aeval (R.residue ⟨f, hf⟩) (gA.map (IsLocalRing.residue A)) :=
        (Polynomial.aeval_def _ _).symm

/-- An integral polynomial over `A` attached to a polynomial over `L` with all
coefficients in `A`. -/
def liftA (g : L[X]) (hg : ∀ j, g.coeff j ∈ A) : Polynomial A :=
  g.support.sum fun j => C ⟨g.coeff j, hg j⟩ * X ^ j

/-- `liftA` is a section of `Polynomial.map A.subtype`. -/
lemma liftA_map (g : L[X]) (hg : ∀ j, g.coeff j ∈ A) :
    (liftA A g hg).map A.subtype = g := by
  ext j
  simp only [liftA, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq g.support j]
  by_cases hj : j ∈ g.support
  · simp [hj]
  · simp [hj, Polynomial.notMem_support_iff.mp hj]

/-- A value of a polynomial at `x` lies in `ResidueField A (x)`. -/
lemma aeval_mem_adjoin_simple (x : Fbar) (p : Polynomial (ResidueField A)) :
    aeval x p ∈ IntermediateField.adjoin (ResidueField A) ({x} : Set Fbar) := by
  have hmem : aeval x p ∈ Algebra.adjoin (ResidueField A) ({x} : Set Fbar) := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  exact (IntermediateField.algebra_adjoin_le_adjoin (ResidueField A) ({x} : Set Fbar)) hmem

end PsiSol

open PsiSol

namespace GaussProlongation

/-- The Gauss prolongation: for `w` in the simple extension `L(f)` which is integral
for two prolongations `R i₀` and `R i` along the same transcendental `f`, the
residue of `w` in `R i` lies in `ResidueField A (residue f)`. -/
theorem residue_mem_adjoin_residue_of_mem_adjoin_integers
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (i₀ i : ι) (w : IntermediateField.adjoin L ({f} : Set F)) (hw : (w : F) ∈ (R i₀).integers)
    (hwi : (w : F) ∈ (R i).integers) :
    (R i).residue ⟨(w : F), hwi⟩ ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by
  classical

  rcases eq_or_ne (w : F) 0 with hw0 | hwne
  · have h0 : (⟨(w : F), hwi⟩ : (R i).integers) = 0 := Subtype.ext hw0
    rw [h0, map_zero]; exact zero_mem _

  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff L (w : F)).mp w.2
  have hsf : aeval f s ≠ 0 := fun h => hwne (by rw [hrs, h, div_zero])

  obtain ⟨c, hcmem, hcres⟩ := (R i₀).exists_smul_mem (aeval f s) hsf
  have hc0 : c ≠ 0 := (R i₀).smul_const_ne_zero hcmem hcres

  set q : L[X] := C c * s with hqdef
  have hcq : aeval f q = c • aeval f s := by
    simp only [hqdef, map_mul, aeval_C, Algebra.smul_def]
  have hqf : aeval f q ≠ 0 := hcq ▸ smul_ne_zero hc0 hsf
  have hqmem₀ : aeval f q ∈ (R i₀).integers := hcq ▸ hcmem
  have hqres₀ : (R i₀).residue ⟨aeval f q, hqmem₀⟩ ≠ 0 := by
    intro h; apply hcres
    have heq : (⟨aeval f q, hqmem₀⟩ : (R i₀).integers) = ⟨c • aeval f s, hcmem⟩ := Subtype.ext hcq
    rw [← heq]; exact h

  have hqA : ∀ j, q.coeff j ∈ A := fun j =>
    RegularProlongation.coeff_mem_of_aeval_mem_integers A (R i₀) ⟨f, hf i₀⟩ (htr i₀) q hqmem₀ j
  set qA : Polynomial A := liftA A q hqA with hqAdef
  have hqAmap : qA.map A.subtype = q := liftA_map A q hqA

  have hqbar_ne : qA.map (IsLocalRing.residue A) ≠ 0 := by
    intro hz
    apply hqres₀
    have key : (⟨aeval f q, hqmem₀⟩ : (R i₀).integers) =
        Polynomial.eval₂ (φ A (R i₀)) ⟨f, hf i₀⟩ qA := by
      apply Subtype.ext
      rw [coe_eval₂_φ A (R i₀) f (hf i₀) qA, hqAmap]
    rw [key, residue_eval₂_φ A (R i₀) f (hf i₀) qA, hz, map_zero]

  set p : L[X] := C c * r with hpdef
  have hep : (w : F) * aeval f q = aeval f p := by
    simp only [hqdef, hpdef, map_mul, aeval_C, hrs]; field_simp
  have hpmem₀ : aeval f p ∈ (R i₀).integers := hep ▸ mul_mem hw hqmem₀
  have hpA : ∀ j, p.coeff j ∈ A := fun j =>
    RegularProlongation.coeff_mem_of_aeval_mem_integers A (R i₀) ⟨f, hf i₀⟩ (htr i₀) p hpmem₀ j
  set pA : Polynomial A := liftA A p hpA with hpAdef
  have hpAmap : pA.map A.subtype = p := liftA_map A p hpA

  set qOi : (R i).integers := Polynomial.eval₂ (φ A (R i)) ⟨f, hf i⟩ qA with hqOidef
  set pOi : (R i).integers := Polynomial.eval₂ (φ A (R i)) ⟨f, hf i⟩ pA with hpOidef
  have hqOi_coe : (qOi : F) = aeval f q := by
    rw [hqOidef, coe_eval₂_φ A (R i) f (hf i) qA, hqAmap]
  have hpOi_coe : (pOi : F) = aeval f p := by
    rw [hpOidef, coe_eval₂_φ A (R i) f (hf i) pA, hpAmap]
  have hqOi_res : (R i).residue qOi =
      aeval ((R i).residue ⟨f, hf i⟩) (qA.map (IsLocalRing.residue A)) :=
    residue_eval₂_φ A (R i) f (hf i) qA
  have hpOi_res : (R i).residue pOi =
      aeval ((R i).residue ⟨f, hf i⟩) (pA.map (IsLocalRing.residue A)) :=
    residue_eval₂_φ A (R i) f (hf i) pA

  have hqOi_res_ne : (R i).residue qOi ≠ 0 := by
    rw [hqOi_res]
    intro hz
    exact hqbar_ne ((transcendental_iff.mp (htr i)) _ hz)

  have hq_mem_adjoin : (R i).residue qOi ∈
      IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by
    rw [hqOi_res]; exact aeval_mem_adjoin_simple A _ _
  have hp_mem_adjoin : (R i).residue pOi ∈
      IntermediateField.adjoin (ResidueField A) ({(R i).residue ⟨f, hf i⟩} : Set (Fb i)) := by
    rw [hpOi_res]; exact aeval_mem_adjoin_simple A _ _

  have heq_in_O : (⟨(w : F), hwi⟩ : (R i).integers) * qOi = pOi := by
    apply Subtype.ext
    show (w : F) * (qOi : F) = (pOi : F)
    rw [hqOi_coe, hpOi_coe]; exact hep
  have hres_mul : (R i).residue ⟨(w : F), hwi⟩ * (R i).residue qOi = (R i).residue pOi := by
    rw [← map_mul, heq_in_O]

  have hw_eq : (R i).residue ⟨(w : F), hwi⟩ = (R i).residue pOi * ((R i).residue qOi)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hqOi_res_ne]; exact hres_mul
  rw [hw_eq]
  exact mul_mem hp_mem_adjoin (inv_mem hq_mem_adjoin)

end GaussProlongation

end
