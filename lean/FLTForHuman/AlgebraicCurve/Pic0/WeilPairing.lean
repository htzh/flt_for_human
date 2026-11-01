/-
**The divisorial Weil pairing is a class invariant.**  After FLT's
`S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.lean` (439 ln) and its wrapper
`Theorems/Thm_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.lean>).

A `WeilDatum K F n` pairs two degree-`n` divisors `D₁`, `D₂` through the value
`evalFun f₁ D₂ / evalFun f₂ D₁` (`Defs/WeilDatum.lean`).  This module proves that the value
depends only on the classes of `D₁` and `D₂` in `Pic0 K F`: if the differences `D₁' - D₁`,
`D₂' - D₂` are principal then `d'.pairing = d.pairing`.  That is the well-definedness the
Weil pairing `Pic0[n] × Pic0[n] → K` is built on.

Three inputs are hypotheses rather than theorems, exactly as in the pin:

* `hrec : WeilReciprocity K F`, the reciprocity law for `F` (for `F = RatFunc K` it is the
  ℙ¹ theorem in `P1/Dictionary.lean`);
* `hconst`, "a function with no zeros and no poles is a constant" — the pin's
  `hconst`-shaped form of the residue-field degree-one statement;
* `hmove`, that every `n`-torsion class has a representative with rational support avoiding
  a prescribed finite set of places (an Abel–Jacobi/weak approximation input).

The shape of the proof is the pin's, unchanged.  The engine
`pairing_eq_of_addPrincipalLeft_i` moves `D₁` by a principal divisor `E = div h` and `f₁` by
`h ^ n`: `evalFun` of the numerator splits by `evalFun_mul` and `evalFun_zpow_left`, and
reciprocity turns `evalFun h D₂ ^ n` into `evalFun f₂ E`, which the denominator also gains,
so `mul_div_mul_right` cancels it.  The two `pairing_eq_of_isPrincipal_sub_{left,right}_i`
lemmas normalize an arbitrary principal difference to that shape: the quotient
`d'.f₁ * w⁻¹` has zero order everywhere, so `hconst` makes it a constant `c`, whose
`evalFun` against the degree-zero `D₂` is `1`; the right-hand case is the left-hand one on
`symm`, using `symm_pairing` and `inv_inj`.  The headline composes those around `hmove`-
chosen representatives `A₁`, `A₂` of the two classes, with a two-place avoidance set.

The support block the pin states privately here (`ord_f₁…_i`, `ord_f₂…_i`,
`rational_of_mem_support_{left,right}_i`) is **not** restated: it is public in
`Defs/WeilDatum.lean` and is imported.

SET 7 adds the file's companion row, `Pic0.torsion.exists_addMonoidHom_eval_eq_pairing`
(the existence of the pairing hom `Pic0[n] →+ Additive (HomPic0Gm K F n)`), after the pin's
381-line `S_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing.lean`: the
`_i` helpers above are its private prelude, and the public class/datum laws and the
headline are appended below.

**The third subject is the carrier, `DivisorialWeilPairingData`** — the definition gate of the
nondegeneracy rows (`DivisorialWeilPairingData.toHom_injective_of_divisible` and its siblings).
The pin states its datum layer (the `degZeroLeft`/`classLeft` block) twice: in
`Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial` at the clean names, and in the two `S_`
files above at an `_i`-suffixed renaming.  The module carries the **clean** spelling throughout,
because the carrier's `compatible` field is stated there.  The one consequence is the `S_` file's
own two generalised datum lemmas (`exists_datum_i`, `exists_datum_pair_i`), whose statements name
the `_i` spelling: they are stated here at the clean one and are `own:` marker rows in
`spec/decl_markers.tsv`.

spec-pin: Theorems/Thm_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing.lean
spec-pin: Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.WeilDatum
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluationAlgebra
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import FLTForHuman.AlgebraicCurve.Pic0.Torsion

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem prod_zpow_eq_zpow_sum_i {c : K} (hc : c ≠ 0) {ι : Type*} (s : Finset ι)
    (m : ι → ℤ) : ∏ i ∈ s, c ^ m i = c ^ (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

private theorem support_zsmul_subset_i (c : ℤ) (D : Divisor K F) :
    ((c • D : Divisor K F)).support ⊆ D.support := by
  intro v hv
  rw [Finsupp.mem_support_iff] at hv ⊢
  intro h0
  exact hv (by rw [Finsupp.smul_apply, h0, smul_zero])

private theorem isPrincipal_neg_i {D : Divisor K F} (h : Divisor.IsPrincipal D) :
    Divisor.IsPrincipal (-D) := by
  obtain ⟨g, hg0, hg⟩ := h
  refine ⟨g⁻¹, inv_ne_zero hg0, fun v => ?_⟩
  rw [Finsupp.neg_apply, Place.ord_inv, ← hg v]

private theorem isPrincipal_add_i {A B : Divisor K F} (hA : Divisor.IsPrincipal A)
    (hB : Divisor.IsPrincipal B) : Divisor.IsPrincipal (A + B) := by
  obtain ⟨f, hf0, hfv⟩ := hA
  obtain ⟨g, hg0, hgv⟩ := hB
  refine ⟨f * g, mul_ne_zero hf0 hg0, fun v => ?_⟩
  rw [Finsupp.add_apply, hfv v, hgv v, v.ord_mul hf0 hg0]

private theorem isPrincipal_sub_of_mk_eq_i {A B : Divisor.degZero (K := K) (F := F)}
    (h : Pic0.mk A = Pic0.mk B) :
    Divisor.IsPrincipal ((A : Divisor K F) - (B : Divisor K F)) := by
  have hsub0 : Pic0.mk (A - B) = 0 := by
    show QuotientAddGroup.mk (A - B) = 0
    rw [QuotientAddGroup.mk_sub, sub_eq_zero]
    exact h
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hsub0
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  have hcoe : ((A - B : Divisor.degZero (K := K) (F := F)) : Divisor K F)
      = (A : Divisor K F) - (B : Divisor K F) := rfl
  rw [hcoe] at hmem
  exact Divisor.mem_principal.mp hmem

namespace Divisor

/-- Pin `Divisor.evalFun_one` (`Definitions/Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial.lean`
line 17), public in the pin: the evaluation at the constant `1` is `1`.  The carrier's
`pair_zero_left` consumes it. -/
theorem evalFun_one (D : Divisor K F) : Divisor.evalFun (1 : F) D = 1 := by
  rw [Divisor.evalFun_def]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [Place.evalAt_one, one_zpow]

end Divisor

private theorem evalFun_algebraMap_of_degree_eq_zero_i {c : K} (hc : c ≠ 0) {D : Divisor K F}
    (hdeg : Divisor.degree D = 0) (hrat : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.evalFun (algebraMap K F c) D = 1 := by
  classical
  rw [Divisor.evalFun_def]
  have hfac : ∀ v ∈ D.support, v.evalAt (algebraMap K F c) ^ D v = c ^ D v := fun v _ => by
    rw [Place.evalAt_algebraMap]
  rw [Finset.prod_congr rfl hfac, prod_zpow_eq_zpow_sum_i hc]
  have hsum : ∑ v ∈ D.support, D v = 0 := by
    have h1 : Divisor.degree D = D.sum fun v m => m * (v.deg : ℤ) :=
      Finsupp.liftAddHom_apply _ _
    have h2 : D.sum (fun v m => m * (v.deg : ℤ)) = ∑ v ∈ D.support, D v := by
      refine Finset.sum_congr rfl fun v hv => ?_
      show D v * (v.deg : ℤ) = D v
      rw [(Place.isRational_iff_deg_eq_one v).mp (hrat v hv), Nat.cast_one, mul_one]
    rw [← h2, ← h1, hdeg]
  rw [hsum, zpow_zero]

namespace WeilDatum

variable {n : ℕ}

private theorem isPrincipal_smul_left (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₁) :=
  ⟨d.f₁, d.f₁_ne_zero, fun v => by rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₁ v]⟩

theorem isPrincipal_smul_right (d : WeilDatum K F n) :
    Divisor.IsPrincipal ((n : ℤ) • d.D₂) :=
  d.symm.isPrincipal_smul_left

private theorem degree_eq_zero_of_isPrincipal_i [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : Divisor.IsPrincipal D) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDv⟩ := hD
  obtain ⟨D', hD'v, hD'deg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have hDD' : D = D' := Finsupp.ext fun v => by rw [hDv v, hD'v v]
  exact hDD' ▸ hD'deg

theorem degree_D₁_eq_zero [HasPrincipalDivisors K F] (d : WeilDatum K F n)
    (hn : n ≠ 0) : Divisor.degree d.D₁ = 0 := by
  have h := degree_eq_zero_of_isPrincipal_i d.isPrincipal_smul_left
  rw [map_zsmul, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hn)

theorem degree_D₂_eq_zero [HasPrincipalDivisors K F] (d : WeilDatum K F n)
    (hn : n ≠ 0) : Divisor.degree d.D₂ = 0 :=
  d.symm.degree_D₁_eq_zero hn

section ClassLayer

variable [NeZero n] [HasPrincipalDivisors K F]

def degZeroLeft (d : WeilDatum K F n) : Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₁, Divisor.mem_degZero.mpr (d.degree_D₁_eq_zero (NeZero.ne n))⟩

def degZeroRight (d : WeilDatum K F n) : Divisor.degZero (K := K) (F := F) :=
  ⟨d.D₂, Divisor.mem_degZero.mpr (d.degree_D₂_eq_zero (NeZero.ne n))⟩

theorem coe_degZeroLeft (d : WeilDatum K F n) :
    (d.degZeroLeft : Divisor K F) = d.D₁ := rfl

theorem coe_degZeroRight (d : WeilDatum K F n) :
    (d.degZeroRight : Divisor K F) = d.D₂ := rfl

omit [NeZero n] [HasPrincipalDivisors K F] in
theorem mk_mem_torsion (D : Divisor.degZero (K := K) (F := F))
    (h : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F))) :
    Pic0.mk D ∈ Pic0.torsion K F n := by
  rw [Pic0.mem_torsion]
  have h1 : (n : ℤ) • Pic0.mk D = Pic0.mk ((n : ℤ) • D) := by
    show (n : ℤ) • (QuotientAddGroup.mk D) = QuotientAddGroup.mk ((n : ℤ) • D)
    exact (QuotientAddGroup.mk_zsmul
      ((Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F))) D (n : ℤ)).symm
  rw [h1]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  have hcoe : (((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) : Divisor K F)
      = (n : ℤ) • (D : Divisor K F) := rfl
  show ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
    (Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))
  rw [AddSubgroup.mem_addSubgroupOf, hcoe]
  exact Divisor.mem_principal.mpr h

def classLeft (d : WeilDatum K F n) : Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroLeft, mk_mem_torsion d.degZeroLeft (by
    rw [coe_degZeroLeft]; exact d.isPrincipal_smul_left)⟩

def classRight (d : WeilDatum K F n) : Pic0.torsion K F n :=
  ⟨Pic0.mk d.degZeroRight, mk_mem_torsion d.degZeroRight (by
    rw [coe_degZeroRight]; exact d.isPrincipal_smul_right)⟩

@[simp] theorem coe_classLeft (d : WeilDatum K F n) :
    (d.classLeft : Pic0 K F) = Pic0.mk d.degZeroLeft := rfl

@[simp] theorem coe_classRight (d : WeilDatum K F n) :
    (d.classRight : Pic0 K F) = Pic0.mk d.degZeroRight := rfl

theorem classLeft_symm (d : WeilDatum K F n) : d.symm.classLeft = d.classRight := rfl

theorem classRight_symm (d : WeilDatum K F n) : d.symm.classRight = d.classLeft := rfl

theorem classLeft_addLeft (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).classLeft = d.classLeft + d'.classLeft := by
  refine Subtype.ext ?_
  show Pic0.mk (d.addLeft d' hD hf).degZeroLeft
      = Pic0.mk d.degZeroLeft + Pic0.mk d'.degZeroLeft
  rw [← Pic0.mk_add]
  exact congrArg Pic0.mk (Subtype.ext rfl)

theorem classRight_addLeft (d d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (hf : d.f₂ = d'.f₂) :
    (d.addLeft d' hD hf).classRight = d.classRight :=
  rfl

end ClassLayer

theorem evalAt_f₁_ne_zero_i (d : WeilDatum K F n) {v : Place K F}
    (hv : v ∈ d.D₂.support) : v.evalAt d.f₁ ≠ 0 :=
  v.evalAt_ne_zero (d.rational_of_mem_support_right hv) d.f₁_ne_zero
    (d.ord_f₁_eq_zero_of_mem_support hv)

private theorem evalAt_f₂_ne_zero_i (d : WeilDatum K F n) {v : Place K F}
    (hv : v ∈ d.D₁.support) : v.evalAt d.f₂ ≠ 0 :=
  v.evalAt_ne_zero (d.rational_of_mem_support_left hv) d.f₂_ne_zero
    (d.ord_f₂_eq_zero_of_mem_support hv)

theorem pairing_eq_of_addPrincipalLeft_i (hrec : WeilReciprocity K F)
    (d d' : WeilDatum K F n) {E : Divisor K F} {h : F} (hh : h ≠ 0)
    (hE : ∀ v : Place K F, E v = v.ord h)
    (hD₁ : d'.D₁ = d.D₁ + E) (hD₂ : d'.D₂ = d.D₂)
    (hf₁ : d'.f₁ = d.f₁ * h ^ (n : ℤ)) (hf₂ : d'.f₂ = d.f₂) :
    d'.pairing = d.pairing := by
  classical
  have hE0 : ∀ v : Place K F, d.D₂ v ≠ 0 → E v = 0 := by
    intro v hv
    have h1 : d.D₁ v = 0 := (d.disjoint v).resolve_right hv
    have h2 : d'.D₁ v = 0 := (d'.disjoint v).resolve_right (by rw [hD₂]; exact hv)
    have h3 : d'.D₁ v = d.D₁ v + E v := by rw [hD₁]; rfl
    rw [h1, h2, zero_add] at h3
    exact h3.symm
  have hordh : ∀ v ∈ d.D₂.support, v.ord h = 0 := by
    intro v hv
    rw [← hE v]
    exact hE0 v (Finsupp.mem_support_iff.mp hv)
  have hratD₂ : ∀ v ∈ d.D₂.support, Place.IsRational v :=
    fun v hv => d.rational_of_mem_support_right hv
  have hratE : ∀ v ∈ E.support, Place.IsRational v := by
    intro v hv
    have hEv : E v ≠ 0 := Finsupp.mem_support_iff.mp hv
    by_cases hD₁v : d.D₁ v = 0
    · refine d'.rational v (Or.inl ?_)
      rw [hD₁]
      show d.D₁ v + E v ≠ 0
      rw [hD₁v, zero_add]
      exact hEv
    · exact d.rational v (Or.inl hD₁v)
  have hordf₂E : ∀ v ∈ E.support, v.ord d.f₂ = 0 := by
    intro v hv
    have hEv : E v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have hD₂v : d.D₂ v = 0 := by
      by_contra hne
      exact hEv (hE0 v hne)
    rw [d.ord_f₂ v, hD₂v, mul_zero]
  have hevalf₂E : ∀ v ∈ E.support, v.evalAt d.f₂ ≠ 0 := fun v hv =>
    v.evalAt_ne_zero (hratE v hv) d.f₂_ne_zero (hordf₂E v hv)
  have hnum : Divisor.evalFun d'.f₁ d'.D₂
      = Divisor.evalFun d.f₁ d.D₂ * Divisor.evalFun h d.D₂ ^ (n : ℤ) := by
    rw [hf₁, hD₂,
      Divisor.evalFun_mul hratD₂
        (fun v hv => v.mem_of_ord_nonneg d.f₁_ne_zero
          (d.ord_f₁_eq_zero_of_mem_support hv).ge)
        (fun v hv => v.mem_of_ord_nonneg (zpow_ne_zero _ hh)
          (by rw [Place.ord_zpow, hordh v hv, mul_zero])),
      Divisor.evalFun_zpow_left hh (n : ℤ) hratD₂ hordh]
  have hrecip : Divisor.evalFun h d.D₂ ^ (n : ℤ) = Divisor.evalFun d.f₂ E := by
    rw [← Divisor.evalFun_zsmul]
    refine (hrec d.f₂ h ((n : ℤ) • d.D₂) E d.f₂_ne_zero hh
      (fun v => ?_) (fun v => (hE v).symm ▸ rfl) (fun v => ?_) (fun v hv => ?_) hratE).symm
    · rw [Finsupp.smul_apply, smul_eq_mul, d.ord_f₂ v]
    · by_cases hD₂v : d.D₂ v = 0
      · exact Or.inl (by rw [d.ord_f₂ v, hD₂v, mul_zero])
      · exact Or.inr (by rw [← hE v]; exact hE0 v hD₂v)
    · exact hratD₂ v (support_zsmul_subset_i _ _ hv)
  have hden : Divisor.evalFun d'.f₂ d'.D₁
      = Divisor.evalFun d.f₂ d.D₁ * Divisor.evalFun d.f₂ E := by
    rw [hf₂, hD₁]
    exact Divisor.evalFun_add d.f₂ (fun v hv => d.evalAt_f₂_ne_zero_i hv) hevalf₂E
  have hEne : Divisor.evalFun d.f₂ E ≠ 0 := Divisor.evalFun_ne_zero hevalf₂E
  show Divisor.evalFun d'.f₁ d'.D₂ / Divisor.evalFun d'.f₂ d'.D₁ = d.pairing
  rw [hnum, hrecip, hden]
  rw [show d.pairing = Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁ from rfl]
  rw [mul_div_mul_right _ _ hEne]

theorem pairing_eq_of_isPrincipal_sub_left_i [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (d d' : WeilDatum K F n) (hD₂ : d'.D₂ = d.D₂) (hf₂ : d'.f₂ = d.f₂)
    (hprin : Divisor.IsPrincipal (d'.D₁ - d.D₁)) :
    d'.pairing = d.pairing := by
  classical
  obtain ⟨h, hh0, hhord⟩ := hprin
  set w : F := d.f₁ * h ^ (n : ℤ) with hw
  have hw0 : w ≠ 0 := mul_ne_zero d.f₁_ne_zero (zpow_ne_zero _ hh0)
  have hordw : ∀ v : Place K F, v.ord w = n * d'.D₁ v := by
    intro v
    rw [hw, v.ord_mul d.f₁_ne_zero (zpow_ne_zero _ hh0), Place.ord_zpow, d.ord_f₁ v,
      ← hhord v, Finsupp.sub_apply]
    ring
  set d'' : WeilDatum K F n :=
    ⟨d'.D₁, d.D₂, w, d.f₂, hw0, d.f₂_ne_zero, hordw, d.ord_f₂,
      fun v => by rw [← hD₂]; exact d'.disjoint v,
      fun v hv => d'.rational v (by rw [hD₂]; exact hv)⟩ with hd''
  have hengine : d''.pairing = d.pairing := by
    refine pairing_eq_of_addPrincipalLeft_i hrec d d'' hh0 hhord ?_ rfl rfl rfl
    show d'.D₁ = d.D₁ + (d'.D₁ - d.D₁)
    abel
  have hordu : ∀ v : Place K F, v.ord (d'.f₁ * w⁻¹) = 0 := by
    intro v
    rw [v.ord_mul d'.f₁_ne_zero (inv_ne_zero hw0), Place.ord_inv, d'.ord_f₁ v, hordw v]
    ring
  obtain ⟨c, hc⟩ := hconst (d'.f₁ * w⁻¹) (mul_ne_zero d'.f₁_ne_zero (inv_ne_zero hw0)) hordu
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (mul_ne_zero d'.f₁_ne_zero (inv_ne_zero hw0)) (by rw [hc, map_zero])
  have hf₁' : d'.f₁ = algebraMap K F c * w := by
    have h1 : d'.f₁ * w⁻¹ * w = algebraMap K F c * w := by rw [hc]
    rwa [mul_assoc, inv_mul_cancel₀ hw0, mul_one] at h1
  have hratD₂ : ∀ v ∈ d.D₂.support, Place.IsRational v :=
    fun v hv => d.rational_of_mem_support_right hv
  have hordwD₂ : ∀ v ∈ d.D₂.support, v.ord w = 0 := by
    intro v hv
    rw [hordw v]
    have hzero : d'.D₁ v = 0 := (d'.disjoint v).resolve_right (by
      rw [hD₂]
      exact Finsupp.mem_support_iff.mp hv)
    rw [hzero, mul_zero]
  have hnum : Divisor.evalFun d'.f₁ d.D₂ = Divisor.evalFun w d.D₂ := by
    rw [hf₁', Divisor.evalFun_mul hratD₂
      (fun v _ => v.algebraMap_mem' c)
      (fun v hv => v.mem_of_ord_nonneg hw0 (hordwD₂ v hv).ge),
      evalFun_algebraMap_of_degree_eq_zero_i hc0 (d.degree_D₂_eq_zero (NeZero.ne n))
        hratD₂, one_mul]
  have hpair' : d'.pairing = d''.pairing := by
    show Divisor.evalFun d'.f₁ d'.D₂ / Divisor.evalFun d'.f₂ d'.D₁
      = Divisor.evalFun w d.D₂ / Divisor.evalFun d.f₂ d'.D₁
    rw [hD₂, hf₂, hnum]
  rw [hpair', hengine]

theorem pairing_eq_of_isPrincipal_sub_right_i [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (d d' : WeilDatum K F n) (hD₁ : d'.D₁ = d.D₁) (hf₁ : d'.f₁ = d.f₁)
    (hprin : Divisor.IsPrincipal (d'.D₂ - d.D₂)) :
    d'.pairing = d.pairing := by
  have hsymm : d'.symm.pairing = d.symm.pairing := by
    refine pairing_eq_of_isPrincipal_sub_left_i hrec hconst d.symm d'.symm ?_ ?_ ?_
    · show d'.D₁ = d.D₁
      exact hD₁
    · show d'.f₁ = d.f₁
      exact hf₁
    · show Divisor.IsPrincipal (d'.D₂ - d.D₂)
      exact hprin
  rw [WeilDatum.symm_pairing, WeilDatum.symm_pairing] at hsymm
  exact inv_inj.mp hsymm

end WeilDatum

section Datum

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]

/-- **A Weil datum exists for any two torsion classes.**  `hmove` chooses representatives
with rational support avoiding a prescribed finite set; `exists_forall_ord_eq_mul` turns
them into the two functions.  Statement from the pin's `S_` file (the declarations below are
the public surface of that file; the `_i` helpers above are its private prelude). -/
theorem exists_datum_i
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S))
    (x y : Pic0.torsion K F n) :
    ∃ d : WeilDatum K F n, d.classLeft = x ∧ d.classRight = y := by
  classical
  obtain ⟨D₁, hD₁mk, hD₁rat, -⟩ := hmove x ∅
  obtain ⟨D₂, hD₂mk, hD₂rat, hD₂avoid⟩ := hmove y (D₁ : Divisor K F).support
  obtain ⟨f₁, hf₁0, hf₁⟩ := Pic0.torsion.exists_forall_ord_eq_mul x D₁ hD₁mk
  obtain ⟨f₂, hf₂0, hf₂⟩ := Pic0.torsion.exists_forall_ord_eq_mul y D₂ hD₂mk
  refine ⟨⟨(D₁ : Divisor K F), (D₂ : Divisor K F), f₁, f₂, hf₁0, hf₂0, hf₁, hf₂, ?_, ?_⟩,
    ?_, ?_⟩
  · intro v
    by_cases hv : (D₂ : Divisor K F) v = 0
    · exact Or.inr hv
    · refine Or.inl ?_
      by_contra hv1
      exact hD₂avoid v (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hv1)
  · intro v hv
    rcases hv with h1 | h2
    · exact hD₁rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (x : Pic0 K F)
    rw [← hD₁mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)

/-- **A pair of Weil data exists for `x + x'` and `y` with a shared second half.**  The
`addLeft` bilinearity needs the two data at `x` and `x'` to agree on `D₂` and `f₂`; the
proof chooses both `D₁`'s against the same `D₂`. -/
theorem exists_datum_pair_i
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S))
    (x x' y : Pic0.torsion K F n) :
    ∃ d d' : WeilDatum K F n, d.D₂ = d'.D₂ ∧ d.f₂ = d'.f₂ ∧
      d.classLeft = x ∧ d'.classLeft = x' ∧ d.classRight = y ∧ d'.classRight = y := by
  classical
  obtain ⟨D₂, hD₂mk, hD₂rat, -⟩ := hmove y ∅
  obtain ⟨D₁, hD₁mk, hD₁rat, hD₁avoid⟩ := hmove x (D₂ : Divisor K F).support
  obtain ⟨D₁', hD₁'mk, hD₁'rat, hD₁'avoid⟩ := hmove x' (D₂ : Divisor K F).support
  obtain ⟨f₂, hf₂0, hf₂⟩ := Pic0.torsion.exists_forall_ord_eq_mul y D₂ hD₂mk
  obtain ⟨f₁, hf₁0, hf₁⟩ := Pic0.torsion.exists_forall_ord_eq_mul x D₁ hD₁mk
  obtain ⟨f₁', hf₁'0, hf₁'⟩ := Pic0.torsion.exists_forall_ord_eq_mul x' D₁' hD₁'mk
  have hdisj : ∀ (D : Divisor.degZero (K := K) (F := F)),
      (∀ v ∈ (D : Divisor K F).support, v ∉ (D₂ : Divisor K F).support) →
      ∀ v : Place K F, (D : Divisor K F) v = 0 ∨ (D₂ : Divisor K F) v = 0 := by
    intro D havoid v
    by_cases hv : (D : Divisor K F) v = 0
    · exact Or.inl hv
    · refine Or.inr ?_
      by_contra hv2
      exact havoid v (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hv2)
  refine ⟨⟨(D₁ : Divisor K F), (D₂ : Divisor K F), f₁, f₂, hf₁0, hf₂0, hf₁, hf₂,
      hdisj D₁ hD₁avoid, ?_⟩,
    ⟨(D₁' : Divisor K F), (D₂ : Divisor K F), f₁', f₂, hf₁'0, hf₂0, hf₁', hf₂,
      hdisj D₁' hD₁'avoid, ?_⟩, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases hv with h1 | h2
    · exact hD₁rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  · intro v hv
    rcases hv with h1 | h2
    · exact hD₁'rat v (Finsupp.mem_support_iff.mpr h1)
    · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (x : Pic0 K F)
    rw [← hD₁mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (x' : Pic0 K F)
    rw [← hD₁'mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  · refine Subtype.ext ?_
    show Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)

end Datum

/-- **The divisorial Weil pairing is a class invariant.**  Statement from
`Theorems/Thm_AlgebraicCurve_WeilDatum_pairing_eq_of_isPrincipal_sub.lean`, exactly the
wrapper's; the proof is the pin's `solution`: move `d` to representatives `A₁`, `A₂` of its
two `Pic0` classes by `hmove`, walk to `d'` through the two one-sided case lemmas, and use
`hconst` inside them to kill the constant. -/
theorem WeilDatum.pairing_eq_of_isPrincipal_sub {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S))
    (d d' : WeilDatum K F n)
    (hL : Divisor.IsPrincipal (d'.D₁ - d.D₁)) (hR : Divisor.IsPrincipal (d'.D₂ - d.D₂)) :
    d'.pairing = d.pairing := by
  classical
  obtain ⟨A₁, hA₁mk, hA₁rat, hA₁avoid⟩ := hmove (WeilDatum.classLeft d) d.D₂.support
  obtain ⟨A₂, hA₂mk, hA₂rat, hA₂avoid⟩ :=
    hmove (WeilDatum.classRight d) ((A₁ : Divisor K F).support ∪ d'.D₁.support)
  obtain ⟨a₁, ha₁0, ha₁⟩ :=
    Pic0.torsion.exists_forall_ord_eq_mul (WeilDatum.classLeft d) A₁ hA₁mk
  obtain ⟨a₂, ha₂0, ha₂⟩ :=
    Pic0.torsion.exists_forall_ord_eq_mul (WeilDatum.classRight d) A₂ hA₂mk
  set e₁ : WeilDatum K F n :=
    ⟨(A₁ : Divisor K F), d.D₂, a₁, d.f₂, ha₁0, d.f₂_ne_zero, ha₁, d.ord_f₂,
      fun v => by
        by_cases hv : (A₁ : Divisor K F) v = 0
        · exact Or.inl hv
        · refine Or.inr ?_
          by_contra hv2
          exact hA₁avoid v (Finsupp.mem_support_iff.mpr hv) (Finsupp.mem_support_iff.mpr hv2),
      fun v hv => by
        rcases hv with h1 | h2
        · exact hA₁rat v (Finsupp.mem_support_iff.mpr h1)
        · exact d.rational v (Or.inr h2)⟩ with he₁
  set e₂ : WeilDatum K F n :=
    ⟨(A₁ : Divisor K F), (A₂ : Divisor K F), a₁, a₂, ha₁0, ha₂0, ha₁, ha₂,
      fun v => by
        by_cases hv : (A₂ : Divisor K F) v = 0
        · exact Or.inr hv
        · refine Or.inl ?_
          by_contra hv2
          exact hA₂avoid v (Finsupp.mem_support_iff.mpr hv)
            (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hv2)),
      fun v hv => by
        rcases hv with h1 | h2
        · exact hA₁rat v (Finsupp.mem_support_iff.mpr h1)
        · exact hA₂rat v (Finsupp.mem_support_iff.mpr h2)⟩ with he₂
  set e₃ : WeilDatum K F n :=
    ⟨d'.D₁, (A₂ : Divisor K F), d'.f₁, a₂, d'.f₁_ne_zero, ha₂0, d'.ord_f₁, ha₂,
      fun v => by
        by_cases hv : (A₂ : Divisor K F) v = 0
        · exact Or.inr hv
        · refine Or.inl ?_
          by_contra hv2
          exact hA₂avoid v (Finsupp.mem_support_iff.mpr hv)
            (Finset.mem_union_right _ (Finsupp.mem_support_iff.mpr hv2)),
      fun v hv => by
        rcases hv with h1 | h2
        · exact d'.rational v (Or.inl h1)
        · exact hA₂rat v (Finsupp.mem_support_iff.mpr h2)⟩ with he₃

  have hA₁cl : Pic0.mk A₁ = Pic0.mk (WeilDatum.degZeroLeft d) := hA₁mk
  have hA₂cl : Pic0.mk A₂ = Pic0.mk (WeilDatum.degZeroRight d) := hA₂mk
  have iL1 : Divisor.IsPrincipal ((A₁ : Divisor K F) - d.D₁) :=
    isPrincipal_sub_of_mk_eq_i hA₁cl
  have iR2 : Divisor.IsPrincipal ((A₂ : Divisor K F) - d.D₂) :=
    isPrincipal_sub_of_mk_eq_i hA₂cl
  have iL1' : Divisor.IsPrincipal (d.D₁ - (A₁ : Divisor K F)) := by
    have hneg := isPrincipal_neg_i iL1
    rwa [neg_sub] at hneg
  have iR2' : Divisor.IsPrincipal (d.D₂ - (A₂ : Divisor K F)) := by
    have hneg := isPrincipal_neg_i iR2
    rwa [neg_sub] at hneg
  have iL3 : Divisor.IsPrincipal (d'.D₁ - (A₁ : Divisor K F)) := by
    have hadd := isPrincipal_add_i hL iL1'
    rwa [sub_add_sub_cancel] at hadd
  have iR4 : Divisor.IsPrincipal (d'.D₂ - (A₂ : Divisor K F)) := by
    have hadd := isPrincipal_add_i hR iR2'
    rwa [sub_add_sub_cancel] at hadd

  have h₁ : e₁.pairing = d.pairing :=
    WeilDatum.pairing_eq_of_isPrincipal_sub_left_i hrec hconst d e₁ rfl rfl iL1
  have h₂ : e₂.pairing = e₁.pairing :=
    WeilDatum.pairing_eq_of_isPrincipal_sub_right_i hrec hconst e₁ e₂ rfl rfl iR2
  have h₃ : e₃.pairing = e₂.pairing :=
    WeilDatum.pairing_eq_of_isPrincipal_sub_left_i hrec hconst e₂ e₃ rfl rfl iL3
  have h₄ : d'.pairing = e₃.pairing :=
    WeilDatum.pairing_eq_of_isPrincipal_sub_right_i hrec hconst e₃ d' rfl rfl iR4
  rw [h₄, h₃, h₂, h₁]

/-- **The pairing is a homomorphism on `Pic0.torsion`.**  Statement from
`Theorems/Thm_AlgebraicCurve_Pic0_torsion_exists_addMonoidHom_eval_eq_pairing.lean`; proof
after the pin's `S_` file: choose a datum for each pair of classes by `hmove`
(`exists_datum_i`), prove the resulting `pair` is multiplicative on the left by
`exists_datum_pair_i` and the `addLeft` laws, get the right action and the involution from
the swap, and package it as the `AddChar`-valued hom. -/
theorem Pic0.torsion.exists_addMonoidHom_eval_eq_pairing
    {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
    (hrec : WeilReciprocity K F)
    (hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) → ∃ c : K, u = algebraMap K F c)
    (hmove : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
      ∃ D : Divisor.degZero (K := K) (F := F),
        Pic0.mk D = (x : Pic0 K F) ∧
        (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
        (∀ v ∈ (D : Divisor K F).support, v ∉ S)) :
    ∃ hom : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n),
      ∀ (d : WeilDatum K F n) (x y : Pic0.torsion K F n),
        (∃ E : Divisor.degZero (K := K) (F := F), (E : Divisor K F) = d.D₁ ∧ Pic0.mk E = (x : Pic0 K F)) →
        (∃ E : Divisor.degZero (K := K) (F := F), (E : Divisor K F) = d.D₂ ∧ Pic0.mk E = (y : Pic0 K F)) →
        (Additive.toMul (hom x)) y = d.pairing := by
  classical

  choose d₀ hd₀L hd₀R using fun x y : Pic0.torsion K F n => exists_datum_i hmove x y

  set pair : Pic0.torsion K F n → Pic0.torsion K F n → K := fun x y => (d₀ x y).pairing
    with hpairdef

  have compat : ∀ d : WeilDatum K F n,
      pair (WeilDatum.classLeft d) (WeilDatum.classRight d) = d.pairing := by
    intro d
    have hL' := hd₀L (WeilDatum.classLeft d) (WeilDatum.classRight d)
    have hR' := hd₀R (WeilDatum.classLeft d) (WeilDatum.classRight d)
    have hmkL : Pic0.mk (WeilDatum.degZeroLeft
          (d₀ (WeilDatum.classLeft d) (WeilDatum.classRight d)))
        = Pic0.mk (WeilDatum.degZeroLeft d) := congrArg Subtype.val hL'
    have hmkR : Pic0.mk (WeilDatum.degZeroRight
          (d₀ (WeilDatum.classLeft d) (WeilDatum.classRight d)))
        = Pic0.mk (WeilDatum.degZeroRight d) := congrArg Subtype.val hR'
    exact WeilDatum.pairing_eq_of_isPrincipal_sub hrec hconst hmove d
      (d₀ (WeilDatum.classLeft d) (WeilDatum.classRight d))
      (isPrincipal_sub_of_mk_eq_i hmkL) (isPrincipal_sub_of_mk_eq_i hmkR)

  have pair_ne : ∀ x y : Pic0.torsion K F n, pair x y ≠ 0 := fun x y =>
    WeilDatum.pairing_ne_zero (d₀ x y)

  have pair_add_left : ∀ x x' y : Pic0.torsion K F n,
      pair (x + x') y = pair x y * pair x' y := by
    intro x x' y
    obtain ⟨da, da', hD₂, hf₂, hx, hx', hy, hy'⟩ := exists_datum_pair_i hmove x x' y
    have h1 := compat (da.addLeft da' hD₂ hf₂)
    rw [WeilDatum.classLeft_addLeft, WeilDatum.classRight_addLeft,
      WeilDatum.addLeft_pairing, hx, hx', hy] at h1
    rw [h1, ← compat da, ← compat da', hx, hx', hy, hy']

  have pair_swap_one : ∀ x y : Pic0.torsion K F n, pair x y * pair y x = 1 := by
    intro x y
    obtain ⟨d, hx, hy⟩ := exists_datum_i hmove x y
    have h1 := compat d
    have h2 := compat d.symm
    rw [hx, hy] at h1
    rw [WeilDatum.classLeft_symm, WeilDatum.classRight_symm, hx, hy] at h2
    rw [h1, h2, WeilDatum.symm_pairing]
    exact mul_inv_cancel₀ (WeilDatum.pairing_ne_zero d)

  have pair_zero_left : ∀ y : Pic0.torsion K F n, pair 0 y = 1 := by
    intro y
    obtain ⟨D₂, hD₂mk, hD₂rat, -⟩ := hmove y ∅
    obtain ⟨f₂, hf₂0, hf₂⟩ := Pic0.torsion.exists_forall_ord_eq_mul y D₂ hD₂mk
    set dz : WeilDatum K F n :=
      ⟨0, (D₂ : Divisor K F), 1, f₂, one_ne_zero, hf₂0,
        fun v => by simp [Place.ord_one],
        hf₂, fun v => Or.inl rfl,
        fun v hv => by
          rcases hv with h1 | h2
          · exact absurd rfl h1
          · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)⟩ with hdz
    have h1 := compat dz
    have hclassL : WeilDatum.classLeft dz = 0 := by
      have h0 : WeilDatum.degZeroLeft dz = (0 : Divisor.degZero (K := K) (F := F)) :=
        Subtype.ext rfl
      refine Subtype.ext ?_
      show Pic0.mk (WeilDatum.degZeroLeft dz) = ((0 : Pic0.torsion K F n) : Pic0 K F)
      rw [h0, Pic0.mk_zero]
      simp
    have hclassR : WeilDatum.classRight dz = y := by
      refine Subtype.ext ?_
      show Pic0.mk (WeilDatum.degZeroRight dz) = (y : Pic0 K F)
      rw [← hD₂mk]
      exact congrArg Pic0.mk (Subtype.ext rfl)
    have hpairing : dz.pairing = 1 := by
      show Divisor.evalFun (1 : F) (D₂ : Divisor K F) / Divisor.evalFun f₂ (0 : Divisor K F) = 1
      rw [Divisor.evalFun_one, Divisor.evalFun_zero, div_one]
    rw [hclassL, hclassR, hpairing] at h1
    exact h1

  have pair_zero_right : ∀ x : Pic0.torsion K F n, pair x 0 = 1 := by
    intro x
    have h1 := pair_swap_one x 0
    rw [pair_zero_left x, mul_one] at h1
    exact h1

  have pair_swap_inv : ∀ x y : Pic0.torsion K F n, pair y x = (pair x y)⁻¹ := fun x y =>
    eq_inv_of_mul_eq_one_left (pair_swap_one y x)

  have pair_add_right : ∀ x y y' : Pic0.torsion K F n,
      pair x (y + y') = pair x y * pair x y' := by
    intro x y y'
    calc pair x (y + y') = (pair (y + y') x)⁻¹ := pair_swap_inv (y + y') x
      _ = (pair y x * pair y' x)⁻¹ := by rw [pair_add_left y y' x]
      _ = (pair y x)⁻¹ * (pair y' x)⁻¹ := by rw [mul_inv]
      _ = pair x y * pair x y' := by
          rw [pair_swap_inv x y, pair_swap_inv x y', inv_inv, inv_inv]

  set chr : Pic0.torsion K F n → HomPic0Gm K F n := fun x =>
    { toFun := fun y => pair x y
      map_zero_eq_one' := pair_zero_right x
      map_add_eq_mul' := fun y y' => pair_add_right x y y' } with hchr
  have hadd : ∀ x x' : Pic0.torsion K F n,
      Additive.ofMul (chr (x + x')) = Additive.ofMul (chr x) + Additive.ofMul (chr x') := by
    intro x x'
    have h : chr (x + x') = chr x * chr x' := by
      ext y
      rw [AddChar.mul_apply]
      exact pair_add_left x x' y
    rw [h, ofMul_mul]
  refine ⟨AddMonoidHom.mk' (fun x => Additive.ofMul (chr x)) hadd, ?_⟩
  rintro d x y ⟨E₁, hE₁d, hE₁mk⟩ ⟨E₂, hE₂d, hE₂mk⟩
  have hx : x = WeilDatum.classLeft d := by
    have hE : E₁ = WeilDatum.degZeroLeft d := Subtype.ext hE₁d
    refine Subtype.ext ?_
    show (x : Pic0 K F) = Pic0.mk (WeilDatum.degZeroLeft d)
    rw [← hE₁mk, hE]
  have hy : y = WeilDatum.classRight d := by
    have hE : E₂ = WeilDatum.degZeroRight d := Subtype.ext hE₂d
    refine Subtype.ext ?_
    show (y : Pic0 K F) = Pic0.mk (WeilDatum.degZeroRight d)
    rw [← hE₂mk, hE]
  show pair x y = d.pairing
  rw [hx, hy]
  exact compat d

/-! ## The divisorial Weil pairing data

`DivisorialWeilPairingData K F n` bundles the datum the pairing is built from: a pairing of
`n`-torsion classes (`pair`), its agreement with the datum pairing of every `WeilDatum`
(`compatible`), and the moving lemma (`move`) which chooses a degree-zero representative of a class
with rational support avoiding a prescribed finite set.  From it the two laws the bridge needs are
proved (`pair_zero_right`, `pair_add_right`), and `toChar`/`toHom` package the pairing as the
additive character valued hom `Pic0[n] →+ Additive (HomPic0Gm K F n)` on which nondegeneracy is
stated.

The block is the carrier part of the pin's `Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial`
(lines 444–709), at the pin's public names; `Perfect`/`toWeilPairingData` are not here (they need
`WeilPairingData`, which is the next `Def_` module's gate).
-/

section Carrier

variable (K F) in
/-- A divisorial Weil pairing datum: a pairing of `n`-torsion classes compatible with the datum
pairing, plus the moving lemma.  Pin `DivisorialWeilPairingData`. -/
structure DivisorialWeilPairingData (n : ℕ) [NeZero n] [HasPrincipalDivisors K F] where

  pair : Pic0.torsion K F n → Pic0.torsion K F n → K

  compatible : ∀ d : WeilDatum K F n, pair d.classLeft d.classRight = d.pairing

  move : ∀ (x : Pic0.torsion K F n) (S : Finset (Place K F)),
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = (x : Pic0 K F) ∧
      (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
      (∀ v ∈ (D : Divisor K F).support, v ∉ S)

namespace DivisorialWeilPairingData

variable {n : ℕ} [NeZero n] [HasPrincipalDivisors K F]
variable (e : DivisorialWeilPairingData K F n)

omit [NeZero n] [HasPrincipalDivisors K F] in
/-- A torsion class represented by `D` has a function whose orders are `n` times `D`'s.  Pin
`DivisorialWeilPairingData.exists_witness`. -/
theorem exists_witness (x : Pic0.torsion K F n) (D : Divisor.degZero (K := K) (F := F))
    (hD : Pic0.mk D = (x : Pic0 K F)) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  have hx : (n : ℤ) • (x : Pic0 K F) = 0 := Pic0.mem_torsion.mp x.2
  have h1 : Pic0.mk ((n : ℤ) • D) = 0 := by
    have h2 : Pic0.mk ((n : ℤ) • D) = (n : ℤ) • Pic0.mk D := by
      show QuotientAddGroup.mk ((n : ℤ) • D) = (n : ℤ) • (QuotientAddGroup.mk D)
      exact QuotientAddGroup.mk_zsmul
        ((Divisor.principal (K := K) (F := F)).addSubgroupOf
          (Divisor.degZero (K := K) (F := F))) D (n : ℤ)
    rw [h2, hD, hx]
  have h3 : ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
      (Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F)) :=
    (QuotientAddGroup.eq_zero_iff _).mp h1
  rw [AddSubgroup.mem_addSubgroupOf] at h3
  have h4 : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F)) := Divisor.mem_principal.mp h3
  obtain ⟨f, hf0, hford⟩ := h4
  refine ⟨f, hf0, fun v => ?_⟩
  have := hford v
  rw [Finsupp.smul_apply, smul_eq_mul] at this
  exact this.symm

include e in
/-- A Weil datum exists for any two torsion classes.  Pin
`DivisorialWeilPairingData.exists_datum`; it is the port's `hmove`-generalised `exists_datum_i` at
the datum's own `move`. -/
theorem exists_datum (x y : Pic0.torsion K F n) :
    ∃ d : WeilDatum K F n, d.classLeft = x ∧ d.classRight = y :=
  exists_datum_i e.move x y

include e in
/-- A pair of Weil data exists for `x + x'` and `y` with a shared second half.  Pin
`DivisorialWeilPairingData.exists_datum_pair`. -/
theorem exists_datum_pair (x x' y : Pic0.torsion K F n) :
    ∃ d d' : WeilDatum K F n, d.D₂ = d'.D₂ ∧ d.f₂ = d'.f₂ ∧
      d.classLeft = x ∧ d'.classLeft = x' ∧ d.classRight = y ∧ d'.classRight = y :=
  exists_datum_pair_i e.move x x' y

/-- Pin `DivisorialWeilPairingData.pair_ne_zero`. -/
theorem pair_ne_zero (x y : Pic0.torsion K F n) : e.pair x y ≠ 0 := by
  obtain ⟨d, hx, hy⟩ := e.exists_datum x y
  rw [← hx, ← hy, e.compatible d]
  exact d.pairing_ne_zero

/-- Pin `DivisorialWeilPairingData.pair_add_left`: the pairing is additive in its left argument. -/
theorem pair_add_left (x x' y : Pic0.torsion K F n) :
    e.pair (x + x') y = e.pair x y * e.pair x' y := by
  obtain ⟨d, d', hD₂, hf₂, hx, hx', hy, hy'⟩ := e.exists_datum_pair x x' y
  have h1 := e.compatible (d.addLeft d' hD₂ hf₂)
  rw [WeilDatum.classLeft_addLeft, WeilDatum.classRight_addLeft,
    WeilDatum.addLeft_pairing, hx, hx', hy] at h1
  rw [h1, ← e.compatible d, ← e.compatible d', hx, hx', hy, hy']

/-- Pin `DivisorialWeilPairingData.pair_mul_pair_swap`: the pairing of the swapped pair is the
inverse. -/
theorem pair_mul_pair_swap (x y : Pic0.torsion K F n) :
    e.pair x y * e.pair y x = 1 := by
  obtain ⟨d, hx, hy⟩ := e.exists_datum x y
  have h1 := e.compatible d
  have h2 := e.compatible d.symm
  rw [hx, hy] at h1
  rw [WeilDatum.classLeft_symm, WeilDatum.classRight_symm, hx, hy] at h2
  rw [h1, h2, WeilDatum.symm_pairing]
  exact mul_inv_cancel₀ (WeilDatum.pairing_ne_zero d)

/-- Pin `DivisorialWeilPairingData.pair_zero_left`. -/
theorem pair_zero_left (y : Pic0.torsion K F n) : e.pair 0 y = 1 := by
  classical
  obtain ⟨D₂, hD₂mk, hD₂rat, -⟩ := e.move y ∅
  obtain ⟨f₂, hf₂0, hf₂⟩ := exists_witness y D₂ hD₂mk
  set d : WeilDatum K F n :=
    ⟨0, (D₂ : Divisor K F), 1, f₂, one_ne_zero, hf₂0,
      fun v => by simp [Place.ord_one],
      hf₂, fun v => Or.inl rfl,
      fun v hv => by
        rcases hv with h1 | h2
        · exact absurd rfl h1
        · exact hD₂rat v (Finsupp.mem_support_iff.mpr h2)⟩ with hd
  have h1 := e.compatible d
  have hclassL : d.classLeft = 0 := by
    have h0 : d.degZeroLeft = (0 : Divisor.degZero (K := K) (F := F)) := Subtype.ext rfl
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classLeft, h0, Pic0.mk_zero]
    simp
  have hclassR : d.classRight = y := by
    refine Subtype.ext ?_
    show Pic0.mk _ = (y : Pic0 K F)
    rw [← hD₂mk]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  have hpairing : d.pairing = 1 := by
    show Divisor.evalFun (1 : F) (D₂ : Divisor K F) / Divisor.evalFun f₂ (0 : Divisor K F) = 1
    rw [Divisor.evalFun_one, Divisor.evalFun_zero, div_one]
  rw [hclassL, hclassR, hpairing] at h1
  exact h1

/-- Pin `DivisorialWeilPairingData.pair_zero_right`. -/
theorem pair_zero_right (x : Pic0.torsion K F n) : e.pair x 0 = 1 := by
  have h1 := e.pair_mul_pair_swap x 0
  rw [e.pair_zero_left x, mul_one] at h1
  exact h1

/-- Pin `DivisorialWeilPairingData.pair_swap_eq_inv`. -/
theorem pair_swap_eq_inv (x y : Pic0.torsion K F n) : e.pair y x = (e.pair x y)⁻¹ :=
  eq_inv_of_mul_eq_one_left (e.pair_mul_pair_swap y x)

/-- Pin `DivisorialWeilPairingData.pair_add_right`: additivity in the right argument, from the
swap. -/
theorem pair_add_right (x y y' : Pic0.torsion K F n) :
    e.pair x (y + y') = e.pair x y * e.pair x y' := by
  calc e.pair x (y + y') = (e.pair (y + y') x)⁻¹ := e.pair_swap_eq_inv (y + y') x
    _ = (e.pair y x * e.pair y' x)⁻¹ := by rw [e.pair_add_left y y' x]
    _ = (e.pair y x)⁻¹ * (e.pair y' x)⁻¹ := by rw [mul_inv]
    _ = e.pair x y * e.pair x y' := by
        rw [e.pair_swap_eq_inv x y, e.pair_swap_eq_inv x y', inv_inv, inv_inv]

/-- Pin `DivisorialWeilPairingData.toChar`: the pairing is a character in its second argument. -/
def toChar (x : Pic0.torsion K F n) : HomPic0Gm K F n where
  toFun y := e.pair x y
  map_zero_eq_one' := e.pair_zero_right x
  map_add_eq_mul' y y' := e.pair_add_right x y y'

@[simp] theorem toChar_apply (x y : Pic0.torsion K F n) : e.toChar x y = e.pair x y := rfl

/-- Pin `DivisorialWeilPairingData.toHom`: the pairing as an additive homomorphism into the
character group. -/
def toHom : Pic0.torsion K F n →+ Additive (HomPic0Gm K F n) :=
  AddMonoidHom.mk' (fun x => Additive.ofMul (e.toChar x)) (by
    intro x x'
    have h : e.toChar (x + x') = e.toChar x * e.toChar x' := by
      ext y
      rw [AddChar.mul_apply]
      exact e.pair_add_left x x' y
    show Additive.ofMul (e.toChar (x + x'))
        = Additive.ofMul (e.toChar x) + Additive.ofMul (e.toChar x')
    rw [h, ofMul_mul])

@[simp] theorem toHom_apply_apply (x y : Pic0.torsion K F n) :
    (Additive.toMul (e.toHom x)) y = e.pair x y := rfl

end DivisorialWeilPairingData

end Carrier

end AlgebraicCurve
