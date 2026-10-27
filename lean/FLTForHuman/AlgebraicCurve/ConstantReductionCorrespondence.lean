/-
Constant reduction commutes with a correspondence, and with the base change of a
correspondence along a constant field extension of the base field.

Let `K ⊆ F` be the function field of a curve over an algebraically closed field
`K` of characteristic zero, `F'` a second function field over `K`, and
`φ ψ : F →ₐ[K] F'` integral `K`-algebra maps, defining the correspondence
`ψ_* ∘ φ^*` on divisors.  Let `E ⊇ K` be a second algebraically closed field, with
`FE ⊇ F` and `F'E ⊇ F'` function fields over `E` (constant field extensions), and
let `r` send a place of `FE` to its centre over `K`: for a valuation subring `A` of
`E` with residue field `K`, the reduced place `r P` is characterised by
`f ∈ r P ↔ ∃ a ∈ A, f - a` has positive valuation at `P`.  Under this reduction
the base-changed correspondence and the correspondence agree:

`mapDomain r (correspondence φE ψE D) = correspondence φ ψ (mapDomain r D)`.

The proof computes both sides place by place.  For a place `P` of `FE` centred at an
embedding `e : F →ₐ[K] E`, every place `W` of `F'E` above `P` is unramified over
`FE` and is centred at an embedding `σ : F' →ₐ[K] E` with `σ ∘ φ = e`, and
conversely, so the places above `P` are exactly the embeddings over it; the
multiplicity of a place `q` of `F'` above `r P` is then the number of those `σ`
with `σ ∘ ψ` the centre of `q`, which is the count of `K`-embeddings above a place.
For a place `P` that is not centred, `r P` is the comap of `P` along the structure
map and the fibre above `P` is a single place, whose ramification index equals that
of `q` above `r P` — both read off at a uniformiser of `r P`.  Summing the two
fibrewise identities over the places above `r P` gives the identity on a single
place, and additivity gives it for every divisor.

Assumes: the uniqueness of the centred place, the existence of a place with
prescribed comap, and the count of `K`-embeddings above a place, together with the
fibre computation for a base-changed correspondence.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence.lean

spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.Defs.RestrictAlongAPI
import FLTForHuman.AlgebraicCurve.IsCurveOver.BaseChangeCorrespondence
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionExists
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtensionRamification
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing

namespace AlgebraicCurve

namespace PlaceReductionCorrespondence

open BaseChangeCorrespondence

section General

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [Algebra K E] [Algebra F L]

/-- A place centred at an embedding of `F` cuts out the same place as `A` does. -/
theorem exists_mem_valuation_sub_lt_one_iff_of_centred (P : Place E L) {σ : F →ₐ[K] E}
    (hσ : ∀ f : F, P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L (σ f)) < 1)
    (A : ValuationSubring E) (f : F) :
    (∃ a : E, a ∈ A ∧
        P.toValuationSubring.valuation (algebraMap F L f - algebraMap E L a) < 1) ↔ σ f ∈ A := by
  constructor
  · rintro ⟨a, haA, ha⟩
    have h : P.toValuationSubring.valuation (algebraMap E L (σ f - a)) < 1 := by
      have := Valuation.map_sub P.toValuationSubring.valuation
        (algebraMap F L f - algebraMap E L a) (algebraMap F L f - algebraMap E L (σ f))
      rw [sub_sub_sub_cancel_left, ← map_sub] at this
      exact this.trans_lt (max_lt ha (hσ f))
    rwa [sub_eq_zero.mp (CentredPlaceRigidity.eq_zero_of_valuation_algebraMap_lt_one P h)]
  · intro h
    exact ⟨σ f, h, hσ f⟩

end General

section Transport

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

/-- A `K`-algebra map into `E` cannot be integral into a proper valuation subring
whose residue field is `K`: a transcendental generator would have an algebraic
residue. -/
theorem comap_ne_top_of_transcendental {L E : Type*} [Field L] [Field E] [Algebra K L]
    [Algebra K E] (A : ValuationSubring E)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (σ : L →ₐ[K] E) {x : L} (hx : Transcendental K x) : A.comap σ.toRingHom ≠ ⊤ := by
  intro htop
  have hall : ∀ y : L, σ y ∈ A := fun y => by
    have hy : y ∈ A.comap σ.toRingHom := by rw [htop]; exact ValuationSubring.mem_top y
    exact hy
  obtain ⟨k, hk⟩ := hArat (σ x) (hall x)
  have hy0 : x - algebraMap K L k ≠ 0 := fun h => hx (by
    rw [sub_eq_zero.mp h]
    exact isAlgebraic_algebraMap k)
  have hval : A.valuation (σ (x - algebraMap K L k)) < 1 := by
    rwa [map_sub, AlgHom.commutes]
  have hσ0 : σ (x - algebraMap K L k) ≠ 0 := (map_ne_zero σ).mpr hy0
  exact (valuation_lt_one_iff_inv_not_mem A hσ0).mp hval (by rw [← map_inv₀]; exact hall _)

end Transport

section NotIntegral

variable {K L E LE : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K] [IsCurveOver K L]
  [Field E] [Field LE] [Algebra K E] [Algebra E LE] [Algebra L LE] [Algebra K LE]
  [IsScalarTower K E LE] [IsScalarTower K L LE]

/-- At a place that is not centred, the condition defining the reduced place is
equivalent to membership in the comap. -/
theorem exists_mem_valuation_sub_lt_one_iff_of_comap (Q : Place E LE) (q : Place K L)
    (hq : q.toValuationSubring = Q.toValuationSubring.comap (algebraMap L LE))
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A) (g : L) :
    (∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1) ↔
      algebraMap L LE g ∈ Q.toValuationSubring := by
  constructor
  · rintro ⟨a, -, ha⟩
    have h := add_mem (CentredPlaceRigidity.mem_of_valuation_lt_one Q ha) (Q.algebraMap_mem' a)
    rwa [sub_add_cancel] at h
  · intro hg
    have hgq : g ∈ q.toValuationSubring := by rw [hq]; exact hg
    haveI : Module.Finite K q.ResidueField := IsCurveOver.finiteResidue q
    haveI : Algebra.IsIntegral K q.ResidueField := Algebra.IsIntegral.of_finite K q.ResidueField
    have hsurj : Function.Surjective (algebraMap K q.ResidueField) :=
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := q.ResidueField)).2
    obtain ⟨k, hk⟩ := hsurj (IsLocalRing.residue _ ⟨g, hgq⟩)
    have hmem : (⟨g, hgq⟩ : q.toValuationSubring) - algebraMap K q.toValuationSubring k ∈
        IsLocalRing.maximalIdeal q.toValuationSubring := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      change IsLocalRing.residue _ _ = IsLocalRing.residue _ _
      rw [← hk, IsScalarTower.algebraMap_apply K q.toValuationSubring q.ResidueField]
      rfl
    have hlt : q.toValuationSubring.valuation (g - algebraMap K L k) < 1 := by
      have h := (ValuationSubring.valuation_lt_one_iff _ _).mp hmem
      simpa only [AddSubgroupClass.coe_sub, Place.coe_algebraMap] using h
    rw [hq, valuation_comap_lt_one_iff] at hlt
    refine ⟨algebraMap K E k, hKA k, ?_⟩
    rwa [map_sub, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K E LE] at hlt

end NotIntegral

section Restrict

variable {E FE F'E : Type*} [Field E] [Field FE] [Algebra E FE] [Field F'E] [Algebra E F'E]

/-- Reduction of a place commutes with restriction along an integral map, when
both sides are cut out by the same valuation subring `A` of `E`. -/
theorem reduction_restrictAlong {K F F' : Type*} [Field K] [Field F] [Algebra K F] [Field F']
    [Algebra K F'] [Algebra K E] [Algebra F FE] [Algebra F' F'E]
    [HasPrincipalDivisors E F'E] [HasPrincipalDivisors K F']
    (χ : F →ₐ[K] F') (hχ : χ.toRingHom.IsIntegral) (χE : FE →ₐ[E] F'E)
    (hχE : χE.toRingHom.IsIntegral)
    (hcomm : ∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f))
    (A : ValuationSubring E)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (r' : Place E F'E → Place K F')
    (hr' : ∀ (Q : Place E F'E) (g : F'), g ∈ (r' Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap F' F'E g - algebraMap E F'E a) < 1)
    (W : Place E F'E) :
    r (W.restrictAlong χE hχE) = (r' W).restrictAlong χ hχ := by
  refine Place.ext (SetLike.ext fun f => ?_)
  rw [Place.mem_restrictAlong_iff, hr, hr']
  refine exists_congr fun a => and_congr_right fun _ => ?_
  rw [valuation_restrictAlong_lt_one_iff, map_sub, hcomm, AlgHom.commutes]

end Restrict

/-- Sum a function of `g ∘ θ` over `S` fibre by fibre, against prescribed fibre
sums `b`: the two finsupp sums agree when the coefficients agree on every fibre. -/
theorem sum_single_fiberwise {ι κ Pl : Type*} [DecidableEq κ] (S : Finset ι) (T : Finset κ)
    (θ : ι → κ) (g : κ → Pl) (a : ι → ℤ) (b : κ → ℤ) (n : ℤ)
    (hθ : ∀ i ∈ S, θ i ∈ T) (hfib : ∀ k ∈ T, ∑ i ∈ S with θ i = k, a i = b k) :
    ∑ i ∈ S, Finsupp.single (g (θ i)) (n * a i) =
      ∑ k ∈ T, (Finsupp.single (g k) (n * b k) : Pl →₀ ℤ) := by
  rw [← Finset.sum_fiberwise_of_maps_to hθ]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← hfib k hk, Finset.mul_sum, Finsupp.single_finsetSum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

section Reduction

variable {K L E LE : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed K] [CharZero K]
  [IsCurveOver K L]
  [Field E] [Field LE] [Algebra K E] [Algebra E LE] [Algebra L LE] [Algebra K LE]
  [IsScalarTower K E LE] [IsScalarTower K L LE] [IsAlgClosed E] [IsCurveOver E LE]

/-- Existence of the constant reduction of places: on a constant field extension
of `L`, centred places are cut out by the valuation subring `A` of `E`. -/
theorem exists_reduction
    (hfg : ∃ x : L, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L)
    (hfgE : ∃ x : LE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set LE)) LE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap L LE)) = ⊤)
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1) :
    ∃ r : Place E LE → Place K L, ∀ (Q : Place E LE) (g : L), g ∈ (r Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1 := by
  classical
  have C1 := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K L hfg E LE hfgE hgen
  obtain ⟨x, hx, hfinx⟩ := hfg
  haveI := hfinx
  suffices h : ∀ Q : Place E LE, ∃ q : Place K L, ∀ g : L, g ∈ q.toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1 by
    choose r hr using h
    exact ⟨r, hr⟩
  intro Q
  by_cases hint : ∀ g : L, algebraMap L LE g ∈ Q.toValuationSubring
  ·
    obtain ⟨σ, hσ⟩ := C1.2 Q hint
    have hAK : ∀ k : K, algebraMap K L k ∈ A.comap σ.toRingHom := fun k => by
      rw [ValuationSubring.mem_comap]
      change σ (algebraMap K L k) ∈ A
      rw [AlgHom.commutes]
      exact hKA k
    have hne : A.comap σ.toRingHom ≠ ⊤ := comap_ne_top_of_transcendental A hArat σ hx
    obtain ⟨q, hq⟩ := Place.exists_of_valuationSubring x (A.comap σ.toRingHom) hAK hne
    refine ⟨q, fun g => ?_⟩
    rw [hq, ValuationSubring.mem_comap, exists_mem_valuation_sub_lt_one_iff_of_centred Q hσ A g]
    rfl
  ·
    push Not at hint
    obtain ⟨g₀, hg₀⟩ := hint
    have hwK : ∀ k : K, algebraMap L LE (algebraMap K L k) ∈ Q.toValuationSubring := fun k => by
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K E LE]
      exact Q.algebraMap_mem' _
    obtain ⟨q, hq⟩ := Place.exists_toValuationSubring_eq_comap_ringHom x (algebraMap L LE)
      Q.toValuationSubring hwK ⟨g₀, hg₀⟩
    refine ⟨q, fun g => ?_⟩
    rw [exists_mem_valuation_sub_lt_one_iff_of_comap Q q hq A hKA g, hq,
      ValuationSubring.mem_comap]

omit [IsAlgClosed E] [IsCurveOver E LE] in

/-- At a place that is not centred, the reduced place is the comap along the
structure map of `L` into `LE`. -/
theorem reduction_eq_comap_of_not_forall_mem
    (hfg : ∃ x : L, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set L)) L)
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (r : Place E LE → Place K L)
    (hr : ∀ (Q : Place E LE) (g : L), g ∈ (r Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1)
    {Q : Place E LE} (hQ : ¬ ∀ g : L, algebraMap L LE g ∈ Q.toValuationSubring) :
    (r Q).toValuationSubring = Q.toValuationSubring.comap (algebraMap L LE) := by
  obtain ⟨x, -, hfinx⟩ := hfg
  haveI := hfinx
  push Not at hQ
  obtain ⟨g₀, hg₀⟩ := hQ
  have hwK : ∀ k : K, algebraMap L LE (algebraMap K L k) ∈ Q.toValuationSubring := fun k => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K E LE]
    exact Q.algebraMap_mem' _
  obtain ⟨q, hq⟩ := Place.exists_toValuationSubring_eq_comap_ringHom x (algebraMap L LE)
    Q.toValuationSubring hwK ⟨g₀, hg₀⟩
  refine SetLike.ext fun g => ?_
  rw [hr, exists_mem_valuation_sub_lt_one_iff_of_comap Q q hq A hKA g, ValuationSubring.mem_comap]

omit [IsAlgClosed K] [CharZero K] [IsCurveOver K L] [Algebra K LE] [IsScalarTower K E LE]
  [IsScalarTower K L LE] [IsAlgClosed E] [IsCurveOver E LE] in

/-- The membership form of the reduction, at a place centred at `σ`. -/
theorem mem_reduction_iff_of_centred
    (A : ValuationSubring E) (r : Place E LE → Place K L)
    (hr : ∀ (Q : Place E LE) (g : L), g ∈ (r Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE a) < 1)
    {Q : Place E LE} {σ : L →ₐ[K] E}
    (hσ : ∀ g : L, Q.toValuationSubring.valuation (algebraMap L LE g - algebraMap E LE (σ g)) < 1)
    (g : L) : g ∈ (r Q).toValuationSubring ↔ σ g ∈ A := by
  rw [hr, exists_mem_valuation_sub_lt_one_iff_of_centred Q hσ A g]

end Reduction

section Fibre

variable {K F E FE F' F'E : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
  [IsCurveOver K F]
  [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
  [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
  [Field F'] [Algebra K F'] [IsCurveOver K F']
  [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
  [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]

/-- The fibrewise identity for the reduction at a centred place: the places of
`F'E` above `P` that reduce to a fixed place `q` of `F'` carry, counted with their
ramification indices, exactly the number of embeddings over `q`. -/
theorem fibre_identity_of_forall_mem
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfinφ : FiniteAlong K φ)
    (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hFIE : FundamentalIdentityAlong E φE hφE)
    (A : ValuationSubring E)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (r' : Place E F'E → Place K F')
    (hr' : ∀ (Q : Place E F'E) (g : F'), g ∈ (r' Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap F' F'E g - algebraMap E F'E a) < 1)
    {P : Place E FE} (hint : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring)
    {q : Place K F'} (hq : q ∈ Place.fiberAlong φ hφ (r P)) [DecidableEq (Place K F')] :
    ∑ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q),
        (W.ramificationIndexAlong φE : ℤ) = q.ramificationIndexAlong φ := by

  obtain ⟨e, hP⟩ := (Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F hfg E FE hfgE hgen).2 P hint
  have C1F' := Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension
    K F' hfg' E F'E hfgE' hgen'
  choose Qc hQc hQu using C1F'.1
  obtain ⟨ha, hb, hc, hSfin⟩ :=
    fibre_centred hfg hfgE hgen hfg' hfgE' hgen' φ hfinφ φE hφE hφcomm hFIE hP

  have hev₀ : ∀ f : F, f ∈ (r P).toValuationSubring ↔ e f ∈ A := fun f =>
    mem_reduction_iff_of_centred A r hr hP f

  have hcount := Place.ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong K F F' hfg φ hφ
    hfinφ E A e (r P) hev₀ q (Place.mem_fiberAlong.mp hq)
  set Sq : Set (F' →ₐ[K] E) := {σ | σ.comp φ = e ∧
    ∀ g : F', g ∈ q.toValuationSubring ↔ σ g ∈ A} with hSq

  have hinj : Function.Injective Qc := fun σ τ h =>
    CentredPlaceRigidity.centre_unique (Qc σ) (hQc σ) (fun y => by rw [h]; exact hQc τ y)
  have himage : (((Place.fiberAlong φE hφE P).filter (fun W => r' W = q) : Finset (Place E F'E)) :
      Set (Place E F'E)) = Qc '' Sq := by
    ext W
    rw [Finset.coe_filter, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hW, hWq⟩
      obtain ⟨σ, hσ, hWσ⟩ := hb W hW
      refine ⟨σ, ⟨hσ, fun g => ?_⟩, (hQu σ W hWσ).symm⟩
      rw [← hWq]
      exact mem_reduction_iff_of_centred A r' hr' hWσ g
    · rintro ⟨σ, ⟨hσ, hσq⟩, rfl⟩
      refine ⟨hc σ _ hσ (hQc σ), Place.ext (SetLike.ext fun g => ?_)⟩
      rw [mem_reduction_iff_of_centred A r' hr' (hQc σ) g, hσq g]

  have hone : ∀ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q),
      (W.ramificationIndexAlong φE : ℤ) = 1 := fun W hW => by
    rw [ha W (Finset.mem_filter.mp hW).1, Nat.cast_one]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one, ← hcount,
    ← Set.ncard_coe_finset, himage, Set.ncard_image_of_injective _ hinj]

omit [CharZero K] [IsAlgClosed K] [IsCurveOver K F] [Algebra K E] [Algebra K FE] [IsScalarTower K E FE]
  [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE] [IsCurveOver K F'] [Algebra K F'E]
  [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E] in

/-- At a uniformiser of the reduced place, the ramification index of a place of
`F'E` is that of the place of `F'` it reduces to. -/
theorem ramificationIndexAlong_eq_of_ord_eq [HasPrincipalDivisors K F']
    [HasPrincipalDivisors E F'E]
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    {P : Place E FE} {v₀ : Place K F} (hPord : ∀ f : F, P.ord (algebraMap F FE f) = v₀.ord f)
    {q : Place K F'} (hq : q.restrictAlong φ hφ = v₀)
    {W : Place E F'E} (hWord : ∀ g : F', W.ord (algebraMap F' F'E g) = q.ord g)
    (hWP : W.restrictAlong φE hφE = P) :
    W.ramificationIndexAlong φE = q.ramificationIndexAlong φ := by

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v₀.toValuationSubring
  have hg : v₀.ord (π : F) = 1 := v₀.ord_coe_irreducible hπ
  have h1 : q.ord (φ π) = q.ramificationIndexAlong φ := by
    rw [Place.ord_restrictAlong φ hφ, hq, hg, mul_one]
  have h2 : W.ord (φE (algebraMap F FE π)) = W.ramificationIndexAlong φE := by
    rw [Place.ord_restrictAlong φE hφE, hWP, hPord, hg, mul_one]
  have h3 : (W.ramificationIndexAlong φE : ℤ) = q.ramificationIndexAlong φ := by
    rw [← h1, ← h2, hφcomm, hWord]
  exact_mod_cast h3

omit [IsAlgClosed E] [IsCurveOver E FE] in

/-- The fibrewise identity at a place that is not centred: the fibre is a single
place, whose ramification index is that of its reduction. -/
theorem fibre_identity_of_not_forall_mem
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (φE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (r' : Place E F'E → Place K F')
    (hr' : ∀ (Q : Place E F'E) (g : F'), g ∈ (r' Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap F' F'E g - algebraMap E F'E a) < 1)
    {P : Place E FE} (hint : ¬ ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring)
    {q : Place K F'} (hq : q ∈ Place.fiberAlong φ hφ (r P)) [DecidableEq (Place K F')] :
    ∑ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q),
        (W.ramificationIndexAlong φE : ℤ) = q.ramificationIndexAlong φ := by

  have hrP : (r P).toValuationSubring = P.toValuationSubring.comap (algebraMap F FE) :=
    reduction_eq_comap_of_not_forall_mem hfg A hKA r hr hint
  obtain ⟨P', -, hP'ord, hP'u⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE hfg hfgE hgen (r P)
  have hPP' : P = P' := hP'u P hrP.symm
  have hPord : ∀ f : F, P.ord (algebraMap F FE f) = (r P).ord f := fun f => by
    rw [← hP'ord f, hPP']

  obtain ⟨Wq, hWq, hWqord, hWqu⟩ :=
    Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F' E F'E hfg' hfgE' hgen' q
  have hqv : q.restrictAlong φ hφ = r P := Place.mem_fiberAlong.mp hq

  have hWqP : Wq.restrictAlong φE hφE = P := by
    rw [hPP']
    refine hP'u _ (SetLike.ext fun f => ?_)
    rw [ValuationSubring.mem_comap, Place.mem_restrictAlong_iff, hφcomm, ← hqv,
      Place.mem_restrictAlong_iff,
      ← hWq, ValuationSubring.mem_comap]

  have hrWq : r' Wq = q := by
    refine Place.ext (SetLike.ext fun g => ?_)
    rw [hr', exists_mem_valuation_sub_lt_one_iff_of_comap Wq q hWq.symm A hKA g, ← hWq,
      ValuationSubring.mem_comap]

  obtain ⟨f₀, hf₀⟩ : ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring := by
    push Not at hint
    exact hint
  have huniq : ∀ W ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q), W = Wq := by
    intro W hW
    obtain ⟨hWZ, hWq'⟩ := Finset.mem_filter.mp hW
    have hWP : W.restrictAlong φE hφE = P := Place.mem_fiberAlong.mp hWZ

    have hWint : ¬ ∀ g : F', algebraMap F' F'E g ∈ W.toValuationSubring := fun h => hf₀ (by
      rw [← hWP, Place.mem_restrictAlong_iff, hφcomm]
      exact h (φ f₀))
    have hW' : (r' W).toValuationSubring = W.toValuationSubring.comap (algebraMap F' F'E) :=
      reduction_eq_comap_of_not_forall_mem hfg' A hKA r' hr' hWint
    rw [hWq'] at hW'
    exact hWqu W hW'.symm

  have he : Wq.ramificationIndexAlong φE = q.ramificationIndexAlong φ :=
    ramificationIndexAlong_eq_of_ord_eq φ hφ φE hφE hφcomm hPord hqv hWqord hWqP

  have hmem : Wq ∈ (Place.fiberAlong φE hφE P).filter (fun W => r' W = q) :=
    Finset.mem_filter.mpr ⟨Place.mem_fiberAlong.mpr hWqP, hrWq⟩
  have hsingle : (Place.fiberAlong φE hφE P).filter (fun W => r' W = q) = {Wq} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hmem, huniq⟩
  rw [hsingle, Finset.sum_singleton, he]

/-- The reduction identity on a single place: the correspondence and the reduction
commute on `single P n`, by the fibrewise identities above. -/
theorem mapDomain_correspondence_single
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfinφ : FiniteAlong K φ)
    (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hFIE : FundamentalIdentityAlong E φE hφE)
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (r' : Place E F'E → Place K F')
    (hr' : ∀ (Q : Place E F'E) (g : F'), g ∈ (r' Q).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧
        Q.toValuationSubring.valuation (algebraMap F' F'E g - algebraMap E F'E a) < 1)
    (P : Place E FE) (n : ℤ) :
    Finsupp.mapDomain r (Divisor.correspondence φE ψE hφE hψE (Finsupp.single P n)) =
      Divisor.correspondence φ ψ hφ hψ (Finsupp.mapDomain r (Finsupp.single P n)) := by
  classical

  have hR : ∀ q ∈ Place.fiberAlong φ hφ (r P),
      Divisor.pushforwardAlong ψ hψ (Finsupp.single q (n * (q.ramificationIndexAlong φ : ℤ))) =
        Finsupp.single (q.restrictAlong ψ hψ) (n * (q.ramificationIndexAlong φ : ℤ)) := by
    intro q _
    rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one, Nat.cast_one, mul_one]
  have hRHS : Divisor.correspondence φ ψ hφ hψ (Finsupp.mapDomain r (Finsupp.single P n)) =
      ∑ q ∈ Place.fiberAlong φ hφ (r P),
        Finsupp.single (q.restrictAlong ψ hψ) (n * (q.ramificationIndexAlong φ : ℤ)) := by
    rw [Finsupp.mapDomain_single, Divisor.correspondence_apply, Divisor.pullbackAlong_single,
      map_sum]
    exact Finset.sum_congr rfl hR

  have hL : ∀ W ∈ Place.fiberAlong φE hφE P,
      Finsupp.mapDomain r (Divisor.pushforwardAlong ψE hψE
        (Finsupp.single W (n * (W.ramificationIndexAlong φE : ℤ)))) =
        Finsupp.single ((r' W).restrictAlong ψ hψ) (n * (W.ramificationIndexAlong φE : ℤ)) := by
    intro W _
    rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one, Nat.cast_one, mul_one,
      Finsupp.mapDomain_single, reduction_restrictAlong ψ hψ ψE hψE hψcomm A r hr r' hr' W]
  have hLHS : Finsupp.mapDomain r (Divisor.correspondence φE ψE hφE hψE (Finsupp.single P n)) =
      ∑ W ∈ Place.fiberAlong φE hφE P,
        Finsupp.single ((r' W).restrictAlong ψ hψ) (n * (W.ramificationIndexAlong φE : ℤ)) := by
    rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum,
      Finsupp.mapDomain_finsetSum]
    exact Finset.sum_congr rfl hL
  rw [hLHS, hRHS]

  refine sum_single_fiberwise (Place.fiberAlong φE hφE P) (Place.fiberAlong φ hφ (r P)) r'
    (fun q => q.restrictAlong ψ hψ) (fun W => (W.ramificationIndexAlong φE : ℤ))
    (fun q => (q.ramificationIndexAlong φ : ℤ)) n (fun W hW => ?_) (fun q hq => ?_)
  ·
    rw [Place.mem_fiberAlong, ← reduction_restrictAlong φ hφ φE hφE hφcomm A r hr r' hr' W,
      Place.mem_fiberAlong.mp hW]
  ·
    by_cases hint : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring
    · exact fibre_identity_of_forall_mem hfg hfgE hgen hfg' hfgE' hgen' φ hφ hfinφ φE hφE
        hφcomm hFIE A r hr r' hr' hint hq
    · exact fibre_identity_of_not_forall_mem hfg hfgE hgen hfg' hfgE' hgen' φ hφ φE hφE hφcomm
        A hKA r hr r' hr' hint hq

end Fibre

end PlaceReductionCorrespondence

end AlgebraicCurve

open AlgebraicCurve.PlaceReductionCorrespondence AlgebraicCurve.BaseChangeCorrespondence in
theorem AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ)
    (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [IsAlgClosed E] [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE ψE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (hFIE : FundamentalIdentityAlong E φE hφE)
    (hfinE : FiniteAlong E ψE) (hNE : NormFormulaAlong E ψE hfinE)
    (A : ValuationSubring E) (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (r : Place E FE → Place K F)
    (hr : ∀ (P : Place E FE) (f : F), f ∈ (r P).toValuationSubring ↔
      ∃ a : E, a ∈ A ∧ P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE a) < 1)
    (D : Divisor E FE) :
    Finsupp.mapDomain r (Divisor.correspondence φE ψE hφE hψE D) =
      Divisor.correspondence φ ψ hφ hψ (Finsupp.mapDomain r D) := by
  classical

  have _hFI := hFI
  have _hN := hN
  have _hNE := hNE
  clear hFI hN _hFI _hN _hNE
  obtain ⟨x, hx, hfinx⟩ := id hfg

  have hroof := fg_of_finiteAlong ψ hfin hx hfinx
  have hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F' :=
    ⟨ψ x, hroof.1, hroof.2⟩
  haveI : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  haveI hCF' : IsCurveOver K F' := by
    haveI := hroof.2
    haveI : Algebra.IsSeparable (IntermediateField.adjoin K ({ψ x} : Set F')) F' :=
      Algebra.IsSeparable.of_integral _ _
    exact isCurveOver_of_transcendental_of_isSeparable K F' (ψ x) hroof.1 hroof.2 inferInstance
  haveI : Algebra.EssFiniteType K F' := essFiniteType_of_fg hfg'
  have hfinφ : FiniteAlong K φ := finiteAlong_of_isIntegral φ hφ

  obtain ⟨r', hr'⟩ := exists_reduction (K := K) (L := F') (E := E) (LE := F'E)
    hfg' hfgE' hgen' A hKA hArat

  suffices h : (Finsupp.mapDomain.addMonoidHom r).comp
      (Divisor.correspondence φE ψE hφE hψE) =
      (Divisor.correspondence φ ψ hφ hψ).comp (Finsupp.mapDomain.addMonoidHom r) from
    DFunLike.congr_fun h D
  refine Finsupp.addHom_ext fun P n => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.mapDomain.addMonoidHom_apply]
  exact mapDomain_correspondence_single hfg hfgE hgen hfg' hfgE' hgen' φ ψ hφ hψ hfinφ φE ψE
    hφE hψE hφcomm hψcomm hFIE A hKA r hr r' hr' P n
