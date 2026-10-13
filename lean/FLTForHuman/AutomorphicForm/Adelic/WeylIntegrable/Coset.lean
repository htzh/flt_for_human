/-
  The coset transversal of the integral finite adèles and its finite modulus.

  `slab S T = {x : 𝔸 | x.1 ∈ S ∧ x.2 ∈ T}` is the product of an archimedean set and a
  finite set; `measure_slab_eq_relIndex_mul` computes the measure of a slab over a
  subgroup `B` as the relative index `A.relIndex B` times the measure over `A`, which is
  the index bookkeeping the Bruhat-transversal bound uses. `intLattice` is the integral
  finite adèles as an additive subgroup, `dilate y` its dilation by a finite idèle, and
  `distribHaarChar_finIdele` identifies the distributive Haar character of the
  corresponding adèle idèle with that relative index.

  Transcribed from `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`
  lines 677–851 (pinned `aa2d8b3`), sections `Coset` and `ModFin` of the pin namespace
  `AutomorphicForm.WeylIntegrable`.
-/
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum TopologicalSpace Filter
open NumberField.AdelicBox
open NumberField.AdelicHaar
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace AutomorphicForm

namespace WeylIntegrable

section Coset

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

-- pin: toAdele (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:687)
def toAdele (a : 𝔸∞) (b : 𝔸f) : 𝔸 := (a, b)

-- pin: toAdele_fst (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:689)
@[scoped simp] theorem toAdele_fst (a : 𝔸∞) (b : 𝔸f) : (toAdele F a b).1 = a := rfl
-- pin: toAdele_snd (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:690)
@[scoped simp] theorem toAdele_snd (a : 𝔸∞) (b : 𝔸f) : (toAdele F a b).2 = b := rfl

-- pin: slab (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:692)
def slab (S : Set 𝔸∞) (T : Set 𝔸f) : Set 𝔸 := {x | x.1 ∈ S ∧ x.2 ∈ T}

-- pin: mem_slab (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:694)
theorem mem_slab {S : Set 𝔸∞} {T : Set 𝔸f} {x : 𝔸} : x ∈ slab F S T ↔ x.1 ∈ S ∧ x.2 ∈ T := Iff.rfl

-- pin: isClosed_slab (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:696)
theorem isClosed_slab {S : Set 𝔸∞} {T : Set 𝔸f} (hS : IsClosed S) (hT : IsClosed T) : IsClosed (slab F S T) :=
  (hS.preimage continuous_fst).inter (hT.preimage continuous_snd)

-- pin: vadd_slab (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:699)
theorem vadd_slab (S : Set 𝔸∞) (T : Set 𝔸f) (c : 𝔸f) :
    toAdele F 0 c +ᵥ slab F S T = slab F S (c +ᵥ T) := by
  ext x
  simp only [Set.mem_vadd_set, mem_slab, vadd_eq_add]
  constructor
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have h1 : (toAdele F 0 c + z).1 = z.1 := show (0 : 𝔸∞) + z.1 = z.1 from zero_add _
    have h2 : (toAdele F 0 c + z).2 = c + z.2 := rfl
    rw [h1, h2]
    exact ⟨hz1, z.2, hz2, rfl⟩
  · rintro ⟨hx1, ⟨t, ht, hxt⟩⟩
    refine ⟨toAdele F x.1 t, ⟨hx1, ht⟩, Prod.ext ?_ ?_⟩
    · show (0 : 𝔸∞) + x.1 = x.1
      rw [zero_add]
    · show c + t = x.2
      exact hxt

-- the pin's `haveI` walls are load-bearing: they feed the instance searches below.
set_option linter.style.haveILetI false in
-- pin: measure_slab_eq_relIndex_mul (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:716)
theorem measure_slab_eq_relIndex_mul (μ : Measure 𝔸) [μ.IsAddLeftInvariant] {S : Set 𝔸∞} (hS : IsClosed S)
    (A B : AddSubgroup 𝔸f) (hAB : A ≤ B) (hA : IsClosed (A : Set 𝔸f)) (hfin : A.relIndex B ≠ 0) :
    μ (slab F S B) = A.relIndex B * μ (slab F S A) := by
  classical

  set H : AddSubgroup B := A.addSubgroupOf B with hH
  haveI : H.FiniteIndex := ⟨hfin⟩
  obtain ⟨s, hs, -⟩ := H.exists_isComplement_left 0
  haveI : Finite s := hs.finite_left_iff.mpr inferInstance
  have hcard : Nat.card s = A.relIndex B := hs.card_left

  have hcover : (B : Set 𝔸f) = ⋃ c : s, ((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f) := by
    ext b
    simp only [Set.mem_iUnion, Set.mem_vadd_set, SetLike.mem_coe]
    constructor
    · intro hb
      have hmem : (⟨b, hb⟩ : B) ∈ (Set.univ : Set B) := Set.mem_univ _
      rw [← hs.add_eq] at hmem
      obtain ⟨c, hc, h, hh, hsum⟩ := Set.mem_add.mp hmem
      refine ⟨⟨c, hc⟩, (h : 𝔸f), ?_, ?_⟩
      · exact AddSubgroup.mem_addSubgroupOf.mp hh
      · exact congrArg Subtype.val hsum
    · rintro ⟨c, a, ha, rfl⟩
      exact B.add_mem (c : B).2 (hAB ha)
  have hdisj : Pairwise fun c c' : s => Disjoint (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) (((c' : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := by
    intro c c' hcc'
    have hd : Disjoint ((c : B) +ᵥ (H : Set B)) ((c' : B) +ᵥ (H : Set B)) :=
      hs.pairwiseDisjoint_vadd c.2 c'.2 (fun h => hcc' (Subtype.ext h))
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨a', ha', rfl⟩ heq
    have haB : a ∈ B := hAB ha
    have ha'B : a' ∈ B := hAB ha'
    refine hd.ne_of_mem (Set.mem_vadd_set.mpr ⟨⟨a, haB⟩, AddSubgroup.mem_addSubgroupOf.mpr ha, rfl⟩)
      (Set.mem_vadd_set.mpr ⟨⟨a', ha'B⟩, AddSubgroup.mem_addSubgroupOf.mpr ha', rfl⟩) ?_
    exact Subtype.ext heq

  have hslab : slab F S B = ⋃ c : s, slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f)) := by
    ext x; simp only [mem_slab, hcover, Set.mem_iUnion]; exact ⟨fun ⟨h1, c, h2⟩ => ⟨c, h1, h2⟩, fun ⟨c, h1, h2⟩ => ⟨h1, c, h2⟩⟩
  have hmeasA : MeasurableSet (slab F S (A : Set 𝔸f)) := (isClosed_slab F hS hA).measurableSet
  have hmeas : ∀ c : s, MeasurableSet (slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) := fun c => by
    rw [← vadd_slab]; exact hmeasA.const_vadd _
  have hdisj' : Pairwise fun c c' : s => Disjoint (slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) (slab F S (((c' : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) := by
    intro c c' hcc'
    rw [Set.disjoint_iff_forall_ne]
    rintro x ⟨-, hx⟩ x' ⟨-, hx'⟩ rfl
    exact Set.disjoint_iff_forall_ne.mp (hdisj hcc') hx hx' rfl
  have hconst : ∀ c : s, μ (slab F S (((c : B) : 𝔸f) +ᵥ (A : Set 𝔸f))) = μ (slab F S A) := fun c => by
    rw [← vadd_slab, measure_vadd]
  rw [hslab, measure_iUnion hdisj' hmeas, tsum_congr hconst]
  haveI := Fintype.ofFinite s
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]

end Coset

section ModFin

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸∞" => InfiniteAdeleRing F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

-- pin: intLattice (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:782)
def intLattice : AddSubgroup 𝔸f where
  carrier := integralFiniteAdeles (𝓞 F) F
  zero_mem' := fun _ => zero_mem _
  add_mem' hx hy := fun v => add_mem (hx v) (hy v)
  neg_mem' hx := fun v => neg_mem (hx v)

-- pin: coe_intLattice (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:788)
@[scoped simp] theorem coe_intLattice : (intLattice F : Set 𝔸f) = integralFiniteAdeles (𝓞 F) F := rfl

-- pin: dilate (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:790)
def dilate (y : (𝔸f)ˣ) : AddSubgroup 𝔸f := (intLattice F).map (DistribSMul.toAddMonoidHom 𝔸f (y : 𝔸f))

-- pin: coe_dilate (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:792)
theorem coe_dilate (y : (𝔸f)ˣ) : (dilate F y : Set 𝔸f) = (y : 𝔸f) • integralFiniteAdeles (𝓞 F) F := by
  ext z; simp [dilate, Set.mem_smul_set]

-- pin: finIdele (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:795)
def finIdele (y : (𝔸f)ˣ) : (𝔸)ˣ where
  val := toAdele F 1 (y : 𝔸f)
  inv := toAdele F 1 ((y⁻¹ : (𝔸f)ˣ) : 𝔸f)
  val_inv := Prod.ext (show (1 : 𝔸∞) * 1 = 1 from one_mul 1) (show (y : 𝔸f) * ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) = 1 from Units.mul_inv y)
  inv_val := Prod.ext (show (1 : 𝔸∞) * 1 = 1 from one_mul 1) (show ((y⁻¹ : (𝔸f)ˣ) : 𝔸f) * (y : 𝔸f) = 1 from Units.inv_mul y)

-- pin: finIdele_smul_slab (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:801)
theorem finIdele_smul_slab (y : (𝔸f)ˣ) (S : Set 𝔸∞) (T : Set 𝔸f) :
    finIdele F y • slab F S T = slab F S ((y : 𝔸f) • T) := by
  ext x
  simp only [Set.mem_smul_set, mem_slab]
  constructor
  · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
    have h1 : (finIdele F y • z).1 = z.1 := show (1 : 𝔸∞) * z.1 = z.1 from one_mul _
    have h2 : (finIdele F y • z).2 = (y : 𝔸f) * z.2 := rfl
    rw [h1, h2]
    exact ⟨hz1, z.2, hz2, rfl⟩
  · rintro ⟨hx1, ⟨t, ht, hxt⟩⟩
    refine ⟨toAdele F x.1 t, ⟨hx1, ht⟩, Prod.ext ?_ ?_⟩
    · show (1 : 𝔸∞) * x.1 = x.1
      rw [one_mul]
    · show (y : 𝔸f) * t = x.2
      exact hxt

-- the pin's `haveI` is load-bearing: it feeds the instance searches below.
set_option linter.style.haveILetI false in
-- pin: distribHaarChar_finIdele (S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:818)
theorem distribHaarChar_finIdele (y : (𝔸f)ˣ) (hy : intLattice F ≤ dilate F y) (hfin : (intLattice F).relIndex (dilate F y) ≠ 0) :
    (distribHaarChar 𝔸 (finIdele F y) : ℝ≥0∞) = (intLattice F).relIndex (dilate F y) := by

  obtain ⟨S, hScpt, hSnhds⟩ := exists_compact_mem_nhds (0 : 𝔸∞)
  have hSclosed : IsClosed S := hScpt.isClosed
  have hZclosed : IsClosed (integralFiniteAdeles (𝓞 F) F) := isClosed_integralFiniteAdeles F
  have hZopen : IsOpen (integralFiniteAdeles (𝓞 F) F) := isOpen_integralFiniteAdeles F
  have hZcpt : IsCompact (integralFiniteAdeles (𝓞 F) F) := isCompact_integralFiniteAdeles F
  set μ : Measure 𝔸 := adelicAddHaar (𝓞 F) F
  have hpos : 0 < μ (slab F S (integralFiniteAdeles (𝓞 F) F)) := by
    have hU : IsOpen (slab F (interior S) (integralFiniteAdeles (𝓞 F) F)) :=
      (isOpen_interior.preimage continuous_fst).inter (hZopen.preimage continuous_snd)
    have hne : (slab F (interior S) (integralFiniteAdeles (𝓞 F) F)).Nonempty :=
      ⟨((0 : 𝔸∞), (0 : 𝔸f)), mem_interior_iff_mem_nhds.mpr hSnhds, (intLattice F).zero_mem⟩
    exact (hU.measure_pos μ hne).trans_le (measure_mono fun x ⟨h1, h2⟩ => ⟨interior_subset h1, h2⟩)
  have hlt : μ (slab F S (integralFiniteAdeles (𝓞 F) F)) < ∞ := by
    have hc : IsCompact (slab F S (integralFiniteAdeles (𝓞 F) F)) := by
      have : slab F S (integralFiniteAdeles (𝓞 F) F) = (fun p : 𝔸∞ × 𝔸f => (p : 𝔸)) '' (S ×ˢ integralFiniteAdeles (𝓞 F) F) := by
        ext x; simp only [mem_slab]
        exact ⟨fun ⟨h1, h2⟩ => ⟨(x.1, x.2), ⟨h1, h2⟩, rfl⟩, by rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩⟩
      rw [this]
      exact (hScpt.prod hZcpt).image continuous_id
    exact hc.measure_lt_top

  haveI : μ.Regular := by
    show (adelicAddHaar (𝓞 F) F).Regular
    unfold adelicAddHaar
    infer_instance
  have h := distribHaarChar_mul μ (finIdele F y) (slab F S (integralFiniteAdeles (𝓞 F) F))
  rw [finIdele_smul_slab, ← coe_dilate, ← coe_intLattice,
    measure_slab_eq_relIndex_mul F μ hSclosed (intLattice F) (dilate F y) hy hZclosed hfin] at h
  exact (ENNReal.mul_left_inj hpos.ne' hlt.ne).mp h

end ModFin

end WeylIntegrable

end AutomorphicForm

end
