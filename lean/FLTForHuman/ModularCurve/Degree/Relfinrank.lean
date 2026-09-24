/-
  m7 (second half) — the Laurent/`coeffEmb` glue's relative-degree theorem:
  `relfinrank_laurentBaseChange`.

  This is the pin's `TransportDev`/`TransportRows` block
  (`P2M/Sol/S_ModularCurve_relfinrank_laurentBaseChange.lean`, 265 content lines)
  transcribed with every helper `private` (the pin keeps them out of the exported
  surface the same way, through its local `W1`/`TransportDev` namespaces).

  The pin also defines `relfinrank_laurentBaseChange_full`,
  `relfinrank_restrictScalars` and `relfinrank_full_prime` in the same file;
  `relfinrank_full_prime` is **not** an M4 node and needs m5's
  `finrank_adjoin_jqNModC_eq_of_prime`, so all three are omitted. The target's
  proof goes through `relfinrank_eq` alone, exactly as the pin's `solution` does.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relfinrank_laurentBaseChange.lean
-/
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.GeometricBaseChange
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.PhiSlotRoots
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct
import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.AlgebraTower
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

set_option autoImplicit false

noncomputable section

open Module IntermediateField Polynomial

namespace ModularCurve

namespace TransportDev

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (t : LaurentSeries ℚ)

private abbrev K₀ : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ ({t} : Set (LaurentSeries ℚ))

private abbrev K : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L ({coeffEmb L t} : Set (LaurentSeries L))

variable {F₀ t}

private theorem K₀_le (ht : t ∈ F₀) : K₀ t ≤ F₀ :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ht)

private theorem K_le (ht : t ∈ F₀) : K L t ≤ laurentBaseChange L F₀ :=
  adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (coeffEmb_mem_laurentBaseChange L ht))

private theorem coeffEmb_aeval (r : ℚ[X]) :
    coeffEmb L (aeval t r) = aeval (coeffEmb L t) (r.map (algebraMap ℚ L)) := by
  simp only [aeval_def, eval₂_map, hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

private theorem coeffEmb_mem_K {x : LaurentSeries ℚ} (hx : x ∈ K₀ t) :
    coeffEmb L x ∈ K L t := by
  rw [mem_adjoin_simple_iff] at hx ⊢
  obtain ⟨r, s, rfl⟩ := hx
  exact ⟨r.map (algebraMap ℚ L), s.map (algebraMap ℚ L),
    by rw [map_div₀, coeffEmb_aeval, coeffEmb_aeval]⟩

variable (F₀ t) in

private abbrev E₀ (ht : t ∈ F₀) : IntermediateField (K₀ t) (LaurentSeries ℚ) :=
  extendScalars (K₀_le ht)

variable (F₀ t) in

private abbrev E (ht : t ∈ F₀) : IntermediateField (K L t) (LaurentSeries L) :=
  extendScalars (K_le L ht)

private def φ : K₀ t →+* K L t :=
  (coeffEmb L).restrict _ _ fun _ hx => coeffEmb_mem_K L hx

private def ψ (ht : t ∈ F₀) : E₀ F₀ t ht →+* E L F₀ t ht :=
  (coeffEmb L).restrict _ _ fun _ hx => coeffEmb_mem_laurentBaseChange L ((mem_extendScalars _).mp hx)

private theorem coe_φ (x : K₀ t) : (φ L x : LaurentSeries L) = coeffEmb L x := rfl

private theorem coe_ψ (ht : t ∈ F₀) (x : E₀ F₀ t ht) :
    (ψ L ht x : LaurentSeries L) = coeffEmb L x := rfl

private theorem ψ_compat (ht : t ∈ F₀) :
    (algebraMap (K L t) (E L F₀ t ht)).comp (φ L) =
      (ψ L ht).comp (algebraMap (K₀ t) (E₀ F₀ t ht)) := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  rfl

private theorem isAlgebraic_coeffEmb (ht : t ∈ F₀) [FiniteDimensional (K₀ t) (E₀ F₀ t ht)]
    (f : LaurentSeries ℚ) (hf : f ∈ F₀) :
    IsAlgebraic (K L t) (coeffEmb L f) := by
  have : Algebra.IsIntegral (K₀ t) (E₀ F₀ t ht) := Algebra.IsIntegral.of_finite _ _
  have h1 : IsIntegral (K₀ t) (⟨f, (mem_extendScalars _).mpr hf⟩ : E₀ F₀ t ht) :=
    Algebra.IsIntegral.isIntegral _
  have h2 := h1.map_of_comp_eq (φ L) (ψ L ht) (ψ_compat L ht)
  have h3 : IsIntegral (K L t)
      ((ψ L ht ⟨f, (mem_extendScalars _).mpr hf⟩ : E L F₀ t ht) : LaurentSeries L) :=
    h2.algebraMap
  exact h3.isAlgebraic

private theorem laurentBaseChange_eq_adjoin :
    laurentBaseChange L F₀ =
      IntermediateField.adjoin L (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) := rfl

private theorem restrictScalars_adjoin_K (ht : t ∈ F₀) :
    (IntermediateField.adjoin (K L t) (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)))).restrictScalars L
      = laurentBaseChange L F₀ := by
  have h1 : IntermediateField.adjoin (K L t)
      (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) ≤ E L F₀ t ht :=
    adjoin_le_iff.mpr (subset_adjoin L _)
  have h2 : laurentBaseChange L F₀ ≤
      (IntermediateField.adjoin (K L t)
        (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)))).restrictScalars L :=
    adjoin_le_iff.mpr (subset_adjoin (K L t) _)
  exact le_antisymm (fun x hx => h1 hx) h2

private theorem closure_image_eq :
    (Submonoid.closure (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) : Set (LaurentSeries L))
      = coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)) := by
  have : (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)))
      = ((F₀.toSubfield.map (coeffEmb L)).toSubmonoid : Set (LaurentSeries L)) := by
    ext x; simp
  rw [this, Submonoid.closure_eq]

section Finite

variable (ht : t ∈ F₀) [FiniteDimensional (K₀ t) (E₀ F₀ t ht)]
include ht

private theorem mem_span_image (x : LaurentSeries L) (hx : x ∈ laurentBaseChange L F₀) :
    x ∈ Submodule.span (K L t) (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) := by
  have hx' : x ∈ IntermediateField.adjoin (K L t)
      (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ))) := by
    rw [← mem_restrictScalars L, restrictScalars_adjoin_K L ht]; exact hx
  have halg : ∀ y ∈ coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)), IsAlgebraic (K L t) y := by
    rintro _ ⟨f, hf, rfl⟩; exact isAlgebraic_coeffEmb L ht f hf
  rw [← mem_toSubalgebra, adjoin_toSubalgebra_of_isAlgebraic halg] at hx'
  have hx'' : x ∈ Subalgebra.toSubmodule
      (Algebra.adjoin (K L t) (coeffEmb L '' (F₀ : Set (LaurentSeries ℚ)))) := hx'
  rw [Algebra.adjoin_eq_span] at hx''
  rwa [closure_image_eq] at hx''

private theorem mem_span_range {ι : Type*} (b : Module.Basis ι (K₀ t) (E₀ F₀ t ht))
    (x : LaurentSeries L) (hx : x ∈ laurentBaseChange L F₀) :
    x ∈ Submodule.span (K L t)
      (Set.range fun i => ((ψ L ht (b i) : E L F₀ t ht) : LaurentSeries L)) := by
  refine Submodule.span_le.mpr ?_ (mem_span_image L ht x hx)
  rintro _ ⟨f, hf, rfl⟩
  have hrepr := b.linearCombination_repr ⟨f, (mem_extendScalars _).mpr hf⟩
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hrepr
  have : coeffEmb L f = ∑ i ∈ (b.repr ⟨f, (mem_extendScalars _).mpr hf⟩).support,
      (φ L (b.repr ⟨f, (mem_extendScalars _).mpr hf⟩ i)) •
        ((ψ L ht (b i) : E L F₀ t ht) : LaurentSeries L) := by
    have h2 := congrArg (fun z : E₀ F₀ t ht => coeffEmb L (z : LaurentSeries ℚ)) hrepr
    dsimp only at h2
    rw [← h2, AddSubmonoidClass.coe_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [IntermediateField.coe_smul, Algebra.smul_def, map_mul, Algebra.smul_def]
    rfl
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem finite_and_finrank_le :
    Module.Finite (K L t) (E L F₀ t ht) ∧
      Module.finrank (K L t) (E L F₀ t ht) ≤ Module.finrank (K₀ t) (E₀ F₀ t ht) := by
  classical
  let b := Module.Free.chooseBasis (K₀ t) (E₀ F₀ t ht)
  let y : Module.Free.ChooseBasisIndex (K₀ t) (E₀ F₀ t ht) → E L F₀ t ht :=
    fun i => ψ L ht (b i)
  have htop : ∀ x : E L F₀ t ht, x ∈ Submodule.span (K L t) (Set.range y) := fun x => by
    have hx := mem_span_range L ht b (x : LaurentSeries L) ((mem_extendScalars _).mp x.2)
    have hr : (Set.range fun i => ((ψ L ht (b i) : E L F₀ t ht) : LaurentSeries L))
        = (E L F₀ t ht).val.toLinearMap '' (Set.range y) := by
      rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image] at hx
    obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp hx
    have hzx' : z = x := Subtype.ext hzx
    exact hzx' ▸ hz
  have hspan : Submodule.span (K L t) (Set.range y) = ⊤ := eq_top_iff.mpr fun x _ => htop x
  have hfin : Module.Finite (K L t) (E L F₀ t ht) :=
    ⟨by rw [← hspan]; exact Submodule.fg_span (Set.finite_range y)⟩
  refine ⟨hfin, ?_⟩
  conv_rhs => rw [Module.finrank_eq_card_chooseBasisIndex]
  conv_lhs => rw [← finrank_top, ← hspan]
  calc Module.finrank (K L t) (Submodule.span (K L t) (Set.range y))
        ≤ (Set.range y).toFinset.card := finrank_span_le_card _
    _ ≤ Fintype.card (Module.Free.ChooseBasisIndex (K₀ t) (E₀ F₀ t ht)) := by
        rw [Set.toFinset_range]; exact Finset.card_image_le.trans (by rw [Finset.card_univ])

end Finite

private theorem linearIndependent_pow_mul (ht : t ∈ F₀) (htr : Transcendental ℚ t) {ι : Type*}
    {v : ι → E₀ F₀ t ht} (hv : LinearIndependent (K₀ t) v) :
    LinearIndependent ℚ fun p : ℕ × ι => t ^ p.1 * ((v p.2 : E₀ F₀ t ht) : LaurentSeries ℚ) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro S μ hS p hp
  let c : ι → LaurentSeries ℚ := fun i =>
    ∑ q ∈ S, if q.2 = i then algebraMap ℚ (LaurentSeries ℚ) (μ q) * t ^ q.1 else 0
  have hcmem : ∀ i, c i ∈ K₀ t := fun i => by
    refine sum_mem fun q _ => ?_
    split_ifs
    · exact mul_mem ((K₀ t).algebraMap_mem _) (pow_mem (mem_adjoin_simple_self ℚ t) _)
    · exact zero_mem _
  have hrel : ∑ i ∈ S.image Prod.snd, (⟨c i, hcmem i⟩ : K₀ t) • v i = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
    have h1 : ∀ i, ((((⟨c i, hcmem i⟩ : K₀ t) • v i : E₀ F₀ t ht)) : LaurentSeries ℚ)
        = ∑ q ∈ S, if q.2 = i then
            algebraMap ℚ (LaurentSeries ℚ) (μ q) * t ^ q.1 * ((v i : E₀ F₀ t ht) : LaurentSeries ℚ) else 0 := by
      intro i
      show c i * ((v i : E₀ F₀ t ht) : LaurentSeries ℚ) = _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun q _ => by by_cases h : q.2 = i <;> simp [h]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun q hq => ?_) hS
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_image_of_mem Prod.snd hq),
      ← HahnSeries.single_zero_mul_eq_smul, algebraMap_laurentSeries_eq_single, mul_assoc]
  have hci : (⟨c p.2, hcmem p.2⟩ : K₀ t) = 0 :=
    hv _ _ hrel p.2 (Finset.mem_image_of_mem Prod.snd hp)
  have hc0 : c p.2 = 0 := congrArg Subtype.val hci
  have hQ : aeval t (∑ q ∈ S, if q.2 = p.2 then monomial q.1 (μ q) else 0) = 0 := by
    rw [map_sum, ← hc0]
    exact Finset.sum_congr rfl fun q _ => by by_cases h : q.2 = p.2 <;> simp [h, aeval_monomial]
  have hQ0 : (∑ q ∈ S, if q.2 = p.2 then monomial q.1 (μ q) else 0 : ℚ[X]) = 0 :=
    transcendental_iff_injective.mp htr (by rw [map_zero]; exact hQ)
  have hco := congrArg (fun P : ℚ[X] => P.coeff p.1) hQ0
  beta_reduce at hco
  rw [finsetSum_coeff, coeff_zero, Finset.sum_eq_single p] at hco
  · simpa using hco
  · intro q _ hqp
    by_cases h2 : q.2 = p.2
    · rw [ite_eq_left h2, coeff_monomial, ite_eq_right]
      intro h1
      exact hqp (Prod.ext h1 h2)
    · rw [ite_eq_right h2, coeff_zero]
  · intro hpS
    exact absurd hp hpS

private theorem exists_common_denom {ι : Type*} (s : Finset ι) (g : ι → K L t) :
    ∃ d : L[X], aeval (coeffEmb L t) d ≠ 0 ∧
      ∀ i ∈ s, ∃ p : L[X], aeval (coeffEmb L t) d * (g i : LaurentSeries L) = aeval (coeffEmb L t) p := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a s has ih =>
    obtain ⟨d, hd, hs⟩ := ih
    obtain ⟨r, q, hrq⟩ := (mem_adjoin_simple_iff L _).mp (g a).2
    by_cases hq : aeval (coeffEmb L t) q = 0
    · refine ⟨d, hd, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨0, by rw [hrq, hq, div_zero, mul_zero, map_zero]⟩
      · exact hs i hi
    · refine ⟨d * q, by rw [map_mul]; exact mul_ne_zero hd hq, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · refine ⟨d * r, ?_⟩
        rw [hrq, map_mul, map_mul, mul_assoc, mul_div_cancel₀ _ hq]
      · obtain ⟨p, hp⟩ := hs i hi
        exact ⟨p * q, by rw [map_mul, map_mul, mul_right_comm, hp]⟩

private theorem linearIndependent_ψ (ht : t ∈ F₀) (htr : Transcendental ℚ t) {ι : Type*} [Fintype ι]
    {v : ι → E₀ F₀ t ht} (hv : LinearIndependent (K₀ t) v) :
    LinearIndependent (K L t) fun i => ψ L ht (v i) := by
  classical
  have hw := linearIndependent_coeffEmb L (linearIndependent_pow_mul ht htr hv)
  rw [linearIndependent_iff'] at hw ⊢
  intro s g hg i hi
  obtain ⟨d, hd, hs⟩ := exists_common_denom L Finset.univ g
  choose! P hP using hs

  have hg' : ∑ j ∈ s, aeval (coeffEmb L t) (P j) *
      coeffEmb L ((v j : E₀ F₀ t ht) : LaurentSeries ℚ) = 0 := by
    have := congrArg (fun z : E L F₀ t ht => aeval (coeffEmb L t) d * (z : LaurentSeries L)) hg
    beta_reduce at this
    rw [ZeroMemClass.coe_zero, mul_zero, AddSubmonoidClass.coe_finsetSum, Finset.mul_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IntermediateField.coe_smul]
    show _ = aeval (coeffEmb L t) d * (((g j : K L t) : LaurentSeries L) *
      ((ψ L ht (v j) : E L F₀ t ht) : LaurentSeries L))
    rw [← mul_assoc, hP j (Finset.mem_univ j)]
    rfl

  let n : ℕ := (s.sup fun j => (P j).natDegree) + 1
  have hdeg : ∀ j ∈ s, (P j).natDegree < n := fun j hj =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (P j).natDegree) hj)
  have hrel : ∑ p ∈ (Finset.range n) ×ˢ s,
      (P p.2).coeff p.1 • coeffEmb L (t ^ p.1 * ((v p.2 : E₀ F₀ t ht) : LaurentSeries ℚ)) = 0 := by
    rw [Finset.sum_product_right, ← hg']
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [aeval_eq_sum_range' (hdeg j hj), Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← HahnSeries.single_zero_mul_eq_smul, map_mul, map_pow, Algebra.smul_def,
      algebraMap_laurentSeries_eq_single, mul_assoc]
  have hcoeff : ∀ j ∈ s, ∀ k ∈ Finset.range n, (P j).coeff k = 0 := fun j hj k hk =>
    hw ((Finset.range n) ×ˢ s) (fun p => (P p.2).coeff p.1) hrel (k, j)
      (Finset.mem_product.mpr ⟨hk, hj⟩)
  have hP0 : P i = 0 := by
    ext k
    by_cases hk : k < n
    · rw [hcoeff i hi k (Finset.mem_range.mpr hk), coeff_zero]
    · rw [coeff_zero, coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i hi) (not_lt.mp hk))]
  have h3 : aeval (coeffEmb L t) d * (g i : LaurentSeries L) = 0 := by
    rw [hP i (Finset.mem_univ i), hP0, map_zero]
  exact Subtype.ext ((mul_eq_zero.mp h3).resolve_left hd)

private theorem relfinrank_eq (ht : t ∈ F₀) (htr : Transcendental ℚ t) :
    relfinrank (K L t) (laurentBaseChange L F₀) = relfinrank (K₀ t) F₀ := by
  classical
  rw [relfinrank_eq_finrank_of_le (K_le L ht), relfinrank_eq_finrank_of_le (K₀_le ht)]
  change Module.finrank (K L t) (E L F₀ t ht) = Module.finrank (K₀ t) (E₀ F₀ t ht)
  have : Module.Free (K₀ t) (E₀ F₀ t ht) := Module.Free.of_divisionRing (K₀ t) (E₀ F₀ t ht)
  by_cases hfin : FiniteDimensional (K₀ t) (E₀ F₀ t ht)
  · obtain ⟨hfinE, hle⟩ := finite_and_finrank_le L ht
    have := hfinE
    refine le_antisymm hle ?_
    let b := Module.Free.chooseBasis (K₀ t) (E₀ F₀ t ht)
    have hind := linearIndependent_ψ L ht htr b.linearIndependent
    rw [Module.finrank_eq_card_chooseBasisIndex]
    exact hind.fintype_card_le_finrank
  · rw [Module.finrank_of_not_finite hfin]
    by_contra hE
    have hE' : 0 < Module.finrank (K L t) (E L F₀ t ht) := Nat.pos_of_ne_zero hE
    have : Module.Free (K L t) (E L F₀ t ht) :=
      Module.Free.of_divisionRing (K L t) (E L F₀ t ht)
    have : Module.Finite (K L t) (E L F₀ t ht) := Module.finite_of_finrank_pos hE'
    apply hfin
    have hrank : Module.rank (K₀ t) (E₀ F₀ t ht) ≤ Module.finrank (K L t) (E L F₀ t ht) := by
      refine _root_.rank_le fun s hs => ?_
      have hind := linearIndependent_ψ L ht htr hs
      simpa using hind.fintype_card_le_finrank
    exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0))

end TransportDev

theorem relfinrank_laurentBaseChange (L : Type*) [Field L] [Algebra ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (t : LaurentSeries ℚ) (ht : t ∈ F₀)
    (htr : Transcendental ℚ t) :
    IntermediateField.relfinrank (IntermediateField.adjoin L ({coeffEmb L t} : Set (LaurentSeries L)))
        (laurentBaseChange L F₀)
      = IntermediateField.relfinrank
        (IntermediateField.adjoin ℚ ({t} : Set (LaurentSeries ℚ))) F₀ :=
  TransportDev.relfinrank_eq L ht htr

/-! ## `relfinrank_qExpand_full` — the relative degree of `q ↦ q ^ ℓ`

The pin's file carries the ~370-raw-line `TS`/`conj`/`phiAtSeed`/
`roots_prime_at_slot` prelude at its head; all of it is published by the port in
`Defs/{TS,PhiAtSlot,Twist,Cyclotomic}.lean`, `PhiSlotRoots.lean` and
`PhiGenSplits.lean`, and is imported, never rewritten. The genuinely new block is
the `g2_*` glue and the two `finrank_adjoin_jq_of_subset_range_qExpand` heads
below. `jqN_congr` is public in `Defs/Jq.lean`; `phiAtSeed_eval_symm` in
`Defs/PhiAtSlot.lean`; `coeffEmb_injective` in `Defs/Laurent.lean`.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relfinrank_qExpand_full.lean -/

section RelfinrankQExpandFull

private theorem g2_relfinrank_union_left (E : IntermediateField ℚ (LaurentSeries ℚ))
    (α : LaurentSeries ℚ) :
    IntermediateField.relfinrank E
      (IntermediateField.adjoin ℚ ((E : Set (LaurentSeries ℚ)) ∪ {α}))
      = Module.finrank E (IntermediateField.adjoin E ({α} : Set (LaurentSeries ℚ))) := by
  have h : E ≤ IntermediateField.adjoin ℚ ((E : Set (LaurentSeries ℚ)) ∪ {α}) := by
    intro x hx
    exact IntermediateField.subset_adjoin _ _ (Set.mem_union_left _ hx)
  have hEq : IntermediateField.adjoin E ((E : Set (LaurentSeries ℚ)) ∪ {α})
      = IntermediateField.adjoin E ({α} : Set (LaurentSeries ℚ)) := by
    refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | rfl)
      · exact (IntermediateField.adjoin E ({α} : Set (LaurentSeries ℚ))).algebraMap_mem ⟨x, hx⟩
      · exact IntermediateField.subset_adjoin _ _ rfl
    · exact IntermediateField.adjoin.mono _ _ _ Set.subset_union_right
  rw [IntermediateField.relfinrank_eq_finrank_of_le h, IntermediateField.extendScalars_adjoin h,
    hEq]

section g2core

variable {K : Type*} [Field K] [Algebra ℚ K]

variable (ℓ : ℕ) [hl : Fact (Nat.Prime ℓ)]

private theorem g2_zeta_mod (a : ℕ) :
    (cycUnit ℓ) ^ a = (cycUnit ℓ) ^ (a % ℓ) := by
  conv_lhs => rw [← Nat.div_add_mod a ℓ]
  rw [pow_add, pow_mul, cycUnit_pow, one_pow, one_mul]

private theorem g2_seed_eq :
    coeffEmb (CyclotomicField ℓ ℚ) (jqN ℓ)
      = qExpand (CyclotomicField ℓ ℚ) (ℓ * 1)
          (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ ℓ) (coeffEmb (CyclotomicField ℓ ℚ) jq)) := by
  rw [jqN, coeffEmb_qExpand, one_pow, qTwist_one_apply]
  exact qExpand_congr (mul_one ℓ).symm _

private theorem g2_y0_eq :
    coeffEmb (CyclotomicField ℓ ℚ) (jqN (ℓ * ℓ))
      = qExpand (CyclotomicField ℓ ℚ) (ℓ * (ℓ * 1))
          (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ (ℓ * ℓ))
            (coeffEmb (CyclotomicField ℓ ℚ) jq)) := by
  rw [jqN, coeffEmb_qExpand, one_pow, qTwist_one_apply]
  exact qExpand_congr (by ring) _

private theorem g2_twist_fix (x : LaurentSeries ℚ) :
    qTwist (cycUnit ℓ) (coeffEmb (CyclotomicField ℓ ℚ) (qExpand ℚ ℓ x))
      = coeffEmb (CyclotomicField ℓ ℚ) (qExpand ℚ ℓ x) := by
  rw [coeffEmb_qExpand, qTwist_qExpand, zpow_natCast, cycUnit_pow, qTwist_one_apply]

end g2core

private theorem finrank_adjoin_jq_of_subset_range_qExpand
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (ℓ : ℕ) [hl : Fact (Nat.Prime ℓ)]
    (hF : (F : Set (LaurentSeries ℚ)) ⊆ Set.range (qExpand ℚ ℓ)) (hmem : jqN ℓ ∈ F)
    (hnot : jqN (ℓ * ℓ) ∉ F) :
    Module.finrank F (IntermediateField.adjoin F ({jq} : Set (LaurentSeries ℚ))) = ℓ + 1 := by
  classical
  obtain ⟨data, -, hs⟩ := exists_phiIrreducible_evalSymm ℓ
  set jlF : F := ⟨jqN ℓ, hmem⟩ with hjlF
  set Q : Polynomial F := phiAtSeed data jlF with hQdef
  have hQmonic : Q.Monic := phiAtSeed_monic data jlF
  have hQdeg : Q.natDegree = ℓ + 1 := by
    rw [hQdef, phiAtSeed_natDegree, dedekindPsi_prime hl.out]
  have hQmap : Q.map (algebraMap F (LaurentSeries ℚ)) = phiAtSeed data (jqN ℓ) := by
    rw [hQdef, phiAtSeed_map]; rfl
  have h1ℓ : jqN (1 : ℕ) = jq := by
    rw [jqN]; exact qExpand_one_apply jq
  have hbase : (phiAtSeed data (jqN ℓ)).eval jq = 0 := by
    rw [phiAtSeed_eval_symm data hs]
    have h := phiAtSeed_jqN_eval ℓ data 1
    rwa [jqN_congr (one_mul ℓ), h1ℓ] at h
  have hQjq : Polynomial.aeval jq Q = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hQmap]
    exact hbase
  have hint : IsIntegral F jq := ⟨Q, hQmonic, by rwa [Polynomial.aeval_def] at hQjq⟩

  let : Algebra F (LaurentSeries (CyclotomicField ℓ ℚ)) :=
    ((coeffEmb (CyclotomicField ℓ ℚ)).comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
  have halg : ∀ a : F, algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a
      = coeffEmb (CyclotomicField ℓ ℚ) (a : LaurentSeries ℚ) := fun a => rfl
  have hQmapL : Q.map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))
      = phiAtSeed data (qExpand (CyclotomicField ℓ ℚ) (ℓ * 1)
          (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ ℓ) (coeffEmb (CyclotomicField ℓ ℚ) jq))) := by
    rw [RingHom.algebraMap_toAlgebra, ← Polynomial.map_map, hQmap, phiAtSeed_map, g2_seed_eq]
  have hQroots : (Q.map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots
      = (qExpand (CyclotomicField ℓ ℚ) (ℓ * (ℓ * 1))
          (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ (ℓ * ℓ)) (coeffEmb (CyclotomicField ℓ ℚ) jq)))
        ::ₘ (Multiset.range ℓ).map
          (fun c => qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq)) := by
    rw [hQmapL, phiAtSeed,
      roots_prime_at_slot ℓ (cycUnit ℓ) (cycUnit_spec ℓ) ℓ (dvd_refl ℓ) data 1 1]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    rw [Nat.div_self hl.out.pos, mul_one, one_mul, qExpand_one_apply]
  have hQnodup : (Q.map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots.Nodup := by
    rw [hQmapL, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup ℓ (cycUnit ℓ) (cycUnit_spec ℓ) ℓ (dvd_refl ℓ) data 1 1
  have hQsplits : (Q.map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).Splits := by
    rw [Polynomial.splits_iff_card_roots, hQroots, Multiset.card_cons, Multiset.card_map,
      Multiset.card_range, hQmonic.natDegree_map, hQdeg]
  have hσfix : ∀ a : F,
      (qTwistEquiv (cycUnit ℓ)) (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a)
        = algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a := by
    intro a
    obtain ⟨x, hx⟩ := hF a.2
    rw [halg, ← hx, qTwistEquiv_apply, g2_twist_fix]
  have hcycle : ∀ i < ℓ,
      (qTwistEquiv (cycUnit ℓ)) (qTwist (cycUnit ℓ ^ i) (coeffEmb (CyclotomicField ℓ ℚ) jq))
        = qTwist (cycUnit ℓ ^ ((i + 1) % ℓ)) (coeffEmb (CyclotomicField ℓ ℚ) jq) := by
    intro i _
    rw [qTwistEquiv_apply, qTwist_qTwist, ← pow_succ', g2_zeta_mod ℓ (i + 1)]
  have hy₀ : (qExpand (CyclotomicField ℓ ℚ) (ℓ * (ℓ * 1))
      (qTwist ((1 : (CyclotomicField ℓ ℚ)ˣ) ^ (ℓ * ℓ)) (coeffEmb (CyclotomicField ℓ ℚ) jq)))
      ∉ (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ))).range := by
    rintro ⟨f, hf⟩
    rw [halg] at hf
    have hval : (f : LaurentSeries ℚ) = jqN (ℓ * ℓ) := by
      apply coeffEmb_injective (CyclotomicField ℓ ℚ)
      rw [hf, g2_y0_eq]
    exact hnot (hval ▸ f.2)
  have hirr : Irreducible Q :=
    Polynomial.irreducible_of_transitive_ringAut Q hQmonic hQsplits (qTwistEquiv (cycUnit ℓ))
      hσfix _ _ ℓ hQroots hQnodup hcycle hy₀
  have hmin : Q = minpoly F jq := minpoly.eq_of_irreducible_of_monic hirr hQjq hQmonic
  rw [IntermediateField.adjoin.finrank hint, ← hmin, hQdeg]

private theorem finrank_adjoin_jq_of_subset_range_qExpand_of_mem
    (F : IntermediateField ℚ (LaurentSeries ℚ)) (ℓ : ℕ) [hl : Fact (Nat.Prime ℓ)]
    (hF : (F : Set (LaurentSeries ℚ)) ⊆ Set.range (qExpand ℚ ℓ)) (hmem : jqN ℓ ∈ F)
    (hin : jqN (ℓ * ℓ) ∈ F) :
    Module.finrank F (IntermediateField.adjoin F ({jq} : Set (LaurentSeries ℚ))) = ℓ := by
  classical
  obtain ⟨data, -, hs⟩ := exists_phiIrreducible_evalSymm ℓ
  set jlF : F := ⟨jqN ℓ, hmem⟩ with hjlF
  set j2F : F := ⟨jqN (ℓ * ℓ), hin⟩ with hj2F
  set Q : Polynomial F := phiAtSeed data jlF with hQdef
  have hQmonic : Q.Monic := phiAtSeed_monic data jlF
  have hQdeg : Q.natDegree = ℓ + 1 := by
    rw [hQdef, phiAtSeed_natDegree, dedekindPsi_prime hl.out]
  have hQmap : Q.map (algebraMap F (LaurentSeries ℚ)) = phiAtSeed data (jqN ℓ) := by
    rw [hQdef, phiAtSeed_map]; rfl
  have h1ℓ : jqN (1 : ℕ) = jq := by
    rw [jqN]; exact qExpand_one_apply jq
  have hbase : (phiAtSeed data (jqN ℓ)).eval jq = 0 := by
    rw [phiAtSeed_eval_symm data hs]
    have h := phiAtSeed_jqN_eval ℓ data 1
    rwa [jqN_congr (one_mul ℓ), h1ℓ] at h
  have hQjq : Polynomial.aeval jq Q = 0 := by
    rw [← Polynomial.eval_map_algebraMap, hQmap]
    exact hbase
  have hint : IsIntegral F jq := ⟨Q, hQmonic, by rwa [Polynomial.aeval_def] at hQjq⟩

  have hQj2 : Q.IsRoot j2F := by
    have h0m : algebraMap F (LaurentSeries ℚ) (Q.eval j2F) = algebraMap F (LaurentSeries ℚ) 0 := by
      rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map, hQmap]
      exact phiAtSeed_jqN_eval ℓ data ℓ
    exact (algebraMap F (LaurentSeries ℚ)).injective h0m
  set P : Polynomial F := Q /ₘ (Polynomial.X - Polynomial.C j2F) with hPdef
  have hfact : (Polynomial.X - Polynomial.C j2F) * P = Q :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hQj2
  have hPmonic : P.Monic :=
    Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C j2F)
      (by rw [hfact]; exact hQmonic)
  have hPdeg : P.natDegree = ℓ := by
    have h := congrArg Polynomial.natDegree hfact
    rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C j2F) hPmonic,
      Polynomial.natDegree_X_sub_C, hQdeg] at h
    omega
  have hne : jq ≠ jqN (ℓ * ℓ) := by
    intro h
    have hA : jq.coeff (-1 : ℤ) = 1 := coeff_jq_neg_one
    have hB : (jqN (ℓ * ℓ)).coeff (-1 : ℤ) = 0 := by
      rw [jqN]
      refine qExpand_coeff_of_not_dvd (ℓ * ℓ) jq ?_
      intro hdvd
      have h4 : (4 : ℕ) ≤ ℓ * ℓ := Nat.mul_le_mul hl.out.two_le hl.out.two_le
      have h1 : ((ℓ * ℓ : ℕ) : ℤ) ∣ 1 := dvd_neg.mp hdvd
      have h2 : ((ℓ * ℓ : ℕ) : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
      have h3 : (4 : ℤ) ≤ ((ℓ * ℓ : ℕ) : ℤ) := by exact_mod_cast h4
      linarith
    rw [h, hB] at hA
    exact zero_ne_one hA
  have hProot : Polynomial.aeval jq P = 0 := by
    have h : Polynomial.aeval jq ((Polynomial.X - Polynomial.C j2F) * P) = 0 := by
      rw [hfact]; exact hQjq
    rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
    rcases mul_eq_zero.mp h with h1' | h2'
    · exact absurd (sub_eq_zero.mp h1') hne
    · exact h2'
  have hdvd : minpoly F jq ∣ P := minpoly.dvd F jq hProot

  let : Algebra F (LaurentSeries (CyclotomicField ℓ ℚ)) :=
    ((coeffEmb (CyclotomicField ℓ ℚ)).comp (algebraMap F (LaurentSeries ℚ))).toAlgebra
  have halg : ∀ a : F, algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a
      = coeffEmb (CyclotomicField ℓ ℚ) (a : LaurentSeries ℚ) := fun a => rfl
  have hσfixR : ∀ a : F,
      qTwist (cycUnit ℓ) (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a)
        = algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)) a := by
    intro a
    obtain ⟨x, hx⟩ := hF a.2
    rw [halg, ← hx, g2_twist_fix]

  have hW0 : (minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ))) ≠ 0 :=
    ((minpoly.monic hint).map _).ne_zero
  have hWdeg : ((minpoly F jq).map
      (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).natDegree
      = (minpoly F jq).natDegree := (minpoly.monic hint).natDegree_map _
  have hWfix : ((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).map
      (qTwist (cycUnit ℓ)) = (minpoly F jq).map
        (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ))) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext hσfixR
  have hstab : ∀ y : LaurentSeries (CyclotomicField ℓ ℚ),
      ((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval y = 0 →
      ((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval
        (qTwist (cycUnit ℓ) y) = 0 := by
    intro y hy
    have h2 : (((minpoly F jq).map
        (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).map (qTwist (cycUnit ℓ))).eval
        (qTwist (cycUnit ℓ) y)
        = qTwist (cycUnit ℓ)
            (((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval y) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [hWfix] at h2
    rw [h2, hy, map_zero]
  have hkill0 : ((minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval
      (coeffEmb (CyclotomicField ℓ ℚ) jq) = 0 := by
    have hV : ((minpoly F jq).map (algebraMap F (LaurentSeries ℚ))).eval jq = 0 := by
      have h := minpoly.aeval F jq
      rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at h
    have hWV : (minpoly F jq).map (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))
        = ((minpoly F jq).map (algebraMap F (LaurentSeries ℚ))).map
            (coeffEmb (CyclotomicField ℓ ℚ)) := by
      rw [Polynomial.map_map]; rfl
    rw [hWV, Polynomial.eval_map, Polynomial.eval₂_hom, hV, map_zero]
  have horbit : ∀ c : ℕ, ((minpoly F jq).map
      (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).eval
        (qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq)) = 0 := by
    intro c
    induction c with
    | zero => rw [pow_zero, qTwist_one_apply]; exact hkill0
    | succ c ih =>
      have h := hstab _ ih
      rwa [qTwist_qTwist, ← pow_succ'] at h
  have hdist : Set.InjOn (fun c : ℕ => qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq))
      ↑(Finset.range ℓ) := by
    intro a ha b hb h
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    have hTS : TS (CyclotomicField ℓ ℚ) 1 (cycUnit ℓ ^ a)
        = TS (CyclotomicField ℓ ℚ) 1 (cycUnit ℓ ^ b) :=
      congrArg (qExpand (CyclotomicField ℓ ℚ) 1) h
    have hu : (cycUnit ℓ) ^ a = (cycUnit ℓ) ^ b := (TS_injective hTS).2
    have hval : ((cycUnit ℓ : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ^ a
        = ((cycUnit ℓ : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ^ b := by
      have h2 := congrArg Units.val hu
      rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h2
    exact (cycUnit_spec ℓ).pow_inj ha hb hval
  have hcard : ℓ ≤ (minpoly F jq).natDegree := by
    have hsub : (Finset.range ℓ).image
        (fun c => qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq))
        ⊆ ((minpoly F jq).map
            (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots.toFinset := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨c, -, rfl⟩ := hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots']
      exact ⟨hW0, horbit c⟩
    calc ℓ = ((Finset.range ℓ).image
          (fun c => qTwist (cycUnit ℓ ^ c) (coeffEmb (CyclotomicField ℓ ℚ) jq))).card := by
          rw [Finset.card_image_of_injOn hdist, Finset.card_range]
    _ ≤ ((minpoly F jq).map
          (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots.toFinset.card :=
        Finset.card_le_card hsub
    _ ≤ Multiset.card ((minpoly F jq).map
          (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).roots :=
        Multiset.toFinset_card_le _
    _ ≤ ((minpoly F jq).map
          (algebraMap F (LaurentSeries (CyclotomicField ℓ ℚ)))).natDegree :=
        Polynomial.card_roots' _
    _ = (minpoly F jq).natDegree := hWdeg
  have hle : (minpoly F jq).natDegree ≤ ℓ := by
    have h := Polynomial.natDegree_le_of_dvd hdvd hPmonic.ne_zero
    rwa [hPdeg] at h
  rw [IntermediateField.adjoin.finrank hint]
  exact le_antisymm hle hcard

theorem relfinrank_qExpand_full (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] :
    IntermediateField.relfinrank ((modularFunctionFieldFull N).map (qExpandₐ ℓ))
        (modularFunctionFieldFull (N * ℓ)) = if ℓ ∣ N then ℓ else ℓ + 1 := by
  classical
  have hFr : (((modularFunctionFieldFull N).map (qExpandₐ ℓ) :
      IntermediateField ℚ (LaurentSeries ℚ)) : Set (LaurentSeries ℚ))
      ⊆ Set.range (qExpand ℚ ℓ) := by
    rintro x hx
    rw [IntermediateField.coe_map] at hx
    obtain ⟨e, -, rfl⟩ := hx
    exact ⟨e, rfl⟩
  have hjqfull : jq ∈ modularFunctionFieldFull N := by
    have h := jqd_mem_full N (one_dvd N)
    rwa [qExpand_one_apply] at h
  have hmemF : jqN ℓ ∈ (modularFunctionFieldFull N).map (qExpandₐ ℓ) := by
    rw [IntermediateField.mem_map]
    exact ⟨jq, hjqfull, by rw [qExpandₐ_apply, jqN]⟩
  have hall : ∀ d : ℕ, d ∣ N → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
          ({jqN d} : Set (LaurentSeries ℚ))) = dedekindPsi d
      ∧ modularFunctionField d = modularFunctionFieldFull d := by
    intro d _ _
    exact ⟨finrank_adjoin_jqN_eq_dedekindPsi d, modularFunctionField_eq_full d⟩
  have hmulsq : qExpand ℚ ℓ (jqN ℓ) = jqN (ℓ * ℓ) := by
    rw [jqN, jqN, qExpand_qExpand]
  have hiff : jqN (ℓ * ℓ) ∈ (modularFunctionFieldFull N).map (qExpandₐ ℓ) ↔ ℓ ∣ N := by
    constructor
    · intro hin
      by_contra hnd
      rw [IntermediateField.mem_map] at hin
      obtain ⟨e, he, heq⟩ := hin
      rw [qExpandₐ_apply] at heq
      have he2 : e = jqN ℓ := by
        apply qExpand_injective ℓ
        rw [heq, ← hmulsq]
      rw [he2] at he
      exact jqN_prime_not_mem_full N ℓ hnd hall he
    · intro hdvdN
      rw [IntermediateField.mem_map]
      refine ⟨jqN ℓ, ?_, by rw [qExpandₐ_apply, hmulsq]⟩
      show qExpand ℚ ℓ jq ∈ modularFunctionFieldFull N
      exact jqd_mem_full N hdvdN
  have hgen : modularFunctionFieldFull (N * ℓ)
      = IntermediateField.adjoin ℚ
          ((((modularFunctionFieldFull N).map (qExpandₐ ℓ) :
            IntermediateField ℚ (LaurentSeries ℚ)) : Set (LaurentSeries ℚ)) ∪ {jq}) := by
    refine le_antisymm ?_ ?_
    · rw [← modularFunctionField_eq_full (N * ℓ), modularFunctionField,
        IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_union_right _ rfl)
      · refine IntermediateField.subset_adjoin _ _ (Set.mem_union_left _ ?_)
        show qExpand ℚ (N * ℓ) jq ∈ (modularFunctionFieldFull N).map (qExpandₐ ℓ)
        rw [IntermediateField.mem_map]
        refine ⟨jqN N, ?_, ?_⟩
        · show qExpand ℚ N jq ∈ modularFunctionFieldFull N
          exact jqd_mem_full N dvd_rfl
        · rw [qExpandₐ_apply, jqN, qExpand_qExpand]
          exact qExpand_congr (mul_comm ℓ N) jq
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (hx | rfl)
      · exact full_degeneracy_map_le N ℓ hx
      · have h := jqd_mem_full (N * ℓ) (one_dvd _)
        rwa [qExpand_one_apply] at h
  rw [hgen, g2_relfinrank_union_left]
  by_cases hd : ℓ ∣ N
  · rw [ite_eq_left hd]
    exact finrank_adjoin_jq_of_subset_range_qExpand_of_mem _ ℓ hFr hmemF (hiff.mpr hd)
  · rw [ite_eq_right hd]
    exact finrank_adjoin_jq_of_subset_range_qExpand _ ℓ hFr hmemF
      (fun hin => hd (hiff.mp hin))

end RelfinrankQExpandFull

end ModularCurve

end
