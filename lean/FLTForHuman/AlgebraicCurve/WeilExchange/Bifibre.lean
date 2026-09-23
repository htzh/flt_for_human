/-
The bifibre count: the fibre/cardinality bridge, surjectivity of restriction, and
the double-fibration orbit–stabiliser count, after FLT's
`P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_bifiber.lean>).

This is the assembly the pin calls `BifibreDev`, minus the shared prelude (already
public in `WeilExchange/Transport.lean` and imported, never restated; SET-2 §0) and
minus the fibre dictionary (T2's `Defs/PlaceDictionary.lean`). The three public
nodes are:

* `Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` — for a Galois
  `F' ⊆ M`, the weighted fibre over `w` is `finrank F' M` concentrated at `W`;
* `Place.exists_restrict_eq` — restriction of places is surjective along a finite
  separable extension;
* `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber` — the `F`-weighted sum over
  the bifibre `T` of `w₁` and `w₂` is the product
  `(e₁f₁)(e₂f₂)`, by the generic orbit–intersection count
  `MulAction.ncard_orbit_inter_orbit_mul_card` applied to the
  `Gal(M/F)`-orbit of a lift `P₁`.

T6's local exchange and the human's T7 divisor exchange consume the first two and
the count (`TOPIC-t6-local-exchange.md` §2, `TOPIC-t7-divisor-exchange.md`).
-/
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
import FLTForHuman.AlgebraicCurve.WeilExchange.FiberOverCount
import FLTForHuman.FieldTheory.FiniteGroupAction
import Mathlib.FieldTheory.Galois.Basic

set_option autoImplicit false

-- The pin's `haveI`/`letI` walls are kept literal (SET-1 §3).
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain

namespace AlgebraicCurve

open Place

/-! ## The two small `Place` nodes -/

theorem Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg {K F' M : Type*} [Field K]
    [Field F'] [Field M] [Algebra K F'] [Algebra K M] [Algebra F' M]
    [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M] (w : Place K F')
    (W : Place K M) (hW : W.restrict F' = w) :
    (w.fiberOver M).card * (W.ramificationIndex F' * W.inertiaDeg F') =
      Module.finrank F' M := by
  have hsum := sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := M) w
  have hconst : ∀ W' ∈ w.fiberOver M,
      (W'.ramificationIndex F' : ℤ) * (W'.inertiaDeg F' : ℤ)
        = (W.ramificationIndex F' : ℤ) * (W.inertiaDeg F' : ℤ) := by
    intro W' hW'
    have h : W'.restrict F' = W.restrict F' :=
      (restrict_eq_of_mem_fiberOver w hW').trans hW.symm
    rw [Place.ramificationIndex_eq_of_restrict_eq W W' h,
      Place.inertiaDeg_eq_of_restrict_eq W W' h]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul] at hsum
  exact_mod_cast hsum

theorem Place.exists_restrict_eq {K F' M : Type*} [Field K] [Field F'] [Field M]
    [Algebra K F'] [Algebra K M] [Algebra F' M] [IsScalarTower K F' M]
    [FiniteDimensional F' M] [Algebra.IsSeparable F' M] (w : Place K F') :
    ∃ W : Place K M, W.restrict F' = w := by
  by_contra hne
  push Not at hne
  have hempty : w.fiberOver M = ∅ :=
    Finset.eq_empty_of_forall_notMem fun W hW => hne W (restrict_eq_of_mem_fiberOver w hW)
  have hsum := sum_ramificationIndex_mul_inertiaDeg_fiberOver (F' := M) w
  rw [hempty, Finset.sum_empty] at hsum
  have hpos : 0 < Module.finrank F' M := Module.finrank_pos
  omega

/-! ## The `Gal(M/F)`-action packaging -/

namespace BifibreDev

section Action

variable (F M : Type*) [Field F] [Field M] [Algebra F M]

def resHom (L : Type*) [Field L] [Algebra F L] [Algebra L M] [IsScalarTower F L M] :
    (M ≃ₐ[L] M) →* (M ≃ₐ[F] M) where
  toFun σ := σ.restrictScalars F
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

variable (K : Type*) [Field K] [Algebra K F] [Algebra K M] [IsScalarTower K F M]

@[reducible] noncomputable def galAction : MulAction (M ≃ₐ[F] M) (Place K M) :=
  MulAction.compHom (Place K M)
    ((SemilinearAut.ofAlgAut (K := K) (F := M)).comp (resHom K M F))

attribute [local instance] galAction

variable {K F M}

theorem gal_smul_def (g : M ≃ₐ[F] M) (W : Place K M) :
    g • W = SemilinearAut.ofAlgAut (g.restrictScalars K) • W := rfl

variable {L : Type*} [Field L] [Algebra F L] [Algebra L M] [IsScalarTower F L M]

theorem mem_range_resHom_iff {g : M ≃ₐ[F] M} :
    g ∈ (resHom F M L).range ↔ ∀ x : L, g (algebraMap L M x) = algebraMap L M x := by
  constructor
  · rintro ⟨τ, rfl⟩ x
    exact τ.commutes x
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := (g : M ≃+* M)) h, AlgEquiv.ext fun _ => rfl⟩

theorem card_range_resHom : Nat.card (resHom F M L).range = Nat.card (M ≃ₐ[L] M) :=
  (Nat.card_congr (MonoidHom.ofInjective (f := resHom F M L)
    (fun _ _ h => AlgEquiv.restrictScalars_injective F h)).toEquiv).symm

theorem index_range_resHom [FiniteDimensional F M] [IsGalois F M] [FiniteDimensional L M]
    [IsGalois L M] : (resHom F M L).range.index = Module.finrank F L := by
  have h1 := Subgroup.card_mul_index (resHom F M L).range
  rw [card_range_resHom, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank] at h1
  have h2 := Module.finrank_mul_finrank F L M
  have hpos : 0 < Module.finrank L M := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h2, mul_comm]

variable [Algebra K L] [IsScalarTower K L M]

theorem orbit_range_resHom_eq [FiniteDimensional L M] [IsGalois L M] (P : Place K M) :
    MulAction.orbit (resHom F M L).range P = ↑((P.restrict L).fiberOver M) := by
  ext Q
  rw [MulAction.mem_orbit_iff, Finset.mem_coe, Place.mem_fiberOver]
  constructor
  · rintro ⟨⟨_, τ, rfl⟩, rfl⟩
    exact Place.restrict_ofAlgAut_smul τ P
  · intro h
    obtain ⟨σ, hσ⟩ := Place.exists_algEquiv_smul_eq_of_restrict_eq P Q h
    exact ⟨⟨σ.restrictScalars F, σ, rfl⟩, hσ⟩

omit [Algebra F L] [Algebra L M] [IsScalarTower F L M] [Algebra K L] [IsScalarTower K L M] in
theorem orbit_gal_eq [FiniteDimensional F M] [IsGalois F M] (P : Place K M) :
    MulAction.orbit (M ≃ₐ[F] M) P = ↑((P.restrict F).fiberOver M) := by
  ext Q
  rw [MulAction.mem_orbit_iff, Finset.mem_coe, Place.mem_fiberOver]
  constructor
  · rintro ⟨g, rfl⟩
    exact Place.restrict_ofAlgAut_smul g P
  · intro h
    exact Place.exists_algEquiv_smul_eq_of_restrict_eq P Q h

omit [Algebra F L] [Algebra L M] [IsScalarTower F L M] [Algebra K L] [IsScalarTower K L M] in
theorem image_val_orbit {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G) (a : X)
    (x : MulAction.orbit G a) :
    Subtype.val '' MulAction.orbit H x = MulAction.orbit H (x : X) :=
  (Set.range_comp _ _).symm

end Action

section Compositum

variable {F F₁ F₂ E M : Type*} [Field F] [Field F₁] [Field F₂] [Field E] [Field M]
    [Algebra F E] [Algebra F M] [Algebra F₁ E] [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M]
    [Algebra E M] [IsScalarTower F E M] [IsScalarTower F₁ E M] [IsScalarTower F₂ E M]

theorem forall_apply_algebraMap_eq_of_adjoin_eq_top
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (g : M ≃ₐ[F] M) (h₁ : ∀ x : F₁, g (algebraMap F₁ M x) = algebraMap F₁ M x)
    (h₂ : ∀ x : F₂, g (algebraMap F₂ M x) = algebraMap F₂ M x) (z : E) :
    g (algebraMap E M z) = algebraMap E M z := by
  let φ : E →ₐ[F] M := (g : M →ₐ[F] M).comp (IsScalarTower.toAlgHom F E M)
  let ψ : E →ₐ[F] M := IsScalarTower.toAlgHom F E M
  have htop : AlgHom.equalizer φ ψ = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Algebra.adjoin_le ?_
    rintro x (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · show g (algebraMap E M (algebraMap F₁ E y)) = algebraMap E M (algebraMap F₁ E y)
      rw [← IsScalarTower.algebraMap_apply]
      exact h₁ y
    · show g (algebraMap E M (algebraMap F₂ E y)) = algebraMap E M (algebraMap F₂ E y)
      rw [← IsScalarTower.algebraMap_apply]
      exact h₂ y
  have hz : z ∈ AlgHom.equalizer φ ψ := htop ▸ Algebra.mem_top
  exact hz

end Compositum

end BifibreDev

open BifibreDev

attribute [local instance] galAction

/-! ## The bifibre count -/

theorem Place.sum_ramificationIndex_mul_inertiaDeg_bifiber
    {K F F₁ F₂ E : Type*} (M : Type*) [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Field M] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra K M]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F M] [Algebra F₁ E] [Algebra F₂ E]
    [Algebra F₁ M] [Algebra F₂ M] [Algebra E M] [IsScalarTower K F F₁]
    [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower K F₁ M]
    [IsScalarTower K F₂ M] [IsScalarTower K E M] [IsScalarTower F F₁ M]
    [IsScalarTower F F₂ M] [IsScalarTower F E M] [IsScalarTower F₁ E M]
    [IsScalarTower F₂ E M] [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    [FiniteDimensional F E] [FiniteDimensional F₁ E] [FiniteDimensional F₂ E]
    [FiniteDimensional F M] [IsGalois F M]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v)
    (hw₂ : w₂.restrict F = v) (T : Finset (Place K E))
    (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F =
      (w₁.ramificationIndex F * w₁.inertiaDeg F)
        * (w₂.ramificationIndex F * w₂.inertiaDeg F) := by
  classical

  haveI : FiniteDimensional F₁ M := Module.Finite.of_restrictScalars_finite F F₁ M
  haveI : FiniteDimensional F₂ M := Module.Finite.of_restrictScalars_finite F F₂ M
  haveI : FiniteDimensional E M := Module.Finite.of_restrictScalars_finite F E M
  haveI : IsGalois F₁ M := IsGalois.tower_top_of_isGalois F F₁ M
  haveI : IsGalois F₂ M := IsGalois.tower_top_of_isGalois F F₂ M
  haveI : IsGalois E M := IsGalois.tower_top_of_isGalois F E M

  obtain ⟨P₁, hP₁⟩ := Place.exists_restrict_eq (M := M) w₁
  obtain ⟨P₂, hP₂⟩ := Place.exists_restrict_eq (M := M) w₂
  have hP₁F : P₁.restrict F = v := by rw [← restrict_restrict (E := F₁) P₁, hP₁, hw₁]
  have hP₂F : P₂.restrict F = v := by rw [← restrict_restrict (E := F₂) P₂, hP₂, hw₂]
  have hP₂P₁ : P₂.restrict F = P₁.restrict F := by rw [hP₁F, hP₂F]

  have hA : (v.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F) =
      Module.finrank F M :=
    Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg v P₁ hP₁F
  have hA₁ : (w₁.ramificationIndex F * w₁.inertiaDeg F) * Module.finrank F₁ M =
      (w₁.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F) := by
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg w₁ P₁ hP₁
    have he := Place.ramificationIndex_eq_mul_ramificationIndex_restrict (F := F) (E := F₁) P₁
    have hf := Place.inertiaDeg_eq_mul_inertiaDeg_restrict (F := F) (E := F₁) P₁
    rw [hP₁] at he hf
    rw [← hTC, he, hf]; ring
  have hA₂ : (w₂.ramificationIndex F * w₂.inertiaDeg F) * Module.finrank F₂ M =
      (w₂.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F) := by
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg w₂ P₂ hP₂
    have he := Place.ramificationIndex_eq_mul_ramificationIndex_restrict (F := F) (E := F₂) P₂
    have hf := Place.inertiaDeg_eq_mul_inertiaDeg_restrict (F := F) (E := F₂) P₂
    rw [hP₂] at he hf
    rw [← Place.ramificationIndex_eq_of_restrict_eq P₁ P₂ hP₂P₁,
      ← Place.inertiaDeg_eq_of_restrict_eq P₁ P₂ hP₂P₁, ← hTC, he, hf]; ring

  have hEpt : ∀ W ∈ T, (W.ramificationIndex F * W.inertiaDeg F) * Module.finrank E M =
      (W.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F) := by
    intro W hW
    obtain ⟨hW₁, -⟩ := (hT W).mp hW
    obtain ⟨P, hP⟩ := Place.exists_restrict_eq (M := M) W
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg W P hP
    have he := Place.ramificationIndex_eq_mul_ramificationIndex_restrict (F := F) (E := E) P
    have hf := Place.inertiaDeg_eq_mul_inertiaDeg_restrict (F := F) (E := E) P
    rw [hP] at he hf
    have hPF : P.restrict F = P₁.restrict F := by
      rw [← restrict_restrict (E := F₁) P, ← restrict_restrict (F := F₁) (E := E) P, hP, hW₁,
        hw₁, hP₁F]
    rw [← Place.ramificationIndex_eq_of_restrict_eq P₁ P hPF,
      ← Place.inertiaDeg_eq_of_restrict_eq P₁ P hPF, ← hTC, he, hf]; ring
  have hbi : w₁.fiberOver M ∩ w₂.fiberOver M = T.biUnion fun W => W.fiberOver M := by
    ext P
    simp only [Finset.mem_inter, Place.mem_fiberOver, Finset.mem_biUnion, hT]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨P.restrict E, ⟨(restrict_restrict P).trans h₁, (restrict_restrict P).trans h₂⟩, rfl⟩
    · rintro ⟨W, ⟨h₁, h₂⟩, rfl⟩
      exact ⟨(restrict_restrict P).symm.trans h₁, (restrict_restrict P).symm.trans h₂⟩
  have hdisj : (↑T : Set (Place K E)).PairwiseDisjoint fun W => W.fiberOver M := by
    intro W _ W' _ hne
    change Disjoint (W.fiberOver M) (W'.fiberOver M)
    exact Finset.disjoint_left.mpr fun P h h' =>
      hne (((Place.mem_fiberOver W).mp h).symm.trans ((Place.mem_fiberOver W').mp h'))
  have hEsum : (∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F) * Module.finrank E M =
      (w₁.fiberOver M ∩ w₂.fiberOver M).card
        * (P₁.ramificationIndex F * P₁.inertiaDeg F) := by
    rw [hbi, Finset.card_biUnion hdisj, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl hEpt

  have hle : (resHom F M F₁).range ⊓ (resHom F M F₂).range ≤ (resHom F M E).range :=
    fun g hg => mem_range_resHom_iff.mpr (forall_apply_algebraMap_eq_of_adjoin_eq_top hgen g
      (mem_range_resHom_iff.mp hg.1) (mem_range_resHom_iff.mp hg.2))
  have hidx : ((resHom F M F₁).range ⊓ (resHom F M F₂).range).index =
      (resHom F M F₁).range.index * (resHom F M F₂).range.index := by
    have hle' := Subgroup.index_inf_le (H := (resHom F M F₁).range) (K := (resHom F M F₂).range)
    have hdvd := Subgroup.index_dvd_of_le hle
    rw [index_range_resHom, index_range_resHom] at hle' ⊢
    rw [index_range_resHom, hLD] at hdvd
    exact le_antisymm hle' (Nat.le_of_dvd (Nat.pos_of_ne_zero
      Subgroup.FiniteIndex.index_ne_zero) hdvd)
  have hprod := Subgroup.exists_eq_mul_of_index_inf_eq _ _ hidx

  have hx₂ : P₂ ∈ MulAction.orbit (M ≃ₐ[F] M) P₁ := by
    rw [orbit_gal_eq, Finset.mem_coe, Place.mem_fiberOver]
    exact hP₂P₁
  obtain ⟨x₁, hx₁⟩ : ∃ x : MulAction.orbit (M ≃ₐ[F] M) P₁, (x : Place K M) = P₁ :=
    ⟨⟨P₁, MulAction.mem_orbit_self P₁⟩, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x : MulAction.orbit (M ≃ₐ[F] M) P₁, (x : Place K M) = P₂ :=
    ⟨⟨P₂, hx₂⟩, rfl⟩
  have hO := MulAction.ncard_orbit_inter_orbit_mul_card (X := MulAction.orbit (M ≃ₐ[F] M) P₁)
    (resHom F M F₁).range (resHom F M F₂).range hprod x₁ x₂
  have cX : Nat.card (MulAction.orbit (M ≃ₐ[F] M) P₁) = (v.fiberOver M).card := by
    rw [Nat.card_coe_set_eq, orbit_gal_eq, hP₁F, Set.ncard_coe_finset]
  have c₁ : (MulAction.orbit (resHom F M F₁).range x₁).ncard = (w₁.fiberOver M).card := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, image_val_orbit, hx₁,
      orbit_range_resHom_eq, hP₁, Set.ncard_coe_finset]
  have c₂ : (MulAction.orbit (resHom F M F₂).range x₂).ncard = (w₂.fiberOver M).card := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, image_val_orbit, hx₂,
      orbit_range_resHom_eq, hP₂, Set.ncard_coe_finset]
  have c₁₂ : (MulAction.orbit (resHom F M F₁).range x₁ ∩
      MulAction.orbit (resHom F M F₂).range x₂).ncard =
      (w₁.fiberOver M ∩ w₂.fiberOver M).card := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.image_inter Subtype.val_injective, image_val_orbit, image_val_orbit, hx₁, hx₂,
      orbit_range_resHom_eq, orbit_range_resHom_eq, hP₁, hP₂, ← Finset.coe_inter,
      Set.ncard_coe_finset]
  rw [cX, c₁, c₂, c₁₂] at hO

  have hn₁ := Module.finrank_mul_finrank F F₁ M
  have hn₂ := Module.finrank_mul_finrank F F₂ M
  have hnE := Module.finrank_mul_finrank F E M
  have hnn : Module.finrank F₁ M * Module.finrank F₂ M =
      Module.finrank F M * Module.finrank E M := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := F) (M := E))
    calc Module.finrank F E * (Module.finrank F₁ M * Module.finrank F₂ M)
        = (Module.finrank F F₁ * Module.finrank F₁ M) *
            (Module.finrank F F₂ * Module.finrank F₂ M) := by rw [hLD]; ring
      _ = Module.finrank F M * Module.finrank F M := by rw [hn₁, hn₂]
      _ = (Module.finrank F E * Module.finrank E M) * Module.finrank F M := by rw [hnE]
      _ = Module.finrank F E * (Module.finrank F M * Module.finrank E M) := by ring

  have hpos : 0 < Module.finrank F M * Module.finrank E M :=
    Nat.mul_pos Module.finrank_pos Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc (∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F) *
        (Module.finrank F M * Module.finrank E M)
      = Module.finrank F M * ((∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F) *
          Module.finrank E M) := by ring
    _ = ((v.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F)) *
          ((w₁.fiberOver M ∩ w₂.fiberOver M).card *
            (P₁.ramificationIndex F * P₁.inertiaDeg F)) := by rw [hEsum, hA]
    _ = ((w₁.fiberOver M ∩ w₂.fiberOver M).card * (v.fiberOver M).card) *
          ((P₁.ramificationIndex F * P₁.inertiaDeg F) *
            (P₁.ramificationIndex F * P₁.inertiaDeg F)) := by ring
    _ = ((w₁.fiberOver M).card * (w₂.fiberOver M).card) *
          ((P₁.ramificationIndex F * P₁.inertiaDeg F) *
            (P₁.ramificationIndex F * P₁.inertiaDeg F)) := by rw [hO]
    _ = ((w₁.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F)) *
          ((w₂.fiberOver M).card * (P₁.ramificationIndex F * P₁.inertiaDeg F)) := by ring
    _ = ((w₁.ramificationIndex F * w₁.inertiaDeg F) * Module.finrank F₁ M) *
          ((w₂.ramificationIndex F * w₂.inertiaDeg F) * Module.finrank F₂ M) := by rw [hA₁, hA₂]
    _ = (w₁.ramificationIndex F * w₁.inertiaDeg F)
          * (w₂.ramificationIndex F * w₂.inertiaDeg F)
          * (Module.finrank F₁ M * Module.finrank F₂ M) := by ring
    _ = (w₁.ramificationIndex F * w₁.inertiaDeg F)
          * (w₂.ramificationIndex F * w₂.inertiaDeg F)
          * (Module.finrank F M * Module.finrank E M) := by rw [hnn]

end AlgebraicCurve
