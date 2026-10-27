/-
The two places-over-a-constant-field-extension statements: the count of `K`-embeddings
above a fixed place through `ramificationIndexAlong`, and the non-cancellation of
`K'`-weighted `F`-sums at a lifted place.

Statements from the `Theorems/` wrappers, proofs after the `P2M/Sol/S_` files of the
pinned FLT (`anthropics/fermats-last-theorem`, `aa2d8b3`).

**Counting embeddings above a place.** For an integral `φ : F →ₐ[K] F'` that is finite
along a curve `F'/K`, an algebraically closed extension `E ⊇ K`, a valuation subring
`A` of `E` and a place `q` of `F'` above `v₀ = q.restrictAlong φ`, the number of
`K`-embeddings `F' →ₐ[K] E` that extend the embedding `e : F →ₐ[K] E` attached to `A`
and that carry `q`'s valuation subring into `A` equals the ramification index
`q.ramificationIndexAlong φ`. The count is taken inside the Galois closure `M` of
`F'` over `F`: the `F`-automorphisms of `M` act transitively on the places above a
fixed one (`exists_smul_eq_of_restrict_eq`), so a preimage count reduces to the
stabiliser, whose cardinality is `ramificationIndex * inertiaDeg`
(`ncard_stabilizer`); the inertia degree is `1` over an algebraically closed base
(`inertiaDeg_eq_one`), and the tower formula `ramificationIndex_tower` converts
`F ⊆ F' ⊆ M` into the `F'`-index.

**Non-cancellation of `K'`-weighted sums.** Let `K ⊆ K'` be algebraically closed
fields, `F/K` and `F'/K'` curves with `K' F = F'` and a place lift `lift` preserving
orders along `F ↪ F'`. For a `K`-linearly independent family `B` of `K'` and a nonzero
finitely supported family `g` of `F`, the `F'`-element
`∑ j, B j * g j` is nonzero, and its order at `lift v` is at most `v.ord (g j)` for
every `j` in the support. The proof expands `(π)⁻ᵐ g j = c j + π * o' j` with
`c j ∈ K` in the residue field of `v`, and reads the `K'`-coefficients `c j` off a
`K`-linear relation: they cannot all vanish because `B` is independent.

The pin's machine namespaces are rectified: `SpecialisationCount` is descriptive and
kept, `W7XChildL`'s single lemma lands in `AlgebraicCurve.Place` with the headline.

Wire: `spec/check_port.py` diffs every public declaration of this module against the
pin files named by the `spec-pin:` lines below.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus
import FLTForHuman.AlgebraicCurve.Defs.PlaceDictionary
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.SemilinearAut
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import FLTForHuman.AlgebraicCurve.WeilExchange.Bifibre
import FLTForHuman.AlgebraicCurve.WeilExchange.FiberOverCount
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
import Mathlib.FieldTheory.Galois.Basic

set_option autoImplicit false

-- The pin's `haveI`/`letI` walls are kept literal.
set_option linter.style.haveILetI false

noncomputable section

open scoped Pointwise

namespace AlgebraicCurve

namespace SpecialisationCount

theorem ncard_preimage_eq_mul {G T : Type*} [Finite G] (Θ : G → T) (p : Set T) (hp : p.Finite)
    (h : ℕ) (hfib : ∀ t ∈ p, Set.ncard {g | Θ g = t} = h) :
    Set.ncard {g | Θ g ∈ p} = h * p.ncard := by
  classical
  induction p, hp using Set.Finite.induction_on with
  | empty => simp
  | @insert t s hts hs ih =>
    have hfib' : ∀ t' ∈ s, Set.ncard {g | Θ g = t'} = h := fun t' ht' =>
      hfib t' (Set.mem_insert_of_mem _ ht')
    have hunion : {g | Θ g ∈ insert t s} = {g | Θ g = t} ∪ {g | Θ g ∈ s} := by
      ext g
      simp
    have hdisj : Disjoint {g | Θ g = t} {g | Θ g ∈ s} := by
      rw [Set.disjoint_left]
      rintro g (rfl : Θ g = t) hg
      exact hts hg
    rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), ih hfib',
      hfib t (Set.mem_insert _ _), Set.ncard_insert_of_notMem hts hs]
    ring

section Galois

variable {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M]
  [Algebra F M] [IsScalarTower K F M]

noncomputable def toAutK : (M ≃ₐ[F] M) →* (M ≃ₐ[K] M) where
  toFun g := g.restrictScalars K
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

@[simp] theorem toAutK_apply (g : M ≃ₐ[F] M) (x : M) : toAutK (K := K) g x = g x := rfl

theorem mem_smul_iff (g : M ≃ₐ[F] M) (W : Place K M) (x : M) :
    x ∈ (toAutK (K := K) g • W).toValuationSubring ↔ g⁻¹ x ∈ W.toValuationSubring := by
  have h := Place.mem_smul_iff_symm_mem (g.restrictScalars K) W x
  simpa [toAutK] using h

theorem restrict_smul [Algebra.IsIntegral F M] (g : M ≃ₐ[F] M) (W : Place K M) :
    (toAutK (K := K) g • W).restrict F = W.restrict F := by
  refine Place.ext (SetLike.ext fun f => ?_)
  rw [Place.mem_restrict_iff, Place.mem_restrict_iff, mem_smul_iff, AlgEquiv.commutes]

theorem restrict_restrict {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F'] [Algebra F' M]
    [IsScalarTower K F F'] [IsScalarTower K F' M] [IsScalarTower F F' M]
    [Algebra.IsIntegral F F'] [Algebra.IsIntegral F' M] [Algebra.IsIntegral F M] (W : Place K M) :
    (W.restrict F').restrict F = W.restrict F :=
  BifibreDev.restrict_restrict W

variable [FiniteDimensional F M] [IsGalois F M]

theorem exists_smul_eq_of_restrict_eq (W W' : Place K M) (h : W'.restrict F = W.restrict F) :
    ∃ g : M ≃ₐ[F] M, toAutK (K := K) g • W = W' := by
  set v := W.restrict F with hv
  let S := Place.integralClosureAt M v
  have hW : W.restrict F = v := rfl
  have h1 : (Place.fiberCenter M v hW).asIdeal ∈
      (IsLocalRing.maximalIdeal v.toValuationSubring).primesOver S :=
    ⟨(Place.fiberCenter M v hW).isPrime, Place.fiberCenter_liesOver hW⟩
  have h2 : (Place.fiberCenter M v h).asIdeal ∈
      (IsLocalRing.maximalIdeal v.toValuationSubring).primesOver S :=
    ⟨(Place.fiberCenter M v h).isPrime, Place.fiberCenter_liesOver h⟩
  obtain ⟨σ, hσ⟩ := Ideal.exists_comap_galRestrict_eq v.toValuationSubring F M S h1 h2
  refine ⟨σ⁻¹, ?_⟩
  have hW'' : (toAutK (K := K) σ⁻¹ • W).restrict F = v := restrict_smul _ _
  refine Place.eq_of_fiberCenter_eq hW'' h (IsDedekindDomain.HeightOneSpectrum.ext ?_)
  rw [← hσ]
  ext c
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hσc : galRestrict v.toValuationSubring F M S σ c ≠ 0 :=
    (map_ne_zero_iff _ (galRestrict v.toValuationSubring F M S σ).injective).mpr hc
  rw [Ideal.mem_comap, Place.mem_fiberCenter_iff_ord_pos hW'' hc,
    Place.mem_fiberCenter_iff_ord_pos hW hσc, algebraMap_galRestrict_apply]
  have : (toAutK (K := K) σ⁻¹ • W).ord (algebraMap S M c)
      = (toAutK (K := K) σ⁻¹ • W).ord (toAutK (K := K) σ⁻¹ (σ (algebraMap S M c))) := by
    rw [toAutK_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  rw [this, Place.ord_smul]

theorem ncard_setOf_smul_eq (W₁ W : Place K M) (h : W.restrict F = W₁.restrict F) :
    Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W} =
      Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} := by
  obtain ⟨g₀, rfl⟩ := exists_smul_eq_of_restrict_eq W₁ W h
  have : {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = toAutK (K := K) g₀ • W₁} =
      (fun g => g₀ * g) '' {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hg
      refine ⟨g₀⁻¹ * g, ?_, by group⟩
      rw [map_mul, mul_smul, hg, ← mul_smul, map_inv, inv_mul_cancel, one_smul]
    · rintro ⟨g', hg', rfl⟩
      rw [map_mul, mul_smul, hg']
  rw [this, Set.ncard_image_of_injective _ (mul_right_injective g₀)]

theorem ncard_stabilizer [IsAlgClosed K] (W₁ : Place K M) :
    Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} =
      W₁.ramificationIndex F * W₁.inertiaDeg F := by
  classical
  set s : ℕ := Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} with hs

  have hcount := ncard_preimage_eq_mul (fun g : M ≃ₐ[F] M => toAutK (K := K) g • W₁)
    (↑((W₁.restrict F).fiberOver M) : Set (Place K M)) (Finset.finite_toSet _) s
    (fun W hW => by
      rw [Finset.mem_coe, Place.mem_fiberOver] at hW
      exact ncard_setOf_smul_eq W₁ W hW)
  have huniv : {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ ∈
      (↑((W₁.restrict F).fiberOver M) : Set (Place K M))} = Set.univ := by
    refine Set.eq_univ_of_forall fun g => ?_
    rw [Set.mem_ofPred_eq, Finset.mem_coe, Place.mem_fiberOver, restrict_smul]
  rw [huniv, Set.ncard_univ, Set.ncard_coe_finset, IsGalois.card_aut_eq_finrank] at hcount
  have hfi := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (W₁.restrict F) W₁ rfl
  have hr : ((W₁.restrict F).fiberOver M).card ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨W₁, Place.restrict_mem_fiberOver W₁⟩
  rw [hcount] at hfi
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr) (hfi.trans (mul_comm _ _))).symm

end Galois

section Tower

variable {K F F' M : Type*} [Field K] [Field F] [Field F'] [Field M] [Algebra K F] [Algebra K F']
  [Algebra K M] [Algebra F F'] [Algebra F' M] [Algebra F M] [IsScalarTower K F F']
  [IsScalarTower K F' M] [IsScalarTower K F M] [IsScalarTower F F' M]
  [Algebra.IsIntegral F F'] [Algebra.IsIntegral F' M] [Algebra.IsIntegral F M]

theorem inertiaDeg_eq_one [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K M]
    (W : Place K M) : W.inertiaDeg F = 1 := by
  have h := W.deg_restrict_mul_inertiaDeg (F := F)
  rwa [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed,
    one_mul] at h

theorem ramificationIndex_tower (W : Place K M) :
    W.ramificationIndex F = W.ramificationIndex F' * (W.restrict F').ramificationIndex F := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (W.restrict F).toValuationSubring
  have h1 : (W.restrict F).ord (π : F) = 1 := Place.ord_coe_irreducible _ hπ
  have h2 := W.ord_restrict (F := F) (π : F)
  have h3 := W.ord_restrict (F := F') (algebraMap F F' (π : F))
  have h4 := (W.restrict F').ord_restrict (F := F) (π : F)
  rw [← IsScalarTower.algebraMap_apply, h2, h4, restrict_restrict, h1, mul_one, mul_one]
    at h3
  exact_mod_cast h3

end Tower

section Core

variable {K F F' M E : Type*} [Field K] [Field F] [Field F'] [Field M] [Field E]
  [Algebra K F] [Algebra K F'] [Algebra K M]
  [Algebra F F'] [Algebra F' M] [Algebra F M] [Algebra F E]
  [IsScalarTower K F F'] [IsScalarTower K F' M] [IsScalarTower K F M] [IsScalarTower F F' M]

noncomputable def theta (ι : M →ₐ[F] E) (g : M ≃ₐ[F] M) : F' →ₐ[F] E :=
  ι.comp ((g : M →ₐ[F] M).comp (IsScalarTower.toAlgHom F F' M))

@[simp] theorem theta_apply (ι : M →ₐ[F] E) (g : M ≃ₐ[F] M) (y : F') :
    theta ι g y = ι (g (algebraMap F' M y)) := rfl

theorem theta_mul_restrictScalars (ι : M →ₐ[F] E) (g : M ≃ₐ[F] M) (h : M ≃ₐ[F'] M) :
    theta ι (g * h.restrictScalars F) = theta (F' := F') ι g := by
  ext y
  simp only [theta_apply, AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]

theorem setOf_theta_eq (ι : M →ₐ[F] E) (g₀ : M ≃ₐ[F] M) :
    {g : M ≃ₐ[F] M | theta (F' := F') ι g = theta ι g₀} =
      (fun h : M ≃ₐ[F'] M => g₀ * h.restrictScalars F) '' Set.univ := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]
  constructor
  · intro hg
    have hfix : ∀ y : F', (g₀⁻¹ * g) (algebraMap F' M y) = algebraMap F' M y := by
      intro y
      have := congrArg (fun τ : F' →ₐ[F] E => τ y) hg
      simp only [theta_apply] at this
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
      exact ι.toRingHom.injective this
    refine ⟨{ (g₀⁻¹ * g).toRingEquiv with commutes' := hfix }, ?_⟩
    refine AlgEquiv.ext fun x => ?_
    change g₀ ((g₀⁻¹ * g) x) = g x
    rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
  · rintro ⟨h, rfl⟩
    exact theta_mul_restrictScalars ι g₀ h

variable [FiniteDimensional F M] [IsGalois F M] [IsAlgClosed E]

theorem theta_surjective (ι : M →ₐ[F] E) : Function.Surjective (theta (F' := F') ι) := by
  intro τ
  haveI : Algebra.IsAlgebraic F M := Algebra.IsAlgebraic.of_finite F M
  letI : Algebra F' E := τ.toRingHom.toAlgebra
  haveI : IsScalarTower F F' E := IsScalarTower.of_algebraMap_eq fun x => (τ.commutes x).symm
  haveI : Algebra.IsAlgebraic F' M :=
    Algebra.IsAlgebraic.tower_top (K := F) F'
  let σ' : M →ₐ[F'] E := IsAlgClosed.lift
  let σ : M →ₐ[F] E := σ'.restrictScalars F
  letI : Algebra M E := ι.toRingHom.toAlgebra
  haveI : IsScalarTower F M E := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  refine ⟨σ.restrictNormal' M, ?_⟩
  ext y
  rw [theta_apply]
  have h1 : ι (σ.restrictNormal' M (algebraMap F' M y)) = σ (algebraMap F' M y) := by
    have := AlgHom.restrictNormal_commutes σ M (algebraMap F' M y)
    rw [Algebra.algebraMap_self, RingHom.id_apply] at this
    exact this
  rw [h1]
  change σ' (algebraMap F' M y) = τ y
  rw [σ'.commutes]
  rfl

theorem ncard_setOf_theta_eq (ι : M →ₐ[F] E) (τ : F' →ₐ[F] E) :
    Set.ncard {g : M ≃ₐ[F] M | theta ι g = τ} = Nat.card (M ≃ₐ[F'] M) := by
  obtain ⟨g₀, rfl⟩ := theta_surjective ι τ
  have hinj : Function.Injective (fun h : M ≃ₐ[F'] M => g₀ * h.restrictScalars F) :=
    (mul_right_injective g₀).comp (AlgEquiv.restrictScalars_injective F)
  rw [setOf_theta_eq, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]

omit [IsScalarTower K F F'] [FiniteDimensional F M] [IsGalois F M] [IsAlgClosed E] in

theorem restrict_smul_eq_iff (ι : M →ₐ[F] E) (A : ValuationSubring E) (W₁ : Place K M)
    (hW₁ : W₁.toValuationSubring = A.comap ι.toRingHom) [Algebra.IsIntegral F' M]
    (g : M ≃ₐ[F] M) (q : Place K F') :
    (toAutK (K := K) g⁻¹ • W₁).restrict F' = q ↔
      ∀ y : F', y ∈ q.toValuationSubring ↔ theta ι g y ∈ A := by
  constructor
  · rintro rfl y
    rw [Place.mem_restrict_iff, mem_smul_iff, inv_inv, hW₁, ValuationSubring.mem_comap]
    rfl
  · intro h
    refine Place.ext (SetLike.ext fun y => ?_)
    rw [Place.mem_restrict_iff, mem_smul_iff, inv_inv, hW₁, ValuationSubring.mem_comap, h y]
    rfl

theorem ncard_setOf_forall_mem_iff [IsAlgClosed K] [IsCurveOver K F] [IsCurveOver K F']
    [IsCurveOver K M] [FiniteDimensional F F']
    (ι : M →ₐ[F] E) (A : ValuationSubring E) (W₁ : Place K M)
    (hW₁ : W₁.toValuationSubring = A.comap ι.toRingHom) (q : Place K F')
    (hq : q.restrict F = W₁.restrict F) :
    Set.ncard {τ : F' →ₐ[F] E | ∀ y : F', y ∈ q.toValuationSubring ↔ τ y ∈ A} =
      q.ramificationIndex F := by
  classical
  haveI : FiniteDimensional F' M := Module.Finite.of_restrictScalars_finite F F' M
  haveI : IsGalois F' M := IsGalois.tower_top_of_isGalois F F' M
  set p : Set (F' →ₐ[F] E) := {τ | ∀ y : F', y ∈ q.toValuationSubring ↔ τ y ∈ A} with hp

  have h1 : Set.ncard {g : M ≃ₐ[F] M | theta ι g ∈ p} = Nat.card (M ≃ₐ[F'] M) * p.ncard :=
    ncard_preimage_eq_mul _ p (Set.toFinite p) _ fun τ _ => ncard_setOf_theta_eq ι τ

  have h2 : {g : M ≃ₐ[F] M | theta ι g ∈ p} =
      (fun g => g⁻¹) '' {g : M ≃ₐ[F] M | (toAutK (K := K) g • W₁).restrict F' = q} := by
    rw [Set.image_inv_eq_inv]
    ext g
    simp only [Set.mem_inv, Set.mem_ofPred_eq, hp]
    exact (restrict_smul_eq_iff ι A W₁ hW₁ g q).symm
  have h2' : Set.ncard {g : M ≃ₐ[F] M | theta ι g ∈ p} =
      Set.ncard {g : M ≃ₐ[F] M | (toAutK (K := K) g • W₁).restrict F' = q} := by
    rw [h2, Set.ncard_image_of_injective _ inv_injective]

  have h3 : Set.ncard {g : M ≃ₐ[F] M | (toAutK (K := K) g • W₁).restrict F' = q} =
      Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} * (q.fiberOver M).card := by
    have := ncard_preimage_eq_mul (fun g : M ≃ₐ[F] M => toAutK (K := K) g • W₁)
      (↑(q.fiberOver M) : Set (Place K M)) (Finset.finite_toSet _)
      (Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁}) (fun W hW => by
        rw [Finset.mem_coe, Place.mem_fiberOver] at hW
        refine ncard_setOf_smul_eq W₁ W ?_
        rw [← hq, ← hW, restrict_restrict])
    rw [Set.ncard_coe_finset] at this
    rw [← this]
    congr 1
    ext g
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Finset.mem_coe, Place.mem_fiberOver]

  have h4 : Set.ncard {g : M ≃ₐ[F] M | toAutK (K := K) g • W₁ = W₁} =
      W₁.ramificationIndex F := by
    rw [ncard_stabilizer, inertiaDeg_eq_one, mul_one]
  obtain ⟨W, hW⟩ := Place.exists_restrict_eq (M := M) q
  have h5 : (q.fiberOver M).card * W.ramificationIndex F' = Nat.card (M ≃ₐ[F'] M) := by
    have := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg q W hW
    rwa [inertiaDeg_eq_one, mul_one, ← IsGalois.card_aut_eq_finrank] at this
  have h6 : W.ramificationIndex F = W₁.ramificationIndex F := by
    have hWv : W.restrict F = W₁.restrict F := by rw [← restrict_restrict (F' := F'), hW, hq]
    have a := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (W₁.restrict F) W hWv
    have b := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg (W₁.restrict F) W₁ rfl
    rw [inertiaDeg_eq_one, mul_one] at a b
    have hr : ((W₁.restrict F).fiberOver M).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨W₁, Place.restrict_mem_fiberOver W₁⟩
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr) (a.trans b.symm)
  have h7 : W.ramificationIndex F = W.ramificationIndex F' * q.ramificationIndex F := by
    rw [ramificationIndex_tower (F' := F'), hW]

  have hpos : 0 < (q.fiberOver M).card * W.ramificationIndex F' :=
    Nat.pos_of_ne_zero (mul_ne_zero (Finset.card_ne_zero.mpr ⟨W, (Place.mem_fiberOver _).mpr hW⟩)
      (W.ramificationIndex_pos (F := F')).ne')
  have key : (q.fiberOver M).card * W.ramificationIndex F' * p.ncard =
      (q.fiberOver M).card * W.ramificationIndex F' * q.ramificationIndex F := by
    calc (q.fiberOver M).card * W.ramificationIndex F' * p.ncard
        = Nat.card (M ≃ₐ[F'] M) * p.ncard := by rw [h5]
      _ = W₁.ramificationIndex F * (q.fiberOver M).card := by rw [← h1, h2', h3, h4]
      _ = (q.fiberOver M).card * W.ramificationIndex F' * q.ramificationIndex F := by
          rw [← h6, h7]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos key

end Core

theorem fg_of_finite {K F M : Type*} [Field K] [Field F] [Field M] [Algebra K F] [Algebra K M]
    [Algebra F M] [IsScalarTower K F M] [Module.Finite F M] {x : F} (hx : Transcendental K x)
    (hfinx : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Transcendental K (algebraMap F M x) ∧
      FiniteDimensional (IntermediateField.adjoin K ({algebraMap F M x} : Set M)) M := by
  let χ : F →ₐ[K] M := IsScalarTower.toAlgHom K F M
  have hχ : ∀ y, χ y = algebraMap F M y := fun _ => rfl
  have hinj : Function.Injective χ := χ.toRingHom.injective
  refine ⟨fun h => hx ((isAlgebraic_algHom_iff χ hinj).mp h), ?_⟩
  let Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  haveI : FiniteDimensional Kx F := hfinx
  haveI : IsScalarTower Kx F M := inferInstance
  haveI : Module.Finite Kx M := Module.Finite.trans F M
  let L : IntermediateField K M := IntermediateField.adjoin K ({algebraMap F M x} : Set M)
  have hmap : ∀ y ∈ IntermediateField.adjoin K ({x} : Set F), χ y ∈ L := by
    intro y hy
    have h1 : χ y ∈ (IntermediateField.adjoin K ({x} : Set F)).map χ := ⟨y, hy, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at h1
  have hmem : ∀ c : Kx, χ (c : F) ∈ L := fun c => hmap c c.2
  letI : Algebra Kx L :=
    (((χ : F →+* M).comp (algebraMap Kx F)).codRestrict L fun c => hmem c).toAlgebra
  haveI : IsScalarTower Kx L M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite Kx L M

end SpecialisationCount

namespace Place

/-- **The count of `K`-embeddings above a place is the ramification index.** Statement
from
`Theorems/Thm_AlgebraicCurve_Place_ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong.lean`;
proof after the pin's `S_` file. -/
theorem ncard_algHom_comp_eq_preimage_eq_ramificationIndexAlong
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [IsCurveOver K F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (E : Type*) [Field E] [Algebra K E] [IsAlgClosed E]
    (A : ValuationSubring E) (e : F →ₐ[K] E) (v₀ : Place K F)
    (hev₀ : ∀ f : F, f ∈ v₀.toValuationSubring ↔ e f ∈ A)
    (q : Place K F') (hq : q.restrictAlong φ hφ = v₀) :
    Set.ncard {σ : F' →ₐ[K] E | σ.comp φ = e ∧
        ∀ g : F', g ∈ q.toValuationSubring ↔ σ g ∈ A} =
      q.ramificationIndexAlong φ := by

  letI : Algebra F F' := algebraAlong φ
  haveI : IsScalarTower K F F' := isScalarTower_along φ
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsIntegral F F' := isIntegral_along φ hφ
  letI : Algebra F E := e.toRingHom.toAlgebra
  haveI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun k => (e.commutes k).symm
  have hq' : q.restrict F = v₀ := hq
  change _ = q.ramificationIndex F

  have hset : {σ : F' →ₐ[K] E | σ.comp φ = e ∧ ∀ g : F', g ∈ q.toValuationSubring ↔ σ g ∈ A} =
      (fun τ : F' →ₐ[F] E => τ.restrictScalars K) ''
        {τ | ∀ g : F', g ∈ q.toValuationSubring ↔ τ g ∈ A} := by
    ext σ
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨hσ, hP⟩
      refine ⟨{ (σ : F' →+* E) with commutes' := fun x => ?_ }, hP, ?_⟩
      · change σ (φ x) = e x
        rw [← hσ]
        rfl
      · ext y
        rfl
    · rintro ⟨τ, hτ, rfl⟩
      refine ⟨?_, hτ⟩
      ext x
      change τ (algebraMap F F' x) = algebraMap F E x
      exact τ.commutes x
  rw [hset, Set.ncard_image_of_injective _ (AlgHom.restrictScalars_injective K)]

  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let L := AlgebraicClosure F'
  letI : Algebra F L := inferInstance
  haveI : IsScalarTower F F' L := inferInstance
  haveI : IsScalarTower K F' L := inferInstance
  haveI : IsScalarTower K F L := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K F' L, IsScalarTower.algebraMap_apply F F' L,
      ← IsScalarTower.algebraMap_apply K F F']
  let M := IntermediateField.normalClosure F F' L
  letI : Algebra F' M := inferInstance
  haveI : IsScalarTower F F' M := inferInstance
  haveI : FiniteDimensional F M := inferInstance
  letI : Algebra K M := inferInstance
  haveI : IsScalarTower K F M := inferInstance
  haveI : Algebra.IsAlgebraic F L := Algebra.IsAlgebraic.trans F F' L
  haveI : IsAlgClosure F L := ⟨inferInstance, inferInstance⟩
  haveI : Normal F M := inferInstance
  haveI : IsGalois F M := IsGalois.mk
  haveI : IsScalarTower K F' M := IsScalarTower.of_algebraMap_eq fun x => by
    apply Subtype.ext
    change algebraMap K L x = algebraMap F' L (algebraMap K F' x)
    exact IsScalarTower.algebraMap_apply K F' L x

  obtain ⟨x, hx, hfinx⟩ := hfg
  obtain ⟨hy, hfiny⟩ := SpecialisationCount.fg_of_finite (M := M) hx hfinx
  haveI := hfiny
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  haveI : IsCurveOver K M := by
    haveI : Algebra.IsSeparable
        (IntermediateField.adjoin K ({algebraMap F M x} : Set M)) M :=
      Algebra.IsSeparable.of_integral _ _
    exact isCurveOver_of_transcendental_of_isSeparable K M _ hy hfiny inferInstance

  haveI : Algebra.IsAlgebraic F M := Algebra.IsAlgebraic.of_finite F M
  let ι : M →ₐ[F] E := IsAlgClosed.lift
  have hwK : ∀ a : K, ι.toRingHom (algebraMap K M a) ∈ A := by
    intro a
    rw [IsScalarTower.algebraMap_apply K F M, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      ι.commutes]
    exact (hev₀ _).mp (v₀.algebraMap_mem' a)
  have hwx : ∃ y : M, ι.toRingHom y ∉ A := by
    obtain ⟨f, hf⟩ : ∃ f : F, f ∉ v₀.toValuationSubring := by
      by_contra! h
      exact v₀.ne_top' (SetLike.ext fun f => ⟨fun _ => ValuationSubring.mem_top f, fun _ => h f⟩)
    refine ⟨algebraMap F M f, fun hA => hf ((hev₀ f).mpr ?_)⟩
    rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ι.commutes] at hA
  obtain ⟨W₁, hW₁⟩ :=
    Place.exists_toValuationSubring_eq_comap_ringHom (K := K) (algebraMap F M x) ι.toRingHom A
      hwK hwx
  have hW₁v : W₁.restrict F = v₀ := by
    refine Place.ext (SetLike.ext fun f => ?_)
    rw [Place.mem_restrict_iff, hW₁, ValuationSubring.mem_comap, hev₀, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, ι.commutes]
    rfl

  exact SpecialisationCount.ncard_setOf_forall_mem_iff ι A W₁ hW₁ q (hq'.trans hW₁v.symm)

section Digit

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- **The residue field of a place of a curve over an algebraically closed field has
every residue of the valuation subring lift to the constants.** Pin
`W7XChildL.exists_digit`, a helper of the constant-field-extension sum `S_` file. -/
theorem exists_digit [IsAlgClosed K] (v : Place K F) [Module.Finite K v.ResidueField]
    {π : v.toValuationSubring} (hπ : Irreducible π) (o : v.toValuationSubring) :
    ∃ a : K, ∃ o' : v.toValuationSubring, o = algebraMap K v.toValuationSubring a + π * o' := by
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K _
  have hbij : Function.Bijective (algebraMap K v.ResidueField) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨a, ha⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring o)
  have hmem : o - algebraMap K v.toValuationSubring a ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← ha,
      IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨a, b, by rw [mul_comm, hb]; ring⟩

end Digit

set_option linter.unusedVariables false in
/-- **Non-cancellation of `K'`-weighted `F`-sums at a lifted place.** Statement from
`Theorems/Thm_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension.lean`;
proof after the pin's `S_` file. -/
theorem ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (v : Place K F) {ι : Type*} (B : ι → K') (hB : LinearIndependent K B)
    (g : ι →₀ F) (hg : g ≠ 0) :
    (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≠ 0 ∧
    ∀ j ∈ g.support,
      (lift v).ord (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) ≤
        v.ord (g j) := by
  classical
  set Tot := ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j) with hTot
  have hsne : g.support.Nonempty := Finsupp.support_nonempty_iff.mpr hg
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  obtain ⟨j₁, hj₁, hj₁m⟩ := g.support.exists_mem_eq_inf' hsne (fun j => v.ord (g j))
  set m := g.support.inf' hsne (fun j => v.ord (g j)) with hm
  have hmle : ∀ j ∈ g.support, m ≤ v.ord (g j) := fun j hj => Finset.inf'_le _ hj
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπord : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hgj0 : ∀ j ∈ g.support, g j ≠ 0 := fun j hj => Finsupp.mem_support_iff.mp hj
  have haj_ne : ∀ j ∈ g.support, (π : F)^(-m) * g j ≠ 0 := fun j hj =>
    mul_ne_zero (zpow_ne_zero _ hπ0) (hgj0 j hj)
  have haj_ord : ∀ j ∈ g.support, v.ord ((π : F)^(-m) * g j) = v.ord (g j) - m := by
    intro j hj
    rw [v.ord_mul (zpow_ne_zero _ hπ0) (hgj0 j hj), v.ord_zpow, hπord]; ring
  have haj_mem : ∀ j ∈ g.support, (π : F)^(-m) * g j ∈ v.toValuationSubring := fun j hj =>
    (v.mem_iff_ord_nonneg (haj_ne j hj)).mpr (by rw [haj_ord j hj]; linarith [hmle j hj])

  have hdig : ∀ j, ∀ hj : j ∈ g.support, ∃ cj : K, ∃ o' : v.toValuationSubring,
      (⟨_, haj_mem j hj⟩ : v.toValuationSubring) =
        algebraMap K v.toValuationSubring cj + π * o' :=
    fun j hj => exists_digit v hπ ⟨_, haj_mem j hj⟩
  choose c o' hco using hdig

  have hcj1 : c j₁ hj₁ ≠ 0 := by
    intro hc0
    have heq : (π : F)^(-m) * g j₁ = (π : F) * ((o' j₁ hj₁ : v.toValuationSubring) : F) := by
      have h := congrArg (Subtype.val (p := (· ∈ v.toValuationSubring))) (hco j₁ hj₁)
      simp only [hc0, map_zero, zero_add, MulMemClass.coe_mul] at h
      exact h
    have haj1ord : v.ord ((π:F)^(-m) * g j₁) = 0 := by rw [haj_ord j₁ hj₁, ← hj₁m]; ring
    rcases eq_or_ne ((o' j₁ hj₁ : v.toValuationSubring) : F) 0 with ho0 | ho0
    · rw [heq, ho0, mul_zero] at haj1ord
      exact haj_ne j₁ hj₁ (by rw [heq, ho0, mul_zero])
    · rw [heq, v.ord_mul hπ0 ho0, hπord] at haj1ord
      have := v.ord_nonneg_of_mem (o' j₁ hj₁).2
      omega

  let c' : ι → K := fun j => if hj : j ∈ g.support then c j hj else 0
  have hc'eq : ∀ j (hj : j ∈ g.support), c' j = c j hj := fun j hj => dite_eq_left hj
  let e' : ι → F := fun j => if hj : j ∈ g.support then ((o' j hj : v.toValuationSubring) : F) else 0
  have he'eq : ∀ j (hj : j ∈ g.support), e' j = ((o' j hj : v.toValuationSubring) : F) :=
    fun j hj => dite_eq_left hj
  have he'mem : ∀ j ∈ g.support, e' j ∈ v.toValuationSubring := fun j hj =>
    (he'eq j hj) ▸ (o' j hj).2

  let d : K' := ∑ j ∈ g.support, c' j • B j
  have hd : d ≠ 0 := by
    intro hd0
    have := linearIndependent_iff'.1 hB g.support c' hd0 j₁ hj₁
    rw [hc'eq j₁ hj₁] at this
    exact hcj1 this

  have hcoe : ∀ j (hj : j ∈ g.support), (π:F)^(-m) * g j =
      algebraMap K F (c' j) + (π:F) * (e' j) := by
    intro j hj
    have h := congrArg (Subtype.val (p := (· ∈ v.toValuationSubring))) (hco j hj)
    simp only [AddMemClass.coe_add, MulMemClass.coe_mul, Place.coe_algebraMap] at h
    rw [hc'eq j hj, he'eq j hj]; exact h

  let R : F' := ∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (e' j)

  have hfact : (algebraMap F F' (π:F))^(-m) * Tot =
      algebraMap K' F' d + algebraMap F F' (π:F) * R := by
    rw [hTot, Finset.mul_sum]
    simp only [d, R, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show (algebraMap F F' (π:F))^(-m) * (algebraMap K' F' (B j) * algebraMap F F' (g j))
        = algebraMap K' F' (B j) * algebraMap F F' ((π:F)^(-m) * g j) by
      rw [map_mul, ← map_zpow₀]; ring]
    rw [hcoe j hj, map_add, map_mul, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply K K' F', ← IsScalarTower.algebraMap_apply K F F']
    ring

  have hφπ0 : algebraMap F F' (π:F) ≠ 0 := by
    simpa using (algebraMap F F').injective.ne hπ0
  have hφπord : (lift v).ord (algebraMap F F' (π:F)) = 1 := by rw [hlift_ord]; exact hπord
  have hRmem : R ∈ (lift v).toValuationSubring := by
    refine Subring.sum_mem _ fun j hj => mul_mem ((lift v).algebraMap_mem' _) ?_
    rcases eq_or_ne (e' j) 0 with h0 | h0
    · rw [h0, map_zero]; exact zero_mem _
    · refine ((lift v).mem_iff_ord_nonneg ?_).mpr ?_
      · simpa using (algebraMap F F').injective.ne h0
      · rw [hlift_ord]; exact v.ord_nonneg_of_mem (he'mem j hj)
  have hd' : algebraMap K' F' d ≠ 0 := by
    simpa using (algebraMap K' F').injective.ne hd
  have hdord : (lift v).ord (algebraMap K' F' d) = 0 := by
    have h1 := (lift v).ord_nonneg_of_mem ((lift v).algebraMap_mem' d)
    have h2 := (lift v).ord_nonneg_of_mem ((lift v).algebraMap_mem' d⁻¹)
    rw [map_inv₀, (lift v).ord_inv] at h2; omega
  set S := algebraMap K' F' d + algebraMap F F' (π:F) * R with hS
  have hSmem : S ∈ (lift v).toValuationSubring :=
    add_mem ((lift v).algebraMap_mem' d)
      (mul_mem (((lift v).mem_iff_ord_nonneg hφπ0).mpr (by omega)) hRmem)

  have hSne : S ≠ 0 := by
    intro h0
    have heq : (algebraMap F F' (π:F))⁻¹ * algebraMap K' F' d = -R := by
      have h1 : algebraMap K' F' d = -(algebraMap F F' (π:F) * R) := by
        rw [eq_neg_iff_add_eq_zero]; exact hS ▸ h0
      rw [h1, mul_neg, ← mul_assoc, inv_mul_cancel₀ hφπ0, one_mul]
    have hmem : (algebraMap F F' (π:F))⁻¹ * algebraMap K' F' d ∈ (lift v).toValuationSubring := by
      rw [heq]; exact neg_mem hRmem
    have := (lift v).ord_nonneg_of_mem hmem
    rw [(lift v).ord_mul (inv_ne_zero hφπ0) hd', (lift v).ord_inv, hφπord, hdord] at this
    omega

  have hSord : (lift v).ord S = 0 := by
    have hge := (lift v).ord_nonneg_of_mem hSmem
    by_contra hne
    have hSge1 : 1 ≤ (lift v).ord S := by omega
    have hπinvS : (algebraMap F F' (π:F))⁻¹ * S ∈ (lift v).toValuationSubring := by
      refine ((lift v).mem_iff_ord_nonneg (mul_ne_zero (inv_ne_zero hφπ0) hSne)).mpr ?_
      rw [(lift v).ord_mul (inv_ne_zero hφπ0) hSne, (lift v).ord_inv, hφπord]; omega
    have hπinvd : (algebraMap F F' (π:F))⁻¹ * algebraMap K' F' d
        ∈ (lift v).toValuationSubring := by
      have heq : (algebraMap F F' (π:F))⁻¹ * algebraMap K' F' d =
          (algebraMap F F' (π:F))⁻¹ * S - R := by
        rw [hS]; field_simp; ring
      rw [heq]; exact sub_mem hπinvS hRmem
    have := (lift v).ord_nonneg_of_mem hπinvd
    rw [(lift v).ord_mul (inv_ne_zero hφπ0) hd', (lift v).ord_inv, hφπord, hdord] at this
    omega

  have hTotne : Tot ≠ 0 := fun h0 => hSne (by rw [← hfact, h0, mul_zero])
  have hTotord : (lift v).ord Tot = m := by
    have h := hSord
    rw [← hfact, (lift v).ord_mul (zpow_ne_zero _ hφπ0) hTotne,
      (lift v).ord_zpow, hφπord] at h
    linarith
  exact ⟨hTotne, fun j hj => hTotord ▸ hmle j hj⟩

end Place

end AlgebraicCurve
