/-
  The type-reproducer engine of the archimedean approximate identity.

  This is the generic representation-theoretic movement `Q3` behind
  `AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`:
  the product representation `piRep` and its coefficient maps
  `coeffFun`/`dualCoeffFun`, the translate representation `transRep`, the right-translate
  span `rt`/`spanTranslates` and the finite-dimensional stable envelope
  `exists_finiteDimensional_stable`, then the positivity engine
  `piE`/`Pm`/`Mint`/`Hm`/`Dm`/`exists_reproducer` that realizes `1` in the span of the
  integrated projections, and the `iSup`-membership tail
  (`Pm_entry_mem_iSup`, `reproducer_mem_iSup_dual`, `reproducer_inv_mem_iSup`).

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:926–2209`
  (pinned `aa2d8b3`), the `TypePiece`…`MultiPlace` and `Delta`/`Mint`/`ZetaB0`
  sections. It mentions neither the adèles nor `GL₂`: everything is stated over the
  abstract compact group `Kc` and the abstract group `G` the pin uses. The pin
  declares the whole engine `private`; here it is the shared engine and is public,
  so the statements are verbatim and every declaration lands as a promotion. The
  pin's `p2m_reactivate` lines are not transcribed.
-/
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Q09

open AutomorphicForm

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

-- pin: exists_out_mul_eq (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:939)
theorem exists_out_mul_eq (ι : H →* G) (x : G) :
    ∃ k : H, (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range x
  obtain ⟨k, hk⟩ := h.2
  exact ⟨k⁻¹, by rw [map_inv, hh, ← hk, mul_inv_cancel_right]⟩

-- pin: cosetCoord (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:945)
noncomputable def cosetCoord (ι : H →* G) (x : G) : H :=
  (exists_out_mul_eq ι x).choose

-- pin: out_mul_cosetCoord (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:948)
theorem out_mul_cosetCoord (ι : H →* G) (x : G) :
    (QuotientGroup.mk x : G ⧸ ι.range).out * ι (cosetCoord ι x) = x :=
  (exists_out_mul_eq ι x).choose_spec

-- pin: cosetCoord_unique (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:952)
theorem cosetCoord_unique {ι : H →* G} (hι : Function.Injective ι) {x : G} {k : H}
    (hk : (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x) : k = cosetCoord ι x :=
  hι (mul_left_cancel (hk.trans (out_mul_cosetCoord ι x).symm))

-- pin: cosetCoord_mul (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:956)
theorem cosetCoord_mul {ι : H →* G} (hι : Function.Injective ι) (x : G) (k : H) :
    cosetCoord ι (x * ι k) = cosetCoord ι x * k := by
  symm
  apply cosetCoord_unique hι
  have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  rw [hmk, map_mul, ← mul_assoc, out_mul_cosetCoord]

-- pin: mem_typeSubmodule_of_isRightEquivariantOn (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:965)
theorem mem_typeSubmodule_of_isRightEquivariantOn {ι : H →* G} (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ (k : H), ∀ v ∈ P, ρ k v ∈ P)
    (S : P →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : P) (x : G), S ⟨ρ k v, hP k v v.2⟩ x = S v (x * ι k)) (v : P) :
    S v ∈ AutomorphicForm.typeSubmodule ι ρ := by
  classical

  let ℓ : G ⧸ ι.range → (P →ₗ[ℂ] ℂ) := fun c =>
    { toFun := fun p => S p c.out
      map_add' := fun p q => by rw [map_add]; rfl
      map_smul' := fun a p => by rw [map_smul]; rfl }
  have hext : ∀ c, ∃ g : W →ₗ[ℂ] ℂ, g.comp P.subtype = ℓ c := fun c => LinearMap.exists_extend (ℓ c)
  let ℓ' : G ⧸ ι.range → (W →ₗ[ℂ] ℂ) := fun c => (hext c).choose
  have hℓ' : ∀ c (p : P), ℓ' c (p : W) = S p c.out := fun c p => by
    have := LinearMap.congr_fun (hext c).choose_spec p
    simpa [ℓ] using this

  let T : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) w)
      map_add' := fun w₁ w₂ => funext fun x => by simp only [map_add, Pi.add_apply]
      map_smul' := fun a w => funext fun x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hT : AutomorphicForm.IsRightEquivariant ι ρ T := by
    intro k w x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (ρ k w)) =
      ℓ' (QuotientGroup.mk (x * ι k)) (ρ (cosetCoord ι (x * ι k)) w)
    have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
      rw [QuotientGroup.eq]
      exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
    rw [hmk, cosetCoord_mul hι, map_mul]
    rfl
  have hTS : T (v : W) = S v := by
    funext x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (v : W)) = S v x
    have hmem : ρ (cosetCoord ι x) (v : W) ∈ P := hP _ _ v.2
    have h1 := hℓ' (QuotientGroup.mk x) ⟨_, hmem⟩
    simp only at h1
    rw [h1, hS (cosetCoord ι x) v, out_mul_cosetCoord]
  rw [← hTS]
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hT _

end TypePiece

section PiRep

variable {H : Type*} [Group H]
variable {A : Type*} {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]

-- pin: piRep (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1014)
def piRep (ρ : ∀ a, Representation ℂ H (W a)) : Representation ℂ H (∀ a, W a) where
  toFun k := LinearMap.pi fun a => (ρ a k).comp (LinearMap.proj a)
  map_one' := by
    ext v a
    simp
  map_mul' k₁ k₂ := by
    ext v a
    simp

-- pin: piRep_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1023)
theorem piRep_apply (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    piRep ρ k v a = ρ a k (v a) :=
  rfl

-- pin: piRep_single (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1027)
theorem piRep_single [DecidableEq A] (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (a : A)
    (v : W a) : piRep ρ k (Pi.single a v) = Pi.single a (ρ a k v) := by
  funext b
  rw [piRep_apply]
  by_cases hb : b = a
  · subst hb
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hb, map_zero]

end PiRep

section Transport

variable {H G : Type*} [Group H] [Group G]

-- pin: typeSubmodule_piRep_le (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1043)
theorem typeSubmodule_piRep_le {A : Type*} [Fintype A] [DecidableEq A] {W : A → Type*}
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] (ι : H →* G)
    (ρ : ∀ a, Representation ℂ H (W a)) :
    typeSubmodule ι (piRep ρ) ≤ ⨆ a, typeSubmodule ι (ρ a) := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, v, rfl⟩
  show T v ∈ ⨆ a, typeSubmodule ι (ρ a)
  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ?_
  have hTa : IsRightEquivariant ι (ρ a) (T.comp (LinearMap.single ℂ W a)) := by
    intro k w x
    show T (Pi.single a (ρ a k w)) x = T (Pi.single a w) (x * ι k)
    rw [← piRep_single]
    exact hT k (Pi.single a w) x
  exact mem_typeSubmodule_of_isRightEquivariant hTa (v a)

-- pin: mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1059)
theorem mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi {A : Type*} [Fintype A] [DecidableEq A]
    {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] {ι : H →* G}
    (hι : Function.Injective ι) (ρ : ∀ a, Representation ℂ H (W a)) (Q : Submodule ℂ (∀ a, W a))
    (hQ : ∀ (k : H), ∀ v ∈ Q, piRep ρ k v ∈ Q) (S : Q →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : Q) (x : G), S ⟨piRep ρ k v, hQ k v v.2⟩ x = S v (x * ι k)) (v : Q) :
    S v ∈ ⨆ a, typeSubmodule ι (ρ a) :=
  typeSubmodule_piRep_le ι ρ (mem_typeSubmodule_of_isRightEquivariantOn hι (piRep ρ) Q hQ S hS v)

-- pin: exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1067)
theorem exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) {θ : G → ℂ} (hθ : θ ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ θ ∈ LinearMap.range Φ := by
  classical
  have h1 : θ ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hθ
  obtain ⟨t, ht, hθt⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hgen : ∀ f : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (f : G → ℂ) ∈ LinearMap.range T := fun f => by
    have hf := ht f.2
    rw [Set.mem_iUnion] at hf
    obtain ⟨j, T, hT, hfT⟩ := hf
    exact ⟨j, T, hT, hfT⟩
  choose i T hT hfT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · refine (Submodule.span_le.mpr ?_) hθt
    intro f hf
    obtain ⟨v, hv⟩ := hfT ⟨f, hf⟩
    refine ⟨Pi.single (⟨f, hf⟩ : t) v, ?_⟩
    rw [hΦ, Finset.sum_eq_single (⟨f, hf⟩ : t)]
    · rw [Pi.single_eq_same]
      exact hv
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

-- pin: mem_iSup_typeSubmodule_of_intertwines (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1105)
theorem mem_iSup_typeSubmodule_of_intertwines {G' : Type*} [Group G'] {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G) {ι' : H →* G'}
    (hι' : Function.Injective ι') (ρ : ∀ j, Representation ℂ H (W j)) (P₀ : Submodule ℂ (G → ℂ))
    (hP₀ : ∀ (k : H), ∀ θ ∈ P₀, (fun x => θ (x * ι k)) ∈ P₀) (A : P₀ →ₗ[ℂ] (G' → ℂ))
    (hA : ∀ (k : H) (θ : P₀) (y : G'), A ⟨fun x => (θ : G → ℂ) (x * ι k), hP₀ k θ θ.2⟩ y =
      A θ (y * ι' k))
    (θ : P₀) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    A θ ∈ ⨆ j, typeSubmodule ι' (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, v, hv⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule ι ρ hθ
  have hQ : ∀ (k : H), ∀ w ∈ P₀.comap Φ, piRep (fun a => ρ (i a)) k w ∈ P₀.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι k) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hP₀ k _ hw
  let ΦQ : P₀.comap Φ →ₗ[ℂ] P₀ :=
    LinearMap.codRestrict P₀ (Φ.comp (P₀.comap Φ).subtype) fun w => w.2
  have hΦQ : ∀ w : P₀.comap Φ, ((ΦQ w : P₀) : G → ℂ) = Φ (w : ∀ a : t, W (i a)) := fun _ => rfl
  let S : P₀.comap Φ →ₗ[ℂ] (G' → ℂ) := A.comp ΦQ
  have hS : ∀ (k : H) (w : P₀.comap Φ) (y : G'),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ y = S w (y * ι' k) := by
    intro k w y
    have h1 : ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ =
        ⟨fun x => ((ΦQ w : P₀) : G → ℂ) (x * ι k), hP₀ k _ (ΦQ w).2⟩ := by
      apply Subtype.ext
      funext x
      exact hΦ k w x
    show A (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩) y = A (ΦQ w) (y * ι' k)
    rw [h1]
    exact hA k (ΦQ w) y
  have hv' : v ∈ P₀.comap Φ := by
    rw [Submodule.mem_comap, hv]
    exact θ.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hι' (fun a => ρ (i a)) (P₀.comap Φ)
    hQ S hS ⟨v, hv'⟩
  have hSv : S ⟨v, hv'⟩ = A θ := by
    show A (ΦQ ⟨v, hv'⟩) = A θ
    congr 1
    exact Subtype.ext hv
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule ι' (ρ j)) (i a)) hmem

end Transport

section Coeff

variable {Kc : Type*} [Group Kc]
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

-- pin: coeffFun (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1158)
def coeffFun (π : Representation ℂ Kc E) (lam : Module.Dual ℂ E) : E →ₗ[ℂ] (Kc → ℂ) where
  toFun v κ := lam (π κ v)
  map_add' v w := funext fun κ => by simp only [map_add, Pi.add_apply]
  map_smul' a v := funext fun κ => by simp only [map_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]

-- pin: coeffFun_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1163)
theorem coeffFun_apply (π : Representation ℂ Kc E) (lam : Module.Dual ℂ E) (v : E) (κ : Kc) :
    coeffFun π lam v κ = lam (π κ v) :=
  rfl

-- pin: isRightEquivariant_coeffFun (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1167)
theorem isRightEquivariant_coeffFun (π : Representation ℂ Kc E) (lam : Module.Dual ℂ E) :
    IsRightEquivariant (MonoidHom.id Kc) π (coeffFun π lam) := by
  intro k v κ
  show lam (π κ (π k v)) = lam (π (κ * k) v)
  rw [map_mul]
  rfl

-- pin: dualCoeffFun (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1174)
def dualCoeffFun (π : Representation ℂ Kc E) (v : E) : Module.Dual ℂ E →ₗ[ℂ] (Kc → ℂ) where
  toFun lam κ := lam (π κ⁻¹ v)
  map_add' l m := funext fun κ => by simp only [LinearMap.add_apply, Pi.add_apply]
  map_smul' a l := funext fun κ => by
    simp only [LinearMap.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply]

-- pin: dualCoeffFun_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1180)
theorem dualCoeffFun_apply (π : Representation ℂ Kc E) (v : E) (lam : Module.Dual ℂ E) (κ : Kc) :
    dualCoeffFun π v lam κ = lam (π κ⁻¹ v) :=
  rfl

-- pin: isRightEquivariant_dualCoeffFun (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1184)
theorem isRightEquivariant_dualCoeffFun (π : Representation ℂ Kc E) (v : E) :
    IsRightEquivariant (MonoidHom.id Kc) π.dual (dualCoeffFun π v) := by
  intro k lam κ
  show (π.dual k lam) (π κ⁻¹ v) = lam (π (κ * k)⁻¹ v)
  rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, mul_inv_rev, map_mul]
  rfl

end Coeff

section LeftTypes

variable {Kw Kc G : Type*} [Group Kw] [Group Kc] [Group G]

-- pin: transRep (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1198)
def transRep (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
    (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E) : Representation ℂ Kc E where
  toFun κ :=
    { toFun := fun v => ⟨fun x => (v : G → ℂ) (x * ι κ), hE κ v v.2⟩
      map_add' := fun v w => by ext x; rfl
      map_smul' := fun c v => by ext x; rfl }
  map_one' := by
    ext v x
    show (v : G → ℂ) (x * ι 1) = (v : G → ℂ) x
    rw [map_one, mul_one]
  map_mul' κ κ' := by
    ext v x
    show (v : G → ℂ) (x * ι (κ * κ')) = (v : G → ℂ) (x * ι κ * ι κ')
    rw [map_mul, mul_assoc]

-- pin: transRep_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1213)
theorem transRep_apply (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
    (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E) (κ : Kc) (v : E) (x : G) :
    ((transRep ι E hE κ v : E) : G → ℂ) x = (v : G → ℂ) (x * ι κ) :=
  rfl

-- pin: coeffFun_transRep_mem_iSup (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1218)
theorem coeffFun_transRep_mem_iSup {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] {incl : Kw →* Kc} (hincl : Function.Injective incl) (ι : Kc →* G)
    (ρ : ∀ j, Representation ℂ Kw (W j)) (E : Submodule ℂ (G → ℂ))
    (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)
    (hEcut : ∀ v ∈ E, v ∈ ⨆ j, typeSubmodule (ι.comp incl) (ρ j))
    (lam : Module.Dual ℂ E) (v : E) :
    coeffFun (transRep ι E hE) lam v ∈ ⨆ j, typeSubmodule incl (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, m, hm⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule (ι.comp incl) ρ (hEcut v v.2)
  have hQ : ∀ (k : Kw), ∀ w ∈ E.comap Φ, piRep (fun a => ρ (i a)) k w ∈ E.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι (incl k)) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hE (incl k) _ hw
  let ΦQ : E.comap Φ →ₗ[ℂ] E := LinearMap.codRestrict E (Φ.comp (E.comap Φ).subtype) fun w => w.2
  let S : E.comap Φ →ₗ[ℂ] (Kc → ℂ) := (coeffFun (transRep ι E hE) lam).comp ΦQ
  have hS : ∀ (k : Kw) (w : E.comap Φ) (κ : Kc),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ κ = S w (κ * incl k) := by
    intro k w κ
    show lam (transRep ι E hE κ (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩)) =
      lam (transRep ι E hE (κ * incl k) (ΦQ w))
    congr 1
    apply Subtype.ext
    funext x
    show Φ (piRep (fun a => ρ (i a)) k w) (x * ι κ) = Φ (w : ∀ a : t, W (i a)) (x * ι (κ * incl k))
    rw [hΦ k w, map_mul, mul_assoc]
    rfl
  have hm' : m ∈ E.comap Φ := by
    rw [Submodule.mem_comap, hm]
    exact v.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hincl (fun a => ρ (i a)) (E.comap Φ)
    hQ S hS ⟨m, hm'⟩
  have hSv : S ⟨m, hm'⟩ = coeffFun (transRep ι E hE) lam v := by
    show coeffFun (transRep ι E hE) lam (ΦQ ⟨m, hm'⟩) = coeffFun (transRep ι E hE) lam v
    congr 1
    exact Subtype.ext hm
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule incl (ρ j)) (i a)) hmem

end LeftTypes

section DualTypes

variable {Kw Kc G : Type*} [Group Kw] [Group Kc] [Group G]

-- pin: exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1267)
theorem exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule {H : Type*} [Group H] {J : Type*}
    {W : J → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) (P : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ P]
    (hP : P ≤ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ P ≤ LinearMap.range Φ := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional P).mpr inferInstance
  have hgenset : ∀ f ∈ s, f ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    intro f hf
    rw [Submodule.span_iUnion]
    exact hP (hs ▸ Submodule.subset_span hf)
  choose tf htf hftf using fun f : s => Submodule.mem_span_finite_of_mem_span (hgenset f f.2)
  let t : Finset (G → ℂ) := Finset.univ.biUnion tf
  have ht : ↑t ⊆ ⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T} := by
    intro g hg
    obtain ⟨f, -, hgf⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hg)
    exact htf f hgf
  have hgen : ∀ g : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (g : G → ℂ) ∈ LinearMap.range T := fun g => by
    have hg := ht g.2
    rw [Set.mem_iUnion] at hg
    obtain ⟨j, T, hT, hgT⟩ := hg
    exact ⟨j, T, hT, hgT⟩
  choose i T hT hgT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · have hspan : Submodule.span ℂ (↑t : Set (G → ℂ)) ≤ LinearMap.range Φ := by
      refine Submodule.span_le.mpr ?_
      intro g hg
      obtain ⟨v, hv⟩ := hgT ⟨g, hg⟩
      refine ⟨Pi.single (⟨g, hg⟩ : t) v, ?_⟩
      rw [hΦ, Finset.sum_eq_single (⟨g, hg⟩ : t)]
      · rw [Pi.single_eq_same]
        exact hv
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, map_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [← hs]
    refine Submodule.span_le.mpr fun f hf => hspan ?_
    have hsub : ↑(tf ⟨f, hf⟩) ⊆ (↑t : Set (G → ℂ)) := fun g hg =>
      Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨⟨f, hf⟩, Finset.mem_univ _, hg⟩)
    exact Submodule.span_mono hsub (hftf ⟨f, hf⟩)

-- pin: dualCoeffFun_transRep_mem_iSup (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1320)
theorem dualCoeffFun_transRep_mem_iSup {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] {incl : Kw →* Kc} (hincl : Function.Injective incl) (ι : Kc →* G)
    (ρ : ∀ j, Representation ℂ Kw (W j)) (E : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ E]
    (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)
    (hEcut : ∀ v ∈ E, v ∈ ⨆ j, typeSubmodule (ι.comp incl) (ρ j))
    (v : E) (lam : Module.Dual ℂ E) :
    dualCoeffFun (transRep ι E hE) v lam ∈ ⨆ j, typeSubmodule incl (ρ j).dual := by
  classical
  obtain ⟨t, i, Φ, hΦ, hEΦ⟩ :=
    exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule (ι.comp incl) ρ E hEcut

  have hQ : ∀ (k : Kw), ∀ w ∈ E.comap Φ, piRep (fun a => ρ (i a)) k w ∈ E.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι (incl k)) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hE (incl k) _ hw
  let π : Representation ℂ Kc E := transRep ι E hE
  let Q : Submodule ℂ (∀ a : t, W (i a)) := E.comap Φ
  let q : Q →ₗ[ℂ] E := LinearMap.codRestrict E (Φ.comp Q.subtype) fun w => w.2
  have hq : ∀ (k : Kw) (w : Q), q ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ = π (incl k) (q w) := by
    intro k w
    apply Subtype.ext
    funext x
    show Φ (piRep (fun a => ρ (i a)) k w) x = Φ (w : ∀ a : t, W (i a)) (x * ι (incl k))
    exact hΦ k w x
  have hqsurj : Function.Surjective q := by
    intro e
    obtain ⟨m, hm⟩ := hEΦ e.2
    exact ⟨⟨m, by rw [Submodule.mem_comap, hm]; exact e.2⟩, Subtype.ext hm⟩
  have hqinj : Function.Injective q.dualMap := LinearMap.dualMap_injective_of_surjective hqsurj

  let glue : (∀ a : t, Module.Dual ℂ (W (i a))) ≃ₗ[ℂ] Module.Dual ℂ (∀ a : t, W (i a)) :=
    LinearMap.lsum ℂ (fun a : t => W (i a)) ℂ
  have hglue : ∀ (ν : ∀ a : t, Module.Dual ℂ (W (i a))) (m : ∀ a : t, W (i a)),
      glue ν m = ∑ a : t, ν a (m a) := fun ν m => by
    simp only [glue, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  let r : Module.Dual ℂ (∀ a : t, W (i a)) →ₗ[ℂ] Module.Dual ℂ Q := Q.subtype.dualMap
  have hrsurj : Function.Surjective r := LinearMap.dualMap_surjective_of_injective Q.injective_subtype

  let S' : Submodule ℂ (∀ a : t, Module.Dual ℂ (W (i a))) :=
    (LinearMap.range q.dualMap).comap (r.comp glue.toLinearMap)
  have hS'mem : ∀ ν : ∀ a : t, Module.Dual ℂ (W (i a)),
      ν ∈ S' ↔ ∃ l : Module.Dual ℂ E, ∀ w : Q, glue ν (w : ∀ a : t, W (i a)) = l (q w) := by
    intro ν
    simp only [S', Submodule.mem_comap, LinearMap.mem_range, LinearMap.comp_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨l, fun w => ?_⟩
      have := LinearMap.congr_fun hl w
      rw [LinearMap.dualMap_apply] at this
      rw [this]
      rfl
    · rintro ⟨l, hl⟩
      refine ⟨l, LinearMap.ext fun w => ?_⟩
      rw [LinearMap.dualMap_apply]
      exact (hl w).symm

  have hpi : ∀ (k : Kw) (ν : ∀ a : t, Module.Dual ℂ (W (i a))) (m : ∀ a : t, W (i a)),
      glue (piRep (fun a => (ρ (i a)).dual) k ν) m = glue ν (piRep (fun a => ρ (i a)) k⁻¹ m) := by
    intro k ν m
    rw [hglue, hglue]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [piRep_apply, piRep_apply, Representation.dual_apply, Module.Dual.transpose_apply,
      LinearMap.comp_apply]
  have hS' : ∀ (k : Kw), ∀ ν ∈ S', piRep (fun a => (ρ (i a)).dual) k ν ∈ S' := by
    intro k ν hν
    obtain ⟨l, hl⟩ := (hS'mem ν).mp hν
    refine (hS'mem _).mpr ⟨π.dual (incl k) l, fun w => ?_⟩
    have hw : piRep (fun a => ρ (i a)) k⁻¹ (w : ∀ a : t, W (i a)) ∈ Q := hQ k⁻¹ _ w.2
    rw [hpi, hl ⟨_, hw⟩, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
      ← map_inv, hq k⁻¹ w]

  have hσex : ∀ ν : S', ∃! l : Module.Dual ℂ E, ∀ w : Q, glue (ν : ∀ a, _) (w : ∀ a : t, W (i a)) = l (q w) := by
    intro ν
    obtain ⟨l, hl⟩ := (hS'mem ν).mp ν.2
    refine ⟨l, hl, fun l' hl' => ?_⟩
    apply hqinj
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply, ← hl w, ← hl' w]
  choose σf hσf hσu using hσex
  let σ : S' →ₗ[ℂ] Module.Dual ℂ E :=
    { toFun := σf
      map_add' := fun ν₁ ν₂ => by
        symm
        apply hσu
        intro w
        rw [LinearMap.add_apply, ← hσf ν₁ w, ← hσf ν₂ w, Submodule.coe_add, map_add, LinearMap.add_apply]
      map_smul' := fun c ν => by
        symm
        apply hσu
        intro w
        rw [RingHom.id_apply, LinearMap.smul_apply, ← hσf ν w, Submodule.coe_smul, map_smul,
          LinearMap.smul_apply] }
  have hσ : ∀ (ν : S') (w : Q), glue (ν : ∀ a, _) (w : ∀ a : t, W (i a)) = σ ν (q w) := hσf
  have hσeq : ∀ (k : Kw) (ν : S'), σ ⟨piRep (fun a => (ρ (i a)).dual) k ν, hS' k ν ν.2⟩ = π.dual (incl k) (σ ν) := by
    intro k ν
    refine (hσu ⟨_, hS' k ν ν.2⟩ _ fun w => ?_).symm
    have hw : piRep (fun a => ρ (i a)) k⁻¹ (w : ∀ a : t, W (i a)) ∈ Q := hQ k⁻¹ _ w.2
    show glue (piRep (fun a => (ρ (i a)).dual) k (ν : ∀ a, _)) (w : ∀ a : t, W (i a)) = _
    rw [hpi, hσ ν ⟨_, hw⟩, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
      ← map_inv, hq k⁻¹ w]

  let S : S' →ₗ[ℂ] (Kc → ℂ) := (dualCoeffFun π v).comp σ
  have hS : ∀ (k : Kw) (ν : S') (κ : Kc),
      S ⟨piRep (fun a => (ρ (i a)).dual) k ν, hS' k ν ν.2⟩ κ = S ν (κ * incl k) := by
    intro k ν κ
    show dualCoeffFun π v (σ ⟨piRep (fun a => (ρ (i a)).dual) k ν, hS' k ν ν.2⟩) κ =
      dualCoeffFun π v (σ ν) (κ * incl k)
    rw [hσeq]
    exact isRightEquivariant_dualCoeffFun π v (incl k) (σ ν) κ

  obtain ⟨μ, hμ⟩ := hrsurj (q.dualMap lam)
  have hν₀ : glue.symm μ ∈ S' := by
    refine (hS'mem _).mpr ⟨lam, fun w => ?_⟩
    rw [LinearEquiv.apply_symm_apply]
    have := LinearMap.congr_fun hμ w
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply] at this
    exact this
  have hlam : σ ⟨glue.symm μ, hν₀⟩ = lam := by
    symm
    apply hσu
    intro w
    show glue (glue.symm μ) (w : ∀ a : t, W (i a)) = lam (q w)
    rw [LinearEquiv.apply_symm_apply]
    have := LinearMap.congr_fun hμ w
    rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply] at this
    exact this
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hincl (fun a => (ρ (i a)).dual) S' hS' S hS
    ⟨glue.symm μ, hν₀⟩
  have hSv : S ⟨glue.symm μ, hν₀⟩ = dualCoeffFun π v lam := by
    show dualCoeffFun π v (σ ⟨glue.symm μ, hν₀⟩) = dualCoeffFun π v lam
    rw [hlam]
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule incl (ρ j).dual) (i a)) hmem

end DualTypes

section SpanTranslates

variable {H G : Type*} [Group H] [Group G]

-- pin: rt (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1464)
def rt (x₀ : G) (v : G → ℂ) : G → ℂ := fun x => v (x * x₀)

-- pin: rt_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1466)
theorem rt_apply (x₀ : G) (v : G → ℂ) (x : G) : rt x₀ v x = v (x * x₀) := rfl

-- pin: rtLinear (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1468)
def rtLinear (x₀ : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun := rt x₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- pin: rtLinear_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1473)
theorem rtLinear_apply (x₀ : G) (v : G → ℂ) : rtLinear x₀ v = rt x₀ v := rfl

-- pin: rt_mul (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1475)
theorem rt_mul (x₀ x₁ : G) (v : G → ℂ) : rt (x₀ * x₁) v = rt x₀ (rt x₁ v) := by
  funext x
  simp only [rt_apply, mul_assoc]

-- pin: rt_mem_typeSubmodule_of_commute (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1479)
theorem rt_mem_typeSubmodule_of_commute {W : Type*} [AddCommGroup W] [Module ℂ W] {ι : H →* G}
    {ρ : Representation ℂ H W} {x₀ : G} (hx₀ : ∀ k : H, x₀ * ι k = ι k * x₀) {v : G → ℂ}
    (hv : v ∈ typeSubmodule ι ρ) : rt x₀ v ∈ typeSubmodule ι ρ := by
  have hmap : ∀ f ∈ typeSubmodule ι ρ, rtLinear x₀ f ∈ typeSubmodule ι ρ := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro g ⟨T, hT, w, rfl⟩
      have hT' : IsRightEquivariant ι ρ ((rtLinear x₀).comp T) := by
        intro k u x
        show T (ρ k u) (x * x₀) = T u (x * ι k * x₀)
        rw [hT k u (x * x₀), mul_assoc, hx₀ k, ← mul_assoc]
      exact mem_typeSubmodule_of_isRightEquivariant hT' w
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro f g _ _ hf hg
      rw [map_add]
      exact Submodule.add_mem _ hf hg
    · intro c f _ hf
      rw [map_smul]
      exact Submodule.smul_mem _ c hf
  exact hmap v hv

-- pin: rt_mem_typeSubmodule_self (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1501)
theorem rt_mem_typeSubmodule_self {W : Type*} [AddCommGroup W] [Module ℂ W] {ι : H →* G}
    {ρ : Representation ℂ H W} (k : H) {v : G → ℂ} (hv : v ∈ typeSubmodule ι ρ) :
    rt (ι k) v ∈ typeSubmodule ι ρ := by
  have hmap : ∀ f ∈ typeSubmodule ι ρ, rtLinear (ι k) f ∈ typeSubmodule ι ρ := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro g ⟨T, hT, w, rfl⟩
      have h1 : rtLinear (ι k) (T w) = T (ρ k w) := funext fun x => (hT k w x).symm
      rw [h1]
      exact mem_typeSubmodule_of_isRightEquivariant hT _
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro f g _ _ hf hg
      rw [map_add]
      exact Submodule.add_mem _ hf hg
    · intro c f _ hf
      rw [map_smul]
      exact Submodule.smul_mem _ c hf
  exact hmap v hv

-- pin: spanTranslates (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1521)
def spanTranslates (ι : H →* G) (V : Submodule ℂ (G → ℂ)) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ {g | ∃ k : H, ∃ v ∈ V, g = rt (ι k) v}

-- pin: le_spanTranslates (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1524)
theorem le_spanTranslates (ι : H →* G) (V : Submodule ℂ (G → ℂ)) : V ≤ spanTranslates ι V := by
  intro v hv
  refine Submodule.subset_span ⟨1, v, hv, ?_⟩
  funext x
  simp only [rt_apply, map_one, mul_one]

-- pin: rt_mem_spanTranslates (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1530)
theorem rt_mem_spanTranslates (ι : H →* G) (V : Submodule ℂ (G → ℂ)) (k : H) {v : G → ℂ} (hv : v ∈ V) :
    rt (ι k) v ∈ spanTranslates ι V :=
  Submodule.subset_span ⟨k, v, hv, rfl⟩

-- pin: rt_mem_spanTranslates_of_mem (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1534)
theorem rt_mem_spanTranslates_of_mem (ι : H →* G) (V : Submodule ℂ (G → ℂ)) (k : H) {g : G → ℂ}
    (hg : g ∈ spanTranslates ι V) : rt (ι k) g ∈ spanTranslates ι V := by
  have hmap : ∀ f ∈ spanTranslates ι V, rtLinear (ι k) f ∈ spanTranslates ι V := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro g ⟨k', v, hv, rfl⟩
      show rt (ι k) (rt (ι k') v) ∈ spanTranslates ι V
      rw [← rt_mul, ← map_mul]
      exact rt_mem_spanTranslates ι V _ hv
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro f g _ _ hf hg
      rw [map_add]
      exact Submodule.add_mem _ hf hg
    · intro c f _ hf
      rw [map_smul]
      exact Submodule.smul_mem _ c hf
  exact hmap g hg

-- pin: finiteDimensional_spanTranslates (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1553)
-- The pin's load-bearing `haveI` registers a Prop-valued instance; the linter's `have` would drop it.
set_option linter.style.haveILetI false in
theorem finiteDimensional_spanTranslates {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] [∀ j, Module.Finite ℂ (W j)] (ι : H →* G) (ρ : ∀ j, Representation ℂ H (W j))
    (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] (hV : V ≤ ⨆ j, typeSubmodule ι (ρ j)) :
    FiniteDimensional ℂ (spanTranslates ι V) := by
  classical
  obtain ⟨t, i, Φ, hΦ, hVΦ⟩ := exists_isRightEquivariant_le_range_of_le_iSup_typeSubmodule ι ρ V hV
  have hle : spanTranslates ι V ≤ LinearMap.range Φ := by
    refine Submodule.span_le.mpr ?_
    rintro g ⟨k, v, hv, rfl⟩
    obtain ⟨m, hm⟩ := hVΦ hv
    refine ⟨piRep (fun a => ρ (i a)) k m, ?_⟩
    funext x
    rw [hΦ k m x, rt_apply, hm]
  haveI : Module.Finite ℂ (∀ a : t, W (i a)) := Module.Finite.pi
  exact Submodule.finiteDimensional_of_le hle

end SpanTranslates

section MultiPlace

variable {G : Type*} [Group G]
variable {Pl : Type*} [Fintype Pl] [DecidableEq Pl] {K : Pl → Type*} [∀ w, Group (K w)]

-- pin: exists_finiteDimensional_stable (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1577)
-- The pin's load-bearing `haveI`s register Prop-valued instances; the linter's `have` would drop them.
set_option linter.style.haveILetI false in
theorem exists_finiteDimensional_stable {J : Pl → Type*} {W : ∀ w, J w → Type*}
    [∀ w j, AddCommGroup (W w j)] [∀ w j, Module ℂ (W w j)] [∀ w j, Module.Finite ℂ (W w j)]
    (ι : ∀ w, K w →* G) (hcomm : ∀ (w w' : Pl), w ≠ w' → ∀ (k : K w) (k' : K w'), ι w k * ι w' k' = ι w' k' * ι w k)
    (ρ : ∀ w j, Representation ℂ (K w) (W w j)) (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ w, V ≤ ⨆ j, typeSubmodule (ι w) (ρ w j)) :
    ∃ E : Submodule ℂ (G → ℂ), FiniteDimensional ℂ E ∧ V ≤ E ∧
      (∀ w, E ≤ ⨆ j, typeSubmodule (ι w) (ρ w j)) ∧ ∀ (w : Pl) (k : K w), ∀ v ∈ E, rt (ι w k) v ∈ E := by
  classical

  have hstab : ∀ (w w' : Pl) (k : K w), ∀ v ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j),
      rt (ι w k) v ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j) := by
    intro w w' k v hv
    have hmap : ∀ f ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j), rtLinear (ι w k) f ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j) := by
      intro f hf
      refine Submodule.iSup_induction _ (motive := fun f => rtLinear (ι w k) f ∈ ⨆ j, typeSubmodule (ι w') (ρ w' j))
        hf ?_ ?_ ?_
      · intro j f hfj
        refine Submodule.mem_iSup_of_mem j ?_
        by_cases hww : w = w'
        · subst hww
          exact rt_mem_typeSubmodule_self k hfj
        · exact rt_mem_typeSubmodule_of_commute (fun k' => hcomm w w' hww k k') hfj
      · rw [map_zero]
        exact Submodule.zero_mem _
      · intro f g hf hg
        rw [map_add]
        exact Submodule.add_mem _ hf hg
    exact hmap v hv

  suffices h : ∀ s : Finset Pl, ∃ E : Submodule ℂ (G → ℂ), FiniteDimensional ℂ E ∧ V ≤ E ∧
      (∀ w, E ≤ ⨆ j, typeSubmodule (ι w) (ρ w j)) ∧ ∀ w ∈ s, ∀ (k : K w), ∀ v ∈ E, rt (ι w k) v ∈ E by
    obtain ⟨E, h1, h2, h3, h4⟩ := h Finset.univ
    exact ⟨E, h1, h2, h3, fun w k v hv => h4 w (Finset.mem_univ w) k v hv⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨V, inferInstance, le_rfl, hV, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | @insert w₀ s hw₀ ih =>
    obtain ⟨E, hEfd, hVE, hEcut, hEst⟩ := ih
    haveI := hEfd
    haveI : FiniteDimensional ℂ (spanTranslates (ι w₀) E) :=
      finiteDimensional_spanTranslates (ι w₀) (ρ w₀) E (hEcut w₀)
    refine ⟨spanTranslates (ι w₀) E, inferInstance, hVE.trans (le_spanTranslates _ _), ?_, ?_⟩
    · intro w
      refine Submodule.span_le.mpr ?_
      rintro g ⟨k, v, hv, rfl⟩
      exact hstab w₀ w k v (hEcut w hv)
    · intro w hw k g hg
      rcases Finset.mem_insert.mp hw with rfl | hws
      · exact rt_mem_spanTranslates_of_mem (ι w) E k hg
      · have hmap : ∀ f ∈ spanTranslates (ι w₀) E, rtLinear (ι w k) f ∈ spanTranslates (ι w₀) E := by
          intro f hf
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
          · rintro g ⟨k₀, v, hv, rfl⟩
            have hne : w ≠ w₀ := fun h => hw₀ (h ▸ hws)
            show rt (ι w k) (rt (ι w₀ k₀) v) ∈ spanTranslates (ι w₀) E
            rw [← rt_mul, hcomm w w₀ hne k k₀, rt_mul]
            exact rt_mem_spanTranslates (ι w₀) E k₀ (hEst w hws k v hv)
          · rw [map_zero]
            exact Submodule.zero_mem _
          · intro f g _ _ hf hg
            rw [map_add]
            exact Submodule.add_mem _ hf hg
          · intro c f _ hf
            rw [map_smul]
            exact Submodule.smul_mem _ c hf
        exact hmap g hg

end MultiPlace

end Q09

end

noncomputable section

open MeasureTheory Matrix

namespace Q09

section Delta

variable {G : Type*} [Group G]
variable {Kc : Type*} [Group Kc] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc]
  [MeasurableSpace Kc] [BorelSpace Kc]
variable (μ : Measure Kc) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant]
  [μ.IsMulRightInvariant]
variable (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
variable (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)

-- pin: piE (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1669)
def piE (κ : Kc) : E →ₗ[ℂ] E where
  toFun v := ⟨fun x => (v : G → ℂ) (x * ι κ), hE κ v v.2⟩
  map_add' v w := by ext x; rfl
  map_smul' c v := by ext x; rfl

-- pin: piE_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1675)
omit [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem piE_apply (κ : Kc) (v : E) (x : G) : (piE ι E hE κ v : G → ℂ) x = (v : G → ℂ) (x * ι κ) := rfl

-- pin: piE_one (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1678)
omit [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem piE_one : piE ι E hE 1 = LinearMap.id := by
  ext v x
  show (v : G → ℂ) (x * ι 1) = (v : G → ℂ) x
  rw [map_one, mul_one]

-- pin: piE_mul (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1684)
omit [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem piE_mul (κ κ' : Kc) : piE ι E hE (κ * κ') = piE ι E hE κ ∘ₗ piE ι E hE κ' := by
  ext v x
  show (v : G → ℂ) (x * ι (κ * κ')) = (v : G → ℂ) (x * ι κ * ι κ')
  rw [map_mul, mul_assoc]

variable [FiniteDimensional ℂ E]

-- pin: Pm (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1691)
def Pm (κ : Kc) : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ E) (Module.finBasis ℂ E) (piE ι E hE κ)

-- pin: Pm_one (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1695)
omit [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem Pm_one : Pm ι E hE 1 = 1 := by
  rw [Pm, piE_one, LinearMap.toMatrix_id]

-- pin: Pm_mul (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1699)
omit [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem Pm_mul (κ κ' : Kc) : Pm ι E hE (κ * κ') = Pm ι E hE κ * Pm ι E hE κ' := by
  rw [Pm, piE_mul, LinearMap.toMatrix_comp (Module.finBasis ℂ E) (Module.finBasis ℂ E)]
  rfl

-- pin: Pm_inv_mul (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1704)
omit [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem Pm_inv_mul (κ : Kc) : Pm ι E hE κ⁻¹ * Pm ι E hE κ = 1 := by
  rw [← Pm_mul, inv_mul_cancel, Pm_one]

-- pin: Pm_mul_inv (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1708)
omit [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem Pm_mul_inv (κ : Kc) : Pm ι E hE κ * Pm ι E hE κ⁻¹ = 1 := by
  rw [← Pm_mul, mul_inv_cancel, Pm_one]

-- pin: continuous_Pm_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1712)
omit [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem continuous_Pm_apply (hcont : ∀ v ∈ E, ∀ x : G, Continuous fun κ : Kc => v (x * ι κ))
    (i j : Fin (Module.finrank ℂ E)) : Continuous fun κ => Pm ι E hE κ i j := by
  let b := Module.finBasis ℂ E
  have h1 : Continuous fun κ : Kc => (piE ι E hE κ (b j) : E) := by
    refine continuous_induced_rng.mpr ?_
    refine continuous_pi fun x => ?_
    exact hcont _ (b j).2 x
  have h2 : Continuous (b.coord i : E →ₗ[ℂ] ℂ) := LinearMap.continuous_of_finiteDimensional _
  have h3 : (fun κ => Pm ι E hE κ i j) = fun κ => b.coord i (piE ι E hE κ (b j)) := by
    funext κ
    rw [Pm, LinearMap.toMatrix_apply]
    rfl
  rw [h3]
  exact h2.comp h1

-- pin: continuous_Pm (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1728)
omit [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem continuous_Pm (hcont : ∀ v ∈ E, ∀ x : G, Continuous fun κ : Kc => v (x * ι κ)) :
    Continuous fun κ => Pm ι E hE κ :=
  continuous_pi fun i => continuous_pi fun j => continuous_Pm_apply ι E hE hcont i j

section Mint

variable {m : Type*} [Fintype m] [DecidableEq m]

-- pin: Mint (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1736)
def Mint (Φ : Kc → Matrix m m ℂ) : Matrix m m ℂ := Matrix.of fun i j => ∫ κ, Φ κ i j ∂μ

omit [Group Kc] [TopologicalSpace Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [BorelSpace Kc] [IsFiniteMeasure μ]
  [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Fintype m] [DecidableEq m] in
-- pin: Mint_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1740)
theorem Mint_apply (Φ : Kc → Matrix m m ℂ) (i j : m) : Mint μ Φ i j = ∫ κ, Φ κ i j ∂μ := rfl

-- pin: hasCompactSupport_of_compactSpace (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1743)
omit [Group Kc] [IsTopologicalGroup Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem hasCompactSupport_of_compactSpace {α : Type*} [Zero α] [TopologicalSpace α] (h : Kc → α) :
    HasCompactSupport h :=
  IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport h) (Set.subset_univ _)

-- pin: integrable_of_continuous (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1748)
omit [IsTopologicalGroup Kc] [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Group Kc] in
theorem integrable_of_continuous {h : Kc → ℂ} (hh : Continuous h) : Integrable h μ :=
  hh.integrable_of_hasCompactSupport (hasCompactSupport_of_compactSpace h)

omit [Group Kc] [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] [IsFiniteMeasure μ]
  [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Fintype m] [DecidableEq m] in
-- pin: continuous_apply_apply_of_continuous (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1753)
theorem continuous_apply_apply_of_continuous {Φ : Kc → Matrix m m ℂ} (hΦ : Continuous Φ) (i j : m) :
    Continuous fun κ => Φ κ i j :=
  (continuous_apply j).comp ((continuous_apply i).comp hΦ)

omit [IsTopologicalGroup Kc] [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [DecidableEq m]
  [Group Kc] in
-- pin: Mint_const_mul (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1759)
theorem Mint_const_mul (A : Matrix m m ℂ) {Φ : Kc → Matrix m m ℂ} (hΦ : Continuous Φ) :
    Mint μ (fun κ => A * Φ κ) = A * Mint μ Φ := by
  ext i j
  rw [Mint_apply, Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Mint_apply]
  rw [integral_finsetSum _ fun k _ => (integrable_of_continuous μ
    (continuous_apply_apply_of_continuous hΦ k j)).const_mul (A i k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact integral_const_mul _ _

omit [IsTopologicalGroup Kc] [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [DecidableEq m]
  [Group Kc] in
-- pin: Mint_mul_const (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1771)
theorem Mint_mul_const (A : Matrix m m ℂ) {Φ : Kc → Matrix m m ℂ} (hΦ : Continuous Φ) :
    Mint μ (fun κ => Φ κ * A) = Mint μ Φ * A := by
  ext i j
  rw [Mint_apply, Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Mint_apply]
  rw [integral_finsetSum _ fun k _ => (integrable_of_continuous μ
    (continuous_apply_apply_of_continuous hΦ i k)).mul_const (A k j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact integral_mul_const _ _

omit [IsTopologicalGroup Kc] [CompactSpace Kc] [BorelSpace Kc] [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Group Kc] [TopologicalSpace Kc] [Fintype m] [DecidableEq m] in
-- pin: Mint_conjTranspose (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1783)
theorem Mint_conjTranspose (Φ : Kc → Matrix m m ℂ) :
    (Mint μ Φ)ᴴ = Mint μ (fun κ => (Φ κ)ᴴ) := by
  ext i j
  rw [Matrix.conjTranspose_apply, Mint_apply, Mint_apply]
  simp_rw [Matrix.conjTranspose_apply]
  exact integral_conj.symm

-- pin: Mint_mul_right (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1791)
omit [CompactSpace Kc] [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] [Fintype m] [DecidableEq m] in
theorem Mint_mul_right (Φ : Kc → Matrix m m ℂ) (k : Kc) :
    Mint μ (fun κ => Φ (κ * k)) = Mint μ Φ := by
  ext i j
  rw [Mint_apply, Mint_apply]
  exact integral_mul_right_eq_self (fun κ => Φ κ i j) k

-- pin: apply_Mint (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1798)
omit [IsTopologicalGroup Kc] [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Group Kc] in
theorem apply_Mint (θ : Matrix m m ℂ →ₗ[ℂ] ℂ) {Φ : Kc → Matrix m m ℂ} (hΦ : Continuous Φ) :
    θ (Mint μ Φ) = ∫ κ, θ (Φ κ) ∂μ := by
  have hexp : ∀ M : Matrix m m ℂ, θ M = ∑ i, ∑ j, M i j * θ (Matrix.single i j 1) := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hexp]
  simp_rw [hexp (Φ _)]
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => ?_]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [Mint_apply]
      exact (integral_mul_const _ _).symm
    · exact (integrable_of_continuous μ (continuous_apply_apply_of_continuous hΦ i j)).mul_const _
  · exact integrable_finsetSum _ fun j _ =>
      (integrable_of_continuous μ (continuous_apply_apply_of_continuous hΦ i j)).mul_const _

omit [IsTopologicalGroup Kc] [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [DecidableEq m]
  [Group Kc] in
-- pin: dotProduct_Mint_mulVec (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1822)
theorem dotProduct_Mint_mulVec (x y : m → ℂ) {Φ : Kc → Matrix m m ℂ} (hΦ : Continuous Φ) :
    x ⬝ᵥ (Mint μ Φ *ᵥ y) = ∫ κ, x ⬝ᵥ (Φ κ *ᵥ y) ∂μ := by
  have hI : ∀ i j, Integrable (fun κ => Φ κ i j) μ := fun i j =>
    integrable_of_continuous μ (continuous_apply_apply_of_continuous hΦ i j)
  simp only [dotProduct, Matrix.mulVec, Mint_apply, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((hI i j).mul_const _).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => ((hI i j).mul_const _).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc x i * ((∫ κ, Φ κ i j ∂μ) * y j) = x i * ∫ κ, Φ κ i j * y j ∂μ := by
        rw [show (∫ κ, Φ κ i j * y j ∂μ) = (∫ κ, Φ κ i j ∂μ) * y j from integral_mul_const _ _]
    _ = ∫ κ, x i * (Φ κ i j * y j) ∂μ := (integral_const_mul _ _).symm

end Mint

variable (hcont : ∀ v ∈ E, ∀ x : G, Continuous fun κ : Kc => v (x * ι κ))

-- pin: Hm (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1841)
def Hm : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
  Mint μ fun κ => (Pm ι E hE κ)ᴴ * Pm ι E hE κ

-- pin: continuous_PHP (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1846)
include hcont in
omit [IsTopologicalGroup Kc] [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem continuous_PHP : Continuous fun κ => (Pm ι E hE κ)ᴴ * Pm ι E hE κ :=
  ((continuous_Pm ι E hE hcont).matrix_conjTranspose).mul (continuous_Pm ι E hE hcont)

-- pin: conjTranspose_mul_Hm_mul (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1851)
omit [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] in
include hcont in
theorem conjTranspose_mul_Hm_mul (k : Kc) :
    (Pm ι E hE k)ᴴ * Hm μ ι E hE * Pm ι E hE k = Hm μ ι E hE := by
  have hΦ := continuous_PHP ι E hE hcont
  have e1 : (Pm ι E hE k)ᴴ * Hm μ ι E hE = Mint μ (fun κ => (Pm ι E hE k)ᴴ * ((Pm ι E hE κ)ᴴ * Pm ι E hE κ)) :=
    (Mint_const_mul μ _ hΦ).symm
  have e2 : Mint μ (fun κ => (Pm ι E hE k)ᴴ * ((Pm ι E hE κ)ᴴ * Pm ι E hE κ)) * Pm ι E hE k =
      Mint μ (fun κ => (Pm ι E hE k)ᴴ * ((Pm ι E hE κ)ᴴ * Pm ι E hE κ) * Pm ι E hE k) :=
    (Mint_mul_const μ _ (continuous_const.mul hΦ)).symm
  have e3 : (fun κ => (Pm ι E hE k)ᴴ * ((Pm ι E hE κ)ᴴ * Pm ι E hE κ) * Pm ι E hE k) =
      fun κ => (Pm ι E hE (κ * k))ᴴ * Pm ι E hE (κ * k) := by
    funext κ
    rw [Pm_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e1, e2, e3, Mint_mul_right μ (fun κ => (Pm ι E hE κ)ᴴ * Pm ι E hE κ) k, Hm]

-- pin: star_dotProduct_conjTranspose_mul_mulVec (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1866)
theorem star_dotProduct_conjTranspose_mul_mulVec {m : Type*} [Fintype m] (A : Matrix m m ℂ) (x : m → ℂ) :
    star x ⬝ᵥ ((Aᴴ * A) *ᵥ x) = ∑ i, (Complex.normSq ((A *ᵥ x) i) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]
  rw [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.normSq_eq_conj_mul_self]

-- pin: Hm_mulVec_injective (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1875)
omit [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsTopologicalGroup Kc] in
include hcont in
theorem Hm_mulVec_injective : Function.Injective (Hm μ ι E hE).mulVec := by
  intro x y hxy
  rw [← sub_eq_zero]
  set z := x - y with hz
  have hz0 : (Hm μ ι E hE) *ᵥ z = 0 := by rw [hz, Matrix.mulVec_sub, hxy, sub_self]
  by_contra hne

  let q : Kc → ℝ := fun κ => ∑ i, Complex.normSq ((Pm ι E hE κ *ᵥ z) i)
  have hq_cont : Continuous q := by
    refine continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp ?_
    exact (continuous_apply i).comp
      ((continuous_Pm ι E hE hcont).matrix_mulVec continuous_const)
  have hq_nonneg : ∀ κ, 0 ≤ q κ := fun κ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hq_one : q 1 ≠ 0 := by
    intro h0
    apply hne
    have h1 : ∀ i, Complex.normSq ((Pm ι E hE 1 *ᵥ z) i) = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).mp h0 i (Finset.mem_univ i)
    funext i
    have := h1 i
    rw [Pm_one, Matrix.one_mulVec, Complex.normSq_eq_zero] at this
    exact this
  have hpos : 0 < ∫ κ, q κ ∂μ :=
    hq_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero (hasCompactSupport_of_compactSpace q)
      hq_nonneg hq_one

  have hform : star z ⬝ᵥ ((Hm μ ι E hE) *ᵥ z) = ((∫ κ, q κ ∂μ : ℝ) : ℂ) := by
    rw [Hm, dotProduct_Mint_mulVec μ _ _ (continuous_PHP ι E hE hcont), ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    show star z ⬝ᵥ (((Pm ι E hE κ)ᴴ * Pm ι E hE κ) *ᵥ z) = ((q κ : ℝ) : ℂ)
    rw [star_dotProduct_conjTranspose_mul_mulVec]
    show _ = ((∑ i, Complex.normSq ((Pm ι E hE κ *ᵥ z) i) : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
  rw [hz0, dotProduct_zero] at hform
  have : (∫ κ, q κ ∂μ) = 0 := by exact_mod_cast hform.symm
  exact (lt_irrefl _) (this ▸ hpos)

-- pin: isUnit_Hm_det (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1914)
include hcont in
omit [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsTopologicalGroup Kc] in
theorem isUnit_Hm_det : IsUnit (Hm μ ι E hE).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact Matrix.mulVec_injective_iff_isUnit.mp (Hm_mulVec_injective μ ι E hE hcont)

-- pin: conjTranspose_Pm (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1920)
omit [μ.IsMulLeftInvariant] in
include hcont in
theorem conjTranspose_Pm (k : Kc) :
    (Pm ι E hE k)ᴴ = Hm μ ι E hE * Pm ι E hE k⁻¹ * (Hm μ ι E hE)⁻¹ := by
  have h1 : (Pm ι E hE k)ᴴ * Hm μ ι E hE = Hm μ ι E hE * Pm ι E hE k⁻¹ := by
    have h := conjTranspose_mul_Hm_mul μ ι E hE hcont k
    calc (Pm ι E hE k)ᴴ * Hm μ ι E hE
        = (Pm ι E hE k)ᴴ * Hm μ ι E hE * (Pm ι E hE k * Pm ι E hE k⁻¹) := by
          rw [Pm_mul_inv, Matrix.mul_one]
      _ = Hm μ ι E hE * Pm ι E hE k⁻¹ := by rw [← Matrix.mul_assoc, h]
  rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_Hm_det μ ι E hE hcont), Matrix.mul_one]

-- pin: Dm (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1930)
def Dm (i j : Fin (Module.finrank ℂ E)) : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
  Mint μ fun κ => Pm ι E hE κ⁻¹ j i • Pm ι E hE κ

-- pin: continuous_Pm_inv (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1935)
include hcont in
omit [CompactSpace Kc] [MeasurableSpace Kc] [BorelSpace Kc] in
theorem continuous_Pm_inv : Continuous fun κ : Kc => Pm ι E hE κ⁻¹ :=
  (continuous_Pm ι E hE hcont).comp continuous_inv

-- pin: one_mem_span_Dm (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:1940)
omit [μ.IsMulLeftInvariant] in
include hcont in
theorem one_mem_span_Dm :
    (1 : Matrix _ _ ℂ) ∈ Submodule.span ℂ (Set.range fun p : Fin (Module.finrank ℂ E) × Fin (Module.finrank ℂ E)
      => Dm μ ι E hE p.1 p.2) := by
  set R := Submodule.span ℂ (Set.range fun p : Fin (Module.finrank ℂ E) × Fin (Module.finrank ℂ E)
      => Dm μ ι E hE p.1 p.2) with hR
  by_contra h1

  have hq : R.mkQ 1 ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (_ ⧸ R), φ (R.mkQ 1) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hq ((Module.forall_dual_apply_eq_zero_iff ℂ _).mp hall)
  let θ : Matrix _ _ ℂ →ₗ[ℂ] ℂ := φ ∘ₗ R.mkQ
  have hθR : ∀ r ∈ R, θ r = 0 := fun r hr => by
    show φ (R.mkQ r) = 0
    rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero R).mpr hr, map_zero]
  have hθ1 : θ 1 ≠ 0 := hφ

  let s : Kc → ℂ := fun κ => θ (Pm ι E hE κ)
  have hθc : Continuous θ := LinearMap.continuous_of_finiteDimensional _
  have hs_cont : Continuous s := hθc.comp (continuous_Pm ι E hE hcont)

  have hstep1 : ∀ i j, ∫ κ, s κ * Pm ι E hE κ⁻¹ j i ∂μ = 0 := by
    intro i j
    have hD : θ (Dm μ ι E hE i j) = 0 := hθR _ (Submodule.subset_span ⟨(i, j), rfl⟩)
    rw [Dm, apply_Mint μ θ (((continuous_apply_apply_of_continuous (continuous_Pm_inv ι E hE hcont) j
      i)).fun_smul (continuous_Pm ι E hE hcont))] at hD
    rw [← hD]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    show s κ * Pm ι E hE κ⁻¹ j i = θ (Pm ι E hE κ⁻¹ j i • Pm ι E hE κ)
    rw [map_smul, smul_eq_mul, mul_comm]

  let Θ : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ :=
    Matrix.of fun b a => θ (Matrix.single a b 1)
  have hsΘ : ∀ κ, s κ = (Θ * Pm ι E hE κ).trace := by
    intro κ
    show θ (Pm ι E hE κ) = _
    conv_lhs => rw [Matrix.matrix_eq_sum_single (Pm ι E hE κ)]
    rw [map_sum, Matrix.trace]
    simp only [Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hsm : Matrix.single b a (Pm ι E hE κ b a) = (Pm ι E hE κ b a) • Matrix.single b a (1 : ℂ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hsm, map_smul, smul_eq_mul, mul_comm]
    rfl

  set S' := (Hm μ ι E hE)⁻¹ * Θᴴ * Hm μ ι E hE with hS'
  have hconj : ∀ κ, (starRingEnd ℂ) (s κ) = (S' * Pm ι E hE κ⁻¹).trace := by
    intro κ
    rw [hsΘ]
    show star ((Θ * Pm ι E hE κ).trace) = _
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, conjTranspose_Pm μ ι E hE hcont κ]
    rw [hS']

    rw [Matrix.trace_mul_comm]
    rw [show Θᴴ * (Hm μ ι E hE * Pm ι E hE κ⁻¹ * (Hm μ ι E hE)⁻¹) =
      (Θᴴ * Hm μ ι E hE * Pm ι E hE κ⁻¹) * (Hm μ ι E hE)⁻¹ by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]

  have hI : ∀ a b, Integrable (fun κ => s κ * Pm ι E hE κ⁻¹ a b) μ := fun a b =>
    integrable_of_continuous μ (hs_cont.mul
      (continuous_apply_apply_of_continuous (continuous_Pm_inv ι E hE hcont) a b))
  have hzero : ∫ κ, s κ * (starRingEnd ℂ) (s κ) ∂μ = 0 := by
    simp_rw [hconj]
    have hexp : ∀ κ, s κ * (S' * Pm ι E hE κ⁻¹).trace =
        ∑ a, ∑ b, S' a b * (s κ * Pm ι E hE κ⁻¹ b a) := by
      intro κ
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    simp_rw [hexp]
    rw [integral_finsetSum (f := fun a κ => ∑ b, S' a b * (s κ * Pm ι E hE κ⁻¹ b a)) _
      fun a _ => integrable_finsetSum _ fun b _ => (hI b a).const_mul _]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (hI b a).const_mul _]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [show (∫ κ, S' a b * (s κ * Pm ι E hE κ⁻¹ b a) ∂μ) = S' a b * ∫ κ, s κ * Pm ι E hE κ⁻¹ b a ∂μ
      from integral_const_mul _ _, hstep1 a b, mul_zero]

  have hreal : ∫ κ, s κ * (starRingEnd ℂ) (s κ) ∂μ = ((∫ κ, Complex.normSq (s κ) ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
    exact Complex.mul_conj (s κ)
  have hpos : 0 < ∫ κ, Complex.normSq (s κ) ∂μ := by
    refine (Complex.continuous_normSq.comp hs_cont).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hasCompactSupport_of_compactSpace _) (fun κ => Complex.normSq_nonneg _) (x := 1) ?_
    show Complex.normSq (s 1) ≠ 0
    rw [Ne, Complex.normSq_eq_zero]
    show θ (Pm ι E hE 1) ≠ 0
    rwa [Pm_one]
  rw [hreal] at hzero
  have : (∫ κ, Complex.normSq (s κ) ∂μ) = 0 := by exact_mod_cast hzero
  exact (lt_irrefl _) (this ▸ hpos)

-- pin: exists_reproducer (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:2040)
omit [μ.IsMulLeftInvariant] in
include hcont in
theorem exists_reproducer :
    ∃ c : Fin (Module.finrank ℂ E) × Fin (Module.finrank ℂ E) → ℂ, ∀ v ∈ E, ∀ x : G,
      ∫ κ, (∑ p, c p * Pm ι E hE κ⁻¹ p.2 p.1) * v (x * ι κ) ∂μ = v x := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (one_mem_span_Dm μ ι E hE hcont)
  refine ⟨c, fun v hv x => ?_⟩
  let b := Module.finBasis ℂ E
  obtain ⟨e, he⟩ : ∃ e : Kc → ℂ, ∀ κ, e κ = ∑ p, c p * Pm ι E hE κ⁻¹ p.2 p.1 := ⟨_, fun _ => rfl⟩
  have he_cont : Continuous e := by
    rw [show e = fun κ => ∑ p, c p * Pm ι E hE κ⁻¹ p.2 p.1 from funext he]
    exact continuous_finsetSum _ fun p _ =>
      continuous_const.mul (continuous_apply_apply_of_continuous (continuous_Pm_inv ι E hE hcont) _ _)

  have hone : ∀ j l, ∫ κ, e κ * Pm ι E hE κ j l ∂μ =
      (1 : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ) j l := by
    intro j l
    have hsum := congrArg (fun M : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ
      => M j l) hc
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hsum
    rw [← hsum]
    have hI : ∀ p : Fin (Module.finrank ℂ E) × Fin (Module.finrank ℂ E),
        Integrable (fun κ => Pm ι E hE κ⁻¹ p.2 p.1 * Pm ι E hE κ j l) μ :=
      fun p => integrable_of_continuous μ
        ((continuous_apply_apply_of_continuous (continuous_Pm_inv ι E hE hcont) _ _).mul
          (continuous_Pm_apply ι E hE hcont j l))
    have hexp : ∀ κ, e κ * Pm ι E hE κ j l = ∑ p, c p * (Pm ι E hE κ⁻¹ p.2 p.1 * Pm ι E hE κ j l) := by
      intro κ
      rw [he, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      ring
    simp_rw [hexp]
    rw [integral_finsetSum _ fun p _ => (hI p).const_mul _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show (∫ κ, c p * (Pm ι E hE κ⁻¹ p.2 p.1 * Pm ι E hE κ j l) ∂μ) =
      c p * ∫ κ, Pm ι E hE κ⁻¹ p.2 p.1 * Pm ι E hE κ j l ∂μ from integral_const_mul _ _]
    rfl

  let r : Fin (Module.finrank ℂ E) → ℂ := b.repr ⟨v, hv⟩
  have hexpand : ∀ κ, v (x * ι κ) = ∑ j, (∑ l, Pm ι E hE κ j l * r l) * (b j : G → ℂ) x := by
    intro κ
    have h1 : (piE ι E hE κ ⟨v, hv⟩ : G → ℂ) x = v (x * ι κ) := rfl
    rw [← h1]
    have h2 : (piE ι E hE κ ⟨v, hv⟩ : E) = ∑ j, (b.repr (piE ι E hE κ ⟨v, hv⟩) j) • b j :=
      (b.sum_repr _).symm
    have h3 : ∀ j, b.repr (piE ι E hE κ ⟨v, hv⟩) j = ∑ l, Pm ι E hE κ j l * r l := by
      intro j
      have := LinearMap.toMatrix_mulVec_repr b b (piE ι E hE κ) ⟨v, hv⟩
      rw [← Pm] at this
      rw [← this]
      rfl
    rw [h2, Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h3]

  have hI2 : ∀ j l, Integrable (fun κ => e κ * Pm ι E hE κ j l) μ := fun j l =>
    integrable_of_continuous μ (he_cont.mul (continuous_Pm_apply ι E hE hcont j l))
  have hexp2 : ∀ κ, e κ * v (x * ι κ) = ∑ j, ∑ l, (b j : G → ℂ) x * r l * (e κ * Pm ι E hE κ j l) := by
    intro κ
    rw [hexpand κ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have key : ∫ κ, e κ * v (x * ι κ) ∂μ = v x := by
    calc ∫ κ, e κ * v (x * ι κ) ∂μ
        = ∫ κ, ∑ j, ∑ l, (b j : G → ℂ) x * r l * (e κ * Pm ι E hE κ j l) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hexp2)
      _ = ∑ j, ∑ l, (b j : G → ℂ) x * r l * ∫ κ, e κ * Pm ι E hE κ j l ∂μ := by
          rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (hI2 j l).const_mul _]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_finsetSum _ fun l _ => (hI2 j l).const_mul _]
          refine Finset.sum_congr rfl fun l _ => ?_
          exact integral_const_mul _ _
      _ = ∑ j, r j * (b j : G → ℂ) x := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp_rw [hone, Matrix.one_apply, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite_eq Finset.univ j]
          simp only [Finset.mem_univ, ite_true]
          ring
      _ = v x := by
          have h2 : (⟨v, hv⟩ : E) = ∑ j, r j • b j := (b.sum_repr _).symm
          have h3 := congrArg (fun w : E => (w : G → ℂ) x) h2
          simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
            smul_eq_mul] at h3
          exact h3.symm
  simp_rw [he] at key
  exact key

end Delta

end Q09

end

noncomputable section

open AutomorphicForm

namespace Q09

section ZetaB0

variable {G : Type*} [Group G] {Kw Kc : Type*} [Group Kw] [Group Kc]
variable (ι : Kc →* G) (E : Submodule ℂ (G → ℂ))
variable (hE : ∀ (κ : Kc), ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E) [FiniteDimensional ℂ E]

-- pin: Pm_apply_eq_coeffFun (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:2149)
theorem Pm_apply_eq_coeffFun (κ : Kc) (i j : Fin (Module.finrank ℂ E)) :
    Pm ι E hE κ i j =
      coeffFun (transRep ι E hE) ((Module.finBasis ℂ E).coord i) ((Module.finBasis ℂ E) j) κ := by
  rw [Pm, LinearMap.toMatrix_apply]
  rfl

-- pin: Pm_inv_apply_eq_dualCoeffFun (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:2155)
theorem Pm_inv_apply_eq_dualCoeffFun (κ : Kc) (i j : Fin (Module.finrank ℂ E)) :
    Pm ι E hE κ⁻¹ i j =
      dualCoeffFun (transRep ι E hE) ((Module.finBasis ℂ E) j) ((Module.finBasis ℂ E).coord i) κ := by
  rw [Pm, LinearMap.toMatrix_apply]
  rfl

variable {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
variable {incl : Kw →* Kc} (hincl : Function.Injective incl) (ρ : ∀ j, Representation ℂ Kw (W j))
variable (hEcut : ∀ v ∈ E, v ∈ ⨆ j, typeSubmodule (ι.comp incl) (ρ j))

-- pin: Pm_entry_mem_iSup (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:2166)
include hincl hEcut in
theorem Pm_entry_mem_iSup (i j : Fin (Module.finrank ℂ E)) :
    (fun κ => Pm ι E hE κ i j) ∈ ⨆ j', typeSubmodule incl (ρ j') := by
  have h : (fun κ => Pm ι E hE κ i j) =
      coeffFun (transRep ι E hE) ((Module.finBasis ℂ E).coord i) ((Module.finBasis ℂ E) j) :=
    funext fun κ => Pm_apply_eq_coeffFun ι E hE κ i j
  rw [h]
  exact coeffFun_transRep_mem_iSup hincl ι ρ E hE hEcut _ _

-- pin: Pm_inv_entry_mem_iSup (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:2175)
include hincl hEcut in
theorem Pm_inv_entry_mem_iSup (i j : Fin (Module.finrank ℂ E)) :
    (fun κ => Pm ι E hE κ⁻¹ i j) ∈ ⨆ j', typeSubmodule incl (ρ j').dual := by
  have h : (fun κ => Pm ι E hE κ⁻¹ i j) =
      dualCoeffFun (transRep ι E hE) ((Module.finBasis ℂ E) j) ((Module.finBasis ℂ E).coord i) :=
    funext fun κ => Pm_inv_apply_eq_dualCoeffFun ι E hE κ i j
  rw [h]
  exact dualCoeffFun_transRep_mem_iSup hincl ι ρ E hE hEcut _ _

-- pin: reproducer_mem_iSup_dual (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:2184)
include hincl hEcut in
theorem reproducer_mem_iSup_dual (c : Fin (Module.finrank ℂ E) × Fin (Module.finrank ℂ E) → ℂ) :
    (fun κ => ∑ p, c p * Pm ι E hE κ⁻¹ p.2 p.1) ∈ ⨆ j', typeSubmodule incl (ρ j').dual := by
  have h : (fun κ => ∑ p, c p * Pm ι E hE κ⁻¹ p.2 p.1) =
      ∑ p, c p • fun κ => Pm ι E hE κ⁻¹ p.2 p.1 := by
    funext κ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact Submodule.sum_mem _ fun p _ =>
    Submodule.smul_mem _ _ (Pm_inv_entry_mem_iSup ι E hE hincl ρ hEcut p.2 p.1)

-- pin: reproducer_inv_mem_iSup (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:2195)
include hincl hEcut in
theorem reproducer_inv_mem_iSup (c : Fin (Module.finrank ℂ E) × Fin (Module.finrank ℂ E) → ℂ) :
    (fun κ => ∑ p, c p * Pm ι E hE κ p.2 p.1) ∈ ⨆ j', typeSubmodule incl (ρ j') := by
  have h : (fun κ => ∑ p, c p * Pm ι E hE κ p.2 p.1) = ∑ p, c p • fun κ => Pm ι E hE κ p.2 p.1 := by
    funext κ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h]
  exact Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Pm_entry_mem_iSup ι E hE hincl ρ hEcut p.2 p.1)

end ZetaB0

end Q09

end
