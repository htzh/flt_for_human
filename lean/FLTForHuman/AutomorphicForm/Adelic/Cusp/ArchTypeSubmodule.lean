/-
  The archimedean type submodules of the cuspidal spectrum.

  Three rows of the `Def_AutomorphicForm_CuspidalSpectrumCarrier` /
  `Def_AutomorphicForm_IsotypicCuspSpace` vocabulary, all about the same object: the
  archimedean `ArchTypeFamily` decomposition of the cuspidal space.

  * `CuspidalSpectrum.exists_isArchBiFinite_flat`: an arch-bi-finite factorizable test
    function stays arch-bi-finite after the cuspidal flattening `flat F σ`
    (`Cusp/SpectrumCarrier.lean`), with an `ArchTypeFamily` that may change.
  * `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup`:
    an irreducible finite-dimensional stable submodule of a supremum of arch type
    submodules is contained in one of finitely many irreducible arch type submodules.
  * `typeSubmodule_inf_typeSubmodule_eq_bot`: the purely algebraic statement behind the
    directness of that supremum — for two inequivalent irreducible representations of
    `H`, the `typeSubmodule`s of `ℂ[G]` are disjoint.

  Transcribed from the three `S_` files below (pinned `aa2d8b3`, 304 + 152 + 646 lines), with their
  `private` engines: the pins' label namespaces (`FlatBiFiniteProof`, `SubqPrep`, `STDProof`) are
  dropped and the engine declarations carry subject names, `private` as in the pin. The engines are
  the transport of a representation along a linear equivalence, the conjugate/dual pieces of
  `Fin n → ℂ` (both used by the `flat` row), the finite-length subquotient calculus
  (`IsSubquotient`, `entryQuot`, the covering list of simple subquotients, the elimination over
  products), and the `typeSubmodule`-as-supremum-of-intertwining-ranges argument behind the
  directness row.

  Drift, statement-preserving: the pins' `set_option backward.isDefEq.respectTransparency false in`
  markers and their `attribute [local instance] glBorel` wall are dropped (nothing here needs
  either); `@[scoped simp]` on the pin's `transportRep_apply` is dropped (the one call site names
  the lemma); `haveI` → `have` throughout (FR-0223); `omit [NumberField F] in` where the linter
  reports an unused section variable. The `hf` binder of `exists_isArchBiFinite_flat` is unused by
  the pin's own proof and is named once in the proof (`have hfac`) rather than renamed, which would
  rewrite the checked statement.

  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_isArchBiFinite_flat.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_typeSubmodule_inf_typeSubmodule_eq_bot.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false

-- Heartbeat probe (recorded, **not installed**): playbook §3.5 says no module carries a
-- `set_option maxHeartbeats` — an in-file cap is a defect marker, not a budget, and `lake build` runs
-- at the project cap. The measurement is kept for the next reader: the module is silent at 20 000 per
-- declaration and fails at 19 000 (three `whnf`/`isDefEq` timeouts, binding on
-- `isSubquotient_of_le_iSup`), i.e. ≈10× under the edit loop's 200 000.

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ComplexConjugate ENNReal InnerProductSpace Classical

namespace AutomorphicForm

/-! ### Engine: transporting representations, and conjugate/dual pieces of `Fin n → ℂ` -/

section Transport

variable {H G : Type*} [Group H] [Group G]
variable {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- Transport a representation along a linear equivalence. -/
private def transportRep (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ H W) : Representation ℂ H W' where
  toFun k := e.toLinearMap ∘ₗ ρ k ∘ₗ e.symm.toLinearMap
  map_one' := by ext v; simp
  map_mul' k k' := by ext v; simp

private theorem transportRep_apply (e : W ≃ₗ[ℂ] W') (ρ : Representation ℂ H W) (k : H)
    (v : W') : transportRep e ρ k v = e (ρ k (e.symm v)) := rfl

/-- A type piece only depends on the isomorphism class of the representation. -/
private theorem typeSubmodule_le_of_equiv (ι : H →* G) (ρ : Representation ℂ H W)
    (ρ' : Representation ℂ H W') (Ψ : W ≃ₗ[ℂ] W')
    (hΨ : ∀ (k : H) (v : W), Ψ (ρ k v) = ρ' k (Ψ v)) :
    typeSubmodule ι ρ ≤ typeSubmodule ι ρ' := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨T, hT, v, rfl⟩
  have hΨ' : ∀ (k : H) (u : W'), ρ k (Ψ.symm u) = Ψ.symm (ρ' k u) := fun k u => by
    apply Ψ.injective
    rw [hΨ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hT' : IsRightEquivariant ι ρ' (T ∘ₗ Ψ.symm.toLinearMap) := fun k u x => by
    show T (Ψ.symm (ρ' k u)) x = T (Ψ.symm u) (x * ι k)
    rw [← hΨ', hT]
  have : T v = (T ∘ₗ Ψ.symm.toLinearMap) (Ψ v) := by simp
  rw [this]
  exact mem_typeSubmodule_of_isRightEquivariant hT' _

end Transport

section Conjugate

variable {H G : Type*} [Group H] [Group G] {n : ℕ}

/-- The conjugate of a representation on `Fin n → ℂ`. -/
private def starConjRep (ρ : Representation ℂ H (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) where
  toFun k :=
    { toFun := fun v => star (ρ k (star v))
      map_add' := fun v w => by simp [star_add]
      map_smul' := fun c v => by simp [star_smul] }
  map_one' := by ext v i; simp
  map_mul' k k' := by ext v i; simp

/-- Complex conjugation carries the type piece of `ρ` into that of `ρ` conjugated. -/
private theorem star_mem_typeSubmodule_starConjRep (ι : H →* G) (ρ : Representation ℂ H (Fin n → ℂ))
    {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ) :
    (fun x => starRingEnd ℂ (f x)) ∈ typeSubmodule ι (starConjRep ρ) := by
  refine Submodule.span_induction
    (p := fun f _ => (fun x => starRingEnd ℂ (f x)) ∈ typeSubmodule ι (starConjRep ρ))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    let Tb : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun u x => starRingEnd ℂ (T (star u) x)
        map_add' := fun u₁ u₂ => funext fun x => by simp [star_add, map_add]
        map_smul' := fun c u => funext fun x => by simp [star_smul, map_smul] }
    have hTb : IsRightEquivariant ι (starConjRep ρ) Tb := fun k u x => by
      show starRingEnd ℂ (T (star (star (ρ k (star u)))) x) = starRingEnd ℂ (T (star u) (x * ι k))
      rw [star_star, hT]
    have : (fun x => starRingEnd ℂ (T v x)) = Tb (star v) := by
      funext x; show _ = starRingEnd ℂ (T (star (star v)) x); rw [star_star]
    rw [this]
    exact mem_typeSubmodule_of_isRightEquivariant hTb _
  · show (fun x => starRingEnd ℂ ((0 : G → ℂ) x)) ∈ typeSubmodule ι (starConjRep ρ)
    have : (fun x => starRingEnd ℂ ((0 : G → ℂ) x)) = 0 := by funext x; simp
    rw [this]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    have : (fun x => starRingEnd ℂ ((a + b) x))
        = (fun x => starRingEnd ℂ (a x)) + fun x => starRingEnd ℂ (b x) := by
      funext x; simp
    rw [this]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have : (fun x => starRingEnd ℂ ((c • a) x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (a x) := by
      funext x; simp
    rw [this]; exact Submodule.smul_mem _ _ ha

/-- The dual of `Fin n → ℂ`, identified with `Fin n → ℂ` through the coordinate basis. -/
private def dualToPi (n : ℕ) : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
  (Pi.basisFun ℂ (Fin n)).toDualEquiv.symm

/-- The conjugate of the dual rep, on `Fin n → ℂ`. -/
private def conjOfDual (ρ : Representation ℂ H (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) :=
  starConjRep (transportRep (dualToPi n) ρ.dual)

/-- The dual of the conjugate rep, on `Fin n → ℂ`. -/
private def dualOfConj (ρ : Representation ℂ H (Fin n → ℂ)) : Representation ℂ H (Fin n → ℂ) :=
  transportRep (dualToPi n) (starConjRep ρ).dual

/-- Conjugation carries the dual type piece into the `conjOfDual` piece. -/
private theorem star_mem_typeSubmodule_conjOfDual (ι : H →* G)
    (ρ : Representation ℂ H (Fin n → ℂ)) {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ.dual) :
    (fun x => starRingEnd ℂ (f x)) ∈ typeSubmodule ι (conjOfDual ρ) := by
  have h1 : f ∈ typeSubmodule ι (transportRep (dualToPi n) ρ.dual) :=
    typeSubmodule_le_of_equiv ι ρ.dual _ (dualToPi n)
      (fun k v => by rw [transportRep_apply, LinearEquiv.symm_apply_apply]) hf
  exact star_mem_typeSubmodule_starConjRep ι _ h1

/-- The conjugate type piece sits inside the dual of the `dualOfConj` piece. -/
private theorem typeSubmodule_le_dualOfConj_dual (ι : H →* G)
    (ρ : Representation ℂ H (Fin n → ℂ)) :
    typeSubmodule ι (starConjRep ρ) ≤ typeSubmodule ι (dualOfConj ρ).dual := by
  set π : Representation ℂ H (Fin n → ℂ) := starConjRep ρ
  let Ψ : (Fin n → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) :=
    (Module.evalEquiv ℂ (Fin n → ℂ)).trans (dualToPi n).symm.dualMap
  refine typeSubmodule_le_of_equiv ι π (dualOfConj ρ).dual Ψ fun k v => ?_
  apply LinearMap.ext
  intro u
  simp only [Ψ, dualOfConj, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply,
    transportRep_apply, LinearEquiv.symm_apply_apply, inv_inv]
  rfl

end Conjugate

section Determinant

variable {F : Type} [Field F] [NumberField F]

/-- The determinant commutes with a map of the base ring. -/
private theorem det_map_generalLinearGroup {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g)
      = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

/-- A row isometry has determinant one. -/
private theorem det_rowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k) = 1 := by
  have hk : ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff (K := w.Completion)).mp k.2).1
  have hfin : Units.map (adeleFin (𝓞 F) F).toMonoidHom
      (Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k)) = 1 := by
    rw [← det_map_generalLinearGroup]
    show Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F (rowIsometryInclAt₀ F w k)) = 1
    rw [glFin_rowIsometryInclAt₀, map_one]
  have harch : ∀ v : InfinitePlace F, Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom
      (Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k)) = 1 := by
    intro v
    rw [← det_map_generalLinearGroup]
    have : Matrix.GeneralLinearGroup.map ((archEval F v).comp (adeleArch (𝓞 F) F))
        (rowIsometryInclAt₀ F w k)
        = archComponent F v (glArch (𝓞 F) F (rowIsometryInclAt₀ F w k)) := rfl
    rw [this, glArch_rowIsometryInclAt₀]
    by_cases hv : v = w
    · subst hv
      show Matrix.GeneralLinearGroup.det (archComponent F v (archGLIncl F v (k : GL (Fin 2) v.Completion))) = 1
      rw [archComponent_archGLIncl_self]
      exact Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hk, Units.val_one])
    · show Matrix.GeneralLinearGroup.det (archComponent F v (archGLIncl F w (k : GL (Fin 2) w.Completion))) = 1
      rw [archComponent_archGLIncl_of_ne F hv, map_one]
  refine Units.ext (Prod.ext (funext fun v => ?_) ?_)
  · have := congrArg (fun u : (v.Completion)ˣ => (u : v.Completion)) (harch v)
    simp at this
    exact this
  · have := congrArg (fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => (u : FiniteAdeleRing (𝓞 F) F)) hfin
    simp at this
    exact this

/-- The weight `‖det‖^{-σ}` is invariant under right multiplication by a row isometry. -/
private theorem weight_mul_rowIsometryInclAt₀ (σ : ℝ) (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 F) F) :
    ((NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (x * rowIsometryInclAt₀ F w k)) ^ (-σ) : ℝ) : ℂ)
      = ((NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) := by
  rw [map_mul, det_rowIsometryInclAt₀, mul_one]

/-- The same invariance for the inverse weight. -/
private theorem weight_inv_mul_rowIsometryInclAt₀ (σ : ℝ) (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 F) F) :
    ((NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (x * rowIsometryInclAt₀ F w k)⁻¹) ^ (-σ) : ℝ) : ℂ)
      = ((NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ) := by
  rw [mul_inv_rev, map_mul, ← map_inv (rowIsometryInclAt₀ F w), det_rowIsometryInclAt₀, one_mul]

end Determinant

section DoubledFamily

variable {F : Type} [Field F] [NumberField F]

/-- The family `tys` with both conjugate-dual pieces adjoined at every place. -/
private def doubledFamilyRep (tys : ArchTypeFamily F) (w : InfinitePlace F) :
    Fin (tys.card w + tys.card w) → ArchRepAt F w :=
  Fin.addCases (fun i => ⟨(tys.rep w i).n, conjOfDual (tys.rep w i).ρ⟩)
    (fun i => ⟨(tys.rep w i).n, dualOfConj (tys.rep w i).ρ⟩)

/-- The family `tys` with both conjugate-dual pieces adjoined at every place. -/
private def doubledFamily (tys : ArchTypeFamily F) : ArchTypeFamily F :=
  ⟨fun w => tys.card w + tys.card w, doubledFamilyRep tys⟩

omit [NumberField F] in
private theorem doubledFamily_rep_castAdd (tys : ArchTypeFamily F) (w : InfinitePlace F)
    (i : Fin (tys.card w)) :
    (doubledFamily tys).rep w (Fin.castAdd (tys.card w) i)
      = ⟨(tys.rep w i).n, conjOfDual (tys.rep w i).ρ⟩ := by
  simp [doubledFamily, doubledFamilyRep]

omit [NumberField F] in
private theorem doubledFamily_rep_natAdd (tys : ArchTypeFamily F) (w : InfinitePlace F)
    (i : Fin (tys.card w)) :
    (doubledFamily tys).rep w (Fin.natAdd (tys.card w) i)
      = ⟨(tys.rep w i).n, dualOfConj (tys.rep w i).ρ⟩ :=
  Fin.addCases_right (m := tys.card w) (n := tys.card w) (motive := fun _ => ArchRepAt F w)
    (left := fun i => ⟨(tys.rep w i).n, conjOfDual (tys.rep w i).ρ⟩)
    (right := fun i => ⟨(tys.rep w i).n, dualOfConj (tys.rep w i).ρ⟩) i

end DoubledFamily

namespace CuspidalSpectrum

theorem exists_isArchBiFinite_flat
    (F : Type) [Field F] [NumberField F] (σ : ℝ) (tys : ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    ∃ tys' : ArchTypeFamily F, IsArchBiFinite F tys' (flat F σ f) := by
  classical
  -- `hf` is part of the frozen statement and is not needed for the archimedean argument;
  -- it is named here so that the declaration carries no unused-variable warning (its
  -- binder cannot be renamed without rewriting the checked statement).
  have hfac : IsFactorizableTestFn F f := hf
  obtain ⟨hcut, hdual⟩ := hft
  refine ⟨doubledFamily tys, ?_, ?_⟩
  ·
    rw [mem_archCutSubmodule_iff]
    intro w
    have hw := (mem_archDualCutSubmodule_iff F tys f).mp hdual w
    have key : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
        φ ∈ (⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i)) →
        (fun x => starRingEnd ℂ (φ x) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
          ∈ ⨆ j : Fin ((doubledFamily tys).card w), archTypeSubmoduleAt F w ((doubledFamily tys).rep w j) := by
      intro φ hφ
      refine Submodule.iSup_induction _ (motive := fun φ => (fun x => starRingEnd ℂ (φ x) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
          ∈ ⨆ j : Fin ((doubledFamily tys).card w),
              archTypeSubmoduleAt F w ((doubledFamily tys).rep w j)) hφ ?_ ?_ ?_
      · intro i φ hφi
        have h1 := star_mem_typeSubmodule_conjOfDual (rowIsometryInclAt₀ F w) (tys.rep w i).ρ hφi
        have h2 : (fun x => starRingEnd ℂ (φ x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
            ∈ typeSubmodule (rowIsometryInclAt₀ F w) (conjOfDual (tys.rep w i).ρ) :=
          comp_mul_mem_typeSubmodule_of_hom (ι := rowIsometryInclAt₀ F w) (ι' := rowIsometryInclAt₀ F w)
            (MonoidHom.id (AdelicGL2 (𝓞 F) F)) (fun _ => rfl)
            (m := fun x => ((NumberField.TateGlobal.ideleNorm F
              (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
            (fun k x => weight_inv_mul_rowIsometryInclAt₀ σ w k x) h1
        refine le_iSup (fun j => archTypeSubmoduleAt F w ((doubledFamily tys).rep w j))
          (Fin.castAdd (tys.card w) i) ?_
        show _ ∈ typeSubmodule (rowIsometryInclAt₀ F w)
          ((doubledFamily tys).rep w (Fin.castAdd (tys.card w) i)).ρ
        rw [doubledFamily_rep_castAdd]
        exact h2
      · show (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((0 : AdelicGL2 (𝓞 F) F → ℂ) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
            ∈ _
        have : (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((0 : AdelicGL2 (𝓞 F) F → ℂ) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
            = 0 := by
          funext x; simp
        rw [this]; exact Submodule.zero_mem _
      · intro a b ha hb
        have : (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((a + b) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
            = (fun x => starRingEnd ℂ (a x) *
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ))
              + fun x => starRingEnd ℂ (b x) *
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ) := by
          funext x; simp [add_mul]
        rw [this]; exact Submodule.add_mem _ ha hb
    have hφ : (fun x => flat F σ f x⁻¹) = fun x => starRingEnd ℂ (f x) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x⁻¹) ^ (-σ) : ℝ) : ℂ) := by
      funext x; simp [flat, inv_inv]
    rw [hφ]
    exact key f hw
  ·
    rw [mem_archDualCutSubmodule_iff]
    intro w
    have hw := (mem_archCutSubmodule_iff F tys (fun x => f x⁻¹)).mp hcut w
    have key : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ,
        φ ∈ (⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) →
        (fun x => starRingEnd ℂ (φ x) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
          ∈ ⨆ j : Fin ((doubledFamily tys).card w),
              archDualTypeSubmoduleAt F w ((doubledFamily tys).rep w j) := by
      intro φ hφ
      refine Submodule.iSup_induction _ (motive := fun φ => (fun x => starRingEnd ℂ (φ x) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
          ∈ ⨆ j : Fin ((doubledFamily tys).card w),
              archDualTypeSubmoduleAt F w ((doubledFamily tys).rep w j)) hφ ?_ ?_ ?_
      · intro i φ hφi
        have h1 := star_mem_typeSubmodule_starConjRep (rowIsometryInclAt₀ F w) (tys.rep w i).ρ hφi
        have h2 : (fun x => starRingEnd ℂ (φ x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
            ∈ typeSubmodule (rowIsometryInclAt₀ F w) (starConjRep (tys.rep w i).ρ) :=
          comp_mul_mem_typeSubmodule_of_hom (ι := rowIsometryInclAt₀ F w) (ι' := rowIsometryInclAt₀ F w)
            (MonoidHom.id (AdelicGL2 (𝓞 F) F)) (fun _ => rfl)
            (m := fun x => ((NumberField.TateGlobal.ideleNorm F
              (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
            (fun k x => weight_mul_rowIsometryInclAt₀ σ w k x) h1
        have h3 := typeSubmodule_le_dualOfConj_dual (rowIsometryInclAt₀ F w) (tys.rep w i).ρ h2
        refine le_iSup (fun j => archDualTypeSubmoduleAt F w ((doubledFamily tys).rep w j))
          (Fin.natAdd (tys.card w) i) ?_
        show _ ∈ typeSubmodule (rowIsometryInclAt₀ F w)
          ((doubledFamily tys).rep w (Fin.natAdd (tys.card w) i)).ρ.dual
        rw [doubledFamily_rep_natAdd]
        exact h3
      · show (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((0 : AdelicGL2 (𝓞 F) F → ℂ) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)) ∈ _
        have : (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((0 : AdelicGL2 (𝓞 F) F → ℂ) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
            = 0 := by
          funext x; simp
        rw [this]; exact Submodule.zero_mem _
      · intro a b ha hb
        have : (fun x : AdelicGL2 (𝓞 F) F => starRingEnd ℂ ((a + b) x) *
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
            = (fun x => starRingEnd ℂ (a x) *
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ))
              + fun x => starRingEnd ℂ (b x) *
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) := by
          funext x; simp [add_mul]
        rw [this]; exact Submodule.add_mem _ ha hb
    have hφ : flat F σ f = fun x => starRingEnd ℂ ((fun y => f y⁻¹) x) *
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) := by
      funext x; simp [flat]
    rw [hφ]
    exact key _ hw

end CuspidalSpectrum

/-! ### Engine: subquotients of a finite-length module -/

section SubquotientCalculus

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- `S` is a subquotient of `M`: a quotient of a submodule of `M`. -/
private def IsSubquotient (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M]
    (S : Type*) [AddCommGroup S] [Module R S] : Prop :=
  ∃ (A : Submodule R M) (f : A →ₗ[R] S), Function.Surjective f

private theorem IsSubquotient.of_injective {N : Type*} [AddCommGroup N] [Module R N]
    {S : Type*} [AddCommGroup S] [Module R S]
    (h : IsSubquotient R N S) (i : N →ₗ[R] M) (hi : Function.Injective i) :
    IsSubquotient R M S := by
  obtain ⟨A, f, hf⟩ := h
  let e : A ≃ₗ[R] (A.map i) := (Submodule.equivMapOfInjective i hi A)
  exact ⟨A.map i, f ∘ₗ e.symm.toLinearMap, hf.comp e.symm.surjective⟩

/-- A subquotient of a simple type is a subquotient of a submodule or of a quotient. -/
private theorem IsSubquotient.dichotomy {S : Type*} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (h : IsSubquotient R M S) (N : Submodule R M) :
    IsSubquotient R N S ∨ IsSubquotient R (M ⧸ N) S := by
  obtain ⟨A, f, hf⟩ := h
  let AN : Submodule R A := Submodule.comap A.subtype N
  let g : AN →ₗ[R] S := f ∘ₗ AN.subtype
  rcases eq_bot_or_eq_top (LinearMap.range g) with hg | hg
  ·
    right
    let h : A →ₗ[R] M ⧸ N := N.mkQ ∘ₗ A.subtype
    have hker : LinearMap.ker h ≤ LinearMap.ker f := by
      intro a ha
      have haN : (a : M) ∈ N := by
        simpa [h, LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero] using ha
      have : g ⟨a, haN⟩ ∈ LinearMap.range g := LinearMap.mem_range_self g _
      rw [hg, Submodule.mem_bot] at this
      simpa [g] using this
    refine ⟨LinearMap.range h,
      (LinearMap.ker h).liftQ f hker ∘ₗ (LinearMap.quotKerEquivRange h).symm.toLinearMap, ?_⟩
    intro s
    obtain ⟨a, rfl⟩ := hf s
    refine ⟨LinearMap.quotKerEquivRange h (Submodule.Quotient.mk a), ?_⟩
    simp
  ·
    left
    have hgs : Function.Surjective g := LinearMap.range_eq_top.mp hg
    let AN' : Submodule R N := Submodule.comap N.subtype A
    let e : AN' →ₗ[R] AN :=
      { toFun := fun x => ⟨⟨(x : N), x.2⟩, by
          show ((⟨(x : N), x.2⟩ : A) : M) ∈ N
          exact (x : N).2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have he : Function.Surjective e := by
      rintro ⟨⟨m, hmA⟩, hmN⟩
      exact ⟨⟨⟨m, hmN⟩, hmA⟩, rfl⟩
    exact ⟨AN', g ∘ₗ e, hgs.comp he⟩

/-- A subquotient of a simple module is the whole module. -/
private theorem IsSubquotient.nonempty_equiv_of_isSimpleModule {S : Type*} [AddCommGroup S]
    [Module R S] [IsSimpleModule R S] [IsSimpleModule R M] (h : IsSubquotient R M S) :
    Nonempty (M ≃ₗ[R] S) := by
  obtain ⟨A, f, hf⟩ := h
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  have hA : A ≠ ⊥ := by
    intro hA
    have hsub : Subsingleton A := by
      rw [hA]
      infer_instance
    have : Subsingleton S := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      rw [Subsingleton.elim a b]⟩
    exact false_of_nontrivial_of_subsingleton S
  have hA' : A = ⊤ := (eq_bot_or_eq_top A).resolve_left hA
  subst hA'
  let f' : M →ₗ[R] S := f ∘ₗ (Submodule.topEquiv (R := R) (M := M)).symm.toLinearMap
  have hf' : Function.Surjective f' := hf.comp (Submodule.topEquiv (R := R) (M := M)).symm.surjective
  have hker : LinearMap.ker f' = ⊥ := by
    rcases eq_bot_or_eq_top (LinearMap.ker f') with h | h
    · exact h
    · exfalso
      have : Subsingleton S := ⟨fun x y => by
        obtain ⟨a, rfl⟩ := hf' x
        obtain ⟨b, rfl⟩ := hf' y
        have ha : a ∈ LinearMap.ker f' := h ▸ Submodule.mem_top
        have hb : b ∈ LinearMap.ker f' := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker] at ha hb
        rw [ha, hb]⟩
      exact false_of_nontrivial_of_subsingleton S
  exact ⟨LinearEquiv.ofBijective f' ⟨LinearMap.ker_eq_bot.mp hker, hf'⟩⟩

end SubquotientCalculus

section EntryQuotients

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The quotient of the submodule `p.1` by the trace of `p.2`. -/
private abbrev entryQuot (p : Submodule R M × Submodule R M) : Type _ :=
  ↥p.1 ⧸ (p.2.comap p.1.subtype)

private theorem nonempty_entryQuot_equiv_map (N : Submodule R M) (A B : Submodule R N) :
    Nonempty (entryQuot (R := R) (A, B) ≃ₗ[R]
      entryQuot (R := R) (A.map N.subtype, B.map N.subtype)) := by
  let e : ↥A ≃ₗ[R] ↥(A.map N.subtype) := Submodule.equivMapOfInjective N.subtype N.injective_subtype A
  refine ⟨Submodule.Quotient.equiv _ _ e ?_⟩
  ext ⟨x, hx⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨a, ha⟩, hB, hax⟩
    have hax' : ((a : N) : M) = x := by
      have := congrArg Subtype.val hax
      simpa [e] using this
    exact ⟨a, hB, hax'⟩
  · rintro ⟨b, hbB, hbx⟩
    obtain ⟨a', ha', hx'⟩ := (Submodule.mem_map.mp hx)
    have hb_a : b = a' := N.injective_subtype (by
      show (b : M) = (a' : M)
      rw [hbx]
      exact hx'.symm)
    refine ⟨⟨b, hb_a ▸ ha'⟩, hbB, ?_⟩
    apply Subtype.ext
    show ((e ⟨b, _⟩ : A.map N.subtype) : M) = x
    simp [e, hbx]

/-- A finite-length module has finitely many simple subquotients, covering all of them. -/
private theorem exists_list_forall_isSubquotient (h : IsFiniteLength R M) :
    ∃ l : List (Submodule R M × Submodule R M),
      (∀ p ∈ l, IsSimpleModule R (entryQuot p)) ∧
      ∀ (S : Type*) [AddCommGroup S] [Module R S], IsSimpleModule R S → IsSubquotient R M S →
        ∃ p ∈ l, Nonempty (entryQuot p ≃ₗ[R] S) := by
  induction h with
  | of_subsingleton =>
      refine ⟨[], fun p hp => by simp at hp, ?_⟩
      intro S _ _ hS hsq
      exfalso
      obtain ⟨A, f, hf⟩ := hsq
      have := IsSimpleModule.nontrivial R S
      have : Subsingleton S := ⟨fun x y => by
        obtain ⟨a, rfl⟩ := hf x
        obtain ⟨b, rfl⟩ := hf y
        rw [Subsingleton.elim a b]⟩
      exact false_of_nontrivial_of_subsingleton S
  | @of_simple_quotient M' _ _ N hsimp hN ih =>
      obtain ⟨l, hl, hcov⟩ := ih
      have etop : entryQuot (R := R) ((⊤ : Submodule R M'), N) ≃ₗ[R] M' ⧸ N :=
        Submodule.Quotient.equiv _ _ Submodule.topEquiv (by
          ext x
          simp only [Submodule.mem_map, Submodule.mem_comap]
          constructor
          · rintro ⟨y, hy, rfl⟩
            simpa using hy
          · intro hx
            exact ⟨⟨x, Submodule.mem_top⟩, by simpa using hx, by simp⟩)
      refine ⟨(l.map fun p => (p.1.map N.subtype, p.2.map N.subtype)) ++
        [((⊤ : Submodule R M'), N)], ?_, ?_⟩
      · intro p hp
        rw [List.mem_append, List.mem_map, List.mem_singleton] at hp
        rcases hp with ⟨q, hq, rfl⟩ | rfl
        · obtain ⟨e⟩ := nonempty_entryQuot_equiv_map N q.1 q.2
          have hsimple := hl q hq
          exact IsSimpleModule.congr e.symm
        · exact IsSimpleModule.congr etop
      · intro S _ _ hS hsq
        rcases hsq.dichotomy N with h1 | h2
        · obtain ⟨p, hp, ⟨e⟩⟩ := hcov S hS h1
          obtain ⟨e'⟩ := nonempty_entryQuot_equiv_map N p.1 p.2
          exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩), ⟨e'.symm.trans e⟩⟩
        · have hSsimple := hS
          obtain ⟨e⟩ := h2.nonempty_equiv_of_isSimpleModule
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ⟨etop.trans e⟩⟩

end EntryQuotients

section SubquotientElimination

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
variable {M' : Type*} [AddCommGroup M'] [Module R M']

private theorem IsSubquotient.of_ambient_equiv {S : Type*} [AddCommGroup S] [Module R S]
    (h : IsSubquotient R M S) (e : M ≃ₗ[R] M') : IsSubquotient R M' S :=
  h.of_injective e.toLinearMap e.injective

/-- A simple subquotient of a product is a subquotient of one of the factors. -/
private theorem IsSubquotient.prod_elim {S : Type*} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] (h : IsSubquotient R (M × M') S) :
    IsSubquotient R M S ∨ IsSubquotient R M' S := by
  rcases h.dichotomy (LinearMap.ker (LinearMap.snd R M M')) with h1 | h2
  · left
    have e1 : M ≃ₗ[R] LinearMap.range (LinearMap.inl R M M') :=
      LinearEquiv.ofInjective (LinearMap.inl R M M') LinearMap.inl_injective
    have e2 : LinearMap.range (LinearMap.inl R M M') ≃ₗ[R]
        LinearMap.ker (LinearMap.snd R M M') :=
      LinearEquiv.ofEq _ _ (LinearMap.range_inl R M M')
    exact h1.of_ambient_equiv (e1.trans e2).symm
  · right
    exact h2.of_ambient_equiv (LinearMap.quotKerEquivOfSurjective _ LinearMap.snd_surjective)

/-- A simple subquotient of a finite product is a subquotient of one of the factors. -/
private theorem IsSubquotient.pi_elim {S : Type*} [AddCommGroup S] [Module R S]
    [IsSimpleModule R S] {n : ℕ} {X : Fin n → Type*} [∀ i, AddCommGroup (X i)]
    [∀ i, Module R (X i)] (h : IsSubquotient R (∀ i, X i) S) : ∃ i, IsSubquotient R (X i) S := by
  induction n with
  | zero =>
      exfalso
      obtain ⟨A, f, hf⟩ := h
      have := IsSimpleModule.nontrivial R S
      have : Subsingleton (∀ i : Fin 0, X i) := ⟨fun a b => funext fun i => Fin.elim0 i⟩
      have : Subsingleton S := ⟨fun x y => by
        obtain ⟨a, rfl⟩ := hf x
        obtain ⟨b, rfl⟩ := hf y
        rw [Subsingleton.elim a b]⟩
      exact false_of_nontrivial_of_subsingleton S
  | succ n ih =>
      have h' := h.of_ambient_equiv (Fin.consLinearEquiv R X).symm
      rcases h'.prod_elim with h0 | hrest
      · exact ⟨0, h0⟩
      · obtain ⟨i, hi⟩ := ih hrest
        exact ⟨i.succ, hi⟩

end SubquotientElimination

section FinRepresentations

open scoped MonoidAlgebra

variable {K : Type*} [Group K]

/-- Every finite-dimensional `ℂ[K]`-module is the associated module of a representation on
some `Fin d → ℂ`. -/
private theorem exists_representation_fin_nonempty_equiv (E : Type*) [AddCommGroup E] [Module ℂ E]
    [Module ℂ[K] E] [IsScalarTower ℂ ℂ[K] E] [FiniteDimensional ℂ E] :
    ∃ (d : ℕ) (σ : Representation ℂ K (Fin d → ℂ)), Nonempty (σ.asModule ≃ₗ[ℂ[K]] E) := by
  let ρE : Representation ℂ K E := Representation.ofModule' E
  let b := Module.finBasis ℂ E
  let e : E ≃ₗ[ℂ] (Fin (Module.finrank ℂ E) → ℂ) := b.equivFun
  let σ : Representation ℂ K (Fin (Module.finrank ℂ E) → ℂ) := transportRep e ρE
  have hρE : ∀ (g : K) (x : E), ρE g x = MonoidAlgebra.of ℂ K g • x := by
    intro g x
    simp [ρE, Representation.ofModule', MonoidAlgebra.lift_symm_apply, Algebra.lsmul_coe]
  let f : σ.asModule →ₗ[ℂ] E := e.symm.toLinearMap ∘ₗ σ.asModuleEquiv.toLinearMap
  have hf : ∀ (c : ℂ[K]) (v : σ.asModule), f (c • v) = c • f v := by
    intro c v
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [add_smul, hx, hy]
    | single g t =>
        simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
        rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single, LinearMap.smul_apply,
          LinearEquiv.map_smul]
        show t • e.symm (σ g (σ.asModuleEquiv v))
          = MonoidAlgebra.single g t • e.symm (σ.asModuleEquiv v)
        rw [transportRep_apply, LinearEquiv.symm_apply_apply, hρE, ← smul_assoc, MonoidAlgebra.of_apply,
          MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  let F : σ.asModule →ₗ[ℂ[K]] E :=
    { toFun := f
      map_add' := fun x y => f.map_add x y
      map_smul' := hf }
  have hFbij : Function.Bijective F := by
    show Function.Bijective f
    exact (e.symm.bijective).comp σ.asModuleEquiv.bijective
  exact ⟨_, σ, ⟨LinearEquiv.ofBijective F hFbij⟩⟩

/-- A finite-dimensional representation whose associated module is a given simple module is
irreducible. -/
private theorem isIrreducible_of_equiv {d : ℕ} (σ : Representation ℂ K (Fin d → ℂ)) (E : Type*)
    [AddCommGroup E] [Module ℂ[K] E] (e : σ.asModule ≃ₗ[ℂ[K]] E) [IsSimpleModule ℂ[K] E] :
    σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr e

end FinRepresentations

/-! ### Engine: the row isometry representation and its stable submodules -/

section RowRepresentation

open scoped MonoidAlgebra
open CuspidalConstituent

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

/-- The right regular representation restricted to the row isometries at `w`. -/
private def rowRightRegular :
    Representation ℂ (rowIsometrySubgroup₀ w.Completion) (AdelicGL2 (𝓞 F) F → ℂ) :=
  (rightRegular F).comp (rowIsometryInclAt₀ F w)

private theorem rowRightRegular_apply (k : rowIsometrySubgroup₀ w.Completion)
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    rowRightRegular F w k f = rightTranslate F (rowIsometryInclAt₀ F w k) f := rfl

/-- The associated `ℂ[row isometries]`-module of the right regular representation. -/
private abbrev rowModule : Type := (rowRightRegular F w).asModule

variable {F w}

/-- The `ℂ[K]`-submodule of the associated module cut out by a stable submodule. -/
private def stableSubmodule (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) :
    Submodule ℂ[rowIsometrySubgroup₀ w.Completion] (rowModule F w) :=
  (Subrepresentation.mk (ρ := rowRightRegular F w) S (fun k v hv => hS k v hv)).asSubmodule

private theorem mem_stableSubmodule_iff (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (f : rowModule F w) : f ∈ stableSubmodule S hS ↔ (rowRightRegular F w).asModuleEquiv f ∈ S :=
  Iff.rfl

private theorem of_smul_eq (k : rowIsometrySubgroup₀ w.Completion) (f : rowModule F w) :
    (MonoidAlgebra.of ℂ (rowIsometrySubgroup₀ w.Completion) k • f : rowModule F w)
      = (rightTranslate F (rowIsometryInclAt₀ F w k)
        ((rowRightRegular F w).asModuleEquiv f) : AdelicGL2 (𝓞 F) F → ℂ) := by
  rw [MonoidAlgebra.of_apply, Representation.single_smul, one_smul]
  rfl

private theorem exists_stable_of_submodule
    (N : Submodule ℂ[rowIsometrySubgroup₀ w.Completion] (rowModule F w)) :
    ∃ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S',
        rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') ∧
      ∀ f : rowModule F w, (rowRightRegular F w).asModuleEquiv f ∈ S' ↔ f ∈ N := by
  let σ : Subrepresentation (rowRightRegular F w) := Subrepresentation.ofSubmodule' N
  refine ⟨σ.toSubmodule, fun k g hg => ?_, fun f => Iff.rfl⟩
  have := σ.apply_mem_toSubmodule k hg
  rwa [rowRightRegular_apply] at this

end RowRepresentation

section StableSubmoduleSimplicity

open scoped MonoidAlgebra
open CuspidalConstituent

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

/-- A stable submodule with no nontrivial stable submodule is a simple `ℂ[K]`-module. -/
private theorem isSimpleModule_stableSubmodule (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (hne : S ≠ ⊥)
    (hsimple : ∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S',
        rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
      S' = ⊥ ∨ S' = S) :
    IsSimpleModule ℂ[rowIsometrySubgroup₀ w.Completion] ↥(stableSubmodule S hS) := by
  obtain ⟨f₀, hf₀S, hf₀ne⟩ := (Submodule.ne_bot_iff S).mp hne
  have : Nontrivial ↥(stableSubmodule S hS) :=
    ⟨⟨⟨(rowRightRegular F w).asModuleEquiv.symm f₀,
        (mem_stableSubmodule_iff S hS _).mpr hf₀S⟩, 0,
      fun h => hf₀ne (congrArg Subtype.val h)⟩⟩
  suffices hall : ∀ N : Submodule ℂ[rowIsometrySubgroup₀ w.Completion] ↥(stableSubmodule S hS),
      N = ⊥ ∨ N = ⊤ by
    have : IsSimpleOrder (Submodule ℂ[rowIsometrySubgroup₀ w.Completion]
        ↥(stableSubmodule S hS)) := ⟨hall⟩
    exact ⟨⟩
  intro N
  let N' : Submodule ℂ[rowIsometrySubgroup₀ w.Completion] (rowModule F w) :=
    N.map (stableSubmodule S hS).subtype
  obtain ⟨S', hS'st, hS'mem⟩ := exists_stable_of_submodule N'
  have hN'le : N' ≤ stableSubmodule S hS := Submodule.map_subtype_le _ _
  have hS'le : S' ≤ S := fun f hf =>
    (mem_stableSubmodule_iff S hS ((rowRightRegular F w).asModuleEquiv.symm f)).mp
      (hN'le ((hS'mem _).mp hf))
  rcases hsimple S' hS'le hS'st with h | h
  · left
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    have hx' : (rowRightRegular F w).asModuleEquiv (x : rowModule F w) ∈ S' :=
      (hS'mem _).mpr (Submodule.mem_map_of_mem hx)
    rw [h, Submodule.mem_bot] at hx'
    exact Subtype.ext hx'
  · right
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    have hxS : (rowRightRegular F w).asModuleEquiv (x : rowModule F w) ∈ S' := by
      rw [h]
      exact (mem_stableSubmodule_iff S hS _).mp x.2
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp ((hS'mem _).mp hxS)
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

omit [NumberField F] in
/-- The associated module of a finite-dimensional representation has finite length. -/
private theorem isFiniteLength_asModule {d : ℕ}
    (ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ)) :
    IsFiniteLength ℂ[rowIsometrySubgroup₀ w.Completion] ρ.asModule := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  have : IsNoetherian ℂ ρ.asModule := IsNoetherian.iff_fg.mpr inferInstance
  have : IsArtinian ℂ ρ.asModule := isArtinian_of_fg_of_artinian'
  exact ⟨isNoetherian_of_tower ℂ inferInstance, isArtinian_of_tower ℂ inferInstance⟩

end StableSubmoduleSimplicity

section FiniteSubquotientReduction

open scoped MonoidAlgebra
open CuspidalConstituent

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

/-- A summand of a type piece: a representation index, an equivariant map into `G → ℂ`, and a
vector of the representation. -/
private abbrev archEntry (m : ℕ) (ρs : Fin m → ArchRepAt F w) : Type :=
  Σ i : Fin m, ((Fin (ρs i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) × (Fin (ρs i).n → ℂ)

/-- An element of a supremum of type pieces is a finite sum of entries. -/
private theorem exists_list_of_mem_iSup (m : ℕ) (ρs : Fin m → ArchRepAt F w)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : f ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    ∃ l : List (archEntry F w m ρs),
      (∀ e ∈ l, IsRightEquivariant (rowIsometryInclAt₀ F w) (ρs e.1).ρ e.2.1) ∧
      f = (l.map fun e => e.2.1 e.2.2).sum := by
  refine Submodule.iSup_induction _
    (motive := fun f => ∃ l : List (archEntry F w m ρs),
      (∀ e ∈ l, IsRightEquivariant (rowIsometryInclAt₀ F w) (ρs e.1).ρ e.2.1) ∧
      f = (l.map fun e => e.2.1 e.2.2).sum)
    hf ?_ ?_ ?_
  · intro i f hfi
    change f ∈ typeSubmodule (rowIsometryInclAt₀ F w) (ρs i).ρ at hfi
    unfold typeSubmodule at hfi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hfi
    · rintro _ ⟨T, hT, v, rfl⟩
      exact ⟨[⟨i, T, v⟩], by simp [hT], by simp⟩
    · exact ⟨[], by simp, by simp⟩
    · rintro f g - - ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
      refine ⟨l₁ ++ l₂, fun e he => ?_, by simp⟩
      rcases List.mem_append.mp he with he | he
      · exact h₁ e he
      · exact h₂ e he
    · rintro c f - ⟨l, hl, rfl⟩
      refine ⟨l.map fun e => ⟨e.1, e.2.1, c • e.2.2⟩, fun e he => ?_, ?_⟩
      · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact hl e' he'
      · rw [List.smul_sum, List.map_map, List.map_map]
        congr 1
        refine List.map_congr_left fun e _ => ?_
        simp
  · exact ⟨[], by simp, by simp⟩
  · rintro f g ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
    refine ⟨l₁ ++ l₂, fun e he => ?_, by simp⟩
    rcases List.mem_append.mp he with he | he
    · exact h₁ e he
    · exact h₂ e he

variable {F w}

/-- An equivariant map out of `Fin d → ℂ` is a map of the associated `ℂ[K]`-modules. -/
private def linOfEquivariant {d : ℕ}
    (σ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ))
    (T : (Fin d → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (hT : IsRightEquivariant (rowIsometryInclAt₀ F w) σ T) :
    σ.asModule →ₗ[ℂ[rowIsometrySubgroup₀ w.Completion]] rowModule F w where
  toFun v := (rowRightRegular F w).asModuleEquiv.symm (T (σ.asModuleEquiv v))
  map_add' x y := by simp
  map_smul' c v := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [add_smul, map_add, hx, hy]
    | single k t =>
        rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single, LinearMap.smul_apply,
          map_smul, RingHom.id_apply]
        apply (rowRightRegular F w).asModuleEquiv.injective
        rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul,
          Representation.asAlgebraHom_single, LinearMap.smul_apply, LinearEquiv.apply_symm_apply]
        congr 1
        funext x
        exact hT k (σ.asModuleEquiv v) x

private theorem linOfEquivariant_apply {d : ℕ}
    (σ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ))
    (T : (Fin d → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (hT : IsRightEquivariant (rowIsometryInclAt₀ F w) σ T) (v : σ.asModule) :
    (rowRightRegular F w).asModuleEquiv (linOfEquivariant σ T hT v) = T (σ.asModuleEquiv v) := rfl

end FiniteSubquotientReduction

section SubquotientOfSupremum

open scoped MonoidAlgebra
open CuspidalConstituent

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

private theorem sum_univ_get_map {α M : Type*} [AddCommMonoid M] (l : List α) (g : α → M) :
    ∑ s : Fin l.length, g (l.get s) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      change ∑ s : Fin (l.length + 1), g ((a :: l).get s) = _
      rw [Fin.sum_univ_succ]
      simp

/-- A finite-dimensional stable submodule of a supremum of type pieces is a subquotient of a
finite product of the corresponding associated modules. -/
private theorem isSubquotient_of_le_iSup (m : ℕ) (ρs : Fin m → ArchRepAt F w)
    (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    [FiniteDimensional ℂ ↥S] (hle : S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    ∃ (n : ℕ) (idx : Fin n → Fin m),
      IsSubquotient ℂ[rowIsometrySubgroup₀ w.Completion]
        (∀ t : Fin n, (ρs (idx t)).ρ.asModule) ↥(stableSubmodule S hS) := by
  classical
  let b := Module.finBasis ℂ ↥S
  choose L hLeq hLsum using fun l : Fin (Module.finrank ℂ ↥S) =>
    exists_list_of_mem_iSup F w m ρs ((b l : ↥S) : AdelicGL2 (𝓞 F) F → ℂ) (hle (b l).2)
  let I : Type := Σ l : Fin (Module.finrank ℂ ↥S), Fin (L l).length
  let ent : I → archEntry F w m ρs := fun p => (L p.1).get p.2
  have hent : ∀ p : I, IsRightEquivariant (rowIsometryInclAt₀ F w) (ρs (ent p).1).ρ (ent p).2.1 :=
    fun p => hLeq p.1 _ (List.get_mem _ _)
  let X : I → Type := fun p => (ρs (ent p).1).ρ.asModule
  let Θ : (∀ p : I, X p) →ₗ[ℂ[rowIsometrySubgroup₀ w.Completion]] rowModule F w :=
    ∑ p : I, (linOfEquivariant (ρs (ent p).1).ρ (ent p).2.1 (hent p)) ∘ₗ LinearMap.proj p
  have hΘ : ∀ l : Fin (Module.finrank ℂ ↥S), ∃ x : ∀ p : I, X p,
      (rowRightRegular F w).asModuleEquiv (Θ x) = ((b l : ↥S) : AdelicGL2 (𝓞 F) F → ℂ) := by
    intro l
    let x : ∀ p : I, X p :=
      fun p => if p.1 = l then (ρs (ent p).1).ρ.asModuleEquiv.symm (ent p).2.2 else 0
    refine ⟨x, ?_⟩
    rw [hLsum l]
    have hgoal : (rowRightRegular F w).asModuleEquiv (Θ x)
        = ∑ p : I, (if p.1 = l then (ent p).2.1 (ent p).2.2 else 0) := by
      simp only [Θ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, map_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      change (rowRightRegular F w).asModuleEquiv (linOfEquivariant (ρs (ent p).1).ρ (ent p).2.1 (hent p)
        (if p.1 = l then (ρs (ent p).1).ρ.asModuleEquiv.symm (ent p).2.2 else 0)) = _
      split_ifs with h
      · rw [linOfEquivariant_apply, LinearEquiv.apply_symm_apply]
      · rw [map_zero, map_zero]
    rw [hgoal, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    rw [Finset.sum_eq_single l]
    · have hif : ∀ s : Fin (L l).length,
          (if (⟨l, s⟩ : I).1 = l then (ent ⟨l, s⟩).2.1 (ent ⟨l, s⟩).2.2 else 0)
            = (ent ⟨l, s⟩).2.1 (ent ⟨l, s⟩).2.2 :=
        fun s => ite_eq_left rfl
      refine (Finset.sum_congr rfl fun s _ => hif s).trans ?_
      exact sum_univ_get_map (L l) fun e => e.2.1 e.2.2
    · intro l' _ hl'
      simp [hl']
    · intro h
      exact absurd (Finset.mem_univ l) h
  choose xs hxs using hΘ
  have hrange : ∀ y : ↥(stableSubmodule S hS), ∃ x : ∀ p : I, X p, Θ x = (y : rowModule F w) := by
    intro y
    let ys : ↥S := ⟨(rowRightRegular F w).asModuleEquiv (y : rowModule F w),
      (mem_stableSubmodule_iff S hS _).mp y.2⟩
    refine ⟨∑ l, (b.repr ys l) • xs l, ?_⟩
    apply (rowRightRegular F w).asModuleEquiv.injective
    rw [map_sum, map_sum]
    have hl : ∀ l, (rowRightRegular F w).asModuleEquiv (Θ ((b.repr ys l) • xs l))
        = (b.repr ys l) • ((b l : ↥S) : AdelicGL2 (𝓞 F) F → ℂ) := by
      intro l
      rw [LinearMap.map_smul_of_tower, LinearEquiv.map_smul, hxs l]
    simp only [hl]
    have hsum := congrArg Subtype.val (b.sum_repr ys)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at hsum
    exact hsum
  have hsq : IsSubquotient ℂ[rowIsometrySubgroup₀ w.Completion] (∀ p : I, X p)
      ↥(stableSubmodule S hS) := by
    refine ⟨(stableSubmodule S hS).comap Θ, Θ.restrict (fun x hx => hx), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hrange y
    exact ⟨⟨x, show Θ x ∈ stableSubmodule S hS by rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  let e := Fintype.equivFin I
  exact ⟨Fintype.card I, fun t => (ent (e.symm t)).1,
    hsq.of_ambient_equiv (LinearEquiv.piCongrLeft' ℂ[rowIsometrySubgroup₀ w.Completion] X e)⟩

end SubquotientOfSupremum

section FiniteEntryQuotient

open scoped MonoidAlgebra
open CuspidalConstituent

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

omit [NumberField F] in
/-- An entry quotient of the associated module of a finite-dimensional representation is
finite-dimensional. -/
private theorem finite_entryQuot {d : ℕ}
    (ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ))
    (p : Submodule ℂ[rowIsometrySubgroup₀ w.Completion] ρ.asModule ×
      Submodule ℂ[rowIsometrySubgroup₀ w.Completion] ρ.asModule) :
    Module.Finite ℂ (entryQuot p) := by
  have : Module.Finite ℂ ↥p.1 :=
    Module.Finite.of_injective (p.1.subtype.restrictScalars ℂ) p.1.injective_subtype
  exact Module.Finite.quotient ℂ _

/-- A finite-dimensional stable submodule isomorphic to a representation's associated module
sits in that representation's type piece. -/
private theorem le_typeSubmodule_of_equiv {d : ℕ}
    (σ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ))
    (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (e : σ.asModule ≃ₗ[ℂ[rowIsometrySubgroup₀ w.Completion]] ↥(stableSubmodule S hS)) :
    S ≤ typeSubmodule (rowIsometryInclAt₀ F w) σ := by
  let T : (Fin d → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    (rowRightRegular F w).asModuleEquiv.toLinearMap ∘ₗ
      ((stableSubmodule S hS).subtype.restrictScalars ℂ) ∘ₗ
      (e.toLinearMap.restrictScalars ℂ) ∘ₗ σ.asModuleEquiv.symm.toLinearMap
  have hTapply : ∀ v : Fin d → ℂ,
      T v = (rowRightRegular F w).asModuleEquiv
        ((e (σ.asModuleEquiv.symm v) : ↥(stableSubmodule S hS)) : rowModule F w) := fun v => rfl
  have hT : IsRightEquivariant (rowIsometryInclAt₀ F w) σ T := by
    intro k v x
    rw [hTapply, hTapply, Representation.asModuleEquiv_symm_map_rho, map_smul, Submodule.coe_smul,
      of_smul_eq]
    rfl
  intro g hg
  have hmem : (rowRightRegular F w).asModuleEquiv.symm g ∈ stableSubmodule S hS :=
    (mem_stableSubmodule_iff S hS _).mpr hg
  have hgT : g = T (σ.asModuleEquiv
      (e.symm ⟨(rowRightRegular F w).asModuleEquiv.symm g, hmem⟩)) := by
    rw [hTapply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
    rfl
  rw [hgT]
  exact mem_typeSubmodule_of_isRightEquivariant hT _

end FiniteEntryQuotient

namespace CuspidalConstituent

theorem exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w) :
    ∃ (r : ℕ) (σs : Fin r → ArchRepAt F w), (∀ j, (σs j).ρ.IsIrreducible) ∧
      ∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs j) := by
  classical
  choose lst hlst_simple hlst_cov using fun i : Fin m =>
    exists_list_forall_isSubquotient (isFiniteLength_asModule F w (ρs i).ρ)
  have hreal := fun (i : Fin m)
      (p : Submodule (MonoidAlgebra ℂ ↥(rowIsometrySubgroup₀ w.Completion)) (ρs i).ρ.asModule ×
        Submodule (MonoidAlgebra ℂ ↥(rowIsometrySubgroup₀ w.Completion)) (ρs i).ρ.asModule) =>
    @exists_representation_fin_nonempty_equiv (rowIsometrySubgroup₀ w.Completion) _
      (entryQuot p) _ _ _ _ (finite_entryQuot F w (ρs i).ρ p)
  choose dq σq heq using hreal
  let data : List (ArchRepAt F w) :=
    (List.finRange m).flatMap fun i => (lst i).map fun p => (⟨dq i p, σq i p⟩ : ArchRepAt F w)
  refine ⟨data.length, fun j => data.get j, fun j => ?_, ?_⟩
  ·
    obtain ⟨i, -, hj⟩ := List.mem_flatMap.mp (List.get_mem data j)
    obtain ⟨p, hp, hpj⟩ := List.mem_map.mp hj
    show (data.get j).ρ.IsIrreducible
    rw [← hpj]
    have hsimple := hlst_simple i p hp
    exact isIrreducible_of_equiv (σq i p) (entryQuot p) (heq i p).some
  · intro S hSfd hSst hSne hSsimple hSle
    -- the simplicity of the stable submodule is what the covering list is applied to
    have hSimple : IsSimpleModule (MonoidAlgebra ℂ ↥(rowIsometrySubgroup₀ w.Completion))
        ↥(stableSubmodule S hSst) := isSimpleModule_stableSubmodule F w S hSst hSne hSsimple
    obtain ⟨n, idx, hsq⟩ := isSubquotient_of_le_iSup F w m ρs S hSst hSle
    obtain ⟨t, ht⟩ := hsq.pi_elim
    obtain ⟨p, hp, ⟨e₂⟩⟩ := hlst_cov (idx t) ↥(stableSubmodule S hSst) inferInstance ht
    have hmem : (⟨dq (idx t) p, σq (idx t) p⟩ : ArchRepAt F w) ∈ data :=
      List.mem_flatMap.mpr ⟨idx t, List.mem_finRange _, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
    refine ⟨j, ?_⟩
    show S ≤ archTypeSubmoduleAt F w (data.get j)
    rw [hj]
    exact le_typeSubmodule_of_equiv F w (σq (idx t) p) S hSst ((heq (idx t) p).some.trans e₂)

end CuspidalConstituent

/-! ### Engine: a type piece is the supremum of its nonzero intertwining ranges -/

section TypePiecePieces

variable {H G : Type*} [Group H] [Group G]

/-- Right translation of `G → ℂ` along `ι : H →* G`, as a representation of `H`. -/
private def rightTranslationRep (ι : H →* G) : Representation ℂ H (G → ℂ) where
  toFun k :=
    { toFun := fun f x => f (x * ι k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp
  map_mul' k₁ k₂ := by
    ext f x
    simp [mul_assoc]

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A right equivariant map `W →ₗ (G → ℂ)` is an intertwining map into right translation. -/
private def intertwiningOfEquivariant {ι : H →* G} {ρ : Representation ℂ H W}
    {T : W →ₗ[ℂ] (G → ℂ)} (hT : IsRightEquivariant ι ρ T) :
    ρ.IntertwiningMap (rightTranslationRep ι) where
  toLinearMap := T
  isIntertwining' k := by
    ext v x
    exact hT k v x

/-- The same map, read as a map of the associated `MonoidAlgebra ℂ H`-modules. -/
private abbrev asModuleMap (ι : H →* G) (ρ : Representation ℂ H W)
    (φ : ρ.IntertwiningMap (rightTranslationRep ι)) :
    ρ.asModule →ₗ[MonoidAlgebra ℂ H] (rightTranslationRep ι).asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := rightTranslationRep ι) φ

/-- The nonzero ranges of the intertwining maps `ρ → rightTranslationRep ι`. -/
private def nonzeroRanges (ι : H →* G) (ρ : Representation ℂ H W) :
    Set (Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule) :=
  {m | ∃ φ : ρ.IntertwiningMap (rightTranslationRep ι), LinearMap.range (asModuleMap ι ρ φ) = m ∧ m ≠ ⊥}

/-- Every nonzero intertwining range is a copy of `ρ`, by irreducibility. -/
private theorem nonzeroRanges_equiv (ι : H →* G) (ρ : Representation ℂ H W) [ρ.IsIrreducible] :
    ∀ m ∈ nonzeroRanges ι ρ, Nonempty (m ≃ₗ[MonoidAlgebra ℂ H] ρ.asModule) := by
  rintro m ⟨φ, rfl, hm⟩
  rcases LinearMap.injective_or_eq_zero (asModuleMap ι ρ φ) with hinj | hzero
  · exact ⟨(LinearEquiv.ofInjective _ hinj).symm⟩
  · exact absurd (by rw [hzero, LinearMap.range_zero]) hm

/-- The type piece of `ρ` is the supremum of the nonzero intertwining ranges. -/
private theorem mem_sSup_nonzeroRanges (ι : H →* G) (ρ : Representation ℂ H W) {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) :
    (rightTranslationRep ι).asModuleEquiv.symm f ∈ sSup (nonzeroRanges ι ρ) := by
  refine Submodule.span_induction
    (p := fun f _ => (rightTranslationRep ι).asModuleEquiv.symm f ∈ sSup (nonzeroRanges ι ρ))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hle : LinearMap.range (asModuleMap ι ρ (intertwiningOfEquivariant hT))
        ≤ sSup (nonzeroRanges ι ρ) := by
      by_cases hbot : LinearMap.range (asModuleMap ι ρ (intertwiningOfEquivariant hT)) = ⊥
      · rw [hbot]
        exact bot_le
      · exact le_sSup ⟨intertwiningOfEquivariant hT, rfl, hbot⟩
    exact hle (LinearMap.mem_range_self (asModuleMap ι ρ (intertwiningOfEquivariant hT))
      (ρ.asModuleEquiv.symm v))
  · simp
  · intro _ _ _ _ hu hw
    rw [map_add]
    exact (sSup (nonzeroRanges ι ρ)).add_mem hu hw
  · intro c _ _ hu
    rw [Representation.asModuleEquiv_symm_map_smul]
    exact (sSup (nonzeroRanges ι ρ)).smul_mem _ hu

end TypePiecePieces

/-- A nonzero element of two suprema of simple modules forces the simple modules to agree. -/
private theorem nonempty_linearEquiv_of_mem_sSup_of_mem_sSup
    {R M S S' : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup S] [Module R S] [IsSimpleModule R S] [AddCommGroup S'] [Module R S'] [IsSimpleModule R S']
    {s s' : Set (Submodule R M)} (hs : ∀ m ∈ s, Nonempty (m ≃ₗ[R] S))
    (hs' : ∀ m ∈ s', Nonempty (m ≃ₗ[R] S'))
    {x : M} (hx : x ≠ 0) (h1 : x ∈ sSup s) (h2 : x ∈ sSup s') : Nonempty (S ≃ₗ[R] S') := by
  have simple_s : ∀ m : s, IsSimpleModule R m := fun m => IsSimpleModule.congr (hs m m.2).some
  have simple_s' : ∀ m : s', IsSimpleModule R m := fun m => IsSimpleModule.congr (hs' m m.2).some
  have hsemi : IsSemisimpleModule R ↥(sSup s) := by
    rw [sSup_eq_iSup]
    exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule (p := fun m : Submodule R M => m)
      (fun m hm => by
        have hsimple := simple_s ⟨m, hm⟩
        exact inferInstance)
  have hP : IsSemisimpleModule R ↥(sSup s ⊓ sSup s') :=
    IsSemisimpleModule.of_injective (Submodule.inclusion (inf_le_left : sSup s ⊓ sSup s' ≤ sSup s))
      (Submodule.inclusion_injective _)
  rcases IsSemisimpleModule.eq_bot_or_exists_simple_le (sSup s ⊓ sSup s') with hbot | ⟨N, hNle, hN⟩
  · have hmem : x ∈ sSup s ⊓ sSup s' := Submodule.mem_inf.2 ⟨h1, h2⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact (hx hmem).elim
  · have hNsimple := hN
    obtain ⟨m, hm, ⟨e₁⟩⟩ := Submodule.linearEquiv_of_le_sSup N s (le_trans hNle inf_le_left)
    obtain ⟨m', hm', ⟨e₂⟩⟩ := Submodule.linearEquiv_of_le_sSup N s' (le_trans hNle inf_le_right)
    exact ⟨(((hs m hm).some.symm.trans e₁.symm).trans e₂).trans (hs' m' hm').some⟩

section EquivOfModules

variable {H : Type*} [Group H] {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W']
  [Module ℂ W']

/-- A module isomorphism of the associated `MonoidAlgebra ℂ H`-modules is an equivalence of
representations. -/
private def equivOfAsModule {ρ : Representation ℂ H W} {ρ' : Representation ℂ H W'}
    (e : ρ.asModule ≃ₗ[MonoidAlgebra ℂ H] ρ'.asModule) : ρ.Equiv ρ' :=
  let φ : ρ.IntertwiningMap ρ' :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := ρ')).symm e.toLinearMap
  have hbij : Function.Bijective φ.toLinearMap := e.bijective
  Representation.Equiv.mk (LinearEquiv.ofBijective φ.toLinearMap hbij) fun g => by
    ext v
    exact LinearMap.congr_fun (φ.isIntertwining' g) v

end EquivOfModules

section MeetOfPieces

variable {H G : Type*} [Group H] [Group G] {W W' : Type*} [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W']

/-- A nonzero element of the intersection of two type pieces makes the representations
equivalent. -/
private theorem nonempty_equiv_of_mem_inf (ι : H →* G) (ρ : Representation ℂ H W)
    (ρ' : Representation ℂ H W') [ρ.IsIrreducible] [ρ'.IsIrreducible] {f : G → ℂ}
    (hf₁ : f ∈ typeSubmodule ι ρ) (hf₂ : f ∈ typeSubmodule ι ρ') (hf0 : f ≠ 0) :
    Nonempty (ρ.Equiv ρ') := by
  have hx : (rightTranslationRep ι).asModuleEquiv.symm f ≠ 0 := fun h =>
    hf0 ((LinearEquiv.map_eq_zero_iff _).1 h)
  obtain ⟨e⟩ := nonempty_linearEquiv_of_mem_sSup_of_mem_sSup (nonzeroRanges_equiv ι ρ)
    (nonzeroRanges_equiv ι ρ') hx (mem_sSup_nonzeroRanges ι ρ hf₁) (mem_sSup_nonzeroRanges ι ρ' hf₂)
  exact ⟨equivOfAsModule e⟩

end MeetOfPieces

theorem typeSubmodule_inf_typeSubmodule_eq_bot
    {H G : Type*} [Group H] [Group G]
    {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    [ρ.IsIrreducible] [ρ'.IsIrreducible] (hne : IsEmpty (ρ.Equiv ρ')) :
    typeSubmodule ι ρ ⊓ typeSubmodule ι ρ' = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  by_contra hf0
  exact hne.elim (nonempty_equiv_of_mem_inf ι ρ ρ' (Submodule.mem_inf.1 hf).1
    (Submodule.mem_inf.1 hf).2 hf0).some

end AutomorphicForm
