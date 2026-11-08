/-
  The archimedean type lattice, and the isotypic cusp submodule.

  `typeSubmodule F tys ρ` is the space of vectors whose archimedean type at `w` lies in a component of
  the family `tys`; `archTypeSubmoduleAt F tys w τ` is the `τ`-isotypic part at `w`; `isotypicCuspSubmodule`
  is their supremum inside the cusp subcarrier. This module carries the lattice algebra those three
  need:

  * `exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates`: a continuous linear
    map out of a supremum of type submodules, whose range is the span of the right translates — the
    interpolation statement the cut arguments use;
  * `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule`: membership in the isotypic cusp submodule implies
    the pointwise isotypic predicate (the direction the spectrum theory consumes — the row has **27
    project consumers**);
  * `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous`: the infimum of a
    supremum of `τ`-isotypic parts is bounded by the supremum of the infima, for continuous data;
  * `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow`: conjugating an archimedean test
    factor by `c⁻¹` and multiplying by `‖det‖ ^ r` keeps it a test factor — the character twist the
    archimedean cut is stable under.

  Transcribed from the pin's four `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`,
  390 + 242 + 214 + 282 lines).

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.ArchApproximation
import FLTForHuman.AutomorphicForm.Adelic.ArchCompactOrbit
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothLeft
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArchTypeSpan
import FLTForHuman.AutomorphicForm.Adelic.Siegel.Covering
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDetGlue
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.RepresentationTheory.CompactGroup

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent MeasureTheory
open IsDedekindDomain Filter Matrix Complex ComplexConjugate
open scoped ENNReal Topology

namespace AutomorphicForm

namespace Ws49
namespace K1

section Translation

variable {K G : Type*} [Group K] [Group G]

def Rtr (ι : K →* G) (k : K) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u y := u (y * ι k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Rtr_apply (ι : K →* G) (k : K) (u : G → ℂ) (y : G) : Rtr ι k u y = u (y * ι k) := rfl

def Rrep (ι : K →* G) (V : Submodule ℂ (G → ℂ)) (hV : ∀ k : K, ∀ u ∈ V, Rtr ι k u ∈ V) :
    Representation ℂ K V where
  toFun k := (Rtr ι k).restrict (hV k)
  map_one' := by
    refine LinearMap.ext fun u => Subtype.ext (funext fun y => ?_)
    show (u : G → ℂ) (y * ι 1) = (u : G → ℂ) y
    rw [map_one, mul_one]
  map_mul' a c := by
    refine LinearMap.ext fun u => Subtype.ext (funext fun y => ?_)
    show (u : G → ℂ) (y * ι (a * c)) = (u : G → ℂ) (y * ι a * ι c)
    rw [map_mul, mul_assoc]

theorem Rrep_apply (ι : K →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ k : K, ∀ u ∈ V, Rtr ι k u ∈ V)
    (k : K) (u : V) (y : G) : (Rrep ι V hV k u : G → ℂ) y = (u : G → ℂ) (y * ι k) := rfl

def Py (ι : K →* G) (y : G) : (G → ℂ) →ₗ[ℂ] (K → ℂ) where
  toFun g k := g (y * ι k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem Py_apply (ι : K →* G) (y : G) (g : G → ℂ) (k : K) : Py ι y g k = g (y * ι k) := rfl

theorem Py_mem_typeSubmodule {W : Type*} [AddCommGroup W] [Module ℂ W] (ι : K →* G)
    (ρ : Representation ℂ K W) (y : G) {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ) :
    Py ι y f ∈ typeSubmodule (MonoidHom.id K) ρ := by
  have hle : typeSubmodule ι ρ ≤ (typeSubmodule (MonoidHom.id K) ρ).comap (Py ι y) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨T, hT, v, rfl⟩
    let T' : W →ₗ[ℂ] (K → ℂ) := (Py ι y).comp T
    have hT' : IsRightEquivariant (MonoidHom.id K) ρ T' := by
      intro k w x
      show T (ρ k w) (y * ι x) = T w (y * ι (x * k))
      rw [hT k w (y * ι x), map_mul, mul_assoc]
    exact mem_typeSubmodule_of_isRightEquivariant hT' v
  exact hle hf

theorem Py_mem_iSup_typeSubmodule {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)]
    [∀ i, Module ℂ (W i)] (ι : K →* G) (ρ : ∀ i, Representation ℂ K (W i)) (y : G) {f : G → ℂ}
    (hf : f ∈ ⨆ i, typeSubmodule ι (ρ i)) :
    Py ι y f ∈ ⨆ i, typeSubmodule (MonoidHom.id K) (ρ i) := by
  have hle : (⨆ i, typeSubmodule ι (ρ i)) ≤
      (⨆ i, typeSubmodule (MonoidHom.id K) (ρ i)).comap (Py ι y) :=
    iSup_le fun i f hf => le_iSup (fun i => typeSubmodule (MonoidHom.id K) (ρ i)) i
      (Py_mem_typeSubmodule ι (ρ i) y hf)
  exact hle hf

end Translation

theorem exists_fin_forall_eq_zero {E V : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] [AddCommGroup V] [Module ℂ V] {Y : Type*} (L : Y → E →ₗ[ℂ] V)
    (h : ∀ v : E, (∀ y, L y v = 0) → v = 0) :
    ∃ (m : ℕ) (ys : Fin m → Y), ∀ v : E, (∀ j, L (ys j) v = 0) → v = 0 := by
  classical
  let N : Finset Y → Submodule ℂ E := fun s => ⨅ y ∈ s, LinearMap.ker (L y)
  have hN : ∀ (s : Finset Y) (v : E), v ∈ N s ↔ ∀ y ∈ s, L y v = 0 := by
    intro s v
    simp only [N, Submodule.mem_iInf, LinearMap.mem_ker]
  have hex : ∃ d, ∃ s : Finset Y, Module.finrank ℂ (N s) = d := ⟨_, ∅, rfl⟩
  obtain ⟨s0, hs0⟩ := Nat.find_spec hex
  have hmin : ∀ s : Finset Y, Module.finrank ℂ (N s0) ≤ Module.finrank ℂ (N s) := fun s => by
    rw [hs0]
    exact Nat.find_min' hex ⟨s, rfl⟩
  have hle : ∀ y, N s0 ≤ LinearMap.ker (L y) := by
    intro y v hv
    have h1 : N (insert y s0) ≤ N s0 := by
      intro w hw
      rw [hN] at hw ⊢
      exact fun y' hy' => hw y' (Finset.mem_insert_of_mem hy')
    have h2 : N (insert y s0) = N s0 := Submodule.eq_of_le_of_finrank_le h1 (hmin _)
    rw [← h2, hN] at hv
    exact hv y (Finset.mem_insert_self y s0)
  refine ⟨Fintype.card s0, fun j => ((Fintype.equivFin s0).symm j : s0), fun v hv => h v fun y => ?_⟩
  have hv0 : v ∈ N s0 := by
    rw [hN]
    intro y' hy'
    have := hv (Fintype.equivFin s0 ⟨y', hy'⟩)
    dsimp only at this
    rwa [Equiv.symm_apply_apply] at this
  exact hle y hv0

section Coeff

variable {K : Type*} [Group K]

def mcMap {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W) :
    Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (K → ℂ) where
  toFun μ k := μ (ρ k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem typeSubmodule_id_le_range {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) :
    typeSubmodule (MonoidHom.id K) ρ ≤ LinearMap.range (mcMap ρ) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨T, hT, v, rfl⟩
  refine ⟨(LinearMap.proj (1 : K)).comp (T.comp (LinearMap.applyₗ v)), funext fun k => ?_⟩
  show T (ρ k v) 1 = T v k
  rw [hT k v 1, one_mul]
  rfl

private instance finiteDimensional_typeSubmodule_id {W : Type*} [AddCommGroup W] [Module ℂ W]
    [Module.Finite ℂ W] (ρ : Representation ℂ K W) :
    FiniteDimensional ℂ (typeSubmodule (MonoidHom.id K) ρ) :=
  Submodule.finiteDimensional_of_le (typeSubmodule_id_le_range ρ)

def contSubmodule (K : Type*) [TopologicalSpace K] : Submodule ℂ (K → ℂ) where
  carrier := {u | Continuous u}
  add_mem' hu hv := hu.add hv
  zero_mem' := continuous_const
  smul_mem' c u hu := by
    show Continuous fun x => c • u x
    exact hu.const_smul c

variable [TopologicalSpace K] [IsTopologicalGroup K]

theorem continuous_dual_Rrep (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ k : K, ∀ u ∈ V, Rtr (MonoidHom.id K) k u ∈ V) (hVc : ∀ u ∈ V, Continuous u)
    (φ : Module.Dual ℂ V) (u : V) :
    Continuous fun k => φ (Rrep (MonoidHom.id K) V hV k u) := by
  obtain ⟨m, xs, hxs⟩ := exists_fin_forall_eq_zero
    (fun x : K => (LinearMap.proj x).comp V.subtype) (fun v hv => Subtype.ext (funext fun x => hv x))
  let ev : V →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun j => (LinearMap.proj (xs j)).comp V.subtype
  have hev : LinearMap.ker ev = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hxs v fun j => congr_fun hv j
  obtain ⟨g, hg⟩ := ev.exists_leftInverse_of_injective hev
  have hφ : (fun k => φ (Rrep (MonoidHom.id K) V hV k u)) =
      (φ.comp g) ∘ fun k => ev (Rrep (MonoidHom.id K) V hV k u) := by
    funext k
    show φ _ = φ (g (ev _))
    rw [← LinearMap.comp_apply g ev, hg, LinearMap.id_apply]
  rw [hφ]
  refine (LinearMap.continuous_of_finiteDimensional _).comp (continuous_pi fun j => ?_)
  show Continuous fun k => (u : K → ℂ) (xs j * k)
  exact (hVc u u.2).comp (continuous_const.mul continuous_id)

end Coeff

section Mat

variable {K : Type*} [Group K] {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def matRep (b : Module.Basis (Fin n) ℂ V) (R : Representation ℂ K V) :
    K →* Matrix (Fin n) (Fin n) ℂ where
  toFun k := LinearMap.toMatrix b b (R k)
  map_one' := by
    rw [map_one]
    exact LinearMap.toMatrix_one b
  map_mul' a c := by
    rw [map_mul]
    exact LinearMap.toMatrix_mul b (R a) (R c)

theorem matRep_apply (b : Module.Basis (Fin n) ℂ V) (R : Representation ℂ K V) (k : K) :
    matRep b R k = LinearMap.toMatrix b b (R k) := rfl

theorem matRep_mulVec (b : Module.Basis (Fin n) ℂ V) (R : Representation ℂ K V) (k : K)
    (u : V) :
    (matRep b R k).mulVec (b.equivFun u) = b.equivFun (R k u) := by
  rw [b.equivFun_apply, b.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr b b (R k) u

theorem equivFun_symm_mulVec (b : Module.Basis (Fin n) ℂ V) (R : Representation ℂ K V)
    (k : K) (x : Fin n → ℂ) : b.equivFun.symm ((matRep b R k).mulVec x) = R k (b.equivFun.symm x) := by
  rw [LinearEquiv.symm_apply_eq, ← matRep_mulVec, LinearEquiv.apply_symm_apply]

def piRep (m : ℕ) (R : Representation ℂ K V) : Representation ℂ K (Fin m → V) where
  toFun k :=
    { toFun := fun w j => R k (w j)
      map_add' := fun w w' => funext fun j => map_add _ _ _
      map_smul' := fun c w => funext fun j => map_smul _ _ _ }
  map_one' := by
    refine LinearMap.ext fun w => funext fun j => ?_
    show R 1 (w j) = w j
    rw [map_one]
    rfl
  map_mul' a c := by
    refine LinearMap.ext fun w => funext fun j => ?_
    show R (a * c) (w j) = R a (R c (w j))
    rw [map_mul]
    rfl

theorem piRep_apply (m : ℕ) (R : Representation ℂ K V) (k : K) (w : Fin m → V)
    (j : Fin m) : piRep m R k w j = R k (w j) := rfl

end Mat

end Ws49.K1

open Ws49.K1 in
theorem exists_continuous_forall_typeSubmodule_le_iSup_and_range_eq_span_translates
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    {I : Type*} [Finite I] {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    [∀ i, Module.Finite ℂ (W i)] (ρ : ∀ i, Representation ℂ K (W i)) :
    ∃ (n : ℕ) (ρc : K →* Matrix (Fin n) (Fin n) ℂ), Continuous ρc ∧
      ∀ (G : Type*) [Group G] (ι : K →* G), Function.Injective ι →
        (∀ (T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)),
          (∀ (k : K) (x : Fin n → ℂ), T ((ρc k).mulVec x) = fun y => T x (y * ι k)) →
          ∀ x : Fin n → ℂ, T x ∈ ⨆ i, typeSubmodule ι (ρ i)) ∧
        (∀ f ∈ ⨆ i, typeSubmodule ι (ρ i), (∀ y : G, Continuous fun k : K => f (y * ι k)) →
          ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] (G → ℂ)),
            (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun j => (ρc k).mulVec (x j)) = fun y => T x (y * ι k)) ∧
            LinearMap.range T = Submodule.span ℂ (Set.range fun k : K => fun y : G => f (y * ι k)))
    := by
  classical

  let M : Submodule ℂ (K → ℂ) := ⨆ i, typeSubmodule (MonoidHom.id K) (ρ i)
  let V : Submodule ℂ (K → ℂ) := M ⊓ contSubmodule K
  have hMst : ∀ k : K, ∀ u ∈ M, Rtr (MonoidHom.id K) k u ∈ M := by
    intro k u hu
    have hle : M ≤ M.comap (Rtr (MonoidHom.id K) k) :=
      iSup_le fun i u hu => le_iSup (fun i => typeSubmodule (MonoidHom.id K) (ρ i)) i
        (comp_mul_mem_typeSubmodule hu k)
    exact hle hu
  have hV : ∀ k : K, ∀ u ∈ V, Rtr (MonoidHom.id K) k u ∈ V := by
    intro k u hu
    refine ⟨hMst k u hu.1, ?_⟩
    show Continuous fun x => u (x * k)
    exact (show Continuous u from hu.2).comp (continuous_id.mul continuous_const)
  have hVc : ∀ u ∈ V, Continuous u := fun u hu => hu.2
  have : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  let R : Representation ℂ K V := Rrep (MonoidHom.id K) V hV
  have hRc : ∀ (φ : Module.Dual ℂ V) (u : V), Continuous fun k => φ (R k u) :=
    continuous_dual_Rrep V hV hVc

  let n := Module.finrank ℂ V
  let b : Module.Basis (Fin n) ℂ V := Module.finBasis ℂ V
  let ρc : K →* Matrix (Fin n) (Fin n) ℂ := matRep b R
  have hρc : Continuous ρc := by
    refine continuous_pi fun a => continuous_pi fun c => ?_
    show Continuous fun k => LinearMap.toMatrix b b (R k) a c
    simp only [LinearMap.toMatrix_apply]
    exact hRc (b.coord a) (b c)
  refine ⟨n, ρc, hρc, fun G _ ι hι => ⟨?_, ?_⟩⟩
  ·
    intro T hT x
    let A : V →ₗ[ℂ] (G → ℂ) := T.comp b.equivFun.toLinearMap
    have hA : ∀ (k : K) (u : V) (y : G),
        A ⟨fun κ => (u : K → ℂ) (κ * (MonoidHom.id K) k), hV k u u.2⟩ y = A u (y * ι k) := by
      intro k u y
      show T (b.equivFun (R k u)) y = T (b.equivFun u) (y * ι k)
      rw [← matRep_mulVec, hT]
    let u : V := b.equivFun.symm x
    have hmem := apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective (MonoidHom.id K) ι hι
      V (fun k u hu => hV k u hu) A hA ρ (u : K → ℂ) u.2 u.2.1
    have hAu : A ⟨(u : K → ℂ), u.2⟩ = T x := by
      show T (b.equivFun (b.equivFun.symm x)) = T x
      rw [LinearEquiv.apply_symm_apply]
    rwa [hAu] at hmem
  ·
    intro f hf hfc

    have hfy : ∀ y : G, Py ι y f ∈ V := fun y =>
      ⟨Py_mem_iSup_typeSubmodule ι ρ y hf, hfc y⟩
    let E : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun k : K => fun y : G => f (y * ι k))

    have hE : ∀ k : K, ∀ g ∈ E, Rtr ι k g ∈ E := by
      intro k g hg
      have hle : E.map (Rtr ι k) ≤ E := by
        refine (Submodule.map_span_le _ _ _).mpr ?_
        rintro _ ⟨k', rfl⟩
        refine Submodule.subset_span ⟨k * k', funext fun y => ?_⟩
        show f (y * ι (k * k')) = f (y * ι k * ι k')
        rw [map_mul, mul_assoc]
      exact hle (Submodule.mem_map_of_mem hg)

    have hEV : ∀ y : G, ∀ g ∈ E, Py ι y g ∈ V := by
      intro y
      have hle : E ≤ V.comap (Py ι y) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨k', rfl⟩
        have heq : Py ι y (fun y' : G => f (y' * ι k')) = Rtr (MonoidHom.id K) k' (Py ι y f) := by
          funext κ
          show f (y * ι κ * ι k') = f (y * ι (κ * k'))
          rw [map_mul, mul_assoc]
        show Py ι y _ ∈ V
        rw [heq]
        exact hV k' _ (hfy y)
      exact fun g hg => hle hg

    let Θ : Module.End ℂ V →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun A y => ((A ⟨Py ι y f, hfy y⟩ : V) : K → ℂ) 1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hEΘ : E ≤ LinearMap.range Θ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨R k, funext fun y => ?_⟩
      show f (y * ι (1 * k)) = f (y * ι k)
      rw [one_mul]
    have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le hEΘ

    let RE : Representation ℂ K E := Rrep ι E hE
    let L : G → E →ₗ[ℂ] V := fun y => (Py ι y).restrict (hEV y)
    have hL : ∀ g : E, (∀ y, L y g = 0) → g = 0 := by
      intro g hg
      refine Subtype.ext (funext fun y => ?_)
      have h1 := congr_fun (congrArg Subtype.val (hg y)) 1
      change (g : G → ℂ) (y * ι 1) = 0 at h1
      rw [map_one, mul_one] at h1
      exact h1
    obtain ⟨m, ys, hys⟩ := exists_fin_forall_eq_zero L hL
    let jm : E →ₗ[ℂ] (Fin m → V) := LinearMap.pi fun j => L (ys j)
    have hj : Function.Injective jm := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro g hg
      exact hys g fun j => congr_fun hg j

    let Rm : Representation ℂ K (Fin m → V) := piRep m R
    have hjeq : ∀ (k : K) (g : E), jm (RE k g) = Rm k (jm g) := by
      intro k g
      refine funext fun j => Subtype.ext (funext fun κ => ?_)
      show (g : G → ℂ) (ys j * ι κ * ι k) = (g : G → ℂ) (ys j * ι (κ * k))
      rw [map_mul, mul_assoc]

    have hRm : ∀ (ℓ : Module.Dual ℂ (Fin m → V)) (w : Fin m → V),
        Continuous fun k => ℓ (Rm k w) := by
      intro ℓ w
      have heq : (fun k => ℓ (Rm k w)) =
          fun k => ∑ j, (ℓ.comp (LinearMap.single ℂ (fun _ : Fin m => V) j)) (R k (w j)) := by
        funext k
        conv_lhs => rw [← Finset.univ_sum_single (Rm k w)]
        rw [map_sum]
        rfl
      rw [heq]
      exact continuous_finsetSum _ fun j _ => hRc _ _

    have hP : ∀ k : K, ∀ w ∈ LinearMap.range jm, Rm k w ∈ LinearMap.range jm := by
      rintro k _ ⟨g, rfl⟩
      exact ⟨RE k g, hjeq k g⟩
    obtain ⟨Pc, hc, hPc⟩ :=
      Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous Rm hRm
        (LinearMap.range jm) hP
    let lp : (Fin m → V) →ₗ[ℂ] E := LinearMap.linearProjOfIsCompl Pc jm hj hc
    have hlp : ∀ (k : K) (w : Fin m → V), lp (Rm k w) = RE k (lp w) := by
      intro k w
      have hcw : w - jm (lp w) ∈ Pc := by
        rw [← LinearMap.ker_linearProjOfIsCompl Pc jm hj hc, LinearMap.mem_ker, map_sub,
          LinearMap.linearProjOfIsCompl_apply_left, sub_self]
      have hw : w = jm (lp w) + (w - jm (lp w)) := by abel
      calc lp (Rm k w) = lp (Rm k (jm (lp w)) + Rm k (w - jm (lp w))) := by
            rw [← map_add, ← hw]
        _ = lp (jm (RE k (lp w))) + lp (Rm k (w - jm (lp w))) := by rw [map_add, hjeq]
        _ = RE k (lp w) := by
            rw [LinearMap.linearProjOfIsCompl_apply_left,
              LinearMap.linearProjOfIsCompl_apply_right' _ _ _ _ _ (hPc k _ hcw), add_zero]

    let Φ : (Fin m → (Fin n → ℂ)) ≃ₗ[ℂ] (Fin m → V) :=
      LinearEquiv.piCongrRight fun _ => b.equivFun.symm
    have hΦ : ∀ (k : K) (x : Fin m → (Fin n → ℂ)),
        Φ (fun j => (ρc k).mulVec (x j)) = Rm k (Φ x) := by
      intro k x
      funext j
      show b.equivFun.symm ((matRep b R k).mulVec (x j)) = R k (b.equivFun.symm (x j))
      exact equivFun_symm_mulVec b R k (x j)
    refine ⟨m, E.subtype.comp (lp.comp Φ.toLinearMap), ?_, ?_⟩
    · intro k x
      show ((lp (Φ (fun j => (ρc k).mulVec (x j))) : E) : G → ℂ) =
        fun y => ((lp (Φ x) : E) : G → ℂ) (y * ι k)
      rw [hΦ, hlp]
      rfl
    · have hlpr : LinearMap.range lp = ⊤ :=
        LinearMap.range_eq_top.mpr fun g => ⟨jm g, LinearMap.linearProjOfIsCompl_apply_left _ _ _ _ g⟩
      have h1 : LinearMap.range (lp.comp Φ.toLinearMap) = ⊤ := by
        rw [LinearMap.range_comp_of_range_eq_top _ Φ.range, hlpr]
      rw [LinearMap.range_comp_of_range_eq_top _ h1, Submodule.range_subtype]

/-! ### Membership in the isotypic cusp submodule

The isotypic cusp submodule is the `ℂ`-span of the isotypic forms, so membership is
`Submodule.span_induction` once the defining predicate is closed under sums and scalar
multiples. Each clause of `IsIsotypicCuspFormAt` is answered separately: the
smooth-cuspidal part through the `LsXi`/cuspidality/`Kf`-smoothness clauses, the Hecke
eigenvalue clause through the independence of the Hecke coset sum
(`HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem`). -/

namespace IsotypicSpanForms

section Cusp

variable {F : Type} [Field F] [NumberField F]

-- The pin's `letI`s feed instance search; the local instances answer them without a proof-local `letI`.
attribute [local instance] NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

/-- The constant-term slice of a continuous function is integrable against the conditional
adelic Haar measure of the box: it is continuous, hence integrable on any compact set
containing the box. -/
theorem integrable_slice_cond {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (x : AdelicGL2 (𝓞 F) F) :
    @Integrable _ _ _ _ (adeleBorel (𝓞 F) F)
      (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x))
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  have hcont : Continuous fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x) :=
    hφ.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul continuous_const)
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hIB : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * x)) (adelicBox F)
      (adelicAddHaar (𝓞 F) F) :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
  rw [ProbabilityTheory.cond]
  exact hIB.smul_measure (ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne')

/-- Cuspidality is closed under addition. -/
theorem isCuspidalFn_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ)
    (hψc : Continuous ψ)
    (hφ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 φ)
    (hψ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 ψ) :
    @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (φ + ψ) := by
  intro g
  have h1 := hφ g
  have h2 := hψ g
  unfold constantTerm constantTermIntegrand at h1 h2 ⊢
  simp only [Pi.add_apply]
  rw [integral_add (integrable_slice_cond hφc g) (integrable_slice_cond hψc g),
    h1, h2, add_zero]

/-- Cuspidality is closed under scalar multiplication. -/
theorem isCuspidalFn_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 φ) :
    @IsCuspidalFn _ (adeleBorel (𝓞 F) F) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F))
      unipotentGL2 (a • φ) := by
  intro g
  have h1 := hφ g
  unfold constantTerm constantTermIntegrand at h1 ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, h1, mul_zero]

section KfSmooth

open FLT.SmoothVectors

/-- `Kf`-smoothness is closed under addition: the smooth vectors of a representation form
an additive submonoid, and an intersection of open stabilizers is open. -/
theorem isKfSmooth_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ)
    (hψ : IsKfSmooth F ψ) : IsKfSmooth F (φ + ψ) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup] at hφ hψ ⊢
  obtain ⟨V₁, hV₁o, hV₁⟩ := hφ
  obtain ⟨V₂, hV₂o, hV₂⟩ := hψ
  refine ⟨V₁ ⊓ V₂, ?_, fun u hu => ?_⟩
  · rw [Subgroup.coe_inf]
    exact hV₁o.inter hV₂o
  · obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
    have h1 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₁ u hu1)
    have h2 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₂ u hu2)
    refine RightTranslationFn.ext fun y => ?_
    simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk,
      Pi.add_apply] at h1 h2 ⊢
    rw [h1 y, h2 y]

/-- `Kf`-smoothness is closed under scalar multiplication. -/
theorem isKfSmooth_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : IsKfSmooth F φ) : IsKfSmooth F (a • φ) := by
  rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup] at hφ ⊢
  obtain ⟨V₁, hV₁o, hV₁⟩ := hφ
  refine ⟨V₁, hV₁o, fun u hu => ?_⟩
  have h1 := fun y => congrArg (fun f => RightTranslationFn.toFun f y) (hV₁ u hu)
  refine RightTranslationFn.ext fun y => ?_
  simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk,
    Pi.smul_apply] at h1 ⊢
  rw [h1 y]

end KfSmooth

/-- The `LsXi`-membership predicate is closed under addition on the nose: left invariance
and the central character are linear in the function. -/
private theorem isLsXiFunction_add {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ}
    {ξ : Z →* ℂˣ} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ)
    (hψ : IsLsXiFunction (𝓞 F) F Z ξ ψ) : IsLsXiFunction (𝓞 F) F Z ξ (φ + ψ) := by
  refine ⟨fun γ g => ?_, fun z g => ?_⟩
  · simp only [Pi.add_apply, hφ.left_invariant γ g, hψ.left_invariant γ g]
  · simp only [Pi.add_apply, hφ.central_transform z g, hψ.central_transform z g, mul_add]

/-- The `LsXi`-membership predicate is closed under scalar multiplication. -/
private theorem isLsXiFunction_smul {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ}
    {ξ : Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : IsLsXiFunction (𝓞 F) F Z ξ φ) : IsLsXiFunction (𝓞 F) F Z ξ (a • φ) := by
  refine ⟨fun γ g => ?_, fun z g => ?_⟩
  · simp only [Pi.smul_apply, hφ.left_invariant γ g]
  · simp only [Pi.smul_apply, smul_eq_mul, hφ.central_transform z g]
    ring

end Cusp

section SmoothCuspClauses

variable {F : Type} [Field F] [NumberField F]
variable (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
  (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)

abbrev pp : CarrierPins F := productionPinsOf F D U gen (adelicBox F)

-- The pin's `letI`s feed instance search; the local instances answer them instead.
attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

/-- `IsSmoothCuspAutomorphicFnAt` is closed under addition. -/
theorem isSmoothCuspAutomorphicFnAt_add
    (ξ : (pp D U gen).Z →* ℂˣ)
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ)
    (hψ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ ψ) :
    IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ (φ + ψ) := by
  have hφm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1.1
  have hψm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ ψ).mp hψ.1.1
  have hLs : IsLsXiFunction (𝓞 F) F (pp D U gen).Z ξ (φ + ψ) :=
    isLsXiFunction_add hφm.1 hψm.1
  have hL2 : MemLp (φ + ψ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) :=
    hφm.2.add hψm.2
  refine ⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ (φ + ψ)).mpr
    ⟨hLs, hL2⟩, ?_⟩, ?_⟩
  · exact isCuspidalFn_add hφc hψc hφ.1.2 hψ.1.2
  · exact isKfSmooth_add hφ.2 hψ.2

/-- `IsSmoothCuspAutomorphicFnAt` is closed under scalar multiplication. -/
theorem isSmoothCuspAutomorphicFnAt_smul
    (ξ : (pp D U gen).Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ φ) :
    IsSmoothCuspAutomorphicFnAt F (pp D U gen) ξ (a • φ) := by
  have hφm := (AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ φ).mp hφ.1.1
  have hLs : IsLsXiFunction (𝓞 F) F (pp D U gen).Z ξ (a • φ) :=
    isLsXiFunction_smul a hφm.1
  have hL2 : MemLp (a • φ) 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict D) :=
    hφm.2.const_mul a
  refine ⟨⟨(AutomorphicForm.lsXiMemberAt_iff (𝓞 F) F _ _ ξ _ (a • φ)).mpr
    ⟨hLs, hL2⟩, ?_⟩, ?_⟩
  · exact isCuspidalFn_smul a hφ.1.2
  · exact isKfSmooth_smul a hφ.2

variable (ξ : (pp D U gen).Z →* ℂˣ) (N : Ideal (𝓞 F))
  (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)

/-- `IsIsotypicCuspFormAt` is closed under addition: the eigenvalue clauses are linear
once the Hecke coset sum is known to be representative-independent. -/
theorem isIsotypicCuspFormAt_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ φ)
    (hψ : IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ ψ) :
    IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ (φ + ψ) where
  smoothCusp := isSmoothCuspAutomorphicFnAt_add D U gen ξ hφ.continuous hψ.continuous
    hφ.smoothCusp hψ.smoothCusp
  continuous := hφ.continuous.add hψ.continuous
  level_invariant g u hu := by
    simp only [Pi.add_apply, hφ.level_invariant g u hu, hψ.level_invariant g u hu]
  hecke_eigen v hv := by
    obtain ⟨reps₁, hsys₁, h₁⟩ := hφ.hecke_eigen v hv
    obtain ⟨reps₂, hsys₂, h₂⟩ := hψ.hecke_eigen v hv
    refine ⟨reps₁, hsys₁, fun g => ?_⟩
    have h₁g := h₁ g
    have h₂g := h₂ g
    unfold SmoothCusp.heckeCosetSum at h₁g h₂g ⊢
    have hind : ∑ i, ψ (g * reps₁ i) = ∑ i, ψ (g * reps₂ i) :=
      HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys₂ hsys₁
        (fun g' u hu => hψ.level_invariant g' u hu) g
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [h₁g, hind, h₂g, mul_add]
  central_eigen v hv g := by
    simp only [Pi.add_apply, hφ.central_eigen v hv g, hψ.central_eigen v hv g, mul_add]

/-- `IsIsotypicCuspFormAt` is closed under scalar multiplication. -/
theorem isIsotypicCuspFormAt_smul {φ : AdelicGL2 (𝓞 F) F → ℂ} (a : ℂ)
    (hφ : IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ φ) :
    IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ (a • φ) where
  smoothCusp := isSmoothCuspAutomorphicFnAt_smul D U gen ξ a hφ.smoothCusp
  continuous := hφ.continuous.const_smul a
  level_invariant g u hu := by
    simp only [Pi.smul_apply, hφ.level_invariant g u hu]
  hecke_eigen v hv := by
    obtain ⟨reps₁, hsys₁, h₁⟩ := hφ.hecke_eigen v hv
    refine ⟨reps₁, hsys₁, fun g => ?_⟩
    have h₁g := h₁ g
    unfold SmoothCusp.heckeCosetSum at h₁g ⊢
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    rw [h₁g]
    ring
  central_eigen v hv g := by
    simp only [Pi.smul_apply, smul_eq_mul, hφ.central_eigen v hv g]
    ring

/-- Every element of the isotypic cusp submodule is either zero or an isotypic form. -/
theorem eq_zero_or_isIsotypicCuspFormAt_of_mem {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ isotypicCuspSubmodule F (pp D U gen) ξ N S Φ) :
    φ = 0 ∨ IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ φ := by
  refine Submodule.span_induction
    (p := fun φ _ => φ = 0 ∨ IsIsotypicCuspFormAt F (pp D U gen) ξ N S Φ φ)
    ?_ ?_ ?_ ?_ hφ
  · exact fun φ h => Or.inr h
  · exact Or.inl rfl
  · intro φ ψ _ _ hφ hψ
    rcases hφ with rfl | hφ
    · simpa using hψ
    rcases hψ with rfl | hψ
    · simpa using Or.inr hφ
    exact Or.inr (isIsotypicCuspFormAt_add D U gen ξ N S Φ hφ hψ)
  · intro a φ _ hφ
    rcases hφ with rfl | hφ
    · exact Or.inl (smul_zero a)
    exact Or.inr (isIsotypicCuspFormAt_smul D U gen ξ N S Φ a hφ)

end SmoothCuspClauses

end IsotypicSpanForms

open IsotypicSpanForms in
theorem isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : φ ∈ isotypicCuspSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ)
    (h0 : φ ≠ 0) :
    IsIsotypicCuspFormAt F (productionPinsOf F D U gen (adelicBox F)) ξ N S Φ φ
    := by
  rcases eq_zero_or_isIsotypicCuspFormAt_of_mem D U gen ξ N S Φ hφ with h | h
  · exact absurd h h0
  · exact h

/-! ### The infimum/supremum exchange for continuous data

`Q ⊓ ⨆ i, archTypeSubmoduleAt w (ρs i) ≤ ⨆ j, Q ⊓ archTypeSubmoduleAt w (σs j)`: a vector
of the cut that also lies in `Q` is captured by finitely many of the `σ`-pieces. The
proof is the pin's `ε`-stability induction on the dimension of the translate span `S`: a
minimal non-zero stable subspace `S₁ ⊆ S` is irreducible, so the hypothesis `hσ` puts it
inside a single `σ`-piece; the compactness of the row-isometry group then splits the rest
off `S₁` with an invariant complement, and induction on `finrank` finishes. -/

namespace CuspidalConstituent

namespace OnePlaceSplit

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

-- The pin's `haveI : CompactSpace (rowIsometrySubgroup₀ w.Completion)`; the port already
-- proves the compactness, so the instance is registered locally instead of re-derived.
attribute [local instance] ArchCompactOrbit.compactSpace_rowIsometrySubgroup₀

private def subRep (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) :
    Representation ℂ (rowIsometrySubgroup₀ w.Completion) ↥S where
  toFun k :=
    { toFun := fun v => ⟨rightTranslate F (rowIsometryInclAt₀ F w k) v, hS k v v.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext v x
    simp [rightTranslate]
  map_mul' k k' := by
    ext v x
    show (v : AdelicGL2 (𝓞 F) F → ℂ) (x * rowIsometryInclAt₀ F w (k * k'))
      = (v : AdelicGL2 (𝓞 F) F → ℂ) (x * rowIsometryInclAt₀ F w k * rowIsometryInclAt₀ F w k')
    rw [map_mul, mul_assoc]

private theorem subRep_apply_coe (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (k : rowIsometrySubgroup₀ w.Completion) (v : ↥S) :
    ((subRep F w S hS k v : ↥S) : AdelicGL2 (𝓞 F) F → ℂ)
      = rightTranslate F (rowIsometryInclAt₀ F w k) v := rfl

private theorem continuous_dual_subRep (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    [FiniteDimensional ℂ ↥S]
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (hSc : ∀ g ∈ S, Continuous g) (ℓ : Module.Dual ℂ ↥S) (v : ↥S) :
    Continuous fun k => ℓ (subRep F w S hS k v) := by
  have hℓ : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
  refine hℓ.comp ?_
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun x => ?_
  show Continuous fun k : rowIsometrySubgroup₀ w.Completion =>
    (v : AdelicGL2 (𝓞 F) F → ℂ) (x * rowIsometryInclAt₀ F w k)
  exact (hSc v v.2).comp (continuous_const.mul (ArchCompactOrbit.continuous_rowIsometryInclAt₀ F w))

private theorem key (m : ℕ) (ρs : Fin m → ArchRepAt F w) (r : ℕ) (σs : Fin r → ArchRepAt F w)
    (hσ : ∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
          rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S',
            rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs j))
    (Q : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hQc : ∀ g ∈ Q, Continuous g) :
    ∀ (d : ℕ) (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), FiniteDimensional ℂ ↥S →
      Module.finrank ℂ ↥S = d →
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S,
        rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
      S ≤ Q → S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
      S ≤ ⨆ j, Q ⊓ archTypeSubmoduleAt F w (σs j) := by
  intro d
  refine Nat.strong_induction_on d (fun d ih => ?_)
  intro S hSfd hSd hSst hSQ hSle
  classical
  by_cases hS0 : S = ⊥
  · rw [hS0]
    exact bot_le
  let hSfdI : FiniteDimensional ℂ ↥S := hSfd

  have hex : ∃ e : ℕ, ∃ S₁ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S₁ ≤ S ∧ S₁ ≠ ⊥ ∧
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S₁,
        rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S₁) ∧
      Module.finrank ℂ ↥S₁ = e :=
    ⟨_, S, le_rfl, hS0, hSst, rfl⟩
  obtain ⟨S₁, hS₁S, hS₁ne, hS₁st, hS₁d⟩ := Nat.find_spec hex
  let hS₁fd : FiniteDimensional ℂ ↥S₁ := Submodule.finiteDimensional_of_le hS₁S
  have hS₁simple : ∀ S'' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S'' ≤ S₁ →
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S'',
        rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S'') →
      S'' = ⊥ ∨ S'' = S₁ := by
    intro S'' hle hst
    by_cases h0 : S'' = ⊥
    · exact Or.inl h0
    · right
      let hS''fd : FiniteDimensional ℂ ↥S'' := Submodule.finiteDimensional_of_le (hle.trans hS₁S)
      have hmin : Nat.find hex ≤ Module.finrank ℂ ↥S'' :=
        Nat.find_min' hex ⟨S'', hle.trans hS₁S, h0, hst, rfl⟩
      exact Submodule.eq_of_le_of_finrank_le hle (hS₁d ▸ hmin)
  obtain ⟨j, hj⟩ := hσ S₁ hS₁fd hS₁st hS₁ne hS₁simple (hS₁S.trans hSle)
  have hS₁R : S₁ ≤ ⨆ j, Q ⊓ archTypeSubmoduleAt F w (σs j) :=
    le_trans (le_inf (hS₁S.trans hSQ) hj) (le_iSup (fun j => Q ⊓ archTypeSubmoduleAt F w (σs j)) j)

  let P : Submodule ℂ ↥S := S₁.comap S.subtype
  have hP : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ v ∈ P, subRep F w S hSst k v ∈ P := by
    intro k v hv
    show ((subRep F w S hSst k v : ↥S) : AdelicGL2 (𝓞 F) F → ℂ) ∈ S₁
    rw [subRep_apply_coe]
    exact hS₁st k _ hv
  obtain ⟨Pc, hcompl, hPc⟩ :=
    Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous (subRep F w S hSst)
      (continuous_dual_subRep F w S hSst (fun g hg => hQc g (hSQ hg))) P hP
  let S₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Pc.map S.subtype
  have hS₂S : S₂ ≤ S := Submodule.map_subtype_le S Pc
  have hS₂st : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S₂,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S₂ := by
    intro k g hg
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hg
    exact Submodule.mem_map.mpr ⟨subRep F w S hSst k v, hPc k v hv, rfl⟩
  have hPmap : P.map S.subtype = S₁ := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hS₁S]
  have hsup : S₁ ⊔ S₂ = S := by
    rw [← hPmap, ← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_top, Submodule.range_subtype]
  have hS₂lt : S₂ < S := by
    refine lt_of_le_of_ne hS₂S fun hS₂eq => hS₁ne ?_

    have hPc_top : Pc = ⊤ := by
      apply le_antisymm le_top
      intro v _
      have hvS₂ : (v : AdelicGL2 (𝓞 F) F → ℂ) ∈ S₂ := by
        rw [hS₂eq]
        exact v.2
      obtain ⟨u, hu, huv⟩ := Submodule.mem_map.mp hvS₂
      have : u = v := Subtype.ext (by simpa using huv)
      exact this ▸ hu
    have hPbot : P = ⊥ := by
      have := hcompl.inf_eq_bot
      rwa [hPc_top, inf_top_eq] at this
    rw [← hPmap, hPbot, Submodule.map_bot]
  let hS₂fd : FiniteDimensional ℂ ↥S₂ := Submodule.finiteDimensional_of_le hS₂S
  have hlt : Module.finrank ℂ ↥S₂ < d := hSd ▸ Submodule.finrank_lt_finrank_of_lt hS₂lt
  have hS₂R := ih _ hlt S₂ hS₂fd rfl hS₂st (hS₂S.trans hSQ) (hS₂S.trans hSle)
  rw [← hsup]
  exact sup_le hS₁R hS₂R

end OnePlaceSplit

end CuspidalConstituent

open OnePlaceSplit in
theorem CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w) (r : ℕ) (σs : Fin r → ArchRepAt F w)
    (hσ : ∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs j))
    (Q : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hQc : ∀ g ∈ Q, Continuous g)
    (hQs : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ Q, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ Q) :
    Q ⊓ (⨆ i, archTypeSubmoduleAt F w (ρs i)) ≤ ⨆ j, Q ⊓ archTypeSubmoduleAt F w (σs j)
    := by
  intro φ hφ
  obtain ⟨hφQ, hφT⟩ := hφ
  obtain ⟨hfd, hst, hle⟩ :=
    AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
      F w m ρs φ hφT
  set S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ
    (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
      rightTranslate F (rowIsometryInclAt₀ F w k) φ) with hSdef
  have hSQ : S ≤ Q := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact hQs k φ hφQ
  have hφS : φ ∈ S := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext x
    simp [rightTranslate]
  exact key F w m ρs r σs hσ Q hQc _ S hfd rfl hst hSQ hle hφS

namespace ArchFlatProof

open scoped Classical
open NumberField.InfinitePlace NumberField.mixedEmbedding

variable {F : Type} [Field F] [NumberField F]

private def NZ (z : mixedSpace F) : Prop := (∀ w, z.1 w ≠ 0) ∧ ∀ w, z.2 w ≠ 0

omit [NumberField F] in
private theorem mul_inv_of_NZ {z : mixedSpace F} (hz : NZ z) : z * z⁻¹ = 1 := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · exact mul_inv_cancel₀ (hz.1 w)
  · exact mul_inv_cancel₀ (hz.2 w)

omit [NumberField F] in
private theorem isUnit_of_NZ {z : mixedSpace F} (hz : NZ z) : IsUnit z :=
  ⟨⟨z, z⁻¹, mul_inv_of_NZ hz, by rw [mul_comm]; exact mul_inv_of_NZ hz⟩, rfl⟩

omit [NumberField F] in
private theorem NZ_of_isUnit {z : mixedSpace F} (hz : IsUnit z) : NZ z := by
  obtain ⟨u, rfl⟩ := hz
  have h1 : (u : mixedSpace F) * ((u⁻¹ : (mixedSpace F)ˣ) : mixedSpace F) = 1 := u.mul_inv
  refine ⟨fun w h0 => ?_, fun w h0 => ?_⟩
  · have := congrArg (fun z : mixedSpace F => z.1 w) h1
    simp only [Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply, h0, zero_mul] at this
    exact zero_ne_one this
  · have := congrArg (fun z : mixedSpace F => z.2 w) h1
    simp only [Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply, h0, zero_mul] at this
    exact zero_ne_one this

private theorem isOpen_NZ : IsOpen {z : mixedSpace F | NZ z} := by
  have h1 : {z : mixedSpace F | NZ z} = (⋂ w, {z : mixedSpace F | z.1 w ≠ 0}) ∩ ⋂ w, {z : mixedSpace F | z.2 w ≠ 0} := by
    ext z; simp [NZ, Set.mem_iInter]
  rw [h1]
  refine (isOpen_iInter_of_finite fun w => ?_).inter (isOpen_iInter_of_finite fun w => ?_)
  · exact isOpen_ne_fun ((continuous_apply w).comp continuous_fst) continuous_const
  · exact isOpen_ne_fun ((continuous_apply w).comp continuous_snd) continuous_const

omit [NumberField F] in
private theorem NZ_ringEquiv_of_isUnit {d : InfiniteAdeleRing F} (hd : IsUnit d) :
    NZ (InfiniteAdeleRing.ringEquiv_mixedSpace F d) :=
  NZ_of_isUnit (hd.map _)

private abbrev Ent (F : Type) [Field F] [NumberField F] := Fin 2 → Fin 2 → mixedSpace F

private def det₂ (A : Ent F) : mixedSpace F := A 0 0 * A 1 1 - A 0 1 * A 1 0

private def adj₂ (A : Ent F) : Ent F := fun i j =>
  if i = 0 then (if j = 0 then A 1 1 else -A 0 1) else (if j = 0 then -A 1 0 else A 0 0)

private def inv₂ (A : Ent F) : Ent F := fun i j => (det₂ A)⁻¹ * adj₂ A i j

private theorem det₂_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    det₂ (archEntries F g) = InfiniteAdeleRing.ringEquiv_mixedSpace F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det := by
  simp only [det₂, archEntries, Matrix.det_fin_two, map_sub, map_mul]

private theorem NZ_det₂_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) : NZ (det₂ (archEntries F g)) := by
  rw [det₂_archEntries]
  exact NZ_ringEquiv_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit)

private theorem inv₂_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) : inv₂ (archEntries F g) = archEntries F g⁻¹ := by
  set R := InfiniteAdeleRing.ringEquiv_mixedSpace F with hR
  set M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) := (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hM
  have hdetU : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit

  have hRinv : R (Ring.inverse M.det) = (R M.det)⁻¹ := by
    have h1 : R M.det * R (Ring.inverse M.det) = 1 := by
      rw [← map_mul, Ring.mul_inverse_cancel _ hdetU, map_one]
    have h2 : R M.det * (R M.det)⁻¹ = 1 := mul_inv_of_NZ (NZ_ringEquiv_of_isUnit hdetU)
    calc R (Ring.inverse M.det) = R (Ring.inverse M.det) * (R M.det * (R M.det)⁻¹) := by rw [h2, mul_one]
      _ = (R M.det * R (Ring.inverse M.det)) * (R M.det)⁻¹ := by ring
      _ = (R M.det)⁻¹ := by rw [h1, one_mul]
  have hinvM : ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = Ring.inverse M.det • M.adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def]
  funext i j
  simp only [inv₂, archEntries, det₂_archEntries, hinvM, Matrix.smul_apply, smul_eq_mul, map_mul, ← hR, ← hM, hRinv,
    Matrix.adjugate_fin_two]
  congr 1
  fin_cases i <;> fin_cases j <;> simp [adj₂, archEntries, Matrix.of_apply, map_neg, ← hR, ← hM]

private theorem exists_archEntries_eq_of_NZ {A : Ent F} (hA : NZ (det₂ A)) : ∃ g : GL (Fin 2) (InfiniteAdeleRing F), archEntries F g = A := by
  set R := InfiniteAdeleRing.ringEquiv_mixedSpace F with hR
  set M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) := Matrix.of fun i j => R.symm (A i j) with hM
  have hdet : R M.det = det₂ A := by
    simp only [hM, Matrix.det_fin_two, Matrix.of_apply, map_sub, map_mul, RingEquiv.apply_symm_apply, det₂]
  have hU : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have : IsUnit (R M.det) := by rw [hdet]; exact isUnit_of_NZ hA
    simpa using this.map R.symm
  obtain ⟨g, hg⟩ := hU
  refine ⟨g, funext fun i => funext fun j => ?_⟩
  simp only [archEntries, hg, hM, Matrix.of_apply, ← hR, RingEquiv.apply_symm_apply]

section Calculus

variable {F : Type} [Field F] [NumberField F]

private theorem contDiff_det₂ : ContDiff ℝ (⊤ : ℕ∞) (det₂ : Ent F → mixedSpace F) :=
  ((contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (0 : Fin 2) (0 : Fin 2)).mul
    (contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (1 : Fin 2) (1 : Fin 2))).sub
  ((contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (0 : Fin 2) (1 : Fin 2)).mul
    (contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (1 : Fin 2) (0 : Fin 2)))

private theorem contDiff_adj₂ (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun A : Ent F => adj₂ A i j) := by
  fin_cases i <;> fin_cases j
  · exact contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (1 : Fin 2) (1 : Fin 2)
  · exact (contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (0 : Fin 2) (1 : Fin 2)).neg
  · exact (contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (1 : Fin 2) (0 : Fin 2)).neg
  · exact contDiff_apply_apply (𝕜 := ℝ) (E := mixedSpace F) (0 : Fin 2) (0 : Fin 2)

private theorem contDiffAt_inv_mixedSpace {z : mixedSpace F} (hz : NZ z) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z : mixedSpace F => z⁻¹) z := by
  have : (fun z : mixedSpace F => z⁻¹) = fun z => (fun w => (z.1 w)⁻¹, fun w => (z.2 w)⁻¹) := rfl
  rw [this]
  refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun w => ?_) (contDiffAt_pi.mpr fun w => ?_)
  · exact (contDiffAt_inv ℝ (hz.1 w)).comp z (((contDiffAt_apply (𝕜 := ℝ) (E := ℝ) w _).comp z contDiffAt_fst))
  · exact (contDiffAt_inv ℝ (hz.2 w)).comp z (((contDiffAt_apply (𝕜 := ℝ) (E := ℂ) w _).comp z contDiffAt_snd))

private theorem contDiffAt_inv₂ {A : Ent F} (hA : NZ (det₂ A)) : ContDiffAt ℝ (⊤ : ℕ∞) (inv₂ : Ent F → Ent F) A := by
  refine contDiffAt_pi.mpr fun i => contDiffAt_pi.mpr fun j => ?_
  show ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Ent F => (det₂ A)⁻¹ * adj₂ A i j) A
  exact ((contDiffAt_inv_mixedSpace hA).comp A contDiff_det₂.contDiffAt).mul (contDiff_adj₂ i j).contDiffAt

private def normProd (z : mixedSpace F) : ℝ := (∏ w, ‖z.1 w‖) * ∏ w, ‖z.2 w‖ ^ 2

private theorem normProd_pos {z : mixedSpace F} (hz : NZ z) : 0 < normProd z :=
  mul_pos (Finset.prod_pos fun w _ => norm_pos_iff.mpr (hz.1 w))
    (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (hz.2 w)) 2)

private theorem contDiffAt_normProd {z : mixedSpace F} (hz : NZ z) : ContDiffAt ℝ (⊤ : ℕ∞) (normProd : mixedSpace F → ℝ) z := by
  refine ContDiffAt.mul ?_ ?_
  · refine contDiffAt_prod fun w _ => ?_
    exact (contDiffAt_norm ℝ (hz.1 w)).comp z ((contDiffAt_apply (𝕜 := ℝ) (E := ℝ) w _).comp z contDiffAt_fst)
  · refine contDiffAt_prod fun w _ => ?_
    exact ((contDiff_norm_sq ℝ (E := ℂ)).contDiffAt).comp z ((contDiffAt_apply (𝕜 := ℝ) (E := ℂ) w _).comp z contDiffAt_snd)

private theorem contDiffAt_omega (σ : ℝ) {A : Ent F} (hA : NZ (det₂ A)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Ent F => ((normProd (det₂ A) ^ (-σ) : ℝ) : ℂ)) A := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Ent F => normProd (det₂ A)) A :=
    (contDiffAt_normProd hA).comp A contDiff_det₂.contDiffAt
  have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun A : Ent F => normProd (det₂ A) ^ (-σ)) A :=
    h1.rpow_const_of_ne (normProd_pos hA).ne'
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp A h2

end Calculus

section Weight

variable {F : Type} [Field F] [NumberField F]

private theorem normProd_det₂_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    normProd (det₂ (archEntries F g))
      = NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F g)) := by
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult (adelicArchGLIncl F g)
    (by rw [glFin_adelicArchGLIncl]; exact one_mem _)]
  set M : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) := (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hM

  have hloc : ∀ w : InfinitePlace F, NumberField.AdelicVolume.archDetNorm w (adelicArchGLIncl F g) = ‖M.det w‖ := by
    intro w
    unfold NumberField.AdelicVolume.archDetNorm
    rw [glArch_adelicArchGLIncl]
    show ‖((archEval F w).mapMatrix M).det‖ = ‖M.det w‖
    rw [← RingHom.map_det]
    rfl
  simp_rw [hloc]

  rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun w : InfinitePlace F => w.IsReal)]
  rw [det₂_archEntries, normProd]
  congr 1
  · refine Fintype.prod_congr _ _ fun w => ?_
    rw [show (w : InfinitePlace F).mult = 1 by simp [NumberField.InfinitePlace.mult, w.2], pow_one]
    show ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (M.det w)‖ = ‖M.det w‖
    exact (AddMonoidHomClass.isometry_iff_norm _).mp (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2) _
  · refine (Fintype.prod_equiv (Equiv.subtypeEquivRight (p := fun w : InfinitePlace F => ¬ w.IsReal)
      (q := fun w : InfinitePlace F => w.IsComplex) fun w => not_isReal_iff_isComplex)
      (fun w => ‖M.det (w : InfinitePlace F)‖ ^ (w : InfinitePlace F).mult)
      (fun w => ‖((InfiniteAdeleRing.ringEquiv_mixedSpace F) M.det).2 w‖ ^ 2) fun w => ?_).symm
    have hw : ¬ (w : InfinitePlace F).IsReal := w.2
    show ‖M.det (w : InfinitePlace F)‖ ^ (w : InfinitePlace F).mult
      = ‖InfinitePlace.Completion.extensionEmbedding (w : InfinitePlace F) (M.det w)‖ ^ 2
    rw [show (w : InfinitePlace F).mult = 2 by simp [NumberField.InfinitePlace.mult, hw]]
    rw [(AddMonoidHomClass.isometry_iff_norm _).mp (InfinitePlace.Completion.isometry_extensionEmbedding (w : InfinitePlace F)) _]

end Weight

section Main

variable {F : Type} [Field F] [NumberField F]

private def extFlat (σ : ℝ) (Φ : Ent F → ℂ) (A : Ent F) : ℂ :=
  if NZ (det₂ A) then conj (Φ (inv₂ A)) * ((normProd (det₂ A) ^ (-σ) : ℝ) : ℂ) else 0

private theorem extFlat_archEntries (σ : ℝ) (Φ : Ent F → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hΦ : ∀ g, fa g = Φ (archEntries F g)) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    extFlat σ Φ (archEntries F g) = conj (fa g⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F g)) ^ (-σ) : ℝ) : ℂ) := by
  rw [extFlat, ite_eq_left (NZ_det₂_archEntries g), inv₂_archEntries, ← hΦ, normProd_det₂_archEntries]

private theorem contDiff_extFlat (σ : ℝ) (Φ : Ent F → ℂ) (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hΦ : ∀ g, fa g = Φ (archEntries F g)) (hK : HasCompactSupport fa) :
    ContDiff ℝ (⊤ : ℕ∞) (extFlat σ Φ) := by

  have hent : Continuous (archEntries F) :=
    continuous_pi fun i => continuous_pi fun j =>
      (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (Units.continuous_val.matrix_elem i j)

  set C : Set (Ent F) := archEntries F '' (tsupport fa)⁻¹ with hC
  have hCcpt : IsCompact C := hK.inv.image hent
  have hCcl : IsClosed C := hCcpt.isClosed

  have hzero : ∀ A : Ent F, A ∉ C → extFlat σ Φ A = 0 := by
    intro A hA
    by_cases hNZ : NZ (det₂ A)
    · obtain ⟨g, rfl⟩ := exists_archEntries_eq_of_NZ hNZ
      rw [extFlat_archEntries σ Φ fa hΦ]
      have hg : g⁻¹ ∉ tsupport fa := fun h => hA ⟨g, by simpa using h, rfl⟩
      rw [image_eq_zero_of_notMem_tsupport hg, map_zero, zero_mul]
    · rw [extFlat, ite_eq_right hNZ]
  refine contDiff_iff_contDiffAt.mpr fun A => ?_
  by_cases hA : A ∈ C
  ·
    obtain ⟨g, -, rfl⟩ := hA
    have hNZ := NZ_det₂_archEntries g
    have hopen : IsOpen {A : Ent F | NZ (det₂ A)} := isOpen_NZ.preimage contDiff_det₂.continuous
    have hev : extFlat σ Φ =ᶠ[nhds (archEntries F g)]
        fun A => conj (Φ (inv₂ A)) * ((normProd (det₂ A) ^ (-σ) : ℝ) : ℂ) := by
      filter_upwards [hopen.mem_nhds hNZ] with A hA'
      exact ite_eq_left hA'
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine ContDiffAt.mul ?_ (contDiffAt_omega σ hNZ)
    exact Complex.conjCLE.contDiff.contDiffAt.comp _ (hΦc.contDiffAt.comp _ (contDiffAt_inv₂ hNZ))
  ·
    have hev : extFlat σ Φ =ᶠ[nhds A] fun _ => 0 := by
      filter_upwards [hCcl.isOpen_compl.mem_nhds hA] with A' hA'
      exact hzero A' hA'
    exact contDiffAt_const.congr_of_eventuallyEq hev

end Main

end ArchFlatProof

open ArchFlatProof in
theorem CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow
    (F : Type) [Field F] [NumberField F] (σ : ℝ)
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun y : GL (Fin 2) (InfiniteAdeleRing F) => conj (fa y⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F y)) ^ (-σ) : ℝ) : ℂ))
    := by
  classical
  obtain ⟨⟨Φ, hΦc, hΦ⟩, hK⟩ := hfa
  refine ⟨⟨extFlat σ Φ, contDiff_extFlat σ Φ hΦc fa hΦ hK, fun g => (extFlat_archEntries σ Φ fa hΦ g).symm⟩, ?_⟩
  refine HasCompactSupport.intro hK.inv ?_
  intro y hy
  have hy' : y⁻¹ ∉ tsupport fa := fun h => hy (by simpa using Set.inv_mem_inv.mpr h)
  show conj (fa y⁻¹) * _ = 0
  rw [image_eq_zero_of_notMem_tsupport hy', map_zero, zero_mul]


end AutomorphicForm
