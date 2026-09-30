/-
  Representation conjugacy from characters: a finite-image representation
  `G →* GL n k` over a characteristic-zero field is determined up to conjugacy
  by its characteristic polynomials.

  Transcribed from the pinned FLT solution file (`aa2d8b3`,
  `P2M/Sol/S_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range.lean`,
  180 lines); its public target is the `Theorems/` wrapper
  `Thm_Representation_exists_conj_eq_of_charpoly_eq_of_finite_range.lean`. The
  mathematics is math/019 §4.

  The route: turn a matrix representation into a `Representation` on the
  coordinate space, transport its `MonoidAlgebra` action trace to the matrix
  trace, and feed the equal traces to phase D's Brauer–Nesbitt theorem
  (`BrauerNesbitt.nonempty_linearEquiv_of_forall_trace_of_eq`), then read an
  intertwining linear equivalence off as a conjugating unit. Finiteness of the
  image restricts the whole statement to the finite subgroup
  `MonoidHom.range (ρ.prod ρ')`.

  No ported prerequisite beyond `FLTForHuman/Algebra/BrauerNesbitt.lean`. The
  pin's helpers are `private`; the only public declaration is the pin's target
  theorem.
-/
import FLTForHuman.Algebra.BrauerNesbitt
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Maschke

set_option autoImplicit false

-- The pin's proof block introduces instances with `haveI` in `Prop` goals; it is
-- transcribed verbatim, as in the other ported proof files.
set_option linter.style.haveILetI false

open scoped MatrixGroups

namespace RepConjAux

open Matrix

section MatrixRep

variable {k : Type*} [Field k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {H : Type*} [Group H]

/-- The coordinate-space representation attached to a matrix representation. -/
private noncomputable def repOfGL (σ : H →* GL n k) : Representation k H (n → k) where
  toFun h := Matrix.toLin' (σ h : Matrix n n k)
  map_one' := by
    simp only [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' a b := by
    simp only [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

private theorem repOfGL_apply (σ : H →* GL n k) (h : H) :
    repOfGL σ h = Matrix.toLin' (σ h : Matrix n n k) := rfl

private theorem trace_repOfGL (σ : H →* GL n k) (h : H) :
    LinearMap.trace k (n → k) (repOfGL σ h) = Matrix.trace (σ h : Matrix n n k) := by
  rw [repOfGL_apply, Matrix.trace_toLin'_eq]

private theorem actionEndo_of_eq_conj {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (g : H) :
    BrauerNesbitt.actionEndo k (MonoidAlgebra k H) ρ.asModule (MonoidAlgebra.of k H g) =
      ρ.asModuleEquiv.symm.conj (ρ g) := by
  apply LinearMap.ext
  intro x
  rw [LinearEquiv.conj_apply, BrauerNesbitt.actionEndo_apply, LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_symm,
    Representation.asModuleEquiv_symm_map_rho, LinearEquiv.symm_apply_apply]

private theorem trace_actionEndo_of {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (g : H) :
    LinearMap.trace k ρ.asModule
        (BrauerNesbitt.actionEndo k (MonoidAlgebra k H) ρ.asModule (MonoidAlgebra.of k H g)) =
      LinearMap.trace k V (ρ g) := by
  rw [actionEndo_of_eq_conj, LinearMap.trace_conj']

private theorem exists_linearEquiv_of_asModule_equiv
    {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρ : Representation k H V) (τ : Representation k H W)
    (E : ρ.asModule ≃ₗ[MonoidAlgebra k H] τ.asModule) :
    ∃ e : V ≃ₗ[k] W, ∀ (g : H) (v : V), e (ρ g v) = τ g (e v) := by
  refine ⟨(ρ.asModuleEquiv.symm.trans (E.restrictScalars k)).trans τ.asModuleEquiv, ?_⟩
  intro g v
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply]
  rw [Representation.asModuleEquiv_symm_map_rho, LinearEquiv.map_smul,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

private theorem exists_conj_eq_of_linearEquiv (σ σ' : H →* GL n k)
    (e : (n → k) ≃ₗ[k] (n → k))
    (he : ∀ (h : H) (v : n → k), e (repOfGL σ h v) = repOfGL σ' h (e v)) :
    ∃ P : GL n k, ∀ h : H, σ' h = P * σ h * P⁻¹ := by
  set Pm : Matrix n n k := LinearMap.toMatrix' (e : (n → k) →ₗ[k] (n → k)) with hPm
  set Pi : Matrix n n k := LinearMap.toMatrix' (e.symm : (n → k) →ₗ[k] (n → k)) with hPi
  have hmul : Pm * Pi = 1 := by
    rw [hPm, hPi, ← LinearMap.toMatrix'_comp, ← LinearEquiv.coe_trans,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hmul' : Pi * Pm = 1 := by
    rw [hPm, hPi, ← LinearMap.toMatrix'_comp, ← LinearEquiv.coe_trans,
      LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  let P : GL n k := ⟨Pm, Pi, hmul, hmul'⟩
  refine ⟨P, fun h => ?_⟩
  have hcomp : (e : (n → k) →ₗ[k] (n → k)) ∘ₗ Matrix.toLin' (σ h : Matrix n n k) =
      Matrix.toLin' (σ' h : Matrix n n k) ∘ₗ (e : (n → k) →ₗ[k] (n → k)) := by
    apply LinearMap.ext
    intro v
    simpa [repOfGL_apply] using he h v
  have hmat : Pm * (σ h : Matrix n n k) = (σ' h : Matrix n n k) * Pm := by
    have := congrArg LinearMap.toMatrix' hcomp
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at this
  apply Units.ext
  change (σ' h : Matrix n n k) = Pm * (σ h : Matrix n n k) * Pi
  rw [hmat, Matrix.mul_assoc, hmul, Matrix.mul_one]

private theorem exists_conj_eq_of_trace_eq [CharZero k] [Finite H] (σ σ' : H →* GL n k)
    (htr : ∀ h : H, Matrix.trace (σ h : Matrix n n k) = Matrix.trace (σ' h : Matrix n n k)) :
    ∃ P : GL n k, ∀ h : H, σ' h = P * σ h * P⁻¹ := by
  classical
  haveI : NeZero (Nat.card H) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card H : k) := inferInstance
  let τ : Representation k H (n → k) := repOfGL σ
  let τ' : Representation k H (n → k) := repOfGL σ'

  haveI : IsSemisimpleModule (MonoidAlgebra k H) τ.asModule := inferInstance
  haveI : IsSemisimpleModule (MonoidAlgebra k H) τ'.asModule := inferInstance

  have htr' : ∀ g : H,
      LinearMap.trace k τ.asModule
          (BrauerNesbitt.actionEndo k (MonoidAlgebra k H) τ.asModule (MonoidAlgebra.of k H g)) =
        LinearMap.trace k τ'.asModule
          (BrauerNesbitt.actionEndo k (MonoidAlgebra k H) τ'.asModule
            (MonoidAlgebra.of k H g)) := by
    intro g
    rw [trace_actionEndo_of, trace_actionEndo_of]
    change LinearMap.trace k (n → k) (repOfGL σ g) = LinearMap.trace k (n → k) (repOfGL σ' g)
    rw [trace_repOfGL, trace_repOfGL, htr g]

  obtain ⟨E⟩ := BrauerNesbitt.nonempty_linearEquiv_of_forall_trace_of_eq
    (k := k) (G := H) (M := τ.asModule) (N := τ'.asModule) htr'
  obtain ⟨e, he⟩ := exists_linearEquiv_of_asModule_equiv τ τ' E
  exact exists_conj_eq_of_linearEquiv σ σ' e he

end MatrixRep

section FiniteRange

variable {k : Type*} [Field k] [CharZero k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Group G]

private theorem trace_eq_of_charpoly_eq {R : Type*} [CommRing R] (A B : Matrix n n R)
    (h : A.charpoly = B.charpoly) : A.trace = B.trace := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
      simp [Matrix.trace]
  | inr hn =>
      haveI := hn
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

private theorem exists_conj_eq_of_charpoly_eq_of_finite_range_aux (ρ ρ' : G →* GL n k)
    (hρ : Finite (MonoidHom.range ρ)) (hρ' : Finite (MonoidHom.range ρ'))
    (h : ∀ g : G, ((ρ g : GL n k) : Matrix n n k).charpoly =
      ((ρ' g : GL n k) : Matrix n n k).charpoly) :
    ∃ P : GL n k, ∀ g : G, ρ' g = P * ρ g * P⁻¹ := by
  classical
  let π : G →* GL n k × GL n k := ρ.prod ρ'
  let H : Subgroup (GL n k × GL n k) := π.range
  have hmem₁ : ∀ x : H, (x : GL n k × GL n k).1 ∈ ρ.range := by
    rintro ⟨x, g, rfl⟩
    exact ⟨g, rfl⟩
  have hmem₂ : ∀ x : H, (x : GL n k × GL n k).2 ∈ ρ'.range := by
    rintro ⟨x, g, rfl⟩
    exact ⟨g, rfl⟩
  haveI : Finite H := by
    refine Finite.of_injective
      (fun x : H => ((⟨_, hmem₁ x⟩ : ρ.range), (⟨_, hmem₂ x⟩ : ρ'.range))) ?_
    intro x y hxy
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hxy
    exact Subtype.ext (Prod.ext hxy.1 hxy.2)

  let σ : H →* GL n k := (MonoidHom.fst _ _).comp H.subtype
  let σ' : H →* GL n k := (MonoidHom.snd _ _).comp H.subtype
  have htr : ∀ x : H, Matrix.trace (σ x : Matrix n n k) = Matrix.trace (σ' x : Matrix n n k) := by
    rintro ⟨x, g, rfl⟩
    exact trace_eq_of_charpoly_eq _ _ (h g)
  obtain ⟨P, hP⟩ := exists_conj_eq_of_trace_eq σ σ' htr
  refine ⟨P, fun g => ?_⟩
  exact hP ⟨π g, g, rfl⟩

end FiniteRange

end RepConjAux

namespace Representation

/-- Two finite-image complex `GL₂` representations with equal characteristic
polynomial at every group element are conjugate. -/
theorem exists_conj_eq_of_charpoly_eq_of_finite_range
    {G : Type*} [Group G] (ρ ρ' : G →* GL (Fin 2) ℂ)
    (hρ : Finite (MonoidHom.range ρ)) (hρ' : Finite (MonoidHom.range ρ'))
    (h : ∀ g : G, ((ρ g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly =
      ((ρ' g : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).charpoly) :
    ∃ P : GL (Fin 2) ℂ, ∀ g : G, ρ' g = P * ρ g * P⁻¹ :=
  RepConjAux.exists_conj_eq_of_charpoly_eq_of_finite_range_aux ρ ρ' hρ hρ' h

end Representation
