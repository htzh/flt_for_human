/-
  Archimedean `K`-finiteness.

  `RightTranslatesSpanFinite K f` says the right translates of `f : G → ℂ` by `K` span a finite
  set; `IsArchKFiniteAt w φ` is that property for the archimedean row-isometry subgroup
  `archRowIsometrySubgroup w` (the image of `rowIsometrySubgroup w.Completion` under
  `adelicArchGLInclAt w`), and `IsArchKFinite φ` asks it at every infinite place. The two basic
  members are `isArchKFinite_const`/`isArchKFinite_zero`, and `isArchKFinite_of_hasArchType`
  turns an archimedean type `HasArchType F χ φ` into `K`-finiteness via the spanning singleton
  `{φ}`.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_ArchKFinite.lean` (pinned
  `aa2d8b3`, 69 lines / 9 declarations). The pin's single import `Def_AutomorphicForm_ArchType`
  is replaced by the port's `AutomorphicForm/Adelic/ArchType.lean` (which owns `adelicArchGLInclAt`,
  `HasArchType`, and `rowIsometrySubgroup` through `WindowedSiegel/RowIsometry.lean`); the pin
  namespace `AutomorphicForm` is kept. mathlib `v4.34.0` has no counterpart, so all declarations
  are residue. The pin module is imported by 731 pin files and `IsArchKFinite` occurs in 542 of
  them, so this is the shared archimedean-`K`-finiteness vocabulary, not a local helper.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchType

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField IsDedekindDomain Matrix

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

section Generic

variable {G : Type*} [Group G]

def RightTranslatesSpanFinite (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∃ s : Finset (G → ℂ),
    ∀ k ∈ K, (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))

theorem rightTranslatesSpanFinite_const (K : Subgroup G) (c : ℂ) :
    RightTranslatesSpanFinite K (fun _ : G => c) := by
  refine ⟨{fun _ => c}, fun k _hk => ?_⟩
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

theorem rightTranslatesSpanFinite_bot (f : G → ℂ) :
    RightTranslatesSpanFinite (⊥ : Subgroup G) f := by
  refine ⟨{f}, fun k hk => ?_⟩
  rw [Subgroup.mem_bot] at hk; subst hk
  have h1 : (fun x : G => f (x * 1)) = f := by funext x; rw [mul_one]
  rw [h1]
  exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _))

end Generic

section Arch

variable (F : Type) [Field F] [NumberField F]

def archRowIsometrySubgroup (w : InfinitePlace F) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (rowIsometrySubgroup w.Completion).map (adelicArchGLInclAt F w)

def IsArchKFiniteAt (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  RightTranslatesSpanFinite (archRowIsometrySubgroup F w) φ

def IsArchKFinite (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ w : InfinitePlace F, IsArchKFiniteAt F w φ

theorem isArchKFinite_const (c : ℂ) : IsArchKFinite F (fun _ => c) :=
  fun w => rightTranslatesSpanFinite_const (archRowIsometrySubgroup F w) c

theorem isArchKFinite_zero : IsArchKFinite F (fun _ => (0 : ℂ)) := isArchKFinite_const F 0

theorem isArchKFinite_of_hasArchType
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : HasArchType F χ φ) :
    IsArchKFinite F φ := by
  intro w
  refine ⟨{φ}, ?_⟩
  rintro _ ⟨k, hk, rfl⟩
  have hχ : (fun x => φ (x * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)))
      = ((χ w ⟨k, hk⟩ : ℂˣ) : ℂ) • φ := by
    funext x
    exact hφ w ⟨k, hk⟩ x
  rw [hχ]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_singleton_self _)))

end Arch

end AutomorphicForm

end
