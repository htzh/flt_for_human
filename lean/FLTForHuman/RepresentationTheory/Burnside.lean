/-
  Burnside's theorem for a finite-dimensional irreducible representation over an
  algebraically closed field: its image spans the endomorphism ring.

  For a field `k`, a monoid `G` and a finite-dimensional `k`-vector space `V`, an
  irreducible representation `ρ : Representation k G V` spans `End k V`:

      `Submodule.span k (Set.range ⇑ρ) = ⊤`.

  Equivalently (the pin's private reformulation, now public) the algebra map
  `ρ.asAlgebraHom : k[G] →ₐ[k] End k V` is surjective. Over an algebraically closed
  field this is the Jacobson-density form of Burnside's theorem: `k[G] → End k V` is
  surjective by Jacobson density (`jacobson_density`) applied to the `End k V`-linear
  endomorphism of `V` obtained by conjugating with `ρ.asModuleEquiv`, and the two
  dictionaries `range_asAlgebraHom_toLinearMap`,
  `span_range_eq_top_iff_surjective_asAlgebraHom` translate injectivity of the span into
  surjectivity of the algebra map.

  Transcribed from the pin's node `Representation.span_range_eq_top_of_isIrreducible` —
  `Theorems/Thm_Representation_span_range_eq_top_of_isIrreducible.lean` (the statement
  authority) and `P2M/Sol/S_Representation_span_range_eq_top_of_isIrreducible.lean`
  (151 pin lines, pinned `aa2d8b3`). The pin's public target is its `solution` tail; the
  port keeps the wrapper's statement (whose binders are the wrapper's, not the `S_`
  file's inline ones) verbatim and strips the pin's `P2MW.S_…` wrapper namespace, and drops
  `import P2M.Util` and the `p2m_export`/`p2m_open_scoped` scaffolding.

  Two of the node's helpers — `Representation.range_asAlgebraHom_toLinearMap` and
  `Representation.span_range_eq_top_iff_surjective_asAlgebraHom` — are pin-private
  declarations that the port already had, `private`, in
  `FLTForHuman/Algebra/BrauerNesbittRepresentation.lean`; they are **promoted** there and
  imported here rather than re-proved (their statements are the pin's). The node's third
  `Dictionary` helper, `trace_asAlgebraHom_eq_of_forall_trace_eq`, lives in the port at
  exactly that name and statement as a private declaration of the same module; it is not
  duplicated here because it has no consumer in this node (its consumer is the
  Brauer–Nesbitt proof), per playbook §2.4 — shared mathematics is written once.

  Mathlib-first audit (one line per declaration; the pin's two remaining helpers stay
  `private`, the two promoted ones are audited where they were written):

  * `Representation.span_range_eq_top_of_isIrreducible` (public; the pin's `private`
    `span_range_eq_top_of_isIrreducible` and its public `solution` share this statement) —
    searched `Burnside`, `span_range`, `IsIrreducible` over `Mathlib`
    (`rg -n --multiline 'span_range' Mathlib`, `rg -ni 'burnside' Mathlib`, the whole
    `RepresentationTheory/Irreducible.lean`): mathlib has no Burnside/spanning theorem for
    an irreducible representation. It supplies the two inputs used verbatim — Schur's
    lemma `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`
    (`RepresentationTheory/AlgebraRepresentation/Basic.lean:28`) and Jacobson density
    `jacobson_density` (`RingTheory/SimpleModule/Basic.lean:560`) — and the dictionary
    `Representation.irreducible_iff_isSimpleModule_asModule`
    (`RepresentationTheory/Irreducible.lean:34`); the pin's proof is transcribed;
  * `IsSimpleModule.surjective_toModuleEnd_of_surjective_algebraMap_end` (private) —
    searched `toModuleEnd`, `jacobson_density`, `algebraMap_end` (`rg -n 'toModuleEnd'
    Mathlib`, `rg -n 'algebraMap_end' Mathlib`): mathlib states the neighbouring
    `Module.Finite.toModuleEnd_moduleEnd_surjective`
    (`RingTheory/SimpleModule/Basic.lean:575`), whose hypothesis is `[Module.Finite
    (End R M) M]`, not the pin's `[Module.Free k V] [Module.Finite k V]` plus surjective
    scalar endomorphisms, so it is not a substitute; the pin's proof (a direct
    `jacobson_density` application) is transcribed;
  * `range_asAlgebraHom_toLinearMap` (promoted, in `BrauerNesbittRepresentation.lean`) —
    searched `asAlgebraHom`, `range`, `span_range`
    (`rg -n 'asAlgebraHom' Mathlib/RepresentationTheory`): no statement that the range of
    `asAlgebraHom` is the span of the image; the pin's `MonoidAlgebra.induction_linear`
    proof is transcribed;
  * `span_range_eq_top_iff_surjective_asAlgebraHom` (promoted, same module) — searched the
    same area for a span/surjectivity dictionary: nothing; mathlib's
    `LinearMap.range_eq_top` is the whole proof, as in the pin;
  * `nontrivial_of_isIrreducible` (private) — searched `IsSimpleModule.nontrivial`,
    `Nontrivial` over `RepresentationTheory`: mathlib has `IsSimpleModule.nontrivial`
    (`RingTheory/SimpleModule/Basic.lean:87`) and no representation-level corollary; the
    pin's two-line proof through `asModuleEquiv` is transcribed;
  * `trace_asAlgebraHom_eq_of_forall_trace_eq` (pin-private, not declared here) — its
    port copy is private in `BrauerNesbittRepresentation.lean` with the pin's name and
    statement (`MonoidAlgebra.induction_linear` over the trace); mathlib has no such
    trace-algebra dictionary (`rg -n 'trace.*asAlgebraHom' Mathlib` finds nothing).

  Assumes: mathlib `v4.34.0` and the two promoted helpers of
  `FLTForHuman/Algebra/BrauerNesbittRepresentation.lean`.

  spec-pin: Theorems/Thm_Representation_span_range_eq_top_of_isIrreducible.lean
  spec-pin: P2M/Sol/S_Representation_span_range_eq_top_of_isIrreducible.lean
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Basic
import FLTForHuman.Algebra.BrauerNesbittRepresentation

set_option autoImplicit false

-- The pin's proofs supply their `IsSimpleModule` instances with `haveI`; v4.34's style
-- linter prefers `have` in a proposition goal, which would drop an instance the following
-- elaboration consumes. Suppress the style rule, keep the pin's proofs.
set_option linter.style.haveILetI false

open Module LinearMap


section Burnside

variable {k A V : Type*} [CommRing k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V]
  [Module A V] [IsScalarTower k A V]

private theorem IsSimpleModule.surjective_toModuleEnd_of_surjective_algebraMap_end
    [Module.Free k V] [Module.Finite k V] [IsSimpleModule A V]
    (hcomm : Function.Surjective (algebraMap k (Module.End A V))) :
    Function.Surjective (Module.toModuleEnd k V : A →+* Module.End k V) := by
  classical
  intro f₀

  have hsmul : ∀ (φ : Module.End A V) (v : V), f₀ (φ • v) = φ • (f₀ v) := by
    intro φ v
    obtain ⟨c, rfl⟩ := hcomm φ
    rw [Module.End.smul_def, Module.End.smul_def, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
  let F : Module.End (Module.End A V) V :=
    { toFun := f₀
      map_add' := f₀.map_add
      map_smul' := hsmul }

  let b := Module.Free.chooseBasis k V
  obtain ⟨a, ha⟩ := jacobson_density (R := A) (M := V) F (Finset.univ.image b)
  refine ⟨a, b.ext fun i ↦ ?_⟩
  have := ha (b i) (Finset.mem_image_of_mem b (Finset.mem_univ i))
  have h__af := this.symm
  simp at h__af ⊢
  exact h__af

end Burnside

theorem Representation.span_range_eq_top_of_isIrreducible
    {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    Submodule.span k (Set.range ⇑ρ) = ⊤ := by
  rw [_root_.Representation.span_range_eq_top_iff_surjective_asAlgebraHom ρ]
  haveI : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance

  have hcomm : Function.Surjective (algebraMap k (Module.End (MonoidAlgebra k G) ρ.asModule)) :=
    (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k).surjective

  have hact := IsSimpleModule.surjective_toModuleEnd_of_surjective_algebraMap_end
    (k := k) (A := MonoidAlgebra k G) (V := ρ.asModule) hcomm

  intro f
  obtain ⟨r, hr⟩ := hact (ρ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ρ.asModuleEquiv.toLinearMap)
  refine ⟨r, LinearMap.ext fun v ↦ ?_⟩

  have happ : (r • (ρ.asModuleEquiv.symm v) : ρ.asModule)
      = (ρ.asModuleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ρ.asModuleEquiv.toLinearMap)
          (ρ.asModuleEquiv.symm v) :=
    LinearMap.congr_fun hr (ρ.asModuleEquiv.symm v)

  have hdict : ρ.asAlgebraHom r v = ρ.asModuleEquiv (r • ρ.asModuleEquiv.symm v) := by
    rw [Representation.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]
  rw [hdict, happ]
  simp

private theorem nontrivial_of_isIrreducible {k G V : Type*} [Field k] [Monoid G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    Nontrivial V := by
  haveI : IsSimpleModule (MonoidAlgebra k G) ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule
  exact ρ.asModuleEquiv.symm.toEquiv.nontrivial

