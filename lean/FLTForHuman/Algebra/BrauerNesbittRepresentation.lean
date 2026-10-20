/-
  The Brauer–Nesbitt theorem for finite-dimensional representations over a field: if
  two representations `ρ₁ : Representation k G V₁`, `ρ₂ : Representation k G V₂` of a
  monoid `G` span `End k Vᵢ` and have the same trace on every group element, then
  there is a `k`-linear equivalence `V₁ ≃ₗ[k] V₂` intertwining them.

  The route is the pin's, and it is the characteristic-free one: the span hypothesis
  turns a trace identity into an identity on the whole `MonoidAlgebra k G` action
  (`trace_asAlgebraHom_eq_of_forall_trace_eq`), non-degeneracy of the trace form on
  `End k V` (`eq_zero_of_forall_trace_mul_right_eq_zero`, from
  `Matrix.ext_iff_trace_mul_left`) identifies the two representations' algebra maps
  up to a unique algebra homomorphism `End k V₁ →ₐ[k] End k V₂` (Skolem–Noether by
  hand: `exists_linearEquiv_conj_of_algHom` produces the conjugating equivalence),
  and the finrank equality `finrank k V₁ = finrank k V₂` comes from comparing the
  dimensions of the spans of the trace functions (`finrank_span_range_eq_of_trace_eq`).

  Transcribed verbatim from the pin
  `Theorems/Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq.lean`
  / `P2M/Sol/S_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq.lean`
  (414 pin lines, pinned `aa2d8b3`). Every helper of the pin's `S_` file is `private`,
  including its intermediate `exists_linearEquiv_of_span_range_eq_top_of_trace_eq`;
  the port keeps all of them private and renames that single helper to
  `exists_linearEquiv_aux` so that the **public** headline can carry the pin's own name
  (`Theorems/` wrapper text, verbatim) — the rename is invisible to the checker and to
  the statement. The pin's inner namespaces `Module`, `Module.End`, `Representation`
  and `BrauerNesbitt` are the port's (`p2m_export`/`p2m_open` scaffolding dropped; it
  only re-aliased mathlib's own `Module`/`Representation` vocabulary, which resolves
  directly). The pin's two `end Module.End` closers are written as two bare `end`s
  (playbook §7: `end A.B` closes one scope for the checker's namespace tracker).

  Two helpers are **promoted** (2026-10-20): `Representation.range_asAlgebraHom_toLinearMap`
  and `Representation.span_range_eq_top_iff_surjective_asAlgebraHom` are also pin
  declarations of the node `S_Representation_span_range_eq_top_of_isIrreducible`, whose
  port (`FLTForHuman/RepresentationTheory/Burnside.lean`) imports them from here instead
  of re-proving them; the promotion drops only `private` and leaves both statements
  untouched. `trace_asAlgebraHom_eq_of_forall_trace_eq` stays private here — that node's
  module records why it is not duplicated there.

  Drift against `v4.34.0` — statements untouched:

  * port:381: the pin's private `exists_linearEquiv_of_span_range_eq_top_of_trace_eq` is
    renamed `exists_linearEquiv_aux`; without the rename the pin's own public headline
    name is shadowed in the file (the helper and the wrapper carry the same last name
    and the same statement). The helper stays `private`, so nothing checked changes;
  * port:72–74 and port:253–255: the pin's two `end Module.End` closers are written as
    two bare `end`s (playbook §7, the `end A.B` trap: the checker's namespace tracker
    would otherwise leave `Module` open and misname every later declaration);
  * `import P2M.Util` is not carried; the pin's `p2m_open "Module …"` becomes
    `open Module LinearMap` and its `p2m_export`/`p2m_reactivate` lines are dropped.
    The `@[scoped simp]` attributes on `skolemAux_apply` and `traceAgainst_apply` are
    carried verbatim and need no reactivation in the port;
  * `Mathlib.Tactic.Ring`/`Mathlib.Tactic.Push` are added for the `ring`/`push_cast`
    steps the pin got from `import Mathlib`; every other import is the pin's own.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port. This is
  a different theorem from the port's `FLTForHuman/Algebra/BrauerNesbitt.lean` (which
  homes `Def_RepTheory_BrauerNesbitt_TraceCharZero`, the `MonoidAlgebra` version over
  a characteristic-zero field); the two share no declaration and neither imports the
  other.

  Mathlib-first check (2026-10-20): mathlib has no Brauer–Nesbitt trace theorem.
  `rg -i "brauer"` over `Mathlib/` returns only the Brauer *group* material
  (`Algebra/BrauerGroup/*`) and `rg` for `span_range_eq_top` / `exists_linearEquiv_of_trace`
  finds no statement of this shape; the `Representation` API is mathlib's
  (`asAlgebraHom`, `asAlgebraHom_single`, `IntertwiningMap`) and is imported, not
  re-proved. A more general form does not exist to import: the theorem is equivalent
  to the uniqueness of the semisimple module structure with prescribed character, and
  mathlib's `RingTheory/SimpleModule` material supplies only the simple-module
  vocabulary. Trace-form non-degeneracy is mathlib's
  `Matrix.ext_iff_trace_mul_left`, used as-is.

  spec-pin: Theorems/Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq.lean
  spec-pin: P2M/Sol/S_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq.lean
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push

set_option autoImplicit false

open Module LinearMap

namespace Module
namespace End

section TraceForm

variable {k V : Type*} [CommRing k] [AddCommGroup V] [Module k V]
  [Module.Free k V] [Module.Finite k V]

private theorem eq_zero_of_forall_trace_mul_left_eq_zero {f : Module.End k V}
    (h : ∀ x : Module.End k V, trace k V (x * f) = 0) : f = 0 := by
  classical
  let b := Module.Free.chooseBasis k V
  have hmat : ∀ x : Matrix _ _ k, (x * LinearMap.toMatrix b b f).trace = (x * 0).trace := by
    intro x
    rw [Matrix.mul_zero, Matrix.trace_zero]
    conv_lhs => rw [← (LinearMap.toMatrix b b).apply_symm_apply x]
    rw [← LinearMap.toMatrix_mul b, ← LinearMap.trace_eq_matrix_trace k b]
    exact h _
  have hf0 : LinearMap.toMatrix b b f = 0 := by
    simpa using Matrix.ext_iff_trace_mul_left.mpr hmat
  simpa using congrArg (LinearMap.toMatrix b b).symm hf0

private theorem eq_zero_of_forall_trace_mul_right_eq_zero {f : Module.End k V}
    (h : ∀ x : Module.End k V, trace k V (f * x) = 0) : f = 0 :=
  eq_zero_of_forall_trace_mul_left_eq_zero fun x ↦ (trace_mul_comm k x f).trans (h x)

private theorem ext_of_forall_trace_mul_left_eq {f g : Module.End k V}
    (h : ∀ x : Module.End k V, trace k V (x * f) = trace k V (x * g)) : f = g := by
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_trace_mul_left_eq_zero fun x ↦ by
    rw [mul_sub, map_sub, h, sub_self]

private theorem ext_of_forall_trace_mul_right_eq {f g : Module.End k V}
    (h : ∀ x : Module.End k V, trace k V (f * x) = trace k V (g * x)) : f = g :=
  ext_of_forall_trace_mul_left_eq fun x ↦ by
    rw [trace_mul_comm, h, trace_mul_comm]

end TraceForm

end End

end Module

namespace Module
namespace End

section SkolemNoether

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [FiniteDimensional k V] [FiniteDimensional k W]

omit [FiniteDimensional k V] in

private theorem submodule_eq_bot_or_eq_top_of_forall_map_le {U : Submodule k V}
    (hU : ∀ f : Module.End k V, U.map f ≤ U) : U = ⊥ ∨ U = ⊤ := by
  rcases eq_or_ne U ⊥ with hbot | hbot
  · exact Or.inl hbot
  · refine Or.inr (Submodule.eq_top_iff'.mpr fun w ↦ ?_)
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot

    obtain ⟨f, -, hf⟩ := LinearMap.exists_extend_of_notMem
      (0 : (⊥ : Submodule k V) →ₗ[k] V) (by simpa using hu0) w
    exact hf ▸ hU f ⟨u, hu, rfl⟩

variable (k) in

private noncomputable def skolemAux {n : ℕ} (b : Basis (Fin n) k V)
    (φ : Module.End k V →ₐ[k] Module.End k W) (w : W) (i : Fin n) : V →ₗ[k] W :=
  LinearMap.applyₗ w ∘ₗ φ.toLinearMap ∘ₗ (b.constr k).toLinearMap ∘ₗ
    LinearMap.single k (fun _ : Fin n ↦ V) i

omit [FiniteDimensional k V] [FiniteDimensional k W] in
@[scoped simp] private theorem skolemAux_apply {n : ℕ} (b : Basis (Fin n) k V)
    (φ : Module.End k V →ₐ[k] Module.End k W) (w : W) (i : Fin n) (v : V) :
    skolemAux k b φ w i v = φ (b.constr k (Pi.single i v)) w := rfl

omit [FiniteDimensional k V] [FiniteDimensional k W] in

private theorem skolemAux_comm {n : ℕ} (b : Basis (Fin n) k V)
    (φ : Module.End k V →ₐ[k] Module.End k W) (w : W) (i : Fin n) (a : Module.End k V)
    (v : V) : skolemAux k b φ w i (a v) = φ a (skolemAux k b φ w i v) := by
  have hcon : b.constr k (Pi.single i (a v)) = a * b.constr k (Pi.single i v) := by
    refine b.ext fun l ↦ ?_
    rcases eq_or_ne l i with rfl | hl
    · simp [Module.End.mul_apply]
    · simp [Pi.single_eq_of_ne hl, Module.End.mul_apply]
  rw [skolemAux_apply, skolemAux_apply, hcon, map_mul, Module.End.mul_apply]

omit [FiniteDimensional k V] [FiniteDimensional k W] in

private theorem sum_skolemAux {n : ℕ} (b : Basis (Fin n) k V)
    (φ : Module.End k V →ₐ[k] Module.End k W) (w : W) (f : Module.End k V) :
    ∑ i, skolemAux k b φ w i (f (b i)) = φ f w := by
  have hf : ∑ i, b.constr k (Pi.single i (f (b i))) = f := by
    rw [← map_sum, Finset.univ_sum_single (fun i ↦ f (b i))]
    refine b.ext fun l ↦ ?_
    rw [Basis.constr_basis]
  calc ∑ i, skolemAux k b φ w i (f (b i))
      = ∑ i, φ (b.constr k (Pi.single i (f (b i)))) w := by simp
    _ = φ (∑ i, b.constr k (Pi.single i (f (b i)))) w := by
        rw [map_sum, LinearMap.sum_apply]
    _ = φ f w := by rw [hf]

private theorem exists_linearEquiv_conj_of_algHom [Nontrivial V]
    (φ : Module.End k V →ₐ[k] Module.End k W)
    (hrank : Module.finrank k W = Module.finrank k V) :
    ∃ e : V ≃ₗ[k] W, ∀ a : Module.End k V,
      φ a = e.toLinearMap ∘ₗ a ∘ₗ e.symm.toLinearMap := by
  classical
  have hW : Nontrivial W :=
    Module.nontrivial_of_finrank_pos (R := k) (hrank ▸ Module.finrank_pos)
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  set n := Module.finrank k V with hn
  let b : Basis (Fin n) k V := Module.finBasis k V

  have hex : ∃ i, skolemAux k b φ w i ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hw (by simpa [hno] using (sum_skolemAux b φ w 1).symm)
  obtain ⟨i, hi⟩ := hex

  have hstab : ∀ a : Module.End k V, (LinearMap.ker (skolemAux k b φ w i)).map a ≤
      LinearMap.ker (skolemAux k b φ w i) := by
    rintro a _ ⟨v, hv, rfl⟩
    have hv' : skolemAux k b φ w i v = 0 := hv
    rw [LinearMap.mem_ker, skolemAux_comm, hv', map_zero]
  have hker : LinearMap.ker (skolemAux k b φ w i) = ⊥ := by
    rcases submodule_eq_bot_or_eq_top_of_forall_map_le hstab with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.mp h) hi

  have hinj : Function.Injective (skolemAux k b φ w i) := LinearMap.ker_eq_bot.mp hker
  have hbij : Function.Bijective (skolemAux k b φ w i) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank.symm).mp hinj⟩
  refine ⟨LinearEquiv.ofBijective _ hbij, fun a ↦ ?_⟩

  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  show φ a v = skolemAux k b φ w i (a ((LinearEquiv.ofBijective _ hbij).symm v))
  rw [skolemAux_comm]
  congr 1
  exact ((LinearEquiv.ofBijective _ hbij).apply_symm_apply v).symm

end SkolemNoether

section TraceRank

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {G : Type*} [Mul G]

private noncomputable def traceAgainst (ρ : G → Module.End k V) : Module.End k V →ₗ[k] (G → k) where
  toFun a := fun g ↦ trace k V (a * ρ g)
  map_add' a b := by ext g; simp [add_mul]
  map_smul' c a := by ext g; simp

omit [FiniteDimensional k V] [Mul G] in
@[scoped simp] private theorem traceAgainst_apply (ρ : G → Module.End k V) (a : Module.End k V) (g : G) :
    traceAgainst ρ a g = trace k V (a * ρ g) := rfl

omit [FiniteDimensional k V] [Mul G] in

private theorem traceAgainst_injOn_span (ρ : G → Module.End k V)
    (hnd : ∀ a ∈ Submodule.span k (Set.range ρ),
      (∀ b ∈ Submodule.span k (Set.range ρ), trace k V (a * b) = 0) → a = 0)
    ⦃a : Module.End k V⦄ (ha : a ∈ Submodule.span k (Set.range ρ))
    (h0 : traceAgainst ρ a = 0) : a = 0 := by
  refine hnd a ha fun c hc ↦ ?_

  induction hc using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact congrFun h0 g
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [mul_smul_comm, map_smul, hx, smul_zero]

omit [FiniteDimensional k V] in

private theorem finrank_span_range_eq_finrank_span_traceAgainst (ρ : G → Module.End k V)
    (hmul : ∀ g h : G, ρ g * ρ h = ρ (g * h))
    (hnd : ∀ a ∈ Submodule.span k (Set.range ρ),
      (∀ b ∈ Submodule.span k (Set.range ρ), trace k V (a * b) = 0) → a = 0) :
    Module.finrank k (Submodule.span k (Set.range ρ)) =
      Module.finrank k (Submodule.span k
        (Set.range fun h : G ↦ fun g : G ↦ trace k V (ρ (h * g)))) := by

  set S := Submodule.span k (Set.range ρ) with hS
  have hinj : Function.Injective ((traceAgainst ρ).domRestrict S) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨a, ha⟩ h0
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply] at h0
    exact (Submodule.mk_eq_zero _ _).mpr (traceAgainst_injOn_span ρ hnd ha h0)
  have hrange : LinearMap.range ((traceAgainst ρ).domRestrict S) =
      Submodule.span k (Set.range fun h : G ↦ fun g : G ↦ trace k V (ρ (h * g))) := by
    have h1 : LinearMap.range ((traceAgainst ρ).domRestrict S) = S.map (traceAgainst ρ) := by
      rw [LinearMap.domRestrict, LinearMap.range_comp, Submodule.range_subtype]
    rw [h1, hS, Submodule.map_span, ← Set.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, by ext g; simp [hmul]⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h, by ext g; simp [hmul]⟩
  calc Module.finrank k S
      = Module.finrank k (LinearMap.range ((traceAgainst ρ).domRestrict S)) :=
        (LinearEquiv.ofInjective _ hinj).finrank_eq
    _ = _ := by rw [hrange]

omit [FiniteDimensional k V] in

private theorem finrank_span_range_eq_of_trace_eq {V₂ : Type*} [AddCommGroup V₂] [Module k V₂]
    (ρ₁ : G → Module.End k V) (ρ₂ : G → Module.End k V₂)
    (hmul₁ : ∀ g h : G, ρ₁ g * ρ₁ h = ρ₁ (g * h))
    (hmul₂ : ∀ g h : G, ρ₂ g * ρ₂ h = ρ₂ (g * h))
    (htr : ∀ g : G, trace k V (ρ₁ g) = trace k V₂ (ρ₂ g))
    (hnd₁ : ∀ a ∈ Submodule.span k (Set.range ρ₁),
      (∀ b ∈ Submodule.span k (Set.range ρ₁), trace k V (a * b) = 0) → a = 0)
    (hnd₂ : ∀ a ∈ Submodule.span k (Set.range ρ₂),
      (∀ b ∈ Submodule.span k (Set.range ρ₂), trace k V₂ (a * b) = 0) → a = 0) :
    Module.finrank k (Submodule.span k (Set.range ρ₁)) =
      Module.finrank k (Submodule.span k (Set.range ρ₂)) := by
  have hfun : (fun h : G ↦ fun g : G ↦ trace k V (ρ₁ (h * g))) =
      (fun h : G ↦ fun g : G ↦ trace k V₂ (ρ₂ (h * g))) :=
    funext fun h ↦ funext fun g ↦ htr (h * g)
  rw [finrank_span_range_eq_finrank_span_traceAgainst ρ₁ hmul₁ hnd₁,
    finrank_span_range_eq_finrank_span_traceAgainst ρ₂ hmul₂ hnd₂, hfun]

end TraceRank

end End

end Module


namespace Representation

section Dictionary

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

theorem _root_.Representation.range_asAlgebraHom_toLinearMap (ρ : Representation k G V) :
    LinearMap.range ρ.asAlgebraHom.toLinearMap = Submodule.span k (Set.range ⇑ρ) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨r, rfl⟩
    show ρ.asAlgebraHom r ∈ _
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | single g a =>
      rw [asAlgebraHom_single]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨g, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.single g 1, ρ.asAlgebraHom_single_one g⟩


theorem _root_.Representation.span_range_eq_top_iff_surjective_asAlgebraHom (ρ : Representation k G V) :
    Submodule.span k (Set.range ⇑ρ) = ⊤ ↔ Function.Surjective ρ.asAlgebraHom := by
  rw [← range_asAlgebraHom_toLinearMap]
  exact LinearMap.range_eq_top


private theorem trace_asAlgebraHom_eq_of_forall_trace_eq {V₂ : Type*} [AddCommGroup V₂] [Module k V₂]
    (ρ₁ : Representation k G V) (ρ₂ : Representation k G V₂)
    (htr : ∀ g, trace k V (ρ₁ g) = trace k V₂ (ρ₂ g)) (r : MonoidAlgebra k G) :
    trace k V (ρ₁.asAlgebraHom r) = trace k V₂ (ρ₂.asAlgebraHom r) := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g a => rw [asAlgebraHom_single, asAlgebraHom_single, map_smul, map_smul, htr g]

end Dictionary

end Representation

namespace BrauerNesbitt

section TraceFormCorrespondence

variable {k G V₁ V₂ : Type*} [Field k] [Monoid G]
  [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
  (ρ₁ : Representation k G V₁) (ρ₂ : Representation k G V₂)

private theorem exists_algHom_of_span_range_eq_top_of_trace_eq
    (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span k (Set.range ⇑ρ₂) = ⊤)
    (htr : ∀ g, trace k V₁ (ρ₁ g) = trace k V₂ (ρ₂ g)) :
    ∃ T : Module.End k V₁ →ₐ[k] Module.End k V₂, ∀ g, T (ρ₁ g) = ρ₂ g := by

  have hrange₁ : LinearMap.range ρ₁.asAlgebraHom.toLinearMap = ⊤ :=
    (ρ₁.range_asAlgebraHom_toLinearMap).trans hspan₁
  have hsurj₂ : Function.Surjective ρ₂.asAlgebraHom :=
    (ρ₂.span_range_eq_top_iff_surjective_asAlgebraHom).mp hspan₂

  have hTr := Representation.trace_asAlgebraHom_eq_of_forall_trace_eq ρ₁ ρ₂ htr

  have hext : ∀ c d : Module.End k V₂,
      (∀ r, trace k V₂ (c * ρ₂.asAlgebraHom r) = trace k V₂ (d * ρ₂.asAlgebraHom r)) →
      c = d := by
    intro c d h
    refine Module.End.ext_of_forall_trace_mul_right_eq fun x ↦ ?_
    obtain ⟨r, rfl⟩ := hsurj₂ x
    exact h r

  obtain ⟨s, hs⟩ := ρ₁.asAlgebraHom.toLinearMap.exists_rightInverse_of_surjective hrange₁
  have hs' : ∀ a : Module.End k V₁, ρ₁.asAlgebraHom (s a) = a := fun a ↦
    LinearMap.congr_fun hs a

  set Φ : Module.End k V₁ →ₗ[k] Module.End k V₂ := ρ₂.asAlgebraHom.toLinearMap ∘ₗ s with hΦ
  have hΦ_apply : ∀ a, Φ a = ρ₂.asAlgebraHom (s a) := fun a ↦ by rw [hΦ]; rfl
  have key : ∀ (a : Module.End k V₁) (r : MonoidAlgebra k G),
      trace k V₂ (Φ a * ρ₂.asAlgebraHom r) = trace k V₁ (a * ρ₁.asAlgebraHom r) := by
    intro a r
    rw [hΦ_apply, ← map_mul, ← hTr, map_mul, hs']

  have hval : ∀ r : MonoidAlgebra k G, Φ (ρ₁.asAlgebraHom r) = ρ₂.asAlgebraHom r := by
    intro r
    refine hext _ _ fun r' ↦ ?_
    rw [key, ← map_mul, ← map_mul, hTr]

  have hone : Φ 1 = 1 := by simpa only [map_one] using hval 1
  have hmul : ∀ a b : Module.End k V₁, Φ (a * b) = Φ a * Φ b := by
    intro a b
    refine hext _ _ fun r ↦ ?_

    have h1 : Φ a * Φ b * ρ₂.asAlgebraHom r = Φ a * ρ₂.asAlgebraHom (s b * r) := by
      rw [mul_assoc, hΦ_apply b, ← map_mul]
    have h2 : ρ₁.asAlgebraHom (s b * r) = b * ρ₁.asAlgebraHom r := by
      rw [map_mul, hs']
    rw [h1, key a (s b * r), key (a * b) r, h2, mul_assoc]

  refine ⟨AlgHom.ofLinearMap Φ hone hmul, fun g ↦ ?_⟩
  have hg := hval (MonoidAlgebra.single g 1)
  rw [Representation.asAlgebraHom_single_one, Representation.asAlgebraHom_single_one] at hg
  simpa using hg

private theorem nondeg_of_span_eq_top
    (hspan : Submodule.span k (Set.range ⇑ρ₁) = ⊤) :
    ∀ a ∈ Submodule.span k (Set.range ⇑ρ₁),
      (∀ b ∈ Submodule.span k (Set.range ⇑ρ₁), trace k V₁ (a * b) = 0) → a = 0 := by
  intro a _ h
  exact Module.End.eq_zero_of_forall_trace_mul_right_eq_zero fun x ↦
    h x (hspan ▸ Submodule.mem_top)

private theorem finrank_eq_of_span_range_eq_top_of_trace_eq
    (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span k (Set.range ⇑ρ₂) = ⊤)
    (htr : ∀ g, trace k V₁ (ρ₁ g) = trace k V₂ (ρ₂ g)) :
    finrank k V₂ = finrank k V₁ := by
  have hrk := Module.End.finrank_span_range_eq_of_trace_eq (k := k) ⇑ρ₁ ⇑ρ₂
    (fun g h ↦ (ρ₁.map_mul g h).symm) (fun g h ↦ (ρ₂.map_mul g h).symm) htr
    (nondeg_of_span_eq_top ρ₁ hspan₁) (nondeg_of_span_eq_top ρ₂ hspan₂)
  rw [hspan₁, hspan₂, finrank_top, finrank_top, Module.finrank_linearMap,
    Module.finrank_linearMap] at hrk
  exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp hrk.symm

private theorem exists_linearEquiv_aux [Nontrivial V₁]
    (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span k (Set.range ⇑ρ₂) = ⊤)
    (htr : ∀ g, trace k V₁ (ρ₁ g) = trace k V₂ (ρ₂ g)) :
    ∃ e : V₁ ≃ₗ[k] V₂, ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v) := by
  obtain ⟨T, hT⟩ := exists_algHom_of_span_range_eq_top_of_trace_eq ρ₁ ρ₂ hspan₁ hspan₂ htr
  obtain ⟨e, he⟩ := Module.End.exists_linearEquiv_conj_of_algHom T
    (finrank_eq_of_span_range_eq_top_of_trace_eq ρ₁ ρ₂ hspan₁ hspan₂ htr)
  refine ⟨e, fun g v ↦ ?_⟩
  have hg : ρ₂ g = e.toLinearMap ∘ₗ ρ₁ g ∘ₗ e.symm.toLinearMap := (hT g).symm.trans (he _)
  rw [hg]
  simp

end TraceFormCorrespondence

end BrauerNesbitt

theorem BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq {k : Type*} {G : Type*}
  {V₁ : Type*} {V₂ : Type*} [Field k] [Monoid G] [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂] (ρ₁ : Representation k G V₁)
  (ρ₂ : Representation k G V₂) [Nontrivial V₁] (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
  (hspan₂ : Submodule.span k (Set.range ⇑ρ₂) = ⊤)
  (htr : ∀ (g : G), (LinearMap.trace k V₁) (ρ₁ g) = (LinearMap.trace k V₂) (ρ₂ g)) :
  ∃ e : V₁ ≃ₗ[k] V₂, ∀ (g : G) (v : V₁), e ((ρ₁ g) v) = (ρ₂ g) (e v) :=
  BrauerNesbitt.exists_linearEquiv_aux ρ₁ ρ₂ hspan₁ hspan₂ htr
