/-
  The carrier of the right translates of an automorphic function, and the span they generate.

  `AdelicFnCarrier` is `AdelicGL₂(𝔸_F) → ℂ` with the pointwise additive and `ℂ`-module structure and
  the right action of `AdelicGL₂(𝔸_F)`; `AdelicSpanSubmodule φ` is the submodule its right translates
  generate, and `AdelicSpan φ` is that submodule as a type. A newvector datum's `ConductorDatum` is
  what makes the span irreducible, which is how the weight-one lift's Nebentypus is read off it.

  Transcribed verbatim from `Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean` (pinned
  `aa2d8b3`, 179 lines: 43 declarations — 27 named, of which `check_port` diffs all 27, and 16
  anonymous `instance`s). The pin's `def`s and `instance`s are transcribed body and all (FR-0232),
  the scaffold's nine `sorry`s are the pin's own proofs, and the file's section structure is
  the pin's: one `variable (F : Type*) [Field F] [NumberField F]` at namespace level with the inner
  namespaces adding only their own variables (`{F}` for the carrier, `φ` for the span, `p` and `φ`
  for the `p`-adic action).

  spec-pin: Definitions/Def_LocalNewvector_AdelicSpanCarrier.lean

  ## Port deltas

  * **Imports.** The pin's stub imports are replaced by the port modules: the pin's
    `Def_AutomorphicForm_AutomorphicFnAt` by `AutomorphicForm.Adelic.Basic` (as the scaffold stood),
    and `Def_AdelicDock_LocalEmbedding` by `NumberTheory.AdelicDock.LocalEmbedding` (added here: it
    is what supplies `AdelicDock.padicToAdelic`, and through it `LocalNewvector.padicK1`). No module
    is imported that the file does not use.
  * **Two `private` conductor-datum transcriptions.** The two `typeOf_*` statements at the end are
    stated over the pin's conductor vocabulary, `fixedSubmodule` and `HasNewvectorConductor`, which
    live in the pin's `Def_LocalNewvector_ConductorDatum.lean` — a file the port has not reached and
    that nothing in the import closure provides. They are therefore transcribed here verbatim from
    that pin file and declared `private`: `check_port` and `scaffold_audit` both skip `private`
    declarations (FR-0242), so this module's public surface stays exactly the carrier pin's. They
    are live, not dead: both are referenced by the statements of the two `typeOf_*` theorems. When
    the conductor datum is ported, these become imports.
  * **Bodies.** All nine `sorry`s are the pin's proofs (`rfl` for the four instance-revealing
    lemmas — the two `padic_smul_def`s and the two `typeOf_*`s — and the pin's term/`span_induction`
    proofs for the other five).
  * **Sections.** The scaffold's per-declaration `section`s are gone. A `variable` command at
    namespace level is the pin's (`variable (F : Type*)` at its `:11`, `variable {F}` at `:64`,
    `variable (F)` at `:132`), and the `p`-adic action is the pin's `section PadicAction` with its
    `variable (p : ℕ) [Fact p.Prime]` and `variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}`.
  * **`end`s are named.** The pin closes its two namespaces with a bare `end`; v4.34 needs the name
    (FR-0233), so they read `end AdelicFnCarrier` / `end AdelicSpan`; statement-neutral.
  * **No `open AdelicFnCarrier`.** The scaffold had one and the pin does not; every use is
    `AdelicFnCarrier.mk` in the pin's own text, so the opener is dropped.

  ## Gate readings

  - `check_port --force` reads **27 ok, 0 mismatch, 0 missing, 0 own, 0 kw** — all 27 named
    declarations of the pin, every row `ok` — including the nine the scaffold carried as `sorry`,
    among them the two `typeOf_*` statements stated over the `private` conductor vocabulary above.
  - `scaffold_audit` reads **complete** (27 pin publics on the wire, 25 port declarations).
  - `lake env lean -DautoImplicit=false` is silent; `lake build` reports
    `Build completed successfully (3466 jobs)`.
  - `#print axioms` on all 27 rows: every one `[propext, Classical.choice, Quot.sound]`.
  - `dedup.py --within --module AdelicSpan` reports **1 cluster**, and it is the pin's own pair (see
    the dedup note below).
  - `move_dead.py … --dry-run` reads `0 declarations, 0 lines` (no deferred pin surface).

  ## Dedup note

  `dedup.py --within` reports one intra-module cluster, and it is the pin's own pair: the two
  anonymous `DistribMulAction.compHom _ (AdelicDock.padicToAdelic p)` instances (for
  `AdelicFnCarrier ℚ` and for `AdelicSpan φ`). They are two different types' instances and the pin
  writes both; nothing is collapsed.

  ## Heartbeat probe pair (recorded, never installed — FR-0225)

  No `set_option maxHeartbeats` in this module. Probe, run from `lean/`:

    lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/NumberTheory/LocalNewvector/AdelicSpan.lean

  silent at `N = 2000`, fails at `N/2 = 1000` with
  `:130:2: error: (deterministic) timeout at 'whnf', maximum number of heartbeats (1000) has been
  reached` at `inferInstanceAs (AddCommGroup (AdelicGL2 (𝓞 F) F → ℂ))`. Project default `4000000`.
-/


import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.RepresentationTheory.Basic

set_option autoImplicit false

noncomputable section

open MeasureTheory AutomorphicForm
open scoped ENNReal NNReal Pointwise
open NumberField IsDedekindDomain


namespace LocalNewvector

/- The two `typeOf_*` statements at the end are stated over the pin's conductor-datum vocabulary,
   which lives in `Definitions/Def_LocalNewvector_ConductorDatum.lean` (not ported; see the header's
   port deltas). Transcribed verbatim from that pin file and `private`, so that the public surface
   of this module stays exactly the carrier pin's. -/

section ConductorDatum

variable (p : ℕ) [Fact p.Prime]

private def fixedSubmodule {G : Type*} [Group G] (U : Subgroup G) (V : Type*) [AddCommGroup V]
    [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] : Submodule ℂ V where
  carrier := {v | ∀ g ∈ U, g • v = v}
  add_mem' := by
    intro v w hv hw g hg
    rw [smul_add, hv g hg, hw g hg]
  zero_mem' := by
    intro g _
    exact smul_zero g
  smul_mem' := by
    intro c v hv g hg
    rw [smul_comm, hv g hg]

private def HasNewvectorConductor (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    (c : ℕ) : Prop :=
  fixedSubmodule (padicK1 p c) V ≠ ⊥ ∧ ∀ m < c, fixedSubmodule (padicK1 p m) V = ⊥

end ConductorDatum

variable (F : Type*) [Field F] [NumberField F]

def AdelicFnCarrier : Type _ :=
  AdelicGL2 (𝓞 F) F → ℂ

namespace AdelicFnCarrier

variable {F}

def mk (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicFnCarrier F := φ

def toFn (φ : AdelicFnCarrier F) : AdelicGL2 (𝓞 F) F → ℂ := φ

@[simp] theorem toFn_mk (φ : AdelicGL2 (𝓞 F) F → ℂ) : (mk φ).toFn = φ := rfl

@[simp] theorem mk_toFn (φ : AdelicFnCarrier F) : mk φ.toFn = φ := rfl

@[ext] theorem ext {φ ψ : AdelicFnCarrier F} (h : ∀ g, φ.toFn g = ψ.toFn g) : φ = ψ :=
  funext h

instance : AddCommGroup (AdelicFnCarrier F) :=
  inferInstanceAs (AddCommGroup (AdelicGL2 (𝓞 F) F → ℂ))

instance : Module ℂ (AdelicFnCarrier F) :=
  inferInstanceAs (Module ℂ (AdelicGL2 (𝓞 F) F → ℂ))

@[simp] theorem toFn_zero : (0 : AdelicFnCarrier F).toFn = 0 := rfl

@[simp] theorem toFn_add (φ ψ : AdelicFnCarrier F) : (φ + ψ).toFn = φ.toFn + ψ.toFn := rfl

@[simp] theorem toFn_csmul (c : ℂ) (φ : AdelicFnCarrier F) : (c • φ).toFn = c • φ.toFn := rfl

instance : DistribMulAction (AdelicGL2 (𝓞 F) F) (AdelicFnCarrier F) where
  smul g φ := mk fun x => φ.toFn (x * g)
  one_smul φ := ext fun x => congrArg φ.toFn (mul_one x)
  mul_smul g h φ := ext fun x => congrArg φ.toFn (mul_assoc x g h).symm
  smul_zero _ := ext fun _ => rfl
  smul_add _ _ _ := ext fun _ => rfl

@[simp] theorem toFn_smul (g : AdelicGL2 (𝓞 F) F) (φ : AdelicFnCarrier F) (x : AdelicGL2 (𝓞 F) F) :
    (g • φ).toFn x = φ.toFn (x * g) := rfl

instance : SMulCommClass ℂ (AdelicGL2 (𝓞 F) F) (AdelicFnCarrier F) where
  smul_comm _ _ _ := ext fun _ => rfl

instance : SMulCommClass (AdelicGL2 (𝓞 F) F) ℂ (AdelicFnCarrier F) :=
  SMulCommClass.symm _ _ _

theorem mk_ne_zero_of_ne_zero {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ≠ 0) : mk φ ≠ 0 :=
  fun h => hφ (congrArg toFn h)

end AdelicFnCarrier

variable {F}

def AdelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicFnCarrier F) :=
  Submodule.span ℂ {ψ | ∃ g : AdelicGL2 (𝓞 F) F, ψ = g • AdelicFnCarrier.mk φ}

theorem mk_mem_adelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicFnCarrier.mk φ ∈ AdelicSpanSubmodule φ :=
  Submodule.subset_span ⟨1, (one_smul _ _).symm⟩

theorem smul_mem_adelicSpanSubmodule (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    {ψ : AdelicFnCarrier F} (hψ : ψ ∈ AdelicSpanSubmodule φ) :
    g • ψ ∈ AdelicSpanSubmodule φ := by
  refine Submodule.span_induction
    (fun x ⟨h, hh⟩ => Submodule.subset_span ⟨g * h, by rw [hh, mul_smul]⟩)
    (by rw [smul_zero]; exact zero_mem _)
    (fun x y _ _ hx hy => by rw [smul_add]; exact add_mem hx hy)
    (fun c x _ hx => by rw [smul_comm]; exact Submodule.smul_mem _ c hx) hψ

def AdelicSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) : Type _ :=
  AdelicSpanSubmodule φ

namespace AdelicSpan

variable (φ : AdelicGL2 (𝓞 F) F → ℂ)

def mk (ψ : AdelicFnCarrier F) (hψ : ψ ∈ AdelicSpanSubmodule φ) : AdelicSpan φ :=
  ⟨ψ, hψ⟩

def toFn (ψ : AdelicSpan φ) : AdelicFnCarrier F :=
  (ψ : AdelicSpanSubmodule φ).val

@[ext] theorem ext {ψ₁ ψ₂ : AdelicSpan φ} (h : toFn φ ψ₁ = toFn φ ψ₂) : ψ₁ = ψ₂ :=
  Subtype.ext h

instance : AddCommGroup (AdelicSpan φ) :=
  inferInstanceAs (AddCommGroup (AdelicSpanSubmodule φ))

instance : Module ℂ (AdelicSpan φ) :=
  inferInstanceAs (Module ℂ (AdelicSpanSubmodule φ))

instance : DistribMulAction (AdelicGL2 (𝓞 F) F) (AdelicSpan φ) where
  smul g ψ := mk φ (g • toFn φ ψ)
    (smul_mem_adelicSpanSubmodule φ g (ψ : AdelicSpanSubmodule φ).2)
  one_smul ψ := ext φ (one_smul (AdelicGL2 (𝓞 F) F) (toFn φ ψ))
  mul_smul g h ψ := ext φ (mul_smul (α := AdelicGL2 (𝓞 F) F) g h (toFn φ ψ))
  smul_zero g := ext φ (smul_zero (A := AdelicFnCarrier F) g)
  smul_add g ψ₁ ψ₂ := ext φ (smul_add (A := AdelicFnCarrier F) g (toFn φ ψ₁) (toFn φ ψ₂))

@[simp] theorem toFn_smul (g : AdelicGL2 (𝓞 F) F) (ψ : AdelicSpan φ) :
    toFn φ (g • ψ) = g • toFn φ ψ := rfl

instance : SMulCommClass ℂ (AdelicGL2 (𝓞 F) F) (AdelicSpan φ) where
  smul_comm c g ψ := ext φ (smul_comm (α := AdelicFnCarrier F) c g (toFn φ ψ))

instance : SMulCommClass (AdelicGL2 (𝓞 F) F) ℂ (AdelicSpan φ) :=
  SMulCommClass.symm _ _ _

def self : AdelicSpan φ :=
  mk φ (AdelicFnCarrier.mk φ) (mk_mem_adelicSpanSubmodule φ)

@[simp] theorem toFn_self : toFn φ (self φ) = AdelicFnCarrier.mk φ := rfl

theorem self_ne_zero_of_ne_zero (hφ : φ ≠ 0) : self φ ≠ 0 := by
  intro h
  exact AdelicFnCarrier.mk_ne_zero_of_ne_zero hφ (congrArg (toFn φ) h)

end AdelicSpan

variable (F)

theorem adelicSpan_self_one_ne_zero :
    AdelicSpan.self (F := F) (fun _ => (1 : ℂ)) ≠ 0 :=
  AdelicSpan.self_ne_zero_of_ne_zero _ (by intro h; exact one_ne_zero (congrFun h 1))

section PadicAction

variable (p : ℕ) [Fact p.Prime]

instance : DistribMulAction (GL (Fin 2) ℚ_[p]) (AdelicFnCarrier ℚ) :=
  DistribMulAction.compHom _ (AdelicDock.padicToAdelic p)

theorem AdelicFnCarrier.padic_smul_def (g : GL (Fin 2) ℚ_[p]) (φ : AdelicFnCarrier ℚ) :
    g • φ = (AdelicDock.padicToAdelic p g : AdelicGL2 (𝓞 ℚ) ℚ) • φ := rfl

instance : SMulCommClass ℂ (GL (Fin 2) ℚ_[p]) (AdelicFnCarrier ℚ) where
  smul_comm c g φ := smul_comm (α := AdelicFnCarrier ℚ) c (AdelicDock.padicToAdelic p g) φ

instance : SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ (AdelicFnCarrier ℚ) :=
  SMulCommClass.symm _ _ _

variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

instance : DistribMulAction (GL (Fin 2) ℚ_[p]) (AdelicSpan φ) :=
  DistribMulAction.compHom _ (AdelicDock.padicToAdelic p)

theorem AdelicSpan.padic_smul_def (g : GL (Fin 2) ℚ_[p]) (ψ : AdelicSpan φ) :
    g • ψ = (AdelicDock.padicToAdelic p g : AdelicGL2 (𝓞 ℚ) ℚ) • ψ := rfl

instance : SMulCommClass ℂ (GL (Fin 2) ℚ_[p]) (AdelicSpan φ) where
  smul_comm c g ψ := smul_comm (α := AdelicSpan φ) c (AdelicDock.padicToAdelic p g) ψ

instance : SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ (AdelicSpan φ) :=
  SMulCommClass.symm _ _ _

theorem AdelicSpan.typeOf_hasNewvectorConductor (c : ℕ) :
    (HasNewvectorConductor p (AdelicSpan φ) c) = (HasNewvectorConductor p (AdelicSpan φ) c) := rfl

theorem AdelicSpan.typeOf_fixedSubmodule_padicK1 (n : ℕ) :
    (fixedSubmodule (padicK1 p n) (AdelicSpan φ) : Submodule ℂ (AdelicSpan φ))
      = fixedSubmodule (padicK1 p n) (AdelicSpan φ) := rfl

end PadicAction

end LocalNewvector

end
