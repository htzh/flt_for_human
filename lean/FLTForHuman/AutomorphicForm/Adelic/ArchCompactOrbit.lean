/-
  The archimedean compact group's right-regular action, and the carrier of continuous
  functions with finite-dimensional orbit span.

  At a number field `F` the product `ArchIsometryProd F` of the local row-isometry compact
  groups `rowIsometrySubgroup₀ w.Completion` maps into `GL₂(𝔸_F)` through the finite-support
  product `archProdIncl F`, whose range is the supremum of the local images and whose image is
  compact (`isCompact_iSup_range_rowIsometryInclAt₀`). Composing the adèlic right-regular
  representation with that inclusion gives `archRep F` on *all* functions `GL₂(𝔸_F) → ℂ`; its
  orbit span `orbitSpan F φ` is the `ℂ`-span of the archimedean right translates of `φ`.
  `Ecf F` is the submodule of continuous `φ` whose orbit span is finite-dimensional — the
  carrier — and `ρc F` is the restricted representation on it. `exists_invt_compl` is the
  compact-group invariant-complement statement for the carrier, and `isSemisimpleModule_ρc`
  the semisimplicity of its type-algebra module.

  This is the engine half of `AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate`
  (and of the sibling right-convolution node, whose pin file carries the same block
  byte-identically). It states no headline: that is a fact about the mathematics, not about
  the wiring.

  **Spellings.** `spec/check_port.py` diffs a module declaration by declaration against the
  pin's `Theorems/` wrapper and `P2M/Sol/S_` file, matching on the *statement text* up to the
  pin's `kw`-prefix and namespace erasures (`spec/lean_parser.py:norm`). A declaration's own
  name is not part of its statement, so a renamed declaration still verifies by content — but
  its *mentioners* would have to be rewritten, and each of those becomes `MISSING`, because its
  statement text then has no counterpart in the wire. With `0 missing` demanded of both
  `spec-pin:` files, every name that occurs *inside* a statement keeps the pin's spelling:
  `ArchIsometryProd`, `archRep`, `Ecf`, `ρc`, `orbitSpan` are the pin's verbatim. The pin's
  abbreviated carriers are also its statement vocabulary, so the order's §3 rectification is
  not reachable for this node's declarations (an added public alias would itself be `MISSING`:
  it is not in the wire). See the set's record.

  **Do not "fix" these names.** They are load-bearing, not leftovers: the normalizer
  `spec/lean_parser.py:300` erases exactly three things from a statement before hashing it — the
  `ModularCurve.`/`AlgebraicCurve.` namespace prefixes and the `kw*` promotion prefixes — and
  nothing else, so a name that is *mentioned inside* a statement can be rectified only by moving
  it into a namespace those rules erase, by making it `private` (and giving up its diff), or by
  making it a `kw*` name (a residual `kw` prefix is itself a checker failure). Renaming
  `ArchIsometryProd`, `archRep`, `Ecf`, `ρc` to their order-§3 tokens without one of those three
  homes turns every declaration that mentions them into a `MISSING`; adding `pin:` rows cannot
  help, because a marker still requires the statement hash to match.

  Reuse, by import and never restated:
  * `BiIsotypic.orbitSpan` — `orbitSpan` and `orbitSpanc` below *are* the generic orbit span at
    the concrete representations, `archRep F` and `ρc F` (reducible aliases, so every
    `Submodule.span_induction`/`span_le` step of the pin's proofs fires unchanged);
  * the two ported `Representation` premises, `exists_isCompl_forall_mem_of_compactSpace_of_continuous`
    and `exists_extend_forall_apply_mul_of_injective`, in place of the pin's
    `exists_stable_compl`/`exists_equivariant_extend` restatements (not ported);
  * `ArchInfra.isCompact_rowIsometrySubgroup₀` in place of the pin's 33-line compactness proof.

  `IsotypicCuspSpace`'s definition layer is imported for the `rowIsometrySubgroup₀`/
  `rowIsometryInclAt₀`/`adelicArchGLInclAt` vocabulary; `RightConvComm/SliceCentrality`'s
  `contSubmodule` (the same carrier construction without the finiteness condition) was read and
  is **not** shared: our carrier lives on `AdelicGL2 (𝓞 F) F` and adds finite-dimensionality of
  the orbit span, so no generic lemma fell out cheaply, and the bridge
  `typeSubmodule_eq_typeSpan` is used by `ArchCutProjector`, which imports it itself.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean:19–418`
  (pinned `aa2d8b3`; the pin's `F4CutWords` and `PartB`/`PartB3` sections), minus its
  `solution`-staging.

  spec-pin: Theorems/Thm_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean   -- comparable copy
-/
import FLTForHuman.RepTheory.BiIsotypic
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra
import FLTForHuman.RepresentationTheory.CompactGroup
import Mathlib.RepresentationTheory.Submodule
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.CuspidalConstituent
open scoped Pointwise BigOperators

namespace AutomorphicForm.ArchCompactOrbit

/-! ### Generic continuity lemmas -/

theorem continuous_finset_noncommProd {X M ι : Type*} [TopologicalSpace X] [TopologicalSpace M] [Monoid M]
    [ContinuousMul M] (s : Finset ι) (f : ι → X → M) (hf : ∀ i, Continuous (f i))
    (comm : ∀ x, (s : Set ι).Pairwise fun i j => Commute (f i x) (f j x)) :
    Continuous fun x => s.noncommProd (fun i => f i x) (comm x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.noncommProd_empty]; exact continuous_const
  | @insert a s ha ih =>
    have comm' : ∀ x, (s : Set ι).Pairwise fun i j => Commute (f i x) (f j x) := fun x =>
      (comm x).mono (by simp)
    simp_rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
    exact (hf a).mul (ih comm')

/-- Weak continuity of a representation follows from continuity of a separating family of
matrix coefficients: the separating functionals are all of them. -/
theorem continuous_dual_apply_of_separating {H : Type*} [Group H] [TopologicalSpace H]
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] (π : Representation ℂ H E)
    {X : Type*} (ev : X → Module.Dual ℂ E) (hsep : ∀ v : E, (∀ x, ev x v = 0) → v = 0)
    (hcont : ∀ (x : X) (v : E), Continuous fun k => ev x (π k v)) :
    ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v) := by
  let D : Submodule ℂ (Module.Dual ℂ E) :=
    { carrier := {ℓ | ∀ v : E, Continuous fun k => ℓ (π k v)}
      zero_mem' := fun v => by simpa using continuous_const
      add_mem' := fun {a b} ha hb v => by have h__af := (ha v).add (hb v); simp at h__af ⊢; exact h__af
      smul_mem' := fun c {a} ha v => by have h__af := (ha v).const_smul c; simp at h__af ⊢; exact h__af }
  have hD : D = ⊤ := by
    have hco : D.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      rw [Submodule.mem_bot]
      exact hsep v fun x => hv _ (hcont x)
    have hfin := Subspace.finrank_add_finrank_dualCoannihilator_eq D
    rw [hco, finrank_bot, add_zero] at hfin
    exact Submodule.eq_top_of_finrank_eq (hfin.trans (Subspace.dual_finrank_eq).symm)
  intro ℓ v
  have : ℓ ∈ D := by rw [hD]; trivial
  exact this v

/-! ### The archimedean product compact group -/

section Compactness

variable (K : Type*) [Field K] [NumberField K]

/-- The local row-isometry subgroup of `GL₂(K_w)` is compact, hence a `CompactSpace`; the pin
proves the compactness in 33 lines, and the port's `ArchInfra` already has it. -/
scoped instance compactSpace_rowIsometrySubgroup₀ (w : InfinitePlace K) :
    CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
  isCompact_iff_compactSpace.mp (@ArchInfra.isCompact_rowIsometrySubgroup₀ w.Completion _
    (NumberField.AdelicBox.properSpace_completion (K := K) w))

end Compactness

variable (F : Type) [Field F] [NumberField F]

theorem val_adelicArchGLInclAt_apply (w : InfinitePlace F) (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    ((adelicArchGLInclAt F w k : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      (archMatrixUpdate F w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) := rfl

section FieldLevel

variable (F : Type) [Field F]

theorem continuous_archMatrixUpdate (w : InfinitePlace F) : Continuous (archMatrixUpdate F w) := by
  classical
  have h1 : Continuous fun m : Matrix (Fin 2) (Fin 2) w.Completion =>
      Function.update (1 : Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) w m :=
    continuous_const.update w continuous_id

  have h2 : Continuous fun f : (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) =>
      (archMatrixPiEquiv F).symm f := by
    refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => ?_
    exact ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply v)))
  exact h2.comp h1

end FieldLevel

variable (F : Type) [Field F] [NumberField F]

theorem continuous_adelicArchGLInclAt (w : InfinitePlace F) : Continuous (adelicArchGLInclAt F w) := by
  rw [Units.continuous_iff]
  have hval : ∀ {f : GL (Fin 2) w.Completion → GL (Fin 2) w.Completion}, Continuous f →
      Continuous fun k => ((adelicArchGLInclAt F w (f k) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    intro f hf
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp_rw [val_adelicArchGLInclAt_apply]
    refine Continuous.prodMk ?_ continuous_const
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_archMatrixUpdate F w).comp (Units.continuous_val.comp hf)))
  refine ⟨hval continuous_id, ?_⟩
  simp_rw [← map_inv]
  exact hval continuous_inv

theorem continuous_rowIsometryInclAt₀ (w : InfinitePlace F) : Continuous (rowIsometryInclAt₀ F w) :=
  (continuous_adelicArchGLInclAt F w).comp continuous_subtype_val

abbrev ArchIsometryProd : Type := Π w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion

def archProdIncl : ArchIsometryProd F →* AdelicGL2 (𝓞 F) F :=
  MonoidHom.noncommPiCoprod (fun w => rowIsometryInclAt₀ F w) fun v w hvw x y => by
    rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
    exact commute_adelicArchGLInclAt_of_ne F hvw _ _

theorem archProdIncl_range :
    (archProdIncl F).range = ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range := by
  unfold archProdIncl
  exact MonoidHom.noncommPiCoprod_range _

theorem continuous_archProdIncl : Continuous (archProdIncl F) := by
  classical
  have hcomm : ∀ x : ArchIsometryProd F,
      ((Finset.univ : Finset (InfinitePlace F)) : Set (InfinitePlace F)).Pairwise fun i j =>
        Commute (rowIsometryInclAt₀ F i (x i)) (rowIsometryInclAt₀ F j (x j)) := by
    intro x i _ j _ hij
    rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
    exact commute_adelicArchGLInclAt_of_ne F hij _ _
  exact continuous_finset_noncommProd (s := (Finset.univ : Finset (InfinitePlace F)))
    (f := fun w (k : ArchIsometryProd F) => rowIsometryInclAt₀ F w (k w))
    (fun w => (continuous_rowIsometryInclAt₀ F w).comp (continuous_apply w)) hcomm

theorem isCompact_iSup_range_rowIsometryInclAt₀ :
    IsCompact ((⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by
  rw [← archProdIncl_range, MonoidHom.coe_range]
  exact isCompact_range (continuous_archProdIncl F)

/-! ### The right-regular representation and the carrier -/

def archRep : Representation ℂ (ArchIsometryProd F) (AdelicGL2 (𝓞 F) F → ℂ) :=
  (rightRegular F).comp (archProdIncl F)

theorem archRep_apply (k : ArchIsometryProd F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archRep F k φ = rightTranslate F (archProdIncl F k) φ := rfl

theorem archRep_apply_apply (k : ArchIsometryProd F) (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) :
    archRep F k φ x = φ (x * archProdIncl F k) := rfl

theorem continuous_archRep {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (k : ArchIsometryProd F) :
    Continuous (archRep F k φ) :=
  hφ.comp (continuous_mul_const _)

/-- The `ℂ`-span of the archimedean right translates of `φ` — `BiIsotypic.orbitSpan` at the
right-regular representation through the product inclusion. Spelled at the concrete
representation (the two are `rfl`-equal, `orbitSpan_eq_biIsotypic`); the head must be
`Submodule.span` for the pin's `span_induction` steps to elaborate. -/
abbrev orbitSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (Set.range fun k : ArchIsometryProd F => archRep F k φ)

private theorem orbitSpan_eq_biIsotypic (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    orbitSpan F φ = BiIsotypic.orbitSpan (V := AdelicGL2 (𝓞 F) F → ℂ) (archRep F) φ := by
  simp only [orbitSpan, BiIsotypic.orbitSpan]

theorem mem_orbitSpan_self (φ : AdelicGL2 (𝓞 F) F → ℂ) : φ ∈ orbitSpan F φ :=
  Submodule.subset_span ⟨1, by simp⟩

theorem archRep_mem_orbitSpan (φ : AdelicGL2 (𝓞 F) F → ℂ) (k : ArchIsometryProd F) :
    ∀ ψ ∈ orbitSpan F φ, archRep F k ψ ∈ orbitSpan F φ := by
  intro ψ hψ
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨j, rfl⟩
    refine Submodule.subset_span ⟨k * j, ?_⟩
    show archRep F (k * j) φ = archRep F k (archRep F j φ)
    rw [map_mul]; rfl
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem orbitSpan_le_of_mem {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (h : ψ ∈ orbitSpan F φ) :
    orbitSpan F ψ ≤ orbitSpan F φ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact archRep_mem_orbitSpan F φ k ψ h

theorem continuous_of_mem_orbitSpan {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) :
    ∀ ψ ∈ orbitSpan F φ, Continuous ψ := by
  intro ψ hψ
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨k, rfl⟩; exact continuous_archRep F hφ k
  · exact continuous_const
  · intro a b _ _ ha hb; exact ha.add hb
  · intro c a _ ha; exact ha.const_smul c

def Ecf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) where
  carrier := {φ | Continuous φ ∧ FiniteDimensional ℂ (orbitSpan F φ)}
  zero_mem' := by
    refine ⟨continuous_const, ?_⟩
    have : orbitSpan F (0 : AdelicGL2 (𝓞 F) F → ℂ) ≤ ⊥ := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩; simp
    exact Submodule.finiteDimensional_of_le this
  add_mem' := by
    rintro a b ⟨hac, haf⟩ ⟨hbc, hbf⟩
    refine ⟨hac.add hbc, ?_⟩
    have : orbitSpan F (a + b) ≤ orbitSpan F a ⊔ orbitSpan F b := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show archRep F k (a + b) ∈ _
      rw [map_add]
      exact Submodule.add_mem_sup (archRep_mem_orbitSpan F a k a (mem_orbitSpan_self F a))
        (archRep_mem_orbitSpan F b k b (mem_orbitSpan_self F b))
    exact Submodule.finiteDimensional_of_le this
  smul_mem' := by
    rintro c a ⟨hac, haf⟩
    refine ⟨hac.const_smul c, ?_⟩
    have : orbitSpan F (c • a) ≤ orbitSpan F a := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show archRep F k (c • a) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ c (archRep_mem_orbitSpan F a k a (mem_orbitSpan_self F a))
    exact Submodule.finiteDimensional_of_le this

theorem mem_Ecf {φ : AdelicGL2 (𝓞 F) F → ℂ} :
    φ ∈ Ecf F ↔ Continuous φ ∧ FiniteDimensional ℂ (orbitSpan F φ) := Iff.rfl

theorem archRep_mem_Ecf (k : ArchIsometryProd F) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ Ecf F) :
    archRep F k φ ∈ Ecf F :=
  letI : FiniteDimensional ℂ (orbitSpan F φ) := hφ.2
  ⟨continuous_archRep F hφ.1 k,
    Submodule.finiteDimensional_of_le
      (orbitSpan_le_of_mem F (archRep_mem_orbitSpan F φ k φ (mem_orbitSpan_self F φ)))⟩

def ρc : Representation ℂ (ArchIsometryProd F) (Ecf F) where
  toFun k := (archRep F k).restrict fun φ hφ => archRep_mem_Ecf F k hφ
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp

theorem ρc_apply_coe (k : ArchIsometryProd F) (φ : Ecf F) :
    ((ρc F k φ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = archRep F k φ := rfl

/-- Every finite-dimensional stable subspace of the carrier has a stable complement inside any
larger finite-dimensional stable subspace — the pin's `exists_invt_compl`, obtained from the
ported compact-group premise instead of the pin's own restatement of it. -/
theorem exists_invt_compl (E : Submodule ℂ (Ecf F)) [FiniteDimensional ℂ E] (hE : E ∈ (ρc F).invtSubmodule)
    (P : Submodule ℂ (Ecf F)) (hP : P ∈ (ρc F).invtSubmodule) (hPE : P ≤ E) :
    ∃ Pc : Submodule ℂ (Ecf F), Pc ∈ (ρc F).invtSubmodule ∧ P ⊓ Pc = ⊥ ∧ P ⊔ Pc = E := by
  rw [Representation.mem_invtSubmodule] at hE hP

  let π : Representation ℂ (ArchIsometryProd F) E :=
    { toFun := fun k => (ρc F k).restrict fun v hv => hE k hv
      map_one' := by ext v; simp
      map_mul' := fun a b => by ext v; simp }
  have hπ : ∀ (k : ArchIsometryProd F) (v : E), ((π k v : E) : Ecf F) = ρc F k v := fun k v => rfl

  have hcont : ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v) := by
    refine continuous_dual_apply_of_separating (H := ArchIsometryProd F) (E := E) π
      (fun x : AdelicGL2 (𝓞 F) F => (LinearMap.proj x).comp ((Ecf F).subtype.comp E.subtype)) ?_ ?_
    · intro v hv
      apply Subtype.ext; apply Subtype.ext
      funext x; exact hv x
    · intro x v
      show Continuous fun k => (((π k v : E) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) x
      simp only [hπ, ρc_apply_coe, archRep_apply_apply]
      exact (v.1.2.1).comp (continuous_const.mul (continuous_archProdIncl F))
  let P₀ : Submodule ℂ E := P.comap E.subtype
  have hP₀ : ∀ (k : ArchIsometryProd F) (v : E), v ∈ P₀ → π k v ∈ P₀ := fun k v hv => hP k hv
  obtain ⟨Pc₀, hc, hst⟩ :=
    Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous
      (H := ArchIsometryProd F) (E := E) π hcont P₀ hP₀
  refine ⟨Pc₀.map E.subtype, ?_, ?_, ?_⟩
  · rw [Representation.mem_invtSubmodule]
    intro g x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨π g v, hst g v hv, rfl⟩
  · have hPmap : P = P₀.map E.subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hPE]
    rw [hPmap, ← Submodule.map_inf E.subtype Subtype.val_injective, hc.inf_eq_bot, Submodule.map_bot]
  · have hPmap : P = P₀.map E.subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hPE]
    rw [hPmap, ← Submodule.map_sup, hc.sup_eq_top, Submodule.map_top, Submodule.range_subtype]

/-! ### The orbit span on the carrier -/

/-- The orbit span of `φ` inside the carrier — again `BiIsotypic.orbitSpan`, now at the
restricted representation `ρc F` (`orbitSpanc_eq_biIsotypic`). -/
abbrev orbitSpanc (φ : Ecf F) : Submodule ℂ (Ecf F) :=
  Submodule.span ℂ (Set.range fun k : ArchIsometryProd F => ρc F k φ)

private theorem orbitSpanc_eq_biIsotypic (φ : Ecf F) :
    orbitSpanc F φ = BiIsotypic.orbitSpan (V := Ecf F) (ρc F) φ := by
  simp only [orbitSpanc, BiIsotypic.orbitSpan]

theorem mem_orbitSpanc_self (φ : Ecf F) : φ ∈ orbitSpanc F φ :=
  Submodule.subset_span ⟨1, by simp⟩

theorem map_orbitSpanc (φ : Ecf F) : (orbitSpanc F φ).map (Ecf F).subtype = orbitSpan F φ := by
  rw [orbitSpanc, Submodule.map_span, orbitSpan]
  congr 1
  ext ψ
  simp only [Set.mem_image, Set.mem_range, Submodule.subtype_apply, exists_exists_eq_and, ρc_apply_coe]

scoped instance finiteDimensional_orbitSpanc (φ : Ecf F) : FiniteDimensional ℂ (orbitSpanc F φ) := by
  refine letI : FiniteDimensional ℂ (orbitSpan F (φ : AdelicGL2 (𝓞 F) F → ℂ)) := φ.2.2; ?_
  have e := Submodule.equivMapOfInjective (Ecf F).subtype Subtype.val_injective (orbitSpanc F φ)
  rw [map_orbitSpanc] at e
  exact LinearEquiv.finiteDimensional e.symm

theorem orbitSpanc_mem_invtSubmodule (φ : Ecf F) : orbitSpanc F φ ∈ (ρc F).invtSubmodule := by
  rw [Representation.mem_invtSubmodule]
  intro k
  change orbitSpanc F φ ≤ (orbitSpanc F φ).comap (ρc F k)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  refine Submodule.subset_span ⟨k * j, ?_⟩
  show ρc F (k * j) φ = ρc F k (ρc F j φ)
  rw [map_mul]; rfl

theorem isSemisimpleModule_ρc :
    IsSemisimpleModule (MonoidAlgebra ℂ (ArchIsometryProd F)) (ρc F).asModule := by
  classical
  let e := (ρc F).mapSubmodule
  let O : Ecf F → (ρc F).invtSubmodule := fun φ => ⟨orbitSpanc F φ, orbitSpanc_mem_invtSubmodule F φ⟩
  let p : Ecf F → Submodule (MonoidAlgebra ℂ (ArchIsometryProd F)) (ρc F).asModule := fun φ => e (O φ)
  refine isSemisimpleModule_of_isSemisimpleModule_submodule' (p := p) (fun φ => ?_) ?_
  ·
    rw [isSemisimpleModule_iff, (Submodule.mapIic (p φ)).complementedLattice_iff]
    refine ⟨fun q => ?_⟩
    obtain ⟨q, hq⟩ := q
    let T : (ρc F).invtSubmodule := e.symm q
    have hT : (T : Submodule ℂ (Ecf F)) ≤ orbitSpanc F φ := by
      have : T ≤ O φ := by
        have := e.symm.monotone hq
        simpa [T, p, e.symm_apply_apply] using this
      exact this
    obtain ⟨Pc, hPcinv, hinf, hsup⟩ :=
      exists_invt_compl F (orbitSpanc F φ) (orbitSpanc_mem_invtSubmodule F φ) T T.2 hT
    let Tc : (ρc F).invtSubmodule := ⟨Pc, hPcinv⟩
    have hTc : Tc ≤ O φ := by
      show (Pc : Submodule ℂ (Ecf F)) ≤ orbitSpanc F φ
      rw [← hsup]; exact le_sup_right
    have hq' : e T = q := e.apply_symm_apply q
    refine ⟨⟨e Tc, e.monotone hTc⟩, ?_, ?_⟩
    · rw [disjoint_iff]
      apply Subtype.ext
      show q ⊓ e Tc = ⊥
      rw [← hq', ← e.map_inf, ← e.map_bot]
      congr 1
      apply Subtype.ext
      show (T : Submodule ℂ (Ecf F)) ⊓ Pc = ⊥
      exact hinf
    · rw [codisjoint_iff]
      apply Subtype.ext
      show q ⊔ e Tc = p φ
      rw [← hq', ← e.map_sup]
      congr 1
      apply Subtype.ext
      show (T : Submodule ℂ (Ecf F)) ⊔ Pc = orbitSpanc F φ
      exact hsup
  ·
    rw [eq_top_iff]
    intro m _
    refine Submodule.mem_iSup_of_mem ((ρc F).asModuleEquiv m) ?_
    change m ∈ ((orbitSpanc F ((ρc F).asModuleEquiv m)).toAddSubmonoid.map
      ((ρc F).asModuleEquiv.symm : (Ecf F) →+ (ρc F).asModule))
    exact AddSubmonoid.mem_map.mpr ⟨(ρc F).asModuleEquiv m, mem_orbitSpanc_self F _,
      (ρc F).asModuleEquiv.symm_apply_apply m⟩

end AutomorphicForm.ArchCompactOrbit
