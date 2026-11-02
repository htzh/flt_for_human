/-
  The archimedean cut is admissible: the span of its translates is finite-dimensional.

  `archCutSubmodule F tys` is the subspace of functions on `GL₂(𝔸_F)` whose archimedean
  translates lie in finitely many archimedean types `tys`; `archDualCutSubmodule` is its
  dual twin.  An archimedean compact group acts on both by right translation, through a
  product homomorphism `ι` whose one-place factors are the row-isometry subgroups
  `rowIsometrySubgroup₀ w.Completion`.

  This module proves that the span of the translates of one cut vector by that action is
  finite-dimensional, in three forms:

  * `finiteDimensional_span_translates_of_mem_archCutSubmodule`: for an arbitrary product
    `ι` with componentwise hypothesis `hι`, the span of
    `{fun g => x (g * adelicArchGLIncl F (ι κ)) | κ}` is finite-dimensional, all its members
    are continuous, it lies in the cut, and it is stable under the right translates by the
    action;
  * `finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule` and
    `finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule`: the span of the
    right translates of a vector of the cut (resp. of the dual cut) by the subgroup
    `⨆ w, (rowIsometryInclAt₀ F w).range` of `AdelicGL2 (𝓞 F) F` is finite-dimensional.

  What is assumed: the archimedean span engines of the port —
  `ArchCutProjector.placeOrbitSpan` with its per-place finite-dimensionality lemmas,
  `ArchCompactOrbit.orbitSpan`/`archRep` with the dictionary `orbitSpan_eq_span` and the
  subgroup induction `rightTranslate_mem_of_mem_iSup_range'`,
  `CuspidalConstituent.rightTranslate` and the per-place span
  `CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`
  — and the two dictionary lemmas of the ground module `ArchComponentDictionary`
  (`ext_archComponent`, `adelicArchGLIncl_iota_mulSingle`).

  Transcribed from the three `S_` files of the rows (pinned `aa2d8b3`), whose statements are
  the `Theorems/` wrappers'; the pin's private helpers are private here too, and its
  proof-search namespaces (`KFinSpanProof`, `F4CutWords`, `F4Iso`) are dropped.

  spec-pin: Theorems/Thm_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchComponentDictionary
import FLTForHuman.AutomorphicForm.Adelic.ArchCutProjector
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArchTypeSpan
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
  IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [-ext] NumberField.InfinitePlace.Completion.ext
attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext

namespace AutomorphicForm

/-! ### The translate span supported on a finite set of places -/

section SpanOn

variable {F : Type} [Field F] [NumberField F]

/-- The span of the archimedean right translates of `f` by the products `ι κ` whose components
outside the finite place set `s` are trivial. -/
private def spanOn
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (s : Finset (InfinitePlace F)) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ ((fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
    rightTranslate F (adelicArchGLIncl F (ι κ)) f) ''
    {κ | ∀ v : InfinitePlace F, v ∉ s → κ v = 1})

/-- The span supported on a finite place set is finite-dimensional and stays inside the cut: the
induction splits a product supported on `insert w s` into its `w`-component and a product supported
on `s`, and the `w`-component acts by a translate of the per-place span. -/
private theorem finiteDimensional_spanOn_and_le
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : ArchTypeFamily F) (s : Finset (InfinitePlace F)) :
    ∀ f : AdelicGL2 (𝓞 F) F → ℂ, f ∈ archCutSubmodule F tys →
      FiniteDimensional ℂ ↥(spanOn ι s f) ∧ spanOn ι s f ≤ archCutSubmodule F tys := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    have hle : spanOn ι ∅ f ≤ Submodule.span ℂ {f} := by
      refine Submodule.span_mono ?_
      rintro _ ⟨κ, hκ, rfl⟩
      have : κ = 1 := funext fun v => hκ v (Finset.notMem_empty v)
      subst this
      show rightTranslate F (adelicArchGLIncl F (ι 1)) f ∈ ({f} : Set (AdelicGL2 (𝓞 F) F → ℂ))
      rw [map_one, map_one]
      refine Set.mem_singleton_iff.mpr (funext fun g => ?_)
      rw [rightTranslate_apply, mul_one]
    have : FiniteDimensional ℂ ↥(Submodule.span ℂ ({f} : Set (AdelicGL2 (𝓞 F) F → ℂ))) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_singleton f)
    exact ⟨Submodule.finiteDimensional_of_le hle,
      hle.trans (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hf))⟩
  | insert w s hws ih =>
    intro f hf
    obtain ⟨hMfd, hMle⟩ := ih f hf
    set M := spanOn ι s f with hM

    have := hMfd
    obtain ⟨T, hT⟩ : M.FG := (Submodule.fg_iff_finiteDimensional M).mpr hMfd

    let Sw : (AdelicGL2 (𝓞 F) F → ℂ) → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := fun t =>
      Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        rightTranslate F (rowIsometryInclAt₀ F w k) t)
    have hSwfd : ∀ t ∈ T, FiniteDimensional ℂ ↥(Sw t) := by
      intro t ht
      have htM : t ∈ M := by rw [← hT]; exact Submodule.subset_span ht
      have htcut : t ∈ archCutSubmodule F tys := hMle htM
      have htw := (mem_archCutSubmodule_iff F tys t).mp htcut w
      exact (CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
        F w (tys.card w) (tys.rep w) t htw).1
    set W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := ⨆ t : ↥T, Sw (t : AdelicGL2 (𝓞 F) F → ℂ) with hW
    have : ∀ t : ↥T, FiniteDimensional ℂ ↥(Sw (t : AdelicGL2 (𝓞 F) F → ℂ)) := fun t => hSwfd t t.2
    have hWfd : FiniteDimensional ℂ ↥W := Submodule.finiteDimensional_iSup _

    have hRW : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ m ∈ M,
        rightTranslate F (rowIsometryInclAt₀ F w k) m ∈ W := by
      intro k m hm
      rw [← hT] at hm
      refine Submodule.span_induction
        (p := fun m _ => rightTranslate F (rowIsometryInclAt₀ F w k) m ∈ W) ?_ ?_ ?_ ?_ hm
      · intro t ht
        refine (le_iSup (fun t : ↥T => Sw (t : AdelicGL2 (𝓞 F) F → ℂ)) ⟨t, ht⟩) ?_
        exact Submodule.subset_span ⟨k, rfl⟩
      · show rightTranslate F (rowIsometryInclAt₀ F w k) 0 ∈ W
        rw [rightTranslate_zero]; exact W.zero_mem
      · intro a b _ _ ha hb; rw [rightTranslate_add]; exact W.add_mem ha hb
      · intro c a _ ha; rw [rightTranslate_smul]; exact W.smul_mem c ha

    have hgen : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∀ v, v ∉ insert w s → κ v = 1) →
        ∃ m ∈ M, rightTranslate F (adelicArchGLIncl F (ι κ)) f
          = rightTranslate F (rowIsometryInclAt₀ F w (κ w)) m := by
      intro κ hκ
      set κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Function.update κ w 1
        with hκ'
      have hκ's : ∀ v, v ∉ s → κ' v = 1 := by
        intro v hv
        by_cases hvw : v = w
        · subst hvw; simp [hκ']
        · rw [hκ', Function.update_of_ne hvw]
          exact hκ v (by simp [hvw, hv])
      have hdec : κ = Pi.mulSingle w (κ w) * κ' := by
        funext v
        by_cases hvw : v = w
        · subst hvw; simp [hκ']
        · simp [hκ', Pi.mulSingle_eq_of_ne hvw, Function.update_of_ne hvw]
      refine ⟨rightTranslate F (adelicArchGLIncl F (ι κ')) f, Submodule.subset_span ⟨κ', hκ's, rfl⟩, ?_⟩
      conv_lhs => rw [hdec]
      rw [map_mul, map_mul, ← rightTranslate_rightTranslate, adelicArchGLIncl_iota_mulSingle ι hι]
    have hle : spanOn ι (insert w s) f ≤ W := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨κ, hκ, rfl⟩
      obtain ⟨m, hm, heq⟩ := hgen κ hκ
      show rightTranslate F (adelicArchGLIncl F (ι κ)) f ∈ _
      rw [heq]
      exact hRW _ m hm
    refine ⟨Submodule.finiteDimensional_of_le hle, Submodule.span_le.mpr ?_⟩
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨m, hm, heq⟩ := hgen κ hκ
    show rightTranslate F (adelicArchGLIncl F (ι κ)) f ∈ _
    rw [heq]
    exact rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule F tys (hMle hm) w (κ w)

end SpanOn

/-- **The translate span of a cut vector is an admissible archimedean module.** For a product
homomorphism `ι` whose components are the row-isometry subgroups, the span of the translates
`fun g => x (g * adelicArchGLIncl F (ι κ))` is finite-dimensional, consists of continuous
functions, lies in the cut, and is stable under every right translate of the action. -/
theorem finiteDimensional_span_translates_of_mem_archCutSubmodule
    (F : Type) [Field F] [NumberField F]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hxc : Continuous x) (hxt : x ∈ archCutSubmodule F tys) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ)))) ∧
    (∀ v ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))), Continuous v) ∧
    Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) ≤ archCutSubmodule F tys ∧
    ∀ v ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))), ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      (fun g : AdelicGL2 (𝓞 F) F => v (g * adelicArchGLIncl F (ι κ))) ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) := by
  classical

  have hE : Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) = spanOn ι Finset.univ x := by
    show Submodule.span ℂ _ = Submodule.span ℂ _
    congr 1
    ext v
    simp only [Set.mem_range, Set.mem_image, Set.mem_ofPred_eq, Finset.mem_univ, not_true_eq_false,
      IsEmpty.forall_iff, implies_true, true_and]
    rfl
  obtain ⟨hfd, hle⟩ := finiteDimensional_spanOn_and_le ι hι tys Finset.univ x hxt
  refine ⟨by rw [hE]; exact hfd, ?_, by rw [hE]; exact hle, ?_⟩
  ·
    intro v hv
    refine Submodule.span_induction (p := fun v _ => Continuous v) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨κ, rfl⟩
      exact hxc.comp (continuous_id.mul continuous_const)
    · exact continuous_const
    · intro a b _ _ ha hb; exact ha.add hb
    · intro c a _ ha; exact ha.const_smul c
  ·
    intro v hv κ
    refine Submodule.span_induction
      (p := fun v _ => (fun g : AdelicGL2 (𝓞 F) F => v (g * adelicArchGLIncl F (ι κ))) ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ)))) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨κ', rfl⟩
      refine Submodule.subset_span ⟨κ * κ', ?_⟩
      funext g
      simp only [map_mul, mul_assoc]
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; exact Submodule.smul_mem _ c ha

/-! ### The orbit span on the cut and on the dual cut

The two rows `finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule` and
`finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule` share one engine: a
finite-dimensional, stable envelope of a vector in a pointwise `⨆` of type submodules, and the
`ArchCutProjector` dictionary between the product orbit span and the span over
`⨆ w, (rowIsometryInclAt₀ F w).range`. -/

section OrbitEnvelope

variable (F : Type) [Field F] [NumberField F]

/-- A generator `T v` of a type submodule has a finite-dimensional orbit span at its place: the
orbit is the image of the finite-dimensional representation space under the equivariant map `T`. -/
private theorem finiteDimensional_placeOrbitSpan_of_mem_typeSubmodule
    (w : InfinitePlace F) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) V)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ typeSubmodule (rowIsometryInclAt₀ F w) ρ) :
    FiniteDimensional ℂ (ArchCutProjector.placeOrbitSpan F w φ) := by
  refine Submodule.span_induction
    (p := fun φ _ => FiniteDimensional ℂ (ArchCutProjector.placeOrbitSpan F w φ)) ?_ ?_ ?_ ?_ hφ
  · rintro f ⟨T, hT, v, rfl⟩
    have : ArchCutProjector.placeOrbitSpan F w (T v) ≤ LinearMap.range T := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨ρ k v, ?_⟩
      funext x; exact hT k v x
    exact Submodule.finiteDimensional_of_le this
  · have : ArchCutProjector.placeOrbitSpan F w (0 : AdelicGL2 (𝓞 F) F → ℂ) ≤ ⊥ :=
      Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; simp [rightTranslate_zero])
    exact Submodule.finiteDimensional_of_le this
  · intro a b _ _ ha hb
    have : ArchCutProjector.placeOrbitSpan F w (a + b)
        ≤ ArchCutProjector.placeOrbitSpan F w a ⊔ ArchCutProjector.placeOrbitSpan F w b := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (a + b) ∈ _
      rw [rightTranslate_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this
  · intro c a _ ha
    have : ArchCutProjector.placeOrbitSpan F w (c • a)
        ≤ ArchCutProjector.placeOrbitSpan F w a := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (c • a) ∈ _
      rw [rightTranslate_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this

/-- The same for a vector of a finite pointwise `⨆` of type submodules. -/
private theorem finiteDimensional_placeOrbitSpan_of_mem_iSup_typeSubmodule
    (w : InfinitePlace F) {m : ℕ}
    (V : Fin m → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ (rowIsometrySubgroup₀ w.Completion) (V i))
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ F w) (ρ i)) :
    FiniteDimensional ℂ (ArchCutProjector.placeOrbitSpan F w φ) := by
  refine Submodule.iSup_induction _
    (motive := fun φ => FiniteDimensional ℂ (ArchCutProjector.placeOrbitSpan F w φ)) hφ
    (fun i f hf => finiteDimensional_placeOrbitSpan_of_mem_typeSubmodule F w (ρ i) hf) ?_ ?_
  · have : ArchCutProjector.placeOrbitSpan F w (0 : AdelicGL2 (𝓞 F) F → ℂ) ≤ ⊥ :=
      Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; simp [rightTranslate_zero])
    exact Submodule.finiteDimensional_of_le this
  · intro a b ha hb
    have : ArchCutProjector.placeOrbitSpan F w (a + b)
        ≤ ArchCutProjector.placeOrbitSpan F w a ⊔ ArchCutProjector.placeOrbitSpan F w b := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (a + b) ∈ _
      rw [rightTranslate_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this

/-- A one-place translate of a vector in a pointwise `⨆` of type submodules stays in the `⨆` at
every place: at its own place by right equivariance, elsewhere by commutation of the one-place
factors. -/
private theorem rightTranslate_mem_iSup_typeSubmodule
    {n : InfinitePlace F → ℕ} (W : ∀ w : InfinitePlace F, Fin (n w) → Type)
    [∀ w i, AddCommGroup (W w i)] [∀ w i, Module ℂ (W w i)]
    (ρ : ∀ (w : InfinitePlace F) (i : Fin (n w)),
      Representation ℂ (rowIsometrySubgroup₀ w.Completion) (W w i))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (g : AdelicGL2 (𝓞 F) F → ℂ)
    (hg : ∀ v : InfinitePlace F, g ∈ ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i))
    (v : InfinitePlace F) :
    rightTranslate F (rowIsometryInclAt₀ F w k) g ∈
      ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i) := by
  refine Submodule.iSup_induction _
    (motive := fun f => rightTranslate F (rowIsometryInclAt₀ F w k) f ∈
      ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i)) (hg v) ?_ ?_ ?_
  · intro i f hfi
    refine le_iSup (fun j => typeSubmodule (rowIsometryInclAt₀ F v) (ρ v j)) i ?_
    by_cases hw : v = w
    · subst hw
      exact comp_mul_mem_typeSubmodule hfi k
    · exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
        commute_adelicArchGLInclAt_of_ne F (fun h => hw h.symm) _ _
  · show rightTranslate F _ 0 ∈ _
    rw [rightTranslate_zero]; exact Submodule.zero_mem _
  · intro a b ha hb
    show rightTranslate F _ (a + b) ∈ _
    rw [rightTranslate_add]; exact Submodule.add_mem _ ha hb

/-- **The stable envelope.** A vector lying, at every place, in the `⨆` of a finite family of type
submodules has a finite-dimensional subspace containing it that is stable under every one-place
right translate: the envelope is built by a `Finset` induction over the places, and each `insert`
step is a supremum of the per-place orbit spans of a basis of the previous envelope. -/
private theorem exists_finiteDimensional_stable_of_forall_mem_iSup_typeSubmodule
    {n : InfinitePlace F → ℕ} (W : ∀ w : InfinitePlace F, Fin (n w) → Type)
    [∀ w i, AddCommGroup (W w i)] [∀ w i, Module ℂ (W w i)]
    [∀ w i, FiniteDimensional ℂ (W w i)]
    (ρ : ∀ (w : InfinitePlace F) (i : Fin (n w)),
      Representation ℂ (rowIsometrySubgroup₀ w.Completion) (W w i))
    {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : ∀ w : InfinitePlace F, f ∈ ⨆ i : Fin (n w), typeSubmodule (rowIsometryInclAt₀ F w) (ρ w i))
    (hst : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
      (g : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ v : InfinitePlace F, g ∈ ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i)) →
      ∀ v : InfinitePlace F, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈
        ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i)) :
    ∃ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ Z ∧ f ∈ Z ∧
      ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ z ∈ Z,
        rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z := by
  classical

  let Cut : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    ⨅ v : InfinitePlace F, ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i)
  have hmemCut : ∀ g, g ∈ Cut ↔
      ∀ v, g ∈ ⨆ i : Fin (n v), typeSubmodule (rowIsometryInclAt₀ F v) (ρ v i) :=
    fun g => Submodule.mem_iInf _
  have hfCut : f ∈ Cut := (hmemCut f).mpr hf
  have hstCut : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ Cut,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ Cut := fun w k g hg =>
    (hmemCut _).mpr (hst w k g ((hmemCut g).mp hg))
  have key : ∀ s : Finset (InfinitePlace F), ∃ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ Z ∧ f ∈ Z ∧ Z ≤ Cut ∧
      ∀ w ∈ s, ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ z ∈ Z,
        rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Submodule.span ℂ {f}, inferInstance, Submodule.subset_span rfl,
        Submodule.span_le.mpr (by simpa using hfCut), by simp⟩
    | @insert w s hw ih =>
      obtain ⟨Z, hZfd, hφZ, hZA, hZst⟩ := ih
      let Z' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
        ⨆ k : rowIsometrySubgroup₀ w.Completion, Z.map (rightRegular F (rowIsometryInclAt₀ F w k))
      have hgen : ∀ (k : rowIsometrySubgroup₀ w.Completion) (z), z ∈ Z →
          rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z' := fun k z hz =>
        Submodule.mem_iSup_of_mem k ⟨z, hz, rfl⟩
      refine ⟨Z', ?_, ?_, ?_, ?_⟩
      · let b := Module.finBasis ℂ Z
        have hle : Z' ≤ ⨆ i, ArchCutProjector.placeOrbitSpan F w
            (b i : AdelicGL2 (𝓞 F) F → ℂ) := by
          refine iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun z hz => ?_
          rw [Submodule.mem_comap]
          have hz' : (⟨z, hz⟩ : Z) ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
          have : z ∈ Submodule.span ℂ (Set.range fun i => (b i : AdelicGL2 (𝓞 F) F → ℂ)) := by
            have := Submodule.mem_map_of_mem (f := Z.subtype) hz'
            rw [Submodule.map_span, ← Set.range_comp] at this
            exact this
          refine Submodule.span_induction ?_ ?_ ?_ ?_ this
          · rintro _ ⟨i, rfl⟩
            exact Submodule.mem_iSup_of_mem i (Submodule.subset_span ⟨k, rfl⟩)
          · show rightTranslate F (rowIsometryInclAt₀ F w k) 0 ∈ _
            rw [rightTranslate_zero]; exact Submodule.zero_mem _
          · intro a c _ _ ha hc
            show rightTranslate F _ (a + c) ∈ _
            rw [rightTranslate_add]; exact Submodule.add_mem _ ha hc
          · intro c a _ ha
            show rightTranslate F _ (c • a) ∈ _
            rw [rightTranslate_smul]; exact Submodule.smul_mem _ c ha
        have : ∀ i, FiniteDimensional ℂ (ArchCutProjector.placeOrbitSpan F w
            (b i : AdelicGL2 (𝓞 F) F → ℂ)) := fun i =>
          finiteDimensional_placeOrbitSpan_of_mem_iSup_typeSubmodule F w (W w) (ρ w)
            (((hmemCut _).mp (hZA (b i).2)) w)
        exact Submodule.finiteDimensional_of_le hle
      · have := hgen 1 f hφZ
        rwa [map_one, show rightTranslate F (1 : AdelicGL2 (𝓞 F) F) f = f from
          funext fun x => by simp [rightTranslate]] at this
      · refine iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun z hz => ?_
        rw [Submodule.mem_comap]
        exact hstCut w k z (hZA hz)
      · intro w' hw' k'
        refine fun z hz => Submodule.iSup_induction _
          (motive := fun z => rightTranslate F (rowIsometryInclAt₀ F w' k') z ∈ Z') hz ?_ ?_ ?_
        · rintro k _ ⟨z₀, hz₀, rfl⟩
          show rightTranslate F (rowIsometryInclAt₀ F w' k')
            (rightTranslate F (rowIsometryInclAt₀ F w k) z₀) ∈ Z'
          rcases Finset.mem_insert.mp hw' with rfl | hw's
          · rw [rightTranslate_rightTranslate, ← map_mul]
            exact hgen _ z₀ hz₀
          · have hne : w' ≠ w := fun h => hw (h ▸ hw's)
            rw [rightTranslate_rightTranslate, rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply,
              (commute_adelicArchGLInclAt_of_ne F hne _ _).eq, ← rightTranslate_rightTranslate]
            exact hgen k _ (hZst w' hw's k' z₀ hz₀)
        · show rightTranslate F _ 0 ∈ Z'
          rw [rightTranslate_zero]; exact Submodule.zero_mem _
        · intro a c ha hc; rw [rightTranslate_add]; exact Submodule.add_mem _ ha hc
  obtain ⟨Z, hZfd, hfZ, -, hZst⟩ := key Finset.univ
  exact ⟨Z, hZfd, hfZ, fun w k z hz => hZst w (Finset.mem_univ w) k z hz⟩

/-- A finite-dimensional stable envelope bounds the span of the orbit: the span of the right
translates over `⨆ w, (rowIsometryInclAt₀ F w).range` is finite-dimensional. -/
private theorem finiteDimensional_span_rightTranslate_of_exists_stable
    {f : AdelicGL2 (𝓞 F) F → ℂ}
    (h : ∃ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ Z ∧ f ∈ Z ∧
      ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ z ∈ Z,
        rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z) :
    FiniteDimensional ℂ (Submodule.span ℂ
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k f}) := by
  obtain ⟨Z, hZfd, hfZ, hZst⟩ := h
  have := hZfd
  refine Submodule.finiteDimensional_of_le (S₂ := Z) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, hk, rfl⟩
  exact ArchCutProjector.rightTranslate_mem_of_mem_iSup_range' F Z hZst hk f hfZ

end OrbitEnvelope

/-- **The orbit span on the cut.** The span of the right translates of a vector of the archimedean
cut by `⨆ w, (rowIsometryInclAt₀ F w).range` is finite-dimensional. -/
theorem finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archCutSubmodule F tys) :
    FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k f}) := by
  refine finiteDimensional_span_rightTranslate_of_exists_stable F ?_
  exact exists_finiteDimensional_stable_of_forall_mem_iSup_typeSubmodule F
    (n := fun w => tys.card w)
    (W := fun w (i : Fin (tys.card w)) => Fin ((tys.rep w i).n) → ℂ)
    (ρ := fun w i => (tys.rep w i).ρ) (f := f)
    (fun w => (mem_archCutSubmodule_iff F tys f).mp hf w)
    (fun w k g hg v => rightTranslate_mem_iSup_typeSubmodule F
      (fun w (i : Fin (tys.card w)) => Fin ((tys.rep w i).n) → ℂ) (fun w i => (tys.rep w i).ρ) w k g hg v)

/-- **The orbit span on the dual cut.** The same for the dual cut `archDualCutSubmodule`, whose
type modules are the duals of the archimedean types. -/
theorem finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualCutSubmodule F tys) :
    FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k f}) := by
  refine finiteDimensional_span_rightTranslate_of_exists_stable F ?_
  exact exists_finiteDimensional_stable_of_forall_mem_iSup_typeSubmodule F
    (n := fun w => tys.card w)
    (W := fun w (i : Fin (tys.card w)) => Module.Dual ℂ (Fin ((tys.rep w i).n) → ℂ))
    (ρ := fun w i => (tys.rep w i).ρ.dual) (f := f)
    (fun w => (mem_archDualCutSubmodule_iff F tys f).mp hf w)
    (fun w k g hg v => rightTranslate_mem_iSup_typeSubmodule F
      (fun w (i : Fin (tys.card w)) => Module.Dual ℂ (Fin ((tys.rep w i).n) → ℂ))
      (fun w i => (tys.rep w i).ρ.dual) w k g hg v)

end AutomorphicForm
