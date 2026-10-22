/-
  The archimedean type projector on the K-finite cut.

  `TypeWitness` is one archimedean type together with a right-equivariant map out of it;
  `exists_finset_typeWitness_of_mem_iSup` shows that a vector of a finite supremum of type
  submodules already lies in a supremum of finitely many such ranges, and
  `le_iSup_archTypeSubmoduleAt_of_surjective` transports a type-boundedness statement across
  an equivariant surjection. `cutc` is the archimedean cut `archCutSubmodule F tys` seen inside
  the carrier `Ecf F` of `ArchCompactOrbit`, `cutM` the same cut as a module for the type
  algebra `ℂK`, and `typeComponents`/`CA`/`CB` split the isotypic components of that module into
  those inside the cut and those outside, with `isCompl_CA_CB` the `IsCompl`. `projectorOnTypeComponents`
  is the resulting projection, `QM` its endomorphic form and `Qc` its transport to the carrier,
  which commutes with the restricted representation (`Qc_ρc`), fixes the cut
  (`Qc_eq_self_of_mem_cutc`) and lands in the orbit span (`Qc_mem_orbitSpanc`). The headline
  `exists_linearMap_archCutProjector_comm_rightTranslate` extends `Qc` to all functions on
  `GL₂(𝔸_F)` and assembles the three properties.

  This is not a wrapper around `ArchCompactOrbit`: the K-finite cut and the type projector on
  it are mathematics that module does not state. It imports the engine.

  Reuse actually taken (see the set's record for the full table):
  * `ArchCompactOrbit` — `Ecf`, `ρc`, `orbitSpan`, `orbitSpanc`, `map_orbitSpanc`,
    `orbitSpanc_mem_invtSubmodule`, `mem_orbitSpanc_self`, `isSemisimpleModule_ρc`,
    `archRep`, `archProdIncl`, `archProdIncl_range`, `archRep_apply`, `ρc_apply_coe`;
  * `IsotypicCuspSpace`'s definition layer — `typeSubmodule`, `archTypeSubmoduleAt`,
    `archCutSubmodule`, `mem_archCutSubmodule_iff`, `rowIsometryInclAt₀`,
    `comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule`, `ArchTypeFamily`, `ArchRepAt`,
    `mem_typeSubmodule_of_isRightEquivariant`;
  * the ported premise `Representation.exists_extend_forall_apply_mul_of_injective` in place of
    the pin's `exists_equivariant_extend` restatement;
  * `BiIsotypic.finiteDimensional_orbitSpan`, through the type-submodule ↔ type-span dictionary,
    in place of the pin's concrete span induction
    (`finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt`);
  * mathlib's `Isotypic` API (`isotypicComponents`, `sSupIndep_isotypicComponents`,
    `sSup_isotypicComponents`, `le_isotypicComponent_iff`, `LinearMap.le_comap_isotypicComponent`)
    under `le_biSup_isotypicComponents_of_forall_linearEquiv_le`,
    `exists_add_eq_of_isCompl_biSup_isotypicComponents` and `exists_eq_span_singleton_of_isSimpleModule`,
    which mathlib does not state (they are ported).

  **The dictionary is one step too specialised.** `RightConvComm/SliceCentrality.lean:76` (not
  imported: its `e`'s codomain is the archimedean `GL₂`, so calling it would not typecheck here)
  states `typeSubmodule e σ = BiIsotypic.typeSpan (rightRep e) σ` for
  `e : H →* GL (Fin 2) (InfiniteAdeleRing F)`, i.e. on the archimedean `GL₂`; the cut of this
  module lives on `AdelicGL2 (𝓞 F) F` (`rowIsometryInclAt₀ F w` lands there). So the bridge does
  not apply in the shape needed — the codomain side differs — and the brief's fallback is used:
  the `private` adapter `typeSubmodule_eq_typeSpanOf` below, the same twelve-line proof at an
  arbitrary codomain group. It is an adapter, not a re-derivation: nothing about `G` is used.

  **Spellings** are the pin's, for the reason recorded in `ArchCompactOrbit`'s header: the
  checker diffs statement text, so a name that occurs inside a statement cannot be rectified
  without turning every mentioner into `MISSING`. `ℂK`, `cutc`, `cutM`, `TypeWitness`, `CA`,
  `CB`, `QM`, `Qc`, `underSub` are the pin's tokens.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean:420–1259`
  (pinned `aa2d8b3`; the pin's `PartB4`–`PartTQE` sections) and the headline's statement from
  `Theorems/Thm_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean`,
  minus the pin's `solution`-staging and its `coann`/`isIrreducible_dual` block (imported from
  `BiIsotypic` by the sibling, unused here).

  spec-pin: Theorems/Thm_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_linearMap_archCutProjector_comm_rightTranslate.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchCompactOrbit
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.RepresentationTheory.SubrepresentationExtension
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.CuspidalConstituent AutomorphicForm.ArchCompactOrbit
open scoped Pointwise BigOperators
open scoped AutomorphicForm.ArchCompactOrbit

attribute [-ext] NumberField.InfinitePlace.Completion.ext
attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext

namespace AutomorphicForm.ArchCutProjector

variable (F : Type) [Field F] [NumberField F]

/-- The type-submodule ↔ type-span dictionary at an arbitrary codomain group.

`RightConvComm/SliceCentrality.lean:76` proves this for `e : H →* GL (Fin 2) (InfiniteAdeleRing F)`;
the archimedean cut lives on `AdelicGL2 (𝓞 F) F`, so the published form does not apply here.
Nothing in the proof mentions the codomain. -/
private theorem typeSubmodule_eq_typeSpanOf {H G : Type*} [Group H] [Group G]
    (ι : H →* G) {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W) :
    typeSubmodule ι σ = BiIsotypic.typeSpan (BiIsotypic.rightRep (k := ℂ) ι) σ := by
  unfold typeSubmodule BiIsotypic.typeSpan IsRightEquivariant
  congr 1
  ext f
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨T, hT, hf⟩
    exact ⟨T, fun g u => funext fun x => by rw [BiIsotypic.rightRep_apply]; exact hT g u x, hf⟩
  · rintro ⟨T, hT, hf⟩
    exact ⟨T, fun g u x => by
      rw [← BiIsotypic.rightRep_apply (k := ℂ) ι g (T u) x]; exact congrFun (hT g u) x, hf⟩

/-! ### The type algebra and the isotypic-component split -/

abbrev ℂK : Type := MonoidAlgebra ℂ (ArchIsometryProd F)

/-- The isotypic components falling inside a set of them and those falling outside are
complementary submodules. -/
theorem isCompl_biSup_isotypicComponents (good : Set (isotypicComponents (ℂK F) (ρc F).asModule)) :
    IsCompl (⨆ c ∈ good, (c : Submodule (ℂK F) (ρc F).asModule))
      (⨆ c ∈ goodᶜ, (c : Submodule (ℂK F) (ρc F).asModule)) :=
  letI := isSemisimpleModule_ρc F
  letI : IsModularLattice (Submodule (ℂK F) (ρc F).asModule) :=
    @Submodule.instIsModularLattice (ℂK F) (ρc F).asModule _ inferInstance (ρc F).instModuleMonoidAlgebraAsModule
  letI : IsCompactlyGenerated (Submodule (ℂK F) (ρc F).asModule) :=
    @Submodule.instIsCompactlyGenerated (ℂK F) (ρc F).asModule _ inferInstance (ρc F).instModuleMonoidAlgebraAsModule
  show IsCompl (⨆ c ∈ good, (c : Submodule (ℂK F) (ρc F).asModule))
    (⨆ c ∈ goodᶜ, (c : Submodule (ℂK F) (ρc F).asModule)) from by
  have hind : iSupIndep (Subtype.val : isotypicComponents (ℂK F) (ρc F).asModule → _) :=
    (sSupIndep_iff _).mp (sSupIndep_isotypicComponents (ℂK F) (ρc F).asModule)
  refine ⟨hind.disjoint_biSup_biSup disjoint_compl_right, ?_⟩
  rw [codisjoint_iff, eq_top_iff, ← sSup_isotypicComponents (ℂK F) (ρc F).asModule, sSup_eq_iSup']
  refine iSup_le fun c => ?_
  by_cases hc : c ∈ good
  · exact le_sup_of_le_left (le_biSup _ hc)
  · exact le_sup_of_le_right (le_biSup _ hc)

/-! ### The archimedean orbit span at a single place -/

theorem rightTranslate_mem_of_mem_iSup_range' (Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hZ : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ Z, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ Z)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    ∀ φ ∈ Z, rightTranslate F g φ ∈ Z := by
  refine Subgroup.iSup_induction _ (C := fun g => ∀ φ ∈ Z, rightTranslate F g φ ∈ Z) hg ?_ ?_ ?_
  · rintro w g ⟨k', rfl⟩; exact hZ w k'
  · intro φ hφ
    have : rightTranslate F 1 φ = φ := by funext x; simp [rightTranslate]
    rwa [this]
  · intro a b ha hb φ hφ
    rw [← rightTranslate_rightTranslate]
    exact ha _ (hb _ hφ)

def placeOrbitSpan (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion => rightTranslate F (rowIsometryInclAt₀ F w k) φ)

/-- A vector of an archimedean type has a finite-dimensional orbit span at its place:
`BiIsotypic.finiteDimensional_orbitSpan`, read through the type-submodule ↔ type-span
dictionary at `rowIsometryInclAt₀ F w`. -/
theorem finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archTypeSubmoduleAt F w τ) :
    FiniteDimensional ℂ (placeOrbitSpan F w φ) := by
  have hspan : placeOrbitSpan F w φ
      = BiIsotypic.orbitSpan (V := AdelicGL2 (𝓞 F) F → ℂ)
        (BiIsotypic.rightRep (k := ℂ) (rowIsometryInclAt₀ F w)) φ := by
    simp only [placeOrbitSpan, BiIsotypic.orbitSpan]
    congr 1
    ext ψ
    simp only [Set.mem_range]
    refine ⟨fun ⟨k, hk⟩ => ⟨k, ?_⟩, fun ⟨k, hk⟩ => ⟨k, ?_⟩⟩
    · rw [← hk]; funext y; rw [BiIsotypic.rightRep_apply]; rfl
    · rw [← hk]; funext y; rw [BiIsotypic.rightRep_apply]; rfl
  have htype : φ ∈ BiIsotypic.typeSpan (BiIsotypic.rightRep (k := ℂ) (rowIsometryInclAt₀ F w)) τ.ρ := by
    rw [← typeSubmodule_eq_typeSpanOf]
    exact hφ
  rw [hspan]
  exact BiIsotypic.finiteDimensional_orbitSpan _ τ.ρ htype

theorem finiteDimensional_placeOrbitSpan_of_mem_archCutSubmodule (tys : ArchTypeFamily F) (w : InfinitePlace F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ archCutSubmodule F tys) :
    FiniteDimensional ℂ (placeOrbitSpan F w φ) := by
  rw [mem_archCutSubmodule_iff] at hφ
  refine Submodule.iSup_induction _ (motive := fun φ => FiniteDimensional ℂ (placeOrbitSpan F w φ)) (hφ w)
    (fun i f hf => finiteDimensional_placeOrbitSpan_of_mem_archTypeSubmoduleAt F w _ hf) ?_ ?_
  · have : placeOrbitSpan F w (0 : AdelicGL2 (𝓞 F) F → ℂ) ≤ ⊥ :=
      Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; simp [rightTranslate_zero])
    exact Submodule.finiteDimensional_of_le this
  · intro a b ha hb
    have : placeOrbitSpan F w (a + b) ≤ placeOrbitSpan F w a ⊔ placeOrbitSpan F w b := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      show rightTranslate F _ (a + b) ∈ _
      rw [rightTranslate_add]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
    exact Submodule.finiteDimensional_of_le this

theorem mem_Ecf_of_mem_archCutSubmodule (tys : ArchTypeFamily F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ archCutSubmodule F tys) (hc : Continuous φ) : φ ∈ Ecf F := by
  classical
  refine ⟨hc, ?_⟩

  have key : ∀ s : Finset (InfinitePlace F), ∃ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      FiniteDimensional ℂ Z ∧ φ ∈ Z ∧ Z ≤ archCutSubmodule F tys ∧
      ∀ w ∈ s, ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ z ∈ Z, rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨Submodule.span ℂ {φ}, inferInstance, Submodule.subset_span rfl,
        Submodule.span_le.mpr (by simpa using hφ), by simp⟩
    | @insert w s hw ih =>
      obtain ⟨Z, hZfd, hφZ, hZA, hZst⟩ := ih
      let Z' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
        ⨆ k : rowIsometrySubgroup₀ w.Completion, Z.map (rightRegular F (rowIsometryInclAt₀ F w k))
      have hgen : ∀ (k : rowIsometrySubgroup₀ w.Completion) (z), z ∈ Z →
          rightTranslate F (rowIsometryInclAt₀ F w k) z ∈ Z' := fun k z hz =>
        Submodule.mem_iSup_of_mem k ⟨z, hz, rfl⟩
      refine ⟨Z', ?_, ?_, ?_, ?_⟩
      ·
        let b := Module.finBasis ℂ Z
        have hle : Z' ≤ ⨆ i, placeOrbitSpan F w (b i : AdelicGL2 (𝓞 F) F → ℂ) := by
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
        refine letI : ∀ i, FiniteDimensional ℂ (placeOrbitSpan F w (b i : AdelicGL2 (𝓞 F) F → ℂ)) :=
          fun i => finiteDimensional_placeOrbitSpan_of_mem_archCutSubmodule F tys w (hZA (b i).2); ?_
        exact Submodule.finiteDimensional_of_le hle
      · have := hgen 1 φ hφZ
        rwa [map_one, show rightTranslate F (1 : AdelicGL2 (𝓞 F) F) φ = φ from funext fun x => by simp [rightTranslate]]
          at this
      · refine iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun z hz => ?_
        rw [Submodule.mem_comap]
        exact comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F (hZA hz) w k
      · intro w' hw' k'
        refine fun z hz => Submodule.iSup_induction _
          (motive := fun z => rightTranslate F (rowIsometryInclAt₀ F w' k') z ∈ Z') hz ?_ ?_ ?_
        · rintro k _ ⟨z₀, hz₀, rfl⟩
          show rightTranslate F (rowIsometryInclAt₀ F w' k') (rightTranslate F (rowIsometryInclAt₀ F w k) z₀) ∈ Z'
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
  obtain ⟨Z, hZfd, hφZ, -, hZst⟩ := key Finset.univ
  have hsub : orbitSpan F φ ≤ Z := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    show archRep F k φ ∈ Z
    rw [archRep_apply]
    refine rightTranslate_mem_of_mem_iSup_range' F Z (fun w k z hz => hZst w (Finset.mem_univ w) k z hz) ?_ φ hφZ
    rw [← archProdIncl_range]; exact ⟨k, rfl⟩
  exact Submodule.finiteDimensional_of_le hsub

/-! ### The type-witness set -/

abbrev TypeWitness (w : InfinitePlace F) (tys : ArchTypeFamily F) : Type :=
  Σ i : Fin (tys.card w), {T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) //
    IsRightEquivariant (rowIsometryInclAt₀ F w) (tys.rep w i).ρ T}

theorem exists_finset_typeWitness_of_mem_iSup (w : InfinitePlace F) (tys : ArchTypeFamily F)
    {s : AdelicGL2 (𝓞 F) F → ℂ} (hs : s ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) :
    ∃ J : Finset (TypeWitness F w tys), s ∈ ⨆ j ∈ J, LinearMap.range j.2.1 := by
  classical
  have mono : ∀ (A B : Finset (TypeWitness F w tys)), A ⊆ B →
      (⨆ j ∈ A, LinearMap.range j.2.1) ≤ ⨆ j ∈ B, LinearMap.range j.2.1 := fun A B h =>
    biSup_mono fun j hj => h hj
  refine Submodule.iSup_induction _
    (motive := fun s => ∃ J : Finset (TypeWitness F w tys), s ∈ ⨆ j ∈ J, LinearMap.range j.2.1) hs ?_ ?_ ?_
  · intro i f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro f ⟨T, hT, hfT⟩
      refine ⟨{⟨i, T, hT⟩}, ?_⟩
      simp only [Finset.mem_singleton, iSup_iSup_eq_left]
      exact hfT
    · exact ⟨∅, by simp⟩
    · rintro a b - - ⟨Ja, ha⟩ ⟨Jb, hb⟩
      refine ⟨Ja ∪ Jb, Submodule.add_mem _ ?_ ?_⟩
      · exact mono _ _ Finset.subset_union_left ha
      · exact mono _ _ Finset.subset_union_right hb
    · rintro c a - ⟨J, ha⟩
      exact ⟨J, Submodule.smul_mem _ c ha⟩
  · exact ⟨∅, by simp⟩
  · rintro a b ⟨Ja, ha⟩ ⟨Jb, hb⟩
    refine ⟨Ja ∪ Jb, Submodule.add_mem _ ?_ ?_⟩
    · exact mono _ _ Finset.subset_union_left ha
    · exact mono _ _ Finset.subset_union_right hb

theorem le_iSup_archTypeSubmoduleAt_of_surjective (w : InfinitePlace F) (tys : ArchTypeFamily F)
    (S S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ S]
    (hS' : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ s ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) s ∈ S')
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ s ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) s ∈ S)
    (θ : S →ₗ[ℂ] S') (hθs : Function.Surjective θ)
    (hθ : ∀ (k : rowIsometrySubgroup₀ w.Completion) (s : S),
      (θ ⟨rightTranslate F (rowIsometryInclAt₀ F w k) s, hS k s s.2⟩ : AdelicGL2 (𝓞 F) F → ℂ) =
        rightTranslate F (rowIsometryInclAt₀ F w k) (θ s))
    (hSA : S ≤ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) :
    S' ≤ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) := by
  classical
  -- `hS'` is the pin's hypothesis that `S'` is stable; the argument below only needs the
  -- stability of `S` and the equivariance of `θ`, so record it and keep the signature.
  have _hS' := hS'

  obtain ⟨J, hJ⟩ : ∃ J : Finset (TypeWitness F w tys), S ≤ ⨆ j ∈ J, LinearMap.range j.2.1 := by
    let b := Module.finBasis ℂ S
    choose Jf hJf using fun l => exists_finset_typeWitness_of_mem_iSup F w tys (hSA (b l).2)
    refine ⟨Finset.univ.biUnion Jf, ?_⟩
    have mono : ∀ (A B : Finset (TypeWitness F w tys)), A ⊆ B →
        (⨆ j ∈ A, LinearMap.range j.2.1) ≤ ⨆ j ∈ B, LinearMap.range j.2.1 := fun A B h =>
      biSup_mono fun j hj => h hj
    intro s hs
    have hs' : (⟨s, hs⟩ : S) ∈ Submodule.span ℂ (Set.range b) := by rw [b.span_eq]; trivial
    have hs'' : s ∈ Submodule.span ℂ (Set.range fun l => (b l : AdelicGL2 (𝓞 F) F → ℂ)) := by
      have := Submodule.mem_map_of_mem (f := S.subtype) hs'
      rw [Submodule.map_span, ← Set.range_comp] at this
      exact this
    refine (Submodule.span_le.mpr ?_) hs''
    rintro _ ⟨l, rfl⟩
    exact mono _ _ (Finset.subset_biUnion_of_mem Jf (Finset.mem_univ l)) (hJf l)

  let K := rowIsometrySubgroup₀ w.Completion
  let WJ : Type := ∀ j : J, (Fin (tys.rep w j.1.1).n → ℂ)
  let ρJ : Representation ℂ K WJ :=
    { toFun := fun k => LinearMap.pi fun j => ((tys.rep w j.1.1).ρ k) ∘ₗ LinearMap.proj j
      map_one' := by ext x j; simp
      map_mul' := fun a c => by ext x j; simp }
  have hρJ : ∀ (k : K) (x : WJ) (j : J), ρJ k x j = (tys.rep w j.1.1).ρ k (x j) := fun k x j => rfl
  let TJ : WJ →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := ∑ j : J, (j.1.2.1) ∘ₗ LinearMap.proj j
  have hTJ_apply : ∀ x : WJ, TJ x = ∑ j : J, j.1.2.1 (x j) := fun x => by
    simp only [TJ, LinearMap.sum_apply, LinearMap.comp_apply]
    rfl
  have hTJ : ∀ (k : K) (x : WJ) (y : AdelicGL2 (𝓞 F) F),
      TJ (ρJ k x) y = TJ x (y * rowIsometryInclAt₀ F w k) := by
    intro k x y
    simp only [hTJ_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hρJ]; exact j.1.2.2 k (x j) y

  have hSrange : S ≤ LinearMap.range TJ := by
    refine hJ.trans (iSup₂_le fun j hj => ?_)
    rintro _ ⟨v, rfl⟩
    refine ⟨Pi.single ⟨j, hj⟩ v, ?_⟩
    rw [hTJ_apply, Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro j' _ hj'; simp [Pi.single_eq_of_ne hj']
    · simp

  let P : Submodule ℂ WJ := S.comap TJ
  have hP : ∀ k : K, ∀ x ∈ P, ρJ k x ∈ P := by
    intro k x hx
    show TJ (ρJ k x) ∈ S
    have : TJ (ρJ k x) = rightTranslate F (rowIsometryInclAt₀ F w k) (TJ x) := funext fun y => hTJ k x y
    rw [this]; exact hS k _ hx
  let toS : P →ₗ[ℂ] S := LinearMap.codRestrict S (TJ ∘ₗ P.subtype) fun x => x.2
  let f : P →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := S'.subtype ∘ₗ θ ∘ₗ toS
  have hf : ∀ (k : K) (x : P) (y : AdelicGL2 (𝓞 F) F), f ⟨ρJ k x, hP k x x.2⟩ y = f x (y * rowIsometryInclAt₀ F w k) := by
    intro k x y
    have h1 : toS ⟨ρJ k x, hP k x x.2⟩ = ⟨rightTranslate F (rowIsometryInclAt₀ F w k) (toS x : _), hS k _ (toS x).2⟩ := by
      apply Subtype.ext
      funext y'
      exact hTJ k x y'
    show (θ (toS ⟨ρJ k x, hP k x x.2⟩) : AdelicGL2 (𝓞 F) F → ℂ) y = (θ (toS x) : AdelicGL2 (𝓞 F) F → ℂ) (y * _)
    rw [h1, hθ k (toS x)]
    rfl
  have hinj : Function.Injective (rowIsometryInclAt₀ F w) := by
    intro a c hac
    apply Subtype.ext
    apply Units.ext
    ext i j' : 1
    have := congrArg (fun g : AdelicGL2 (𝓞 F) F => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j').1 w) hac
    simp only [rowIsometryInclAt₀_apply, val_adelicArchGLInclAt_apply, archMatrixUpdate_apply_self] at this
    exact this
  obtain ⟨T', hT'eq, hT'ext⟩ :=
    Representation.exists_extend_forall_apply_mul_of_injective (rowIsometryInclAt₀ F w) hinj ρJ P hP f hf

  intro s' hs'
  obtain ⟨s, hθs'⟩ := hθs ⟨s', hs'⟩
  rw [show s' = ((θ s : S') : AdelicGL2 (𝓞 F) F → ℂ) from (congrArg Subtype.val hθs').symm]
  obtain ⟨x, hx⟩ : ∃ x : WJ, TJ x = s := hSrange s.2
  have hxP : x ∈ P := by show TJ x ∈ S; rw [hx]; exact s.2
  have hs_eq : (θ s : AdelicGL2 (𝓞 F) F → ℂ) = T' x := by
    rw [hT'ext ⟨x, hxP⟩]
    show _ = (θ (toS ⟨x, hxP⟩) : AdelicGL2 (𝓞 F) F → ℂ)
    congr 2
    apply Subtype.ext; exact hx.symm
  show (θ s : AdelicGL2 (𝓞 F) F → ℂ) ∈ _
  rw [hs_eq, show x = ∑ j : J, Pi.single j (x j) from (Finset.univ_sum_single x).symm, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  refine Submodule.mem_iSup_of_mem j.1.1 ?_

  refine mem_typeSubmodule_of_isRightEquivariant (T := T' ∘ₗ LinearMap.single ℂ (fun j : J => Fin (tys.rep w j.1.1).n → ℂ) j) ?_ (x j)
  intro k v y
  show T' (Pi.single j ((tys.rep w j.1.1).ρ k v)) y = T' (Pi.single j v) (y * _)
  rw [← hT'eq k]
  have hsingle : (Pi.single j ((tys.rep w j.1.1).ρ k v) : WJ) = ρJ k (Pi.single j v) := by
    funext j'
    rw [hρJ]
    by_cases hjj : j' = j
    · subst hjj; simp
    · simp [Pi.single_eq_of_ne hjj]
  rw [hsingle]

/-! ### The archimedean cut inside the carrier -/

def cutc (tys : ArchTypeFamily F) : Submodule ℂ (Ecf F) := (archCutSubmodule F tys).comap (Ecf F).subtype

theorem mem_cutc {tys : ArchTypeFamily F} {φ : Ecf F} :
    φ ∈ cutc F tys ↔ (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys := Iff.rfl

theorem archProdIncl_mem_iSup (k : ArchIsometryProd F) :
    archProdIncl F k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range := by
  rw [← archProdIncl_range]; exact ⟨k, rfl⟩

theorem cutc_mem_invtSubmodule (tys : ArchTypeFamily F) : cutc F tys ∈ (ρc F).invtSubmodule := by
  rw [Representation.mem_invtSubmodule]
  intro k φ hφ
  show ((ρc F k φ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys
  rw [ρc_apply_coe, archRep_apply]
  exact rightTranslate_mem_of_mem_iSup_range' F (archCutSubmodule F tys)
    (fun w k φ hφ => comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F hφ w k) (archProdIncl_mem_iSup F k) _ hφ

def cutM (tys : ArchTypeFamily F) : Submodule (ℂK F) (ρc F).asModule :=
  (ρc F).mapSubmodule ⟨cutc F tys, cutc_mem_invtSubmodule F tys⟩

def goodComponents (tys : ArchTypeFamily F) : Set (isotypicComponents (ℂK F) (ρc F).asModule) :=
  {c | (c : Submodule (ℂK F) (ρc F).asModule) ≤ cutM F tys}

def CA (tys : ArchTypeFamily F) : Submodule (ℂK F) (ρc F).asModule :=
  ⨆ c ∈ goodComponents F tys, (c : Submodule (ℂK F) (ρc F).asModule)

def CB (tys : ArchTypeFamily F) : Submodule (ℂK F) (ρc F).asModule :=
  ⨆ c ∈ (goodComponents F tys)ᶜ, (c : Submodule (ℂK F) (ρc F).asModule)

theorem isCompl_CA_CB (tys : ArchTypeFamily F) : IsCompl (CA F tys) (CB F tys) :=
  isCompl_biSup_isotypicComponents F (goodComponents F tys)

theorem CA_le_cutM (tys : ArchTypeFamily F) : CA F tys ≤ cutM F tys :=
  iSup₂_le fun _ hc => hc

def projCA (tys : ArchTypeFamily F) : (ρc F).asModule →ₗ[ℂK F] CA F tys :=
  @Submodule.projectionOnto (ℂK F) _ (ρc F).asModule inferInstance (ρc F).instModuleMonoidAlgebraAsModule
    (CA F tys) (CB F tys) (isCompl_CA_CB F tys)

theorem projCA_apply_left (tys : ArchTypeFamily F) (x : CA F tys) : projCA F tys x = x :=
  @Submodule.projectionOnto_apply_left (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule (CA F tys) (CB F tys) (isCompl_CA_CB F tys) x

theorem projCA_apply_right (tys : ArchTypeFamily F) (x : CB F tys) : projCA F tys x = 0 :=
  @Submodule.projectionOnto_apply_right (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule (CA F tys) (CB F tys) (isCompl_CA_CB F tys) x

def QM (tys : ArchTypeFamily F) : (ρc F).asModule →ₗ[ℂK F] (ρc F).asModule :=
  (CA F tys).subtype.comp (projCA F tys)

theorem QM_apply_of_mem_CA (tys : ArchTypeFamily F) {m : (ρc F).asModule} (hm : m ∈ CA F tys) : QM F tys m = m := by
  show ((projCA F tys m : CA F tys) : (ρc F).asModule) = m
  rw [projCA_apply_left F tys ⟨m, hm⟩]

theorem QM_apply_of_mem_CB (tys : ArchTypeFamily F) {m : (ρc F).asModule} (hm : m ∈ CB F tys) : QM F tys m = 0 := by
  show ((projCA F tys m : CA F tys) : (ρc F).asModule) = 0
  rw [projCA_apply_right F tys ⟨m, hm⟩]; rfl

theorem QM_mem_CA (tys : ArchTypeFamily F) (m : (ρc F).asModule) : QM F tys m ∈ CA F tys :=
  Submodule.coe_mem (projCA F tys m)

def Qc (tys : ArchTypeFamily F) : Ecf F →ₗ[ℂ] Ecf F :=
  (ρc F).asModuleEquiv.toLinearMap ∘ₗ (QM F tys).restrictScalars ℂ ∘ₗ (ρc F).asModuleEquiv.symm.toLinearMap

theorem Qc_apply (tys : ArchTypeFamily F) (φ : Ecf F) :
    Qc F tys φ = (ρc F).asModuleEquiv (QM F tys ((ρc F).asModuleEquiv.symm φ)) := rfl

theorem Qc_ρc (tys : ArchTypeFamily F) (k : ArchIsometryProd F) (φ : Ecf F) :
    Qc F tys (ρc F k φ) = ρc F k (Qc F tys φ) := by
  rw [Qc_apply, Qc_apply, Representation.asModuleEquiv_symm_map_rho, map_smul,
    Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

/-! ### The generic isotypic-component lemmas mathlib does not state -/

theorem le_biSup_isotypicComponents_of_forall_linearEquiv_le
    {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
    (A : Submodule R M)
    (hA : ∀ (m m' : Submodule R M), IsSimpleModule R m → Nonempty (m ≃ₗ[R] m') → m ≤ A → m' ≤ A) :
    A ≤ ⨆ c ∈ {c : isotypicComponents R M | (c : Submodule R M) ≤ A}, (c : Submodule R M) := by
  conv_lhs => rw [← IsSemisimpleModule.sSup_simples_le (R := R) (M := M) A]
  refine sSup_le fun T ⟨hT, hTA⟩ => ?_
  refine letI := hT; ?_
  have hcA : isotypicComponent R M T ≤ A := sSup_le fun m ⟨e⟩ => hA T m hT ⟨e.symm⟩ hTA
  have hc : isotypicComponent R M T ∈ isotypicComponents R M := ⟨T, hT, rfl⟩
  exact T.le_isotypicComponent.trans
    (le_biSup (fun c : isotypicComponents R M => (c : Submodule R M)) (i := ⟨_, hc⟩) hcA)

open scoped MonoidAlgebra

section MonoidAlgebraVariables

variable {k : Type*} [Field k] {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module k V]

private def restrictEquiv (ρ : Representation k G V) (N : Submodule (MonoidAlgebra k G) ρ.asModule) :
    ↥(N.restrictScalars k) ≃ₗ[k] ↥N where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem exists_linearEquiv_map_asModuleEquiv_of_linearEquiv
    (ρ : Representation k G V) (N N' : Submodule (MonoidAlgebra k G) ρ.asModule)
    (e : N ≃ₗ[MonoidAlgebra k G] N') :
    ∃ (hS : ∀ (g : G), ∀ v ∈ (N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap,
          ρ g v ∈ (N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap)
      (θ : ((N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) ≃ₗ[k]
          ((N'.restrictScalars k).map ρ.asModuleEquiv.toLinearMap)),
      ∀ (g : G) (s : (N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap),
        ((θ ⟨ρ g s, hS g s s.2⟩ : (N'.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) : V) = ρ g (θ s : V) := by

  have hstab : ∀ (M : Submodule (MonoidAlgebra k G) ρ.asModule) (g : G),
      ∀ v ∈ (M.restrictScalars k).map ρ.asModuleEquiv.toLinearMap, ρ g v ∈ (M.restrictScalars k).map ρ.asModuleEquiv.toLinearMap := by
    intro M g v hv
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
    refine Submodule.mem_map.mpr ⟨MonoidAlgebra.of k G g • x, M.smul_mem _ hx, ?_⟩
    change ρ.asModuleEquiv (MonoidAlgebra.of k G g • x) = ρ g (ρ.asModuleEquiv x)
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

  let θ : ((N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) ≃ₗ[k] ((N'.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) :=
    (ρ.asModuleEquiv.submoduleMap (N.restrictScalars k)).symm
      ≪≫ₗ restrictEquiv ρ N ≪≫ₗ e.restrictScalars k ≪≫ₗ (restrictEquiv ρ N').symm
      ≪≫ₗ ρ.asModuleEquiv.submoduleMap (N'.restrictScalars k)
  have hθ : ∀ s : (N.restrictScalars k).map ρ.asModuleEquiv.toLinearMap,
      ((θ s : (N'.restrictScalars k).map ρ.asModuleEquiv.toLinearMap) : V) =
        ρ.asModuleEquiv ((e ⟨ρ.asModuleEquiv.symm (s : V),
          by obtain ⟨x, hx, hxs⟩ := Submodule.mem_map.mp s.2; rw [← hxs]; simpa using hx⟩ : N') : ρ.asModule) := by
    intro s
    rfl
  refine ⟨hstab N, θ, fun g s => ?_⟩
  rw [hθ, hθ]

  have h1 : (⟨ρ.asModuleEquiv.symm (ρ g (s : V)), by
        obtain ⟨x, hx, hxs⟩ := Submodule.mem_map.mp (hstab N g s s.2); rw [← hxs]; simpa using hx⟩ : N) =
      MonoidAlgebra.of k G g • ⟨ρ.asModuleEquiv.symm (s : V), by
        obtain ⟨x, hx, hxs⟩ := Submodule.mem_map.mp s.2; rw [← hxs]; simpa using hx⟩ := by
    apply Subtype.ext
    change ρ.asModuleEquiv.symm (ρ g (s : V)) = MonoidAlgebra.of k G g • ρ.asModuleEquiv.symm (s : V)
    exact Representation.asModuleEquiv_symm_map_rho ρ g (s : V)
  rw [h1, map_smul, Submodule.coe_smul, Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

end MonoidAlgebraVariables

theorem exists_add_eq_of_isCompl_biSup_isotypicComponents {R : Type*} [Ring R] {M : Type*} [AddCommGroup M]
    [Module R M] [IsSemisimpleModule R M] (good : Set (isotypicComponents R M))
    (hc : IsCompl (⨆ c ∈ good, (c : Submodule R M)) (⨆ c ∈ goodᶜ, (c : Submodule R M)))
    (N : Submodule R M) (x : M) (hx : x ∈ N) :
    ∃ a ∈ N ⊓ ⨆ c ∈ good, (c : Submodule R M), ∃ b ∈ N ⊓ ⨆ c ∈ goodᶜ, (c : Submodule R M), x = a + b := by
  -- the complementarity is the pin's hypothesis; the split is built from `sSup_simples_le` below
  have _hc := hc

  have hN : N ≤ (N ⊓ ⨆ c ∈ good, (c : Submodule R M)) ⊔ (N ⊓ ⨆ c ∈ goodᶜ, (c : Submodule R M)) := by
    conv_lhs => rw [← IsSemisimpleModule.sSup_simples_le N]
    refine sSup_le ?_
    rintro T ⟨hT, hTN⟩
    let cT : isotypicComponents R M := ⟨isotypicComponent R M T, ⟨T, hT, rfl⟩⟩
    have hTc : T ≤ (cT : Submodule R M) := T.le_isotypicComponent
    by_cases hg : cT ∈ good
    · refine le_sup_of_le_left (le_inf hTN (hTc.trans ?_))
      exact le_biSup (fun c : isotypicComponents R M => (c : Submodule R M)) hg
    · refine le_sup_of_le_right (le_inf hTN (hTc.trans ?_))
      exact le_biSup (fun c : isotypicComponents R M => (c : Submodule R M)) (Set.mem_compl hg)
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hN hx)
  exact ⟨a, ha, b, hb, hab.symm⟩

theorem exists_eq_span_singleton_of_isSimpleModule {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
    (T : Submodule R M) [IsSimpleModule R T] : ∃ t : M, t ∈ T ∧ T = R ∙ t := by
  have hne : T ≠ ⊥ := by
    intro h
    have := IsSimpleModule.nontrivial R T
    rw [Submodule.nontrivial_iff_ne_bot] at this
    exact this h
  obtain ⟨t, htT, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨t, htT, ?_⟩
  have hatom : IsAtom T := isSimpleModule_iff_isAtom.mp inferInstance
  have hle : R ∙ t ≤ T := (Submodule.span_singleton_le_iff_mem t T).mpr htT
  rcases hatom.le_iff.mp hle with h | h
  · exact absurd (Submodule.span_singleton_eq_bot.mp h) ht0
  · exact h.symm

/-! ### The projector on the cut, and its transport to the carrier -/

theorem mem_mapSubmodule_iff {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
    (ρ : Representation k G V) (p : ρ.invtSubmodule) (x : ρ.asModule) :
    x ∈ ρ.mapSubmodule p ↔ ρ.asModuleEquiv x ∈ (p : Submodule k V) := by
  change x ∈ ((p : Submodule k V).toAddSubmonoid.map (ρ.asModuleEquiv.symm : V →+ ρ.asModule)) ↔ _
  rw [AddSubmonoid.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩; simpa using hv
  · intro h; exact ⟨ρ.asModuleEquiv x, h, by simp⟩

open scoped Classical in
theorem archProdIncl_mulSingle (w : InfinitePlace F) (kw : rowIsometrySubgroup₀ w.Completion) :
    archProdIncl F (Pi.mulSingle w kw) = rowIsometryInclAt₀ F w kw := by
  classical
  unfold archProdIncl
  exact MonoidHom.noncommPiCoprod_mulSingle (fun v => rowIsometryInclAt₀ F v) w kw

theorem mem_cutM_iff (tys : ArchTypeFamily F) (x : (ρc F).asModule) :
    x ∈ cutM F tys ↔ (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys :=
  mem_mapSubmodule_iff (ρc F) _ x

abbrev underSub (N : Submodule (ℂK F) (ρc F).asModule) : Submodule ℂ (Ecf F) :=
  (N.restrictScalars ℂ).map (ρc F).asModuleEquiv.toLinearMap

theorem mem_underSub_iff (N : Submodule (ℂK F) (ρc F).asModule) (v : Ecf F) :
    v ∈ underSub F N ↔ (ρc F).asModuleEquiv.symm v ∈ N := by
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨(ρc F).asModuleEquiv.symm v, h, by simp⟩

theorem finiteDimensional_underSub_of_eq_span (N : Submodule (ℂK F) (ρc F).asModule) (t : (ρc F).asModule)
    (hNt : N = Submodule.span (ℂK F) {t}) :
    FiniteDimensional ℂ (underSub F N) := by

  let t' : Ecf F := (ρc F).asModuleEquiv t
  have hle : N ≤ (ρc F).mapSubmodule ⟨orbitSpanc F t', orbitSpanc_mem_invtSubmodule F t'⟩ := by
    rw [hNt]
    refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    rw [mem_mapSubmodule_iff]
    exact mem_orbitSpanc_self F t'
  have : underSub F N ≤ orbitSpanc F t' := by
    intro v hv
    rw [mem_underSub_iff] at hv
    have := hle hv
    rw [mem_mapSubmodule_iff] at this
    simpa using this
  exact Submodule.finiteDimensional_of_le this

theorem cutM_le_CA (tys : ArchTypeFamily F) : cutM F tys ≤ CA F tys := by
  classical
  refine letI := isSemisimpleModule_ρc F; ?_
  refine @le_biSup_isotypicComponents_of_forall_linearEquiv_le (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule inferInstance (cutM F tys) ?_
  intro m m' hm hmm' hmA
  obtain ⟨e⟩ := hmm'
  obtain ⟨hS, θ, hθ⟩ := exists_linearEquiv_map_asModuleEquiv_of_linearEquiv (ρc F) m m' e
  obtain ⟨t, -, hmt⟩ := @exists_eq_span_singleton_of_isSimpleModule (ℂK F) _ (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule m hm
  have hfdm : FiniteDimensional ℂ (underSub F m) := finiteDimensional_underSub_of_eq_span F m t hmt

  let ι₀ := (Ecf F).subtype
  let Sf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F m).map ι₀
  let Sf' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F m').map ι₀
  have hS' := (exists_linearEquiv_map_asModuleEquiv_of_linearEquiv (ρc F) m' m' (LinearEquiv.refl _ _)).1
  let eS : underSub F m ≃ₗ[ℂ] Sf := Submodule.equivMapOfInjective ι₀ Subtype.val_injective _
  let eS' : underSub F m' ≃ₗ[ℂ] Sf' := Submodule.equivMapOfInjective ι₀ Subtype.val_injective _
  refine letI : FiniteDimensional ℂ Sf := Module.Finite.map (underSub F m) ι₀; ?_
  let θf : Sf →ₗ[ℂ] Sf' := eS'.toLinearMap ∘ₗ θ.toLinearMap ∘ₗ eS.symm.toLinearMap
  have hθf_surj : Function.Surjective θf := by
    intro y
    refine ⟨eS (θ.symm (eS'.symm y)), ?_⟩
    simp [θf]
  have heS : ∀ (v : underSub F m), ((eS v : Sf) : AdelicGL2 (𝓞 F) F → ℂ) = (v : Ecf F) := fun v => rfl
  have heS' : ∀ (v : underSub F m'), ((eS' v : Sf') : AdelicGL2 (𝓞 F) F → ℂ) = (v : Ecf F) := fun v => rfl
  have heSsymm : ∀ (s : Sf), (((eS.symm s : underSub F m) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := fun s => by
    rw [← heS (eS.symm s), eS.apply_symm_apply]

  have hact : ∀ (w : InfinitePlace F) (kw : rowIsometrySubgroup₀ w.Completion) (v : Ecf F),
      ((ρc F (Pi.mulSingle w kw) v : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = rightTranslate F (rowIsometryInclAt₀ F w kw) v := by
    intro w kw v
    rw [ρc_apply_coe, archRep_apply, archProdIncl_mulSingle]

  have hstab : ∀ (N : Submodule (ℂK F) (ρc F).asModule)
      (hN : ∀ (g : ArchIsometryProd F), ∀ v ∈ underSub F N, ρc F g v ∈ underSub F N)
      (w : InfinitePlace F) (kw : rowIsometrySubgroup₀ w.Completion),
      ∀ s ∈ (underSub F N).map ι₀, rightTranslate F (rowIsometryInclAt₀ F w kw) s ∈ (underSub F N).map ι₀ := by
    intro N hN w kw s hs
    obtain ⟨v, hv, rfl⟩ := hs
    refine ⟨ρc F (Pi.mulSingle w kw) v, hN _ v hv, ?_⟩
    exact hact w kw v

  intro x hx
  rw [mem_cutM_iff, mem_archCutSubmodule_iff]
  intro w
  have hxSf' : (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ Sf' :=
    ⟨(ρc F).asModuleEquiv x, (mem_underSub_iff F m' _).mpr (by simpa using hx), rfl⟩
  refine le_iSup_archTypeSubmoduleAt_of_surjective F w tys Sf Sf' (hstab m' hS' w) (hstab m hS w) θf hθf_surj ?_ ?_ hxSf'
  ·
    intro kw s
    have h1 : eS.symm ⟨rightTranslate F (rowIsometryInclAt₀ F w kw) s, hstab m hS w kw s s.2⟩ =
        ⟨ρc F (Pi.mulSingle w kw) (eS.symm s : underSub F m), hS _ _ (eS.symm s).2⟩ := by
      apply eS.injective
      rw [eS.apply_symm_apply]
      apply Subtype.ext
      rw [heS, hact, heSsymm]
    show ((eS' (θ (eS.symm ⟨_, _⟩)) : Sf') : AdelicGL2 (𝓞 F) F → ℂ) = rightTranslate F _ ((eS' (θ (eS.symm s)) : Sf') : _)
    rw [h1, heS', heS', hθ (Pi.mulSingle w kw) (eS.symm s), hact]
  ·
    rintro _ ⟨v, hv, rfl⟩
    replace hv := (mem_underSub_iff F m v).mp hv
    have := hmA hv
    rw [mem_cutM_iff, mem_archCutSubmodule_iff] at this
    have h__af := this w
    simp at h__af
    exact h__af

theorem Qc_eq_self_of_mem_cutc (tys : ArchTypeFamily F) {φ : Ecf F} (hφ : φ ∈ cutc F tys) : Qc F tys φ = φ := by
  rw [Qc_apply]
  have hx : (ρc F).asModuleEquiv.symm φ ∈ cutM F tys := by
    rw [mem_cutM_iff]; (simp at hφ ⊢; exact hφ)
  rw [QM_apply_of_mem_CA F tys (cutM_le_CA F tys hx)]
  simp

theorem Qc_mem_orbitSpanc (tys : ArchTypeFamily F) (φ : Ecf F) : Qc F tys φ ∈ orbitSpanc F φ := by
  classical
  refine letI := isSemisimpleModule_ρc F; ?_
  let N : Submodule (ℂK F) (ρc F).asModule := (ρc F).mapSubmodule ⟨orbitSpanc F φ, orbitSpanc_mem_invtSubmodule F φ⟩
  have hxN : (ρc F).asModuleEquiv.symm φ ∈ N := by
    rw [mem_mapSubmodule_iff]; simpa using mem_orbitSpanc_self F φ
  obtain ⟨a, ha, b, hb, hab⟩ := exists_add_eq_of_isCompl_biSup_isotypicComponents (goodComponents F tys)
    (isCompl_CA_CB F tys) N _ hxN
  rw [Qc_apply, hab, map_add, QM_apply_of_mem_CA F tys ha.2, QM_apply_of_mem_CB F tys hb.2, add_zero]
  exact (mem_mapSubmodule_iff (ρc F) _ a).mp ha.1

/-! ### The headline -/

theorem range_archRep_eq (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    Set.range (fun k : ArchIsometryProd F => archRep F k φ) =
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k φ} := by
  ext ψ
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨archProdIncl F k, archProdIncl_mem_iSup F k, archRep_apply F k φ⟩
  · rintro ⟨k, hk, rfl⟩
    rw [← archProdIncl_range] at hk
    obtain ⟨k', rfl⟩ := hk
    exact ⟨k', archRep_apply F k' φ⟩

theorem orbitSpan_eq_span (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    orbitSpan F φ = Submodule.span ℂ
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k φ} := by
  rw [orbitSpan, range_archRep_eq]

theorem mem_Ecf_of_finiteDimensional_span {φ : AdelicGL2 (𝓞 F) F → ℂ} (hc : Continuous φ)
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k φ})) : φ ∈ Ecf F := by
  refine ⟨hc, ?_⟩
  rw [orbitSpan_eq_span]
  exact hfd

theorem exists_archCutProjector (tys : ArchTypeFamily F) :
    ∃ Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
            ψ = rightTranslate F k φ}) →
        Q φ ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
            ψ = rightTranslate F k φ}) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
            ψ = rightTranslate F k φ}) →
        ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          Q (rightTranslate F k φ) = rightTranslate F k (Q φ)) := by
  classical
  obtain ⟨Q, hQ⟩ := LinearMap.exists_extend ((Ecf F).subtype ∘ₗ Qc F tys)
  have hQ' : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ Ecf F), Q φ = Qc F tys ⟨φ, hφ⟩ :=
    fun φ hφ => LinearMap.congr_fun hQ ⟨φ, hφ⟩
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro φ hc hA
    have hE : φ ∈ Ecf F := mem_Ecf_of_mem_archCutSubmodule F tys hA hc
    rw [hQ' φ hE, Qc_eq_self_of_mem_cutc F tys (show (⟨φ, hE⟩ : Ecf F) ∈ cutc F tys from hA)]
  · intro φ hc hfd
    have hE : φ ∈ Ecf F := mem_Ecf_of_finiteDimensional_span F hc hfd
    rw [hQ' φ hE]
    refine ⟨?_, ?_⟩
    · have h1 : QM F tys ((ρc F).asModuleEquiv.symm ⟨φ, hE⟩) ∈ cutM F tys :=
        CA_le_cutM F tys (QM_mem_CA F tys _)
      rw [mem_cutM_iff] at h1
      rw [Qc_apply]
      exact h1
    · have h2 := Qc_mem_orbitSpanc F tys ⟨φ, hE⟩
      have h3 : ((Qc F tys ⟨φ, hE⟩ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ (orbitSpanc F ⟨φ, hE⟩).map (Ecf F).subtype :=
        Submodule.mem_map_of_mem h2
      rw [map_orbitSpanc] at h3
      change _ ∈ orbitSpan F φ at h3
      rwa [orbitSpan_eq_span] at h3
  · intro φ hc hfd k hk
    have hE : φ ∈ Ecf F := mem_Ecf_of_finiteDimensional_span F hc hfd
    rw [← archProdIncl_range] at hk
    obtain ⟨k', rfl⟩ := hk
    have hE' : rightTranslate F (archProdIncl F k') φ ∈ Ecf F := archRep_mem_Ecf F k' hE
    rw [hQ' _ hE', hQ' φ hE]
    have hρ : (ρc F k' ⟨φ, hE⟩ : Ecf F) = ⟨rightTranslate F (archProdIncl F k') φ, hE'⟩ := Subtype.ext rfl
    rw [← hρ, Qc_ρc F tys k' ⟨φ, hE⟩, ρc_apply_coe, archRep_apply]

end AutomorphicForm.ArchCutProjector

open AutomorphicForm.ArchCutProjector in
theorem AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F) :
    ∃ Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        Q φ ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          Q (rightTranslate F k φ) = rightTranslate F k (Q φ)) :=
  exists_archCutProjector F tys
