/-
  The irreducibility spine of the cuspidal constituent.

  Four rows of the cuspidal `K`-finite subrepresentation, all of them of the form "the invariants of a
  cusp subrepresentation are already inside finitely many irreducible archimedean types":

  * `CuspidalConstituent.exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep`: for a compact
    open `U` of the finite level, `V ⊓ invariants U ⊓ archCut tys` lies in a finite supremum of
    `V ⊓ invariants U ⊓ archCut` of families whose every archimedean rep is irreducible.
  * `CuspidalConstituent.exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep`: the same
    with the level-`N`-invariant submodule in place of `U`'s invariants.
  * `CuspidalSpectrum.isClosedCuspSubrep_orthogonal`: the orthogonal complement of a closed cusp
    subrepresentation is again a closed cusp subrepresentation (the `L²` orthogonality that makes the
    decomposition available at all).
  * `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep`: the
    image of a cusp subrepresentation under the map to the cusp subcarrier, closed up, is a closed cusp
    subrepresentation.

  The two constituent rows are single-headline files: each pin carries its row as a `solution` and 15
  `private` engine declarations behind it. Those 30 private declarations are ported here as 15 private
  declarations of `CuspidalConstituent.ArchSplit` — the pins' own 14-declaration engine is *the same
  text* in both files and is written once (the two pins differ only in their last helper, whose two
  forms are the two declarations `rightTranslate_rowIsometryInclAt₀_mem_inf_invariants` and
  `…_mem_inf_levelInvariantSubmodule`).

  The two `CuspidalSpectrum` rows are flattened files whose engine declarations are all public (10 + 2
  of them besides the row itself), in the pins' own in-file namespaces, which the port renames to
  subject namespaces `CuspidalSpectrum.Orthogonal` and `CuspidalSpectrum.Closure`.

  `CuspidalSpectrum.Orthogonal` is general Hilbert-space mathematics over `{E} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]` (the pin's `Ws48Perp` block, `map_orthogonal_le_orthogonal`,
  `inner_apply_eq_of_dense`, `compress`, …), kept at the pin's generality and with the pin's
  `@[scoped simp]` on `compress_apply_coe`; the rest of that block works on the cusp subcarrier and
  follows the right-translation / right-convolution adjoint pairs.

  Transcribed from the four `S_` files below (pinned `aa2d8b3`, 320 + 317 + 234 + 75 lines), the pins'
  label namespaces dropped (`Ws48Perp` -> `Orthogonal`, `ClosureSubrep` -> `Closure`,
  `S12Reduce` -> `ArchSplit`) — no tokens in names.

  Deviations, all statement-preserving and recorded here:

  * The two constituent pins' private `eq_of_glArch_eq_of_glFin_eq'` (`:235` in each) is **not**
    restated: the port has the same fact publicly at the pin's own name,
    `AutomorphicForm.eq_of_glArch_eq_of_glFin_eq` (`AutomorphicForm/Adelic/LevelCompactness.lean`).
  * The rows' hypothesis binders `hU`/`hO` (compactness/openness of the level subgroups) are part of
    the frozen statement and are not consumed by the proof (`hUO` is what carries the level). They are
    named by `have _ := hU` / `have _ := hO` rather than renamed, which the checker would report.
  * `inf_archCutSubmodule_eq_bot_of_eq_zero` writes the empty-index instance as `have : IsEmpty …`
    (the pin's `haveI`), the `linter.style.haveILetI` suggestion (FR-0223).
  * The pins' `attribute [-instance]`/`[-simp]` walls are dropped, as the port's practice; the module
    elaborates silent without them.

  Heartbeat probe (gate 6, a measurement — the module carries **no** `set_option maxHeartbeats`):
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` is silent at the edit-loop cap 200000 and at
  **N = 18500**, and fails at **N = 9250** (= 18500/2, 7 errors, at `map_orthogonal_le_of_rightTranslate`,
  `map_orthogonal_le_of_rightConv`, `map_closure_le` and the four rows) and at 12000. The floor is
  per-declaration and sits just under 18500.

  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrier
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumSubrep
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumTranslation
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumConvAction
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumLift
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArchTypeSubmodule
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelSphericalTestFn
import FLTForHuman.AutomorphicForm.Adelic.IsotypicArchType
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSet
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.NumberTheory.AdelicBox
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Invariants

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped Classical InnerProductSpace ENNReal ComplexConjugate

namespace AutomorphicForm

namespace CuspidalConstituent

/-! The archimedean splitting engine: a cusp subrepresentation's invariants meet only finitely many
irreducible archimedean types. `mixedCut` pins one type at each place of a finite set `P` and keeps a
full cut elsewhere; `otherCut` does the same with one place `w` deleted. The induction on `P` replaces
one place at a time (`split_one_place`), and the empty case (`inf_archCutSubmodule_eq_bot_of_eq_zero`)
is what allows a family with a zero-length place in the conclusion. -/

namespace ArchSplit

variable (F : Type) [Field F] [NumberField F]

private theorem continuous_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hcont, -⟩
    exact hcont
  · exact continuous_const
  · intro u w _ _ hu hw
    exact hu.add hw
  · intro c u _ hu
    exact hu.const_smul c

private noncomputable def mixedCut (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w) (P : Finset (InfinitePlace F))
    (J : (w : InfinitePlace F) → Fin (r w)) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  (⨅ (w : InfinitePlace F) (_ : w ∈ P), archTypeSubmoduleAt F w (σs w (J w))) ⊓
    ⨅ (w : InfinitePlace F) (_ : w ∉ P), ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)

private theorem archCutSubmodule_le_mixedCut_empty (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w) (J : (w : InfinitePlace F) → Fin (r w)) :
    archCutSubmodule F tys ≤ mixedCut F tys r σs ∅ J := by
  intro f hf
  rw [mem_archCutSubmodule_iff] at hf
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Submodule.mem_iInf _).mpr fun w => (Submodule.mem_iInf _).mpr fun h => absurd h (Finset.notMem_empty w)
  · exact (Submodule.mem_iInf _).mpr fun w => (Submodule.mem_iInf _).mpr fun _ => hf w

private theorem mixedCut_univ_le_archCutSubmodule (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w) (J : (w : InfinitePlace F) → Fin (r w)) :
    mixedCut F tys r σs Finset.univ J ≤
      archCutSubmodule F (⟨fun _ => 1, fun w _ => σs w (J w)⟩ : AutomorphicForm.ArchTypeFamily F) := by
  intro f hf
  rw [mem_archCutSubmodule_iff]
  intro w
  have h1 : f ∈ archTypeSubmoduleAt F w (σs w (J w)) :=
    (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hf).1 w) (Finset.mem_univ w)
  exact Submodule.mem_iSup_of_mem (0 : Fin 1) h1

private theorem rightTranslate_mem_archTypeSubmoduleAt_of_ne {v w : InfinitePlace F} (hvw : v ≠ w) (τ : ArchRepAt F v)
    (k : rowIsometrySubgroup₀ w.Completion) {g : AdelicGL2 (𝓞 F) F → ℂ} (hg : g ∈ archTypeSubmoduleAt F v τ) :
    rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ archTypeSubmoduleAt F v τ := by
  refine comp_mul_mem_typeSubmodule_of_commute hg _ fun k' => ?_
  rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
  exact (commute_adelicArchGLInclAt_of_ne F hvw _ _).symm

private theorem rightTranslate_mem_iSup_archTypeSubmoduleAt_of_ne {v w : InfinitePlace F} (hvw : v ≠ w) {m : ℕ}
    (τ : Fin m → ArchRepAt F v) (k : rowIsometrySubgroup₀ w.Completion) {g : AdelicGL2 (𝓞 F) F → ℂ}
    (hg : g ∈ ⨆ i, archTypeSubmoduleAt F v (τ i)) :
    rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ ⨆ i, archTypeSubmoduleAt F v (τ i) := by
  have key : ∀ i, (archTypeSubmoduleAt F v (τ i)).map (rightRegular F (rowIsometryInclAt₀ F w k))
      ≤ archTypeSubmoduleAt F v (τ i) := by
    intro i f hf
    obtain ⟨f₀, hf₀, rfl⟩ := Submodule.mem_map.mp hf
    exact rightTranslate_mem_archTypeSubmoduleAt_of_ne F hvw (τ i) k hf₀
  have hmap : (⨆ i, archTypeSubmoduleAt F v (τ i)).map (rightRegular F (rowIsometryInclAt₀ F w k))
      ≤ ⨆ i, archTypeSubmoduleAt F v (τ i) := by
    rw [Submodule.map_iSup]; exact iSup_mono key
  exact hmap (Submodule.mem_map_of_mem hg)

private theorem split_one_place (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w) (w : InfinitePlace F)
    (hσw : ∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (tys.rep w i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs w j))
    (Q : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hQc : ∀ g ∈ Q, Continuous g)
    (hQs : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ Q, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ Q) :
    Q ⊓ (⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)) ≤
      ⨆ j : Fin (r w), Q ⊓ archTypeSubmoduleAt F w (σs w j) :=
  AutomorphicForm.CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous F w
    (tys.card w) (tys.rep w) (r w) (σs w) (hσw) Q hQc hQs

private noncomputable def otherCut (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w) (P : Finset (InfinitePlace F))
    (J : (w : InfinitePlace F) → Fin (r w)) (w : InfinitePlace F) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  (⨅ (v : InfinitePlace F) (_ : v ∈ P) (_ : v ≠ w), archTypeSubmoduleAt F v (σs v (J v))) ⊓
    ⨅ (v : InfinitePlace F) (_ : v ∉ P) (_ : v ≠ w), ⨆ i : Fin (tys.card v), archTypeSubmoduleAt F v (tys.rep v i)

private theorem rightTranslate_mem_otherCut (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w) (P : Finset (InfinitePlace F))
    (J : (w : InfinitePlace F) → Fin (r w)) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    {g : AdelicGL2 (𝓞 F) F → ℂ} (hg : g ∈ otherCut F tys r σs P J w) :
    rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ otherCut F tys r σs P J w := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hg
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · refine (Submodule.mem_iInf _).mpr fun v => (Submodule.mem_iInf _).mpr fun hv =>
      (Submodule.mem_iInf _).mpr fun hvw => ?_
    have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h1 v) hv) hvw
    exact rightTranslate_mem_archTypeSubmoduleAt_of_ne F hvw _ k h
  · refine (Submodule.mem_iInf _).mpr fun v => (Submodule.mem_iInf _).mpr fun hv =>
      (Submodule.mem_iInf _).mpr fun hvw => ?_
    have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h2 v) hv) hvw
    exact rightTranslate_mem_iSup_archTypeSubmoduleAt_of_ne F hvw _ k h

private theorem mixedCut_le_otherCut_inf (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w) (P : Finset (InfinitePlace F))
    (J : (w : InfinitePlace F) → Fin (r w)) {w : InfinitePlace F} (hw : w ∉ P) :
    mixedCut F tys r σs P J ≤ otherCut F tys r σs P J w ⊓ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) := by
  intro f hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hf
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact (Submodule.mem_iInf _).mpr fun v => (Submodule.mem_iInf _).mpr fun hv => (Submodule.mem_iInf _).mpr fun _ =>
      (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h1 v) hv
  · exact (Submodule.mem_iInf _).mpr fun v => (Submodule.mem_iInf _).mpr fun hv => (Submodule.mem_iInf _).mpr fun _ =>
      (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h2 v) hv
  · exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h2 w) hw

open scoped Classical in

private theorem otherCut_inf_le_mixedCut_insert (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w) (P : Finset (InfinitePlace F))
    (J : (w : InfinitePlace F) → Fin (r w)) (w : InfinitePlace F) (j : Fin (r w)) :
    otherCut F tys r σs P J w ⊓ archTypeSubmoduleAt F w (σs w j) ≤
      mixedCut F tys r σs (insert w P) (Function.update J w j) := by
  classical
  intro f hf
  obtain ⟨h12, h3⟩ := Submodule.mem_inf.mp hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp h12
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · refine (Submodule.mem_iInf _).mpr fun v => (Submodule.mem_iInf _).mpr fun hv => ?_
    by_cases hvw : v = w
    · subst hvw
      rw [Function.update_self]
      exact h3
    · rw [Function.update_of_ne hvw]
      have hvP : v ∈ P := by simpa [hvw] using hv
      exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h1 v) hvP) hvw
  · refine (Submodule.mem_iInf _).mpr fun v => (Submodule.mem_iInf _).mpr fun hv => ?_
    have hvw : v ≠ w := fun h => hv (by simp [h])
    have hvP : v ∉ P := fun h => hv (Finset.mem_insert_of_mem h)
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h2 v) hvP) hvw

private theorem le_iSup_inf_mixedCut (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w)
    (hσ : ∀ (w : InfinitePlace F) (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (tys.rep w i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs w j))
    (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hWc : ∀ g ∈ W, Continuous g)
    (hWs : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ W,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ W)
    (hne : ∀ w, 0 < r w) (P : Finset (InfinitePlace F)) :
    W ⊓ archCutSubmodule F tys ≤ ⨆ J : (w : InfinitePlace F) → Fin (r w), W ⊓ mixedCut F tys r σs P J := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    let J₀ : (w : InfinitePlace F) → Fin (r w) := fun w => ⟨0, hne w⟩
    exact le_trans (inf_le_inf_left W (archCutSubmodule_le_mixedCut_empty F tys r σs J₀))
      (le_iSup (fun J : (w : InfinitePlace F) → Fin (r w) => W ⊓ mixedCut F tys r σs ∅ J) J₀)
  | insert w P hwP ih =>
    refine le_trans ih (iSup_le fun J => ?_)
    let Q : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := W ⊓ otherCut F tys r σs P J w
    have hQc : ∀ g ∈ Q, Continuous g := fun g hg => hWc g hg.1
    have hQs : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ Q, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ Q :=
      fun k g hg => ⟨hWs w k g hg.1, rightTranslate_mem_otherCut F tys r σs P J w k hg.2⟩
    have hsplit := split_one_place F tys r σs w (hσ w) Q hQc hQs
    calc W ⊓ mixedCut F tys r σs P J
        ≤ Q ⊓ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) := by
          intro f hf
          obtain ⟨hfW, hfm⟩ := Submodule.mem_inf.mp hf
          obtain ⟨hfo, hfw⟩ := Submodule.mem_inf.mp (mixedCut_le_otherCut_inf F tys r σs P J hwP hfm)
          exact ⟨⟨hfW, hfo⟩, hfw⟩
      _ ≤ ⨆ j : Fin (r w), Q ⊓ archTypeSubmoduleAt F w (σs w j) := hsplit
      _ ≤ ⨆ J' : (w : InfinitePlace F) → Fin (r w), W ⊓ mixedCut F tys r σs (insert w P) J' := by
          refine iSup_le fun j => le_trans ?_ (le_iSup _ (Function.update J w j))
          intro f hf
          obtain ⟨⟨hfW, hfo⟩, hfw⟩ := Submodule.mem_inf.mp hf
          exact ⟨hfW, otherCut_inf_le_mixedCut_insert F tys r σs P J w j ⟨⟨hfo.1, hfo.2⟩, hfw⟩⟩

private theorem inf_archCutSubmodule_eq_bot_of_eq_zero (tys : ArchTypeFamily F) (r : InfinitePlace F → ℕ)
    (σs : (w : InfinitePlace F) → Fin (r w) → ArchRepAt F w)
    (hσ : ∀ (w : InfinitePlace F) (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (tys.rep w i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs w j))
    (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hWc : ∀ g ∈ W, Continuous g)
    (hWs : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ W,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ W)
    (w₀ : InfinitePlace F) (hw₀ : r w₀ = 0) :
    W ⊓ archCutSubmodule F tys = ⊥ := by
  classical
  let Q : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    W ⊓ ⨅ (v : InfinitePlace F) (_ : v ≠ w₀), ⨆ i : Fin (tys.card v), archTypeSubmoduleAt F v (tys.rep v i)
  have hQc : ∀ g ∈ Q, Continuous g := fun g hg => hWc g hg.1
  have hQs : ∀ (k : rowIsometrySubgroup₀ w₀.Completion), ∀ g ∈ Q, rightTranslate F (rowIsometryInclAt₀ F w₀ k) g ∈ Q := by
    intro k g hg
    refine ⟨hWs w₀ k g hg.1, (Submodule.mem_iInf _).mpr fun v => (Submodule.mem_iInf _).mpr fun hv => ?_⟩
    exact rightTranslate_mem_iSup_archTypeSubmoduleAt_of_ne F hv _ k
      ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hg.2 v) hv)
  have hsplit := split_one_place F tys r σs w₀ (hσ w₀) Q hQc hQs
  rw [eq_bot_iff]
  calc W ⊓ archCutSubmodule F tys
      ≤ Q ⊓ ⨆ i : Fin (tys.card w₀), archTypeSubmoduleAt F w₀ (tys.rep w₀ i) := by
        intro f hf
        obtain ⟨hfW, hfc⟩ := Submodule.mem_inf.mp hf
        rw [mem_archCutSubmodule_iff] at hfc
        exact ⟨⟨hfW, (Submodule.mem_iInf _).mpr fun v => (Submodule.mem_iInf _).mpr fun _ => hfc v⟩, hfc w₀⟩
    _ ≤ ⨆ j : Fin (r w₀), Q ⊓ archTypeSubmoduleAt F w₀ (σs w₀ j) := hsplit
    _ ≤ ⊥ := by
        have : IsEmpty (Fin (r w₀)) := by rw [hw₀]; infer_instance
        rw [iSup_of_empty]

private theorem rightTranslate_rowIsometryInclAt₀_mem_inf_invariants
    (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F pins ξ V)
    (hU : ∀ u ∈ U, NumberField.AdelicLevel.glArch (𝓞 F) F u = 1)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    {g : AdelicGL2 (𝓞 F) F → ℂ} (hg : g ∈ V ⊓ Representation.invariants ((rightRegular F).comp U.subtype)) :
    rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) := by
  refine ⟨hV.rightTranslate_arch_mem w k g hg.1, ?_⟩
  show rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ Representation.invariants ((rightRegular F).comp U.subtype)
  rw [Representation.mem_invariants]
  rintro ⟨u, hu⟩
  have hgu : rightTranslate F u g = g := by
    have := (Representation.mem_invariants _ _).mp hg.2 ⟨u, hu⟩
    exact this
  show rightTranslate F u (rightTranslate F (rowIsometryInclAt₀ F w k) g) = rightTranslate F (rowIsometryInclAt₀ F w k) g
  have hcomm : u * rowIsometryInclAt₀ F w k = rowIsometryInclAt₀ F w k * u := by
    refine eq_of_glArch_eq_of_glFin_eq F ?_ ?_
    · rw [map_mul, map_mul, hU u hu, one_mul, mul_one]
    · rw [map_mul, map_mul, glFin_rowIsometryInclAt₀, mul_one, one_mul]
  rw [rightTranslate_rightTranslate, hcomm, ← rightTranslate_rightTranslate, hgu]

private theorem rightTranslate_rowIsometryInclAt₀_mem_inf_levelInvariantSubmodule
    (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 F))
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F pins ξ V)
    (hU : ∀ u ∈ pins.U N, NumberField.AdelicLevel.glArch (𝓞 F) F u = 1)
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    {g : AdelicGL2 (𝓞 F) F → ℂ} (hg : g ∈ V ⊓ levelInvariantSubmodule F pins N) :
    rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ V ⊓ levelInvariantSubmodule F pins N := by
  refine ⟨hV.rightTranslate_arch_mem w k g hg.1, ?_⟩
  intro x u hu
  show g (x * u * rowIsometryInclAt₀ F w k) = g (x * rowIsometryInclAt₀ F w k)
  have hcomm : u * rowIsometryInclAt₀ F w k = rowIsometryInclAt₀ F w k * u := by
    refine eq_of_glArch_eq_of_glFin_eq F ?_ ?_
    · rw [map_mul, map_mul, hU u hu, one_mul, mul_one]
    · rw [map_mul, map_mul, glFin_rowIsometryInclAt₀, mul_one, one_mul]
  rw [mul_assoc, hcomm, ← mul_assoc]
  exact hg.2 (x * rowIsometryInclAt₀ F w k) u hu

end ArchSplit

theorem exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V) :
    ∃ (n : ℕ) (τs : Fin n → ∀ w : InfinitePlace F, ArchRepAt F w),
      (∀ j w, (τs j w).ρ.IsIrreducible) ∧
      V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys ≤
        ⨆ j : Fin n, V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F) := by
  classical
  -- `hU`/`hO` are part of the frozen statement and are not needed: the compact-open hypothesis
  -- `hUO` is what the proof consumes. Named so the declaration carries no unused-variable warning
  -- (the binders cannot be renamed without rewriting the checked statement).
  have _ := hU
  have _ := hO
  set pins := productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F) with hpins
  choose r σs hirr hσ using fun w : InfinitePlace F =>
    AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup F w
      (tys.card w) (tys.rep w)
  set W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) with hW
  have hWc : ∀ g ∈ W, Continuous g := fun g hg =>
    ArchSplit.continuous_of_mem_cuspKFiniteSubmodule F pins ξ (hV.le hg.1)
  have hWs : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ W,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ W := fun w k g hg =>
    ArchSplit.rightTranslate_rowIsometryInclAt₀_mem_inf_invariants F pins ξ U V hV
      (fun u hu => (mem_finiteAdelicGL2Subgroup_iff F u).mp (Subgroup.mem_inf.mp (hUO ▸ hu)).2) w k hg
  by_cases hzero : ∃ w, r w = 0
  · obtain ⟨w₀, hw₀⟩ := hzero
    refine ⟨0, Fin.elim0, fun j => Fin.elim0 j, ?_⟩
    have hbot := ArchSplit.inf_archCutSubmodule_eq_bot_of_eq_zero F tys r σs hσ W hWc hWs w₀ hw₀
    rw [show V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F tys = W ⊓ archCutSubmodule F tys from rfl, hbot]
    exact bot_le
  · push Not at hzero
    have hne : ∀ w, 0 < r w := fun w => Nat.pos_of_ne_zero (hzero w)
    let e := Fintype.equivFin ((w : InfinitePlace F) → Fin (r w))
    refine ⟨Fintype.card ((w : InfinitePlace F) → Fin (r w)), fun j w => σs w (e.symm j w),
      fun j w => hirr w _, ?_⟩
    have hmain := ArchSplit.le_iSup_inf_mixedCut F tys r σs hσ W hWc hWs hne Finset.univ
    refine le_trans hmain (iSup_le fun J => ?_)
    refine le_trans ?_ (le_iSup _ (e J))
    show W ⊓ ArchSplit.mixedCut F tys r σs Finset.univ J ≤
      V ⊓ Representation.invariants ((rightRegular F).comp U.subtype) ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => σs w (e.symm (e J) w)⟩ : AutomorphicForm.ArchTypeFamily F)
    rw [Equiv.symm_apply_apply]
    exact inf_le_inf_left _ (ArchSplit.mixedCut_univ_le_archCutSubmodule F tys r σs J)

theorem exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V) :
    ∃ (n : ℕ) (τs : Fin n → ∀ w : InfinitePlace F, ArchRepAt F w),
      (∀ j w, (τs j w).ρ.IsIrreducible) ∧
      V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤
        ⨆ j : Fin n, V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τs j w⟩ : AutomorphicForm.ArchTypeFamily F) := by
  classical
  set pins := productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F) with hpins
  choose r σs hirr hσ using fun w : InfinitePlace F =>
    AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup F w
      (tys.card w) (tys.rep w)
  set W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := V ⊓ levelInvariantSubmodule F pins N with hW
  have hWc : ∀ g ∈ W, Continuous g := fun g hg =>
    ArchSplit.continuous_of_mem_cuspKFiniteSubmodule F pins ξ (hV.le hg.1)
  have hWs : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ W,
      rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ W := fun w k g hg =>
    ArchSplit.rightTranslate_rowIsometryInclAt₀_mem_inf_levelInvariantSubmodule F pins ξ N V hV
      (fun u hu => (mem_finiteAdelicGL2Subgroup_iff F u).mp (Subgroup.mem_inf.mp hu).2) w k hg
  by_cases hzero : ∃ w, r w = 0
  · obtain ⟨w₀, hw₀⟩ := hzero
    refine ⟨0, Fin.elim0, fun j => Fin.elim0 j, ?_⟩
    have hbot := ArchSplit.inf_archCutSubmodule_eq_bot_of_eq_zero F tys r σs hσ W hWc hWs w₀ hw₀
    rw [show V ⊓ levelInvariantSubmodule F pins N ⊓ archCutSubmodule F tys = W ⊓ archCutSubmodule F tys from rfl, hbot]
    exact bot_le
  · push Not at hzero
    have hne : ∀ w, 0 < r w := fun w => Nat.pos_of_ne_zero (hzero w)
    let e := Fintype.equivFin ((w : InfinitePlace F) → Fin (r w))
    refine ⟨Fintype.card ((w : InfinitePlace F) → Fin (r w)), fun j w => σs w (e.symm j w),
      fun j w => hirr w _, ?_⟩
    have hmain := ArchSplit.le_iSup_inf_mixedCut F tys r σs hσ W hWc hWs hne Finset.univ
    refine le_trans hmain (iSup_le fun J => ?_)
    refine le_trans ?_ (le_iSup _ (e J))
    show W ⊓ ArchSplit.mixedCut F tys r σs Finset.univ J ≤
      V ⊓ levelInvariantSubmodule F pins N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => σs w (e.symm (e J) w)⟩ : AutomorphicForm.ArchTypeFamily F)
    rw [Equiv.symm_apply_apply]
    exact inf_le_inf_left _ (ArchSplit.mixedCut_univ_le_archCutSubmodule F tys r σs J)


end CuspidalConstituent

namespace CuspidalSpectrum

namespace Orthogonal

section generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem map_orthogonal_le_orthogonal (M : Submodule ℂ E) (S S' : E →L[ℂ] E) (c : ℂ)
    (h : ∀ u v, ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ)
    (hM : M.map (S' : E →ₗ[ℂ] E) ≤ M) :
    Mᗮ.map (S : E →ₗ[ℂ] E) ≤ Mᗮ := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hw
  have hx' : x ∈ Mᗮ := hx
  rw [Submodule.mem_orthogonal] at hx'
  show S x ∈ Mᗮ
  rw [Submodule.mem_orthogonal]
  intro m hm
  have h1 : ⟪S' m, x⟫_ℂ = 0 := hx' (S' m) (hM ⟨m, hm, rfl⟩)
  have h2 : ⟪S x, m⟫_ℂ = 0 := by
    rw [h, ← inner_conj_symm, h1, map_zero, mul_zero]
  rw [← inner_conj_symm, h2, map_zero]

theorem inner_apply_eq_of_dense (D : Set E) (hD : Dense D) (S S' : E →L[ℂ] E) (c : ℂ)
    (h : ∀ u ∈ D, ∀ v ∈ D, ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ) :
    ∀ u v, ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ := by
  have step1 : ∀ v ∈ D, ∀ u, ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ := by
    intro v hv u
    have hc : IsClosed {u : E | ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ} :=
      isClosed_eq (Continuous.inner S.continuous continuous_const)
        (continuous_const.mul (Continuous.inner continuous_id continuous_const))
    have hsub : D ⊆ {u : E | ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ} := fun u hu => h u hu v hv
    have : u ∈ closure D := by rw [hD.closure_eq]; trivial
    exact hc.closure_subset_iff.2 hsub this
  intro u v
  have hc : IsClosed {v : E | ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ} :=
    isClosed_eq (Continuous.inner continuous_const continuous_id)
      (continuous_const.mul (Continuous.inner continuous_const S'.continuous))
  have hsub : D ⊆ {v : E | ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ} := fun v hv => step1 v hv u
  have : v ∈ closure D := by rw [hD.closure_eq]; trivial
  exact hc.closure_subset_iff.2 hsub this

end generic

variable {F : Type} [Field F] [NumberField F]
variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}

theorem dense_range_toCuspSubcarrier (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    Dense (Set.range (toCuspSubcarrier F hΦ₀ σ ξ) : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
  set N : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hN
  have hcl : cuspSubcarrier F hΦ₀ σ ξ = N.topologicalClosure := rfl
  have himg : Subtype.val '' Set.range (toCuspSubcarrier F hΦ₀ σ ξ) = (N : Set (Carrier F Φ₀ σ)) := by
    ext w
    constructor
    · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
      exact ⟨⟨(φ : AdelicGL2 (𝓞 F) F → ℂ), φ.2.1.1.1⟩, φ.2, rfl⟩
    · rintro ⟨ψ, hψ, rfl⟩
      have hψ' : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hψ
      refine ⟨toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ'⟩, ⟨_, rfl⟩, ?_⟩
      rw [toCuspSubcarrier_apply_coe]
  rw [dense_iff_closure_eq, Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himg,
    ← Submodule.topologicalClosure_coe, ← hcl, Set.eq_univ_iff_forall]
  exact fun v => v.2

def compress (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ)
    (hT : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ) :
    ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
  (T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) fun v => hT v v.2

@[scoped simp] theorem compress_apply_coe (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ)
    (hT : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) :
    (compress hΦ₀ σ ξ T hT v : Carrier F Φ₀ σ) = T v := rfl

theorem contMember_of_cuspMember {ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : φ ∈ cuspMemberSubmodule F Φ₀ ξ) : φ ∈ contMemberSubmodule F Φ₀ ξ :=
  ⟨h.1.1.1, h.2⟩

theorem apply_mem_cuspSubcarrier_of_isLift (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hop : ∀ φ ∈ cuspMemberSubmodule F Φ₀ ξ, op φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ op T) :
    ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ := by
  intro v hv
  set N : Submodule ℂ (Carrier F Φ₀ σ) :=
    Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hN
  have hcl : cuspSubcarrier F hΦ₀ σ ξ = N.topologicalClosure := rfl
  have hmaps : Set.MapsTo T (N : Set (Carrier F Φ₀ σ)) (N : Set (Carrier F Φ₀ σ)) := by
    rintro w ⟨ψ, hψ, rfl⟩
    have hψ' : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hψ
    have hcont : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨ψ.2, hψ'.2⟩
    have hcomm := hT.comm (ψ : AdelicGL2 (𝓞 F) F → ℂ) hcont
    have hcusp : op (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hop _ hψ'
    have heta : (⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hcont.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ψ :=
      Subtype.coe_eta ψ hcont.1
    rw [heta] at hcomm
    refine ⟨⟨op (ψ : AdelicGL2 (𝓞 F) F → ℂ), hcusp.1.1.1⟩, hcusp, ?_⟩
    exact hcomm.symm
  have hv' : v ∈ closure (N : Set (Carrier F Φ₀ σ)) := by
    rw [← Submodule.topologicalClosure_coe, ← hcl]; exact hv
  have := map_mem_closure T.continuous hv' hmaps
  rw [← Submodule.topologicalClosure_coe, ← hcl] at this
  exact this

theorem isCuspLift_compress (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ op T)
    (hT' : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T v ∈ cuspSubcarrier F hΦ₀ σ ξ) :
    IsCuspLift F hΦ₀ σ ξ op (compress hΦ₀ σ ξ T hT') := by
  intro φ h
  apply Subtype.ext
  rw [compress_apply_coe, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
  exact hT.comm (φ : AdelicGL2 (𝓞 F) F → ℂ) (contMember_of_cuspMember φ.2)

theorem map_orthogonal_le_of_rightTranslate (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ) (y : AdelicGL2 (𝓞 F) F)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hM : ∀ S' : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      IsCuspLift F hΦ₀ σ ξ (rightTranslate F y⁻¹) S' →
        M.map (S' : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M)
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hS : IsCuspLift F hΦ₀ σ ξ (rightTranslate F y) S) :
    Mᗮ.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ Mᗮ := by
  obtain ⟨T, T', hT, hT', hadj, -⟩ := exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ y
  have hmem : ∀ z, ∀ φ ∈ cuspMemberSubmodule F Φ₀ ξ, rightTranslate F z φ ∈ cuspMemberSubmodule F Φ₀ ξ :=
    fun z φ hφ => rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ z φ hφ
  have hT'sub := apply_mem_cuspSubcarrier_of_isLift hΦ₀ σ ξ _ (hmem y⁻¹) T' hT'
  set S' := compress hΦ₀ σ ξ T' hT'sub with hS'def
  have hS'lift : IsCuspLift F hΦ₀ σ ξ (rightTranslate F y⁻¹) S' := isCuspLift_compress hΦ₀ σ ξ _ T' hT' hT'sub
  set c : ℂ := ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) with hc
  have hdense : ∀ u ∈ Set.range (toCuspSubcarrier F hΦ₀ σ ξ), ∀ v ∈ Set.range (toCuspSubcarrier F hΦ₀ σ ξ),
      ⟪S u, v⟫_ℂ = c * ⟪u, S' v⟫_ℂ := by
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩
    have e1 : (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F y φ, hmem y φ φ.2⟩ : Carrier F Φ₀ σ)
        = T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) := by
      rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
      exact (hT.comm (φ : AdelicGL2 (𝓞 F) F → ℂ) (contMember_of_cuspMember φ.2)).symm
    have e2 : (S' (toCuspSubcarrier F hΦ₀ σ ξ ψ) : Carrier F Φ₀ σ)
        = T' (toCuspSubcarrier F hΦ₀ σ ξ ψ : Carrier F Φ₀ σ) := rfl
    rw [hS φ (hmem y φ φ.2), Submodule.coe_inner, Submodule.coe_inner, e1, e2,
      ← ContinuousLinearMap.adjoint_inner_right, hadj, smul_apply, inner_smul_right]
  have hall := inner_apply_eq_of_dense _ (dense_range_toCuspSubcarrier hΦ₀ σ ξ) S S' c hdense
  exact map_orthogonal_le_orthogonal M S S' c hall (hM S' hS'lift)

theorem map_orthogonal_le_of_rightConv (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F) (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M)
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hS : IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) S) :
    Mᗮ.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ Mᗮ := by
  obtain ⟨hfc, hfcs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨T, T', hT, hT', hadj⟩ := exists_isLift_rightConv F α β Φ₀ hΦ₀ σ ξ hσ f hfc hfcs
  have hflat : IsFactorizableTestFn F (flat F σ f) := isFactorizableTestFn_flat F σ f hf
  obtain ⟨tys', hft'⟩ := exists_isArchBiFinite_flat F σ tys f hf hft
  have hT'sub : ∀ v ∈ cuspSubcarrier F hΦ₀ σ ξ, T' v ∈ cuspSubcarrier F hΦ₀ σ ξ :=
    fun v hv => apply_mem_cuspSubcarrier_of_isLift_rightConv F hΦ₀ σ ξ hσ (flat F σ f) hflat T' hT' v hv
  set S' := compress hΦ₀ σ ξ T' hT'sub with hS'def
  have hS'lift : IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ (flat F σ f)) S' :=
    isCuspLift_compress hΦ₀ σ ξ _ T' hT' hT'sub
  have hdense : ∀ u ∈ Set.range (toCuspSubcarrier F hΦ₀ σ ξ), ∀ v ∈ Set.range (toCuspSubcarrier F hΦ₀ σ ξ),
      ⟪S u, v⟫_ℂ = (1 : ℂ) * ⟪u, S' v⟫_ℂ := by
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩
    have hm : rightConv F (φ : AdelicGL2 (𝓞 F) F → ℂ) f ∈ cuspMemberSubmodule F Φ₀ ξ :=
      rightConv_mem_cuspMemberSubmodule F hΦ₀ ξ f hf φ φ.2
    have e1 : (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F (φ : AdelicGL2 (𝓞 F) F → ℂ) f, hm⟩ : Carrier F Φ₀ σ)
        = T (toCuspSubcarrier F hΦ₀ σ ξ φ : Carrier F Φ₀ σ) := by
      rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
      exact (hT.comm (φ : AdelicGL2 (𝓞 F) F → ℂ) (contMember_of_cuspMember φ.2)).symm
    have e2 : (S' (toCuspSubcarrier F hΦ₀ σ ξ ψ) : Carrier F Φ₀ σ)
        = T' (toCuspSubcarrier F hΦ₀ σ ξ ψ : Carrier F Φ₀ σ) := rfl
    rw [hS φ hm, Submodule.coe_inner, Submodule.coe_inner, e1, e2,
      ← ContinuousLinearMap.adjoint_inner_right, hadj, one_mul]
  have hall := inner_apply_eq_of_dense _ (dense_range_toCuspSubcarrier hΦ₀ σ ξ) S S' 1 hdense
  exact map_orthogonal_le_orthogonal M S S' 1 hall (hM.map_le_of_rightConv (flat F σ f) tys' hflat hft' S' hS'lift)

end Orthogonal

namespace Closure

variable {F : Type} [Field F] [NumberField F]
variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

theorem cuspKFiniteSubmodule_fdPins_le : cuspKFiniteSubmodule F (fdPins F Φ₀) ξ ≤ cuspMemberSubmodule F Φ₀ ξ := by
  refine Submodule.span_le.mpr ?_
  rintro φ ⟨hsat, hcont, -⟩
  have h1 := hsat 1
  have : rightTranslate F 1 φ = φ := by funext x; simp [rightTranslate]
  rw [this] at h1
  exact ⟨h1, hcont⟩

theorem map_closure_le (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hWm : W ≤ cuspMemberSubmodule F Φ₀ ξ)
    (op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ)) (hop : ∀ w ∈ W, op w ∈ W)
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hS : IsCuspLift F hΦ₀ σ ξ op S) :
    Submodule.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
        (Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ)
          (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W)).topologicalClosure ≤
      (Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ)
          (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W)).topologicalClosure := by
  set X := Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ) (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W) with hX
  have hSX : ∀ x ∈ X, S x ∈ X := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hw : op (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ W := hop _ hφ
    have e := hS φ (hWm hw)
    show (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) (toCuspSubcarrier F hΦ₀ σ ξ φ) ∈ X
    rw [ContinuousLinearMap.coe_coe, e]
    exact ⟨⟨op φ, hWm hw⟩, hw, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  have hcont : Continuous (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) → ↥(cuspSubcarrier F hΦ₀ σ ξ)) := S.continuous
  have himage : (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) → ↥(cuspSubcarrier F hΦ₀ σ ξ)) '' closure (X : Set _) ⊆ closure (X : Set _) := by
    refine (image_closure_subset_closure_image hcont).trans (closure_mono ?_)
    rintro _ ⟨y, hy, rfl⟩
    exact hSX y hy
  have : S x ∈ closure (X : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := himage ⟨x, (Submodule.topologicalClosure_coe X) ▸ hx, rfl⟩
  rw [← Submodule.topologicalClosure_coe] at this
  exact this

end Closure

theorem isClosedCuspSubrep_orthogonal
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M) :
    IsClosedCuspSubrep F hΦ₀ σ ξ Mᗮ := by
  refine ⟨Submodule.isClosed_orthogonal M, fun g hg S hS => ?_, fun w k S hS => ?_, fun f tys hf hft S hS => ?_⟩
  · exact Orthogonal.map_orthogonal_le_of_rightTranslate hΦ₀ σ ξ hσ g M
      (fun S' h' => hM.map_le_of_rightTranslate_fin g⁻¹ (inv_mem hg) S' h') S hS
  · refine Orthogonal.map_orthogonal_le_of_rightTranslate hΦ₀ σ ξ hσ (rowIsometryInclAt₀ F w k) M
      (fun S' h' => ?_) S hS
    rw [← map_inv] at h'
    exact hM.map_le_of_rightTranslate_arch w k⁻¹ S' h'
  · exact Orthogonal.map_orthogonal_le_of_rightConv hΦ₀ σ ξ hσ f tys hf hft M hM S hS

theorem isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hW : IsCuspSubrep F (fdPins F Φ₀) ξ W) :
    IsClosedCuspSubrep F hΦ₀ σ ξ
      (Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ)
        (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W)).topologicalClosure := by
  have hWm : W ≤ cuspMemberSubmodule F Φ₀ ξ :=
    hW.le.trans (Closure.cuspKFiniteSubmodule_fdPins_le (Φ₀ := Φ₀) ξ)
  refine ⟨Submodule.isClosed_topologicalClosure _, fun g hg S hS => ?_, fun w k S hS => ?_, fun f tys hf hft S hS => ?_⟩
  · exact Closure.map_closure_le hΦ₀ σ ξ W hWm _ (fun ψ hψ => hW.rightTranslate_fin_mem g hg ψ hψ) S hS
  · exact Closure.map_closure_le hΦ₀ σ ξ W hWm _ (fun ψ hψ => hW.rightTranslate_arch_mem w k ψ hψ) S hS
  · exact Closure.map_closure_le hΦ₀ σ ξ W hWm _ (fun ψ hψ => hW.rightConv_mem f tys hf hft ψ hψ) S hS

end CuspidalSpectrum

end AutomorphicForm
