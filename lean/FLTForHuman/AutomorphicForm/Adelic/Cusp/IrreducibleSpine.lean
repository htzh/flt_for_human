/-
  The irreducibility spine of the cuspidal constituent.

  Five rows of the cuspidal `K`-finite subrepresentation. The first four are all of the form "the
  invariants of a cusp subrepresentation are already inside finitely many irreducible archimedean
  types":

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
  * `CuspidalConstituent.iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le`: the fifth row, one
    cut down — the sup of a *finite* family of cusp subreps commutes with the level-`N`-invariant and
    the archimedean cut (`(⨆ V ∈ 𝒱, V) ⊓ L ⊓ A ≤ ⨆ V ∈ 𝒱, V ⊓ L ⊓ A`), by averaging over the finite
    level subgroup `Ulev = levelOne N ⊓ finiteAdelicGL2Subgroup`.

  The two constituent rows are single-headline files: each pin carries its row as a `solution` and 15
  `private` engine declarations behind it. Those 30 private declarations are ported here as 15 private
  declarations of `CuspidalConstituent.ArchSplit` — the pins' own 14-declaration engine is *the same
  text* in both files and is written once (the two pins differ only in their last helper, whose two
  forms are the two declarations `rightTranslate_rowIsometryInclAt₀_mem_inf_invariants` and
  `…_mem_inf_levelInvariantSubmodule`).

  The fifth row (`S_…_iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le.lean`, 364 lines) is the
  flattened `CuspidalConstituent` pin: its 21 engine declarations are all **public**, and they are
  transcribed in a `CuspidalConstituent` block of their own (the pin's `T2Cut` label dropped) at the
  pin's own names — the three `abbrev`s `Kinf`, `kspan`, `Ulev` included, because they occur inside the
  pin's public statements. `Kinf` is the sup of the archimedean row-isometry ranges and `kspan φ` the
  span of the `Kinf`-right translates of `φ`; `exists_reps` (finite near-coset representatives of
  `Ulev`) and `exists_levelAverage` (the average lands in the level-`N`-invariants and fixes them) are
  the substantive rows, and `main` assembles them with the archimedean projector `Q`
  (`exists_linearMap_archCutProjector_comm_rightTranslate`). The headline's proof is the pin's own
  `exact main …`.

  The two `CuspidalSpectrum` rows are flattened files whose engine declarations are all public (10 + 2
  of them besides the row itself), in the pins' own in-file namespaces, which the port renames to
  subject namespaces `CuspidalSpectrum.Orthogonal` and `CuspidalSpectrum.Closure`.

  `CuspidalSpectrum.Orthogonal` is general Hilbert-space mathematics over `{E} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E]` (the pin's `Ws48Perp` block, `map_orthogonal_le_orthogonal`,
  `inner_apply_eq_of_dense`, `compress`, …), kept at the pin's generality and with the pin's
  `@[scoped simp]` on `compress_apply_coe`; the rest of that block works on the cusp subcarrier and
  follows the right-translation / right-convolution adjoint pairs.

  Transcribed from the five `S_` files below (pinned `aa2d8b3`, 320 + 317 + 234 + 75 + 364 lines), the
  pins' label namespaces dropped (`Ws48Perp` -> `Orthogonal`, `ClosureSubrep` -> `Closure`,
  `S12Reduce` -> `ArchSplit`, `T2Cut` -> the enclosing `CuspidalConstituent`) — no tokens in names.

  Deviations, all statement-preserving and recorded here:

  * The two constituent pins' private `eq_of_glArch_eq_of_glFin_eq'` (`:235` in each) is **not**
    restated *for those two pins*: the port has the same fact publicly at the pin's own name,
    `AutomorphicForm.eq_of_glArch_eq_of_glFin_eq` (`AutomorphicForm/Adelic/LevelCompactness.lean`).
    The fifth pin states the same theorem **publicly** (`:130`), so it *is* transcribed there (the
    checker wants the pin's declaration) — with the pin's statement and a one-line body calling the
    port's copy.
  * The rows' hypothesis binders `hU`/`hO` (compactness/openness of the level subgroups) are part of
    the frozen statement and are not consumed by the proof (`hUO` is what carries the level). They are
    named by `have _ := hU` / `have _ := hO` rather than renamed, which the checker would report.
  * `inf_archCutSubmodule_eq_bot_of_eq_zero` writes the empty-index instance as `have : IsEmpty …`
    (the pin's `haveI`), the `linter.style.haveILetI` suggestion (FR-0223).
  * The pins' `attribute [-instance]`/`[-simp]` walls are dropped, as the port's practice; the module
    elaborates silent without them.

  Deltas of the fifth row, all proof-side except two imports:

  * One import is added to the scaffold's list: `FLTForHuman.MeasureTheory.HaarAveraging`, for
    `exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup` (pin `:219`). The declaration was in the
    port but **not** in this module's import closure.
  * `haveI` → `have` / `letI` → `let` at seven instance binders (pin `:95`, `:98`, `:178`, `:179`,
    `:184`, `:197`), the linter's own suggestion (FR-0223/FR-0224). The `letI : MeasurableSpace` and
    the `Fintype`/`FiniteDimensional` instances still resolve as local instances through `have`/`let`.
  * The pin's `scoped instance compactSpace_Ulev` (`:168`) is kept at the pin's own spelling and name;
    `spec/statement_db.py` does not index a named `scoped instance`, so it is neither a row nor a
    wire-side extra.

  `tools/deps/dedup.py --within` reports two clusters, both the pin's own and both kept:
  `main` ≡ the headline `iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le` (18 lines, shape
  tier — the pin states the row twice, `:269` and `:352 solution`, and the checker needs both), and
  `continuous_of_mem_cuspKFiniteSubmodule` private in `ArchSplit` ≡ public in `CuspidalConstituent`
  (8 lines, name tier — the two `ArchSplit` pins carry the helper privately, the `T2Cut` pin carries
  the same text publicly). Removing either would edit a landed row's declaration or drop a pin row.

  The pin `S_…_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul` (`:23`, `:82`,
  `:168`, `:195`, `:217`) is transcribed verbatim at five declarations; deltas, all proof-side:

  * One import is added to the scaffold's fifteen:
    `FLTForHuman.Analysis.Normed.Operator.CompactFiniteDimensional`, for
    `Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq` (pin `:245`). The declaration
    was in the port but **not** in this module's import closure.
  * `haveI` → `have` at six instance binders (pin `:76`, `:106`, `:133`, `:244`, `:249`, `:257`), the
    linter's own suggestion (FR-0223).
  * Two v4.34 spellings in the row's proof: `ContinuousLinearMap.coe_smul'` → `FunLike.coe_smul` and
    `ContinuousLinearMap.smul_apply` → `smul_apply` (pin `:246`, `:247`).
  * The three `Submodule` lemmas are the pin's own and stay **public** (the pin states them public in
    its `Submodule` namespace); `HilbertExhaust` is kept as the namespace the scaffold froze, although
    the work order names it as a pin label — the row's name is the checker's.

  Heartbeat probe (gate 7, a measurement — the module carries **no** `set_option maxHeartbeats`):
  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` is silent at the edit-loop cap 200000 and at
  **N = 35000**, and fails at **N = 32000** and 30000 (one error, timeout at `whnf` on the row
  `exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul`, which owns the module's floor
  since this wave), at 25000 (the same single error), at 22000 / 20000 / 18500 (that error plus one
  `isDefEq` inside the row's proof) and at 12000 / 9250 (9 errors, now reaching the landed rows'
  engines: `map_orthogonal_le_of_rightTranslate`, `map_orthogonal_le_of_rightConv`, `map_closure_le`
  and the four landed rows). The fifth row's 21 engines do **not** move the floor: re-measured after
  they landed, the pair is unchanged (silent at 35000, one `whnf` timeout at 32000 on the same row),
  and the fifth row's first casualty is at N = 20000 (6 errors there: `exists_levelAverage`'s header
  plus two steps inside its proof, the rest on the older rows; 9 at N = 15000).

  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_inf_invariants_le_iSup_isIrreducible_of_isCuspSubrep.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le.lean
-/
import FLTForHuman.Analysis.Normed.Operator.CompactFiniteDimensional
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
import FLTForHuman.MeasureTheory.HaarAveraging
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

/-! The orthogonal exhaustion of a compact operator's eigenspace by minimal orthogonal
subrepresentations. The three generic lemmas are Hilbert-space mathematics over an arbitrary complex
inner-product space (`Submodule.exists_le_minimal_inf_ne_bot_of_forall_sInf_of_forall_orthogonal` and its
two consequences); `CuspidalSpectrum.HilbertExhaust.isClosedCuspSubrep_sInf` records that the closed cusp
subrepresentations are closed under arbitrary infima, i.e. that they instantiate the generic hypothesis;
the row is the exhaustion statement on the cusp subcarrier. -/

namespace Submodule

/-- A submodule `N ≤ W` with `N ⊓ E₀ ≠ ⊥` that is minimal among the `P`-submodules of `W` meeting `E₀`
nontrivially, for a `P` closed under infima and orthogonal complements and splitting over a
finite-dimensional `E₀`. -/
theorem exists_le_minimal_inf_ne_bot_of_forall_sInf_of_forall_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : Submodule ℂ E → Prop)
    (hPinf : ∀ S : Set (Submodule ℂ E), (∀ N ∈ S, P N) → P (sInf S))
    (hPorth : ∀ N, P N → P Nᗮ)
    (E₀ : Submodule ℂ E) [FiniteDimensional ℂ ↥E₀]
    (hsplit : ∀ N, P N → ∀ x ∈ E₀, ∃ y ∈ N ⊓ E₀, x - y ∈ Nᗮ)
    (W : Submodule ℂ E) (hW : P W) (hWE : W ⊓ E₀ ≠ ⊥) :
    ∃ N : Submodule ℂ E, N ≤ W ∧ P N ∧ N ≠ ⊥ ∧ N ⊓ E₀ ≠ ⊥ ∧
      ∀ N' : Submodule ℂ E, P N' → N' ≤ N → N' = ⊥ ∨ N' = N := by
  classical

  have hex : ∃ k : ℕ, ∃ N : Submodule ℂ E, N ≤ W ∧ P N ∧ N ⊓ E₀ ≠ ⊥ ∧ Module.finrank ℂ ↥(N ⊓ E₀) = k :=
    ⟨_, W, le_rfl, hW, hWE, rfl⟩
  obtain ⟨N, hNW, hPN, hNE, hNk⟩ := Nat.find_spec hex
  have hmin : ∀ M : Submodule ℂ E, M ≤ W → P M → M ⊓ E₀ ≠ ⊥ →
      Module.finrank ℂ ↥(N ⊓ E₀) ≤ Module.finrank ℂ ↥(M ⊓ E₀) := by
    intro M hMW hPM hME
    rw [hNk]
    exact Nat.find_min' hex ⟨M, hMW, hPM, hME, rfl⟩

  set D : Submodule ℂ E := N ⊓ E₀ with hD
  set N' : Submodule ℂ E := sInf {M : Submodule ℂ E | P M ∧ D ≤ M} with hN'
  have hPN' : P N' := hPinf _ fun M hM => hM.1
  have hDN' : D ≤ N' := le_sInf fun M hM => hM.2
  have hN'N : N' ≤ N := sInf_le ⟨hPN, inf_le_left⟩
  have hN'E : N' ⊓ E₀ = D :=
    le_antisymm (fun x hx => ⟨hN'N hx.1, hx.2⟩) (le_inf hDN' inf_le_right)
  have hDne : D ≠ ⊥ := hNE
  refine ⟨N', hN'N.trans hNW, hPN', ?_, by rwa [hN'E], ?_⟩
  · intro h
    exact hDne (le_bot_iff.mp (h ▸ hDN'))
  · intro M hPM hMN'
    by_cases hME : M ⊓ E₀ = ⊥
    ·
      left
      have hDM : D ≤ Mᗮ := by
        intro e he
        obtain ⟨y, hy, hey⟩ := hsplit M hPM e he.2
        have hy0 : y = 0 := by
          have : y ∈ (⊥ : Submodule ℂ E) := hME ▸ hy
          exact (Submodule.mem_bot ℂ).mp this
        rw [hy0, sub_zero] at hey
        exact hey
      have hN'M : N' ≤ Mᗮ := sInf_le ⟨hPorth M hPM, hDM⟩
      have : M ≤ M ⊓ Mᗮ := le_inf le_rfl (hMN'.trans hN'M)
      rw [Submodule.inf_orthogonal_eq_bot] at this
      exact le_bot_iff.mp this
    ·
      right
      have hle : M ⊓ E₀ ≤ D := fun x hx => ⟨hN'N (hMN' hx.1), hx.2⟩
      have hfin : Module.finrank ℂ ↥D ≤ Module.finrank ℂ ↥(M ⊓ E₀) :=
        hmin M (hMN'.trans (hN'N.trans hNW)) hPM hME
      have : FiniteDimensional ℂ ↥D := Submodule.finiteDimensional_inf_right _ _
      have heq : M ⊓ E₀ = D := Submodule.eq_of_le_of_finrank_le hle hfin
      have hDM : D ≤ M := heq ▸ inf_le_left
      exact le_antisymm hMN' (sInf_le ⟨hPM, hDM⟩)

/-- Every element of `W ⊓ E₀` is a finite sum of vectors lying in pairwise orthogonal minimal
`P`-submodules of `W`. -/
theorem exists_orthogonal_minimal_sum_eq_of_forall_sInf_of_forall_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : Submodule ℂ E → Prop)
    (hPinf : ∀ S : Set (Submodule ℂ E), (∀ N ∈ S, P N) → P (sInf S))
    (hPorth : ∀ N, P N → P Nᗮ)
    (E₀ : Submodule ℂ E) [FiniteDimensional ℂ ↥E₀]
    (hsplit : ∀ N, P N → ∀ x ∈ E₀, ∃ y ∈ N ⊓ E₀, x - y ∈ Nᗮ)
    (W : Submodule ℂ E) (hW : P W) (v : E) (hv : v ∈ W ⊓ E₀) :
    ∃ (n : ℕ) (M : Fin n → Submodule ℂ E) (vs : Fin n → E),
      (∀ i, M i ≤ W ∧ P (M i) ∧ M i ≠ ⊥ ∧ ∀ N' : Submodule ℂ E, P N' → N' ≤ M i → N' = ⊥ ∨ N' = M i) ∧
      (Pairwise fun i j => (M i) ⟂ (M j)) ∧
      (∀ i, vs i ∈ M i ⊓ E₀) ∧
      v = ∑ i, vs i := by
  classical

  suffices key : ∀ (d : ℕ) (W : Submodule ℂ E), P W → Module.finrank ℂ ↥(W ⊓ E₀) ≤ d → ∀ v ∈ W ⊓ E₀,
      ∃ (n : ℕ) (M : Fin n → Submodule ℂ E) (vs : Fin n → E),
        (∀ i, M i ≤ W ∧ P (M i) ∧ M i ≠ ⊥ ∧ ∀ N' : Submodule ℂ E, P N' → N' ≤ M i → N' = ⊥ ∨ N' = M i) ∧
        (Pairwise fun i j => (M i) ⟂ (M j)) ∧ (∀ i, vs i ∈ M i ⊓ E₀) ∧ v = ∑ i, vs i from
    key _ W hW le_rfl v hv
  intro d
  induction d with
  | zero =>
    intro W hW hd v hv
    have : FiniteDimensional ℂ ↥(W ⊓ E₀) := Submodule.finiteDimensional_inf_right _ _
    have hbot : W ⊓ E₀ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hd)
    have hv0 : v = 0 := by rw [hbot] at hv; exact (Submodule.mem_bot ℂ).mp hv
    exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [hv0]⟩
  | succ d ih =>
    intro W hW hd v hv
    by_cases hv0 : v = 0
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [hv0]⟩

    have hWE : W ⊓ E₀ ≠ ⊥ := fun h => hv0 ((Submodule.mem_bot ℂ).mp (h ▸ hv))
    obtain ⟨M₁, hM₁W, hPM₁, hM₁ne, hM₁E, hM₁min⟩ :=
      Submodule.exists_le_minimal_inf_ne_bot_of_forall_sInf_of_forall_orthogonal P hPinf hPorth E₀ hsplit W hW hWE

    obtain ⟨y, hy, hz⟩ := hsplit M₁ hPM₁ v hv.2
    set z := v - y with hzdef

    set W' : Submodule ℂ E := W ⊓ M₁ᗮ with hW'
    have hPW' : P W' := by
      have : W' = sInf {W, M₁ᗮ} := by rw [hW', sInf_pair]
      rw [this]
      refine hPinf _ ?_
      intro N hN
      rcases hN with rfl | rfl
      · exact hW
      · exact hPorth M₁ hPM₁
    have hzW' : z ∈ W' ⊓ E₀ := by
      refine ⟨⟨W.sub_mem hv.1 (hM₁W hy.1), hz⟩, E₀.sub_mem hv.2 hy.2⟩
    have : FiniteDimensional ℂ ↥(W ⊓ E₀) := Submodule.finiteDimensional_inf_right _ _
    have hlt : Module.finrank ℂ ↥(W' ⊓ E₀) < Module.finrank ℂ ↥(W ⊓ E₀) := by
      apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne (fun x hx => ⟨hx.1.1, hx.2⟩) fun heq => hM₁E ?_

      rw [← le_bot_iff, ← Submodule.inf_orthogonal_eq_bot M₁]
      intro x hx
      have hx' : x ∈ W' ⊓ E₀ := heq ▸ ⟨hM₁W hx.1, hx.2⟩
      exact ⟨hx.1, hx'.1.2⟩
    have hd' : Module.finrank ℂ ↥(W' ⊓ E₀) ≤ d := Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hd)
    obtain ⟨n, M, vs, hM, hMo, hvs, hsum⟩ := ih W' hPW' hd' z hzW'

    refine ⟨n + 1, Fin.cons M₁ M, Fin.cons y vs, ?_, ?_, ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_)
      · simpa only [Fin.cons_zero] using ⟨hM₁W, hPM₁, hM₁ne, hM₁min⟩
      · simp only [Fin.cons_succ]
        obtain ⟨h1, h2, h3, h4⟩ := hM i
        exact ⟨h1.trans inf_le_left, h2, h3, h4⟩
    ·
      intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;> rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact absurd rfl hij
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact (Submodule.isOrtho_iff_le.mpr (((hM j').1.trans inf_le_right))).symm
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact Submodule.isOrtho_iff_le.mpr ((hM i').1.trans inf_le_right)
      · simp only [Fin.cons_succ]
        exact hMo fun h => hij (congrArg Fin.succ h)
    · refine Fin.cases ?_ (fun i => ?_)
      · simpa only [Fin.cons_zero] using hy
      · simpa only [Fin.cons_succ] using hvs i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, ← hsum, hzdef, add_sub_cancel]

/-- The orthogonal splitting of an eigenvector: if `T` preserves both `N` and `Nᗮ` and `x` is a
`lam`-eigenvector of `T`, the component of `x` in `N` is itself a `lam`-eigenvector. -/
theorem exists_mem_sub_mem_orthogonal_and_apply_eq_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (N : Submodule ℂ E) [N.HasOrthogonalProjection] (T : E →ₗ[ℂ] E)
    (hTN : ∀ m ∈ N, T m ∈ N) (hTN' : ∀ m ∈ Nᗮ, T m ∈ Nᗮ) (lam : ℂ) (x : E) (hx : T x = lam • x) :
    ∃ y ∈ N, x - y ∈ Nᗮ ∧ T y = lam • y := by
  obtain ⟨y, hyN, hz⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := N) x
  have h1 : T y - lam • y ∈ N := N.sub_mem (hTN y hyN) (N.smul_mem lam hyN)
  have h3 : T (x - y) ∈ Nᗮ := hTN' _ hz
  have h4 : lam • (x - y) ∈ Nᗮ := Nᗮ.smul_mem lam hz
  have h5 : T (x - y) - lam • (x - y) ∈ Nᗮ := Nᗮ.sub_mem h3 h4
  have heq : T (x - y) - lam • (x - y) = -(T y - lam • y) := by
    rw [map_sub, smul_sub, hx, sub_sub_sub_cancel_left, neg_sub]
  have h2 : T y - lam • y ∈ Nᗮ := by
    have := Nᗮ.neg_mem h5
    rwa [heq, neg_neg] at this
  have h0 : T y - lam • y = 0 := by
    have hmem : T y - lam • y ∈ N ⊓ Nᗮ := ⟨h1, h2⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact ⟨y, hyN, hz, sub_eq_zero.mp h0⟩

end Submodule

namespace AutomorphicForm

namespace CuspidalSpectrum

namespace HilbertExhaust

variable {F : Type} [Field F] [NumberField F]

/-- The closed cusp subrepresentations are closed under arbitrary infima. -/
theorem isClosedCuspSubrep_sInf {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (S : Set (Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ))) (hS : ∀ M ∈ S, IsClosedCuspSubrep F hΦ₀ σ ξ M) :
    IsClosedCuspSubrep F hΦ₀ σ ξ (sInf S) := by
  refine ⟨?_, fun g hg T hT => ?_, fun w k T hT => ?_, fun f tys hf hft T hT => ?_⟩
  · have : ((sInf S : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Set ↥(cuspSubcarrier F hΦ₀ σ ξ))
        = ⋂ M ∈ S, (M : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
      ext x
      simp only [SetLike.mem_coe, Submodule.mem_sInf, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun M hM => (hS M hM).isClosed
  · exact le_sInf fun M hM => (Submodule.map_mono (sInf_le hM)).trans ((hS M hM).map_le_of_rightTranslate_fin g hg T hT)
  · exact le_sInf fun M hM => (Submodule.map_mono (sInf_le hM)).trans ((hS M hM).map_le_of_rightTranslate_arch w k T hT)
  · exact le_sInf fun M hM => (Submodule.map_mono (sInf_le hM)).trans ((hS M hM).map_le_of_rightConv f tys hf hft T hT)

end HilbertExhaust

/-- An eigenvector of a compact cusp operator on the cusp subcarrier is a finite sum of eigenvectors
lying in pairwise orthogonal irreducible cusp subrepresentations. -/
theorem exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (tys : ArchTypeFamily F)
    (hft : IsArchBiFinite F tys f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hTc : IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc) (hcpt : IsCompactOperator Tc)
    (lam : ℂ) (hlam : lam ≠ 0) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : Tc v = lam • v) :
    ∃ (n : ℕ) (M : Fin n → Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (vs : Fin n → ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ i, IsIrreducibleCuspSubrep F hΦ₀ σ ξ (M i)) ∧
      (Pairwise fun i j => (M i) ⟂ (M j)) ∧
      (∀ i, vs i ∈ M i ∧ Tc (vs i) = lam • vs i) ∧
      v = ∑ i, vs i := by
  classical

  have hPinf : ∀ S : Set (Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ N ∈ S, IsClosedCuspSubrep F hΦ₀ σ ξ N) → IsClosedCuspSubrep F hΦ₀ σ ξ (sInf S) :=
    fun S hS => HilbertExhaust.isClosedCuspSubrep_sInf hΦ₀ σ ξ S hS
  have hPorth : ∀ N, IsClosedCuspSubrep F hΦ₀ σ ξ N → IsClosedCuspSubrep F hΦ₀ σ ξ Nᗮ :=
    fun N hN => AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal F hΦ₀ σ ξ hσ N hN

  set E₀ : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    LinearMap.ker ((Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) - lam • LinearMap.id) with hE₀
  have hmemE₀ : ∀ w, w ∈ E₀ ↔ Tc w = lam • w := fun w => by
    rw [hE₀, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have : FiniteDimensional ℂ ↥E₀ :=
    Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq (T := lam⁻¹ • Tc)
      (by rw [FunLike.coe_smul]; exact hcpt.smul lam⁻¹) E₀ fun w hw => by
      rw [smul_apply, (hmemE₀ w).mp hw, smul_smul, inv_mul_cancel₀ hlam, one_smul]

  have : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    have : IsClosed ((cuspSubcarrier F hΦ₀ σ ξ : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
      unfold cuspSubcarrier
      exact Submodule.isClosed_topologicalClosure _
    exact this.completeSpace_coe

  have hsplit : ∀ N, IsClosedCuspSubrep F hΦ₀ σ ξ N → ∀ x ∈ E₀, ∃ y ∈ N ⊓ E₀, x - y ∈ Nᗮ := by
    intro N hN x hx
    have : CompleteSpace ↥N := hN.isClosed.completeSpace_coe
    have hTN : ∀ m ∈ N, Tc m ∈ N := fun m hm => hN.map_le_of_rightConv f tys hf hft Tc hTc ⟨m, hm, rfl⟩
    have hTN' : ∀ m ∈ Nᗮ, Tc m ∈ Nᗮ := fun m hm => (hPorth N hN).map_le_of_rightConv f tys hf hft Tc hTc ⟨m, hm, rfl⟩
    obtain ⟨y, hyN, hz, hTy⟩ := Submodule.exists_mem_sub_mem_orthogonal_and_apply_eq_smul N
      (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) hTN hTN' lam x ((hmemE₀ x).mp hx)
    exact ⟨y, ⟨hyN, (hmemE₀ y).mpr hTy⟩, hz⟩

  have hPtop : IsClosedCuspSubrep F hΦ₀ σ ξ ⊤ := by
    have := hPinf ∅ (fun N hN => hN.elim)
    rwa [sInf_empty] at this
  obtain ⟨n, M, vs, hM, hMo, hvs, hsum⟩ :=
    Submodule.exists_orthogonal_minimal_sum_eq_of_forall_sInf_of_forall_orthogonal
      (IsClosedCuspSubrep F hΦ₀ σ ξ) hPinf hPorth E₀ hsplit ⊤ hPtop v ⟨trivial, (hmemE₀ v).mpr hv⟩
  exact ⟨n, M, vs, fun i => ⟨(hM i).2.1, (hM i).2.2.1, (hM i).2.2.2⟩, hMo,
    fun i => ⟨(hvs i).1, (hmemE₀ _).mp (hvs i).2⟩, hsum⟩

end CuspidalSpectrum

end AutomorphicForm

namespace AutomorphicForm

namespace CuspidalConstituent

variable (F : Type) [Field F] [NumberField F]

abbrev Kinf : Subgroup (AdelicGL2 (𝓞 F) F) := ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range

abbrev kspan (φ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
    ψ = rightTranslate F k φ}

theorem continuous_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hc, -⟩; exact hc
  · exact continuous_const
  · intro u w _ _ hu hw; exact hu.add hw
  · intro c u _ hu; exact hu.const_smul c

theorem isKfSmooth_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (φ + ψ) :=
  FLT.SmoothVectors.IsSmoothVector.add hφ hψ

theorem isKfSmooth_smul (c : ℂ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) : IsKfSmooth F (c • φ) := by
  unfold IsKfSmooth FLT.SmoothVectors.IsSmoothVector at hφ ⊢
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer _ (FLT.SmoothVectors.RightTranslationFn.mk φ))
    (fun g hg => ?_) hφ
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
  have hx := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) hg
  simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
    FLT.SmoothVectors.RightTranslationFn.toFun_mk] at hx ⊢
  show c • φ (x * _) = c • φ x
  rw [hx]

theorem isKfSmooth_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : IsKfSmooth F φ := by
  refine Submodule.span_induction (p := fun φ _ => IsKfSmooth F φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, -, -⟩
    have h1 := (hsat 1).2
    rwa [show rightTranslate F 1 φ = φ from funext fun x => by rw [rightTranslate_apply, mul_one]] at h1
  · exact isKfSmooth_zero F
  · intro u w _ _ hu hw; exact isKfSmooth_add F hu hw
  · intro c u _ hu; exact isKfSmooth_smul F c hu

theorem kspan_add_le (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) : kspan F (φ + ψ) ≤ kspan F φ ⊔ kspan F ψ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [rightTranslate_add]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨k, hk, rfl⟩) (Submodule.subset_span ⟨k, hk, rfl⟩)

theorem kspan_smul_le (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : kspan F (c • φ) ≤ kspan F φ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, hk, rfl⟩
  rw [rightTranslate_smul]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, hk, rfl⟩)

theorem kspan_zero : kspan F (0 : AdelicGL2 (𝓞 F) F → ℂ) = ⊥ := by
  refine le_bot_iff.mp (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, hk, rfl⟩
  rw [rightTranslate_zero]
  exact Submodule.zero_mem _

theorem finiteDimensional_kspan_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) :
    FiniteDimensional ℂ ↥(kspan F φ) := by
  refine Submodule.span_induction (p := fun φ _ => FiniteDimensional ℂ ↥(kspan F φ)) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, -, tys, htys⟩
    exact AutomorphicForm.finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule F tys htys
  · show FiniteDimensional ℂ ↥(kspan F 0)
    rw [kspan_zero]; infer_instance
  · intro u w _ _ hu hw
    have := hu; have := hw
    exact Submodule.finiteDimensional_of_le (kspan_add_le F u w)
  · intro c u _ hu
    have := hu
    exact Submodule.finiteDimensional_of_le (kspan_smul_le F c u)

theorem rightTranslate_one' (φ : AdelicGL2 (𝓞 F) F → ℂ) : rightTranslate F 1 φ = φ :=
  funext fun x => by rw [rightTranslate_apply, mul_one]

theorem rightTranslate_mul' (g h : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    rightTranslate F (g * h) φ = rightTranslate F g (rightTranslate F h φ) :=
  funext fun x => by simp only [rightTranslate_apply, mul_assoc]

theorem rightTranslate_mem_of_mem_Kinf (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ S)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ Kinf F) : ∀ {φ : AdelicGL2 (𝓞 F) F → ℂ}, φ ∈ S → rightTranslate F k φ ∈ S := by
  refine Subgroup.iSup_induction (fun w : InfinitePlace F => (rowIsometryInclAt₀ F w).range)
    (C := fun k => ∀ {φ : AdelicGL2 (𝓞 F) F → ℂ}, φ ∈ S → rightTranslate F k φ ∈ S) hk ?_ ?_ ?_
  · rintro w _ ⟨k, rfl⟩ φ hφ
    exact hS w k φ hφ
  · intro φ hφ
    rwa [rightTranslate_one']
  · intro g h hg hh φ hφ
    rw [rightTranslate_mul']
    exact hg (hh hφ)

theorem kspan_le (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ S,
      rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ S)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ S) : kspan F φ ≤ S := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, hk, rfl⟩
  exact rightTranslate_mem_of_mem_Kinf F S hS hk hφ

theorem eq_of_glArch_eq_of_glFin_eq' {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : AdelicLevel.glArch (𝓞 F) F x = AdelicLevel.glArch (𝓞 F) F y)
    (h₂ : AdelicLevel.glFin (𝓞 F) F x = AdelicLevel.glFin (𝓞 F) F y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ finiteAdelicGL2Subgroup F) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    u * rowIsometryInclAt₀ F w k = rowIsometryInclAt₀ F w k * u := by
  refine eq_of_glArch_eq_of_glFin_eq' F ?_ ?_
  · rw [map_mul, map_mul, (mem_finiteAdelicGL2Subgroup_iff F u).mp hu, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_rowIsometryInclAt₀, mul_one, one_mul]

theorem rightTranslate_rowIsometryInclAt₀_mem_levelInvariantSubmodule (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) :
    rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N := by
  intro x u hu
  show φ (x * u * rowIsometryInclAt₀ F w k) = φ (x * rowIsometryInclAt₀ F w k)
  have hu' : u ∈ finiteAdelicGL2Subgroup F := (Subgroup.mem_inf.mp hu).2
  rw [mul_assoc, commute_rowIsometryInclAt₀_of_mem_finiteAdelicGL2Subgroup F hu' w k, ← mul_assoc]
  exact hφ (x * rowIsometryInclAt₀ F w k) u hu

section LevelAverage

variable (N : Ideal (𝓞 F))

abbrev Ulev : Subgroup (AdelicGL2 (𝓞 F) F) := levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F

scoped instance compactSpace_Ulev : CompactSpace ↥(Ulev F N) :=
  isCompact_iff_compactSpace.mp (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup F N)

theorem exists_reps {ι : Type} [Finite ι] (Φ : ι → (AdelicGL2 (𝓞 F) F → ℂ)) (hΦ : ∀ i, IsKfSmooth F (Φ i)) :
    ∃ (n : ℕ) (r : Fin n → ↥(Ulev F N)) (H : Subgroup ↥(Ulev F N)), 0 < n ∧
      (∀ v : ↥(Ulev F N), ∃ j, (r j)⁻¹ * v ∈ H) ∧
      (∀ j j', (r j)⁻¹ * r j' ∈ H → j = j') ∧
      (∀ h ∈ H, ∀ i, ∀ y : AdelicGL2 (𝓞 F) F, Φ i (y * (h : AdelicGL2 (𝓞 F) F)) = Φ i y) := by
  classical

  let : MeasurableSpace ↥(Ulev F N) := borel _
  have : BorelSpace ↥(Ulev F N) := ⟨rfl⟩
  let K₀ : TopologicalSpace.PositiveCompacts ↥(Ulev F N) :=
    { carrier := Set.univ, isCompact' := isCompact_univ,
      interior_nonempty' := by rw [interior_univ]; exact ⟨1, Set.mem_univ 1⟩ }
  let μ : Measure ↥(Ulev F N) := Measure.haarMeasure K₀
  have : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self (K₀ := K₀)⟩

  let H : Subgroup ↥(Ulev F N) :=
    { carrier := {v | ∀ i, ∀ y : AdelicGL2 (𝓞 F) F, Φ i (y * (v : AdelicGL2 (𝓞 F) F)) = Φ i y}
      one_mem' := fun i y => by simp
      mul_mem' := fun {a b} ha hb i y => by
        rw [Subgroup.coe_mul, ← mul_assoc, hb i, ha i]
      inv_mem' := fun {a} ha i y => by
        have := ha i (y * ((a⁻¹ : ↥(Ulev F N)) : AdelicGL2 (𝓞 F) F))
        rw [mul_assoc, Subgroup.coe_inv, inv_mul_cancel, mul_one] at this
        exact this.symm }
  have hHopen : IsOpen (H : Set ↥(Ulev F N)) := by

    have : Fintype ι := Fintype.ofFinite ι
    let incl : ↥(Ulev F N) → ↥(finiteAdelicGL2Subgroup F) := fun v => ⟨v, (Subgroup.mem_inf.mp v.2).2⟩
    have hincl : Continuous incl := continuous_subtype_val.subtype_mk _
    have hset : (H : Set ↥(Ulev F N)) = ⋂ i, incl ⁻¹'
        ((MulAction.stabilizer ↥(finiteAdelicGL2Subgroup F) (FLT.SmoothVectors.RightTranslationFn.mk (Φ i)) :
          Subgroup ↥(finiteAdelicGL2Subgroup F)) : Set ↥(finiteAdelicGL2Subgroup F)) := by
      ext v
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      constructor
      · intro hv i
        refine FLT.SmoothVectors.RightTranslationFn.ext fun y => ?_
        rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
          FLT.SmoothVectors.RightTranslationFn.toFun_mk]
        exact hv i y
      · intro hv i y
        have := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f y) (hv i)
        simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
          FLT.SmoothVectors.RightTranslationFn.toFun_mk] at this
        exact this
    rw [hset]
    exact isOpen_iInter_of_finite fun i => (hΦ i).preimage hincl
  obtain ⟨n, r, -, hn, hcov, hdis, -⟩ :=
    MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup μ H hHopen
  exact ⟨n, r, H, hn, hcov, hdis, fun h hh i y => hh i y⟩

theorem exists_levelAverage (D : Set (AdelicGL2 (𝓞 F) F)) {ι : Type} [Finite ι]
    (Φ : ι → (AdelicGL2 (𝓞 F) F → ℂ)) (hΦ : ∀ i, IsKfSmooth F (Φ i)) :
    ∃ (n : ℕ) (u : Fin n → AdelicGL2 (𝓞 F) F), 0 < n ∧
      (∀ j, u j ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) ∧
      (∀ i, (fun x => (n : ℂ)⁻¹ * ∑ j, Φ i (x * u j)) ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N) ∧
      (∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, ψ ∈ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N →
        (fun x => (n : ℂ)⁻¹ * ∑ j, ψ (x * u j)) = ψ) := by
  classical
  obtain ⟨n, r, H, hn, hcov, hdis, hfix⟩ := exists_reps F N Φ hΦ
  refine ⟨n, fun j => (r j : AdelicGL2 (𝓞 F) F), hn, fun j => (r j).2, fun i => ?_, fun ψ hψ => ?_⟩
  ·
    intro x u hu
    let v : ↥(Ulev F N) := ⟨u, hu⟩
    choose σ hσ using fun j => hcov (v * r j)
    have hσinj : Function.Injective σ := by
      intro j j' hjj
      apply hdis
      have h1 := hσ j
      have h2 := hσ j'
      rw [← hjj] at h2
      have := H.mul_mem (H.inv_mem h1) h2
      simpa [mul_assoc] using this
    have hσbij : Function.Bijective σ := (Finite.injective_iff_bijective).mp hσinj
    let e : Fin n ≃ Fin n := Equiv.ofBijective σ hσbij
    show (n : ℂ)⁻¹ * ∑ j, Φ i (x * u * (r j : AdelicGL2 (𝓞 F) F)) = (n : ℂ)⁻¹ * ∑ j, Φ i (x * (r j : AdelicGL2 (𝓞 F) F))
    congr 1
    have hterm : ∀ j, Φ i (x * u * (r j : AdelicGL2 (𝓞 F) F)) = Φ i (x * (r (σ j) : AdelicGL2 (𝓞 F) F)) := by
      intro j

      have hh : (r (σ j))⁻¹ * (v * r j) ∈ H := hσ j
      have := hfix _ hh i (x * (r (σ j) : AdelicGL2 (𝓞 F) F))
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at this
      rw [← this]
      congr 1
      simp only [v, mul_assoc, mul_inv_cancel_left]
    simp_rw [hterm]
    exact Equiv.sum_comp e (fun j => Φ i (x * (r j : AdelicGL2 (𝓞 F) F)))
  · funext x
    have hψ' : ∀ j, ψ (x * (r j : AdelicGL2 (𝓞 F) F)) = ψ x := fun j => hψ x _ (r j).2
    simp_rw [hψ']
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_mul]

end LevelAverage

theorem main
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (tys : AutomorphicForm.ArchTypeFamily F)
    (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ V ∈ 𝒱, IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V) :
    (⨆ V ∈ 𝒱, V) ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤
      ⨆ V ∈ 𝒱, (V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys) := by
  classical

  set L : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N with hL
  set A : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := archCutSubmodule F tys with hA
  intro φ hφ
  obtain ⟨⟨hφsup, hφL⟩, hφA⟩ := hφ

  have hsupKF : (⨆ V ∈ 𝒱, V) ≤ cuspKFiniteSubmodule F _ ξ := iSup₂_le fun V hV => (h𝒱 V hV).le
  have hφc : Continuous φ := continuous_of_mem_cuspKFiniteSubmodule F _ ξ (hsupKF hφsup)

  obtain ⟨c, hc⟩ := (Submodule.mem_iSup_finset_iff_exists_sum (s := 𝒱) (fun V => V) φ).mp hφsup

  have hcKF : ∀ V : ↥𝒱, (c V : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspKFiniteSubmodule F _ ξ :=
    fun V => (h𝒱 V V.2).le (c V).2
  obtain ⟨n, u, hn, hu, hAinv, hAid⟩ := exists_levelAverage F N D (fun V : ↥𝒱 => (c V : AdelicGL2 (𝓞 F) F → ℂ))
    (fun V => isKfSmooth_of_mem_cuspKFiniteSubmodule F _ ξ (hcKF V))
  let Av : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun ψ x => (n : ℂ)⁻¹ * ∑ j, ψ (x * u j)
      map_add' := fun ψ ψ' => funext fun x => by
        simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
      map_smul' := fun a ψ => funext fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
        ring }
  have hAv_apply : ∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, Av ψ = fun x => (n : ℂ)⁻¹ * ∑ j, ψ (x * u j) := fun _ => rfl

  have hψV : ∀ V : ↥𝒱, Av (c V) ∈ (V : Submodule ℂ _) := by
    intro V
    rw [hAv_apply]
    have : (fun x => (n : ℂ)⁻¹ * ∑ j, (c V : AdelicGL2 (𝓞 F) F → ℂ) (x * u j)) =
        (n : ℂ)⁻¹ • ∑ j, rightTranslate F (u j) (c V : AdelicGL2 (𝓞 F) F → ℂ) := by
      funext x
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, rightTranslate_apply]
    rw [this]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => ?_)
    exact (h𝒱 V V.2).rightTranslate_fin_mem (u j) (Subgroup.mem_inf.mp (hu j)).2 _ (c V).2
  have hψL : ∀ V : ↥𝒱, Av (c V) ∈ L := fun V => hAinv V
  have hsumψ : ∑ V : ↥𝒱, Av (c V) = φ := by
    rw [← map_sum, show (∑ V : ↥𝒱, (c V : AdelicGL2 (𝓞 F) F → ℂ)) = φ from ?_]
    · exact hAid φ hφL
    · rw [← hc]
      exact (Finset.sum_coe_sort 𝒱 (fun V => (c V : AdelicGL2 (𝓞 F) F → ℂ)))

  obtain ⟨Q, hQ1, hQ2, -⟩ := AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate F tys
  have hθ : ∀ V : ↥𝒱, Q (Av (c V)) ∈ (V : Submodule ℂ _) ⊓ L ⊓ A := by
    intro V
    have hmemKF : Av (c V) ∈ cuspKFiniteSubmodule F _ ξ := (h𝒱 V V.2).le (hψV V)
    have hcont : Continuous (Av (c V)) := continuous_of_mem_cuspKFiniteSubmodule F _ ξ hmemKF
    have hfd : FiniteDimensional ℂ ↥(kspan F (Av (c V))) :=
      finiteDimensional_kspan_of_mem_cuspKFiniteSubmodule F _ ξ hmemKF
    obtain ⟨hQA, hQspan⟩ := Submodule.mem_inf.mp (hQ2 (Av (c V)) hcont hfd)
    have hstab : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ (V : Submodule ℂ _) ⊓ L,
        rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ (V : Submodule ℂ _) ⊓ L := fun w k g hg =>
      ⟨(h𝒱 V V.2).rightTranslate_arch_mem w k g hg.1,
        rightTranslate_rowIsometryInclAt₀_mem_levelInvariantSubmodule F D N w k hg.2⟩
    have hle : kspan F (Av (c V)) ≤ (V : Submodule ℂ _) ⊓ L := kspan_le F _ hstab ⟨hψV V, hψL V⟩
    exact ⟨hle hQspan, hQA⟩
  have hsumθ : ∑ V : ↥𝒱, Q (Av (c V)) = φ := by
    rw [← map_sum, hsumψ]
    exact hQ1 φ hφc hφA

  rw [← hsumθ]
  refine Submodule.sum_mem _ fun V _ => ?_
  exact (le_iSup₂ (f := fun (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : W ∈ 𝒱) => W ⊓ L ⊓ A) V.1 V.2) (hθ V)


end CuspidalConstituent

end AutomorphicForm

namespace AutomorphicForm

namespace CuspidalConstituent

theorem iSup_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (tys : AutomorphicForm.ArchTypeFamily F)
    (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ V ∈ 𝒱, IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V) :
    (⨆ V ∈ 𝒱, V) ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤
      ⨆ V ∈ 𝒱, (V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys) := by
  exact main F D ξ N tys 𝒱 h𝒱

end CuspidalConstituent

end AutomorphicForm
