/-
The cuspidal constituent's intersection with the level `archCut` piece.

Two rows closing the constituent story SET-AF104/105 opened:

* `AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent`
  — a cusp constituent `V`, intersected with the level-invariant `archCut` piece, sits inside the
  closed span of the right convolutions of its own vectors: the constituent is generated, as a
  topological module, by the translates of any one level-spherical eigenvector (this is SET-AF105B's
  eigenvector result applied to `V`);
* `AutomorphicForm.CuspidalSpectrum.map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed` —
  an irreducible closed cuspidal subrepresentation maps its own intersection: the image under a closed
  subrepresentation's projector is either `⊥` or contained in it.

The engine is the constituent's own structure (`Cusp/{Constituent,ConstituentModulus,
SpectrumConstituentClosure}.lean`), the arch-type/level piece
(`Cusp/{ArchTypeSubmodule,LevelSphericalEigenvector}.lean`, the latter SET-AF105B's), the
irreducibility spine (`Cusp/IrreducibleSpine.lean`, `Cusp/ConstituentSpine.lean`), the right
convolution action (`RightConvComm/Action.lean`, `TestFnTop.lean`) and the carrier API
(`Cusp/{SpectrumLift,SpectrumTranslation}.lean`).

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed.lean>

## Port notes

Pins: `P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_
archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent.lean` (650 lines / **34 rows**: one
public `solution` + 33 private) and
`P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_
isClosed.lean` (232 lines / **6 public rows**).  Both rows landed; no `sorry`, no `axiom`.

* **Substituted (imported, not rewritten).** The two headlines' **twelve premises** are all public in
  the port and are imported: `exists_hasModulus_of_isCuspConstituent`
  (`Cusp/ConstituentModulus.lean`), `exists_rightConv_ne_zero_of_ne_bot`
  (`Cusp/SpectrumConstituentClosure.lean`), `exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType`
  (`Cusp/LevelSphericalEigenvector.lean`, SET-AF105B's row — the 650-row is that result plus the
  constituent's own `iSup` computation), `exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep`
  (`Cusp/IrreducibleSpine.lean`), `typeSubmodule_inf_typeSubmodule_eq_bot`
  (`Cusp/ArchTypeSubmodule.lean`), `rightConv_mem_archCutSubmodule_of_isArchBiFinite`
  (`Adelic/ArchApproximation.lean`), `continuous_and_hasCompactSupport_of_isFactorizableTestFn`
  (`Adelic/TestFnTop.lean`), `rightTranslate_rightConv_of_isLevelSphericalOfType`
  (`RightConvComm/Action.lean`), and row 2's
  `isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep`
  (`Cusp/SpectrumLift.lean`), `isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep`
  (`Cusp/IrreducibleSpine.lean`), `exists_idempotent_cutProjector_of_isCompact`
  (`Cusp/LevelSphericalEigenvector.lean`), `rightTranslate_mem_cuspMemberSubmodule`
  (`Cusp/SpectrumTranslation.lean`), `iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le`
  (`Cusp/ConstituentSpine.lean`).
* **Two pin rows are port declarations under another name** (`port_advise`'s binder-spelling tier,
  both statements read against the pin's): `isCuspSubrep_iInf` (`S_232:71`) is
  `AutomorphicForm.CuspidalConstituent.Spine.isCuspSubrep_iInf₂` (`Cusp/SpectrumDensity.lean`, public),
  and `continuous_of_mem_cuspKFiniteSubmodule` (`S_650:518`) is
  `AutomorphicForm.CuspidalConstituent.continuous_of_mem_cuspKFiniteSubmodule` (`Cusp/IrreducibleSpine.lean:1066`,
  public).  Both are imported; neither is re-proved here.
* **`private` in the port ⇒ transcribed** (the preamble's rule: a `private` port declaration is not
  importable).  Nine pin rows are already in the port but `private`, so they are written here with
  the port's own text and stay `private` as in the pin:
  `rightTranslationRep`, `intertwiningOfEquivariant`, `asModuleMap`, `nonzeroRanges`,
  `nonzeroRanges_equiv`, `mem_sSup_nonzeroRanges` (`Cusp/ArchTypeSubmodule.lean:1079–1143`),
  `mem_inf_inf` (`Cusp/LevelSphericalEigenvector.lean`, `SphericalCutScalar.mem_inf_inf`), and the two
  arch-family helpers of row 2 — the pin's `appendFamily` is `archTypeFamilyJoin`
  (`Cusp/RightConvSubrep.lean:62`, `private`) and the pin's `archCutSubmodule_le_append_left/right` are
  `IsContainedIn` statements over it (`isContainedIn_archTypeFamilyJoin_left/right`), because the port
  restates the join through `ArchTypeFamily.IsContainedIn` (`Adelic/IsotypicCuspSpace.lean:788`) and
  `archCutSubmodule_mono`.  Those two are the only rows whose statement is *not* the pin's — the pin's
  `≤` form is recovered through `archCutSubmodule_mono` at the two call sites.
* **Not carried**: the `p2m_open`/`p2m_export`/`p2m_reactivate` macro scaffolding and the pin's
  `attribute [-instance]` / `attribute [-simp]` walls.  Carried, because the mathematics needs them:
  the pin's `set_option backward.isDefEq.respectTransparency false in` on the seven `asModule`-shaped
  declarations (`S_650:261–380`) — `map_mem_typeSubmodule` is not decidable at implicit transparency,
  and `Cusp/ArchTypeSubmodule.lean` does not carry the last four of them, so the option is not
  redundant here; and `set_option linter.style.haveILetI false` (style only) for the pins' `haveI`
  blocks.  **No `set_option maxHeartbeats`**, no `synthInstance.maxHeartbeats`.
* **Heartbeat probe pair (recorded, not installed)**: `lake env lean -DautoImplicit=false
  -DmaxHeartbeats=N` is **silent for N = 200000 (the edit-loop cap), 150000, 100000, 80000, 60000 and
  50000**, and **first fails at N = 45000** (deterministic `isDefEq` timeout at 928, the
  `Submodule.topologicalClosure` step of row 2, plus a `whnf` timeout at 918); N = 40000 fails
  earlier, at 909/906.  So the module's tightest declaration needs ≈ 47 k and the edit-loop cap is
  ≈ 4× that: no declaration is near the cap and there is no residual for the manager.
spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent.lean
spec-pin: Theorems/Thm_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed.lean
spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent.lean
spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed.lean
## Manager's decisions at review (SET-AF106D)

* **the 36 `private` helpers stay `private`, and no promotion happens in this module.**  Eight of
  them (`typeSubmodule_le_of_equiv`, `typeSubmodule_eq_of_equiv`, `rightTranslationRep`,
  `intertwiningOfEquivariant`, `asModuleMap`, `nonzeroRanges`, `nonzeroRanges_equiv`,
  `mem_sSup_nonzeroRanges`) already exist `private` in `Cusp/ArchTypeSubmodule.lean`, so promoting
  this module's copies would publish a second copy of the same mathematics at root level — the one
  home is the arch-type module, and promoting *there* plus importing is a hub refactor (its
  dependents re-elaborate), registered in CARRY-FORWARD rather than done mid-wave.  The surface
  probe's 36 `ok` is recorded above; the pin has these rows `private` too.
* **`backward.isDefEq.respectTransparency false` is kept, scoped to the seven declarations that need
  it.**  It is the pin's own option and the port has the precedent (`RepTheory/BiIsotypic.lean`, five
  scoped uses); it is elaboration semantics, not a budget, and without it
  `map_mem_typeSubmodule`'s `rw [LinearEquiv.apply_symm_apply]` is not type-correct at implicit
  transparency — the FR-0309 transparency class.  The proper cure (state the term in the shape `rw`
  needs) is a refactor-round option, not a reason to carry a file-wide option; it is scoped here.
* **the two `IsContainedIn` restatements stay.**  `isContainedIn_archTypeFamilyJoin_left/right` are
  the pin's `archCutSubmodule_le_append_left/right` in this port's interface for that family
  (`ArchTypeFamily.IsContainedIn`, as landed in `Cusp/RightConvSubrep.lean`), i.e. the same
  mathematics in the port's own spelling — the surface probe's two `missing` rows are that spelling
  difference, not an omission.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchApproximation
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArchTypeSubmodule
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ConstituentModulus
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ConstituentSpine
import FLTForHuman.AutomorphicForm.Adelic.Cusp.IrreducibleSpine
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelSphericalEigenvector
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumConstituentClosure
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumLift
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumTranslation
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Action
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop

noncomputable section

set_option autoImplicit false

-- The pins' `haveI` blocks (instance binders feeding `Representation.asModule` and the
-- `CompleteSpace` of the carrier) are transcribed verbatim; this is a style linter only.
set_option linter.style.haveILetI false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent
open AutomorphicForm.CuspidalSpectrum

open scoped BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

/-! ### Right-convolution sums

The test function of the 650-row is a finite sum of the individual eigen-test-functions, so
`rightConv` has to distribute over a finite sum on its right. -/

section RightConvSums

variable (K : Type) [Field K] [NumberField K]

private theorem rightConv_add_right {φ f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ)
    (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁)
    (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂) :
    rightConv K φ (fun x => f₁ x + f₂ x) = fun g => rightConv K φ f₁ g + rightConv K φ f₂ g := by
  have hHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
    isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hint : ∀ {f : AdelicGL2 (𝓞 K) K → ℂ}, Continuous f → HasCompactSupport f →
      ∀ g : AdelicGL2 (𝓞 K) K, Integrable (fun x => φ (g * x) * f x)
        (adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro f hf hfc g
    have hc : Continuous fun x : AdelicGL2 (𝓞 K) K => φ (g * x) * f x :=
      (hφ.comp (continuous_const.mul continuous_id)).mul hf
    have hs : HasCompactSupport fun x : AdelicGL2 (𝓞 K) K => φ (g * x) * f x := hfc.mul_left
    exact hc.integrable_of_hasCompactSupport hs
  funext g
  simp only [rightConv_apply, mul_add]
  exact integral_add (hint hf₁ hf₁c g) (hint hf₂ hf₂c g)

private theorem continuous_and_hasCompactSupport_finsetSum {ι : Type} (s : Finset ι)
    (z : ι → AdelicGL2 (𝓞 K) K → ℂ) (hz : ∀ j, Continuous (z j) ∧ HasCompactSupport (z j)) :
    Continuous (fun x => ∑ j ∈ s, z j x) ∧ HasCompactSupport (fun x => ∑ j ∈ s, z j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨continuous_const, HasCompactSupport.zero⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact ⟨(hz a).1.add ih.1, (hz a).2.add ih.2⟩

private theorem rightConv_finsetSum_right {ι : Type} (s : Finset ι) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : Continuous φ) (z : ι → AdelicGL2 (𝓞 K) K → ℂ)
    (hz : ∀ j, Continuous (z j) ∧ HasCompactSupport (z j)) :
    rightConv K φ (fun x => ∑ j ∈ s, z j x) = fun g => ∑ j ∈ s, rightConv K φ (z j) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact rightConv_zero_right K φ
  | insert a s ha ih =>
    have hs := continuous_and_hasCompactSupport_finsetSum K s z hz
    simp only [Finset.sum_insert ha]
    rw [rightConv_add_right K hφ (hz a).1 (hz a).2 hs.1 hs.2, ih]

end RightConvSums

/-! ### Type pieces and the arch cut up to equivalence

Two equivalent archimedean representations have the same type piece, hence the same arch cut: this
is what lets the 650-row compare the pieces indexed by `X` with each other along `piece_congr`. -/

section TypePieceCongr

variable {H G : Type*} [Group H] [Group G]
variable {W W' : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

private theorem typeSubmodule_le_of_equiv (ι : H →* G) {ρ : Representation ℂ H W}
    {ρ' : Representation ℂ H W'} (e : ρ.Equiv ρ') : typeSubmodule ι ρ' ≤ typeSubmodule ι ρ := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, v, rfl⟩
  have hS : IsRightEquivariant ι ρ (T ∘ₗ e.toLinearMap) := by
    intro k u x
    have hek : e (ρ k u) = ρ' k (e u) :=
      Representation.IntertwiningMap.isIntertwining ρ ρ' e.toIntertwiningMap k u
    simp only [LinearMap.comp_apply, Representation.Equiv.coe_toLinearMap]
    rw [hek]
    exact hT k (e u) x
  have hv : T v = (T ∘ₗ e.toLinearMap) (e.symm v) := by
    simp only [LinearMap.comp_apply, Representation.Equiv.coe_toLinearMap,
      Representation.Equiv.apply_symm_apply]
  rw [hv]
  exact mem_typeSubmodule_of_isRightEquivariant hS _

private theorem typeSubmodule_eq_of_equiv (ι : H →* G) {ρ : Representation ℂ H W}
    {ρ' : Representation ℂ H W'} (e : ρ.Equiv ρ') : typeSubmodule ι ρ = typeSubmodule ι ρ' :=
  le_antisymm (typeSubmodule_le_of_equiv ι e.symm) (typeSubmodule_le_of_equiv ι e)

end TypePieceCongr

section ArchCutCongr

variable (F : Type) [Field F] [NumberField F]

private theorem archTypeSubmoduleAt_eq_of_equiv (w : InfinitePlace F) {τ τ' : ArchRepAt F w}
    (e : τ.ρ.Equiv τ'.ρ) : archTypeSubmoduleAt F w τ = archTypeSubmoduleAt F w τ' :=
  typeSubmodule_eq_of_equiv (rowIsometryInclAt₀ F w) e

private theorem archCutSubmodule_eq_of_forall_equiv {τ τ' : ∀ w : InfinitePlace F, ArchRepAt F w}
    (e : ∀ w, (τ w).ρ.Equiv (τ' w).ρ) :
    archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) =
      archCutSubmodule F (⟨fun _ => 1, fun w _ => τ' w⟩ : AutomorphicForm.ArchTypeFamily F) := by
  unfold archCutSubmodule
  exact iInf_congr fun w => iSup_congr fun _ => archTypeSubmoduleAt_eq_of_equiv F w (e w)

end ArchCutCongr

/-! ### Finite sums of test functions

The 650-row's test function `f` is the sum of one eigen-test-function per irreducible piece of the
arch cut.  It is factorisable because every summand is `fa j` times the indicator of the *same*
compact open level group. -/

section TestFnSums

open NumberField.AdelicLevel
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

namespace IsArchTestFactor

private theorem add {fa fb : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (ha : IsArchTestFactor F fa) (hb : IsArchTestFactor F fb) :
    IsArchTestFactor F (fun x => fa x + fb x) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hca⟩ := ha
  obtain ⟨⟨Ψ, hΨ, hfb⟩, hcb⟩ := hb
  refine ⟨⟨fun e => Φ e + Ψ e, hΦ.add hΨ, fun g => ?_⟩, ?_⟩
  · simp only [hfa g, hfb g]
  · exact hca.add hcb

end IsArchTestFactor

private theorem isArchTestFactor_finsetSum {ι : Type} (s : Finset ι)
    (fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (h : ∀ j, IsArchTestFactor F (fa j)) :
    IsArchTestFactor F (fun x => ∑ j ∈ s, fa j x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isArchTestFactor_zero F
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsArchTestFactor.add F (h a) ih

private theorem isFinTestFactor_indicator_of_isClopen_of_isCompact
    {S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))} (hS : IsClopen S) (hSc : IsCompact S) :
    IsFinTestFactor F (Set.indicator S (fun _ => (1 : ℂ))) := by
  refine ⟨?_, ?_⟩
  · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
    by_cases hx : x ∈ S
    · refine ⟨S, hS.isOpen, hx, fun y hy => ?_⟩
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · refine ⟨Sᶜ, hS.isClosed.isOpen_compl, hx, fun y hy => ?_⟩
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · rw [hasCompactSupport_def]
    exact hSc.of_isClosed_subset isClosed_closure
      (closure_minimal Set.support_indicator_subset hS.isClosed)

private theorem image_glFin_levelOne_inf_finiteAdelicGL2Subgroup (N : Ideal (𝓞 F)) :
    glFin (𝓞 F) F ''
        ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
          Set (AdelicGL2 (𝓞 F) F)) =
      (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  ext b
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (Subgroup.mem_inf.1 hg).1
  · intro hb
    refine ⟨AdelicDock.finEmbed (𝓞 F) F b, Subgroup.mem_inf.2 ⟨?_, ?_⟩,
      AdelicDock.glFin_finEmbed (𝓞 F) F b⟩
    · exact (AdelicDock.finEmbed_mem_levelOne_iff (𝓞 F) F (N := N) b).2 hb
    · exact (mem_finiteAdelicGL2Subgroup_iff F _).2 (AdelicDock.glArch_finEmbed (𝓞 F) F b)

private theorem isFinTestFactor_indicator_image_glFin_levelOne_inf (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) :
    IsFinTestFactor F (Set.indicator (glFin (𝓞 F) F ''
      ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
        Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))) := by
  rw [image_glFin_levelOne_inf_finiteAdelicGL2Subgroup F N]
  exact isFinTestFactor_indicator_of_isClopen_of_isCompact F
    ⟨isClosed_finiteLevelOne (𝓞 F) F N, isOpen_finiteLevelOne (𝓞 F) F hN⟩
    (isCompact_finiteLevelOne (𝓞 F) F N)

private theorem isFactorizableTestFn_finsetSum_of_forall_eq_mul_indicator {ι : Type} (s : Finset ι)
    (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (hU : IsFinTestFactor F
      (Set.indicator (glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))))
    (z : ι → AdelicGL2 (𝓞 F) F → ℂ) (fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : ∀ j, IsArchTestFactor F (fa j))
    (hz : ∀ j, ∀ g : AdelicGL2 (𝓞 F) F, z j g = fa j (glArch (𝓞 F) F g) *
      Set.indicator (glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))
        (glFin (𝓞 F) F g)) :
    IsFactorizableTestFn F (fun g => ∑ j ∈ s, z j g) :=
  ⟨fun x => ∑ j ∈ s, fa j x,
    Set.indicator (glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ)),
    isArchTestFactor_finsetSum F s fa hfa, hU, fun g => by simp only [hz, Finset.sum_mul]⟩

private theorem isFactorizableTestFn_finsetSum_of_forall_eq_mul_indicator_levelOne_inf {ι : Type} (s : Finset ι)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (hUN : U = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (z : ι → AdelicGL2 (𝓞 F) F → ℂ) (fa : ι → GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hfa : ∀ j, IsArchTestFactor F (fa j))
    (hz : ∀ j, ∀ g : AdelicGL2 (𝓞 F) F, z j g = fa j (glArch (𝓞 F) F g) *
      Set.indicator (glFin (𝓞 F) F '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))
        (glFin (𝓞 F) F g)) :
    IsFactorizableTestFn F (fun g => ∑ j ∈ s, z j g) := by
  subst hUN
  exact isFactorizableTestFn_finsetSum_of_forall_eq_mul_indicator F s _
    (isFinTestFactor_indicator_image_glFin_levelOne_inf F N hN) z fa hfa hz

end TestFnSums

end AutomorphicForm

/-! ### The isotypic transport engine

A type piece is the supremum of the nonzero intertwining ranges of the representation into right
translation, so an additive operator that commutes with right translation preserves any type piece
in which its input lies.  This is the engine of `rightConv_mem_archTypeSubmoduleAt_of_isLevelSphericalOfType`
and hence of the `archCut` side of the 650-row. -/

section IsotypicTransport

variable {H G : Type*} [Group H] [Group G]

private def rightTranslationRep (ι : H →* G) : Representation ℂ H (G → ℂ) where
  toFun k :=
    { toFun := fun f x => f (x * ι k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp
  map_mul' k₁ k₂ := by
    ext f x
    simp [mul_assoc]

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private def intertwiningOfEquivariant {ι : H →* G} {ρ : Representation ℂ H W} {T : W →ₗ[ℂ] (G → ℂ)}
    (hT : IsRightEquivariant ι ρ T) : ρ.IntertwiningMap (rightTranslationRep ι) where
  toLinearMap := T
  isIntertwining' k := by
    ext v x
    exact hT k v x

set_option backward.isDefEq.respectTransparency false in

private abbrev asModuleMap (ι : H →* G) (ρ : Representation ℂ H W)
    (φ : ρ.IntertwiningMap (rightTranslationRep ι)) :
    ρ.asModule →ₗ[MonoidAlgebra ℂ H] (rightTranslationRep ι).asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := rightTranslationRep ι) φ

set_option backward.isDefEq.respectTransparency false in

private def nonzeroRanges (ι : H →* G) (ρ : Representation ℂ H W) :
    Set (Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule) :=
  {m | ∃ φ : ρ.IntertwiningMap (rightTranslationRep ι), LinearMap.range (asModuleMap ι ρ φ) = m ∧ m ≠ ⊥}

set_option backward.isDefEq.respectTransparency false in

private theorem nonzeroRanges_equiv (ι : H →* G) (ρ : Representation ℂ H W) [ρ.IsIrreducible] :
    ∀ m ∈ nonzeroRanges ι ρ, Nonempty (m ≃ₗ[MonoidAlgebra ℂ H] ρ.asModule) := by
  rintro m ⟨φ, rfl, hm⟩
  rcases LinearMap.injective_or_eq_zero (asModuleMap ι ρ φ) with hinj | hzero
  · exact ⟨(LinearEquiv.ofInjective _ hinj).symm⟩
  · exact absurd (by rw [hzero, LinearMap.range_zero]) hm

set_option backward.isDefEq.respectTransparency false in

private theorem mem_sSup_nonzeroRanges (ι : H →* G) (ρ : Representation ℂ H W) {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) :
    (rightTranslationRep ι).asModuleEquiv.symm f ∈ sSup (nonzeroRanges ι ρ) := by
  refine Submodule.span_induction
    (p := fun f _ => (rightTranslationRep ι).asModuleEquiv.symm f ∈ sSup (nonzeroRanges ι ρ))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hle : LinearMap.range (asModuleMap ι ρ (intertwiningOfEquivariant hT))
        ≤ sSup (nonzeroRanges ι ρ) := by
      by_cases hbot : LinearMap.range (asModuleMap ι ρ (intertwiningOfEquivariant hT)) = ⊥
      · rw [hbot]
        exact bot_le
      · exact le_sSup ⟨intertwiningOfEquivariant hT, rfl, hbot⟩
    exact hle (LinearMap.mem_range_self (asModuleMap ι ρ (intertwiningOfEquivariant hT))
      (ρ.asModuleEquiv.symm v))
  · simp
  · intro _ _ _ _ hu hw
    rw [map_add]
    exact (sSup (nonzeroRanges ι ρ)).add_mem hu hw
  · intro c _ _ hu
    rw [Representation.asModuleEquiv_symm_map_smul]
    exact (sSup (nonzeroRanges ι ρ)).smul_mem _ hu

set_option backward.isDefEq.respectTransparency false in

private theorem isRightEquivariant_of_intertwining {ι : H →* G} {ρ : Representation ℂ H W}
    (ψ : ρ.IntertwiningMap (rightTranslationRep ι)) : IsRightEquivariant ι ρ ψ.toLinearMap := by
  intro k v x
  exact congrFun (LinearMap.congr_fun (ψ.isIntertwining' k) v) x

set_option backward.isDefEq.respectTransparency false in

private theorem exists_isRightEquivariant_of_simple_le (ι : H →* G) (ρ : Representation ℂ H W)
    [ρ.IsIrreducible]
    (m : Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule)
    [IsSimpleModule (MonoidAlgebra ℂ H) m]
    (hm : m ≤ sSup (nonzeroRanges ι ρ)) :
    ∃ T : W →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ T ∧
      (∀ v : W, (rightTranslationRep ι).asModuleEquiv.symm (T v) ∈ m) ∧
      ∀ g : (rightTranslationRep ι).asModule, g ∈ m → ∃ v : W, T v = (rightTranslationRep ι).asModuleEquiv g := by
  haveI : ∀ r : nonzeroRanges ι ρ, IsSimpleModule (MonoidAlgebra ℂ H) r :=
    fun r => IsSimpleModule.congr (nonzeroRanges_equiv ι ρ r r.2).some
  obtain ⟨r, hr, ⟨e₁⟩⟩ := Submodule.linearEquiv_of_le_sSup m (nonzeroRanges ι ρ) hm
  obtain ⟨e₂⟩ := nonzeroRanges_equiv ι ρ r hr
  let e : ρ.asModule ≃ₗ[MonoidAlgebra ℂ H] m := (e₁.trans e₂).symm
  let L : ρ.asModule →ₗ[MonoidAlgebra ℂ H] (rightTranslationRep ι).asModule := m.subtype ∘ₗ e.toLinearMap
  let ψ : ρ.IntertwiningMap (rightTranslationRep ι) :=
    (Representation.IntertwiningMap.equivLinearMapAsModule (ρ := ρ) (σ := rightTranslationRep ι)).symm L
  have hψ : ∀ v : W,
      ψ.toLinearMap v = (rightTranslationRep ι).asModuleEquiv (L (ρ.asModuleEquiv.symm v)) := fun _ => rfl
  refine ⟨ψ.toLinearMap, isRightEquivariant_of_intertwining ψ, fun v => ?_, fun g hg => ?_⟩
  · rw [hψ, LinearEquiv.symm_apply_apply]
    exact (e (ρ.asModuleEquiv.symm v)).2
  · refine ⟨ρ.asModuleEquiv (e.symm ⟨g, hg⟩), ?_⟩
    have h : L (e.symm ⟨g, hg⟩) = g := by
      show ((e (e.symm ⟨g, hg⟩) : m) : (rightTranslationRep ι).asModule) = g
      rw [LinearEquiv.apply_symm_apply]
    rw [hψ, LinearEquiv.symm_apply_apply, h]

private theorem asAlgebraHom_mem (ι : H →* G) (P : Set (G → ℂ))
    (hP_tr : ∀ (k : H), ∀ f ∈ P, (fun x => f (x * ι k)) ∈ P) (hP_add : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P)
    (hP_smul : ∀ (c : ℂ), ∀ f ∈ P, c • f ∈ P) (r : MonoidAlgebra ℂ H) {f : G → ℂ} (hf : f ∈ P) :
    (rightTranslationRep ι).asAlgebraHom r f ∈ P := by
  refine MonoidAlgebra.induction_on (motive := fun r => (rightTranslationRep ι).asAlgebraHom r f ∈ P) r
    (fun k => ?_) (fun r₁ r₂ h₁ h₂ => ?_) (fun c r h => ?_)
  · show (rightTranslationRep ι).asAlgebraHom (MonoidAlgebra.of ℂ H k) f ∈ P
    rw [Representation.asAlgebraHom_of]
    exact hP_tr k f hf
  · show (rightTranslationRep ι).asAlgebraHom (r₁ + r₂) f ∈ P
    rw [map_add, LinearMap.add_apply]
    exact hP_add _ h₁ _ h₂
  · show (rightTranslationRep ι).asAlgebraHom (c • r) f ∈ P
    rw [map_smul, LinearMap.smul_apply]
    exact hP_smul c _ h

private theorem isSemisimpleModule_of_le {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {N Q : Submodule R M} [IsSemisimpleModule R Q] (h : N ≤ Q) : IsSemisimpleModule R N :=
  IsSemisimpleModule.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective _)

private theorem induction_of_isSemisimpleModule {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (N : Submodule R V) [IsSemisimpleModule R N] {motive : V → Prop}
    (hsimple : ∀ m : Submodule R V, IsSimpleModule R m → m ≤ N → ∀ y ∈ m, motive y) (hzero : motive 0)
    (hadd : ∀ y₁ y₂ : V, y₁ ∈ N → y₂ ∈ N → motive y₁ → motive y₂ → motive (y₁ + y₂))
    {x : V} (hx : x ∈ N) : motive x := by
  have hmem : (⟨x, hx⟩ : N) ∈ sSup {m : Submodule R N | IsSimpleModule R m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    exact Submodule.mem_top
  rw [sSup_eq_iSup'] at hmem
  refine Submodule.iSup_induction (motive := fun y : N => motive (y : V)) _ hmem ?_ ?_ ?_
  · rintro ⟨m, hm⟩ y hy
    haveI : IsSimpleModule R m := hm
    change y ∈ m at hy
    exact hsimple (m.map N.subtype)
      (IsSimpleModule.congr (Submodule.equivMapOfInjective N.subtype N.injective_subtype m).symm)
      (Submodule.map_subtype_le (p := N) m) (y : V) (Submodule.mem_map_of_mem hy)
  · exact hzero
  · intro y₁ y₂ h₁ h₂
    exact hadd (y₁ : V) (y₂ : V) y₁.2 y₂.2 h₁ h₂

set_option backward.isDefEq.respectTransparency false in

private theorem map_mem_typeSubmodule (ι : H →* G) (ρ : Representation ℂ H W) [ρ.IsIrreducible]
    (P : Set (G → ℂ)) (hP_tr : ∀ (k : H), ∀ f ∈ P, (fun x => f (x * ι k)) ∈ P)
    (hP_add : ∀ f ∈ P, ∀ g ∈ P, f + g ∈ P) (hP_smul : ∀ (c : ℂ), ∀ f ∈ P, c • f ∈ P)
    (A : (G → ℂ) → (G → ℂ)) (hA_add : ∀ f ∈ P, ∀ g ∈ P, A (f + g) = A f + A g)
    (hA_smul : ∀ (c : ℂ) (f : G → ℂ), A (c • f) = c • A f) (hA_zero : A 0 = 0)
    (hA_tr : ∀ (k : H) (f : G → ℂ), A (fun x => f (x * ι k)) = fun x => A f (x * ι k))
    {f : G → ℂ} (hfP : f ∈ P) (hf : f ∈ typeSubmodule ι ρ) : A f ∈ typeSubmodule ι ρ := by
  haveI simple_ranges : ∀ r : nonzeroRanges ι ρ, IsSimpleModule (MonoidAlgebra ℂ H) r :=
    fun r => IsSimpleModule.congr (nonzeroRanges_equiv ι ρ r r.2).some
  haveI hsemi : IsSemisimpleModule (MonoidAlgebra ℂ H) ↥(sSup (nonzeroRanges ι ρ)) := by
    rw [sSup_eq_iSup]
    exact isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
      (p := fun m : Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule => m)
      (fun m hm => by
        haveI := simple_ranges ⟨m, hm⟩
        exact inferInstance)
  set f' : (rightTranslationRep ι).asModule := (rightTranslationRep ι).asModuleEquiv.symm f with hf'
  let N : Submodule (MonoidAlgebra ℂ H) (rightTranslationRep ι).asModule :=
    Submodule.span (MonoidAlgebra ℂ H) {f'}
  have hNQ : N ≤ sSup (nonzeroRanges ι ρ) :=
    Submodule.span_le.2 (Set.singleton_subset_iff.2 (mem_sSup_nonzeroRanges ι ρ hf))
  have hNP : ∀ g ∈ N, (rightTranslationRep ι).asModuleEquiv g ∈ P := by
    intro g hg
    refine Submodule.span_induction (p := fun g _ => (rightTranslationRep ι).asModuleEquiv g ∈ P) ?_ ?_ ?_ ?_ hg
    · intro g hg
      rcases Set.mem_singleton_iff.1 hg with rfl
      show (rightTranslationRep ι).asModuleEquiv f' ∈ P
      rw [hf', LinearEquiv.apply_symm_apply]
      exact hfP
    · simpa using hP_smul (0 : ℂ) f hfP
    · intro _ _ _ _ h₁ h₂
      rw [map_add]
      exact hP_add _ h₁ _ h₂
    · intro r _ _ h
      rw [Representation.asModuleEquiv_map_smul]
      exact asAlgebraHom_mem ι P hP_tr hP_add hP_smul r h
  haveI hNsemi : IsSemisimpleModule (MonoidAlgebra ℂ H) N := isSemisimpleModule_of_le hNQ
  have hind : A ((rightTranslationRep ι).asModuleEquiv f') ∈ typeSubmodule ι ρ := by
    refine induction_of_isSemisimpleModule N
      (motive := fun g => A ((rightTranslationRep ι).asModuleEquiv g) ∈ typeSubmodule ι ρ) ?_ ?_ ?_
      (Submodule.mem_span_singleton_self f')
    · intro m hm hmN y hy
      haveI : IsSimpleModule (MonoidAlgebra ℂ H) m := hm
      obtain ⟨T, hT, hTm, hsurj⟩ := exists_isRightEquivariant_of_simple_le ι ρ m (hmN.trans hNQ)
      obtain ⟨v, hv⟩ := hsurj y hy
      show A ((rightTranslationRep ι).asModuleEquiv y) ∈ typeSubmodule ι ρ
      rw [← hv]
      have hTP : ∀ u : W, T u ∈ P := fun u => by
        have h := hNP _ (hmN (hTm u))
        rwa [LinearEquiv.apply_symm_apply] at h
      let TA : W →ₗ[ℂ] (G → ℂ) :=
        { toFun := fun u => A (T u)
          map_add' := fun u u' => by
            show A (T (u + u')) = A (T u) + A (T u')
            rw [map_add, hA_add _ (hTP u) _ (hTP u')]
          map_smul' := fun c u => by
            show A (T (c • u)) = c • A (T u)
            rw [map_smul, hA_smul] }
      have hTA : IsRightEquivariant ι ρ TA := by
        intro k u x
        show A (T (ρ k u)) x = A (T u) (x * ι k)
        rw [show T (ρ k u) = fun y => T u (y * ι k) from funext (hT k u), hA_tr k (T u)]
      exact mem_typeSubmodule_of_isRightEquivariant hTA v
    · show A ((rightTranslationRep ι).asModuleEquiv 0) ∈ typeSubmodule ι ρ
      rw [map_zero, hA_zero]
      exact Submodule.zero_mem _
    · intro y₁ y₂ hy₁ hy₂ h₁ h₂
      show A ((rightTranslationRep ι).asModuleEquiv (y₁ + y₂)) ∈ typeSubmodule ι ρ
      rw [map_add, hA_add _ (hNP _ hy₁) _ (hNP _ hy₂)]
      exact Submodule.add_mem _ h₁ h₂
  rwa [hf', LinearEquiv.apply_symm_apply] at hind

end IsotypicTransport

/-! ### The arch-type piece of a right convolution

Right convolution by a test function of level-spherical type at `σ` lands in `σ`'s type piece; and a
right convolution by a test function of type `τ` lands in `τ`'s arch cut.  Together they let the
650-row prove that the translates belonging to *different* irreducible pieces annihilate each other
(`rightConv_eq_zero_of_isEmpty_equiv`). -/

private theorem AutomorphicForm.rightConv_mem_archTypeSubmoduleAt_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (σ : ArchRepAt F w) [σ.ρ.IsIrreducible]
    (tys : ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F)) (z : AdelicGL2 (𝓞 F) F → ℂ)
    (hzT : IsFactorizableTestFn F z) (hz : IsLevelSphericalOfType F tys U z)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ : φ ∈ archTypeSubmoduleAt F w σ) :
    rightConv F φ z ∈ archTypeSubmoduleAt F w σ := by
  obtain ⟨hzc, hzs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F z hzT
  show rightConv F φ z ∈ typeSubmodule (rowIsometryInclAt₀ F w) σ.ρ
  refine map_mem_typeSubmodule (rowIsometryInclAt₀ F w) σ.ρ {u : AdelicGL2 (𝓞 F) F → ℂ | Continuous u}
    (fun k u hu => (hu : Continuous u).comp (continuous_id.mul continuous_const))
    (fun u hu u' hu' => (hu : Continuous u).add hu') (fun c u hu => (hu : Continuous u).const_smul c)
    (fun u => rightConv F u z) (fun u hu u' hu' => rightConv_add_left F hu hu' hzc hzs)
    (fun c u => convOp_smul F z c u) (rightConv_zero_left F z) (fun k u => ?_) hφc hφ
  exact (rightTranslate_rightConv_of_isLevelSphericalOfType F tys U z hz w k u).symm

private theorem mem_archTypeSubmoduleAt_of_mem_archCutSubmodule_single (F : Type) [Field F]
    [NumberField F] (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (w : InfinitePlace F)
    {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : f ∈ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F)) :
    f ∈ archTypeSubmoduleAt F w (τ w) := by
  have h1 := (mem_archCutSubmodule_iff F _ f).1 hf w
  have h2 : (⨆ i : Fin ((⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F).card w),
      archTypeSubmoduleAt F w ((⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F).rep w i)) ≤
        archTypeSubmoduleAt F w (τ w) :=
    iSup_le fun _ => le_rfl
  exact h2 h1

private theorem AutomorphicForm.rightConv_eq_zero_of_isEmpty_equiv
    (F : Type) [Field F] [NumberField F]
    (σ τ : ∀ w : InfinitePlace F, ArchRepAt F w) (w₀ : InfinitePlace F)
    (hσ : (σ w₀).ρ.IsIrreducible) (hτ : (τ w₀).ρ.IsIrreducible)
    (hne : IsEmpty ((σ w₀).ρ.Equiv ((τ w₀).ρ)))
    (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (z : AdelicGL2 (𝓞 F) F → ℂ) (hzT : IsFactorizableTestFn F z)
    (hz : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) U z)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ)
    (hφ : φ ∈ archCutSubmodule F (⟨fun _ => 1, fun w _ => σ w⟩ : ArchTypeFamily F)) :
    rightConv F φ z = 0 := by
  have hz' := hz
  obtain ⟨fa, -, hB, -, hfeq⟩ := hz'
  have hbi : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) z :=
    IsArchBiFinite.of_factorization F hfeq hB
  have hτcut : rightConv F φ z ∈ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : ArchTypeFamily F) :=
    rightConv_mem_archCutSubmodule_of_isArchBiFinite F _ φ hφc z hzT hbi
  have hτpiece : rightConv F φ z ∈ archTypeSubmoduleAt F w₀ (τ w₀) :=
    mem_archTypeSubmoduleAt_of_mem_archCutSubmodule_single F τ w₀ hτcut
  haveI := hσ
  have hσpiece : rightConv F φ z ∈ archTypeSubmoduleAt F w₀ (σ w₀) :=
    rightConv_mem_archTypeSubmoduleAt_of_isLevelSphericalOfType F w₀ (σ w₀) _ U z hzT hz φ hφc
      (mem_archTypeSubmoduleAt_of_mem_archCutSubmodule_single F σ w₀ hφ)
  haveI := hτ
  have hmeet : rightConv F φ z ∈ typeSubmodule (rowIsometryInclAt₀ F w₀) (σ w₀).ρ ⊓
      typeSubmodule (rowIsometryInclAt₀ F w₀) (τ w₀).ρ :=
    Submodule.mem_inf.2 ⟨hσpiece, hτpiece⟩
  rw [typeSubmodule_inf_typeSubmodule_eq_bot (rowIsometryInclAt₀ F w₀) (σ w₀).ρ (τ w₀).ρ hne] at hmeet
  exact (Submodule.mem_bot ℂ).1 hmeet

/-! ### The constituent's own pieces -/

namespace EigenCapture

variable (F : Type) [Field F] [NumberField F]

private def piece (pins : CarrierPins F) (N : Ideal (𝓞 F)) (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (κ : ∀ w : InfinitePlace F, ArchRepAt F w) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  V ⊓ levelInvariantSubmodule F pins N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => κ w⟩ : ArchTypeFamily F)

private theorem piece_congr (pins : CarrierPins F) (N : Ideal (𝓞 F))
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) {κ κ' : ∀ w : InfinitePlace F, ArchRepAt F w}
    (e : ∀ w, (κ w).ρ.Equiv (κ' w).ρ) : piece F pins N V κ = piece F pins N V κ' := by
  unfold piece
  rw [archCutSubmodule_eq_of_forall_equiv F e]

private theorem mem_inf_inf {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q r : Submodule R M} {x : M} : x ∈ p ⊓ q ⊓ r ↔ (x ∈ p ∧ x ∈ q) ∧ x ∈ r :=
  Iff.rfl

end EigenCapture

open EigenCapture in

theorem AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hX : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≠ ⊥) :
    ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (_ : IsFactorizableTestFn F f) (n : ℕ) (lam : Fin n → ℂ)
      (_ : ∀ i, lam i ≠ 0) (E : Fin n → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ i, ∀ φ ∈ E i, φ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ∧ rightConv F φ f = lam i • φ) ∧
      V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ ⨆ i, E i := by
  have _ := hX
  classical
  obtain ⟨σ, hσ⟩ := exists_hasModulus_of_isCuspConstituent F c u d₁ d₂ T ξ V hV
  obtain ⟨m, τs, hirr, hsplit⟩ :=
    exists_inf_archCutSubmodule_le_iSup_isIrreducible_of_isCuspSubrep F c u d₁ d₂ T ξ N tys V hV.1

  let X : Fin m → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := fun j =>
    piece F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N V (τs j)
  let P : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) := (Finset.univ.filter fun j => X j ≠ ⊥).image X
  have hP : ∀ p ∈ P, ∃ j, X j ≠ ⊥ ∧ X j = p := fun p hp => by
    obtain ⟨j, hj, hjp⟩ := Finset.mem_image.mp hp
    exact ⟨j, (Finset.mem_filter.mp hj).2, hjp⟩
  choose idx hidx_ne hidx_eq using hP

  choose z hzT hzsph hzflat _hzpres hzne using fun k : Fin P.card =>
    exists_rightConv_ne_zero_of_ne_bot F c u d₁ d₂ T ξ σ hσ N hN
      (τs (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2))
      (hirr (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2)) V hV
      (hidx_ne (P.equivFin.symm k).1 (P.equivFin.symm k).2)
  choose lam hlam using fun k : Fin P.card =>
    exists_real_forall_rightConv_eq_smul_of_isLevelSphericalOfType F c u d₁ d₂ T hc hd₁ hd hcov ξ σ hσ N hN
      (τs (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2))
      (hirr (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2)) V hV (z k) (hzT k) (hzsph k)
      (hzflat k)
  choose fa hfa _hfaB _hfaconj hfac using fun k : Fin P.card => hzsph k
  have hzc : ∀ k, Continuous (z k) ∧ HasCompactSupport (z k) := fun k =>
    continuous_and_hasCompactSupport_of_isFactorizableTestFn F (z k) (hzT k)

  have hlam0 : ∀ k, (lam k : ℂ) ≠ 0 := fun k h0 => by
    obtain ⟨φ₀, hφ₀, hne0⟩ := hzne k
    exact hne0 (by rw [hlam k φ₀ hφ₀, h0, zero_smul])

  have hsep : ∀ k k' : Fin P.card, k' ≠ k →
      ∃ w₀, IsEmpty ((τs (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2) w₀).ρ.Equiv
        ((τs (idx (P.equivFin.symm k').1 (P.equivFin.symm k').2) w₀).ρ)) := by
    intro k k' hk'
    by_contra hno
    apply hk'
    have hall : ∀ w₀, Nonempty ((τs (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2) w₀).ρ.Equiv
        ((τs (idx (P.equivFin.symm k').1 (P.equivFin.symm k').2) w₀).ρ)) :=
      fun w₀ => not_isEmpty_iff.mp fun h => hno ⟨w₀, h⟩
    have hXX : X (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2) =
        X (idx (P.equivFin.symm k').1 (P.equivFin.symm k').2) :=
      piece_congr F _ N V fun w₀ => (hall w₀).some
    exact (P.equivFin.symm.injective (Subtype.ext
      (((hidx_eq _ _).symm.trans hXX).trans (hidx_eq _ _)))).symm

  have hact : ∀ k, ∀ φ ∈ X (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2),
      rightConv F φ (fun g => ∑ k' ∈ Finset.univ, z k' g) = (lam k : ℂ) • φ := by
    intro k φ hφ
    have hφV : φ ∈ V := (mem_inf_inf.mp hφ).1.1
    have hφc : Continuous φ :=
      AutomorphicForm.CuspidalConstituent.continuous_of_mem_cuspKFiniteSubmodule F _ ξ (hV.1.le hφV)
    rw [rightConv_finsetSum_right F Finset.univ hφc z hzc]
    funext g
    have hvan : ∀ k' ∈ Finset.univ, k' ≠ k → rightConv F φ (z k') g = 0 := by
      intro k' _ hk'
      obtain ⟨w₀, hw₀⟩ := hsep k k' hk'
      rw [rightConv_eq_zero_of_isEmpty_equiv F _ _ w₀ (hirr _ w₀) (hirr _ w₀) hw₀ _ (z k') (hzT k') (hzsph k')
        φ hφc (mem_inf_inf.mp hφ).2]
      rfl
    rw [Finset.sum_eq_single k hvan (fun h => absurd (Finset.mem_univ k) h), hlam k φ hφ]

  have hfT : IsFactorizableTestFn F (fun g => ∑ k ∈ Finset.univ, z k g) :=
    isFactorizableTestFn_finsetSum_of_forall_eq_mul_indicator_levelOne_inf F Finset.univ N hN _ rfl z fa hfa hfac

  have hdom : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤
      ⨆ k : Fin P.card, X (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2) := by
    refine hsplit.trans (iSup_le fun j => ?_)
    by_cases hj : X j = ⊥
    · exact (le_of_eq hj).trans bot_le
    · have hp : X j ∈ P := Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩, rfl⟩
      refine le_iSup_of_le (P.equivFin ⟨X j, hp⟩) (le_of_eq ?_)
      exact ((hidx_eq _ _).trans (congrArg Subtype.val (P.equivFin.symm_apply_apply ⟨X j, hp⟩))).symm
  exact ⟨fun g => ∑ k ∈ Finset.univ, z k g, hfT, P.card, fun k => (lam k : ℂ), hlam0,
    fun k => X (idx (P.equivFin.symm k).1 (P.equivFin.symm k).2),
    fun k φ hφ => ⟨hV.1.le (mem_inf_inf.mp hφ).1.1, hact k φ hφ⟩, hdom⟩

/-! ## Row 2 — an irreducible closed cuspidal subrepresentation maps its own intersection -/

section JoinOfFamilies

variable (F : Type) [Field F]

private def archTypeFamilyJoin (t₁ t₂ : ArchTypeFamily F) : ArchTypeFamily F where
  card := fun w => t₁.card w + t₂.card w
  rep := fun w => Fin.append (t₁.rep w) (t₂.rep w)

private theorem isContainedIn_archTypeFamilyJoin_left (t₁ t₂ : ArchTypeFamily F) :
    ArchTypeFamily.IsContainedIn F t₁ (archTypeFamilyJoin F t₁ t₂) :=
  fun w i => ⟨Fin.castAdd (t₂.card w) i, Fin.append_left (t₁.rep w) (t₂.rep w) i⟩

private theorem isContainedIn_archTypeFamilyJoin_right (t₁ t₂ : ArchTypeFamily F) :
    ArchTypeFamily.IsContainedIn F t₂ (archTypeFamilyJoin F t₁ t₂) :=
  fun w i => ⟨Fin.natAdd (t₁.card w) i, Fin.append_right (t₁.rep w) (t₂.rep w) i⟩

end JoinOfFamilies

variable (F : Type) [Field F] [NumberField F]

private theorem exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F)
    (ξ : pins.Z →* ℂˣ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) :
    ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys := by
  refine Submodule.span_induction
    (p := fun φ _ => ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨-, -, tys, htys⟩
    exact ⟨tys, htys⟩
  · exact ⟨⟨fun _ => 0, fun _ i => Fin.elim0 i⟩, (archCutSubmodule F _).zero_mem⟩
  · rintro u v _ _ ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    exact ⟨archTypeFamilyJoin F t₁ t₂,
      (archCutSubmodule F _).add_mem
        (archCutSubmodule_mono F (isContainedIn_archTypeFamilyJoin_left F t₁ t₂) h₁)
        (archCutSubmodule_mono F (isContainedIn_archTypeFamilyJoin_right F t₁ t₂) h₂)⟩
  · rintro c u _ ⟨t, ht⟩
    exact ⟨t, (archCutSubmodule F t).smul_mem c ht⟩

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYc : Y ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hYM : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ Y), toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hYc hψ⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F tys)
    (L : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hL : IsClosed (L : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hLk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L),
        rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L))
    (hLhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L) ⊓ Representation.invariants ((rightRegular F).comp U.subtype),
        (fun x => ∑ i, φ (x * reps i)) ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L))
    (hLconv : ∀ h : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F h → IsArchBiFinite F tys h →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, h (u * x) = h x ∧ h (x * u) = h x) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L), rightConv F φ h ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L)) :
    Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ⊓ L = ⊥ ∨
      Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ≤ L := by
  classical
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier; exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set pins : CarrierPins F := fdPins F Φ₀ with hpins
  set Lf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L) with hLf
  have memLf : ∀ {φ : AdelicGL2 (𝓞 F) F → ℂ}, φ ∈ Lf ↔
      ∃ hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ ∈ L := by
    intro φ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩; exact ⟨ψ.2, by simpa using hψ⟩
    · rintro ⟨hφ, hl⟩; exact ⟨⟨φ, hφ⟩, hl, rfl⟩
  set LU : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Representation.invariants ((rightRegular F).comp U.subtype) with hLU
  have memLU : ∀ {φ : AdelicGL2 (𝓞 F) F → ℂ}, φ ∈ LU ↔ ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x := by
    intro φ
    rw [hLU, Representation.mem_invariants]
    constructor
    · intro h x u hu; exact congrFun (h ⟨u, hu⟩) x
    · intro h u; funext x; exact h x u u.2
  set A : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := archCutSubmodule F tys with hA

  set VM : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := cuspKFiniteSubmodule F pins ξ ⊓
    Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) M) with hVM
  have hVM : IsCuspSubrep F pins ξ VM :=
    AutomorphicForm.CuspidalSpectrum.isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
      F hΦ₀ σ ξ hσ M hM.1
  have hKFm : cuspKFiniteSubmodule F pins ξ ≤ cuspMemberSubmodule F Φ₀ ξ := by
    refine Submodule.span_le.mpr ?_
    rintro φ ⟨hsat, hcont, -⟩
    have h1 := hsat 1
    have : rightTranslate F 1 φ = φ := by funext x; simp [rightTranslate]
    rw [this] at h1
    exact ⟨h1, hcont⟩
  have hYVM : Y ≤ VM := by
    intro y hy
    refine ⟨Submodule.subset_span ⟨fun g => ?_, (hYc hy).2, tys, hYt hy⟩, ⟨⟨y, hYc hy⟩, hYM y hy, rfl⟩⟩
    exact (AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g y (hYc hy)).1
  have hYLU : Y ≤ LU := fun y hy => memLU.mpr (hYU y hy)

  let p : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) → Prop := fun W => IsCuspSubrep F pins ξ W ∧ VM ⊓ LU ⊓ A ⊓ Lf ≤ W
  set W₀ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := ⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : p W), W with hW₀
  have hpVM : p VM := ⟨hVM, fun φ hφ => hφ.1.1.1⟩
  have hW₀ : IsCuspSubrep F pins ξ W₀ :=
    AutomorphicForm.CuspidalConstituent.Spine.isCuspSubrep_iInf₂ (pins := pins) (ξ := ξ)
      (fun W hW => hW.1) hpVM
  have hW₀VM : W₀ ≤ VM := iInf₂_le VM hpVM
  have hZW₀ : VM ⊓ LU ⊓ A ⊓ Lf ≤ W₀ := le_iInf₂ fun W hW => hW.2
  have hW₀m : W₀ ≤ cuspMemberSubmodule F Φ₀ ξ := hW₀VM.trans (hVM.le.trans hKFm)

  have hcut : W₀ ⊓ LU ⊓ A ≤ Lf :=
    AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le F Φ₀ ξ U hU O hO hUO tys
      VM hVM Lf hLk hLhecke hLconv

  set N : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    (Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ)
      (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W₀)).topologicalClosure with hN
  have hNc : IsClosedCuspSubrep F hΦ₀ σ ξ N :=
    AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep F hΦ₀ σ ξ W₀ hW₀
  have hNM : N ≤ M := by
    rw [hN]
    refine Submodule.topologicalClosure_minimal _ ?_ hM.1.isClosed
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨-, ⟨m, hm, hmw⟩⟩ := hW₀VM hw
    have : m = w := Subtype.ext hmw
    rw [this] at hm
    exact hm
  rcases hM.2.2 N hNc hNM with h0 | hNM'
  ·
    left
    rw [eq_bot_iff]
    rintro v ⟨⟨y, -, rfl⟩, hvL⟩
    have hyLf : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ Lf := memLf.mpr ⟨hYc y.2, hvL⟩
    have hyW₀ : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ W₀ := hZW₀ ⟨⟨⟨hYVM y.2, hYLU y.2⟩, hYt y.2⟩, hyLf⟩
    have hvN : (toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc) y ∈ N := by
      rw [hN]
      exact Submodule.le_topologicalClosure _ ⟨⟨y, hYc y.2⟩, hyW₀, rfl⟩
    rw [h0, Submodule.mem_bot] at hvN
    rw [Submodule.mem_bot]
    exact hvN
  ·
    right
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨P, -, -, hPid, hPcut, -⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact F hΦ₀ σ ξ hσ U hU O hO hUO tys
    set v := (toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc) y with hv
    have hvdef : v = toCuspSubcarrier F hΦ₀ σ ξ ⟨y, hYc y.2⟩ := rfl
    have hPv : P v = v := by rw [hvdef]; exact hPid y (hYc y.2) (hYU y y.2) (hYt y.2)
    have hvM : v ∈ M := by rw [hvdef]; exact hYM y y.2

    have hPW₀ : ∀ x ∈ Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ) (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W₀),
        P x ∈ L := by
      rintro _ ⟨w, hw, rfl⟩
      have hwK : (w : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspKFiniteSubmodule F pins ξ := hVM.le (hW₀VM hw)
      obtain ⟨tys', htys'⟩ := exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule F pins ξ hwK
      obtain ⟨w', hw'm, hw'U, hw't, hw'V, hPw⟩ := hPcut w w.2 ⟨tys', htys'⟩
      have hw'W₀ : w' ∈ W₀ := hw'V W₀ hW₀.rightTranslate_fin_mem hW₀.rightTranslate_arch_mem hw
      have hw'Lf : w' ∈ Lf := hcut ⟨⟨hw'W₀, memLU.mpr hw'U⟩, hw't⟩
      obtain ⟨hm', hl'⟩ := memLf.mp hw'Lf
      have : toCuspSubcarrier F hΦ₀ σ ξ w = toCuspSubcarrier F hΦ₀ σ ξ ⟨w, w.2⟩ := rfl
      rw [this, hPw]
      exact hl'

    have hPN : ∀ x ∈ N, P x ∈ L := by
      intro x hx
      rw [hN] at hx
      have hcl : (P : ↥(cuspSubcarrier F hΦ₀ σ ξ) → ↥(cuspSubcarrier F hΦ₀ σ ξ)) ''
          closure ((Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ) (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W₀)) : Set _) ⊆
          closure (L : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
        refine (image_closure_subset_closure_image P.continuous).trans (closure_mono ?_)
        rintro _ ⟨z, hz, rfl⟩
        exact hPW₀ z hz
      have := hcl ⟨x, by rwa [← Submodule.topologicalClosure_coe], rfl⟩
      rwa [hL.closure_eq] at this
    have := hPN v (hNM' ▸ hvM)
    rwa [hPv] at this

end
