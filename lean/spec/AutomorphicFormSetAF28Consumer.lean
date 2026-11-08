/-
  Cross-module wire test for SET-AF28 (the left Casimir acting on factorizable test functions).

  A `spec/` probe, not a library module. Three composition zones, each one *consuming* a headline of
  `AutomorphicForm/Adelic/LeftCasimirTestFn.lean` (or a helper it carries) instead of restating it:

  * **Zone 1 (the level invariant read off the headline's third conjunct).** At `K = ℚ`, the
    degenerate test function `α = 0` and the char-family `ArchTypeFamily.ofChar 1`, the headline's
    third conjunct is applied at `x'` and split with `Submodule.mem_inf`: its level half is read as
    the invariance `rightConv x' β (g * u) = rightConv x' β g` for `u` in the level-`N` congruence
    subgroup, its archimedean half as a membership of `archCutSubmodule ℚ tys`. The level half is then
    *re-derived* from the module's own
    `rightConv_mem_levelInvariantSubmodule_of_left_inv` fed with
    `leftCasimir_left_inv` at `α = 0`, so the zone joins three declarations, not one.

  * **Zone 2 (the eigenvalue transfer at degenerate data, pin 412).**
    `exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul` is
    instantiated at `lam = 0`, `φ = 0` and `f = 0`: every hypothesis is discharged here (`φ = 0` is
    continuous and in the cut, `f = 0` is factorizable, and the eigenvalue equation is
    `rightConv 0 0 = 0`), and the existential's witness is read back through `rightConv_zero_left`.

  * **Zone 3 (the complex headline's list conjunct).** The complex-place headline carries
    `∀ l : List ArchDirComplex, IsFactorizableTestFn K (l.foldr L α)`; the zone consumes it at
    `l = []` and `l = [.H, .iH]`, where the list fold is the identity and a single left-flow
    derivative.

  It imports the module it consumes plus nothing else: the headline's own hypotheses
  (`IsArchBiFinite ℚ tys 0`, the left invariance of `0`, `rightConv 0 0 = 0 • 0`) are all discharged
  from the module's `isArchBiFinite_zero`/`isFactorizableTestFn_zero`/`rightConv_zero_left`.
-/
import FLTForHuman.AutomorphicForm.Adelic.LeftCasimirTestFn

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open AutomorphicForm
open NumberField.AdelicBox IsDedekindDomain Filter
open AutomorphicForm.CuspidalConstituent
open scoped ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar
attribute [local instance] NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar

namespace SetAF28Consumer

/-- The trivial archimedean type family at `ℚ`: the character family of the trivial character. -/
def tysQ : ArchTypeFamily ℚ := ArchTypeFamily.ofChar ℚ (fun _ => 1)

/-- The production pins at `ℚ` with `D = univ` and `N = ⊥`. -/
def pinsQ : CarrierPins ℚ :=
  productionPinsOf ℚ Set.univ
    (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)

/-- The left flow derivative at the real place `w` of `ℚ`, the pin's `L`. -/
def LQ {w : InfinitePlace ℚ} (hw : w.IsReal) (d : ArchDir) (γ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  fun y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0

/-- The left Casimir of the zero test function, the `β` of the headline's `let`. -/
def βQ {w : InfinitePlace ℚ} (hw : w.IsReal) : AdelicGL2 (𝓞 ℚ) ℚ → ℂ :=
  fun y => -((1 / 4 : ℂ) * LQ hw .H (LQ hw .H 0) y - (1 / 2 : ℂ) * LQ hw .H 0 y +
    LQ hw .E (LQ hw .Fm 0) y)

/-! ## Zone 1: the level invariant read off the headline's third conjunct -/

/-- `βQ` is invariant under the left action of the level-`N` congruence subgroup, the input the
module's `rightConv_mem_levelInvariantSubmodule_of_left_inv` needs; it is
`leftCasimir_left_inv` at `α = 0`. -/
theorem βQ_left_inv {w : InfinitePlace ℚ} (hw : w.IsReal) (N : Ideal (𝓞 ℚ)) :
    ∀ k ∈ (levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ), ∀ y : AdelicGL2 (𝓞 ℚ) ℚ,
      βQ hw (k * y) = βQ hw y :=
  LeftCasimirReal.leftCasimir_left_inv hw N 0 (fun _ _ _ => ⟨rfl, rfl⟩)

/-- **Zone 1a.** The level half, re-derived from the module's own membership lemma and the
left-invariance of the Casimir: right convolution by `βQ` is invariant under the level-`N`
congruence subgroup. -/
theorem zone1a {w : InfinitePlace ℚ} (hw : w.IsReal) (N : Ideal (𝓞 ℚ))
    (x' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    rightConv ℚ x' (βQ hw) ∈ levelInvariantSubmodule ℚ pinsQ N :=
  LeftCasimirShared.rightConv_mem_levelInvariantSubmodule_of_left_inv Set.univ N (βQ hw)
    (βQ_left_inv hw N) x'

/-- **Zone 1b.** The headline's third conjunct at `α = 0`: right convolution by the left Casimir of
the zero test function stays in `levelInvariantSubmodule ⊓ archCutSubmodule`, and its archimedean
half is read as a membership of the cut. -/
theorem zone1b {w : InfinitePlace ℚ} (hw : w.IsReal) (N : Ideal (𝓞 ℚ))
    (x' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hx' : Continuous x')
    (hx'L : x' ∈ levelInvariantSubmodule ℚ pinsQ N) (hx'A : x' ∈ archCutSubmodule ℚ tysQ) :
    rightConv ℚ x' (βQ hw) ∈ archCutSubmodule ℚ tysQ :=
  (Submodule.mem_inf.mp
    ((isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite ℚ Set.univ w hw N tysQ 0
      (isFactorizableTestFn_zero ℚ) (isArchBiFinite_zero ℚ tysQ)
      (fun _ _ _ => ⟨rfl, rfl⟩)).2.2 x' hx' hx'L hx'A)).2

/-- **Zone 1c.** The two halves joined by `Submodule.mem_inf`: the intersection membership of the
headline's third conjunct, read at `g` and `u`. -/
theorem zone1c {w : InfinitePlace ℚ} (hw : w.IsReal) (N : Ideal (𝓞 ℚ))
    (x' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hx' : Continuous x')
    (hx'L : x' ∈ levelInvariantSubmodule ℚ pinsQ N) (hx'A : x' ∈ archCutSubmodule ℚ tysQ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : AdelicGL2 (𝓞 ℚ) ℚ)
    (hu : u ∈ (levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)) :
    rightConv ℚ x' (βQ hw) (g * u) = rightConv ℚ x' (βQ hw) g :=
  (Submodule.mem_inf.mpr ⟨zone1a hw N x', zone1b hw N x' hx' hx'L hx'A⟩).1 g u hu

/-! ## Zone 2: the eigenvalue transfer at `lam = 0`, `φ = 0`, `f = 0` -/

/-- **Zone 2.** The eigenvalue lemma of pin 412 at degenerate data: an eigenfunction of
`rightConv · 0` is an eigenfunction of `rightConv · f'` for a factorizable, arch-bi-finite `f'`. -/
theorem zone2 :
    ∃ f' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ f' ∧ IsArchBiFinite ℚ tysQ f' ∧
      rightConv ℚ (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) f' = (0 : ℂ) • (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :=
  exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul ℚ tysQ 0
    continuous_const (Submodule.zero_mem _) 0 (isFactorizableTestFn_zero ℚ) 0
    (by
      show rightConv ℚ (fun _ => 0) (fun _ => 0) = (0 : ℂ) • (fun _ => 0)
      rw [rightConv_zero_left, zero_smul]
      rfl)

/-- **Zone 2b.** The witness of zone 2 is annihilated by the zero test function as well: the
eigenvalue equation it satisfies is the trivial one. -/
theorem zone2b (f' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    rightConv ℚ (0 : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) f' = fun _ => 0 :=
  rightConv_zero_left ℚ f'

/-! ## Zone 3: the complex headline's list conjunct -/

/-- The complex left flow derivative, the complex headline's `L`. -/
def LC {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex)
    (d : ArchDirComplex) (γ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0

/-- **Zone 3.** The complex-place headline's `l.foldr L α` conjunct consumed at `l = []`, where the
fold is the identity: every factorizable test function survives the empty list. -/
theorem zone3 {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsComplex)
    (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K)) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K),
      α (k * g) = α g ∧ α (g * k) = α g) :
    IsFactorizableTestFn K (([] : List ArchDirComplex).foldr (LC (w := w) hw) α) :=
  ((isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite K D w hw N tys α hαf hαb
    hαU).2.1 ([] : List ArchDirComplex))

end SetAF28Consumer
