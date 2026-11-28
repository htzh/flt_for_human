/-
A global character's archimedean part is the trace character up to a non-zero rational scaling.

`NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar` (242 pin
lines): for a global additive character `ψ` there is `a : F`, `a ≠ 0`, such that on the infinite adeles
`ψ (a x, 0)` is `fourierChar ∘ trace`. It is the *existence* half of the normalization the trace-dual
rows assume (`hψ_inf`), and the consumer that makes that hypothesis checkable rather than assumed.

Its four premises are the box measure, the circle-valued character API, the mixed embedding and the
vector-integral flip (`Analysis/Fourier/VectorIntegralFlip`); no existing module is above all four, so
the home is new, and it is deliberately *not* ``PureTensorPoisson.lean``: the two rows are independent
(the former does not need the Poisson summation), and making one a consumer of the other would add a
premise the pin does not have.

## The rows

* `NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar` — 242 pin `S_` lines.

The other four declarations of the pin's `S_` file are part of the wire and are transcribed here:

* `AddChar.exists_continuousLinearMap_fourierChar_eq_of_norm_eq_one` (pin `:36`, 14 lines) — the
  real-linear logarithm of a circle-valued character;
* `AddChar.exists_fourierChar_bilinForm_eq_of_norm_eq_one` (pin `:50`, 9 lines) — the same for a
  nondegenerate bilinear form, via `LinearMap.BilinForm.toDual`;
* `Real.fourierChar_eq_one_iff` (pin `:71`, 11 lines) — `𝐞 r = 1 ↔ ∃ n : ℤ, r = n`. Not in this
  mathlib (only `Circle.exp_eq_one` is), so the pin's row is carried;
* `NumberField.InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm` (pin `:85`, 32 lines) — see
  the substitution note below.

## Port deltas

* **The advise's substitution is wrong, as the work order records.** It names a `private`
  `continuous_ringEquiv_mixedSpace_symm` in `AutomorphicForm/Adelic/RightConvRegularity.lean`, where
  no such declaration exists. There are two *public* copies:
  `NumberField.AdelicBox.continuous_ringEquiv_mixedSpace_symm`
  (`NumberTheory/AdelicBox/Normalization.lean:131`) and
  `AutomorphicForm.TestFnNearIdentity.continuous_ringEquiv_mixedSpace_symm`
  (`AutomorphicForm/Adelic/TestFnNearIdentity.lean:58`), both `omit [NumberField F]` and both stated
  `Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm` — statement-identical to the pin's row
  `NumberField.InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm`
  (`Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm`). Neither copy carries the pin's *name*
  (both live in other namespaces, and FR-0274 forbids a second public full name), so the row is
  declared here at the pin's name and statement.

  **Why the pin's proof is transcribed rather than delegated** (measured, not assumed): both port
  copies are declared under `variable (F : Type)` — universe 0 — so neither applies at the pin's
  `(K : Type*)` binder. `NumberField.AdelicBox.continuous_ringEquiv_mixedSpace_symm K` is rejected
  with *"K has type Type u_1 but is expected to have type Type"*. The pin's 32-line proof is therefore
  carried, with two proof-level deltas: `dif_pos`/`dif_neg` are deprecated in this mathlib and become
  `dite_eq_left`/`dite_eq_right`, and the `heg` component computation cannot `simp only` through
  `ringEquiv_mixedSpace_apply` (the abbrev is delta-unfolded before the lemma's LHS can match), so it
  is `rw [he_def, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]` plus a `show` of the beta-reduced
  component.
* The namespaces: the pin's four auxiliary rows sit in `AddChar`, `Real` and
  `NumberField.InfiniteAdeleRing` (the last one *doubled* — its `S_` file opens `namespace NumberField`
  and writes the qualified name). This module declares all five at root with their pin-full names
  (`AddChar.…`, `Real.…`, `NumberField.InfiniteAdeleRing.…`), which is what the wire's `last`-name +
  statement-hash match reads.
* The pin's `hsplit` (`ψ z = ψ (z.1, 0) * ψ (0, z.2)`) is the same fact as
  `NumberField.AdelicFourier.addChar_prod_apply` (`NumberTheory/AdelicFourier/Transform.lean:106`);
  it is *not* imported here because that module is not one of this row's four premises (`Transform` is a
  sibling of `PureTensorPoisson`, not a dependency of the existence half), and importing it would add a
  premise the pin does not have.
* `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — added: `Circle.exp_eq_one` (pin
  `Real.fourierChar_eq_one_iff`'s `:72`) lives only there, not in `Mathlib.Analysis.Complex.Circle`.
* `algebraMap_mem_adicCompletionIntegers` is `NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers`
  in the port (`NumberTheory/AdelicLevel/IdealBall.lean:87`), reached through `AdelicBox/Measure`;
  `norm_apply_eq_one_of_isGlobalAddChar` is `AutomorphicForm.norm_apply_eq_one_of_isGlobalAddChar`
  (`NumberTheory/NumberField/GlobalAddChar/Circle.lean:63`) and `exists_ne_zero_forall_addChar_mul_eq_one`
  is `NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one` (`Measure.lean:667`).
* **`AdeleRing` is a plain `def` here**, so `rw` (matching at `implicit` transparency) cannot
  substitute a `Prod.mk` term for an `AdeleRing` argument under `ψ` (FR-0255; the same friction
  `NumberTheory/NumberField/StandardAddCharTrace.lean` records). The pin's three `rw [← hmul]`
  splittings (`hsplit`, `hι`, `hpair`) are therefore `AddChar.map_add_eq_mul` applications whose
  `AdeleRing`-typed sum equation (`Prod.ext`) is fed through `congrArg`/`Eq.trans`. The pin's
  `Real.fourierChar_eq_one_iff` proof is verbatim.

## Heartbeat probe (measured, never installed — FR-0225)

`cd lean && lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/NumberTheory/AdelicFourier/NonzeroTrace.lean`,
downward: **silent at 200 000 / 100 000 / 50 000 / 40 000** (the edit-loop cap included);
**fails at 20 000** (`whnf`, first at `:164`, the headline's *statement*), and at 10 000 / 5 000 /
1 000. Natural cost ≈ 20–40 k. No in-file `set_option maxHeartbeats`.

## Gates (measured, aa2d8b3)

* `spec/check_port.py --force`: **5 ok, 0 mismatch, 0 missing, 0 own, 0 kw** — the four auxiliary rows
  match the `P2M/Sol/S_…` wire and the headline matches the `Theorems/Thm_…` wrapper.
* Engine diff (pin-vs-module declaration diff, not last-name credit): pin `S_` rows **5** (all
  public), module public decls **5** — **5 by hash, 0 by name, 0 unaccounted** (`9ecd621c35542da6c6b3`,
  `a1f73049cd1fa99f2b13`, `6842af32d3b0964a2f39`, `2ca862121ab4b04951d6`, `cee7d141c94fb15a23ab`).
* Edit loop (`-DmaxHeartbeats=200000`) silent; one locked `lake build` of the module, 0 warning lines
  from this file.
* `#print axioms`: all five public declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no
  `sorryAx`.
* `dedup.py --within`: 0 clusters. `move_dead.py --dry-run`: 0 declarations, 0 lines.
* Linters: none silenced (the file carries no `set_option` beyond `autoImplicit false`).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar.lean>

spec-pin: Theorems/Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar.lean
-/
import FLTForHuman.Analysis.Fourier.VectorIntegralFlip
import FLTForHuman.NumberTheory.AdelicBox.Measure
import FLTForHuman.NumberTheory.AdelicBox.Normalization
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding NumberField.AdelicBox AutomorphicForm
open NumberField.InfinitePlace
open IsDedekindDomain MeasureTheory Real
open scoped Classical nonZeroDivisors FourierTransform RestrictedProduct

theorem AddChar.exists_continuousLinearMap_fourierChar_eq_of_norm_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (χ : AddChar E ℂ) (hχ : Continuous χ) (hχ1 : ∀ x, ‖χ x‖ = 1) :
    ∃ l : E →L[ℝ] ℝ, ∀ x, χ x = (𝐞 (l x) : ℂ) := by
  have hmem : ∀ x : E, χ x ∈ (Submonoid.unitSphere ℂ : Set ℂ) := fun x => by
    simp [Submonoid.unitSphere, hχ1 x]
  let χ' : AddChar E Circle :=
    { toFun := fun x => ⟨χ x, hmem x⟩
      map_zero_eq_one' := Subtype.ext (by simp)
      map_add_eq_mul' := fun x y => Subtype.ext (by
        show ((⟨χ (x + y), hmem (x + y)⟩ : Circle) : ℂ)
          = ((⟨χ x, hmem x⟩ : Circle) : ℂ) * ((⟨χ y, hmem y⟩ : Circle) : ℂ)
        simpa using AddChar.map_add_eq_mul χ x y) }
  have hχ' : Continuous χ' := by
    refine Continuous.subtype_mk hχ _
  obtain ⟨l, hl⟩ := AddChar.exists_continuousLinearMap_fourierChar_eq χ' hχ'
  have hχ'apply : ∀ x, (χ' x : ℂ) = χ x := fun x => rfl
  exact ⟨l, fun x => (hχ'apply x).trans (congrArg ((↑) : Circle → ℂ) (hl x))⟩

theorem AddChar.exists_fourierChar_bilinForm_eq_of_norm_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hB : B.Nondegenerate)
    (χ : AddChar E ℂ) (hχ : Continuous χ) (hχ1 : ∀ x, ‖χ x‖ = 1) :
    ∃ t : E, ∀ x, χ x = (𝐞 (B t x) : ℂ) := by
  obtain ⟨l, hl⟩ := AddChar.exists_continuousLinearMap_fourierChar_eq_of_norm_eq_one χ hχ hχ1
  refine ⟨(B.toDual hB).symm (l : Module.Dual ℝ E), fun x => ?_⟩
  rw [hl x, LinearMap.BilinForm.apply_toDual_symm_apply]
  rfl

theorem Real.fourierChar_eq_one_iff (r : ℝ) : 𝐞 r = 1 ↔ ∃ n : ℤ, r = n := by
  rw [Real.fourierChar_apply', Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h2 : (2 * π : ℝ) ≠ 0 := by positivity
    have : 2 * π * r = 2 * π * n := by rw [hn]; ring
    exact mul_left_cancel₀ h2 this
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩

theorem NumberField.InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm
    (K : Type*) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace K with he_def
  let g : mixedSpace K → InfiniteAdeleRing K := fun y v =>
    if hv : IsReal v then (Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩)
    else (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hv)).symm
      (y.2 ⟨v, not_isReal_iff_isComplex.mp hv⟩)
  have hg : Continuous g := by
    refine continuous_pi fun v => ?_
    by_cases hv : IsReal v
    · simp only [g, dite_eq_left hv]
      exact (Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
        ((continuous_apply _).comp continuous_fst)
    · simp only [g, dite_eq_right hv]
      exact (Completion.isometryEquivComplexOfIsComplex
        (not_isReal_iff_isComplex.mp hv)).symm.continuous.comp
        ((continuous_apply _).comp continuous_snd)
  have heg : ∀ y, e (g y) = y := by
    intro y
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · have hw : IsReal (w : InfinitePlace K) := w.2
      have hgv : g y w = (Completion.isometryEquivRealOfIsReal hw).symm (y.1 ⟨w, hw⟩) := by
        simp only [g, dite_eq_left hw]
      rw [he_def, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      show (Completion.extensionEmbeddingOfIsReal hw) (g y (w : InfinitePlace K)) = y.1 w
      rw [hgv]
      exact (Completion.isometryEquivRealOfIsReal hw).apply_symm_apply (y.1 w)
    · have hw : ¬ IsReal (w : InfinitePlace K) := not_isReal_iff_isComplex.mpr w.2
      have hgv : g y w = (Completion.isometryEquivComplexOfIsComplex
          (not_isReal_iff_isComplex.mp hw)).symm
          (y.2 ⟨w, not_isReal_iff_isComplex.mp hw⟩) := by
        simp only [g, dite_eq_right hw]
      rw [he_def, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
      show (Completion.extensionEmbedding (w : InfinitePlace K)) (g y (w : InfinitePlace K))
        = y.2 w
      rw [hgv]
      exact (Completion.isometryEquivComplexOfIsComplex w.2).apply_symm_apply (y.2 w)
  have hsymm : (e.symm : mixedSpace K → InfiniteAdeleRing K) = g := by
    funext y
    apply e.injective
    rw [e.apply_symm_apply, heg]
  rw [hsymm]
  exact hg

theorem NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ a : F, a ≠ 0 ∧ ∀ x : InfiniteAdeleRing F,
      ψ (algebraMap F (InfiniteAdeleRing F) a * x, 0) =
        (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by
  set V := mixedSpace F
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F with he_def

  have hsplit : ∀ z : AdeleRing (𝓞 F) F, ψ z = ψ (z.1, 0) * ψ (0, z.2) := fun z => by
    have h := AddChar.map_add_eq_mul ψ (z.1, (0 : FiniteAdeleRing (𝓞 F) F)) (0, z.2)
    have hz : (((z.1, (0 : FiniteAdeleRing (𝓞 F) F)) + (0, z.2)) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (z.1, z.2) :=
      Prod.ext (by simp) (by simp)
    have hz' : ((z.1, (0 : FiniteAdeleRing (𝓞 F) F)) + (0, z.2) : AdeleRing (𝓞 F) F) = z := hz
    exact (congrArg ψ hz'.symm).trans h
  have hι : ∀ q : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) q)
      = ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
        * ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) := fun q => by
    have h := AddChar.map_add_eq_mul ψ
      ((algebraMap F (InfiniteAdeleRing F) q, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
      ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
    have hz : (((algebraMap F (InfiniteAdeleRing F) q, 0) + (0,
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q)) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
        = (algebraMap F (InfiniteAdeleRing F) q, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) :=
      Prod.ext (by simp) (by simp)
    have hz' : (((algebraMap F (InfiniteAdeleRing F) q, 0) + (0,
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q) : AdeleRing (𝓞 F) F))
        = algebraMap F (AdeleRing (𝓞 F) F) q := hz
    exact (congrArg ψ hz').symm.trans h
  have hpair : ∀ A B : FiniteAdeleRing (𝓞 F) F, ψ (0, A + B) = ψ (0, A) * ψ (0, B) := fun A B => by
    have h := AddChar.map_add_eq_mul ψ ((0 : InfiniteAdeleRing F), A) (0, B)
    have hz : ((((0 : InfiniteAdeleRing F), A) + (0, B)) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, A + B) :=
      Prod.ext (by simp) (by simp)
    have hz' : (((0 : InfiniteAdeleRing F), A) + (0, B) : AdeleRing (𝓞 F) F) = (0, A + B) := hz
    exact (congrArg ψ hz').symm.trans h

  let ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hψf_apply : ∀ z, ψf z = ψ (0, z) := fun z => rfl
  have hψf_cont : Continuous ψf :=
    hψ.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨d, hd0, hd⟩ := NumberField.AdelicBox.exists_ne_zero_forall_addChar_mul_eq_one F hψf_cont
  have hdF : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd0

  have hψ_inf_fin : ∀ q : F, ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
      * ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) = 1 := fun q => by
    rw [← hι]; exact hψ.principalInvariant q

  let χ : AddChar V ℂ :=
    (ψ.compAddMonoidHom (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
      |>.compAddMonoidHom e.symm.toAddMonoidHom
  have hχ_apply : ∀ v, χ v = ψ (e.symm v, 0) := fun v => rfl
  have hχc : Continuous χ := by
    change Continuous (fun v => χ v)
    simp_rw [hχ_apply]
    exact hψ.continuous.comp
      ((InfiniteAdeleRing.continuous_ringEquiv_mixedSpace_symm F).prodMk continuous_const)
  have hχ1 : ∀ v, ‖χ v‖ = 1 := fun v =>
    AutomorphicForm.norm_apply_eq_one_of_isGlobalAddChar F hψ _
  obtain ⟨t, ht⟩ := AddChar.exists_fourierChar_bilinForm_eq_of_norm_eq_one
    (Algebra.traceForm ℝ V) (traceForm_mixedSpace_nondegenerate F) χ hχc hχ1
  have hψinf : ∀ x : InfiniteAdeleRing F,
      ψ (x, 0) = (𝐞 (Algebra.trace ℝ V (t * e x)) : ℂ) := fun x => by
    have := ht (e x)
    rwa [hχ_apply, RingEquiv.symm_apply_apply, Algebra.traceForm_apply] at this
  have heι : ∀ q : F, e (algebraMap F (InfiniteAdeleRing F) q) = mixedEmbedding F q :=
    fun q => (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F (x := q)).symm

  have hint : ∀ a : 𝓞 F, ∃ m : ℤ,
      Algebra.trace ℝ V (t * mixedEmbedding F ((d : F) * a)) = m := fun a => by
    have h1 := hψ_inf_fin ((d : F) * a)
    have h2 : ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F) * a)) = 1 := by
      rw [map_mul, ← hψf_apply]
      refine hd _ fun v => ?_
      exact NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers (v := v) a
    rw [h2, mul_one, hψinf, heι, Circle.coe_eq_one, Real.fourierChar_eq_one_iff] at h1
    exact h1

  let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
    Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ (d : F))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdF)
  have htdual : t ∈ (LinearMap.BilinForm.dualSubmodule (Algebra.traceForm ℝ V).flip
      (mixedEmbedding.idealLattice F I) : Set V) := by
    change t ∈ LinearMap.BilinForm.dualSubmodule _ _
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    rw [mem_idealLattice] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hq' : q ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ (d : F) := by
      simpa [I] using hq
    rw [FractionalIdeal.mem_spanSingleton] at hq'
    obtain ⟨a, rfl⟩ := hq'
    obtain ⟨m, hm⟩ := hint a
    have hflip : ∀ u w : V, (Algebra.traceForm ℝ V).flip u w = Algebra.trace ℝ V (w * u) :=
      fun u w => by
        show Algebra.traceForm ℝ V w u = _
        exact Algebra.traceForm_apply _ _ _
    rw [hflip, Submodule.mem_one]
    refine ⟨m, ?_⟩
    have hq : a • (d : F) = (d : F) * a := by rw [Algebra.smul_def, mul_comm]
    rw [eq_intCast, ← hm, hq, mul_comm t]
  rw [NumberField.mixedEmbedding.coe_dualSubmodule_flip_traceForm_idealLattice F I] at htdual
  obtain ⟨a₀, -, ha₀t⟩ := htdual

  have ha₀ : a₀ ≠ 0 := by
    rintro rfl
    apply hψ.nontrivial
    have hinf1 : ∀ x : InfiniteAdeleRing F, ψ (x, 0) = 1 := fun x => by
      rw [hψinf, ← ha₀t, map_zero, zero_mul, map_zero, AddChar.map_zero_eq_one, Circle.coe_one]
    have hfinF : ∀ q : F, ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) = 1 := fun q => by
      have := hψ_inf_fin q
      rwa [hinf1, one_mul] at this
    have hfin1 : ∀ z : FiniteAdeleRing (𝓞 F) F, ψ (0, z) = 1 := fun z => by
      obtain ⟨u, hu⟩ := (IsUnit.mk0 (d : F) hdF).map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
      obtain ⟨k, hk⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F ((u⁻¹).val * z)
      have hz : z = u.val * (algebraMap F _ k + (u⁻¹).val * z) + -(u.val * algebraMap F _ k) := by
        rw [mul_add, ← mul_assoc, Units.mul_inv, one_mul]; ring
      rw [hz, hpair]
      have h1 : ψ (0, u.val * (algebraMap F _ k + (u⁻¹).val * z)) = 1 := by
        rw [hu, ← hψf_apply]; exact hd _ hk
      have h2 : ψ (0, -(u.val * algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) = 1 := by
        rw [hu, ← map_mul, ← map_neg]; exact hfinF _
      rw [h1, h2, one_mul]
    refine AddChar.ext _ _ fun z => ?_
    rw [AddChar.one_apply, hsplit z, hinf1, hfin1, one_mul]

  refine ⟨a₀⁻¹, inv_ne_zero ha₀, fun x => ?_⟩
  rw [hψinf, ← ha₀t, RingEquiv.map_mul, heι, ← mul_assoc, ← (mixedEmbedding F).map_mul,
    mul_inv_cancel₀ ha₀, map_one, one_mul]
