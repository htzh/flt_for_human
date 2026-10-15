/-
  The archimedean semi-local comparison: the product of the completions of `L` over the
  extensions of an infinite place `v` of `K` is the base change `K_v ⊗_K L`, and the conorm
  map on infinite adèle rings is continuous.

  Transcribed from the pin's `Definitions/Def_M4aHerbrand_ArchSemilocal.lean` (pinned
  `aa2d8b3`, 283 lines / 23 declarations; one of them, `aux_ker_ne`, is `private`), whole and
  at the pin's names, with a `-- pin:` provenance comment on every declaration.  The pin's
  bare mathlib import is replaced by the explicit imports below; the pin's import of
  `Def_NumberField_InfiniteAdeleRing_BaseChangeData` is this port's module 1.

  ## Substitutions against mathlib `v4.34.0`

  | pin declaration | mathlib `v4.34.0` | action |
  |---|---|---|
  | proof use `Completion.finrank_eq_one_of_isUnramified` (in `finiteDimensional_completion`) | `IsUnramified.finrank_eq_one` | substituted — the pin's name is a deprecated alias since 2026-07-10 |
  | proof use `Completion.finrank_eq_two_of_isRamified` (in `finiteDimensional_completion`) | `IsRamified.finrank_eq_two` | substituted — the pin's name is a deprecated alias since 2026-07-10 |

  Everything else the pin names is mathlib's own (`LiesOver`, `placesOver`,
  `inertiaDeg_eq_finrank`, `sum_inertiaDeg_eq_finrank`, `Completion.denseRange_coe`,
  `Completion.norm_coe`, `isometry_extensionEmbedding`, `WithAbs`, the `Ideal` quotient API,
  `AbsoluteValue.isEquiv_iff_lt_one_iff`, `NontriviallyNormedField.ofNormNeOne`, the
  finite-dimensional continuity lemmas, `Module.finrank_baseChange`, `Module.finrank_pi_fintype`,
  `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one`); the pin's declarations themselves
  (`psiFactor`, `psi`, `placeEquivAlg`, `genuineInfinitePlaceData`, the ramification and
  continuity block) are genuinely absent from mathlib and transcribed at the pin's name.

  ## Cap and lint discipline

  The pin raises its heartbeat budget on `psi_surjective` and on `continuous_conorm`, and
  lowers the instance-search budgets on the private `aux_ker_ne`.  None of that is
  transcribed: every declaration is re-elaborated under the plain 200k cap with no option
  set anywhere in this file.  The `LiesOver` instance the pin installs with `attribute
  [local instance] extLiesOver` is kept as it stands (it is an attribute, not a budget), so
  the `Algebra`/`Module` instances derived from `LiesOver` resolve without any explicit
  instance argument.  The pin's `haveI`/`letI` tactic uses in proofs are written
  `have`/`let` (v4.34.0's `haveILetI` style linter); the local instances they bind are still
  found by instance search.
-/
import FLTForHuman.NumberTheory.NumberField.InfiniteAdeleRing.BaseChangeData
import Mathlib.NumberTheory.NumberField.Completion.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

namespace M4aHerbrand.ArchSemilocal

open NumberField NumberField.InfinitePlace TensorProduct

open scoped NumberField.LiesOver

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

-- pin: liesOver_of_comap_eq (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:14)
omit [NumberField K] [NumberField L] in
theorem liesOver_of_comap_eq {v : InfinitePlace K} {w : InfinitePlace L}
    (h : w.comap (algebraMap K L) = v) : w.1.LiesOver v.1 :=
  ⟨congrArg Subtype.val h⟩

-- pin: finiteDimensional_completion (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:19)
omit [NumberField K] [NumberField L] in
theorem finiteDimensional_completion (v : InfinitePlace K) (w : InfinitePlace L)
    [w.1.LiesOver v.1] : FiniteDimensional v.Completion w.Completion := by
  by_cases h : w.IsUnramified K
  · exact FiniteDimensional.of_finrank_pos
      (by rw [h.finrank_eq_one v]; norm_num)
  · exact FiniteDimensional.of_finrank_pos
      (by rw [IsRamified.finrank_eq_two v h]; norm_num)

-- pin: instIsScalarTowerCompletion (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:28)
omit [NumberField K] [NumberField L] in
instance instIsScalarTowerCompletion (w : InfinitePlace L) : IsScalarTower K L w.Completion :=
  .of_algebraMap_eq fun _ => rfl

-- pin: psiFactor (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:31)
def psiFactor (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] :
    (v.Completion ⊗[K] L) →ₐ[v.Completion] w.Completion :=
  Algebra.TensorProduct.lift (Algebra.ofId v.Completion w.Completion)
    (IsScalarTower.toAlgHom K L w.Completion) (fun _ _ => Commute.all _ _)

-- pin: psiFactor_tmul (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:37)
omit [NumberField K] [NumberField L] in
@[simp] theorem psiFactor_tmul (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1]
    (c : v.Completion) (l : L) :
    psiFactor v w (c ⊗ₜ[K] l) = algebraMap v.Completion w.Completion c * algebraMap L w.Completion l := by
  simp [psiFactor, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
    IsScalarTower.coe_toAlgHom']

-- pin: psiFactor_one_tmul (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:44)
omit [NumberField K] [NumberField L] in
theorem psiFactor_one_tmul (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] (l : L) :
    psiFactor v w ((1 : v.Completion) ⊗ₜ[K] l) = algebraMap L w.Completion l := by
  rw [psiFactor_tmul, map_one, one_mul]

-- pin: nontriviallyNormedCompletion (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:48)
@[reducible] def nontriviallyNormedCompletion (v : InfinitePlace K) :
    NontriviallyNormedField v.Completion :=
  NontriviallyNormedField.ofNormNeOne (by
    have h2 : ‖(2 : v.Completion)‖ = 2 := by
      rw [← (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _), map_ofNat]
      exact Complex.norm_two
    refine ⟨2, ?_, ?_⟩
    · exact norm_ne_zero_iff.mp (by rw [h2]; norm_num)
    · rw [h2]; norm_num)

-- pin: denseRange_algebraMap_completion (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:59)
omit [NumberField L] in
theorem denseRange_algebraMap_completion (w : InfinitePlace L) :
    DenseRange (algebraMap L w.Completion) := by
  have h := InfinitePlace.Completion.denseRange_coe w
  have he : (algebraMap L w.Completion : L → w.Completion)
      = (fun x : WithAbs w.1 => (x : w.Completion)) ∘ (WithAbs.equiv w.1).symm := rfl
  rw [he]
  exact h.comp (WithAbs.equiv w.1).symm.surjective.denseRange
    (InfinitePlace.Completion.continuous_coe w)

-- pin: psiFactor_surjective (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:68)
theorem psiFactor_surjective (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] :
    Function.Surjective (psiFactor v w) := by
  let : NontriviallyNormedField v.Completion := nontriviallyNormedCompletion v
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have : FiniteDimensional v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  set S : Submodule v.Completion w.Completion := LinearMap.range (psiFactor v w).toLinearMap with hS
  have : FiniteDimensional v.Completion ↥S := inferInstance
  have hclosed : IsClosed (S : Set w.Completion) := S.closed_of_finiteDimensional
  have hsub : Set.range (algebraMap L w.Completion) ⊆ (S : Set w.Completion) := by
    rintro - ⟨l, rfl⟩
    exact ⟨(1 : v.Completion) ⊗ₜ[K] l, psiFactor_one_tmul v w l⟩
  have htop : (S : Set w.Completion) = Set.univ := by
    have hdense := (denseRange_algebraMap_completion w).mono hsub
    have h1 := hdense.closure_eq
    rwa [hclosed.closure_eq] at h1
  intro y
  have : y ∈ (S : Set w.Completion) := htop ▸ Set.mem_univ y
  exact this

-- pin: norm_algebraMap_completion (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:89)
omit [NumberField L] in
theorem norm_algebraMap_completion (w : InfinitePlace L) (l : L) :
    ‖algebraMap L w.Completion l‖ = w l := by
  have he : algebraMap L w.Completion l = ((WithAbs.equiv w.1).symm l : w.Completion) := rfl
  rw [he, Completion.norm_coe]
  rfl

-- pin: aux_ker_ne (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:97)
private theorem aux_ker_ne (v : InfinitePlace K) (w w' : InfinitePlace L)
    [w.1.LiesOver v.1] [w'.1.LiesOver v.1] {x : L} (hx : w x < 1) (hx' : ¬ w' x < 1) :
    RingHom.ker (psiFactor v w) ≠ RingHom.ker (psiFactor v w') := by
  intro hker
  let : NontriviallyNormedField v.Completion := nontriviallyNormedCompletion v
  have := finiteDimensional_completion v w
  have := finiteDimensional_completion v w'

  let e₁ := Ideal.quotientKerAlgEquivOfSurjective (psiFactor_surjective v w)
  let e₂ := Ideal.quotientKerAlgEquivOfSurjective (psiFactor_surjective v w')
  let em : ((v.Completion ⊗[K] L) ⧸ RingHom.ker (psiFactor v w)) ≃ₐ[v.Completion]
      ((v.Completion ⊗[K] L) ⧸ RingHom.ker (psiFactor v w')) :=
    Ideal.quotientEquivAlgOfEq v.Completion hker
  let φ : w.Completion ≃ₐ[v.Completion] w'.Completion := (e₁.symm.trans em).trans e₂
  have hφcont : Continuous φ := φ.toLinearMap.continuous_of_finiteDimensional
  have hφψ : ∀ a : v.Completion ⊗[K] L, φ (psiFactor v w a) = psiFactor v w' a := by
    intro a
    have h0 : e₁.symm (psiFactor v w a) = Ideal.Quotient.mk _ a :=
      e₁.toEquiv.symm_apply_eq.mpr
        (Ideal.quotientKerAlgEquivOfSurjective_mk (psiFactor_surjective v w) a).symm
    show e₂ (em (e₁.symm (psiFactor v w a))) = _
    rw [h0]
    have hem : em (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := by
      simp [em, Ideal.quotientEquivAlgOfEq]
    rw [hem]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk (psiFactor_surjective v w') a
  have hφalg : ∀ l : L, φ (algebraMap L w.Completion l) = algebraMap L w'.Completion l := by
    intro l
    rw [← psiFactor_one_tmul v w l, hφψ, psiFactor_one_tmul]

  have h1 : Filter.Tendsto (fun n : ℕ => (algebraMap L w.Completion x) ^ n)
      Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one).mpr
      (by rw [norm_algebraMap_completion]; exact hx)
  have h2 : Filter.Tendsto (fun n : ℕ => (algebraMap L w'.Completion x) ^ n)
      Filter.atTop (nhds 0) := by
    have := (hφcont.tendsto 0).comp h1
    simpa [Function.comp_def, map_pow, hφalg, map_zero,
      -NumberField.InfinitePlace.Completion.algebraMap_apply] using this
  have h3 : ‖algebraMap L w'.Completion x‖ < 1 :=
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one).mp h2
  rw [norm_algebraMap_completion] at h3
  exact hx' h3

-- pin: ker_psiFactor_ne (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:141)
theorem ker_psiFactor_ne (v : InfinitePlace K) (w w' : InfinitePlace L)
    [w.1.LiesOver v.1] [w'.1.LiesOver v.1] (hne : w ≠ w') :
    RingHom.ker (psiFactor v w) ≠ RingHom.ker (psiFactor v w') := by
  have hnequiv : ¬ w.1.IsEquiv w'.1 := fun h => hne (eq_iff_isEquiv.mpr h)
  rw [AbsoluteValue.isEquiv_iff_lt_one_iff] at hnequiv
  push Not at hnequiv
  obtain ⟨x, hx⟩ := hnequiv
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact aux_ker_ne v w w' h1 (not_lt.mpr h2)
  · exact (aux_ker_ne v w' w h2 (not_lt.mpr h1)).symm

-- pin: extLiesOver (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:154)
omit [NumberField K] [NumberField L] in
theorem extLiesOver (v : InfinitePlace K) (w : v.Extension L) : w.1.1.LiesOver v.1 :=
  liesOver_of_comap_eq w.2

attribute [local instance] extLiesOver

-- pin: psi (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:159)
def psi (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) →ₐ[v.Completion]
      ((w : v.Extension L) → w.1.Completion) :=
  AlgHom.pi fun w => psiFactor v w.1

-- pin: psi_apply (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:165)
omit [NumberField K] [NumberField L] in
@[simp] theorem psi_apply (v : InfinitePlace K) (z : v.Completion ⊗[K] L) (w : v.Extension L) :
    psi v z w = psiFactor v w.1 z := rfl

-- pin: psi_surjective (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:169)
theorem psi_surjective (v : InfinitePlace K) : Function.Surjective (psi (K := K) (L := L) v) := by
  classical
  intro y

  have hsurj : ∀ w : v.Extension L, ∃ a, psiFactor v w.1 a = y w := fun w =>
    psiFactor_surjective v w.1 (y w)
  choose xw hxw using hsurj

  have hmax : ∀ w : v.Extension L, (RingHom.ker (psiFactor v w.1)).IsMaximal :=
    fun w => RingHom.ker_isMaximal_of_surjective _
      (psiFactor_surjective v w.1)
  have hcop : ∀ w w' : v.Extension L, w ≠ w' →
      IsCoprime (RingHom.ker (psiFactor v w.1))
        (RingHom.ker (psiFactor v w'.1)) := fun w w' hne =>
    Ideal.isCoprime_of_isMaximal (ker_psiFactor_ne v w.1 w'.1 (fun h => hne (Subtype.ext h)))

  obtain ⟨zq, hzq⟩ := Ideal.quotientInfToPiQuotient_surj
    (I := fun w : v.Extension L => RingHom.ker (psiFactor v w.1)) hcop
    (fun w => Ideal.Quotient.mk _ (xw w))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective zq
  refine ⟨a, ?_⟩
  funext w
  have hcomp := congrFun hzq w
  rw [Ideal.quotientInfToPiQuotient_mk'] at hcomp
  have hmem : a - xw w ∈ RingHom.ker (psiFactor v w.1) :=
    Ideal.Quotient.eq.mp hcomp
  have hval : psiFactor v w.1 a = psiFactor v w.1 (xw w) := by
    have h0 : psiFactor v w.1 (a - xw w) = 0 := hmem
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  rw [psi_apply, hval]
  exact hxw w

-- pin: extensionEquivPlacesOver (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:201)
def extensionEquivPlacesOver (v : InfinitePlace K) : v.Extension L ≃ ↥(v.placesOver L) where
  toFun w := ⟨w.1, liesOver_of_comap_eq w.2⟩
  invFun w := ⟨w.1, by have : w.1.1.LiesOver v.1 := w.2; exact LiesOver.comap_eq w.1 v⟩
  left_inv w := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

-- pin: finrank_pi_extension (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:207)
theorem finrank_pi_extension (v : InfinitePlace K) :
    Module.finrank v.Completion ((w : v.Extension L) → w.1.Completion)
      = Module.finrank K L := by
  classical
  have : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  have : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing _ _
  rw [Module.finrank_pi_fintype v.Completion]
  rw [← sum_inertiaDeg_eq_finrank K L v]
  rw [← Finset.sum_coe_sort ((placesOver L v).toFinset) (fun w => v.inertiaDeg w)]
  let E : v.Extension L ≃ {w : InfinitePlace L // w ∈ (placesOver L v).toFinset} :=
    { toFun := fun w =>
        ⟨w.1, Set.mem_toFinset.mpr
          (show (w.1 : InfinitePlace L) ∈ placesOver L v from extLiesOver v w)⟩
      invFun := fun w =>
        have hmem : (w.1 : InfinitePlace L) ∈ placesOver L v := Set.mem_toFinset.mp w.2
        haveI : w.1.1.LiesOver v.1 := hmem
        ⟨w.1, LiesOver.comap_eq w.1 v⟩
      left_inv := fun w => Subtype.ext rfl
      right_inv := fun w => Subtype.ext rfl }
  exact Fintype.sum_equiv E _ _ (fun w => (inertiaDeg_eq_finrank v w.1).symm)

-- pin: psi_bijective (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:230)
theorem psi_bijective (v : InfinitePlace K) : Function.Bijective (psi (K := K) (L := L) v) := by
  have : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  have : Module.Finite v.Completion ((w : v.Extension L) → w.1.Completion) :=
    Module.Finite.pi
  have : FiniteDimensional v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  have hdim : Module.finrank v.Completion (v.Completion ⊗[K] L)
      = Module.finrank v.Completion ((w : v.Extension L) → w.1.Completion) := by
    rw [Module.finrank_baseChange, finrank_pi_extension]
  have hsurjL : Function.Surjective (psi (K := K) (L := L) v).toLinearMap :=
    psi_surjective v
  have hinjL :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurjL
  exact ⟨hinjL, psi_surjective v⟩

-- pin: placeEquivAlg (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:247)
def placeEquivAlg (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) ≃ₐ[v.Completion] ((w : v.Extension L) → w.1.Completion) :=
  AlgEquiv.ofBijective (psi v) (psi_bijective v)

-- pin: genuineInfinitePlaceData (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:251)
def genuineInfinitePlaceData : FLT.InfiniteAdeleBaseChange.InfinitePlaceData K L where
  placeEquiv v := (placeEquivAlg (K := K) (L := L) v).toRingEquiv
  placeEquiv_one_tmul v l w := psiFactor_one_tmul v w.1 l

-- pin: continuous_algebraMap_completion (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:256)
omit [NumberField K] [NumberField L] in
theorem continuous_algebraMap_completion (v : InfinitePlace K) (w : InfinitePlace L)
    [w.1.LiesOver v.1] : Continuous (algebraMap v.Completion w.Completion) := by
  have he : (algebraMap v.Completion w.Completion : v.Completion → w.Completion)
      = fun c => c • (1 : w.Completion) := by
    funext c
    rw [Algebra.algebraMap_eq_smul_one]
  rw [he]
  exact continuous_id.smul continuous_const

-- pin: continuous_conorm (Definitions/Def_M4aHerbrand_ArchSemilocal.lean:266)
theorem continuous_conorm :
    Continuous (genuineInfinitePlaceData (K := K) (L := L)).conorm := by
  refine continuous_pi fun w => ?_
  have : w.1.LiesOver (w.comap (algebraMap K L)).1 := liesOver_of_comap_eq rfl
  have hcomp : (fun x : InfiniteAdeleRing K =>
      (genuineInfinitePlaceData (K := K) (L := L)).conorm x w)
      = fun x => algebraMap ((w.comap (algebraMap K L)).Completion) w.Completion
          (x (w.comap (algebraMap K L))) := by
    funext x
    show psiFactor (w.comap (algebraMap K L)) w
        ((x (w.comap (algebraMap K L))) ⊗ₜ[K] (1 : L)) = _
    rw [psiFactor_tmul, map_one, mul_one]
  rw [hcomp]
  exact (continuous_algebraMap_completion _ w).comp (continuous_apply _)

end

end M4aHerbrand.ArchSemilocal
