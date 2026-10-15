/-
  The Dedekind adic-completion base change — the pin node
  `Definitions/Def_DedekindDomain_Completion_BaseChange.lean` (pinned `aa2d8b3`,
  1,159 lines / 73 declarations), re-landed whole at the pin's names with `-- pin:`
  provenance on every declaration.  This is W2b of the twisted-orbital definition
  program; W3's `TwistedOrbital` names `HeightOneSpectrum.tensorAdicCompletionIntegersTo`
  (pin `:649`) and `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv` (pin `:1058`) in
  its statements, and both are present here, public, at the pin's names.

  The pin raises its heartbeat budget with four global option declarations (two of them
  instance-search budgets) and adds a `shortcut_instances` block of ~30
  `private ... := inferInstance` bricks.  None of that is transcribed: every declaration
  is proved under the 200k cap with no options set at all, and the pin's
  `shortcut_instances` block is **not** reproduced — where instance search could not find
  an instance, the instance is supplied at the use site (see the instance-fix notes
  below).

  ## Substitutions against mathlib `v4.34.0` (dropped, use the mathlib name)

  * `TensorProduct.RightActions.Algebra.TensorProduct.comm` is
    `Algebra.TensorProduct.commRight`; for the right-module commutativity used by
    `Module.Basis.rightBaseChange` the port's own
    `TensorProduct.RightActions.Module.TensorProduct.comm` is used instead (it is the
    scoped right-module equiv, not the `Algebra.toModule`-based `commRight`);
  * `TensorProduct.RightActions.algebraMap_eval` stays the pin's own (the hub edit to
    `RightActionInstances.lean` restored the pin's scoped `Algebra`, under which it is
    `rfl`); `Algebra.TensorProduct.right_algebraMap_apply` is *not* used;
  * `Ideal.inertiaDeg'` (removed) is `Ideal.inertiaDeg` with the base ring an explicit
    argument, and `Ideal.inertiaDeg_algebra_tower` is `Ideal.inertiaDeg_tower`;
  * `Ideal.ramificationIdx_spec` is the non-deprecated `Ideal.ramificationIdx'_spec`;
  * `ValuationSubring.algebraMap_apply` is mathlib's
    (`Mathlib/RingTheory/Valuation/ValuationSubring.lean:151`);
  * `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` is deprecated in `v4.34.0`; the
    local case of pin `:1013` is re-proved from
    `Ideal.sum_ramification_inertia_eq_finrank` (with hand-rolled instances, below);
  * `Set.mem_setOf_eq` is `Set.mem_ofPred_eq`;
  * `LieAlgebra.ofAssociativeAlgebra.toMulAction` is `inferInstance`;
  * the pin's bare mathlib import is replaced by the explicit imports below.

  ## Proof-level adaptations (statements unchanged)

  * `TensorProduct.inductionOn` (no `zero` alternative) replaces
    `TensorProduct.induction_on`, so the pin's separate `zero` cases are dropped
    (`IsBiscalar` instance, the two `rightActions_*` lemmas);
  * the pin's `IsBiscalar S A ψ.baseChange_of_algebraMap` instance is named
    `SemialgHom.instIsBiscalarBaseChangeOfAlgebraMap` and `baseChangeRightOfAlgebraMap`
    is built as `{ψ.baseChange_of_algebraMap with commutes' := …}` rather than via
    `AlgHom.changeScalars` (instance search cannot invert
    `ψ.baseChange_of_algebraMap` through the `⇑` coercion);
  * `SemialgHom.baseChange_of_algebraMap`'s `hfg` is a tactic proof (the pin's
    `Algebra.commutes s (ρ a)` term is ill-typed under implicit transparency),
    and its tmul lemmas use `Algebra.TensorProduct.lift_tmul`;
  * in `valued_adicCompletionSemialgHom`, `simp only [adicCompletion.valued_coe]`
    replaces the pin's `rw` (the `rw` did not match the coerced RHS);
  * the `Valuation.RankOne` local instance's `strictMono'` uses an explicit `change`
    (the `MonoidWithZeroHom` coercion does not unify with `⇑`);
  * `IsBiscalar B (adicCompletionIntegers) tensorAdicCompletionIntegersTo` uses the
    pin's own `rightActions_smul_eq_one_tmul_mul` (transcribed early, `:1072`) to
    compute the codomain's `Module.compHom`-restricted `Kv`-action.

  ## Instance fixes at the use site (no caps, no option declarations)

  * `baseChangeRight_surjective` (`:583`) and `instModuleFinitePi` (`:604`): the domain
    `Module.Finite (adicCompletion K v) (L ⊗[K] adicCompletion K v)` is supplied by a
    term-mode `letI := inferInstance` (the scoped `Module.Finite` instance);
  * `ramificationIdx_mul_inertiaDeg_eq_finrank` (`:1013`) supplies, all term-mode:
    the two `IsScalarTower`s; `(w.1.completionIdeal L).LiesOver (v.completionIdeal K)`;
    `FaithfulSMul` via `FaithfulSMul.of_field_isFractionRing`; `Subsingleton` of the
    `primesOver` subtype (`Ring.DimensionLEOne.maximalOfPrime` +
    `IsLocalRing.eq_maximalIdeal`); `Fintype` from that `Subsingleton`; and
    `Module.Flat` via `Module.free_of_finite_type_torsion_free'` + `Module.Flat.of_free`.

  ## The `Def_DedekindDomain_AdicValuation_InlineSpecific` residual

  The residual this module actually reaches and mathlib `v4.34.0` lacks is already
  landed in the tree at the pin's own names in
  `FLTForHuman/AlgebraicCurve/Place/Completion.lean` (uniformizer slice, pin 299–551) and
  `FLTForHuman/AlgebraicCurve/Place/AdicCompletion.lean` (dense/valuation/residue slice,
  pin 26–344, 359–429, 555–560); this module imports the latter directly, so the residual
  is empty here.  Rows (pin InlineSpecific line → resolution):

  `exists_ofAdd_natCast_of_le_one` :95, `ne_zero_of_some_le_intValuation` :118,
  `emultiplicity_eq_of_valuation_eq_ofAdd` :123, `exists_adicValued_mul_sub_le` :135,
  `exists_adicValued_sub_lt_of_adicValued_le_one` :167,
  `closureAlgebraMapIntegers_eq_integers` :223, `denseRange_of_integerAlgebraMap` :262,
  `exists_adicValued_sub_lt_of_adicCompletionInteger` :277, `algebraMap_completionIntegers`
  :306, `ResidueFieldToCompletionResidueField` :318,
  `ResidueFieldEquivCompletionResidueField` :325, `inertiaDeg_asIdeal_completionIdeal`
  :345, `exists_forall_adicValued_sub_lt` :359,
  `eq_mul_nonZeroDivisor_inv_adicCompletionIntegers` :392,
  `eq_mul_pi_adicCompletionIntegers` :403, `mem_completionIdeal_iff'` :555,
  `completionIdeal_ne_bot` :560 — all `landed, imported`.  `exists_ofAdd_natCast_lt` :104,
  `completionIdeal` :299, `mem_completionIdeal_iff` :302, `exists_uniformizer` :430,
  `uniformizer_ne_zero` :438, `uniformizer_not_isUnit` :447,
  `eq_pow_uniformizer_mul_unit` :455, `maximalIdeal_eq_span_uniformizer` :474,
  `IsDiscreteValuationRing` :513, `mem_completionIdeal_pow` :525 — all
  `landed, imported`.  Two substitutions: `ValuationSubring.algebraMap_apply` is mathlib's
  (`ValuationSubring.lean:151`), and the `vK` `Valuation.IsRankOneDiscrete` instance is
  mathlib's (`FinitePlace.lean:102`) as well as the import's.  Note mathlib's
  `denseRange_algebraMap` (`AdicValuation.lean:886`) is the **field** statement
  `DenseRange (algebraMap K (v.adicCompletion K))`, not the pin's subring statement, so it
  is not a substitute.  Not reached: the `SeparableSpace` instance :20,
  `ValuationSubring.subtype_inj` :57, the `ValuationSubring` unit helpers :61/:81,
-/
import FLTForHuman.AlgebraicCurve.Place.AdicCompletion
import FLTForHuman.RingTheory.DedekindDomain.IntegralClosure
import FLTForHuman.Topology.Algebra.ModuleTopology
import FLTForHuman.Topology.Algebra.UniformRing
import FLTForHuman.Algebra.RightActionInstances
import FLTForHuman.Topology.Algebra.Valued.WithZeroMulInt
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.TensorProduct.Pi


section

variable {R S : Type*} [Ring R]

-- pin: Subring.toSubmodule (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:17)
def Subring.toSubmodule (S : Subring R) : Submodule S R where
  __ := S
  smul_mem' x y h := by
    rw [smul_def, smul_eq_mul]
    apply S.mul_mem (SetLike.coe_mem x) h

section

-- pin: Pi.semialgHom (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:25)
def Pi.semialgHom {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) :
    A →ₛₐ[φ] (i : I) → f i where
  __ := RingHom.pi fun i ↦ (g i).toRingHom
  map_smul' r a := by ext; simp [RingHom.pi]

-- pin: Pi.semialgHom_apply (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:33)
@[simp]
theorem Pi.semialgHom_apply {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R]
    [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → A →ₛₐ[φ] f i) (a : A) (i : I) :
    (Pi.semialgHom _ φ g) a i = g i a :=
  rfl

-- pin: Pi.semialgHomPi (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:40)
def Pi.semialgHomPi {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i) :
    ((j : J) → g j) →ₛₐ[φ] (i : I) → f i where
  toFun x w := p w (x (r w))
  map_one' := by simp [Pi.one_def]
  map_mul' x y := funext fun w => by simp [map_mul]
  map_zero' := by simp [Pi.zero_def]
  map_add' x y := funext fun w => by simp [map_add]
  map_smul' k x := funext fun w => (p w).map_smul' k (x (r w))

-- pin: Pi.semialgHomPi_apply (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:53)
@[simp]
theorem Pi.semialgHomPi_apply {I J : Type*} {R S : Type*} (f : I → Type*)
    (g : J → Type*) [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)]
    [(j : J) → Algebra R (g j)] {r : I → J} (p : (i : I) → g (r i) →ₛₐ[φ] f i)
    (a : (j : J) → g j) (i : I) :
    Pi.semialgHomPi _ _ p a i = p i (a (r i)) := rfl

-- pin: AlgEquiv.piCongrFiberwise (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:60)
def AlgEquiv.piCongrFiberwise {α : Type*} {β : Type*} {R : Type*} {γ₁ : α → Type*} {γ₂ : β → Type*}
    {f : α → β} [CommSemiring R] [(a : α) → Semiring (γ₁ a)] [(b : β) → Semiring (γ₂ b)]
    [(a : α) → Algebra R (γ₁ a)] [(b : β) → Algebra R (γ₂ b)]
    (e : (b : β) → ((x : { x : α // f x = b }) → γ₁ x.1) ≃ₐ[R] γ₂ b) :
    ((a : α) → γ₁ a) ≃ₐ[R] ((b : β) → γ₂ b) where
  __ := Equiv.piCongrFiberwise fun _ => (e _).toEquiv
  map_add' _ _ := by funext b; simp [← Pi.add_def]
  map_mul' _ _ := by funext b; simp [← Pi.mul_def]
  commutes' r := by funext b; simp [← (e b).commutes' r, Pi.algebraMap_def]

section
open scoped TensorProduct
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*}

-- pin: SemialgHom.baseChange_of_algebraMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:76)
noncomputable
def SemialgHom.baseChange_of_algebraMap [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) :
    S ⊗[R] A →ₐ[S] B :=
  letI : Algebra R B := Algebra.compHom _ (algebraMap R S)
  have : IsScalarTower R S B := .of_algebraMap_eq fun _ ↦ rfl
  let ρ : A →ₐ[R] B := {
    toRingHom := ψ.toRingHom
    commutes' := ψ.commutes
  }
  Algebra.TensorProduct.lift (Algebra.ofId S _) ρ fun s a ↦ by
    change (Algebra.ofId S B s) * (ρ a) = (ρ a) * (Algebra.ofId S B s)
    rw [Algebra.ofId_apply]
    exact Algebra.commutes s (ρ a)

-- pin: SemialgHom.baseChange_of_algebraMap_tmul (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:87)
theorem SemialgHom.baseChange_of_algebraMap_tmul [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (s : S) (a : A) :
    ψ.baseChange_of_algebraMap (s ⊗ₜ[R] a) = algebraMap _ _ s * ψ a := by
  simp [SemialgHom.baseChange_of_algebraMap, Algebra.TensorProduct.lift_tmul,
    SemialgHom.toLinearMap_eq_coe, Algebra.ofId_apply]

-- pin: SemialgHom.baseChange_of_algebraMap_tmul_right (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:93)
@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_right [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (a : A) :
    ψ.baseChange_of_algebraMap (1 ⊗ₜ[R] a) = ψ a := by
  simp [SemialgHom.baseChange_of_algebraMap, Algebra.TensorProduct.lift_tmul,
    SemialgHom.toLinearMap_eq_coe, Algebra.ofId_apply]

-- pin: SemialgHom.baseChange_of_algebraMap_tmul_left (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:99)
@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_left [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : A →ₛₐ[algebraMap R S] B) (s : S) :
    ψ.baseChange_of_algebraMap (s ⊗ₜ[R] 1) = algebraMap _ _ s := by
  simp [SemialgHom.baseChange_of_algebraMap, Algebra.TensorProduct.lift_tmul,
    SemialgHom.toLinearMap_eq_coe, Algebra.ofId_apply]

-- pin: instIsBiscalarBaseChangeOfAlgebraMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:106)
open scoped TensorProduct.RightActions in

instance SemialgHom.instIsBiscalarBaseChangeOfAlgebraMap [Algebra R S] [CommSemiring A]
    [Algebra R A] [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    letI := ψ.toAlgebra
    IsBiscalar S A ψ.baseChange_of_algebraMap :=
  letI := ψ.toAlgebra
  { map_smul₁ := fun s x => map_smulₛₗ (ψ.baseChange_of_algebraMap) s x
    map_smul₂ := fun a x => by
      induction x using TensorProduct.inductionOn with
      | tmul x y =>
        simp [TensorProduct.smul_tmul', -algebraMap_smul,
          algebra_compatible_smul B a, SemialgHom.baseChange_of_algebraMap_tmul,
          RingHom.algebraMap_toAlgebra, SemialgHom.toLinearMap_eq_coe]
        ring_nf
      | add x y hx hy => simp_all }

-- pin: SemialgHom.baseChangeRightOfAlgebraMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:125)
open scoped TensorProduct.RightActions in

noncomputable
def SemialgHom.baseChangeRightOfAlgebraMap [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    letI := ψ.toAlgebra
    S ⊗[R] A →ₐ[A] B :=
  letI := ψ.toAlgebra
  { ψ.baseChange_of_algebraMap with
    commutes' := fun a => by
      change ψ.baseChange_of_algebraMap (1 ⊗ₜ[R] a) = algebraMap A B a
      rw [SemialgHom.baseChange_of_algebraMap_tmul_right, RingHom.algebraMap_toAlgebra]
      rfl }

-- pin: SemialgHom.baseChangeRightOfAlgebraMap_apply (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:135)
open scoped TensorProduct.RightActions in
@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_apply [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) (x : S ⊗[R] A) :
    baseChangeRightOfAlgebraMap ψ x = baseChange_of_algebraMap ψ x :=
  rfl

-- pin: SemialgHom.baseChangeRightOfAlgebraMap_coe (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:143)
open scoped TensorProduct.RightActions in
@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_coe [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B]
    (ψ : A →ₛₐ[algebraMap R S] B) :
    ⇑ψ.baseChangeRightOfAlgebraMap = ⇑ψ.baseChange_of_algebraMap :=
  funext_iff.2 <| ψ.baseChangeRightOfAlgebraMap_apply

variable (F : Type*) [CommSemiring F] {A : Type*} [Ring A]
    [Algebra F A]

-- pin: LinearEquiv.mulLeft (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:152)
def _root_.LinearEquiv.mulLeft (u : Aˣ) : A ≃ₗ[F] A where
  toFun x := u * x
  invFun y := u⁻¹ * y
  left_inv x := by simp
  right_inv y := by simp
  map_add' x₁ x₂ := left_distrib ↑u x₁ x₂
  map_smul' f x := by simp

-- pin: LinearEquiv.coe_mulLeft (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:161)
@[simp]
theorem LinearEquiv.coe_mulLeft (u : Aˣ) :
    (LinearEquiv.mulLeft F u : A →ₗ[F] A) = LinearMap.mulLeft F (u : A) :=
  rfl

-- pin: LinearEquiv.mulRight (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:165)
def _root_.LinearEquiv.mulRight (u : Aˣ) : A ≃ₗ[F] A where
  toFun x := x * u
  invFun y := y * u⁻¹
  left_inv x := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]
  map_add' x₁ x₂ := right_distrib x₁ x₂ u
  map_smul' f x := by simp

-- pin: LinearEquiv.coe_mulRight (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:174)
@[simp]
theorem LinearEquiv.coe_mulRight (u : Aˣ) :
    (LinearEquiv.mulRight F u : A →ₗ[F] A) = LinearMap.mulRight F (u : A) :=
  rfl

section

section Basis

open scoped TensorProduct

open scoped TensorProduct.RightActions

variable {R : Type*} (A : Type*) {B : Type*} {ι : Type*} [CommSemiring R]
variable [CommSemiring A] [Algebra R A] [Fintype ι]
variable [CommSemiring B] [Algebra R B]

-- pin: Module.Basis.rightBaseChange (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:191)
noncomputable
def Module.Basis.rightBaseChange [DecidableEq ι] (b : Module.Basis ι R A) :
    Module.Basis ι B (A ⊗[R] B) where
  repr :=
    let comm : B ⊗[R] A ≃ₗ[B] A ⊗[R] B :=
      TensorProduct.RightActions.Module.TensorProduct.comm R B A
    let π : B ⊗[R] A ≃ₗ[B] (ι → B) :=
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl B B)
        b.equivFun).trans
      (TensorProduct.piScalarRight _ _ _ _)
    let finite : (ι →₀ B) ≃ₗ[B] (ι → B) := Finsupp.linearEquivFunOnFinite B B ι
    comm.symm.trans π |>.trans finite.symm

-- pin: Module.Basis.rightBaseChange_repr (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:205)
@[simp]
lemma Module.Basis.rightBaseChange_repr [DecidableEq ι] (b : Module.Basis ι R A) (i) (x : B) :
    (b.rightBaseChange A).repr (b i ⊗ₜ x) = Finsupp.single i x := by
  have : ∑ (j : ι), (Pi.single i (1 : R) : ι → R) j • (b j) = b i := by
    conv =>
      lhs
      arg 2
      intro j
      rw [Pi.single_comm, Pi.single_apply_smul]
    simp
  rw [← LinearEquiv.eq_symm_apply]
  simp [rightBaseChange, this]

-- pin: Module.Basis.rightBaseChange_apply (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:218)
@[simp]
lemma Module.Basis.rightBaseChange_apply [DecidableEq ι] (b : Basis ι R A) (i) :
    b.rightBaseChange A i = b i ⊗ₜ (1 : B) := by
  rw [apply_eq_iff]
  exact rightBaseChange_repr A b i 1

end Basis

section Finrank

namespace TensorProduct

open scoped TensorProduct.RightActions

variable {R : Type*} (A : Type*) {B : Type*} [CommRing R]
  [CommSemiring A] [Algebra R A] [CommRing B] [Algebra R B] [Nontrivial B]

-- pin: TensorProduct.finrank_rightAlgebra (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:234)
lemma finrank_rightAlgebra [Module.Finite R A] [Module.Free R A] :
    Module.finrank B (A ⊗[R] B) = Module.finrank R A := by
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R B)
  let b := Module.Free.chooseBasis R A
  let b' : Module.Basis _ _ (A ⊗[R] B) := b.rightBaseChange A
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']

end TensorProduct

end Finrank

end

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

open Valuation.IsRankOneDiscrete in

-- pin: closureAlgebraMapIntegers_eq_prodIntegers (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:252)
theorem closureAlgebraMapIntegers_eq_prodIntegers {ι : Type*}
    (v : ι → HeightOneSpectrum A)
    (injective : Function.Injective v) :
    closure (SetLike.coe (algebraMap A ((i : ι) → (v i).adicCompletion K)).range) =
    (Set.pi Set.univ (fun (i : ι) ↦ ((v i).adicCompletionIntegers K).carrier)) := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro c ⟨a, ha⟩ i -
      rw [← ha]
      simp only [Pi.algebraMap_apply]
      exact coe_mem_adicCompletionIntegers (v i) a
    · apply isClosed_set_pi
      rintro w -
      apply Valued.isClosed_valuationSubring
  · intro f hf
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Pi.zero_def, nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨I, t, htn, hts⟩ := hU
    choose g' hg' using fun w => (Valued.is_topological_valuation (t w)).mp (htn w)
    let g := fun w ↦ Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt _).toMulEquiv (g' w)
    obtain ⟨a, ha⟩ :=
      exists_forall_adicValued_sub_lt K I g v injective (fun w => ⟨f w, hf w ⟨⟩⟩)
    use algebraMap A _ a
    constructor
    · rw [RingHom.coe_range]
      exact Set.mem_range_self a
    · refine hts fun w hw ↦ hg' w ?_
      rw [Set.mem_ofPred_eq, ← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
        valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
          (valuedAdicCompletion_surjective K (v w))]
      exact ha w hw

-- pin: denseRange_of_prodAlgebraMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:285)
theorem denseRange_of_prodAlgebraMap {ι : Type*} [Finite ι]
    {valuation : ι → HeightOneSpectrum A} (injective : Function.Injective valuation) :
    DenseRange (algebraMap K ((i : ι) → (valuation i).adicCompletion K)) := by
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  let S := Set.range (algebraMap K ((i : ι) → (valuation i).adicCompletion K))

  have hint : Set.pi Set.univ (fun (i : ι) ↦ ((valuation i).adicCompletionIntegers K).carrier)
      ⊆ closure S := by
    rw [← closureAlgebraMapIntegers_eq_prodIntegers _ _ injective]
    apply closure_mono
    exact fun _ ⟨a, ha⟩ ↦ ⟨algebraMap A K a, ha⟩

  have hmul : ∀x, x ∈ closure S → ∀k : K, k • x ∈ closure S := by
    intro x h k
    let f := fun (z : (i : ι) → (valuation i).adicCompletion K) ↦ k • z
    have hf : ContinuousAt f x := Continuous.continuousAt (continuous_const_smul k)
    apply closure_mono _ <| mem_closure_image hf h
    rintro x ⟨_, ⟨z, rfl⟩, rfl⟩
    use k • algebraMap K _ z
    ext i
    simp [Algebra.smul_def, f]

  intro x
  obtain ⟨k, y, hy, hx⟩ := adicCompletion.eq_mul_pi_adicCompletionIntegers K valuation x
  exact hx ▸ hmul y (hint hy) k

end IsDedekindDomain.HeightOneSpectrum

section

open scoped WithZero Valued TensorProduct
open Valuation.IsRankOneDiscrete WithZero

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]

section assumptions

variable [IsIntegralClosure B A L] [FiniteDimensional K L]

example : IsDomain B := by
  have foo : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective B A _
  have bar : IsDomain L := inferInstance
  exact Function.Injective.isDomain _ foo

example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L

example [IsDomain B] [Algebra.IsSeparable K L] : IsDedekindDomain B :=
  IsIntegralClosure.isDedekindDomain A K L B

example [IsDedekindDomain B] : IsFractionRing B L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L B

example [Algebra.IsSeparable K L] : Module.Finite A B :=
  have := IsIntegralClosure.isNoetherian A K L B
  Module.IsNoetherian.finite A B

example : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L

end assumptions

variable [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

namespace IsDedekindDomain.HeightOneSpectrum

variable (v : HeightOneSpectrum A) {A B}

local notation "σ" => fun v w => algebraMap (WithVal (HeightOneSpectrum.valuation K v))
    (WithVal (HeightOneSpectrum.valuation L w))

private theorem continuousAdd_withVal_pin (w : HeightOneSpectrum B) :
    ContinuousAdd (WithVal (HeightOneSpectrum.valuation L w)) := inferInstance

omit [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsIntegral A B] in
private theorem addMonoidHomClass_withVal_pin (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) :
    AddMonoidHomClass (WithVal (HeightOneSpectrum.valuation K v) →+* WithVal (HeightOneSpectrum.valuation L w))
      (WithVal (HeightOneSpectrum.valuation K v)) (WithVal (HeightOneSpectrum.valuation L w)) := inferInstance

private theorem isTopologicalAddGroup_withVal_pin (v : HeightOneSpectrum A) :
    IsTopologicalAddGroup (WithVal (HeightOneSpectrum.valuation K v)) := inferInstance

attribute [local instance] continuousAdd_withVal_pin addMonoidHomClass_withVal_pin isTopologicalAddGroup_withVal_pin

-- pin: adicValued.continuous_algebraMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:371)
lemma adicValued.continuous_algebraMap
   (w : HeightOneSpectrum B) (hvw : w.under A = v) :
    Continuous (σ v w) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γL _
  let e := v.asIdeal.ramificationIdx' w.asIdeal
  let σL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let σw := valueGroup₀_equiv_withZeroMulInt (w.valuation L)
  let m : ℤᵐ⁰ := σw (σL γL)

  let σv := valueGroup₀_equiv_withZeroMulInt (v.valuation K)
  let σK := (WithVal.valueGroupOrderIso₀ (v.valuation K))
  let γK := σK.symm (σv.symm (exp (m.log / e)))
  have hγK : γK ≠ 0 := by simp [γK]
  use .mk0 _ hγK
  simp only [Units.val_mk0, Set.mem_ofPred_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀; · simp
  rw [σK.lt_symm_apply] at hx
  replace hx := (WithVal.valueGroupOrderIso₀_restrict (v.valuation K) x).symm.trans_lt hx
  rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K),
    OrderMonoidIso.apply_symm_apply, ← log_lt_log (by simp_all) (by simp)] at hx
  rw [← σL.strictMono.lt_iff_lt]
  refine lt_of_eq_of_lt (WithVal.valueGroupOrderIso₀_restrict (w.valuation L) _) ?_
  rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L),
    WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, ← valuation_comap A,
    ← log_lt_log (by simp_all) (by simp), log_pow, nsmul_eq_mul, mul_comm]
  subst hvw
  apply Int.mul_lt_of_lt_ediv (mod_cast pos_of_ne_zero (ramificationIdx_ne_zero A B
    (algebraMap_injective_of_field_isFractionRing A B K L) w)) hx

namespace Extension

variable {v} (w : v.Extension B)

-- pin: WithVal.semialgebraMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:412)
@[simps!]
def _root_.WithVal.semialgebraMap {R S Γ₀ Γ₀' : Type*} [CommRing R]
    [CommRing S] [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀']
    [Algebra R S] (v : Valuation R Γ₀) (w : Valuation S Γ₀') :
    WithVal v →ₛₐ[algebraMap R S] WithVal w where
  __ := algebraMap (WithVal v) (WithVal w)
  map_smul' r x := by
    simp [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, Algebra.smul_def]

-- pin: adicCompletionSemialgHomCompletion (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:420)
noncomputable def adicCompletionSemialgHomCompletion :
    (v.valuation K).Completion →ₛₐ[algebraMap K L] (w.1.valuation L).Completion :=
  .restrictScalars (WithVal.semialgebraMap (v.valuation K) (w.1.valuation L)) <|
    UniformSpace.Completion.mapSemialgHom _ <| adicValued.continuous_algebraMap K L v w.1 w.2

-- pin: adicCompletionSemialgHom (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:425)
noncomputable def adicCompletionSemialgHom :
    v.adicCompletion K →ₛₐ[algebraMap K L] w.1.adicCompletion L where
  toFun x := .ofCompletion (adicCompletionSemialgHomCompletion K L w x.toCompletion)
  map_add' x y := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_add, map_add]
  map_smul' k x := by
    apply adicCompletion.ext
    exact (adicCompletionSemialgHomCompletion K L w).map_smul k x.toCompletion
  map_zero' := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_zero, map_zero]
  map_one' := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_one, map_one]
  map_mul' x y := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_mul, map_mul]

-- pin: adicCompletionSemialgHom_apply (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:444)
lemma adicCompletionSemialgHom_apply (x : v.adicCompletion K) :
    w.adicCompletionSemialgHom K L x =
      .ofCompletion (adicCompletionSemialgHomCompletion K L w x.toCompletion) := rfl

-- pin: toCompletion_adicCompletionSemialgHom (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:448)
lemma toCompletion_adicCompletionSemialgHom (x : v.adicCompletion K) :
    (w.adicCompletionSemialgHom K L x).toCompletion =
      adicCompletionSemialgHomCompletion K L w x.toCompletion := rfl

-- pin: adicCompletionSemialgHom_coe (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:452)
lemma adicCompletionSemialgHom_coe (x : WithVal (v.valuation K)) :
    w.adicCompletionSemialgHom K L x = algebraMap K L x.ofVal :=
  (w.adicCompletionSemialgHom K L).commutes _

open WithZeroTopology in

-- pin: valued_adicCompletionSemialgHom (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:458)
lemma valued_adicCompletionSemialgHom (x) :
    Valued.v (adicCompletionSemialgHom K L w x) = Valued.v x ^
      (w.1.under A).asIdeal.ramificationIdx' w.1.asIdeal := by
  obtain ⟨y, rfl⟩ := adicCompletion.ofCompletion_surjective K v x
  revert y
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact ((Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K)).comp
      (adicCompletion.continuous_ofCompletion K v)).pow _
  · exact (Valued.continuous_valuation_of_surjective (w.1.valuedAdicCompletion_surjective L)).comp
      ((adicCompletion.continuous_ofCompletion L w.1).comp
        (UniformSpace.Completion.continuous_map.comp
          ((adicCompletion.continuous_toCompletion K v).comp (adicCompletion.continuous_ofCompletion K v))))
  intro a
  rw [adicCompletionSemialgHom_coe]
  simp only [adicCompletion.valued_coe]
  rw [← valuation_comap (A := A) (K := K) (L := L) (B := B) (w := w.1)]
  simp only [w.2]
  congr 1
  rw [adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply]
  rfl

-- pin: adicCompletionSemialgHom_image_adicCompletionIntegers (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:480)
lemma adicCompletionSemialgHom_image_adicCompletionIntegers :
    w.adicCompletionSemialgHom K L '' (v.adicCompletionIntegers K) ⊆
      w.1.adicCompletionIntegers L := by
  rintro y ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx ⊢
  rw [w.valued_adicCompletionSemialgHom K L]
  rwa [pow_le_one_iff]
  exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1

-- pin: instAlgebraAdicCompletionExtension (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:490)
noncomputable
instance : Algebra (v.adicCompletion K) (w.1.adicCompletion L) :=
  (w.adicCompletionSemialgHom K L).toAlgebra

-- pin: adicCompletionSemialgHom_continuous (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:493)
lemma adicCompletionSemialgHom_continuous : Continuous (w.adicCompletionSemialgHom K L) :=
  (adicCompletion.continuous_ofCompletion L w.1).comp
    (UniformSpace.Completion.continuous_extension.comp (adicCompletion.continuous_toCompletion K v))

-- pin: instContinuousSMulAdicCompletionExtension (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:497)
instance : ContinuousSMul (adicCompletion K v) (adicCompletion L w.1) := by
  constructor
  have leftCts := w.adicCompletionSemialgHom_continuous K L
  exact Continuous.mul (Continuous.fst' leftCts) continuous_snd

end Extension



namespace adicCompletion

variable (B)

-- pin: adicCompletion.semialgHomPi (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:544)
noncomputable def semialgHomPi :
    v.adicCompletion K →ₛₐ[algebraMap K L] ∀ w : v.Extension B, w.1.adicCompletion L :=
  Pi.semialgHom _ _ fun i ↦ i.adicCompletionSemialgHom K L

-- pin: adicCompletion.baseChange (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:548)
noncomputable abbrev baseChange :
    L ⊗[K] adicCompletion K v →ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  (semialgHomPi K L B v).baseChange_of_algebraMap

-- pin: adicCompletion.baseChange_tmul_apply (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:552)
lemma baseChange_tmul_apply (x y w) : baseChange K L B v (x ⊗ₜ y) w =
    (algebraMap _ (w.1.adicCompletion L) x) * (algebraMap _ (w.1.adicCompletion L) y) := rfl

open scoped TensorProduct.RightActions in

-- pin: adicCompletion.baseChangeRight (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:557)
noncomputable abbrev baseChangeRight :
    L ⊗[K] adicCompletion K v →ₐ[adicCompletion K v] Π w : v.Extension B, w.1.adicCompletion L :=
  (semialgHomPi K L B v).baseChangeRightOfAlgebraMap

section ModuleTopology

open WithZeroMulInt Valued in

noncomputable local instance :
    Valuation.RankOne (Valued.v : Valuation (adicCompletion K v) ℤᵐ⁰) where
  hom' := (toNNReal (by norm_num : (2 : NNReal) ≠ 0)).comp
    (valueGroup₀_equiv_withZeroMulInt _).toMonoidWithZeroHom
  strictMono' := by
    change StrictMono ((toNNReal (by norm_num : (2 : NNReal) ≠ 0)) ∘
      ⇑(valueGroup₀_equiv_withZeroMulInt _))
    exact (toNNReal_strictMono (by norm_num)).comp
      (valueGroup₀_equiv_withZeroMulInt_strictMono _)
  exists_val_nontrivial := by
    obtain ⟨x, hx1, hx2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    use algebraMap A K x
    rw [valuedAdicCompletion_eq_valuation' v (algebraMap A K x)]
    constructor
    · simpa only [ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rwa [valuation_of_algebraMap, intValuation_lt_one_iff_mem]

attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

-- pin: adicCompletion.baseChangeRight_surjective (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:583)
lemma baseChangeRight_surjective [FiniteDimensional K L] :
    Function.Surjective (baseChangeRight K L B v) :=
  letI : Module.Finite (adicCompletion K v) (L ⊗[K] adicCompletion K v) := inferInstance
  by
  let s := (baseChangeRight K L B v).toLinearMap.range
  have isClosed : IsClosed s.carrier :=
    Submodule.closed_of_finiteDimensional (E := (w : Extension B v) → adicCompletion L w.val) s
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, Submodule.eq_top_iff']
  simp_rw [← Submodule.mem_toAddSubmonoid, ← AddSubmonoid.mem_toSubsemigroup,
      ← AddSubsemigroup.mem_carrier]
  have denseL : DenseRange (algebraMap L ((w : Extension B v) → adicCompletion L w.val)) := by
    have := Extension.finite A K L B v
    exact denseRange_of_prodAlgebraMap _ Subtype.val_injective
  rw [← isClosed.closure_eq]
  apply Dense.mono _ denseL
  rintro _ ⟨l, rfl⟩
  use (l ⊗ₜ 1)

  exact SemialgHom.baseChange_of_algebraMap_tmul_left (semialgHomPi K L B v) l

attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

-- pin: adicCompletion.instModuleFinitePi (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:604)
instance [FiniteDimensional K L] :
    Module.Finite (adicCompletion K v) (Π w : v.Extension B, w.1.adicCompletion L) :=
  letI : Module.Finite (adicCompletion K v) (L ⊗[K] adicCompletion K v) := inferInstance
  .of_surjective (baseChangeRight K L B v).toLinearMap (baseChangeRight_surjective K L B v)

attribute [local instance 9999] Algebra.toModule in

-- pin: adicCompletion.instModuleFiniteExtension (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:610)
instance [FiniteDimensional K L] (w : v.Extension B) :
    Module.Finite (adicCompletion K v) (adicCompletion L w.1) :=
  Module.Finite.of_pi (fun (w : Extension B v) => w.1.adicCompletion L) w

-- pin: adicCompletion.instIsModuleTopology (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:614)
instance instIsModuleTopology [FiniteDimensional K L] (w : v.Extension B) :
    IsModuleTopology (v.adicCompletion K) (w.1.adicCompletion L) := by
  let Kv := adicCompletion K v
  let Lw := adicCompletion L w.1
  let iso : ((Fin (Module.finrank Kv Lw)) → Kv) ≃L[Kv] Lw :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Kv)
  apply IsModuleTopology.iso iso

-- pin: adicCompletion.instIsModuleTopologyPi (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:622)
instance instIsModuleTopologyPi [FiniteDimensional K L] :

    IsModuleTopology (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) := by
  let := Extension.finite A K L B v
  exact IsModuleTopology.instPi

open scoped TensorProduct.RightActions in

-- pin: adicCompletion.baseChangeRight_isOpenQuotientMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:630)
lemma baseChangeRight_isOpenQuotientMap [FiniteDimensional K L] :
    IsOpenQuotientMap (baseChangeRight K L B v) := by
  have : T2Space (L ⊗[K] adicCompletion K v) :=
    IsModuleTopology.t2Space' (K := (adicCompletion K v))
  have hsurj := baseChangeRight_surjective K L B v
  rw [← AlgHom.coe_toLinearMap]
  exact ⟨hsurj, LinearMap.continuous_of_finiteDimensional _,
    LinearMap.isOpenMap_of_finiteDimensional _ hsurj⟩

end ModuleTopology

end adicCompletion

section ModuleTopology

open Extension adicCompletion

variable (B)

-- pin: HeightOneSpectrum.tensorAdicCompletionIntegersTo (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:649)
noncomputable def tensorAdicCompletionIntegersTo :
    B ⊗[A] adicCompletionIntegers K v →ₐ[B] L ⊗[K] adicCompletion K v :=
  Algebra.TensorProduct.lift
    (Algebra.algHom _ _ _)
    ((Algebra.TensorProduct.includeRight.restrictScalars A).comp (IsScalarTower.toAlgHom _ _ _))
    (fun _ _ ↦ .all _ _)

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
-- pin: tensorAdicCompletionIntegersTo_tmul (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:658)
@[simp]
lemma tensorAdicCompletionIntegersTo_tmul (v : HeightOneSpectrum A) (b : B)
    (x : v.adicCompletionIntegers K) : tensorAdicCompletionIntegersTo K L B v (b ⊗ₜ x) =
      (algebraMap B L b) ⊗ₜ x.val := by
  simp [tensorAdicCompletionIntegersTo, Algebra.algHom]

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
open scoped TensorProduct.RightActions in

-- pin: tensorAdicCompletionIntegersTo_range_subset_closure (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:666)
lemma tensorAdicCompletionIntegersTo_range_subset_closure [FiniteDimensional K L] :
  (tensorAdicCompletionIntegersTo K L B v).range.carrier ⊆
    closure (algebraMap B (L ⊗[K] adicCompletion K v)).range := by
  rintro _ ⟨s, rfl⟩
  induction s using TensorProduct.inductionOn with
    | add x y hx hy =>

        rw [RingHom.map_add]
        apply map_mem_closure₂ _ hx hy _
        · exact (ModuleTopology.continuousAdd _ _).continuous_add
        intro _ ha _ hb
        exact add_mem ha hb
    | tmul b a' =>

        simp only [RingHom.coe_range, tensorAdicCompletionIntegersTo,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
          AlgHom.coe_comp, AlgHom.coe_restrictScalars', IsScalarTower.coe_toAlgHom',
          Function.comp_apply, ValuationSubring.algebraMap_apply,
          Algebra.TensorProduct.includeRight_apply]

        let f (y : ↥(adicCompletionIntegers K v)) : (L ⊗[K] adicCompletion K v) :=
          (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b * (1 : L) ⊗ₜ[K] (y : adicCompletion K v)
        have hfval : f = fun (y : ↥(adicCompletionIntegers K v)) =>
              (y : adicCompletion K v) • (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b := by
          ext y
          unfold f
          rw [Algebra.smul_def]
          exact mul_comm _ _
        have hcf : ContinuousAt f a' := by
          apply Continuous.continuousAt
          rw [hfval]
          exact continuous_subtype_val.fun_smul continuous_const

        have hy : a' ∈ closure (Set.range (algebraMap A _)) := by
          apply denseRange_of_integerAlgebraMap
        apply mem_closure_image hcf hy
        constructor
        · exact isClosed_closure

        rintro u ⟨_, ⟨a, rfl⟩, rfl⟩
        apply subset_closure
        use algebraMap A B a * b
        unfold f
        rw [Algebra.algebraMap_eq_smul_one (A := (adicCompletionIntegers K v)) a,
          coe_smul_adicCompletionIntegers, ← TensorProduct.smul_tmul, Algebra.ofId_apply,
          Algebra.TensorProduct.algebraMap_apply, RingHom.map_mul, ← Algebra.smul_def]
        simp

open scoped TensorProduct.RightActions in
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L]  in

-- pin: tensorAdicCompletionIntegersTo_isClopen_range (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:721)
lemma tensorAdicCompletionIntegersTo_isClopen_range
    [IsIntegralClosure B A L] [FiniteDimensional K L] :
    IsClopen (SetLike.coe (tensorAdicCompletionIntegersTo K L B v).range) := by

  have : SeparatelyContinuousAdd (L ⊗[K] v.adicCompletion K) :=
    instSeparatelyContinuousAddOfContinuousAdd
  rw [← Subalgebra.coe_toSubring, ← Subring.coe_toAddSubgroup]
  refine OpenAddSubgroup.isClopen ⟨_, ?_⟩

  apply AddSubgroup.isOpen_of_zero_mem_interior
  rw [mem_interior, Subring.coe_toAddSubgroup, Subalgebra.coe_toSubring]

  obtain ⟨ι, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' : Module.Basis ι (adicCompletion K v) (L ⊗[K] (adicCompletion K v)) := by
    classical
    exact b.rightBaseChange L

  let equiv : L ⊗[K] (adicCompletion K v) ≃L[v.adicCompletion K] (ι → adicCompletion K v) :=
    IsModuleTopology.continuousLinearEquiv (b'.equivFun)

  use equiv.symm '' (Set.pi Set.univ (fun _ => SetLike.coe (adicCompletionIntegers K v)))
  refine ⟨?_, ?_, by simp⟩
  · intro t ⟨g, hg, ht⟩

    have hf : ∀ (i : ι), ∃ (w : B), (algebraMap B L w) = (b i) := by
      intro i
      apply IsIntegralClosure.isIntegral_iff.mp (hb i)
    choose f hf_prop using hf
    let b : B ⊗[A] ↥(adicCompletionIntegers K v) := ∑ (i : ι), (f i) ⊗ₜ ⟨g i, hg i trivial⟩
    use b
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, ← ht]
    unfold equiv
    rw [IsModuleTopology.continuousLinearEquiv_symm_apply, Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro x
    simp only [Finset.univ_eq_attach, Finset.mem_attach, tensorAdicCompletionIntegersTo_tmul,
      hf_prop, Module.Basis.rightBaseChange_apply, Algebra.smul_def,
      TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, imp_self, b']
  · rw [ContinuousLinearEquiv.image_symm_eq_preimage]
    apply IsOpen.preimage equiv.continuous
    apply isOpen_set_pi Set.finite_univ
    rintro i -
    exact Valued.isOpen_valuationSubring (v.adicCompletion K)

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
open scoped TensorProduct.RightActions in

-- pin: range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:769)
lemma range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap
    [IsIntegralClosure B A L] [FiniteDimensional K L] :
    Set.range (tensorAdicCompletionIntegersTo K L B v) =
      closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) := by
  apply Set.Subset.antisymm
  · apply tensorAdicCompletionIntegersTo_range_subset_closure
  · apply closure_minimal
    · rintro _ ⟨b, rfl⟩
      use b ⊗ₜ[A] 1
      simp
    · apply IsClopen.isClosed
      apply tensorAdicCompletionIntegersTo_isClopen_range

omit [Algebra A L] [IsScalarTower A B L] in

-- pin: pi_adicCompletionIntegers_eq_closure_range_algebraMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:784)
lemma pi_adicCompletionIntegers_eq_closure_range_algebraMap :
    (Set.univ.pi (fun (w : Extension B v) ↦ (w.1.adicCompletionIntegers L).carrier)) =
      closure (Set.range (algebraMap B _)) := by
  let val := fun (w : Extension B v) ↦ w.1
  have hinj : Function.Injective val :=
    (Set.injective_codRestrict Subtype.property).mp fun _ _ a ↦ a
  rw [← closureAlgebraMapIntegers_eq_prodIntegers L _ hinj]
  rfl

open scoped TensorProduct.RightActions in

-- pin: isClosed_baseChange_image_closure_range_algebraMap (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:795)
lemma isClosed_baseChange_image_closure_range_algebraMap [FiniteDimensional K L] :
    IsClosed ((baseChange K L B v) ''
        closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v)))) := by
  let S := AddSubgroup.map
      (baseChange K L B v).toAddMonoidHom
      (tensorAdicCompletionIntegersTo K L B v).range.toSubring.toAddSubgroup
  have hSclosed : IsClosed S.carrier := by
    apply AddSubgroup.isClosed_of_isOpen
    apply (baseChangeRight_isOpenQuotientMap K L B v).isOpenMap
    apply (tensorAdicCompletionIntegersTo_isClopen_range K L B v).isOpen
  suffices h : (baseChange K L B v) ''
    closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) = S.carrier by
    rwa [h]
  rw [← range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap]
  rfl

-- pin: instMulActionHomClass (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:811)
instance : MulActionHomClass
    (L ⊗[K] adicCompletion K v →ₐ[L] (w : Extension B v) → adicCompletion L w.1) B
    (L ⊗[K] adicCompletion K v) ((w : Extension B v) → adicCompletion L w.1) where
  map_smulₛₗ φ b x := by
    rw [← IsScalarTower.algebraMap_smul L, AlgHom.map_smul_of_tower,
      IsScalarTower.algebraMap_smul, id_def]

open scoped TensorProduct.RightActions in

-- pin: range_baseChange_comp_tensorAdicCompletionTo_eq_pi (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:820)
theorem range_baseChange_comp_tensorAdicCompletionTo_eq_pi [FiniteDimensional K L] :
    Set.range (baseChange K L B v ∘ tensorAdicCompletionIntegersTo K L B v) =
    Set.univ.pi (fun w ↦ (w.1.adicCompletionIntegers L).carrier) := by
  have hrange :
    Set.range (algebraMap B ((w : Extension B v) → adicCompletion L w.1)) =
      (baseChange K L B v) '' (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]
  have hrange' := isClosed_baseChange_image_closure_range_algebraMap K L B v
  rw [Set.range_comp, range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap,
    pi_adicCompletionIntegers_eq_closure_range_algebraMap, hrange, ← IsClosed.closure_eq hrange']
  exact closure_image_closure
    (baseChangeRight_isOpenQuotientMap K L B v).continuous

namespace Extension

variable {B} (w : v.Extension B)

-- pin: Extension.adicCompletionIntegersRingHom (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:838)
noncomputable def adicCompletionIntegersRingHom :
    v.adicCompletionIntegers K →+* w.1.adicCompletionIntegers L :=
  RingHom.restrict (w.adicCompletionSemialgHom K L) _ _
    fun x hx ↦ w.adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨x, hx, rfl⟩

-- pin: Extension.instAlgebraAdicCompletionIntegers (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:843)
noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  (w.adicCompletionIntegersRingHom K L).toAlgebra

-- pin: Extension.integer_algebraMap_apply (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:846)
lemma integer_algebraMap_apply (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) x =
      (w.adicCompletionSemialgHom K L) x.val := rfl

variable {v} in

-- pin: Extension.instAlgebraAdicCompletionIntegersAdicCompletion (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:852)
noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletion L) :=
  Algebra.compHom (w.1.adicCompletion L) (algebraMap _ (adicCompletion K v))

end Extension

-- pin: rightActions_smul_tmul_right (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1064)
open scoped TensorProduct.RightActions in
private lemma rightActions_smul_tmul_right {R S M : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid M] [Module R M] (s : S) (m : M) (t : S) :
    s • (m ⊗ₜ[R] t) = m ⊗ₜ[R] (s * t) := by
  rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
    smul_eq_mul, TensorProduct.comm_symm_tmul]

-- pin: rightActions_smul_eq_one_tmul_mul (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1072)
open scoped TensorProduct.RightActions in
private lemma rightActions_smul_eq_one_tmul_mul {R S M : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [CommSemiring M] [Algebra R M] (s : S) (x : M ⊗[R] S) :
    s • x = (1 ⊗ₜ[R] s) * x := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => rw [smul_add, mul_add, ha, hb]
  | tmul m t => rw [rightActions_smul_tmul_right, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

open scoped TensorProduct.RightActions in
-- pin: instIsBiscalarTensorAdicCompletionIntegersTo (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:858)
instance : IsBiscalar B (v.adicCompletionIntegers K) (tensorAdicCompletionIntegersTo K L B v) where
  map_smul₁ _ _ := map_smul ..
  map_smul₂ s x := by
    have hdom : s • x = (1 ⊗ₜ[A] s) * x := rightActions_smul_eq_one_tmul_mul s x
    rw [hdom, map_mul, tensorAdicCompletionIntegersTo_tmul]
    have hcod : ∀ y : L ⊗[K] adicCompletion K v,
        s • y = (1 ⊗ₜ[K] (s : adicCompletion K v)) * y := by
      intro y
      change (s : adicCompletion K v) • y = _
      rw [rightActions_smul_eq_one_tmul_mul]
    rw [hcod]
    simp

attribute [local instance 9999] Algebra.toModule Algebra.toSMul in
-- pin: instIsScalarTowerAdicCompletionIntegers (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:866)
instance {w : v.Extension B} : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v)
    (w.1.adicCompletion L) := Submonoid.instIsScalarTowerSubtypeMem (adicCompletionIntegers K v)

open scoped TensorProduct.RightActions in

-- pin: tensorAdicCompletionIntegersToPiRight (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:871)
noncomputable def tensorAdicCompletionIntegersToPiRight :
    B ⊗[A] v.adicCompletionIntegers K →ₐ[v.adicCompletionIntegers K]
        Π w : v.Extension B, w.1.adicCompletion L :=
  ((baseChangeRight K L B v).restrictScalars _).comp
    ((tensorAdicCompletionIntegersTo K L B v).changeScalars _)

namespace Extension

variable (w : v.Extension B)

open scoped TensorProduct.RightActions in

-- pin: Extension.tensorAdicCompletionIntegersToAdicCompletion (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:883)
noncomputable def tensorAdicCompletionIntegersToAdicCompletion :
    B ⊗[A] (adicCompletionIntegers K v) →ₐ[adicCompletionIntegers K v] adicCompletion L w.1 :=
  Pi.evalAlgHom _ _ w |>.comp (tensorAdicCompletionIntegersToPiRight K L B v)

open scoped TensorProduct.RightActions in

-- pin: Extension.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:889)
lemma tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers [FiniteDimensional K L] :
    Set.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v) =
      adicCompletionIntegers L w.1 := by
  ext x
  have memrange := (range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L B v)
  rw [Set.ext_iff] at memrange
  constructor
  · rintro ⟨y, rfl⟩
    exact (memrange _).mp (Set.mem_range_self y) w trivial
  · intro hx
    classical
    set x' : (w : Extension B v) → adicCompletion L w.val := Pi.single w x with hx'
    obtain ⟨y, (hy : _ = x')⟩ : x' ∈ Set.range _ := by
      rw [memrange x', Set.mem_pi]
      intro w' _
      by_cases h : w = w'
      · rw [← h, hx', Pi.single_eq_same]
        exact hx
      · rw [hx', Pi.single_eq_of_ne' h]
        exact Subring.zero_mem _
    use y
    have hyw := congr_fun hy w
    simp [hx'] at hyw
    exact hyw

noncomputable local instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  inferInstance

attribute [local instance 9999] Algebra.toSMul Algebra.toModule in
open scoped TensorProduct.RightActions in

-- pin: Extension.instModuleFiniteAdicCompletionIntegers (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:920)
noncomputable instance (priority := 1001) [Module.Finite A B] [FiniteDimensional K L] :
    Module.Finite (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
  let integerSubmodule : Submodule (adicCompletionIntegers K v) (adicCompletion L w.1) :=
    let : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L).toSubring :=
      inferInstanceAs (Algebra (adicCompletionIntegers K v) (adicCompletionIntegers L w.1))
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
        (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
    (adicCompletionIntegers L w.1).toSubmodule.restrictScalars
      (adicCompletionIntegers K v)
  have heq : (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap.range =
      integerSubmodule := by
    ext x
    apply w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v |> Set.ext_iff.mp
  have := Module.Finite.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap
  have := w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v
  exact Module.Finite.equiv <| LinearEquiv.ofEq
    (LinearMap.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap) _ heq

end Extension

end ModuleTopology

namespace adicCompletion

open Extension

section RamificationInertia

variable {v} (w : v.Extension B)

-- pin: WithZero.ofAdd_neg_ofNat_pow (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:950)
lemma _root_.WithZero.ofAdd_neg_ofNat_pow (n : ℕ) :
    (WithZero.coe (Multiplicative.ofAdd (-n : ℤ))) = (Multiplicative.ofAdd (-1 : ℤ)) ^ n := by
  rw [← WithZero.coe_pow, ← ofAdd_nsmul, nsmul_eq_mul, Int.mul_neg_one]

-- pin: ramificationIdx_eq_ramificationIdx (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:954)
theorem ramificationIdx_eq_ramificationIdx :
    (v.completionIdeal K).ramificationIdx' (w.1.completionIdeal L) =
      v.asIdeal.ramificationIdx' w.1.asIdeal := by
  apply Ideal.ramificationIdx'_spec
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [mem_completionIdeal_iff'] at hx
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, integer_algebraMap_apply,
      valued_adicCompletionSemialgHom]
    rw [WithZero.ofAdd_neg_ofNat_pow, w.2]
    apply pow_le_pow_left' hx
  · obtain ⟨ϖ, hϖ⟩ := adicCompletion.exists_uniformizer K v
    have hϖ' : ϖ ∈ v.completionIdeal K := by
      rw [mem_completionIdeal_iff, hϖ]
      decide
    rw [Ideal.map_le_iff_le_comap]
    intro h
    have hcomap := h hϖ'
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, integer_algebraMap_apply,
      valued_adicCompletionSemialgHom, hϖ, ← WithZero.ofAdd_neg_ofNat_pow,
      WithZero.coe_le_coe, w.2, Multiplicative.ofAdd_le] at hcomap
    simp at hcomap

-- pin: inertiaDeg_eq_inertiaDeg (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:977)
theorem inertiaDeg_eq_inertiaDeg :
    Ideal.inertiaDeg w.1.asIdeal A =
      Ideal.inertiaDeg (w.1.completionIdeal L) (adicCompletionIntegers K v) :=
  letI := Algebra.compHom (adicCompletionIntegers L w.1) (algebraMap A B)
  have : IsScalarTower A B (adicCompletionIntegers L w.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    ext
    rw [Algebra.compHom_algebraMap_eq, RingHom.coe_comp, Function.comp_apply,
      algebraMap_completionIntegers, integer_algebraMap_apply, algebraMap_completionIntegers,
      IsScalarTower.algebraMap_apply B L (adicCompletion L w.1),
      ← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
    symm
    apply SemialgHom.commutes
  have : w.1.asIdeal.LiesOver v.asIdeal := ⟨by simp_rw [← w.2]; rfl⟩

  have : (completionIdeal L w.1).LiesOver (completionIdeal K v) := {
    «over» := by
      rw [Ideal.under_def]
      ext x
      rw [Ideal.mem_comap, mem_completionIdeal_iff, mem_completionIdeal_iff,
        integer_algebraMap_apply, valued_adicCompletionSemialgHom K L, pow_lt_one_iff]
      exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1
  }
  calc Ideal.inertiaDeg w.1.asIdeal A
      = Ideal.inertiaDeg (w.1.completionIdeal L) A := by
        rw [Ideal.inertiaDeg_tower (R := A) (S := B)
            (q := w.1.asIdeal) (r := w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, mul_one]
    _ = Ideal.inertiaDeg (w.1.completionIdeal L) (adicCompletionIntegers K v) := by
        rw [Ideal.inertiaDeg_tower (R := A) (S := adicCompletionIntegers K v)
            (q := v.completionIdeal K) (r := w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, one_mul]

noncomputable local instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  inferInstance

end RamificationInertia

end adicCompletion

namespace adicCompletion

open Extension

section RamificationInertia

variable {v} (w : v.Extension B)

-- pin: ramificationIdx_mul_inertiaDeg_eq_finrank (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1013)
theorem ramificationIdx_mul_inertiaDeg_eq_finrank [FiniteDimensional K L] [Module.Finite A B] :
    v.asIdeal.ramificationIdx' w.1.asIdeal * Ideal.inertiaDeg w.1.asIdeal A =
      Module.finrank (adicCompletion K v) (adicCompletion L w.1) :=
  letI : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
      (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v) (adicCompletion L w.1) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  letI : (w.1.completionIdeal L).LiesOver (v.completionIdeal K) := {
    «over» := by
      rw [Ideal.under_def]
      ext x
      rw [Ideal.mem_comap, mem_completionIdeal_iff, mem_completionIdeal_iff,
        integer_algebraMap_apply, valued_adicCompletionSemialgHom K L, pow_lt_one_iff]
      exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1 }
  letI : FaithfulSMul (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) :=
    FaithfulSMul.of_field_isFractionRing (adicCompletionIntegers K v)
      (adicCompletionIntegers L w.1) (adicCompletion K v) (adicCompletion L w.1)
  letI : Subsingleton ((v.completionIdeal K).primesOver (adicCompletionIntegers L w.1)) :=
    ⟨fun Q1 Q2 => Subtype.ext (by
      have h1 : Q1.1.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (Ideal.ne_bot_of_liesOver_of_ne_bot (p := v.completionIdeal K) (v.completionIdeal_ne_bot K)
          Q1.1) Q1.2.1
      have h2 : Q2.1.IsMaximal := Ring.DimensionLEOne.maximalOfPrime
        (Ideal.ne_bot_of_liesOver_of_ne_bot (p := v.completionIdeal K) (v.completionIdeal_ne_bot K)
          Q2.1) Q2.2.1
      rw [IsLocalRing.eq_maximalIdeal h1, IsLocalRing.eq_maximalIdeal h2])⟩
  letI : Fintype ((v.completionIdeal K).primesOver (adicCompletionIntegers L w.1)) :=
    Fintype.ofSubsingleton
      (Ideal.primesOver.mk (v.completionIdeal K) (w.1.completionIdeal L))
  letI : Module.Flat (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
    have : Module.Free (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) :=
      Module.free_of_finite_type_torsion_free'
    exact Module.Flat.of_free
  by
    have hlocal : (v.completionIdeal K).ramificationIdx' (w.1.completionIdeal L) *
        Ideal.inertiaDeg (w.1.completionIdeal L) (adicCompletionIntegers K v) =
        Module.finrank (adicCompletion K v) (adicCompletion L w.1) := by
      have hsum := Ideal.sum_ramification_inertia_eq_finrank (p := v.completionIdeal K)
        (S := adicCompletionIntegers L w.1)
      rw [Finset.sum_eq_single
        (Ideal.primesOver.mk (v.completionIdeal K) (w.1.completionIdeal L))] at hsum
      · rw [show (v.completionIdeal K).ramificationIdx' (w.1.completionIdeal L) =
            (w.1.completionIdeal L).ramificationIdx (adicCompletionIntegers K v) from
          Ideal.ramificationIdx'_eq_ramificationIdx (v.completionIdeal K)
            (w.1.completionIdeal L) (v.completionIdeal_ne_bot K), hsum,
          IsFractionRing.finrank_eq (adicCompletionIntegers K v) (adicCompletion K v)
            (adicCompletionIntegers L w.1) (adicCompletion L w.1)]
      · intro b _ hb
        exact absurd (Subsingleton.elim b _) hb
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [← ramificationIdx_eq_ramificationIdx K L w, inertiaDeg_eq_inertiaDeg K L w]
    exact hlocal

end RamificationInertia

end adicCompletion

namespace adicCompletion

variable [FiniteDimensional K L] [Module.Finite A B] (B)
variable (v : HeightOneSpectrum A) (w : v.Extension B)

local instance : Module.Free (v.adicCompletion K) (adicCompletion L w.1) :=
  Module.free_of_finite_type_torsion_free'

open scoped TensorProduct.RightActions in

-- pin: finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1034)
lemma finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion :
    Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v) =
      Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  letI := Extension.fintype A K L B v
  calc Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v)
    _ = Module.finrank K L := by rw [TensorProduct.finrank_rightAlgebra]
    _ = ∑ (w : Extension B v), Ideal.ramificationIdx' v.asIdeal w.val.asIdeal *
        Ideal.inertiaDeg w.val.asIdeal A := by
        rw [Ideal.sum_ramification_inertia_extensions]
    _ = ∑ (w : Extension B v), Module.finrank (adicCompletion K v) (adicCompletion L w.val) :=
        Finset.sum_congr rfl fun w _ ↦ ramificationIdx_mul_inertiaDeg_eq_finrank K L w
    _ = Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) := by
        rw [Module.finrank_pi_fintype (adicCompletion K v)]

attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

-- pin: baseChange_bijective (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1051)
theorem baseChange_bijective : Function.Bijective (baseChange K L B v) := by
  change Function.Bijective (baseChangeRight K L B v)
  have hsurj := baseChangeRight_surjective K L B v
  refine ⟨?_, hsurj⟩
  have hrank := finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion K L B v
  rwa [← AlgHom.coe_toLinearMap, LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank]

-- pin: baseChangeAlgEquiv (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1058)
noncomputable def baseChangeAlgEquiv :
    L ⊗[K] v.adicCompletion K ≃ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  AlgEquiv.ofBijective (baseChange K L B v) <| baseChange_bijective K L B v

attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

-- pin: baseChangeContinuousAlgEquiv (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1083)
noncomputable def baseChangeContinuousAlgEquiv :
    L ⊗[K] v.adicCompletion K ≃A[L] Π w : v.Extension B, w.1.adicCompletion L :=

  have : IsBiscalar L (v.adicCompletion K) (baseChangeAlgEquiv K L B v).toAlgHom :=
    { map_smul₁ := fun l x => by exact (baseChange K L B v).toLinearMap.map_smul l x
      map_smul₂ := fun s x => by
        rw [rightActions_smul_eq_one_tmul_mul, map_mul]
        funext w
        rw [Pi.mul_apply, Pi.smul_apply, Algebra.smul_def]
        congr 1

        show baseChange K L B v (1 ⊗ₜ[K] s) w = algebraMap (adicCompletion K v) (adicCompletion L w.1) s
        rw [baseChange_tmul_apply, map_one, one_mul] }
  IsModuleTopology.continuousAlgEquivOfIsBiscalar (v.adicCompletion K)
    (baseChangeAlgEquiv K L B v)

-- pin: integerBaseChangeLinearEquiv (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1099)
noncomputable def integerBaseChangeLinearEquiv :
    B ⊗[A] v.adicCompletion K ≃ₗ[B] ∀ w : v.Extension B, w.1.adicCompletion L :=
  (linearEquivTensorProductModuleLeft A K L B (v.adicCompletion K)).symm.trans
    ((baseChangeAlgEquiv K L B v).toLinearEquiv.restrictScalars B)

-- pin: integerBaseChangeLinearEquiv_tmul_apply (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1105)
@[simp]
lemma integerBaseChangeLinearEquiv_tmul_apply (b x) :
    integerBaseChangeLinearEquiv K L B v (b ⊗ₜ[A] x) w =
      algebraMap B _ b * algebraMap _ _ x := by
  rw [integerBaseChangeLinearEquiv, LinearEquiv.trans_apply,
    linearEquivTensorProductModuleLeft_symm_tmul]
  rfl

-- pin: integerSubmodule (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1112)
noncomputable def integerSubmodule (v : HeightOneSpectrum A) : Submodule A (adicCompletion K v) :=
  let s : Submodule (adicCompletionIntegers K v) _ := (adicCompletionIntegers K v).toSubmodule
  s.restrictScalars A

end adicCompletion

namespace adicCompletionIntegers

open adicCompletion

variable (B)

-- pin: adicCompletionIntegers.tensorCoe (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1124)
noncomputable def tensorCoe : B ⊗[A] v.adicCompletionIntegers K →ₗ[B] B ⊗[A] v.adicCompletion K :=
  TensorProduct.AlgebraTensorModule.lTensor _ _
    (Algebra.algHom A (adicCompletionIntegers K v) (adicCompletion K v))

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] in
-- pin: adicCompletionIntegers.tensorCoe_tmul (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1130)
@[simp]
lemma tensorCoe_tmul (b : B) (x : v.adicCompletionIntegers K) :
    tensorCoe K B v (b ⊗ₜ x) = b ⊗ₜ x.val := rfl

end adicCompletionIntegers

namespace adicCompletion

open Extension

variable [FiniteDimensional K L] [Module.Finite A B]

attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left
  IsScalarTower.right in
-- pin: integerBaseChangeLinearEquiv_bijOn (Definitions/Def_DedekindDomain_Completion_BaseChange.lean:1143)
theorem integerBaseChangeLinearEquiv_bijOn (v : HeightOneSpectrum A) :
    Set.BijOn (integerBaseChangeLinearEquiv K L B v)
      (Set.range (adicCompletionIntegers.tensorCoe K B v))
      (Submodule.pi Set.univ fun (w : Extension B v) ↦ integerSubmodule L w.val) := by
  suffices h : ((integerBaseChangeLinearEquiv K L B v) ''
      (LinearMap.range (adicCompletionIntegers.tensorCoe K B v))) =
      Submodule.pi .univ fun (w : Extension B v) ↦ (integerSubmodule L w.val).restrictScalars A from
    h ▸ Equiv.bijOn_image (integerBaseChangeLinearEquiv K L B v).toEquiv
  apply Eq.trans _ (range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L B v)
  rw [LinearMap.coe_range, ← Set.range_comp, ← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  rw [← AlgHom.coe_restrictScalars' B (baseChange K L B v), ← AlgHom.coe_comp,
    ← AlgHom.coe_toLinearMap]
  congr
  ext
  simp [baseChange_tmul_apply]

end adicCompletion

end IsDedekindDomain.HeightOneSpectrum
