/-
Completion trace sum — `AlgebraicCurve.completionTraceSum_of_isSeparable`, after FLT's
`P2M/Sol/S_AlgebraicCurve_completionTraceSum_of_isSeparable.lean` (867 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_completionTraceSum_of_isSeparable.lean>),
published by
`Theorems/Thm_AlgebraicCurve_completionTraceSum_of_isSeparable.lean` as
`AlgebraicCurve.completionTraceSum_of_isSeparable`.

This is set 3.4's second module: the pin's `KwHgfV352CompletionTraceSum` atom is
discharged for a finite separable extension by the semilocal decomposition

`KwHgfV352CompletionTraceSum = ∑_{w' ∈ v.fiber F} Algebra.trace v.adicCompletion w'.1.adicCompletion`,

whose engine is the tensor-product trace (`gapsw7_x3x_trace_*`), the `v.fiber`
component decomposition (`kwF4R1V384a_semilocalDiag`), its bijectivity from distinct
kernels plus `ramificationIdx * inertiaDeg = finrank`, and finally the two discharge
inputs: distinctness of the component kernels and the `finrank` identity on completions.

Import-discharged (not re-proved here): the 13 pin helpers that `Tate/TraceCompat.lean`
(set 3.3d) already carries with identical statements — `kw_ffgc_norm_adicCompletion_eq`,
`kw_ffgc_absoluteValue_extends`, `kw_ffgc_isIntegral_adicCompletionIntegers_of_algebraic`,
`kw_ffgc_isIntegralClosure_adicCompletionIntegers`, the five `kwF4R1V384a_*`
semilocal-component facts and their three `scoped instance`s, and the two
`kwF4R1V386a_isSeparable_*` rows.

Re-landed `private` (promotion debt, future home `Place/Completion.lean`): the pin's
`Def_DedekindDomain_AdicValuation_InlineSpecific.lean` slice the target reaches —
`completionIdeal`, `mem_completionIdeal_iff` (pin 299/302) and the uniformizer chain
`exists_uniformizer`/`uniformizer_ne_zero`/`uniformizer_not_isUnit`/
`isUnit_adicCompletionIntegers_of_valued_eq_one`/`eq_pow_uniformizer_mul_unit`/
`maximalIdeal_eq_span_uniformizer`/`mem_completionIdeal_pow`
(pin 430/438/447/455/464/513/525).  The pin's `ResidueFieldEquivCompletionResidueField`
(pin 318/325) is replaced by the port's public
`ModularCurve.KwF4R1V410a.kwF4R1V410a_quotientEquiv` at `n = 1`, which is the same
residue-field comparison without re-landing the pin's `exists_adicValued_sub_lt_*`
density chain.

The pin's `p2m_*` scaffolding, its outer `P2MW.S_...` namespace, its `attribute`
disables and its `maxHeartbeats` raises are dropped (the project cap is 4,000,000);
its section/`variable` structure is preserved so every statement is diffed verbatim
from the pin's wrapper.
-/
import FLTForHuman.AlgebraicCurve.Defs.TateResidueCurrency
import FLTForHuman.AlgebraicCurve.Tate.CommFinite
import FLTForHuman.AlgebraicCurve.Place.Completion
import FLTForHuman.AlgebraicCurve.Tate.TraceCompat
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.WeilExchange.FiberOverCount
import Mathlib.NumberTheory.RamificationInertia.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open LinearMap Submodule IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open IsDedekindDomain.HeightOneSpectrum.adicCompletion
open WithZero Multiplicative MonoidWithZeroHom
open AlgebraicCurve AlgebraicCurve.Place
open ModularCurve.KwF4R1V384a
open ModularCurve.KwF4R1V386a
open WithZeroMulInt Valuation.IsRankOneDiscrete
open scoped TensorProduct Valued NNReal WithZero

noncomputable section

/-! ### The unported `InlineSpecific` uniformizer slice (private, promotion debt)

`Def_DedekindDomain_AdicValuation_InlineSpecific.lean` (pin 299–551) supplies
`completionIdeal` and the uniformizer facts reached by the completion
`ramificationIdx'` computation.  The port did not port that module; the rows reached
here are transcribed `private` at the pin's names (already carried `private` in
`Tate/CommFinite.lean`, where a `private` is module-local). -/


/-! ### The tensor-product trace decomposition (the pin's `gapsw7_x3x_*`) -/

section ProductTrace

open scoped TensorProduct

private theorem gapsw7_x3x_trace_pi (R : Type*) [CommRing R] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    [∀ i, Module.Free R (S i)] [∀ i, Module.Finite R (S i)]
    (x : ∀ i, S i) :
    Algebra.trace R (∀ i, S i) x = ∑ i, Algebra.trace R (S i) (x i) := by
  have _em := Classical.em
  classical
  let b : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex R (S i)) R (S i) :=
    fun i => Module.Free.chooseBasis R (S i)
  have key : Algebra.leftMulMatrix (Pi.basis b) x
      = Matrix.blockDiagonal' (fun i => Algebra.leftMulMatrix (b i) (x i)) := by
    refine Matrix.ext fun ji ji' => ?_
    obtain ⟨i, j⟩ := ji
    obtain ⟨i', j'⟩ := ji'
    rcases eq_or_ne i i' with rfl | hne
    · rw [Matrix.blockDiagonal'_apply_eq, Algebra.leftMulMatrix_eq_repr_mul,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i (b i j')) i = x i * b i j' := by
        simp
      rw [hx]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hne,
        Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply, Pi.basis_repr]
      have hx : (x * Pi.single i' (b i' j')) i = 0 := by
        simp [Pi.single_eq_of_ne hne]
      rw [hx]
      simp
  rw [Algebra.trace_eq_matrix_trace (Pi.basis b), key,
    Matrix.trace_blockDiagonal']
  exact Finset.sum_congr rfl fun i _ =>
    (Algebra.trace_eq_matrix_trace (b i) (x i)).symm

private theorem gapsw7_x3x_trace_baseChange (R A B : Type*) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Module.Free R B]
    [Module.Finite R B] (b : B) :
    Algebra.trace A (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b)
      = algebraMap R A (Algebra.trace R B b) := by
  have _em := Classical.em
  have h := LinearMap.trace_baseChange (Algebra.lmul R B b) A
  rw [Algebra.baseChange_lmul] at h
  exact h

private theorem gapsw7_x3x_trace_decomposition_of_prod_iso (R A B : Type*)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Module.Free R B] [Module.Finite R B] {ι : Type*} [Fintype ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)]
    [∀ i, Module.Free A (S i)] [∀ i, Module.Finite A (S i)]
    (e : (A ⊗[R] B) ≃ₐ[A] ∀ i, S i) (b : B) :
    algebraMap R A (Algebra.trace R B b)
      = ∑ i, Algebra.trace A (S i) (e ((1 : A) ⊗ₜ[R] b) i) := by
  have _em := Classical.em
  rw [← gapsw7_x3x_trace_baseChange R A B b,
    ← Algebra.trace_eq_of_algEquiv e ((1 : A) ⊗ₜ[R] b),
    gapsw7_x3x_trace_pi A S]

end ProductTrace

/-! ### The completion-integers local hom and residue-field comparison -/

section IntegerComap

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero MonoidWithZeroHom
open AlgebraicCurve AlgebraicCurve.Place
open scoped AlgebraicCurve.Place

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable (F)
variable [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (W : Place K F')

private theorem kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal
    {x : (W.restrict F).adicCompletionIntegers}
    (hx : x ∈ maximalIdeal (W.restrict F).adicCompletionIntegers) :
    kw_ffgc_adicCompletionComapIntegers F W x ∈ maximalIdeal W.adicCompletionIntegers := by
  have hrpos := W.ramificationIndex_pos (F := F)
  rw [show maximalIdeal (W.restrict F).adicCompletionIntegers
      = (W.restrict F).heightOneSpectrum.completionIdeal F from rfl,
    mem_completionIdeal_iff] at hx
  rw [show maximalIdeal W.adicCompletionIntegers
      = W.heightOneSpectrum.completionIdeal F' from rfl,
    mem_completionIdeal_iff, kw_ffgc_adicCompletionComapIntegers_coe,
    kw_ffgc_valued_adicCompletionComap]
  calc Valued.v (x : (W.restrict F).adicCompletion) ^ W.ramificationIndex F
      < 1 ^ W.ramificationIndex F := pow_lt_pow_left₀ hx zero_le hrpos.ne'
    _ = 1 := one_pow _

private instance kw_ffgc_isLocalHom_adicCompletionComapIntegers :
    IsLocalHom (kw_ffgc_adicCompletionComapIntegers F W) where
  map_nonunit x hx := by
    by_contra hnu
    exact (IsLocalRing.notMem_maximalIdeal.mpr hx)
      (kw_ffgc_adicCompletionComapIntegers_mem_maximalIdeal F W
        ((IsLocalRing.mem_maximalIdeal x).mpr hnu))

end IntegerComap

section ResidueCompletion

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing WithZero
open scoped Valued WithZero
open AlgebraicCurve AlgebraicCurve.Place
open scoped AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (V : Place K F)

/-- The residue field of a place is the residue field of its completion integers.
The pin gets this from `ResidueFieldEquivCompletionResidueField`
(`Def_DedekindDomain_AdicValuation_InlineSpecific.lean:325`); the port reaches the
same comparison through the public `kwF4R1V410a_quotientEquiv` at `n = 1`. -/
private noncomputable def kw_ffgc_residueFieldEquivCompletionResidueField :
    V.ResidueField ≃+* IsLocalRing.ResidueField V.adicCompletionIntegers :=
  (Ideal.quotEquivOfEq (pow_one (IsLocalRing.maximalIdeal V.toValuationSubring)).symm).trans
    ((ModularCurve.KwF4R1V410a.kwF4R1V410a_quotientEquiv V 1).trans
      (Ideal.quotEquivOfEq (pow_one (IsLocalRing.maximalIdeal V.adicCompletionIntegers))))

end ResidueCompletion

/-! ### The semilocal decomposition engine -/

section Semilocal

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain TensorProduct

set_option synthInstance.maxHeartbeats 800000

/-- The port's `SumRamificationInertia` is produced by
`Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` (`WeilExchange/FiberOverCount.lean`);
the pin's scoped instance (`S_..._sum_ramificationIndex_mul_inertiaDeg.lean:963`) is the
same statement.  Re-landed `private` because the port's producer in
`Genus/Stichtenoth.lean` is `private` too. -/
private instance instSumRamificationInertiaOfFiniteDimensional {K E F : Type*} [Field K]
    [Field E] [Field F] [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsIntegral E F] [HasPrincipalDivisors K F]
    [FiniteDimensional E F] [Algebra.IsSeparable E F] :
    SumRamificationInertia K E F :=
  ⟨fun v => by
    have hfe : v.fiber F = v.fiberOver F := Finset.ext fun w => by
      rw [Place.mem_fiber, Place.mem_fiberOver]
    rw [hfe]
    exact Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver v⟩

section FiberAlgebra

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

private instance kwF4R1V384a_instFiniteDimensionalFiberCompletion [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) :
    FiniteDimensional v.adicCompletion w'.1.adicCompletion := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kw_ffgc_finiteDimensional_adicCompletion E w'

end FiberAlgebra

section SemilocalDiag

variable {K : Type*} (F : Type*) [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

private def kwF4R1V384a_semilocalDiag (v : Place K E) :
    v.adicCompletion ⊗[E] F →ₐ[v.adicCompletion]
      ((w' : v.fiber F) → w'.1.adicCompletion) :=
  Pi.algHom v.adicCompletion _ (kwF4R1V384a_semilocalComponent F v)

variable {F}

private theorem kwF4R1V384a_semilocalDiag_apply (v : Place K E) (x : v.adicCompletion ⊗[E] F)
    (w' : v.fiber F) :
    kwF4R1V384a_semilocalDiag F v x w' = kwF4R1V384a_semilocalComponent F v w' x := rfl

private theorem kwF4R1V384a_semilocalDiag_one_tmul (v : Place K E) (g : F) (w' : v.fiber F) :
    kwF4R1V384a_semilocalDiag F v ((1 : v.adicCompletion) ⊗ₜ[E] g) w'
      = algebraMap F w'.1.adicCompletion g := by
  rw [kwF4R1V384a_semilocalDiag_apply, kwF4R1V384a_semilocalComponent_tmul,
    map_one, one_mul]

end SemilocalDiag

section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private def KwF4R1V384aCompletionSemilocalBij : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E),
    Function.Bijective (kwF4R1V384a_semilocalDiag (K := K) (E := E) F v)

end Mint

section SpecificMints

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private def KwF4R1V384aDistinctKernels : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' w'' : v.fiber F), w' ≠ w'' →
    RingHom.ker (kwF4R1V384a_semilocalComponent (K := K) (E := E) F v w').toRingHom
      ≠ RingHom.ker (kwF4R1V384a_semilocalComponent (K := K) (E := E) F v w'').toRingHom

private def KwF4R1V384aFinrankCompletionEF : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F),
    (Module.finrank v.adicCompletion w'.1.adicCompletion : ℤ)
      = (w'.1.ramificationIndex E : ℤ) * (w'.1.inertiaDeg E : ℤ)

end SpecificMints

section BijEngine

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private instance kwF4R1V384a_ker_semilocalComponent_isMaximal
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) :
    (RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (kwF4R1V384a_semilocalComponent F v w').toRingHom
    (kwF4R1V384a_semilocalComponent_surjective v w')

private theorem kwF4R1V384a_semilocalDiag_surjective_of_distinctKernels
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (hdist : KwF4R1V384aDistinctKernels K F E) (v : Place K E) :
    Function.Surjective (kwF4R1V384a_semilocalDiag F v) := by
  classical
  intro y
  let m : v.fiber F → Ideal (v.adicCompletion ⊗[E] F) :=
    fun w' => RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom
  haveI : ∀ w', (m w').IsMaximal :=
    kwF4R1V384a_ker_semilocalComponent_isMaximal v
  have hcop : Pairwise (Function.onFun IsCoprime m) := fun i j hij =>
    Ideal.isCoprime_of_isMaximal (I := m i) (J := m j) (hdist v i j hij)
  choose xw hxw using fun w' => kwF4R1V384a_semilocalComponent_surjective v w' (y w')
  obtain ⟨xbar, hxbar⟩ :=
    Ideal.quotientInfToPiQuotient_surj hcop (fun w' => Ideal.Quotient.mk (m w') (xw w'))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  refine ⟨x, funext fun w' => ?_⟩
  show kwF4R1V384a_semilocalComponent F v w' x = y w'
  have hcomp : Ideal.Quotient.mk (m w') x = Ideal.Quotient.mk (m w') (xw w') := by
    have := congrFun hxbar w'
    rwa [Ideal.quotientInfToPiQuotient_mk' m x w'] at this
  have hmod : x - xw w' ∈ m w' := Ideal.Quotient.eq.mp hcomp
  have hzero : kwF4R1V384a_semilocalComponent F v w' (x - xw w') = 0 := hmod
  rw [map_sub, sub_eq_zero] at hzero
  rw [hzero, hxw w']

private theorem kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF
    [Algebra.IsSeparable E F]
    (hdist : KwF4R1V384aDistinctKernels K F E)
    (hef : KwF4R1V384aFinrankCompletionEF K F E) :
    KwF4R1V384aCompletionSemilocalBij K F E := by
  intro _ _ _ v
  have hsurj := kwF4R1V384a_semilocalDiag_surjective_of_distinctKernels hdist v
  refine ⟨?_, hsurj⟩
  letI srPi : Semiring ((w' : v.fiber F) → w'.1.adicCompletion) := inferInstance
  letI algPi : Algebra v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) :=
    inferInstance
  letI modPi : Module v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) :=
    @Algebra.toModule _ _ _ srPi algPi
  have hdimcod : Module.finrank v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion)
      = Module.finrank E F := by
    have hpi : (Module.finrank v.adicCompletion ((w' : v.fiber F) → w'.1.adicCompletion) : ℕ)
        = ∑ w' : v.fiber F, Module.finrank v.adicCompletion w'.1.adicCompletion := by
      convert Module.finrank_pi_fintype v.adicCompletion using 2 <;>
        exact fun i => inferInstance
    rw [hpi]
    have hsum := @SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg K E F
      ‹Field K› ‹Field E› ‹Field F› ‹Algebra K E› ‹Algebra K F› ‹Algebra E F›
      ‹IsScalarTower K E F› ‹Algebra.IsIntegral E F› ‹HasPrincipalDivisors K F›
      (instSumRamificationInertiaOfFiniteDimensional (K := K) (E := E) (F := F)) v
    rw [← Nat.cast_inj (R := ℤ), Nat.cast_sum]
    calc ∑ w' : v.fiber F,
          ((Module.finrank v.adicCompletion w'.1.adicCompletion : ℤ))
        = ∑ w' : v.fiber F,
            ((w'.1.ramificationIndex E : ℤ) * (w'.1.inertiaDeg E : ℤ)) :=
          Finset.sum_congr rfl fun w' _ => hef v w'
      _ = ∑ w' ∈ v.fiber F,
            ((w'.ramificationIndex E : ℤ) * (w'.inertiaDeg E : ℤ)) :=
          Finset.sum_attach (v.fiber F)
            (fun w => (w.ramificationIndex E : ℤ) * (w.inertiaDeg E : ℤ))
      _ = (Module.finrank E F : ℤ) := hsum
  have hdimdom : Module.finrank v.adicCompletion (v.adicCompletion ⊗[E] F)
      = Module.finrank E F := by
    rw [Module.finrank_tensorProduct, Module.finrank_self, one_mul]
  have hsurj' : Function.Surjective
      (kwF4R1V384a_semilocalDiag F v).toLinearMap := hsurj
  haveI fdPi : FiniteDimensional v.adicCompletion
      ((w' : v.fiber F) → w'.1.adicCompletion) := inferInstance
  exact (@LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    v.adicCompletion (v.adicCompletion ⊗[E] F) _ _ _
    ((w' : v.fiber F) → w'.1.adicCompletion) _ modPi _ fdPi
    (hdimdom.trans hdimcod.symm)
    (kwF4R1V384a_semilocalDiag F v).toLinearMap).mpr hsurj'

end BijEngine

section SemilocalHeadline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private theorem kwF4R1V384a_trace_algebraMap_eq_completionTraceAt
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) (g : F) :
    Algebra.trace v.adicCompletion w'.1.adicCompletion (algebraMap F w'.1.adicCompletion g)
      = AlgebraicCurve.kwHgfV352_completionTraceAt v w'.1 w'.2 g := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  rfl

private theorem kwF4R1V384a_completionTraceSum_of_semilocalBij
    (hbij : KwF4R1V384aCompletionSemilocalBij K F E) :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E := by
  classical
  intro _ _ _ v g
  let e : v.adicCompletion ⊗[E] F ≃ₐ[v.adicCompletion]
      ((w' : v.fiber F) → w'.1.adicCompletion) :=
    AlgEquiv.ofBijective (kwF4R1V384a_semilocalDiag F v) (hbij v)
  rw [gapsw7_x3x_trace_decomposition_of_prod_iso E v.adicCompletion F
        (fun w' : v.fiber F => w'.1.adicCompletion) e g]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [show e ((1 : v.adicCompletion) ⊗ₜ[E] g) w'
      = kwF4R1V384a_semilocalDiag F v ((1 : v.adicCompletion) ⊗ₜ[E] g) w' from rfl,
    kwF4R1V384a_semilocalDiag_one_tmul,
    kwF4R1V384a_trace_algebraMap_eq_completionTraceAt]

private theorem kwF4R1V384a_completionTraceSum_of_distinctKernels_finrankEF
    [Algebra.IsSeparable E F]
    (hdist : KwF4R1V384aDistinctKernels K F E)
    (hef : KwF4R1V384aFinrankCompletionEF K F E) :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V384a_completionTraceSum_of_semilocalBij
    (kwF4R1V384a_completionSemilocalBij_of_distinctKernels_finrankEF hdist hef)

end SemilocalHeadline

end Semilocal

/-! ### The two discharge inputs: distinct component kernels and `finrank` -/

section Discharge

open AlgebraicCurve AlgebraicCurve.Place IsDedekindDomain TensorProduct IsLocalRing
open scoped AlgebraicCurve.Place Valued NNReal WithZero

section DistinctKernels

open scoped Valued NNReal WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private theorem kwF4R1V386a_spectralNorm_eq_absoluteValue [FiniteDimensional E F]
    (w' : Place K F) (y : w'.adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion (w'.restrict E)
    letI : NontriviallyNormedField (w'.restrict E).adicCompletion :=
      Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion ℤᵐ⁰
    spectralNorm (w'.restrict E).adicCompletion w'.adicCompletion y
      = kw_ffgc_absoluteValue E w' y := by
  letI := kw_ffgc_rankOne_adicCompletion (w'.restrict E)
  letI : NontriviallyNormedField (w'.restrict E).adicCompletion :=
    Valued.toNontriviallyNormedField (w'.restrict E).adicCompletion ℤᵐ⁰
  haveI : IsUltrametricDist (w'.restrict E).adicCompletion :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (fun a b => Valuation.norm_add_le Valued.v a b)
  haveI : Algebra.IsAlgebraic (w'.restrict E).adicCompletion w'.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  exact (spectralNorm_unique_field_norm_ext (f := kw_ffgc_absoluteValue E w')
    (kw_ffgc_absoluteValue_extends E w') y).symm

private theorem kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber
    [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w' : v.fiber F) (y : w'.1.adicCompletion) :
    letI := kw_ffgc_rankOne_adicCompletion v
    letI : NontriviallyNormedField v.adicCompletion :=
      Valued.toNontriviallyNormedField v.adicCompletion ℤᵐ⁰
    spectralNorm v.adicCompletion w'.1.adicCompletion y
      = kw_ffgc_absoluteValue E w'.1 y := by
  rcases w' with ⟨w', hw'⟩
  have hv : w'.restrict E = v := Place.mem_fiber.mp hw'
  subst hv
  exact kwF4R1V386a_spectralNorm_eq_absoluteValue (K := K) (E := E) w' y

private theorem kwF4R1V386a_valuedAlgebraMap_le_one_iff (w' : Place K F) (g : F) :
    Valued.v (algebraMap F w'.adicCompletion g) ≤ 1 ↔ g ∈ w'.toValuationSubring :=
  AlgebraicCurve.kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff w' g

private theorem kwF4R1V386a_absoluteValue_algebraMap_le_one_iff
    (w' : Place K F) (g : F) :
    kw_ffgc_absoluteValue E w' (algebraMap F w'.adicCompletion g) ≤ 1
      ↔ g ∈ w'.toValuationSubring := by
  letI := kw_ffgc_rankOne_adicCompletion w'
  have hr : (0 : ℝ) < ((w'.ramificationIndex E : ℝ))⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (w'.ramificationIndex_pos (F := E)))
  show ‖algebraMap F w'.adicCompletion g‖ ^ ((w'.ramificationIndex E : ℝ))⁻¹ ≤ 1
    ↔ g ∈ w'.toValuationSubring
  constructor
  · intro hle
    have hn : ‖algebraMap F w'.adicCompletion g‖ ≤ 1 := by
      by_contra hgt
      have hgt' : 1 < ‖algebraMap F w'.adicCompletion g‖ := not_le.mp hgt
      exact absurd ((Real.one_lt_rpow_iff_of_pos (lt_trans one_pos hgt')).mpr
        (Or.inl ⟨hgt', hr⟩)) (not_lt.mpr hle)
    rw [Valued.toNormedField.norm_le_one_iff] at hn
    exact (kwF4R1V386a_valuedAlgebraMap_le_one_iff w' g).mp hn
  · intro hmem
    have hn : ‖algebraMap F w'.adicCompletion g‖ ≤ 1 := by
      rw [Valued.toNormedField.norm_le_one_iff]
      exact (kwF4R1V386a_valuedAlgebraMap_le_one_iff w' g).mpr hmem
    calc ‖algebraMap F w'.adicCompletion g‖ ^ ((w'.ramificationIndex E : ℝ))⁻¹
        ≤ 1 ^ ((w'.ramificationIndex E : ℝ))⁻¹ :=
          Real.rpow_le_rpow (norm_nonneg _) hn hr.le
      _ = 1 := Real.one_rpow _

set_option backward.isDefEq.respectTransparency false in
private theorem kwF4R1V386a_distinctKernels :
    KwF4R1V384aDistinctKernels K F E := by
  intro _ _ _ v w' w'' hne hker
  apply hne
  have hsurj' := kwF4R1V384a_semilocalComponent_surjective v w'
  have hann : ∀ a ∈ RingHom.ker (kwF4R1V384a_semilocalComponent F v w').toRingHom,
      kwF4R1V384a_semilocalComponent F v w'' a = 0 := fun a ha => by
    have : a ∈ RingHom.ker (kwF4R1V384a_semilocalComponent F v w'').toRingHom :=
      hker ▸ ha
    exact this
  let σ : w'.1.adicCompletion →ₐ[v.adicCompletion] w''.1.adicCompletion :=
    (Ideal.Quotient.liftₐ _ (kwF4R1V384a_semilocalComponent F v w'') hann).comp
      (Ideal.quotientKerAlgEquivOfSurjective hsurj').symm.toAlgHom
  have hσcomp : ∀ x, σ (kwF4R1V384a_semilocalComponent F v w' x)
      = kwF4R1V384a_semilocalComponent F v w'' x := by
    intro x
    have hstep1 : (Ideal.quotientKerAlgEquivOfSurjective hsurj').symm
        (kwF4R1V384a_semilocalComponent F v w' x) = Ideal.Quotient.mk _ x := by
      rw [show kwF4R1V384a_semilocalComponent F v w' x
          = Ideal.quotientKerAlgEquivOfSurjective hsurj' (Ideal.Quotient.mk _ x) from rfl,
        AlgEquiv.symm_apply_apply]
    simp only [σ, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.liftₐ_apply]
    erw [hstep1, Ideal.Quotient.lift_mk]
  have hσF : ∀ g : F, σ (algebraMap F w'.1.adicCompletion g)
      = algebraMap F w''.1.adicCompletion g := by
    intro g
    have h' := hσcomp ((1 : v.adicCompletion) ⊗ₜ[E] g)
    rwa [kwF4R1V384a_semilocalComponent_tmul, map_one, one_mul,
      kwF4R1V384a_semilocalComponent_tmul, map_one, one_mul] at h'
  letI := kw_ffgc_rankOne_adicCompletion v
  letI : NontriviallyNormedField v.adicCompletion :=
    Valued.toNontriviallyNormedField v.adicCompletion ℤᵐ⁰
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hσspec : ∀ y, spectralNorm v.adicCompletion w''.1.adicCompletion (σ y)
      = spectralNorm v.adicCompletion w'.1.adicCompletion y := by
    intro y
    unfold spectralNorm
    congr 1
    exact minpoly.algHom_eq σ hσinj y
  refine Subtype.ext ?_
  refine AlgebraicCurve.Place.ext (K := K) (F := F) (SetLike.ext fun g => ?_)
  rw [← kwF4R1V386a_absoluteValue_algebraMap_le_one_iff (K := K) (E := E) w'.1 g,
    ← kwF4R1V386a_absoluteValue_algebraMap_le_one_iff (K := K) (E := E) w''.1 g,
    ← kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber (K := K) (E := E) v w'
      (algebraMap F w'.1.adicCompletion g),
    ← kwF4R1V386a_spectralNorm_eq_absoluteValue_fiber (K := K) (E := E) v w''
      (algebraMap F w''.1.adicCompletion g),
    ← hσF g, hσspec]

end DistinctKernels

section FinrankCompletionEF

open IsLocalRing Valuation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private theorem kwF4R1V386a_ramificationIdx_completion_eq
    (w' : Place K F) :
    (maximalIdeal (w'.restrict E).adicCompletionIntegers).ramificationIdx'
      (maximalIdeal w'.adicCompletionIntegers) = w'.ramificationIndex E := by
  set e := w'.ramificationIndex E with he
  have hepos : 0 < e := w'.ramificationIndex_pos (F := E)
  obtain ⟨π, hπval⟩ := IsDedekindDomain.HeightOneSpectrum.adicCompletion.exists_uniformizer E
    (w'.restrict E).heightOneSpectrum
  have hmap : (maximalIdeal (w'.restrict E).adicCompletionIntegers).map
      (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers)
        = Ideal.span {algebraMap _ w'.adicCompletionIntegers π} := by
    rw [maximalIdeal_eq_span_uniformizer E (w'.restrict E).heightOneSpectrum hπval,
      Ideal.map_span, Set.image_singleton]
  have hπval' : Valued.v (π : (w'.restrict E).adicCompletion)
      = (↑(Multiplicative.ofAdd (-1 : ℤ)) : ℤᵐ⁰) := hπval
  have hval : Valued.v ((algebraMap (w'.restrict E).adicCompletionIntegers
        w'.adicCompletionIntegers π : w'.adicCompletionIntegers) : w'.adicCompletion)
      = (↑(Multiplicative.ofAdd (-(e : ℤ))) : ℤᵐ⁰) := by
    rw [show ((algebraMap _ w'.adicCompletionIntegers π
          : w'.adicCompletionIntegers) : w'.adicCompletion)
        = kw_ffgc_adicCompletionComap E w' (π : (w'.restrict E).adicCompletion) from
      (kw_ffgc_adicCompletionComapIntegers_coe E w' π).symm,
      kw_ffgc_valued_adicCompletionComap, hπval', ← WithZero.coe_pow, WithZero.coe_inj,
      ← ofAdd_nsmul, nsmul_eq_mul, mul_neg_one, he]
  refine Ideal.ramificationIdx_spec ?_ ?_
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      show maximalIdeal (w'.adicCompletionIntegers : Type _)
        = w'.heightOneSpectrum.completionIdeal F from rfl,
      mem_completionIdeal_pow, hval]
  · rw [hmap, Ideal.span_singleton_le_iff_mem,
      show maximalIdeal (w'.adicCompletionIntegers : Type _)
        = w'.heightOneSpectrum.completionIdeal F from rfl,
      mem_completionIdeal_pow, hval]
    simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le, not_le]
    omega

set_option backward.isDefEq.respectTransparency false in
private theorem kwF4R1V386a_integersToCompletion_commute
    (w' : Place K F) (a : (w'.restrict E).toValuationSubring) :
    algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers
        (algebraMap (w'.restrict E).toValuationSubring
          (w'.restrict E).adicCompletionIntegers a)
      = algebraMap w'.toValuationSubring w'.adicCompletionIntegers
          (restrictInclusion E w' a) := by
  apply Subtype.ext
  exact (kw_ffgc_adicCompletionComap_algebraMap_algebraMap E w' (a : E)).symm

set_option synthInstance.maxHeartbeats 800000 in
private theorem kwF4R1V386a_inertiaDeg_completion_eq
    (w' : Place K F) :
    (maximalIdeal (w'.restrict E).adicCompletionIntegers).inertiaDeg'
      (maximalIdeal w'.adicCompletionIntegers) = w'.inertiaDeg E := by
  haveI : IsLocalHom (algebraMap (w'.restrict E).adicCompletionIntegers
      w'.adicCompletionIntegers) :=
    kw_ffgc_isLocalHom_adicCompletionComapIntegers E w'
  haveI : (maximalIdeal w'.adicCompletionIntegers).LiesOver
      (maximalIdeal (w'.restrict E).adicCompletionIntegers) := by
    have hcomap : (maximalIdeal w'.adicCompletionIntegers).comap
        (algebraMap (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers)
        = maximalIdeal (w'.restrict E).adicCompletionIntegers :=
      ((IsLocalRing.local_hom_TFAE (algebraMap (w'.restrict E).adicCompletionIntegers
        w'.adicCompletionIntegers)).out 1 5).mp ‹IsLocalHom _›
    exact ⟨hcomap.symm⟩
  rw [Ideal.inertiaDeg_algebraMap]
  symm
  refine Algebra.finrank_eq_of_equiv_equiv
    (kw_ffgc_residueFieldEquivCompletionResidueField (w'.restrict E))
    (kw_ffgc_residueFieldEquivCompletionResidueField w') ?_
  ext a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  simp only [RingHom.coe_comp, Function.comp_apply]
  exact congrArg (IsLocalRing.residue w'.adicCompletionIntegers)
    (kwF4R1V386a_integersToCompletion_commute (K := K) (E := E) w' a)

set_option linter.deprecated false in
private theorem kwF4R1V386a_finrankCompletionEF [Algebra.IsSeparable E F] :
    KwF4R1V384aFinrankCompletionEF K F E := by
  intro _ _ _ v wfib
  have hv : wfib.1.restrict E = v := Place.mem_fiber.mp wfib.2
  haveI hsep : Algebra.IsSeparable v.adicCompletion wfib.1.adicCompletion :=
    kwF4R1V386a_isSeparable_fiberCompletion v wfib
  rcases wfib with ⟨w', hw'⟩
  dsimp only at hv hsep ⊢
  subst hv
  haveI : Algebra.IsSeparable (w'.restrict E).adicCompletion w'.adicCompletion := hsep
  haveI : Algebra.IsAlgebraic (w'.restrict E).adicCompletion w'.adicCompletion :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : IsIntegralClosure w'.adicCompletionIntegers
      (w'.restrict E).adicCompletionIntegers w'.adicCompletion :=
    kw_ffgc_isIntegralClosure_adicCompletionIntegers E w'
  haveI : IsNoetherian (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    IsIntegralClosure.isNoetherian (w'.restrict E).adicCompletionIntegers
      (w'.restrict E).adicCompletion w'.adicCompletion w'.adicCompletionIntegers
  haveI : Module.Finite (w'.restrict E).adicCompletionIntegers w'.adicCompletionIntegers :=
    Module.IsNoetherian.finite _ _
  have hpne : maximalIdeal (w'.restrict E).adicCompletionIntegers ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField _
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)
  have hef := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    w'.adicCompletionIntegers (w'.restrict E).adicCompletion w'.adicCompletion hpne
  rw [kwF4R1V386a_ramificationIdx_completion_eq (K := K) w',
    kwF4R1V386a_inertiaDeg_completion_eq (K := K) w'] at hef
  exact_mod_cast hef.symm

end FinrankCompletionEF

section DischargeHeadline

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

private theorem kwF4R1V386a_completionTraceSum_of_isSeparable [Algebra.IsSeparable E F] :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V384a_completionTraceSum_of_distinctKernels_finrankEF
    kwF4R1V386a_distinctKernels kwF4R1V386a_finrankCompletionEF

end DischargeHeadline

end Discharge

namespace AlgebraicCurve

/-- The completion trace sum of a finite separable extension: the trace over the
completion at a place `v` of `E` is the sum of the traces over the completions at the
places of `F` above `v`. -/
theorem completionTraceSum_of_isSeparable
    {K F E : Type*} [Field K] [Field F] [Algebra K F]
    [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [Algebra.IsSeparable E F] :
    AlgebraicCurve.KwHgfV352CompletionTraceSum K F E :=
  kwF4R1V386a_completionTraceSum_of_isSeparable (K := K) (F := F) (E := E)

end AlgebraicCurve

end
