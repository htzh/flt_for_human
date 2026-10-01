/-
Tate residue currency — the shared API definitions of row 3.3, after FLT's
`Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean` (449 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean>).

This is set 3.3a's definitions layer: the `tateComm`/`tateCommTrace` trace-commutator
vocabulary, the Kähler pullback/cotrace of a place, the `kwHgfV352_*` completion
residue rows, the `KwF4gRRTate*` Tate atoms (`CommFinite`, `Agreement`, `ChainRule`,
`TraceCompat`) and the two K-currency residue identities.  The theory that discharges
these atoms lives in `AlgebraicCurve/Tate/`; this module holds only the public API
definitions (plus the five adapter/`rfl` lemmas the pin states beside them), so a
consumer of the definitions does not import the proof theory
(PLAN-RECTIFY-DEFS §2, `Defs/` exception 1/2).

The pin's `import Mathlib` and its nine `Definitions/` imports are replaced by the
port's `Defs` modules; the statements are transcribed textually.  The pin's
`p2m_*` scaffolding and its unused `variable` blocks are dropped.  The two proof-level
v4.34 drifts are recorded in `logs/riemann-roch-friction.md`: `Set.mem_setOf_eq` is
`Set.mem_ofPred_eq` in `regularSubmodule`, and the pin's `FunctionField` open is
dropped (the port has no such namespace); the adic-completion `Algebra K` instance is
the port's own `instAlgebraKAdicCompletionIntegers` rather than a re-declaration.
-/
import FLTForHuman.AlgebraicCurve.Defs.PlaceCompletion
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor
import FLTForHuman.AlgebraicCurve.Defs.LocalResidue
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
import Mathlib.RingTheory.Kaehler.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

open LinearMap Submodule

noncomputable section

namespace ModularCurve.KwF4gRRTate

section FinrankTrace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The trace of an endomorphism restricted to its own range, as an element of the
base field.  This is the pin's `finrankTrace`, the currency of `tateCommTrace`. -/
def finrankTrace (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)] : K :=
  LinearMap.trace K (LinearMap.range φ)
    (φ.restrict (fun x _ => LinearMap.mem_range_self φ x))

end FinrankTrace

section TateComm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The commutator of two endomorphisms, sandwiched by a projection `pA`:
`pA φ pA ψ - pA ψ pA φ`. -/
def tateComm (pA φ ψ : V →ₗ[K] V) : V →ₗ[K] V :=
  pA ∘ₗ φ ∘ₗ pA ∘ₗ ψ - pA ∘ₗ ψ ∘ₗ pA ∘ₗ φ

theorem tateComm_apply (pA φ ψ : V →ₗ[K] V) (x : V) :
    tateComm pA φ ψ x = pA (φ (pA (ψ x))) - pA (ψ (pA (φ x))) := rfl

theorem tateComm_mem_range (pA φ ψ : V →ₗ[K] V) (x : V) :
    tateComm pA φ ψ x ∈ LinearMap.range pA :=
  sub_mem (LinearMap.mem_range_self pA _) (LinearMap.mem_range_self pA _)

theorem tateComm_antisymm (pA φ ψ : V →ₗ[K] V) :
    tateComm pA φ ψ = - tateComm pA ψ φ := by
  unfold tateComm; rw [neg_sub]

/-- `tateComm pA φ ψ` restricted to the range of `pA`. -/
def tateCommRestrict (pA φ ψ : V →ₗ[K] V) :
    LinearMap.range pA →ₗ[K] LinearMap.range pA :=
  (tateComm pA φ ψ).restrict (fun x _ => tateComm_mem_range pA φ ψ x)

theorem tateCommRestrict_apply (pA φ ψ : V →ₗ[K] V) (a : LinearMap.range pA) :
    (tateCommRestrict pA φ ψ a : V) = tateComm pA φ ψ (a : V) := rfl

/-- The trace of the restricted commutator — the Tate residue of `(φ, ψ)` at `pA`. -/
def tateCommTrace (pA φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range (tateCommRestrict pA φ ψ))] : K :=
  finrankTrace (tateCommRestrict pA φ ψ)

end TateComm

section TateFactoring

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- When `φ` and `ψ` commute, the sandwiched commutator factors through the
projection defect `1 - pA`.  This is the pin's factorization that makes the Tate
residue finite-dimensional. -/
theorem tateComm_eq_of_commute {pA φ ψ : V →ₗ[K] V}
    (hcomm : φ ∘ₗ ψ = ψ ∘ₗ φ) (a : V) :
    tateComm pA φ ψ a
      = pA (ψ (φ a - pA (φ a))) - pA (φ (ψ a - pA (ψ a))) := by
  have hφψ : φ (ψ a) = ψ (φ a) := by
    have := congrArg (fun f => f a) (congrArg DFunLike.coe hcomm)
    simpa using this
  rw [tateComm_apply, map_sub, map_sub, map_sub, map_sub, hφψ]
  abel

end TateFactoring

end ModularCurve.KwF4gRRTate

set_option linter.unusedSectionVars false

open AlgebraicCurve.Place

namespace AlgebraicCurve

section CorrectedCarrier

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

/-- The pullback of a Kähler differential along `E → F`. -/
def kaehlerPullback (ωE : Ω[E⁄K]) : Ω[F⁄K] :=
  KaehlerDifferential.map K K E F ωE

end CorrectedCarrier

section KaehlerCotrace

variable (K E F : Type*) [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

/-- The Kähler cotrace `Ω[E⁄K] → Ω[F⁄K]` as an `E`-linear map. -/
abbrev kaehlerCotrace : Ω[E⁄K] →ₗ[E] Ω[F⁄K] :=
  KaehlerDifferential.map K K E F

end KaehlerCotrace

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The `K`-submodule of `F` on which `f ↦ f * w.differentialCoeff ωF` is integral
at `w`. -/
def regularSubmodule (w : Place K F) (ωF : Ω[F⁄K]) : Submodule K F where
  carrier := {f : F | f * w.differentialCoeff ωF ∈ w.toValuationSubring}
  zero_mem' := by simp only [Set.mem_ofPred_eq, zero_mul]; exact zero_mem _
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq, add_mul]; exact add_mem hf hg
  smul_mem' c f hf := by
    simp only [Set.mem_ofPred_eq, Algebra.smul_def, mul_assoc]
    exact mul_mem (w.algebraMap_mem' c) hf

end Place

section LocalResidueCompletion

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

variable [HasCanonicalLocalResidueKStar K E]

/-- The residue at `v` of a completion element, read through the canonical local
residue of an integral approximation. -/
def kwHgfV352_localResidueCompletion (v : Place K E) (xh : v.adicCompletion) :
    v.ResidueField :=
  v.localResidue (kwHgfV352_exists_sub_mem_adicCompletionIntegers v xh).choose

end LocalResidueCompletion

section CompletionTraceAt

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F] [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]

/-- The trace `E → E` of `g ∈ F` at the place `v` of `E`, transported along the
completion map into `v.adicCompletion` (the pin's `kwHgfV352_completionTraceAt`). -/
def kwHgfV352_completionTraceAt [FiniteDimensional E F]
    (v : Place K E) (w' : Place K F) (hw' : w' ∈ v.fiber F) (g : F) :
    v.adicCompletion :=
  Place.mem_fiber.mp hw' ▸ kw_ffgc_completionTraceF' E w' g

end CompletionTraceAt

section MPGKPowBasisLocalMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

/-- The local Tate-agreement row on a power basis of the residue field: the
residue of `θ^j (π^{k+1})⁻¹` times the differential of `ωE` equals the trace of the
completion residue. -/
def KwHgfV352R3MPGKPowBasisLocal : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [∀ w : Place K F, w.FiniteResidue]
    [FiniteDimensional E F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F)
    (_ : ∀ w'' ∈ v.fiber F,
      w''.differentialCoeff (kaehlerPullback K F E ωE) ∈ w''.toValuationSubring)
    (θ : F) (_ : ∀ w' ∈ v.fiber F, θ ∈ w'.toValuationSubring)
    (π : F) (_ : π ≠ 0) (_ : w.ord π = 1)
    (_ : ∀ w' ∈ v.fiber F, w' ≠ w → w'.ord π = 0)
    (j : ℕ) (_ : j < Module.finrank K w.ResidueField) (k : ℕ),
    kaehlerResidueTerm (kaehlerPullback K F E ωE)
        (diagonalHom K F (θ ^ j * (π ^ (k + 1))⁻¹)) w
      = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (kwHgfV352_completionTraceAt v w hw (θ ^ j * (π ^ (k + 1))⁻¹)
              * algebraMap E v.adicCompletion (v.differentialCoeff ωE)))

end MPGKPowBasisLocalMint

section CompletionTraceSumMint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]

/-- The completion trace is the sum of the fiber traces over the places above
`v`. -/
def KwHgfV352CompletionTraceSum : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (g : F),
    algebraMap E v.adicCompletion (Algebra.trace E F g)
      = ∑ w' ∈ (v.fiber F).attach, kwHgfV352_completionTraceAt v w'.1 w'.2 g

end CompletionTraceSumMint

end AlgebraicCurve

set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place LinearMap Submodule
open ModularCurve.KwF4gRRTate

namespace ModularCurve.KwF4gRRTate

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- The integers of the completion `u.adicCompletion` as a `K`-submodule. -/
def adicIntegersKSubmod : Submodule K u.adicCompletion where
  carrier := u.adicCompletionIntegers
  add_mem' := add_mem
  zero_mem' := zero_mem _
  smul_mem' c x hx := by
    rw [Algebra.smul_def]
    exact mul_mem (by
      rw [IsScalarTower.algebraMap_apply K L u.adicCompletion]
      exact (kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
        (u.algebraMap_mem' c)) hx

/-- The projection of the completion onto its integer submodule along a chosen
complement. -/
def tateProj : u.adicCompletion →ₗ[K] u.adicCompletion :=
  letI B := Classical.choose (Submodule.exists_isCompl (adicIntegersKSubmod u))
  (adicIntegersKSubmod u).subtype ∘ₗ
    Submodule.projectionOnto (adicIntegersKSubmod u) B
      (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u)))

end TateProj

section TateResDef

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

/-- Left multiplication by `fh` as a `K`-linear endomorphism of the completion. -/
abbrev lmulK (fh : u.adicCompletion) : u.adicCompletion →ₗ[K] u.adicCompletion :=
  (Algebra.lmul K u.adicCompletion) fh

/-- The Tate residue `tateCommTrace (tateProj u) (lmulK fh) (lmulK gh)`. -/
def tateRes (fh gh : u.adicCompletion)
    [FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)))] : K :=
  tateCommTrace (tateProj u) (lmulK u fh) (lmulK u gh)

end TateResDef

section TateAtoms

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The finiteness atom: the restricted Tate commutator is finite-dimensional over
`K` (row 3.3's target). -/
def KwF4gRRTateCommFinite : Prop :=
  ∀ (u : Place K L) (fh gh : u.adicCompletion),
    FiniteDimensional K (LinearMap.range
      (tateCommRestrict (tateProj u) (lmulK u fh) (lmulK u gh)))

variable [HasCanonicalLocalResidueKStar K L]

/-- The Tate agreement atom: the Tate residue at the uniformizer agrees with the
residue-field trace of the completion residue. -/
def KwF4gRRTateAgreement (hfin : KwF4gRRTateCommFinite K L) : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (fh : u.adicCompletion),
    haveI := hfin u fh (algebraMap L u.adicCompletion u.uniformizer)
    tateRes u fh (algebraMap L u.adicCompletion u.uniformizer)
      = Algebra.trace K u.ResidueField (kwHgfV352_localResidueCompletion u fh)

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]
variable [Algebra E F] [IsScalarTower K E F] [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

/-- The Tate chain rule: the Tate residue is unchanged when the differential
coefficient is folded into the argument. -/
def KwF4gRRTateChainRule (hfinF : KwF4gRRTateCommFinite K F) : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    [Nontrivial Ω[E⁄K]] [Nontrivial Ω[F⁄K]]
    (v : Place K E) [v.DCoordGenerates] (w : Place K F) [w.DCoordGenerates]
    (_ : w ∈ v.fiber F) (fh : w.adicCompletion),
    haveI := hfinF w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
    haveI := hfinF w (fh * algebraMap F w.adicCompletion
      (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
      (algebraMap F w.adicCompletion w.uniformizer)
    tateRes w fh (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes w (fh * algebraMap F w.adicCompletion
          (w.differentialCoeff (kaehlerPullback K F E v.dCoord)))
          (algebraMap F w.adicCompletion w.uniformizer)

/-- Tate compatibility: the Tate residue at `w` of the completion trace of `g`
equals the Tate residue at `v` of `g`. -/
def KwF4gRRTateTraceCompat (hfinF : KwF4gRRTateCommFinite K F)
    (hfinE : KwF4gRRTateCommFinite K E) : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F] [FiniteDimensional E F]
    (v : Place K E) (w : Place K F) (hw : w ∈ v.fiber F) (g : F),
    haveI := hfinF w (algebraMap F w.adicCompletion g)
      (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
    haveI := hfinE v (kwHgfV352_completionTraceAt v w hw g)
      (algebraMap E v.adicCompletion v.uniformizer)
    tateRes w (algebraMap F w.adicCompletion g)
        (algebraMap F w.adicCompletion (algebraMap E F v.uniformizer))
      = tateRes v (kwHgfV352_completionTraceAt v w hw g)
          (algebraMap E v.adicCompletion v.uniformizer)

end TateAtoms

end ModularCurve.KwF4gRRTate

set_option linter.unusedSectionVars false

open AlgebraicCurve AlgebraicCurve.Place KaehlerDifferential

namespace ModularCurve.KwF4R1V391a

section Mint

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [Algebra.IsIntegral E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]

/-- The K-currency Kähler cotrace identity: the residue of the pulled-back
differential equals the trace of the completion residue. -/
def KwF4R1V391aResidueTraceCompletionCommute : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    [∀ w : Place K F, w.FiniteResidue] [FiniteDimensional E F]
    [Nontrivial Ω[E⁄K]] (v : Place K E) [v.DCoordGenerates]
    (w : Place K F) [w.DCoordGenerates] (_ : w ∈ v.fiber F) (g : F),
    kaehlerResidueTerm (kaehlerPullback K F E v.dCoord) (diagonalHom K F g) w
      = Algebra.trace K v.ResidueField
          (kwHgfV352_localResidueCompletion v
            (kwHgfV352_completionTraceAt v w ‹w ∈ v.fiber F› g))

end Mint

end ModularCurve.KwF4R1V391a

set_option linter.unusedSectionVars false

namespace AlgebraicCurve

section KCurrencyRow

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

/-- The fiber Kähler cotrace residue identity: the sum of the residue terms over the
fiber equals the residue term of the traced differential at the base place. -/
def FiberKaehlerCotraceResidueIdentityK : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0),
    ∃ RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK,
      ∀ (v : Place K E) (f : F),
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F f) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F f)) v

end KCurrencyRow

section KCurrencyRowA

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

/-- The fiber-localized form of the K-currency cotrace residue identity: the sum
over the (essentially unique nontrivial) fiber place. -/
def CotraceResidueIdentityOnFiberLocalizedK : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    (RfamF : ∀ w : Place K F, w.CanonicalLocalResidueDataK)
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0),
    ∃ RfamE : ∀ v : Place K E, v.CanonicalLocalResidueDataK,
      ∀ (v : Place K E) (p : F),
        (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
          p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
          p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
        ∑ w ∈ v.fiber F, kaehlerResidueTermKFam RfamF (kaehlerPullback K F E ωE)
            (diagonalHom K F p) w
          = kaehlerResidueTermKFam RfamE ωE (diagonalHom K E (Algebra.trace E F p)) v

end KCurrencyRowA

end AlgebraicCurve

end
