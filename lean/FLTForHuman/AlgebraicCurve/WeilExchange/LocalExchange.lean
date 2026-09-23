/-
The local exchange identity and the normal closure, after FLT's
`P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean>).

The public node `Place.sum_ramificationIndex_mul_inertiaDeg_exchange` is the local
identity T7's divisor exchange reduces to for a single place `wA` of `A`
(`TOPIC-t7-divisor-exchange.md` §1):

  `∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ = w₁.inertiaDeg F * w₂.ramificationIndex F`.

It is proved by the pin's two stages, both kept public: the Galois case
`BifibreW2.exchange_of_isGalois` (a cancellation inside T5's bifibre count) and the
separable reduction through the **normal closure** `Env F E`, which installs the
envelope's `Algebra`/`IsScalarTower`/`IsGalois` instances. The envelope itself
(`Env`, `algebraEnv`, the four tower instances) is `private` instance plumbing, as
in the work order.

The shared prelude the pin copies here as `BifibreW2.*` is imported from
`WeilExchange/Transport.lean`; the pin's `BifibreW2` prelude copies are **not**
reproduced (SET-2 §0). The only `BifibreW2` declaration written here is the
Galois-case exchange.
-/
import FLTForHuman.AlgebraicCurve.WeilExchange.Bifibre
import Mathlib.FieldTheory.SeparableClosure

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls are kept literal (SET-1 §3).
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain

namespace AlgebraicCurve

open Place BifibreDev

/-! ## The normal-closure envelope (private instance plumbing) -/

section Envelope

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

private abbrev Env : Type _ := ↥(IntermediateField.normalClosure F E (AlgebraicClosure E))

private theorem isGalois_env [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    IsGalois F (Env F E) := by
  haveI : Normal F (AlgebraicClosure E) := IsAlgClosure.normal F _
  haveI : ∀ f : E →ₐ[F] AlgebraicClosure E, Algebra.IsSeparable F f.fieldRange := fun f =>
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
  haveI : Algebra.IsSeparable F (Env F E) :=
    IntermediateField.isSeparable_iSup (F := F) (E := AlgebraicClosure E)
      (t := fun f : E →ₐ[F] AlgebraicClosure E => f.fieldRange)
  exact ⟨⟩

variable (R : Type*) [Field R] [Algebra R E]

@[reducible] private noncomputable def algebraEnv : Algebra R (Env F E) :=
  ((algebraMap E (Env F E)).comp (algebraMap R E)).toAlgebra

private theorem isScalarTower_env_mid : letI := algebraEnv F E R; IsScalarTower R E (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem isScalarTower_env_base [Algebra F R] [IsScalarTower F R E] :
    letI := algebraEnv F E R; IsScalarTower F R (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    show algebraMap F (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap R E (algebraMap F R x))
    rw [← IsScalarTower.algebraMap_apply F R E x,
      ← IsScalarTower.algebraMap_apply F E (AlgebraicClosure E) x])

variable (K : Type*) [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E]

private theorem isScalarTower_env_bot [Algebra K R] [IsScalarTower K R E] :
    letI := algebraEnv F E R; IsScalarTower K R (Env F E) :=
  letI := algebraEnv F E R
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    show algebraMap K (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap R E (algebraMap K R x))
    rw [← IsScalarTower.algebraMap_apply K R E x,
      ← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) x])

omit [Algebra R E] in
private theorem isScalarTower_env_const : IsScalarTower K E (Env F E) :=
  IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (by
    show algebraMap K (AlgebraicClosure E) x =
      algebraMap E (AlgebraicClosure E) (algebraMap K E x)
    rw [← IsScalarTower.algebraMap_apply K E (AlgebraicClosure E) x])

end Envelope

/-! ## Stage 1: the Galois-case exchange -/

theorem BifibreW2.exchange_of_isGalois {K F F₁ F₂ E : Type*} (M : Type*)
    [Field K] [Field F] [Field F₁] [Field F₂] [Field E] [Field M]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra K M]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F M]
    [Algebra F₁ E] [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M] [Algebra E M]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower K F₁ M] [IsScalarTower K F₂ M]
    [IsScalarTower K E M]
    [IsScalarTower F F₁ E] [IsScalarTower F F₂ E] [IsScalarTower F F₁ M] [IsScalarTower F F₂ M]
    [IsScalarTower F E M] [IsScalarTower F₁ E M] [IsScalarTower F₂ E M]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E]
    [FiniteDimensional F M] [IsGalois F M]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ =
      w₁.inertiaDeg F * w₂.ramificationIndex F := by
  have hB := Place.sum_ramificationIndex_mul_inertiaDeg_bifiber M hgen hLD v w₁ w₂
    hw₁ hw₂ T hT

  have hsum : ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F =
      (∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂) *
        (w₁.ramificationIndex F * w₂.inertiaDeg F) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun W hW => ?_
    obtain ⟨h₁, h₂⟩ := (hT W).mp hW
    rw [Place.ramificationIndex_eq_mul_ramificationIndex_restrict (F := F) (E := F₁) W, h₁,
      Place.inertiaDeg_eq_mul_inertiaDeg_restrict (F := F) (E := F₂) W, h₂]
    ring

  have he₁ : 0 < w₁.ramificationIndex F := Place.ramificationIndex_pos (F := F) w₁
  have hf₂ : 0 < w₂.inertiaDeg F := by
    haveI : FiniteDimensional F₂ M := Module.Finite.of_restrictScalars_finite F F₂ M
    haveI : IsGalois F₂ M := IsGalois.tower_top_of_isGalois F F₂ M
    obtain ⟨P, hP⟩ := Place.exists_restrict_eq (M := M) w₂
    have hPF : P.restrict F = v := by rw [← restrict_restrict (E := F₂) P, hP, hw₂]
    have hTC := Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg v P hPF
    have hf := Place.inertiaDeg_eq_mul_inertiaDeg_restrict (F := F) (E := F₂) P
    rw [hP] at hf
    have hne : Module.finrank F M ≠ 0 := Module.finrank_pos.ne'
    rw [← hTC, hf] at hne
    exact Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos he₁ hf₂)
  rw [← hsum, hB]
  ring

/-! ## Stage 2: the separable reduction through the envelope -/

theorem Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable
    {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower F F₁ E] [IsScalarTower F F₂ E]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [Algebra.IsSeparable F E]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F =
      (w₁.ramificationIndex F * w₁.inertiaDeg F) * (w₂.ramificationIndex F * w₂.inertiaDeg F) := by
  letI : Algebra F₁ (Env F E) := algebraEnv F E F₁
  letI : Algebra F₂ (Env F E) := algebraEnv F E F₂
  haveI : IsScalarTower F₁ E (Env F E) := isScalarTower_env_mid F E F₁
  haveI : IsScalarTower F₂ E (Env F E) := isScalarTower_env_mid F E F₂
  haveI : IsScalarTower F F₁ (Env F E) := isScalarTower_env_base F E F₁
  haveI : IsScalarTower F F₂ (Env F E) := isScalarTower_env_base F E F₂
  haveI : IsScalarTower K F₁ (Env F E) := isScalarTower_env_bot F E F₁ K
  haveI : IsScalarTower K F₂ (Env F E) := isScalarTower_env_bot F E F₂ K
  haveI : IsScalarTower K E (Env F E) := isScalarTower_env_const F E K
  haveI : IsGalois F (Env F E) := isGalois_env F E
  exact Place.sum_ramificationIndex_mul_inertiaDeg_bifiber (Env F E) hgen hLD v w₁ w₂
    hw₁ hw₂ T hT

/-! ## The public node (T7's capstone calls this) -/

theorem Place.sum_ramificationIndex_mul_inertiaDeg_exchange
    {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower F F₁ E] [IsScalarTower F F₂ E]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [Algebra.IsSeparable F E]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ =
      w₁.inertiaDeg F * w₂.ramificationIndex F := by
  letI : Algebra F₁ (Env F E) := algebraEnv F E F₁
  letI : Algebra F₂ (Env F E) := algebraEnv F E F₂
  haveI : IsScalarTower F₁ E (Env F E) := isScalarTower_env_mid F E F₁
  haveI : IsScalarTower F₂ E (Env F E) := isScalarTower_env_mid F E F₂
  haveI : IsScalarTower F F₁ (Env F E) := isScalarTower_env_base F E F₁
  haveI : IsScalarTower F F₂ (Env F E) := isScalarTower_env_base F E F₂
  haveI : IsScalarTower K F₁ (Env F E) := isScalarTower_env_bot F E F₁ K
  haveI : IsScalarTower K F₂ (Env F E) := isScalarTower_env_bot F E F₂ K
  haveI : IsScalarTower K E (Env F E) := isScalarTower_env_const F E K
  haveI : IsGalois F (Env F E) := isGalois_env F E
  exact BifibreW2.exchange_of_isGalois (Env F E) hgen hLD v w₁ w₂ hw₁ hw₂ T hT

end AlgebraicCurve
