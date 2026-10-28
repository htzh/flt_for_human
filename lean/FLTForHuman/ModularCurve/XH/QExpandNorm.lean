/-
The `q`-expansion of the norm of the `β`-operator on `X_H(M)`:
`ModularCurve.qExpand_norm_heckeBetaHBar`, statement verbatim from
`Theorems/Thm_ModularCurve_qExpand_norm_heckeBetaHBar.lean` (pin `aa2d8b3`).

For a prime `ℓ ∤ M` and `u` in the function field `xHFunctionFieldBar M H` of `X_H(M)`
over `ℚ̄`, the `ℓ`-stretch of the norm of `β u` along the `α`-row is the product of the
`ℓ` unit twists `qTwist (ζ ^ b)` of the diamond conjugates of `u`, times
`qExpand ℓ (qExpand ℓ u)`:

  `qExpand ℚ̄ ℓ (norm_α (β u))
     = ∏_{b < ℓ} qTwist (ζ ^ b) (diamondAutHBar (unitOfCoprime ℓ _) u) * qExpand ℚ̄ ℓ (qExpand ℚ̄ ℓ u)`.

The norm is `Algebra.norm` under `AlgebraicCurve.algebraAlong (heckeAlphaHBar …)`, i.e. the field
norm of the degree-`ℓ + 1` extension `X_H(M) ∩ X₀(Mℓ) / X_H(M)`, and `ζ` is a primitive `ℓ`-th
root of unity in `ℚ̄`.

The proof is the pin's (`P2M/Sol/S_ModularCurve_qExpand_norm_heckeBetaHBar.lean`):
`finrankAlong_heckeAlphaHBar` gives the degree `ℓ + 1`; the Atkin–Lehner automorphism `w` of
`exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar` carries `β` to `α ∘ diamondAutHBar`;
and `Algebra.norm_eq_prod_embeddings` writes the norm as the product over the `ℓ + 1`
`K`-embeddings of the level-`Mℓ` field into an algebraic closure — the `q`-expansion embedding
`σ_last` together with the `ℓ` twisted ones `qTwist (ζ ^ b) ∘ w`. The two families are distinct,
so they are all of them: their values on one element already separate them, and the cardinality
count `AlgHom.card` closes the enumeration.

Two proof-side deviations from the pin. The pin separates the embeddings by a `-1728`-normalised
element built from `E₄`/`E₆`; here `jq` does that job: its `q`-coefficient is `196884 ≠ 0`
(`coeff_jq_one`), its `ℓ`-stretch has `q`-coefficient `0` because `ℓ ∤ 1`, and it lies in
`xHFunctionField M H` since `j` is `Γ_H(M)`-invariant. The pin's `attribute [-simp]`/
`attribute [-instance]` prelude and its heartbeat overrides are not reproduced.

  spec-pin: Theorems/Thm_ModularCurve_qExpand_norm_heckeBetaHBar.lean
  spec-pin: P2M/Sol/S_ModularCurve_qExpand_norm_heckeBetaHBar.lean

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_qExpand_norm_heckeBetaHBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_qExpand_norm_heckeBetaHBar.lean
-/
import FLTForHuman.ModularCurve.X1.AtkinLehnerExchange
import FLTForHuman.ModularCurve.XH.HeckeDegree
import FLTForHuman.ModularCurve.XH.Operators
import FLTForHuman.ModularCurve.Defs.Twist
import FLTForHuman.ModularCurve.JqCoefficients

set_option autoImplicit false

noncomputable section

open HahnSeries AlgebraicCurve

namespace ModularCurve

namespace QExpandNorm

/-- An algebraic closure of the Laurent series over `ℚ̄`, indexed by the prime only so that the
`β`-row's `Algebra` structure can be an instance (its head mentions `ℓ`). -/
private def Om (_ℓ : ℕ) : Type := AlgebraicClosure (LaurentSeries (AlgebraicClosure ℚ))

private instance Om.instField (ℓ : ℕ) : Field (Om ℓ) :=
  inferInstanceAs (Field (AlgebraicClosure (LaurentSeries (AlgebraicClosure ℚ))))

private instance Om.instIsAlgClosed (ℓ : ℕ) : IsAlgClosed (Om ℓ) :=
  inferInstanceAs (IsAlgClosed (AlgebraicClosure (LaurentSeries (AlgebraicClosure ℚ))))

/-- The coefficient embedding of `LaurentSeries ℚ̄` into `Om ℓ`: the common target of the
`ℓ + 1` embeddings whose product is the norm. -/
private def iotaE (ℓ : ℕ) : LaurentSeries (AlgebraicClosure ℚ) →+* Om ℓ :=
  algebraMap (LaurentSeries (AlgebraicClosure ℚ))
    (AlgebraicClosure (LaurentSeries (AlgebraicClosure ℚ)))

/-- The function field of `X_H(M)` over `ℚ̄`: the base field of the norm. -/
private abbrev KK (M : ℕ) (H : Subgroup (ZMod M)ˣ) := xHFunctionFieldBar M H

/-- The function field of the level-`Mℓ` curve over `ℚ̄`: the source of the `α`- and `β`-rows. -/
private abbrev EEt (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) :=
  laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ))

/-- The `α`-row `KK → EEt` as an algebra structure, so that `Algebra.norm` is its field norm. -/
private abbrev algAlongAlpha (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    Algebra (KK M H) (EEt M H ℓ) :=
  algebraAlong (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)

/-- The `β`-row as an algebra structure into `Om ℓ`: `KK` acts through `β`, then `q`-expansion
and the coefficient embedding. -/
private abbrev algBetaOm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] :
    Algebra (KK M H) (Om ℓ) :=
  (((iotaE ℓ).comp (algebraMap (EEt M H ℓ) (LaurentSeries (AlgebraicClosure ℚ)))).comp
    (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom).toAlgebra

attribute [local instance] algAlongAlpha algBetaOm

private theorem iotaE_injective (ℓ : ℕ) : Function.Injective (iotaE ℓ) :=
  (algebraMap (LaurentSeries (AlgebraicClosure ℚ))
    (AlgebraicClosure (LaurentSeries (AlgebraicClosure ℚ)))).injective

/-- The diamond automorphism at the diamond unit `unitOfCoprime ℓ _`. -/
private def sigmaL (M : ℕ) (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    KK M H ≃ₐ[AlgebraicClosure ℚ] KK M H :=
  diamondAutHBar M H (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))

/-- The two Atkin–Lehner conclusions: `w` intertwines `α` with `β`, and `β` with `α ∘ σ`. -/
private def ALSpec (M : ℕ) (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ) : Prop :=
  (∀ x : KK M H, w (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ x) =
      heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ x) ∧
    ∀ x : KK M H, w (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ x) =
      heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ (sigmaL M H hℓM x)

private theorem exists_AL (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓM : ¬ ℓ ∣ M) (hin : HeckeDiamondInputsHAll M H) :
    ∃ w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ, ALSpec M H hℓM w :=
  exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar M H hℓM hin

/-- The `α`-row has degree `ℓ + 1`, so the norm runs over `ℓ + 1` embeddings. -/
private theorem finrank_alpha (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓM : ¬ ℓ ∣ M) : Module.finrank (KK M H) (EEt M H ℓ) = ℓ + 1 :=
  finrankAlong_heckeAlphaHBar (AlgebraicClosure ℚ) M H hℓM

private theorem finiteDimensional_alpha (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) : FiniteDimensional (KK M H) (EEt M H ℓ) :=
  Module.finite_of_finrank_pos (by rw [finrank_alpha M H hℓM]; exact Nat.succ_pos ℓ)

private theorem algebraMap_KE_apply (M : ℕ) (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    (f : KK M H) :
    algebraMap (KK M H) (EEt M H ℓ) f = heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ f := rfl

private theorem algebraMap_ELS_apply (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) (x : EEt M H ℓ) :
    algebraMap (EEt M H ℓ) (LaurentSeries (AlgebraicClosure ℚ)) x =
      (x : LaurentSeries (AlgebraicClosure ℚ)) := rfl

private theorem algebraMap_KOm_apply (M : ℕ) (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    (f : KK M H) :
    algebraMap (KK M H) (Om ℓ) f =
      iotaE ℓ ((heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f : EEt M H ℓ) :
        LaurentSeries (AlgebraicClosure ℚ)) := rfl

/-- The `q`-expansion embedding of the level-`Mℓ` field into `Om ℓ` is `K`-linear: on `KK` it
agrees with `β`, because `q ↦ q ^ ℓ` is `β` on `q`-expansions. -/
private theorem sigmaLast_comm (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    (h0 : HeckeBetaHDefined M H ℓ) (f : KK M H) :
    ((iotaE ℓ).comp ((qExpand (AlgebraicClosure ℚ) ℓ).comp
      (algebraMap (EEt M H ℓ) (LaurentSeries (AlgebraicClosure ℚ)))))
      (algebraMap (KK M H) (EEt M H ℓ) f) = algebraMap (KK M H) (Om ℓ) f := by
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_KE_apply, algebraMap_ELS_apply,
    algebraMap_KOm_apply, coe_heckeAlphaHBar, coe_heckeBetaHBar M H ℓ h0]

/-- The `q`-expansion embedding of the level-`Mℓ` field into `Om ℓ`. -/
private def sigmaLast (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    (h0 : HeckeBetaHDefined M H ℓ) : EEt M H ℓ →ₐ[KK M H] Om ℓ where
  toRingHom := (iotaE ℓ).comp ((qExpand (AlgebraicClosure ℚ) ℓ).comp
    (algebraMap (EEt M H ℓ) (LaurentSeries (AlgebraicClosure ℚ))))
  commutes' := sigmaLast_comm M H h0

private theorem sigmaLast_apply (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ}
    [Fact ℓ.Prime] (h0 : HeckeBetaHDefined M H ℓ) (v : EEt M H ℓ) :
    sigmaLast M H h0 v =
      iotaE ℓ (qExpand (AlgebraicClosure ℚ) ℓ (v : LaurentSeries (AlgebraicClosure ℚ))) := by
  show ((iotaE ℓ).comp ((qExpand (AlgebraicClosure ℚ) ℓ).comp
    (algebraMap (EEt M H ℓ) (LaurentSeries (AlgebraicClosure ℚ))))) v = _
  rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_ELS_apply]

private theorem zeta_pow_pow {ℓ : ℕ} {ζ : (AlgebraicClosure ℚ)ˣ} (hζ : IsPrimitiveRoot ζ ℓ)
    (j : ℕ) : (ζ ^ j) ^ ℓ = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

/-- The `qTwist (ζ ^ b) ∘ w` embedding: `K`-linearity is `w`'s first half together with the
`ℓ`-th-root-of-unity property of `ζ`. -/
private def sigmaTwist (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    (h0 : HeckeBetaHDefined M H ℓ) {hℓM : ¬ ℓ ∣ M}
    {w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ} (hw : ALSpec M H hℓM w)
    (c : (AlgebraicClosure ℚ)ˣ) (hc : c ^ ℓ = 1) : EEt M H ℓ →ₐ[KK M H] Om ℓ where
  toRingHom := (iotaE ℓ).comp ((qTwist c).comp
    ((algebraMap (EEt M H ℓ) (LaurentSeries (AlgebraicClosure ℚ))).comp w.toAlgHom.toRingHom))
  commutes' f := by
    show iotaE ℓ (qTwist c ((w (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ f) : EEt M H ℓ) :
        LaurentSeries (AlgebraicClosure ℚ))) =
      iotaE ℓ ((heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ f : EEt M H ℓ) :
        LaurentSeries (AlgebraicClosure ℚ))
    rw [hw.1, coe_heckeBetaHBar M H ℓ h0, qTwist_qExpand c ℓ, zpow_natCast, hc,
      qTwist_one_apply]

private theorem sigmaTwist_apply (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ}
    [Fact ℓ.Prime] (h0 : HeckeBetaHDefined M H ℓ) {hℓM : ¬ ℓ ∣ M}
    {w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ} (hw : ALSpec M H hℓM w)
    (c : (AlgebraicClosure ℚ)ˣ) (hc : c ^ ℓ = 1) (v : EEt M H ℓ) :
    sigmaTwist M H h0 hw c hc v =
      iotaE ℓ (qTwist c ((w v : EEt M H ℓ) : LaurentSeries (AlgebraicClosure ℚ))) := rfl

/-- The `ℓ + 1` embeddings: the `q`-expansion one, then the `ℓ` twists of `w`. -/
private def emb (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    (h0 : HeckeBetaHDefined M H ℓ) {ζ : (AlgebraicClosure ℚ)ˣ} (hζ : IsPrimitiveRoot ζ ℓ)
    {hℓM : ¬ ℓ ∣ M} {w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ} (hw : ALSpec M H hℓM w) :
    Option (Fin ℓ) → (EEt M H ℓ →ₐ[KK M H] Om ℓ)
  | none => sigmaLast M H h0
  | some j => sigmaTwist M H h0 hw (ζ ^ (j : ℕ)) (zeta_pow_pow hζ j)

private theorem emb_none_apply (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ}
    [Fact ℓ.Prime] (h0 : HeckeBetaHDefined M H ℓ) {ζ : (AlgebraicClosure ℚ)ˣ}
    (hζ : IsPrimitiveRoot ζ ℓ) {hℓM : ¬ ℓ ∣ M}
    {w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ} (hw : ALSpec M H hℓM w) (v : EEt M H ℓ) :
    emb M H h0 hζ hw none v =
      iotaE ℓ (qExpand (AlgebraicClosure ℚ) ℓ (v : LaurentSeries (AlgebraicClosure ℚ))) :=
  sigmaLast_apply M H h0 v

private theorem emb_some_apply (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ}
    [Fact ℓ.Prime] (h0 : HeckeBetaHDefined M H ℓ) {ζ : (AlgebraicClosure ℚ)ˣ}
    (hζ : IsPrimitiveRoot ζ ℓ) {hℓM : ¬ ℓ ∣ M}
    {w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ} (hw : ALSpec M H hℓM w) (j : Fin ℓ)
    (v : EEt M H ℓ) :
    emb M H h0 hζ hw (some j) v =
      iotaE ℓ (qTwist (ζ ^ (j : ℕ)) ((w v : EEt M H ℓ) :
        LaurentSeries (AlgebraicClosure ℚ))) := rfl

/-! ### The separating element

`jq` lies in the function field, its `q`-coefficient is `196884 ≠ 0`, and its `ℓ`-stretch has
`q`-coefficient `0`; the pin instead builds a `-1728`-normalised element out of `E₄`/`E₆`. -/

private theorem jq_mem (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    jq ∈ xHFunctionField M H :=
  x0_le_xHFunctionFieldC ℚ M H
    (modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M (HeckeDegree.jq_mem_F0 M))

/-- The separating element: `jq`, base-changed to `ℚ̄`. -/
private def x1 (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : KK M H :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem M H)⟩

private theorem coe_x1_coeff_one (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ((x1 M H : KK M H) : LaurentSeries (AlgebraicClosure ℚ)).coeff 1 = 196884 := by
  show (coeffEmb (AlgebraicClosure ℚ) jq).coeff 1 = 196884
  rw [coeffEmb_coeff, coeff_jq_one]
  norm_num

/-- The preimage of `x1` under the diamond automorphism, so that `w` sends `β x0` to `x1`. -/
private def x0 (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓM : ¬ ℓ ∣ M) : KK M H :=
  (sigmaL M H hℓM).symm (x1 M H)

private theorem w_beta_x0 (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime]
    {hℓM : ¬ ℓ ∣ M} {w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ} (hw : ALSpec M H hℓM w) :
    ((w (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (x0 M H hℓM)) : EEt M H ℓ) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      ((x1 M H : KK M H) : LaurentSeries (AlgebraicClosure ℚ)) := by
  rw [hw.2, coe_heckeAlphaHBar, x0, AlgEquiv.apply_symm_apply]

/-- The `ℓ + 1` embeddings are distinct: a twist multiplies the `q`-coefficient of `x1` by a
power of `ζ`, while the `q`-expansion embedding kills it (`ℓ ∤ 1`). -/
private theorem emb_injective (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ}
    [Fact ℓ.Prime] (h0 : HeckeBetaHDefined M H ℓ) {ζ : (AlgebraicClosure ℚ)ˣ}
    (hζ : IsPrimitiveRoot ζ ℓ) {hℓM : ¬ ℓ ∣ M}
    {w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ} (hw : ALSpec M H hℓM w) :
    Function.Injective (emb M H h0 hζ hw) := by
  have hprime : ℓ.Prime := Fact.out
  have hζ' : IsPrimitiveRoot (ζ : AlgebraicClosure ℚ) ℓ := IsPrimitiveRoot.coe_units_iff.mpr hζ
  let cf : Option (Fin ℓ) → AlgebraicClosure ℚ :=
    fun o => Option.elim o 0 fun j => ((ζ : AlgebraicClosure ℚ) ^ (j : ℕ)) * 196884
  have key : ∀ o : Option (Fin ℓ), ∃ s : LaurentSeries (AlgebraicClosure ℚ),
      emb M H h0 hζ hw o (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ (x0 M H hℓM)) =
        iotaE ℓ s ∧ s.coeff 1 = cf o := by
    rintro (_ | j)
    · refine ⟨qExpand (AlgebraicClosure ℚ) ℓ (qExpand (AlgebraicClosure ℚ) ℓ
        ((x0 M H hℓM : KK M H) : LaurentSeries (AlgebraicClosure ℚ))), ?_, ?_⟩
      · rw [emb_none_apply, coe_heckeBetaHBar M H ℓ h0]
      · show (qExpand (AlgebraicClosure ℚ) ℓ (qExpand (AlgebraicClosure ℚ) ℓ _)).coeff 1 = 0
        refine qExpand_coeff_of_not_dvd ℓ _ fun h => ?_
        have h2 : (ℓ : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h
        exact hprime.one_lt.ne' (by exact_mod_cast h2)
    · refine ⟨qTwist (ζ ^ (j : ℕ))
        ((x1 M H : KK M H) : LaurentSeries (AlgebraicClosure ℚ)), ?_, ?_⟩
      · rw [emb_some_apply, w_beta_x0 M H hw]
      · show (qTwist (ζ ^ (j : ℕ)) _).coeff 1 = (ζ : AlgebraicClosure ℚ) ^ (j : ℕ) * 196884
        rw [qTwist_coeff, coe_x1_coeff_one, zpow_one, Units.val_pow_eq_pow_val]
  intro o₁ o₂ h
  obtain ⟨s₁, hs₁, hc₁⟩ := key o₁
  obtain ⟨s₂, hs₂, hc₂⟩ := key o₂
  have hs : s₁ = s₂ := iotaE_injective ℓ (by rw [← hs₁, ← hs₂, h])
  rw [hs] at hc₁
  have hc : cf o₁ = cf o₂ := hc₁.symm.trans hc₂
  have hz : ∀ j : ℕ, (ζ : AlgebraicClosure ℚ) ^ j * 196884 ≠ 0 := fun j =>
    mul_ne_zero (pow_ne_zero _ (Units.ne_zero ζ)) (by norm_num)
  rcases o₁ with _ | j₁ <;> rcases o₂ with _ | j₂
  · rfl
  · exact absurd hc.symm (hz _)
  · exact absurd hc (hz _)
  · have hv : (ζ : AlgebraicClosure ℚ) ^ (j₁ : ℕ) = (ζ : AlgebraicClosure ℚ) ^ (j₂ : ℕ) :=
      mul_right_cancel₀ (by norm_num : (196884 : AlgebraicClosure ℚ) ≠ 0) hc
    exact congrArg some (Fin.ext (hζ'.pow_inj j₁.2 j₂.2 hv))

/-- The `ℓ + 1` embeddings are all the `K`-embeddings, by the cardinality count
`AlgHom.card = finrank = ℓ + 1`. -/
private theorem emb_bijective (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ}
    [Fact ℓ.Prime] (h0 : HeckeBetaHDefined M H ℓ) {ζ : (AlgebraicClosure ℚ)ˣ}
    (hζ : IsPrimitiveRoot ζ ℓ) {hℓM : ¬ ℓ ∣ M}
    {w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ} (hw : ALSpec M H hℓM w) :
    Function.Bijective (emb M H h0 hζ hw) := by
  have := finiteDimensional_alpha M H hℓM
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨emb_injective M H h0 hζ hw, ?_⟩
  rw [Fintype.card_option, Fintype.card_fin, AlgHom.card, finrank_alpha M H hℓM]

/-- **The norm's `q`-expansion is the product of the twisted conjugates.** The pin's engine:
`Algebra.norm_eq_prod_embeddings` over the `ℓ + 1` embeddings, reindexed by `Option (Fin ℓ)`. -/
private theorem qExpand_norm (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ}
    [Fact ℓ.Prime] (h0 : HeckeBetaHDefined M H ℓ) {ζ : (AlgebraicClosure ℚ)ˣ}
    (hζ : IsPrimitiveRoot ζ ℓ) {hℓM : ¬ ℓ ∣ M}
    {w : EEt M H ℓ ≃ₐ[AlgebraicClosure ℚ] EEt M H ℓ} (hw : ALSpec M H hℓM w)
    (v : EEt M H ℓ) :
    qExpand (AlgebraicClosure ℚ) ℓ ((Algebra.norm (KK M H) v : KK M H) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      (∏ j ∈ Finset.range ℓ,
          qTwist (ζ ^ j) ((w v : EEt M H ℓ) : LaurentSeries (AlgebraicClosure ℚ))) *
        qExpand (AlgebraicClosure ℚ) ℓ (v : LaurentSeries (AlgebraicClosure ℚ)) := by
  have := finiteDimensional_alpha M H hℓM
  apply iotaE_injective ℓ
  have h1 := Algebra.norm_eq_prod_embeddings (K := KK M H) (L := EEt M H ℓ) (E := Om ℓ) v
  have h2 : algebraMap (KK M H) (Om ℓ) (Algebra.norm (KK M H) v) =
      iotaE ℓ (qExpand (AlgebraicClosure ℚ) ℓ
        ((Algebra.norm (KK M H) v : KK M H) : LaurentSeries (AlgebraicClosure ℚ))) := by
    rw [algebraMap_KOm_apply, coe_heckeBetaHBar M H ℓ h0]
  rw [← h2, h1, ← (emb_bijective M H h0 hζ hw).prod_comp (fun σ => σ v),
    Fintype.prod_option, map_mul, map_prod, Finset.prod_range]
  simp only [emb_none_apply, emb_some_apply]
  exact mul_comm _ _

end QExpandNorm

/-- **The `q`-expansion of the `β`-operator's norm.** Verbatim from
`Theorems/Thm_ModularCurve_qExpand_norm_heckeBetaHBar.lean:11-26`. -/
theorem qExpand_norm_heckeBetaHBar (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (ζ : (AlgebraicClosure ℚ)ˣ) (hζ : IsPrimitiveRoot ζ ℓ)
    (u : ModularCurve.xHFunctionFieldBar M H) :
    ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ
        ((letI := AlgebraicCurve.algebraAlong (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
          Algebra.norm (ModularCurve.xHFunctionFieldBar M H)
            (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ u) :
            ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ)) =
      (∏ b ∈ Finset.range ℓ,
          ModularCurve.qTwist (ζ ^ b)
            ((ModularCurve.diamondAutHBar M H
                (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM)) u :
              ModularCurve.xHFunctionFieldBar M H) : LaurentSeries (AlgebraicClosure ℚ))) *
        ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ
          (ModularCurve.qExpand (AlgebraicClosure ℚ) ℓ (u : LaurentSeries (AlgebraicClosure ℚ))) := by
  have h0 : HeckeBetaHDefined M H ℓ := (hin.heckeInputsHAlong ℓ Fact.out).betaHDefined
  obtain ⟨w, hw⟩ := QExpandNorm.exists_AL M H hℓM hin
  have hnorm := QExpandNorm.qExpand_norm M H h0 hζ hw
    (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ u)
  rw [hw.2, coe_heckeAlphaHBar, coe_heckeBetaHBar M H ℓ h0] at hnorm
  exact hnorm

end ModularCurve

end
