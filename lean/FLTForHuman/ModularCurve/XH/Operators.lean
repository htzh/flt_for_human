/-
The `X_H(M)` diamond-operator vocabulary and the input bundle `HeckeDiamondInputsHAll`,
after FLT's `Definitions/Def_ModularCurve_XHOperators.lean`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XHOperators.lean>).

This module hosts the pin's whole `Diamond` section — the diamond predicate
`IsDiamondAutHBar`, the choice function `diamondAutHBar` with its two lemmas, and
the `ℤ̄`-linear diamond operator `diamondHBar` with `diamondHBar_apply` and
`diamondHBar_of_not` — its `GenOp` block up to the Tate layer (`genOpH` on
`CohCarrier.Gen M S` with the three computation lemmas `genOpH_T`/`_U`/`_dia`),
and the bundle `HeckeDiamondInputsHAll` with its two accessors.

The pin's `tateGenOpH` and `tateGenOpH_apply_coe` are **not** transcribed: they are
`Module.End ℤ_[p] (TateModule p (JH M H))`, and the `TateModule` definition layer
(`Definitions/Def_EllipticCurve_TateModule.lean`, 69 declarations) is absent from
the port — it is the T1 plan of `topics/modularCurve/TOPIC-padic-tate-module.md`.
`genOpH` itself needs no Tate module and is the vocabulary of the `X_H` Hecke rows
(`galois_smul_genOpH_comm`, `qExpand_norm_heckeBetaHBar`).

The module also hosts the MC-4d `X_H` row **`galois_smul_genOpH_comm`**: the
Galois action of `ℚ̄ ≃ₐ[ℚ] ℚ̄` commutes with `genOpH`, proved by cases on
`CohCarrier.Gen` (`T`/`U` through `heckeOperatorHAlong`, `dia` through
`diamondHBar`).  Its engine — the `S_` copy's α/β intertwining of
`arithmeticGalois`, the `Pic⁰`-level Hecke commutation, the `SemilinearAut`
bookkeeping and the diamond case — is transcribed from
`P2M/Sol/S_ModularCurve_galois_smul_genOpH_comm.lean` (265 lines) and kept
`private`; only the headline is public.  The pin's `coeffMap_qExpand_comm` is
already public here as `coeffMap_qExpand` (`Defs/Laurent.lean`, same statement and
proof), so it is used rather than restated.  The 27-line sibling row
`heckeOperatorHAlong_diamondHBar_comm` cannot live here — it needs the diamond lift
`exists_algEquiv_intertwinesAlong_diamondAutHBar`, declared in `XH/DiamondLift.lean`,
which imports this module — so it is hosted by `XH/DiamondLift.lean`.

`IsDiamondAutHBar` is the base-changed (`ℚ̄`) sibling of the ported X₁ predicate
`ModularCurve.IsDiamondAut` (`ModularCurve/X1/Diamond.lean`): the same slash-ratio
condition, but read through `coeffEmb`/`xHFunctionFieldBar` rather than over `ℚ`.
Its inputs — `intSeriesC`, `div_mem_qExpFunctionFieldC` (`JqIntegralRatios.lean`),
`coeffEmb_mem_laurentBaseChange` (`Defs/Laurent.lean`), `IsIntegralQExp`
(`ModularForms/WeightOne/Gamma0Integral.lean`) and `xHFunctionFieldBar` — are all
ported.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_XHOperators.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_galois_smul_genOpH_comm.lean

spec-pin: Definitions/Def_ModularCurve_XHOperators.lean
spec-pin: Theorems/Thm_ModularCurve_galois_smul_genOpH_comm.lean
spec-pin: P2M/Sol/S_ModularCurve_galois_smul_genOpH_comm.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.XH.HeckeOperator
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.ArithmeticGalois
import FLTForHuman.ModularForms.CohCarrier.Inst
import FLTForHuman.ModularForms.WeightOne.Gamma0Integral
import FLTForHuman.AlgebraicCurve.WeilExchange.GaloisRamification

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve

section Diamond

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

/-- The diamond automorphism of `X_H(M)` attached to `d`: it is the `ℚ̄`-algebra
automorphism multiplying the `q`-expansion of a ratio by the `γ`-slash with
`γ 0 0 ≡ d (mod M)`. -/
def IsDiamondAutHBar (d : (ZMod M)ˣ)
    (σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (γ : SL(2, ℤ)), γ ∈ Gamma0 M → ((γ 0 0 : ℤ) : ZMod M) = (d : ZMod M) →
      ∃ y : LaurentSeries ℚ, y ∈ xHFunctionField M H ∧
        ((σ ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (div_mem_qExpFunctionFieldC f g hf hg hg0)⟩ : xHFunctionFieldBar M H) :
            LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y ∧
        coeffMap (algebraMap ℚ ℂ) y *
            HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] (γ : GL (Fin 2) ℝ))) =
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] (γ : GL (Fin 2) ℝ)))

/-- The diamond automorphism at `d`, or the identity when none exists. -/
def diamondAutHBar (d : (ZMod M)ˣ) :
    xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H :=
  haveI := Classical.dec (∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
    IsDiamondAutHBar M H d σ)
  if h : ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ
  then h.choose else AlgEquiv.refl

variable {M H}

theorem isDiamondAutHBar_diamondAutHBar {d : (ZMod M)ˣ}
    (h : ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) :
    IsDiamondAutHBar M H d (diamondAutHBar M H d) := by
  rw [diamondAutHBar, dite_eq_left h]
  exact h.choose_spec

theorem diamondAutHBar_of_not {d : (ZMod M)ˣ}
    (h : ¬ ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) :
    diamondAutHBar M H d = AlgEquiv.refl := by
  rw [diamondAutHBar, dite_eq_right h]

variable (M H)

/-- The diamond operator on `J_H(M)`: the `ℤ`-linear action of the chosen diamond
automorphism `diamondAutHBar M H d`. -/
def diamondHBar (d : (ZMod M)ˣ) : JH M H →+ JH M H :=
  DistribSMul.toAddMonoidHom (JH M H) (SemilinearAut.ofAlgAut (diamondAutHBar M H d))

theorem diamondHBar_apply (d : (ZMod M)ˣ) (x : JH M H) :
    diamondHBar M H d x = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • x :=
  rfl

theorem diamondHBar_of_not {d : (ZMod M)ˣ}
    (h : ¬ ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ) (x : JH M H) :
    diamondHBar M H d x = x := by
  rw [diamondHBar_apply, diamondAutHBar_of_not h]
  have : SemilinearAut.ofAlgAut
      (AlgEquiv.refl : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H) = 1 :=
    map_one _
  rw [this, one_smul]

/-- The bundle of inputs for the `X_H(M)` Hecke operators (every prime `ℓ`) and
the diamond automorphisms (every `d ∈ (ZMod M)ˣ`). -/
def HeckeDiamondInputsHAll : Prop :=
  (∀ ℓ : ℕ, ∀ hℓ : ℓ.Prime, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ) ∧
    ∀ d : (ZMod M)ˣ, ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ

variable {M H}

theorem HeckeDiamondInputsHAll.heckeInputsHAlong (h : HeckeDiamondInputsHAll M H) (ℓ : ℕ)
    (hℓ : ℓ.Prime) : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ :=
  h.1 ℓ hℓ

theorem HeckeDiamondInputsHAll.isDiamondAutHBar (h : HeckeDiamondInputsHAll M H) (d : (ZMod M)ˣ) :
    IsDiamondAutHBar M H d (diamondAutHBar M H d) :=
  isDiamondAutHBar_diamondAutHBar (h.2 d)

end Diamond

section GenOp

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)

/-- The `X_H(M)` Hecke operator attached to a Hecke generator: `T_ℓ` and `U_q` both
reduce to `heckeOperatorHAlong`, and `dia d` is the diamond operator. -/
def genOpH : CohCarrier.Gen M S → (JH M H →+ JH M H)
  | .T ℓ hℓ _ _ => haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ
  | .U q hq _ => haveI : NeZero q := ⟨hq.ne_zero⟩; heckeOperatorHAlong (AlgebraicClosure ℚ) M H q
  | .dia d => diamondHBar M H d

theorem genOpH_T (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S) (hℓM : ¬ ℓ ∣ M) :
    genOpH M H S (.T ℓ hℓ hℓS hℓM) =
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ) :=
  rfl

theorem genOpH_U (q : ℕ) (hq : q.Prime) (hqM : q ∣ M) :
    genOpH M H S (.U q hq hqM) =
      (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeOperatorHAlong (AlgebraicClosure ℚ) M H q) :=
  rfl

theorem genOpH_dia (d : (ZMod M)ˣ) : genOpH M H S (.dia d) = diamondHBar M H d := rfl

end GenOp

section GenOpGalois

/-! ### The Galois action commutes with the `X_H(M)` generator operators

The engine of the pin's `S_ModularCurve_galois_smul_genOpH_comm.lean` (265 lines, pinned
`aa2d8b3`), transcribed in the pin's namespace `ModularCurve.GaloisSmulGenOpHComm` with its
declarations `private`: the α/β intertwining of `arithmeticGalois`, the Hecke commutation at
`Pic⁰`, the `SemilinearAut` bookkeeping and the diamond case.  The pin's
`coeffMap_qExpand_comm` is the ported public `coeffMap_qExpand`
(`ModularCurve/Defs/Laurent.lean`), so it is consumed, not restated. -/

namespace GaloisSmulGenOpHComm

section Hecke

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

omit [NeZero ℓ] in

private theorem intertwines_alpha (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.IntertwinesAlong (heckeAlphaHBar L M H ℓ).toRingHom
      (arithmeticGalois (xHFunctionField M H) σ)
      (arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ) := by
  intro x
  apply Subtype.ext
  change ((arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ • heckeAlphaHBar L M H ℓ x :
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries L) =
    ((heckeAlphaHBar L M H ℓ (arithmeticGalois (xHFunctionField M H) σ • x) :
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries L)
  rw [coe_arithmeticGalois_smul, coe_heckeAlphaHBar, coe_heckeAlphaHBar, coe_arithmeticGalois_smul]

private theorem intertwines_beta (σ : L ≃ₐ[ℚ] L) :
    SemilinearAut.IntertwinesAlong (heckeBetaHBar L M H ℓ).toRingHom
      (arithmeticGalois (xHFunctionField M H) σ)
      (arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ) := by
  rcases Classical.em (HeckeBetaHDefined M H ℓ) with h | h
  · intro x
    apply Subtype.ext
    change ((arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ • heckeBetaHBar L M H ℓ x :
        laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries L) =
      ((heckeBetaHBar L M H ℓ (arithmeticGalois (xHFunctionField M H) σ • x) :
        laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) : LaurentSeries L)
    rw [coe_arithmeticGalois_smul, coe_heckeBetaHBar M H ℓ h, coe_heckeBetaHBar M H ℓ h,
      coe_arithmeticGalois_smul, coeffMap_qExpand]
  · rw [heckeBetaHBar_of_not M H ℓ h]
    exact intertwines_alpha M H ℓ σ

private theorem galois_smul_heckeOperatorHAlong (σ : L ≃ₐ[ℚ] L)
    (P : Pic0 L (laurentBaseChange L (xHFunctionField M H))) :
    σ • heckeOperatorHAlong L M H ℓ P = heckeOperatorHAlong L M H ℓ (σ • P) := by
  rcases Classical.em (HeckeInputsHAlong L M H ℓ) with h | h
  · obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := h
    rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN, galois_smul_pic0_def, galois_smul_pic0_def]
    exact (SemilinearAut.pic0_correspondence_smul
      (g := arithmeticGalois (xHFunctionField M H) σ)
      (g' := arithmeticGalois (xHTopFunctionFieldC ℚ M H (M * ℓ)) σ)
      (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) hβ hα hFI hfin hN
      (intertwines_beta M H ℓ σ) (intertwines_alpha M H ℓ σ) P).symm
  · rw [heckeOperatorHAlong_of_not h, AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, smul_zero]

end Hecke

section Semilinear

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem mul_ofAlgAut_comm (g : SemilinearAut K F) (τ : F ≃ₐ[K] F)
    (h : ∀ x : F, g • (τ x) = τ (g • x)) :
    g * SemilinearAut.ofAlgAut τ = SemilinearAut.ofAlgAut τ * g := by
  apply Subtype.ext
  apply Prod.ext
  · apply RingEquiv.ext
    intro x
    exact h x
  · apply RingEquiv.ext
    intro a
    change (SemilinearAut.baseAut g * 1) a = (1 * SemilinearAut.baseAut g) a
    rw [mul_one, one_mul]

private theorem smul_smul_comm_of_mul_comm (A B : SemilinearAut K F) (h : A * B = B * A)
    (P : Pic0 K F) : A • (B • P) = B • (A • P) := by
  rw [← mul_smul, ← mul_smul, h]

end Semilinear

section Rational

variable {L : Type*} [Field L] [Algebra ℚ L]

private theorem ringHom_apply_eq_of_eqOn_generators {X : Type*} [DivisionRing X]
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {R : Set (LaurentSeries ℚ)} (hRF : R ⊆ F₀)
    (hFR : F₀ ≤ IntermediateField.adjoin ℚ R) (f₁ f₂ : laurentBaseChange L F₀ →+* X)
    (hconst : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      f₁ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = f₂ ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hgen : ∀ (r : LaurentSeries ℚ) (hr : r ∈ R),
      f₁ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ =
        f₂ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩)
    (x : laurentBaseChange L F₀) : f₁ x = f₂ x := by
  let T : Subfield (LaurentSeries L) :=
    (RingHom.eqLocusField f₁ f₂).map (SubringClass.subtype (laurentBaseChange L F₀))
  have hT : ∀ z : laurentBaseChange L F₀, f₁ z = f₂ z → (z : LaurentSeries L) ∈ T := fun z hz =>
    Subfield.mem_map.mpr ⟨z, hz, rfl⟩
  suffices hx : (x : LaurentSeries L) ∈ T by
    obtain ⟨x', hx', hx'x⟩ := Subfield.mem_map.mp hx
    have hxx : x' = x := Subtype.ext hx'x
    subst hxx
    exact hx'
  have hgenT : ∀ r ∈ R, coeffEmb L r ∈ T := fun r hr =>
    hT ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ (hgen r hr)
  have hF₀ : ∀ z ∈ F₀, coeffEmb L z ∈ T := by
    intro z hz
    have hz' : z ∈ (IntermediateField.adjoin ℚ R).toSubfield :=
      (IntermediateField.mem_toSubfield _ _).mpr (hFR hz)
    rw [IntermediateField.adjoin_toSubfield] at hz'
    have hle : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ R) ≤
        T.comap (coeffEmb L) := by
      rw [Subfield.closure_le]
      rintro w (⟨a, rfl⟩ | hw)
      · rw [SetLike.mem_coe, Subfield.mem_comap, eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) a,
          map_ratCast]
        exact SubfieldClass.ratCast_mem T a
      · rw [SetLike.mem_coe, Subfield.mem_comap]
        exact hgenT w hw
    exact Subfield.mem_comap.mp (hle hz')
  have hx := x.2
  rw [mem_laurentBaseChange_iff] at hx
  refine (Subfield.closure_le.mpr ?_) hx
  rintro _ (⟨a, rfl⟩ | ⟨z, hz, rfl⟩)
  · exact hT ⟨algebraMap L (LaurentSeries L) a, (laurentBaseChange L F₀).algebraMap_mem a⟩
      (hconst a _)
  · exact hF₀ z hz

private theorem arithmeticRingAut_comm_of_rational_on_generators
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {R : Set (LaurentSeries ℚ)} (hRF : R ⊆ F₀)
    (hFR : F₀ ≤ IntermediateField.adjoin ℚ R)
    (τ : laurentBaseChange L F₀ →+* laurentBaseChange L F₀)
    (hτL : ∀ (a : L) (ha : algebraMap L (LaurentSeries L) a ∈ laurentBaseChange L F₀),
      τ ⟨algebraMap L (LaurentSeries L) a, ha⟩ = ⟨algebraMap L (LaurentSeries L) a, ha⟩)
    (hτ : ∀ (r : LaurentSeries ℚ) (hr : r ∈ R), ∃ y : LaurentSeries ℚ,
      ((τ ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ : laurentBaseChange L F₀) :
        LaurentSeries L) = coeffEmb L y)
    (σ : L ≃ₐ[ℚ] L) (x : laurentBaseChange L F₀) :
    arithmeticRingAut F₀ σ (τ x) = τ (arithmeticRingAut F₀ σ x) := by
  refine ringHom_apply_eq_of_eqOn_generators (X := laurentBaseChange L F₀) hRF hFR
    ((arithmeticRingAut F₀ σ).toRingHom.comp τ) (τ.comp (arithmeticRingAut F₀ σ).toRingHom)
    ?_ ?_ x
  ·
    intro a ha
    have h1 : ∀ (b : L) (hb : algebraMap L (LaurentSeries L) b ∈ laurentBaseChange L F₀),
        arithmeticRingAut F₀ σ ⟨algebraMap L (LaurentSeries L) b, hb⟩ =
          ⟨algebraMap L (LaurentSeries L) (σ b), (laurentBaseChange L F₀).algebraMap_mem (σ b)⟩ :=
      fun b hb => Subtype.ext (coeffMap_algebraMap (σ : L →+* L) b)
    change arithmeticRingAut F₀ σ (τ _) = τ (arithmeticRingAut F₀ σ _)
    rw [hτL a ha, h1, hτL]
  ·
    intro r hr
    obtain ⟨y, hy⟩ := hτ r hr
    have hfix : arithmeticRingAut F₀ σ
        (⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ : laurentBaseChange L F₀) =
          ⟨coeffEmb L r, coeffEmb_mem_laurentBaseChange L (hRF hr)⟩ :=
      Subtype.ext (coeffMap_coeffEmb σ r)
    change arithmeticRingAut F₀ σ (τ _) = τ (arithmeticRingAut F₀ σ _)
    rw [hfix]
    apply Subtype.ext
    rw [coe_arithmeticRingAut_apply, hy, coeffMap_coeffEmb]

end Rational

section Diamond

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

private theorem isDiamondAutHBar_rational {d : (ZMod M)ˣ}
    {τ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H}
    (hτ : IsDiamondAutHBar M H d τ) (r : LaurentSeries ℚ)
    (hr : r ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H)) :
    ∃ y : LaurentSeries ℚ,
      (((τ : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H)
          ⟨coeffEmb (AlgebraicClosure ℚ) r, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H) hr)⟩ : xHFunctionFieldBar M H) :
        LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) y := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hr

  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have h00 : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have h1 : (((CohCarrier.gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) =
        (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) := rfl
    rw [← h1, hγ, inv_inv]
  obtain ⟨y, -, hy, -⟩ := hτ k f g pf pg hf hg hg0 γ γ.2 h00
  exact ⟨y, hy⟩

private theorem arithmeticRingAut_diamondAutHBar_comm {d : (ZMod M)ˣ}
    (hτ : IsDiamondAutHBar M H d (diamondAutHBar M H d))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : xHFunctionFieldBar M H) :
    arithmeticRingAut (xHFunctionField M H) σ
        ((diamondAutHBar M H d : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H) x) =
      (diamondAutHBar M H d : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H)
        (arithmeticRingAut (xHFunctionField M H) σ x) :=
  arithmeticRingAut_comm_of_rational_on_generators
    (intFormRatiosC_subset ℚ (CohCarrier.GammaH M H)) le_rfl
    (diamondAutHBar M H d : xHFunctionFieldBar M H →+* xHFunctionFieldBar M H)
    (fun a _ => (diamondAutHBar M H d).commutes a)
    (isDiamondAutHBar_rational M H hτ) σ x

private theorem arithmeticGalois_mul_ofAlgAut_diamondAutHBar {d : (ZMod M)ˣ}
    (hτ : IsDiamondAutHBar M H d (diamondAutHBar M H d))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    arithmeticGalois (xHFunctionField M H) σ * SemilinearAut.ofAlgAut (diamondAutHBar M H d) =
      SemilinearAut.ofAlgAut (diamondAutHBar M H d) * arithmeticGalois (xHFunctionField M H) σ :=
  mul_ofAlgAut_comm _ _ (arithmeticRingAut_diamondAutHBar_comm M H hτ σ)

private theorem galois_smul_diamondHBar (d : (ZMod M)ˣ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : JH M H) :
    σ • diamondHBar M H d P = diamondHBar M H d (σ • P) := by
  rcases Classical.em (∃ τ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d τ) with hex | hex
  · rw [diamondHBar_apply, diamondHBar_apply, galois_smul_pic0_def, galois_smul_pic0_def]
    exact smul_smul_comm_of_mul_comm _ _
      (arithmeticGalois_mul_ofAlgAut_diamondAutHBar M H (isDiamondAutHBar_diamondAutHBar hex) σ) P
  · rw [diamondHBar_of_not M H hex, diamondHBar_of_not M H hex]

end Diamond

end GaloisSmulGenOpHComm

open GaloisSmulGenOpHComm in

/-- **The Galois action commutes with the `X_H(M)` generator operators**: for every Hecke
generator `g` of `CohCarrier.Gen M S`, `σ • (genOpH M H S g P) = genOpH M H S g (σ • P)`.
Statement verbatim from `Theorems/Thm_ModularCurve_galois_smul_genOpH_comm.lean`; proof after
the pin's `S_` file. -/
theorem galois_smul_genOpH_comm (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M S)
    (P : ModularCurve.JH M H) :
    σ • (ModularCurve.genOpH M H S g P) = ModularCurve.genOpH M H S g (σ • P) := by
  cases g with
  | T ℓ hℓ hℓS hℓM =>
      have : NeZero ℓ := ⟨hℓ.ne_zero⟩
      exact galois_smul_heckeOperatorHAlong M H ℓ σ P
  | U q hq hqM =>
      have : NeZero q := ⟨hq.ne_zero⟩
      exact galois_smul_heckeOperatorHAlong M H q σ P
  | dia d => exact galois_smul_diamondHBar M H d σ P

end GenOpGalois

end ModularCurve

end
