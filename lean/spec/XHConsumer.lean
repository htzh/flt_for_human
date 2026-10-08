/-
  Consumer specification for the `X_H(M)` definition layer (SET-H-A of
  `topics/hecke/TOPIC-xH-hecke-diamond-inputs.md`).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the `X_H(M)` vocabulary: the objects the port must make
  possible, expressed in Lean so each one is either bound or not. It is a
  deliverable measure, not a proof obligation.

  It is deliberately **not part of any library**. `lake build` does not see it
  (nothing globs `spec/`), so it cannot break the verified port's green build.
  Run it by hand:

      cd lean
      lake env lean spec/XHConsumer.lean 2>&1 | grep -c 'error\|warning'

  The error count is the metric.

  HOW TO READ IT
  --------------
  Every zone is labelled:

    [xh-ff]      ZONE XH-A — after `XH/FunctionField.lean`. The `X_H(M)` function
                 field, its `ℚ̄` base change, and every `Γ_H` monotonicity bridge.
    [xh-hecke]   ZONE XH-B — after `XH/HeckeOperator.lean`. The α/β degeneracy
                 maps, their coefficient formulas, and the seven-input bundle
                 `HeckeInputsHAlong` with its constructor and β accessor.
    [xh-diamond] ZONE XH-C — after `XH/Operators.lean`. The diamond predicate
                 `IsDiamondAutHBar`, the choice function `diamondAutHBar` with its
                 two lemmas, and the bundle `HeckeDiamondInputsHAll` destructured
                 into a real `HeckeInputsHAlong` and a real diamond automorphism.

  Every example names its declaration, so deleting any of the three modules (or
  the one declaration it consumes) makes that line fail. The bundle halves are
  *consumed* under a hypothesis — SET-H-C supplies the proofs, not this set.
-/

import FLTForHuman.ModularCurve.XH.FunctionField
import FLTForHuman.ModularCurve.XH.HeckeOperator
import FLTForHuman.ModularCurve.XH.Operators

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve

/-! ## Zone XH-A — `[xh-ff]` the `X_H(M)` function field -/

-- The definition, at `(K, M, H) = (ℚ, 2, ⊥)`: a real `IntermediateField`.
example : IntermediateField ℚ (LaurentSeries ℚ) := xHFunctionFieldC ℚ 2 ⊥

-- The `ℚ`-specialization, definitionally.
example : xHFunctionFieldC ℚ 2 ⊥ = xHFunctionField 2 ⊥ := xHFunctionFieldC_rat 2 ⊥

-- The top field at `t = M * ℓ`, the codomain of both Hecke maps.
example (ℓ : ℕ) [NeZero ℓ] : IntermediateField ℚ (LaurentSeries ℚ) :=
  xHTopFunctionFieldC ℚ 2 ⊥ (2 * ℓ)

-- The α-inclusion bridge.
example : xHFunctionFieldC ℚ 2 ⊥ ≤ xHTopFunctionFieldC ℚ 2 ⊥ (2 * 3) :=
  xHFunctionFieldC_le_top ℚ 2 ⊥ (2 * 3)

-- The level-one collapse.
example : xHTopFunctionFieldC ℚ 2 ⊥ 1 = xHFunctionFieldC ℚ 2 ⊥ :=
  xHTopFunctionFieldC_one ℚ 2 ⊥

-- `H = ⊤` is `Γ₀`; `H = ⊥` is `Γ₁`.
example : xHFunctionFieldC ℚ 2 ⊤ = qExpFunctionFieldC ℚ (Gamma0 2) :=
  xHFunctionFieldC_top ℚ 2

example : xHFunctionFieldC ℚ 2 ⊥ = x1FunctionFieldC ℚ 2 :=
  xHFunctionFieldC_bot ℚ 2

example : qExpFunctionFieldC ℚ (Gamma0 2) ≤ xHFunctionFieldC ℚ 2 ⊥ :=
  x0_le_xHFunctionFieldC ℚ 2 ⊥

example : xHFunctionFieldC ℚ 2 ⊥ ≤ x1FunctionFieldC ℚ 2 :=
  xHFunctionFieldC_le_x1 ℚ 2 ⊥

-- The antitone direction: `⊥ ≤ ⊤`, so `X_⊤ ≤ X_⊥`.
example : xHFunctionFieldC ℚ 2 ⊤ ≤ xHFunctionFieldC ℚ 2 ⊥ :=
  xHFunctionFieldC_antitone (K := ℚ) (M := 2) (H := ⊥) (H' := ⊤) bot_le

-- The `ℚ̄`-base change, as a real `IntermediateField`.
example : IntermediateField (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) :=
  xHFunctionFieldBar 2 ⊥

/-! ## Zone XH-B — `[xh-hecke]` the α/β Hecke maps and `HeckeInputsHAlong` -/

-- The α map at `(L, M, H, ℓ) = (ℚ̄, 2, ⊥, 3)`, with the pinned codomain.
example : xHFunctionFieldBar 2 ⊥ →ₐ[AlgebraicClosure ℚ]
    laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ 2 ⊥ (2 * 3)) :=
  heckeAlphaHBar (AlgebraicClosure ℚ) 2 ⊥ 3

-- Its coefficient formula, through the `[simp]` bridge.
example (x : laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField 2 ⊥)) :
    (heckeAlphaHBar (AlgebraicClosure ℚ) 2 ⊥ 3 x : LaurentSeries (AlgebraicClosure ℚ))
      = (x : LaurentSeries (AlgebraicClosure ℚ)) :=
  coe_heckeAlphaHBar 2 ⊥ 3 x

-- It is *the* inclusion, definitionally.
example (h : laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField 2 ⊥)
    ≤ laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ 2 ⊥ (2 * 3))) :
    heckeAlphaHBar (AlgebraicClosure ℚ) 2 ⊥ 3 = IntermediateField.inclusion h :=
  heckeAlphaHBar_eq_inclusion 2 ⊥ 3 h

-- The β map: the `q ↦ q^ℓ` substitution, with the pinned codomain.
example : laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField 2 ⊥) →ₐ[AlgebraicClosure ℚ]
    laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ 2 ⊥ (2 * 3)) :=
  heckeBetaHBar (AlgebraicClosure ℚ) 2 ⊥ 3

-- Its coefficient formula, under the β-definedness hypothesis.
example (h : HeckeBetaHDefined 2 ⊥ 3)
    (x : laurentBaseChange (AlgebraicClosure ℚ) (xHFunctionField 2 ⊥)) :
    (heckeBetaHBar (AlgebraicClosure ℚ) 2 ⊥ 3 x : LaurentSeries (AlgebraicClosure ℚ))
      = qExpand (AlgebraicClosure ℚ) 3 (x : LaurentSeries (AlgebraicClosure ℚ)) :=
  coe_heckeBetaHBar 2 ⊥ 3 h x

-- `HeckeInputsHAlong` is a real `Prop`; its β accessor destructures the bundle.
example (h : HeckeInputsHAlong (AlgebraicClosure ℚ) 2 ⊥ 3) : HeckeBetaHDefined 2 ⊥ 3 :=
  h.betaHDefined

-- The constructor, at the pinned binder order.
example (h0 : HeckeBetaHDefined 2 ⊥ 3)
    (hα : HeckeAlphaHBarIntegral (AlgebraicClosure ℚ) 2 ⊥ 3)
    (hβ : HeckeBetaHBarIntegral (AlgebraicClosure ℚ) 2 ⊥ 3)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ 2 ⊥ (2 * 3)))]
    (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ)
      (heckeBetaHBar (AlgebraicClosure ℚ) 2 ⊥ 3) hβ)
    (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaHBar (AlgebraicClosure ℚ) 2 ⊥ 3))
    (hN : NormFormulaAlong (AlgebraicClosure ℚ)
      (heckeAlphaHBar (AlgebraicClosure ℚ) 2 ⊥ 3) hfin) :
    HeckeInputsHAlong (AlgebraicClosure ℚ) 2 ⊥ 3 :=
  heckeInputsHAlong_intro h0 hα hβ hFI hfin hN

/-! ## Zone XH-C — `[xh-diamond]` `IsDiamondAutHBar`, `diamondAutHBar`,
`HeckeDiamondInputsHAll` -/

-- `IsDiamondAutHBar` is a real `Prop` on the `ℚ̄`-automorphisms.
example (d : (ZMod 2)ˣ)
    (σ : xHFunctionFieldBar 2 ⊥ ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 2 ⊥) :
    Prop :=
  IsDiamondAutHBar 2 ⊥ d σ

-- The choice function at a concrete `d`.
example (d : (ZMod 2)ˣ) :
    xHFunctionFieldBar 2 ⊥ ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 2 ⊥ :=
  diamondAutHBar 2 ⊥ d

-- The choice lemma: an existing diamond automorphism is `diamondAutHBar`.
example {d : (ZMod 2)ˣ}
    (h : ∃ σ : xHFunctionFieldBar 2 ⊥ ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 2 ⊥,
      IsDiamondAutHBar 2 ⊥ d σ) :
    IsDiamondAutHBar 2 ⊥ d (diamondAutHBar 2 ⊥ d) :=
  isDiamondAutHBar_diamondAutHBar h

-- The junk branch.
example {d : (ZMod 2)ˣ}
    (h : ¬ ∃ σ : xHFunctionFieldBar 2 ⊥ ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 2 ⊥,
      IsDiamondAutHBar 2 ⊥ d σ) :
    diamondAutHBar 2 ⊥ d = AlgEquiv.refl :=
  diamondAutHBar_of_not h

-- The bundle, destructured: the Hecke half at the concrete prime `ℓ = 3` ...
example (h : HeckeDiamondInputsHAll 2 ⊥) :
    HeckeInputsHAlong (AlgebraicClosure ℚ) 2 ⊥ 3 :=
  h.heckeInputsHAlong 3 Nat.prime_three

-- ... and the diamond half at a concrete `d`, as a real diamond automorphism ...
example (h : HeckeDiamondInputsHAll 2 ⊥) (d : (ZMod 2)ˣ) :
    IsDiamondAutHBar 2 ⊥ d (diamondAutHBar 2 ⊥ d) :=
  h.isDiamondAutHBar d

-- ... whose `∃`-half is consumed directly.
example (h : HeckeDiamondInputsHAll 2 ⊥) (d : (ZMod 2)ˣ) :
    ∃ σ : xHFunctionFieldBar 2 ⊥ ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar 2 ⊥,
      IsDiamondAutHBar 2 ⊥ d σ :=
  h.2 d

end ModularCurve

end
