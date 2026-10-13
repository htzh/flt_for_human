/-
  The Tate curve and its `ℓ`-torsion points at the `p`-th power of the Tate
  parameter: `curve (q ^ p) = tateBase`, and the `pointX`/`pointY` coordinates of
  `q ^ p` at `C c` and at `C c * q ^ j`, identified with the toric and non-toric
  points.

  These are the port's tier-1 surface over the tier-3 engine
  (`TateCurve/Bridge.lean`, `TateCurve/NonToricSlot.lean`). Each statement is the
  pin's `Theorems/Thm_ModularCurve_<name>.lean` wrapper verbatim — that wrapper,
  not the `S_` file's `solution`, is the checker's statement authority — and each
  proof is the one-line application of the engine's kernel
  `ModularCurve.TateCurve.<name>`.

  The five near-identical pin `S_ModularCurve_tateCurve_*` files carry one shared
  `ModularCurve.BridgeX` development written up to five times; see
  TOPIC-tate-curve-twins.md. The engine is tier 3 and recorded in
  spec/UNWIRED-PUBLIC.md.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_tateCurve_curve_X_pow_eq_tateBase.lean
  (and the four sibling wrappers `Theorems/Thm_ModularCurve_tateCurve_*.lean`).
-/
import FLTForHuman.ModularCurve.TateCurve.Bridge
import FLTForHuman.ModularCurve.TateCurve.NonToricSlot

set_option autoImplicit false

noncomputable section

open scoped LaurentSeries.XAdic

open PowerSeries HahnSeries

namespace ModularCurve

-- pin: tateCurve_curve_X_pow_eq_tateBase (Theorems/Thm_ModularCurve_tateCurve_curve_X_pow_eq_tateBase.lean)
theorem tateCurve_curve_X_pow_eq_tateBase (F : Type*) [Field F] (p : ℕ) [NeZero p] :
    TateCurve.curve ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) = ModularCurve.tateBase F p :=
  TateCurve.curve_X_pow_eq_tateBase F p

-- pin: tateCurve_pointX_C_eq_tateToricPoint_fst (Theorems/Thm_ModularCurve_tateCurve_pointX_C_eq_tateToricPoint_fst.lean)
theorem tateCurve_pointX_C_eq_tateToricPoint_fst (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (hc : (c : F) ≠ 1) :
    TateCurve.pointX ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C (c : F))
      = (ModularCurve.tateToricPoint F p c).1 :=
  TateCurve.pointX_toric F p c hc

-- pin: tateCurve_pointY_C_eq_tateToricPoint_snd (Theorems/Thm_ModularCurve_tateCurve_pointY_C_eq_tateToricPoint_snd.lean)
theorem tateCurve_pointY_C_eq_tateToricPoint_snd (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (hc : (c : F) ≠ 1) :
    TateCurve.pointY ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C (c : F))
      = (ModularCurve.tateToricPoint F p c).2 :=
  TateCurve.pointY_toric F p c hc

-- pin: tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst (Theorems/Thm_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean)
theorem tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointX ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (ModularCurve.nonToricPoint F p c j).1 :=
  TateCurve.pointX_slot F p c j hj hjp

-- pin: tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd (Theorems/Thm_ModularCurve_tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd.lean)
theorem tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointY ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (ModularCurve.nonToricPoint F p c j).2 :=
  TateCurve.pointY_slot F p c j hj hjp

end ModularCurve

end
