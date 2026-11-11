/-
  The evaluated form of a bivariate integer polynomial, and the transpose.

  `ev Φ x y` is `Φ ∈ ℤ[X][Y]` evaluated at `(x, y)` with the integer coefficients cast
  into a commutative ring `A`: the coefficient-cast evaluation, which mathlib's same-ring
  `Polynomial.evalEval` does not cover. Two identifications place it in mathlib's
  bivariate API (`ev_eq_evalEval`, `ev_eq_aevalAeval`); the rest is the calculus the
  transpose argument needs — naturality in the coefficient ring (`map_ev`), commutation
  with `Bivariate.swap` (`ev_swap`), its value at integer points (`ev_int`), and
  additivity on differences (`ev_sub`). `swap_eq_of_evalSymm` is the converse half of
  the symmetry equivalence: a polynomial whose evaluations agree on swapped arguments
  is its own transpose.

  FLT provenance, pinned `aa2d8b3`: the `SepFibre` prelude that the pin copies into its
  `q`-expansion `S_` files;
  `P2M/Sol/S_ModularCurve_swapBivar_eq_of_evalSymm.lean` (95 lines) carries it whole.
  The pin's `ev_int` reads `ev Φ a b = Φ.evalEval a b`, which leaves the coefficient ring
  to be inferred and so elaborates at `ℤ`; `ev_int` below pins `A` and makes the cast
  explicit, which is the form the transpose argument reads off `Int.cast_injective`.

  Assumes `EvalSymm` and `swapBivar` from `Defs/PhiGen`, `LaurentSeries ℚ` from
  `Defs/Laurent`, and mathlib's bivariate API (`Bivariate.swap`, `aevalAeval`,
  `mapRingHom_evalEval`).

  spec-pin: P2M/Sol/S_ModularCurve_swapBivar_eq_of_evalSymm.lean
-/
import FLTForHuman.ModularCurve.Defs.PhiGen
import Mathlib.Algebra.Polynomial.Bivariate

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ModularCurve

section Eval

variable {A : Type*} [CommRing A]

/-- The evaluated form of `Φ` in two variables of a commutative ring: the bivariate
`Φ ∈ ℤ[X][Y]` at `(x, y)`, with the integer coefficients cast into `A`. -/
def ev (Φ : Polynomial (Polynomial ℤ)) (x y : A) : A :=
  Φ.eval₂ (eval₂RingHom (Int.castRingHom A) x) y

theorem aeval_toRingHom_eq [Algebra ℤ A] (x : A) :
    (Polynomial.aeval (R := ℤ) x).toRingHom = eval₂RingHom (Int.castRingHom A) x :=
  Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp)

/-- `ev` is mathlib's coefficient-cast `evalEval`. -/
theorem ev_eq_evalEval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = (Φ.map (mapRingHom (Int.castRingHom A))).evalEval x y := by
  rw [ev, ← eval₂_eval₂RingHom_apply]

/-- `ev` is mathlib's `aevalAeval`. -/
theorem ev_eq_aevalAeval (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev Φ x y = aevalAeval x y Φ := by
  have h : eval₂RingHom (eval₂RingHom (Int.castRingHom A) x) y
      = (aevalAeval (R := ℤ) x y).toRingHom := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_) ?_
    · simp
    · simp
  exact RingHom.congr_fun h Φ

variable {B : Type*} [CommRing B]

/-- `ev` is natural in the coefficient ring. -/
theorem map_ev (φ : A →+* B) (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    φ (ev Φ x y) = ev Φ (φ x) (φ y) := by
  rw [ev_eq_evalEval, ev_eq_evalEval, ← map_mapRingHom_evalEval φ, Polynomial.map_map,
    mapRingHom_comp, RingHom.ext_int (φ.comp (Int.castRingHom A)) (Int.castRingHom B)]

/-- `ev` commutes with the transpose: evaluating the swapped polynomial at `(x, y)` is
evaluating `Φ` at `(y, x)`. -/
theorem ev_swap (Φ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev (Bivariate.swap Φ) x y = ev Φ y x := by
  rw [ev_eq_aevalAeval, ev_eq_aevalAeval, Bivariate.aevalAeval_swap]

/-- `ev` at integer points is the integer evaluation, cast into `A`. -/
theorem ev_int (Φ : Polynomial (Polynomial ℤ)) (a b : ℤ) :
    ev Φ (a : A) (b : A) = ((Φ.evalEval a b : ℤ) : A) := by
  rw [ev, eval₂_eval₂RingHom_apply]
  exact map_mapRingHom_evalEval (Int.castRingHom A) Φ a b

theorem ev_sub (Φ Ψ : Polynomial (Polynomial ℤ)) (x y : A) :
    ev (Φ - Ψ) x y = ev Φ x y - ev Ψ x y := by
  rw [ev_eq_aevalAeval, map_sub, ← ev_eq_aevalAeval, ← ev_eq_aevalAeval]

end Eval

/-- Evaluated symmetry forces the transpose to be `Φ` itself. `Bivariate.swap Φ - Φ`
evaluates to zero at every pair over `LaurentSeries ℚ` (that is `EvalSymm`, read through
`ev`), hence at every pair of integers, hence is zero. -/
theorem swap_eq_of_evalSymm {Φ : Polynomial (Polynomial ℤ)} (h : EvalSymm Φ) :
    Bivariate.swap Φ = Φ := by
  set G : Polynomial (Polynomial ℤ) := Bivariate.swap Φ - Φ with hG
  have hL : ∀ x y : LaurentSeries ℚ, ev G x y = 0 := fun x y => by
    have hxy := h x y
    rw [aeval_toRingHom_eq, aeval_toRingHom_eq] at hxy
    rw [hG, ev_sub, ev_swap, sub_eq_zero]
    exact hxy.symm
  have hZ : ∀ a b : ℤ, G.evalEval a b = 0 := fun a b => by
    have h0 : ((G.evalEval a b : ℤ) : LaurentSeries ℚ) = 0 := by
      rw [← ev_int G a b]
      simpa using hL (a : LaurentSeries ℚ) (b : LaurentSeries ℚ)
    exact Int.cast_injective (α := ℚ)
      ((algebraMap ℚ (LaurentSeries ℚ)).injective (by simpa using h0))
  have h1 : ∀ b : ℤ, G.eval (Polynomial.C b) = 0 := fun b =>
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun a : ℤ => a) (fun _ _ h => h) fun a => hZ a b)
  have h2 : G = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ (Set.infinite_of_injective_forall_mem
      (f := fun b : ℤ => Polynomial.C b) (fun _ _ h => Polynomial.C_injective h) fun b => h1 b)
  exact sub_eq_zero.mp h2

end ModularCurve

end
