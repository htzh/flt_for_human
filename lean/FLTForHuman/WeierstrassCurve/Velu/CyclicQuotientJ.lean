/-
The cyclic quotient's `j`-invariant: the `cyclicQuotientJ` vocabulary and its two
well-definedness lemmas (V1-SET-3, `Velu/CyclicQuotientJ.lean`).

Statements are transcribed verbatim from the pinned FLT `aa2d8b3` sources — the
`Theorems/` wrappers are the statement authority for the two headline nodes, and
`Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean` (207 lines, 46
declarations) for the vocabulary it declares:

* `Theorems/Thm_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.lean`
* `Theorems/Thm_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.lean`

Proof bodies come from the corresponding `P2M/Sol/S_*.lean` files
(`S_..._cyclicQuotientJ_variableChange_eq.lean` 315 lines, namespace
`P2MKcCQJvc`; `S_..._cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.lean` 264
lines, namespace `P2MKcCQJbc`), adapted to mathlib `v4.34.0`. Every proof-local
helper is `private`, so the checker diffs only the pin's public surface. The
pin's `set_option maxHeartbeats` bumps are dropped (the port's global cap is
4,000,000 and every node closes under it); no `maxRecDepth` bump is needed.

The column's subject: `cyclicQuotientJ V H N` is `c₄³/Δ` of the curve obtained by
iterating the ℓ-step quotient over `N.primeFactorsList`; the quotient curve is
`stepCurve V H ℓ`, which is the order-two quotient `twoVeluCurve` for `ℓ = 2`
(the SET-1 vocabulary) and the odd-order `xVeluCurve` otherwise. The two lemmas
say the construction is invariant under a variable change `C` (given the
transport `vcInvFun_add` of `Velu/VariableChangePoint.lean`) and commutes with
base change to an algebraically closed field.

`absSum` over a possibly infinite set (`absSum_of_finite`/`absSum_of_infinite`)
is the pin's "sum over the finite kernel, zero if infinite" device; mathlib has
no analogue, and no `cyclicQuotientCurve`/`cyclicQuotientJ`. The `map_velu*`
commutation block that `xVeluG_map` consumes is **imported** from
`Velu/Formula.lean` (public since the H5/SET-1 work), not re-declared.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.Defs
import FLTForHuman.WeierstrassCurve.Velu.OrderTwo
import FLTForHuman.WeierstrassCurve.Velu.Formula
import FLTForHuman.WeierstrassCurve.Velu.VariableChangePoint
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

set_option autoImplicit false

noncomputable section

open Polynomial Finset

namespace WeierstrassCurve

section XData

variable {R : Type*} [CommRing R] (V : WeierstrassCurve R)

def xVeluT (x : R) : R := 6 * x ^ 2 + V.b₂ * x + V.b₄

def xVeluU (x : R) : R := 4 * x ^ 3 + V.b₂ * x ^ 2 + 2 * V.b₄ * x + V.b₆

def xVeluW (x : R) : R := V.xVeluU x + x * V.xVeluT x

theorem xVeluT_eq_veluT (x y : R) : V.xVeluT x = V.veluT x y := by
  rw [xVeluT, veluT_eq]

theorem xVeluU_eq_veluU {x y : R} (h : V.toAffine.Equation x y) : V.xVeluU x = V.veluU x y := by
  rw [V.veluU_eq_Ψ₂Sq_eval h, xVeluU, Ψ₂Sq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]

theorem xVeluW_eq_veluW {x y : R} (h : V.toAffine.Equation x y) : V.xVeluW x = V.veluW x y := by
  rw [xVeluW, veluW, V.xVeluU_eq_veluU h, V.xVeluT_eq_veluT x y]

end XData

section Field

variable {L : Type*} [Field L]

def absSum (X : Set L) (g : L → L) : L :=
  haveI := Classical.dec X.Finite
  if X.Finite then ∑ᶠ x ∈ X, g x else 0

theorem absSum_of_finite {X : Set L} (hX : X.Finite) (g : L → L) :
    absSum X g = ∑ x ∈ hX.toFinset, g x := by
  rw [absSum, if_pos hX, finsum_mem_eq_finite_toFinset_sum g hX]

theorem absSum_of_infinite {X : Set L} (hX : X.Infinite) (g : L → L) : absSum X g = 0 := by
  rw [absSum, if_neg hX]

def xVeluCurve (V : WeierstrassCurve L) (X : Set L) : WeierstrassCurve L where
  a₁ := V.a₁
  a₂ := V.a₂
  a₃ := V.a₃
  a₄ := V.a₄ - 5 * absSum X V.xVeluT
  a₆ := V.a₆ - V.b₂ * absSum X V.xVeluT - 7 * absSum X V.xVeluW

def xVeluX (V : WeierstrassCurve L) (X : Set L) (x : L) : L :=
  x + absSum X fun x₀ => V.xVeluT x₀ / (x - x₀) + V.xVeluU x₀ / (x - x₀) ^ 2

@[simp] theorem xVeluCurve_a₁ (V : WeierstrassCurve L) (X : Set L) : (V.xVeluCurve X).a₁ = V.a₁ := rfl
@[simp] theorem xVeluCurve_a₂ (V : WeierstrassCurve L) (X : Set L) : (V.xVeluCurve X).a₂ = V.a₂ := rfl
@[simp] theorem xVeluCurve_a₃ (V : WeierstrassCurve L) (X : Set L) : (V.xVeluCurve X).a₃ = V.a₃ := rfl
theorem xVeluCurve_a₄ (V : WeierstrassCurve L) (X : Set L) :
    (V.xVeluCurve X).a₄ = V.a₄ - 5 * absSum X V.xVeluT := rfl
theorem xVeluCurve_a₆ (V : WeierstrassCurve L) (X : Set L) :
    (V.xVeluCurve X).a₆ = V.a₆ - V.b₂ * absSum X V.xVeluT - 7 * absSum X V.xVeluW := rfl

def twoTorsionY (V : WeierstrassCurve L) (x₀ : L) : L := -(V.a₁ * x₀ + V.a₃) / 2

def xVeluG (V : WeierstrassCurve L) (x₀ : L) : L := V.veluGx x₀ (V.twoTorsionY x₀)

def twoVeluCurve (V : WeierstrassCurve L) (X : Set L) : WeierstrassCurve L where
  a₁ := V.a₁
  a₂ := V.a₂
  a₃ := V.a₃
  a₄ := V.a₄ - 5 * absSum X V.xVeluG
  a₆ := V.a₆ - V.b₂ * absSum X V.xVeluG - 7 * absSum X fun x => x * V.xVeluG x

def twoVeluX (V : WeierstrassCurve L) (X : Set L) (x : L) : L :=
  x + absSum X fun x₀ => V.xVeluG x₀ / (x - x₀)

@[simp] theorem twoVeluCurve_a₁ (V : WeierstrassCurve L) (X : Set L) : (V.twoVeluCurve X).a₁ = V.a₁ := rfl
@[simp] theorem twoVeluCurve_a₂ (V : WeierstrassCurve L) (X : Set L) : (V.twoVeluCurve X).a₂ = V.a₂ := rfl
@[simp] theorem twoVeluCurve_a₃ (V : WeierstrassCurve L) (X : Set L) : (V.twoVeluCurve X).a₃ = V.a₃ := rfl
theorem twoVeluCurve_a₄ (V : WeierstrassCurve L) (X : Set L) :
    (V.twoVeluCurve X).a₄ = V.a₄ - 5 * absSum X V.xVeluG := rfl
theorem twoVeluCurve_a₆ (V : WeierstrassCurve L) (X : Set L) :
    (V.twoVeluCurve X).a₆ = V.a₆ - V.b₂ * absSum X V.xVeluG - 7 * absSum X fun x => x * V.xVeluG x :=
  rfl

variable [DecidableEq L]

def kernelXSet (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) : Set L :=
  (fun P => P.coordsOrZero.1) '' {P | P ∈ H ∧ P ≠ 0 ∧ ℓ • P = 0}

def coKernelXSet (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) : Set L :=
  (fun P => P.coordsOrZero.1) '' {P | P ∈ H ∧ ℓ • P ≠ 0}

def stepCurve (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    WeierstrassCurve L :=
  if ℓ = 2 then V.twoVeluCurve (V.kernelXSet H 2) else V.xVeluCurve (V.kernelXSet H ℓ)

def stepX (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) (x : L) : L :=
  if ℓ = 2 then V.twoVeluX (V.kernelXSet H 2) x else V.xVeluX (V.kernelXSet H ℓ) x

theorem stepCurve_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.stepCurve H 2 = V.twoVeluCurve (V.kernelXSet H 2) :=
  if_pos rfl

theorem stepCurve_of_ne_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) {ℓ : ℕ}
    (hℓ : ℓ ≠ 2) : V.stepCurve H ℓ = V.xVeluCurve (V.kernelXSet H ℓ) :=
  if_neg hℓ

theorem stepX_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (x : L) :
    V.stepX H 2 x = V.twoVeluX (V.kernelXSet H 2) x :=
  if_pos rfl

theorem stepX_of_ne_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) {ℓ : ℕ}
    (hℓ : ℓ ≠ 2) (x : L) : V.stepX H ℓ x = V.xVeluX (V.kernelXSet H ℓ) x :=
  if_neg hℓ

def subgroupOfX (V' : WeierstrassCurve L) (Y : Set L) : AddSubgroup V'.toAffine.Point :=
  AddSubgroup.closure {P | P ≠ 0 ∧ P.coordsOrZero.1 ∈ Y}

def stepSubgroup (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    AddSubgroup (V.stepCurve H ℓ).toAffine.Point :=
  subgroupOfX (V.stepCurve H ℓ) (V.stepX H ℓ '' V.coKernelXSet H ℓ)

variable (L) in

abbrev CQJState : Type _ := (Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) × ℕ

def cqjStep (s : CQJState L) : CQJState L :=
  ⟨⟨s.1.1.stepCurve s.1.2 s.2.minFac, s.1.1.stepSubgroup s.1.2 s.2.minFac⟩, s.2 / s.2.minFac⟩

def cqjIterate (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) : CQJState L :=
  cqjStep^[N.primeFactorsList.length] ⟨⟨V, H⟩, N⟩

def cyclicQuotientCurve (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    WeierstrassCurve L :=
  (V.cqjIterate H N).1.1

def cyclicQuotientJ (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) : L :=
  (V.cyclicQuotientCurve H N).c₄ ^ 3 / (V.cyclicQuotientCurve H N).Δ

theorem cqjIterate_def (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    V.cqjIterate H N = cqjStep^[N.primeFactorsList.length] ⟨⟨V, H⟩, N⟩ := rfl

theorem cyclicQuotientCurve_def (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point)
    (N : ℕ) : V.cyclicQuotientCurve H N = (V.cqjIterate H N).1.1 := rfl

theorem cyclicQuotientJ_def (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    V.cyclicQuotientJ H N =
      (V.cyclicQuotientCurve H N).c₄ ^ 3 / (V.cyclicQuotientCurve H N).Δ := rfl

theorem cqjStep_apply (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (n : ℕ) :
    cqjStep ⟨⟨V, H⟩, n⟩ =
      ⟨⟨V.stepCurve H n.minFac, V.stepSubgroup H n.minFac⟩, n / n.minFac⟩ := rfl

theorem cqjIterate_one (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.cqjIterate H 1 = ⟨⟨V, H⟩, 1⟩ := by
  simp [cqjIterate, Nat.primeFactorsList_one]

theorem cyclicQuotientCurve_one (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.cyclicQuotientCurve H 1 = V := by
  rw [cyclicQuotientCurve_def, cqjIterate_one]

theorem cyclicQuotientJ_one (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.cyclicQuotientJ H 1 = V.c₄ ^ 3 / V.Δ := by
  rw [cyclicQuotientJ_def, cyclicQuotientCurve_one]

theorem length_primeFactorsList_eq_succ {N : ℕ} (hN : 2 ≤ N) :
    N.primeFactorsList.length = (N / N.minFac).primeFactorsList.length + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  rw [Nat.primeFactorsList, List.length_cons]

theorem cqjIterate_eq_of_two_le (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point)
    {N : ℕ} (hN : 2 ≤ N) :
    V.cqjIterate H N =
      (V.stepCurve H N.minFac).cqjIterate (V.stepSubgroup H N.minFac) (N / N.minFac) := by
  rw [cqjIterate, length_primeFactorsList_eq_succ hN, Function.iterate_succ_apply]
  rfl

theorem cyclicQuotientCurve_eq_of_two_le (V : WeierstrassCurve L)
    (H : AddSubgroup V.toAffine.Point) {N : ℕ} (hN : 2 ≤ N) :
    V.cyclicQuotientCurve H N =
      (V.stepCurve H N.minFac).cyclicQuotientCurve (V.stepSubgroup H N.minFac) (N / N.minFac) := by
  rw [cyclicQuotientCurve_def, cqjIterate_eq_of_two_le V H hN, cyclicQuotientCurve_def]

theorem cyclicQuotientJ_eq_of_two_le (V : WeierstrassCurve L)
    (H : AddSubgroup V.toAffine.Point) {N : ℕ} (hN : 2 ≤ N) :
    V.cyclicQuotientJ H N =
      (V.stepCurve H N.minFac).cyclicQuotientJ (V.stepSubgroup H N.minFac) (N / N.minFac) := by
  rw [cyclicQuotientJ_def, cyclicQuotientCurve_eq_of_two_le V H hN, cyclicQuotientJ_def]

theorem cyclicQuotientJ_eq_j (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ)
    [(V.cyclicQuotientCurve H N).IsElliptic] :
    V.cyclicQuotientJ H N = (V.cyclicQuotientCurve H N).j := by
  rw [cyclicQuotientJ_def, WeierstrassCurve.j, div_eq_mul_inv, mul_comm, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ']

end Field

end WeierstrassCurve


/-! ### `S_WeierstrassCurve_cyclicQuotientJ_variableChange_eq.lean` — the variable-change transport

The pin's own namespace `P2MKcCQJvc`, kept verbatim. Every declaration of the pin's
file is `private` here: the pin's `vcInvHom` (the bundled `→+` built from
`Affine.Point.vcInvFun_add`) is proof-local, so only the headline below is part of
the port's public surface. -/

open WeierstrassCurve WeierstrassCurve.Affine

namespace P2MKcCQJvc

variable {L : Type*} [Field L] [DecidableEq L] (C : VariableChange L)

private noncomputable def vcInvHom (W : WeierstrassCurve L) : W.toAffine.Point →+ (C • W).toAffine.Point where
  toFun := Point.vcInvFun C W
  map_zero' := rfl
  map_add' := Point.vcInvFun_add C W

private theorem vcInvHom_apply (W : WeierstrassCurve L) (P : W.toAffine.Point) :
    vcInvHom C W P = Point.vcInvFun C W P := rfl

private theorem vcFun_vcInvHom (W : WeierstrassCurve L) (P : W.toAffine.Point) :
    Point.vcFun C W (vcInvHom C W P) = P := Point.vcFun_rightInverse P

private theorem vcInvHom_vcFun (W : WeierstrassCurve L) (P : (C • W).toAffine.Point) :
    vcInvHom C W (Point.vcFun C W P) = P := Point.vcFun_leftInverse P

private theorem vcInvHom_injective (W : WeierstrassCurve L) : Function.Injective (vcInvHom C W) :=
  Function.LeftInverse.injective (g := Point.vcFun C W) (vcFun_vcInvHom C W)

private theorem vcInvHom_ne_zero (W : WeierstrassCurve L) {P : W.toAffine.Point} :
    vcInvHom C W P ≠ 0 ↔ P ≠ 0 := by
  rw [Ne, Ne, ← map_zero (vcInvHom C W), (vcInvHom_injective C W).eq_iff]

private theorem fst_coordsOrZero_vcInvHom (W : WeierstrassCurve L) {P : W.toAffine.Point} (hP : P ≠ 0) :
    (vcInvHom C W P).coordsOrZero.1 = vcXInv C P.coordsOrZero.1 := by
  rcases P with _ | ⟨x, y, h⟩
  · exact absurd rfl hP
  · rfl

private theorem kernelXSet_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (ℓ : ℕ) :
    (C • W).kernelXSet (H.map (vcInvHom C W)) ℓ = vcXInv C '' W.kernelXSet H ℓ := by
  ext x'
  simp only [kernelXSet, Set.mem_image, Set.mem_setOf_eq, AddSubgroup.mem_map]
  constructor
  · rintro ⟨P', ⟨⟨P, hP, rfl⟩, hne, hsm⟩, rfl⟩
    have hne' : P ≠ 0 := (vcInvHom_ne_zero C W).1 hne
    refine ⟨P.coordsOrZero.1, ⟨P, ⟨hP, hne', ?_⟩, rfl⟩, (fst_coordsOrZero_vcInvHom C W hne').symm⟩
    apply vcInvHom_injective C W
    rw [map_nsmul, hsm, map_zero]
  · rintro ⟨x, ⟨P, ⟨hP, hne, hsm⟩, rfl⟩, rfl⟩
    refine ⟨vcInvHom C W P, ⟨⟨P, hP, rfl⟩, (vcInvHom_ne_zero C W).2 hne, ?_⟩,
      fst_coordsOrZero_vcInvHom C W hne⟩
    rw [← map_nsmul, hsm, map_zero]

private theorem coKernelXSet_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (ℓ : ℕ) :
    (C • W).coKernelXSet (H.map (vcInvHom C W)) ℓ = vcXInv C '' W.coKernelXSet H ℓ := by
  ext x'
  simp only [coKernelXSet, Set.mem_image, Set.mem_setOf_eq, AddSubgroup.mem_map]
  constructor
  · rintro ⟨P', ⟨⟨P, hP, rfl⟩, hsm⟩, rfl⟩
    have hne' : P ≠ 0 := by rintro rfl; exact hsm (by rw [map_zero, smul_zero])
    refine ⟨P.coordsOrZero.1, ⟨P, ⟨hP, fun h => hsm ?_⟩, rfl⟩, (fst_coordsOrZero_vcInvHom C W hne').symm⟩
    rw [← map_nsmul, h, map_zero]
  · rintro ⟨x, ⟨P, ⟨hP, hsm⟩, rfl⟩, rfl⟩
    have hne : P ≠ 0 := by rintro rfl; exact hsm (smul_zero _)
    refine ⟨vcInvHom C W P, ⟨⟨P, hP, rfl⟩, fun h => hsm ?_⟩, fst_coordsOrZero_vcInvHom C W hne⟩
    apply vcInvHom_injective C W
    rw [map_nsmul, h, map_zero]

omit [DecidableEq L] in
private theorem xVeluT_vc (W : WeierstrassCurve L) (x : L) :
    (C • W).xVeluT (vcXInv C x) = ((C.u⁻¹ : Lˣ) : L) ^ 4 * W.xVeluT x := by
  simp only [xVeluT, vcXInv, variableChange_b₂, variableChange_b₄]
  ring

omit [DecidableEq L] in
private theorem xVeluU_vc (W : WeierstrassCurve L) (x : L) :
    (C • W).xVeluU (vcXInv C x) = ((C.u⁻¹ : Lˣ) : L) ^ 6 * W.xVeluU x := by
  simp only [xVeluU, vcXInv, variableChange_b₂, variableChange_b₄, variableChange_b₆]
  ring

omit [DecidableEq L] in
private theorem xVeluW_vc (W : WeierstrassCurve L) (x : L) :
    (C • W).xVeluW (vcXInv C x) = ((C.u⁻¹ : Lˣ) : L) ^ 6 * (W.xVeluW x - C.r * W.xVeluT x) := by
  rw [xVeluW, xVeluW, xVeluU_vc, xVeluT_vc, vcXInv]
  ring

omit [DecidableEq L] in
private theorem xVeluG_eq (W : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) (x : L) : W.xVeluG x = W.xVeluT x / 2 := by
  rw [xVeluG, twoTorsionY, veluGx, xVeluT, b₂, b₄]
  field_simp
  ring

omit [DecidableEq L] in
private theorem xVeluG_vc (W : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) (x : L) :
    (C • W).xVeluG (vcXInv C x) = ((C.u⁻¹ : Lˣ) : L) ^ 4 * W.xVeluG x := by
  rw [xVeluG_eq (C • W) h2, xVeluG_eq W h2, xVeluT_vc, mul_div_assoc]

omit [DecidableEq L] in
private theorem absSum_image_vc (X : Set L) (g : L → L) :
    absSum (vcXInv C '' X) g = absSum X (fun x => g (vcXInv C x)) := by
  have hinj : Set.InjOn (vcXInv C) X := fun a _ b _ h => by
    simpa only [vcX_vcXInv] using congrArg (vcX C) h
  by_cases hX : X.Finite
  · rw [absSum, if_pos (hX.image _), absSum, if_pos hX, finsum_mem_image hinj]
  · have hX' : ¬ (vcXInv C '' X).Finite := fun h => hX (Set.Finite.of_finite_image h hinj)
    rw [absSum, if_neg hX', absSum, if_neg hX]

omit [DecidableEq L] in
private theorem absSum_mul (X : Set L) (c : L) (g : L → L) :
    absSum X (fun x => c * g x) = c * absSum X g := by
  by_cases hX : X.Finite
  · rw [absSum_of_finite hX, absSum_of_finite hX, Finset.mul_sum]
  · rw [absSum_of_infinite hX, absSum_of_infinite hX, mul_zero]

omit [DecidableEq L] in
private theorem absSum_sub (X : Set L) (g h : L → L) :
    absSum X (fun x => g x - h x) = absSum X g - absSum X h := by
  by_cases hX : X.Finite
  · rw [absSum_of_finite hX, absSum_of_finite hX, absSum_of_finite hX, Finset.sum_sub_distrib]
  · rw [absSum_of_infinite hX, absSum_of_infinite hX, absSum_of_infinite hX, sub_zero]

omit [DecidableEq L] in
private theorem absSum_congr (X : Set L) {g h : L → L} (hgh : ∀ x, g x = h x) : absSum X g = absSum X h := by
  rw [show g = h from funext hgh]

omit [DecidableEq L] in
private theorem xVeluCurve_vc (W : WeierstrassCurve L) (X : Set L) :
    (C • W).xVeluCurve (vcXInv C '' X) = C • (W.xVeluCurve X) := by
  have hT : absSum (vcXInv C '' X) (C • W).xVeluT = ((C.u⁻¹ : Lˣ) : L) ^ 4 * absSum X W.xVeluT := by
    rw [absSum_image_vc, absSum_congr X (xVeluT_vc C W), absSum_mul]
  have hW : absSum (vcXInv C '' X) (C • W).xVeluW =
      ((C.u⁻¹ : Lˣ) : L) ^ 6 * (absSum X W.xVeluW - C.r * absSum X W.xVeluT) := by
    rw [absSum_image_vc, absSum_congr X (xVeluW_vc C W), absSum_mul, absSum_sub, absSum_mul]
  ext
  · rfl
  · rfl
  · rfl
  · rw [xVeluCurve_a₄, hT, variableChange_a₄, variableChange_a₄]
    simp only [xVeluCurve_a₁, xVeluCurve_a₂, xVeluCurve_a₃, xVeluCurve_a₄]
    ring
  · rw [xVeluCurve_a₆, hT, hW, variableChange_a₆, variableChange_a₆, variableChange_b₂]
    simp only [xVeluCurve_a₁, xVeluCurve_a₂, xVeluCurve_a₃, xVeluCurve_a₄, xVeluCurve_a₆]
    ring

omit [DecidableEq L] in
private theorem twoVeluCurve_vc (W : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) (X : Set L) :
    (C • W).twoVeluCurve (vcXInv C '' X) = C • (W.twoVeluCurve X) := by
  have hG : absSum (vcXInv C '' X) (C • W).xVeluG = ((C.u⁻¹ : Lˣ) : L) ^ 4 * absSum X W.xVeluG := by
    rw [absSum_image_vc, absSum_congr X (xVeluG_vc C W h2), absSum_mul]
  have hXG : absSum (vcXInv C '' X) (fun x => x * (C • W).xVeluG x) =
      ((C.u⁻¹ : Lˣ) : L) ^ 6 * (absSum X (fun x => x * W.xVeluG x) - C.r * absSum X W.xVeluG) := by
    rw [absSum_image_vc, ← absSum_mul X C.r, ← absSum_sub, ← absSum_mul]
    refine absSum_congr X fun x => ?_
    rw [xVeluG_vc C W h2, vcXInv]
    ring
  ext
  · rfl
  · rfl
  · rfl
  · rw [twoVeluCurve_a₄, hG, variableChange_a₄, variableChange_a₄]
    simp only [twoVeluCurve_a₁, twoVeluCurve_a₂, twoVeluCurve_a₃, twoVeluCurve_a₄]
    ring
  · rw [twoVeluCurve_a₆, hG, hXG, variableChange_a₆, variableChange_a₆, variableChange_b₂]
    simp only [twoVeluCurve_a₁, twoVeluCurve_a₂, twoVeluCurve_a₃, twoVeluCurve_a₄, twoVeluCurve_a₆]
    ring

omit [DecidableEq L] in
private theorem xVeluX_vc (W : WeierstrassCurve L) (X : Set L) (x : L) :
    (C • W).xVeluX (vcXInv C '' X) (vcXInv C x) = vcXInv C (W.xVeluX X x) := by
  rw [xVeluX, xVeluX, absSum_image_vc]
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have key : ∀ x₀, (C • W).xVeluT (vcXInv C x₀) / (vcXInv C x - vcXInv C x₀) +
      (C • W).xVeluU (vcXInv C x₀) / (vcXInv C x - vcXInv C x₀) ^ 2 =
      ((C.u⁻¹ : Lˣ) : L) ^ 2 * (W.xVeluT x₀ / (x - x₀) + W.xVeluU x₀ / (x - x₀) ^ 2) := by
    intro x₀
    rw [xVeluT_vc, xVeluU_vc]
    have hd : vcXInv C x - vcXInv C x₀ = ((C.u⁻¹ : Lˣ) : L) ^ 2 * (x - x₀) := by
      simp only [vcXInv]; ring
    rw [hd]
    rcases eq_or_ne x x₀ with rfl | hne
    · simp
    · have hx : x - x₀ ≠ 0 := sub_ne_zero.2 hne
      simp only [Units.val_inv_eq_inv_val]
      field_simp
  rw [absSum_congr X key, absSum_mul]
  simp only [vcXInv]
  ring

omit [DecidableEq L] in
private theorem twoVeluX_vc (W : WeierstrassCurve L) (h2 : (2 : L) ≠ 0) (X : Set L) (x : L) :
    (C • W).twoVeluX (vcXInv C '' X) (vcXInv C x) = vcXInv C (W.twoVeluX X x) := by
  rw [twoVeluX, twoVeluX, absSum_image_vc]
  have hu : (C.u : L) ≠ 0 := C.u.ne_zero
  have key : ∀ x₀, (C • W).xVeluG (vcXInv C x₀) / (vcXInv C x - vcXInv C x₀) =
      ((C.u⁻¹ : Lˣ) : L) ^ 2 * (W.xVeluG x₀ / (x - x₀)) := by
    intro x₀
    rw [xVeluG_vc C W h2]
    have hd : vcXInv C x - vcXInv C x₀ = ((C.u⁻¹ : Lˣ) : L) ^ 2 * (x - x₀) := by
      simp only [vcXInv]; ring
    rw [hd]
    rcases eq_or_ne x x₀ with rfl | hne
    · simp
    · have hx : x - x₀ ≠ 0 := sub_ne_zero.2 hne
      simp only [Units.val_inv_eq_inv_val]
      field_simp
  rw [absSum_congr X key, absSum_mul]
  simp only [vcXInv]
  ring

private theorem stepCurve_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (ℓ : ℕ)
    (h2 : ℓ = 2 → (2 : L) ≠ 0) :
    (C • W).stepCurve (H.map (vcInvHom C W)) ℓ = C • (W.stepCurve H ℓ) := by
  by_cases hℓ : ℓ = 2
  · subst hℓ
    rw [stepCurve_two, stepCurve_two, kernelXSet_vc, twoVeluCurve_vc C W (h2 rfl)]
  · rw [stepCurve_of_ne_two _ _ hℓ, stepCurve_of_ne_two _ _ hℓ, kernelXSet_vc, xVeluCurve_vc]

private theorem stepX_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (ℓ : ℕ)
    (h2 : ℓ = 2 → (2 : L) ≠ 0) (x : L) :
    (C • W).stepX (H.map (vcInvHom C W)) ℓ (vcXInv C x) = vcXInv C (W.stepX H ℓ x) := by
  by_cases hℓ : ℓ = 2
  · subst hℓ
    rw [stepX_two, stepX_two, kernelXSet_vc, twoVeluX_vc C W (h2 rfl)]
  · rw [stepX_of_ne_two _ _ hℓ, stepX_of_ne_two _ _ hℓ, kernelXSet_vc, xVeluX_vc]

private theorem subgroupOfX_vc (V : WeierstrassCurve L) (Y : Set L) :
    subgroupOfX (C • V) (vcXInv C '' Y) = (subgroupOfX V Y).map (vcInvHom C V) := by
  rw [subgroupOfX, subgroupOfX, AddMonoidHom.map_closure]
  congr 1
  ext P'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hne, ⟨y, hyY, hy⟩⟩
    have hne' : Point.vcFun C V P' ≠ 0 := by
      intro h
      apply hne
      rw [← vcInvHom_vcFun C V P', h, map_zero]
    refine ⟨Point.vcFun C V P', ⟨hne', ?_⟩, vcInvHom_vcFun C V P'⟩
    have := fst_coordsOrZero_vcInvHom C V hne'
    rw [vcInvHom_vcFun] at this
    have h' : vcX C P'.coordsOrZero.1 = (Point.vcFun C V P').coordsOrZero.1 := by
      rw [this, vcX_vcXInv]
    rw [← h', ← hy, vcX_vcXInv]
    exact hyY
  · rintro ⟨P, ⟨hne, hY⟩, rfl⟩
    exact ⟨(vcInvHom_ne_zero C V).2 hne, ⟨_, hY, (fst_coordsOrZero_vcInvHom C V hne).symm⟩⟩

private noncomputable def vcState (s : CQJState L) : CQJState L :=
  ⟨⟨C • s.1.1, s.1.2.map (vcInvHom C s.1.1)⟩, s.2⟩

private theorem sigma_eq_of_eq {V₁ V₂ : WeierstrassCurve L} (h : V₁ = V₂) {Y₁ Y₂ : Set L} (hY : Y₁ = Y₂) :
    (⟨V₁, subgroupOfX V₁ Y₁⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨V₂, subgroupOfX V₂ Y₂⟩ := by
  subst h hY; rfl

private theorem cqjStep_vcState (s : CQJState L) (h2 : s.2.minFac = 2 → (2 : L) ≠ 0) :
    cqjStep (vcState C s) = vcState C (cqjStep s) := by
  obtain ⟨⟨V, H⟩, n⟩ := s
  change (⟨⟨(C • V).stepCurve (H.map (vcInvHom C V)) n.minFac,
      (C • V).stepSubgroup (H.map (vcInvHom C V)) n.minFac⟩, n / n.minFac⟩ : CQJState L) =
    ⟨⟨C • (V.stepCurve H n.minFac), (V.stepSubgroup H n.minFac).map (vcInvHom C _)⟩, n / n.minFac⟩
  congr 1
  rw [stepSubgroup, stepSubgroup, ← subgroupOfX_vc]
  refine sigma_eq_of_eq (stepCurve_vc C V H _ h2) ?_
  rw [coKernelXSet_vc, Set.image_image, Set.image_image]
  exact Set.image_congr fun x _ => stepX_vc C V H _ h2 x

private theorem cqjStep_snd_dvd (s : CQJState L) : (cqjStep s).2 ∣ s.2 :=
  Nat.div_dvd_of_dvd (Nat.minFac_dvd _)

private theorem iterate_cqjStep_vcState {N : ℕ} (hN2 : 2 ∣ N → (2 : L) ≠ 0) (k : ℕ) (s : CQJState L)
    (hs : s.2 ∣ N) : cqjStep^[k] (vcState C s) = vcState C (cqjStep^[k] s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, cqjStep_vcState C s, ih]
    · exact (cqjStep_snd_dvd s).trans hs
    · intro h
      exact hN2 ((h ▸ Nat.minFac_dvd s.2).trans hs)

private theorem cyclicQuotientJ_vc (W : WeierstrassCurve L) (H : AddSubgroup W.toAffine.Point) (N : ℕ)
    (hN2 : 2 ∣ N → (2 : L) ≠ 0) :
    (C • W).cyclicQuotientJ (H.map (vcInvHom C W)) N = W.cyclicQuotientJ H N := by
  have h := iterate_cqjStep_vcState C hN2 N.primeFactorsList.length ⟨⟨W, H⟩, N⟩ dvd_rfl
  have hc : (C • W).cyclicQuotientCurve (H.map (vcInvHom C W)) N = C • (W.cyclicQuotientCurve H N) := by
    rw [cyclicQuotientCurve_def, cyclicQuotientCurve_def, cqjIterate_def, cqjIterate_def]
    exact congrArg (fun s : CQJState L => s.1.1) h
  rw [cyclicQuotientJ_def, cyclicQuotientJ_def, hc, variableChange_c₄, variableChange_Δ]
  have hu : ((C.u⁻¹ : Lˣ) : L) ≠ 0 := (C.u⁻¹).ne_zero
  rw [mul_pow, ← pow_mul, show 4 * 3 = 12 by norm_num, mul_div_mul_left _ _ (pow_ne_zero 12 hu)]

end P2MKcCQJvc


/-! ### `S_WeierstrassCurve_cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed.lean` — base change

The pin's own namespace `P2MKcCQJbc`, again entirely `private`: `ptMap` is the plain
ring hom's point map with the `letI : Algebra A B := f.toAlgebra` instance that
`WeierstrassCurve.Affine.Point.map` expects, and `subgroupOfX_map` is the
`IsAlgClosed A` root-lifting step. -/

namespace P2MKcCQJbc

variable {A B : Type*} [Field A] [Field B] [DecidableEq A] [DecidableEq B] (f : A →+* B)

private noncomputable def ptMap (V : WeierstrassCurve A) : V.toAffine.Point →+ (V.map f).toAffine.Point :=
  letI : Algebra A B := f.toAlgebra
  (WeierstrassCurve.Affine.Point.map (W' := V.toAffine) (Algebra.ofId A B) :
    (V.toAffine⁄A).Point →+ (V.toAffine⁄B).Point)

private theorem ptMap_zero (V : WeierstrassCurve A) : ptMap f V 0 = 0 := rfl

private theorem ptMap_some (V : WeierstrassCurve A) {x y : A} (h : V.toAffine.Nonsingular x y) :
    ptMap f V (.some x y h) = .some (f x) (f y) ((Affine.map_nonsingular V.toAffine f.injective x y).2 h) := rfl

private theorem ptMap_injective (V : WeierstrassCurve A) : Function.Injective (ptMap f V) := by
  letI : Algebra A B := f.toAlgebra
  exact WeierstrassCurve.Affine.Point.map_injective (W' := V.toAffine) (Algebra.ofId A B)

private theorem coordsOrZero_ptMap (V : WeierstrassCurve A) (P : V.toAffine.Point) :
    (ptMap f V P).coordsOrZero = Prod.map f f P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · change (ptMap f V 0).coordsOrZero = Prod.map f f (0, 0)
    rw [ptMap_zero]
    change ((0, 0) : B × B) = (f 0, f 0)
    rw [map_zero]
  · rfl

private theorem ptMap_ne_zero (V : WeierstrassCurve A) {P : V.toAffine.Point} :
    ptMap f V P ≠ 0 ↔ P ≠ 0 := by
  rw [Ne, Ne, ← ptMap_zero f V, (ptMap_injective f V).eq_iff]

private theorem kernelXSet_map (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    (V.map f).kernelXSet (H.map (ptMap f V)) ℓ = f '' V.kernelXSet H ℓ := by
  ext x'
  simp only [kernelXSet, Set.mem_image, Set.mem_setOf_eq, AddSubgroup.mem_map]
  constructor
  · rintro ⟨P', ⟨⟨P, hP, rfl⟩, hne, hsm⟩, rfl⟩
    refine ⟨P.coordsOrZero.1, ⟨P, ⟨hP, (ptMap_ne_zero f V).1 hne, ?_⟩, rfl⟩, ?_⟩
    · apply ptMap_injective f V
      rw [map_nsmul, hsm, map_zero]
    · rw [coordsOrZero_ptMap]; rfl
  · rintro ⟨x, ⟨P, ⟨hP, hne, hsm⟩, rfl⟩, rfl⟩
    refine ⟨ptMap f V P, ⟨⟨P, hP, rfl⟩, (ptMap_ne_zero f V).2 hne, ?_⟩, ?_⟩
    · rw [← map_nsmul, hsm, map_zero]
    · rw [coordsOrZero_ptMap]; rfl

private theorem coKernelXSet_map (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    (V.map f).coKernelXSet (H.map (ptMap f V)) ℓ = f '' V.coKernelXSet H ℓ := by
  ext x'
  simp only [coKernelXSet, Set.mem_image, Set.mem_setOf_eq, AddSubgroup.mem_map]
  constructor
  · rintro ⟨P', ⟨⟨P, hP, rfl⟩, hsm⟩, rfl⟩
    refine ⟨P.coordsOrZero.1, ⟨P, ⟨hP, fun h => hsm ?_⟩, rfl⟩, ?_⟩
    · rw [← map_nsmul, h, map_zero]
    · rw [coordsOrZero_ptMap]; rfl
  · rintro ⟨x, ⟨P, ⟨hP, hsm⟩, rfl⟩, rfl⟩
    refine ⟨ptMap f V P, ⟨⟨P, hP, rfl⟩, fun h => hsm ?_⟩, ?_⟩
    · apply ptMap_injective f V
      rw [map_nsmul, h, map_zero]
    · rw [coordsOrZero_ptMap]; rfl

omit [DecidableEq A] [DecidableEq B] in
private theorem xVeluT_map (V : WeierstrassCurve A) (x : A) : (V.map f).xVeluT (f x) = f (V.xVeluT x) := by
  simp only [xVeluT, map_b₂, map_b₄, map_add, map_mul, map_pow, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
private theorem xVeluU_map (V : WeierstrassCurve A) (x : A) : (V.map f).xVeluU (f x) = f (V.xVeluU x) := by
  simp only [xVeluU, map_b₂, map_b₄, map_b₆, map_add, map_mul, map_pow, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
private theorem xVeluW_map (V : WeierstrassCurve A) (x : A) : (V.map f).xVeluW (f x) = f (V.xVeluW x) := by
  simp [xVeluW, xVeluT_map, xVeluU_map]

omit [DecidableEq A] [DecidableEq B] in
private theorem twoTorsionY_map (V : WeierstrassCurve A) (x : A) :
    (V.map f).twoTorsionY (f x) = f (V.twoTorsionY x) := by
  simp only [twoTorsionY, map_a₁, map_a₃, map_div₀, map_neg, map_add, map_mul, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
private theorem xVeluG_map (V : WeierstrassCurve A) (x : A) : (V.map f).xVeluG (f x) = f (V.xVeluG x) := by
  rw [xVeluG, xVeluG, twoTorsionY_map, map_veluGx]

omit [DecidableEq A] [DecidableEq B] in
private theorem absSum_image_eq {TA : A → A} {TB : B → B} (hT : ∀ x, TB (f x) = f (TA x)) (X : Set A) :
    absSum (f '' X) TB = f (absSum X TA) := by
  by_cases hX : X.Finite
  · have hX' : (f '' X).Finite := hX.image f
    rw [absSum, if_pos hX', absSum, if_pos hX, finsum_mem_image f.injective.injOn]
    simp_rw [hT]
    exact ((f : A →+ B).map_finsum_mem' (hX.inter_of_left _)).symm
  · have hX' : ¬ (f '' X).Finite := fun h => hX (Set.Finite.of_finite_image h f.injective.injOn)
    rw [absSum, if_neg hX', absSum, if_neg hX, map_zero]

omit [DecidableEq A] [DecidableEq B] in
private theorem xVeluCurve_map (V : WeierstrassCurve A) (X : Set A) :
    (V.map f).xVeluCurve (f '' X) = (V.xVeluCurve X).map f := by
  have hT := absSum_image_eq f (xVeluT_map f V) X
  have hW := absSum_image_eq f (xVeluW_map f V) X
  ext
  · rfl
  · rfl
  · rfl
  · simp only [xVeluCurve_a₄, map_a₄, hT, map_sub, map_mul, map_ofNat]
  · simp only [xVeluCurve_a₆, map_a₆, map_b₂, hT, hW, map_sub, map_mul, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
private theorem twoVeluCurve_map (V : WeierstrassCurve A) (X : Set A) :
    (V.map f).twoVeluCurve (f '' X) = (V.twoVeluCurve X).map f := by
  have hG := absSum_image_eq f (xVeluG_map f V) X
  have hXG := absSum_image_eq f (TA := fun x => x * V.xVeluG x)
    (TB := fun y => y * (V.map f).xVeluG y) (fun x => by simp only [xVeluG_map, map_mul]) X
  ext
  · rfl
  · rfl
  · rfl
  · simp only [twoVeluCurve_a₄, map_a₄, hG, map_sub, map_mul, map_ofNat]
  · simp only [twoVeluCurve_a₆, map_a₆, map_b₂, hG, hXG, map_sub, map_mul, map_ofNat]

omit [DecidableEq A] [DecidableEq B] in
private theorem xVeluX_map (V : WeierstrassCurve A) (X : Set A) (x : A) :
    (V.map f).xVeluX (f '' X) (f x) = f (V.xVeluX X x) := by
  rw [xVeluX, xVeluX, map_add, absSum_image_eq f
    (TA := fun x₀ => V.xVeluT x₀ / (x - x₀) + V.xVeluU x₀ / (x - x₀) ^ 2)
    (TB := fun y₀ => (V.map f).xVeluT y₀ / (f x - y₀) + (V.map f).xVeluU y₀ / (f x - y₀) ^ 2)]
  intro x₀
  simp only [xVeluT_map, xVeluU_map, map_add, map_div₀, map_sub, map_pow]

omit [DecidableEq A] [DecidableEq B] in
private theorem twoVeluX_map (V : WeierstrassCurve A) (X : Set A) (x : A) :
    (V.map f).twoVeluX (f '' X) (f x) = f (V.twoVeluX X x) := by
  rw [twoVeluX, twoVeluX, map_add, absSum_image_eq f
    (TA := fun x₀ => V.xVeluG x₀ / (x - x₀)) (TB := fun y₀ => (V.map f).xVeluG y₀ / (f x - y₀))]
  intro x₀
  simp only [xVeluG_map, map_div₀, map_sub]

private theorem stepCurve_map (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) :
    (V.map f).stepCurve (H.map (ptMap f V)) ℓ = (V.stepCurve H ℓ).map f := by
  by_cases hℓ : ℓ = 2
  · subst hℓ
    rw [stepCurve_two, stepCurve_two, kernelXSet_map, twoVeluCurve_map]
  · rw [stepCurve_of_ne_two _ _ hℓ, stepCurve_of_ne_two _ _ hℓ, kernelXSet_map, xVeluCurve_map]

private theorem stepX_map (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point) (ℓ : ℕ) (x : A) :
    (V.map f).stepX (H.map (ptMap f V)) ℓ (f x) = f (V.stepX H ℓ x) := by
  by_cases hℓ : ℓ = 2
  · subst hℓ
    rw [stepX_two, stepX_two, kernelXSet_map, twoVeluX_map]
  · rw [stepX_of_ne_two _ _ hℓ, stepX_of_ne_two _ _ hℓ, kernelXSet_map, xVeluX_map]

private theorem subgroupOfX_map [IsAlgClosed A] (V : WeierstrassCurve A) (Y : Set A) :
    subgroupOfX (V.map f) (f '' Y) = (subgroupOfX V Y).map (ptMap f V) := by
  rw [subgroupOfX, subgroupOfX, AddMonoidHom.map_closure]
  congr 1
  ext P'
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hne, ⟨x, hxY, hx⟩⟩
    rcases P' with _ | ⟨x', y', h'⟩
    · exact absurd rfl hne
    · simp only [Affine.Point.coordsOrZero] at hx
      subst hx

      have heq : (V.map f).toAffine.Equation (f x) y' := h'.1
      set q : Polynomial A := Polynomial.X ^ 2 + Polynomial.C (V.a₁ * x + V.a₃) * Polynomial.X -
        Polynomial.C (x ^ 3 + V.a₂ * x ^ 2 + V.a₄ * x + V.a₆) with hq
      have hqm : q.Monic := by
        rw [hq]
        refine (Polynomial.monic_X_pow 2).add_of_left ?_ |>.sub_of_left ?_
        · exact (Polynomial.degree_C_mul_X_le _).trans_lt (by
            rw [Polynomial.degree_X_pow]; exact WithBot.coe_lt_coe.2 (by norm_num))
        · refine (Polynomial.degree_C_le).trans_lt ?_
          rw [Polynomial.degree_add_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]
          · exact WithBot.coe_lt_coe.2 (by norm_num)
          · exact (Polynomial.degree_C_mul_X_le _).trans_lt (WithBot.coe_lt_coe.2 (by norm_num))
      have hsplit : (q.map f).Splits := (IsAlgClosed.splits q).map f
      have hroot : (q.map f).IsRoot y' := by
        rw [Affine.equation_iff] at heq
        simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
        rw [Polynomial.IsRoot.def, Polynomial.eval_map, hq]
        simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
          Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_add, map_mul, map_pow]
        linear_combination heq
      have hy' : y' ∈ (q.map f).roots := (Polynomial.mem_roots (Polynomial.map_ne_zero hqm.ne_zero)).2 hroot
      rw [(IsAlgClosed.splits q).roots_map f, Multiset.mem_map] at hy'
      obtain ⟨y, -, rfl⟩ := hy'
      have h : V.toAffine.Nonsingular x y := (Affine.map_nonsingular V.toAffine f.injective x y).1 h'
      exact ⟨.some x y h, ⟨Affine.Point.some_ne_zero h, hxY⟩, ptMap_some f V h⟩
  · rintro ⟨P, ⟨hne, hY⟩, rfl⟩
    refine ⟨(ptMap_ne_zero f V).2 hne, ⟨P.coordsOrZero.1, hY, ?_⟩⟩
    rw [coordsOrZero_ptMap]; rfl

private noncomputable def stMap (s : CQJState A) : CQJState B :=
  ⟨⟨s.1.1.map f, s.1.2.map (ptMap f s.1.1)⟩, s.2⟩

private theorem sigma_eq_of_eq {V₁ V₂ : WeierstrassCurve B} (h : V₁ = V₂) {Y₁ Y₂ : Set B} (hY : Y₁ = Y₂) :
    (⟨V₁, subgroupOfX V₁ Y₁⟩ : Σ V : WeierstrassCurve B, AddSubgroup V.toAffine.Point) =
      ⟨V₂, subgroupOfX V₂ Y₂⟩ := by
  subst h hY; rfl

private theorem cqjStep_stMap [IsAlgClosed A] (s : CQJState A) : cqjStep (stMap f s) = stMap f (cqjStep s) := by
  obtain ⟨⟨V, H⟩, n⟩ := s
  change (⟨⟨(V.map f).stepCurve (H.map (ptMap f V)) n.minFac,
      (V.map f).stepSubgroup (H.map (ptMap f V)) n.minFac⟩, n / n.minFac⟩ : CQJState B) =
    ⟨⟨(V.stepCurve H n.minFac).map f, (V.stepSubgroup H n.minFac).map (ptMap f _)⟩, n / n.minFac⟩
  congr 1
  rw [stepSubgroup, stepSubgroup, ← subgroupOfX_map]
  refine sigma_eq_of_eq (stepCurve_map f V H _) ?_
  rw [coKernelXSet_map, Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  exact stepX_map f V H _ x

private theorem iterate_cqjStep_stMap [IsAlgClosed A] (n : ℕ) (s : CQJState A) :
    cqjStep^[n] (stMap f s) = stMap f (cqjStep^[n] s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, cqjStep_stMap, ih]

private theorem cyclicQuotientJ_map [IsAlgClosed A] (V : WeierstrassCurve A) (H : AddSubgroup V.toAffine.Point)
    (N : ℕ) : (V.map f).cyclicQuotientJ (H.map (ptMap f V)) N = f (V.cyclicQuotientJ H N) := by
  have h := iterate_cqjStep_stMap f N.primeFactorsList.length ⟨⟨V, H⟩, N⟩
  have hc : (V.map f).cyclicQuotientCurve (H.map (ptMap f V)) N = (V.cyclicQuotientCurve H N).map f := by
    rw [cyclicQuotientCurve_def, cyclicQuotientCurve_def, cqjIterate_def, cqjIterate_def]
    exact congrArg (fun s : CQJState B => s.1.1) h
  rw [cyclicQuotientJ_def, cyclicQuotientJ_def, hc, map_c₄, map_Δ, map_div₀, map_pow]

private theorem cyclicQuotientJ_map' [IsAlgClosed A] (V : WeierstrassCurve A) (VB : WeierstrassCurve B)
    (hVB : V.map f = VB) (φ : V.toAffine.Point →+ VB.toAffine.Point)
    (hφ : ∀ (x y : A) (h : V.toAffine.Nonsingular x y), ∃ h', φ (.some x y h) = .some (f x) (f y) h')
    (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    VB.cyclicQuotientJ (H.map φ) N = f (V.cyclicQuotientJ H N) := by
  subst hVB
  have hφ' : φ = ptMap f V := by
    ext P
    rcases P with _ | ⟨x, y, h⟩
    · exact (map_zero φ).trans (map_zero _).symm
    · obtain ⟨h', e⟩ := hφ x y h
      rw [e, ptMap_some]
  rw [hφ']
  exact cyclicQuotientJ_map f V H N

end P2MKcCQJbc


/-! ### The two headline nodes

`cyclicQuotientJ_variableChange_eq`: invariance under a variable change, given the
transport hypothesis `∀ P, P ∈ H' ↔ vcFun C E P ∈ H`.
`cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed`: commutation with base change
along `f : A →ₐ[R] B` over an algebraically closed `A`. -/

open P2MKcCQJvc P2MKcCQJbc

namespace WeierstrassCurve

universe u v w

theorem cyclicQuotientJ_variableChange_eq
    {L : Type u} [Field L] [DecidableEq L] (C : VariableChange L) (E : WeierstrassCurve L)
    (H : AddSubgroup E.toAffine.Point) (H' : AddSubgroup (C • E).toAffine.Point)
    (hH' : ∀ P, P ∈ H' ↔ WeierstrassCurve.Affine.Point.vcFun C E P ∈ H)
    (N : ℕ) (hN : (N : L) ≠ 0) :
    (C • E).cyclicQuotientJ H' N = E.cyclicQuotientJ H N := by
  have hH'eq : H' = H.map (vcInvHom C E) := by
    ext P
    rw [hH', AddSubgroup.mem_map]
    constructor
    · intro h
      exact ⟨_, h, vcInvHom_vcFun C E P⟩
    · rintro ⟨Q, hQ, rfl⟩
      rwa [vcFun_vcInvHom]
  rw [hH'eq]
  refine cyclicQuotientJ_vc C E H N fun h2 h => hN ?_
  obtain ⟨m, rfl⟩ := h2
  rw [Nat.cast_mul, Nat.cast_ofNat, h, zero_mul]

theorem cyclicQuotientJ_baseChange_map_eq_of_isAlgClosed
    {R : Type u} [CommRing R] (E : WeierstrassCurve R)
    {A : Type v} {B : Type w} [Field A] [DecidableEq A] [IsAlgClosed A] [Field B] [DecidableEq B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B)
    (H : AddSubgroup (E.baseChange A).toAffine.Point) (N : ℕ) :
    (E.baseChange B).cyclicQuotientJ (H.map (WeierstrassCurve.Affine.Point.map f)) N =
      f ((E.baseChange A).cyclicQuotientJ H N) := by
  refine cyclicQuotientJ_map' (f : A →+* B) (E.baseChange A) (E.baseChange B) ?_ _ ?_ H N
  · exact E.map_baseChange f
  · intro x y h
    exact ⟨_, WeierstrassCurve.Affine.Point.map_some f h⟩

end WeierstrassCurve
