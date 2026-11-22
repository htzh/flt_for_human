/-
The torsion basis at the two exceptional `j`-invariants: an order-three (resp. order-four)
automorphism of a `j = 0` (resp. `j = 1728`) curve acts regularly on an `M`-torsion basis.

The two headlines say: over an algebraically closed field and for `M` a natural number whose
image in the field is nonzero, there is a curve `E₀` with `j(E₀) = 0` (resp. `1728`), an admissible
variable change `σ` fixing it, and an `M`-torsion basis `(P, Q)` of `E₀` on which `σ` acts through
`Point.vcInvFun` as the matrix `[[0,1],[-1,-1]]` (resp. `σ P = Q`, `σ Q = -P`).  That is the
"regular module" input for the fibre of the modular curve above `j = 0` and `j = 1728`.

Both pins are three-case splits — `2 = 0`, `3 = 0`, generic — each case re-deriving its own curve
model (`E₀`, `E2`, `E3`) and calling the already-ported exceptional automorphism engines
(`Automorphism/{CharTwo,CharThree}.lean`, `Automorphism/DeuringForm.lean`).  The point-transport
prelude (`xy`, `xy_injective`, `xy_vcInvFun`, `castPt`, `heq_castPt`, `xy_castPt`, `vcHom`,
`vcHom_apply`, `heq_vcHom`, `xy_vcHom`, `heq_of_xy_eq`) is public in `Automorphism/Basic.lean` and
is imported, never redeclared; the pair also shares `exists_common_scalar` and
`eq_or_eq_neg_of_xco_eq`, written once.

## What landed (order AF102A1, rows 816 + 713)

63 public declarations, at the pins' names, silent, no `sorry`: `check_port` **63 ok / 0 mismatch /
0 missing / 0 own**.  The whole engine of both `S_` files, less what the port already had.  The
declaration accounting against the two pins (93 rows = 49 + 44):

| bucket | 816 | 713 |
|---|---:|---:|
| rows matched to a declaration here (statement hash) | 37 | 31 |
| rows matched up to binder spelling (`E2`, `K` vs `L`) | — | 1 |
| rows matched to the same proposition with the type variable spelled `L` | — | 1 (`E2_c₄`) |
| rows imported from `Automorphism/Basic.lean` | 10 | 10 |
| rows carried by the headline (`main` and `solution`; see below) | 2 | 1 |
| unaccounted | 0 | 0 |

Seven declarations serve a row in **both** pins by hash: `xco`, `xco_zero`, `xco_some`, `xco_neg`,
`eq_or_eq_neg_of_xco_eq`, `exists_common_scalar`, `baseChange_self`.  The eleven point-transport
rows of the pins' prelude are `Automorphism/Basic.lean`'s (imported): `xy`, `xy_injective`,
`xy_vcInvFun`, `castPt`, `heq_castPt`, `xy_castPt`, `vcHom`, `vcHom_apply`, `heq_vcHom`,
`xy_vcHom` — ten; the eleventh, `heq_of_xy_eq`, is `Basic.lean`'s own addition and is not needed by
either pin (the two headlines use `heq_vcHom` and `heq_of_eq`).

**`main` and `solution` are carried by the headlines, not declared.**  Both pins' `main` / `solution`
rows have the statement of their `Theorems/` wrapper (`28ca7b0d…`, `1a53ad69…`), which the headline
*is*: a second declaration would be a third copy of one statement.  It is also forced for 816's
`main`: `WeierstrassCurve.Automorphism.main` is already public in `Automorphism/StabilizerOrder.lean`
(FR-0274 — two modules must not declare the same public full name, and no gate reports it).  The
order-three headline therefore *is* the case split (`case_two` / `case_three` / `case_generic`), and
the order-four one is `main_of_charTwo` / `main_of_two_ne_zero`.

**The `OrderFour` namespace.**  Four last names occur in *both* pins with **different** statements:
`smul_E2` (816: `⟨w,0,0,0⟩` on `E2`; 713: `⟨1,1,1,w⟩` on `E2`), `exists_addOrderOf_eq_and_ne_nsmul`
(the `EB B = ⟨0,0,0,0,B⟩` order-three version resp. the `EA A = ⟨0,0,0,A,0⟩` order-two version),
`main` and `solution` (dropped, above).  `E2_Δ` and `isElliptic_E2` differ in their written binder
(`[CharP K 2]` in the 713 file, supplied by the section in the 816 file), so the checker's textual
diff cannot see one declaration behind both rows either.  The 713 spelling of each is declared in
`WeierstrassCurve.Automorphism.OrderFour` — a subject namespace, not the pins' label namespace — and
every other declaration keeps its pin name in `WeierstrassCurve.Automorphism`.  Nothing else is
renamed; both models (`EA`, `EB`) stay at the outer level, so the two rows read as
`E2_Δ` / `OrderFour.E2_Δ`.

Two proof bodies are **not** the pins' text: `exists_cube_root` and `exists_sq_eq_neg_one` avoid
`HasEnoughRootsOfUnity.exists_primitiveRoot`'s `NeZero ((n : K))` instance (an `haveI` on a `Prop`,
which the `linter.style.haveILetI` of mathlib `v4.34.0` flags; the pins' mathlib predates it) and
instead build the root from `IsAlgClosed.exists_root` / `IsAlgClosed.exists_pow_nat_eq`.  Every other
body is the pin's, with `haveI` → `have` (an instance in a tactic proof needs no inlining).

`set_option linter.unusedSectionVars false` and `linter.unusedVariables false` are transcribed (both
pins carry them); the pin's `set_option maxHeartbeats 6400000` is **not** — see the probe below.

## Gates (measured, order AF102A1)

* `check_port`: **63 ok, 0 mismatch, 0 missing, 0 own, 0 kw**.
* Silent at the edit loop (`lake env lean -DautoImplicit=false`), no `sorry`; one locked
  `lake build FLTForHuman.WeierstrassCurve.Automorphism.TorsionBasis` — completed (33 s, 3295 jobs).
* `#print axioms` on all 63 public declarations: 39 read `[propext, Classical.choice, Quot.sound]`
  and 24 the pair `[propext, Quot.sound]` — **no `sorryAx`** in any of them.
* `dedup.py --within --module TorsionBasis`: **2 `shape` clusters, 33 removable lines**, both the
  pins' own case-splitter↔headline pairs, recorded here for the gate and *not* to be merged:
  `case_three` ↔ order-three headline (17 lines; the pin's `main` is the same statement, so the
  816 file writes this statement three times) and `main_of_charTwo` ↔ order-four headline (16 lines;
  the pin's `solution` is the same statement).  `case_generic` / `case_two` / `main_of_two_ne_zero`
  carry the extra `2 = 0` / `3 = 0` hypotheses and so do not cluster.
* `move_dead.py --dry-run`: **0 declarations, 0 lines** — nothing dead, nothing to shelve.
* **Heartbeat probe** (FR-0225 — recorded, never installed): `lake env lean -DautoImplicit=false
  -DmaxHeartbeats=N` is silent at **200 000** (the edit loop's and the project's default) and at
  **400 000**; first failures at **100 000**, both in the closing `nlinarith` of the two
  `exists_addOrderOf_eq_and_ne_nsmul` proofs after their `zify` — `:724` `(deterministic) timeout at
  whnf` (the `EB` / order-three copy) and `:1260` `(deterministic) timeout at isDefEq` (the `EA` /
  order-two copy).  Against the 6 400 000 the pin carries, the port needs ≤ 200 000: no
  `set_option maxHeartbeats` is installed.
* FR-0274 / the set-level collision probe: `tmp/af102/collision-probe.lean` cannot run yet (it
  imports the other four AF102 modules, still on the workbench), so the same check was run as a name
  scan over all 1 316 other modules of the port: **0 duplicate public full names**.  Rerun the probe
  when the set is complete.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four.lean>

spec-pin: Theorems/Thm_WeierstrassCurve_exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three.lean
spec-pin: Theorems/Thm_WeierstrassCurve_exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four.lean
spec-pin: P2M/Sol/S_WeierstrassCurve_exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three.lean
spec-pin: P2M/Sol/S_WeierstrassCurve_exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four.lean
-/
import FLTForHuman.Algebra.Module.Torsion.Coordinates
import FLTForHuman.Elliptic.PointArithmetic
import FLTForHuman.Elliptic.TorsionZMod
import FLTForHuman.WeierstrassCurve.Automorphism.Basic
import FLTForHuman.WeierstrassCurve.Automorphism.CharThree
import FLTForHuman.WeierstrassCurve.Automorphism.CharTwo
import FLTForHuman.WeierstrassCurve.Automorphism.DeuringForm
import FLTForHuman.WeierstrassCurve.Velu.VariableChangePoint
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open scoped WeierstrassCurve

namespace WeierstrassCurve.Automorphism

section Points

variable {L : Type*} [Field L] [DecidableEq L]

def xco {W : WeierstrassCurve L} : W.toAffine.Point → Option L
  | 0 => none
  | .some x _ _ => some x

@[scoped simp] theorem xco_zero {W : WeierstrassCurve L} : xco (0 : W.toAffine.Point) = none := rfl
@[scoped simp] theorem xco_some {W : WeierstrassCurve L} {x y : L} (h : W.toAffine.Nonsingular x y) :
    xco (Point.some x y h) = some x := rfl

theorem xco_neg {W : WeierstrassCurve L} (P : W.toAffine.Point) : xco (-P) = xco P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]; rfl

theorem eq_or_eq_neg_of_xco_eq {W : WeierstrassCurve L} {P Q : W.toAffine.Point} (hPQ : xco P = xco Q) :
    P = Q ∨ P = -Q := by
  rcases P with _ | ⟨x, y, h⟩ <;> rcases Q with _ | ⟨x', y', h'⟩
  · exact Or.inl rfl
  · simp [xco] at hPQ
  · simp [xco] at hPQ
  · simp only [xco_some, Option.some.injEq] at hPQ
    subst hPQ
    have hy : y = y' ∨ y = W.toAffine.negY x y' := by
      have h1 := h.1; have h2 := h'.1
      rw [WeierstrassCurve.Affine.equation_iff] at h1 h2
      have : (y - y') * (y - W.toAffine.negY x y') = 0 := by
        rw [WeierstrassCurve.Affine.negY]; linear_combination h1 - h2
      rcases mul_eq_zero.mp this with h0 | h0
      · exact Or.inl (sub_eq_zero.mp h0)
      · exact Or.inr (sub_eq_zero.mp h0)
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · right; rw [Point.neg_some]

theorem exists_eq_some_of_xy_eq {W : WeierstrassCurve L} {Q : W.toAffine.Point} {x y : L}
    (h : xy Q = some (x, y)) : ∃ h', Q = Point.some x y h' := by
  rcases Q with _ | ⟨x', y', h'⟩
  · exact absurd h (by simp [xy])
  · simp only [xy, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h', rfl⟩

theorem baseChange_self (W : WeierstrassCurve L) : (W⁄L) = W.toAffine := by
  show (W.baseChange L).toAffine = W.toAffine
  rw [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]

end Points

section Torsion

variable {A : Type*} [AddCommGroup A]

theorem natCard_torsionBy_of_addEquiv (n : ℕ) (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n) :
    Nat.card (Submodule.torsionBy ℤ A n) = n ^ 2 := by
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]

theorem mem_torsionBy_iff_nsmul (n : ℕ) (T : A) : T ∈ Submodule.torsionBy ℤ A n ↔ n • T = 0 := by
  rw [Submodule.mem_torsionBy_iff, natCast_zsmul]

theorem addEquiv_apply_eq (n : ℕ) [NeZero n] (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n)
    (c : ZMod n × ZMod n) :
    ((e c : Submodule.torsionBy ℤ A n) : A) =
      c.1.val • ((e (1, 0) : Submodule.torsionBy ℤ A n) : A) +
        c.2.val • ((e (0, 1) : Submodule.torsionBy ℤ A n) : A) := by
  obtain ⟨c₁, c₂⟩ := c
  have hv : (c₁, c₂) = c₁.val • ((1 : ZMod n), (0 : ZMod n)) + c₂.val • ((0 : ZMod n), (1 : ZMod n)) := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_mk, smul_zero, add_zero, nsmul_eq_mul, mul_one,
        ZMod.natCast_zmod_val]
    · simp only [Prod.snd_add, Prod.smul_mk, smul_zero, zero_add, nsmul_eq_mul, mul_one,
        ZMod.natCast_zmod_val]
  dsimp only
  rw [hv, map_add, map_nsmul, map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul,
    AddSubmonoidClass.coe_nsmul]

theorem coords_of_addEquiv (n : ℕ) [NeZero n] (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n)
    (T : A) (hT : n • T = 0) :
    ∃! c : ZMod n × ZMod n,
      T = c.1.val • ((e (1, 0) : Submodule.torsionBy ℤ A n) : A) +
        c.2.val • ((e (0, 1) : Submodule.torsionBy ℤ A n) : A) := by
  have hT' : T ∈ Submodule.torsionBy ℤ A n := (mem_torsionBy_iff_nsmul n T).mpr hT
  refine ⟨e.symm ⟨T, hT'⟩, ?_, ?_⟩
  · show T = _
    rw [← addEquiv_apply_eq, AddEquiv.apply_symm_apply]
  · intro c hc
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    exact Subtype.ext (by rw [addEquiv_apply_eq]; exact hc.symm)

theorem nsmul_coe_addEquiv_eq_zero (n : ℕ) (e : ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n)
    (c : ZMod n × ZMod n) : n • ((e c : Submodule.torsionBy ℤ A n) : A) = 0 :=
  (mem_torsionBy_iff_nsmul n _).mp (e c).2

end Torsion

section Glue

variable {A : Type*} [AddCommGroup A] {M : ℕ} [NeZero M]

theorem nsmul_coe_eq_zero (x : Submodule.torsionBy ℤ A M) : M • (x : A) = 0 := by
  have hx := x.2
  rw [Submodule.mem_torsionBy_iff] at hx
  rw [← natCast_zsmul]
  exact hx

theorem mem_torsionBy_of_nsmul_eq_zero {T : A} (hT : M • T = 0) : T ∈ Submodule.torsionBy ℤ A M := by
  rw [Submodule.mem_torsionBy_iff]
  show ((M : ℕ) : ℤ) • T = 0
  rw [natCast_zsmul]
  exact hT

theorem coe_apply_eq (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M) (c : ZMod M × ZMod M) :
    ((e c : Submodule.torsionBy ℤ A M) : A) =
      c.1.val • ((e (1, 0) : Submodule.torsionBy ℤ A M) : A) +
        c.2.val • ((e (0, 1) : Submodule.torsionBy ℤ A M) : A) := by
  have hc : c.1.val • ((1 : ZMod M), (0 : ZMod M)) + c.2.val • ((0 : ZMod M), (1 : ZMod M)) = c := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_mk, smul_zero, add_zero, nsmul_eq_mul, mul_one,
        ZMod.natCast_zmod_val]
    · simp only [Prod.snd_add, Prod.smul_mk, smul_zero, zero_add, nsmul_eq_mul, mul_one,
        ZMod.natCast_zmod_val]
  calc ((e c : Submodule.torsionBy ℤ A M) : A)
        = ((e (c.1.val • ((1 : ZMod M), (0 : ZMod M)) + c.2.val • ((0 : ZMod M), (1 : ZMod M))) :
            Submodule.torsionBy ℤ A M) : A) := by rw [hc]
    _ = _ := by
      rw [map_add, map_nsmul, map_nsmul, Submodule.coe_add, AddSubmonoidClass.coe_nsmul,
        AddSubmonoidClass.coe_nsmul]

theorem existsUnique_coords (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M) (T : A)
    (hT : M • T = 0) :
    ∃! c : ZMod M × ZMod M,
      T = c.1.val • ((e (1, 0) : Submodule.torsionBy ℤ A M) : A) +
        c.2.val • ((e (0, 1) : Submodule.torsionBy ℤ A M) : A) := by
  refine ⟨e.symm ⟨T, mem_torsionBy_of_nsmul_eq_zero hT⟩, ?_, ?_⟩
  · have h := coe_apply_eq e (e.symm ⟨T, mem_torsionBy_of_nsmul_eq_zero hT⟩)
    rw [e.apply_symm_apply] at h
    exact h
  · intro d hd
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [coe_apply_eq e d]
    exact hd.symm

theorem natCard_torsionBy_eq_sq (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ A M) :
    Nat.card (Submodule.torsionBy ℤ A M) = M ^ 2 := by
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod, sq]

end Glue

section Assembly

variable {K : Type*} [Field K] [DecidableEq K]

theorem finish (M : ℕ) [NeZero M]
    (E₀ : WeierstrassCurve K) [hE : E₀.IsElliptic] (hj : E₀.j = 0)
    (γ : VariableChange K) (hγ : γ • E₀ = E₀)
    (σ : E₀.toAffine.Point →+ E₀.toAffine.Point)
    (hheq : ∀ T, HEq (Point.vcInvFun γ E₀.toAffine T) (σ T))
    (hσ : ∀ T, σ (σ T) + σ T + T = 0)
    (P : E₀.toAffine.Point) (hP : M • P = 0)
    (hc : ∀ T : E₀.toAffine.Point, M • T = 0 →
      ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • σ P) :
    ∃ (E₀ : WeierstrassCurve K) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange K)
      (P Q : E₀.toAffine.Point),
      E₀.j = 0 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P - Q) := by
  refine ⟨E₀, hE, γ, P, σ P, hj, hγ, hP, by rw [← map_nsmul, hP, map_zero], hc, hheq P, ?_⟩
  have h2 : σ (σ P) = -P - σ P := by
    have h := hσ P
    rw [add_assoc, add_eq_zero_iff_eq_neg] at h
    rw [h]; abel
  exact (hheq (σ P)).trans (heq_of_eq h2)

theorem finish_of_addEquiv (M : ℕ) [NeZero M]
    (E₀ : WeierstrassCurve K) [hE : E₀.IsElliptic] (hj : E₀.j = 0)
    (γ : VariableChange K) (hγ : γ • E₀ = E₀)
    (σ : E₀.toAffine.Point →+ E₀.toAffine.Point)
    (hheq : ∀ T, HEq (Point.vcInvFun γ E₀.toAffine T) (σ T))
    (hσ : ∀ T, σ (σ T) + σ T + T = 0)
    (e' : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ E₀.toAffine.Point M)
    (he' : ((e' (0, 1) : Submodule.torsionBy ℤ E₀.toAffine.Point M) : E₀.toAffine.Point) =
      σ ((e' (1, 0) : Submodule.torsionBy ℤ E₀.toAffine.Point M) : E₀.toAffine.Point)) :
    ∃ (E₀ : WeierstrassCurve K) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange K)
      (P Q : E₀.toAffine.Point),
      E₀.j = 0 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P - Q) := by
  refine finish M E₀ hj γ hγ σ hheq hσ _ (nsmul_coe_addEquiv_eq_zero M e' (1, 0)) fun T hT => ?_
  have h := coords_of_addEquiv M e' T hT
  rwa [he'] at h

theorem assemble (M : ℕ) [NeZero M] (E₀ : WeierstrassCurve K) (hE : E₀.IsElliptic)
    (hj : E₀.j = 1728) (C : VariableChange K) (hC : C • E₀ = E₀)
    (σ : E₀.toAffine.Point →+ E₀.toAffine.Point)
    (hheq : ∀ T : E₀.toAffine.Point, HEq (Point.vcInvFun C E₀.toAffine T) (σ T))
    (hσ : ∀ T, σ (σ T) = -T)
    (hns : ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ a : E₀.toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a)
    (e : ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ E₀.toAffine.Point M) :
    ∃ (E₀ : WeierstrassCurve K) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange K)
      (P Q : E₀.toAffine.Point),
      E₀.j = 1728 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P) := by
  obtain ⟨e', he'⟩ :=
    AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul M e σ hns
  refine ⟨E₀, hE, C, ((e' (1, 0) : Submodule.torsionBy ℤ E₀.toAffine.Point M) : E₀.toAffine.Point),
    ((e' (0, 1) : Submodule.torsionBy ℤ E₀.toAffine.Point M) : E₀.toAffine.Point), hj, hC,
    nsmul_coe_eq_zero _, nsmul_coe_eq_zero _, fun T hT => existsUnique_coords e' T hT, ?_, ?_⟩
  · exact (hheq _).trans (heq_of_eq he'.symm)
  · refine (hheq _).trans (heq_of_eq ?_)
    rw [he', hσ]

end Assembly

section Roots

variable {K : Type*} [Field K] [IsAlgClosed K]

theorem exists_cube_root (h3 : (3 : K) ≠ 0) : ∃ u : Kˣ, (u : K) ^ 3 = 1 ∧ (u : K) ≠ 1 := by
  have : NeZero ((3 : ℕ) : K) := ⟨by exact_mod_cast h3⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K 3
  refine ⟨Units.mk0 ζ (hζ.ne_zero (by norm_num)), ?_, ?_⟩
  · show ζ ^ 3 = 1; exact hζ.pow_eq_one
  · show ζ ≠ 1; exact hζ.ne_one (by norm_num)

theorem exists_sq_eq_neg_one (h2 : (2 : K) ≠ 0) : ∃ i : Kˣ, (i : K) ^ 2 = -1 := by
  have : NeZero ((4 : ℕ) : K) := ⟨by
    have : ((4 : ℕ) : K) = 2 ^ 2 := by push_cast; norm_num
    rw [this]; exact pow_ne_zero 2 h2⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K 4
  refine ⟨Units.mk0 ζ (hζ.ne_zero (by norm_num)), ?_⟩
  show ζ ^ 2 = -1
  have h4 : ζ ^ 4 = 1 := hζ.pow_eq_one
  have h2' : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) h2'
  · linear_combination h

end Roots

section Scalar

variable {V : Type*} [AddCommGroup V]

theorem exists_common_scalar {p : ℕ} [Fact p.Prime] (e : ZMod p × ZMod p ≃+ V) (σ : V →+ V)
    (heig : ∀ v : V, ∃ a : ℤ, σ v = a • v) : ∃ c : ℤ, ∀ v : V, σ v = c • v := by
  obtain ⟨a, ha⟩ := heig (e (1, 0))
  obtain ⟨b, hb⟩ := heig (e (0, 1))
  obtain ⟨c, hc⟩ := heig (e (1, 1))
  have hsum : e (1, 1) = e (1, 0) + e (0, 1) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  have key : c • e (1, 0) + c • e (0, 1) = a • e (1, 0) + b • e (0, 1) := by
    rw [← smul_add, ← hsum, ← hc, hsum, map_add, ha, hb]
  have key' : ((c : ZMod p), (c : ZMod p)) = ((a : ZMod p), (b : ZMod p)) := by
    apply e.injective
    have h1 : e ((c : ZMod p), (c : ZMod p)) = c • e (1, 0) + c • e (0, 1) := by
      rw [← map_zsmul, ← map_zsmul, ← map_add]; congr 1; ext <;> simp
    have h2 : e ((a : ZMod p), (b : ZMod p)) = a • e (1, 0) + b • e (0, 1) := by
      rw [← map_zsmul, ← map_zsmul, ← map_add]; congr 1; ext <;> simp
    rw [h1, h2, key]
  have hca : (c : ZMod p) = a := congrArg Prod.fst key'
  have hcb : (c : ZMod p) = b := congrArg Prod.snd key'
  have hpV : ∀ v : V, (p : ℤ) • v = 0 := by
    intro v
    obtain ⟨w, rfl⟩ := e.surjective v
    rw [← map_zsmul, show (p : ℤ) • w = 0 from ?_, map_zero]
    ext <;> simp [zsmul_eq_mul]
  have hzs : ∀ (m n : ℤ) (v : V), (m : ZMod p) = n → m • v = n • v := by
    intro m n v hmn
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub n m p).mp hmn.symm
    have : m = n + p * k := by linarith
    rw [this, add_zsmul, mul_comm, mul_zsmul, hpV, zsmul_zero, add_zero]
  refine ⟨c, fun v => ?_⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := e.surjective v
  have hv : e (s, t) = (s.val : ℤ) • e (1, 0) + (t.val : ℤ) • e (0, 1) := by
    rw [← map_zsmul, ← map_zsmul, ← map_add]; congr 1; ext <;> simp
  rw [hv, map_add, map_zsmul, map_zsmul, ha, hb, smul_add, smul_comm c (s.val : ℤ),
    smul_comm c (t.val : ℤ), hzs a c _ hca.symm, hzs b c _ hcb.symm]

end Scalar

section Generic

variable {L : Type*} [Field L] [DecidableEq L]

theorem natDegree_Phi_sub_C_mul_X_mul_PsiSq_le (W : WeierstrassCurve L) (c : L) (m : ℕ) (hm : 1 ≤ m) :
    (W.Φ (m : ℤ) - C c * X * W.ΨSq (m : ℤ)).natDegree ≤ m ^ 2 := by
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · have hΦ := W.natDegree_Φ_le (m : ℤ)
    simp only [Int.natAbs_natCast] at hΦ
    exact hΦ
  · refine (natDegree_mul_le).trans ?_
    have hΨ := W.natDegree_ΨSq_le (m : ℤ)
    simp only [Int.natAbs_natCast] at hΨ
    have hCX : (C c * X : L[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
    omega

abbrev EB (B : L) : WeierstrassCurve L := ⟨0, 0, 0, 0, B⟩

theorem EB_Δ (B : L) : (EB B).Δ = -432 * B ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]; ring

theorem EB_c₄ (B : L) : (EB B).c₄ = 0 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring

theorem isElliptic_EB (B : L) (hB : B ≠ 0) (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) :
    (EB B).IsElliptic := by
  refine ⟨?_⟩
  rw [EB_Δ, isUnit_iff_ne_zero]
  have h432 : (432 : L) ≠ 0 := by
    rw [show (432 : L) = 2 ^ 4 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  exact mul_ne_zero (neg_ne_zero.mpr h432) (pow_ne_zero 2 hB)

theorem exists_addOrderOf_eq_and_ne_nsmul [IsAlgClosed L] (B : L) (hB : B ≠ 0) (u : Lˣ)
    (hu1 : (u : L) ≠ 1) (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)
    (σ : (EB B).toAffine.Point →+ (EB B).toAffine.Point)
    (hσx : ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y),
      xco (σ (Point.some x y h)) = some ((u : L) * x))
    (hσ : ∀ P : (EB B).toAffine.Point, σ (σ P) + σ P + P = 0)
    (p : ℕ) (hp : p.Prime) (hpL : (p : L) ≠ 0) :
    ∃ T : (EB B).toAffine.Point, addOrderOf T = p ∧ ∀ k : ℕ, σ T ≠ k • T := by
  have : Fact p.Prime := ⟨hp⟩
  have hE : (EB B).IsElliptic := isElliptic_EB B hB h2 h3
  have hσ0 : ∀ P : (EB B).toAffine.Point, σ P = 0 ↔ P = 0 := fun P =>
    ⟨fun h0 => by have := hσ P; rwa [h0, map_zero, zero_add, zero_add] at this,
     fun h0 => by rw [h0, map_zero]⟩

  have hbasis : ∀ n : ℕ, (n : L) ≠ 0 →
      Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ (EB B).toAffine.Point n) := by
    intro n hn
    have h := (EB B).nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := L) hn
    rwa [baseChange_self] at h
  have hcard_of : ∀ n : ℕ, (n : L) ≠ 0 →
      Nat.card (Submodule.torsionBy ℤ (EB B).toAffine.Point n) = n ^ 2 := by
    intro n hn
    obtain ⟨e⟩ := hbasis n hn
    exact natCard_torsionBy_of_addEquiv n e

  suffices core : ∃ (x y : L) (h : (EB B).toAffine.Nonsingular x y), addOrderOf (Point.some x y h) = p ∧
      ∀ k : ℕ, xco (k • Point.some x y h) ≠ some ((u : L) * x) by
    obtain ⟨x, y, h, hord, hk⟩ := core
    refine ⟨Point.some x y h, hord, fun k hk' => hk k ?_⟩
    rw [← hk', hσx]
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    obtain ⟨a, ha⟩ : ∃ a : L, a ^ 3 = -B := by
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-B) (n := 3) (by norm_num)
      exact ⟨a, ha⟩
    have ha0 : a ≠ 0 := by rintro rfl; apply hB; simpa using ha.symm
    have heq : (EB B).toAffine.Equation a 0 := by
      rw [WeierstrassCurve.Affine.equation_iff]; simp; linear_combination -ha
    have hns : (EB B).toAffine.Nonsingular a 0 := by
      rw [WeierstrassCurve.Affine.nonsingular_iff']
      refine ⟨heq, Or.inl ?_⟩
      show (0 : L) * 0 - (3 * a ^ 2 + 2 * 0 * a + 0) ≠ 0
      intro h3a
      apply ha0
      have : (3 : L) * a ^ 2 = 0 := by linear_combination -h3a
      simpa [h3] using this
    have hneg : -Point.some a 0 hns = Point.some a 0 hns := by
      rw [Point.neg_some]; congr 1; simp [WeierstrassCurve.Affine.negY]
    have h2T : (2 : ℕ) • Point.some a 0 hns = 0 := by
      rw [two_nsmul]; nth_rewrite 1 [← hneg]; rw [neg_add_cancel]
    have hord : addOrderOf (Point.some a 0 hns) = 2 :=
      addOrderOf_eq_prime_iff.mpr ⟨h2T, Point.some_ne_zero hns⟩
    refine ⟨a, 0, hns, hord, fun k => ?_⟩
    have hkT : k • Point.some a 0 hns = 0 ∨ k • Point.some a 0 hns = Point.some a 0 hns := by
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left; rw [← two_mul, mul_nsmul, h2T, nsmul_zero]
      · right; rw [add_nsmul, mul_nsmul, h2T, nsmul_zero, zero_add, one_nsmul]
    rcases hkT with h0 | h1
    · rw [h0, xco_zero]; simp
    · rw [h1, xco_some]; simp only [ne_eq, Option.some.injEq]
      intro h; apply hu1
      have : (1 - (u : L)) * a = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact (sub_eq_zero.mp h').symm
      · exact absurd h' ha0
  ·
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases this.eq_or_lt with h | h
      · exact absurd hpodd (by rw [← h]; decide)
      · omega
    have hcard : Nat.card (Submodule.torsionBy ℤ (EB B).toAffine.Point p) = p ^ 2 := hcard_of p hpL
    by_contra hcon
    push Not at hcon

    have heig : ∀ T : (EB B).toAffine.Point, (p : ℤ) • T = 0 → ∃ a : ℤ, σ T = a • T := by
      intro T hpT
      rcases T with _ | ⟨x, y, h⟩
      · exact ⟨0, by rw [zero_smul]; exact map_zero σ⟩
      · have hord : addOrderOf (Point.some x y h) = p := by
          refine addOrderOf_eq_prime_iff.mpr ⟨?_, Point.some_ne_zero h⟩
          rw [← natCast_zsmul]; exact hpT
        obtain ⟨k, hk⟩ := hcon x y h hord
        have hx : xco (σ (Point.some x y h)) = xco (k • Point.some x y h) := by rw [hσx, hk]
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · exact ⟨k, by rw [h1, natCast_zsmul]⟩
        · exact ⟨-k, by rw [h1, neg_smul, natCast_zsmul]⟩

    let Ep := (Submodule.torsionBy ℤ (EB B).toAffine.Point p).toAddSubgroup
    have hEp_mem : ∀ T : (EB B).toAffine.Point, T ∈ Ep ↔ (p : ℤ) • T = 0 := fun T =>
      Submodule.mem_torsionBy_iff _ _
    have hσEp : ∀ T ∈ Ep, σ T ∈ Ep := by
      intro T hT
      rw [hEp_mem] at hT ⊢
      rw [← map_zsmul, hT, map_zero]
    let σ' : Ep →+ Ep := (σ.domRestrict Ep).codRestrict Ep (fun T => hσEp T T.2)
    obtain ⟨eb⟩ : Nonempty (ZMod p × ZMod p ≃+ Ep) := hbasis p hpL
    have heig' : ∀ v : Ep, ∃ a : ℤ, σ' v = a • v := by
      rintro ⟨T, hT⟩
      obtain ⟨a, ha⟩ := heig T ((hEp_mem T).mp hT)
      exact ⟨a, Subtype.ext ha⟩
    obtain ⟨c, hc⟩ := exists_common_scalar eb σ' heig'

    obtain ⟨m, hm1, hmle, hmx⟩ : ∃ m : ℕ, 1 ≤ m ∧ 2 * m ≤ p - 1 ∧
        ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 →
          xco ((m : ℤ) • Point.some x y h) = some ((u : L) * x) := by
      let r : ℕ := ((c : ZMod p)).val
      have hr : (r : ZMod p) = c := by simp [r]
      have hrp : r < p := ZMod.val_lt _
      have hσc : ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 →
          σ (Point.some x y h) = (r : ℤ) • Point.some x y h := by
        intro x y h hpT
        have hT : Point.some x y h ∈ Ep := (hEp_mem _).mpr hpT
        have := hc ⟨_, hT⟩
        have hval : σ (Point.some x y h) = c • Point.some x y h := congrArg Subtype.val this
        rw [hval]
        obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (r : ℤ) c p).mp (by exact_mod_cast hr)
        have : c = r + p * k := by linarith
        rw [this, add_zsmul, mul_comm, mul_zsmul, hpT, zsmul_zero, add_zero]
      obtain ⟨x₀, y₀, h₀, hp₀⟩ : ∃ (x y : L) (h : (EB B).toAffine.Nonsingular x y),
          (p : ℤ) • Point.some x y h = 0 := by
        have h1 : 1 < Nat.card Ep := by rw [show Nat.card Ep = p ^ 2 from hcard]; nlinarith
        have : Finite Ep := Nat.finite_of_card_ne_zero (by rw [show Nat.card Ep = p ^ 2 from hcard]; positivity)
        have : Nontrivial Ep := Finite.one_lt_card_iff_nontrivial.mp h1
        obtain ⟨⟨T, hT⟩, hT0⟩ := exists_ne (0 : Ep)
        rcases T with _ | ⟨x, y, h⟩
        · exact absurd rfl (fun h => hT0 (Subtype.ext h))
        · exact ⟨x, y, h, (hEp_mem _).mp hT⟩
      have hr0 : r ≠ 0 := by
        intro hr0
        have := hσc x₀ y₀ h₀ hp₀
        rw [hr0, Nat.cast_zero, zero_smul, hσ0] at this
        exact Point.some_ne_zero h₀ this
      by_cases hle : 2 * r ≤ p - 1
      · refine ⟨r, Nat.one_le_iff_ne_zero.mpr hr0, hle, fun x y h hpT => ?_⟩
        rw [← hσc x y h hpT, hσx]
      · obtain ⟨k0, hk0⟩ := hpodd
        refine ⟨p - r, by omega, by omega, fun x y h hpT => ?_⟩
        have : ((p - r : ℕ) : ℤ) • Point.some x y h = -((r : ℤ) • Point.some x y h) := by
          rw [Nat.cast_sub hrp.le, sub_zsmul, hpT]; simp
        rw [this, xco_neg, ← hσc x y h hpT, hσx]

    set F : L[X] := (EB B).Φ (m : ℤ) - C (u : L) * X * (EB B).ΨSq (m : ℤ) with hFdef
    have hFdeg : F.natDegree ≤ m ^ 2 := natDegree_Phi_sub_C_mul_X_mul_PsiSq_le (EB B) (u : L) m hm1

    have hxm : ∀ (q : ℕ), q.Prime → m < q → ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y),
        (q : ℤ) • Point.some x y h = 0 →
        ((EB B).ΨSq (m : ℤ)).eval x ≠ 0 ∧
          xco ((m : ℤ) • Point.some x y h) = some (((EB B).Φ (m : ℤ)).eval x / ((EB B).ΨSq (m : ℤ)).eval x) := by
      intro q hq hmq x y h hqT
      have : Fact q.Prime := ⟨hq⟩
      have hord : addOrderOf (Point.some x y h) = q :=
        addOrderOf_eq_prime_iff.mpr ⟨by rw [← natCast_zsmul]; exact hqT, Point.some_ne_zero h⟩
      have hmT : (m : ℤ) • Point.some x y h ≠ 0 := by
        rw [natCast_zsmul]
        intro h0
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
        rw [hord] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      have hψ : ((EB B).ψ (m : ℤ)).evalEval x y ≠ 0 := fun h0 =>
        hmT ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (EB B) h (m : ℤ)).mpr h0)
      obtain ⟨y', h', hmul⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (EB B) h hψ
      refine ⟨?_, by rw [hmul, xco_some]⟩
      rw [← WeierstrassCurve.Affine.evalEval_psi_sq (EB B) h.1 (m : ℤ)]; exact pow_ne_zero 2 hψ

    have hF0 : F ≠ 0 := by
      intro hF

      obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (max (m ^ 2 + m + 2) (ringChar L + 1))
      have hqm : m ^ 2 + m + 1 < q := by have := le_max_left (m ^ 2 + m + 2) (ringChar L + 1); omega
      have hqc : ringChar L < q := by have := le_max_right (m ^ 2 + m + 2) (ringChar L + 1); omega
      have hqL : (q : L) ≠ 0 := by
        intro h0
        have hdvd : ringChar L ∣ q := (ringChar.spec L q).mp h0
        rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
        · exact CharP.ringChar_ne_one h1
        · omega
      have : Fact q.Prime := ⟨hq⟩

      have hcardq : Nat.card (Submodule.torsionBy ℤ (EB B).toAffine.Point q) = q ^ 2 := hcard_of q hqL
      obtain ⟨x₀, y₀, h₀, hq₀⟩ : ∃ (x y : L) (h : (EB B).toAffine.Nonsingular x y),
          (q : ℤ) • Point.some x y h = 0 := by
        let Eq' := (Submodule.torsionBy ℤ (EB B).toAffine.Point q).toAddSubgroup
        have hq1 : 1 < q := hq.one_lt
        have h1 : 1 < Nat.card Eq' := by rw [show Nat.card Eq' = q ^ 2 from hcardq]; nlinarith
        have : Finite Eq' := Nat.finite_of_card_ne_zero (by rw [show Nat.card Eq' = q ^ 2 from hcardq]; positivity)
        have : Nontrivial Eq' := Finite.one_lt_card_iff_nontrivial.mp h1
        obtain ⟨⟨T, hT⟩, hT0⟩ := exists_ne (0 : Eq')
        rcases T with _ | ⟨x, y, h⟩
        · exact absurd rfl (fun h => hT0 (Subtype.ext h))
        · exact ⟨x, y, h, (Submodule.mem_torsionBy_iff _ _).mp hT⟩
      have hordq : addOrderOf (Point.some x₀ y₀ h₀) = q :=
        addOrderOf_eq_prime_iff.mpr ⟨by rw [← natCast_zsmul]; exact hq₀, Point.some_ne_zero h₀⟩

      obtain ⟨hΨ, hxq⟩ := hxm q hq (by nlinarith) x₀ y₀ h₀ hq₀
      have hΦ : ((EB B).Φ (m : ℤ)).eval x₀ = (u : L) * x₀ * ((EB B).ΨSq (m : ℤ)).eval x₀ := by
        have := congrArg (Polynomial.eval x₀) hF
        rw [hFdef, eval_zero, eval_sub, eval_mul, eval_mul, eval_C, eval_X] at this
        linear_combination this
      have hx : xco (σ (Point.some x₀ y₀ h₀)) = xco ((m : ℤ) • Point.some x₀ y₀ h₀) := by
        rw [hσx, hxq, hΦ, mul_div_assoc, div_self hΨ, mul_one]

      obtain ⟨a, ha, haT⟩ : ∃ a : ℤ, (a = m ∨ a = -m) ∧
          σ (Point.some x₀ y₀ h₀) = a • Point.some x₀ y₀ h₀ := by
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · exact ⟨m, Or.inl rfl, h1⟩
        · exact ⟨-m, Or.inr rfl, by rw [h1, neg_smul]⟩

      have hkill : (a * a + a + 1) • Point.some x₀ y₀ h₀ = 0 := by
        have := hσ (Point.some x₀ y₀ h₀)
        rw [haT, map_zsmul, haT, smul_smul] at this
        rwa [add_smul, add_smul, one_smul]
      have hdvd : ((q : ℕ) : ℤ) ∣ a * a + a + 1 := by
        rw [← hordq]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkill
      have hpos : 0 < a * a + a + 1 := by nlinarith
      have hle := Int.le_of_dvd hpos hdvd
      have hqm' : ((m : ℤ)) ^ 2 + m + 1 < q := by exact_mod_cast hqm
      rcases ha with rfl | rfl <;> nlinarith
    have hroot : ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y),
        (p : ℤ) • Point.some x y h = 0 → F.IsRoot x := by
      intro x y h hpT
      obtain ⟨hΨ, hxp⟩ := hxm p hp (by omega) x y h hpT
      have hx : xco ((m : ℤ) • Point.some x y h) = some ((u : L) * x) := hmx x y h hpT
      rw [hxp, Option.some.injEq, div_eq_iff hΨ] at hx
      show F.eval x = 0
      rw [hFdef, eval_sub, eval_mul, eval_mul, eval_C, eval_X]
      linear_combination hx

    have hfinEp : Finite Ep := Nat.finite_of_card_ne_zero (by rw [show Nat.card Ep = p ^ 2 from hcard]; positivity)
    have : Fintype Ep := Fintype.ofFinite Ep
    classical
    let g : Ep → Option L := fun T => xco (T.1 : (EB B).toAffine.Point)
    let s : Finset Ep := Finset.univ.filter (fun T => T ≠ 0)
    have hs_card : s.card = p ^ 2 - 1 := by
      have : s.card + 1 = p ^ 2 := by
        rw [show s = Finset.univ.erase 0 by ext T; simp [s], Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ← Nat.card_eq_fintype_card, show Nat.card Ep = p ^ 2 from hcard]
        have : 1 ≤ p ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
      omega
    have hfib : ∀ b ∈ s.image g, (s.filter (fun T => g T = b)).card ≤ 2 := by
      intro b hb
      obtain ⟨T₁, hT₁, rfl⟩ := Finset.mem_image.mp hb
      have hsub : s.filter (fun T => g T = g T₁) ⊆ {T₁, -T₁} := by
        intro T hT
        rw [Finset.mem_filter] at hT
        have hx : xco (T.1 : (EB B).toAffine.Point) = xco (T₁.1 : (EB B).toAffine.Point) := hT.2
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · rw [Finset.mem_insert]; left; exact Subtype.ext h1
        · rw [Finset.mem_insert, Finset.mem_singleton]; right
          exact Subtype.ext (by rw [h1]; rfl)
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
    have hle : s.card ≤ 2 * (s.image g).card := Finset.card_le_mul_card_image s 2 hfib
    have himg : s.image g ⊆ (F.roots.toFinset).image some := by
      intro b hb
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hb
      rw [Finset.mem_filter] at hT
      obtain ⟨⟨T, hTp⟩, hT0⟩ := T, hT.2
      rcases T with _ | ⟨x, y, h⟩
      · exact absurd rfl (fun h => hT0 (Subtype.ext h))
      · refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
        rw [Multiset.mem_toFinset, mem_roots hF0]
        exact hroot x y h ((hEp_mem _).mp hTp)
    have hR : ((F.roots.toFinset).image some).card ≤ m ^ 2 := by
      refine Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans ?_)
      exact (Polynomial.card_roots' F).trans hFdeg
    have hfinal : p ^ 2 - 1 ≤ 2 * m ^ 2 := by
      rw [← hs_card]; exact hle.trans (Nat.mul_le_mul_left 2 ((Finset.card_le_card himg).trans hR))
    have h4 : 4 * m ^ 2 ≤ (p - 1) ^ 2 := by nlinarith
    have hp1 : 1 ≤ p := hp.one_lt.le
    zify [hp1, Nat.one_le_iff_ne_zero.mpr (show p ^ 2 ≠ 0 by positivity)] at hfinal h4 hmle
    nlinarith
theorem case_generic [IsAlgClosed L] (M : ℕ) [NeZero M] (hM : (M : L) ≠ 0)
    (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) :
    ∃ (E₀ : WeierstrassCurve L) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange L)
      (P Q : E₀.toAffine.Point),
      E₀.j = 0 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P - Q) := by
  obtain ⟨u, hu, hu1⟩ := exists_cube_root (K := L) h3
  have hE : (EB (1 : L)).IsElliptic := isElliptic_EB 1 one_ne_zero h2 h3

  have hW : (⟨u, 0, 0, 0⟩ : VariableChange L) • EB (1 : L) = EB 1 :=
    WeierstrassCurve.variableChange_mk_smul_eq_self_of_pow_three_eq_one u hu 1
  set γ : VariableChange L := ⟨u, 0, 0, 0⟩ with hγdef
  set W : WeierstrassCurve L := EB (1 : L) with hWdef
  let σ : W.toAffine.Point →+ W.toAffine.Point := vcHom γ W hW
  have hi3 : ((u⁻¹ : Lˣ) : L) ^ 3 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_one]
  have hi2 : ((u⁻¹ : Lˣ) : L) ^ 2 = u := by
    rw [Units.val_inv_eq_inv_val, inv_pow]
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ, hu])

  have σ_some : ∀ (x y : L) (h : W.toAffine.Nonsingular x y),
      ∃ h', σ (Point.some x y h) = Point.some ((u : L) * x) y h' := by
    intro x y h
    apply exists_eq_some_of_xy_eq
    rw [xy_vcHom]
    simp only [xy, Option.map_some, hγdef, vcXInv, vcYInv, sub_zero, zero_mul, hi2, hi3, one_mul]
  have hσx : ∀ (x y : L) (h : W.toAffine.Nonsingular x y),
      xco (σ (Point.some x y h)) = some ((u : L) * x) := by
    intro x y h
    obtain ⟨h', e⟩ := σ_some x y h
    rw [e, xco_some]

  have hσ : ∀ P : W.toAffine.Point, σ (σ P) + σ P + P = 0 := by
    rintro (_ | ⟨x, y, h⟩)
    · simp only [← WeierstrassCurve.Affine.Point.zero_def, map_zero, add_zero]
    · obtain ⟨h1, e1⟩ := σ_some x y h
      obtain ⟨h2', e2⟩ := σ_some ((u : L) * x) y h1
      rw [e1, e2]
      by_cases hx : x = 0
      · subst hx
        have hy0 : y ≠ 0 := by
          have heq := h.left
          rw [WeierstrassCurve.Affine.equation_iff] at heq
          simp only [hWdef, zero_mul, mul_zero, add_zero] at heq
          rintro rfl
          simp at heq
        have e0 : ∀ (h' : W.toAffine.Nonsingular ((u : L) * 0) y),
            Point.some ((u : L) * 0) y h' = Point.some 0 y h := by
          intro h'; apply xy_injective; simp [xy]
        have e00 : ∀ (h' : W.toAffine.Nonsingular ((u : L) * ((u : L) * 0)) y),
            Point.some ((u : L) * ((u : L) * 0)) y h' = Point.some 0 y h := by
          intro h'; apply xy_injective; simp [xy]
        rw [e0, e00, WeierstrassCurve.Affine.Point.some_zero_add_self_eq_neg_of_a6_model (1 : L) h2 hy0 h,
          neg_add_cancel]
      · have hw2x : W.toAffine.Nonsingular ((u : L) ^ 2 * x) y := by
          have : (u : L) ^ 2 * x = (u : L) * ((u : L) * x) := by ring
          rw [this]; exact h2'
        have e3 : Point.some ((u : L) * ((u : L) * x)) y h2' = Point.some ((u : L) ^ 2 * x) y hw2x := by
          apply xy_injective; simp only [xy, Option.some.injEq, Prod.mk.injEq, and_true]; ring
        rw [e3, add_assoc, add_comm (Point.some ((u : L) * x) y h1),
          WeierstrassCurve.Affine.Point.some_add_some_eq_neg_some_of_pow_three_eq_one (1 : L) (u : L) hu hu1 h h1
            hw2x hx,
          add_neg_cancel]

  have hns : ∀ p : ℕ, p.Prime → p ∣ M → ∃ a : W.toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a := by
    intro p hp hpM
    have hpL : (p : L) ≠ 0 := by
      obtain ⟨c, rfl⟩ := hpM
      intro h0; apply hM; push_cast; rw [h0, zero_mul]
    exact exists_addOrderOf_eq_and_ne_nsmul 1 one_ne_zero u hu1 h2 h3 σ hσx hσ p hp hpL

  obtain ⟨e⟩ : Nonempty (ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ W.toAffine.Point M) := by
    have h := W.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := L) hM
    rwa [baseChange_self] at h
  obtain ⟨e', he'⟩ :=
    AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul M e σ hns
  exact finish_of_addEquiv M W (WeierstrassCurve.j_eq_zero _ (EB_c₄ (1 : L))) γ hW σ (heq_vcHom γ W hW) hσ e' he'

end Generic

section CharTwo

variable {L : Type*} [Field L] [CharP L 2]

theorem two_eq_zero' : (2 : L) = 0 := by simpa using CharP.cast_eq_zero L 2

abbrev E2 (L : Type*) [Field L] : WeierstrassCurve L := ⟨0, 0, 1, 0, 0⟩

theorem E2_Δ : (E2 L).Δ = 1 := by
  have h2 := two_eq_zero' (L := L)
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (-14 : L) * h2

theorem isElliptic_E2 : (E2 L).IsElliptic := ⟨by rw [E2_Δ]; exact isUnit_one⟩

theorem E2_c₄ : (E2 L).c₄ = 0 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring

theorem smul_E2 (w : Lˣ) (hw : (w : L) ^ 3 = 1) : (⟨w, 0, 0, 0⟩ : VariableChange L) • E2 L = E2 L := by
  have h2 := two_eq_zero' (L := L)
  have hv3 : ((w⁻¹ : Lˣ) : L) ^ 3 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hw, inv_one]
  ext
  · simp [variableChange_a₁]
  · simp [variableChange_a₂]
  · simp only [variableChange_a₃]
    linear_combination hv3
  · simp [variableChange_a₄]
  · simp [variableChange_a₆]

end CharTwo

section CharTwoCase

variable {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]

theorem case_two (M : ℕ) [NeZero M] (hM : (M : L) ≠ 0) :
    ∃ (E₀ : WeierstrassCurve L) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange L)
      (P Q : E₀.toAffine.Point),
      E₀.j = 0 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P - Q) := by
  have h3 : (3 : L) ≠ 0 := by
    have h2 := two_eq_zero' (L := L)
    intro h; apply one_ne_zero (α := L); linear_combination h - h2
  obtain ⟨w, hw, hw1⟩ := exists_cube_root (K := L) h3
  have hE : (E2 L).IsElliptic := isElliptic_E2
  obtain ⟨σ, ι, hσpow, -, hσσ, -, hnsσ, -⟩ :=
    WeierstrassCurve.exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two w hw hw1 M hM

  set γ : VariableChange L := (⟨w, 0, 0, 0⟩ : VariableChange L) ^ 1 with hγdef
  have hγ : γ • E2 L = E2 L := by rw [hγdef, pow_one]; exact smul_E2 w hw
  have hheq : ∀ T : (E2 L).toAffine.Point, HEq (Point.vcInvFun γ (E2 L).toAffine T) (σ T) := fun T =>
    hσpow 1 T

  obtain ⟨e⟩ : Nonempty (ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ (E2 L).toAffine.Point M) := by
    have h := (E2 L).nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := L) hM
    rwa [baseChange_self] at h
  obtain ⟨e', he'⟩ :=
    AddCommGroup.exists_addEquiv_prod_torsionBy_apply_eq_of_forall_exists_ne_smul M e σ hnsσ
  exact finish_of_addEquiv M (E2 L) (WeierstrassCurve.j_eq_zero _ E2_c₄) γ hγ σ hheq hσσ e' he'

end CharTwoCase

section CharThree

variable {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] [CharP K 3]

theorem three_eq_zero' : (3 : K) = 0 := by simpa using CharP.cast_eq_zero K 3

abbrev E3 (K : Type*) [Field K] : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩

theorem E3_Δ : (E3 K).Δ = 1 := by
  have h3 := three_eq_zero' (K := K)
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (21 : K) * h3

theorem isElliptic_E3 : (E3 K).IsElliptic := ⟨by rw [E3_Δ]; exact isUnit_one⟩

theorem E3_c₄ : (E3 K).c₄ = 0 := by
  have h3 := three_eq_zero' (K := K)
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  linear_combination (16 : K) * h3

theorem case_three (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ (E₀ : WeierstrassCurve K) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange K)
      (P Q : E₀.toAffine.Point),
      E₀.j = 0 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P - Q) := by
  have h3 := three_eq_zero' (K := K)
  have h2 : (2 : K) ≠ 0 := by
    intro h; apply one_ne_zero (α := K); linear_combination h3 - h
  obtain ⟨i, hi⟩ := exists_sq_eq_neg_one (K := K) h2
  have hE : (E3 K).IsElliptic := isElliptic_E3
  obtain ⟨α, β, -, -, hαα, hββ, hαβ, -, hconv⟩ :=
    WeierstrassCurve.exists_addMonoidHom_i_tau_vcInvFun_of_char_three i hi

  obtain ⟨γ, hγ, hheq⟩ := hconv β (Or.inr (Or.inr (Or.inl rfl)))

  have hM3 : ¬ 3 ∣ M := by
    rintro ⟨c, hc⟩
    apply hM
    rw [hc, Nat.cast_mul, show ((3 : ℕ) : K) = 0 from CharP.cast_eq_zero K 3, zero_mul]

  obtain ⟨e⟩ : Nonempty (ZMod M × ZMod M ≃+ Submodule.torsionBy ℤ (E3 K).toAffine.Point M) := by
    have h := (E3 K).nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := K) hM
    rwa [baseChange_self] at h
  obtain ⟨⟨P, hPM, hPc⟩, -⟩ :=
    AddCommGroup.exists_torsionBy_coords_of_dicyclic_relations M hM3 e α β hαα hββ hαβ
  refine finish M (E3 K) (WeierstrassCurve.j_eq_zero _ E3_c₄) γ hγ β hheq hββ P
    (by rw [← natCast_zsmul]; exact hPM) fun T hT => ?_
  have h := hPc T (by rw [natCast_zsmul]; exact hT)
  exact (existsUnique_congr fun c => eq_comm).mp h

end CharThree


section OrderFour

variable {L : Type*} [Field L] [DecidableEq L]

theorem xy_neg {W : WeierstrassCurve L} (P : W.toAffine.Point) :
    xy (-P) = (xy P).map (fun q => (q.1, W.toAffine.negY q.1 q.2)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Affine.Point.neg_some]; rfl

theorem xco_eq_map_xy {W : WeierstrassCurve L} (P : W.toAffine.Point) : xco P = (xy P).map Prod.fst := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

theorem natDegree_Phi_add_X_mul_PsiSq_le (W : WeierstrassCurve L) (m : ℕ) (hm : 1 ≤ m) :
    (W.Φ (m : ℤ) + X * W.ΨSq (m : ℤ)).natDegree ≤ m ^ 2 := by
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · have hΦ := W.natDegree_Φ_le (m : ℤ)
    simp only [Int.natAbs_natCast] at hΦ
    exact hΦ
  · refine (natDegree_mul_le).trans ?_
    have hΨ := W.natDegree_ΨSq_le (m : ℤ)
    simp only [Int.natAbs_natCast] at hΨ
    have hX : (X : L[X]).natDegree ≤ 1 := natDegree_X_le
    omega

abbrev EA (A : L) : WeierstrassCurve L := ⟨0, 0, 0, A, 0⟩

theorem EA_Δ (A : L) : (EA A).Δ = -64 * A ^ 3 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]; ring

theorem EA_c₄ (A : L) : (EA A).c₄ = -48 * A := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]; ring

theorem isElliptic_EA (A : L) (hA : A ≠ 0) (h2 : (2 : L) ≠ 0) : (EA A).IsElliptic := by
  refine ⟨?_⟩
  rw [EA_Δ, isUnit_iff_ne_zero]
  have h64 : (64 : L) ≠ 0 := by
    rw [show (64 : L) = 2 ^ 6 by norm_num]
    exact pow_ne_zero _ h2
  exact mul_ne_zero (neg_ne_zero.mpr h64) (pow_ne_zero 3 hA)

theorem EA_j (A : L) (hA : A ≠ 0) (h2 : (2 : L) ≠ 0) :
    @WeierstrassCurve.j L _ (EA A) (isElliptic_EA A hA h2) = 1728 := by
  have := isElliptic_EA A hA h2
  have h64 : (64 : L) ≠ 0 := by
    rw [show (64 : L) = 2 ^ 6 by norm_num]
    exact pow_ne_zero _ h2
  have hΔ0 : (-64 * A ^ 3 : L) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h64) (pow_ne_zero 3 hA)
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', EA_c₄, EA_Δ]
  field_simp
  ring

theorem exists_torsion_equiv [IsAlgClosed L] (W : WeierstrassCurve L) [W.IsElliptic] {n : ℕ}
    (hn : (n : L) ≠ 0) : Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ W.toAffine.Point n) := by
  have h := W.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed (K := L) hn
  rwa [baseChange_self] at h

end OrderFour

namespace OrderFour

variable {L : Type*} [Field L] [DecidableEq L]

theorem exists_addOrderOf_eq_and_ne_nsmul [IsAlgClosed L] (A : L) (hA : A ≠ 0) (h2 : (2 : L) ≠ 0)
    (σ : (EA A).toAffine.Point →+ (EA A).toAffine.Point)
    (hσx : ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y), xco (σ (Point.some x y h)) = some (-x))
    (hσ : ∀ P : (EA A).toAffine.Point, σ (σ P) = -P)
    (p : ℕ) (hp : p.Prime) (hpL : (p : L) ≠ 0) :
    ∃ T : (EA A).toAffine.Point, addOrderOf T = p ∧ ∀ k : ℕ, σ T ≠ k • T := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hE : (EA A).IsElliptic := isElliptic_EA A hA h2
  have hσ0 : ∀ P : (EA A).toAffine.Point, σ P = 0 ↔ P = 0 := fun P =>
    ⟨fun h0 => by have := hσ P; rw [h0, map_zero] at this; exact neg_eq_zero.mp this.symm,
     fun h0 => by rw [h0, map_zero]⟩

  suffices core : ∃ (x y : L) (h : (EA A).toAffine.Nonsingular x y), addOrderOf (Point.some x y h) = p ∧
      ∀ k : ℕ, xco (k • Point.some x y h) ≠ some (-x) by
    obtain ⟨x, y, h, hord, hk⟩ := core
    refine ⟨Point.some x y h, hord, fun k hk' => hk k ?_⟩
    rw [← hk', hσx]
  rcases hp.eq_two_or_odd' with rfl | hpodd
  ·
    obtain ⟨a, ha⟩ : ∃ a : L, a ^ 2 = -A := by
      obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-A) (n := 2) (by norm_num)
      exact ⟨a, ha⟩
    have ha0 : a ≠ 0 := by rintro rfl; apply hA; simpa using ha.symm
    have heq : (EA A).toAffine.Equation a 0 := by
      rw [WeierstrassCurve.Affine.equation_iff]; simp; linear_combination -a * ha
    have hns : (EA A).toAffine.Nonsingular a 0 := by
      rw [WeierstrassCurve.Affine.nonsingular_iff']
      refine ⟨heq, Or.inl ?_⟩
      show (0 : L) * 0 - (3 * a ^ 2 + 2 * 0 * a + A) ≠ 0
      intro h3a
      apply ha0
      have : (2 : L) * a ^ 2 = 0 := by linear_combination -h3a - ha
      simpa [h2] using this
    have hneg : -Point.some a 0 hns = Point.some a 0 hns := by
      rw [Point.neg_some]; congr 1; simp [WeierstrassCurve.Affine.negY]
    have h2T : (2 : ℕ) • Point.some a 0 hns = 0 := by
      rw [two_nsmul]; nth_rewrite 1 [← hneg]; rw [neg_add_cancel]
    have hord : addOrderOf (Point.some a 0 hns) = 2 :=
      addOrderOf_eq_prime_iff.mpr ⟨h2T, Point.some_ne_zero hns⟩
    refine ⟨a, 0, hns, hord, fun k => ?_⟩
    have hkT : k • Point.some a 0 hns = 0 ∨ k • Point.some a 0 hns = Point.some a 0 hns := by
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · left; rw [← two_mul, mul_nsmul, h2T, nsmul_zero]
      · right; rw [add_nsmul, mul_nsmul, h2T, nsmul_zero, zero_add, one_nsmul]
    rcases hkT with h0 | h1
    · rw [h0, xco_zero]; simp
    · rw [h1, xco_some]; simp only [ne_eq, Option.some.injEq]
      intro h; apply ha0
      have : (2 : L) * a = 0 := by linear_combination h
      simpa [h2] using this
  ·
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      rcases this.eq_or_lt with h | h
      · exact absurd hpodd (by rw [← h]; decide)
      · omega

    let Ep := (Submodule.torsionBy ℤ (EA A).toAffine.Point p).toAddSubgroup
    have hEp_mem : ∀ T : (EA A).toAffine.Point, T ∈ Ep ↔ (p : ℤ) • T = 0 := fun T =>
      Submodule.mem_torsionBy_iff _ _
    obtain ⟨eb⟩ : Nonempty (ZMod p × ZMod p ≃+ Ep) := exists_torsion_equiv (EA A) hpL
    have hcard : Nat.card Ep = p ^ 2 := natCard_torsionBy_eq_sq eb
    by_contra hcon
    push Not at hcon

    have heig : ∀ T : (EA A).toAffine.Point, (p : ℤ) • T = 0 → ∃ a : ℤ, σ T = a • T := by
      intro T hpT
      rcases T with _ | ⟨x, y, h⟩
      · exact ⟨0, by rw [zero_smul]; exact map_zero σ⟩
      · have hord : addOrderOf (Point.some x y h) = p := by
          refine addOrderOf_eq_prime_iff.mpr ⟨?_, Point.some_ne_zero h⟩
          rw [← natCast_zsmul]; exact hpT
        obtain ⟨k, hk⟩ := hcon x y h hord
        have hx : xco (σ (Point.some x y h)) = xco (k • Point.some x y h) := by rw [hσx, hk]
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · exact ⟨k, by rw [h1, natCast_zsmul]⟩
        · exact ⟨-k, by rw [h1, neg_smul, natCast_zsmul]⟩
    have hσEp : ∀ T ∈ Ep, σ T ∈ Ep := by
      intro T hT
      rw [hEp_mem] at hT ⊢
      rw [← map_zsmul, hT, map_zero]
    let σ' : Ep →+ Ep := (σ.domRestrict Ep).codRestrict Ep (fun T => hσEp T T.2)
    have heig' : ∀ v : Ep, ∃ a : ℤ, σ' v = a • v := by
      rintro ⟨T, hT⟩
      obtain ⟨a, ha⟩ := heig T ((hEp_mem T).mp hT)
      exact ⟨a, Subtype.ext ha⟩
    obtain ⟨c, hc⟩ := exists_common_scalar eb σ' heig'

    obtain ⟨m, hm1, hmle, hmx⟩ : ∃ m : ℕ, 1 ≤ m ∧ 2 * m ≤ p - 1 ∧
        ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 →
          xco ((m : ℤ) • Point.some x y h) = some (-x) := by
      let r : ℕ := ((c : ZMod p)).val
      have hr : (r : ZMod p) = c := by simp [r]
      have hrp : r < p := ZMod.val_lt _
      have hσc : ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y), (p : ℤ) • Point.some x y h = 0 →
          σ (Point.some x y h) = (r : ℤ) • Point.some x y h := by
        intro x y h hpT
        have hT : Point.some x y h ∈ Ep := (hEp_mem _).mpr hpT
        have := hc ⟨_, hT⟩
        have hval : σ (Point.some x y h) = c • Point.some x y h := congrArg Subtype.val this
        rw [hval]
        obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (r : ℤ) c p).mp (by exact_mod_cast hr)
        have : c = r + p * k := by linarith
        rw [this, add_zsmul, mul_comm, mul_zsmul, hpT, zsmul_zero, add_zero]
      obtain ⟨x₀, y₀, h₀, hp₀⟩ : ∃ (x y : L) (h : (EA A).toAffine.Nonsingular x y),
          (p : ℤ) • Point.some x y h = 0 := by
        have h1 : 1 < Nat.card Ep := by rw [hcard]; nlinarith
        have : Finite Ep := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
        have : Nontrivial Ep := Finite.one_lt_card_iff_nontrivial.mp h1
        obtain ⟨⟨T, hT⟩, hT0⟩ := exists_ne (0 : Ep)
        rcases T with _ | ⟨x, y, h⟩
        · exact absurd rfl (fun h => hT0 (Subtype.ext h))
        · exact ⟨x, y, h, (hEp_mem _).mp hT⟩
      have hr0 : r ≠ 0 := by
        intro hr0
        have := hσc x₀ y₀ h₀ hp₀
        rw [hr0, Nat.cast_zero, zero_smul, hσ0] at this
        exact Point.some_ne_zero h₀ this
      by_cases hle : 2 * r ≤ p - 1
      · refine ⟨r, Nat.one_le_iff_ne_zero.mpr hr0, hle, fun x y h hpT => ?_⟩
        rw [← hσc x y h hpT, hσx]
      · obtain ⟨k0, hk0⟩ := hpodd
        refine ⟨p - r, by omega, by omega, fun x y h hpT => ?_⟩
        have : ((p - r : ℕ) : ℤ) • Point.some x y h = -((r : ℤ) • Point.some x y h) := by
          rw [Nat.cast_sub hrp.le, sub_zsmul, hpT]; simp
        rw [this, xco_neg, ← hσc x y h hpT, hσx]

    set F : L[X] := (EA A).Φ (m : ℤ) + X * (EA A).ΨSq (m : ℤ) with hFdef
    have hFdeg : F.natDegree ≤ m ^ 2 := natDegree_Phi_add_X_mul_PsiSq_le (EA A) m hm1

    have hxm : ∀ (q : ℕ), q.Prime → m < q → ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y),
        (q : ℤ) • Point.some x y h = 0 →
        ((EA A).ΨSq (m : ℤ)).eval x ≠ 0 ∧
          xco ((m : ℤ) • Point.some x y h) =
            some (((EA A).Φ (m : ℤ)).eval x / ((EA A).ΨSq (m : ℤ)).eval x) := by
      intro q hq hmq x y h hqT
      have : Fact q.Prime := ⟨hq⟩
      have hord : addOrderOf (Point.some x y h) = q :=
        addOrderOf_eq_prime_iff.mpr ⟨by rw [← natCast_zsmul]; exact hqT, Point.some_ne_zero h⟩
      have hmT : (m : ℤ) • Point.some x y h ≠ 0 := by
        rw [natCast_zsmul]
        intro h0
        have hdvd := addOrderOf_dvd_of_nsmul_eq_zero h0
        rw [hord] at hdvd
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      have hψ : ((EA A).ψ (m : ℤ)).evalEval x y ≠ 0 := fun h0 =>
        hmT ((WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff (EA A) h (m : ℤ)).mpr h0)
      obtain ⟨y', h', hmul⟩ := WeierstrassCurve.Affine.Point.zsmul_some_eq_some_div (EA A) h hψ
      refine ⟨?_, by rw [hmul, xco_some]⟩
      rw [← WeierstrassCurve.Affine.evalEval_psi_sq (EA A) h.1 (m : ℤ)]; exact pow_ne_zero 2 hψ

    have hF0 : F ≠ 0 := by
      intro hF

      obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (max (m ^ 2 + 2) (ringChar L + 1))
      have hqm : m ^ 2 + 1 < q := by have := le_max_left (m ^ 2 + 2) (ringChar L + 1); omega
      have hqc : ringChar L < q := by have := le_max_right (m ^ 2 + 2) (ringChar L + 1); omega
      have hqL : (q : L) ≠ 0 := by
        intro h0
        have hdvd : ringChar L ∣ q := (ringChar.spec L q).mp h0
        rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
        · exact CharP.ringChar_ne_one h1
        · omega
      have : Fact q.Prime := ⟨hq⟩
      have : NeZero q := ⟨hq.ne_zero⟩

      obtain ⟨eq'⟩ := exists_torsion_equiv (EA A) hqL
      have hcardq : Nat.card (Submodule.torsionBy ℤ (EA A).toAffine.Point q) = q ^ 2 :=
        natCard_torsionBy_eq_sq eq'
      obtain ⟨x₀, y₀, h₀, hq₀⟩ : ∃ (x y : L) (h : (EA A).toAffine.Nonsingular x y),
          (q : ℤ) • Point.some x y h = 0 := by
        let Eq' := (Submodule.torsionBy ℤ (EA A).toAffine.Point q).toAddSubgroup
        have hq1 : 1 < q := hq.one_lt
        have h1 : 1 < Nat.card Eq' := by rw [show Nat.card Eq' = q ^ 2 from hcardq]; nlinarith
        have : Finite Eq' :=
          Nat.finite_of_card_ne_zero (by rw [show Nat.card Eq' = q ^ 2 from hcardq]; positivity)
        have : Nontrivial Eq' := Finite.one_lt_card_iff_nontrivial.mp h1
        obtain ⟨⟨T, hT⟩, hT0⟩ := exists_ne (0 : Eq')
        rcases T with _ | ⟨x, y, h⟩
        · exact absurd rfl (fun h => hT0 (Subtype.ext h))
        · exact ⟨x, y, h, (Submodule.mem_torsionBy_iff _ _).mp hT⟩
      have hordq : addOrderOf (Point.some x₀ y₀ h₀) = q :=
        addOrderOf_eq_prime_iff.mpr ⟨by rw [← natCast_zsmul]; exact hq₀, Point.some_ne_zero h₀⟩

      have hm2q : m < q := by nlinarith
      obtain ⟨hΨ, hxq⟩ := hxm q hq hm2q x₀ y₀ h₀ hq₀
      have hΦ : ((EA A).Φ (m : ℤ)).eval x₀ = -x₀ * ((EA A).ΨSq (m : ℤ)).eval x₀ := by
        have := congrArg (Polynomial.eval x₀) hF
        rw [hFdef, eval_zero, eval_add, eval_mul, eval_X] at this
        linear_combination this
      have hx : xco (σ (Point.some x₀ y₀ h₀)) = xco ((m : ℤ) • Point.some x₀ y₀ h₀) := by
        rw [hσx, hxq, hΦ, mul_div_assoc, div_self hΨ, mul_one]

      obtain ⟨a, ha, haT⟩ : ∃ a : ℤ, (a = m ∨ a = -m) ∧
          σ (Point.some x₀ y₀ h₀) = a • Point.some x₀ y₀ h₀ := by
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · exact ⟨m, Or.inl rfl, h1⟩
        · exact ⟨-m, Or.inr rfl, by rw [h1, neg_smul]⟩

      have hkill : (a * a + 1) • Point.some x₀ y₀ h₀ = 0 := by
        have := hσ (Point.some x₀ y₀ h₀)
        rw [haT, map_zsmul, haT, smul_smul] at this
        rw [add_smul, one_smul, this, neg_add_cancel]
      have hdvd : ((q : ℕ) : ℤ) ∣ a * a + 1 := by
        rw [← hordq]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkill
      have hpos : 0 < a * a + 1 := by nlinarith
      have hle := Int.le_of_dvd hpos hdvd
      have hqm' : ((m : ℤ)) ^ 2 + 1 < q := by exact_mod_cast hqm
      rcases ha with rfl | rfl <;> nlinarith
    have hroot : ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y),
        (p : ℤ) • Point.some x y h = 0 → F.IsRoot x := by
      intro x y h hpT
      obtain ⟨hΨ, hxp⟩ := hxm p hp (by omega) x y h hpT
      have hx : xco ((m : ℤ) • Point.some x y h) = some (-x) := hmx x y h hpT
      rw [hxp, Option.some.injEq, div_eq_iff hΨ] at hx
      show F.eval x = 0
      rw [hFdef, eval_add, eval_mul, eval_X]
      linear_combination hx

    have hfinEp : Finite Ep := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    have : Fintype Ep := Fintype.ofFinite Ep
    classical
    let g : Ep → Option L := fun T => xco (T.1 : (EA A).toAffine.Point)
    let s : Finset Ep := Finset.univ.filter (fun T => T ≠ 0)
    have hs_card : s.card = p ^ 2 - 1 := by
      have : s.card + 1 = p ^ 2 := by
        rw [show s = Finset.univ.erase 0 by ext T; simp [s], Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
        have : 1 ≤ p ^ 2 := Nat.one_le_iff_ne_zero.mpr (by positivity); omega
      omega
    have hfib : ∀ b ∈ s.image g, (s.filter (fun T => g T = b)).card ≤ 2 := by
      intro b hb
      obtain ⟨T₁, hT₁, rfl⟩ := Finset.mem_image.mp hb
      have hsub : s.filter (fun T => g T = g T₁) ⊆ {T₁, -T₁} := by
        intro T hT
        rw [Finset.mem_filter] at hT
        have hx : xco (T.1 : (EA A).toAffine.Point) = xco (T₁.1 : (EA A).toAffine.Point) := hT.2
        rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
        · rw [Finset.mem_insert]; left; exact Subtype.ext h1
        · rw [Finset.mem_insert, Finset.mem_singleton]; right
          exact Subtype.ext (by rw [h1]; rfl)
      exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
    have hle : s.card ≤ 2 * (s.image g).card := Finset.card_le_mul_card_image s 2 hfib
    have himg : s.image g ⊆ (F.roots.toFinset).image some := by
      intro b hb
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hb
      rw [Finset.mem_filter] at hT
      obtain ⟨⟨T, hTp⟩, hT0⟩ := T, hT.2
      rcases T with _ | ⟨x, y, h⟩
      · exact absurd rfl (fun h => hT0 (Subtype.ext h))
      · refine Finset.mem_image.mpr ⟨x, ?_, rfl⟩
        rw [Multiset.mem_toFinset, mem_roots hF0]
        exact hroot x y h ((hEp_mem _).mp hTp)
    have hR : ((F.roots.toFinset).image some).card ≤ m ^ 2 := by
      refine Finset.card_image_le.trans ((Multiset.toFinset_card_le _).trans ?_)
      exact (Polynomial.card_roots' F).trans hFdeg
    have hfinal : p ^ 2 - 1 ≤ 2 * m ^ 2 := by
      rw [← hs_card]; exact hle.trans (Nat.mul_le_mul_left 2 ((Finset.card_le_card himg).trans hR))
    have h4 : 4 * m ^ 2 ≤ (p - 1) ^ 2 := by nlinarith
    have hp1 : 1 ≤ p := hp.one_lt.le
    zify [hp1, Nat.one_le_iff_ne_zero.mpr (show p ^ 2 ≠ 0 by positivity)] at hfinal h4 hmle
    nlinarith

end OrderFour

section MainTwoNeZero

variable {L : Type*} [Field L] [DecidableEq L]

theorem main_of_two_ne_zero [IsAlgClosed L] (M : ℕ) [NeZero M] (hM : (M : L) ≠ 0)
    (h2 : (2 : L) ≠ 0) :
    ∃ (E₀ : WeierstrassCurve L) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange L)
      (P Q : E₀.toAffine.Point),
      E₀.j = 1728 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P) := by

  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : L) (n := 2) (by norm_num)
  have hi0 : i ≠ 0 := by
    rintro rfl
    have : (1 : L) = 0 := by
      have h := hi; simp at h
    exact one_ne_zero this
  let u : Lˣ := Units.mk0 i hi0
  have hu : (u : L) ^ 2 = -1 := hi

  have hE : (EA (1 : L)).IsElliptic := isElliptic_EA 1 one_ne_zero h2
  have hW : (⟨u, 0, 0, 0⟩ : VariableChange L) • EA (1 : L) = EA 1 :=
    WeierstrassCurve.variableChange_mk_smul_eq_self_of_sq_eq_neg_one u hu 1
  let σ : (EA (1 : L)).toAffine.Point →+ (EA (1 : L)).toAffine.Point := vcHom ⟨u, 0, 0, 0⟩ (EA 1) hW
  have hi2 : ((u⁻¹ : Lˣ) : L) ^ 2 = -1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_neg, inv_one]

  have hσ : ∀ P : (EA (1 : L)).toAffine.Point, σ (σ P) = -P := by
    intro P
    apply xy_injective
    rw [xy_vcHom, xy_vcHom, xy_neg]
    rcases xy P with _ | ⟨x, y⟩
    · rfl
    · simp only [Option.map_some, vcXInv, vcYInv, Affine.negY, sub_zero, zero_mul,
        Option.some.injEq, Prod.mk.injEq]
      constructor
      · linear_combination (((u⁻¹ : Lˣ) : L) ^ 2 * x - x) * hi2
      · linear_combination (((u⁻¹ : Lˣ) : L) ^ 4 * y - ((u⁻¹ : Lˣ) : L) ^ 2 * y + y) * hi2

  have hσx : ∀ (x y : L) (h : (EA (1 : L)).toAffine.Nonsingular x y),
      xco (σ (Point.some x y h)) = some (-x) := by
    intro x y h
    rw [xco_eq_map_xy, xy_vcHom]
    simp only [xy, Option.map_some, vcXInv, sub_zero, hi2, Option.some.injEq]
    ring

  have hns : ∀ p : ℕ, p.Prime → p ∣ M →
      ∃ a : (EA (1 : L)).toAffine.Point, addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a := by
    intro p hp hpM
    have hpL : (p : L) ≠ 0 := by
      obtain ⟨c, rfl⟩ := hpM
      intro h0; apply hM; push_cast; rw [h0, zero_mul]
    exact OrderFour.exists_addOrderOf_eq_and_ne_nsmul 1 one_ne_zero h2 σ hσx hσ p hp hpL

  obtain ⟨e⟩ := exists_torsion_equiv (EA (1 : L)) hM
  exact assemble M (EA 1) hE (EA_j 1 one_ne_zero h2) ⟨u, 0, 0, 0⟩ hW σ
    (heq_vcHom ⟨u, 0, 0, 0⟩ (EA 1) hW) hσ hns e

end MainTwoNeZero

section CharTwoOrderFour

variable {K : Type*} [Field K] [DecidableEq K]

theorem E2_j [CharP K 2] : @WeierstrassCurve.j K _ (E2 K) isElliptic_E2 = 1728 := by
  have hinst : (E2 K).IsElliptic := isElliptic_E2
  have h2 : (2 : K) = 0 := two_eq_zero' (L := K)
  have h1728 : (1728 : K) = 0 := by linear_combination (864 : K) * h2
  rw [WeierstrassCurve.j, E2_c₄, h1728]
  ring

theorem exists_omega (K : Type*) [Field K] [IsAlgClosed K] : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K)
    (by
      have : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial K).degree = 2 := by compute_degree!
      rw [this]; norm_num)
  exact ⟨ω, by simpa using hω⟩

theorem heq_vcInvFun_of_eq {C C' : VariableChange K} (h : C = C') (W : WeierstrassCurve K)
    (P : W.toAffine.Point) :
    HEq (Point.vcInvFun C W.toAffine P) (Point.vcInvFun C' W.toAffine P) := by
  subst h; exact HEq.rfl

end CharTwoOrderFour

namespace OrderFour

variable {K : Type*} [Field K]

theorem E2_Δ [CharP K 2] : (E2 K).Δ = 1 := by
  have h2 : (2 : K) = 0 := two_eq_zero' (L := K)
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  linear_combination (-14 : K) * h2

theorem isElliptic_E2 [CharP K 2] : (E2 K).IsElliptic := ⟨by rw [E2_Δ]; exact isUnit_one⟩

theorem smul_E2 [CharP K 2] (w : K) (hw : w ^ 2 + w + 1 = 0) :
    (⟨1, 1, 1, w⟩ : VariableChange K) • E2 K = E2 K := by
  have h2 : (2 : K) = 0 := two_eq_zero' (L := K)
  ext
  · simp only [variableChange_a₁, inv_one, Units.val_one]; linear_combination h2
  · simp only [variableChange_a₂, inv_one, Units.val_one]; linear_combination h2
  · simp only [variableChange_a₃, inv_one, Units.val_one]; linear_combination w * h2
  · simp only [variableChange_a₄, inv_one, Units.val_one]; linear_combination (1 - w) * h2
  · simp only [variableChange_a₆, inv_one, Units.val_one]; linear_combination -hw + h2

end OrderFour

section MainCharTwo

variable {K : Type*} [Field K] [DecidableEq K]

theorem main_of_charTwo [IsAlgClosed K] [CharP K 2] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ (E₀ : WeierstrassCurve K) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange K)
      (P Q : E₀.toAffine.Point),
      E₀.j = 1728 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P) := by
  have h2 : (2 : K) = 0 := two_eq_zero'

  obtain ⟨w, hw⟩ := exists_omega K
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hw1 : w ≠ 1 := by
    intro h
    rw [h] at hw
    have : (1 : K) = 0 := by linear_combination hw - h2
    exact one_ne_zero this
  have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  let wu : Kˣ := Units.mk0 w hw0
  have hwu : (wu : K) = w := rfl

  obtain ⟨-, ι, -, hιk, -, hιι, -, hnsι⟩ :=
    WeierstrassCurve.exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two
      wu (by rw [hwu]; exact hw3) (by rw [hwu]; exact hw1) M hM
  have hC : (⟨1, 1, 1, (wu : K)⟩ : VariableChange K) • E2 K = E2 K := OrderFour.smul_E2 w hw
  have hheq : ∀ T : (E2 K).toAffine.Point,
      HEq (Point.vcInvFun (⟨1, 1, 1, (wu : K)⟩ : VariableChange K) (E2 K).toAffine T) (ι T) := by
    intro T
    have h := hιk 1 T
    rw [Function.iterate_one] at h
    exact (heq_vcInvFun_of_eq (pow_one _).symm (E2 K) T).trans h
  have hE : (E2 K).IsElliptic := isElliptic_E2
  obtain ⟨e⟩ := exists_torsion_equiv (E2 K) hM
  exact assemble M (E2 K) hE E2_j ⟨1, 1, 1, (wu : K)⟩ hC ι hheq hιι hnsι e

end MainCharTwo

end WeierstrassCurve.Automorphism

namespace WeierstrassCurve

theorem exists_j_eq_zero_torsion_basis_heq_vcInvFun_of_order_three
    (K : Type*) [Field K] [DecidableEq K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ (E₀ : WeierstrassCurve K) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange K)
      (P Q : E₀.toAffine.Point),
      E₀.j = 0 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P - Q) := by
  by_cases h2 : (2 : K) = 0
  · have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h2)
    exact Automorphism.case_two M hM
  by_cases h3 : (3 : K) = 0
  · have : CharP K 3 := (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr (by exact_mod_cast h3)
    exact Automorphism.case_three M hM
  exact Automorphism.case_generic M hM h2 h3

theorem exists_j_eq_1728_torsion_basis_heq_vcInvFun_of_order_four
    (K : Type*) [Field K] [DecidableEq K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0) :
    ∃ (E₀ : WeierstrassCurve K) (_ : E₀.IsElliptic) (σ : WeierstrassCurve.VariableChange K)
      (P Q : E₀.toAffine.Point),
      E₀.j = 1728 ∧ σ • E₀ = E₀ ∧ M • P = 0 ∧ M • Q = 0 ∧
      (∀ T : E₀.toAffine.Point, M • T = 0 →
        ∃! c : ZMod M × ZMod M, T = c.1.val • P + c.2.val • Q) ∧
      HEq (Point.vcInvFun σ E₀.toAffine P) Q ∧
      HEq (Point.vcInvFun σ E₀.toAffine Q) (-P) := by
  by_cases h2 : (2 : K) = 0
  · have : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by exact_mod_cast h2)
    exact Automorphism.main_of_charTwo M hM
  · exact Automorphism.main_of_two_ne_zero M hM h2

end WeierstrassCurve
