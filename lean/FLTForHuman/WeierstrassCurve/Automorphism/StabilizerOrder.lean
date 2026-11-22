/-
  The order of the automorphism group of a Weierstrass curve.

  The stabilizer `MulAction.stabilizer (WeierstrassCurve.VariableChange F) E` of an elliptic curve
  in the group of variable changes is finite (the port holds that in
  `Automorphism/NormalForm.lean`); here is its *order*:

    `j = 0` and `6 ≠ 0`        → `Nat.card ≤ 6`,
    `j = 1728` and `6 ≠ 0`     → `Nat.card ≤ 4`,
    `j = 0` and `ringChar F = 3` → `Nat.card ≤ 12`,
    `j = 0` and `ringChar F = 2` → `Nat.card ≤ 24`,

  and away from the two exceptional `j`-invariants the order is exactly `2`, both in residue
  characteristic `≠ 2, 3` and in characteristic `2` or `3`.  (The `j = 0` / `j = 1728` cases are the
  curves with extra automorphisms `ζ₃` and `i`; the characteristic-2 and characteristic-3 bounds are
  the ones that grow because the group scheme degenerates.)

  Transcribed from the three pins below (pinned `aa2d8b3`, 496 + 256 + 187 lines), all public: the
  496-line pin is a 35-declaration flattened file and the other two are 26 and 4 declarations.
  The pins' label namespaces (`AutCardCharTwoThree` and friends) are rectified to subject names.

  Assumes mathlib's variable-change action (`Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange`,
  `WeierstrassCurve.VariableChange`, `E.j`), mathlib's normal forms
  (`Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms`: `IsShortNF`, `IsCharTwoJEqZeroNF`,
  `IsCharThreeJNeZeroNF`, `toShortNF`, `exists_variableChange_is*NF`) and the port's finiteness row
  (`Automorphism/NormalForm.lean`'s `finite_stabilizer_variableChange`) and the exceptional
  automorphisms of `Automorphism/{CharTwo,CharThree}.lean`.  The pins' `P2M.Util` import, their
  `p2m_reactivate` lines and their `set_option synthInstance.maxHeartbeats` / `maxHeartbeats` bumps
  are not transcribed.

  Engine: `WeierstrassCurve.Automorphism.*` — the pins' label namespaces (`P2MKcAutBound`, `K2L1`,
  `AutCardCharTwoThree`) rectified to one subject namespace, the declaration last names kept.  Three
  of the 65 pin declarations are `private` (`three_eq_zero`, `two_ne_zero'`, `two_eq_zero`) and
  `check_port` does not diff a `private` declaration, so the module reads 62 ok = the 3 headlines
  plus the 59 public engine rows.

  Heartbeat probe (`lake env lean -DautoImplicit=false -DmaxHeartbeats=N` on this file, recorded and
  **never installed**, FR-0225): silent at **N = 6000**, first failure at **5000** — a
  `(deterministic) timeout at whnf` / `«tactic execution»` in the closing `linear_combination` rows
  of `Automorphism.stab_of_char_two`.  The edit loop's default `200000` is silent with ≳ 30× headroom,
  so this module carries no `set_option maxHeartbeats`.

  `tools/deps/dedup.py --within` reports two `shape` clusters, both **the pin's own pairs** and both
  kept: `c3_jne_card` / `c2_jne_card` (pin `…_char_two_or_three.lean:116` and `:212`) and
  `card_stabilizer_char_three` / `card_stabilizer_char_two` (`:139` and `:227`).  Their *statements*
  agree only in shape ("the stabilizer has `2` elements"): the two halves of the pin sit over
  different normal-form classes (`IsCharThreeJNeZeroNF` vs `IsCharTwoJNeZeroNF`), different
  `IsChar{Three,Two}NF` case splits, and different witnesses for the non-trivial element
  (`ofUnit (-1)` vs the characteristic-`2` `sigma = ⟨1, 0, 1, 0⟩`); the pins state them separately,
  so generalising them would invent a shared abstraction the pin does not have.  `move_dead` reads
  `0 declarations, 0 lines` — the three `private` helpers are live, so nothing is shelved.

  spec-pin: Theorems/Thm_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three.lean
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

set_option autoImplicit false

-- The pins' `letI`/`haveI` walls feed instance search (`Invertible (2 : F)`, the normal-form
-- classes of the variable change), so the style linter's `have`/`let` rewrite does not apply.
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open WeierstrassCurve Polynomial

namespace WeierstrassCurve

namespace Automorphism

section General

variable {F : Type*} [Field F]

lemma stabilizer_smul_natCard (C : VariableChange F) (W : WeierstrassCurve F) :
    Nat.card (MulAction.stabilizer (VariableChange F) (C • W)) =
      Nat.card (MulAction.stabilizer (VariableChange F) W) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj C).injective

lemma stabilizer_smul_finite_iff (C : VariableChange F) (W : WeierstrassCurve F) :
    Finite (MulAction.stabilizer (VariableChange F) (C • W)) ↔
      Finite (MulAction.stabilizer (VariableChange F) W) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact (Equiv.finite_iff (Subgroup.equivMapOfInjective _ _ (MulAut.conj C).injective).toEquiv).symm

lemma bound_of_smul (C : VariableChange F) (W : WeierstrassCurve F) (k : ℕ)
    (h : Finite (MulAction.stabilizer (VariableChange F) (C • W)) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) (C • W)) ≤ k) :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ k :=
  ⟨(stabilizer_smul_finite_iff C W).mp h.1, (stabilizer_smul_natCard C W) ▸ h.2⟩

lemma bound_of_injective {β : Type*} (W : WeierstrassCurve F) (T : Finset β)
    (f : MulAction.stabilizer (VariableChange F) W → β) (hf : Function.Injective f)
    (hT : ∀ x, f x ∈ T) :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ T.card := by
  let g : MulAction.stabilizer (VariableChange F) W → T := fun x => ⟨f x, hT x⟩
  have hg : Function.Injective g := fun x y h => hf (congrArg Subtype.val h)
  haveI : Finite (MulAction.stabilizer (VariableChange F) W) := Finite.of_injective g hg
  refine ⟨inferInstance, ?_⟩
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective g hg

def rootsOfUnityFinset [DecidableEq F] (n : ℕ) : Finset F := (nthRoots n (1 : F)).toFinset

lemma mem_rootsOfUnityFinset [DecidableEq F] {n : ℕ} (hn : 0 < n) {x : F} (hx : x ^ n = 1) :
    x ∈ rootsOfUnityFinset (F := F) n := by
  rw [rootsOfUnityFinset, Multiset.mem_toFinset, mem_nthRoots hn]; exact hx

lemma card_rootsOfUnityFinset_le [DecidableEq F] (n : ℕ) : (rootsOfUnityFinset (F := F) n).card ≤ n :=
  (Multiset.toFinset_card_le _).trans (card_nthRoots n 1)

def rootFinset [DecidableEq F] (q : F[X]) : Finset F := q.roots.toFinset

lemma mem_rootFinset [DecidableEq F] {q : F[X]} (hq : q ≠ 0) {x : F} (hx : q.eval x = 0) :
    x ∈ rootFinset q := by
  rw [rootFinset, Multiset.mem_toFinset, mem_roots hq]; exact hx

lemma card_rootFinset_le [DecidableEq F] (q : F[X]) : (rootFinset q).card ≤ q.natDegree :=
  (Multiset.toFinset_card_le _).trans (card_roots' q)

lemma pow_eq_one_of_inv_pow_mul_eq {u : Fˣ} {n : ℕ} {a : F} (ha : a ≠ 0)
    (h : ((u⁻¹ : Fˣ) : F) ^ n * a = a) : (u : F) ^ n = 1 := by
  have h1 : ((u⁻¹ : Fˣ) : F) ^ n = 1 := by
    have := mul_right_cancel₀ ha (h.trans (one_mul a).symm)
    exact this
  rw [Units.val_inv_eq_inv_val, inv_pow] at h1
  exact inv_eq_one.mp h1

end General

section Short

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF]

lemma rst_of_short (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {C : VariableChange F} (hC : C • W = W) :
    C.r = 0 ∧ C.s = 0 ∧ C.t = 0 := by
  have hu : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have h₁ := congrArg WeierstrassCurve.a₁ hC
  have h₂ := congrArg WeierstrassCurve.a₂ hC
  have h₃ := congrArg WeierstrassCurve.a₃ hC
  rw [variableChange_a₁, W.a₁_of_isShortNF] at h₁
  rw [variableChange_a₂, W.a₁_of_isShortNF, W.a₂_of_isShortNF] at h₂
  rw [variableChange_a₃, W.a₁_of_isShortNF, W.a₃_of_isShortNF] at h₃
  have hs : C.s = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) * (2 * C.s) = 0 := by linear_combination h₁
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hu
    · exact (mul_eq_zero.mp h).resolve_left h2
  have ht : C.t = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) ^ 3 * (2 * C.t) = 0 := by linear_combination h₃
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · exact (mul_eq_zero.mp h).resolve_left h2
  have hr : C.r = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) ^ 2 * (3 * C.r) = 0 := by
      rw [hs] at h₂; linear_combination h₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · exact (mul_eq_zero.mp h).resolve_left h3
  exact ⟨hr, hs, ht⟩

lemma u_pow_six_of_short (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha₆ : W.a₆ ≠ 0)
    {C : VariableChange F} (hC : C • W = W) : (C.u : F) ^ 6 = 1 := by
  obtain ⟨hr, hs, ht⟩ := rst_of_short W h2 h3 hC
  have h₆ := congrArg WeierstrassCurve.a₆ hC
  rw [variableChange_a₆, hr, ht] at h₆
  apply pow_eq_one_of_inv_pow_mul_eq ha₆
  linear_combination h₆

lemma u_pow_four_of_short (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (ha₄ : W.a₄ ≠ 0)
    {C : VariableChange F} (hC : C • W = W) : (C.u : F) ^ 4 = 1 := by
  obtain ⟨hr, hs, ht⟩ := rst_of_short W h2 h3 hC
  have h₄ := congrArg WeierstrassCurve.a₄ hC
  rw [variableChange_a₄, hr, hs, ht, W.a₃_of_isShortNF] at h₄
  apply pow_eq_one_of_inv_pow_mul_eq ha₄
  linear_combination h₄

lemma bound_short (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) {n : ℕ} (hn : 0 < n)
    (hpow : ∀ C : VariableChange F, C • W = W → (C.u : F) ^ n = 1) :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ n := by
  have h := bound_of_injective W (rootsOfUnityFinset (F := F) n)
    (fun C => ((C : VariableChange F).u : F)) ?_ ?_
  · exact ⟨h.1, h.2.trans (card_rootsOfUnityFinset_le n)⟩
  · rintro ⟨C, hC⟩ ⟨C', hC'⟩ h
    obtain ⟨hr, hs, ht⟩ := rst_of_short W h2 h3 (MulAction.mem_stabilizer_iff.mp hC)
    obtain ⟨hr', hs', ht'⟩ := rst_of_short W h2 h3 (MulAction.mem_stabilizer_iff.mp hC')
    apply Subtype.ext
    apply VariableChange.ext
    · exact Units.ext h
    · rw [hr, hr']
    · rw [hs, hs']
    · rw [ht, ht']
  · rintro ⟨C, hC⟩
    exact mem_rootsOfUnityFinset hn (hpow C (MulAction.mem_stabilizer_iff.mp hC))

lemma four_a₄_cube_add_ne_zero : 4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2 ≠ 0 := by
  intro h
  apply W.isUnit_Δ.ne_zero
  rw [W.Δ_of_isShortNF, h, mul_zero]

lemma a₄_eq_zero_of_j_eq_zero (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hj : W.j = 0) : W.a₄ = 0 := by
  rw [W.j_of_isShortNF, div_eq_zero_iff] at hj
  rcases hj with h | h
  · have h6912 : (6912 : F) ≠ 0 := by
      rw [show (6912 : F) = 2 ^ 8 * 3 ^ 3 by norm_num]
      exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
    exact pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ((mul_eq_zero.mp h).resolve_left h6912)
  · exact absurd h (four_a₄_cube_add_ne_zero W)

lemma a₆_eq_zero_of_j_eq_1728 (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) (hj : W.j = 1728) :
    W.a₆ = 0 := by
  rw [W.j_of_isShortNF, div_eq_iff (four_a₄_cube_add_ne_zero W)] at hj
  have h : (46656 : F) * W.a₆ ^ 2 = 0 := by linear_combination -hj
  have h46656 : (46656 : F) ≠ 0 := by
    rw [show (46656 : F) = 2 ^ 6 * 3 ^ 6 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ((mul_eq_zero.mp h).resolve_left h46656)

end Short

section CharThree

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 3] (W : WeierstrassCurve F) [W.IsElliptic]
  [W.IsShortNF]

def rPoly (u : F) : F[X] := X ^ 3 + C W.a₄ * X + C (W.a₆ * (1 - u ^ 6))

lemma rPoly_ne_zero (u : F) : rPoly W u ≠ 0 := by
  have : (rPoly W u).Monic := by unfold rPoly; monicity!
  exact this.ne_zero

lemma natDegree_rPoly_le (u : F) : (rPoly W u).natDegree ≤ 3 := by
  unfold rPoly; compute_degree

lemma a₄_ne_zero_of_char_three : W.a₄ ≠ 0 := by
  intro h
  apply W.isUnit_Δ.ne_zero
  rw [W.Δ_of_isShortNF_of_char_three, h]; ring

lemma stab_of_char_three {C : VariableChange F} (hC : C • W = W) :
    C.s = 0 ∧ C.t = 0 ∧ (C.u : F) ^ 4 = 1 ∧ (rPoly W (C.u : F)).eval C.r = 0 := by
  have hu : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have : (3 : F) = 0 := CharP.cast_eq_zero F 3
    exact one_ne_zero (by linear_combination this - h)
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have h₁ := congrArg WeierstrassCurve.a₁ hC
  have h₃ := congrArg WeierstrassCurve.a₃ hC
  have h₄ := congrArg WeierstrassCurve.a₄ hC
  have h₆ := congrArg WeierstrassCurve.a₆ hC
  rw [variableChange_a₁, W.a₁_of_isShortNF] at h₁
  rw [variableChange_a₃, W.a₁_of_isShortNF, W.a₃_of_isShortNF] at h₃
  have hs : C.s = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) * (2 * C.s) = 0 := by linear_combination h₁
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hu
    · exact (mul_eq_zero.mp h).resolve_left h2
  have ht : C.t = 0 := by
    have : ((C.u⁻¹ : Fˣ) : F) ^ 3 * (2 * C.t) = 0 := by linear_combination h₃
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · exact (mul_eq_zero.mp h).resolve_left h2
  rw [variableChange_a₄, hs, ht, W.a₃_of_isShortNF, W.a₂_of_isShortNF] at h₄
  rw [variableChange_a₆, ht, W.a₂_of_isShortNF] at h₆
  have hu4 : (C.u : F) ^ 4 = 1 := by
    apply pow_eq_one_of_inv_pow_mul_eq (a₄_ne_zero_of_char_three W)
    linear_combination h₄ - ((C.u⁻¹ : Fˣ) : F) ^ 4 * C.r ^ 2 * h3
  refine ⟨hs, ht, hu4, ?_⟩

  have hu6inv : ((C.u⁻¹ : Fˣ) : F) ^ 6 * (C.u : F) ^ 6 = 1 := by
    rw [Units.val_inv_eq_inv_val, ← mul_pow, inv_mul_cancel₀ C.u.ne_zero, one_pow]
  simp only [rPoly, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  have key : W.a₆ + C.r * W.a₄ + C.r ^ 3 = (C.u : F) ^ 6 * W.a₆ := by
    have h' : ((C.u⁻¹ : Fˣ) : F) ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 3) = W.a₆ := by
      linear_combination h₆
    calc W.a₆ + C.r * W.a₄ + C.r ^ 3
        = (((C.u⁻¹ : Fˣ) : F) ^ 6 * (C.u : F) ^ 6) * (W.a₆ + C.r * W.a₄ + C.r ^ 3) := by
          rw [hu6inv, one_mul]
      _ = (C.u : F) ^ 6 * W.a₆ := by rw [mul_comm _ ((C.u : F) ^ 6), mul_assoc, h']
  linear_combination key

lemma bound_of_char_three :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ 12 := by
  classical
  let T : Finset (F × F) := (rootsOfUnityFinset (F := F) 4).biUnion
    fun u => (rootFinset (rPoly W u)).map ⟨fun r => (u, r), fun a b h => (Prod.mk.inj h).2⟩
  have hT : T.card ≤ 12 := by
    calc T.card ≤ ∑ u ∈ rootsOfUnityFinset (F := F) 4,
          ((rootFinset (rPoly W u)).map ⟨fun r => (u, r), fun a b h => (Prod.mk.inj h).2⟩).card :=
            Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ rootsOfUnityFinset (F := F) 4, 3 := by
            apply Finset.sum_le_sum
            intro u _
            rw [Finset.card_map]
            exact (card_rootFinset_le _).trans (natDegree_rPoly_le W u)
      _ ≤ 4 * 3 := by
            rw [Finset.sum_const, smul_eq_mul]
            exact Nat.mul_le_mul_right 3 (card_rootsOfUnityFinset_le 4)
      _ = 12 := by norm_num
  have h := bound_of_injective W T (fun C => (((C : VariableChange F).u : F), (C : VariableChange F).r)) ?_ ?_
  · exact ⟨h.1, h.2.trans hT⟩
  · rintro ⟨C, hC⟩ ⟨C', hC'⟩ h
    obtain ⟨hu, hr⟩ := Prod.mk.inj h
    obtain ⟨hs, ht, -, -⟩ := stab_of_char_three W (MulAction.mem_stabilizer_iff.mp hC)
    obtain ⟨hs', ht', -, -⟩ := stab_of_char_three W (MulAction.mem_stabilizer_iff.mp hC')
    apply Subtype.ext
    apply VariableChange.ext
    · exact Units.ext hu
    · exact hr
    · rw [hs, hs']
    · rw [ht, ht']
  · rintro ⟨C, hC⟩
    obtain ⟨-, -, hu4, hr⟩ := stab_of_char_three W (MulAction.mem_stabilizer_iff.mp hC)
    simp only [T, Finset.mem_biUnion, Finset.mem_map]
    exact ⟨(C.u : F), mem_rootsOfUnityFinset (by norm_num) hu4, C.r,
      mem_rootFinset (rPoly_ne_zero W _) hr, rfl⟩

end CharThree

section CharTwo

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2] (W : WeierstrassCurve F) [W.IsElliptic]
  [W.IsCharTwoJEqZeroNF]

def sPoly (u : F) : F[X] := X ^ 4 + C W.a₃ * X + C (W.a₄ * (1 + u ^ 4))

def tPoly (r : F) : F[X] := X ^ 2 + C W.a₃ * X + C (r * W.a₄ + r ^ 3)

lemma sPoly_ne_zero (u : F) : sPoly W u ≠ 0 := by
  have : (sPoly W u).Monic := by unfold sPoly; monicity!
  exact this.ne_zero

lemma tPoly_ne_zero (r : F) : tPoly W r ≠ 0 := by
  have : (tPoly W r).Monic := by unfold tPoly; monicity!
  exact this.ne_zero

lemma natDegree_sPoly_le (u : F) : (sPoly W u).natDegree ≤ 4 := by
  unfold sPoly; compute_degree

lemma natDegree_tPoly_le (r : F) : (tPoly W r).natDegree ≤ 2 := by
  unfold tPoly; compute_degree

lemma a₃_ne_zero_of_char_two : W.a₃ ≠ 0 := by
  intro h
  apply W.isUnit_Δ.ne_zero
  rw [W.Δ_of_isCharTwoJEqZeroNF_of_char_two, h]; ring

lemma stab_of_char_two {C : VariableChange F} (hC : C • W = W) :
    (C.u : F) ^ 3 = 1 ∧ C.r = C.s ^ 2 ∧ (sPoly W (C.u : F)).eval C.s = 0 ∧
      (tPoly W C.r).eval C.t = 0 := by
  have hu : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h₂ := congrArg WeierstrassCurve.a₂ hC
  have h₃ := congrArg WeierstrassCurve.a₃ hC
  have h₄ := congrArg WeierstrassCurve.a₄ hC
  have h₆ := congrArg WeierstrassCurve.a₆ hC
  rw [variableChange_a₂, W.a₁_of_isCharTwoJEqZeroNF, W.a₂_of_isCharTwoJEqZeroNF] at h₂
  rw [variableChange_a₃, W.a₁_of_isCharTwoJEqZeroNF] at h₃
  rw [variableChange_a₄, W.a₁_of_isCharTwoJEqZeroNF, W.a₂_of_isCharTwoJEqZeroNF] at h₄
  rw [variableChange_a₆, W.a₁_of_isCharTwoJEqZeroNF, W.a₂_of_isCharTwoJEqZeroNF] at h₆

  have hu3 : (C.u : F) ^ 3 = 1 := by
    apply pow_eq_one_of_inv_pow_mul_eq (a₃_ne_zero_of_char_two W)
    linear_combination h₃ - ((C.u⁻¹ : Fˣ) : F) ^ 3 * C.t * h2

  have hr : C.r = C.s ^ 2 := by
    have : ((C.u⁻¹ : Fˣ) : F) ^ 2 * (3 * C.r - C.s ^ 2) = 0 := by linear_combination h₂
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (pow_ne_zero _ hu)
    · linear_combination h - C.r * h2
  have hu' : ((C.u⁻¹ : Fˣ) : F) * (C.u : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ C.u.ne_zero]
  have hu4inv : ((C.u⁻¹ : Fˣ) : F) ^ 4 * (C.u : F) ^ 4 = 1 := by
    rw [← mul_pow, hu', one_pow]
  have hu6inv : ((C.u⁻¹ : Fˣ) : F) ^ 6 * (C.u : F) ^ 6 = 1 := by
    rw [← mul_pow, hu', one_pow]
  have hu6 : (C.u : F) ^ 6 = 1 := by
    calc (C.u : F) ^ 6 = ((C.u : F) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hu3, one_pow]
  refine ⟨hu3, hr, ?_, ?_⟩
  ·
    simp only [sPoly, eval_add, eval_pow, eval_X, eval_mul, eval_C]
    have key : W.a₄ - C.s * W.a₃ + 3 * C.r ^ 2 - 2 * C.s * C.t = (C.u : F) ^ 4 * W.a₄ := by
      have h' : ((C.u⁻¹ : Fˣ) : F) ^ 4 * (W.a₄ - C.s * W.a₃ + 3 * C.r ^ 2 - 2 * C.s * C.t) = W.a₄ := by
        linear_combination h₄
      calc W.a₄ - C.s * W.a₃ + 3 * C.r ^ 2 - 2 * C.s * C.t
          = (((C.u⁻¹ : Fˣ) : F) ^ 4 * (C.u : F) ^ 4) *
              (W.a₄ - C.s * W.a₃ + 3 * C.r ^ 2 - 2 * C.s * C.t) := by rw [hu4inv, one_mul]
        _ = (C.u : F) ^ 4 * W.a₄ := by rw [mul_comm _ ((C.u : F) ^ 4), mul_assoc, h']
    rw [hr] at key
    linear_combination key + (-C.s ^ 4 + W.a₃ * C.s + (C.u : F) ^ 4 * W.a₄ + C.s * C.t) * h2
  ·
    simp only [tPoly, eval_add, eval_pow, eval_X, eval_mul, eval_C]
    have key : W.a₆ + C.r * W.a₄ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2 = (C.u : F) ^ 6 * W.a₆ := by
      have h' : ((C.u⁻¹ : Fˣ) : F) ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2) =
          W.a₆ := by
        linear_combination h₆
      calc W.a₆ + C.r * W.a₄ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2
          = (((C.u⁻¹ : Fˣ) : F) ^ 6 * (C.u : F) ^ 6) *
              (W.a₆ + C.r * W.a₄ + C.r ^ 3 - C.t * W.a₃ - C.t ^ 2) := by rw [hu6inv, one_mul]
        _ = (C.u : F) ^ 6 * W.a₆ := by rw [mul_comm _ ((C.u : F) ^ 6), mul_assoc, h']
    rw [hu6] at key
    linear_combination key + (C.t ^ 2 + W.a₃ * C.t) * h2

lemma bound_of_char_two :
    Finite (MulAction.stabilizer (VariableChange F) W) ∧
      Nat.card (MulAction.stabilizer (VariableChange F) W) ≤ 24 := by
  classical
  let emb : F → F → (F ↪ F × F × F) := fun u s =>
    ⟨fun t => (u, s, t), fun a b h => (Prod.mk.inj (Prod.mk.inj h).2).2⟩
  let T : Finset (F × F × F) := (rootsOfUnityFinset (F := F) 3).biUnion fun u =>
    (rootFinset (sPoly W u)).biUnion fun s => (rootFinset (tPoly W (s ^ 2))).map (emb u s)
  have hT : T.card ≤ 24 := by
    calc T.card ≤ ∑ u ∈ rootsOfUnityFinset (F := F) 3,
          ((rootFinset (sPoly W u)).biUnion fun s =>
            (rootFinset (tPoly W (s ^ 2))).map (emb u s)).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ rootsOfUnityFinset (F := F) 3, 8 := by
            apply Finset.sum_le_sum
            intro u _
            calc ((rootFinset (sPoly W u)).biUnion fun s =>
                    (rootFinset (tPoly W (s ^ 2))).map (emb u s)).card
                  ≤ ∑ s ∈ rootFinset (sPoly W u), ((rootFinset (tPoly W (s ^ 2))).map (emb u s)).card :=
                    Finset.card_biUnion_le
              _ ≤ ∑ _s ∈ rootFinset (sPoly W u), 2 := by
                    apply Finset.sum_le_sum
                    intro s _
                    rw [Finset.card_map]
                    exact (card_rootFinset_le _).trans (natDegree_tPoly_le W _)
              _ ≤ 4 * 2 := by
                    rw [Finset.sum_const, smul_eq_mul]
                    exact Nat.mul_le_mul_right 2
                      ((card_rootFinset_le _).trans (natDegree_sPoly_le W u))
              _ = 8 := by norm_num
      _ ≤ 3 * 8 := by
            rw [Finset.sum_const, smul_eq_mul]
            exact Nat.mul_le_mul_right 8 (card_rootsOfUnityFinset_le 3)
      _ = 24 := by norm_num
  have h := bound_of_injective W T
    (fun C => (((C : VariableChange F).u : F), (C : VariableChange F).s, (C : VariableChange F).t)) ?_ ?_
  · exact ⟨h.1, h.2.trans hT⟩
  · rintro ⟨C, hC⟩ ⟨C', hC'⟩ h
    obtain ⟨hu, hst⟩ := Prod.mk.inj h
    obtain ⟨hs, ht⟩ := Prod.mk.inj hst
    obtain ⟨-, hr, -, -⟩ := stab_of_char_two W (MulAction.mem_stabilizer_iff.mp hC)
    obtain ⟨-, hr', -, -⟩ := stab_of_char_two W (MulAction.mem_stabilizer_iff.mp hC')
    apply Subtype.ext
    apply VariableChange.ext
    · exact Units.ext hu
    · rw [hr, hr', hs]
    · exact hs
    · exact ht
  · rintro ⟨C, hC⟩
    obtain ⟨hu3, hr, hs, ht⟩ := stab_of_char_two W (MulAction.mem_stabilizer_iff.mp hC)
    simp only [T, Finset.mem_biUnion, Finset.mem_map]
    refine ⟨(C.u : F), mem_rootsOfUnityFinset (by norm_num) hu3, C.s,
      mem_rootFinset (sPoly_ne_zero W _) hs, C.t, mem_rootFinset (tPoly_ne_zero W _) (hr ▸ ht), rfl⟩

end CharTwo

section Assembly

variable {F : Type*} [Field F] (E : WeierstrassCurve F) [E.IsElliptic]

theorem main :
    ((6 : F) ≠ 0 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 6) ∧
    ((6 : F) ≠ 0 → E.j = 1728 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 4) ∧
    (ringChar F = 3 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 12) ∧
    (ringChar F = 2 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 24) := by
  classical
  refine ⟨fun h6 hj => ?_, fun h6 hj => ?_, fun h3 hj => ?_, fun h2 hj => ?_⟩
  ·
    have h2 : (2 : F) ≠ 0 := fun h => h6 (by linear_combination 3 * h)
    have h3 : (3 : F) ≠ 0 := fun h => h6 (by linear_combination 2 * h)
    letI : Invertible (2 : F) := invertibleOfNonzero h2
    letI : Invertible (3 : F) := invertibleOfNonzero h3
    obtain ⟨C, hC⟩ := E.exists_variableChange_isShortNF
    haveI := hC
    apply bound_of_smul C E
    have hj' : (C • E).j = 0 := by rw [variableChange_j, hj]
    have ha₄ : (C • E).a₄ = 0 := a₄_eq_zero_of_j_eq_zero (C • E) h2 h3 hj'
    have ha₆ : (C • E).a₆ ≠ 0 := by
      intro h
      apply four_a₄_cube_add_ne_zero (C • E)
      rw [ha₄, h]; ring
    exact bound_short (C • E) h2 h3 (by norm_num) fun C' hC' => u_pow_six_of_short (C • E) h2 h3 ha₆ hC'
  ·
    have h2 : (2 : F) ≠ 0 := fun h => h6 (by linear_combination 3 * h)
    have h3 : (3 : F) ≠ 0 := fun h => h6 (by linear_combination 2 * h)
    letI : Invertible (2 : F) := invertibleOfNonzero h2
    letI : Invertible (3 : F) := invertibleOfNonzero h3
    obtain ⟨C, hC⟩ := E.exists_variableChange_isShortNF
    haveI := hC
    apply bound_of_smul C E
    have hj' : (C • E).j = 1728 := by rw [variableChange_j, hj]
    have ha₆ : (C • E).a₆ = 0 := a₆_eq_zero_of_j_eq_1728 (C • E) h2 h3 hj'
    have ha₄ : (C • E).a₄ ≠ 0 := by
      intro h
      apply four_a₄_cube_add_ne_zero (C • E)
      rw [ha₆, h]; ring
    exact bound_short (C • E) h2 h3 (by norm_num) fun C' hC' => u_pow_four_of_short (C • E) h2 h3 ha₄ hC'
  ·
    haveI : CharP F 3 := ringChar.of_eq h3
    obtain ⟨C, hC⟩ := E.exists_variableChange_isCharThreeNF
    apply bound_of_smul C E
    have hj' : (C • E).j = 0 := by rw [variableChange_j, hj]
    rcases hC with ⟨h⟩ | ⟨h⟩
    · exact absurd hj' (j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three (C • E))
    · exact bound_of_char_three (C • E)
  ·
    haveI : CharP F 2 := ringChar.of_eq h2
    obtain ⟨C, hC⟩ := E.exists_variableChange_isCharTwoNF
    apply bound_of_smul C E
    have hj' : (C • E).j = 0 := by rw [variableChange_j, hj]
    rcases hC with ⟨h⟩ | ⟨h⟩
    · exact absurd hj' (j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two (C • E))
    · exact bound_of_char_two (C • E)

end Assembly

section TwoOfJ

variable {F : Type*} [Field F]

theorem mem_stabilizer_iff_of_isShortNF (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsShortNF] (ha₄ : E.a₄ ≠ 0) (ha₆ : E.a₆ ≠ 0)
    (C : VariableChange F) :
    C ∈ MulAction.stabilizer (VariableChange F) E ↔
      C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ (C.u : F) ^ 2 = 1 := by
  rw [MulAction.mem_stabilizer_iff]
  have hu : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have hE₁ : E.a₁ = 0 := E.a₁_of_isShortNF
  have hE₂ : E.a₂ = 0 := E.a₂_of_isShortNF
  have hE₃ : E.a₃ = 0 := E.a₃_of_isShortNF
  constructor
  · intro h
    have h₁ : (C • E).a₁ = E.a₁ := by rw [h]
    have h₂ : (C • E).a₂ = E.a₂ := by rw [h]
    have h₃ : (C • E).a₃ = E.a₃ := by rw [h]
    have h₄ : (C • E).a₄ = E.a₄ := by rw [h]
    have h₆ : (C • E).a₆ = E.a₆ := by rw [h]
    rw [variableChange_a₁, hE₁, zero_add] at h₁

    have hs : C.s = 0 := by
      have : ((C.u⁻¹ : Fˣ) : F) * (2 * C.s) = 0 := h₁
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hu
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h2
        · exact h

    have hr : C.r = 0 := by
      rw [variableChange_a₂, hE₂, hE₁, hs] at h₂
      have : ((C.u⁻¹ : Fˣ) : F) ^ 2 * (3 * C.r) = 0 := by
        rw [← h₂]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hu
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h3
        · exact h

    have ht : C.t = 0 := by
      rw [variableChange_a₃, hE₃, hE₁, hr] at h₃
      have : ((C.u⁻¹ : Fˣ) : F) ^ 3 * (2 * C.t) = 0 := by
        rw [← h₃]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp h) hu
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h2
        · exact h

    have h4 : ((C.u⁻¹ : Fˣ) : F) ^ 4 = 1 := by
      rw [variableChange_a₄, hE₁, hE₂, hE₃, hr, hs, ht] at h₄
      have : ((C.u⁻¹ : Fˣ) : F) ^ 4 * E.a₄ = 1 * E.a₄ := by linear_combination h₄
      exact mul_right_cancel₀ ha₄ this
    have h6 : ((C.u⁻¹ : Fˣ) : F) ^ 6 = 1 := by
      rw [variableChange_a₆, hE₁, hE₂, hE₃, hr, ht] at h₆
      have : ((C.u⁻¹ : Fˣ) : F) ^ 6 * E.a₆ = 1 * E.a₆ := by linear_combination h₆
      exact mul_right_cancel₀ ha₆ this
    have hinv2 : ((C.u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
      have h8 : ((C.u⁻¹ : Fˣ) : F) ^ 8 = 1 := by
        calc ((C.u⁻¹ : Fˣ) : F) ^ 8 = (((C.u⁻¹ : Fˣ) : F) ^ 4) ^ 2 := by ring
          _ = 1 := by rw [h4, one_pow]
      have : ((C.u⁻¹ : Fˣ) : F) ^ 8 = ((C.u⁻¹ : Fˣ) : F) ^ 6 * ((C.u⁻¹ : Fˣ) : F) ^ 2 := by ring
      rw [this, h6, one_mul] at h8
      exact h8
    have hu2 : (C.u : F) ^ 2 = 1 := by
      have hmul : (C.u : F) * ((C.u⁻¹ : Fˣ) : F) = 1 := by
        rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ C.u.ne_zero]
      calc (C.u : F) ^ 2 = (C.u : F) ^ 2 * (((C.u⁻¹ : Fˣ) : F) ^ 2) := by rw [hinv2, mul_one]
        _ = ((C.u : F) * ((C.u⁻¹ : Fˣ) : F)) ^ 2 := by ring
        _ = 1 := by rw [hmul, one_pow]
    exact ⟨hr, hs, ht, hu2⟩
  · rintro ⟨hr, hs, ht, hu2⟩
    have hinv2 : ((C.u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
      rw [Units.val_inv_eq_inv_val, inv_pow, hu2, inv_one]
    have hinv4 : ((C.u⁻¹ : Fˣ) : F) ^ 4 = 1 := by
      calc ((C.u⁻¹ : Fˣ) : F) ^ 4 = (((C.u⁻¹ : Fˣ) : F) ^ 2) ^ 2 := by ring
        _ = 1 := by rw [hinv2, one_pow]
    have hinv6 : ((C.u⁻¹ : Fˣ) : F) ^ 6 = 1 := by
      calc ((C.u⁻¹ : Fˣ) : F) ^ 6 = (((C.u⁻¹ : Fˣ) : F) ^ 2) ^ 3 := by ring
        _ = 1 := by rw [hinv2, one_pow]
    ext
    · rw [variableChange_a₁, hE₁, hs]; ring
    · rw [variableChange_a₂, hE₁, hE₂, hr, hs]; ring
    · rw [variableChange_a₃, hE₁, hE₃, hr, ht]; ring
    · rw [variableChange_a₄, hE₁, hE₂, hE₃, hr, hs, ht]
      linear_combination E.a₄ * hinv4
    · rw [variableChange_a₆, hE₁, hE₂, hE₃, hr, ht]
      linear_combination E.a₆ * hinv6

def stabilizerEquivSqEqOne (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsShortNF] (ha₄ : E.a₄ ≠ 0) (ha₆ : E.a₆ ≠ 0) :
    MulAction.stabilizer (VariableChange F) E ≃ {u : Fˣ // (u : F) ^ 2 = 1} where
  toFun C := ⟨C.1.u, ((mem_stabilizer_iff_of_isShortNF h2 h3 E ha₄ ha₆ C.1).mp C.2).2.2.2⟩
  invFun u := ⟨⟨u.1, 0, 0, 0⟩,
    (mem_stabilizer_iff_of_isShortNF h2 h3 E ha₄ ha₆ _).mpr ⟨rfl, rfl, rfl, u.2⟩⟩
  left_inv C := by
    obtain ⟨hr, hs, ht, -⟩ := (mem_stabilizer_iff_of_isShortNF h2 h3 E ha₄ ha₆ C.1).mp C.2
    apply Subtype.ext
    ext
    · rfl
    · exact hr.symm
    · exact hs.symm
    · exact ht.symm
  right_inv u := rfl

theorem natCard_sqEqOne (h2 : (2 : F) ≠ 0) : Nat.card {u : Fˣ // (u : F) ^ 2 = 1} = 2 := by
  classical
  have hne : (1 : Fˣ) ≠ -1 := by
    intro h
    have h' : ((1 : Fˣ) : F) = ((-1 : Fˣ) : F) := congrArg Units.val h
    rw [Units.val_one, Units.val_neg, Units.val_one] at h'
    apply h2
    linear_combination h'
  let e : {u : Fˣ // (u : F) ^ 2 = 1} ≃ Bool :=
    { toFun := fun u => decide (u.1 = 1)
      invFun := fun b => if b then ⟨1, by simp⟩ else ⟨-1, by simp⟩
      left_inv := by
        rintro ⟨u, hu⟩
        have hu' : (u : F) = 1 ∨ (u : F) = -1 := by
          rw [← mul_self_eq_one_iff, ← sq]; exact hu
        rcases hu' with h | h
        · have : u = 1 := Units.ext (by simpa using h)
          subst this; simp
        · have : u = -1 := Units.ext (by simpa using h)
          subst this
          simp [hne.symm]
      right_inv := by
        intro b
        cases b
        · simp [hne.symm]
        · simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_bool]

end TwoOfJ

section CharTwoThree

variable {F : Type*} [Field F]

def ofUnit (u : Fˣ) : VariableChange F := ⟨u, 0, 0, 0⟩

@[scoped simp] lemma ofUnit_u (u : Fˣ) : (ofUnit u).u = u := rfl
@[scoped simp] lemma ofUnit_r (u : Fˣ) : (ofUnit u).r = 0 := rfl
@[scoped simp] lemma ofUnit_s (u : Fˣ) : (ofUnit u).s = 0 := rfl
@[scoped simp] lemma ofUnit_t (u : Fˣ) : (ofUnit u).t = 0 := rfl

lemma ofUnit_one : (ofUnit 1 : VariableChange F) = 1 := by
  rw [VariableChange.one_def]; rfl

lemma mem_stab_iff (C : VariableChange F) (W : WeierstrassCurve F) :
    C ∈ MulAction.stabilizer (VariableChange F) W ↔ C • W = W :=
  MulAction.mem_stabilizer_iff

lemma natCard_stabilizer_eq_two (W : WeierstrassCurve F) (σ : VariableChange F)
    (hσ : σ • W = W) (hσ1 : σ ≠ 1)
    (hall : ∀ C : VariableChange F, C • W = W → C = 1 ∨ C = σ) :
    Nat.card (MulAction.stabilizer (VariableChange F) W) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, (mem_stab_iff _ _).mpr (one_smul _ _)⟩, ⟨σ, (mem_stab_iff _ _).mpr hσ⟩,
    fun h => hσ1 (congrArg Subtype.val h).symm, ?_⟩
  ext ⟨C, hC⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases hall C ((mem_stab_iff _ _).mp hC) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

section Char3

variable [CharP F 3] {E : WeierstrassCurve F}

private lemma three_eq_zero : (3 : F) = 0 := by
  simpa using CharP.cast_eq_zero F 3

private lemma two_ne_zero' : (2 : F) ≠ 0 := by
  intro h
  have h1 : (1 : F) = 0 := by linear_combination three_eq_zero (F := F) - h
  exact one_ne_zero h1

lemma c3_of_smul_eq [E.IsCharThreeJNeZeroNF] (ha₂ : E.a₂ ≠ 0) {C : VariableChange F}
    (hC : C • E = E) : C.r = 0 ∧ C.s = 0 ∧ C.t = 0 ∧ ((C.u : F) = 1 ∨ (C.u : F) = -1) := by
  have hv : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := (C.u⁻¹).ne_zero
  have h1 : (C • E).a₁ = E.a₁ := by rw [hC]
  have h2 : (C • E).a₂ = E.a₂ := by rw [hC]
  have h3 : (C • E).a₃ = E.a₃ := by rw [hC]
  have h4 : (C • E).a₄ = E.a₄ := by rw [hC]
  rw [variableChange_a₁, a₁_of_isCharThreeJNeZeroNF] at h1
  rw [variableChange_a₂, a₁_of_isCharThreeJNeZeroNF] at h2
  rw [variableChange_a₃, a₃_of_isCharThreeJNeZeroNF, a₁_of_isCharThreeJNeZeroNF] at h3
  rw [variableChange_a₄, a₄_of_isCharThreeJNeZeroNF, a₃_of_isCharThreeJNeZeroNF,
    a₁_of_isCharThreeJNeZeroNF] at h4
  have hs : C.s = 0 := by
    have h := (mul_eq_zero.mp h1).resolve_left hv
    rcases mul_eq_zero.mp (by linear_combination h : (2 : F) * C.s = 0) with h' | h'
    · exact absurd h' two_ne_zero'
    · exact h'
  have ht : C.t = 0 := by
    have h := (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 3 hv)
    rcases mul_eq_zero.mp (by linear_combination h : (2 : F) * C.t = 0) with h' | h'
    · exact absurd h' two_ne_zero'
    · exact h'
  have hr : C.r = 0 := by
    have h := (mul_eq_zero.mp h4).resolve_left (pow_ne_zero 4 hv)
    rw [hs, ht] at h
    have h' : (2 * E.a₂) * C.r = 0 := by
      linear_combination h - C.r ^ 2 * three_eq_zero (F := F)
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (mul_ne_zero two_ne_zero' ha₂)
    · exact h''
  have hu : ((C.u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
    rw [hs, hr] at h2
    have h' : (((C.u⁻¹ : Fˣ) : F) ^ 2 - 1) * E.a₂ = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h' with h'' | h''
    · linear_combination h''
    · exact absurd h'' ha₂
  have hu' : (C.u : F) ^ 2 = 1 := by
    have := congrArg (fun z : F => z * (C.u : F) ^ 2) hu
    simp only [one_mul] at this
    rw [← this, ← mul_pow, Units.inv_mul, one_pow]
  exact ⟨hr, hs, ht, sq_eq_one_iff.mp hu'⟩

omit [CharP F 3] in

lemma c3_ofUnit_smul [E.IsCharThreeJNeZeroNF] (u : Fˣ) (hu : (u : F) = 1 ∨ (u : F) = -1) :
    ofUnit u • E = E := by
  have hv2 : ((u⁻¹ : Fˣ) : F) ^ 2 = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow]
    rcases hu with h | h <;> rw [h] <;> norm_num
  have hv6 : ((u⁻¹ : Fˣ) : F) ^ 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hv2, one_pow]
  ext
  · simp only [variableChange_a₁, ofUnit_u, ofUnit_s, a₁_of_isCharThreeJNeZeroNF]
    ring
  · simp only [variableChange_a₂, ofUnit_u, ofUnit_r, ofUnit_s, a₁_of_isCharThreeJNeZeroNF]
    linear_combination E.a₂ * hv2
  · simp only [variableChange_a₃, ofUnit_u, ofUnit_r, ofUnit_t, a₃_of_isCharThreeJNeZeroNF,
      a₁_of_isCharThreeJNeZeroNF]
    ring
  · simp only [variableChange_a₄, ofUnit_u, ofUnit_r, ofUnit_s, ofUnit_t,
      a₄_of_isCharThreeJNeZeroNF, a₃_of_isCharThreeJNeZeroNF, a₁_of_isCharThreeJNeZeroNF]
    ring
  · simp only [variableChange_a₆, ofUnit_u, ofUnit_r, ofUnit_t,
      a₄_of_isCharThreeJNeZeroNF, a₃_of_isCharThreeJNeZeroNF, a₁_of_isCharThreeJNeZeroNF]
    linear_combination E.a₆ * hv6

theorem c3_jne_card [E.IsCharThreeJNeZeroNF] [E.IsElliptic] :
    Nat.card (MulAction.stabilizer (VariableChange F) E) = 2 := by
  have ha₂ : E.a₂ ≠ 0 := by
    intro h
    have hΔ := E.isUnit_Δ.ne_zero
    rw [Δ_of_isCharThreeJNeZeroNF_of_char_three, h] at hΔ
    simp at hΔ
  refine natCard_stabilizer_eq_two E (ofUnit (-1)) (c3_ofUnit_smul (-1) (Or.inr (by simp)))
    ?_ ?_
  · intro h
    have h' : ((ofUnit (-1) : VariableChange F)).u = (1 : VariableChange F).u := by rw [h]
    simp only [ofUnit_u, VariableChange.one_def] at h'
    have h'' : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := by rw [h']
    simp only [Units.val_neg, Units.val_one] at h''
    exact two_ne_zero' (F := F) (by linear_combination -h'')
  · intro C hC
    obtain ⟨hr, hs, ht, hu | hu⟩ := c3_of_smul_eq ha₂ hC
    · left
      rw [VariableChange.one_def]
      ext <;> simp [hr, hs, ht, hu]
    · right
      ext <;> simp [hr, hs, ht, hu, ofUnit]

theorem card_stabilizer_char_three (W : WeierstrassCurve F) [W.IsElliptic] (hj : W.j ≠ 0) :
    Nat.card (MulAction.stabilizer (VariableChange F) W) = 2 := by
  obtain ⟨C, hC⟩ := W.exists_variableChange_isCharThreeNF
  rw [Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : C • W = C • W)).toEquiv]
  cases hC with
  | of_j_ne_zero => exact c3_jne_card
  | of_j_eq_zero =>
    exact absurd ((variableChange_j W C).symm.trans (j_of_isShortNF_of_char_three (C • W))) hj

end Char3

section Char2

variable [CharP F 2] {E : WeierstrassCurve F}

private lemma two_eq_zero : (2 : F) = 0 := by
  simpa using CharP.cast_eq_zero F 2

def sigma : VariableChange F := ⟨1, 0, 1, 0⟩

omit [CharP F 2] in
@[scoped simp] lemma sigma_u : (sigma : VariableChange F).u = 1 := rfl
omit [CharP F 2] in
@[scoped simp] lemma sigma_r : (sigma : VariableChange F).r = 0 := rfl
omit [CharP F 2] in
@[scoped simp] lemma sigma_s : (sigma : VariableChange F).s = 1 := rfl
omit [CharP F 2] in
@[scoped simp] lemma sigma_t : (sigma : VariableChange F).t = 0 := rfl

lemma c2_of_smul_eq [E.IsCharTwoJNeZeroNF] {C : VariableChange F} (hC : C • E = E) :
    C.u = 1 ∧ C.r = 0 ∧ C.t = 0 ∧ (C.s = 0 ∨ C.s = 1) := by
  have h1 : (C • E).a₁ = E.a₁ := by rw [hC]
  have h2 : (C • E).a₂ = E.a₂ := by rw [hC]
  have h3 : (C • E).a₃ = E.a₃ := by rw [hC]
  have h4 : (C • E).a₄ = E.a₄ := by rw [hC]
  rw [variableChange_a₁, a₁_of_isCharTwoJNeZeroNF] at h1
  rw [variableChange_a₂, a₁_of_isCharTwoJNeZeroNF] at h2
  rw [variableChange_a₃, a₃_of_isCharTwoJNeZeroNF, a₁_of_isCharTwoJNeZeroNF] at h3
  rw [variableChange_a₄, a₄_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF,
    a₁_of_isCharTwoJNeZeroNF] at h4
  have hv : ((C.u⁻¹ : Fˣ) : F) = 1 := by
    linear_combination h1 - ((C.u⁻¹ : Fˣ) : F) * C.s * two_eq_zero (F := F)
  have hu : C.u = 1 := by
    have : C.u⁻¹ = 1 := Units.ext (by simpa using hv)
    simpa using this
  rw [hv] at h2 h3 h4
  have hr : C.r = 0 := by
    linear_combination h3 - C.t * two_eq_zero (F := F)
  have ht : C.t = 0 := by
    rw [hr] at h4
    linear_combination -h4 - C.s * C.t * two_eq_zero (F := F)
  have hs : C.s * (C.s - 1) = 0 := by
    rw [hr] at h2
    linear_combination -h2 - C.s * two_eq_zero (F := F)
  refine ⟨hu, hr, ht, ?_⟩
  rcases mul_eq_zero.mp hs with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h)

lemma c2_smul_of [E.IsCharTwoJNeZeroNF] (C : VariableChange F) (hu : C.u = 1) (hr : C.r = 0)
    (ht : C.t = 0) (hs : C.s = 0 ∨ C.s = 1) : C • E = E := by
  have hs' : C.s ^ 2 = C.s := by
    rcases hs with h | h <;> rw [h] <;> norm_num
  ext
  · simp only [variableChange_a₁, a₁_of_isCharTwoJNeZeroNF, hu, inv_one, Units.val_one, one_mul]
    linear_combination C.s * two_eq_zero (F := F)
  · simp only [variableChange_a₂, a₁_of_isCharTwoJNeZeroNF, hu, hr, inv_one, Units.val_one,
      one_pow, one_mul]
    linear_combination -hs' - C.s * two_eq_zero (F := F)
  · simp [variableChange_a₃, hu, hr, ht]
  · simp [variableChange_a₄, hu, hr, ht]
  · simp [variableChange_a₆, hu, hr, ht]

theorem c2_jne_card [E.IsCharTwoJNeZeroNF] :
    Nat.card (MulAction.stabilizer (VariableChange F) E) = 2 := by
  refine natCard_stabilizer_eq_two E sigma (c2_smul_of sigma rfl rfl rfl (Or.inr rfl)) ?_ ?_
  · intro h
    have h' : (sigma : VariableChange F).s = (1 : VariableChange F).s := by rw [h]
    simp only [sigma_s, VariableChange.one_def] at h'
    exact one_ne_zero h'
  · intro C hC
    obtain ⟨hu, hr, ht, hs | hs⟩ := c2_of_smul_eq hC
    · left
      rw [VariableChange.one_def]
      ext <;> simp [hr, hs, ht, hu]
    · right
      ext <;> simp [hr, hs, ht, hu, sigma]

theorem card_stabilizer_char_two (W : WeierstrassCurve F) [W.IsElliptic] (hj : W.j ≠ 0) :
    Nat.card (MulAction.stabilizer (VariableChange F) W) = 2 := by
  obtain ⟨C, hC⟩ := W.exists_variableChange_isCharTwoNF
  rw [Nat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : C • W = C • W)).toEquiv]
  cases hC with
  | of_j_ne_zero => exact c2_jne_card
  | of_j_eq_zero =>
    exact absurd ((variableChange_j W C).symm.trans
      (j_of_isCharTwoJEqZeroNF_of_char_two (C • W))) hj

end Char2

theorem card_stabilizer_of_char_two_or_three (hF : ringChar F = 2 ∨ ringChar F = 3)
    (W : WeierstrassCurve F) [W.IsElliptic] (hj : W.j ≠ 0) :
    Nat.card (MulAction.stabilizer (VariableChange F) W) = 2 := by
  rcases hF with h | h
  · haveI : CharP F 2 := ringChar.of_eq h
    exact card_stabilizer_char_two W hj
  · haveI : CharP F 3 := ringChar.of_eq h
    exact card_stabilizer_char_three W hj

end CharTwoThree

end Automorphism

open WeierstrassCurve.Automorphism

/-- The four-case order bound: `≤ 6` at `j = 0`, `≤ 4` at `j = 1728` (both when `6` is a unit), and
`≤ 12` / `≤ 24` at `j = 0` in characteristic `3` / `2`. -/
theorem finite_stabilizer_and_natCard_le_of_j
    {F : Type*} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] :
    ((6 : F) ≠ 0 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 6) ∧
    ((6 : F) ≠ 0 → E.j = 1728 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 4) ∧
    (ringChar F = 3 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 12) ∧
    (ringChar F = 2 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 24) :=
  Automorphism.main E

/-- Away from `j = 0` and `j = 1728`, with `2` and `3` units, the automorphism group has order `2`. -/
theorem natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_j_ne_1728
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) (hj1728 : E.j ≠ 1728) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 := by
  letI : Invertible (2 : F) := invertibleOfNonzero h2
  letI : Invertible (3 : F) := invertibleOfNonzero h3

  have hj : (E.toShortNF • E).j = E.j := variableChange_j E E.toShortNF

  have hΔ : (E.toShortNF • E).Δ ≠ 0 := by
    rw [← WeierstrassCurve.coe_Δ']; exact (E.toShortNF • E).Δ'.ne_zero
  have hden : 4 * (E.toShortNF • E).a₄ ^ 3 + 27 * (E.toShortNF • E).a₆ ^ 2 ≠ 0 := by
    intro h0
    apply hΔ
    rw [(E.toShortNF • E).Δ_of_isShortNF, h0, mul_zero]
  have ha₄ : (E.toShortNF • E).a₄ ≠ 0 := by
    intro h0
    apply hj0
    rw [← hj, (E.toShortNF • E).j_of_isShortNF, h0]
    simp
  have ha₆ : (E.toShortNF • E).a₆ ≠ 0 := by
    intro h0
    apply hj1728
    rw [← hj, (E.toShortNF • E).j_of_isShortNF, h0]
    have h4 : (4 : F) * (E.toShortNF • E).a₄ ^ 3 ≠ 0 := by
      rw [h0] at hden; simpa using hden
    rw [show (4 : F) * (E.toShortNF • E).a₄ ^ 3 + 27 * (0 : F) ^ 2
        = 4 * (E.toShortNF • E).a₄ ^ 3 by ring, div_eq_iff h4]
    ring

  have e1 : MulAction.stabilizer (VariableChange F) E
      ≃* MulAction.stabilizer (VariableChange F) (E.toShortNF • E) :=
    MulAction.stabilizerEquivStabilizer (g := E.toShortNF) rfl
  rw [Nat.card_congr e1.toEquiv,
    Nat.card_congr (stabilizerEquivSqEqOne h2 h3 (E.toShortNF • E) ha₄ ha₆), natCard_sqEqOne h2]

/-- The same count `2` away from `j = 0`, in characteristic `2` or `3`. -/
theorem natCard_stabilizer_variableChange_eq_two_of_j_ne_zero_of_char_two_or_three
    {F : Type*} [Field F] (hF : ringChar F = 2 ∨ ringChar F = 3)
    (E : WeierstrassCurve F) [E.IsElliptic] (hj0 : E.j ≠ 0) :
    Nat.card (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) = 2 :=
  card_stabilizer_of_char_two_or_three hF E hj0

end WeierstrassCurve
