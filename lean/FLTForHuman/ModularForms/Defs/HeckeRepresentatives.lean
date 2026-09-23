/-
  The Hecke representatives on `ℙ¹(𝔽_p)`: the matrices, the `SL₂(ℤ)` action and
  the two reindexing workhorses for `U_p`/`T_p` slash-invariance.

  This is the shared block FLT writes *publicly* in
  `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean:82–455` (under
  `CuspForm.Gamma1Hecke`) and then re-inlines into every `S_` file of the
  slash-invariance layer. The port has no `Gamma1` yet, so the block gets its own
  definition module — the deliberate placement divergence from the pin, recorded
  here as the `TS` module records its own. The declarations are the `S_`-file
  copies (`S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:25–312` and
  `…_div.lean`), which are the exact statements the Tier-1 workhorses consume:

  - `det_eq` and the four `_mul_of_eq` lemmas: multiplying a Hecke matrix by
    `mapGL ℝ g` stays in the coset system. **The equation conjunct is kept.** The
    port's old private copy in `PhiGenDescends.lean` had dropped the
    `g' 1 0 = …` conjuncts; the Γ₀ invariance proofs need
    `g' 1 0 = p * g 1 0` (resp. `= g 1 0`, `= e`) to show `g' ∈ Γ₀(N)`. The
    statements here restore them, so the private copies are deleted rather than
    promoted. (The pin's *public* home additionally tracks `g' 1 1` and, in
    `heckeRep_mul`, a `wt`-equation; those are Tier-2 Gamma1/Nebentypus
    refinements and are deliberately not pulled in here.)
  - the `ZMod p` reindexing (`sum_range_eq_sum_zmod`, `heckeU_eq_sum_zmod`) and
    the affine permutation `affinePerm` with the workhorse `heckeU_slash_mapGL`;
  - the `OnePoint (ZMod p)` side (`heckeRep`, `redMatrix`, `heckeRep_mul`) and
    `heckeT_slash_mapGL`, together with `heckeT_eq_sum_onePoint` (the range sum
    packaged as a `Fintype.sum_option`; it has no pin wrapper of its own and
    lives in the same `S_` block).

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean:82–455` (public home) and
  `P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean` /
  `P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div.lean` (the Γ₀
  copies). Statements verbatim from the `S_` files; proofs adapted only for
  mathlib `v4.34.0` (`if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`, which are
  proof-only and leave the statements unchanged).
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import FLTForHuman.ModularForms.Defs.HeckeOperator

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm OnePoint

namespace ModularForm.HeckeRepresentatives

@[simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0 + j * g 1 0, e; p * g 1 0, g 1 1 - g 1 0 * j'], ?_⟩, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![e, g 0 1 + j * g 1 1; g 1 0, p * g 1 1], ?_⟩, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 1 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeDiagMatrix_mul_of_eq (g : SL(2, ℤ)) (j' : ℕ) (e : ℤ)
    (he : g 1 1 = g 1 0 * j' + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![p * g 0 0, g 0 1 - g 0 0 * j'; g 1 0, e], ?_⟩, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 0 0) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeDiagMatrix_mul_of_eq' (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = e ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0, p * g 0 1; e, g 1 1], ?_⟩, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * he
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals first
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination this)
      | (have := congrArg (Int.cast : ℤ → ℝ) he; push_cast at this ⊢; linear_combination -this)
      | ring1

end commutation

section reindex

variable {p : ℕ} [NeZero p]

theorem sum_range_eq_sum_zmod {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ j ∈ Finset.range p, F j = ∑ x : ZMod p, F x.val := by
  refine Finset.sum_nbij' (fun j : ℕ ↦ (j : ZMod p)) (fun x : ZMod p ↦ x.val) (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_) (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

theorem heckeU_eq_sum_zmod (k : ℤ) (f : ℍ → ℂ) :
    heckeU k p f = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val := by
  rw [heckeU_def]
  exact sum_range_eq_sum_zmod _

end reindex

section heckeU

variable {p : ℕ}

theorem unit_of_apply_one_zero_eq_zero (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) :
    ((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) = 1 := by
  have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
  push_cast at this
  linear_combination this + ((g 0 1 : ℤ) : ZMod p) * hc

def affinePerm (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) : Equiv.Perm (ZMod p) where
  toFun j := ((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j)
  invFun j := ((g 0 0 : ℤ) : ZMod p) * (((g 0 0 : ℤ) : ZMod p) * j - ((g 0 1 : ℤ) : ZMod p))
  left_inv j := by
    linear_combination (((g 0 0 : ℤ) : ZMod p) * ((g 0 1 : ℤ) : ZMod p)
      + j * (((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) + 1)) *
        unit_of_apply_one_zero_eq_zero g hc
  right_inv j := by
    linear_combination (-(((g 1 1 : ℤ) : ZMod p) * ((g 0 1 : ℤ) : ZMod p))
      + j * (((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) + 1)) *
        unit_of_apply_one_zero_eq_zero g hc

theorem affinePerm_apply (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) (j : ZMod p) :
    affinePerm g hc j =
      ((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j) := rfl

variable [NeZero p]

theorem heckeMatrix_mul_of_dvd (g : SL(2, ℤ)) (hc : (p : ℤ) ∣ g 1 0) (x : ZMod p) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧
      heckeMatrix p x.val * mapGL ℝ g =
        mapGL ℝ g' * heckeMatrix p (affinePerm g ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc) x).val := by
  have hc0 : ((g 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  set x' := affinePerm g hc0 x with hx'
  obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + x.val * g 1 1 - x'.val * (g 0 0 + x.val * g 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hx', affinePerm_apply]
    linear_combination (-(((g 0 1 : ℤ) : ZMod p) + x * ((g 1 1 : ℤ) : ZMod p))) *
      unit_of_apply_one_zero_eq_zero g hc0
      - (((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * x) * x) * hc0
  exact heckeMatrix_mul_of_eq (NeZero.ne p) g x.val x'.val e (by linear_combination he)

variable {N : ℕ} (k : ℤ)

theorem heckeU_slash_mapGL (hpN : p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    heckeU k p f ∣[k] (mapGL ℝ g) = heckeU k p f := by
  have hcN : (N : ℤ) ∣ g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hg)
  have hc : (p : ℤ) ∣ g 1 0 := (Int.natCast_dvd_natCast.mpr hpN).trans hcN
  rw [heckeU_eq_sum_zmod k f, SlashAction.sum_slash]
  calc ∑ x : ZMod p, (f ∣[k] heckeMatrix p x.val) ∣[k] mapGL ℝ g
      = ∑ x : ZMod p, f ∣[k] heckeMatrix p
          (affinePerm g ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc) x).val := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_dvd g hc x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N := by
          rw [CongruenceSubgroup.Gamma0_mem, hg']
          push_cast
          rw [CongruenceSubgroup.Gamma0_mem.mp hg, mul_zero]
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg'N)]
    _ = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val :=
        Equiv.sum_comp (affinePerm g _) (fun x ↦ f ∣[k] heckeMatrix p x.val)

end heckeU

section heckeT

variable {p : ℕ}

def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)

@[simp] theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[simp] theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeMatrix p j.val := rfl

theorem heckeT_eq_sum_onePoint [NeZero p] (k : ℤ) (f : ℍ → ℂ) :
    heckeT k p f = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x := by
  rw [heckeT_eq_heckeU_add, heckeU_eq_sum_zmod, add_comm]
  exact (Fintype.sum_option (fun x : OnePoint (ZMod p) ↦ f ∣[k] heckeRep p x)).symm

variable [Fact p.Prime]

variable (p) in

def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p); ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    (by
      have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
      push_cast at this
      rw [Matrix.det_fin_two_of,
        show ((g 1 1 : ℤ) : ZMod p) * ((g 0 0 : ℤ) : ZMod p) - ((g 0 1 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p)
          = 1 by linear_combination this]
      exact one_ne_zero)

@[simp] theorem redMatrix_apply_zero_zero (g : SL(2, ℤ)) :
    redMatrix p g 0 0 = ((g 1 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[simp] theorem redMatrix_apply_zero_one (g : SL(2, ℤ)) :
    redMatrix p g 0 1 = ((g 0 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[simp] theorem redMatrix_apply_one_zero (g : SL(2, ℤ)) :
    redMatrix p g 1 0 = ((g 1 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[simp] theorem redMatrix_apply_one_one (g : SL(2, ℤ)) :
    redMatrix p g 1 1 = ((g 0 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : (N : ℤ) ∣ g 1 0)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
    ·
      rw [ite_eq_left (by simpa using hc), heckeRep_infty]
      obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      obtain ⟨g', hg', hmul⟩ := heckeDiagMatrix_mul_of_eq' hp g e he
      refine ⟨g', ?_, hmul⟩
      rw [hg']
      have hcop : IsCoprime (N : ℤ) (p : ℤ) :=
        Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm
      exact hcop.dvd_of_dvd_mul_left (he ▸ hg)
    ·
      rw [ite_eq_right (by simpa using hc), heckeRep_infty, heckeRep_coe]
      set y : ZMod p := redMatrix p g 0 0 / redMatrix p g 1 0
        with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 1 1 - g 1 0 * y.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hy, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
          mul_div_cancel₀ _ hc, sub_self]
      obtain ⟨g', hg', hmul⟩ := heckeDiagMatrix_mul_of_eq hp g y.val e (by linear_combination he)
      exact ⟨g', hg' ▸ hg, hmul⟩
  | coe j =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h : redMatrix p g 1 0 * j + redMatrix p g 1 1 = 0
    ·
      rw [ite_eq_left h, heckeRep_infty, heckeRep_coe]
      rw [redMatrix_apply_one_zero, redMatrix_apply_one_one] at h
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 0 + j.val * g 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination h
      obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_eq' hp g j.val e he
      exact ⟨g', hg' ▸ hg, hmul⟩
    ·
      rw [ite_eq_right h, heckeRep_coe, heckeRep_coe]
      set y : ZMod p := (redMatrix p g 0 0 * j + redMatrix p g 0 1) /
        (redMatrix p g 1 0 * j + redMatrix p g 1 1) with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + j.val * g 1 1 - y.val * (g 0 0 + j.val * g 1 0) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
          show ((g 0 0 : ℤ) : ZMod p) + j * ((g 1 0 : ℤ) : ZMod p)
            = redMatrix p g 1 0 * j + redMatrix p g 1 1 by
              rw [redMatrix_apply_one_zero, redMatrix_apply_one_one]; ring,
          hy, div_mul_cancel₀ _ h, redMatrix_apply_zero_zero, redMatrix_apply_zero_one]
        ring
      obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_eq hp g j.val y.val e (by linear_combination he)
      exact ⟨g', hg' ▸ dvd_mul_of_dvd_right hg _, hmul⟩

variable {N : ℕ} (k : ℤ)

theorem heckeT_slash_mapGL (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    heckeT k p f ∣[k] (mapGL ℝ g) = heckeT k p f := by
  have hcN : (N : ℤ) ∣ g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hg)
  rw [heckeT_eq_sum_onePoint k f, SlashAction.sum_slash]
  calc ∑ x : OnePoint (ZMod p), (f ∣[k] heckeRep p x) ∣[k] mapGL ℝ g
      = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p (redMatrix p g • x) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hmul⟩ := heckeRep_mul hpN g hcN x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N :=
          CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hg')
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg'N)]
    _ = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x :=
        Equiv.sum_comp (MulAction.toPerm (redMatrix p g)) (fun x ↦ f ∣[k] heckeRep p x)

end heckeT

end ModularForm.HeckeRepresentatives

end
