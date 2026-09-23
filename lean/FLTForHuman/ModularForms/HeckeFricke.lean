/-
  The Fricke pair at prime level — one development, two public theorems.

  FLT proves the two Fricke statements in two independent `S_` files
  (`S_ModularForm_heckeU_add_slash_fricke_eq_zero.lean`, 229 lines, and
  `S_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke.lean`,
  302 lines) that share nothing: the second re-derives a hand-rolled trace
  (`traceFun`/`traceForm`/`trace_slash_*`/`trace_holo`/`trace_bdd` plus fifteen
  `T`/`S`-generator helpers) although the first already uses mathlib's
  `ModularForm.trace` (`Mathlib/NumberTheory/ModularForms/NormTrace.lean:82`).

  This module writes that shared trace **once**, through mathlib:

  * `R j = S * T^j` — the coset representative `!![0, -1; 1, j]` of the pin's
    `HeckeFricke` half is mathlib's `ModularGroup.S * ModularGroup.T ^ j`;
  * `slash_scalar` — the general scalar slash `f ∣[k] scalar u = u^(k-2) • f`
    (`u : ℝˣ`), from which the weight-2 instance and the `scalar p` instance are
    corollaries;
  * `coe_trace_eq` — the bridge from `ModularForm.coe_trace` to the explicit
    `⇑X + ∑ j ∈ range p, X ∣[k] (S * T^j)` form the `U_p ∣ W` computation
    consumes, built from the coset quotient (`sum_quotientFunc_eq`) that the
    pin's hand-rolled trace was reconstructing;
  * `heckeU_slash_W` — the single general-weight `U_p (X ∣ W)` display.

  The two public statements keep their names, binders and types verbatim from
  their `Theorems/` wrappers (pinned `aa2d8b3`); the port's old private copies of
  the trace and the fifteen generator helpers are gone.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularForm_heckeU_add_slash_fricke_eq_zero.lean`,
  `P2M/Sol/S_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke.lean`.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.NumberTheory.ModularForms.NormTrace
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives

set_option autoImplicit false

-- The pin's `haveI`/`letI` walls are kept literal (as in the `WeilExchange` set).
set_option linter.style.haveILetI false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

open ModularForm.HeckeRepresentatives

namespace ModularForm

namespace HeckeFricke

/-! ## The coset representative `R` and the identification `R j = S * T^j` -/

/-- The coset representative `!![0, -1; 1, j]`, as in the pin's Fricke half. -/
private def R (j : ℤ) : SL(2, ℤ) := ⟨!![0, -1; 1, j], by simp [Matrix.det_fin_two_of]⟩

@[simp] private theorem coe_R (j : ℤ) :
    ((R j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, j] := rfl

private theorem R_apply_10 (j : ℤ) : (R j : SL(2, ℤ)) 1 0 = 1 := rfl

private theorem R_inv_apply_10 (j : ℤ) : ((R j)⁻¹ : SL(2, ℤ)) 1 0 = -1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

private theorem R_mul_R_inv_apply_10 (i j : ℤ) : ((R i) * (R j)⁻¹ : SL(2, ℤ)) 1 0 = j - i := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

private theorem R_mul_apply_10 (j : ℤ) (g : SL(2, ℤ)) :
    ((R j) * g : SL(2, ℤ)) 1 0 = g 0 0 + j * g 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem coe_T_pow (j : ℕ) : ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
    = !![1, (j : ℤ); 0, 1] := by
  rw [← zpow_natCast, ModularGroup.coe_T_zpow]

private theorem coe_T_pow' (j : ℕ) :
    ((ModularGroup.T : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) ^ j = !![1, (j : ℤ); 0, 1] := by
  rw [← Matrix.SpecialLinearGroup.coe_pow, coe_T_pow]

/-- `R j = S * T^j`: the pin's coset representative is the standard
`S`/`T`-word. This is the one identification the two halves shared but neither
proved. -/
private theorem R_eq_S_mul_T_pow (j : ℕ) :
    R (j : ℤ) = ModularGroup.S * ModularGroup.T ^ j := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i l => ?_
  rw [coe_R, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_S,
    Matrix.SpecialLinearGroup.coe_pow, coe_T_pow']
  fin_cases i <;> fin_cases l <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The general scalar slash -/

/-- `f ∣[k] scalar u = u^(k-2) • f` for any unit `u : ℝˣ`. The pin proves only
the weight-2 case (`slash_two_scalar`) in the first half and the `scalar p` case
(`slash_scalar`) in the second; this is both at once. -/
private theorem slash_scalar (k : ℤ) (f : ℍ → ℂ) (u : ℝˣ) :
    f ∣[k] (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = (u : ℂ) ^ (k - 2) • f := by
  ext τ
  have hdet : (((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝˣ) : ℝ) = u * u := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.scalar, sq]
  have hpos : 0 < (((Matrix.GeneralLinearGroup.scalar (Fin 2) u).det : ℝˣ) : ℝ) := by
    rw [hdet]; exact mul_self_pos.mpr u.ne_zero
  have hu : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast u.ne_zero
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, ite_eq_left hpos, hdet,
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar, abs_mul_self]
  simp only [ContinuousAlgEquiv.refl_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  have key : ((u : ℂ) * (u : ℂ)) ^ (k - 1) * (u : ℂ) ^ (-k) = (u : ℂ) ^ (k - 2) := by
    rw [← pow_two, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu]
    congr 1
    ring
  rw [mul_assoc, key, mul_comm]

private theorem slash_two_scalar (f : ℍ → ℂ) (u : ℝˣ) :
    f ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.scalar (Fin 2) u) = f := by
  rw [slash_scalar 2 f u]
  simp

/-! ## The trace bridge

`ModularForm.trace 𝒮ℒ X` is mathlib's bundled trace; `coe_trace` says its
coercion is the quotient sum `∑ q, quotientFunc X q`. `sum_quotientFunc_eq`
enumerates that quotient by the coset list `{1} ∪ {R j}` — the content the pin's
hand-rolled `traceFun` re-derived — and `coe_trace_eq` rewrites the result into
the `S * T^j` form the `U_p ∣ W` computation consumes. -/

private noncomputable abbrev mk' : SL(2, ℤ) →* ↥𝒮ℒ := (Matrix.SpecialLinearGroup.mapGL ℝ).rangeRestrict

private abbrev Γ (p : ℕ) : Subgroup (GL (Fin 2) ℝ) := (CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ))

private abbrev Q (p : ℕ) := ↥𝒮ℒ ⧸ ((Γ p).subgroupOf 𝒮ℒ)

private theorem mk_eq_mk_iff (p : ℕ) (a b : SL(2, ℤ)) :
    (⟦mk' a⟧ : Q p) = ⟦mk' b⟧ ↔ a⁻¹ * b ∈ CongruenceSubgroup.Gamma0 p := by
  rw [Quotient.eq, QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, ← map_inv, ← map_mul]
  exact Subgroup.mem_map_iff_mem Matrix.SpecialLinearGroup.mapGL_injective

private theorem mk'_surjective : Function.Surjective mk' := MonoidHom.rangeRestrict_surjective _

private noncomputable def ι (p : ℕ) : Option (Fin p) → Q p
  | none => ⟦mk' 1⟧
  | some j => ⟦mk' (R (j : ℕ))⁻¹⟧

private theorem ι_bijective (p : ℕ) [hp : Fact p.Prime] : Function.Bijective (ι p) := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  constructor
  · rintro (_ | i) (_ | j) h
    · rfl
    · exfalso
      simp only [ι] at h
      rw [mk_eq_mk_iff, inv_one, one_mul, CongruenceSubgroup.Gamma0_mem, R_inv_apply_10] at h
      simp at h
    · exfalso
      simp only [ι] at h
      rw [mk_eq_mk_iff, inv_inv, mul_one, CongruenceSubgroup.Gamma0_mem, R_apply_10] at h
      simp at h
    · simp only [ι] at h
      rw [mk_eq_mk_iff, inv_inv, CongruenceSubgroup.Gamma0_mem, R_mul_R_inv_apply_10] at h
      push_cast at h
      rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff'] at h
      congr 1
      exact Fin.ext (by
        rw [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt i.isLt] at h
        exact h.symm)
  · intro q
    induction q using Quotient.inductionOn with
    | h x =>
      obtain ⟨g, rfl⟩ := mk'_surjective x
      by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
      · refine ⟨none, ?_⟩
        simp only [ι]
        rw [mk_eq_mk_iff, inv_one, one_mul, CongruenceSubgroup.Gamma0_mem]
        exact hc
      · set j : ZMod p := -((g 0 0 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p)⁻¹ with hj
        refine ⟨some ⟨j.val, ZMod.val_lt j⟩, ?_⟩
        simp only [ι]
        rw [mk_eq_mk_iff, inv_inv, CongruenceSubgroup.Gamma0_mem, R_mul_apply_10]
        push_cast
        rw [ZMod.natCast_zmod_val, hj]
        field_simp
        ring

private theorem quotientFunc_ι_none (p : ℕ) (k : ℤ) (f : ModularForm (Γ p) k) :
    SlashInvariantForm.quotientFunc f (ι p none) = ⇑f := by
  simp [ι, SlashInvariantForm.quotientFunc_mk]

private theorem quotientFunc_ι_some (p : ℕ) (k : ℤ) (f : ModularForm (Γ p) k) (j : Fin p) :
    SlashInvariantForm.quotientFunc f (ι p (some j)) =
      ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ) := by
  simp [ι, SlashInvariantForm.quotientFunc_mk]

/-- The quotient sum over the coset list `{1} ∪ {R j}`: the concrete form of
`ModularForm.coe_trace`. The pin states it at weight 2 (its Fricke half); the
level-one half needs it at general weight, so it is stated once here. -/
private theorem sum_quotientFunc_eq (p : ℕ) [Fact p.Prime] (k : ℤ) (f : ModularForm (Γ p) k)
    [Fintype (Q p)] :
    ∑ q : Q p, SlashInvariantForm.quotientFunc f q =
      ⇑f + ∑ j : Fin p, ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ) := by
  rw [← (Equiv.ofBijective (ι p) (ι_bijective p)).sum_comp, Fintype.sum_option]
  simp only [Equiv.ofBijective_apply, quotientFunc_ι_none, quotientFunc_ι_some]

/-- Reindex the coset sum as `∑ j ∈ range p` and identify `R j` with `S * T^j`. -/
private theorem sum_fin_eq_sum_range_u {p : ℕ} (k : ℤ) (f : ModularForm (Γ p) k) :
    ∑ j : Fin p, ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ)
      = ∑ j ∈ Finset.range p, ⇑f ∣[k] (ModularGroup.S * ModularGroup.T ^ j) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => ⇑f ∣[k]
    (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ)) p]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [R_eq_S_mul_T_pow]
  exact (ModularForm.SL_slash (k := k) ⇑f (ModularGroup.S * ModularGroup.T ^ j)).symm

/-! ## The `U_p ∣ W` computation -/

/-- `W * heckeMatrix p j = scalar p * (S * T^j)` for the Fricke matrix `W`. -/
private theorem fricke_mul_heckeMatrix (p : ℕ) (hp : p ≠ 0) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) (j : ℕ) :
    W * ModularForm.heckeMatrix p j =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (p : ℝ) (by exact_mod_cast hp)) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (R (j : ℕ)) : GL (Fin 2) ℝ) := by
  ext i k
  rw [Units.val_mul, Units.val_mul, hW, ModularForm.val_heckeMatrix hp,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply]
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar,
      Units.coe_map, Matrix.map_apply, R, Matrix.natCast_apply]

/-- The `j`-th translate `X ∣[k] (S * T^j)` summed by `U_p`. -/
private noncomputable def u {p : ℕ} {k : ℤ} (X : ModularForm (Γ p) k) (j : ℕ) : ℍ → ℂ :=
  ⇑X ∣[k] (ModularGroup.S * ModularGroup.T ^ j)

/-- `U_p (X ∣ W) = p^(k-2) • ∑ j ∈ range p, X ∣ (S * T^j)` at general weight. The
weight-2 Fricke relation is the `k = 2` instance (`p^0 = 1`); the pin proves the
two cases separately, the weight-2 one in the other `S_` file. -/
private theorem heckeU_slash_W {p : ℕ} [Fact p.Prime] {k : ℤ} (X : ModularForm (Γ p) k)
    (W : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU k p (⇑X ∣[k] W) = (p : ℂ) ^ (k - 2) • ∑ j ∈ Finset.range p, u X j := by
  rw [ModularForm.heckeU_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpu : ((p : ℝ)) ≠ 0 := by exact_mod_cast hp
  rw [← SlashAction.slash_mul]
  rw [fricke_mul_heckeMatrix p hp W hW j, R_eq_S_mul_T_pow j, SlashAction.slash_mul,
    slash_scalar]
  exact ModularForm.SL_smul_slash k (ModularGroup.S * ModularGroup.T ^ j) ⇑X ((p : ℂ) ^ (k - 2))

/-- The coercion of mathlib's trace in the explicit `S * T^j` form. -/
private theorem coe_trace_eq {p : ℕ} [Fact p.Prime] {k : ℤ} (X : ModularForm (Γ p) k) :
    ⇑(ModularForm.trace 𝒮ℒ X) = ⇑X + ∑ j ∈ Finset.range p, u X j := by
  rw [ModularForm.coe_trace, sum_quotientFunc_eq, sum_fin_eq_sum_range_u]
  rfl

/-! ## The weight-2 vanishing `U_p f + f ∣ W = 0` -/

private theorem main (p : ℕ) [hp : Fact p.Prime] (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p (⇑f ∣[(2 : ℤ)] W) + ⇑f = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have h0 : ModularForm.trace 𝒮ℒ f = 0 :=
    rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero _
  have h1 := congrArg (fun g : ModularForm 𝒮ℒ 2 => (⇑g : ℍ → ℂ)) h0
  simp only [ModularForm.coe_trace, FunLike.coe_zero] at h1
  rw [sum_quotientFunc_eq, sum_fin_eq_sum_range_u] at h1
  rw [heckeU_slash_W f W hW, show (2 : ℤ) - 2 = 0 by norm_num, zpow_zero, one_smul, add_comm]
  exact h1

private def frickeConj (p : ℕ) (g : SL(2, ℤ)) (hg : (p : ℤ) ∣ g 1 0) : SL(2, ℤ) :=
  ⟨!![g 1 1, -(g 1 0 / p); -(p * g 0 1), g 0 0], by
    have hdet := Matrix.det_fin_two g.1
    rw [g.2] at hdet
    rw [Matrix.det_fin_two_of]
    have := Int.ediv_mul_cancel hg
    linear_combination (-1 : ℤ) * hdet - (g 0 1) * this⟩

private theorem frickeConj_mem (p : ℕ) (g : SL(2, ℤ)) (hg : (p : ℤ) ∣ g 1 0) :
    frickeConj p g hg ∈ CongruenceSubgroup.Gamma0 p := by
  rw [CongruenceSubgroup.Gamma0_mem]
  show (((!![g 1 1, -(g 1 0 / p); -(p * g 0 1), g 0 0] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) :
    ZMod p) = 0
  simp

private theorem fricke_mul_mapGL (p : ℕ) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0])
    (g : SL(2, ℤ)) (hg : (p : ℤ) ∣ g 1 0) :
    W * (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) =
      (Matrix.SpecialLinearGroup.mapGL ℝ (frickeConj p g hg) : GL (Fin 2) ℝ) * W := by
  have hc : (((g 1 0 / p : ℤ) : ℝ)) * (p : ℝ) = ((g 1 0 : ℤ) : ℝ) := by
    exact_mod_cast Int.ediv_mul_cancel hg
  ext i k
  rw [Units.val_mul, Units.val_mul, hW, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply]
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, frickeConj, Matrix.map_apply] <;> linarith [hc]

open ConjAct Pointwise in
private theorem le_conj (p : ℕ) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    Γ p ≤ toConjAct W⁻¹ • Γ p := by
  rintro x ⟨g, hg, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← toConjAct_inv, inv_inv, toConjAct_smul]
  have hg' : (p : ℤ) ∣ g 1 0 := by
    have := (CongruenceSubgroup.Gamma0_mem (N := p) (A := g)).mp hg
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  rw [fricke_mul_mapGL p W hW g hg', mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨_, frickeConj_mem p g hg', rfl⟩

open ConjAct Pointwise in

private noncomputable def slashFricke (p : ℕ) (f : ModularForm (Γ p) 2) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ModularForm (Γ p) 2 where
  toFun := ⇑f ∣[(2 : ℤ)] W
  slash_action_eq' γ hγ := (ModularForm.translate f W).slash_action_eq' γ (le_conj p W hW hγ)
  holo' := (ModularForm.translate f W).holo'
  bdd_at_cusps' hc := (ModularForm.translate f W).bdd_at_cusps' (hc.mono (le_conj p W hW))

private theorem coe_slashFricke (p : ℕ) (f : ModularForm (Γ p) 2) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ⇑(slashFricke p f W hW) = ⇑f ∣[(2 : ℤ)] W := rfl

private theorem fricke_mul_self (p : ℕ) (hp : p ≠ 0) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    W * W = Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 (-(p : ℝ)) (neg_ne_zero.mpr (by exact_mod_cast hp))) := by
  ext i k
  rw [Units.val_mul, hW]
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.scalar]

private theorem main' (p : ℕ) [hp : Fact p.Prime] (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p ⇑f + ⇑f ∣[(2 : ℤ)] W = 0 := by
  have h := main p (slashFricke p f W hW) W hW
  rwa [coe_slashFricke, ← SlashAction.slash_mul, fricke_mul_self p hp.out.ne_zero W hW,
    slash_two_scalar] at h

end HeckeFricke

/-- The `U_p`-plus-Fricke relation at prime level: `U_p f + f ∣ W = 0`. Stated
verbatim from `Theorems/Thm_ModularForm_heckeU_add_slash_fricke_eq_zero.lean`. -/
theorem heckeU_add_slash_fricke_eq_zero (p : ℕ) [Fact p.Prime]
    (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (W : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p ⇑f + ⇑f ∣[(2 : ℤ)] W = 0 :=
  HeckeFricke.main' p f W hW

/-! ## The level-one Fricke image

The `U_p`-plus-Fricke combination produces a level-one form. The pin builds the
trace by hand here; this module uses `ModularForm.trace 𝒮ℒ X` and the coercion
bridge `HeckeFricke.coe_trace_eq`. -/

/-- The level-one image of the `U_p`-plus-Fricke combination. Stated verbatim
from
`Theorems/Thm_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke.lean`. -/
theorem exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke (p : ℕ) [Fact p.Prime]
    (k : ℤ) (X : ModularForm (CongruenceSubgroup.Gamma0 p) k) (W : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hW : ((W : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1; (p : ℝ), 0]) :
    ∃ Y : ModularForm 𝒮ℒ k, ⇑Y = (p : ℂ) ^ (k - 2) • ⇑X + ModularForm.heckeU k p (⇑X ∣[k] W) := by
  refine ⟨(p : ℂ) ^ (k - 2) • ModularForm.trace 𝒮ℒ X, ?_⟩
  rw [HeckeFricke.heckeU_slash_W X W hW]
  show (p : ℂ) ^ (k - 2) • ⇑(ModularForm.trace 𝒮ℒ X)
      = (p : ℂ) ^ (k - 2) • ⇑X + (p : ℂ) ^ (k - 2) • ∑ j ∈ Finset.range p, HeckeFricke.u X j
  rw [HeckeFricke.coe_trace_eq X, smul_add]

end ModularForm

end
