/-
  Tier 1 of the Hecke slash-invariance layer: where `U_p`/`T_p` land.

  Three public statements, verbatim from their `Theorems/` wrappers (pinned
  `aa2d8b3`):

  - `heckeU_slash_eq_self_of_mem_Gamma0` (`p ∣ N`),
  - `heckeT_slash_eq_self_of_mem_Gamma0` (`p` prime, `p ∤ N`),
  - `heckeU_slash_eq_self_of_mem_Gamma0_div` (`p² ∣ N`, the lowering step).

  They are ~10-line wrappers around the shared block's workhorses
  `heckeU_slash_mapGL`/`heckeT_slash_mapGL` in
  `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean`; the only extra
  content is the `_div` case's `Γ₀(N/p) ↪ Γ₀(N)` bookkeeping (the pin's
  `heckeU_slash_mapGL_of_sq_dvd`, kept `private` here because it is not an FLT
  node).

  The Fricke pair (`heckeU_add_slash_fricke_eq_zero` and
  `exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke`) now lives in
  `FLTForHuman/ModularForms/HeckeFricke.lean`, developed once through mathlib's
  `ModularForm.trace`; this module imports it.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean`,
  `…_Gamma0_div.lean`. Statements verbatim from the wrappers; proofs adapted to
  mathlib `v4.34.0` where the pin's `P2M` prelude differs — proof-only.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Algebra.Field.ZMod
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives
import FLTForHuman.ModularForms.HeckeFricke

set_option autoImplicit false

-- The pin's `haveI`/`letI` walls are kept literal (as in the `WeilExchange` set).
set_option linter.style.haveILetI false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ModularForm

open ModularForm.HeckeRepresentatives

namespace ModularForm

/-- `U_p` preserves `Γ₀(N)`-invariance when `p ∣ N`. Stated verbatim from
`Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean`. -/
theorem heckeU_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hpN : p ∣ N) {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) : SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  haveI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  exact heckeU_slash_mapGL k hpN f hf g hg

/-- `T_p` preserves `Γ₀(N)`-invariance when `p` is prime and `p ∤ N`. Stated
verbatim from `Theorems/Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0.lean`. -/
theorem heckeT_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {f : UpperHalfPlane → ℂ} (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)), SlashAction.map k γ f = f) (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ) (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) : SlashAction.map k γ (ModularForm.heckeT k p f) = ModularForm.heckeT k p f := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  exact heckeT_slash_mapGL k hpN f hf g hg

/-- The `p² ∣ N` lowering step: `U_p f` is invariant under `Γ₀(N/p)` when `f` is
invariant under `Γ₀(N)`. Private helper: the pin's
`heckeU_slash_mapGL_of_sq_dvd`, which has no `Theorems/` wrapper of its own. -/
private theorem heckeU_slash_mapGL_of_sq_dvd {N : ℕ} (k : ℤ) {p : ℕ} [NeZero p] (hp2N : p ^ 2 ∣ N)
    (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 (N / p)) :
    heckeU k p f ∣[k] (mapGL ℝ g) = heckeU k p f := by
  have hpN : p ∣ N := (dvd_pow_self p two_ne_zero).trans hp2N
  have hpNp : p ∣ N / p := (Nat.dvd_div_iff_mul_dvd hpN).mpr (by rw [← pow_two]; exact hp2N)
  have hcNp : ((N / p : ℕ) : ℤ) ∣ g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hg)
  have hc : (p : ℤ) ∣ g 1 0 := (Int.natCast_dvd_natCast.mpr hpNp).trans hcNp
  rw [heckeU_eq_sum_zmod k f, SlashAction.sum_slash]
  calc ∑ x : ZMod p, (f ∣[k] heckeMatrix p x.val) ∣[k] mapGL ℝ g
      = ∑ x : ZMod p, f ∣[k] heckeMatrix p
          (affinePerm g ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc) x).val := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_dvd g hc x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N := by
          rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, hg']
          have hN : (N : ℤ) = (p : ℤ) * ((N / p : ℕ) : ℤ) := by
            rw [← Nat.cast_mul, Nat.mul_div_cancel' hpN]
          rw [hN]
          exact mul_dvd_mul_left (p : ℤ) hcNp
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg'N)]
    _ = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val :=
        Equiv.sum_comp (affinePerm g _) (fun x ↦ f ∣[k] heckeMatrix p x.val)

/-- `U_p` is invariant under `Γ₀(N/p)` when `p² ∣ N` and `f` is invariant under
`Γ₀(N)`. Stated verbatim from
`Theorems/Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div.lean`. -/
theorem heckeU_slash_eq_self_of_mem_Gamma0_div {N : ℕ} (k : ℤ) {p : ℕ} (hp2N : p ^ 2 ∣ N) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)),
      SlashAction.map k γ f = f)
    (γ : Matrix.GeneralLinearGroup (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 (N / p) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  haveI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  exact heckeU_slash_mapGL_of_sq_dvd k hp2N f hf g hg

end ModularForm

end
