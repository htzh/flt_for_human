/-
  The Petersson adjointness of the Hecke operator on a nebentypus component:
  `⟨T_p f, g⟩ = conj ε(p) ⟨f, T_p g⟩` for `f, g` with nebentypus `ε`, where
  `T_p f = heckeU k p f + ε(p) • (f ∣ heckeDiagMatrix p)`.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean:17–1212`,
  taken whole (119 public declarations, none `private`), less its top-level
  `solution`, which is re-proved in the tier-1 façade
  `FLTForHuman/ModularForms/Analytic/PeterssonHeckeTheorems.lean`.

  **Port-owned, tier 3.** The pin is parked in
  `Reserve/ModularForms/PortOwnedSpecPins.lean` and the departures are registered in
  `topics/TOPIC-interface-changes.md` Entry 7; nothing here is statement-diffed. The
  module carries 66 public declarations against the pin's 118. Two layers of the
  pin's file are statement-identical to declarations the port already owns and are
  imported rather than re-proved.

  The pin wrote its group-and-pairing layer twice; the port carries **one** copy, in the
  wired definition layer `PeterssonCoset.lean`: its 16 coset-integral declarations
  (`mp_smul_*`, `measurable_smul_*`, `splitEquiv`, the `tsum_*` reindexings, `wt`,
  `measurable_wt`, `indicator_smul`, `ae_tsum_wt_smul`,
  `weight_lintegral`, `cvn_lintegral`, `cosum`, `petersson_polarization`) moved there on
  2026-10-18, and this module's remaining 15 — the admissible-function predicate
  (`Nice`), `dens`, `dens_nonneg`, `petersson_self_eq_dens`, `continuous_dens`,
  `Nice.dens_smul`, the `Nice` algebra, `unfold_sum`, and the integral triple
  `integral_cosum_self`/`integral_cosum_polar`/`integral_cosum_pair` — were dropped in
  its favour on the next pass. What stays here is the Hecke-specific part: the
  representatives `rr`, the `Λ`-coset unfolding, `Φ`/`Ψ`, the character identities and
  the assembly. The bookkeeping layer — `det_entries` (`PeterssonCoset`) and `det_mod`,
  `dd`, `dd_mul`, `isUnit_dd`, the `Γ₀`
  lower-right character (`ModularForm.Level`) — is imported from its one home and
  opened below, as is `Γ⁰(p)` (`ModularForms/Level/Upper.lean`), the factor of
  `Λ = Γ₁(N) ⊓ Γ⁰(p)`.

  The interface is the port's in four places (Entry 7): `Lam` is `Γ₁(N) ⊓ Γ⁰(p)`
  rather than a hand-rolled carrier, with `dvd_01_of_mem_Lam` as its upper-right
  eliminator; the Bézout datum is `Level.BezoutPair` with no sign-translating `bez`;
  `conjSL_mem_Gamma1`/`cfwd_coe` name their divisibility witness through that
  eliminator; and the two one-use entry computations `upperRight_T_mul`,
  `upperRight_gInf_mul` are inlined at their site. `mem_Lam` keeps the pin's
  statement, so the two conditions stay readable at every use.

  The proof: unfold `peterssonOn` (coset sum over `SL(2, ℤ) ⧸ Γ₁(N)`, integrated
  over `𝒟`), distribute the density over the `p + 1` representatives `rr`, reindex
  the coset sum over the smaller group `Lam N p` by `unfold_sum`, and apply the
  integral invariance `integral_cosum_pair` plus `Complex.inv_eq_conj` for the
  nebentypus character.
-/
import FLTForHuman.AutomorphicForm.UpperHalfPlane.ModularFundamentalDomain
import FLTForHuman.ModularForms.Analytic.Petersson
import FLTForHuman.ModularForms.Analytic.PeterssonCoset
import FLTForHuman.ModularForms.Defs.Gamma1HeckeOperators
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.Level.Diamond
import FLTForHuman.ModularForms.Level.Upper
import FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupOrder
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter CongruenceSubgroup
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace CuspForm

namespace PetHeckeAdj

/-- The coercion of `mapGL` to matrices, in the spelling the `rw` chains below need (mathlib's
`Matrix.SpecialLinearGroup.mapGL_coe_matrix` states the same fact with the coercion left inside
`SpecialLinearGroup.map`). -/
private theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) :=
  Matrix.SpecialLinearGroup.mapGL_coe_matrix s

open CuspForm.PeterssonCoset
open ModularForm.Level (dd mem_Gamma1_of_d_eq_one Gamma0Upper mem_Gamma0Upper
  mem_Gamma0Upper_iff_dvd Gamma_le_Gamma0Upper)

private theorem mul_apply_10 (A B : SL(2, ℤ)) :
    ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
        + (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
  (Matrix.two_mul_expl _ _).2.2.1

private theorem mul_apply_01 (A B : SL(2, ℤ)) :
    ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
      = (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (B : Matrix (Fin 2) (Fin 2) ℤ) 0 1
        + (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 1 :=
  (Matrix.two_mul_expl _ _).2.1

private theorem mul_apply_00 (A B : SL(2, ℤ)) :
    ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
      = (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
        + (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
  (Matrix.two_mul_expl _ _).1

private theorem mul_apply_11 (A B : SL(2, ℤ)) :
    ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1
      = (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (B : Matrix (Fin 2) (Fin 2) ℤ) 0 1
        + (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 1 :=
  (Matrix.two_mul_expl _ _).2.2.2

-- `det_heckeMatrix` is public in `ModularForms/Defs/HeckeOperator.lean` (it was
-- `private` until 2026-10-18); the local copy that stood here is gone.

private theorem mem_Gamma1_iff (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ Gamma1 N ↔ (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod N) = 1 ∧
      (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = 1 ∧
      (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [Gamma1_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

section Slash

variable {N : ℕ} {k : ℤ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
theorem slash_mem (g : CuspForm Γ₁(N) k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
  SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

end Slash

section Lam

variable {N p : ℕ}

/-- `Λ = Γ₁(N) ⊓ Γ⁰(p)`: the elements of `Γ₁(N)` whose upper-right entry vanishes modulo `p`,
i.e. the subgroup of `Γ₁(N)` that fixes the `p + 1` Hecke cosets of `rr`. -/
def Lam (N p : ℕ) : Subgroup SL(2, ℤ) := (Gamma1 N : Subgroup SL(2, ℤ)) ⊓ Gamma0Upper p

theorem mem_Lam (γ : SL(2, ℤ)) :
    γ ∈ Lam N p ↔ γ ∈ Gamma1 N ∧ (p : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
  rw [show γ ∈ Lam N p ↔ γ ∈ (Gamma1 N : Subgroup SL(2, ℤ)) ∧ γ ∈ Gamma0Upper p
    from Subgroup.mem_inf]
  exact and_congr_right fun _ => mem_Gamma0Upper_iff_dvd

/-- The divisibility that `Lam`-membership gives on the upper-right entry. -/
theorem dvd_01_of_mem_Lam {γ : SL(2, ℤ)} (hγ : γ ∈ Lam N p) :
    (p : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 :=
  mem_Gamma0Upper_iff_dvd.mp hγ.2

theorem Lam_le (N p : ℕ) : Lam N p ≤ Gamma1 N := inf_le_left

theorem Gamma_le_Lam (N p : ℕ) : Gamma (p * N) ≤ Lam N p :=
  le_inf ((Gamma_le_of_dvd (dvd_mul_left N p)).trans Gamma_le_Gamma1)
    (Gamma_le_Gamma0Upper (dvd_mul_right p N))

scoped instance Lam_finiteIndex (N p : ℕ) [NeZero N] [NeZero p] : (Lam N p).FiniteIndex := by
  have hN : NeZero (p * N) := inferInstance
  have hcong : IsCongruenceSubgroup (Lam N p) := ⟨p * N, hN.ne, Gamma_le_Lam N p⟩
  exact hcong.finiteIndex

scoped instance fintypeQuotLam (N p : ℕ) [NeZero N] [NeZero p] : Fintype (SL(2, ℤ) ⧸ Lam N p) :=
  haveI : Finite (SL(2, ℤ) ⧸ Lam N p) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

scoped instance fintypeQuot (M : ℕ) [NeZero M] : Fintype (SL(2, ℤ) ⧸ Gamma1 M) :=
  haveI : Finite (SL(2, ℤ) ⧸ Gamma1 M) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

/-- The Bézout datum of `(p, N)`, in the port's normalization `u * p + v * N = 1`: the Hecke
representatives `gInf`/`sigP` are its `matDiag`/`mat`, whose upper-right entry is `-v`. -/
private def bezPair (hpN : Nat.Coprime p N) : ModularForm.Level.BezoutPair (p : ℤ) (N : ℤ) :=
  (ModularForm.Level.BezoutPair.exists_of_coprime hpN).some

def gInf (hpN : Nat.Coprime p N) : SL(2, ℤ) := (bezPair hpN).matDiag

def sigP (hpN : Nat.Coprime p N) : SL(2, ℤ) := (bezPair hpN).mat

theorem gInf_coe (hpN : Nat.Coprime p N) :
    ((gInf hpN : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(bezPair hpN).u * p, -(bezPair hpN).v; (N : ℤ), 1] :=
  rfl

theorem sigP_coe (hpN : Nat.Coprime p N) :
    ((sigP hpN : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(bezPair hpN).u, -(bezPair hpN).v; (N : ℤ), (p : ℤ)] :=
  rfl

/-- `gInf = !![u * p, -v; N, 1]` is in `Γ₀(N)` because its lower-left entry is `N`, and in
`Γ₁(N)` because its lower-right entry is `1` — no Bézout input is needed, the upper-left entry
follows from the determinant. -/
theorem gInf_mem (hpN : Nat.Coprime p N) : gInf hpN ∈ Gamma1 N := by
  have hΓ₀ : gInf hpN ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show (((N : ℤ) : ZMod N)) = 0
    simp
  exact mem_Gamma1_of_d_eq_one hΓ₀ (by simp [dd, gInf])

theorem sigP_mem (hpN : Nat.Coprime p N) : sigP hpN ∈ Gamma0 N := by
  rw [Gamma0_mem]
  show (((N : ℤ) : ℤ) : ZMod N) = 0
  simp

theorem dd_sigP (hpN : Nat.Coprime p N) : dd (N := N) (sigP hpN) = (p : ZMod N) := by
  show (((p : ℤ) : ℤ) : ZMod N) = (p : ZMod N)
  simp

theorem not_dvd_n (hpN : Nat.Coprime p N) (hp : p ≠ 1) : ¬ (p : ℤ) ∣ (bezPair hpN).v := by
  rintro ⟨t, ht⟩
  have h := (bezPair hpN).huv
  rw [ht] at h
  have h1 : (p : ℤ) ∣ 1 := ⟨(bezPair hpN).u + t * N, by linear_combination -h⟩
  have hp1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h1
  exact hp (by exact_mod_cast hp1)

/-- The `p + 1` Hecke representatives of `Γ₁(N)` in the double coset of `diag(p, 1)`: the Bézout
lift `gInf` at `∞` (the coset on which `d` vanishes mod `p`), and the `p` translates `T ^ j`. -/
def rr (hpN : Nat.Coprime p N) : Option (Fin p) → SL(2, ℤ)
  | none => gInf hpN
  | some j => ModularGroup.T ^ ((j : ℕ) : ℤ)

private theorem T_zpow_mem_Gamma1 (N : ℕ) (t : ℤ) : ModularGroup.T ^ t ∈ Gamma1 N := by
  rw [mem_Gamma1_iff, ModularGroup.coe_T_zpow]; simp

theorem rr_mem (hpN : Nat.Coprime p N) (i : Option (Fin p)) : rr hpN i ∈ Gamma1 N := by
  cases i with
  | none => exact gInf_mem hpN
  | some j => exact T_zpow_mem_Gamma1 N _

/-- Every element of `Γ₁(N)` is one representative of `rr` away from `Λ` — the covering half of
the coset decomposition of `Γ₁(N)` by `Lam`, whose index is `p + 1`. -/
theorem exists_rr_mul_mem [NeZero p] (hpN : Nat.Coprime p N) (hp : p.Prime) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma1 N) : ∃ i : Option (Fin p), rr hpN i * γ ∈ Lam N p := by
  by_cases hd : (p : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  ·
    have h01 : ((gInf hpN * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1
        = (bezPair hpN).u * p * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
          + -(bezPair hpN).v * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
      rw [mul_apply_01, gInf_coe]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
    have hvanish : gInf hpN * γ ∈ Gamma0Upper p := by
      rw [mem_Gamma0Upper_iff_dvd, h01]
      exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_left (p : ℤ) _) _) (hd.mul_left _)
    have hΓ₁ : gInf hpN * γ ∈ (Gamma1 N : Subgroup SL(2, ℤ)) := mul_mem (gInf_mem hpN) hγ
    exact ⟨none, show gInf hpN * γ ∈ Lam N p from
      Subgroup.mem_inf.mpr ⟨hΓ₁, hvanish⟩⟩
  ·
    have hne : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p) ≠ 0 := fun h =>
      hd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
    have : Fact p.Prime := ⟨hp⟩
    set j : ZMod p := -((((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod p)
      * ((((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p))⁻¹) with hj
    have hj' : j * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p)
        = -(((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod p) := by
      rw [hj, neg_mul, mul_assoc, inv_mul_cancel₀ hne, mul_one]
    have h01 : ((ModularGroup.T ^ ((j.val : ℕ) : ℤ) * γ : SL(2, ℤ)) :
          Matrix (Fin 2) (Fin 2) ℤ) 0 1
        = (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
          + ((j.val : ℕ) : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 := by
      rw [mul_apply_01, ModularGroup.coe_T_zpow]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one]
      ring
    have hvanish : ModularGroup.T ^ ((j.val : ℕ) : ℤ) * γ ∈ Gamma0Upper p := by
      rw [mem_Gamma0Upper_iff_dvd, h01, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ZMod.natCast_zmod_val, hj']
      ring
    have hΓ₁ : ModularGroup.T ^ ((j.val : ℕ) : ℤ) * γ ∈ (Gamma1 N : Subgroup SL(2, ℤ)) :=
      mul_mem (T_zpow_mem_Gamma1 N _) hγ
    exact ⟨some ⟨j.val, ZMod.val_lt j⟩,
      show ModularGroup.T ^ ((j.val : ℕ) : ℤ) * γ ∈ Lam N p from
        Subgroup.mem_inf.mpr ⟨hΓ₁, hvanish⟩⟩

/-- `Λ` is upper triangular modulo `p`, so left multiplication by `g ∈ Λ` scales the upper row of
a matrix by `g`'s upper-left entry. -/
theorem upperRow_mul_of_mem_Lam {g : SL(2, ℤ)} (hg : g ∈ Lam N p) (γ : SL(2, ℤ)) :
    (((g * γ) 0 0 : ZMod p), ((g * γ) 0 1 : ZMod p))
      = (g 0 0 : ZMod p) • ((γ 0 0 : ZMod p), (γ 0 1 : ZMod p)) := by
  have h01 : (g 0 1 : ZMod p) = 0 := mem_Gamma0Upper.mp hg.2
  refine Prod.ext ?_ ?_
  · rw [mul_apply_00, Prod.smul_fst, smul_eq_mul]; push_cast; rw [h01]; ring
  · rw [mul_apply_01, Prod.smul_snd, smul_eq_mul]; push_cast; rw [h01]; ring

/-- The representatives of `rr` are distinct modulo `Λ` — the other half of the decomposition
`[Γ₁(N) : Lam] = p + 1`. An element of `Λ` scales the upper row, so `rr i = g * rr i'` forces the
upper rows of `rr i` and `rr i'` to agree up to that scalar, which the representatives' rows
`(u * p, -v)` and `(1, j)` never do. -/
theorem rr_mul_rr_inv_mem (hpN : Nat.Coprime p N) (hp : p.Prime) (i i' : Option (Fin p))
    (h : rr hpN i * (rr hpN i')⁻¹ ∈ Lam N p) : i = i' := by
  have : Fact p.Prime := ⟨hp⟩
  set g := rr hpN i * (rr hpN i')⁻¹ with hg
  set c : ZMod p := (g 0 0 : ZMod p) with hc
  have hgmul : g * rr hpN i' = rr hpN i := by rw [hg, mul_assoc, inv_mul_cancel, mul_one]
  have hrow : (((rr hpN i) 0 0 : ZMod p), ((rr hpN i) 0 1 : ZMod p))
      = c • (((rr hpN i') 0 0 : ZMod p), ((rr hpN i') 0 1 : ZMod p)) := by
    rw [← hgmul]
    simpa [hc] using upperRow_mul_of_mem_Lam h (rr hpN i')
  have hnone : (((rr hpN none) 0 0 : ZMod p), ((rr hpN none) 0 1 : ZMod p))
      = (0, -((bezPair hpN).v : ZMod p)) := by
    refine Prod.ext ?_ ?_ <;> simp [rr, gInf_coe]
  have hsome : ∀ j : Fin p,
      (((rr hpN (some j)) 0 0 : ZMod p), ((rr hpN (some j)) 0 1 : ZMod p))
        = (1, ((j : ℕ) : ZMod p)) := by
    intro j
    have hj : ((rr hpN (some j) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = !![1, ((j : ℕ) : ℤ); 0, 1] := ModularGroup.coe_T_zpow ((j : ℕ) : ℤ)
    refine Prod.ext ?_ ?_ <;> rw [hj] <;> simp
  have hv : ((bezPair hpN).v : ZMod p) ≠ 0 := fun h0 =>
    not_dvd_n hpN hp.one_lt.ne' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0)
  cases i with
  | none =>
    cases i' with
    | none => rfl
    | some j' =>
      exfalso
      rw [hnone, hsome j'] at hrow
      have hc0 : c = 0 := by simpa using (congrArg Prod.fst hrow).symm
      exact hv (by simpa [hc0] using congrArg Prod.snd hrow)
  | some j =>
    cases i' with
    | none =>
      exfalso
      rw [hsome j, hnone] at hrow
      have h10 : (1 : ZMod p) = 0 := by simpa using congrArg Prod.fst hrow
      exact one_ne_zero h10
    | some j' =>
      rw [hsome j, hsome j'] at hrow
      have hc1 : c = 1 := by simpa using (congrArg Prod.fst hrow).symm
      congr 1
      exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt
        ((ZMod.natCast_eq_natCast_iff (j : ℕ) (j' : ℕ) p).mp
          (by simpa [hc1] using congrArg Prod.snd hrow)) j.isLt j'.isLt)

end Lam

section Hecke

variable {N p : ℕ} {k : ℤ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev α (p : ℕ) : GL (Fin 2) ℝ := heckeMatrix p 0

theorem heckeMatrix_eq (hp : p ≠ 0) (j : ℕ) :
    heckeMatrix p j
      = α p * (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ (j : ℤ)) : GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [Units.val_mul, val_heckeMatrix hp, val_heckeMatrix hp, mapGL_coe_eq, ModularGroup.coe_T_zpow]
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]

theorem α_mul_gInf (hp : p ≠ 0) (hpN : Nat.Coprime p N) :
    α p * (Matrix.SpecialLinearGroup.mapGL ℝ (gInf hpN) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ (sigP hpN) : GL (Fin 2) ℝ) * heckeDiagMatrix p := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeMatrix hp, val_heckeDiagMatrix hp, mapGL_coe_eq,
    mapGL_coe_eq, gInf_coe, sigP_coe]
  ext i k; fin_cases i <;> fin_cases k <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]; try ring)

def Sc (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℝ :=
  upperTriangularGL p 0 p (by exact_mod_cast (mul_ne_zero hp hp))

theorem slash_Sc (k : ℤ) (hp : p ≠ 0) (f : ℍ → ℂ) :
    f ∣[k] Sc p hp = ((p : ℂ) ^ (k - 2)) • f := by
  have hqC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hdet : ((Sc p hp).det : ℝ) = ((p * p : ℕ) : ℝ) := by
    push_cast
    simp [Sc, Matrix.det_fin_two_of]
  have hdetpos : 0 < ((Sc p hp).det : ℝ) := by rw [hdet]; positivity
  have hσ : UpperHalfPlane.σ (Sc p hp) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, ite_eq_left hdetpos]
  funext τ
  have hdenom : UpperHalfPlane.denom (Sc p hp) τ = p := by
    simp [UpperHalfPlane.denom, Sc]
  have hsmul : (Sc p hp • τ : ℍ) = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos, hdenom]
    simp [UpperHalfPlane.num, Sc, hqC]
  rw [ModularForm.slash_apply, hσ, hdet, hdenom, hsmul, Pi.smul_apply, smul_eq_mul]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  push_cast
  rw [show ((p : ℂ) * p) = (p : ℂ) ^ (2 : ℤ) by rw [zpow_two], ← zpow_mul, mul_assoc,
    ← zpow_add₀ hqC, show (2 : ℤ) * (k - 1) + -k = k - 2 by ring, mul_comm]

theorem heckeDiagMatrix_mul_α (hp : p ≠ 0) : heckeDiagMatrix p * α p = Sc p hp := by
  apply Units.ext
  rw [Units.val_mul, val_heckeMatrix hp, val_heckeDiagMatrix hp]
  show _ = ((upperTriangularGL (p : ℝ) 0 p _ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [val_upperTriangularGL]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem heckeFun_eq_sum (hp : p ≠ 0) (hpN : Nat.Coprime p N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) :
    heckeFun k ε p ⇑f
      = ∑ i : Option (Fin p), (⇑f : ℍ → ℂ) ∣[k]
          (α p * (Matrix.SpecialLinearGroup.mapGL ℝ (rr hpN i) : GL (Fin 2) ℝ)) := by
  rw [Fintype.sum_option, heckeFun, add_comm]
  congr 1
  ·
    rw [rr, α_mul_gInf hp hpN, SlashAction.slash_mul, (hasNebentypus_iff ε f).mp hf _ (sigP_mem hpN),
      dd_sigP, ModularForm.smul_slash, σ_heckeDiagMatrix]
    rfl
  · rw [heckeU_def, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rr, heckeMatrix_eq hp]

theorem petersson_smul_left' (k : ℤ) (f g : ℍ → ℂ) (c : ℂ) (τ : ℍ) :
    UpperHalfPlane.petersson k (c • f) g τ = conj c * UpperHalfPlane.petersson k f g τ := by
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul, map_mul]; ring

theorem petersson_smul_SL (k : ℤ) (F G : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.petersson k (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ))
        (G ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
      = UpperHalfPlane.petersson k F G (γ • τ) :=
  UpperHalfPlane.petersson_slash_SL k F G γ τ

theorem petersson_transport (hp : p ≠ 0) (f g : ℍ → ℂ) (y : ℍ) :
    UpperHalfPlane.petersson k f (g ∣[k] α p) y
      = UpperHalfPlane.petersson k (f ∣[k] heckeDiagMatrix p) g (α p • y) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  set F : ℍ → ℂ := f ∣[k] heckeDiagMatrix p with hF
  have hFα : F ∣[k] α p = ((p : ℂ) ^ (k - 2)) • f := by
    rw [hF, ← SlashAction.slash_mul, heckeDiagMatrix_mul_α hp, slash_Sc]
  have h1 : UpperHalfPlane.petersson k (F ∣[k] α p) (g ∣[k] α p) y
      = ((p : ℂ) ^ (k - 2)) * UpperHalfPlane.petersson k F g (α p • y) := by
    rw [UpperHalfPlane.petersson_slash, σ_heckeMatrix, det_heckeMatrix hp]
    simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [hFα, petersson_smul_left'] at h1
  have hconj : conj ((p : ℂ) ^ (k - 2)) = (p : ℂ) ^ (k - 2) := by
    rw [map_zpow₀, Complex.conj_natCast]
  rw [hconj] at h1
  exact mul_left_cancel₀ (zpow_ne_zero _ hpC) h1

def Φ (k : ℤ) (p : ℕ) (f g : ℍ → ℂ) : ℍ → ℂ := UpperHalfPlane.petersson k (f ∣[k] α p) g

def Ψ (k : ℤ) (p : ℕ) (f g : ℍ → ℂ) : ℍ → ℂ := UpperHalfPlane.petersson k f (g ∣[k] α p)

theorem norm_char_p (ε : DirichletCharacter ℂ N) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ‖ε (p : ZMod N)‖ = 1 := by
  have hu : IsUnit ((p : ℕ) : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd hp).mpr hpN
  have := DirichletCharacter.unit_norm_eq_one ε hu.unit
  rwa [IsUnit.unit_spec] at this

theorem char_p_ne_zero (ε : DirichletCharacter ℂ N) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    ε (p : ZMod N) ≠ 0 := by
  intro h; have := norm_char_p ε hp hpN; rw [h, norm_zero] at this; exact zero_ne_one this

theorem slash_heckeDiagMatrix_eq (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) :
    (⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix p
      = (ε (p : ZMod N))⁻¹ • (((⇑f : ℍ → ℂ) ∣[k] α p) ∣[k]
          (Matrix.SpecialLinearGroup.mapGL ℝ (gInf ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)) :
            GL (Fin 2) ℝ)) := by
  set hpN' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  rw [← SlashAction.slash_mul, α_mul_gInf hp.ne_zero hpN', SlashAction.slash_mul,
    (hasNebentypus_iff ε f).mp hf _ (sigP_mem hpN'), dd_sigP, ModularForm.smul_slash,
    σ_heckeDiagMatrix]
  change _ = (ε (p : ZMod N))⁻¹ • (ε (p : ZMod N) • ((⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix p))
  rw [smul_smul, inv_mul_cancel₀ (char_p_ne_zero ε hp hpN), one_smul]

theorem Ψ_eq (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f g : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) (y : ℍ) :
    Ψ k p ⇑f ⇑g y = ε (p : ZMod N) *
      Φ k p ⇑f ⇑g (((Matrix.SpecialLinearGroup.mapGL ℝ
        (gInf ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)) : GL (Fin 2) ℝ) * α p) • y) := by
  set hpN' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  rw [Ψ, petersson_transport hp.ne_zero, slash_heckeDiagMatrix_eq hp hpN ε f hf, petersson_smul_left',
    ← slash_mem g (gInf_mem hpN'), petersson_smul_SL, slash_mem g (gInf_mem hpN'), mul_smul,
    map_inv₀, ← Complex.inv_eq_conj (norm_char_p ε hp hpN), inv_inv]
  rfl

end Hecke

-- The coset-integral layer that used to sit here — `mp_smul_*`, `measurable_smul_*`,
-- `splitEquiv`, the `tsum_*` reindexings, the weight function `wt`, `weight_lintegral`
-- and `cvn_lintegral` — is the definition layer
-- `ModularForms/Analytic/PeterssonCoset.lean` (namespace `CuspForm.PeterssonCoset`),
-- imported and opened above. The 18 declarations were statement-identical and are no
-- longer duplicated here (2026-10-18).

section Conj

variable {N p : ℕ}

def conjMat (p : ℕ) (h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(h : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / p;
    (p : ℤ) * (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1]

theorem det_conjMat (hp : p ≠ 0) {h : SL(2, ℤ)} (hh : (p : ℤ) ∣ (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1) :
    (conjMat p h).det = 1 := by
  obtain ⟨t, ht⟩ := hh
  have hq : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  rw [conjMat, Matrix.det_fin_two_of, ht, Int.mul_ediv_cancel_left _ hq]
  linear_combination det_entries h + (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * ht

def conjSL (hp : p ≠ 0) (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1) : SL(2, ℤ) :=
  ⟨conjMat p h, det_conjMat hp hh⟩

theorem conjSL_coe (hp : p ≠ 0) (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1) :
    ((conjSL hp h hh : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = conjMat p h := rfl

theorem conjSL_mem_Gamma1 (hp : p ≠ 0) {h : SL(2, ℤ)} (hh : h ∈ Lam N p) :
    conjSL hp h (dvd_01_of_mem_Lam hh) ∈ Gamma1 N := by
  have h1 := (mem_Gamma1_iff N h).mp hh.1
  rw [mem_Gamma1_iff, conjSL_coe]
  simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  exact ⟨h1.1, h1.2.1, dvd_mul_of_dvd_right h1.2.2 _⟩

theorem conjSL_lowerLeft (hp : p ≠ 0) {h : SL(2, ℤ)} (hh : (p : ℤ) ∣ (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1) :
    (p : ℤ) ∣ ((conjSL hp h hh : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [conjSL_coe]
  simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  exact dvd_mul_right _ _

theorem α_mul_conj (hp : p ≠ 0) (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1) :
    α p * (Matrix.SpecialLinearGroup.mapGL ℝ h : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ (conjSL hp h hh) : GL (Fin 2) ℝ) * α p := by
  obtain ⟨t, ht⟩ := hh
  have hq' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeMatrix hp, mapGL_coe_eq, mapGL_coe_eq, conjSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, conjMat, ht,
      Int.mul_ediv_cancel_left _ hq']; try ring)

def unconjMat (p : ℕ) (h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(h : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (p : ℤ) * (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
    (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / p, (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1]

theorem det_unconjMat (hp : p ≠ 0) {h : SL(2, ℤ)} (hh : (p : ℤ) ∣ (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (unconjMat p h).det = 1 := by
  obtain ⟨t, ht⟩ := hh
  have hq' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  rw [unconjMat, Matrix.det_fin_two_of, ht, Int.mul_ediv_cancel_left _ hq']
  linear_combination det_entries h + (h : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * ht

def unconjSL (hp : p ≠ 0) (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) : SL(2, ℤ) :=
  ⟨unconjMat p h, det_unconjMat hp hh⟩

theorem unconjSL_coe (hp : p ≠ 0) (h : SL(2, ℤ)) (hh : (p : ℤ) ∣ (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ((unconjSL hp h hh : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = unconjMat p h := rfl

theorem gInf_inv_coe (hpN : Nat.Coprime p N) :
    ((gInf hpN)⁻¹ : SL(2, ℤ))
      = (⟨!![1, (bezPair hpN).v; -(N : ℤ), (bezPair hpN).u * p], by
        rw [Matrix.det_fin_two_of]; linear_combination (bezPair hpN).huv⟩ : SL(2, ℤ)) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_inv, gInf_coe]
  simp [Matrix.adjugate_fin_two]

theorem dvd_sandwich_01 (hpN : Nat.Coprime p N) (X : SL(2, ℤ))
    (hX : (p : ℤ) ∣ (X : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (p : ℤ) ∣ ((gInf hpN * X * (gInf hpN)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
  obtain ⟨c, hc⟩ := hX
  rw [mul_apply_01, mul_apply_00, mul_apply_01, gInf_inv_coe, gInf_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hc]
  exact ⟨-(-(bezPair hpN).v * (bezPair hpN).u * (X : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
      - -(bezPair hpN).v * -(bezPair hpN).v * c
      + (bezPair hpN).u * (bezPair hpN).u * p * (X : Matrix (Fin 2) (Fin 2) ℤ) 0 1
      + -(bezPair hpN).v * (bezPair hpN).u * (X : Matrix (Fin 2) (Fin 2) ℤ) 1 1, by ring⟩

theorem dvd_sandwich_10 (hpN : Nat.Coprime p N) (Y : SL(2, ℤ))
    (hY : (p : ℤ) ∣ (Y : Matrix (Fin 2) (Fin 2) ℤ) 0 1) :
    (p : ℤ) ∣ (((gInf hpN)⁻¹ * Y * gInf hpN : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  obtain ⟨b, hb⟩ := hY
  rw [mul_apply_10, mul_apply_10, mul_apply_11, gInf_inv_coe, gInf_coe]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, hb]
  exact ⟨-((N : ℤ) * (bezPair hpN).u * (Y : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
      + (bezPair hpN).u * (bezPair hpN).u * p * (Y : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      - (N : ℤ) * N * b
      + (bezPair hpN).u * N * (Y : Matrix (Fin 2) (Fin 2) ℤ) 1 1, by ring⟩

def cfwd (hp : p ≠ 0) (hpN : Nat.Coprime p N) (h : Lam N p) : Lam N p :=
  ⟨gInf hpN * conjSL hp (h : SL(2, ℤ)) (dvd_01_of_mem_Lam h.2) * (gInf hpN)⁻¹,
    Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem (gInf_mem hpN) (conjSL_mem_Gamma1 hp h.2)) (inv_mem (gInf_mem hpN)),
        mem_Gamma0Upper_iff_dvd.mpr
          (dvd_sandwich_01 hpN _ (conjSL_lowerLeft hp (dvd_01_of_mem_Lam h.2)))⟩⟩

theorem cfwd_coe (hp : p ≠ 0) (hpN : Nat.Coprime p N) (h : Lam N p) :
    ((cfwd hp hpN h : Lam N p) : SL(2, ℤ))
      = gInf hpN * conjSL hp (h : SL(2, ℤ)) (dvd_01_of_mem_Lam h.2) * (gInf hpN)⁻¹ :=
  rfl

theorem sandwich_mem (hpN : Nat.Coprime p N) (h' : Lam N p) :
    (gInf hpN)⁻¹ * (h' : SL(2, ℤ)) * gInf hpN ∈ Gamma1 N :=
  mul_mem (mul_mem (inv_mem (gInf_mem hpN)) h'.2.1) (gInf_mem hpN)

def cbwd (hp : p ≠ 0) (hpN : Nat.Coprime p N) (h' : Lam N p) : Lam N p :=
  ⟨unconjSL hp ((gInf hpN)⁻¹ * (h' : SL(2, ℤ)) * gInf hpN)
      (dvd_sandwich_10 hpN _ (dvd_01_of_mem_Lam h'.2)), by
    have hY := (mem_Gamma1_iff N _).mp (sandwich_mem hpN h')
    obtain ⟨t, ht⟩ := dvd_sandwich_10 hpN (h' : SL(2, ℤ)) (dvd_01_of_mem_Lam h'.2)
    have hq' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_Gamma1_iff, unconjSL_coe]
      simp only [unconjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      refine ⟨hY.1, hY.2.1, ?_⟩
      rw [ht, Int.mul_ediv_cancel_left _ hq']
      have hcop : IsCoprime (N : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr hpN.symm
      exact hcop.dvd_of_dvd_mul_left (ht ▸ hY.2.2)
    · rw [mem_Gamma0Upper_iff_dvd, unconjSL_coe]
      simp only [unconjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      exact dvd_mul_right _ _⟩

def conjEquiv (hp : p ≠ 0) (hpN : Nat.Coprime p N) : Lam N p ≃ Lam N p where
  toFun := cfwd hp hpN
  invFun := cbwd hp hpN
  left_inv h := by
    have hq' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
    obtain ⟨t, ht⟩ := dvd_01_of_mem_Lam h.2
    apply Subtype.ext; apply Subtype.ext
    show unconjMat p ((gInf hpN)⁻¹ * ((cfwd hp hpN h : Lam N p) : SL(2, ℤ)) * gInf hpN) = _
    have hY : (gInf hpN)⁻¹ * ((cfwd hp hpN h : Lam N p) : SL(2, ℤ)) * gInf hpN
        = conjSL hp (h : SL(2, ℤ)) (dvd_01_of_mem_Lam h.2) := by
      rw [cfwd_coe]; group
    rw [hY]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [unconjMat, conjSL_coe, conjMat, ht, Int.mul_ediv_cancel_left _ hq']
  right_inv h' := by
    have hq' : (p : ℤ) ≠ 0 := by exact_mod_cast hp
    obtain ⟨t, ht⟩ := dvd_sandwich_10 hpN (h' : SL(2, ℤ)) (dvd_01_of_mem_Lam h'.2)
    apply Subtype.ext
    rw [cfwd_coe]
    have hX : conjSL hp ((cbwd hp hpN h' : Lam N p) : SL(2, ℤ)) (dvd_01_of_mem_Lam (cbwd hp hpN h').2)
        = (gInf hpN)⁻¹ * (h' : SL(2, ℤ)) * gInf hpN := by
      apply Subtype.ext
      rw [conjSL_coe]
      show conjMat p (unconjSL hp ((gInf hpN)⁻¹ * (h' : SL(2, ℤ)) * gInf hpN)
        (dvd_sandwich_10 hpN _ (dvd_01_of_mem_Lam h'.2))) = _
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [unconjMat, unconjSL_coe, conjMat, ht, Int.mul_ediv_cancel_left _ hq']
    rw [hX]; group

theorem conjEquiv_apply (hp : p ≠ 0) (hpN : Nat.Coprime p N) (h : Lam N p) :
    conjEquiv hp hpN h = cfwd hp hpN h := rfl

theorem beta_mul (hp : p ≠ 0) (hpN : Nat.Coprime p N) (h : Lam N p) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ (gInf hpN) : GL (Fin 2) ℝ) * α p)
        * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((conjEquiv hp hpN h : Lam N p) : SL(2, ℤ)) : GL (Fin 2) ℝ)
        * ((Matrix.SpecialLinearGroup.mapGL ℝ (gInf hpN) : GL (Fin 2) ℝ) * α p) := by
  rw [conjEquiv_apply, cfwd_coe, map_mul, map_mul, map_inv, mul_assoc,
    α_mul_conj hp (h : SL(2, ℤ)) (dvd_01_of_mem_Lam h.2)]
  group

end Conj

section Assembly

variable {N p : ℕ} [NeZero N] {k : ℤ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

omit [NeZero N] in

theorem slash_α_inv (hp : p ≠ 0) (f : CuspForm Γ₁(N) k) (h : SL(2, ℤ)) (hh : h ∈ Lam N p) :
    ((⇑f : ℍ → ℂ) ∣[k] α p) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ h : GL (Fin 2) ℝ)
      = (⇑f : ℍ → ℂ) ∣[k] α p := by
  rw [← SlashAction.slash_mul, α_mul_conj hp h (dvd_01_of_mem_Lam hh), SlashAction.slash_mul,
    slash_mem f (conjSL_mem_Gamma1 hp hh)]

theorem nice_slash_α (hp : p ≠ 0) (f : CuspForm Γ₁(N) k) :
    Nice (Lam N p) k ((⇑f : ℍ → ℂ) ∣[k] α p) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ₁(N) f f
  refine ⟨((CuspFormClass.holo f).slash k (α p)).continuous, ⟨(p : ℝ) ^ (k - 2) * C, fun x => ?_⟩,
    fun h hh => slash_α_inv hp f h hh⟩
  have h1 : UpperHalfPlane.petersson k ((⇑f : ℍ → ℂ) ∣[k] α p) ((⇑f : ℍ → ℂ) ∣[k] α p) x
      = ((p : ℝ) ^ (k - 2) : ℝ) * UpperHalfPlane.petersson k ⇑f ⇑f (α p • x) := by
    rw [UpperHalfPlane.petersson_slash, σ_heckeMatrix, det_heckeMatrix hp]
    simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast]
    push_cast; ring
  have h2 := congrArg Complex.re h1
  rw [petersson_self_eq_dens, petersson_self_eq_dens, Complex.ofReal_re, ← Complex.ofReal_mul,
    Complex.ofReal_re] at h2
  have hle : dens (k := k) (⇑f) (α p • x) ≤ C := by
    have := hC (α p • x)
    rwa [petersson_self_eq_dens, Complex.norm_real, Real.norm_of_nonneg (dens_nonneg _ _ _)] at this
  have hpk : 0 ≤ (p : ℝ) ^ (k - 2) := zpow_nonneg (Nat.cast_nonneg p) _
  calc ‖((⇑f : ℍ → ℂ) ∣[k] α p) x‖ ^ 2 * x.im ^ k = dens (k := k) ((⇑f : ℍ → ℂ) ∣[k] α p) x := rfl
    _ = (p : ℝ) ^ (k - 2) * dens (k := k) (⇑f) (α p • x) := h2
    _ ≤ (p : ℝ) ^ (k - 2) * C := mul_le_mul_of_nonneg_left hle hpk

theorem nice_coe (g : CuspForm Γ₁(N) k) : Nice (Lam N p) k (⇑g : ℍ → ℂ) := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k Γ₁(N) g g
  refine ⟨(CuspFormClass.holo g).continuous, ⟨C, fun x => ?_⟩, fun h hh => slash_mem g hh.1⟩
  have := hC x
  rwa [petersson_self_eq_dens, Complex.norm_real, Real.norm_of_nonneg (dens_nonneg _ _ _)] at this

variable [NeZero p]

theorem main (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f g : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.peterssonOn (Gamma1 N) k (heckeFun k ε p ⇑f) ⇑g
      = conj (ε (p : ZMod N)) * CuspForm.peterssonOn (Gamma1 N) k ⇑f (heckeFun k ε p ⇑g) := by
  set hpN' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
  have hp0 : p ≠ 0 := hp.ne_zero
  set β : GL (Fin 2) ℝ := (Matrix.SpecialLinearGroup.mapGL ℝ (gInf hpN') : GL (Fin 2) ℝ) * α p
  have hleft : CuspForm.peterssonOnIntegrand (Gamma1 N) k (heckeFun k ε p ⇑f) ⇑g
      = cosum (Lam N p) 1 (Φ k p ⇑f ⇑g) := by
    funext τ
    unfold CuspForm.peterssonOnIntegrand cosum
    rw [finsum_eq_sum_of_fintype]
    have hΓ : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
        UpperHalfPlane.petersson k ((heckeFun k ε p ⇑f) ∣[k] (q.out⁻¹ : SL(2, ℤ)))
            ((⇑g : ℍ → ℂ) ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ
          = ∑ i : Option (Fin p), Φ k p ⇑f ⇑g ((rr hpN' i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
      intro q
      calc UpperHalfPlane.petersson k ((heckeFun k ε p ⇑f) ∣[k] (q.out⁻¹ : SL(2, ℤ)))
              ((⇑g : ℍ → ℂ) ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ
          = UpperHalfPlane.petersson k (heckeFun k ε p ⇑f) ⇑g
              ((q.out⁻¹ : SL(2, ℤ)) • τ) := UpperHalfPlane.petersson_slash_SL k _ _ _ _
        _ = UpperHalfPlane.petersson k
              (∑ i : Option (Fin p), (⇑f : ℍ → ℂ) ∣[k] (α p * (rr hpN' i : SL(2, ℤ)))) ⇑g
              ((q.out⁻¹ : SL(2, ℤ)) • τ) := by
            rw [heckeFun_eq_sum hp0 hpN' ε f hf]
            rfl
        _ = ∑ i : Option (Fin p), UpperHalfPlane.petersson k
              ((⇑f : ℍ → ℂ) ∣[k] (α p * (rr hpN' i : SL(2, ℤ)))) ⇑g
              ((q.out⁻¹ : SL(2, ℤ)) • τ) := by
            simp only [UpperHalfPlane.petersson, Finset.sum_apply, map_sum, Finset.sum_mul]
        _ = ∑ i : Option (Fin p), Φ k p ⇑f ⇑g ((rr hpN' i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            calc UpperHalfPlane.petersson k
                    ((⇑f : ℍ → ℂ) ∣[k] (α p * (rr hpN' i : SL(2, ℤ)))) ⇑g
                    ((q.out⁻¹ : SL(2, ℤ)) • τ)
                = UpperHalfPlane.petersson k
                    (((⇑f : ℍ → ℂ) ∣[k] α p) ∣[k] (rr hpN' i : SL(2, ℤ))) ⇑g
                    ((q.out⁻¹ : SL(2, ℤ)) • τ) := by rw [SlashAction.slash_mul]; rfl
              _ = UpperHalfPlane.petersson k
                    (((⇑f : ℍ → ℂ) ∣[k] α p) ∣[k] (rr hpN' i : SL(2, ℤ)))
                    ((⇑g : ℍ → ℂ) ∣[k] (rr hpN' i : SL(2, ℤ)))
                    ((q.out⁻¹ : SL(2, ℤ)) • τ) := by
                  conv_lhs => rw [← slash_mem g (rr_mem hpN' i)]
                  rfl
              _ = UpperHalfPlane.petersson k ((⇑f : ℍ → ℂ) ∣[k] α p) ⇑g
                    ((rr hpN' i : SL(2, ℤ)) • ((q.out⁻¹ : SL(2, ℤ)) • τ)) :=
                  UpperHalfPlane.petersson_slash_SL k _ _ _ _
              _ = Φ k p ⇑f ⇑g ((rr hpN' i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
                  rw [← mul_smul]
                  rfl
    simp_rw [hΓ]
    rw [← unfold_sum (Lam_le N p) (rr hpN') (rr_mem hpN') (exists_rr_mul_mem hpN' hp)
      (fun i i' h => rr_mul_rr_inv_mem hpN' hp i i' h) (Φ k p ⇑f ⇑g)
      (fun h hh x => by
        rw [Φ, ← petersson_smul_SL, slash_α_inv hp0 f h hh, slash_mem g hh.1]) τ]
    simp only [one_smul]
  have hright : CuspForm.peterssonOnIntegrand (Gamma1 N) k ⇑f (heckeFun k ε p ⇑g)
      = fun τ => ε (p : ZMod N) * cosum (Lam N p) β (Φ k p ⇑f ⇑g) τ := by
    funext τ
    unfold CuspForm.peterssonOnIntegrand cosum
    rw [finsum_eq_sum_of_fintype]
    have hΓ : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
        UpperHalfPlane.petersson k ((⇑f : ℍ → ℂ) ∣[k] (q.out⁻¹ : SL(2, ℤ)))
            ((heckeFun k ε p ⇑g) ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ
          = ∑ i : Option (Fin p), Ψ k p ⇑f ⇑g ((rr hpN' i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
      intro q
      calc UpperHalfPlane.petersson k ((⇑f : ℍ → ℂ) ∣[k] (q.out⁻¹ : SL(2, ℤ)))
              ((heckeFun k ε p ⇑g) ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ
          = UpperHalfPlane.petersson k ⇑f (heckeFun k ε p ⇑g)
              ((q.out⁻¹ : SL(2, ℤ)) • τ) := UpperHalfPlane.petersson_slash_SL k _ _ _ _
        _ = UpperHalfPlane.petersson k ⇑f
              (∑ i : Option (Fin p), (⇑g : ℍ → ℂ) ∣[k] (α p * (rr hpN' i : SL(2, ℤ))))
              ((q.out⁻¹ : SL(2, ℤ)) • τ) := by
            rw [heckeFun_eq_sum hp0 hpN' ε g hg]
            rfl
        _ = ∑ i : Option (Fin p), UpperHalfPlane.petersson k ⇑f
              ((⇑g : ℍ → ℂ) ∣[k] (α p * (rr hpN' i : SL(2, ℤ))))
              ((q.out⁻¹ : SL(2, ℤ)) • τ) := by
            simp only [UpperHalfPlane.petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
        _ = ∑ i : Option (Fin p), Ψ k p ⇑f ⇑g ((rr hpN' i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            calc UpperHalfPlane.petersson k ⇑f
                    ((⇑g : ℍ → ℂ) ∣[k] (α p * (rr hpN' i : SL(2, ℤ))))
                    ((q.out⁻¹ : SL(2, ℤ)) • τ)
                = UpperHalfPlane.petersson k ⇑f
                    (((⇑g : ℍ → ℂ) ∣[k] α p) ∣[k] (rr hpN' i : SL(2, ℤ)))
                    ((q.out⁻¹ : SL(2, ℤ)) • τ) := by rw [SlashAction.slash_mul]; rfl
              _ = UpperHalfPlane.petersson k
                    ((⇑f : ℍ → ℂ) ∣[k] (rr hpN' i : SL(2, ℤ)))
                    (((⇑g : ℍ → ℂ) ∣[k] α p) ∣[k] (rr hpN' i : SL(2, ℤ)))
                    ((q.out⁻¹ : SL(2, ℤ)) • τ) := by
                  conv_lhs => rw [← slash_mem f (rr_mem hpN' i)]
                  rfl
              _ = UpperHalfPlane.petersson k ⇑f ((⇑g : ℍ → ℂ) ∣[k] α p)
                    ((rr hpN' i : SL(2, ℤ)) • ((q.out⁻¹ : SL(2, ℤ)) • τ)) :=
                  UpperHalfPlane.petersson_slash_SL k _ _ _ _
              _ = Ψ k p ⇑f ⇑g ((rr hpN' i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
                  rw [← mul_smul]
                  rfl
    simp_rw [hΓ]
    rw [← unfold_sum (Lam_le N p) (rr hpN') (rr_mem hpN') (exists_rr_mul_mem hpN' hp)
      (fun i i' h => rr_mul_rr_inv_mem hpN' hp i i' h) (Ψ k p ⇑f ⇑g)
      (fun h hh x => by
        rw [Ψ, ← petersson_smul_SL, slash_α_inv hp0 g h hh, slash_mem f hh.1]) τ]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Ψ_eq hp hpN ε f g hf]
  have hcvn : ∫ x in (𝒟 : Set ℍ), cosum (Lam N p) β (Φ k p ⇑f ⇑g) x
      = ∫ x in (𝒟 : Set ℍ), cosum (Lam N p) 1 (Φ k p ⇑f ⇑g) x :=
    integral_cosum_pair (Λ₁ := Lam N p) (Λ := Lam N p) β (conjEquiv hp0 hpN') (beta_mul hp0 hpN')
      (nice_slash_α hp0 f) (nice_coe g)
  rw [CuspForm.peterssonOn_def, CuspForm.peterssonOn_def, hleft, hright, integral_const_mul, hcvn,
    ← mul_assoc, ← Complex.inv_eq_conj (norm_char_p ε hp hpN),
    inv_mul_cancel₀ (char_p_ne_zero ε hp hpN), one_mul]

end Assembly


end PetHeckeAdj

end CuspForm
