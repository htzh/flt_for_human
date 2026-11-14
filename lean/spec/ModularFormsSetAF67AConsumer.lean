/-
  Cross-module wire test for SET-AF67A (the primitive-form level reduction).

  A `spec/` probe, not a library module. One zone per headline of
  `ModularForms/PrimitiveFormLevelReduction.lean`, each *consuming* the headline rather than
  restating it: the rows are fired on concrete data and the conclusion is read in the shape the
  downstream cone will read it. No primitive form is constructed anywhere in the corpus, so
  wherever an `IsPrimitiveForm` hypothesis is needed it is carried, not discharged.

  * **Zone A, row `CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq`
    at `q = 2`, `j = 1` and `j = 2`, target level `M₂ = q = 2` (the degenerate case `q ^ 2 ∤ M₂`)
    and `M₂ = 2 ^ 2 = 4`.** The `d = 1` reading is the degeneracy index `1` inside the row: the
    identity degeneracy is the row's `heckeDiagMatrix 1 • τ = τ` wire, quoted below from
    `LiCaseOne` and spent as the first line of the zone. The row is then fired twice: at `j = 1`
    it returns `2 ^ 1 ∣ 2` from a source level with `2 ^ 2 ∣ M₁`, and at `j = 2` it returns
    `2 ^ 2 ∣ 4`, so the row is read both at the bottom power and at the full `q`-power.

  * **Zone B, row `CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq`
    at `M = 1` with the prime set empty.** Both levels are `1`, so the row returns the whole
    `q`-expansion identity; the zone reads it as the single coefficient at `n = 1`.

  * **Zone C, the same row at `M` prime with the prime set empty.** Prime sets are the row's only
    escape hatch, so emptying it makes the hypothesis range over *every* prime; the row is then
    chained into the evaluation at `n = 1`.

  The file contains no `#check`s, no `sorry`s and no placeholder proofs.
-/
import FLTForHuman.ModularForms.PrimitiveFormLevelReduction

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularFormClass
open scoped MatrixGroups ModularForm ComplexConjugate

namespace SetAF67AConsumer

/-- The row's `d = 1` wire, quoted from `LiCaseOne`: the identity degeneracy fixes `τ`. -/
theorem heckeDiagMatrix_one_smul (τ : UpperHalfPlane) :
    ModularForm.heckeDiagMatrix 1 • τ = τ :=
  LiCaseOne.heckeDiagMatrix_one_smul τ

/-- Zone A, at `q = 2`, `j = 1`, target level `M₂ = 2`: the row yields `2 ^ 1 ∣ 2`. -/
theorem zoneA_one {k : ℤ} {M₁ : ℕ} [NeZero M₁] {ε₁ : DirichletCharacter ℂ M₁}
    {ε₂ : DirichletCharacter ℂ 2} {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 2) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n 2 →
      ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n 2 →
      ε₁ (n : ZMod M₁) = ε₂ (n : ZMod 2))
    (hqM : 2 ^ 2 ∣ M₁) (hε₁ : ε₁.FactorsThrough (M₁ / 2)) :
    2 ^ 1 ∣ 2 :=
  CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
    h₁ h₂ ha hε (by norm_num) hqM hε₁ 1
    (by obtain ⟨w, hw⟩ := hqM; exact ⟨2 * w, by rw [hw]; ring⟩)

/-- Zone A, at `q = 2`, `j = 2`, target level `M₂ = 2 ^ 2`: the row yields `2 ^ 2 ∣ 4`. -/
theorem zoneA_two {k : ℤ} {M₁ : ℕ} [NeZero M₁] {ε₁ : DirichletCharacter ℂ M₁}
    {ε₂ : DirichletCharacter ℂ 4} {g₁ : CuspForm (CongruenceSubgroup.Gamma1 M₁) k}
    {g₂ : CuspForm (CongruenceSubgroup.Gamma1 4) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n 4 →
      ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n)
    (hε : ∀ n : ℕ, Nat.Coprime n M₁ → Nat.Coprime n 4 →
      ε₁ (n : ZMod M₁) = ε₂ (n : ZMod 4))
    (hqM : 2 ^ 2 ∣ M₁) (hε₁ : ε₁.FactorsThrough (M₁ / 2)) :
    2 ^ 2 ∣ 4 :=
  CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq
    h₁ h₂ ha hε (by norm_num) hqM hε₁ 2 hqM

/-- Zone B, at `M = 1` with the prime set empty: the row returns the `q`-expansion identity. -/
theorem zoneB_level_one {k : ℤ} {ε₁ ε₂ : DirichletCharacter ℂ 1}
    {g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma1 1) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ p : ℕ, p.Prime → ModularFormClass.qCoeff g₁ p = ModularFormClass.qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → ε₁ (p : ZMod 1) = ε₂ (p : ZMod 1)) :
    ∀ n : ℕ, ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n :=
  (CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq h₁ h₂ ∅
    (fun p hp _ => ha p hp) (fun p hp _ => hε p hp)).2

/-- Zone B, the same row read at the single coefficient `n = 1` (both sides are the eigenvalue `1`). -/
theorem zoneB_level_one_at_one {k : ℤ} {ε₁ ε₂ : DirichletCharacter ℂ 1}
    {g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma1 1) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ p : ℕ, p.Prime → ModularFormClass.qCoeff g₁ p = ModularFormClass.qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → ε₁ (p : ZMod 1) = ε₂ (p : ZMod 1)) :
    ModularFormClass.qCoeff g₁ 1 = ModularFormClass.qCoeff g₂ 1 :=
  zoneB_level_one h₁ h₂ ha hε 1

/-- Zone C, at `M` prime with the prime set empty: the row's hypothesis ranges over every prime. -/
theorem zoneC_prime {k : ℤ} {M : ℕ} [NeZero M]
    {ε₁ ε₂ : DirichletCharacter ℂ M} {g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma1 M) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ p : ℕ, p.Prime → ModularFormClass.qCoeff g₁ p = ModularFormClass.qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → ε₁ (p : ZMod M) = ε₂ (p : ZMod M)) :
    M = M ∧ ∀ n : ℕ, ModularFormClass.qCoeff g₁ n = ModularFormClass.qCoeff g₂ n :=
  CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq h₁ h₂ ∅
    (fun p hp _ => ha p hp) (fun p hp _ => hε p hp)

/-- Zone C, chained: the level is prime, the levels agree, and the coefficients agree at `n = 1`. -/
theorem zoneC_prime_at_one {k : ℤ} {M : ℕ} [NeZero M] (hM : M.Prime)
    {ε₁ ε₂ : DirichletCharacter ℂ M} {g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma1 M) k}
    (h₁ : CuspForm.IsPrimitiveForm ε₁ g₁) (h₂ : CuspForm.IsPrimitiveForm ε₂ g₂)
    (ha : ∀ p : ℕ, p.Prime → ModularFormClass.qCoeff g₁ p = ModularFormClass.qCoeff g₂ p)
    (hε : ∀ p : ℕ, p.Prime → ε₁ (p : ZMod M) = ε₂ (p : ZMod M)) :
    M.Prime ∧ ModularFormClass.qCoeff g₁ 1 = ModularFormClass.qCoeff g₂ 1 :=
  ⟨hM, (zoneC_prime h₁ h₂ ha hε).2 1⟩

end SetAF67AConsumer
