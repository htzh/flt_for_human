/-
  p-stabilisation of a normalised eigenform, and level divisibility.

  * `CuspForm.exists_isNormalizedEigenform_level_mul` — from a normalised
    eigenform at level `M` and a prime `p`, build a normalised eigenform at level
    `M * p` agreeing with it at every coefficient indexed by a number coprime
    to `p`. When `p ∣ M` this is the degeneracy pullback `f(τ) ↦ f(τ)`; when
    `p ∤ M` it is the `p`-stabilisation `g₁ - β g₂`, where `β` is a root of
    `X² - a_p X + p` (the second Hecke eigenvalue at `p`).
  * `CuspForm.exists_isNormalizedEigenform_of_dvd` — iterate the previous step
    over the prime factorisation of `N / M`.

  Both statements are the pin's `Theorems/` wrappers verbatim; the proofs are
  transcribed from

  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_isNormalizedEigenform_level_mul.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_exists_isNormalizedEigenform_of_dvd.lean

  with the pin's `PStab` arithmetic block kept `private`. The pin's blanket
  `import Mathlib` is replaced by the specific mathlib modules used.
-/
import FLTForHuman.ModularForms.Level.Degeneracy
import FLTForHuman.ModularForms.Defs.Eigenform
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.SturmBound
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Factorization.Induction

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing; keep them literal (port convention).
set_option linter.style.haveILetI false

noncomputable section

open ModularFormClass UpperHalfPlane

/- The arithmetic core of the `p`-stabilisation: the recurrence
`a_{p^{r+2}} = a_p a_{p^{r+1}} - p a_{p^r}` with `α + β = a_p`, `αβ = p` gives
`a_{p^{j+1}} - β a_{p^j} = α^{j+1}`. Private. -/
namespace PStab

private theorem pow_sub_beta_mul (a : ℕ → ℂ) (p : ℕ) (α β : ℂ) (h1 : a 1 = 1) (hsum : α + β = a p)
    (hprod : α * β = p)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r)) :
    ∀ j : ℕ, a (p ^ (j + 1)) - β * a (p ^ j) = α ^ (j + 1) := by
  intro j
  induction j with
  | zero => simp only [zero_add, pow_one, pow_zero, h1, mul_one]; linear_combination -hsum
  | succ j ih =>
    have := hrec j
    rw [show j + 1 + 1 = j + 2 from rfl]
    linear_combination this + α * ih - a (p ^ (j + 1)) * hsum + a (p ^ j) * hprod

private theorem stab_clauses {M p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (a b : ℕ → ℂ) (α β : ℂ)
    (hsum : α + β = a p) (hprod : α * β = p)
    (hb : ∀ n, b n = a n - β * (if p ∣ n then a (n / p) else 0))
    (h1 : a 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hT : ∀ ℓ r : ℕ, ℓ.Prime → ¬ ℓ ∣ M →
      a (ℓ ^ (r + 2)) = a ℓ * a (ℓ ^ (r + 1)) - ℓ * a (ℓ ^ r))
    (hU : ∀ ℓ r : ℕ, ℓ.Prime → ℓ ∣ M → a (ℓ ^ (r + 2)) = a ℓ * a (ℓ ^ (r + 1))) :
    b 1 = 1 ∧
    (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) ∧
    (∀ ℓ r : ℕ, ℓ.Prime → ¬ ℓ ∣ M * p →
      b (ℓ ^ (r + 2)) = b ℓ * b (ℓ ^ (r + 1)) - ℓ * b (ℓ ^ r)) ∧
    (∀ ℓ r : ℕ, ℓ.Prime → ℓ ∣ M * p → b (ℓ ^ (r + 2)) = b ℓ * b (ℓ ^ (r + 1))) ∧
    (∀ n : ℕ, ¬ p ∣ n → b n = a n) := by
  have hb0 : ∀ n, ¬ p ∣ n → b n = a n := fun n hn ↦ by rw [hb n, ite_eq_right hn]; ring
  have hb1 : ∀ n, p ∣ n → b n = a n - β * a (n / p) := fun n hn ↦ by rw [hb n, ite_eq_left hn]

  have hℓpow : ∀ ℓ j : ℕ, ℓ.Prime → ℓ ≠ p → ¬ p ∣ ℓ ^ j := fun ℓ j hℓ hne h ↦
    hne ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow h)).symm
  refine ⟨?_, ?_, ?_, ?_, hb0⟩
  · rw [hb0 1 hp.not_dvd_one, h1]
  · intro m n hmn
    by_cases hm : p ∣ m
    · have hn : ¬ p ∣ n := fun hn ↦ hp.one_lt.ne'
        (Nat.dvd_one.mp (Nat.Coprime.gcd_eq_one hmn ▸ Nat.dvd_gcd hm hn))
      have hmn' : (m / p).Coprime n := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hm) hmn
      rw [hb1 _ (dvd_mul_of_dvd_left hm n), hb1 m hm, hb0 n hn, ← Nat.div_mul_right_comm hm n,
        hmul _ _ hmn, hmul _ _ hmn']
      ring
    · by_cases hn : p ∣ n
      · have hmn' : m.Coprime (n / p) := Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hn) hmn
        rw [hb1 _ (dvd_mul_of_dvd_right hn m), hb0 m hm, hb1 n hn, Nat.mul_div_assoc m hn,
          hmul _ _ hmn, hmul _ _ hmn']
        ring
      · have : ¬ p ∣ m * n := fun h ↦ (hp.dvd_mul.mp h).elim hm hn
        rw [hb0 _ this, hb0 m hm, hb0 n hn, hmul m n hmn]
  · intro ℓ r hℓ hℓMp
    have hne : ℓ ≠ p := fun h ↦ hℓMp (h ▸ dvd_mul_left p M)
    have hℓM : ¬ ℓ ∣ M := fun h ↦ hℓMp (dvd_mul_of_dvd_left h p)
    rw [hb0 _ (hℓpow ℓ _ hℓ hne), hb0 _ (by simpa using hℓpow ℓ 1 hℓ hne),
      hb0 _ (hℓpow ℓ _ hℓ hne), hb0 _ (hℓpow ℓ _ hℓ hne)]
    exact hT ℓ r hℓ hℓM
  · intro ℓ r hℓ hℓMp
    rcases (Nat.Prime.dvd_mul hℓ).mp hℓMp with hℓM | hℓp
    · have hne : ℓ ≠ p := fun h ↦ hpM (h ▸ hℓM)
      rw [hb0 _ (hℓpow ℓ _ hℓ hne), hb0 _ (by simpa using hℓpow ℓ 1 hℓ hne),
        hb0 _ (hℓpow ℓ _ hℓ hne)]
      exact hU ℓ r hℓ hℓM
    · have hℓp' : ℓ = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).mp hℓp
      subst hℓp'

      have key : ∀ j : ℕ, b (ℓ ^ (j + 1)) = α ^ (j + 1) := by
        intro j
        rw [hb1 _ (dvd_pow_self ℓ (Nat.succ_ne_zero j)), pow_succ, Nat.mul_div_cancel _ hℓ.pos,
          ← pow_succ]
        exact pow_sub_beta_mul a ℓ α β h1 hsum hprod (fun r ↦ hT ℓ r hℓ hpM) j
      have hbℓ : b ℓ = α := by simpa using key 0
      rw [key (r + 1), hbℓ, key r]
      ring

end PStab

open PStab in

/-- **`p`-stabilisation.** Stated verbatim from
`Theorems/Thm_CuspForm_exists_isNormalizedEigenform_level_mul.lean`. -/
theorem CuspForm.exists_isNormalizedEigenform_level_mul {M : ℕ} [NeZero M]
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform)
    {p : ℕ} (hp : p.Prime) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff f n := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  have hΓM := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 M

  obtain ⟨g₁, hg₁⟩ := CuspForm.exists_degeneracy_Gamma0 (k := 2) (d := 1) (M := M) (N := M * p)
    (by simp) f
  have hq₁ : ∀ n, qCoeff g₁ n = qCoeff f n := by
    intro n
    rw [hg₁, ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f hΓM one_ne_zero n,
      ite_eq_left (one_dvd n), Nat.div_one]
  by_cases hpM : p ∣ M
  · refine ⟨g₁, ⟨?_, ?_, ?_, ?_⟩, fun n _ ↦ hq₁ n⟩
    · rw [hq₁]; exact hf.qCoeff_one
    · intro m n h; simp only [hq₁]; exact hf.qCoeff_mul_of_coprime m n h
    · intro ℓ r hℓ hℓMp
      simp only [hq₁]
      exact hf.qCoeff_prime_pow_of_not_dvd ℓ r hℓ fun h ↦ hℓMp (dvd_mul_of_dvd_left h p)
    · intro ℓ r hℓ hℓMp
      simp only [hq₁]
      refine hf.qCoeff_prime_pow_of_dvd ℓ r hℓ ?_
      rcases (Nat.Prime.dvd_mul hℓ).mp hℓMp with h | h
      · exact h
      · exact ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h) ▸ hpM
  ·
    obtain ⟨g₂, hg₂⟩ := CuspForm.exists_degeneracy_Gamma0 (k := 2) (d := p) (M := M) (N := M * p)
      (by rw [mul_comm]) f
    have hq₂ : ∀ n, qCoeff g₂ n = if p ∣ n then qCoeff f (n / p) else 0 := by
      intro n
      rw [hg₂, ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f hΓM hp.ne_zero n]

    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (qCoeff f p ^ 2 - 4 * p) two_pos
    set α : ℂ := (qCoeff f p + s) / 2 with hα
    set β : ℂ := (qCoeff f p - s) / 2 with hβ
    have hsum : α + β = qCoeff f p := by rw [hα, hβ]; ring
    have hprod : α * β = p := by
      rw [hα, hβ]; linear_combination (-(1:ℂ)/4) * hs

    let g : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2 := g₁ - β • g₂
    have hΓ := CongruenceSubgroup.one_mem_strictPeriods_Gamma0 (M * p)
    have hqg : ∀ n, qCoeff g n = qCoeff f n - β * (if p ∣ n then qCoeff f (n / p) else 0) := by
      intro n
      have ha₁ := ModularFormClass.analyticAt_cuspFunction_zero g₁ one_pos hΓ
      have ha₂ := ModularFormClass.analyticAt_cuspFunction_zero g₂ one_pos hΓ
      have ha₂' : AnalyticAt ℂ (cuspFunction 1 (β • ⇑g₂)) 0 := by
        rw [← FunLike.coe_smul]
        exact ModularFormClass.analyticAt_cuspFunction_zero (β • g₂) one_pos hΓ
      rw [← hq₁ n, ← hq₂ n]
      simp only [qCoeff, g, FunLike.coe_sub, FunLike.coe_smul]
      rw [qExpansion_sub ha₁ ha₂', qExpansion_smul ha₂, map_sub, map_smul, smul_eq_mul]
    obtain ⟨c1, c2, c3, c4, c5⟩ := stab_clauses hp hpM (qCoeff f) (qCoeff g) α β hsum hprod hqg
      hf.qCoeff_one hf.qCoeff_mul_of_coprime hf.qCoeff_prime_pow_of_not_dvd hf.qCoeff_prime_pow_of_dvd
    exact ⟨g, ⟨c1, c2, c3, c4⟩, c5⟩

/-- **Level divisibility.** Stated verbatim from
`Theorems/Thm_CuspForm_exists_isNormalizedEigenform_of_dvd.lean`. -/
theorem CuspForm.exists_isNormalizedEigenform_of_dvd {M N : ℕ} [NeZero N] (hMN : M ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (hf : f.IsNormalizedEigenform) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, n.Coprime N → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff f n := by

  have key : ∀ (t M : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2), M * t ≠ 0 →
      f.IsNormalizedEigenform →
      ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (M * t)) 2, g.IsNormalizedEigenform ∧
        ∀ n : ℕ, n.Coprime t → qCoeff g n = qCoeff f n := by
    intro t
    induction t using Nat.recOnMul with
    | zero => intro M f h; simp at h
    | one => intro M f _ hf; rw [Nat.mul_one]; exact ⟨f, hf, fun n _ ↦ rfl⟩
    | prime p hp =>
      intro M f hM hf
      haveI : NeZero M := ⟨fun h ↦ hM (by rw [h, Nat.zero_mul])⟩
      obtain ⟨g, hg, hq⟩ := CuspForm.exists_isNormalizedEigenform_level_mul f hf hp
      exact ⟨g, hg, fun n hn ↦ hq n fun h ↦ hp.one_lt.ne'
        (Nat.Coprime.eq_one_of_dvd (Nat.coprime_comm.mp hn) h)⟩
    | mul a b iha ihb =>
      intro M f hM hf
      have hMa : M * a ≠ 0 := fun h ↦ hM (by rw [← Nat.mul_assoc, h, Nat.zero_mul])
      obtain ⟨g₁, hg₁, hq₁⟩ := iha M f hMa hf
      obtain ⟨g₂, hg₂, hq₂⟩ := ihb (M * a) g₁ (by rwa [Nat.mul_assoc]) hg₁
      rw [← Nat.mul_assoc]
      exact ⟨g₂, hg₂, fun n hn ↦ (hq₂ n (Nat.Coprime.coprime_mul_left_right hn)).trans
        (hq₁ n (Nat.Coprime.coprime_mul_right_right hn))⟩
  obtain ⟨t, rfl⟩ := hMN
  obtain ⟨g, hg, hq⟩ := key t M f (NeZero.ne _) hf
  exact ⟨g, hg, fun n hn ↦ hq n (Nat.Coprime.coprime_mul_left_right hn)⟩

end
