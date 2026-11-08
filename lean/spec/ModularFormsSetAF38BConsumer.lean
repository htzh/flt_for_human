/-
  Consumer zone for `FLTForHuman/ModularForms/HeckeDiagDegeneracy.lean` (order AF38B).

  A `spec/` probe, not a library module: it *consumes* the two headlines in composition, never by
  `#check`.

  Row C (`exists_degeneracy_gamma1_hasNebentypus`) builds the degeneracy lift
  `G τ = g (heckeDiagMatrix d • τ)` at level `N` from a form at level `M` with `M * d ∣ N`, and reads
  its `q`-expansion as `qCoeff G n = if d ∣ n then qCoeff g (n / d) else 0`. Row D
  (`gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero`) is the coefficient criterion at a prime
  `p ∤ N`. The zones below run C at `d = 1` and at `d = p`, and put C at `d = p` against D at the
  same `p` — the two headlines meet on `qCoeff`:

  * **Zone 1** is C at `d = 1`: the lift is the identity on `q`-expansions (`qCoeff G = qCoeff g`)
    while it does raise the level (`M ∣ N`);
  * **Zone 2** is C at `d = p` with `M * p ∣ N`: the lift reads the `p`-subsequence
    (`qCoeff G (p * n) = qCoeff g n`) and is zero off the `p`-multiples;
  * **Zone 3** draws out the `n = p` coefficient of the lift, `qCoeff G p = qCoeff g 1` — the shape
    in which a lift is normally read off a form;
  * **Zone 4** is the meeting: for `p ∤ M` and `g` vanishing off the `p`-multiples, row D kills `g`,
    and row C's formula then says that every coefficient of the lift `G` at level `M * p` — the
    level `p` *creates* — vanishes too.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/ModularFormsSetAF38BConsumer.lean` and never enters the build.
-/
import FLTForHuman.ModularForms.HeckeDiagDegeneracy

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm
open scoped MatrixGroups

namespace ModularFormsSetAF38BConsumer

variable {M N p : ℕ} {k : ℤ}

/-- **Zone 1.** Row C at `d = 1`, `M ∣ N`: the lift raises the level and preserves the
`q`-expansion coefficientwise. -/
theorem qExpansion_lift_one [NeZero N] (hMN : M ∣ N) (g : CuspForm (Gamma1 M) k) :
    ∃ G : CuspForm (Gamma1 N) k,
      (∀ n : ℕ, ModularFormClass.qCoeff G n = ModularFormClass.qCoeff g n) ∧
      ∀ τ : UpperHalfPlane, G τ = g (heckeDiagMatrix 1 • τ) := by
  obtain ⟨G, hG, hq, -⟩ :=
    CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) (M := M) (N := N) (d := 1)
      (by simpa using hMN) g
  exact ⟨G, fun n => by simpa using hq n, hG⟩

/-- **Zone 2.** Row C at `d = p`, `M * p ∣ N`: the lift reads the `p`-subsequence of the
`q`-expansion and vanishes off the `p`-multiples. -/
theorem qExpansion_lift_prime [NeZero N] (hp : p.Prime) (hMN : M * p ∣ N)
    (g : CuspForm (Gamma1 M) k) :
    ∃ G : CuspForm (Gamma1 N) k,
      (∀ n : ℕ, ModularFormClass.qCoeff G (p * n) = ModularFormClass.qCoeff g n) ∧
      (∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff G n = 0) := by
  obtain ⟨G, -, hq, -⟩ :=
    CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) (M := M) (N := N) (d := p) hMN g
  refine ⟨G, fun n => ?_, fun n hn => ?_⟩
  · rw [hq (p * n), ite_eq_left (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos]
  · rw [hq n, ite_eq_right hn]

/-- **Zone 3.** The `p`-th coefficient of the lift is the first coefficient of `g`. -/
theorem qCoeff_lift_prime_one [NeZero N] (hp : p.Prime) (hMN : M * p ∣ N)
    (g : CuspForm (Gamma1 M) k) :
    ∃ G : CuspForm (Gamma1 N) k,
      ModularFormClass.qCoeff G p = ModularFormClass.qCoeff g 1 := by
  obtain ⟨G, hq, -⟩ := qExpansion_lift_prime (k := k) hp hMN g
  exact ⟨G, by simpa using hq 1⟩

/-- **Zone 4.** Row D at `p ∤ M` and row C at `d = p` meet on `qCoeff`: a form whose coefficients
vanish off the `p`-multiples is zero, and every coefficient of its lift to the level `M * p` — the
level that `p` creates — is zero as well. -/
theorem lift_prime_eq_zero_of_qCoeff_vanish [NeZero M] (hp : p.Prime) (hpM : ¬ p ∣ M)
    (g : CuspForm (Gamma1 M) k)
    (hg : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff g n = 0) :
    g = 0 ∧ ∃ G : CuspForm (Gamma1 (M * p)) k,
      (∀ τ : UpperHalfPlane, G τ = g (heckeDiagMatrix p • τ)) ∧
      ∀ n : ℕ, ModularFormClass.qCoeff G n = 0 := by
  have hMp : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  have hg0 : g = 0 :=
    CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero k hp hpM g hg
  have hgall : ∀ n : ℕ, ModularFormClass.qCoeff g n = 0 := by
    intro n
    rw [hg0]
    simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero]
  obtain ⟨G, hG, hq, -⟩ :=
    CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) (M := M) (N := M * p) (d := p)
      (dvd_refl (M * p)) g
  refine ⟨hg0, G, hG, fun n => ?_⟩
  rw [hq n]
  by_cases hpn : p ∣ n
  · rw [ite_eq_left hpn, hgall]
  · rw [ite_eq_right hpn]

end ModularFormsSetAF38BConsumer
