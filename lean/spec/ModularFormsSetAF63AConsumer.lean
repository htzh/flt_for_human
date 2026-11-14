/-
  Cross-module wire test for SET-AF63A (the `Γ₁` depletion, the coprime-level criterion and the
  Atkin--Lehner lowering).

  A `spec/` probe, not a library module. Three composition zones, each one *consuming* a
  headline of `ModularForms/AtkinLehnerLowering.lean` rather than restating it:

  * **Zone A (`CuspForm.exists_gamma1_qCoeff_eq_ite_coprime`) at `N = 1`, `Q = 2`,
    `M = 1 * 2 ^ 2 = 4`.** The depletion is read as the pin intends it: the coefficients at
    the odd indices are the original ones, the coefficients at the even indices vanish. The
    two readings are then *composed*: at the index `1` (odd) the depleted form has exactly
    `f`'s first coefficient, and the even half is exhibited as a genuine vanishing statement,
    not an `if`.

  * **Zone B (`CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero`)
    as the `K = N` specialisation.** The row is stated for an arbitrary modulus `K`; here it
    is fired at `K = N`, where the hypothesis `hf` is exactly the Atkin--Lehner hypothesis of
    the level `N`, and read off at the index `1`. A second firing at `K = 1` shows the
    direction the criterion actually weakens: vanishing at *every* index implies vanishing
    at the indices prime to `N`.

  * **Zone C
    (`CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero`) at a
    prime `N = p`.** Then `p.primeFactors = {p}`, so the sum over the prime factors has
    exactly one term and the row reads `qCoeff f n = if p ∣ n then qCoeff (g p) (n / p)
    else 0`. At `p = 5` that one term is evaluated: the coefficients at the indices not
    divisible by `5` vanish.

  Every declaration below is an application of one of the three headlines; the file has no
  `#check`s and no `sorry`s.
-/
import FLTForHuman.ModularForms.AtkinLehnerLowering

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm

open scoped MatrixGroups

namespace SetAF63AConsumer

/-! ## Zone A: the `Γ₁` depletion at `Q = 2`, read off at `N = 1` -/

/-- **Zone A, the headline at `Q = 2`.** The depleted form at level `4 = 1 * 2 ^ 2`: its
coefficients are `f`'s exactly at the indices coprime to `2` and zero elsewhere. -/
theorem zoneA_deplete (k : ℤ) (f : CuspForm (Gamma1 1) k) :
    ∃ g : CuspForm (Gamma1 4) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if n.Coprime 2 then ModularFormClass.qCoeff f n else 0 :=
  CuspForm.exists_gamma1_qCoeff_eq_ite_coprime 1 k f 2 (by norm_num) 4 (by norm_num)

/-- **Zone A, the odd half.** At an index prime to `2` the `if` collapses to the original
coefficient: the depletion is the identity there. -/
theorem zoneA_odd (k : ℤ) (f : CuspForm (Gamma1 1) k) :
    ∃ g : CuspForm (Gamma1 4) k,
      ∀ n : ℕ, ¬ 2 ∣ n → ModularFormClass.qCoeff g n = ModularFormClass.qCoeff f n := by
  obtain ⟨g, hg⟩ := zoneA_deplete k f
  refine ⟨g, fun n hn => ?_⟩
  rw [hg n, ite_eq_left]
  exact ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mpr hn).symm

/-- **Zone A, the even half.** At an even index the `if` collapses to `0`, so the exhausted
coefficient is a vanishing statement. -/
theorem zoneA_even (k : ℤ) (f : CuspForm (Gamma1 1) k) :
    ∃ g : CuspForm (Gamma1 4) k,
      ∀ n : ℕ, 2 ∣ n → ModularFormClass.qCoeff g n = 0 := by
  obtain ⟨g, hg⟩ := zoneA_deplete k f
  refine ⟨g, fun n hn => ?_⟩
  rw [hg n, ite_eq_right]
  exact fun hc => (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 2)).mp hc.symm hn

/-- **Zone A composed at the index `1`.** The odd half read at `n = 1` says the depleted
form starts exactly like `f`: the first coefficient survives the depletion. -/
theorem zoneA_coeff_one (k : ℤ) (f : CuspForm (Gamma1 1) k) :
    ∃ g : CuspForm (Gamma1 4) k, ModularFormClass.qCoeff g 1 = ModularFormClass.qCoeff f 1 := by
  obtain ⟨g, hg⟩ := zoneA_odd k f
  exact ⟨g, hg 1 (by norm_num)⟩

/-! ## Zone B: the coprime-level criterion at `K = N` -/

/-- **Zone B at `K = N`.** The row with `K` specialised to the level itself: the hypothesis
is the Atkin--Lehner vanishing hypothesis at `N`, read at the index `1` (prime to every
level). -/
theorem zoneB_coeff_one_eq_zero (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, Nat.Coprime n N → ModularFormClass.qCoeff f n = 0) :
    ModularFormClass.qCoeff f 1 = 0 :=
  CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero N k N (NeZero.ne N)
    f hf 1 (Nat.coprime_one_left N)

/-- **Zone B at `K = 1`.** The criterion only needs the vanishing at the indices prime to
`K`; at `K = 1` that is every index, so it applies to any level. This is the direction the
row is used in, and it is strictly weaker than the hypothesis of the `K = N` firing. -/
theorem zoneB_of_forall_eq_zero (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, ModularFormClass.qCoeff f n = 0) (n : ℕ) (hn : Nat.Coprime n N) :
    ModularFormClass.qCoeff f n = 0 :=
  CuspForm.qCoeff_eq_zero_of_coprime_level_of_forall_coprime_qCoeff_eq_zero N k 1 one_ne_zero f
    (fun m _ => hf m) n hn

/-! ## Zone C: the Atkin--Lehner lowering at a prime, one term -/

/-- **Zone C at a prime `N = p`.** A prime has a single prime factor, so the sum in the
headline has exactly one term and the decomposition collapses to the `p`-th subsequence of
one form at the level `Γ₁(p / p) = Γ₁(1)`. -/
theorem zoneC_prime (p : ℕ) [NeZero p] (hp : p.Prime) (k : ℤ) (f : CuspForm (Gamma1 p) k)
    (hf : ∀ n : ℕ, Nat.Coprime n p → ModularFormClass.qCoeff f n = 0) :
    ∃ g : (q : ℕ) → CuspForm (Gamma1 (p / q)) k, ∀ n : ℕ,
      ModularFormClass.qCoeff f n =
        if p ∣ n then ModularFormClass.qCoeff (g p) (n / p) else 0 := by
  obtain ⟨g, hg⟩ :=
    CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero p k p
      (NeZero.ne p) f hf
  refine ⟨g, fun n => ?_⟩
  rw [hg n, Nat.Prime.primeFactors hp, Finset.sum_singleton]

/-- **Zone C at `p = 5`, the single term named.** The one-term sum read at the level `5`,
with the surviving form `g 5` kept in the statement: the `n`-th coefficient of `f` is the
`(n / 5)`-th coefficient of `g 5` exactly at the multiples of `5`. -/
theorem zoneC_five (k : ℤ) (f : CuspForm (Gamma1 5) k)
    (hf : ∀ n : ℕ, Nat.Coprime n 5 → ModularFormClass.qCoeff f n = 0) :
    ∃ g : (q : ℕ) → CuspForm (Gamma1 (5 / q)) k, ∀ n : ℕ,
      ModularFormClass.qCoeff f n =
        if 5 ∣ n then ModularFormClass.qCoeff (g 5) (n / 5) else 0 := by
  obtain ⟨g, hg⟩ := zoneC_prime 5 (by norm_num) k f hf
  exact ⟨g, hg⟩

/-- **Zone C at `p = 5`, the one term evaluated.** Away from the multiples of `5` the single
surviving term is the `else` branch, so the coefficients of `f` vanish there -- the
Atkin--Lehner conclusion in its read-off form. -/
theorem zoneC_five_off (k : ℤ) (f : CuspForm (Gamma1 5) k)
    (hf : ∀ n : ℕ, Nat.Coprime n 5 → ModularFormClass.qCoeff f n = 0) :
    ∀ n : ℕ, ¬ 5 ∣ n → ModularFormClass.qCoeff f n = 0 := by
  obtain ⟨g, hg⟩ := zoneC_five k f hf
  exact fun n hn => by rw [hg n, ite_eq_right hn]

end SetAF63AConsumer
