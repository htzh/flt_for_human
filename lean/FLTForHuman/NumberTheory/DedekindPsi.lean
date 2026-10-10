/-
  The Dedekind `ψ` function: the divisor-sum definition and its arithmetic
  (`ψ(p) = p + 1`, multiplicativity, the prime step, positivity), the same
  function as a multiplicative `ArithmeticFunction` (`ψ = 1_sqf ∗ id`), and the
  counting core (a full block of coprime residues, and the primitive-coset fibre).

  This is generic number theory with no modular content, so it owns the subject in
  `NumberTheory/` rather than being exported from any consumer — the rule that
  `TsumDivisorsAntidiagonal.lean` records for the `tsum` rearrangement. Before this
  module the ψ block sat in `ModularCurve/Defs/Jq.lean` only because the pin keeps
  it in `Def_ModularCurve_X0.lean`'s `NamedInputs` section, and its
  `ArithmeticFunction` view was `private` there, so `ModularCurve/Gamma0Index.lean`
  had to re-derive it privately; `Degree/Roof.lean`,
  `FunctionFieldGeneration/{Spine,SlotProduct}.lean` and
  `Analytic/CuspDichotomy.lean` each re-proved part of the public surface as well.
  All of them now import here.

  The `ModularCurve`-namespaced view of the pin's `dedekindPsi` names is the shim
  `FLTForHuman/ModularCurve/Defs/DedekindPsi.lean`; consumers inside that namespace
  see the pin's spelling as before.

  FLT provenance, pinned `aa2d8b3`:
  * `Definitions/Def_ModularCurve_X0.lean` lines 111–212 — the definition and the
    arithmetic facts (`Theorems/Thm_ModularCurve_dedekindPsi_*` are their wrappers).
  * `P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean` — the
    `ArithmeticFunction` view (`sqf`, `Psi`, `Psi_apply`, `isMultiplicative_Psi`)
    and the counting core (`h`, `card_filter_coprime_range_mul`, `card_fibre`).
  * `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean` — the port's re-derived
    closed form of the fibre value, renamed `dedekindPsiFibre` here because the
    pin's `slotH` is taken publicly by `ModularCurve.QExpN.slotH`.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean

  The pin writes the `ArithmeticFunction` view and the counting core `private` in
  the two `S_` files; here they are promoted (or renamed, for the fibre value),
  and the port-authored names go on the statement checker's `OWN_PROOFS`.
-/
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Finset

/-! ### The divisor-sum function -/

/-- The Dedekind psi function: `ψ(N) = ∑_{d ∣ N, d squarefree} N / d`, which
equals `N ∏_{p ∣ N} (1 + 1/p)`. -/
def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d

@[simp]
theorem dedekindPsi_one : dedekindPsi 1 = 1 := by
  rw [dedekindPsi, Nat.divisors_one, Finset.filter_singleton, ite_eq_left squarefree_one]
  simp

/-- `ψ(p) = p + 1` for a prime `p`. Part of the cone's outbound interface
(indeg 72). -/
theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1 := by
  rw [dedekindPsi, Finset.sum_filter, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  simp [hp.squarefree, Nat.div_self hp.pos]

/-- `ψ(p ^ k) = p ^ k + p ^ (k - 1)` for a prime `p` and `k ≠ 0`. Part of the
cone's outbound interface (indeg 33). -/
theorem dedekindPsi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    dedekindPsi (p ^ k) = p ^ k + p ^ (k - 1) := by
  have hsqfree : ∀ j, Squarefree (p ^ j) ↔ j ≤ 1 := fun j => by
    constructor
    · intro hsq
      by_contra hj
      exact hp.one_lt.ne'
        (Nat.isUnit_iff.mp (hsq p (by rw [← pow_two]; exact pow_dvd_pow p (by omega))))
    · intro hj
      interval_cases j
      · simp
      · simpa using hp.prime.squarefree
  have hfilter : {d ∈ (p ^ k).divisors | Squarefree d} = {1, p} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hsq⟩
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      have : j ≤ 1 := (hsqfree j).mp hsq
      interval_cases j
      · exact Or.inl (pow_zero p)
      · exact Or.inr (pow_one p)
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, pow_ne_zero _ hp.pos.ne'⟩, squarefree_one⟩
      · exact ⟨⟨dvd_pow_self _ hk, pow_ne_zero _ hp.pos.ne'⟩, hp.prime.squarefree⟩
  have hdiv : p ^ k / p = p ^ (k - 1) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ]
    exact Nat.mul_div_cancel _ hp.pos
  rw [dedekindPsi, hfilter, Finset.sum_pair hp.one_lt.ne, Nat.div_one, hdiv]

/-! ### `ψ` as a multiplicative arithmetic function -/

/-- The squarefree indicator as an arithmetic function. -/
private def squarefreeIndicator : ArithmeticFunction ℕ :=
  ⟨fun n => if Squarefree n then 1 else 0, by simp [not_squarefree_zero]⟩

@[simp]
private theorem squarefreeIndicator_apply {n : ℕ} :
    squarefreeIndicator n = if Squarefree n then 1 else 0 :=
  rfl

private theorem isMultiplicative_squarefreeIndicator :
    squarefreeIndicator.IsMultiplicative := by
  refine ⟨by simp, fun {m n} h => ?_⟩
  simp only [squarefreeIndicator_apply, Nat.squarefree_mul h]
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;> simp [hm, hn]

/-- The Dedekind `ψ` function as an arithmetic function, `ψ = 1_sqf ∗ id`. The
pin's name is `Psi`; keeping it makes the cross-reference to
`S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean` direct. -/
def Psi : ArithmeticFunction ℕ := squarefreeIndicator * ArithmeticFunction.id

private theorem dedekindPsi_eq_mul_apply (N : ℕ) : dedekindPsi N = Psi N := by
  rw [Psi, ArithmeticFunction.mul_apply, dedekindPsi,
    Nat.sum_divisorsAntidiagonal (fun x y => squarefreeIndicator x * ArithmeticFunction.id y),
    Finset.sum_filter]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [squarefreeIndicator_apply, ArithmeticFunction.id_apply]
  split_ifs <;> simp

/-- The arithmetic-function view computes `ψ`. -/
theorem Psi_apply (n : ℕ) : Psi n = dedekindPsi n :=
  (dedekindPsi_eq_mul_apply n).symm

/-- `ψ` is multiplicative, as an arithmetic function. -/
theorem isMultiplicative_Psi : Psi.IsMultiplicative :=
  isMultiplicative_squarefreeIndicator.mul ArithmeticFunction.isMultiplicative_id

/-- `ψ` is multiplicative: `ψ(mn) = ψ(m)ψ(n)` for coprime `m`, `n`. Part of the
cone's outbound interface (indeg 46). -/
theorem dedekindPsi_mul_of_coprime (M N : ℕ) (h : Nat.Coprime M N) :
    dedekindPsi (M * N) = dedekindPsi M * dedekindPsi N := by
  simp only [dedekindPsi_eq_mul_apply]
  exact isMultiplicative_Psi.map_mul_of_coprime h

/-- The prime step of `ψ`: `ψ(Mℓ) = (if ℓ ∣ M then ℓ else ℓ + 1) · ψ(M)`. Part of
the cone's neighbourhood interface (indeg 20). FLT publishes it as a `Them_`
wrapper; the port had re-proved its two cases privately in `Spine.lean` and again
in the T19 pin's slot-counting block, so it is written once here. Verbatim from
`Thm_ModularCurve_dedekindPsi_mul_prime`. -/
theorem dedekindPsi_mul_prime (M ℓ : ℕ) [NeZero M] (hℓ : ℓ.Prime) :
    dedekindPsi (M * ℓ) = (if ℓ ∣ M then ℓ else ℓ + 1) * dedekindPsi M := by
  have hM : M ≠ 0 := NeZero.ne M
  obtain ⟨k, M', hM', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM ℓ hℓ.ne_one
  have hcop : Nat.Coprime (ℓ ^ k) M' :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hM')
  have hcop' : Nat.Coprime M' ℓ := ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hM').symm
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_mul] at hcop ⊢
    rw [ite_eq_right hM', dedekindPsi_mul_of_coprime M' ℓ hcop', dedekindPsi_prime hℓ,
      mul_comm]
  · have hdvd : ℓ ∣ ℓ ^ k * M' := dvd_mul_of_dvd_left (dvd_pow_self ℓ hk.ne') M'
    rw [ite_eq_left hdvd]
    have e1 : ℓ ^ k * M' * ℓ = ℓ ^ (k + 1) * M' := by ring
    have hcop1 : Nat.Coprime (ℓ ^ (k + 1)) M' :=
      Nat.Coprime.pow_left (k + 1) ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hM')
    rw [e1, dedekindPsi_mul_of_coprime _ _ hcop1, dedekindPsi_mul_of_coprime _ _ hcop,
      dedekindPsi_prime_pow ℓ (k + 1) hℓ (Nat.succ_ne_zero k),
      dedekindPsi_prime_pow ℓ k hℓ hk.ne', Nat.add_sub_cancel]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hk
    simp only [Nat.zero_add, Nat.add_sub_cancel]
    ring

/-- The prime step in the case `p ∣ m`. Promoted once here: it had been written
privately in both `FunctionFieldGeneration/Spine.lean` and
`FunctionFieldGeneration/SlotProduct.lean`. -/
theorem dedekindPsi_mul_prime_dvd {m p : ℕ} [NeZero m] (hp : p.Prime) (hpm : p ∣ m) :
    dedekindPsi (m * p) = dedekindPsi m * p := by
  rw [dedekindPsi_mul_prime m p hp, ite_eq_left hpm, mul_comm]

/-- The prime step in the case `p ∤ m`. Promoted once here, as above; this is the
form that does not need `m ≠ 0`. -/
theorem dedekindPsi_mul_prime_not_dvd {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    dedekindPsi (m * p) = dedekindPsi m * (p + 1) := by
  have hco : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  rw [dedekindPsi_mul_of_coprime m p hco, dedekindPsi_prime hp]

/-- `ψ` is positive at every nonzero level. Part of the cone's neighbourhood
interface (indeg 76); the pin proves it from `le_dedekindPsi`, whose argument is
inlined here. Verbatim statement from `Thm_ModularCurve_dedekindPsi_pos`. -/
theorem dedekindPsi_pos (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ {d ∈ N.divisors | Squarefree d} :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hN, squarefree_one⟩
  have hs : N ≤ ∑ d ∈ {d ∈ N.divisors | Squarefree d}, N / d := by
    simpa using Finset.single_le_sum (f := fun d => N / d) (fun d _ => Nat.zero_le _) h1
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero hN) hs

/-! ### The counting core -/

/-- A full block of `g * m` consecutive residues contains `m * φ(g)` coprime to
`g`: `Coprime g` is `g`-periodic and each period has `φ(g)` of them. -/
theorem card_filter_coprime_range_mul (g m : ℕ) :
    ((range (g * m)).filter (fun b => Nat.Coprime g b)).card = m * Nat.totient g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.count_eq_card_filter_range] at ih ⊢
    rw [Nat.mul_succ, Nat.count_add, ih, Nat.succ_mul]
    congr 1
    rw [Nat.count_eq_card_filter_range, Nat.totient_eq_card_coprime]
    refine congrArg card (filter_congr (fun k _ => ?_))
    have hper := (Nat.periodic_coprime g).nat_mul m
    rw [Nat.cast_id] at hper
    rw [show g * m + k = k + m * g by ring]
    exact Iff.of_eq (hper k)

/-- The Dedekind-`ψ` fibre value `(d / gcd a d) * φ(gcd a d)`. -/
abbrev dedekindPsiFibre (x : ℕ × ℕ) : ℕ :=
  (x.2 / Nat.gcd x.1 x.2) * Nat.totient (Nat.gcd x.1 x.2)

/-- The fibre count: the `b < d` coprime to `gcd a d` number `dedekindPsiFibre (a, d)`. -/
theorem card_fibre (a d : ℕ) :
    ((range d).filter (fun b => Nat.Coprime (Nat.gcd a d) b)).card =
      dedekindPsiFibre (a, d) := by
  set g := Nat.gcd a d with hg
  have hgd : g ∣ d := Nat.gcd_dvd_right a d
  obtain ⟨m, hm⟩ := hgd
  rcases Nat.eq_zero_or_pos g with hg0 | hgpos
  ·
    have hd0 : d = 0 := by rw [hm, hg0, zero_mul]
    simp [dedekindPsiFibre, hd0]
  · conv_lhs => rw [hm]
    rw [card_filter_coprime_range_mul, dedekindPsiFibre]
    simp only
    rw [← hg, hm, Nat.mul_div_cancel_left m hgpos]
