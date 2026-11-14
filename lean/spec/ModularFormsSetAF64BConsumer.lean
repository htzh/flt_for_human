/-
  Cross-module wire test for SET-AF64B (the character separation of a sum, and the slash-sum
  trace).

  A `spec/` probe, not a library module. Every zone below *consumes* one of the two headlines
  of `ModularForms/NebentypusDirectSum.lean` rather than restating it:

  * **Zone C, row `CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq`.** The headline separates a
    finite sum of cusp forms whose nebentypus characters are pairwise different. Two readings
    are executed:

    - at `s = {0, 1}` with two *distinct* characters `ψ ≠ ψ'`: both summands are the zero form
      (so each has its own nebentypus, whatever it is), `f = 0`, and the conclusion is that the
      `ε`-filtered subsum still equals `f`. The distinctness of the pair is exactly what makes
      the filter a proper subset of `s`, so this is the non-vacuous shape of the row;
    - at `s = ∅`: the hypotheses on the summands are vacuous, `∑ i ∈ ∅, g i = 0 = f`, and the
      row degenerates to `∑ i ∈ ∅, g i = f` --- the vacuous reading of the same statement.

  * **Zone D, row `CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash`.**
    The headline says the `q`-slash trace from level `q * t` down to `t` keeps the coefficient
    vanishing at the indices prime to `K`, for `q` coprime to `K`. Two readings:

    - at `q = 1` the trace is `q = 1` times the identity (`∑_{j < 1}` is a single term,
      `S T⁰ S⁻¹ = 1`), so the vanishing is inherited unchanged;
    - at `q = t = 2`, `K = 3` and the index `n = 1`: the exponential sum of the trace collapses
      to `q = 2` exactly at the indices that are divisible by `q` (`sum_exp_two_pi_mul`), so the
      index `1`, which is prime to `K = 3`, is untouched by the depletion.

  In both rows the witness form is `0`, the only cusp form for which the coefficient vanishing
  and the nebentypus hypothesis are available without constructing an eigenform; every zone is
  nevertheless an application of the headline itself, with all of the headline's own premises
  discharged. The file contains no `#check` commands and no placeholder proofs.
-/
import FLTForHuman.ModularForms.NebentypusDirectSum

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace SetAF64BConsumer

/- `Finset.filter` in the statements below needs the very decidability hypothesis that the
headline itself carries; `classical` only reaches proofs, so it is installed here. -/
attribute [local instance] Classical.decEq

/-! ## The zero form, as the witness of both rows -/

/-- The zero cusp form has every nebentypus character: both sides of the twist law are `0`. -/
theorem hasNebentypus_zero {N : ℕ} {k : ℤ} (ε : DirichletCharacter ℂ N) :
    CuspForm.HasNebentypus ε (0 : CuspForm (CongruenceSubgroup.Gamma1 N) k) := by
  intro γ hγ τ
  simp

/-- The `q`-coefficients of the zero cusp form vanish, so the row's vanishing hypothesis is
free at the zero form. -/
theorem qCoeff_zero_form {N : ℕ} {k : ℤ} (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma1 N) k)) n = 0 := by
  simp [ModularFormClass.qCoeff, UpperHalfPlane.qExpansion_zero]

/-! ## Zone C: the character separation -/

/-- **Zone C, `s = {0, 1}` with two distinct characters.** The two summands are both the zero
form and carry the characters `ψ` and `ψ'` with `ψ ≠ ψ'`; the target `f` is the zero form with
character `ε`. The headline returns the `ε`-filtered subsum, and `ε ≠ ψ'` is what makes that
subsum a proper part of `s`. -/
theorem zoneC_pair (N : ℕ) [NeZero N] (k : ℤ) (ψ ψ' ε : DirichletCharacter ℂ N)
    (_hε : ε = ψ) (_hne : ψ ≠ ψ') :
    ∑ _i ∈ (Finset.univ : Finset (Fin 2)).filter
        (fun i => (![ψ, ψ'] : Fin 2 → DirichletCharacter ℂ N) i = ε),
        (0 : CuspForm (CongruenceSubgroup.Gamma1 N) k) = 0 := by
  classical
  exact CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq
    (s := (Finset.univ : Finset (Fin 2)))
    (χ := ![ψ, ψ'])
    (g := fun _ => (0 : CuspForm (CongruenceSubgroup.Gamma1 N) k))
    (fun _ _ => hasNebentypus_zero _)
    (ε := ε) (f := 0) (hasNebentypus_zero ε) (by simp)

/-- **Zone C at `s = ∅`.** The hypotheses on the summands hold vacuously and the total sum is
`0 = f`, so the row's `ε`-filtered sum is the empty sum, which is `f` because `f` is the zero
form. -/
theorem zoneC_empty (N : ℕ) [NeZero N] (k : ℤ) (ψ ε : DirichletCharacter ℂ N) :
    ∑ _i ∈ (∅ : Finset (Fin 2)).filter
        (fun i => (![ψ, ψ] : Fin 2 → DirichletCharacter ℂ N) i = ε),
        (0 : CuspForm (CongruenceSubgroup.Gamma1 N) k) = 0 := by
  classical
  exact CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq
    (s := (∅ : Finset (Fin 2)))
    (χ := ![ψ, ψ])
    (g := fun _ => (0 : CuspForm (CongruenceSubgroup.Gamma1 N) k))
    (fun _ h => absurd h (Finset.notMem_empty _))
    (ε := ε) (f := 0) (hasNebentypus_zero ε) (by simp)

/-! ## Zone D: the slash-sum trace -/

/-- **Zone D at `q = 1`.** The trace is `∑_{j < 1}`: a single term, `S T⁰ S⁻¹ = 1`, i.e. the
identity, so the coefficient vanishing at the indices prime to `K` is inherited from `E`
unchanged. Here `t = 1`, `K` is arbitrary and the level of `E` is `q * t = 1`. -/
theorem zoneD_q_one (k : ℤ) (ε : DirichletCharacter ℂ 1) (K n : ℕ) (hK : K ≠ 0)
    (hn : Nat.Coprime n K) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma1 1) k)) n = 0 := by
  classical
  refine CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash
    (q := 1) (t := 1) one_ne_zero dvd_rfl (k := k) ε
    (0 : CuspForm (CongruenceSubgroup.Gamma1 (1 * 1)) k)
    (hasNebentypus_zero _) (K := K) hK (Nat.coprime_one_right K)
    (fun m _ => qCoeff_zero_form m) (N' := 1) 0 ?_ n hn
  intro τ
  simp

/-- **Zone D at `q = t = 2`, `K = 3`, `n = 1`.** The trace from level `q * t = 4` down to `t = 2`
is `q = 2` times the identity on the `q`-part of the `q`-expansion and `0` off it, so the index
`1` --- prime to `K = 3`, and not divisible by `q` --- is untouched: the trace's coefficient
there is the coefficient of `E`, which vanishes. -/
theorem zoneD_q_two (k : ℤ) (ε : DirichletCharacter ℂ 2) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma1 2) k)) 1 = 0 := by
  classical
  refine CuspForm.HasNebentypus.qCoeff_eq_zero_of_coprime_of_apply_eq_sum_slash
    (q := 2) (t := 2) (by norm_num) ⟨1, by norm_num⟩ (k := k) ε
    (0 : CuspForm (CongruenceSubgroup.Gamma1 (2 * 2)) k)
    (hasNebentypus_zero _) (K := 3) (by norm_num) (by norm_num)
    (fun m _ => qCoeff_zero_form m) (N' := 2) 0 ?_ 1 (by norm_num)
  intro τ
  simp

end SetAF64BConsumer
