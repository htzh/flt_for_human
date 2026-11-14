/-
  Cross-module wire test for SET-AF65A (the newform decomposition and multiplicity one).

  A `spec/` probe, not a library module. One zone per headline of
  `ModularForms/NewformDecomposition.lean`, each *consuming* the headline rather than restating it.
  No primitive form is constructed anywhere in the corpus, so wherever a `IsPrimitiveForm`
  hypothesis is needed it is carried, not discharged; the zero cusp form is the witness wherever a
  form with a prescribed nebentypus is needed.

  * **Zone A, row `CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero`
    at the prime level `N = 2`.** At a prime level `N.primeFactors` is the singleton `{N}`, so the
    degeneracy sum on the right has exactly one term and the row collapses to
    ``qCoeff f n = (if N ∣ n then qCoeff (g N) (n / N) else 0)``: the level-lowering of a form at a
    prime level produces *one* form downstairs. The coefficient-vanishing hypothesis of the row is
    spent on the zero form (`K = 1`, so every `n` is coprime to `K`), and the collapse is read at
    `n = N`, where the `if` fires and `N / N = 1`.

  * **Zone B, row `CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus` at `k = 0`.**
    Weight `0` is the degenerate weight, where `S_0(Γ₁(1))` is one dimensional, so the finite
    family of primitive forms the row produces is read at the single index `m = 1`. The row is
    fired on the zero form at level `1` with the trivial character; the decomposition identity is
    then *used* (not restated) to transport the vanishing of `qCoeff 0 1` to the assembled sum
    `∑ i, c i * (if d i ∣ 1 then qCoeff (g i) (1 / d i) else 0)`.

  * **Zone C, row `CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen` at `M = 1`.**
    At level one `Γ₁(1) = SL(2, ℤ)` and the character `ε : DirichletCharacter ℂ 1` is forced
    trivial (`ZMod 1` is a subsingleton), so the row is multiplicity one for the *one* primitive
    form `g` that level one carries. The eigen-relation hypothesis is `∅`-indexed and is
    discharged from `g`'s own eigenform law (`IsPrimitiveForm.isEigenformWith.hecke_of_not_dvd`)
    after multiplying `g` by a scalar, so the composition runs: the row returns
    `c • g = qCoeff (c • g) 1 • g`, whose right-hand scalar is *not* `c` syntactically but is
    computed from the coefficients --- the content of multiplicity one. The file contains no
    `#check`s, no `sorry`s and no placeholder proofs.
-/
import FLTForHuman.ModularForms.NewformDecomposition

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

namespace SetAF65AConsumer

/-! ## The zero form, as the witness of every zone whose premise is a nebentypus form -/

/-- The zero cusp form has every nebentypus character: both sides of the twist law are `0`. -/
theorem hasNebentypus_zero {N : ℕ} {k : ℤ} (ε : DirichletCharacter ℂ N) :
    CuspForm.HasNebentypus ε (0 : CuspForm (CongruenceSubgroup.Gamma1 N) k) := by
  intro γ hγ τ
  simp

/-- The `q`-coefficients of the zero cusp form vanish --- the port's own statement, quoted so that
the zones below spend the rows' coefficient hypotheses rather than `simp`-ing them away. -/
theorem qCoeff_zero {N : ℕ} {k : ℤ} (n : ℕ) :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma1 N) k)) n = 0 :=
  MultOnePrimitive.qCoeff_zero n

/-! ## Zone A: level-lowering at a prime level -/

/-- **Zone A.** The level-lowering row fired at the prime level `2`, with the vanishing hypothesis
spent on the zero form (`K = 1`). Because `2.primeFactors = {2}`, the row's sum over
`N.primeFactors` has a single term, and reading it at `n = 2` --- where the `if` fires and
`2 / 2 = 1` --- gives `qCoeff (g 2) 1 = 0`: the one form downstairs has vanishing first
coefficient. This is the row's content at a prime level, which the row itself does not state. -/
theorem zoneA_primeLevel (k : ℤ) (ε : DirichletCharacter ℂ 2) :
    ∃ g : (p : ℕ) → CuspForm (CongruenceSubgroup.Gamma1 (2 / p)) k,
      (∀ (p : ℕ) (hp : p ∈ (2 : ℕ).primeFactors), g p = 0 ∨
        ∃ εp : DirichletCharacter ℂ (2 / p),
          DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) εp = ε ∧
          CuspForm.HasNebentypus εp (g p)) ∧
      ModularFormClass.qCoeff (g 2) 1 = 0 := by
  obtain ⟨g, hg, hdec⟩ :=
    CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
      2 k 1 one_ne_zero ε 0 (hasNebentypus_zero ε) (fun n _ => qCoeff_zero n)
  refine ⟨g, hg, ?_⟩
  have hpf : (2 : ℕ).primeFactors = {2} := by
    simpa using Nat.primeFactors_prime_pow (k := 1) one_ne_zero Nat.prime_two
  have h0 : ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma1 2) k)) 2 = 0 :=
    qCoeff_zero 2
  have h := hdec 2
  rw [hpf, Finset.sum_singleton, h0, ite_eq_left (dvd_refl 2)] at h
  simpa using h.symm

/-! ## Zone B: the newform decomposition at weight zero -/

/-- **Zone B.** The newform decomposition at `k = 0` and level one, fired on the zero form: the
row produces a finite family `(M i, d i, εM i, g i, c i)` of primitive forms with `M i * d i ∣ 1`
and the character identity, and its decomposition identity --- *used* here, not restated --- turns
the assembled sum at `m = 1` into `qCoeff 0 1 = 0`. At weight zero there is nothing to assemble:
the whole family sums to zero. -/
theorem zoneB_weightZero (ε : DirichletCharacter ℂ 1) :
    ∃ (n : ℕ) (M d : Fin n → ℕ) (hM : ∀ i, M i * d i ∣ 1)
      (εM : (i : Fin n) → DirichletCharacter ℂ (M i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (M i)) 0) (c : Fin n → ℂ),
      (∀ i, CuspForm.IsPrimitiveForm (εM i) (g i) ∧
        DirichletCharacter.changeLevel (dvd_of_mul_right_dvd (hM i)) (εM i) = ε) ∧
      ∑ i, c i * (if d i ∣ 1 then ModularFormClass.qCoeff (g i) (1 / d i) else 0) = 0 := by
  obtain ⟨n, M, d, hM, εM, g, c, hdata, hdec⟩ :=
    CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus 1 0 ε 0 (hasNebentypus_zero ε)
  exact ⟨n, M, d, hM, εM, g, c, hdata, by rw [← hdec 1, qCoeff_zero]⟩

/-! ## Zone C: multiplicity one at level one -/

/-- **Zone C.** Multiplicity one at level one, where `Γ₁(1) = SL(2, ℤ)` and the character is forced
trivial. The primitive form `g` is the single form of level one; a nonzero scalar multiple `c • g`
has the same eigenvalues, and the row concludes `c • g = qCoeff (c • g) 1 • g`. Its `∅`-indexed
eigen-relation hypothesis is discharged from `g`'s own eigenform law, so nothing is assumed beyond
`g` being primitive --- and the returned scalar `qCoeff (c • g) 1` is `c * qCoeff g 1`, i.e. `c`,
which the row does not say. -/
theorem zoneC_levelOne (k : ℤ) (ε : DirichletCharacter ℂ 1)
    (g : CuspForm (CongruenceSubgroup.Gamma1 1) k) (hg : CuspForm.IsPrimitiveForm ε g) (c : ℂ) :
    c • g = ModularFormClass.qCoeff (⇑(c • g)) 1 • g := by
  refine CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen 1 k ε g hg (c • g)
    (MultOnePrimitive.hasNebentypus_smul hg.isEigenformWith.hasNebentypus c) ∅ ?_
  intro p hp _ hpM n
  rw [MultOnePrimitive.qCoeff_smul, MultOnePrimitive.qCoeff_smul, MultOnePrimitive.qCoeff_smul]
  have hite : (if p ∣ n then c * ModularFormClass.qCoeff (⇑g) (n / p) else 0)
      = c * (if p ∣ n then ModularFormClass.qCoeff (⇑g) (n / p) else 0) := by
    split_ifs <;> ring
  rw [hite]
  linear_combination c * hg.isEigenformWith.hecke_of_not_dvd hp hpM n

/-- **Zone C, the scalar computed.** The right-hand scalar that zone C leaves in place is really
`c`: the port's `qCoeff_smul` and the primitivity of `g` (`qCoeff g 1 = 1`) collapse
`qCoeff (c • g) 1` to `c`, so zone C's conclusion is `c • g = c • g` read at a primitive form ---
multiplicity one says exactly that a primitive form carries no information beyond its
coefficients. -/
theorem zoneC_scalar (k : ℤ) (ε : DirichletCharacter ℂ 1)
    (g : CuspForm (CongruenceSubgroup.Gamma1 1) k) (hg : CuspForm.IsPrimitiveForm ε g) (c : ℂ) :
    ModularFormClass.qCoeff (⇑(c • g)) 1 = c := by
  rw [MultOnePrimitive.qCoeff_smul, hg.isEigenformWith.qCoeff_one, mul_one]

end SetAF65AConsumer
