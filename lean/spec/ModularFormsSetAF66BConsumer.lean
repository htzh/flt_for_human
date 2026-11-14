/-
  Cross-module wire test for SET-AF66B (a primitive form behind a Hecke eigenform, and the
  `j`-conjugation invariance).

  A `spec/` probe, not a library module. Every zone below *consumes* one of the three headlines
  rather than restating it. The witness that carries the eigenform hypotheses everywhere is
  `CuspForm.IsEigenformWith`, which bundles exactly the three facts the two existence headlines ask
  for --- `qCoeff f 1 = 1`, the Hecke eigen-relation at every prime not dividing the level, and
  `HasNebentypus` --- so no eigenform has to be constructed, and the eigenvalue relation of row G is
  *discharged* from it rather than assumed.

  * **Zone G, row `CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen`.** Read at a
    prime level `M`. The eigen-relation `hf` (with eigenvalues `lam p = qCoeff f p`) is not an
    assumption of the zone: it is produced from the carried eigenform hypothesis by
    `CuspForm.IsEigenformWith.hecke_of_not_dvd`, and the `HasNebentypus` premise of the headline is
    the third component of the same hypothesis. The *new* content is the dichotomy on the returned
    level: `M' ∣ M` with `M` prime forces `M' = 1` or `M' = M` --- so behind an eigenform at a prime
    level sits a primitive form at level `1` or at the prime itself, and nowhere else.

  * **Zone H, row `CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen`.** Read at `N = 1`. Here
    `M' ∣ 1` collapses the returned level to `1` outright, so the headline says that a level-`1`
    eigenform is already primitive at level `1` up to the character, and the character relation
    `ε p * p ^ (k - 1) = χ p` becomes an identity read at `χ p = ε p * p ^ (k - 1)`. The
    eigen-relation `hf` (which carries the `p ^ (k - 1)` factor that row G's version has) is again
    discharged from the carried eigenform hypothesis.

  * **Zone I, row `CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem`.** The
    invariance hypothesis `∀ γ ∈ Γ, jConjSL γ ∈ Γ` is spent at `γ = 1`: at `Γ = ⊥` the only element
    *is* `1`, so `jConjSL 1 = 1 ∈ ⊥` discharges it with no structure theory, and the headline yields
    the `j`-conjugated form. The second reading spends it at `Γ = ⊤` instead, where it is free, and
    reads the conclusion at a form invariant under `τ ↦ J • τ`: then the conjugated form is
    `τ ↦ conj (f τ)`, the `j`-conjugation acting as complex conjugation alone.
-/
import FLTForHuman.ModularForms.PrimitiveFormExistence

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup
open scoped MatrixGroups

namespace SetAF66BConsumer

/-! ## Zone G: a primitive form behind an eigenform at a prime level -/

/-- **Zone G.** At a prime level `M`, an eigenform with nebentypus whose coefficients satisfy the
Hecke relation at every prime not dividing `M` has a primitive form at a level dividing `M`. The
relation itself is *discharged* from the eigenform hypothesis: `CuspForm.IsEigenformWith.hecke_of_not_dvd`
is exactly the headline's `hf` with eigenvalues `lam p = qCoeff f p`, and the nebentypus premise is
the same hypothesis' third component.

The conclusion is the dichotomy the headline does not state: `M' ∣ M` with `M` prime leaves only
`M' = 1` or `M' = M`. -/
theorem zoneG_prime_level (M : ℕ) (hM : M.Prime) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (hf0 : f ≠ 0)
    (hh : CuspForm.IsEigenformWith ε f) :
    ∃ (M' : ℕ) (_ : NeZero M') (εM : DirichletCharacter ℂ M') (g : CuspForm (Gamma1 M') k),
      (M' = 1 ∨ M' = M) ∧ CuspForm.IsPrimitiveForm εM g ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M →
        ModularFormClass.qCoeff g p = ModularFormClass.qCoeff f p ∧
          εM (p : ZMod M') = ε (p : ZMod M) := by
  have : NeZero M := ⟨hM.ne_zero⟩
  obtain ⟨M', hne, εM, g, hdvd, hprim, hcoeff⟩ :=
    CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen M k ε f hf0 hh.2.2.2
      (fun p => ModularFormClass.qCoeff f p)
      (fun p hp hpM n => hh.2.1 p hp hpM n)
  exact ⟨M', hne, εM, g, (Nat.dvd_prime hM).mp hdvd, hprim, hcoeff⟩

/-! ## Zone H: level `1` collapses -/

/-- **Zone H** at `N = 1`. The returned level divides `1`, so it *is* `1`, and the headline returns a
primitive level-`1` form whose coefficients at every prime agree with those of `f` and whose
character reproduces `χ p = ε p * p ^ (k - 1)`.

Both premises of the headline are discharged from the carried eigenform hypothesis `hh`: `hf₁` is
`hh.1`, and `hf` is `hh.2.1` read at `χ p = ε p * p ^ (k - 1)` (row H's relation carries no explicit
`p ^ (k - 1)` factor, so that factor is folded into `χ`). -/
theorem zoneH_level_one (k : ℤ) (ε : DirichletCharacter ℂ 1) (f : CuspForm (Gamma1 1) k)
    (hh : CuspForm.IsEigenformWith ε f) :
    ∃ (M' : ℕ) (_ : NeZero M') (εM : DirichletCharacter ℂ M') (g : CuspForm (Gamma1 M') k),
      M' = 1 ∧ CuspForm.IsPrimitiveForm εM g ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ 1 →
        ModularFormClass.qCoeff g p = ModularFormClass.qCoeff f p ∧
          εM (p : ZMod M') * (p : ℂ) ^ (k - 1) = ε (p : ZMod 1) * (p : ℂ) ^ (k - 1) := by
  obtain ⟨M', hne, εM, g, hdvd, hprim, hcoeff⟩ :=
    CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen 1 k f hh.1
      (fun p => ε (p : ZMod 1) * (p : ℂ) ^ (k - 1))
      (fun p hp hp1 n => hh.2.1 p hp hp1 n)
  exact ⟨M', hne, εM, g, Nat.dvd_one.mp hdvd, hprim, hcoeff⟩

/-! ## Zone I: the `j`-conjugation invariance spent at `γ = 1` -/

/-- **Zone I**, first reading: at `Γ = ⊥` the invariance hypothesis `∀ γ ∈ Γ, jConjSL γ ∈ Γ` is spent
at `γ = 1`, the only element of `⊥`, where it holds by `map_one`. The headline then returns a cusp
form for `⊥` that is the `j`-conjugate of `f`, read at every `τ`. -/
theorem zoneI_bot_jConj (k : ℤ) (f : CuspForm (⊥ : Subgroup SL(2, ℤ)) k) :
    ∃ g : CuspForm (⊥ : Subgroup SL(2, ℤ)) k,
      ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)) :=
  CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem ⊥ (fun γ hγ => by
    rw [Subgroup.mem_bot] at hγ ⊢
    subst hγ
    simp) k f

/-- **Zone I**, second reading: at `Γ = ⊤` the invariance hypothesis is free, and the conclusion is
read at a form invariant under `τ ↦ J • τ`. Then `f (J • τ) = f τ`, so the conjugated form of the
headline is `τ ↦ conj (f τ)`: the `j`-conjugation acts as complex conjugation, with no visible
`J`-translate left. -/
theorem zoneI_top_J_invariant (k : ℤ) (f : CuspForm (⊤ : Subgroup SL(2, ℤ)) k)
    (hfJ : ∀ τ : UpperHalfPlane, f (UpperHalfPlane.J • τ) = f τ) :
    ∃ g : CuspForm (⊤ : Subgroup SL(2, ℤ)) k,
      ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f τ) := by
  obtain ⟨g, hg⟩ :=
    CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem ⊤
      (fun γ _ => Subgroup.mem_top γ) k f
  exact ⟨g, fun τ => by rw [hg τ, hfJ τ]⟩

end SetAF66BConsumer
