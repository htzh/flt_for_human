/-
  Cross-module wire test for SET-AF64A (the `T_p`-invariance on `Γ₀(N)` and the simultaneous
  eigenbasis).

  A `spec/` probe, not a library module. Two composition zones, each one *consuming* a
  headline of `ModularForms/NebentypusEigenbasis.lean` rather than restating it:

  * **Zone A (`ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0`) at
    `N = 1` and `p = 2`.** At level `1` the group `Γ₀(1)` is all of `SL(2, ℤ)` and the
    character `ε : DirichletCharacter ℂ 1` is forced trivial (`ZMod 1` is a subsingleton),
    so the row's two nondegenerate inputs are exactly `2.Prime` and `¬ 2 ∣ 1`; the
    nebentypus law is the zero law, discharged by `simp` on the zero form. The identity is
    then read off at `γ = 1 ∈ Γ₀(1)`, so the `T₂`-operator is seen to preserve the
    (trivial) nebentypus of a level-`1` form with no analytic side conditions.

  * **Zone B (`CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen`) at `k = 0`.**
    Weight `0` is the degenerate weight, where `S_0(Γ₁(N))` is at most one dimensional, so
    the basis is `Fin 0` or `Fin 1` and the row's content is its *conjunct structure*: the
    basis is unpacked and the `CuspForm.HasNebentypus` conjunct is read off `b i` for each
    basis vector, and then spent through `SSbasis.hasNebentypus_iff` to obtain the
    `Γ₀(N)`-slash form of the same law. Both declarations are applications of the
    headline; the file has no `#check`s and no `sorry`s.
-/
import FLTForHuman.ModularForms.NebentypusEigenbasis

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped ModularForm UpperHalfPlane MatrixGroups

namespace SetAF64AConsumer

/-! ## Zone A: the `Γ₀`-invariance of `T_p` at `N = 1` and `p = 2` -/

/-- **Zone A.** Row A at level `1` (`Γ₀(1) = SL(2, ℤ)`, trivial nebentypus) and at the
prime `p = 2`, read off at `γ = 1`: the operator
`f ↦ U₂ f + ε(2) • (f ∣[k] diag(2))` preserves the `ε`-eigenspace on `Γ₀(1)`. -/
theorem zoneA :
    (ModularForm.heckeU (0 : ℤ) 2 (0 : ℍ → ℂ) + (1 : DirichletCharacter ℂ 1) (2 : ZMod 1) •
        ((0 : ℍ → ℂ) ∣[(0 : ℤ)] heckeDiagMatrix 2)) ∣[(0 : ℤ)]
        (Matrix.SpecialLinearGroup.mapGL ℝ (1 : SL(2, ℤ)))
      = (1 : DirichletCharacter ℂ 1) (((1 : SL(2, ℤ)) 1 1 : ℤ) : ZMod 1) •
        (ModularForm.heckeU (0 : ℤ) 2 (0 : ℍ → ℂ) + (1 : DirichletCharacter ℂ 1) (2 : ZMod 1) •
          ((0 : ℍ → ℂ) ∣[(0 : ℤ)] heckeDiagMatrix 2)) :=
  ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 0
    (by norm_num) (by norm_num) (1 : DirichletCharacter ℂ 1)
    (fun (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma0 1) => by
      rw [SlashAction.zero_slash]
      simp) (1 : SL(2, ℤ)) (one_mem _)

/-- **Zone A, general `γ`.** The same row fired with `γ` an arbitrary element of `Γ₀(1)`
and an arbitrary level-`1` form `f` obeying the (trivial) nebentypus law: the conclusion is
literally the row's, with the two number-theoretic side conditions already spent. -/
theorem zoneA_slash (k : ℤ) (ε : DirichletCharacter ℂ 1) (f : ℍ → ℂ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 1)
    (hf : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 1 →
      f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = ε (((γ 1 1 : ℤ)) : ZMod 1) • f) :
    (ModularForm.heckeU k 2 f + ε (2 : ZMod 1) • (f ∣[k] heckeDiagMatrix 2)) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ)
      = ε (((γ 1 1 : ℤ)) : ZMod 1) •
        (ModularForm.heckeU k 2 f + ε (2 : ZMod 1) • (f ∣[k] heckeDiagMatrix 2)) :=
  ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 k
    (by norm_num) (by norm_num) ε hf γ hγ

/-- **Zone A, an odd level.** The same row at `N = 3` and `p = 2`: `Γ₀(3)` is a proper
subgroup of `SL(2, ℤ)` and `ε : DirichletCharacter ℂ 3` is no longer forced trivial, so this
is the level-`1` zone's nondegenerate companion (`2 ∤ 3` is the row's own side condition).
Fired on the zero form at `γ = 1`. -/
theorem zoneA_oddLevel :
    (ModularForm.heckeU (0 : ℤ) 2 (0 : ℍ → ℂ) + (1 : DirichletCharacter ℂ 3) (2 : ZMod 3) •
        ((0 : ℍ → ℂ) ∣[(0 : ℤ)] heckeDiagMatrix 2)) ∣[(0 : ℤ)]
        (Matrix.SpecialLinearGroup.mapGL ℝ (1 : SL(2, ℤ)))
      = (1 : DirichletCharacter ℂ 3) (((1 : SL(2, ℤ)) 1 1 : ℤ) : ZMod 3) •
        (ModularForm.heckeU (0 : ℤ) 2 (0 : ℍ → ℂ) + (1 : DirichletCharacter ℂ 3) (2 : ZMod 3) •
          ((0 : ℍ → ℂ) ∣[(0 : ℤ)] heckeDiagMatrix 2)) :=
  ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0 (N := 3) 0
    (by norm_num) (by norm_num) (1 : DirichletCharacter ℂ 3)
    (fun (γ : SL(2, ℤ)) (_ : γ ∈ CongruenceSubgroup.Gamma0 3) => by
      rw [SlashAction.zero_slash]
      simp) (1 : SL(2, ℤ)) (one_mem _)

/-! ## Zone B: the eigenbasis at weight `0` -/

/-- **Zone B.** Row B at `k = 0`: the eigenbasis of `S_0(Γ₁(N))` is unpacked, and the
`CuspForm.HasNebentypus` conjunct is read off each basis vector `b i`. -/
theorem zoneB (N : ℕ) [NeZero N] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 N) 0)),
      ∀ i : Fin n, ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε (b i) := by
  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen N 0
  exact ⟨n, b, fun i => by obtain ⟨ε, hε, -⟩ := hb i; exact ⟨ε, hε⟩⟩

/-- **Zone B, slash form.** The `HasNebentypus` conjunct read off in `zoneB`, spent through
`SSbasis.hasNebentypus_iff`: each basis vector of the weight-`0` eigenbasis transforms by
`ε` under every `γ ∈ Γ₀(N)`. -/
theorem zoneB_slash (N : ℕ) [NeZero N] {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 N) 0))
    (hb : ∀ i : Fin n, ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε (b i))
    (i : Fin n) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    ∃ ε : DirichletCharacter ℂ N,
      (⇑(b i) : ℍ → ℂ) ∣[(0 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ)
        = ε (SSbasis.dd (N := N) γ) • ⇑(b i) := by
  obtain ⟨ε, hε⟩ := hb i
  exact ⟨ε, (SSbasis.hasNebentypus_iff ε (b i)).mp hε γ hγ⟩

end SetAF64AConsumer
