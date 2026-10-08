/-
  Cross-module wire test for **S-4**, the `E₄³ − E₆²` / `jLattice` modular-polynomial
  tail: the `SL₂(ℤ)` Smith leaf of
  `FLTForHuman/Algebra/SpecialLinearGroupSmith.lean` and the three
  `ModularCurve.ModularPolynomialData` headlines, the `E₄³`/`Δ` forms and the
  `q`-expansion bookkeeping of `FLTForHuman/ModularCurve/ModularPolynomialE4Cube.lean`.

  A `spec/` probe, not a library module: it is outside every lake target and is run
  with `lake env lean`, so a green library build stays meaningful. Deleting either
  module makes it fail (the imports and every zone name vanish).

  Executed zones (each a real composition, no `#check`, no `sorry`):

  * zone 1 — the **leaf at concrete `a, b, d`**: `exists_coprime_mul_add` and the
    headline at `(N, a, b, d) = (6, 2, 1, 3)`, with the produced matrices' determinant
    certificates extracted;
  * zone 2 — the **`E₄³`/`Δ` forms** (`coe_e4cubeSL`/`coe_deltaSL`) and the **smul
    headline at a concrete level-one form**, the ported `modularPolynomialDataOne`,
    together with the `ModularForm` degeneracy step at `d = 1`;
  * zone 3 — the **coset headline at the concrete primitive triple `(2, 1, 3)`**
    (membership discharged through `mem_primCosetReps`), i.e. the leaf feeding the
    smul form through `upperTriangularGL`;
  * zone 4 — **S-3's headline into the `jLattice` form**: the coset triple is produced
    by `PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic`, both
    `jLattice`s are rewritten by `PeriodPair.jLattice_ofTau`, and the coset headline
    closes; the packaged `jLattice` headline is exercised as well;
  * zone 5 — the `jt` invariance bridge of `CosetRootAux`.
-/
import FLTForHuman.Algebra.SpecialLinearGroupSmith
import FLTForHuman.ModularCurve.ModularPolynomialE4Cube

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open scoped Matrix MatrixGroups UpperHalfPlane
open UpperHalfPlane

namespace ModularPolynomialE4CubeConsumer

/-! ### Zone 1 — the leaf at concrete `a, b, d` -/

/-- `exists_coprime_mul_add` at `(a, b, d) = (2, 1, 3)`: some `p` makes `2p + 1`
coprime to `3`. -/
example : ∃ p : ℕ, Nat.Coprime (2 * p + 1) 3 :=
  Matrix.SpecialLinearGroup.PrimitiveSmith.exists_coprime_mul_add (by norm_num) (by norm_num)

/-- The headline at `(N, a, b, d) = (6, 2, 1, 3)`: the two matrices are produced and
their determinant certificates are read off. -/
example :
    ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (γ₁ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∧ (γ₂ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∧
        !![(2 : ℤ), 1; 0, 3] =
          (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(6 : ℤ), 0; 0, 1] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) := by
  obtain ⟨γ₁, γ₂, hM⟩ :=
    Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one
      (N := 6) (a := 2) (b := 1) (d := 3) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨γ₁, γ₂, γ₁.det_coe, γ₂.det_coe, hM⟩

/-- The `SL₂(ℤ)` sandwich is exactly the pin's shape at the concrete triple: the same
statement at `(2, 1, 3)`, consumed as the leaf's conclusion. -/
example :
    ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      !![(2 : ℤ), 1; 0, 3] =
        (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(6 : ℤ), 0; 0, 1] * (γ₂ : Matrix (Fin 2) (Fin 2) ℤ) :=
  Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one
    (N := 6) (a := 2) (b := 1) (d := 3) (by norm_num) (by norm_num) (by norm_num)

/-! ### Zone 2 — the `E₄³`/`Δ` forms and the smul headline -/

/-- The level-one form `e4cubeSL` really is `E₄³`. -/
example : (ModularCurve.DeepCosetAux.e4cubeSL : ℍ → ℂ) =
    fun τ => (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 :=
  ModularCurve.DeepCosetAux.coe_e4cubeSL

/-- The level-one form `deltaSL` really is `Δ`. -/
example : (ModularCurve.DeepCosetAux.deltaSL : ℍ → ℂ) = ModularForm.discriminant :=
  ModularCurve.DeepCosetAux.coe_deltaSL

/-- The ported `ModularForm` degeneracy step at `e4cube1` and `d = 1`. -/
example : ∃ e : ModularForm (CongruenceSubgroup.Gamma0 1) 12,
    ⇑e = fun τ => ModularCurve.DeepCosetAux.e4cube1 (ModularForm.heckeDiagMatrix 1 • τ) :=
  ModularForm.exists_degeneracy_Gamma0 (show 1 * 1 ∣ 1 by norm_num)
    ModularCurve.DeepCosetAux.e4cube1

/-- **The smul headline at a concrete level-one form**: the ported
`modularPolynomialDataOne`, with `σ' = σ` (the `N = 1` case of `σ' = N · σ`). -/
example (τ : ℍ) :
    ((ModularCurve.modularPolynomialDataOne).Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ) = 0 :=
  ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_smul_eq_zero 1
    ModularCurve.modularPolynomialDataOne τ τ (by simp)

/-! ### Zone 3 — the coset headline at the concrete primitive triple `(2, 1, 3)` -/

/-- `(2, 1, 3)` is a primitive coset triple at `N = 6`. -/
example : (2, 1, 3) ∈ ModularCurve.primCosetReps 6 := by
  rw [ModularCurve.mem_primCosetReps (by norm_num)]
  norm_num

/-- **The coset headline at `(2, 1, 3)`**: the leaf's sandwich is consumed inside the
proof, and `τ' = (2τ + 1)/3`. -/
example (data : ModularCurve.ModularPolynomialData 6) (τ τ' : ℍ)
    (hτ' : (τ' : ℂ) = ((2 : ℂ) * τ + 1) / 3) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') = 0 := by
  refine ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero
    (N := 6) data (a := 2) (b := 1) (d := 3) ?_ τ τ' ?_
  · rw [ModularCurve.mem_primCosetReps (by norm_num)]
    norm_num
  · simpa using hτ'

/-! ### Zone 4 — S-3's headline into the `jLattice` form -/

/-- **S-3's headline composed into the coset form**: produce `(a, b, d, τ, σ)` from
`PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic`, rewrite both
`jLattice`s by `PeriodPair.jLattice_ofTau`, and apply the coset headline. -/
example (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).eval L'.jLattice = 0 := by
  obtain ⟨a, b, d, τ, σ, habd, hσ, hjL, hjL'⟩ :=
    PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic L L' hsub hidx hcyc
  rw [hjL, hjL', PeriodPair.jLattice_ofTau, PeriodPair.jLattice_ofTau]
  exact ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero
    N data habd τ σ hσ

/-- The packaged `jLattice` headline, at the same S-2-shaped hypotheses. -/
example (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N) (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).eval L'.jLattice = 0 :=
  ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic N data L L' hsub hidx hcyc

/-! ### Zone 5 — the `jt` invariance bridge -/

/-- `jt` is `𝒮ℒ`-invariant, through the `sl_mem` inclusion of the coset module. -/
example (γ : SL(2, ℤ)) (z : ℍ) :
    ModularCurve.CosetRootAux.jt ((γ : GL (Fin 2) ℝ) • z) = ModularCurve.CosetRootAux.jt z :=
  ModularCurve.CosetRootAux.jt_smul γ z

end ModularPolynomialE4CubeConsumer

end
