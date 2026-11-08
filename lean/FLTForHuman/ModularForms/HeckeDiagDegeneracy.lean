/-
  The degeneracy lift `Diag_d` of a `Γ₁`-cusp form, and the coefficient criterion for vanishing.

  `exists_degeneracy_gamma1_hasNebentypus`: for `M · d ∣ N` and a cusp form `g` at level `M`, the form
  `G τ = g (heckeDiagMatrix d • τ)` is a cusp form at level `N`, its `q`-expansion is the `d`-th
  subsequence padded with zeros (`qCoeff G n = if d ∣ n then qCoeff g (n/d) else 0`), and its nebentypus is
  the level change of `g`'s — the *degeneracy lift* `V_d` used to raise the level of a weight-one form.

  `gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero`: conversely, a `Γ₁(N)`-cusp form whose coefficients
  vanish at every `n` not divisible by a prime `p ∤ N` is zero — the coefficient criterion that makes the
  lift's `d`-subsequence reading lossless at the places where `U_p` is invertible.

  Transcribed whole from the pin's proof files
  `P2M/Sol/S_CuspForm_exists_degeneracy_gamma1_hasNebentypus.lean` (pinned `aa2d8b3`, 218 lines / 13
  declarations) and `S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.lean` (351 lines / 26
  declarations), with the statements from their `Theorems/` wrappers.

  spec-pin: Theorems/Thm_CuspForm_exists_degeneracy_gamma1_hasNebentypus.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_degeneracy_gamma1_hasNebentypus.lean
  spec-pin: Theorems/Thm_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.lean
  spec-pin: P2M/Sol/S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.lean
-/
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.HeckeNebentypus
import FLTForHuman.ModularForms.Gamma1Vanishing
import FLTForHuman.ModularForms.HeckePrelude
import FLTForHuman.ModularCurve.X1.QExpandStretch

set_option autoImplicit false

open CongruenceSubgroup
open ModularForm
open scoped MatrixGroups

noncomputable section

namespace CuspForm

open scoped UpperHalfPlane Manifold Real

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-! ## Row C — the degeneracy lift `Diag_d`

The pin's proof (`P2M/Sol/S_CuspForm_exists_degeneracy_gamma1_hasNebentypus.lean`, `aa2d8b3`): the
`1`-cocycle `diagMatInt d * γ = γ' * diagMatInt d` of the level pair `M ∣ N` (`exists_cocycle`,
`mem_Gamma1_of_cocycle`), its `SL(2, ℤ)` shadow `heckeDiagMatrix_mul_eq`, the stretched slash
`stretchSlash`/`stretch`, and the three properties read off it (`stretch_apply`, `qCoeff_stretch`,
`hasNebentypus_stretch`).

The pin's `T_mem_Gamma1`/`periodic_of_slash_T` pair and the `rescaleSlash_isZeroAt` cusp bound are not
repeated: the port's `CuspForm.cusp_periodic` (`ModularForms/HeckePrelude.lean`) is the same periodicity,
and the cusp bound is the `IsZeroAt.smul_iff` step written inline in `stretchSlash`. The pin's
`exists_cocycle_rescale` (`Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean:17`) is inlined in
`exists_cocycle`, and `diagMatInt`/`diagMatInt_map_eq` (:15, :60) are carried here since the port has no
`FreyPackage.ModMCarrier`.

Two imports are added to the manager's four (reported): `ModularForms/HeckePrelude.lean` for
`cusp_periodic`/`cusp_holo`/`cusp_bdd`, and `ModularCurve/X1/QExpandStretch.lean` for
`isCusp_heckeDiagMatrix_smul` (the pin's `heckeDiagMatrixQ`/`isCusp_smul_of_rat` cusp transport). -/

namespace DegeneracyGamma1

section Cocycle

variable {M N d : ℕ}

/-- The integer diagonal matrix `!![d, 0; 0, 1]` whose `ℤ`-side cocycle is `heckeDiagMatrix`'s on `ℍ`.
From `Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean:15`. -/
def diagMatInt (d : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(d : ℤ), 0; 0, 1]

/-- `diagMatInt d` is `heckeDiagMatrix d` after the scalar extension `ℤ → ℝ`.
From `Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean:60`. -/
theorem diagMatInt_map_eq (hd : d ≠ 0) :
    (diagMatInt d).map (algebraMap ℤ ℝ)
      = ((heckeDiagMatrix d : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [val_heckeDiagMatrix hd]; unfold diagMatInt
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The `1`-cocycle of the level pair `M · d ∣ N`: `Γ₀(N)` conjugated by `diagMatInt d` lands in
`Γ₀(M)`. The existence step is the pin's `exists_cocycle_rescale`
(`Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean:17`), inlined; the entry equations are the
pin's. -/
theorem exists_cocycle (hd : d ≠ 0) (hdMN : d * M ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 M ∧
      diagMatInt d * (γ : Matrix (Fin 2) (Fin 2) ℤ)
        = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * diagMatInt d ∧
      γ' 0 0 = γ 0 0 ∧ γ' 1 1 = γ 1 1 ∧ γ' 1 0 * d = γ 1 0 := by
  have key : ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      diagMatInt d * (γ : Matrix (Fin 2) (Fin 2) ℤ)
        = (δ : Matrix (Fin 2) (Fin 2) ℤ) * diagMatInt d := by
    have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
        (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
      have := γ.det_coe; rwa [Matrix.det_fin_two] at this
    have hMc : (N : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      have := Gamma0_mem.mp hγ; rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
    set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
    set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
    set e : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with he
    have hγmat : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, e] := by
      rw [ha, hb, hc, he]; exact Matrix.eta_fin_two _
    have hdMc : ((d * M : ℕ) : ℤ) ∣ c := dvd_trans (by exact_mod_cast hdMN) hMc
    obtain ⟨c', hc'⟩ := hdMc
    rw [Nat.cast_mul] at hc'
    have hdetδ : Matrix.det !![a, (d : ℤ) * b; (M : ℤ) * c', e] = 1 := by
      rw [Matrix.det_fin_two_of]; linear_combination hdet + b * hc'
    let δ : SL(2, ℤ) := ⟨!![a, (d : ℤ) * b; (M : ℤ) * c', e], hdetδ⟩
    refine ⟨δ, ?_, ?_⟩
    · rw [Gamma0_mem]
      show (((M : ℤ) * c' : ℤ) : ZMod M) = 0
      push_cast; rw [ZMod.natCast_self, zero_mul]
    · have hδval : (δ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, (d : ℤ) * b; (M : ℤ) * c', e] := rfl
      rw [hδval, hγmat]
      unfold diagMatInt
      rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      · show ((d : ℤ) * a + 0 * c : ℤ) = a * (d : ℤ) + (d : ℤ) * b * 0; ring
      · show ((d : ℤ) * b + 0 * e : ℤ) = a * 0 + (d : ℤ) * b * 1; ring
      · show (0 * a + 1 * c : ℤ) = (M : ℤ) * c' * (d : ℤ) + e * 0; linear_combination hc'
      · show (0 * b + 1 * e : ℤ) = (M : ℤ) * c' * 0 + e * 1; ring
  obtain ⟨γ', hγ', hconj⟩ := key
  have e00 := congrFun (congrFun hconj 0) 0
  have e11 := congrFun (congrFun hconj 1) 1
  have e10 := congrFun (congrFun hconj 1) 0
  simp [diagMatInt, Matrix.mul_apply, Fin.sum_univ_two] at e00 e11 e10
  have hd' : (d : ℤ) ≠ 0 := by exact_mod_cast hd
  refine ⟨γ', hγ', hconj, ?_, ?_, ?_⟩
  · have h' : (d : ℤ) * γ' 0 0 = (d : ℤ) * γ 0 0 := by linear_combination e00.symm
    exact mul_left_cancel₀ hd' h'
  · linear_combination e11.symm
  · linear_combination e10.symm

/-- `Γ₁(N)`-membership descends along the cocycle's diagonal entries. -/
theorem mem_Gamma1_of_cocycle (hMN : M ∣ N) {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N)
    (hγ' : γ' ∈ Gamma0 M) (h00 : γ' 0 0 = γ 0 0) (h11 : γ' 1 1 = γ 1 1) : γ' ∈ Gamma1 M := by
  rw [Gamma1_mem] at hγ ⊢
  obtain ⟨ha, he, -⟩ := hγ
  refine ⟨?_, ?_, by simpa using Gamma0_mem.mp hγ'⟩
  · rw [h00]
    have := (ZMod.castHom hMN (ZMod M)).congr_arg ha
    simpa only [map_intCast, map_one] using this
  · rw [h11]
    have := (ZMod.castHom hMN (ZMod M)).congr_arg he
    simpa only [map_intCast, map_one] using this

end Cocycle

section Form

variable {M N d : ℕ} [NeZero N] {k : ℤ}

/-- `M` is nonzero at level `M ∣ N`. -/
theorem neZero_of_dvd (hMN : M ∣ N) : NeZero M :=
  ⟨fun h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hMN))⟩

/-- The `SL(2, ℤ)` shadow of the cocycle: the diagonal Hecke matrix conjugates `γ` to `γ'`. -/
theorem heckeDiagMatrix_mul_eq (hd : d ≠ 0) {γ γ' : SL(2, ℤ)}
    (hconj : diagMatInt d * (γ : Matrix (Fin 2) (Fin 2) ℤ)
      = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * diagMatInt d) :
    heckeDiagMatrix d * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = Matrix.SpecialLinearGroup.mapGL ℝ γ' * heckeDiagMatrix d := by
  have mapGL_coe_eq : ∀ s : SL(2, ℤ),
      ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := fun _ => rfl
  have map_int_mul_eq : ∀ A B : Matrix (Fin 2) (Fin 2) ℤ,
      (A * B).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * B.map (algebraMap ℤ ℝ) := by
    intro A B
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← diagMatInt_map_eq hd, mapGL_coe_eq, mapGL_coe_eq,
    ← map_int_mul_eq, ← map_int_mul_eq, hconj]

/-- The stretched slash `g ∣[k] heckeDiagMatrix d`, which is already a `Γ₁(N)`-cusp form (the
automorphy factor `d ^ (k - 1)` is stripped in `stretch`). -/
def stretchSlash (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k) :
    CuspForm Γ₁(N) k where
  toFun := (⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix d
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    obtain ⟨γ', hγ'0, hconj, h00, h11, -⟩ := exists_cocycle (M := M) hd hdMN (Gamma1_in_Gamma0 N hγ)
    have hγ'1 : γ' ∈ Gamma1 M :=
      mem_Gamma1_of_cocycle (dvd_of_mul_left_dvd hdMN) hγ hγ'0 h00 h11
    rw [← SlashAction.slash_mul, heckeDiagMatrix_mul_eq hd hconj, SlashAction.slash_mul,
      SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ'1)]
  holo' := g.holo'.slash k _
  zero_at_cusps' := by
    have : NeZero M := neZero_of_dvd (dvd_of_mul_left_dvd hdMN)
    intro c hc
    have hcSL : IsCusp c 𝒮ℒ := by
      rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    refine (OnePoint.IsZeroAt.smul_iff (c := c) (f := ⇑g) (k := k) (g := heckeDiagMatrix d)).mp ?_
    refine CuspFormClass.zero_at_cusps g ?_
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
    exact ModularCurve.isCusp_heckeDiagMatrix_smul hd hcSL

/-- The `q ↦ q^d` stretch `τ ↦ g(dτ)` displayed as a slash. -/
theorem stretchSlash_apply (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k)
    (τ : ℍ) : stretchSlash hd hdMN g τ = (d : ℂ) ^ (k - 1) * g (heckeDiagMatrix d • τ) :=
  slash_heckeDiagMatrix_apply k hd _ τ

/-- The degeneracy lift: the normalized stretch `τ ↦ g(dτ)`. -/
def stretch (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k) :
    CuspForm Γ₁(N) k :=
  ((d : ℂ) ^ (k - 1))⁻¹ • stretchSlash hd hdMN g

theorem stretch_apply (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k)
    (τ : ℍ) : stretch hd hdMN g τ = g (heckeDiagMatrix d • τ) := by
  have hpk : ((d : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hd)
  rw [stretch, smul_apply, stretchSlash_apply, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hpk, one_mul]

/-- The lift's `q`-expansion is the `d`-th subsequence, padded with zeros. -/
theorem qCoeff_stretch (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k)
    (n : ℕ) :
    ModularFormClass.qCoeff (⇑(stretch hd hdMN g)) n
      = if d ∣ n then ModularFormClass.qCoeff (⇑g) (n / d) else 0 := by
  have hcoe : (⇑(stretch hd hdMN g) : ℍ → ℂ) = fun τ => g (heckeDiagMatrix d • τ) :=
    funext (stretch_apply hd hdMN g)
  rw [hcoe]
  exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul (CuspForm.cusp_periodic g) g.holo'
    (CuspForm.cusp_bdd g) hd n

/-- The lift carries the level-changed nebentypus. -/
theorem hasNebentypus_stretch (hd : d ≠ 0) (hdMN : d * M ∣ N) (g : CuspForm Γ₁(M) k)
    (ε : DirichletCharacter ℂ M) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus (DirichletCharacter.changeLevel (dvd_of_mul_left_dvd hdMN) ε)
      (stretch hd hdMN g) := by
  have hMN : M ∣ N := dvd_of_mul_left_dvd hdMN
  intro γ hγ τ
  obtain ⟨γ', hγ'0, hconj, h00, h11, h10⟩ := exists_cocycle (M := M) hd hdMN hγ
  have hGL := heckeDiagMatrix_mul_eq hd hconj
  rw [stretch_apply, stretch_apply]

  have hsm : heckeDiagMatrix d • (γ • τ) = γ' • (heckeDiagMatrix d • τ) := by
    change heckeDiagMatrix d • ((Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • τ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) • (heckeDiagMatrix d • τ)
    rw [← mul_smul, hGL, mul_smul]
  rw [hsm, hg γ' hγ'0 (heckeDiagMatrix d • τ)]

  have hunit : IsUnit ((γ 1 1 : ℤ) : ZMod N) := by
    have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have h := γ.det_coe; rwa [Matrix.det_fin_two] at h
    have := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at this
    rw [hc, mul_zero, sub_zero] at this
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)
  have hchar : (DirichletCharacter.changeLevel hMN ε) ((γ 1 1 : ℤ) : ZMod N)
      = ε ((γ' 1 1 : ℤ) : ZMod M) := by
    rw [h11, ← hunit.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd ε hMN,
      hunit.unit_spec, ZMod.cast_intCast hMN]
  rw [hchar]

  have hcoe : ((heckeDiagMatrix d • τ : ℍ) : ℂ) = (d : ℂ) * (τ : ℂ) := coe_heckeDiagMatrix_smul hd τ
  have hfac : ((γ' 1 0 : ℤ) : ℂ) * ((heckeDiagMatrix d • τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)
      = ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) := by
    rw [hcoe, h11, ← h10]
    push_cast
    ring
  rw [hfac]

end Form

end DegeneracyGamma1

theorem exists_degeneracy_gamma1_hasNebentypus
    {k : ℤ} {M N d : ℕ} [NeZero N] (hd : M * d ∣ N) (g : CuspForm (Gamma1 M) k) :
    ∃ G : CuspForm (Gamma1 N) k,
      (∀ τ : UpperHalfPlane, G τ = g (ModularForm.heckeDiagMatrix d • τ)) ∧
      (∀ n : ℕ, ModularFormClass.qCoeff G n =
        if d ∣ n then ModularFormClass.qCoeff g (n / d) else 0) ∧
      ∀ ε : DirichletCharacter ℂ M, CuspForm.HasNebentypus ε g →
        CuspForm.HasNebentypus (DirichletCharacter.changeLevel (dvd_of_mul_right_dvd hd) ε) G := by
  have hdMN : d * M ∣ N := by rwa [mul_comm] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (by simpa using hd))
  exact ⟨DegeneracyGamma1.stretch hd0 hdMN g, DegeneracyGamma1.stretch_apply hd0 hdMN g,
    DegeneracyGamma1.qCoeff_stretch hd0 hdMN g,
    fun ε hε => DegeneracyGamma1.hasNebentypus_stretch hd0 hdMN g ε hε⟩

/-! ## Row D — the coefficient criterion

The pin's `SupportVanishing` block (`P2M/Sol/S_CuspForm_gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero.lean`,
`aa2d8b3`): `f` is invariant under the translations `τ ↦ τ + p⁻¹` because its coefficients vanish off the
`p`-multiples (`apply_vadd_eq`, `slash_transGL_eq`, `slash_transGL_pow_eq`), the low `GL`-model
`lowGL`/`lowForm` turns that into the `Γ₁(N)`-invariance of `f ∣[k] heckeDiagMatrix p`, and D's premise
`CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1`
(`ModularForms/Gamma1Vanishing.lean`) finishes.

The pin's `T_mem_Gamma1`/`periodic_of_slash_T` pair is not repeated (`CuspForm.cusp_periodic` in
`ModularForms/HeckePrelude.lean`), and `mapGL_apply` is the port's
`ModularForm.HeckeRepresentatives.mapGL_apply`. Two deviations, both proof-only: `val_transGL_pow`
drops the pin's `hp : p ≠ 0`, which the pin never uses and which the port cannot keep silent
(`linter.unusedVariables`; the port may not `set_option` it away), and `det_lowGL` is kept although
the pin's own file never consumes it (playbook §3.8: the pin's unreachable mathematics is ported). -/

namespace SupportVanishing

section Criterion

variable {N p : ℕ} {k : ℤ}

section Trans

/-- The translation `τ ↦ τ + p⁻¹` as an upper triangular `GL₂(ℝ)`-matrix. -/
def transGL (p : ℕ) : GL (Fin 2) ℝ := upperTriangularGL 1 ((p : ℝ)⁻¹) 1 (by norm_num)

/-- The stretch `τ ↦ pτ` as an upper triangular `GL₂(ℝ)`-matrix. -/
def lowGL (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℝ := upperTriangularGL 1 0 p (by simpa using hp)

theorem val_transGL (p : ℕ) :
    ((transGL p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (p : ℝ)⁻¹; 0, 1] := rfl

theorem val_lowGL (p : ℕ) (hp : p ≠ 0) :
    ((lowGL p hp : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), 0; 0, (p : ℝ)] := rfl

theorem det_transGL (p : ℕ) : ((transGL p).det : ℝ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_transGL, Matrix.det_fin_two_of]; ring

theorem det_lowGL (p : ℕ) (hp : p ≠ 0) : ((lowGL p hp).det : ℝ) = p := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_lowGL, Matrix.det_fin_two_of]; ring

theorem val_mapGL_eq (g : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![((g 0 0 : ℤ) : ℝ), ((g 0 1 : ℤ) : ℝ); ((g 1 0 : ℤ) : ℝ), ((g 1 1 : ℤ) : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem val_transGL_pow (p : ℕ) (n : ℕ) :
    ((transGL p ^ n : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![(1 : ℝ), (n : ℝ) * (p : ℝ)⁻¹; 0, 1] := by
  induction n with
  | zero =>
    rw [pow_zero]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, val_transGL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

theorem transGL_smul (p : ℕ) (τ : ℍ) : transGL p • τ = ((p : ℝ)⁻¹) +ᵥ τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [det_transGL]; exact one_pos), UpperHalfPlane.coe_vadd]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_transGL]
  ring

theorem slash_transGL_apply (p : ℕ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] transGL p) τ = f (transGL p • τ) := by
  rw [ModularForm.slash_apply]
  have hσ : UpperHalfPlane.σ (transGL p) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, ite_eq_left (by rw [det_transGL]; exact one_pos)]
  rw [hσ, det_transGL]
  simp [UpperHalfPlane.denom, val_transGL]

theorem slash_lowGL_slash_heckeDiagMatrix (hp : p ≠ 0) (f : ℍ → ℂ) :
    (f ∣[k] lowGL p hp) ∣[k] heckeDiagMatrix p = ((p : ℂ) ^ (k - 2)) • f := by
  have hprod : lowGL p hp * heckeDiagMatrix p
      = Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity) := by
    ext i j
    rw [Units.val_mul, val_lowGL, val_heckeDiagMatrix hp]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]
  rw [← SlashAction.slash_mul, hprod]
  funext τ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]
  have hdet : ((Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)).det : ℝ)
      = (p : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [Fintype.card_fin]
  have hdetpos : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  have hσ : UpperHalfPlane.σ (Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, ite_eq_left (by rw [hdet]; exact hdetpos)]
  have hsmul : (Matrix.GeneralLinearGroup.mkOfDetNeZero ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)) • τ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [hdet]; exact hdetpos)]
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, Matrix.smul_apply]
    field_simp
  rw [hσ, hdet, hsmul]
  simp only [ContinuousAlgEquiv.refl_apply]
  have hden : UpperHalfPlane.denom (Matrix.GeneralLinearGroup.mkOfDetNeZero
      ((p : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; positivity)) (τ : ℂ) = p := by
    simp [UpperHalfPlane.denom, Matrix.smul_apply]
  rw [hden]
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [abs_of_pos hdetpos]
  push_cast
  rw [← zpow_natCast, ← zpow_mul, mul_assoc, ← zpow_add₀ hp', mul_comm]
  congr 2
  push_cast
  ring

/-- `f` is invariant under `τ ↦ τ + p⁻¹` when its coefficients vanish off the `p`-multiples
(`q`-expansion comparison). -/
theorem apply_vadd_eq (hp : p ≠ 0) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) (τ : ℍ) :
    f (((p : ℝ)⁻¹) +ᵥ τ) = f τ := by
  have hper : Function.Periodic (⇑f ∘ UpperHalfPlane.ofComplex) 1 := CuspForm.cusp_periodic f
  have hhol : MDiff (⇑f : ℍ → ℂ) := CuspForm.cusp_holo f
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty (⇑f) := CuspForm.cusp_bdd f
  have h1 := UpperHalfPlane.hasSum_qExpansion one_pos hper hhol hbdd τ
  have h2 := UpperHalfPlane.hasSum_qExpansion one_pos hper hhol hbdd (((p : ℝ)⁻¹) +ᵥ τ)

  set ζ : ℂ := Complex.exp (2 * π * Complex.I * (p : ℂ)⁻¹) with hζ
  have hq : Function.Periodic.qParam 1 ((((p : ℝ)⁻¹) +ᵥ τ : ℍ) : ℂ)
      = Function.Periodic.qParam 1 (τ : ℂ) * ζ := by
    rw [UpperHalfPlane.coe_vadd, Function.Periodic.qParam, Function.Periodic.qParam, hζ,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hζp : ζ ^ p = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
    rw [show (p : ℂ) * (2 * π * Complex.I * (p : ℂ)⁻¹) = (1 : ℕ) * (2 * π * Complex.I) by
      field_simp; push_cast; ring]
    exact Complex.exp_nat_mul_two_pi_mul_I 1
  have hterm : (fun m : ℕ => (UpperHalfPlane.qExpansion 1 (⇑f)).coeff m •
        Function.Periodic.qParam 1 ((((p : ℝ)⁻¹) +ᵥ τ : ℍ) : ℂ) ^ m)
      = fun m : ℕ => (UpperHalfPlane.qExpansion 1 (⇑f)).coeff m •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m := by
    funext m
    by_cases hpm : p ∣ m
    · obtain ⟨r, rfl⟩ := hpm
      rw [hq, mul_pow, pow_mul, pow_mul, hζp, one_pow, mul_one]
    · have h0 : (UpperHalfPlane.qExpansion 1 (⇑f)).coeff m = 0 := hf m hpm
      rw [h0, zero_smul, zero_smul]
  rw [hterm] at h2
  exact h2.unique h1

theorem slash_transGL_eq (hp : p ≠ 0) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) :
    (⇑f : ℍ → ℂ) ∣[k] transGL p = ⇑f := by
  funext τ
  rw [slash_transGL_apply, transGL_smul, apply_vadd_eq hp f hf τ]

theorem slash_transGL_pow_eq (hp : p ≠ 0) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) (n : ℕ) :
    (⇑f : ℍ → ℂ) ∣[k] (transGL p ^ n) = ⇑f := by
  induction n with
  | zero => rw [pow_zero, SlashAction.slash_one]
  | succ n ih => rw [pow_succ, SlashAction.slash_mul, ih, slash_transGL_eq hp f hf]

end Trans

section Cocycle

/-- The `Γ₁(N)`-cocycle for the `p`-translation: `x`, `y` clear the first row and column so that
`γ'' ∈ Γ₁(N)` has `γ'' 1 0 = p γ 1 0`. -/
theorem exists_cocycle (hp : p.Prime) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    ∃ (x y : ℕ) (γ'' : SL(2, ℤ)), γ'' ∈ Gamma1 N ∧
      γ'' 0 0 = γ 0 0 - x * γ 1 0 ∧ γ'' 1 0 = p * γ 1 0 ∧ γ'' 1 1 = γ 1 1 - y * γ 1 0 ∧
      (p : ℤ) * γ'' 0 1 = γ 0 1 - x * γ 1 1 - y * (γ 0 0 - x * γ 1 0) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe; rwa [Matrix.det_fin_two] at h

  obtain ⟨x, hx⟩ : ∃ x : ℕ, ¬ (p : ℤ) ∣ γ 0 0 - x * γ 1 0 := by
    by_cases ha : (p : ℤ) ∣ γ 0 0
    · refine ⟨1, ?_⟩
      intro h
      have hc : (p : ℤ) ∣ γ 1 0 := by
        have : (p : ℤ) ∣ γ 0 0 - (γ 0 0 - 1 * γ 1 0) := dvd_sub ha h
        simpa using this
      have : (p : ℤ) ∣ 1 := by
        rw [← hdet]
        exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hc _)
      exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
    · exact ⟨0, by simpa using ha⟩
  set u : ℤ := γ 0 0 - x * γ 1 0 with hu
  set b' : ℤ := γ 0 1 - x * γ 1 1 with hb'
  have hu0 : ((u : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

  set y : ℕ := (((b' : ℤ) : ZMod p) * ((u : ℤ) : ZMod p)⁻¹).val with hy
  have hyc : ((y : ℕ) : ZMod p) = ((b' : ℤ) : ZMod p) * ((u : ℤ) : ZMod p)⁻¹ := by
    rw [hy, ZMod.natCast_zmod_val]
  have hdiv : (p : ℤ) ∣ b' - y * u := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hyc, mul_assoc, inv_mul_cancel₀ hu0, mul_one, sub_self]
  obtain ⟨r, hr⟩ := hdiv
  have hdet'' : Matrix.det !![u, r; (p : ℤ) * γ 1 0, γ 1 1 - y * γ 1 0] = 1 := by
    rw [Matrix.det_fin_two_of]
    have hr' : (p : ℤ) * r = b' - y * u := hr.symm
    linear_combination hdet - γ 1 0 * hr'
  let γ'' : SL(2, ℤ) := ⟨!![u, r; (p : ℤ) * γ 1 0, γ 1 1 - y * γ 1 0], hdet''⟩
  refine ⟨x, y, γ'', ?_, ?_, ?_, ?_, ?_⟩
  · rw [Gamma1_mem] at hγ ⊢
    obtain ⟨ha, he, hc⟩ := hγ
    refine ⟨?_, ?_, ?_⟩
    · show ((u : ℤ) : ZMod N) = 1
      rw [hu]; push_cast; rw [ha, hc]; ring
    · show ((γ 1 1 - y * γ 1 0 : ℤ) : ZMod N) = 1
      push_cast; rw [he, hc]; ring
    · show (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0
      push_cast; rw [hc]; ring
  · rfl
  · rfl
  · rfl
  · show (p : ℤ) * r = _
    rw [← hr]

/-- The `SL₂`-shadow of the cocycle: `lowGL p` times `γ` is the translate/conjugate product. -/
theorem lowGL_mul_eq (hp : p ≠ 0) {γ γ'' : SL(2, ℤ)} {x y : ℕ}
    (h00 : γ'' 0 0 = γ 0 0 - x * γ 1 0) (h10 : γ'' 1 0 = p * γ 1 0) (h11 : γ'' 1 1 = γ 1 1 - y * γ 1 0)
    (h01 : (p : ℤ) * γ'' 0 1 = γ 0 1 - x * γ 1 1 - y * (γ 0 0 - x * γ 1 0)) :
    lowGL p hp * Matrix.SpecialLinearGroup.mapGL ℝ γ
      = transGL p ^ x * Matrix.SpecialLinearGroup.mapGL ℝ γ'' * transGL p ^ y * lowGL p hp := by
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have h00' : ((γ'' 0 0 : ℤ) : ℝ) = γ 0 0 - x * γ 1 0 := by exact_mod_cast h00
  have h10' : ((γ'' 1 0 : ℤ) : ℝ) = p * γ 1 0 := by exact_mod_cast h10
  have h11' : ((γ'' 1 1 : ℤ) : ℝ) = γ 1 1 - y * γ 1 0 := by exact_mod_cast h11
  have h01' : (p : ℝ) * ((γ'' 0 1 : ℤ) : ℝ) = γ 0 1 - x * γ 1 1 - y * (γ 0 0 - x * γ 1 0) := by
    exact_mod_cast h01
  have h01'' : ((γ'' 0 1 : ℤ) : ℝ) = (p : ℝ)⁻¹ * (γ 0 1 - x * γ 1 1 - y * (γ 0 0 - x * γ 1 0)) := by
    rw [← h01', ← mul_assoc, inv_mul_cancel₀ hp', one_mul]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, val_lowGL, val_transGL_pow p,
    val_transGL_pow p, val_mapGL_eq, val_mapGL_eq, h00', h10', h11', h01'']
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> ring

end Cocycle

section Main

variable [NeZero N]

/-- The rational model of `lowGL p`. -/
def lowGLQ (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), 0; 0, (p : ℚ)]
    (by rw [Matrix.det_fin_two_of]; simp; exact_mod_cast hp)

theorem lowGLQ_map (hp : p ≠ 0) : (lowGLQ hp).map (Rat.castHom ℝ) = lowGL p hp := by
  apply Units.ext
  rw [val_lowGL]
  show (lowGLQ hp : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold lowGLQ
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem isCusp_smul_of_rat {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) {g : GL (Fin 2) ℝ}
    (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) : IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨gQ • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

/-- The low model `f ∣[k] lowGL p` of `f`: a `Γ₁(N)`-cusp form whose `heckeDiagMatrix p`-translate is
`p ^ (k - 2) • f`. -/
def lowForm (hp : p.Prime) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) : CuspForm Γ₁(N) k :=
  { toFun := (⇑f : ℍ → ℂ) ∣[k] lowGL p hp.ne_zero
    slash_action_eq' := by
      intro A hA
      obtain ⟨γ, hγ, rfl⟩ := hA
      obtain ⟨x, y, γ'', hγ'', h00, h10, h11, h01⟩ := exists_cocycle (N := N) hp hγ
      rw [← SlashAction.slash_mul, lowGL_mul_eq hp.ne_zero h00 h10 h11 h01, SlashAction.slash_mul,
        SlashAction.slash_mul, SlashAction.slash_mul, slash_transGL_pow_eq hp.ne_zero f hf x,
        SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ''),
        slash_transGL_pow_eq hp.ne_zero f hf y]
    holo' := f.holo'.slash k _
    zero_at_cusps' := by
      intro c hc
      refine OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f ?_)
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
      exact isCusp_smul_of_rat hc (lowGLQ hp.ne_zero) (lowGLQ_map hp.ne_zero) }

theorem coe_lowForm (hp : p.Prime) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) :
    (⇑(lowForm hp f hf) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] lowGL p hp.ne_zero := rfl

/-- The coefficient criterion: a `Γ₁(N)`-cusp form vanishing off the `p`-multiples is zero. -/
theorem main (hp : p.Prime) (hpN : ¬ p ∣ N) (f : CuspForm Γ₁(N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) : f = 0 := by
  set g := lowForm hp f hf with hg
  have hgδ : (⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p = ((p : ℂ) ^ (k - 2)) • (⇑f : ℍ → ℂ) := by
    rw [hg, coe_lowForm, slash_lowGL_slash_heckeDiagMatrix hp.ne_zero]
  have hy : ∀ γ ∈ Γ₁(N), ((⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ
      = (⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p := by
    intro γ hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    rw [hgδ]
    change (((p : ℂ) ^ (k - 2)) • (⇑f : ℍ → ℂ)) ∣[k] γ₀ = _
    have hfix : (⇑f : ℍ → ℂ) ∣[k] γ₀ = ⇑f :=
      SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hγ₀)
    rw [ModularForm.SL_smul_slash, hfix]
  have hg0 : g = 0 := CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 hp hpN k g hy
  have hf0 : ((p : ℂ) ^ (k - 2)) • (⇑f : ℍ → ℂ) = 0 := by
    rw [← hgδ, hg0]
    change ((0 : ℍ → ℂ)) ∣[k] heckeDiagMatrix p = 0
    exact SlashAction.zero_slash k _
  have hpk : ((p : ℂ) ^ (k - 2)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hf0' : (⇑f : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ℍ → ℂ => ((p : ℂ) ^ (k - 2))⁻¹ • F) hf0
    simpa [smul_smul, inv_mul_cancel₀ hpk] using this
  exact DFunLike.ext f 0 fun τ => congrFun hf0' τ

end Main

end Criterion

end SupportVanishing

theorem gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
    {N p : ℕ} [NeZero N] (k : ℤ) (hp : p.Prime) (hpN : ¬ p ∣ N) (f : CuspForm (Gamma1 N) k)
    (hf : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = 0) : f = 0 :=
  SupportVanishing.main hp hpN f hf

end CuspForm
