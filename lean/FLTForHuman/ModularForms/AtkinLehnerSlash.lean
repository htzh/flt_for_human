/-
  The Atkin–Lehner slash: the `alSlash` calculus on `Γ₀ M`.

  ## What the module is

  `ModularForms/Defs/AtkinLehnerDatum.lean` supplies the datum and `alSlash W k f = f ∣[k] W.alGL`.
  This module is the calculus the two `CuspForm` headlines over it consume:

  * a datum exists whenever `q ∣ M` and `q² ∤ M` (`nonempty_of_prime_of_dvd_of_not_sq_dvd'`, the
    Bézout step), and none exists for `M = 4`, `q = 2` (`isEmpty_four_two`);
  * the slash of a `Γ₀ M`-invariant function is again `Γ₀ M`-invariant (`exists_cocycle_al` is
    the `1`-cocycle that makes it well defined, `alSlash_slash` the invariance);
  * `alSlash` preserves holomorphy (`alSlash_mdiff`), boundedness (`alSlash_isBoundedAt`) and
    vanishing (`alSlash_isZeroAt`) at the cusps of `Γ₀ M`, and is an involution up to the
    scalar `(q : ℂ) ^ (k - 2)` (`alSlash_alSlash`, `alSlash_alSlash_two`).

  The pin's two premise files, `S_ModularForm_isZeroAt_alSlash.lean` (307 lines) and
  `S_ModularForm_mdifferentiable_alSlash.lean` (306 lines), are the *same* development: the
  same 23 declarations, differing only in which `alSlash` lemma their final `solution` states.
  Porting it once gives both headlines; the two root wrappers below are those two `solution`s,
  at the statement of the matching `Theorems/` wrapper.

  The pin keeps `mat_mul_normalizes`, `denom_scalarGL` and `num_scalarGL` `private`; so does this
  module. The six `scalarGL`-block helpers (`map_int_mul`, `val_det_scalarGL`,
  `det_scalarGL_pos`, `scalarGL_smul`, `slash_scalarGL`, `alGL_mul_alGL`) are public here
  because the twin headline file (`WeightOne/PrimitiveQCoeffNorm.lean`, A) states the same six
  publicly and imports them from here rather than repeating them — each carries a `-- pin:`
  comment naming its row in that file.

  FLT provenance, pinned `aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_isZeroAt_alSlash.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_mdifferentiable_alSlash.lean

  spec-pin: P2M/Sol/S_ModularForm_isZeroAt_alSlash.lean
  spec-pin: P2M/Sol/S_ModularForm_mdifferentiable_alSlash.lean
  spec-pin: Theorems/Thm_ModularForm_isZeroAt_alSlash.lean
  spec-pin: Theorems/Thm_ModularForm_mdifferentiable_alSlash.lean
-/
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.BoundedAtCusp
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.SlashActions
import FLTForHuman.ModularForms.Defs.AtkinLehnerDatum

set_option autoImplicit false

noncomputable section

open Matrix UpperHalfPlane CongruenceSubgroup OnePoint
open scoped MatrixGroups ModularForm Manifold

namespace ModularForm

namespace AtkinLehnerDatum

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

private theorem _root_.ModularForm.AtkinLehnerDatum.mat_mul_normalizes (α β c δ : ℤ)
    (hdet : α * δ - β * ((q : ℤ) * (W.R : ℤ) * c) = 1) :
    ∃ p r s t : ℤ, p * t - r * ((q : ℤ) * (W.R : ℤ) * s) = 1 ∧
      W.mat * !![α, β; (q : ℤ) * (W.R : ℤ) * c, δ]
        = !![p, r; (q : ℤ) * (W.R : ℤ) * s, t] * W.mat := by

  refine ⟨(q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ)) * c
        - (W.R : ℤ) * ((q : ℤ) * W.a * β + W.b * δ),
      -(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (q : ℤ) * W.a ^ 2 * β + W.a * W.b * δ,
      α + (q : ℤ) * c - (W.R : ℤ) * β - δ,
      -((W.R : ℤ) * W.b) * (α + (q : ℤ) * c) + W.a * ((q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ),
      ?_, ?_⟩
  ·
    linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b) ^ 2 * hdet
      + ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout
  ·
    rw [mat, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j
    · show (q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ) * c)
        = ((q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((q : ℤ) * W.a * β + W.b * δ)) * ((q : ℤ) * W.a)
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (q : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * ((q : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * W.b * c * (q : ℤ) + W.a * α * (q : ℤ))) * W.bezout
    · show (q : ℤ) * W.a * β + W.b * δ
        = ((q : ℤ) * W.a * α + W.b * ((q : ℤ) * (W.R : ℤ)) * c
            - (W.R : ℤ) * ((q : ℤ) * W.a * β + W.b * δ)) * W.b
          + (-(W.a * α * W.b) - W.b ^ 2 * (W.R : ℤ) * c + (q : ℤ) * W.a ^ 2 * β
              + W.a * W.b * δ) * (q : ℤ)
      linear_combination (-(W.a * β * (q : ℤ) + W.b * δ)) * W.bezout
    · show (q : ℤ) * (W.R : ℤ) * α + (q : ℤ) * ((q : ℤ) * (W.R : ℤ) * c)
        = (q : ℤ) * (W.R : ℤ) * (α + (q : ℤ) * c - (W.R : ℤ) * β - δ) * ((q : ℤ) * W.a)
          + (-((W.R : ℤ) * W.b) * (α + (q : ℤ) * c)
              + W.a * ((q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ)) * ((q : ℤ) * (W.R : ℤ))
      linear_combination
        (-((W.R : ℤ) * α * (q : ℤ) + (W.R : ℤ) * c * (q : ℤ) ^ 2)) * W.bezout
    · show (q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ
        = (q : ℤ) * (W.R : ℤ) * (α + (q : ℤ) * c - (W.R : ℤ) * β - δ) * W.b
          + (-((W.R : ℤ) * W.b) * (α + (q : ℤ) * c)
              + W.a * ((q : ℤ) * (W.R : ℤ) * β + (q : ℤ) * δ)) * (q : ℤ)
      linear_combination (-((W.R : ℤ) * β * (q : ℤ) + δ * (q : ℤ))) * W.bezout


theorem nonempty_of_prime_of_dvd_of_not_sq_dvd' (hq : q.Prime) (hqM : q ∣ M)
    (hsq : ¬ q ^ 2 ∣ M) : Nonempty (AtkinLehnerDatum M q) := by
  obtain ⟨R, hR⟩ := hqM

  have hqR : ¬ q ∣ R := by
    rintro ⟨t, rfl⟩
    exact hsq ⟨t, by rw [hR]; ring⟩

  have hqR' : ¬ (q : ℤ) ∣ (R : ℤ) := by exact_mod_cast hqR
  have hcop : IsCoprime (q : ℤ) (R : ℤ) :=
    (Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd.mpr hqR'
  obtain ⟨u, v, huv⟩ := hcop
  exact ⟨⟨R, hR, u, -v, by linear_combination huv⟩⟩

theorem isEmpty_four_two : IsEmpty (AtkinLehnerDatum 4 2) := by
  constructor
  rintro ⟨R, hM, a, b, hbez⟩

  have hR : R = 2 := by omega
  subst hR

  omega

end AtkinLehnerDatum


variable {M q : ℕ} (W : AtkinLehnerDatum M q)

lemma isCusp_smul_of_rat' {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) {g : GL (Fin 2) ℝ}
    (gQ : GL (Fin 2) ℚ) (hg : gQ.map (Rat.castHom ℝ) = g) : IsCusp (g • c) 𝒮ℒ := by
  subst hg
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  refine ⟨gQ • c₀, ?_⟩
  rw [← Rat.coe_castHom, OnePoint.map_smul]

lemma isCusp_alGL_smul [NeZero M] {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsCusp (W.alGL • c) ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact isCusp_smul_of_rat' hc W.alGLQ W.alGLQ_map_castHom

private lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

-- pin: map_int_mul (P2M/Sol/S_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd.lean:36)
lemma map_int_mul (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

lemma exists_cocycle_al [NeZero M] {g : SL(2, ℤ)} (hg : g ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 M ∧
      W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g
        = Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL := by

  have hdetG : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  have hMc : (M : ℤ) ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := Gamma0_mem.mp hg
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  set α : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with hα
  set β : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hβ
  set γlo : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hγlo
  set δen : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hδen
  obtain ⟨c, hc⟩ := hMc

  have hgmat : (g : Matrix (Fin 2) (Fin 2) ℤ) = !![α, β; (q : ℤ) * (W.R : ℤ) * c, δen] := by
    rw [← W.hM_int, ← hc, hα, hβ, hγlo, hδen]
    exact Matrix.eta_fin_two _

  have hdet' : α * δen - β * ((q : ℤ) * (W.R : ℤ) * c) = 1 := by
    rw [← W.hM_int, ← hc]; linear_combination hdetG
  obtain ⟨p, r, s, t, hdet1, hmat⟩ := W.mat_mul_normalizes α β c δen hdet'

  have hdetδ : Matrix.det !![p, r; (q : ℤ) * (W.R : ℤ) * s, t] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination hdet1
  set δ : SL(2, ℤ) := ⟨!![p, r; (q : ℤ) * (W.R : ℤ) * s, t], hdetδ⟩ with hδ
  have hδcoe : (δ : Matrix (Fin 2) (Fin 2) ℤ)
      = !![p, r; (q : ℤ) * (W.R : ℤ) * s, t] := rfl
  refine ⟨δ, ?_, ?_⟩
  ·
    rw [Gamma0_mem]
    show ((((q : ℤ) * (W.R : ℤ) * s : ℤ)) : ZMod M) = 0
    rw [← W.hM_int]
    push_cast
    simp
  ·
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = ((Matrix.SpecialLinearGroup.mapGL ℝ δ : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) * (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
    rw [AtkinLehnerDatum.alGL_coe, mapGL_coe_eq, mapGL_coe_eq, hδcoe, ← map_int_mul,
      ← map_int_mul]
    congr 1
    rw [hgmat]
    exact hmat

theorem alSlash_slash {k : ℤ} [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (alSlash W k f) ∣[k] γ = alSlash W k f := by
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨δ, hδ, hcocycle⟩ := exists_cocycle_al W hg
  calc (f ∣[k] W.alGL) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ g)
      = f ∣[k] (W.alGL * Matrix.SpecialLinearGroup.mapGL ℝ g) := by
        rw [SlashAction.slash_mul]
    _ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ δ * W.alGL) := by rw [hcocycle]
    _ = (f ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ δ) ∣[k] W.alGL := by
        rw [SlashAction.slash_mul]
    _ = f ∣[k] W.alGL := by
        rw [hf (Matrix.SpecialLinearGroup.mapGL ℝ δ) (Subgroup.mem_map.mpr ⟨δ, hδ, rfl⟩)]

lemma alSlash_mdiff {k : ℤ} [NeZero M] {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (alSlash W k f) :=
  hf.slash k (W.alGL)

lemma alSlash_isBoundedAt {k : ℤ} [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsBoundedAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsBoundedAt c (alSlash W k f) k :=
  IsBoundedAt.smul_iff.mp (hf _ (isCusp_alGL_smul W hc))

lemma alSlash_isZeroAt {k : ℤ} [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ c' : OnePoint ℝ,
      IsCusp c' ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) →
      IsZeroAt c' f k)
    {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    IsZeroAt c (alSlash W k f) k :=
  IsZeroAt.smul_iff.mp (hf _ (isCusp_alGL_smul W hc))

variable (q) in

def scalarGL (hq : 0 < q) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, (q : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    simpa using mul_ne_zero hq' hq')

@[scoped simp] lemma scalarGL_coe (hq : 0 < q) :
    (scalarGL q hq : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, (q : ℝ)] := rfl

-- pin: val_det_scalarGL (P2M/Sol/S_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd.lean:919)
lemma val_det_scalarGL (hq : 0 < q) : ((scalarGL q hq).det : ℝ) = (q : ℝ) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_fin_two_of]
  ring

private lemma denom_scalarGL (hq : 0 < q) (z : ℂ) : denom (scalarGL q hq) z = (q : ℝ) := by
  simp [UpperHalfPlane.denom, scalarGL_coe]

private lemma num_scalarGL (hq : 0 < q) (z : ℂ) : num (scalarGL q hq) z = (q : ℝ) * z := by
  simp [UpperHalfPlane.num, scalarGL_coe]

-- pin: det_scalarGL_pos (P2M/Sol/S_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd.lean:923)
lemma det_scalarGL_pos (hq : 0 < q) : 0 < ((scalarGL q hq).det : ℝ) := by
  rw [val_det_scalarGL]
  have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  positivity

-- pin: scalarGL_smul (P2M/Sol/S_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd.lean:928)
lemma scalarGL_smul (hq : 0 < q) (τ : ℍ) : scalarGL q hq • τ = τ := by
  have hqC : ((q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast hq.ne' : ((q : ℝ)) ≠ 0)
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_scalarGL_pos hq), num_scalarGL, denom_scalarGL,
    mul_comm, mul_div_assoc, div_self hqC, mul_one]

-- pin: slash_scalarGL (P2M/Sol/S_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd.lean:938)
lemma slash_scalarGL (k : ℤ) (hq : 0 < q) (f : ℍ → ℂ) :
    f ∣[k] scalarGL q hq = ((q : ℂ) ^ (k - 2)) • f := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  ext τ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]
  have hσ : σ (scalarGL q hq) (f (scalarGL q hq • τ)) = f (scalarGL q hq • τ) := by
    rw [UpperHalfPlane.σ, ite_eq_left (det_scalarGL_pos hq)]
    rfl
  rw [hσ, scalarGL_smul, val_det_scalarGL, denom_scalarGL,
    abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)]

  have h1 : (((q : ℝ) ^ 2 : ℝ) : ℂ) = (q : ℂ) ^ (2 : ℕ) := by push_cast; ring
  have h2 : (((q : ℝ) : ℝ) : ℂ) = (q : ℂ) := by push_cast; ring
  rw [h1, h2, ← _root_.zpow_natCast ((q : ℂ)) 2, ← _root_.zpow_mul, mul_assoc, ← zpow_add₀ hqC]
  rw [show (2 : ℕ) * (k - 1) + -k = k - 2 by push_cast; ring]
  ring

-- pin: alGL_mul_alGL (P2M/Sol/S_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd.lean:956)
lemma alGL_mul_alGL [NeZero M] :
    W.alGL * W.alGL = scalarGL q W.q_pos * Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (W.alGL : Matrix (Fin 2) (Fin 2) ℝ) * (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
      = (scalarGL q W.q_pos : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)
  rw [AtkinLehnerDatum.alGL_coe, scalarGL_coe, mapGL_coe_eq, AtkinLehnerDatum.sqUnitSL_coe, ← map_int_mul, W.mat_sq]

  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.natCast_apply]

theorem alSlash_alSlash (k : ℤ) [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    alSlash W k (alSlash W k f) = ((q : ℂ) ^ (k - 2)) • f := by

  have hfu : f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) = f :=
    hf _ (Subgroup.mem_map.mpr ⟨W.sqUnitSL, W.sqUnitSL_mem, rfl⟩)
  calc alSlash W k (alSlash W k f)
      = f ∣[k] (W.alGL * W.alGL) := by
        rw [alSlash, alSlash, SlashAction.slash_mul]
    _ = (f ∣[k] scalarGL q W.q_pos) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) := by
        rw [alGL_mul_alGL, SlashAction.slash_mul]
    _ = (((q : ℂ) ^ (k - 2)) • f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL) := by
        rw [slash_scalarGL]
    _ = ((q : ℂ) ^ (k - 2)) • (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ W.sqUnitSL)) := by
        rw [ModularForm.smul_slash]
        congr 1
        rw [UpperHalfPlane.σ, ite_eq_left]
        · rfl
        · simp
    _ = ((q : ℂ) ^ (k - 2)) • f := by rw [hfu]

theorem alSlash_alSlash_two [NeZero M] {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[(2 : ℤ)] γ = f) :
    alSlash W 2 (alSlash W 2 f) = f := by
  rw [alSlash_alSlash W 2 hf]
  norm_num

end ModularForm

/-! ## The two headlines -/

/-- `alSlash` of a form vanishing at the cusps of `Γ₀ M` vanishes at the cusps of `Γ₀ M`. -/
theorem ModularForm.isZeroAt_alSlash {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ c' : OnePoint ℝ, IsCusp c' (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) → OnePoint.IsZeroAt c' f k)
    {c : OnePoint ℝ} (hc : IsCusp c (CongruenceSubgroup.Gamma0 M : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (ModularForm.alSlash W k f) k :=
  ModularForm.alSlash_isZeroAt W hf hc

/-- `alSlash` of a holomorphic function is holomorphic. -/
theorem ModularForm.mdifferentiable_alSlash {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.alSlash W k f) :=
  ModularForm.alSlash_mdiff W hf

end
