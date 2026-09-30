/-
  The bridge from the analytic `τ`-model to the torsion/level data.

  `base/018-congruence-subgroups-and-invariance.md` computes the congruence
  subgroups `Γ₀(N)`, `Γ₁(N)`, `Γ(N)` from the **algebraic** action of an
  integer matrix on the `N`-torsion of an elliptic curve (the FLT
  `LevelPData.relabel` convention).  `SL(2, ℤ)` is, however, classically
  introduced through its Möbius action on `ℍ`, and the FLT development never
  glues the two pictures.  This module checks the glue in the analytic model,
  with mathlib only:

  * `lat τ = ℤ + ℤτ` is the period lattice of `E_τ = ℂ / lat τ`;
  * the canonical full `N`-level structure is the pair `(1/N, τ/N)`;
  * the marking change `E_τ → E_{γτ}`, `z ↦ z / (cτ + d)`, carries that pair to
    `(a - c·γτ)/N` and `(d·γτ - b)/N`, whose label matrix is
    `torsionMatrix γ = !![a, -b; -c, d] = D γ D` with `D = !![1,0;0,-1]`;
  * `torsionMatrix γ` has determinant `1` and satisfies the same three
    stabiliser conditions (`c ≡ 0`; `a ≡ d ≡ 1, c ≡ 0`; `≡ I`) as `γ`, so the
    analytic stabilisers are the congruence subgroups.

  Nothing here imports FLT; it is our own module, cited from `base/018` §1.5.
  It lives in `Reserve` because nothing in `FLTForHuman` uses it: it is a
  verification of the note's reasoning, not part of the critical-path port.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Span.Basic

set_option autoImplicit false

noncomputable section

open Matrix UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve.TauBridge

/-! ## The period lattice `ℤ + ℤτ` -/

/-- The period lattice `ℤ + ℤτ ⊆ ℂ` of the torus `E_τ = ℂ / lat τ`. -/
def lat (τ : ℂ) : Submodule ℤ ℂ := Submodule.span ℤ ({1, τ} : Set ℂ)

theorem mem_lat {τ z : ℂ} :
    z ∈ lat τ ↔ ∃ m n : ℤ, (m : ℂ) + (n : ℂ) * τ = z := by
  rw [lat, Submodule.mem_span_pair]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨m, n, by simpa using h⟩
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp⟩

/-- **The marking change preserves the lattice.**  For `γ = !![a,b;c,d] ∈ SL(2, ℤ)`
the pair `(cτ + d, aτ + b)` is another `ℤ`-basis of `ℤ + ℤτ`; the change of
basis matrix is `!![d,b;c,a]`, of determinant `1`. -/
theorem lat_sl2_span (γ : SL(2, ℤ)) (τ : ℂ) :
    Submodule.span ℤ
        ({((γ.val 1 0 : ℤ) : ℂ) * τ + ((γ.val 1 1 : ℤ) : ℂ),
          ((γ.val 0 0 : ℤ) : ℂ) * τ + ((γ.val 0 1 : ℤ) : ℂ)} : Set ℂ) = lat τ := by
  set a : ℤ := γ.val 0 0 with ha
  set b : ℤ := γ.val 0 1 with hb
  set c : ℤ := γ.val 1 0 with hc
  set d : ℤ := γ.val 1 1 with hd
  have hZ : a * d - b * c = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    rw [← ha, ← hb, ← hc, ← hd] at h
    exact h
  have hdet : (a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ) = 1 := by exact_mod_cast hZ
  have hg1 : (c : ℂ) * τ + (d : ℂ) ∈ lat τ := mem_lat.mpr ⟨d, c, by ring⟩
  have hg2 : (a : ℂ) * τ + (b : ℂ) ∈ lat τ := mem_lat.mpr ⟨b, a, by ring⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro w hw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · rw [hw]; exact hg1
    · rw [hw]; exact hg2
  · rw [lat, Submodule.span_le]
    intro w hw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with hw | hw
    · rw [hw]
      refine Submodule.mem_span_pair.mpr ⟨a, -c, ?_⟩
      linear_combination (norm := ring_nf) hdet
    · rw [hw]
      refine Submodule.mem_span_pair.mpr ⟨-b, d, ?_⟩
      linear_combination (norm := ring_nf) (τ * hdet)

/-! ## The induced action on the canonical `N`-torsion basis -/

/-- The relabelling matrix induced by the marking change: `D γ D` with
`D = !![1,0;0,-1]`, i.e. `γ` with the signs of its off-diagonal entries flipped.
It is the matrix that acts on the canonical torsion basis `(1/N, τ/N)` when `τ`
moves to `γ • τ`. -/
def torsionMatrix (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ.val 0 0, -γ.val 0 1; -γ.val 1 0, γ.val 1 1]

theorem torsionMatrix_eq_conj (γ : SL(2, ℤ)) :
    torsionMatrix γ = !![1, 0; 0, -1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [torsionMatrix, Matrix.mul_apply, Matrix.vecMul_eq_sum, Fin.sum_univ_two]

/-- The analytic relabelling matrix is still integral of determinant one, hence
lies in `SL(2, ℤ)` (before reduction). -/
theorem torsionMatrix_det (γ : SL(2, ℤ)) : (torsionMatrix γ).det = 1 := by
  rw [torsionMatrix_eq_conj, Matrix.det_mul, Matrix.det_mul, Matrix.det_fin_two, Matrix.det_fin_two]
  have hZ : (γ.val 0 0 : ℤ) * (γ.val 1 1 : ℤ) - (γ.val 0 1 : ℤ) * (γ.val 1 0 : ℤ) = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  rw [hZ]
  norm_num

/-! ## The Möbius formula with integer entries

`denomC` is the denominator `cτ + d` written purely with `ℤ`-coercions, so that
the analytic identities below are stated with the same arithmetic as
`torsionMatrix`. -/

/-- `cτ + d`, with the entries of `γ` read as integers. -/
def denomC (γ : SL(2, ℤ)) (τ : ℂ) : ℂ :=
  ((γ.val 1 0 : ℤ) : ℂ) * τ + ((γ.val 1 1 : ℤ) : ℂ)

theorem denomC_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) : denomC γ (τ : ℂ) ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ γ) τ
  simpa [denomC, UpperHalfPlane.denom, Matrix.SpecialLinearGroup.mapGL] using h

/-- The `ℤ → ℝ → ℂ` coercion is the `ℤ → ℂ` one; this is what lets `denomC`
match mathlib's `algebraMap`-based Möbius formula. -/
private theorem algebraMap_intCast_complex (n : ℤ) :
    ((algebraMap ℤ ℝ n : ℝ) : ℂ) = (n : ℂ) := by simp

/-- Bridge from `denomC` to mathlib's `UpperHalfPlane.denom` on the `SL(2, ℤ)`
coercion. -/
private theorem denomC_eq_denom (γ : SL(2, ℤ)) (τ : ℂ) : denomC γ τ = denom γ τ := by
  rw [denomC]
  simp only [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, Matrix.map_apply, RingHom.mapMatrix_apply,
    Int.coe_castRingHom]
  push_cast
  ring

/- Mathlib's Möbius formula, rewritten with the integer entries and stated at
the pin's `coe_smul_eq` (H2 reconciliation: `denom`, `γ 0 0`). -/
section CoeSmul

variable (τ : ℍ)

/-- The pin's `coe_smul_eq`. -/
theorem coe_smul_eq (γ : SL(2, ℤ)) :
    ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) / denom γ τ := by
  rw [← denomC_eq_denom]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [denomC, algebraMap_intCast_complex]

end CoeSmul

/-- Multiplication by a complex scalar as a `ℤ`-linear endomorphism of `ℂ`. -/
def mulBy (s : ℂ) : ℂ →ₗ[ℤ] ℂ where
  toFun z := s * z
  map_add' x y := by ring
  map_smul' n z := by simp only [zsmul_eq_mul, RingHom.id_apply]; ring

/-- **The homothety.**  `(cτ + d)·lat(γτ) = lat τ`: the marking change sends the
torus `E_τ` to the homothetic torus `E_{γτ}`, so `γτ` is the modulus of the
changed marking. -/
theorem lat_smul_moebius (γ : SL(2, ℤ)) (τ : ℍ) :
    Submodule.map (mulBy (denomC γ (τ : ℂ))) (lat ((γ • τ : ℍ) : ℂ)) = lat (τ : ℂ) := by
  have hs : mulBy (denomC γ (τ : ℂ)) 1 = ((γ.val 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ.val 1 1 : ℤ) : ℂ) := by
    show denomC γ (τ : ℂ) * 1 = _
    rw [mul_one, denomC]
  have hst : mulBy (denomC γ (τ : ℂ)) ((γ • τ : ℍ) : ℂ)
      = ((γ.val 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ.val 0 1 : ℤ) : ℂ) := by
    show denomC γ (τ : ℂ) * ((γ • τ : ℍ) : ℂ) = _
    rw [coe_smul_eq, ← denomC_eq_denom, mul_div_cancel₀ _ (denomC_ne_zero γ τ)]
  rw [lat, Submodule.map_span, Set.image_insert_eq, Set.image_singleton, hs, hst]
  exact lat_sl2_span γ (τ : ℂ)

/-- The determinant identity over `ℂ`: `a·d - b·c = 1`. -/
theorem detC (γ : SL(2, ℤ)) :
    ((γ.val 0 0 : ℤ) : ℂ) * ((γ.val 1 1 : ℤ) : ℂ)
      - ((γ.val 0 1 : ℤ) : ℂ) * ((γ.val 1 0 : ℤ) : ℂ) = 1 := by
  have h : (γ.val 0 0 : ℤ) * (γ.val 1 1 : ℤ) - (γ.val 0 1 : ℤ) * (γ.val 1 0 : ℤ) = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  exact_mod_cast h

/-- The two pure-algebra identities behind the marking change, with no matrix
structure: if `ad - bc = 1` then `1/(cτ+d) = a - c·(aτ+b)/(cτ+d)` and
`τ/(cτ+d) = d·(aτ+b)/(cτ+d) - b`. -/
private theorem inv_denom_alg {a b c d τ : ℂ} (h : a * d - b * c = 1) (hd : c * τ + d ≠ 0) :
    1 / (c * τ + d) = a - c * ((a * τ + b) / (c * τ + d)) := by
  rw [div_eq_iff hd, sub_mul, mul_assoc, div_mul_cancel₀ _ hd]
  rw [show a * (c * τ + d) - c * (a * τ + b) = a * d - b * c from by ring, h]

private theorem tau_div_denom_alg {a b c d τ : ℂ} (h : a * d - b * c = 1)
    (hd : c * τ + d ≠ 0) :
    τ / (c * τ + d) = d * ((a * τ + b) / (c * τ + d)) - b := by
  rw [div_eq_iff hd, sub_mul, mul_assoc, div_mul_cancel₀ _ hd]
  rw [show d * (a * τ + b) - b * (c * τ + d) = (a * d - b * c) * τ from by ring, h]
  ring

/-- `1/(cτ + d) = a - c·(γτ)`. -/
theorem inv_denom_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    (1 : ℂ) / denomC γ (τ : ℂ)
      = ((γ.val 0 0 : ℤ) : ℂ) - ((γ.val 1 0 : ℤ) : ℂ) * ((γ • τ : ℍ) : ℂ) := by
  rw [coe_smul_eq, ← denomC_eq_denom]
  simpa only [denomC] using
    inv_denom_alg (a := ((γ.val 0 0 : ℤ) : ℂ)) (b := ((γ.val 0 1 : ℤ) : ℂ))
      (c := ((γ.val 1 0 : ℤ) : ℂ)) (d := ((γ.val 1 1 : ℤ) : ℂ)) (τ := (τ : ℂ))
      (detC γ) (denomC_ne_zero γ τ)

/-- `τ/(cτ + d) = d·(γτ) - b`. -/
theorem tau_div_denom_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    (τ : ℂ) / denomC γ (τ : ℂ)
      = ((γ.val 1 1 : ℤ) : ℂ) * ((γ • τ : ℍ) : ℂ) - ((γ.val 0 1 : ℤ) : ℂ) := by
  rw [coe_smul_eq, ← denomC_eq_denom]
  simpa only [denomC] using
    tau_div_denom_alg (a := ((γ.val 0 0 : ℤ) : ℂ)) (b := ((γ.val 0 1 : ℤ) : ℂ))
      (c := ((γ.val 1 0 : ℤ) : ℂ)) (d := ((γ.val 1 1 : ℤ) : ℂ)) (τ := (τ : ℂ))
      (detC γ) (denomC_ne_zero γ τ)

/-! ## The induced action on the canonical `N`-torsion basis -/

/-- The image of the first canonical `N`-torsion generator `1/N` under the
marking change `z ↦ z/(cτ + d)` is `(a - c·γτ)/N`, i.e. it has coordinates
`(a, -c)` in the canonical basis `(1/N, γτ/N)` of `E_{γτ}[N]`. -/
theorem image_P_eq (N : ℕ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (1 : ℂ) / ((N : ℂ) * denomC γ (τ : ℂ))
      = (((γ.val 0 0 : ℤ) : ℂ) - ((γ.val 1 0 : ℤ) : ℂ) * ((γ • τ : ℍ) : ℂ)) / (N : ℂ) := by
  rw [mul_comm (N : ℂ), ← div_div, inv_denom_eq]

/-- The image of the second canonical `N`-torsion generator `τ/N` under the
marking change is `(d·γτ - b)/N`, i.e. it has coordinates `(-b, d)`. -/
theorem image_Q_eq (N : ℕ) (γ : SL(2, ℤ)) (τ : ℍ) :
    (τ : ℂ) / ((N : ℂ) * denomC γ (τ : ℂ))
      = (((γ.val 1 1 : ℤ) : ℂ) * ((γ • τ : ℍ) : ℂ) - ((γ.val 0 1 : ℤ) : ℂ)) / (N : ℂ) := by
  rw [mul_comm (N : ℂ), ← div_div, tau_div_denom_eq]

/-! ## The three congruence subgroups

The point of the module: the relabelling matrix `torsionMatrix γ` (not `γ`
itself) is what the analytic marking change induces on the torsion labels, but
its three stabiliser conditions are the same as those of `γ`. -/

theorem gamma0_iff_torsionMatrix (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma0 N ↔ ((torsionMatrix γ 1 0 : ℤ) : ZMod N) = 0 := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [torsionMatrix]

theorem gamma1_iff_torsionMatrix (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma1 N ↔
      ((torsionMatrix γ 0 0 : ℤ) : ZMod N) = 1
        ∧ ((torsionMatrix γ 1 1 : ℤ) : ZMod N) = 1
        ∧ ((torsionMatrix γ 1 0 : ℤ) : ZMod N) = 0 := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [torsionMatrix]

theorem Gamma_iff_torsionMatrix (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma N ↔
      ((torsionMatrix γ 0 0 : ℤ) : ZMod N) = 1
        ∧ ((torsionMatrix γ 0 1 : ℤ) : ZMod N) = 0
        ∧ ((torsionMatrix γ 1 0 : ℤ) : ZMod N) = 0
        ∧ ((torsionMatrix γ 1 1 : ℤ) : ZMod N) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [torsionMatrix]

end ModularCurve.TauBridge
