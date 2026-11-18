/-
  The Hecke representatives on `ℙ¹(𝔽_p)`: the matrices, the `SL₂(ℤ)` action and
  the two reindexing workhorses for `U_p`/`T_p` slash-invariance.

  This is the shared block FLT writes *publicly* in
  `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean:82–455` (under
  `CuspForm.Gamma1Hecke`) and then re-inlines into every `S_` file of the
  slash-invariance layer. The port has no `Gamma1` yet, so the block gets its own
  definition module — the deliberate placement divergence from the pin, recorded
  here as the `TS` module records its own. The declarations are the `S_`-file
  copies (`S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean:25–312` and
  `…_div.lean`), which are the exact statements the Tier-1 workhorses consume:

  - `det_eq` and the four `_mul_of_eq` lemmas: multiplying a Hecke matrix by
    `mapGL ℝ g` stays in the coset system. **The equation conjunct is kept.** The
    port's old private copy in `PhiGenDescends.lean` had dropped the
    `g' 1 0 = …` conjuncts; the Γ₀ invariance proofs need
    `g' 1 0 = p * g 1 0` (resp. `= g 1 0`, `= e`) to show `g' ∈ Γ₀(N)`. H2 promoted
    the pin's **three-conjunct** statements (the phase-D `_11` refinements) to the
    public pin names, so `heckeMatrix_mul_of_dvd` consumes that form directly and
    no two-conjunct copy is kept.
  - `heckeRep_mul`: **SET-2 (PORTING-Level) restores the pin's public Tier-2
    statement** (`Def_CuspForm_Gamma1HeckeOperators.lean:281–285`): the
    hypothesis is `g ∈ Γ₀(N)` and the result additionally tracks the witness's
    `g' 1 1` entry and the `wt`-equation. It is declared under the pin's
    `Gamma1Hecke` namespace segment so the statement checker's dotted-name
    fallback verifies it against that public block rather than the Γ₀ `S_` copy
    (which shares the last name); the four `_mul_of_eq` lemmas supply the proof.
  - the `ZMod p` reindexing (`sum_range_eq_sum_zmod`, `heckeU_eq_sum_zmod`), the
    affine permutation `affinePerm` with the cocycle `heckeMatrix_mul_of_dvd`, and
    the workhorse `heckeU_slash_mapGL`;
  - the `OnePoint (ZMod p)` side (`heckeRep`, `redMatrix`, `heckeRep_mul`) and
    `heckeT_slash_mapGL`, together with `heckeT_eq_sum_onePoint` (the range sum
    packaged as a `Fintype.sum_option`; it has no pin wrapper of its own and
    lives in the same `S_` block).

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean:82–455` (public home) and
  `P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0.lean` /
  `P2M/Sol/S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div.lean` (the Γ₀
  copies). Statements verbatim from the `S_` files; proofs adapted only for
  mathlib `v4.34.0` (`if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`, which are
  proof-only and leave the statements unchanged).
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.Level.Diamond

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane

open ModularForm.Level

open scoped MatrixGroups ModularForm OnePoint

namespace ModularForm.HeckeRepresentatives

@[simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ℕ) (e : ℤ)
    (he : g 0 1 + j * g 1 1 = j' * (g 0 0 + j * g 1 0) + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧ g' 1 1 = g 1 1 - g 1 0 * j' ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0 + j * g 1 0, e; p * g 1 0, g 1 1 - g 1 0 * j'], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 1 0) * he
  · have heR : (g 0 1 : ℝ) + (j : ℝ) * g 1 1 = (j' : ℝ) * (g 0 0 + (j : ℝ) * g 1 0) + (p : ℝ) * e := by
      exact_mod_cast he
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination heR | ring

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeMatrix_mul_of_eq' (g : SL(2, ℤ)) (j : ℕ) (e : ℤ)
    (he : g 0 0 + j * g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ g' 1 1 = p * g 1 1 ∧
      heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![e, g 0 1 + j * g 1 1; g 1 0, p * g 1 1], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 1 1) * he
  · have heR : (g 0 0 : ℝ) + (j : ℝ) * g 1 0 = (p : ℝ) * e := by
      exact_mod_cast he
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination heR | ring

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeDiagMatrix_mul_of_eq (g : SL(2, ℤ)) (j' : ℕ) (e : ℤ)
    (he : g 1 1 = g 1 0 * j' + p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = g 1 0 ∧ g' 1 1 = e ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  have hdet := det_eq g
  refine ⟨⟨!![p * g 0 0, g 0 1 - g 0 0 * j'; g 1 0, e], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet - (g 0 0) * he
  · have heR : (g 1 1 : ℝ) = g 1 0 * (j' : ℝ) + (p : ℝ) * e := by
      exact_mod_cast he
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination heR | ring

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeDiagMatrix_mul_of_eq' (g : SL(2, ℤ)) (e : ℤ) (he : g 1 0 = p * e) :
    ∃ g' : SL(2, ℤ), g' 1 0 = e ∧ g' 1 1 = g 1 1 ∧
      heckeDiagMatrix p * mapGL ℝ g = mapGL ℝ g' * heckeDiagMatrix p := by
  have hdet := det_eq g
  refine ⟨⟨!![g 0 0, p * g 0 1; e, g 1 1], ?_⟩, rfl, rfl, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + (g 0 1) * he
  · have heR : (g 1 0 : ℝ) = (p : ℝ) * e := by
      exact_mod_cast he
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [hp, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination heR | ring

end commutation

section reindex

variable {p : ℕ} [NeZero p]

theorem sum_range_eq_sum_zmod {A : Type*} [AddCommMonoid A] (G : ℕ → A) :
    ∑ j ∈ Finset.range p, G j = ∑ x : ZMod p, G x.val := by
  refine Finset.sum_nbij' (fun j : ℕ ↦ (j : ZMod p)) (fun x : ZMod p ↦ x.val) (fun _ _ ↦ Finset.mem_univ _)
    (fun x _ ↦ Finset.mem_range.mpr x.val_lt) (fun j hj ↦ ?_) (fun x _ ↦ ?_) (fun j hj ↦ ?_)
  · exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · exact ZMod.natCast_zmod_val x
  · rw [ZMod.val_cast_of_lt (Finset.mem_range.mp hj)]

theorem heckeU_eq_sum_zmod (k : ℤ) (f : ℍ → ℂ) :
    heckeU k p f = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val := by
  rw [heckeU_def]
  exact sum_range_eq_sum_zmod _

end reindex

section matrices

/-- The translation `j ↦ j + t` as an integral matrix. -/
private def translate (t : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, t; 0, 1]

/-- The dilation `diag(1, p)` as an integral matrix. -/
private def dilate (p : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (p : ℤ)]

@[simp] private theorem translate_zero : translate 0 = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [translate]

private theorem translate_add (s t : ℤ) : translate (s + t) = translate s * translate t := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [translate, Matrix.mul_apply, Fin.sum_univ_two]
  ring

@[simp] private theorem translate_neg_mul (t : ℤ) : translate (-t) * translate t = 1 := by
  rw [← translate_add, neg_add_cancel, translate_zero]

@[simp] private theorem det_translate (t : ℤ) : (translate t).det = 1 := by
  rw [translate, Matrix.det_fin_two_of]
  ring

@[simp] private theorem det_dilate (p : ℕ) : (dilate p).det = (p : ℤ) := by
  rw [dilate, Matrix.det_fin_two_of]
  ring

private theorem translate_mul (s : ℤ) (G : Matrix (Fin 2) (Fin 2) ℤ) :
    translate s * G = !![G 0 0 + s * G 1 0, G 0 1 + s * G 1 1; G 1 0, G 1 1] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [translate, Matrix.mul_apply, Fin.sum_univ_two]

private theorem mul_translate (t : ℤ) (G : Matrix (Fin 2) (Fin 2) ℤ) :
    G * translate t = !![G 0 0, G 0 0 * t + G 0 1; G 1 0, G 1 0 * t + G 1 1] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [translate, Matrix.mul_apply, Fin.sum_univ_two]

/-- The shear formula: translating a matrix on both sides. -/
private theorem translate_mul_translate (s t : ℤ) (G : Matrix (Fin 2) (Fin 2) ℤ) :
    translate s * G * translate t =
      !![G 0 0 + s * G 1 0, G 0 1 + s * G 1 1 + t * (G 0 0 + s * G 1 0); G 1 0,
        G 1 1 + t * G 1 0] := by
  rw [translate_mul, mul_translate]
  ext i k
  fin_cases i <;> fin_cases k <;> simp <;> ring

/-- The Hecke matrix `!![1, t; 0, p]` is a dilation followed by a translation. -/
private theorem dilate_mul_translate (p : ℕ) (t : ℤ) :
    dilate p * translate t = !![1, t; 0, (p : ℤ)] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [dilate, translate, Matrix.mul_apply, Fin.sum_univ_two]

/-- Conjugation preserves the determinant: `A * B = C * A` with `det A ≠ 0` gives `det C = det B`. -/
private theorem det_eq_of_mul_eq_mul {A B C : Matrix (Fin 2) (Fin 2) ℤ} (h : A * B = C * A)
    (hA : A.det ≠ 0) : C.det = B.det := by
  have h' : A.det * B.det = A.det * C.det := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm C.det A.det] at this
    exact this
  exact (mul_left_cancel₀ hA h').symm

/-- Clearing the dilation: a factor `p` in the `0 1`-entry is exactly what `dilate p` absorbs, and
the factor is picked up in the `1 0`-entry. -/
private theorem dilate_mul_eq (p : ℕ) (a b c d : ℤ) :
    dilate p * !![a, b * (p : ℤ); c, d] = !![a, b; (p : ℤ) * c, d] * dilate p := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [dilate, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

/-- Transporting a conjugation: if `X = U * B * V` is the conjugate of `B`, `V * W = 1`, and `X`
clears the dilation `D` as `D * X = g' * D`, then `B` itself satisfies `D * U * B = g' * (D * W)`. -/
private theorem mul_eq_of_conj {D U V W X B g' : Matrix (Fin 2) (Fin 2) ℤ} (hX : X = U * B * V)
    (hVW : V * W = 1) (hfac : D * X = g' * D) : D * U * B = g' * (D * W) := by
  subst hX
  calc D * U * B
      = (D * U) * (B * 1) := by rw [mul_one]
    _ = (D * U) * (B * (V * W)) := by rw [hVW]
    _ = (D * (U * B * V)) * W := by noncomm_ring
    _ = (g' * D) * W := by rw [hfac]
    _ = g' * (D * W) := by rw [mul_assoc]

end matrices

section heckeU

variable {p : ℕ}

theorem unit_of_apply_one_zero_eq_zero (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) :
    ((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) = 1 := by
  have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
  push_cast at this
  linear_combination this + ((g 0 1 : ℤ) : ZMod p) * hc

/-- The image of `j` under `g`, read mod `p`. -/
def affineMap (g : SL(2, ℤ)) (j : ZMod p) : ZMod p :=
  ((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j)

@[simp] theorem affineMap_apply (g : SL(2, ℤ)) (j : ZMod p) :
    affineMap g j =
      ((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j) := rfl

/-- `affineMap g` is a permutation of `ZMod p` when `g` is in `Γ₀(p)`. -/
def affinePerm (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) : Equiv.Perm (ZMod p) where
  toFun := affineMap g
  invFun j := ((g 0 0 : ℤ) : ZMod p) * (((g 0 0 : ℤ) : ZMod p) * j - ((g 0 1 : ℤ) : ZMod p))
  left_inv j := by
    simp only [affineMap]
    linear_combination (((g 0 0 : ℤ) : ZMod p) * ((g 0 1 : ℤ) : ZMod p)
      + j * (((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) + 1)) *
        unit_of_apply_one_zero_eq_zero g hc
  right_inv j := by
    simp only [affineMap]
    linear_combination (-(((g 1 1 : ℤ) : ZMod p) * ((g 0 1 : ℤ) : ZMod p))
      + j * (((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) + 1)) *
        unit_of_apply_one_zero_eq_zero g hc

theorem affinePerm_apply (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) (j : ZMod p) :
    affinePerm g hc j =
      ((g 1 1 : ℤ) : ZMod p) * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j) := rfl

/-- The Hecke matrix is the integer model `!![1, j; 0, p]` read through `ℤ → ℝ`. -/
private theorem heckeMatrix_map_int (hp : p ≠ 0) (j : ℕ) :
    (!![1, (j : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) =
      (heckeMatrix p j : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [val_heckeMatrix hp]
  ext i k
  fin_cases i <;> fin_cases k <;> simp

/-- A `ℤ`-matrix identity `!![1, j; 0, p] * g = g' * !![1, j'; 0, p]`, read through `ℤ → ℝ` as an
identity of `GL (Fin 2) ℝ` matrices. -/
private theorem mapGL_mul_of_matrix (hp : p ≠ 0) {j j' : ℕ} {g g' : SL(2, ℤ)}
    (h : (!![1, (j : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * (↑g : Matrix (Fin 2) (Fin 2) ℤ)
      = (↑g' : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (j' : ℤ); 0, (p : ℤ)]) :
    heckeMatrix p j * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j' := by
  apply Units.ext
  simp only [Units.val_mul, ← heckeMatrix_map_int hp j, ← heckeMatrix_map_int hp j',
    mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    ← Matrix.map_mul, h]

variable [NeZero p]

/-- `Γ₀` is antitone in the level. -/
private theorem Gamma0_antitone {m n : ℕ} (h : n ∣ m) :
    CongruenceSubgroup.Gamma0 m ≤ CongruenceSubgroup.Gamma0 n := by
  intro g hg
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg ⊢
  exact (Int.natCast_dvd_natCast.mpr h).trans hg

/-- `U_p` raises the level: for `g ∈ Γ₀(M)` with `p ∣ M` the product `!![1, x; 0, p] * g`
re-associates as `g' * !![1, affineMap g x; 0, p]` with `g' ∈ Γ₀(p * M)` — the Hecke representative
commutes past `g` at the cost of moving `x` to its image and multiplying the level by `p`. The three
factors are the dilation `dilate p` and the translations `translate x`, `translate (-(affineMap g x))`;
over `ℝ` the witness is `dilate p * X * (dilate p)⁻¹` for the integral matrix
`X = translate x * g * translate (-(affineMap g x))`, so only its integrality has to be checked, and
`exists_dilate_mul` reduces that to `p ∣ X 0 1`. -/
theorem heckeMatrix_mul_of_dvd (g : SL(2, ℤ)) (M : ℕ) (hpM : p ∣ M) (hg : (M : ℤ) ∣ g 1 0)
    (x : ZMod p) :
    ∃ g' : SL(2, ℤ), g' ∈ CongruenceSubgroup.Gamma0 (p * M) ∧
      heckeMatrix p x.val * mapGL ℝ g =
        mapGL ℝ g' * heckeMatrix p (affineMap g x).val := by
  have hc : (p : ℤ) ∣ g 1 0 := (Int.natCast_dvd_natCast.mpr hpM).trans hg
  have hc0 : ((g 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have hunit : ((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) = 1 :=
    unit_of_apply_one_zero_eq_zero g hc0
  set x' := affineMap g x with hx'
  let X : Matrix (Fin 2) (Fin 2) ℤ :=
    translate (x.val : ℤ) * (↑g : Matrix (Fin 2) (Fin 2) ℤ) * translate (-(x'.val : ℤ))
  have hX10 : X 1 0 = g 1 0 := by
    simp [X, translate_mul_translate]
  have hX01 : X 0 1 = g 0 1 + x.val * g 1 1 - x'.val * (g 0 0 + x.val * g 1 0) := by
    simp [X, translate_mul_translate]
    ring
  have hcocycle : (g 0 1 : ZMod p) + x * (g 1 1 : ZMod p) =
      x' * ((g 0 0 : ZMod p) + x * (g 1 0 : ZMod p)) := by
    rw [hx', affineMap_apply, hc0, mul_zero, add_zero]
    calc (g 0 1 : ZMod p) + x * (g 1 1 : ZMod p)
        = ((g 0 1 : ZMod p) + x * (g 1 1 : ZMod p)) * 1 := by ring
      _ = ((g 0 1 : ZMod p) + x * (g 1 1 : ZMod p)) *
            ((g 0 0 : ZMod p) * (g 1 1 : ZMod p)) := by rw [hunit]
      _ = (g 1 1 : ZMod p) * ((g 0 1 : ZMod p) + (g 1 1 : ZMod p) * x) *
            (g 0 0 : ZMod p) := by ring
  have hdvd : (p : ℤ) ∣ X 0 1 := by
    rw [hX01]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast
    simp only [ZMod.natCast_zmod_val, sub_eq_zero]
    exact hcocycle
  obtain ⟨c, hXc⟩ := hdvd
  have hXeq : X = !![X 0 0, c * (p : ℤ); X 1 0, X 1 1] := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hXc, mul_comm]
  have hfac : dilate p * X = !![X 0 0, c; (p : ℤ) * X 1 0, X 1 1] * dilate p := by
    rw [hXeq]
    exact dilate_mul_eq p (X 0 0) c (X 1 0) (X 1 1)
  have hdetX : X.det = (↑g : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [X, Matrix.det_mul]
  have hp0 : (dilate p).det ≠ 0 := by
    rw [det_dilate]
    exact_mod_cast NeZero.ne p
  have hdet : (!![X 0 0, c; (p : ℤ) * X 1 0, X 1 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [det_eq_of_mul_eq_mul hfac hp0, hdetX, Matrix.SpecialLinearGroup.det_coe]
  have hXW : translate (x.val : ℤ) * (↑g : Matrix (Fin 2) (Fin 2) ℤ) = X * translate (x'.val : ℤ) := by
    simp only [X]
    rw [mul_assoc, translate_neg_mul, mul_one]
  refine ⟨⟨!![X 0 0, c; (p : ℤ) * X 1 0, X 1 1], hdet⟩, ?_, ?_⟩
  · refine CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_)
    show ((p * M : ℕ) : ℤ) ∣ (!![X 0 0, c; (p : ℤ) * X 1 0, X 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0
    rw [show (!![X 0 0, c; (p : ℤ) * X 1 0, X 1 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        (p : ℤ) * g 1 0 by simp [hX10]]
    push_cast
    exact mul_dvd_mul_left (p : ℤ) hg
  · refine mapGL_mul_of_matrix (NeZero.ne p) ?_
    show (!![1, (x.val : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) *
          (↑g : Matrix (Fin 2) (Fin 2) ℤ)
        = (!![X 0 0, c; (p : ℤ) * X 1 0, X 1 1] : Matrix (Fin 2) (Fin 2) ℤ) *
            !![1, (x'.val : ℤ); 0, (p : ℤ)]
    rw [← dilate_mul_translate, ← dilate_mul_translate]
    exact mul_eq_of_conj (D := dilate p) (U := translate (x.val : ℤ))
      (V := translate (-(x'.val : ℤ))) (W := translate (x'.val : ℤ)) (X := X) (B := ↑g)
      rfl (translate_neg_mul (x'.val : ℤ)) hfac

variable {N : ℕ} (k : ℤ)

theorem heckeU_slash_mapGL (hpN : p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    heckeU k p f ∣[k] (mapGL ℝ g) = heckeU k p f := by
  have hcN : (N : ℤ) ∣ g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp hg)
  have hc : (p : ℤ) ∣ g 1 0 := (Int.natCast_dvd_natCast.mpr hpN).trans hcN
  have hc0 : ((g 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  rw [heckeU_eq_sum_zmod k f, SlashAction.sum_slash]
  calc ∑ x : ZMod p, (f ∣[k] heckeMatrix p x.val) ∣[k] mapGL ℝ g
      = ∑ x : ZMod p, f ∣[k] heckeMatrix p (affinePerm g hc0 x).val := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hmul⟩ := heckeMatrix_mul_of_dvd g N hpN hcN x
        have hx : affinePerm g hc0 x = affineMap g x := rfl
        rw [← hx] at hmul
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) (Gamma0_antitone (dvd_mul_left N p) hg'))]
    _ = ∑ x : ZMod p, f ∣[k] heckeMatrix p x.val :=
        Equiv.sum_comp (affinePerm g hc0) (fun x ↦ f ∣[k] heckeMatrix p x.val)

end heckeU

section heckeT

variable {p : ℕ}

def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)

@[simp] theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[simp] theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeMatrix p j.val := rfl

theorem heckeT_eq_sum_onePoint [NeZero p] (k : ℤ) (f : ℍ → ℂ) :
    heckeT k p f = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x := by
  rw [heckeT_eq_heckeU_add, heckeU_eq_sum_zmod, add_comm]
  exact (Fintype.sum_option (fun x : OnePoint (ZMod p) ↦ f ∣[k] heckeRep p x)).symm

variable [Fact p.Prime]

variable (p) in

def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p); ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    (by
      have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
      push_cast at this
      rw [Matrix.det_fin_two_of,
        show ((g 1 1 : ℤ) : ZMod p) * ((g 0 0 : ℤ) : ZMod p) - ((g 0 1 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p)
          = 1 by linear_combination this]
      exact one_ne_zero)

@[simp] theorem redMatrix_apply_zero_zero (g : SL(2, ℤ)) :
    redMatrix p g 0 0 = ((g 1 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[simp] theorem redMatrix_apply_zero_one (g : SL(2, ℤ)) :
    redMatrix p g 0 1 = ((g 0 1 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[simp] theorem redMatrix_apply_one_zero (g : SL(2, ℤ)) :
    redMatrix p g 1 0 = ((g 1 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

@[simp] theorem redMatrix_apply_one_one (g : SL(2, ℤ)) :
    redMatrix p g 1 1 = ((g 0 0 : ℤ) : ZMod p) := by
  simp [redMatrix]

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

namespace Gamma1Hecke

-- The pin's public `heckeRep_mul`: the Γ₀ `S_` copy in this module states only
-- the multiplication conjunct (with an `(N : ℤ) ∣ g 1 0` hypothesis), while the
-- pin's public `CuspForm.Gamma1Hecke` block additionally records the `1 1` entry
-- of the witness and the `wt`-equation that the diamond operator needs. The
-- declaration keeps the pin's `Gamma1Hecke` namespace segment so the statement
-- checker's dotted-name fallback verifies it against that public block, while the
-- Γ₀ copy keeps its own `HeckeSlashInvariance` namespace.
set_option backward.isDefEq.respectTransparency.types false in
theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      ((g' 1 1 : ℤ) : ZMod N) * wt N p x = ((g 1 1 : ℤ) : ZMod N) * wt N p (redMatrix p g • x) ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hgC' : ((g 1 0 : ℤ) : ZMod N) = 0 := by simpa using CongruenceSubgroup.Gamma0_mem.mp hg
  have hgN : (N : ℤ) ∣ g 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hgC'
  induction x using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : ((g 1 0 : ℤ) : ZMod p) = 0
    ·
      rw [ite_eq_left (by simpa using hc), heckeRep_infty]
      obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
      obtain ⟨g', hg', hd', hmul⟩ := heckeDiagMatrix_mul_of_eq' hp g e he
      refine ⟨g', ?_, ?_, hmul⟩
      · rw [hg']
        have hcop : IsCoprime (N : ℤ) (p : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN).symm
        exact hcop.dvd_of_dvd_mul_left (he ▸ hgN)
      · rw [hd', wt_infty]
    ·
      rw [ite_eq_right (by simpa using hc), heckeRep_infty, heckeRep_coe]
      set y : ZMod p := redMatrix p g 0 0 / redMatrix p g 1 0
        with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 1 1 - g 1 0 * y.val := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, hy, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
          mul_div_cancel₀ _ hc, sub_self]
      obtain ⟨g', hg', hd', hmul⟩ := heckeDiagMatrix_mul_of_eq hp g y.val e (by linear_combination he)
      refine ⟨g', hg' ▸ hgN, ?_, hmul⟩
      rw [hd', wt_infty, wt_coe]
      have : ((g 1 1 : ℤ) : ZMod N) = ((g 1 0 : ℤ) : ZMod N) * (y.val : ℤ) + (p : ℤ) * e := by
        have := congrArg (Int.cast : ℤ → ZMod N)
          (show g 1 1 = g 1 0 * y.val + p * e by linear_combination he)
        push_cast at this ⊢
        exact this
      rw [hgC', zero_mul, zero_add] at this
      push_cast at this
      rw [mul_one, mul_comm, this]
  | coe j =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h : redMatrix p g 1 0 * j + redMatrix p g 1 1 = 0
    ·
      rw [ite_eq_left h, heckeRep_infty, heckeRep_coe]
      rw [redMatrix_apply_one_zero, redMatrix_apply_one_one] at h
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 0 + j.val * g 1 0 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val]
        linear_combination h
      obtain ⟨g', hg', hd', hmul⟩ := heckeMatrix_mul_of_eq' hp g j.val e he
      refine ⟨g', hg' ▸ hgN, ?_, hmul⟩
      rw [hd', wt_infty, wt_coe, mul_one]
      push_cast
      rw [mul_comm]
    ·
      rw [ite_eq_right h, heckeRep_coe, heckeRep_coe]
      set y : ZMod p := (redMatrix p g 0 0 * j + redMatrix p g 0 1) /
        (redMatrix p g 1 0 * j + redMatrix p g 1 1) with hy
      obtain ⟨e, he⟩ : (p : ℤ) ∣ g 0 1 + j.val * g 1 1 - y.val * (g 0 0 + j.val * g 1 0) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
          show ((g 0 0 : ℤ) : ZMod p) + j * ((g 1 0 : ℤ) : ZMod p)
            = redMatrix p g 1 0 * j + redMatrix p g 1 1 by
              rw [redMatrix_apply_one_zero, redMatrix_apply_one_one]; ring,
          hy, div_mul_cancel₀ _ h, redMatrix_apply_zero_zero, redMatrix_apply_zero_one]
        ring
      obtain ⟨g', hg', hd', hmul⟩ :=
        heckeMatrix_mul_of_eq hp g j.val y.val e (by linear_combination he)
      refine ⟨g', hg' ▸ dvd_mul_of_dvd_right hgN _, ?_, hmul⟩
      rw [hd', wt_coe, wt_coe, mul_one, mul_one]
      push_cast
      rw [hgC', zero_mul, sub_zero]

end Gamma1Hecke

-- The pin's Γ₁ copy of `heckeRep_mul` (no extra `g 1 1` factor on the `wt`
-- equation), landing H2's clash reconciliation. It lives in a distinct
-- namespace from the Γ₀ copy above so both public statements verify; the Γ₀
-- consumers `sum_slash_mapGL_of_mem_Gamma0` / `PhiGenDescends` keep using
-- `Gamma1Hecke.heckeRep_mul`.
namespace HeckeGamma1

theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 N)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      ((g' 1 1 : ℤ) : ZMod N) * wt N p x = wt N p (redMatrix p g • x) ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hd : ((g 1 1 : ℤ) : ZMod N) = 1 := by
    simpa using ((CongruenceSubgroup.Gamma1_mem N g).mp hg).2.1
  obtain ⟨g', hg', hd', hmul⟩ :=
    Gamma1Hecke.heckeRep_mul (p := p) hpN g (CongruenceSubgroup.Gamma1_in_Gamma0 N hg) x
  rw [hd, one_mul] at hd'
  exact ⟨g', hg', hd', hmul⟩

end HeckeGamma1

open Gamma1Hecke

variable {N : ℕ} (k : ℤ)

theorem heckeT_slash_mapGL (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    heckeT k p f ∣[k] (mapGL ℝ g) = heckeT k p f := by
  rw [heckeT_eq_sum_onePoint k f, SlashAction.sum_slash]
  calc ∑ x : OnePoint (ZMod p), (f ∣[k] heckeRep p x) ∣[k] mapGL ℝ g
      = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p (redMatrix p g • x) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', -, hmul⟩ := heckeRep_mul hpN g hg x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N :=
          CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hg')
        rw [← SlashAction.slash_mul, hmul, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg'N)]
    _ = ∑ x : OnePoint (ZMod p), f ∣[k] heckeRep p x :=
        Equiv.sum_comp (MulAction.toPerm (redMatrix p g)) (fun x ↦ f ∣[k] heckeRep p x)

end heckeT

end ModularForm.HeckeRepresentatives

end
