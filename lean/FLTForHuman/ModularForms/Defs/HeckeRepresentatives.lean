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

  - `det_eq` and `heckeMatrix_mul_of_eq`: multiplying a Hecke matrix by
    `mapGL ℝ g` stays in the coset system, and the witness's two column entries
    are recorded (`g' 1 0 = p * g 1 0`, `g' 1 1 = g 1 1 - g 1 0 * j'.val`) — the
    Γ₀ layer reads `g' ∈ Γ₀(N)` off the first. The lemma is stated over labels
    (`j j' : ZMod p`), so the pin's quotient `e` is not needed: `p` vanishes in
    `ZMod p`. The pin's other three `_mul_of_eq` corners were proof steps of its
    own `heckeRep_mul` and are not carried.
  - `heckeRep_mul`: the pin's public Tier-2 statement
    (`Def_CuspForm_Gamma1HeckeOperators.lean:281–285`). The hypothesis is
    `g ∈ Γ₀(N)`, the witness is `repMatrix_mul`'s, and the level and the weight
    are the `1 0` and `1 1` entries of its coset identity turned into unit
    cancellations (`repMatrix` carries `p` on its diagonal exactly once, and
    `wt` is its `0 0` entry). The four label transitions live in
    `dvd_conjugate`, so the theorem itself has no case split. It is declared
    under the pin's `Gamma1Hecke` namespace segment, where the statement
    checker's dotted-name fallback finds it.
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

/-- The Weyl element `!![0, 1; 1, 0]`: it moves the `p` of `dilate` from the lower-right to the
upper-left slot. -/
private def weyl : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

@[simp] private theorem weyl_mul_weyl : weyl * weyl = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [weyl]

@[simp] private theorem det_weyl : weyl.det = -1 := by
  rw [weyl, Matrix.det_fin_two_of]
  ring

private theorem weyl_mul_eq (G : Matrix (Fin 2) (Fin 2) ℤ) :
    weyl * G = !![G 1 0, G 1 1; G 0 0, G 0 1] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [weyl, Matrix.mul_apply, Fin.sum_univ_two]

private theorem mul_weyl_eq (G : Matrix (Fin 2) (Fin 2) ℤ) :
    G * weyl = !![G 0 1, G 0 0; G 1 1, G 1 0] := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [weyl, Matrix.mul_apply, Fin.sum_univ_two]

end matrices

section coset

variable {p : ℕ}

/-- The representative of a label over `ℝ`, indexed like the integral one below: `∞` is
`heckeDiagMatrix`, the point `j` is `heckeMatrix p j.val`. -/
def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)

@[simp] theorem heckeRep_infty : heckeRep p ∞ = heckeDiagMatrix p := rfl

@[simp] theorem heckeRep_coe (j : ZMod p) : heckeRep p j = heckeMatrix p j.val := rfl

/-- A Hecke label as an integral representative: `∞` is `!![p, 0; 0, 1]`, the point `j` is
`!![1, j.val; 0, p]`.  The entry is the canonical lift `j.val`, so the matrix depends on the label
only, not on a choice of lift. -/
private def repMatrix (p : ℕ) : OnePoint (ZMod p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p : ℤ), 0; 0, 1]
  | some j => !![1, (j.val : ℤ); 0, (p : ℤ)]

/-- The left factor `weyl`: at `∞` the `p` of the representative sits in the upper-left slot, which
is `dilate` conjugated by the Weyl element. -/
private def weylPart : OnePoint (ZMod p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => weyl
  | some _ => 1

/-- The right factor: the label as a translation. -/
private def shear : OnePoint (ZMod p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => weyl
  | some j => translate (j.val : ℤ)

/-- The inverse of `shear`. -/
private def unshear : OnePoint (ZMod p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => weyl
  | some j => translate (-(j.val : ℤ))

/-- The shear conjugate of `g` at two labels: its `0 1` entry is the `ℙ¹(𝔽_p)`-cocycle. -/
private def conjugate (g : SL(2, ℤ)) (x y : OnePoint (ZMod p)) : Matrix (Fin 2) (Fin 2) ℤ :=
  shear x * (↑g : Matrix (Fin 2) (Fin 2) ℤ) * unshear y

/-- The `p`-cleared form of a shear conjugate whose `0 1` entry is `p * c`. -/
private def clearedWitness (p : ℕ) (X : Matrix (Fin 2) (Fin 2) ℤ) (c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![X 0 0, c; (p : ℤ) * X 1 0, X 1 1]

/-- Both representatives are upper triangular. -/
private theorem repMatrix_apply_one_zero (x : OnePoint (ZMod p)) :
    repMatrix p x 1 0 = 0 := by
  induction x using OnePoint.rec <;> rfl

/-- The weight is the `0 0` entry of the representative. -/
private theorem cast_repMatrix_apply_zero_zero (N : ℕ) (x : OnePoint (ZMod p)) :
    ((repMatrix p x 0 0 : ℤ) : ZMod N) = wt N p x := by
  induction x using OnePoint.rec <;> simp [repMatrix]

/-- The representative carries the `p` on its diagonal exactly once: `1 1` times the weight is `p`. -/
private theorem cast_repMatrix_apply_one_one_mul (N : ℕ) (x : OnePoint (ZMod p)) :
    ((repMatrix p x 1 1 : ℤ) : ZMod N) * wt N p x = (p : ZMod N) := by
  induction x using OnePoint.rec <;> simp [repMatrix]

/-- A unit is cancellable on the left, and a unit times zero is zero. -/
private theorem eq_zero_of_mul_eq_zero_of_isUnit {N : ℕ} {w t : ZMod N} (hw : IsUnit w)
    (h : t * w = 0) : t = 0 := by
  obtain ⟨u, hu⟩ := hw
  rw [← hu] at h
  calc t = t * ↑u * (↑u⁻¹ : ZMod N) := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = 0 := by rw [h, zero_mul]

private theorem eq_of_mul_eq_mul_of_isUnit {N : ℕ} {w a b : ZMod N} (hw : IsUnit w)
    (h : w * a = w * b) : a = b := by
  obtain ⟨u, hu⟩ := hw
  rw [← hu] at h
  calc a = (↑u⁻¹ : ZMod N) * (↑u * a) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = (↑u⁻¹ : ZMod N) * (↑u * b) := by rw [h]
    _ = b := by rw [← mul_assoc, Units.inv_mul, one_mul]

private theorem unshear_mul_shear (x : OnePoint (ZMod p)) : unshear x * shear x = 1 := by
  cases x with
  | infty => exact weyl_mul_weyl
  | coe j => simp [shear, unshear, ← translate_add]

/-- Every representative is `dilate p` between the two integer factors. -/
private theorem repMatrix_eq (x : OnePoint (ZMod p)) :
    repMatrix p x = weylPart x * dilate p * shear x := by
  cases x with
  | infty => ext i k; fin_cases i <;> fin_cases k <;> simp [repMatrix, weylPart, shear, weyl, dilate]
  | coe j => ext i k; fin_cases i <;> fin_cases k <;> simp [repMatrix, weylPart, shear, translate, dilate]

private theorem det_weylPart_mul_shear (x : OnePoint (ZMod p)) : (weylPart x).det * (shear x).det = 1 := by
  cases x with
  | infty => simp [weylPart, shear]
  | coe j => simp [weylPart, shear]

private theorem det_unshear_mul_weylPart (x : OnePoint (ZMod p)) : (unshear x).det * (weylPart x).det = 1 := by
  cases x with
  | infty => simp [weylPart, unshear]
  | coe j => simp [weylPart, unshear]

/-- Cancelling the pair of `weyl` factors that the left and the right factor contribute. -/
private theorem weylPart_sandwich (A B : Matrix (Fin 2) (Fin 2) ℤ) (y : OnePoint (ZMod p)) :
    (A * weylPart y) * (weylPart y * B) = A * B := by
  cases y with
  | infty =>
    show (A * weyl) * (weyl * B) = A * B
    rw [← mul_assoc, mul_assoc A weyl weyl, weyl_mul_weyl, mul_one]
  | coe j => simp [weylPart]

private theorem repMatrix_map_int (hp : p ≠ 0) (x : OnePoint (ZMod p)) :
    (repMatrix p x).map (algebraMap ℤ ℝ) = (heckeRep p x : Matrix (Fin 2) (Fin 2) ℝ) := by
  cases x with
  | infty =>
    ext i k
    fin_cases i <;> fin_cases k <;> simp [repMatrix, heckeRep, val_heckeDiagMatrix hp]
  | coe j =>
    ext i k
    fin_cases i <;> fin_cases k <;> simp [repMatrix, heckeRep, val_heckeMatrix hp]

/-- A `ℤ`-matrix identity, read through `ℤ → ℝ` as an identity of `GL (Fin 2) ℝ`. -/
private theorem mapGL_mul_of_matrix (hp : p ≠ 0) {x y : OnePoint (ZMod p)} {g g' : SL(2, ℤ)}
    (h : repMatrix p x * (↑g : Matrix (Fin 2) (Fin 2) ℤ) =
      (↑g' : Matrix (Fin 2) (Fin 2) ℤ) * repMatrix p y) :
    heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p y := by
  apply Units.ext
  simp only [Units.val_mul, ← repMatrix_map_int hp x, ← repMatrix_map_int hp y,
    mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    ← Matrix.map_mul, h]

/-- **The coset action.**  Multiplying the representative of `x` by `g` gives the representative of
`y`, up to the integral factor `weylPart x * clearedWitness p (conjugate g x y) c * weylPart y`,
provided the cocycle `conjugate g x y 0 1` is divisible by `p`.  The witness is recorded explicitly,
with its quotient, so its entries can be read off the matrix as well as off the identity. -/
private theorem repMatrix_mul (hp : p ≠ 0) (g : SL(2, ℤ)) (x y : OnePoint (ZMod p))
    (hc : (p : ℤ) ∣ conjugate g x y 0 1) :
    ∃ (c : ℤ) (g' : SL(2, ℤ)),
      (↑g' : Matrix (Fin 2) (Fin 2) ℤ) =
        weylPart x * clearedWitness p (conjugate g x y) c * weylPart y ∧
      repMatrix p x * (↑g : Matrix (Fin 2) (Fin 2) ℤ) =
        (↑g' : Matrix (Fin 2) (Fin 2) ℤ) * repMatrix p y := by
  obtain ⟨c, hc⟩ := hc
  set X := conjugate g x y with hX
  have hcX : X 0 1 = (p : ℤ) * c := by rw [hX]; exact hc
  have hXeq : X = !![X 0 0, c * (p : ℤ); X 1 0, X 1 1] := by
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hcX, mul_comm]
  have hfac : dilate p * X = clearedWitness p X c * dilate p := by
    rw [hXeq, clearedWitness]
    exact dilate_mul_eq p (X 0 0) c (X 1 0) (X 1 1)
  have hp0 : (dilate p).det ≠ 0 := by
    rw [det_dilate]
    exact_mod_cast hp
  have hdetX : X.det = (shear x).det * (unshear y).det := by
    simp [hX, conjugate, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe]
  have hdet : (weylPart x * clearedWitness p X c * weylPart y).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, det_eq_of_mul_eq_mul hfac hp0, hdetX]
    rw [show ((weylPart x).det * ((shear x).det * (unshear y).det)) * (weylPart y).det
        = ((weylPart x).det * (shear x).det) * ((unshear y).det * (weylPart y).det) by ring,
      det_weylPart_mul_shear, det_unshear_mul_weylPart, one_mul]
  refine ⟨c, ⟨weylPart x * clearedWitness p X c * weylPart y, hdet⟩, rfl, ?_⟩
  have hXshear : X * shear y = shear x * (↑g : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [hX, conjugate, mul_assoc, unshear_mul_shear, mul_one]
  calc repMatrix p x * (↑g : Matrix (Fin 2) (Fin 2) ℤ)
      = weylPart x * dilate p * (shear x * (↑g : Matrix (Fin 2) (Fin 2) ℤ)) := by
        rw [repMatrix_eq x]
        noncomm_ring
    _ = weylPart x * dilate p * (X * shear y) := by rw [hXshear]
    _ = weylPart x * (dilate p * X) * shear y := by noncomm_ring
    _ = weylPart x * (clearedWitness p X c * dilate p) * shear y := by rw [hfac]
    _ = (weylPart x * clearedWitness p X c * weylPart y) * (weylPart y * (dilate p * shear y)) := by
        rw [weylPart_sandwich (weylPart x * clearedWitness p X c) (dilate p * shear y) y]
        noncomm_ring
    _ = (weylPart x * clearedWitness p X c * weylPart y) * repMatrix p y := by
        rw [repMatrix_eq y]
        noncomm_ring

/-- The four entry shapes of the shear conjugate, one per pair of endpoint types. -/
private theorem conjugate_coe_coe (g : SL(2, ℤ)) (j j' : ZMod p) :
    conjugate g (j : OnePoint (ZMod p)) (j' : OnePoint (ZMod p))
      = !![((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 + (j.val : ℤ) * ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0,
          ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 + (j.val : ℤ) * ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 1
            + -(j'.val : ℤ) * (((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 + (j.val : ℤ) * ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0);
          ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0,
          ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 1 + -(j'.val : ℤ) * ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0] := by
  simp only [conjugate, shear, unshear, translate_mul_translate]

private theorem conjugate_coe_infty (g : SL(2, ℤ)) (j : ZMod p) :
    conjugate g (j : OnePoint (ZMod p)) ∞
      = !![((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 + (j.val : ℤ) * ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 1,
          ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 + (j.val : ℤ) * ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0;
          ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 1, ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0] := by
  simp only [conjugate, shear, unshear, translate_mul, mul_weyl_eq]
  rfl

private theorem conjugate_infty_coe (g : SL(2, ℤ)) (j' : ZMod p) :
    conjugate g ∞ (j' : OnePoint (ZMod p))
      = !![((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0,
          ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 * -(j'.val : ℤ) + ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 1;
          ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 0,
          ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 * -(j'.val : ℤ) + ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 1] := by
  simp only [conjugate, shear, unshear, weyl_mul_eq, mul_translate]
  rfl

private theorem conjugate_infty_infty (g : SL(2, ℤ)) :
    conjugate g (∞ : OnePoint (ZMod p)) ∞
      = !![((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 1, ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 1 0;
          ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 1, ((↑g : Matrix (Fin 2) (Fin 2) ℤ)) 0 0] := by
  simp only [conjugate, shear, unshear, weyl_mul_eq, mul_weyl_eq]
  rfl

end coset

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

set_option backward.isDefEq.respectTransparency.types false in
/-- The pin's `_mul_of_eq` over labels: `j` and `j'` are labels, not lifts, so the cocycle
condition is an identity in `ZMod p` — the pin's quotient `e` and its `p * e` term vanish. -/
theorem heckeMatrix_mul_of_eq (g : SL(2, ℤ)) (j j' : ZMod p)
    (he : ((g 0 1 : ℤ) : ZMod p) + j * ((g 1 1 : ℤ) : ZMod p)
        = j' * (((g 0 0 : ℤ) : ZMod p) + j * ((g 1 0 : ℤ) : ZMod p))) :
    ∃ g' : SL(2, ℤ), g' 1 0 = p * g 1 0 ∧ g' 1 1 = g 1 1 - g 1 0 * (j'.val : ℤ) ∧
      heckeMatrix p j.val * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p j'.val := by
  have : NeZero p := ⟨hp⟩
  have hc : (p : ℤ) ∣ conjugate g (j : OnePoint (ZMod p)) (j' : OnePoint (ZMod p)) 0 1 := by
    rw [conjugate_coe_coe, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    linear_combination he
  obtain ⟨-, g', -, hmul⟩ :=
    repMatrix_mul hp g (j : OnePoint (ZMod p)) (j' : OnePoint (ZMod p)) hc
  obtain ⟨h10, h11⟩ : (p : ℤ) * g 1 0 = g' 1 0 ∧
      (p : ℤ) * g 1 1 = g' 1 0 * (j'.val : ℤ) + g' 1 1 * (p : ℤ) := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => (M 1 0, M 1 1)) hmul
    simpa [repMatrix, Matrix.mul_apply, Fin.sum_univ_two] using h
  refine ⟨g', h10.symm, ?_, mapGL_mul_of_matrix hp hmul⟩
  rw [← h10] at h11
  refine mul_left_cancel₀ (by exact_mod_cast hp : (p : ℤ) ≠ 0) ?_
  linear_combination -h11

end commutation

section heckeU

variable {p : ℕ}

theorem unit_of_apply_one_zero_eq_zero (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0) :
    ((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) = 1 := by
  have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
  push_cast at this
  linear_combination this + ((g 0 1 : ℤ) : ZMod p) * hc

/-- The label of the image of the point `j`, in the form that is convenient on `Γ₀(p)`: there the
denominator of the label action is the unit `g 0 0`, with inverse `g 1 1`, so the general action
collapses to `g 1 1 * (g 0 1 + g 1 1 * j)`; see `affineMap_eq_smul_redMatrix`. -/
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

variable [NeZero p]

/-- `Γ₀` is antitone in the level. -/
private theorem Gamma0_antitone {m n : ℕ} (h : n ∣ m) :
    CongruenceSubgroup.Gamma0 m ≤ CongruenceSubgroup.Gamma0 n := by
  intro g hg
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg ⊢
  exact (Int.natCast_dvd_natCast.mpr h).trans hg

/-- `U_p` raises the level: for `g ∈ Γ₀(M)` with `p ∣ M` the product `!![1, x; 0, p] * g`
re-associates as `g' * !![1, affineMap g x; 0, p]` with `g' ∈ Γ₀(p * M)` — the Hecke representative
commutes past `g` at the cost of moving `x` to its image and multiplying the level by `p`. Over
`ℤ` this is the coset action `repMatrix_mul`: the image label is read off the row of `!![1, x; 0, p] * g`
that does not carry the `p`, which is where `Γ₀(p)` enters (its lower-left entry vanishes mod `p`, so
the denominator of that row is the unit `g 0 0`). -/
theorem heckeMatrix_mul_of_dvd (g : SL(2, ℤ)) (M : ℕ) (hpM : p ∣ M) (hg : (M : ℤ) ∣ g 1 0)
    (x : ZMod p) :
    ∃ g' : SL(2, ℤ), g' ∈ CongruenceSubgroup.Gamma0 (p * M) ∧
      heckeMatrix p x.val * mapGL ℝ g =
        mapGL ℝ g' * heckeMatrix p (affineMap g x).val := by
  have hc : (p : ℤ) ∣ g 1 0 := (Int.natCast_dvd_natCast.mpr hpM).trans hg
  have hc0 : ((g 1 0 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have hunit : ((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) = 1 :=
    unit_of_apply_one_zero_eq_zero g hc0
  have hcocycle : (g 0 1 : ZMod p) + x * (g 1 1 : ZMod p) =
      affineMap g x * ((g 0 0 : ZMod p) + x * (g 1 0 : ZMod p)) := by
    rw [affineMap_apply, hc0, mul_zero, add_zero]
    calc (g 0 1 : ZMod p) + x * (g 1 1 : ZMod p)
        = ((g 0 1 : ZMod p) + x * (g 1 1 : ZMod p)) * 1 := by ring
      _ = ((g 0 1 : ZMod p) + x * (g 1 1 : ZMod p)) *
            ((g 0 0 : ZMod p) * (g 1 1 : ZMod p)) := by rw [hunit]
      _ = (g 1 1 : ZMod p) * ((g 0 1 : ZMod p) + (g 1 1 : ZMod p) * x) *
            (g 0 0 : ZMod p) := by ring
  have hdvd : (p : ℤ) ∣ conjugate g (x : OnePoint (ZMod p)) (affineMap g x) 0 1 := by
    rw [conjugate_coe_coe]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination hcocycle
  obtain ⟨-, g', -, hmul⟩ :=
    repMatrix_mul (NeZero.ne p) g (x : OnePoint (ZMod p)) (affineMap g x) hdvd
  refine ⟨g', ?_, mapGL_mul_of_matrix (NeZero.ne p) hmul⟩
  have h10 : g' 1 0 = (p : ℤ) * g 1 0 := by
    simpa [repMatrix, Matrix.mul_apply, Fin.sum_univ_two] using (congrArg (· 1 0) hmul).symm
  refine CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_)
  show ((p * M : ℕ) : ℤ) ∣ g' 1 0
  rw [h10]
  push_cast
  exact mul_dvd_mul_left (p : ℤ) hg

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

/-- `affineMap` is the `Γ₀(p)` convenience of the general label action: on `Γ₀(p)` the denominator
of `redMatrix p g • j` is the unit `g 0 0`, whose inverse is `g 1 1`, so the image stays finite and
its coordinate is `g 1 1 * (g 0 1 + g 1 1 * j)`.  Off `Γ₀(p)` the general action must be used. -/
theorem affineMap_eq_smul_redMatrix (g : SL(2, ℤ)) (hc : ((g 1 0 : ℤ) : ZMod p) = 0)
    (j : ZMod p) :
    ((affineMap g j : ZMod p) : OnePoint (ZMod p)) = redMatrix p g • (j : OnePoint (ZMod p)) := by
  have hunit : ((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p) = 1 :=
    unit_of_apply_one_zero_eq_zero g hc
  have hne : ((g 0 0 : ℤ) : ZMod p) ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hunit
    exact zero_ne_one hunit
  rw [OnePoint.smul_some_eq_ite, redMatrix_apply_one_zero, redMatrix_apply_one_one,
    redMatrix_apply_zero_zero, redMatrix_apply_zero_one, hc, zero_mul, zero_add,
    ite_eq_right hne, affineMap_apply, OnePoint.coe_eq_coe]
  rw [eq_div_iff hne]
  calc ((g 1 1 : ℤ) : ZMod p)
        * (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j)
        * ((g 0 0 : ℤ) : ZMod p)
      = (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j)
          * (((g 0 0 : ℤ) : ZMod p) * ((g 1 1 : ℤ) : ZMod p)) := by ring
    _ = (((g 0 1 : ℤ) : ZMod p) + ((g 1 1 : ℤ) : ZMod p) * j) * 1 := by rw [hunit]
    _ = ((g 1 1 : ℤ) : ZMod p) * j + ((g 0 1 : ℤ) : ZMod p) := by ring


omit [Fact p.Prime] in
scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- The coset action sends `∞` to `∞` exactly when the lower-left entry vanishes mod `p`. -/
private theorem smul_infty_eq_infty_iff (g : SL(2, ℤ)) :
    redMatrix p g • (∞ : OnePoint (ZMod p)) = ∞ ↔ ((g 1 0 : ℤ) : ZMod p) = 0 := by
  rw [OnePoint.smul_infty_eq_ite]
  simp only [redMatrix_apply_one_zero]
  by_cases h : ((g 1 0 : ℤ) : ZMod p) = 0
  · simp [h]
  · simp [h]

/-- Otherwise the coset action sends `∞` to the point `g 0 0 / g 1 0`. -/
private theorem smul_infty_eq_coe_iff (g : SL(2, ℤ)) {k : ZMod p} :
    redMatrix p g • (∞ : OnePoint (ZMod p)) = (k : OnePoint (ZMod p)) ↔
      ((g 1 0 : ℤ) : ZMod p) ≠ 0 ∧ k = redMatrix p g 0 0 / redMatrix p g 1 0 := by
  rw [OnePoint.smul_infty_eq_ite]
  simp only [redMatrix_apply_one_zero, redMatrix_apply_zero_zero]
  by_cases h : ((g 1 0 : ℤ) : ZMod p) = 0
  · simp [h]
  · simp [h, eq_comm]

/-- The coset action sends the point `j` to `∞` exactly when the denominator vanishes. -/
private theorem smul_coe_eq_infty_iff (g : SL(2, ℤ)) (j : ZMod p) :
    redMatrix p g • (j : OnePoint (ZMod p)) = ∞ ↔
      redMatrix p g 1 0 * j + redMatrix p g 1 1 = 0 := by
  rw [OnePoint.smul_some_eq_ite]
  simp only [redMatrix_apply_one_zero, redMatrix_apply_one_one]
  by_cases h : ((g 1 0 : ℤ) : ZMod p) * j + ((g 0 0 : ℤ) : ZMod p) = 0
  · simp [h]
  · simp [h]

/-- Otherwise the coset action sends `j` to the Möbius image
`(g 1 1 * j + g 0 1) / (g 1 0 * j + g 0 0)`. -/
private theorem smul_coe_eq_coe_iff (g : SL(2, ℤ)) (j : ZMod p) {k : ZMod p} :
    redMatrix p g • (j : OnePoint (ZMod p)) = (k : OnePoint (ZMod p)) ↔
      redMatrix p g 1 0 * j + redMatrix p g 1 1 ≠ 0 ∧
        k = (redMatrix p g 0 0 * j + redMatrix p g 0 1) /
          (redMatrix p g 1 0 * j + redMatrix p g 1 1) := by
  rw [OnePoint.smul_some_eq_ite]
  simp only [redMatrix_apply_one_zero, redMatrix_apply_one_one, redMatrix_apply_zero_zero,
    redMatrix_apply_zero_one]
  by_cases h : ((g 1 0 : ℤ) : ZMod p) * j + ((g 0 0 : ℤ) : ZMod p) = 0
  · simp [h]
  · simp [h, eq_comm]

/-- The cocycle entry vanishes mod `p` once `y` is the image of `x`: the four label transitions, in
the lift the coset engine is stated for. -/
private theorem dvd_conjugate (g : SL(2, ℤ)) {x y : OnePoint (ZMod p)}
    (h : y = redMatrix p g • x) :
    (p : ℤ) ∣ conjugate g x y 0 1 := by
  simp only [conjugate]
  induction x using OnePoint.rec <;> induction y using OnePoint.rec
  case infty.infty =>
    change (p : ℤ) ∣ conjugate g (∞ : OnePoint (ZMod p)) ∞ 0 1
    have h0 := (smul_infty_eq_infty_iff g).mp h.symm
    rw [conjugate_infty_infty]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  case infty.coe =>
    rename_i k
    change (p : ℤ) ∣ conjugate g (∞ : OnePoint (ZMod p)) (k : OnePoint (ZMod p)) 0 1
    obtain ⟨h0, hk⟩ := (smul_infty_eq_coe_iff g).mp h.symm
    rw [conjugate_infty_coe]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [ZMod.natCast_zmod_val, hk, redMatrix_apply_zero_zero, redMatrix_apply_one_zero,
      mul_neg, mul_div_cancel₀ _ h0, neg_add_cancel]
  case coe.infty =>
    rename_i j
    change (p : ℤ) ∣ conjugate g (j : OnePoint (ZMod p)) ∞ 0 1
    have hden := (smul_coe_eq_infty_iff g j).mp h.symm
    rw [redMatrix_apply_one_zero, redMatrix_apply_one_one] at hden
    rw [conjugate_coe_infty]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [ZMod.natCast_zmod_val]
    linear_combination hden
  case coe.coe =>
    rename_i j k
    change (p : ℤ) ∣ conjugate g (j : OnePoint (ZMod p)) (k : OnePoint (ZMod p)) 0 1
    obtain ⟨hden, hk⟩ := (smul_coe_eq_coe_iff g j).mp h.symm
    rw [conjugate_coe_coe]
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      show ((g 0 0 : ℤ) : ZMod p) + j * ((g 1 0 : ℤ) : ZMod p)
        = redMatrix p g 1 0 * j + redMatrix p g 1 1 by
          rw [redMatrix_apply_one_zero, redMatrix_apply_one_one]; ring,
      hk, neg_mul, div_mul_cancel₀ _ hden, redMatrix_apply_zero_zero, redMatrix_apply_zero_one]
    ring

namespace Gamma1Hecke

set_option backward.isDefEq.respectTransparency.types false in
/-- **The coset action with the level and the weight.**  `heckeRep p x` conjugated past
`g ∈ Γ₀(N)` is `heckeRep p` of the moved label `redMatrix p g • x`, up to an integral `g'` — the
witness of `repMatrix_mul`, whose cocycle is divisible by `p` because the label is the image
(`dvd_conjugate`).  The two facts the nebentypus needs are the `1 0` and `1 1` entries of that
coset identity: the representative carries `p` on its diagonal exactly once (`1 1` times the weight
is `p`), the weight is its `0 0` entry, and the two labels' weights are units — so both facts are
cancellations of units, with no case analysis over labels. -/
theorem heckeRep_mul {N : ℕ} (hpN : ¬ p ∣ N) (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N)
    (x : OnePoint (ZMod p)) :
    ∃ g' : SL(2, ℤ), (N : ℤ) ∣ g' 1 0 ∧
      ((g' 1 1 : ℤ) : ZMod N) * wt N p x = ((g 1 1 : ℤ) : ZMod N) * wt N p (redMatrix p g • x) ∧
      heckeRep p x * mapGL ℝ g = mapGL ℝ g' * heckeRep p (redMatrix p g • x) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hg0 : ((g 1 0 : ℤ) : ZMod N) = 0 := by simpa using CongruenceSubgroup.Gamma0_mem.mp hg
  have hpU : IsUnit (p : ZMod N) := ZMod.isUnit_prime_of_not_dvd Fact.out hpN
  obtain ⟨c, hc⟩ := dvd_conjugate (p := p) g (y := redMatrix p g • x) rfl
  obtain ⟨-, g', -, hmul⟩ := repMatrix_mul hp g x (redMatrix p g • x) ⟨c, hc⟩
  set wx := wt N p x
  set wy := wt N p (redMatrix p g • x)
  have hyU : IsUnit wy := isUnit_wt hpN _
  have h1 : ((repMatrix p x 1 1 : ℤ) : ZMod N) * wx = (p : ZMod N) :=
    cast_repMatrix_apply_one_one_mul N x
  have h2 : ((repMatrix p (redMatrix p g • x) 1 1 : ℤ) : ZMod N) * wy = (p : ZMod N) :=
    cast_repMatrix_apply_one_one_mul N _
  have hlev : ((g' 1 0 : ℤ) : ZMod N) = 0 := by
    have hentry : (repMatrix p x 1 1 : ℤ) * g 1 0
        = g' 1 0 * repMatrix p (redMatrix p g • x) 0 0 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 0) hmul
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, repMatrix_apply_one_zero, zero_mul,
        zero_add, mul_zero, add_zero] using this
    have hcast : ((repMatrix p x 1 1 : ℤ) : ZMod N) * ((g 1 0 : ℤ) : ZMod N)
        = ((g' 1 0 : ℤ) : ZMod N) * wy := by
      have h := congrArg (fun z : ℤ => (z : ZMod N)) hentry
      rw [Int.cast_mul, Int.cast_mul] at h
      rwa [cast_repMatrix_apply_zero_zero] at h
    rw [hg0, mul_zero] at hcast
    exact eq_zero_of_mul_eq_zero_of_isUnit hyU hcast.symm
  have hwt : ((g' 1 1 : ℤ) : ZMod N) * wx = ((g 1 1 : ℤ) : ZMod N) * wy := by
    have hentry : (repMatrix p x 1 1 : ℤ) * g 1 1
        = g' 1 0 * repMatrix p (redMatrix p g • x) 0 1
          + g' 1 1 * repMatrix p (redMatrix p g • x) 1 1 := by
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M 1 1) hmul
      simpa only [Matrix.mul_apply, Fin.sum_univ_two, repMatrix_apply_one_zero, zero_mul,
        zero_add, mul_zero, add_zero] using this
    have hcast : ((repMatrix p x 1 1 : ℤ) : ZMod N) * ((g 1 1 : ℤ) : ZMod N)
        = ((g' 1 0 : ℤ) : ZMod N) * ((repMatrix p (redMatrix p g • x) 0 1 : ℤ) : ZMod N)
          + ((g' 1 1 : ℤ) : ZMod N)
            * ((repMatrix p (redMatrix p g • x) 1 1 : ℤ) : ZMod N) := by
      have h := congrArg (fun z : ℤ => (z : ZMod N)) hentry
      rw [Int.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_mul] at h
      exact h
    rw [hlev, zero_mul, zero_add] at hcast
    refine (eq_of_mul_eq_mul_of_isUnit hpU ?_).symm
    calc (p : ZMod N) * (((g 1 1 : ℤ) : ZMod N) * wy)
        = (((repMatrix p x 1 1 : ℤ) : ZMod N) * wx)
            * (((g 1 1 : ℤ) : ZMod N) * wy) := by rw [← h1]
      _ = (((repMatrix p x 1 1 : ℤ) : ZMod N) * ((g 1 1 : ℤ) : ZMod N))
            * (wx * wy) := by ring
      _ = (((g' 1 1 : ℤ) : ZMod N)
            * ((repMatrix p (redMatrix p g • x) 1 1 : ℤ) : ZMod N)) * (wx * wy) := by
          rw [hcast]
      _ = (((g' 1 1 : ℤ) : ZMod N) * wx)
            * (((repMatrix p (redMatrix p g • x) 1 1 : ℤ) : ZMod N) * wy) := by ring
      _ = (((g' 1 1 : ℤ) : ZMod N) * wx) * (p : ZMod N) := by rw [h2]
      _ = (p : ZMod N) * (((g' 1 1 : ℤ) : ZMod N) * wx) := by ring
  refine ⟨g', ?_, hwt, mapGL_mul_of_matrix hp hmul⟩
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hlev

end Gamma1Hecke

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
