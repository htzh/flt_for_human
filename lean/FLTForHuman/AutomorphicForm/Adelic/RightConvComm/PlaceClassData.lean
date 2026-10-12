/-
  The place-class datum of the archimedean anti-involution.

  For each real or complex place `w` of a number field `F`, `placeDatum` produces a
  determinant-one row-isometry matrix `k` conjugating a `2 × 2` matrix `g` over the
  completion `w.Completion` into the `thetaMat (placeSign w)` normal form (the real
  orthogonal and the complex special-unitary normal form assembled from the round-1
  `RotationConjugacy`/`HalfTurnConjugacy`/`HalfTurnAxis` normal forms). Transport along
  the completion ring equivalences (`exists_datum_of_transport`) and assembly over all
  places (`exists_mem_closure_thetaArch_eq`) give the `thetaArch` anti-involution of the
  archimedean adèles; `convKer_comm_of_place_invariant` is the kernel identity for
  functions invariant under every row-isometry subgroup, via the round-1
  `AntiInvolutionHaar.convKer_comm`.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean:1594–2062`
  (byte-identical in the compact silo at `:1547–2015`), pinned `aa2d8b3`. The
  declarations are `private` at the pin and land here public as the shared engine; the
  statements are verbatim.
-/
import FLTForHuman.RepTheory.AntiInvolutionHaar
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightChar
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightCharTransport
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import Mathlib.Tactic

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering


open scoped BigOperators

noncomputable section

namespace PlaceClassData

open Matrix

def RowForm {K : Type*} [NormedField K] (k : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ x y : K, ‖x * k 0 0 + y * k 1 0‖ ^ 2 + ‖x * k 0 1 + y * k 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2

def wmat {K : Type*} [Ring K] (ε : K) : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, ε]

def thetaMat {K : Type*} [Ring K] (ε : K) (g : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  wmat ε * g.transpose * wmat ε

theorem wmat_one {K : Type*} [Ring K] : wmat (1 : K) = 1 := by
  rw [Matrix.one_fin_two]
  rfl

theorem thetaMat_one {K : Type*} [Ring K] (g : Matrix (Fin 2) (Fin 2) K) : thetaMat 1 g = g.transpose := by
  rw [thetaMat, wmat_one, Matrix.one_mul, Matrix.mul_one]

theorem rowForm_of_mul_transpose_eq_one (k : Matrix (Fin 2) (Fin 2) ℝ) (hk : k * k.transpose = 1) :
    RowForm k := by
  have h00 := congrFun (congrFun hk 0) 0
  have h01 := congrFun (congrFun hk 0) 1
  have h11 := congrFun (congrFun hk 1) 1
  rw [Matrix.one_apply_eq] at h00 h11
  rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at h01
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] at h00 h01 h11
  intro x y
  simp only [Real.norm_eq_abs, sq_abs]
  linear_combination x ^ 2 * h00 + 2 * x * y * h01 + y ^ 2 * h11

theorem rowForm_of_mul_conjTranspose_eq_one (v : Matrix (Fin 2) (Fin 2) ℂ) (hv : v * v.conjTranspose = 1) :
    RowForm v := by
  have h00 := congrFun (congrFun hv 0) 0
  have h01 := congrFun (congrFun hv 0) 1
  have h10 := congrFun (congrFun hv 1) 0
  have h11 := congrFun (congrFun hv 1) 1
  rw [Matrix.one_apply_eq] at h00 h11
  rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at h01
  rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at h10
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at h00 h01 h10 h11
  intro x y
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  apply Complex.ofReal_injective
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_conj_mul_self]
  simp only [map_add, map_mul, starRingEnd_apply]
  linear_combination (x * star x) * h00 + (y * star y) * h11 + (x * star y) * h01 + (y * star x) * h10

theorem mul_eq_thetaMat_mul_of_real (g k : Matrix (Fin 2) (Fin 2) ℝ) (hk : k.transpose * k = 1)
    (hconj : k * g * k.transpose = thetaMat (-1) g) : k * g = thetaMat (-1) g * k := by
  calc k * g = k * g * (k.transpose * k) := by rw [hk, Matrix.mul_one]
    _ = k * g * k.transpose * k := by rw [Matrix.mul_assoc (k * g)]
    _ = thetaMat (-1) g * k := by rw [hconj]

theorem mul_eq_thetaMat_mul_of_complex (g v : Matrix (Fin 2) (Fin 2) ℂ) (hv : v * v.conjTranspose = 1)
    (hconj : v * g * v.conjTranspose = g.transpose) : v * g = thetaMat 1 g * v := by
  have hv' : v.conjTranspose * v = 1 := mul_eq_one_comm.mp hv
  rw [thetaMat_one]
  calc v * g = v * g * (v.conjTranspose * v) := by rw [hv', Matrix.mul_one]
    _ = v * g * v.conjTranspose * v := by rw [Matrix.mul_assoc (v * g)]
    _ = g.transpose * v := by rw [hconj]

section Transport

variable {K L : Type*} [NormedField K] [NormedField L]

theorem rowForm_mapMatrix_symm (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) {k' : Matrix (Fin 2) (Fin 2) L}
    (hk' : RowForm k') : RowForm (e.symm.mapMatrix k') := by
  intro x y
  have h := hk' (e x) (e y)
  simp only [RingEquiv.mapMatrix_apply, Matrix.map_apply]
  rw [← he x, ← he y, ← he (x * e.symm (k' 0 0) + y * e.symm (k' 1 0)),
    ← he (x * e.symm (k' 0 1) + y * e.symm (k' 1 1))]
  simpa only [map_add, map_mul, RingEquiv.apply_symm_apply] using h

theorem det_mapMatrix_symm (e : K ≃+* L) {k' : Matrix (Fin 2) (Fin 2) L} (hk' : k'.det = 1) :
    (e.symm.mapMatrix k').det = 1 := by
  rw [RingEquiv.mapMatrix_apply, Matrix.det_fin_two]
  simp only [Matrix.map_apply]
  rw [← map_mul, ← map_mul, ← map_sub, ← Matrix.det_fin_two k', hk', map_one]

theorem mapMatrix_symm_mul_eq (e : K ≃+* L) {g t : Matrix (Fin 2) (Fin 2) K} {k' : Matrix (Fin 2) (Fin 2) L}
    (h : k' * e.mapMatrix g = e.mapMatrix t * k') : e.symm.mapMatrix k' * g = t * e.symm.mapMatrix k' := by
  have hk : e.mapMatrix (e.symm.mapMatrix k') = k' := by
    ext i j
    simp
  apply e.mapMatrix.injective
  rw [map_mul, map_mul, hk]
  exact h

theorem mapMatrix_wmat (e : K ≃+* L) (ε : K) : e.mapMatrix (wmat ε) = wmat (e ε) := by
  unfold wmat
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem mapMatrix_transpose (e : K ≃+* L) (g : Matrix (Fin 2) (Fin 2) K) :
    e.mapMatrix g.transpose = (e.mapMatrix g).transpose := by
  ext i j
  simp

theorem mapMatrix_thetaMat (e : K ≃+* L) (ε : K) (g : Matrix (Fin 2) (Fin 2) K) :
    e.mapMatrix (thetaMat ε g) = thetaMat (e ε) (e.mapMatrix g) := by
  unfold thetaMat
  rw [map_mul, map_mul, mapMatrix_wmat, mapMatrix_transpose]

theorem exists_datum_of_transport (e : K ≃+* L) (he : ∀ x : K, ‖e x‖ = ‖x‖) (ε : K)
    (H : ∀ g' : Matrix (Fin 2) (Fin 2) L, ∃ k' : Matrix (Fin 2) (Fin 2) L,
      k'.det = 1 ∧ RowForm k' ∧ k' * g' = thetaMat (e ε) g' * k')
    (g : Matrix (Fin 2) (Fin 2) K) :
    ∃ k : Matrix (Fin 2) (Fin 2) K, k.det = 1 ∧ RowForm k ∧ k * g = thetaMat ε g * k := by
  obtain ⟨k', hdet, hrow, hcomm⟩ := H (e.mapMatrix g)
  refine ⟨e.symm.mapMatrix k', det_mapMatrix_symm e hdet, rowForm_mapMatrix_symm e he hrow, ?_⟩
  apply mapMatrix_symm_mul_eq e
  rw [mapMatrix_thetaMat]
  exact hcomm

end Transport

theorem conj_invariant_of_mem_closure {G : Type*} [Group G] {α : Type*} (f : G → α) (T : Set G)
    (hT : ∀ t ∈ T, ∀ x, f (t * x * t⁻¹) = f x) :
    ∀ k ∈ Subgroup.closure T, ∀ x, f (k * x * k⁻¹) = f x := by
  intro k hk
  induction hk using Subgroup.closure_induction with
  | mem t ht => exact hT t ht
  | one => intro x; simp
  | mul a b _ _ ha hb =>
    intro x
    have h1 : a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
    rw [h1, ha, hb]
  | inv a _ ha =>
    intro x
    have h1 := ha (a⁻¹ * x * a)
    have h2 : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
    rw [h2] at h1
    rw [inv_inv]
    exact h1.symm

section ThetaUnit

variable {R : Type*} [CommRing R]

omit [CommRing R] in
theorem transpose_fin_two_lit (a b c d : R) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R).transpose = !![a, c; b, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem thetaMat_eq (ε : R) (g : Matrix (Fin 2) (Fin 2) R) :
    thetaMat ε g = !![g 0 0, ε * g 1 0; ε * g 0 1, ε * ε * g 1 1] := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : R, g = !![a, b; c, d] :=
    ⟨g 0 0, g 0 1, g 1 0, g 1 1, Matrix.eta_fin_two g⟩
  unfold thetaMat wmat
  rw [transpose_fin_two_lit]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem wmat_mul_wmat (ε : R) (hε : ε * ε = 1) : wmat ε * wmat ε = 1 := by
  unfold wmat
  rw [Matrix.one_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hε]

theorem thetaMat_mul (ε : R) (hε : ε * ε = 1) (a b : Matrix (Fin 2) (Fin 2) R) :
    thetaMat ε a * thetaMat ε b = thetaMat ε (b * a) := by
  unfold thetaMat
  rw [Matrix.transpose_mul]
  calc wmat ε * a.transpose * wmat ε * (wmat ε * b.transpose * wmat ε)
      = wmat ε * a.transpose * (wmat ε * wmat ε) * b.transpose * wmat ε := by
        simp only [Matrix.mul_assoc]
    _ = wmat ε * (a.transpose * b.transpose) * wmat ε := by
        rw [wmat_mul_wmat ε hε, Matrix.mul_one, Matrix.mul_assoc (wmat ε)]

theorem thetaMat_one_matrix (ε : R) (hε : ε * ε = 1) : thetaMat ε (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  rw [thetaMat, Matrix.transpose_one, Matrix.mul_one, wmat_mul_wmat ε hε]

def thetaGL (ε : R) (hε : ε * ε = 1) (g : GL (Fin 2) R) : GL (Fin 2) R where
  val := thetaMat ε (g : Matrix (Fin 2) (Fin 2) R)
  inv := thetaMat ε ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
  val_inv := by
    rw [thetaMat_mul ε hε, ← Units.val_mul, inv_mul_cancel, Units.val_one, thetaMat_one_matrix ε hε]
  inv_val := by
    rw [thetaMat_mul ε hε, ← Units.val_mul, mul_inv_cancel, Units.val_one, thetaMat_one_matrix ε hε]

theorem thetaGL_val (ε : R) (hε : ε * ε = 1) (g : GL (Fin 2) R) :
    ((thetaGL ε hε g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = thetaMat ε (g : Matrix (Fin 2) (Fin 2) R) :=
  rfl

end ThetaUnit

section Facts

variable {R : Type*} [CommRing R]

theorem thetaGL_mul (ε : R) (hε : ε * ε = 1) (x y : GL (Fin 2) R) :
    thetaGL ε hε (x * y) = thetaGL ε hε y * thetaGL ε hε x := by
  apply Units.ext
  rw [Units.val_mul, thetaGL_val, thetaGL_val, thetaGL_val, thetaMat_mul ε hε, Units.val_mul]

theorem thetaMat_thetaMat (ε : R) (hε : ε * ε = 1) (g : Matrix (Fin 2) (Fin 2) R) :
    thetaMat ε (thetaMat ε g) = g := by
  rw [thetaMat_eq, thetaMat_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← mul_assoc, hε]

theorem thetaGL_thetaGL (ε : R) (hε : ε * ε = 1) (x : GL (Fin 2) R) : thetaGL ε hε (thetaGL ε hε x) = x := by
  apply Units.ext
  rw [thetaGL_val, thetaGL_val, thetaMat_thetaMat ε hε]

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_thetaMat (ε : R) :
    Continuous (thetaMat ε : Matrix (Fin 2) (Fin 2) R → Matrix (Fin 2) (Fin 2) R) :=
  (continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const

theorem continuous_thetaGL (ε : R) (hε : ε * ε = 1) :
    Continuous (thetaGL ε hε : GL (Fin 2) R → GL (Fin 2) R) :=
  Units.continuous_iff.mpr
    ⟨(continuous_thetaMat ε).comp Units.continuous_val, (continuous_thetaMat ε).comp Units.continuous_coe_inv⟩

end Facts

theorem exists_special_unitary_mul_mul_conjTranspose_eq_transpose (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ v : Matrix (Fin 2) (Fin 2) ℂ, v * v.conjTranspose = 1 ∧ v.det = 1 ∧ v * g * v.conjTranspose = g.transpose := by
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℂ, g = !![a, b; c, d] :=
    ⟨g 0 0, g 0 1, g 1 0, g 1 1, Matrix.eta_fin_two g⟩
  obtain ⟨n₁, n₂, n₃, hn, horth⟩ := HalfTurnAxis.exists_axis a b c d
  exact HalfTurnConjugacy.exists_special_unitary_mul_mul_conjTranspose_eq_transpose_of_axis a b c d n₁ n₂ n₃ hn horth

theorem realDatum (g : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ k : Matrix (Fin 2) (Fin 2) ℝ, k.det = 1 ∧ RowForm k ∧ k * g = thetaMat (-1) g * k := by
  obtain ⟨k, hk, hdet, hconj⟩ := RotationConjugacy.exists_rotation_mul_mul_transpose_eq g
  exact ⟨k, hdet, rowForm_of_mul_transpose_eq_one k (mul_eq_one_comm.mp hk),
    mul_eq_thetaMat_mul_of_real g k hk hconj⟩

theorem complexDatum (g : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ k : Matrix (Fin 2) (Fin 2) ℂ, k.det = 1 ∧ RowForm k ∧ k * g = thetaMat 1 g * k := by
  obtain ⟨v, hv, hdet, hconj⟩ := exists_special_unitary_mul_mul_conjTranspose_eq_transpose g
  exact ⟨v, hdet, rowForm_of_mul_conjTranspose_eq_one v hv, mul_eq_thetaMat_mul_of_complex g v hv hconj⟩

section PlaceSign

open NumberField

variable {F : Type*} [Field F]

open scoped Classical in

noncomputable def placeSign (w : InfinitePlace F) : w.Completion := if w.IsReal then -1 else 1

theorem placeSign_mul_self (w : InfinitePlace F) : placeSign w * placeSign w = 1 := by
  unfold placeSign
  split_ifs <;> simp

theorem placeSign_of_isReal {w : InfinitePlace F} (hw : w.IsReal) : placeSign w = -1 := by
  simp [placeSign, hw]

theorem placeSign_of_not_isReal {w : InfinitePlace F} (hw : ¬ w.IsReal) : placeSign w = 1 := by
  simp [placeSign, hw]

end PlaceSign

section NumberField

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type*} [Field F]

theorem placeDatum (w : InfinitePlace F) (g : Matrix (Fin 2) (Fin 2) w.Completion) :
    ∃ k : Matrix (Fin 2) (Fin 2) w.Completion, k.det = 1 ∧ RowForm k ∧ k * g = thetaMat (placeSign w) g * k := by
  by_cases hw : w.IsReal
  · have he : ∀ x : w.Completion, ‖ringEquivRealOfIsReal hw x‖ = ‖x‖ := fun x => by
      rw [ringEquivRealOfIsReal_apply]
      exact (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x
    refine exists_datum_of_transport (ringEquivRealOfIsReal hw) he (placeSign w) ?_ g
    rw [placeSign_of_isReal hw, map_neg, map_one]
    exact realDatum
  · have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    have he : ∀ x : w.Completion, ‖ringEquivComplexOfIsComplex hw' x‖ = ‖x‖ := fun x => by
      rw [ringEquivComplexOfIsComplex_apply]
      exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
    refine exists_datum_of_transport (ringEquivComplexOfIsComplex hw') he (placeSign w) ?_ g
    rw [placeSign_of_not_isReal hw, map_one]
    exact complexDatum

end NumberField

end PlaceClassData

open NumberField AutomorphicForm Matrix

namespace PlaceClassData

section Place

variable {K : Type*} [NormedField K]

theorem exists_mem_rowIsometrySubgroup₀_thetaGL_eq (ε : K) (hε : ε * ε = 1)
    (H : ∀ g : Matrix (Fin 2) (Fin 2) K, ∃ k : Matrix (Fin 2) (Fin 2) K,
      k.det = 1 ∧ RowForm k ∧ k * g = thetaMat ε g * k)
    (g : GL (Fin 2) K) :
    ∃ k ∈ rowIsometrySubgroup₀ K, thetaGL ε hε g = k * g * k⁻¹ := by
  obtain ⟨k, hdet, hrow, hcomm⟩ := H (g : Matrix (Fin 2) (Fin 2) K)
  have hk0 : k.det ≠ 0 := by
    rw [hdet]
    exact one_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero k hk0, ?_, ?_⟩
  · rw [mem_rowIsometrySubgroup₀_iff]
    refine ⟨hdet, ?_, fun x y => hrow x y⟩
    show ‖k.det‖ = 1
    rw [hdet, norm_one]
  · rw [eq_mul_inv_iff_mul_eq]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, thetaGL_val]
    exact hcomm.symm

end Place

section Assembly

variable (F : Type) [Field F] [NumberField F]

noncomputable def archSign : InfiniteAdeleRing F := fun w => placeSign w

omit [NumberField F] in
theorem archSign_mul_self : archSign F * archSign F = 1 := by
  funext w
  exact placeSign_mul_self w

noncomputable def thetaArch (x : GL (Fin 2) (InfiniteAdeleRing F)) : GL (Fin 2) (InfiniteAdeleRing F) :=
  thetaGL (archSign F) (archSign_mul_self F) x

omit [NumberField F] in
theorem thetaArch_val (x : GL (Fin 2) (InfiniteAdeleRing F)) :
    ((thetaArch F x : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) =
      thetaMat (archSign F) (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  rfl

omit [NumberField F] in

theorem archComponent_thetaArch (w : InfinitePlace F) (x : GL (Fin 2) (InfiniteAdeleRing F)) :
    AdelicLevel.archComponent F w (thetaArch F x) =
      thetaGL (placeSign w) (placeSign_mul_self w) (AdelicLevel.archComponent F w x) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [AdelicLevel.archComponent_apply, thetaArch_val, thetaGL_val, thetaMat_eq, thetaMat_eq]
  fin_cases i <;> fin_cases j <;> rfl

omit [NumberField F] in

theorem archComponent_ext {a b : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, AdelicLevel.archComponent F w a = AdelicLevel.archComponent F w b) : a = b := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  funext w
  rw [← AdelicLevel.archComponent_apply (K := F) w a i j, ← AdelicLevel.archComponent_apply (K := F) w b i j, h w]

open scoped Classical in
omit [NumberField F] in

theorem archComponent_noncommProd (kv : ∀ w : InfinitePlace F, GL (Fin 2) w.Completion)
    (s : Finset (InfinitePlace F))
    (comm : (s : Set (InfinitePlace F)).Pairwise (Function.onFun Commute fun w => archGLIncl F w (kv w)))
    (u : InfinitePlace F) :
    AdelicLevel.archComponent F u (s.noncommProd (fun w => archGLIncl F w (kv w)) comm) =
      if u ∈ s then kv u else 1 := by
  revert comm
  refine Finset.induction_on s ?_ ?_
  · intro comm
    rw [Finset.noncommProd_empty, map_one, ite_eq_right (Finset.notMem_empty u)]
  · intro a s ha ih comm
    rw [Finset.noncommProd_insert_of_notMem s a _ comm ha, map_mul, ih]
    by_cases hu : u = a
    · subst hu
      simp [archComponent_archGLIncl_self, ha]
    · simp [archComponent_archGLIncl_of_ne (F := F) hu, hu]

theorem exists_mem_closure_thetaArch_eq
    (hmat : ∀ (w : InfinitePlace F) (g : Matrix (Fin 2) (Fin 2) w.Completion),
      ∃ k : Matrix (Fin 2) (Fin 2) w.Completion, k.det = 1 ∧ RowForm k ∧ k * g = thetaMat (placeSign w) g * k)
    (x : GL (Fin 2) (InfiniteAdeleRing F)) :
    ∃ k ∈ Subgroup.closure (⋃ w : InfinitePlace F, Set.range (archRowIsometryInclAt₀ F w)),
      thetaArch F x = k * x * k⁻¹ := by
  have hplace : ∀ w : InfinitePlace F, ∃ k ∈ rowIsometrySubgroup₀ w.Completion,
      thetaGL (placeSign w) (placeSign_mul_self w) (AdelicLevel.archComponent F w x) =
        k * AdelicLevel.archComponent F w x * k⁻¹ :=
    fun w => exists_mem_rowIsometrySubgroup₀_thetaGL_eq (placeSign w) (placeSign_mul_self w) (hmat w)
      (AdelicLevel.archComponent F w x)
  choose kv hkv_mem hkv_eq using hplace
  have hc : ∀ v w : InfinitePlace F, Commute (archGLIncl F v (kv v)) (archGLIncl F w (kv w)) := by
    intro v w
    by_cases hvw : v = w
    · subst hvw
      exact Commute.refl _
    · exact commute_archGLIncl_of_ne (F := F) hvw _ _
  have comm : ((Finset.univ : Finset (InfinitePlace F)) : Set (InfinitePlace F)).Pairwise
      (Function.onFun Commute fun w => archGLIncl F w (kv w)) :=
    fun v _ w _ _ => hc v w
  refine ⟨Finset.univ.noncommProd (fun w => archGLIncl F w (kv w)) comm, ?_, ?_⟩
  · refine Subgroup.noncommProd_mem _ comm (fun w _ => Subgroup.subset_closure ?_)
    exact Set.mem_iUnion.mpr ⟨w, ⟨⟨kv w, hkv_mem w⟩, rfl⟩⟩
  · apply archComponent_ext F
    intro u
    rw [archComponent_thetaArch, map_mul, map_mul, map_inv, archComponent_noncommProd, ite_eq_left (Finset.mem_univ u)]
    exact hkv_eq u

end Assembly

section ArchInvolution

open AntiInvolutionHaar MeasureTheory

variable (F : Type) [Field F] [NumberField F]

noncomputable def archAntiInvolution : AntiInvolution (GL (Fin 2) (InfiniteAdeleRing F)) where
  θ := thetaArch F
  continuous := continuous_thetaGL (archSign F) (archSign_mul_self F)
  anti := thetaGL_mul (archSign F) (archSign_mul_self F)
  invol := thetaGL_thetaGL (archSign F) (archSign_mul_self F)

omit [NumberField F] in
theorem archAntiInvolution_θ (x : GL (Fin 2) (InfiniteAdeleRing F)) :
    (archAntiInvolution F).θ x = thetaArch F x :=
  rfl

def archIsometryImages : Set (GL (Fin 2) (InfiniteAdeleRing F)) :=
  ⋃ w : InfinitePlace F, Set.range (archRowIsometryInclAt₀ F w)

theorem exists_mem_closure_archIsometryImages (x : GL (Fin 2) (InfiniteAdeleRing F)) :
    ∃ k ∈ Subgroup.closure (archIsometryImages F), thetaArch F x = k * x * k⁻¹ :=
  exists_mem_closure_thetaArch_eq F placeDatum x

omit [NumberField F] in
theorem conj_invariant_of_place_invariant (P : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hP : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      P (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = P x) :
    ∀ k ∈ Subgroup.closure (archIsometryImages F), ∀ x, P (k * x * k⁻¹) = P x := by
  refine conj_invariant_of_mem_closure P (archIsometryImages F) ?_
  intro t ht x
  rcases Set.mem_iUnion.mp ht with ⟨w, hw⟩
  rcases Set.mem_range.mp hw with ⟨k, rfl⟩
  exact hP w k x

theorem convKer_comm_of_place_invariant [MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F))]
    [BorelSpace (GL (Fin 2) (InfiniteAdeleRing F))] (ν : Measure (GL (Fin 2) (InfiniteAdeleRing F)))
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] [ν.IsInvInvariant] (hν : ν.map (thetaArch F) = ν)
    (P Q : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hP : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      P (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = P x)
    (hQ : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      Q (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = Q x) :
    convKer ν P Q = convKer ν Q P :=
  convKer_comm ν (archAntiInvolution F) hν (Subgroup.closure (archIsometryImages F) : Set _)
    (exists_mem_closure_archIsometryImages F) P Q
    (conj_invariant_of_place_invariant F P hP) (conj_invariant_of_place_invariant F Q hQ)

end ArchInvolution

end PlaceClassData

end
