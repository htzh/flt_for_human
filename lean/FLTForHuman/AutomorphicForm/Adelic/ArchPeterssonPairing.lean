/-
  The archimedean test factor and the Petersson pairing.

  Three rows of the archimedean–Petersson dictionary the smooth cusp realisation is
  stated against:

  * `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing`:
    a Hecke eigensystem whose `SmoothCuspRealizationAt` datum satisfies the listed
    Petersson pairing conditions (sesquilinearity along right translates, nondegeneracy,
    and a sesquilinear form `P` with the same invariance) has both eigenvalue sequences
    bounded by a fixed power of the absolute norm.
  * `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat`: for a
    bi-invariant finite measure on a product of row-isometry groups, a conjugation
    invariant `e` and a `σ`-flat family `h`, the double integral of `e p₁ * e p₂ * h` is
    invariant under conjugation of `h`'s argument and equals the conjugate of its inverse
    argument times the idele norm to the `-σ` power.
  * `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det`:
    a smooth compactly supported `Φ` on the archimedean entry space whose support avoids
    the singular matrices defines an archimedean test factor.

  Transcribed from the three `S_` files below (pinned `aa2d8b3`, 384 + 196 + 165 lines).

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.PeterssonIntegral
import FLTForHuman.AutomorphicForm.Adelic.HeckeEigensystem
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SmoothRealization
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSet
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs

set_option autoImplicit false

-- Heartbeat probe (work order AF83C, gate 6) — **recorded, not installed**. Playbook §3.5: no
-- module carries a `set_option maxHeartbeats` (an in-file cap is a defect marker, not a budget).
-- The number is kept here for the next reader. Bisection with `-DmaxHeartbeats=N` over the whole
-- module: *silent* at 45000 and above; timeouts at 40000 (`whnf`, the row
-- `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat`'s `hWinv` step), 30000
-- (`isDefEq`), 20000 and below. The worst declaration costs ≈45000 units — well under the edit
-- loop's 200000 — so no floor is owed.

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open IsDedekindDomain AutomorphicForm.WindowedSiegel
open scoped Classical InnerProductSpace ComplexConjugate

namespace AutomorphicForm

/-! ### The Petersson coefficient bound

The engine of the eigenvalue bound. A positive hermitian sesquilinear form satisfies
Cauchy–Schwarz in the form `‖P x y‖² ≤ (P x x).re * (P y y).re` (via the
`PreInnerProductSpace.Core` it defines on the submodule), the Petersson integral is such a
form (conjugate-symmetric with nonnegative real square), and the Hecke operators
`T_v`-eigenvalue equation `a_v · φ = ∑_i φ(· · reps_i)` bounds `‖π'.a v‖` by the number of
double cosets times the square root of the covariance eigenvalue. The central eigenvalue
`b_v` is then read off the invariance of the pairing under `scalar (ϖ_v)`.
-/

section CoefficientBoundGeneric

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Cauchy–Schwarz for a positive hermitian sesquilinear form. -/
private theorem norm_mul_self_le (P : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (W : Submodule ℂ V)
    (hherm : ∀ x ∈ W, ∀ y ∈ W, conj (P x y) = P y x)
    (hpos : ∀ x ∈ W, 0 ≤ (P x x).re)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) :
    ‖P x y‖ * ‖P x y‖ ≤ (P x x).re * (P y y).re := by
  let c : PreInnerProductSpace.Core ℂ W :=
    { inner := fun a b => P (b : V) (a : V)
      conj_inner_symm := fun a b => hherm _ a.2 _ b.2
      re_inner_nonneg := fun a => hpos _ a.2
      add_left := fun a b z => by
        change P (z : V) ((a : V) + (b : V)) = P (z : V) (a : V) + P (z : V) (b : V)
        exact map_add _ _ _
      smul_left := fun a b r => by
        change P (b : V) (r • (a : V)) = conj r * P (b : V) (a : V)
        rw [LinearMap.map_smulₛₗ, smul_eq_mul] }
  have h := @InnerProductSpace.Core.inner_mul_inner_self_le ℂ W _ _ _ c ⟨x, hx⟩ ⟨y, hy⟩
  change ‖P y x‖ * ‖P x y‖ ≤ RCLike.re (P x x) * RCLike.re (P y y) at h
  have e : ‖P y x‖ = ‖P x y‖ := by
    rw [← hherm x hx y hy]
    exact RCLike.norm_conj _
  rw [e] at h
  simpa using h

end CoefficientBoundGeneric

section CoefficientBoundMatrix

variable {A : Type*} [CommRing A]

/-- A scalar matrix is central in `GL₂`. -/
private theorem scalarMatrix_mul_comm (a : Aˣ) (g : GL (Fin 2) A) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 2) a ∈ Subgroup.center (GL (Fin 2) A) :=
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨a, rfl⟩
  exact ((Subgroup.mem_center_iff.mp hz) g).symm

/-- The determinant of a `2 × 2` scalar matrix is the square of the scalar. -/
private theorem det_scalarMatrix_two (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) a) = a * a := by
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, pow_two]

/-- The determinant of `diagOne a` is `a`. -/
private theorem det_diagOne (a : Aˣ) : Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, diagOne_coe_apply,
    diagOne_coe_apply, diagOne_coe_apply, diagOne_coe_apply]
  simp

/-- A real number is bounded by `N` raised to its own natCeil, for `N ≥ 2`. -/
private theorem le_rpow_natCeil {N x : ℝ} (hN : 2 ≤ N) : x ≤ N ^ ((⌈x⌉₊ : ℕ) : ℝ) := by
  rw [Real.rpow_natCast]
  calc x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    _ ≤ ((2 : ℕ) ^ ⌈x⌉₊ : ℕ) := by exact_mod_cast (Nat.lt_two_pow_self).le
    _ = (2 : ℝ) ^ ⌈x⌉₊ := by push_cast; ring
    _ ≤ N ^ ⌈x⌉₊ := pow_le_pow_left₀ (by norm_num) hN _

end CoefficientBoundMatrix

-- The pin's local Borel instance on `GL₂(𝔸)`: `peterssonIntegral` is defined against it, so
-- the unfolded form `peterssonIntegral_eq_integral` is a `rfl` only with it in scope.
attribute [local instance] NumberField.AdelicHaar.glBorel

section CoefficientBoundPairing

variable (F : Type) [Field F] [NumberField F]

/-- The Petersson integral, unfolded. -/
private theorem peterssonIntegral_eq_integral (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F))
    (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F s S x y =
      ∫ w in S, x w * conj (y w) *
        ((ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (-s) : ℝ) : ℂ)
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := rfl

/-- The Petersson integral is conjugate-symmetric. -/
private theorem peterssonIntegral_conj (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F))
    (x y : AdelicGL2 (𝓞 F) F → ℂ) :
    conj (peterssonIntegral F s S x y) = peterssonIntegral F s S y x := by
  rw [peterssonIntegral_eq_integral, peterssonIntegral_eq_integral, ← integral_conj]
  congr 1
  funext w
  rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- The Petersson square is the integral of the squared modulus. -/
private theorem peterssonIntegral_self (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    peterssonIntegral F s S f f =
      ((∫ w in S, ‖f w‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (-s)
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ) := by
  rw [peterssonIntegral_eq_integral]
  have h : ∀ w : AdelicGL2 (𝓞 F) F,
      f w * conj (f w) * ((ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (-s) : ℝ) : ℂ) =
        ((‖f w‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (-s) : ℝ) : ℂ) := fun w => by
    rw [Complex.mul_conj, Complex.ofReal_mul, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [h]
  exact integral_ofReal

/-- The Petersson square has nonnegative real part. -/
private theorem peterssonIntegral_self_re_nonneg (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) :
    0 ≤ (peterssonIntegral F s S f f).re := by
  rw [peterssonIntegral_self, Complex.ofReal_re]
  exact integral_nonneg fun w =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (ideleNorm_pos _).le _)

/-- The absolute norm of a height-one prime is at least `2`. -/
private theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 F)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

end CoefficientBoundPairing

section CoefficientBoundOffExceptional

variable (F : Type) [Field F] [NumberField F]

/-- Away from the exceptional set, the Hecke eigenvalues of a smooth cusp realization
satisfying the Petersson pairing hypotheses are bounded: `‖a_v‖ ≤ (N + 1) N^{-s/2}` and
`‖b_v‖ = N^{-s}`, `N` the absolute norm of `v`. -/
private theorem bounds_of_not_mem_exceptionalSet
    (pins : CarrierPins F) (Φ : HeckeEigensystem F ℂ) (R' : SmoothCuspRealizationAt F pins Φ) (s : ℝ)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hPcov : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      P (fun z => x (z * g)) (fun z => y (z * g)) =
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y)
    (hherm : ∀ x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      ∀ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      conj (P x y) = P y x)
    (hpos : ∀ x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      0 ≤ (P x x).re)
    (hne : P R'.toFun R'.toFun ≠ 0)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R'.exceptionalSet)
    (hgen : pins.gen v = diagOne (uniformizerIdele F v))
    (hnormv : ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) :
    ‖Φ.a v‖ ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 1) *
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s / 2) ∧
    ‖Φ.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s) := by

  have memV : ∀ h : AdelicGL2 (𝓞 F) F, (fun z => R'.toFun (z * h)) ∈
      Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) :=
    fun h => Submodule.subset_span ⟨h, rfl⟩
  have fmem : R'.toFun ∈
      Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) := by
    simpa using memV 1

  set N : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) with hN
  have hN2 : 2 ≤ N := by
    rw [hN]
    exact_mod_cast two_le_absNorm F v
  have hNpos : 0 < N := by linarith

  have hreal : (((P R'.toFun R'.toFun).re : ℝ) : ℂ) = P R'.toFun R'.toFun :=
    Complex.conj_eq_iff_re.mp (hherm _ fmem _ fmem)
  have hc₀pos : 0 < (P R'.toFun R'.toFun).re := by
    rcases (hpos _ fmem).eq_or_lt with h | h
    · exact absurd (by rw [← hreal, ← h, Complex.ofReal_zero]) hne
    · exact h
  have hnormff : ‖P R'.toFun R'.toFun‖ = (P R'.toFun R'.toFun).re := by
    rw [← hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc₀pos, Complex.ofReal_re]

  have hcovff : ∀ g : AdelicGL2 (𝓞 F) F,
      P (fun z => R'.toFun (z * g)) (fun z => R'.toFun (z * g)) =
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P R'.toFun R'.toFun :=
    fun g => hPcov g _ _ fmem fmem

  have hlev : ∀ w ∈ pins.U Φ.level, ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ s = 1 := by
    intro w hw
    have hfun : (fun z => R'.toFun (z * w)) = R'.toFun := funext fun z => R'.level_invariant z w hw
    have h := hcovff w
    rw [hfun] at h
    have h2 : ((ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ s : ℝ) : ℂ) = 1 :=
      (mul_right_cancel₀ hne (h.symm.trans (one_mul _).symm))
    exact_mod_cast h2

  obtain ⟨reps, hsys, heig⟩ := R'.hecke_eigen v hv

  have hdet_reps : ∀ i, ideleNorm F (Matrix.GeneralLinearGroup.det (reps i)) ^ s = N ^ (-s) := by
    intro i
    obtain ⟨u₁, hu₁, u₂, hu₂, heq⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    have e1 : Matrix.GeneralLinearGroup.det (reps i) =
        Matrix.GeneralLinearGroup.det u₁ * uniformizerIdele F v *
          Matrix.GeneralLinearGroup.det u₂ := by
      rw [← heq, map_mul, map_mul, hgen, det_diagOne]
    rw [e1, ideleNorm_mul, ideleNorm_mul,
      Real.mul_rpow (mul_nonneg (ideleNorm_pos _).le (ideleNorm_pos _).le) (ideleNorm_pos _).le,
      Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, hlev u₁ hu₁, hlev u₂ hu₂, one_mul,
      mul_one, hnormv, Real.inv_rpow hNpos.le, Real.rpow_neg hNpos.le]

  have hsum : (∑ i, fun z => R'.toFun (z * reps i)) = Φ.a v • R'.toFun := by
    funext z
    rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact heig z
  have hPsum : Φ.a v * P R'.toFun R'.toFun = ∑ i, P (fun z => R'.toFun (z * reps i)) R'.toFun := by
    have h := congrArg (fun x => P x R'.toFun) hsum
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h
    exact h.symm

  have hterm : ∀ i, ‖P (fun z => R'.toFun (z * reps i)) R'.toFun‖ ≤
      N ^ (-s / 2) * (P R'.toFun R'.toFun).re := by
    intro i
    have hcs := norm_mul_self_le P _ hherm hpos (memV (reps i)) fmem
    have huu : (P (fun z => R'.toFun (z * reps i))
        (fun z => R'.toFun (z * reps i))).re = N ^ (-s) * (P R'.toFun R'.toFun).re := by
      rw [hcovff (reps i), hdet_reps i, Complex.re_ofReal_mul]
    rw [huu] at hcs
    have hb : 0 ≤ N ^ (-s / 2) * (P R'.toFun R'.toFun).re :=
      mul_nonneg (Real.rpow_nonneg hNpos.le _) hc₀pos.le
    have hhalf : N ^ (-s / 2) * N ^ (-s / 2) = N ^ (-s) := by
      rw [← Real.rpow_add hNpos]
      ring_nf
    have hsq : ‖P (fun z => R'.toFun (z * reps i)) R'.toFun‖ *
          ‖P (fun z => R'.toFun (z * reps i)) R'.toFun‖ ≤
        (N ^ (-s / 2) * (P R'.toFun R'.toFun).re) *
          (N ^ (-s / 2) * (P R'.toFun R'.toFun).re) := by
      calc _ ≤ N ^ (-s) * (P R'.toFun R'.toFun).re * (P R'.toFun R'.toFun).re := hcs
        _ = (N ^ (-s / 2) * (P R'.toFun R'.toFun).re) *
            (N ^ (-s / 2) * (P R'.toFun R'.toFun).re) := by rw [← hhalf]; ring
    exact (mul_self_le_mul_self_iff (norm_nonneg _) hb).mpr hsq

  have hA : ‖Φ.a v‖ ≤ (N + 1) * N ^ (-s / 2) := by
    have h1 : ‖Φ.a v‖ * (P R'.toFun R'.toFun).re ≤
        (N + 1) * N ^ (-s / 2) * (P R'.toFun R'.toFun).re := by
      calc ‖Φ.a v‖ * (P R'.toFun R'.toFun).re = ‖Φ.a v * P R'.toFun R'.toFun‖ := by
            rw [norm_mul, hnormff]
        _ = ‖∑ i, P (fun z => R'.toFun (z * reps i)) R'.toFun‖ := by rw [hPsum]
        _ ≤ ∑ i, ‖P (fun z => R'.toFun (z * reps i)) R'.toFun‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin (Ideal.absNorm v.asIdeal + 1), N ^ (-s / 2) * (P R'.toFun R'.toFun).re :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = (N + 1) * N ^ (-s / 2) * (P R'.toFun R'.toFun).re := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hN]
          push_cast
          ring
    exact le_of_mul_le_mul_right h1 hc₀pos

  have hcen := R'.central_eigen v hv
  rw [hgen, det_diagOne] at hcen
  have hcomm : ∀ w : AdelicGL2 (𝓞 F) F,
      w * centralScalar (𝓞 F) F (uniformizerIdele F v) =
        centralScalar (𝓞 F) F (uniformizerIdele F v) * w :=
    fun w => (scalarMatrix_mul_comm _ w).symm
  have hfunz : (fun w => R'.toFun (w * centralScalar (𝓞 F) F (uniformizerIdele F v))) =
      Φ.b v • R'.toFun := by
    funext w
    rw [Pi.smul_apply, smul_eq_mul, hcomm w]
    exact hcen w
  have hdetz : Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F (uniformizerIdele F v)) =
      uniformizerIdele F v * uniformizerIdele F v := det_scalarMatrix_two _
  have hbb : ‖Φ.b v‖ * ‖Φ.b v‖ = N ^ (-s) * N ^ (-s) := by
    have h := hcovff (centralScalar (𝓞 F) F (uniformizerIdele F v))
    rw [hfunz, P.map_smul (Φ.b v) R'.toFun, LinearMap.smul_apply,
      (P R'.toFun).map_smulₛₗ (Φ.b v) R'.toFun, hdetz, ideleNorm_mul, hnormv, smul_eq_mul,
      smul_eq_mul, ← mul_assoc] at h
    have h2 : Φ.b v * conj (Φ.b v) = (((N⁻¹ * N⁻¹) ^ s : ℝ) : ℂ) := mul_right_cancel₀ hne h
    rw [Complex.mul_conj, Complex.ofReal_inj, Complex.normSq_eq_norm_sq] at h2
    rw [← pow_two, h2, Real.mul_rpow (inv_nonneg.mpr hNpos.le) (inv_nonneg.mpr hNpos.le),
      Real.inv_rpow hNpos.le, Real.rpow_neg hNpos.le]
  have hB : ‖Φ.b v‖ = N ^ (-s) := by
    have h0 : 0 ≤ N ^ (-s) := Real.rpow_nonneg hNpos.le _
    rcases mul_self_eq_mul_self_iff.mp hbb with h | h
    · exact h
    · have hz : ‖Φ.b v‖ = 0 := le_antisymm (by linarith [norm_nonneg (Φ.b v)]) (norm_nonneg _)
      linarith
  exact ⟨hA, hB⟩

end CoefficientBoundOffExceptional

theorem exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      π'.toRawCentral)
    (s : ℝ)
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hpair :
      (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
        x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
        peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
            peterssonIntegral F s S x y) ∧
      peterssonIntegral F s S R'.toFun R'.toFun ≠ 0 ∧
      (R'.centralChar = R'.centralChar →
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
          x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) ⊔
              Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
          peterssonIntegral F s S (fun z => x (z * g)) (fun z => y (z * g)) =
            ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) *
              peterssonIntegral F s S x y) ∧
        ∃ P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ,
          (∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
            x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) ⊔
                Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            P (fun z => x (z * g)) (fun z => y (z * g)) =
              ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y) ∧
          (∃ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
            P y y ≠ 0) ∧
          ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
            x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) ⊔
                Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
            P x y = peterssonIntegral F s S x y))
    (hnorm : ∀ v : HeightOneSpectrum (𝓞 F),
      ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ v : HeightOneSpectrum (𝓞 F),
      ‖π'.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖π'.b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ := by
  obtain ⟨-, hne, hP⟩ := hpair
  obtain ⟨-, P, hPcov, -, hPagree⟩ := hP rfl
  have hPcov' : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
      x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) →
      P (fun z => x (z * g)) (fun z => y (z * g)) =
        ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y :=
    fun g x y hx hy => hPcov g x y (Submodule.mem_sup_left hx) hy
  have hherm : ∀ x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      ∀ y ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      conj (P x y) = P y x := fun x hx y hy => by
    rw [hPagree x y (Submodule.mem_sup_left hx) hy, hPagree y x (Submodule.mem_sup_left hy) hx]
    exact peterssonIntegral_conj F s S x y
  have hpos : ∀ x ∈ Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)),
      0 ≤ (P x x).re := fun x hx => by
    rw [hPagree x x (Submodule.mem_sup_left hx) hx]
    exact peterssonIntegral_self_re_nonneg F s S x
  have fmem : R'.toFun ∈
      Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)) := by
    simpa using (Submodule.subset_span ⟨1, rfl⟩ :
      (fun z => R'.toFun (z * 1)) ∈
        Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h)))
  have hneP : P R'.toFun R'.toFun ≠ 0 := by
    rw [hPagree _ _ (Submodule.mem_sup_left fmem) fmem]
    exact hne

  have hoff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ R'.exceptionalSet →
      ‖π'.toRawCentral.a v‖ ≤
          (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 1) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s / 2) ∧
        ‖π'.toRawCentral.b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s) :=
    fun v hv => bounds_of_not_mem_exceptionalSet F _ _ R' s P hPcov' hherm hpos hneP v hv rfl (hnorm v)

  refine ⟨|s| + 2 + ∑ w ∈ R'.exceptionalSet, ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ),
    add_nonneg (add_nonneg (abs_nonneg s) zero_le_two) (Finset.sum_nonneg fun w _ => Nat.cast_nonneg _),
    fun v => ?_⟩
  have hN2 : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast two_le_absNorm F v
  have hN1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have hNpos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by linarith
  have hsum0 : 0 ≤ ∑ w ∈ R'.exceptionalSet, ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ) :=
    Finset.sum_nonneg fun w _ => Nat.cast_nonneg _
  by_cases hv : v ∈ R'.exceptionalSet
  ·
    have hle : ((⌈‖π'.a v‖⌉₊ + ⌈‖π'.b v‖⌉₊ : ℕ) : ℝ) ≤
        ∑ w ∈ R'.exceptionalSet, ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ) :=
      Finset.single_le_sum (f := fun w => ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ))
        (fun w _ => Nat.cast_nonneg _) hv
    push_cast at hle
    have ha0 : (0 : ℝ) ≤ ⌈‖π'.a v‖⌉₊ := Nat.cast_nonneg _
    have hb0 : (0 : ℝ) ≤ ⌈‖π'.b v‖⌉₊ := Nat.cast_nonneg _
    have hs0 := abs_nonneg s
    constructor
    · calc ‖π'.a v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((⌈‖π'.a v‖⌉₊ : ℕ) : ℝ) :=
            le_rpow_natCeil hN2
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
    · calc ‖π'.b v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((⌈‖π'.b v‖⌉₊ : ℕ) : ℝ) :=
            le_rpow_natCeil hN2
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN1 (by push_cast; linarith)
  ·
    obtain ⟨ha, hb⟩ := hoff v hv
    have hκ : |s| + 2 ≤ |s| + 2 + ∑ w ∈ R'.exceptionalSet,
        ((⌈‖π'.a w‖⌉₊ + ⌈‖π'.b w‖⌉₊ : ℕ) : ℝ) :=
      le_add_of_nonneg_right hsum0
    rw [HeckeEigensystem.toRawCentral_a] at ha
    rw [HeckeEigensystem.toRawCentral_b, norm_mul, norm_inv, HeckeEigensystem.cNorm,
      Complex.norm_natCast] at hb

    have hb' : ‖π'.b v‖ =
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s) := by
      have h := congrArg (fun t => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) * t) hb
      rwa [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul] at h
    constructor
    · refine ha.trans (le_trans ?_ (Real.rpow_le_rpow_of_exponent_le hN1 hκ))
      calc (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 1) *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s / 2)
          ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (2 : ℝ) *
              ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ |s| :=
            mul_le_mul (by rw [Real.rpow_two]; nlinarith)
              (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [neg_le_abs s, abs_nonneg s]))
              (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hNpos.le _)
        _ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (|s| + 2) := by
            rw [← Real.rpow_add hNpos]
            ring_nf
    · rw [hb']
      refine le_trans ?_ (Real.rpow_le_rpow_of_exponent_le hN1 hκ)
      calc ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s)
          = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (1 + -s) := by
            rw [Real.rpow_add hNpos, Real.rpow_one]
        _ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (|s| + 2) :=
            Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [neg_le_abs s, abs_nonneg s])

/-! ### The bi-invariant average over the archimedean row-isometry product

The archimedean half of the Petersson dictionary: for a finite bi-invariant measure on the
product of the row-isometry subgroups, a conjugation-invariant `e` and a `σ`-flat family `h`,
the double integral `∫∫ e p₁ · e p₂ · h ((ι p₁)⁻¹ · x · (ι p₂)⁻¹)` is invariant under
conjugating `x` by a single row-isometry factor, and equals the conjugate of its value at
`x⁻¹` times the idèle norm of `det (adelicArchGLIncl x)` to the `-σ` power. -/

section BiInvariantAverage

variable {F : Type} [Field F]

/-- An element of `GL₂(K_∞)` is determined by its archimedean components. -/
private theorem ext_archComponent {g g' : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ v : InfinitePlace F, archComponent F v g = archComponent F v g') : g = g' := by
  refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
  have := congrArg (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion) i j) (h v)
  simpa only [archComponent_apply] using this

/-- The row-isometry inclusion of a single factor is the inclusion at that place. -/
private theorem archRowIsometryInclAt_of_mulSingle [DecidableEq (InfinitePlace F)]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →*
      GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    ι (Pi.mulSingle w k) = archRowIsometryInclAt₀ F w k := by
  refine ext_archComponent fun v => ?_
  rw [hι]
  show ((Pi.mulSingle w k : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) v :
      GL (Fin 2) v.Completion)
    = archComponent F v (archGLIncl F w (k : GL (Fin 2) w.Completion))
  by_cases hv : v = w
  · subst hv; rw [Pi.mulSingle_eq_same, archComponent_archGLIncl_self]
  · rw [Pi.mulSingle_eq_of_ne hv, archComponent_archGLIncl_of_ne F hv]; rfl

/-- The determinant of a general linear group element is functorial under a ring
homomorphism on `2 × 2` matrices. -/
private theorem det_map_generalLinearGroup {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : GL (Fin 2) R) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ g) =
      Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

variable [NumberField F]

/-- The determinant of the archimedean inclusion of a row-isometry is trivial. -/
private theorem det_adelicArchGLIncl_iota
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →*
      GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ)) = 1 := by
  have hfin : Units.map (adeleFin (𝓞 F) F).toMonoidHom
      (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ))) = 1 := by
    rw [← det_map_generalLinearGroup]
    show Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F (adelicArchGLIncl F (ι κ))) = 1
    rw [glFin_adelicArchGLIncl, map_one]
  have harch : ∀ v : InfinitePlace F, Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom
      (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ))) = 1 := by
    intro v
    rw [← det_map_generalLinearGroup]
    have : Matrix.GeneralLinearGroup.map ((archEval F v).comp (adeleArch (𝓞 F) F))
        (adelicArchGLIncl F (ι κ))
        = archComponent F v (glArch (𝓞 F) F (adelicArchGLIncl F (ι κ))) := rfl
    rw [this, glArch_adelicArchGLIncl, hι]
    exact Units.ext (by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
      exact ((mem_rowIsometrySubgroup₀_iff (K := v.Completion)).mp (κ v).2).1)
  refine Units.ext (Prod.ext (funext fun v => ?_) ?_)
  · have := congrArg (fun u : (v.Completion)ˣ => (u : v.Completion)) (harch v)
    simp at this
    exact this
  · have := congrArg (fun u : (FiniteAdeleRing (𝓞 F) F)ˣ => (u : FiniteAdeleRing (𝓞 F) F)) hfin
    simp at this
    exact this

end BiInvariantAverage

theorem integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (σ : ℝ)
    (e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ)
    (hecl : ∀ κ κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e (κ' * κ * κ'⁻¹) = e κ)
    (hefl : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e κ⁻¹ = conj (e κ))
    (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hhc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      h (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = h x)
    (hhf : ∀ x : GL (Fin 2) (InfiniteAdeleRing F), h x = conj (h x⁻¹) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ)) :
    (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
      (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
          e p.1 * e p.2 * h ((ι p.1)⁻¹ * (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) * (ι p.2)⁻¹)
          ∂(μ.prod μ)) =
      ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) ∂(μ.prod μ)) ∧
    ∀ x : GL (Fin 2) (InfiniteAdeleRing F),
      (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) ∂(μ.prod μ)) =
        conj (∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e p.1 * e p.2 * h ((ι p.1)⁻¹ * x⁻¹ * (ι p.2)⁻¹) ∂(μ.prod μ)) *
          ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) := by
  classical
  have : SigmaFinite μ := IsFiniteMeasure.toSigmaFinite μ
  have : SFinite μ := inferInstance
  have : MeasurableMul (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := inferInstance
  have : MeasurableInv (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := inferInstance

  set G : GL (Fin 2) (InfiniteAdeleRing F) →
      (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ := fun x p =>
    e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹) with hG
  set W : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun x =>
    ((NumberField.TateGlobal.ideleNorm F
      (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)) ^ (-σ) : ℝ) : ℂ) with hW
  have hdet1 : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      Matrix.GeneralLinearGroup.det (adelicArchGLIncl F (ι κ)) = 1 :=
    det_adelicArchGLIncl_iota ι hι
  refine ⟨fun w k x => ?_, fun x => ?_⟩

  · set κ₀ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := Pi.mulSingle w k with hκ₀
    have hικ₀ : ι κ₀ = archRowIsometryInclAt₀ F w k := archRowIsometryInclAt_of_mulSingle ι hι w k

    set cj : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ≃ᵐ
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
      (MeasurableEquiv.mulLeft κ₀).trans (MeasurableEquiv.mulRight κ₀⁻¹) with hcj
    have hcj_apply : ∀ q : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        cj q = κ₀ * q * κ₀⁻¹ := fun q => rfl
    have hcjmp : MeasurePreserving cj μ μ :=
      (measurePreserving_mul_right μ κ₀⁻¹).comp (measurePreserving_mul_left μ κ₀)
    set Φ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ≃ᵐ
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
      MeasurableEquiv.prodCongr cj cj with hΦ
    have hΦmp : MeasurePreserving Φ (μ.prod μ) (μ.prod μ) := hcjmp.prod hcjmp
    show ∫ p, G (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) p
        ∂(μ.prod μ) = ∫ p, G x p ∂(μ.prod μ)
    rw [← hΦmp.integral_comp' (G (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹))]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    show e (cj p.1) * e (cj p.2) *
        h ((ι (cj p.1))⁻¹ * (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) * (ι (cj p.2))⁻¹)
      = e p.1 * e p.2 * h ((ι p.1)⁻¹ * x * (ι p.2)⁻¹)
    rw [hcj_apply, hcj_apply, hecl, hecl, ← hικ₀]
    congr 1
    rw [← hhc w k ((ι p.1)⁻¹ * x * (ι p.2)⁻¹), ← hικ₀]
    congr 1
    simp only [map_mul, map_inv]
    group

  ·
    have hWι : ∀ (p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
        (y : GL (Fin 2) (InfiniteAdeleRing F)), W ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) = W y := by
      intro p y
      simp only [hW, map_mul, map_inv, hdet1, inv_one, one_mul, mul_one]
    have hN1 : NumberField.TateGlobal.ideleNorm F 1 = 1 := by
      have h := NumberField.TateGlobal.ideleNorm_mul (F := F) 1 1
      rw [mul_one] at h
      have hp := NumberField.TateGlobal.ideleNorm_pos (F := F) 1
      nlinarith [h, hp]
    have hWinv : W x⁻¹ * W x = 1 := by
      simp only [hW, map_inv]
      have hpos := NumberField.TateGlobal.ideleNorm_pos
        (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x))
      have hinv : NumberField.TateGlobal.ideleNorm F
            (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x))⁻¹ =
          (NumberField.TateGlobal.ideleNorm F
            (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x)))⁻¹ := by
        have h := NumberField.TateGlobal.ideleNorm_mul (F := F)
          (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x))⁻¹
          (Matrix.GeneralLinearGroup.det (adelicArchGLIncl F x))
        rw [inv_mul_cancel, hN1] at h
        field_simp
        linarith
      rw [hinv, Real.inv_rpow hpos.le, ← Complex.ofReal_mul,
        inv_mul_cancel₀ (Real.rpow_pos_of_pos hpos _).ne', Complex.ofReal_one]
    have hWreal : ∀ y, conj (W y) = W y := fun y => by simp only [hW, Complex.conj_ofReal]
    have hconjh : ∀ z : GL (Fin 2) (InfiniteAdeleRing F), conj (h z) = h z⁻¹ * W z := by
      intro z
      have := congrArg conj (hhf z)
      rw [map_mul] at this
      rw [this, Complex.conj_conj]
      show h z⁻¹ * conj (W z) = h z⁻¹ * W z
      rw [hWreal]

    set H : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ :=
      fun p => e p.1⁻¹ * e p.2⁻¹ * h (ι p.2 * x * ι p.1) with hH
    have hstep : conj (∫ p, G x⁻¹ p ∂(μ.prod μ)) * W x = ∫ p, H p ∂(μ.prod μ) := by
      rw [← integral_conj, ← integral_mul_const]
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      show conj (e p.1 * e p.2 * h ((ι p.1)⁻¹ * x⁻¹ * (ι p.2)⁻¹)) * W x =
        e p.1⁻¹ * e p.2⁻¹ * h (ι p.2 * x * ι p.1)
      rw [map_mul, map_mul, ← hefl, ← hefl, hconjh, hWι p x⁻¹]
      rw [show ((ι p.1)⁻¹ * x⁻¹ * (ι p.2)⁻¹)⁻¹ = ι p.2 * x * ι p.1 by group]
      rw [mul_assoc, mul_assoc (h (ι p.2 * x * ι p.1)), hWinv, mul_one]

    set Ψ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ≃ᵐ
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) :=
      MeasurableEquiv.prodComm.trans
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.inv (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
          (MeasurableEquiv.inv (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))) with hΨ
    have hΨ_apply : ∀ q : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
        (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), Ψ q = (q.2⁻¹, q.1⁻¹) := fun q => rfl
    have hΨmp : MeasurePreserving Ψ (μ.prod μ) (μ.prod μ) :=
      ((Measure.measurePreserving_inv μ).prod (Measure.measurePreserving_inv μ)).comp
        (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    show ∫ p, G x p ∂(μ.prod μ) = conj (∫ p, G x⁻¹ p ∂(μ.prod μ)) * W x
    rw [hstep, ← hΨmp.integral_comp' H]
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    show e q.1 * e q.2 * h ((ι q.1)⁻¹ * x * (ι q.2)⁻¹) = H (Ψ q)
    rw [hΨ_apply]
    show e q.1 * e q.2 * h ((ι q.1)⁻¹ * x * (ι q.2)⁻¹) =
      e q.2⁻¹⁻¹ * e q.1⁻¹⁻¹ * h (ι q.1⁻¹ * x * ι q.2⁻¹)
    rw [inv_inv, inv_inv, map_inv, map_inv, mul_comm (e q.2) (e q.1)]

/-! ### The archimedean test factor

A `C^∞` function `Φ` of the archimedean coordinates whose support stays inside the units of
the determinant defines an archimedean test factor: `archEntries` is continuous and, over the
open set where the determinant is a unit, it is inverted by an explicit continuous section
`sectionGL` built from the archimedean ring equivalence. -/

section ArchTestFactor

variable (F : Type) [Field F]

/-- `archEntries` is continuous, being entrywise the continuous archimedean ring
equivalence. -/
private theorem continuous_archEntries : Continuous (archEntries F) := by
  have hval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := Units.continuous_val
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (hval.matrix_elem i j)

/-- Reading `archEntries` back as a matrix is applying the archimedean ring equivalence
entrywise. -/
private theorem of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix.of (archEntries F g) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F :
        InfiniteAdeleRing F →+* mixedEmbedding.mixedSpace F).mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  Matrix.ext fun _ _ => rfl

/-- The archimedean coordinates of a unit of `GL₂` have unit determinant. -/
private theorem isUnit_det_of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    IsUnit (Matrix.det (Matrix.of (archEntries F g))) := by
  rw [of_archEntries, ← RingHom.map_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).map _

/-- The inverse of the archimedean ring equivalence is continuous: on the real places it is
the inverse isometry onto `ℝ`, on the complex ones the inverse isometry onto `ℂ`. -/
private theorem continuous_symm_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  by_cases hv : InfinitePlace.IsReal v
  · have h : (fun y : mixedEmbedding.mixedSpace F =>
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      change InfinitePlace.Completion.extensionEmbeddingOfIsReal hv _ = _
      rw [IsometryEquiv.apply_symm_apply]
      have hy := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y
      rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hy
      exact congrFun (congrArg Prod.fst hy) ⟨v, hv⟩
    rw [h]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hv' : InfinitePlace.IsComplex v := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have h : (fun y : mixedEmbedding.mixedSpace F =>
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm y v) =
        fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm (y.2 ⟨v, hv'⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').injective
      change InfinitePlace.Completion.extensionEmbedding v _ = _
      rw [IsometryEquiv.apply_symm_apply]
      have hy := (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y
      rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at hy
      exact congrFun (congrArg Prod.snd hy) ⟨v, hv'⟩
    rw [h]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

/-- The preimage of an archimedean matrix under the reverse archimedean ring equivalence. -/
private def adeleMatrix (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm :
    mixedEmbedding.mixedSpace F →+* InfiniteAdeleRing F).mapMatrix (Matrix.of E)

/-- `adeleMatrix` is continuous, entrywise. -/
private theorem continuous_adeleMatrix : Continuous (adeleMatrix F) := by
  refine continuous_matrix fun i j => ?_
  simp only [adeleMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    RingEquiv.coe_toRingHom]
  exact (continuous_symm_ringEquiv_mixedSpace F).comp ((continuous_apply j).comp (continuous_apply i))

/-- A matrix with unit determinant has unit determinant after the reverse archimedean ring
equivalence. -/
private theorem isUnit_det_adeleMatrix (E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)
    (hE : IsUnit (Matrix.det (Matrix.of E))) : IsUnit (adeleMatrix F E).det := by
  unfold adeleMatrix
  rw [← RingHom.map_det]
  exact hE.map _

/-- Inversion is continuous at a unit of the archimedean adèle ring. -/
private theorem continuousAt_inverse [NumberField F] (u : (InfiniteAdeleRing F)ˣ) :
    ContinuousAt (Ring.inverse : InfiniteAdeleRing F → InfiniteAdeleRing F) u := by
  let : NormedRing (InfiniteAdeleRing F) :=
    inferInstanceAs (NormedRing ((v : InfinitePlace F) → v.Completion))
  let : CompleteSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (CompleteSpace ((v : InfinitePlace F) → v.Completion))
  exact NormedRing.inverse_continuousAt u

/-- An explicit continuous section of `archEntries` over the matrices with unit determinant. -/
private noncomputable def sectionGL
    (E : {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F // IsUnit (Matrix.det (Matrix.of E))}) :
    GL (Fin 2) (InfiniteAdeleRing F) :=
  ⟨adeleMatrix F E.1, (adeleMatrix F E.1)⁻¹,
    Matrix.mul_nonsing_inv _ (isUnit_det_adeleMatrix F E.1 E.2),
    Matrix.nonsing_inv_mul _ (isUnit_det_adeleMatrix F E.1 E.2)⟩

/-- The section `sectionGL` is continuous. -/
private theorem continuous_sectionGL [NumberField F] : Continuous (sectionGL F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_adeleMatrix F).comp continuous_subtype_val
  · change Continuous fun E : {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F //
      IsUnit (Matrix.det (Matrix.of E))} => (adeleMatrix F E.1)⁻¹
    refine continuous_iff_continuousAt.2 fun E => ?_
    have hdet : ContinuousAt Ring.inverse (adeleMatrix F E.1).det := by
      obtain ⟨u, hu⟩ := isUnit_det_adeleMatrix F E.1 E.2
      rw [← hu]
      exact continuousAt_inverse F u
    exact ContinuousAt.comp (g := Inv.inv)
      (f := fun E' : {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F //
        IsUnit (Matrix.det (Matrix.of E))} => adeleMatrix F E'.1)
      (continuousAt_matrix_inv _ hdet)
      ((continuous_adeleMatrix F).comp continuous_subtype_val).continuousAt

/-- A compact set of archimedean matrices supported away from the singular ones has compact
preimage under `archEntries`. -/
private theorem isCompact_preimage_archEntries [NumberField F]
    (K : Set (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)) (hK : IsCompact K)
    (hKU : K ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    IsCompact (archEntries F ⁻¹' K) := by
  have hKs : IsCompact (Subtype.val ⁻¹' K :
      Set {E : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F // IsUnit (Matrix.det (Matrix.of E))}) := by
    refine (Topology.IsInducing.subtypeVal.isCompact_preimage_iff ?_).2 hK
    exact fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩
  refine (hKs.image (continuous_sectionGL F)).of_isClosed_subset
    (hK.isClosed.preimage (continuous_archEntries F)) fun g hg => ?_
  refine ⟨⟨archEntries F g, isUnit_det_of_archEntries F g⟩, hg, ?_⟩
  apply Units.ext
  change adeleMatrix F (archEntries F g) = (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
  refine Matrix.ext fun i j => ?_
  simp only [adeleMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    RingEquiv.coe_toRingHom, archEntries_apply, RingEquiv.symm_apply_apply]

end ArchTestFactor

theorem isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det
    (F : Type) [Field F] [NumberField F] (Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    (hU : tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))}) :
    IsArchTestFactor F fun g => Φ (archEntries F g) := by
  refine ⟨⟨Φ, hΦ, fun _ => rfl⟩, ?_⟩
  refine (isCompact_preimage_archEntries F (tsupport Φ) hc hU).of_isClosed_subset
    (isClosed_tsupport _) ?_
  exact closure_minimal (fun g hg => subset_tsupport Φ hg)
    ((isClosed_tsupport Φ).preimage (continuous_archEntries F))

end AutomorphicForm
