/-
  Γ₁-vanishing of the `U_p + T_p` Hecke operator, in four steps.

  Transcribed from the pinned FLT sources (`aa2d8b3`)
  `P2M/Sol/S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean`,
  `S_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant.lean`,
  `S_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq.lean` and
  `S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean`:

  * `ModularForm.heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1` — the
    `Γ₁(N)`-invariance of `U_p + T_p` (a thin wrapper over the port declaration
    `CuspForm.Gamma1Hecke.heckeU_add_slash_heckeDiagMatrix_slash`);
  * `CuspForm.vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant` — the Ihara
    argument turning `T_{q'}`-invariance into invariance under the translations
    `(q'^j)⁻¹ +ᵥ ·`;
  * `CuspForm.eq_zero_of_forall_vadd_inv_pow_eq` — such a form vanishes
    (`q`-expansion / `q`-parameter argument);
  * `CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1` — the
    norm/trace reduction from `Γ₁(M)` to `Γ₀(M)`.

  The first three `solution`s are proved here; the body of the first is the
  existing port declaration, and the second's only missing ingredient while the
  parallel `IharaSurjective` port lands is
  `Ihara.amalgamToGamma0Away_surjective`.
-/
import FLTForHuman.ModularForms.Defs.Gamma1HeckeOperators
import FLTForHuman.ModularCurve.Defs.IharaAmalgamMap
import FLTForHuman.ModularCurve.IharaSurjective
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
import Mathlib.Data.Nat.Prime.Int

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm UpperHalfPlane SlashInvariantForm
open scoped ModularForm UpperHalfPlane MatrixGroups Pointwise Real

namespace ModularForm

/-- `U_p + T_p` is `Γ₁(N)`-invariant, for `p ∤ N` and `σ ∈ Γ₀(N)` with
`σ 1 1 = p` (mod `N`). Transcribed from
`Theorems/Thm_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean`;
the port's `CuspForm.Gamma1Hecke.heckeU_add_slash_heckeDiagMatrix_slash` is the
same statement. -/
theorem heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeU k p f + (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ)) ∣[k] heckeDiagMatrix p) ∣[k] γ
      = heckeU k p f + (f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ)) ∣[k] heckeDiagMatrix p :=
  CuspForm.Gamma1Hecke.heckeU_add_slash_heckeDiagMatrix_slash k hp hpN hf σ hσ hσp γ hγ

end ModularForm

namespace CuspForm

/-- A cusp form invariant under the translations `(q'^j)⁻¹ +ᵥ ·` is zero
(`hq' : 1 < q'`). Transcribed from
`Theorems/Thm_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq.lean`. -/
theorem eq_zero_of_forall_vadd_inv_pow_eq
    {R q' : ℕ} [NeZero R] (hq' : 1 < q') (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (h : ∀ (j : ℕ) (τ : ℍ), y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ) :
    y = 0 := by
  have h1 : (1 : ℝ) ∈ (((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    rw [show (((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) =
      Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma0 R) from rfl, CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  haveI : Fact (IsCusp OnePoint.infty (((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  have hper : Function.Periodic ((⇑y : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex y h1
  have hmd := ModularFormClass.holo y
  have hbd : IsBoundedAtImInfty (⇑y : ℍ → ℂ) := ModularFormClass.bdd_at_infty y
  have hcoeff : ∀ m, PowerSeries.coeff m (qExpansion 1 (⇑y : ℍ → ℂ)) = 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [qExpansion_coeff]
      simp [CuspFormClass.cuspFunction_apply_zero y one_pos h1]
    · set δ : ℝ := ((q' : ℝ) ^ m)⁻¹ with hδ
      set ζ : ℂ := Complex.exp (2 * π * Complex.I * (δ : ℂ)) with hζdef
      have hζq : ∀ τ : ℍ, Function.Periodic.qParam 1 ((δ +ᵥ τ : ℍ) : ℂ) = ζ * Function.Periodic.qParam 1 (τ : ℂ) := by
        intro τ
        rw [UpperHalfPlane.coe_vadd]
        simp only [Function.Periodic.qParam, Complex.ofReal_one, div_one]
        rw [hζdef, ← Complex.exp_add]
        congr 1
        ring
      have key := ModularFormClass.qExpansion_coeff_unique (k := k) one_pos h1 (f := y)
        (c := fun n => PowerSeries.coeff n (qExpansion 1 (⇑y : ℍ → ℂ)) * ζ ^ n) (fun τ => by
          have hs := UpperHalfPlane.hasSum_qExpansion one_pos hper hmd hbd (δ +ᵥ τ)
          rw [h m τ] at hs
          simp_rw [hζq τ, mul_pow, smul_eq_mul] at hs
          simp_rw [smul_eq_mul]
          convert hs using 1
          ext n
          ring) m

      have hζ : ζ ^ m ≠ 1 := by
        rw [hζdef, ← Complex.exp_nat_mul, Ne, Complex.exp_eq_one_iff]
        rintro ⟨n, hn⟩
        have h2pi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        have hreal : ((m : ℝ) * δ : ℝ) = (n : ℝ) := by
          have : ((m : ℂ)) * (δ : ℂ) * (2 * π * Complex.I) = (n : ℂ) * (2 * π * Complex.I) := by
            rw [← hn]; ring
          have := mul_right_cancel₀ h2pi this
          exact_mod_cast this

        have hpos : (0 : ℝ) < (m : ℝ) * δ := by
          have : (0 : ℝ) < δ := by rw [hδ]; positivity
          positivity
        have hlt : (m : ℝ) * δ < 1 := by
          rw [hδ, ← div_eq_mul_inv, div_lt_one (by positivity)]
          exact_mod_cast Nat.lt_pow_self hq'
        rw [hreal] at hpos hlt
        have h0 : (0 : ℤ) < n := by exact_mod_cast hpos
        have h1' : n < (1 : ℤ) := by exact_mod_cast hlt
        omega
      have h2 : PowerSeries.coeff m (qExpansion 1 (⇑y : ℍ → ℂ)) * (ζ ^ m - 1) = 0 := by
        linear_combination key
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact h3
      · exact absurd (sub_eq_zero.mp h3) hζ
  have hq0 : qExpansion 1 (⇑y : ℍ → ℂ) = 0 := by
    ext m; rw [hcoeff m, map_zero]
  have hf : (⇑y : ℍ → ℂ) = 0 := (qExpansion_eq_zero_iff one_pos hper hmd hbd).1 hq0
  exact DFunLike.ext y 0 (fun τ => by simpa using congrFun hf τ)

/-! ### The Ihara step (target 2)

  The `q'`-translation invariance of a `Γ₀(R)`-cusp form whose `T_{q'}`-translate is
  `Γ₀(R)`-invariant, via the Ihara amalgam and the surjectivity of
  `amalgamToGamma0Away`. -/

namespace IharaSlashB2a

open Ihara

private def slashStab (k : ℤ) (f : ℍ → ℂ) : Subgroup (GL (Fin 2) ℝ) where
  carrier := {g | f ∣[k] g = f}
  one_mem' := SlashAction.slash_one k f
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [SlashAction.slash_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    calc f ∣[k] a⁻¹ = (f ∣[k] a) ∣[k] a⁻¹ := by rw [ha]
      _ = f := by rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

private theorem mem_slashStab {k : ℤ} {f : ℍ → ℂ} {g : GL (Fin 2) ℝ} :
    g ∈ slashStab k f ↔ f ∣[k] g = f :=
  Iff.rfl

private noncomputable def transGL (s : ℝ) : GL (Fin 2) ℝ := upperTriangularGL 1 s 1 (by norm_num)

private theorem val_transGL (s : ℝ) :
    ((transGL s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![1, s; 0, 1] := rfl

private theorem det_transGL (s : ℝ) : ((transGL s).det : ℝ) = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_transGL, Matrix.det_fin_two_of]; ring

private theorem slash_transGL_apply (k : ℤ) (s : ℝ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] transGL s) τ = f (s +ᵥ τ) := by
  have hdetpos : 0 < ((transGL s).det : ℝ) := by rw [det_transGL]; exact one_pos
  have hσ : UpperHalfPlane.σ (transGL s) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, ite_eq_left hdetpos]
  have hdenom : UpperHalfPlane.denom (transGL s) τ = 1 := by
    simp [UpperHalfPlane.denom, val_transGL]
  have hsmul : (transGL s) • τ = s +ᵥ τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos, UpperHalfPlane.coe_vadd]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, val_transGL, add_comm]
  rw [ModularForm.slash_apply, hσ, det_transGL, hdenom, hsmul]
  simp

variable (q : ℕ) (hq : q ≠ 0)

private noncomputable def awayToReal : ZAway q →+* ℝ :=
  IsLocalization.Away.lift (q : ℤ) (g := Int.castRingHom ℝ)
    (by rw [eq_intCast, Int.cast_natCast]; exact isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hq))

private theorem awayToReal_algebraMap (a : ℤ) : awayToReal q hq (algebraMap ℤ (ZAway q) a) = a := by
  rw [awayToReal, IsLocalization.Away.lift_eq, eq_intCast]

private theorem awayToReal_invSelf :
    awayToReal q hq (IsLocalization.Away.invSelf (S := ZAway q) (q : ℤ)) = (q : ℝ)⁻¹ := by
  have h := congrArg (awayToReal q hq) (q_mul_invSelf q)
  rw [map_mul, map_one, map_natCast] at h
  exact (inv_eq_of_mul_eq_one_right h).symm

private noncomputable def rho : SL(2, ZAway q) →* GL (Fin 2) ℝ :=
  (Matrix.SpecialLinearGroup.toGL : SL(2, ℝ) →* GL (Fin 2) ℝ).comp
    (Matrix.SpecialLinearGroup.map (awayToReal q hq))

private theorem rho_apply_coe (g : SL(2, ZAway q)) :
    ((rho q hq g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((g : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)).map (awayToReal q hq) :=
  rfl

private theorem map_wMat : (wMat q).map (awayToReal q hq) = !![(1 : ℝ), 0; 0, (q : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMat]

private theorem map_wMatInv : (wMatInv q).map (awayToReal q hq) = !![(1 : ℝ), 0; 0, (q : ℝ)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wMatInv, awayToReal_invSelf]

private theorem rho_wConj_mul (v : SL(2, ZAway q)) :
    rho q hq (wConj q v) * heckeDiagMatrix q = heckeDiagMatrix q * rho q hq v := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix hq, rho_apply_coe, rho_apply_coe,
    show ((wConj q v : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)) = wMatInv q * v * wMat q from rfl,
    Matrix.map_mul, Matrix.map_mul, map_wMat, map_wMatInv,
    Matrix.eta_fin_two (((v : SL(2, ZAway q)) : Matrix (Fin 2) (Fin 2) (ZAway q)).map (awayToReal q hq))]
  simp only [Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> (simp; try field_simp; try ring)

private theorem rho_wConj_eq (v : SL(2, ZAway q)) :
    rho q hq (wConj q v) = heckeDiagMatrix q * rho q hq v * (heckeDiagMatrix q)⁻¹ :=
  eq_mul_inv_of_mul_eq (rho_wConj_mul q hq v)

private theorem rho_vertexZero (R : ℕ) (g : Gamma0 R) :
    rho q hq (vertexZero R q g) = Matrix.SpecialLinearGroup.mapGL ℝ (g : SL(2, ℤ)) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [rho_apply_coe, coe_vertexZero, Matrix.map_apply, Matrix.map_apply, awayToReal_algebraMap]
  show ((g : SL(2, ℤ)) i j : ℝ) = algebraMap ℤ ℝ ((g : SL(2, ℤ)) i j)
  simp

end IharaSlashB2a

open IharaSlashB2a Ihara in
/-- The Ihara translation step: `T_{q'}`-invariance of a `Γ₀(R)`-cusp form forces
invariance under all the translations `(q'^j)⁻¹ +ᵥ ·`. Transcribed from
`Theorems/Thm_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant.lean`. -/
theorem vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant
    {R q' : ℕ} [NeZero R] (hq' : q'.Prime) (hq'R : ¬ q' ∣ R) (k : ℤ)
    (y : CuspForm ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hy : ∀ γ ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q') ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix q')
    (j : ℕ) (τ : ℍ) :
    y ((((q' : ℝ) ^ j)⁻¹) +ᵥ τ) = y τ := by
  have hq0 : q' ≠ 0 := hq'.ne_zero
  have hcop : Nat.Coprime R q' := ((Nat.Prime.coprime_iff_not_dvd hq').2 hq'R).symm
  have hmemΓ : ∀ g : Gamma0 R, Matrix.SpecialLinearGroup.mapGL ℝ (g : SL(2, ℤ)) ∈
      ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    fun g => Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) g.2

  have hV0 : ∀ g : Gamma0 R, (⇑y : ℍ → ℂ) ∣[k] rho q' hq0 (vertexZero R q' g) = ⇑y := fun g => by
    rw [rho_vertexZero]
    exact SlashInvariantFormClass.slash_action_eq y _ (hmemΓ g)
  have hV1 : ∀ g : Gamma0 R, (⇑y : ℍ → ℂ) ∣[k] rho q' hq0 (wConj q' (vertexZero R q' g)) = ⇑y := fun g => by
    rw [rho_wConj_eq, rho_vertexZero, SlashAction.slash_mul, SlashAction.slash_mul, hy _ (hmemΓ g),
      ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

  let K : Subgroup SL(2, ZAway q') :=
    (slashStab k (⇑y : ℍ → ℂ)).comap ((rho q' hq0).comp (wConj q').toMonoidHom)
  have hKmem : ∀ v : SL(2, ZAway q'), v ∈ K ↔ (⇑y : ℍ → ℂ) ∣[k] rho q' hq0 (wConj q' v) = ⇑y := fun v => by
    rw [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, mem_slashStab]
  have hv1 : ∀ g : Gamma0 R, wConj q' (vertexOne R q' g) = vertexZero R q' g := fun g => by
    rw [Ihara.vertexOne, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hK : (amalgamToAway R q').range ≤ K := by
    rw [MonoidHom.range_eq_map, ← iharaVertex_range_sup, Subgroup.map_sup, sup_le_iff,
      MonoidHom.map_range, MonoidHom.map_range]
    constructor
    · rintro _ ⟨g, rfl⟩
      rw [MonoidHom.comp_apply, amalgamToAway_vertex_zero, hKmem]
      exact hV1 g
    · rintro _ ⟨g, rfl⟩
      rw [MonoidHom.comp_apply, amalgamToAway_vertex_one, hKmem, hv1]
      exact hV0 g

  obtain ⟨t, ht⟩ : ∃ t : ZAway q', t = IsLocalization.Away.invSelf (S := ZAway q') (q' : ℤ) ^ j := ⟨_, rfl⟩
  have hdet : Matrix.det !![(1 : ZAway q'), t; 0, 1] = 1 := by
    rw [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero]
  obtain ⟨u, hu_def⟩ : ∃ u : SL(2, ZAway q'), u = ⟨!![(1 : ZAway q'), t; 0, 1], hdet⟩ := ⟨_, rfl⟩
  have hu' : (wConj q').symm u ∈ Gamma0Away R q' := by
    rw [mem_Gamma0Away]
    rw [wConj_symm_coe, wMat_mul_mul_wMatInv, hu_def]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, mul_zero]
    exact dvd_zero _
  obtain ⟨a, ha⟩ := Ihara.amalgamToGamma0Away_surjective R q' hcop hq' ⟨(wConj q').symm u, hu'⟩
  have ha' : amalgamToAway R q' a = (wConj q').symm u := by
    rw [← coe_amalgamToGamma0Away, ha]
  have hu : (⇑y : ℍ → ℂ) ∣[k] rho q' hq0 u = ⇑y := by
    have h1 := (hKmem _).1 (hK (MonoidHom.mem_range.mpr ⟨a, rfl⟩))
    rw [ha', MulEquiv.apply_symm_apply] at h1
    exact h1

  have hρu : rho q' hq0 u = transGL (((q' : ℝ) ^ j)⁻¹) := by
    refine Matrix.GeneralLinearGroup.ext fun a b => ?_
    rw [val_transGL, rho_apply_coe, Matrix.map_apply, hu_def]
    fin_cases a <;> fin_cases b <;> simp [ht, map_pow, awayToReal_invSelf, inv_pow]
  have key := congrFun hu τ
  rw [hρu, slash_transGL_apply] at key
  exact key

/-! ### The norm/trace reduction (target 4)

  A `Γ₁(M)`-cusp form whose `T_p`-translate is `Γ₁(M)`-invariant is zero, by
  taking the norm down to `Γ₀(M)`. -/

namespace Gamma1Stretch

variable {M : ℕ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

private theorem mapGL_injective : Function.Injective (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) → _) := by
  intro a b h
  ext i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa using this

private theorem mem_coe_iff {Γ : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) ↔ γ ∈ Γ := by
  constructor
  · rintro ⟨g, hg, hgg⟩
    rwa [← mapGL_injective hgg]
  · exact fun h => Subgroup.mem_map_of_mem _ h

private theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

private theorem det_mod {N : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) (det_eq γ)
  push_cast at this
  rw [hc] at this
  linear_combination this

private theorem mem_Gamma1_iff_of_mem_Gamma0 {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    γ ∈ Gamma1 N ↔ ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  rw [Gamma1_mem]
  constructor
  · rintro ⟨-, h, -⟩; simpa using h
  · intro hd
    have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
      have := det_mod γ hγ; rw [hd, mul_one] at this; exact this
    exact ⟨by simpa using ha, by simpa using hd, by simpa using Gamma0_mem.mp hγ⟩

private theorem inv_mul_apply_one_one (γ₁ γ₂ : SL(2, ℤ)) :
    (γ₁⁻¹ * γ₂) 1 1 = -(γ₁ 1 0) * γ₂ 0 1 + γ₁ 0 0 * γ₂ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp

private theorem inv_mul_mem_Gamma1_iff {N : ℕ} {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N) :
    γ₁⁻¹ * γ₂ ∈ Gamma1 N ↔ ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ₂ 1 1 : ℤ) : ZMod N) := by
  have hmem : γ₁⁻¹ * γ₂ ∈ Gamma0 N := mul_mem (inv_mem h₁) h₂
  rw [mem_Gamma1_iff_of_mem_Gamma0 hmem, inv_mul_apply_one_one]
  have hc : ((γ₁ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp h₁
  have hdet := det_mod γ₁ h₁
  push_cast
  rw [hc, neg_zero, zero_mul, zero_add]
  constructor
  · intro h
    calc ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ₁ 1 1 : ℤ) : ZMod N) * (((γ₁ 0 0 : ℤ) : ZMod N) * ((γ₂ 1 1 : ℤ) : ZMod N)) := by
          rw [h, mul_one]
      _ = ((γ₂ 1 1 : ℤ) : ZMod N) := by
          rw [← mul_assoc, mul_comm ((γ₁ 1 1 : ℤ) : ZMod N), hdet, one_mul]
  · intro h
    rw [← h, hdet]

section Reps

variable {p : ℕ}

private theorem T_zpow_mem_Gamma1 (M : ℕ) (t : ℤ) : ModularGroup.T ^ t ∈ Gamma1 M := by
  rw [Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

private def lowerV (M : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (M : ℤ), 1], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem lowerV_mem_Gamma1 (M : ℕ) : lowerV M ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [lowerV]

private theorem mul_T_zpow_apply_zero_one (r : SL(2, ℤ)) (t : ℤ) :
    (r * ModularGroup.T ^ t) 0 1 = r 0 0 * t + r 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
    Fin.sum_univ_two]
  simp

private theorem mul_lowerV_apply_zero_zero (M : ℕ) (r : SL(2, ℤ)) :
    (r * lowerV M) 0 0 = r 0 0 + r 0 1 * M := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [lowerV]

private theorem mul_lowerV_apply_zero_one (M : ℕ) (r : SL(2, ℤ)) :
    (r * lowerV M) 0 1 = r 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [lowerV]

private theorem exists_T_zpow_dvd [Fact p.Prime] (r : SL(2, ℤ)) (ha : ¬ (p : ℤ) ∣ r 0 0) :
    ∃ t : ℤ, (p : ℤ) ∣ (r * ModularGroup.T ^ t) 0 1 := by
  have ha' : ((r 0 0 : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨((-((r 0 1 : ℤ) : ZMod p)) * ((r 0 0 : ℤ) : ZMod p)⁻¹).val, ?_⟩
  rw [mul_T_zpow_apply_zero_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_comm, mul_assoc, inv_mul_cancel₀ ha', mul_one, neg_add_cancel]

private theorem exists_mul_mem_Gamma1_dvd [Fact p.Prime] (hpM : ¬ p ∣ M) (r : SL(2, ℤ))
    (hr : r ∈ Gamma0 M) :
    ∃ g : SL(2, ℤ), g ∈ Gamma1 M ∧ (p : ℤ) ∣ (r * g) 0 1 := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  by_cases ha : (p : ℤ) ∣ r 0 0
  ·
    have hb : ¬ (p : ℤ) ∣ r 0 1 := by
      intro hb
      have h1 : (p : ℤ) ∣ 1 := by
        rw [← det_eq r]
        exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left hb _)
      exact hp.not_dvd_one h1
    have ha' : ¬ (p : ℤ) ∣ (r * lowerV M) 0 0 := by
      rw [mul_lowerV_apply_zero_zero]
      intro h
      have : (p : ℤ) ∣ r 0 1 * M := (dvd_add_right ha).mp h
      rcases hp.dvd_or_dvd this with h1 | h1
      · exact hb h1
      · exact hpM (Int.natCast_dvd_natCast.mp h1)
    obtain ⟨t, ht⟩ := exists_T_zpow_dvd (r * lowerV M) ha'
    exact ⟨lowerV M * ModularGroup.T ^ t, mul_mem (lowerV_mem_Gamma1 M) (T_zpow_mem_Gamma1 M t),
      by rwa [← mul_assoc]⟩
  · obtain ⟨t, ht⟩ := exists_T_zpow_dvd r ha
    exact ⟨ModularGroup.T ^ t, T_zpow_mem_Gamma1 M t, ht⟩

private def conjRep (p : ℕ) (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) : SL(2, ℤ) :=
  ⟨!![r 0 0, e; p * r 1 0, r 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination det_eq r + (r 1 0) * he⟩

private theorem conjRep_apply_one_one (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) :
    conjRep p r e he 1 1 = r 1 1 := rfl

private theorem conjRep_apply_one_zero (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) :
    conjRep p r e he 1 0 = p * r 1 0 := rfl

private theorem conjRep_mem_Gamma0 (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) (hr : r ∈ Gamma0 M) :
    conjRep p r e he ∈ Gamma0 M := by
  rw [Gamma0_mem] at hr ⊢
  rw [conjRep_apply_one_zero]
  push_cast
  rw [hr, mul_zero]

private theorem mapGL_mul_heckeDiagMatrix (hp : p ≠ 0) (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) :
    Matrix.SpecialLinearGroup.mapGL ℝ r * heckeDiagMatrix p
      = heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ (conjRep p r e he) := by
  have he' : ((r 0 1 : ℤ) : ℝ) = (p : ℝ) * (e : ℝ) := by exact_mod_cast he
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Units.val_mul,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    ModularForm.val_heckeDiagMatrix hp]
  rw [Matrix.SpecialLinearGroup.map_apply_coe (algebraMap ℤ ℝ),
    Matrix.SpecialLinearGroup.map_apply_coe (algebraMap ℤ ℝ)]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, RingHom.mapMatrix_apply, Matrix.map_apply, conjRep, he']
  <;> ring

end Reps

section Analytic

variable {p : ℕ} {k : ℤ}

private def diagQ (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [hp])

private theorem map_diagQ (hp : p ≠ 0) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (diagQ p hp) = heckeDiagMatrix p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagQ, hp]

private theorem isArithmetic_conj_heckeDiagMatrix (hp : p ≠ 0) (𝒢 : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsArithmetic] :
    (ConjAct.toConjAct (heckeDiagMatrix p)⁻¹ • 𝒢).IsArithmetic := by
  have := Subgroup.IsArithmetic.conj 𝒢 (diagQ p hp)⁻¹
  rwa [map_inv, map_diagQ hp] at this

variable [NeZero M]

private def stretch (hp : p ≠ 0) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    CuspForm Γ₁(M) k where
  toFun := (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p
  slash_action_eq' := hy
  holo' := (CuspForm.holo' y).slash k _
  zero_at_cusps' := by
    intro c hc
    haveI := isArithmetic_conj_heckeDiagMatrix hp Γ₁(M)
    have hc' : IsCusp c (ConjAct.toConjAct (heckeDiagMatrix p)⁻¹ • Γ₁(M)) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢; exact hc
    exact (CuspForm.translate y (heckeDiagMatrix p)).zero_at_cusps' hc'

private theorem coe_stretch (hp : p ≠ 0) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    ⇑(stretch hp y hy) = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p := rfl

private instance instIsFiniteRelIndex : (Γ₁(M)).IsFiniteRelIndex Γ₀(M) :=
  Subgroup.isFiniteRelIndex_of_le_right (H := Γ₁(M)) (Subgroup.map_le_range _ _)

private abbrev CosetQ (M : ℕ) := (↥(Γ₀(M))) ⧸ (Γ₁(M)).subgroupOf Γ₀(M)

local notation "𝒬" => CosetQ M

private def normCusp (f : CuspForm Γ₁(M) k) : CuspForm Γ₀(M) (k * Nat.card 𝒬) where
  __ := ModularForm.norm Γ₀(M) f
  zero_at_cusps' h γ := by
    rintro rfl
    simp only [ModularForm.toFun_eq_coe, ModularForm.coe_norm]
    let := Fintype.ofFinite 𝒬
    rw [IsZeroAtImInfty, Filter.ZeroAtFilter, Nat.card_eq_fintype_card, ← Finset.card_univ,
      ModularForm.prod_slash]
    rw [show (0 : ℂ) = (|(γ.det : ℝ)| ^ ((Finset.univ : Finset 𝒬).card - 1 : ℤ)) • ∏ _c : 𝒬, (0 : ℂ) by
      rw [Finset.prod_const, Finset.card_univ, zero_pow Fintype.card_ne_zero, smul_zero]]
    refine Filter.Tendsto.const_smul ?_ _
    rw [Finset.prod_fn]
    refine tendsto_finset_prod _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ => ?_)
    refine (CuspForm.translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr

private theorem coe_normCusp (f : CuspForm Γ₁(M) k) :
    ⇑(normCusp f) = ⇑(ModularForm.norm Γ₀(M) f) := rfl

end Analytic

section Main

variable {p : ℕ} {k : ℤ} [NeZero M] [Fact p.Prime]

local notation "𝒬" => CosetQ M

private theorem quotientFunc_mk' {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] (f : F)
    [SlashInvariantFormClass F 𝒢 k] (h : ℋ) :
    quotientFunc f (QuotientGroup.mk h : ℋ ⧸ 𝒢.subgroupOf ℋ) = (⇑f : ℍ → ℂ) ∣[k] h.val⁻¹ := rfl

private theorem exists_rep (hpM : ¬ p ∣ M) (q : 𝒬) :
    ∃ (r : SL(2, ℤ)) (hr : r ∈ Gamma0 M), (p : ℤ) ∣ r 0 1 ∧
      (QuotientGroup.mk ⟨Matrix.SpecialLinearGroup.mapGL ℝ r, Subgroup.mem_map_of_mem _ hr⟩ : 𝒬) = q := by
  induction q using QuotientGroup.induction_on with
  | H h =>
    obtain ⟨r₀, hr₀, hr₀h⟩ := h.2
    obtain ⟨g, hg, hdvd⟩ := exists_mul_mem_Gamma1_dvd hpM r₀ hr₀
    have hg0 : g ∈ Gamma0 M := Gamma1_in_Gamma0 M hg
    refine ⟨r₀ * g, mul_mem hr₀ hg0, hdvd, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (Matrix.SpecialLinearGroup.mapGL ℝ (r₀ * g))⁻¹ * (h : GL (Fin 2) ℝ) ∈ Γ₁(M)
    rw [← hr₀h, ← map_inv, ← map_mul, mem_coe_iff]
    simpa using inv_mem hg

private def rep (hpM : ¬ p ∣ M) (q : 𝒬) : SL(2, ℤ) := (exists_rep hpM q).choose

private theorem rep_mem (hpM : ¬ p ∣ M) (q : 𝒬) : rep hpM q ∈ Gamma0 M :=
  (exists_rep hpM q).choose_spec.1

private theorem rep_dvd (hpM : ¬ p ∣ M) (q : 𝒬) : (p : ℤ) ∣ rep hpM q 0 1 :=
  (exists_rep hpM q).choose_spec.2.1

private theorem mk_rep (hpM : ¬ p ∣ M) (q : 𝒬) :
    (QuotientGroup.mk ⟨Matrix.SpecialLinearGroup.mapGL ℝ (rep hpM q),
      Subgroup.mem_map_of_mem _ (rep_mem hpM q)⟩ : 𝒬) = q :=
  (exists_rep hpM q).choose_spec.2.2

private def repE (hpM : ¬ p ∣ M) (q : 𝒬) : ℤ := (rep_dvd hpM q).choose

private theorem rep_eq (hpM : ¬ p ∣ M) (q : 𝒬) : rep hpM q 0 1 = p * repE hpM q :=
  (rep_dvd hpM q).choose_spec

private def rep' (hpM : ¬ p ∣ M) (q : 𝒬) : SL(2, ℤ) := conjRep p (rep hpM q) (repE hpM q) (rep_eq hpM q)

private theorem rep'_mem (hpM : ¬ p ∣ M) (q : 𝒬) : rep' hpM q ∈ Gamma0 M :=
  conjRep_mem_Gamma0 _ _ _ (rep_mem hpM q)

private def Phi (hpM : ¬ p ∣ M) (q : 𝒬) : 𝒬 :=
  QuotientGroup.mk ⟨Matrix.SpecialLinearGroup.mapGL ℝ (rep' hpM q),
    Subgroup.mem_map_of_mem _ (rep'_mem hpM q)⟩

private theorem Phi_injective (hpM : ¬ p ∣ M) : Function.Injective (Phi (M := M) hpM) := by
  intro q₁ q₂ h
  rw [Phi, Phi, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  change (Matrix.SpecialLinearGroup.mapGL ℝ (rep' hpM q₁))⁻¹
    * Matrix.SpecialLinearGroup.mapGL ℝ (rep' hpM q₂) ∈ Γ₁(M) at h
  rw [← map_inv, ← map_mul, mem_coe_iff, inv_mul_mem_Gamma1_iff (rep'_mem hpM q₁) (rep'_mem hpM q₂),
    rep', rep', conjRep_apply_one_one, conjRep_apply_one_one,
    ← inv_mul_mem_Gamma1_iff (rep_mem hpM q₁) (rep_mem hpM q₂)] at h
  rw [← mk_rep hpM q₁, ← mk_rep hpM q₂, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  change (Matrix.SpecialLinearGroup.mapGL ℝ (rep hpM q₁))⁻¹
    * Matrix.SpecialLinearGroup.mapGL ℝ (rep hpM q₂) ∈ Γ₁(M)
  rwa [← map_inv, ← map_mul, mem_coe_iff]

private theorem Phi_bijective (hpM : ¬ p ∣ M) : Function.Bijective (Phi (M := M) hpM) :=
  Finite.injective_iff_bijective.mp (Phi_injective hpM)

private theorem quotientFunc_slash_heckeDiagMatrix (hpM : ¬ p ∣ M) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p)
    (q : 𝒬) :
    quotientFunc y q ∣[k] heckeDiagMatrix p
      = quotientFunc (stretch (Fact.out : p.Prime).ne_zero y hy) (Phi hpM q) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  conv_lhs => rw [← mk_rep hpM q]
  rw [Phi, quotientFunc_mk', quotientFunc_mk', coe_stretch, ← SlashAction.slash_mul,
    ← SlashAction.slash_mul]
  congr 1
  have h := mapGL_mul_heckeDiagMatrix hp0 (rep hpM q) (repE hpM q) (rep_eq hpM q)
  change (Matrix.SpecialLinearGroup.mapGL ℝ (rep hpM q))⁻¹ * heckeDiagMatrix p
    = heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ (rep' hpM q))⁻¹
  rw [rep', eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact h.symm

private theorem normCusp_slash_heckeDiagMatrix (hpM : ¬ p ∣ M) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    ∃ C : ℝ, (⇑(normCusp y) : ℍ → ℂ) ∣[k * Nat.card 𝒬] heckeDiagMatrix p
      = C • ⇑(SlashInvariantForm.norm Γ₀(M) (stretch (Fact.out : p.Prime).ne_zero y hy)) := by
  let _ := Fintype.ofFinite 𝒬
  refine ⟨|((heckeDiagMatrix p).det : ℝ)| ^ ((Finset.univ : Finset 𝒬).card - 1 : ℤ), ?_⟩
  rw [coe_normCusp, ModularForm.coe_norm, SlashInvariantForm.coe_norm, Nat.card_eq_fintype_card,
    ← Finset.card_univ, ModularForm.prod_slash]
  congr 1
  rw [← (Phi_bijective hpM).prod_comp fun q => quotientFunc (stretch _ y hy) q]
  exact Finset.prod_congr rfl fun q _ => quotientFunc_slash_heckeDiagMatrix hpM y hy q

private theorem main (hp : p.Prime) (hpM : ¬ p ∣ M) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    y = 0 := by
  obtain ⟨C, hC⟩ := normCusp_slash_heckeDiagMatrix hpM y hy
  have hinv : ∀ γ ∈ Γ₀(M), ((⇑(normCusp y) : ℍ → ℂ) ∣[k * Nat.card 𝒬] heckeDiagMatrix p)
      ∣[k * Nat.card 𝒬] γ = (⇑(normCusp y) : ℍ → ℂ) ∣[k * Nat.card 𝒬] heckeDiagMatrix p := by
    intro γ hγ
    obtain ⟨r, hr, rfl⟩ := hγ
    rw [hC]
    change (C • ⇑(SlashInvariantForm.norm Γ₀(M) (stretch _ y hy))) ∣[k * Nat.card 𝒬] r = _
    rw [ModularForm.SL_smul_slash]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq _ _ (Subgroup.mem_map_of_mem _ hr)
  have hper := CuspForm.vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant hp hpM _ (normCusp y) hinv
  have h0 := CuspForm.eq_zero_of_forall_vadd_inv_pow_eq hp.one_lt _ (normCusp y) hper
  have hy0 : (⇑y : ℍ → ℂ) = 0 := by
    by_contra hne
    apply ModularForm.norm_ne_zero Γ₀(M) hne
    apply DFunLike.coe_injective
    change ⇑(normCusp y) = ⇑(0 : ModularForm Γ₀(M) (k * Nat.card 𝒬))
    rw [h0]
    rfl
  apply DFunLike.coe_injective
  change ⇑y = ⇑(0 : CuspForm Γ₁(M) k)
  rw [hy0]
  rfl

end Main

end Gamma1Stretch

open Gamma1Stretch in
/-- A `Γ₁(M)`-cusp form whose `T_p`-translate is `Γ₁(M)`-invariant is zero.
Transcribed from
`Theorems/Thm_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean`. -/
theorem eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
    {M p : ℕ} [NeZero M] (hp : p.Prime) (hpM : ¬ p ∣ M) (k : ℤ)
    (y : CuspForm ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hy : ∀ γ ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    y = 0 :=
  haveI : Fact p.Prime := ⟨hp⟩
  Gamma1Stretch.main hp hpM y hy

end CuspForm
