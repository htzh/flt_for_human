/-
  Cross-module wire test for SET-AF63B (the Petersson product's definiteness and the
  conjugate Hecke eigenvalue).

  A `spec/` probe, not a library module. Three composition zones, each one *consuming* a
  headline of `ModularForms/Analytic/HeckeEigenvalueConj.lean` rather than restating it:

  * **Zone D (`peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff`) at `k = 0` and
    `f = 0`.** The level is `⊤` (index one, so `FiniteIndex` is the global instance) and
    the weight is the degenerate `0`. The `↔` is fired in both directions: `.mpr` at
    `f = 0` turns the reflexivity `0 = 0` into the vanishing of the product, `.mp` is the
    cancellation direction kept as a function, and the two real-valued conjuncts are then
    *composed* into the statement that `⟪f, f⟫` is the coercion of its own real part --
    which is the shape the weight-`0` read-off needs.

  * **Zone E (`peterssonOn_add_smul_conj`) at `c = 0`.** The three conjuncts are read off
    at the degenerate scalar: additivity in the second argument, `ℂ`-homogeneity at
    `c = 0` (which collapses `0 • g` to `0`), and the Hermitian symmetry. The symmetry
    conjunct is then applied to `⟪f, f⟫` itself, where it says the self-product is a fixed
    point of `conj`.

  * **Zone F (`conj_heckeEigenvalue_eq_of_hasNebentypus`) at a real eigenvalue.** Take
    `lam = 1`, which is real, so `conj lam = lam` and the row reads
    `lam = ε⁻¹(p) · lam`; cancelling the unit `lam` leaves `ε⁻¹(p) = 1`. This is exactly
    the pin's intended read-off ("if `ε` is trivial then `ε⁻¹(p) = 1`"), with the
    eigenvalue hypothesis left as the row's own premise -- as it must be, since no nonzero
    `g` is constructed here.

  Every declaration below is an application of one of the three headlines; the file has no
  `#check`s and no `sorry`s.
-/
import FLTForHuman.ModularForms.Analytic.HeckeEigenvalueConj

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm ModularFormClass Filter CongruenceSubgroup
open scoped MatrixGroups ModularForm ComplexConjugate

namespace SetAF63BConsumer

/-- The full modular group as a subgroup of `GL (Fin 2) ℝ`: the level of zone D. -/
abbrev topLevel : Subgroup (GL (Fin 2) ℝ) := ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/-! ## Zone D: the definiteness row at `k = 0` and `f = 0` -/

/-- **Zone D, `.mpr`.** The `↔` of the definiteness row fired forwards at `f = 0`: the
reflexivity `0 = 0` becomes the vanishing of the weight-`0` self-product. -/
theorem zoneD_self_eq_zero :
    CuspForm.peterssonOn (⊤ : Subgroup SL(2, ℤ)) 0 (0 : CuspForm topLevel 0) 0 = 0 :=
  (CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (⊤ : Subgroup SL(2, ℤ)) 0
    (0 : CuspForm topLevel 0)).2.2.mpr rfl

/-- **Zone D, `.mp`.** The cancellation direction of the same `↔`, kept as a function of the
cusp form rather than fired. -/
theorem zoneD_eq_zero_of_self_eq_zero (f : CuspForm topLevel 0)
    (h : CuspForm.peterssonOn (⊤ : Subgroup SL(2, ℤ)) 0 f f = 0) : f = 0 :=
  (CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (⊤ : Subgroup SL(2, ℤ)) 0 f).2.2.mp h

/-- **Zone D, the nonnegativity conjunct.** At weight `0` the real part of `⟪f, f⟫` is
nonnegative for every `f`. -/
theorem zoneD_re_nonneg (f : CuspForm topLevel 0) :
    0 ≤ (CuspForm.peterssonOn (⊤ : Subgroup SL(2, ℤ)) 0 f f).re :=
  (CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (⊤ : Subgroup SL(2, ℤ)) 0 f).1

/-- **Zone D composed with itself.** The two real-valued conjuncts together say that the
weight-`0` self-product *is* the coercion of its real part: real part by reflexivity,
imaginary part by the row's `im = 0`. This is the form a real-valued read-off consumes. -/
theorem zoneD_eq_ofReal_re (f : CuspForm topLevel 0) :
    ((CuspForm.peterssonOn (⊤ : Subgroup SL(2, ℤ)) 0 f f).re : ℂ) =
      CuspForm.peterssonOn (⊤ : Subgroup SL(2, ℤ)) 0 f f := by
  have him := (CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (⊤ : Subgroup SL(2, ℤ)) 0
    f).2.1
  refine Complex.ext ?_ ?_
  · simp
  · simpa using him.symm

/-! ## Zone E: the polarization row at `c = 0` -/

/-- **Zone E, additivity.** The first conjunct of the polarization row. -/
theorem zoneE_add (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f g h : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    CuspForm.peterssonOn Γ k f (g + h) =
      CuspForm.peterssonOn Γ k f g + CuspForm.peterssonOn Γ k f h :=
  (CuspForm.peterssonOn_add_smul_conj Γ k f g h 0).1

/-- **Zone E, homogeneity at `c = 0`.** The scalarity conjunct fired at the degenerate
scalar: `⟪f, 0 • g⟫ = 0 · ⟪f, g⟫ = 0`. -/
theorem zoneE_smul_zero (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f g : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    CuspForm.peterssonOn Γ k f ((0 : ℂ) • (⇑g : ℍ → ℂ)) = 0 := by
  rw [(CuspForm.peterssonOn_add_smul_conj Γ k f g g (0 : ℂ)).2.1, zero_mul]

/-- **Zone E, Hermitian symmetry.** The third conjunct, at the same degenerate scalar (it
does not depend on `c`). -/
theorem zoneE_conj_symm (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f g : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    starRingEnd ℂ (CuspForm.peterssonOn Γ k g f) = CuspForm.peterssonOn Γ k f g :=
  (CuspForm.peterssonOn_add_smul_conj Γ k f g g (0 : ℂ)).2.2

/-- **Zone E applied to the self-product.** Hermitian symmetry at `f = g` says `⟪f, f⟫` is
a fixed point of `conj`; that is the real-valuedness a conjugation read-off needs, obtained
here from row E alone. -/
theorem zoneE_self_conj (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ)
    (f : CuspForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    starRingEnd ℂ (CuspForm.peterssonOn Γ k f f) = CuspForm.peterssonOn Γ k f f :=
  zoneE_conj_symm Γ k f f

/-! ## Zone F: the conjugate Hecke eigenvalue at a real eigenvalue -/

/-- **Zone F.** The eigenvalue row instantiated at `lam = 1`. The eigenvalue is real, so the
headline's left-hand side `conj lam` collapses to `lam`, and the conclusion reads
`1 = ε⁻¹(p) · 1`; cancelling the unit gives `ε⁻¹(p) = 1`, the pin's trivial-nebentypus
read-off. The eigen-relation `heig` stays a premise: no nonzero eigenform is constructed
in this probe. -/
theorem zoneF_inv_apply_eq_one (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (Gamma1 M) k) (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g)
    (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (heig : ∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
      1 * ModularFormClass.qCoeff g n) :
    ε⁻¹ (p : ZMod M) = 1 := by
  have h := CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus M k ε g hg0 hg p hp hpM 1 heig
  simpa using h.symm

/-- **Zone F, the general real eigenvalue.** With `lam` a real number instead of `1`, the
same row reads `lam = ε⁻¹(p) · lam`; cancelling a nonzero `lam` is the same read-off. This
zone shows the `conj lam = lam` step is the only place reality is used. -/
theorem zoneF_inv_apply_eq_one_of_real (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)
    (g : CuspForm (Gamma1 M) k) (hg0 : g ≠ 0) (hg : CuspForm.HasNebentypus ε g)
    (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M) (lam : ℝ) (hlam : lam ≠ 0)
    (heig : ∀ n : ℕ, ModularFormClass.qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
      (lam : ℂ) * ModularFormClass.qCoeff g n) :
    ε⁻¹ (p : ZMod M) = 1 := by
  have h := CuspForm.conj_heckeEigenvalue_eq_of_hasNebentypus M k ε g hg0 hg p hp hpM (lam : ℂ) heig
  rw [show starRingEnd ℂ (lam : ℂ) = (lam : ℂ) from by simp] at h
  have hlam' : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
  have h' : ε⁻¹ (p : ZMod M) * (lam : ℂ) = 1 * (lam : ℂ) := by simpa using h.symm
  exact mul_right_cancel₀ hlam' h'

end SetAF63BConsumer
