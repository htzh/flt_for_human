/-
  Cross-module wire test for SET-AF35A (the Satake parameters of a covariant self-pairing).

  A `spec/` probe, not a library module. Three composition zones, each one *consuming* the headline
  of `AutomorphicForm/Adelic/Cusp/SatakeParameters.lean` at `s = 1` rather than restating it:

  * **Zone 1 (the headline at `s = 1`).** At `s = 1` the table reads
    `a v * conj (b v) = conj (a v)` and `‖b v‖ = 1`. Both rows are extracted from the instantiation
    (`norm_b_eq_one`, `mul_conj_b_eq_conj_a`), and conjugating the product relation turns it into a
    statement about the *Hecke eigenvalue alone*: the central eigenvalue is the phase of the Hecke
    eigenvalue, `b v = a v / conj (a v)`. Together the two rows say the pair `(a v, b v)` carries no
    information beyond `a v`, with `‖b v‖ = 1` the normalisation that makes the read-off a phase.

  * **Zone 2 (the headline at `s = 1` through the normalization).** `SmoothCuspRealizationAt`'s
    `central_eigen` produces the eigenvalue of the *raw-central* eigensystem, i.e.
    `(cNorm v)⁻¹ * b v`; `centralChar_det_gen_eq_b` identifies that scalar with the central character
    of the realization at `diag (det (heckeGen v))`. Composing the two with `‖b v‖ = 1` gives
    `‖(R'.centralChar z : ℂ)‖ = N v⁻¹`: the arithmetic central character is unitary, and the raw one
    carries exactly the `N v⁻¹` normalization that `toRawCentral` installs.

  * **Zone 3 (the headline at `s = 1` under a `‖·‖^(-t)` twist).** Twisting the eigensystem by the
    real character `χ t v = N v ^ (-t)` (`HeckeEigensystem.twist`, so `(twist χ).b v = χ v ^ 2 * b v`)
    multiplies the modulus by `‖χ v‖ ^ 2 = N v ^ (-2t)`: the `‖b‖ = 1` row is the `t = 0` case, and
    the twist moves the Satake parameter along the real line rather than off the unit circle.

  Every proof below is an application of the headline; the file has no `#check`s.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SatakeParameters

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField Matrix
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm

namespace SetAF35AConsumer

variable (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))

/-- The carrier of the headline: the production pins over the level family
`levelOne ⊓ finiteAdelicGL2Subgroup` and the Hecke generators `heckeGen`. -/
abbrev pinsOf : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

/-- The right-translate span of a realization — the domain on which the covariant form `P` lives. -/
abbrev carrier (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsOf F D) π'.toRawCentral) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ (Set.range fun h : AdelicGL2 (𝓞 F) F => fun z => R'.toFun (z * h))

/-- The covariance hypothesis of the headline, in the consumer's spelling. -/
abbrev Covariant (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsOf F D) π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ) (s : ℝ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F, ∀ x y : AdelicGL2 (𝓞 F) F → ℂ,
    x ∈ carrier F D π' R' → y ∈ carrier F D π' R' →
    P (fun z => x (z * g)) (fun z => y (z * g)) =
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * P x y

/-- The real `‖·‖ ^ (-t)` character as a complex-valued family on the places: the twist of zone 3. -/
def normTwist (t : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ)

variable {F} {D}

/-- The element of the centre at which the central character is `b v`: `diag (det (heckeGen v))`.
The production pins have `Z = ⊤`, so every idèle qualifies. -/
def detHeckeGenZ (v : HeightOneSpectrum (𝓞 F)) : (pinsOf F D).Z :=
  ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v), Subgroup.mem_top _⟩

/-! ## Zone 1: at `s = 1`, the two eigenvalues are not independent -/

/-- **Zone 1, step 1.** The headline at `s = 1`: the modulus of the central eigenvalue is `1`. -/
theorem norm_b_eq_one (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsOf F D) π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hP : Covariant F D π' R' P 1) (hself : P R'.toFun R'.toFun ≠ 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ R'.exceptionalSet) (hlev : ¬ v.asIdeal ∣ π'.level) :
    ‖π'.b v‖ = 1 := by
  have h := a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero F D π' R' P 1 hP hself
    v hv hlev
  simpa using h.2

/-- **Zone 1, step 2.** The headline's first conjunct at `s = 1`, in the consumer's spelling:
`a v * conj (b v) = conj (a v)`. -/
theorem mul_conj_b_eq_conj_a (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsOf F D) π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hP : Covariant F D π' R' P 1) (hself : P R'.toFun R'.toFun ≠ 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ R'.exceptionalSet) (hlev : ¬ v.asIdeal ∣ π'.level) :
    π'.a v * starRingEnd ℂ (π'.b v) = starRingEnd ℂ (π'.a v) := by
  have h := a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero F D π' R' P 1 hP hself
    v hv hlev
  simpa using h.1

/-- **Zone 1.** At `s = 1` the central eigenvalue is the phase of the Hecke eigenvalue:
`b v = a v / conj (a v)`. Conjugating the headline's product relation gives `conj (a v) * b v = a v`,
and dividing by `conj (a v)` (non-zero because `a v ≠ 0`) reads the Satake parameter off the Hecke
eigenvalue; with zone 1's `norm_b_eq_one`, the normalisation that makes it a phase, the two
eigenvalues carry no information beyond `a v`. -/
theorem b_eq_a_div_conj_a (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsOf F D) π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hP : Covariant F D π' R' P 1) (hself : P R'.toFun R'.toFun ≠ 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ R'.exceptionalSet) (hlev : ¬ v.asIdeal ∣ π'.level)
    (ha : π'.a v ≠ 0) :
    π'.b v = π'.a v / starRingEnd ℂ (π'.a v) := by
  have h1 := mul_conj_b_eq_conj_a π' R' P hP hself hv hlev
  -- the same relation after conjugating: `conj (a v) * b v = a v`
  have h2 : starRingEnd ℂ (π'.a v) * π'.b v = π'.a v := by
    have h := congrArg (starRingEnd ℂ) h1
    rw [map_mul] at h
    rw [show starRingEnd ℂ (starRingEnd ℂ (π'.b v)) = π'.b v from star_star _,
      show starRingEnd ℂ (starRingEnd ℂ (π'.a v)) = π'.a v from star_star _] at h
    exact h
  have hca : starRingEnd ℂ (π'.a v) ≠ 0 := by
    simpa only [starRingEnd_apply, star_ne_zero] using ha
  rw [eq_div_iff hca]
  rw [mul_comm]
  exact h2

/-! ## Zone 2: the normalization `‖b‖ = 1` installs -/

/-- **Zone 2.** At `s = 1` the raw central eigenvalue has modulus `N v⁻¹`, and the central character
of the realization at `diag (det (heckeGen v))` is that same scalar. Composing the headline with
`SmoothCuspRealizationAt.centralChar_det_gen_eq_b` reads the headline as a statement about the
*character*: the arithmetic central character is unitary, while the raw one carries `N v⁻¹`. -/
theorem norm_centralChar_det_heckeGen_eq_inv_absNorm (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsOf F D) π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hP : Covariant F D π' R' P 1) (hself : P R'.toFun R'.toFun ≠ 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ R'.exceptionalSet) (hlev : ¬ v.asIdeal ∣ π'.level) :
    ‖(((R'.centralChar (detHeckeGenZ v) : ℂˣ)) : ℂ)‖ =
      (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := by
  have hb := norm_b_eq_one π' R' P hP hself hv hlev
  have hchar := R'.centralChar_det_gen_eq_b (Φ := π'.toRawCentral) hv
    (detHeckeGenZ v) rfl
  rw [HeckeEigensystem.toRawCentral_b, HeckeEigensystem.cNorm] at hchar
  rw [hchar, norm_mul, hb, mul_one, norm_inv, Complex.norm_natCast]

/-- **Zone 2, the raw eigenvalue itself.** The same composition stated on the eigenvalue rather than
on the character: at `s = 1` the raw-central eigenvalue is `N v⁻¹` in modulus. -/
theorem norm_toRawCentral_b_eq_inv_absNorm (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsOf F D) π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hP : Covariant F D π' R' P 1) (hself : P R'.toFun R'.toFun ≠ 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ R'.exceptionalSet) (hlev : ¬ v.asIdeal ∣ π'.level) :
    ‖π'.toRawCentral.b v‖ = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹ := by
  have hb := norm_b_eq_one π' R' P hP hself hv hlev
  rw [HeckeEigensystem.toRawCentral_b, HeckeEigensystem.cNorm, norm_mul, hb, mul_one, norm_inv,
    Complex.norm_natCast]

/-! ## Zone 3: the `‖·‖ ^ (-t)` twist -/

/-- **Zone 3.** Twisting the eigensystem by the real character `χ t` multiplies the central
eigenvalue by `χ v ^ 2`, so the headline's `‖b v‖ = 1` becomes `‖(twist (χ t)).b v‖ = ‖χ v‖ ^ 2`:
the twist moves the Satake parameter by `N v ^ (-2t)`, and `t = 0` recovers the headline. -/
theorem norm_b_twist (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsOf F D) π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hP : Covariant F D π' R' P 1) (hself : P R'.toFun R'.toFun ≠ 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ R'.exceptionalSet) (hlev : ¬ v.asIdeal ∣ π'.level)
    (t : ℝ) :
    ‖(π'.twist (normTwist (F := F) t)).b v‖ = ‖normTwist (F := F) t v‖ ^ 2 := by
  have hb := norm_b_eq_one π' R' P hP hself hv hlev
  rw [HeckeEigensystem.twist_b, norm_mul, norm_pow, hb, mul_one]

/-- **Zone 3, the exponent form.** The modulus of the twisted central eigenvalue is `N v ^ (-2t)`:
the `‖b‖ = 1` row of the headline is the `t = 0` point of this one-parameter family. -/
theorem norm_b_twist_eq_rpow (π' : HeckeEigensystem F ℂ)
    (R' : SmoothCuspRealizationAt F (pinsOf F D) π'.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) →ₗ⋆[ℂ] ℂ)
    (hP : Covariant F D π' R' P 1) (hself : P R'.toFun R'.toFun ≠ 0)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ R'.exceptionalSet) (hlev : ¬ v.asIdeal ∣ π'.level)
    (t : ℝ) :
    ‖(π'.twist (normTwist (F := F) t)).b v‖ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-2 * t) := by
  have h := norm_b_twist π' R' P hP hself hv hlev t
  have hN : (0 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := Nat.cast_nonneg _
  have he : (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-t)) ^ 2 =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-t * 2) := by
    rw [show (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-t)) ^ 2 =
        (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-t)) ^ (2 : ℝ) from (Real.rpow_natCast _ 2).symm,
      ← Real.rpow_mul hN]
  rw [h, normTwist, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hN _), he,
    show -t * 2 = -2 * t by ring]

end SetAF35AConsumer
