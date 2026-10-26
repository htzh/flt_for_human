/-
  The log-derivative — "order" — reading of Pompeiu's identity for a locally meromorphic `F`.

  Pompeiu's identity as it was ported in `Pompeiu.lean` reads, for a `C¹` function `h` with
  compact support in an open `U` and a function `F` with only *simple* poles on `U`,

  `∫ z, F z * ∂̄h z = -π * ∑ᶠ a, (residue of F at a) * h a`.

  The two theorems here are that identity with `F` replaced by the *logarithmic derivative*
  `F'/F`, whose poles are simple and whose residue at `a` is the order of `F` at `a`.  So the sum
  of residues becomes a sum of orders, and no simple-pole hypothesis is needed: `F` meromorphic on
  `U` with finite order everywhere suffices, because `F'/F` automatically has only simple poles
  there.  This is the form the period theory consumes — `∑ᶠ a, ordₐ F * E a * h a` is the divisor
  sum of the meromorphic section `F`, weighted by the test function `h`.

  The second theorem is the same identity in the normal form `Φ = (z - τ) ^ (n τ) * Ψ` that a
  meromorphic function takes near each point of its divisor: the local branch is split off, and
  what remains is the *wedge*
  `fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1`
  of `Φ` and `h` — a 2×2 Jacobian determinant, i.e. the Jacobian of `(Φ, h)` as a map `ℝ² → ℝ²`,
  not a differential form.  Its integral vanishes against a holomorphic `Φ` (`integral_wedge_eq_zero`
  below is exactly the `∂̄` identity in this disguise, integration by parts plus symmetry of the
  second derivative), which is why the identity can be written with the wedge on the left.  The
  statement also asserts the integrability of both integrands, because `E / Φ` has poles on the
  divisor of `Φ` and the wedge is what makes the product integrable: on a disc around a point `τ`
  with `Φ = (z - τ)^{n τ} Ψ` the wedge is a bounded factor times `∂̄(E · k)`, so the singularity is
  that of `(z - τ)⁻¹ · ∂̄(E · k)` — order one, hence locally integrable.

  The method of proof of the second theorem is a partition of unity: cover the compact support of
  `h` by finitely many discs on which the normal form holds with a branch of the logarithm, split
  `h = ∑ i, h * ρ i` through a smooth partition of unity subordinate to the cover, and reduce to a
  global statement on each disc.  On a disc the identity is elementary: write the integrands through
  `∂̄` and `∂Φ/Φ`, apply the Cauchy-kernel identity
  `∫ z, (z - a)⁻¹ * ∂̄k z = -π * k a` from `Pompeiu.lean` to the first summand and the vanishing of
  the wedge integral to the second; the `∑ᶠ` over all of `ℂ` collapses to the single term at the
  centre of the disc because `n` vanishes on the punctured disc (it is `0` wherever `Φ` is
  continuous and non-zero).

  spec-pin: Theorems/Thm_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum.lean
  spec-pin: Theorems/Thm_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.lean
  spec-pin: P2M/Sol/S_Complex_integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum.lean   -- comparable copy
  spec-pin: P2M/Sol/S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.lean   -- comparable copy
-/
import FLTForHuman.Analysis.Complex.Pompeiu
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Metric Set Function
open scoped Topology Real Manifold

namespace Complex

/-! ### The logarithmic derivative: poles of order one

`F'/F` has, near a point `a` where `ordₐ F = n`, the form `n / (z - a) + (analytic)`.  That is the
simple-pole hypothesis of `integral_mul_dbar_eq_neg_pi_mul_finsum_residue`, with residue `n`. -/

/-- A statement that holds in the punctured neighbourhood of every point near `z` also holds
almost everywhere near `z`. -/
private theorem eventually_nhdsNE_eventually_nhds {z : ℂ} {P : ℂ → Prop}
    (h : ∀ᶠ w in 𝓝[≠] z, P w) : ∀ᶠ w in 𝓝[≠] z, ∀ᶠ u in 𝓝 w, P u := by
  rw [eventually_nhdsWithin_iff] at h ⊢
  filter_upwards [h.eventually_nhds] with w hw hwz
  have hne : ∀ᶠ u in 𝓝 w, u ≠ z := isOpen_ne.eventually_mem hwz
  filter_upwards [hw, hne] with u hu hune using hu hune

/-- The logarithmic derivative of `(w - a) ^ n * G w` at `z ≠ a`, where `G` is differentiable at
`z` and does not vanish there. -/
private theorem deriv_zpow_mul_div {G : ℂ → ℂ} {a z : ℂ} (n : ℤ) (hza : z ≠ a)
    (hG : DifferentiableAt ℂ G z) (hG0 : G z ≠ 0) :
    deriv (fun w => (w - a) ^ n * G w) z / ((z - a) ^ n * G z) =
      (n : ℂ) / (z - a) + deriv G z / G z := by
  have hsub : z - a ≠ 0 := sub_ne_zero.2 hza
  have h1 : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1) * 1) z := by
    have := (hasDerivAt_zpow n (z - a) (Or.inl hsub)).comp z ((hasDerivAt_id z).sub_const a)
    exact this
  have h2 : HasDerivAt (fun w : ℂ => (w - a) ^ n * G w)
      ((n : ℂ) * (z - a) ^ (n - 1) * 1 * G z + (z - a) ^ n * deriv G z) z :=
    h1.mul hG.hasDerivAt
  rw [h2.deriv, zpow_sub_one₀ hsub]
  have hpow : (z - a) ^ n ≠ 0 := zpow_ne_zero n hsub
  field_simp

/-- The divided slope of an analytic function is analytic: the difference quotient
`(E z - E a) / (z - a)` extends across `a`. -/
private theorem analyticAt_dslope {E : ℂ → ℂ} {a : ℂ} (hE : AnalyticAt ℂ E a) :
    AnalyticAt ℂ (dslope E a) a := by
  obtain ⟨p, hp⟩ := hE
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

/-- Near a point of finite order `n`, the logarithmic derivative of `F` has a simple pole with
residue `n`. -/
private theorem logDeriv_simplePole {F E : ℂ → ℂ} {a : ℂ} (hF : MeromorphicAt F a) {n : ℤ}
    (hn : meromorphicOrderAt F a = (n : WithTop ℤ)) (hE : AnalyticAt ℂ E a) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, E z * (deriv F z / F z) = (n : ℂ) * E a / (z - a) + g z := by
  obtain ⟨G, hGan, hG0, hev⟩ := (meromorphicOrderAt_eq_int_iff hF).1 hn
  refine ⟨fun z => (n : ℂ) * dslope E a z + E z * (deriv G z / G z),
    (analyticAt_const.mul (analyticAt_dslope hE)).add (hE.mul (hGan.deriv.div hGan hG0)), ?_⟩
  have ha : ∀ᶠ z in 𝓝[≠] a, AnalyticAt ℂ G z :=
    eventually_nhdsWithin_of_eventually_nhds hGan.eventually_analyticAt
  have hb : ∀ᶠ z in 𝓝[≠] a, G z ≠ 0 :=
    eventually_nhdsWithin_of_eventually_nhds (hGan.continuousAt.eventually_ne hG0)
  have hd : ∀ᶠ z in 𝓝[≠] a, z ≠ a := eventually_mem_nhdsWithin
  filter_upwards [eventually_nhdsNE_eventually_nhds hev, ha, hb, hd, hev] with z hz hGz hGz0 hza hfz
  have hderiv : deriv F z = deriv (fun w => (w - a) ^ n * G w) z := by
    refine Filter.EventuallyEq.deriv_eq ?_
    filter_upwards [hz] with u hu
    rw [hu, smul_eq_mul]
  rw [hderiv, hfz, smul_eq_mul, deriv_zpow_mul_div n hza hGz.differentiableAt hGz0,
    dslope_of_ne _ hza, slope_def_field]
  have hsub : z - a ≠ 0 := sub_ne_zero.2 hza
  field_simp
  ring

/-! ### The order form of Pompeiu's identity -/

/-- **Pompeiu's identity for a logarithmic derivative.**  For `F` meromorphic on an open `U` with
finite order at every point, `E` holomorphic on `U` and `h` of class `C¹` with compact support in
`U`, the integral of `E * (F'/F) * ∂̄h` is `-π` times the order-weighted sum of `E * h`. -/
theorem integral_mul_logDeriv_mul_dbar_eq_neg_pi_mul_finsum (U : Set ℂ) (hU : IsOpen U)
    (F : ℂ → ℂ) (hF : ∀ z ∈ U, MeromorphicAt F z) (hF' : ∀ z ∈ U, meromorphicOrderAt F z ≠ ⊤)
    (E : ℂ → ℂ) (hE : DifferentiableOn ℂ E U) (h : ℂ → ℂ) (hh : ContDiff ℝ 1 h)
    (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    ∫ z, E z * (deriv F z / F z) * ((fderiv ℝ h z 1 + I * fderiv ℝ h z I) / 2) =
      -π * ∑ᶠ a, (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a * h a := by
  have hEan : AnalyticOnNhd ℂ E U := hE.analyticOnNhd hU
  set c : ℂ → ℂ := fun a => (((meromorphicOrderAt F a).untop₀ : ℤ) : ℂ) * E a with hc
  have hloc : ∀ a ∈ U, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, E z * (deriv F z / F z) = c a / (z - a) + g z := by
    intro a ha
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 (hF' a ha)
    obtain ⟨g, hg, hev⟩ := logDeriv_simplePole (hF a ha) hn.symm (hEan a ha)
    refine ⟨g, hg, ?_⟩
    have hca : c a = (n : ℂ) * E a := by simp [hc, ← hn]
    rw [hca]
    exact hev
  have := Complex.integral_mul_dbar_eq_neg_pi_mul_finsum_residue U hU
    (fun z => E z * (deriv F z / F z)) c hloc h hh hsupp hU'
  simpa only [hc, mul_assoc] using this

/-! ### The wedge of two functions, and integration by parts

For `u v : ℂ → ℂ` the *wedge* `fderiv ℝ u z 1 * fderiv ℝ v z I - fderiv ℝ u z I * fderiv ℝ v z 1`
is the Jacobian determinant of `(u, v)` at `z`.  Against a compactly supported `C²` `v` and a `C¹`
`u` it integrates to zero: integrate each summand by parts over `1` and `I` respectively, and the
two boundary terms cancel because the mixed second partials of `v` agree. -/

private theorem integrable_mul_of_tsupport_subset_swap {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgV : tsupport g ⊆ V) : Integrable fun z => g z * f z := by
  simpa only [mul_comm] using integrable_mul_of_tsupport_subset hV hf hg hgs hgV

/-- For a `C¹` compactly supported `ψ`, the map `z ↦ fderiv ℝ ψ z v` is continuous, compactly
supported, and supported in the support of `ψ`. -/
private theorem fderiv_apply_props {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ)
    (v : ℂ) :
    Continuous (fun z => fderiv ℝ ψ z v) ∧ HasCompactSupport (fun z => fderiv ℝ ψ z v) ∧
      tsupport (fun z => fderiv ℝ ψ z v) ⊆ tsupport ψ :=
  ⟨(hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const, hψs.fderiv_apply ℝ v,
    tsupport_fderiv_apply_subset ℝ v⟩

private theorem contDiff_fderiv_apply {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) (w : ℂ) :
    ContDiff ℝ 1 fun z => fderiv ℝ v z w := by
  have h : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (m := 1) (by norm_num)
  exact h.clm_apply contDiff_const

/-- The mixed second partials of a `C²` function agree, read through `fderiv`. -/
private theorem mixed_partials_symm {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) (z a b : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ v w a) z b = fderiv ℝ (fun w => fderiv ℝ v w b) z a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  have hs : IsSymmSndFDerivAt ℝ v z :=
    hv.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  exact hs.eq b a

/-- **Vanishing of the wedge integral.**  For `u` of class `C¹` on an open `O` and `v` of class
`C²` with compact support in `O`, the integral of the Jacobian determinant of `(u, v)` is zero. -/
private theorem integral_wedge_eq_zero {O : Set ℂ} (hO : IsOpen O) {u v : ℂ → ℂ}
    (hu : ContDiffOn ℝ 1 u O) (hv : ContDiff ℝ 2 v) (hvs : HasCompactSupport v)
    (hvO : tsupport v ⊆ O) :
    ∫ z, (fderiv ℝ u z 1 * fderiv ℝ v z I - fderiv ℝ u z I * fderiv ℝ v z 1) = 0 := by
  set vx : ℂ → ℂ := fun z => fderiv ℝ v z 1 with hvx
  set vy : ℂ → ℂ := fun z => fderiv ℝ v z I with hvy
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  obtain ⟨hvxc, hvxs, hvxt⟩ := fderiv_apply_props hv1 hvs 1
  obtain ⟨hvyc, hvys, hvyt⟩ := fderiv_apply_props hv1 hvs I
  have hvxO : tsupport vx ⊆ O := hvxt.trans hvO
  have hvyO : tsupport vy ⊆ O := hvyt.trans hvO
  have hvxd : ContDiff ℝ 1 vx := contDiff_fderiv_apply hv 1
  have hvyd : ContDiff ℝ 1 vy := contDiff_fderiv_apply hv I

  have huc : ContinuousOn u O := hu.continuousOn
  have hu' : ContinuousOn (fderiv ℝ u) O := hu.continuousOn_fderiv_of_isOpen hO le_rfl
  have hux : ContinuousOn (fun z => fderiv ℝ u z 1) O := hu'.clm_apply continuousOn_const
  have huy : ContinuousOn (fun z => fderiv ℝ u z I) O := hu'.clm_apply continuousOn_const
  have hud : ∀ z ∈ O, DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn one_ne_zero z hz).differentiableAt (hO.mem_nhds hz)

  obtain ⟨hvyxc, hvyxs, hvyxt⟩ := fderiv_apply_props hvyd hvys 1
  obtain ⟨hvxyc, hvxys, hvxyt⟩ := fderiv_apply_props hvxd hvxs I

  have ibp1 : ∫ z, vy z * fderiv ℝ u z 1 = -∫ z, fderiv ℝ vy z 1 * u z := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of_tsupport_subset_swap hO huc hvyxc hvyxs (hvyxt.trans hvyO)
    · exact integrable_mul_of_tsupport_subset_swap hO hux hvyc hvys hvyO
    · exact integrable_mul_of_tsupport_subset_swap hO huc hvyc hvys hvyO
    · intro x _; exact (hvyd.differentiable one_ne_zero) x
    · intro x hx; exact hud x (hvyO hx)

  have ibp2 : ∫ z, vx z * fderiv ℝ u z I = -∫ z, fderiv ℝ vx z I * u z := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of_tsupport_subset_swap hO huc hvxyc hvxys (hvxyt.trans hvxO)
    · exact integrable_mul_of_tsupport_subset_swap hO huy hvxc hvxs hvxO
    · exact integrable_mul_of_tsupport_subset_swap hO huc hvxc hvxs hvxO
    · intro x _; exact (hvxd.differentiable one_ne_zero) x
    · intro x hx; exact hud x (hvxO hx)

  have hsymm : ∀ z, fderiv ℝ vy z 1 = fderiv ℝ vx z I := fun z => mixed_partials_symm hv z I 1
  have hI1 : Integrable fun z => vy z * fderiv ℝ u z 1 :=
    integrable_mul_of_tsupport_subset_swap hO hux hvyc hvys hvyO
  have hI2 : Integrable fun z => vx z * fderiv ℝ u z I :=
    integrable_mul_of_tsupport_subset_swap hO huy hvxc hvxs hvxO
  calc ∫ z, (fderiv ℝ u z 1 * fderiv ℝ v z I - fderiv ℝ u z I * fderiv ℝ v z 1)
      = ∫ z, (vy z * fderiv ℝ u z 1 - vx z * fderiv ℝ u z I) := by
        congr 1; funext z; simp only [hvx, hvy]; ring
    _ = (∫ z, vy z * fderiv ℝ u z 1) - ∫ z, vx z * fderiv ℝ u z I := integral_sub hI1 hI2
    _ = 0 := by
        rw [ibp1, ibp2]
        simp only [hsymm, sub_self]

/-! ### `∂̄` transfers to compactly supported functions -/

/-! ### The Cauchy kernel times a compactly supported continuous function

`z ↦ (z - a)⁻¹ * u z` is integrable for continuous compactly supported `u`: the singularity is
locally integrable in two real dimensions, and `u` is bounded and vanishes far out. -/

/-! ### The local model `Φ = (z - a) ^ n * Ψ` on a disc

On a disc where `Ψ` is `C¹` and within a factor `1` of its centre value (so that `Ψ z / Ψ a` stays
in the slit plane), `Ψ` admits a holomorphic logarithm `localLog Ψ a`.  Writing `Φ` through that
logarithm turns `∂̄Φ / Φ` into a simple pole plus the `∂̄` of the logarithm, and the wedge
`fderiv Φ 1 * fderiv k I - fderiv Φ I * fderiv k 1` into the sum of three integrable pieces. -/

private def localLog (Ψ : ℂ → ℂ) (a z : ℂ) : ℂ := log (Ψ z * (Ψ a)⁻¹)

private theorem mul_inv_mem_slitPlane {a : ℂ} {r : ℝ} {Ψ : ℂ → ℂ}
    (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1) {z : ℂ} (hz : z ∈ ball a r) :
    Ψ z * (Ψ a)⁻¹ ∈ slitPlane := by
  have : Ψ z * (Ψ a)⁻¹ = 1 + (Ψ z * (Ψ a)⁻¹ - 1) := by ring
  rw [this]; exact mem_slitPlane_of_norm_lt_one (hΨ1 z hz)

private theorem localFactor_ne_zero {a : ℂ} {r : ℝ} {Ψ : ℂ → ℂ}
    (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1) {z : ℂ}
    (hz : z ∈ ball a r) : Ψ z ≠ 0 := by
  have := slitPlane_ne_zero (mul_inv_mem_slitPlane hΨ1 hz)
  exact left_ne_zero_of_mul this

private theorem contDiffOn_localLog {a : ℂ} {r : ℝ} {Ψ : ℂ → ℂ}
    (hΨ : ContDiffOn ℝ 1 Ψ (ball a r))
    (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1) :
    ContDiffOn ℝ 1 (localLog Ψ a) (ball a r) := by
  intro z hz
  have h1 : ContDiffWithinAt ℝ 1 (fun w => Ψ w * (Ψ a)⁻¹) (ball a r) z :=
    (hΨ z hz).mul contDiffWithinAt_const
  have h2 : ContDiffAt ℝ 1 log (Ψ z * (Ψ a)⁻¹) :=
    (Complex.contDiffAt_log (mul_inv_mem_slitPlane hΨ1 hz)).restrict_scalars ℝ
  exact h2.comp_contDiffWithinAt z h1

private theorem exp_localLog {a : ℂ} {r : ℝ} {Ψ : ℂ → ℂ}
    (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1) (hΨa : Ψ a ≠ 0) {z : ℂ}
    (hz : z ∈ ball a r) : exp (localLog Ψ a z) = Ψ z * (Ψ a)⁻¹ :=
  Complex.exp_log (mul_ne_zero (localFactor_ne_zero hΨ1 hz) (inv_ne_zero hΨa))

private theorem fderiv_eq_smul_fderiv_localLog {a : ℂ} {r : ℝ} {Ψ : ℂ → ℂ}
    (hΨ : ContDiffOn ℝ 1 Ψ (ball a r))
    (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1) (hΨa : Ψ a ≠ 0) {z : ℂ}
    (hz : z ∈ ball a r) : fderiv ℝ Ψ z = Ψ z • fderiv ℝ (localLog Ψ a) z := by
  have hLd : DifferentiableAt ℝ (localLog Ψ a) z :=
    ((contDiffOn_localLog hΨ hΨ1).differentiableOn one_ne_zero z hz).differentiableAt
      (isOpen_ball.mem_nhds hz)
  have hΨd : DifferentiableAt ℝ Ψ z :=
    ((hΨ.differentiableOn one_ne_zero) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  have hcomp : HasFDerivAt (fun w => exp (localLog Ψ a w))
      (exp (localLog Ψ a z) • fderiv ℝ (localLog Ψ a) z) z :=
    (Complex.hasDerivAt_exp _).comp_hasFDerivAt z hLd.hasFDerivAt
  have hev : (fun w => exp (localLog Ψ a w)) =ᶠ[𝓝 z] fun w => Ψ w * (Ψ a)⁻¹ := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using exp_localLog hΨ1 hΨa hw
  have h1 : HasFDerivAt (fun w => Ψ w * (Ψ a)⁻¹)
      (exp (localLog Ψ a z) • fderiv ℝ (localLog Ψ a) z) z :=
    hcomp.congr_of_eventuallyEq hev.symm
  have h2 : HasFDerivAt (fun w => Ψ w * (Ψ a)⁻¹) ((Ψ a)⁻¹ • fderiv ℝ Ψ z) z := by
    have := hΨd.hasFDerivAt.mul_const (Ψ a)⁻¹
    simpa [mul_comm] using this
  have heq := h1.unique h2
  rw [exp_localLog hΨ1 hΨa hz] at heq
  have : fderiv ℝ Ψ z = (Ψ a) • ((Ψ a)⁻¹ • fderiv ℝ Ψ z) := by
    rw [smul_smul, mul_inv_cancel₀ hΨa, one_smul]
  rw [this, ← heq, smul_smul]
  congr 1
  field_simp

/-! ### The coefficient times the test function on a disc -/

/-- The pointwise product of a coefficient function and a localized test function. -/
private def mulFun (E k : ℂ → ℂ) (z : ℂ) : ℂ := E z * k z

private theorem analyticOnNhd_of_hasDerivAt {a : ℂ} {r : ℝ} {E E' : ℂ → ℂ}
    (hE : ∀ z ∈ ball a r, HasDerivAt E (E' z) z) : AnalyticOnNhd ℂ E (ball a r) := by
  have hd : DifferentiableOn ℂ E (ball a r) := fun z hz =>
    (hE z hz).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd isOpen_ball

private theorem contDiffAt_of_analyticOnNhd {a : ℂ} {r : ℝ} {E E' : ℂ → ℂ}
    (hE : ∀ z ∈ ball a r, HasDerivAt E (E' z) z) {z : ℂ} (hz : z ∈ ball a r) (m : ℕ∞) :
    ContDiffAt ℝ m E z :=
  ((analyticOnNhd_of_hasDerivAt hE z hz).contDiffAt (n := m)).restrict_scalars ℝ

private theorem continuousOn_deriv_of_hasDerivAt {a : ℂ} {r : ℝ} {E E' : ℂ → ℂ}
    (hE : ∀ z ∈ ball a r, HasDerivAt E (E' z) z) : ContinuousOn E' (ball a r) := by
  have h1 : ContinuousOn (deriv E) (ball a r) := (analyticOnNhd_of_hasDerivAt hE).deriv.continuousOn
  refine h1.congr fun z hz => ?_
  exact ((hE z hz).deriv).symm

private theorem contDiff_mulFun {a : ℂ} {r : ℝ} {E E' k : ℂ → ℂ}
    (hE : ∀ z ∈ ball a r, HasDerivAt E (E' z) z) (hk : ContDiff ℝ 2 k)
    (hkr : tsupport k ⊆ ball a r) : ContDiff ℝ 2 (mulFun E k) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ ball a r
  · exact (contDiffAt_of_analyticOnNhd hE hz 2).mul hk.contDiffAt
  · have hz' : z ∉ tsupport k := fun h' => hz (hkr h')
    have h0 : k =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
    have : mulFun E k =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with w hw
      simp [mulFun, hw]
    exact contDiffAt_const.congr_of_eventuallyEq this

private theorem hasCompactSupport_mulFun (E : ℂ → ℂ) {k : ℂ → ℂ} (hks : HasCompactSupport k) :
    HasCompactSupport (mulFun E k) := hks.mul_left

private theorem tsupport_mulFun_subset (E k : ℂ → ℂ) : tsupport (mulFun E k) ⊆ tsupport k :=
  closure_minimal (fun _ hz => subset_tsupport _ (right_ne_zero_of_mul hz)) (isClosed_tsupport _)

private theorem fderiv_mulFun {a : ℂ} {r : ℝ} {E E' k : ℂ → ℂ}
    (hE : ∀ z ∈ ball a r, HasDerivAt E (E' z) z) (hk : ContDiff ℝ 2 k)
    {z : ℂ} (hz : z ∈ ball a r) (w : ℂ) :
    fderiv ℝ (mulFun E k) z w = E z * fderiv ℝ k z w + k z * (E' z * w) := by
  have h1 : HasFDerivAt E (E' z • (1 : ℂ →L[ℝ] ℂ)) z := (hE z hz).complexToReal_fderiv
  have h2 : HasFDerivAt k (fderiv ℝ k z) z := (hk.differentiable (by norm_num) z).hasFDerivAt
  have h3 : HasFDerivAt (mulFun E k) (E z • fderiv ℝ k z + k z • E' z • (1 : ℂ →L[ℝ] ℂ)) z :=
    h1.mul h2
  rw [h3.fderiv]
  simp [smul_eq_mul, mul_comm]

private theorem dbar_mulFun {a : ℂ} {r : ℝ} {E E' k : ℂ → ℂ}
    (hE : ∀ z ∈ ball a r, HasDerivAt E (E' z) z) (hk : ContDiff ℝ 2 k)
    (hkr : tsupport k ⊆ ball a r) (z : ℂ) : dbar (mulFun E k) z = E z * dbar k z := by
  by_cases hz : z ∈ ball a r
  · simp only [dbar, fderiv_mulFun hE hk hz]
    have : I * I = -1 := Complex.I_mul_I
    linear_combination (k z * E' z / 2) * this
  · have hzk : z ∉ tsupport k := fun h' => hz (hkr h')
    have hzv : z ∉ tsupport (mulFun E k) := fun h' => hzk (tsupport_mulFun_subset E k h')
    rw [dbar_eq_zero_of_notMem_tsupport hzv, dbar_eq_zero_of_notMem_tsupport hzk, mul_zero]

private theorem fderiv_div_eq_localLog {a : ℂ} {r : ℝ} {n : ℤ} {Ψ Φ : ℂ → ℂ}
    (hΨ : ContDiffOn ℝ 1 Ψ (ball a r))
    (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1) (hΨa : Ψ a ≠ 0)
    (hΦ : ∀ z ∈ ball a r, Φ z = (z - a) ^ n * Ψ z) {z : ℂ} (hz : z ∈ ball a r) (hza : z ≠ a)
    (w : ℂ) : fderiv ℝ Φ z w / Φ z = n * w / (z - a) + fderiv ℝ (localLog Ψ a) z w := by
  have hd : z - a ≠ 0 := sub_ne_zero.2 hza
  have hΨz : Ψ z ≠ 0 := localFactor_ne_zero hΨ1 hz
  have hΨd : DifferentiableAt ℝ Ψ z :=
    ((hΨ.differentiableOn one_ne_zero) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  have hp : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1)) z := by
    have := (hasDerivAt_zpow n (z - a) (Or.inl hd)).comp z ((hasDerivAt_id z).sub_const a)
    simp at this
    exact this
  have hmodel : HasFDerivAt (fun w => (w - a) ^ n * Ψ w)
      ((z - a) ^ n • fderiv ℝ Ψ z +
        Ψ z • (((n : ℂ) * (z - a) ^ (n - 1)) • (1 : ℂ →L[ℝ] ℂ))) z :=
    hp.complexToReal_fderiv.mul hΨd.hasFDerivAt
  have hev : Φ =ᶠ[𝓝 z] fun w => (w - a) ^ n * Ψ w := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hΦ w hw
  have hΦd : HasFDerivAt Φ _ z := hmodel.congr_of_eventuallyEq hev
  rw [hΦd.fderiv, hΦ z hz, fderiv_eq_smul_fderiv_localLog hΨ hΨ1 hΨa hz]
  simp only [add_apply, smul_apply, one_apply_eq_self, smul_eq_mul]
  have hp' : (z - a) ^ (n - 1) = (z - a) ^ n / (z - a) := by
    rw [zpow_sub_one₀ hd, div_eq_mul_inv]
  rw [hp']
  have hzn : (z - a) ^ n ≠ 0 := zpow_ne_zero _ hd
  field_simp
  ring

private theorem ne_zero_of_local_form {a : ℂ} {r : ℝ} {n : ℤ} {Ψ Φ : ℂ → ℂ}
    (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1)
    (hΦ : ∀ z ∈ ball a r, Φ z = (z - a) ^ n * Ψ z) {z : ℂ} (hz : z ∈ ball a r)
    (hza : z ≠ a) : Φ z ≠ 0 := by
  rw [hΦ z hz]
  exact mul_ne_zero (zpow_ne_zero _ (sub_ne_zero.2 hza)) (localFactor_ne_zero hΨ1 hz)

/-! ### The identity on one disc

On a disc carrying the local model, the wedge integrand splits as
`-2 I n * (z - a)⁻¹ * ∂̄(E k) + wedge(log Ψ, E k) - 2 I * E' * ∂̄(log Ψ) * k`.  The first summand
integrates to `-π * E a * k a` by the Cauchy kernel, the second vanishes by
`integral_wedge_eq_zero`, and the third is an explicit integral.  All three are integrable, which
gives the two integrability conjuncts. -/

private theorem integral_wedge_identity_on_ball {a : ℂ} {r : ℝ} {n : ℤ} {Ψ Φ E E' k : ℂ → ℂ}
    (hΨ : ContDiffOn ℝ 1 Ψ (ball a r))
    (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1) (hΨa : Ψ a ≠ 0)
    (hΦ : ∀ z ∈ ball a r, Φ z = (z - a) ^ n * Ψ z)
    (hE : ∀ z ∈ ball a r, HasDerivAt E (E' z) z)
    (hk : ContDiff ℝ 2 k) (hks : HasCompactSupport k) (hkr : tsupport k ⊆ ball a r) :
    Integrable (fun z => E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1)) ∧
    Integrable (fun z => E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
    I / π * (∫ z, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1)) +
      2 * ((n : ℂ) * E a * k a) =
    2 / π * ∫ z, E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by
  have hv2 : ContDiff ℝ 2 (mulFun E k) := contDiff_mulFun hE hk hkr
  have hv1 : ContDiff ℝ 1 (mulFun E k) := hv2.of_le (by norm_num)
  have hvs : HasCompactSupport (mulFun E k) := hasCompactSupport_mulFun E hks
  have hvt : tsupport (mulFun E k) ⊆ ball a r := (tsupport_mulFun_subset E k).trans hkr
  have hLg := contDiffOn_localLog hΨ hΨ1
  have hLg' : ContinuousOn (fderiv ℝ (localLog Ψ a)) (ball a r) :=
    hLg.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hLx : ContinuousOn (fun z => fderiv ℝ (localLog Ψ a) z 1) (ball a r) :=
    hLg'.clm_apply continuousOn_const
  have hLy : ContinuousOn (fun z => fderiv ℝ (localLog Ψ a) z I) (ball a r) :=
    hLg'.clm_apply continuousOn_const
  have hDL : ContinuousOn (dbar (localLog Ψ a)) (ball a r) := by
    unfold dbar; exact (hLx.add (continuousOn_const.mul hLy)).div_const _
  have hE'c := continuousOn_deriv_of_hasDerivAt hE

  set P1 : ℂ → ℂ := fun z => (z - a)⁻¹ * dbar (mulFun E k) z with hP1
  set P2 : ℂ → ℂ := fun z => fderiv ℝ (localLog Ψ a) z 1 * fderiv ℝ (mulFun E k) z I -
    fderiv ℝ (localLog Ψ a) z I * fderiv ℝ (mulFun E k) z 1 with hP2
  set P3 : ℂ → ℂ := fun z => E' z * dbar (localLog Ψ a) z * k z with hP3
  have iP1 : Integrable P1 := integrable_inv_sub_mul a (dbar_continuous hv1) (dbar_hasCompactSupport hvs)
  obtain ⟨hvxc, hvxs, hvxt⟩ := fderiv_apply_props hv1 hvs 1
  obtain ⟨hvyc, hvys, hvyt⟩ := fderiv_apply_props hv1 hvs I
  have iP2 : Integrable P2 :=
    (integrable_mul_of_tsupport_subset isOpen_ball hLx hvyc hvys (hvyt.trans hvt)).sub
      (integrable_mul_of_tsupport_subset isOpen_ball hLy hvxc hvxs (hvxt.trans hvt))
  have iP3 : Integrable P3 :=
    integrable_mul_of_tsupport_subset isOpen_ball (hE'c.mul hDL) hk.continuous hks hkr

  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ a := by
    have : ({a}ᶜ : Set ℂ) ∈ ae (volume : Measure ℂ) := compl_mem_ae_iff.2 (measure_singleton a)
    filter_upwards [this] with z hz using hz
  have hpt1 : ∀ z, z ≠ a → E z / Φ z *
      (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1) =
      -2 * I * n * P1 z + P2 z - 2 * I * P3 z := by
    intro z hza
    by_cases hz : z ∈ ball a r
    · have hΦz : Φ z ≠ 0 := ne_zero_of_local_form hΨ1 hΦ hz hza
      have hd : z - a ≠ 0 := sub_ne_zero.2 hza
      have h1 := fderiv_div_eq_localLog hΨ hΨ1 hΨa hΦ hz hza 1
      have hI := fderiv_div_eq_localLog hΨ hΨ1 hΨa hΦ hz hza I
      rw [div_eq_iff hΦz] at h1 hI
      simp only [hP1, hP2, hP3, fderiv_mulFun hE hk hz, dbar]
      rw [h1, hI]
      have hII : I * I = -1 := Complex.I_mul_I
      field_simp
      linear_combination ((n : ℂ) * k z * E' z * I + E z * n * fderiv ℝ k z I +
        (z - a) * fderiv ℝ (localLog Ψ a) z I * k z * E' z) * hII
    · have hzk : z ∉ tsupport k := fun h' => hz (hkr h')
      have hzv : z ∉ tsupport (mulFun E k) := fun h' => hz (hvt h')
      simp only [hP1, hP2, hP3, fderiv_of_notMem_tsupport ℝ hzk, fderiv_of_notMem_tsupport ℝ hzv,
        image_eq_zero_of_notMem_tsupport hzk, dbar_eq_zero_of_notMem_tsupport hzv]
      simp
  have hpt2 : ∀ z, z ≠ a →
      E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) = P3 z := by
    intro z hza
    by_cases hz : z ∈ ball a r
    · have hΦz : Φ z ≠ 0 := ne_zero_of_local_form hΨ1 hΦ hz hza
      have hd : z - a ≠ 0 := sub_ne_zero.2 hza
      have h1 := fderiv_div_eq_localLog hΨ hΨ1 hΨa hΦ hz hza 1
      have hI := fderiv_div_eq_localLog hΨ hΨ1 hΨa hΦ hz hza I
      rw [div_eq_iff hΦz] at h1 hI
      simp only [hP3, dbar]
      rw [h1, hI]
      have hII : I * I = -1 := Complex.I_mul_I
      field_simp
      linear_combination ((n : ℂ) * k z * E' z) * hII
    · have hzk : z ∉ tsupport k := fun h' => hz (hkr h')
      simp only [hP3, image_eq_zero_of_notMem_tsupport hzk]
      simp
  have hae1 : (fun z => E z / Φ z *
      (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1)) =ᵐ[volume]
      fun z => -2 * I * n * P1 z + P2 z - 2 * I * P3 z := by
    filter_upwards [hae] with z hz using hpt1 z hz
  have hae2 : (fun z => E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) =ᵐ[volume]
      P3 := by
    filter_upwards [hae] with z hz using hpt2 z hz
  have iA1 : Integrable fun z => -2 * I * n * P1 z := iP1.const_mul _
  have iA : Integrable fun z => -2 * I * n * P1 z + P2 z := iA1.add iP2
  have iB : Integrable fun z => 2 * I * P3 z := iP3.const_mul _
  have iRHS : Integrable fun z => -2 * I * n * P1 z + P2 z - 2 * I * P3 z := iA.sub iB
  refine ⟨iRHS.congr hae1.symm, iP3.congr hae2.symm, ?_⟩
  rw [integral_congr_ae hae1, integral_congr_ae hae2, integral_sub iA iB, integral_add iA1 iP2,
    integral_const_mul, integral_const_mul]

  have vP1 : ∫ z, P1 z = -π * (E a * k a) := by
    have := integral_inv_sub_mul_dbar_eq_neg_pi_mul a (mulFun E k) hv1 hvs
    simpa [hP1, mulFun] using this
  have vP2 : ∫ z, P2 z = 0 := integral_wedge_eq_zero isOpen_ball hLg hv2 hvs hvt
  rw [vP1, vP2]
  have hI : I * I = -1 := Complex.I_mul_I
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination (2 * (n : ℂ) * (E a * k a) * π - 2 * ∫ z, P3 z) * hI

/-! ### The global statement, by a partition of unity

`n` vanishes wherever `Φ` is continuous and non-zero, since the local model `Φ = (z - τ) ^ (n τ) Ψ`
with `Ψ τ ≠ 0` shows that a non-zero value of `Φ` forces `n a = 0`.  Covering the compact support of
`h` by finitely many discs carrying the local model, a smooth partition of unity splits `h` into
summands supported in those discs, and on each disc the identity is
`integral_wedge_identity_on_ball`.  The `∑ᶠ` over all of `ℂ` collapses to `∑ i, n i * E i * k i i`
because `n` vanishes off the diagonal. -/

private theorem order_eq_zero_of_continuousAt {U : Set ℂ} {Φ : ℂ → ℂ} {n : ℂ → ℤ}
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    {a : ℂ} (ha : a ∈ U) (hc : ContinuousAt Φ a) (hΦa : Φ a ≠ 0) : n a = 0 := by
  obtain ⟨Ψ, hΨ, hΨ0, hev⟩ := hloc a ha
  rcases lt_trichotomy (n a) 0 with hlt | heq | hgt
  ·
    exfalso
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -n a = (m : ℤ) := ⟨(-n a).toNat, by omega⟩
    have hm0 : 0 < m := by omega
    have hev' : Ψ =ᶠ[𝓝[≠] a] fun z => (z - a) ^ m * Φ z := by
      have h1 : ∀ᶠ z in 𝓝[≠] a, Φ z = (z - a) ^ (n a) * Ψ z :=
        mem_nhdsWithin_of_mem_nhds hev
      filter_upwards [h1, self_mem_nhdsWithin] with z hz hza
      have hd : z - a ≠ 0 := sub_ne_zero.2 hza
      rw [hz, ← mul_assoc, ← zpow_natCast, ← hm, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, one_mul]
    have hT : Tendsto (fun z => (z - a) ^ m * Φ z) (𝓝[≠] a) (𝓝 (0 * Φ a)) := by
      refine Tendsto.mul ?_ (hc.tendsto.mono_left nhdsWithin_le_nhds)
      have : Tendsto (fun z : ℂ => (z - a) ^ m) (𝓝 a) (𝓝 ((a - a) ^ m)) :=
        ((continuous_id.sub continuous_const).pow m).continuousAt.tendsto
      rw [sub_self, zero_pow hm0.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    rw [zero_mul] at hT
    have hΨT : Tendsto Ψ (𝓝[≠] a) (𝓝 (Ψ a)) := hΨ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact hΨ0 (tendsto_nhds_unique hΨT (hT.congr' hev'.symm))
  · exact heq
  · exfalso
    have := hev.self_of_nhds
    simp only [sub_self, zero_zpow _ hgt.ne', zero_mul] at this
    exact hΦa this

private theorem exists_ball_local_form {U : Set ℂ} {Φ : ℂ → ℂ} {n : ℂ → ℤ}
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    {τ : ℂ} (hτ : τ ∈ U) (hUn : U ∈ 𝓝 τ) :
    ∃ r : ℝ, ∃ Ψ : ℂ → ℂ, 0 < r ∧ ball τ r ⊆ U ∧ ContDiffOn ℝ 1 Ψ (ball τ r) ∧
      (∀ z ∈ ball τ r, ‖Ψ z * (Ψ τ)⁻¹ - 1‖ < 1) ∧ Ψ τ ≠ 0 ∧
      (∀ z ∈ ball τ r, Φ z = (z - τ) ^ (n τ) * Ψ z) := by
  obtain ⟨Ψ, hΨ, hΨ0, hev⟩ := hloc τ hτ
  have h1 : ∀ᶠ z in 𝓝 τ, ContDiffAt ℝ 1 Ψ z := hΨ.eventually (by simp)
  have h2 : ∀ᶠ z in 𝓝 τ, ‖Ψ z * (Ψ τ)⁻¹ - 1‖ < 1 := by
    have hc : ContinuousAt (fun z => Ψ z * (Ψ τ)⁻¹ - 1) τ :=
      (hΨ.continuousAt.mul continuousAt_const).sub continuousAt_const
    have h0 : ‖Ψ τ * (Ψ τ)⁻¹ - 1‖ < 1 := by rw [mul_inv_cancel₀ hΨ0]; simp
    exact hc.norm.eventually (gt_mem_nhds h0)
  have h0 : ∀ᶠ z in 𝓝 τ, z ∈ U := hUn
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (((h0.and hev).and h1).and h2)
  refine ⟨r, Ψ, hr, fun z hz => (hball hz).1.1.1, fun z hz => (hball hz).1.2.contDiffWithinAt,
    fun z hz => (hball hz).2, hΨ0, fun z hz => (hball hz).1.1.2⟩

private theorem tsupport_ofReal_comp (ρ : ℂ → ℝ) : tsupport (fun z => ((ρ z : ℝ) : ℂ)) = tsupport ρ := by
  simp only [tsupport]
  congr 1
  ext z
  simp

/-- **Pompeiu's identity in arbitrary-order form.**  If `Φ` is locally `(z - τ) ^ (n τ) * Ψ` with
`Ψ` of class `C¹` and non-zero at `τ`, `E` has derivative `E'` on `U`, and `h` is of class `C²` with
compact support in `U`, then both integrands below are integrable and the identity
`I / π * ∫ E / Φ * wedge(Φ, h) + 2 * ∑ᶠ a, n a * E a * h a = 2 / π * ∫ E' * h * ∂̄Φ / Φ`
holds. -/
theorem integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv (U : Set ℂ)
    (hU : IsOpen U) (Φ : ℂ → ℂ) (n : ℂ → ℤ)
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ,
      ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧ Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    (E E' : ℂ → ℂ) (hE : ∀ z ∈ U, HasDerivAt E (E' z) z) (h : ℂ → ℂ) (hh : ContDiff ℝ 2 h)
    (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    Integrable (fun z : ℂ =>
        E z / Φ z * (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) ∧
      Integrable (fun z : ℂ =>
        E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
      I / π * (∫ z : ℂ, E z / Φ z *
          (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) +
        2 * ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a =
      2 / π * ∫ z : ℂ, E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by
  classical

  have hdisc : ∀ τ, τ ∈ U → ∃ r : ℝ, ∃ Ψ : ℂ → ℂ, 0 < r ∧ ball τ r ⊆ U ∧
      ContDiffOn ℝ 1 Ψ (ball τ r) ∧ (∀ z ∈ ball τ r, ‖Ψ z * (Ψ τ)⁻¹ - 1‖ < 1) ∧ Ψ τ ≠ 0 ∧
      (∀ z ∈ ball τ r, Φ z = (z - τ) ^ (n τ) * Ψ z) := fun τ hτ =>
    exists_ball_local_form hloc hτ (hU.mem_nhds hτ)
  choose! r Ψf hr hrU hΨf hΨ1 hΨ0 hΦf using hdisc

  have hiso : ∀ τ ∈ U, ∀ a ∈ ball τ (r τ), a ≠ τ → n a = 0 := by
    intro τ hτ a ha haτ
    have haU : a ∈ U := hrU τ hτ ha
    have hcont : ContinuousAt Φ a := by
      have hev : Φ =ᶠ[𝓝 a] fun z => (z - τ) ^ (n τ) * Ψf τ z := by
        filter_upwards [isOpen_ball.mem_nhds ha] with z hz using hΦf τ hτ z hz
      refine (ContinuousAt.congr ?_ hev.symm)
      refine ContinuousAt.mul ?_ ((hΨf τ hτ).continuousOn.continuousAt (isOpen_ball.mem_nhds ha))
      exact ((continuousAt_id.sub continuousAt_const).zpow₀ _ (Or.inl (sub_ne_zero.2 haτ)))
    have hΦa : Φ a ≠ 0 :=
      ne_zero_of_local_form (hΨ1 τ hτ) (hΦf τ hτ) ha haτ
    exact order_eq_zero_of_continuousAt hloc haU hcont hΦa

  set K := tsupport h with hK
  have hKc : IsCompact K := hsupp
  obtain ⟨t, htK, hcov⟩ := hKc.elim_nhds_subcover (fun x => ball x (r x / 2)) fun x hx =>
    ball_mem_nhds x (half_pos (hr x (hU' hx)))
  have htU : ∀ x ∈ t, x ∈ U := fun x hx => hU' (htK x hx)

  set ι := {x // x ∈ t}
  set Uc : ι → Set ℂ := fun i => ball (i : ℂ) (r i / 2) with hUc
  have hUo : ∀ i, IsOpen (Uc i) := fun i => isOpen_ball
  have hKU : K ⊆ ⋃ i, Uc i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hcov hx)
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨f, hf⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) (isClosed_tsupport h) Uc hUo hKU
  set ρ : ι → ℂ → ℂ := fun i z => ((f i z : ℝ) : ℂ) with hρ
  have hρs : ∀ i, ContDiff ℝ 2 (ρ i) := fun i => by
    have h1 : ContDiff ℝ 2 ((f i) : ℂ → ℝ) :=
      (contMDiff_iff_contDiff.1 (f i).contMDiff).of_le (by simp)
    exact ((Complex.ofRealCLM.contDiff).of_le le_top).comp h1
  have hρt : ∀ i, tsupport (ρ i) ⊆ ball (i : ℂ) (r i / 2) := fun i => by
    rw [hρ, tsupport_ofReal_comp]; exact hf i
  have hρ1 : ∀ z ∈ K, ∑ i : ι, ρ i z = 1 := by
    intro z hz
    have := f.sum_eq_one hz
    rw [finsum_eq_sum_of_fintype] at this
    simp only [hρ]
    exact_mod_cast this

  set k : ι → ℂ → ℂ := fun i z => h z * ρ i z with hkdef
  have hk2 : ∀ i, ContDiff ℝ 2 (k i) := fun i => hh.mul (hρs i)
  have hks : ∀ i, HasCompactSupport (k i) := fun i => hsupp.mul_right
  have hkt : ∀ i, tsupport (k i) ⊆ ball (i : ℂ) (r i) := fun i =>
    (closure_minimal (fun _ hz => subset_tsupport _ (right_ne_zero_of_mul hz))
      (isClosed_tsupport _)).trans
      ((hρt i).trans (ball_subset_ball (by linarith [hr i (htU i i.2)])))
  have hsum : h = ∑ i : ι, k i := by
    funext z
    rw [Finset.sum_apply]
    simp only [hkdef, ← Finset.mul_sum]
    by_cases hz : z ∈ K
    · rw [hρ1 z hz, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

  have hD : ∀ i : ι, _ := fun i => integral_wedge_identity_on_ball (hΨf i (htU i i.2))
    (hΨ1 i (htU i i.2)) (hΨ0 i (htU i i.2)) (hΦf i (htU i i.2))
    (fun z hz => hE z (hrU i (htU i i.2) hz)) (hk2 i) (hks i) (hkt i)

  have hfd : ∀ z w, fderiv ℝ h z w = ∑ i : ι, fderiv ℝ (k i) z w := by
    intro z w
    rw [hsum, fderiv_sum fun i _ => (hk2 i).differentiable (by norm_num) z]
    simp
  have hhz : ∀ z, h z = ∑ i : ι, k i z := fun z => by rw [hsum, Finset.sum_apply]

  have hI1 : (fun z : ℂ => E z / Φ z *
      (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) =
      fun z => ∑ i : ι, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ (k i) z I - fderiv ℝ Φ z I * fderiv ℝ (k i) z 1) := by
    funext z
    rw [hfd z I, hfd z 1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
  have hI2 : (fun z : ℂ => E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) =
      fun z => ∑ i : ι, E' z * k i z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by
    funext z
    rw [hhz z, Finset.mul_sum, Finset.sum_mul]

  have hpt : ∀ i : ι, ∑ᶠ a : ℂ, (n a : ℂ) * E a * k i a = (n i : ℂ) * E i * k i i := by
    intro i
    refine finsum_eq_single _ (i : ℂ) fun a hai => ?_
    by_cases hka : k i a = 0
    · rw [hka, mul_zero]
    · have ha : a ∈ ball (i : ℂ) (r i) := hkt i (subset_tsupport _ hka)
      rw [hiso i (htU i i.2) a ha hai]; simp
  have hfin : ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a = ∑ i : ι, (n i : ℂ) * E i * k i i := by
    have h1 : (fun a : ℂ => (n a : ℂ) * E a * h a) = fun a => ∑ i : ι, (n a : ℂ) * E a * k i a := by
      funext a; rw [hhz a, Finset.mul_sum]
    rw [h1, finsum_sum_comm]
    · exact Finset.sum_congr rfl fun i _ => hpt i
    · intro i _
      refine Set.Finite.subset (Set.finite_singleton (i : ℂ)) fun a ha => ?_
      by_contra hai
      apply ha
      show (n a : ℂ) * E a * k i a = 0
      by_cases hka : k i a = 0
      · rw [hka, mul_zero]
      · have ha' : a ∈ ball (i : ℂ) (r i) := hkt i (subset_tsupport _ hka)
        rw [hiso i (htU i i.2) a ha' hai]; simp

  refine ⟨?_, ?_, ?_⟩
  · rw [hI1]; exact integrable_finsetSum _ fun i _ => (hD i).1
  · rw [hI2]; exact integrable_finsetSum _ fun i _ => (hD i).2.1
  · rw [hI1, hI2, integral_finsetSum _ fun i _ => (hD i).1,
      integral_finsetSum _ fun i _ => (hD i).2.1, hfin, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (hD i).2.2

end Complex
