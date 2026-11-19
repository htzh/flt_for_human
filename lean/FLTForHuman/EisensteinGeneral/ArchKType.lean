/-
  The archimedean `K`-types of the Eisenstein piece.

  Two existence statements for the archimedean factor of an Eisenstein section, each producing a
  function `J` of the spectral variable `w` and of a one-parameter family (a complex `ζ` for the
  `GL₂(ℂ)`-type, a real `t` for the `GL₂(ℝ)`-type) with three properties:

  * `exists_complexKType`: `J w ζ` is holomorphic in `w` off `ζ = 0`, is the integral over `z : ℂ` of
    `z ^ a * conj z ^ b * (1 + ‖z‖ ^ 2) ^ (-w) * exp (-4πi Re (ζ z))` on the half-plane
    `Re w > (a + b) / 2 + 1`, and decays like `‖ζ‖ ^ (-N) * exp (-c ‖ζ‖)` uniformly for `‖w‖ ≤ R`;
  * `exists_realKType`: the same for the `GL₂(ℝ)`-type: the integral over `x : ℝ` of
    `((x - i) / √(1 + x²)) ^ k * (1 + x²) ^ (-w) * exp (-2πi t x)` on `Re w > 1/2`, with the bound
    `|t| ^ (-N) * exp (-c |t|)`.

  This is pure analysis over the archimedean completion: no adelic vocabulary appears. Its only
  premise is the archimedean integral bound `EisensteinGeneral.Arch.exists_norm_archIntegral_le`
  (`EisensteinGeneral/ArchIntegralBound.lean`), which is the summability input for the uniform
  estimates; the two files' shared engine is transcribed once.

  Transcribed from the two `S_` files below (pinned `aa2d8b3`, 1004 + 790 lines), the pins'
  search-stage namespace `EgenArch` dropped in favour of the row's own namespace.

  **The pin's own duplication, deduplicated.** The two `S_` files share twelve declarations, 185
  lines (complex pin `:26-210` = real pin `:28-212`, `diff`-clean once the real pin's bare
  `exists_norm_archIntegral_le` is spelled with the complex pin's `EisensteinGeneral.Arch.`
  qualification — the port is inside that namespace, so it writes the qualified form once). Those
  twelve are transcribed **once**, `private`, at the top of this module, and both developments
  consume them. The rest of each pin follows in place: the `GL₂(ℂ)` development (complex pin
  `:212-991`, 47 declarations) then the `GL₂(ℝ)` one (real pin `:214-757`, 34).

  **Names.** The pins' label prefixes are dropped (`e1_`/`e4_` on the shared block, `e7_` on the
  complex development, `e6_` on the real one) and the few names that would strip to a single letter
  (`e7G`, `e7E`, `e7T`, `e7c`, `e7Gd`, `e7Thol`, `e7Tder`, `e6_K`, `e6_A`, `e6_Phi`, `e6_sgn`,
  `e6_J`, `e6_chr`, `e6_G`) are given subject names (`kernelG`, `kernelE`, `kernelT`, `phaseC`,
  `kernelGd`, `kernelThol`, `kernelTder`, `kernelK`, `gammaFactor`, `termFamily`, `signWeight`,
  `realJ`, `charFn`, `realG`); the two same-named `laplace` theorems are separated as
  `laplace_complex` / `laplace_real`. The full 105-row table (port name, pin name, pin line) is in
  `lean/tmp/af85/AF85A-REPORT.md`. Every engine is `private` — the pins state all of them
  `private` — and only the two rows are public.

  **The rows.** `exists_complexKType` is the pin's `solution` (`:994`) applied to the pin's own
  engine pair `head_of_family`/`family`; `exists_realKType` transcribes the pin's 15-line
  `solution` proof (`:771-789`) at the row's statement.

  **Departures from the pins**, all recorded (nothing else: neither pin carries an
  `attribute [-…]` wall, a `scoped` instance or a `set_option` beyond `autoImplicit false`):
  * `if_pos` / `if_neg` → `ite_eq_left` / `ite_eq_right` at the two sites of `weight_eq`
    (real pin `:719`, `:724`; v4.34 deprecations, the port's standing substitution).
  * `open Set MeasureTheory` — the pins' `open Set MeasureTheory` (`:21`); the scaffold carried
    `open MeasureTheory` only and `Ioi`/`mem_Ioi` need the `Set` scope.
  * the imports are extended with the pins' mathlib list (`MellinTransform`, `Gamma.Beta`,
    `Gaussian.FourierTransform`, `Gaussian.GaussianIntegral`, `FourierTransformDeriv`,
    `JapaneseBracket`, `Integral.Prod`, `ExpDeriv`, `ParametricIntegral`,
    `Complex.RealDeriv`, `InnerProductSpace.Basic`, `LinearAlgebra.Complex.FiniteDimensional`,
    `Pow.Real`) — the scaffold's two did not close the pins' proof terms.
  * the real pin's `open EgenArch` / `open EisensteinGeneral.Arch` (`:26`, `:760`) are dropped:
    the port declares everything inside `EisensteinGeneral.Arch` already.

  Gates: `check_port --force` 2 ok / 0 mismatch / 0 missing / 0 own / 0 kw (95 port
  declarations: 2 public rows + 93 private engines); `lake env lean` silent at
  `-DmaxHeartbeats=200000`; `#print axioms` on all 95 → `[propext, Classical.choice, Quot.sound]`;
  `dedup.py --within` 0 clusters; `move_dead.py` 0 declarations / 0 lines;
  `scaffold_audit.py` complete (both pins' only public declaration is the folded `solution`).

  Heartbeat probe: silent at 78000, aborts at 39000 (`lake env lean -DautoImplicit=false
  -DmaxHeartbeats=N`); the floor is 77–78 k, since 77000 already aborts. The peak is
  `kernelThol_hasDerivAt` (pin `e7Thol_hasDerivAt`, complex pin `:448`). No in-file cap is carried —
  playbook §3.5, FR-0225.

  spec-pin: P2M/Sol/S_EisensteinGeneral_Arch_exists_complexKType.lean
  spec-pin: P2M/Sol/S_EisensteinGeneral_Arch_exists_realKType.lean
-/
import FLTForHuman.EisensteinGeneral.ArchIntegralBound
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open Set MeasureTheory

namespace EisensteinGeneral.Arch

/-! ### The shared archimedean engine

  The twelve declarations the two pin files duplicate (pin `:26-210` of the complex file, `:28-212`
  of the real one, `diff`-clean after the `EisensteinGeneral.Arch` qualification), written once here
  at the top: the Mellin/Laplace kernel estimates and the uniform bound
  `exists_norm_sum_archIntegral_le` that both `K`-type constructions consume, whose only premise is
  this module's import `EisensteinGeneral.Arch.exists_norm_archIntegral_le`. -/

private theorem kernel_norm (c : ℂ) (r u : ℝ) :
    ‖Complex.exp (-c * (u + r ^ 2 / u))‖ = Real.exp (-c.re * (u + r ^ 2 / u)) := by
  have h : (u + r ^ 2 / u : ℂ) = ((u + r ^ 2 / u : ℝ) : ℂ) := by
    simp only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow]
  rw [Complex.norm_exp, h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.neg_re]

private theorem kernel_continuousOn (c : ℂ) (r : ℝ) :
    ContinuousOn (fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) (Ioi 0) :=
  ContinuousOn.cexp (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.add
    (continuousOn_const.div Complex.continuous_ofReal.continuousOn fun _ hu =>
      Complex.ofReal_ne_zero.mpr (ne_of_gt hu))))

open Asymptotics _root_.Filter _root_.Asymptotics.Filter in

private theorem kernel_isBigO_atTop (c : ℂ) (hc : 0 < c.re) (r : ℝ) :
    (fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) =O[atTop] fun u : ℝ => Real.exp (-c.re * u) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [kernel_norm, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
  exact mul_le_mul_of_nonpos_left (le_add_of_nonneg_right (div_nonneg (sq_nonneg r) hu.le))
    (neg_nonpos.mpr hc.le)

open Asymptotics _root_.Filter _root_.Asymptotics.Filter Topology in

private theorem kernel_isBigO_nhdsGT (c : ℂ) (hc : 0 < c.re) (r : ℝ) (hr : r ≠ 0) (b : ℝ) :
    (fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) =O[𝓝[>] 0] fun u : ℝ => u ^ (-b) := by
  have hκ : 0 < c.re * r ^ 2 := mul_pos hc (lt_of_le_of_ne (sq_nonneg r) (Ne.symm (pow_ne_zero 2 hr)))
  have h1 : (fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) =O[𝓝[>] 0]
      fun u : ℝ => Real.exp (-(c.re * r ^ 2) * u⁻¹) := by
    refine IsBigO.of_bound 1 (eventually_nhdsWithin_of_forall fun u hu => ?_)
    rw [kernel_norm, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    calc -c.re * (u + r ^ 2 / u) ≤ -c.re * (r ^ 2 / u) :=
          mul_le_mul_of_nonpos_left (le_add_of_nonneg_left (le_of_lt hu)) (neg_nonpos.mpr hc.le)
      _ = -(c.re * r ^ 2) * u⁻¹ := by ring
  have h2 : (fun u : ℝ => Real.exp (-(c.re * r ^ 2) * u⁻¹)) =o[𝓝[>] 0] fun u : ℝ => u ^ (-b) := by
    refine ((isLittleO_exp_neg_mul_rpow_atTop hκ b).comp_tendsto tendsto_inv_nhdsGT_zero).congr'
      (Eventually.of_forall fun u => rfl) (eventually_nhdsWithin_of_forall fun u hu => ?_)
    show u⁻¹ ^ b = u ^ (-b)
    rw [Real.inv_rpow (le_of_lt hu), Real.rpow_neg (le_of_lt hu)]
  exact h1.trans h2.isBigO

private theorem mellin_differentiableAt (c : ℂ) (hc : 0 < c.re) (r : ℝ) (hr : r ≠ 0) (s : ℂ) :
    DifferentiableAt ℂ (mellin fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) s :=
  mellin_differentiableAt_of_isBigO_rpow_exp hc
    ((kernel_continuousOn c r).locallyIntegrableOn measurableSet_Ioi)
    (kernel_isBigO_atTop c hc r) (kernel_isBigO_nhdsGT c hc r hr (s.re - 1)) (sub_one_lt _)

private theorem differentiable_archIntegral (c : ℂ) (hc : 0 < c.re) (r : ℝ) (hr : r ≠ 0) :
    Differentiable ℂ (fun z : ℂ =>
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u))) := by
  have h : (fun z : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-c * (u + r ^ 2 / u)))
      = (mellin fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) ∘ fun z : ℂ => z + 1 := by
    funext z
    simp only [Function.comp_apply, mellin, add_sub_cancel_right, smul_eq_mul]
  have hg : Differentiable ℂ (mellin fun u : ℝ => Complex.exp (-c * (u + r ^ 2 / u))) :=
    fun s => mellin_differentiableAt c hc r hr s
  have hf : Differentiable ℂ fun z : ℂ => z + 1 := differentiable_id.add_const 1
  rw [h]
  exact hg.comp hf

private theorem max_pow_mul_exp_le {x k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) (m : ℕ) :
    max 1 (x ^ m) * Real.exp (-k * x)
      ≤ max 1 ((Nat.factorial m : ℝ) / (k / 2) ^ m) * Real.exp (-(k / 2) * x) := by
  have hk2 : 0 < k / 2 := half_pos hk
  have hkx : 0 ≤ k / 2 * x := mul_nonneg hk2.le hx
  have hexp : Real.exp (-k * x) ≤ Real.exp (-(k / 2) * x) := Real.exp_le_exp.mpr (by linarith)
  rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _)]
  refine max_le ?_ ?_
  · rw [one_mul]
    exact hexp.trans (le_mul_of_one_le_left (Real.exp_nonneg _) (le_max_left _ _))
  · have h1 : x ^ m ≤ (Nat.factorial m : ℝ) / (k / 2) ^ m * Real.exp (k / 2 * x) := by
      have h := Real.pow_div_factorial_le_exp _ hkx m
      rw [mul_pow, div_le_iff₀ (by positivity)] at h
      rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hk2 m)]
      calc x ^ m * (k / 2) ^ m = (k / 2) ^ m * x ^ m := mul_comm _ _
        _ ≤ Real.exp (k / 2 * x) * (Nat.factorial m : ℝ) := h
        _ = (Nat.factorial m : ℝ) * Real.exp (k / 2 * x) := mul_comm _ _
    calc x ^ m * Real.exp (-k * x)
        ≤ (Nat.factorial m : ℝ) / (k / 2) ^ m * Real.exp (k / 2 * x) * Real.exp (-k * x) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
      _ = (Nat.factorial m : ℝ) / (k / 2) ^ m * Real.exp (-(k / 2) * x) := by
          rw [mul_assoc, ← Real.exp_add, show k / 2 * x + -k * x = -(k / 2) * x by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_nonneg _)

private theorem pow_mul_exp_le {x k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) (m : ℕ) :
    x ^ m * Real.exp (-k * x) ≤ max 1 ((Nat.factorial m : ℝ) / (k / 2) ^ m) * Real.exp (-(k / 2) * x) :=
  (mul_le_mul_of_nonneg_right (le_max_right 1 (x ^ m)) (Real.exp_nonneg _)).trans (max_pow_mul_exp_le hx hk m)

private theorem max_rpow_le {x : ℝ} (hx : 0 < x) {N N' : ℕ} (h : N ≤ N') :
    max 1 (x ^ (-(N : ℝ))) ≤ max 1 (x ^ (-(N' : ℝ))) := by
  rw [Real.rpow_neg hx.le, Real.rpow_neg hx.le, Real.rpow_natCast, Real.rpow_natCast]
  refine max_le (le_max_left _ _) ?_
  rcases le_or_gt x 1 with h1 | h1
  · exact le_max_of_le_right (inv_anti₀ (pow_pos hx N') (pow_le_pow_of_le_one hx.le h1 h))
  · exact le_max_of_le_left (inv_le_one_of_one_le₀ (one_le_pow₀ h1.le))

private theorem exists_pos_le {κ : Type} (T : Finset κ) (f : κ → ℝ) (hf : ∀ i ∈ T, 0 < f i) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ i ∈ T, c₂ ≤ f i := by
  rcases T.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, fun i hi => by simp [h] at hi⟩
  · obtain ⟨i₀, hi₀T, hi₀⟩ := T.exists_min_image f h
    exact ⟨f i₀, hf i₀ hi₀T, fun i hi => hi₀ i hi⟩

private theorem differentiable_sum_archIntegral {κ : Type} (T : Finset κ) (a : κ → ℂ → ℂ)
    (ha : ∀ i ∈ T, Differentiable ℂ (a i)) (β b : κ → ℂ) (l : κ → ℕ)
    (c : ℂ) (hc : 0 < c.re) (r : ℝ) (hr : r ≠ 0) :
    Differentiable ℂ (fun z : ℂ => ∑ i ∈ T, a i z * β i * (r : ℂ) ^ l i *
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z + b i) * Complex.exp (-c * (u + r ^ 2 / u))) := by
  have hI := differentiable_archIntegral c hc r hr
  have hJ : ∀ i : κ, Differentiable ℂ (fun z : ℂ =>
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z + b i) * Complex.exp (-c * (u + r ^ 2 / u))) :=
    fun i => hI.fun_comp (f := fun z : ℂ => z + b i) (by fun_prop)
  apply Differentiable.fun_sum
  intro i hi
  have h1 := ha i hi
  have h2 := hJ i
  fun_prop

private theorem exists_norm_sum_archIntegral_le {κ : Type} (T : Finset κ) (a : κ → ℂ → ℂ)
    (ha : ∀ i ∈ T, Differentiable ℂ (a i)) (b : κ → ℂ) (l : κ → ℕ) (c : ℂ) (hc : 0 < c.re) (R : ℝ) :
    ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (β : κ → ℂ), (∀ i ∈ T, ‖β i‖ ≤ 1) →
      ∀ (z : ℂ) (r : ℝ), ‖z‖ ≤ R → r ≠ 0 →
      ‖∑ i ∈ T, a i z * β i * (r : ℂ) ^ l i *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z + b i) * Complex.exp (-c * (u + r ^ 2 / u))‖
        ≤ C * max 1 (|r| ^ (-(N : ℝ))) * Real.exp (-c' * |r|) := by
  choose Ci ci Ni hCi hci hE2 using fun i : κ => EisensteinGeneral.Arch.exists_norm_archIntegral_le c hc (R + ‖b i‖)
  have hbound : ∀ i : κ, ∃ A : ℝ, 0 ≤ A ∧ (i ∈ T → ∀ z : ℂ, ‖z‖ ≤ R → ‖a i z‖ ≤ A) := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨B, hB⟩ :=
        (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn (ha i hi).continuous.continuousOn
      refine ⟨max B 0, le_max_right _ _, fun _ z hz => (hB z ?_).trans (le_max_left _ _)⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz
    · exact ⟨0, le_rfl, fun h => absurd h hi⟩
  choose A hA0 hA using hbound
  obtain ⟨c₂, hc₂, hc₂le⟩ := exists_pos_le T (fun i => ci i / 2) (fun i _ => half_pos (hci i))
  obtain ⟨N₂, hN₂⟩ : ∃ N₂ : ℕ, ∀ i ∈ T, Ni i ≤ N₂ := ⟨T.sup Ni, fun i hi => Finset.le_sup (f := Ni) hi⟩
  refine ⟨(∑ i ∈ T, A i * Ci i * max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i)) + 1, c₂, N₂, ?_, hc₂, ?_⟩
  · refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => ?_) one_pos
    have := hA0 i
    have := hCi i
    positivity
  intro β hβ z r hz hr
  have hr0 : 0 < |r| := abs_pos.mpr hr
  have hX : 0 ≤ max 1 (|r| ^ (-(N₂ : ℝ))) * Real.exp (-c₂ * |r|) := by positivity
  have hterm : ∀ i ∈ T,
      ‖a i z * β i * (r : ℂ) ^ l i *
          ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (z + b i) * Complex.exp (-c * (u + r ^ 2 / u))‖
        ≤ A i * Ci i * max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i) *
            (max 1 (|r| ^ (-(N₂ : ℝ))) * Real.exp (-c₂ * |r|)) := by
    intro i hi
    have hre : |(z + b i).re| ≤ R + ‖b i‖ :=
      (Complex.abs_re_le_norm _).trans ((norm_add_le _ _).trans (add_le_add hz le_rfl))
    have hI := hE2 i (z + b i) r hre hr
    have ha' := hA i hi z hz
    have hβ' := hβ i hi
    have hA0i := hA0 i
    have hCi' := hCi i
    have hmax := max_rpow_le hr0 (hN₂ i hi)
    have hpow := pow_mul_exp_le (abs_nonneg r) (hci i) (l i)
    have hc₂i : c₂ ≤ ci i / 2 := hc₂le i hi
    have hexp : Real.exp (-(ci i / 2) * |r|) ≤ Real.exp (-c₂ * |r|) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hc₂i (abs_nonneg r)])
    rw [norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ A i * 1 * |r| ^ l i * (Ci i * max 1 (|r| ^ (-(Ni i : ℝ))) * Real.exp (-ci i * |r|)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul ha' hβ' (norm_nonneg _) hA0i) (by positivity)) hI
            (norm_nonneg _) (by positivity)
      _ = A i * Ci i * (max 1 (|r| ^ (-(Ni i : ℝ))) * (|r| ^ l i * Real.exp (-ci i * |r|))) := by ring
      _ ≤ A i * Ci i * (max 1 (|r| ^ (-(N₂ : ℝ))) *
            (max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i) * Real.exp (-(ci i / 2) * |r|))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hmax hpow (by positivity) (by positivity)) (by positivity)
      _ ≤ A i * Ci i * (max 1 (|r| ^ (-(N₂ : ℝ))) *
            (max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i) * Real.exp (-c₂ * |r|))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity)) (by positivity))
            (by positivity)
      _ = _ := by ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul]
  calc _ ≤ ((∑ i ∈ T, A i * Ci i * max 1 ((Nat.factorial (l i) : ℝ) / (ci i / 2) ^ l i)) + 1) *
        (max 1 (|r| ^ (-(N₂ : ℝ))) * Real.exp (-c₂ * |r|)) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hX
    _ = _ := by ring

/-! ### The `GL₂(ℂ)`-type -/

private noncomputable def kernelG (a b : ℕ) (v : ℝ) (ζ : ℂ) : ℂ :=
  ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
    * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))

private noncomputable def kernelE (v : ℝ) (ζ : ℂ) : ℂ :=
  Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * ((ζ.re : ℂ) ^ 2 + (ζ.im : ℂ) ^ 2) / (v : ℂ))

private noncomputable def kernelT (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ : ℂ) : ℂ :=
  γ * ζ ^ p * (starRingEnd ℂ) ζ ^ q * ((v : ℂ) ^ (m + 1))⁻¹ * kernelE v ζ

private theorem one_add_pow_le (v : ℝ) (hv : 0 < v) (N : ℕ) (hN : 0 < N) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ N ≤ K * Real.exp (v * t) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  refine ⟨(max 1 ((N : ℝ) / v)) ^ N, by positivity, fun t ht => ?_⟩
  have h1 : 1 + t ≤ max 1 ((N : ℝ) / v) * (1 + v / N * t) := by
    rcases le_total 1 ((N : ℝ) / v) with h | h
    · rw [max_eq_right h]
      have h2 : (N : ℝ) / v * (1 + v / N * t) = N / v + t := by
        field_simp
      rw [h2]
      linarith
    · rw [max_eq_left h, one_mul]
      have h3 : (N : ℝ) ≤ v := by rwa [div_le_one hv] at h
      have h4 : 1 ≤ v / N := by rw [le_div_iff₀ hNpos]; linarith
      nlinarith
  have h2 : 1 + v / N * t ≤ Real.exp (v / N * t) := by
    have := Real.add_one_le_exp (v / N * t)
    linarith
  have h3 : (1 + v / N * t) ^ N ≤ Real.exp (v * t) := by
    calc (1 + v / N * t) ^ N ≤ (Real.exp (v / N * t)) ^ N := by
          gcongr
      _ = Real.exp (v * t) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  calc (1 + t) ^ N ≤ (max 1 ((N : ℝ) / v) * (1 + v / N * t)) ^ N := by gcongr
    _ = (max 1 ((N : ℝ) / v)) ^ N * (1 + v / N * t) ^ N := mul_pow _ _ _
    _ ≤ (max 1 ((N : ℝ) / v)) ^ N * Real.exp (v * t) := by gcongr

private theorem gauss_moment_integrable (n : ℕ) (v : ℝ) (hv : 0 < v) :
    Integrable (fun z : ℂ => ‖z‖ ^ n * Real.exp (-(v * ‖z‖ ^ 2))) := by
  obtain ⟨K, hK, hKle⟩ := one_add_pow_le v hv (n + 2) (by omega)
  have hmaj : Integrable (fun z : ℂ => K * ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(4 : ℝ) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)).const_mul K
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Continuous fun z : ℂ => ‖z‖ ^ n * Real.exp (-(v * ‖z‖ ^ 2))).aestronglyMeasurable
  · have ht0 : (0 : ℝ) ≤ ‖z‖ ^ 2 := by positivity
    have h1t : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
    have h1t' : (1 : ℝ) + ‖z‖ ^ 2 ≠ 0 := h1t.ne'
    rw [Real.norm_of_nonneg (by positivity)]
    have hz : ‖z‖ ≤ 1 + ‖z‖ ^ 2 := by nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1)]
    have hzn : ‖z‖ ^ n ≤ (1 + ‖z‖ ^ 2) ^ n := by gcongr
    have hexp : Real.exp (-(v * ‖z‖ ^ 2)) ≤ K / (1 + ‖z‖ ^ 2) ^ (n + 2) := by
      rw [le_div_iff₀ (by positivity), Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      have := hKle (‖z‖ ^ 2) ht0
      linarith [this]
    have hr : ((1 : ℝ) + ‖z‖ ^ 2) ^ (-(4 : ℝ) / 2) = ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
      rw [show (-(4 : ℝ) / 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1t.le, Real.rpow_natCast]
    rw [hr]
    calc ‖z‖ ^ n * Real.exp (-(v * ‖z‖ ^ 2)) ≤ (1 + ‖z‖ ^ 2) ^ n * (K / (1 + ‖z‖ ^ 2) ^ (n + 2)) := by
          gcongr
      _ = K * ((1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
          field_simp
          ring

private theorem norm_Gint (a b : ℕ) (v : ℝ) (ζ z : ℂ) :
    ‖z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))‖
      = ‖z‖ ^ (a + b) * Real.exp (-(v * ‖z‖ ^ 2)) := by
  have hchar : ‖Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have h1 : (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2) = ((-(v * ‖z‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
  have hg : ‖Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)‖ = Real.exp (-(v * ‖z‖ ^ 2)) := by
    rw [Complex.norm_exp, h1, Complex.ofReal_re]
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, hg, hchar, mul_one, pow_add]

private theorem Gint_continuous (a b : ℕ) (v : ℝ) (ζ : ℂ) :
    Continuous (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) := by
  fun_prop

private theorem Gint_integrable (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ : ℂ) :
    Integrable (fun z : ℂ => z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) := by
  refine (gauss_moment_integrable (a + b) v hv).mono'
    (Gint_continuous a b v ζ).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_Gint]

private theorem ofReal_norm_sq (ζ : ℂ) : ((‖ζ‖ : ℝ) : ℂ) ^ 2 = (ζ.re : ℂ) ^ 2 + (ζ.im : ℂ) ^ 2 := by
  rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_apply]
  push_cast
  ring

private theorem kernelG_zero_zero (v : ℝ) (hv : 0 < v) (ζ : ℂ) :
    kernelG 0 0 v ζ = kernelT (Real.pi : ℂ) 0 0 0 v ζ := by
  have hb : (0 : ℝ) < (v : ℂ).re := by simpa using hv
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb
    (-(4 * (Real.pi : ℂ) * Complex.I)) ((starRingEnd ℂ) ζ)
  have hL : kernelG 0 0 v ζ = ∫ z : ℂ, Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2
      + -(4 * (Real.pi : ℂ) * Complex.I) * ((inner ℝ ((starRingEnd ℂ) ζ) z : ℝ) : ℂ)) := by
    unfold kernelG
    congr 1
    funext z
    rw [pow_zero, pow_zero, one_mul, one_mul, ← Complex.exp_add]
    congr 1
    rw [Complex.inner, starRingEnd_self_apply, mul_comm z ζ]
    push_cast
    ring
  have hfin : ((Module.finrank ℝ ℂ : ℂ) / 2) = 1 := by
    rw [Complex.finrank_real_complex]
    norm_num
  have hI : (-(4 * (Real.pi : ℂ) * Complex.I)) ^ 2 = -(16 * (Real.pi : ℂ) ^ 2) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  have hv' : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [hL, h, hfin, Complex.cpow_one, hI, Complex.norm_conj, ofReal_norm_sq]
  unfold kernelT kernelE
  simp only [pow_zero, mul_one, zero_add, pow_one]
  rw [div_eq_mul_inv]
  congr 1
  field_simp
  ring_nf

private noncomputable def phaseC (d z : ℂ) : ℂ := -(((4 * Real.pi * (d * z).re : ℝ) : ℂ) * Complex.I)

private noncomputable def kernelGd (a b : ℕ) (v : ℝ) (ζ d : ℂ) : ℂ :=
  ∫ z : ℂ, phaseC d z * (z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
    * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))

private theorem phaseC_continuous (d : ℂ) : Continuous (fun z : ℂ => phaseC d z) := by
  simp only [phaseC]
  fun_prop

private theorem norm_phaseC_le (d z : ℂ) : ‖phaseC d z‖ ≤ 4 * Real.pi * ‖d‖ * ‖z‖ := by
  have h1 : |(d * z).re| ≤ ‖d‖ * ‖z‖ := by
    rw [← norm_mul]
    exact Complex.abs_re_le_norm _
  have h2 : ‖phaseC d z‖ = 4 * Real.pi * |(d * z).re| := by
    unfold phaseC
    rw [norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
  rw [h2]
  calc 4 * Real.pi * |(d * z).re| ≤ 4 * Real.pi * (‖d‖ * ‖z‖) := by gcongr
    _ = 4 * Real.pi * ‖d‖ * ‖z‖ := by ring

private theorem norm_Gd_le (a b : ℕ) (v : ℝ) (ζ d z : ℂ) :
    ‖phaseC d z * (z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))‖
      ≤ 4 * Real.pi * ‖d‖ * (‖z‖ ^ (a + b + 1) * Real.exp (-(v * ‖z‖ ^ 2))) := by
  rw [norm_mul, norm_Gint]
  calc ‖phaseC d z‖ * (‖z‖ ^ (a + b) * Real.exp (-(v * ‖z‖ ^ 2)))
      ≤ 4 * Real.pi * ‖d‖ * ‖z‖ * (‖z‖ ^ (a + b) * Real.exp (-(v * ‖z‖ ^ 2))) :=
        mul_le_mul_of_nonneg_right (norm_phaseC_le d z) (by positivity)
    _ = 4 * Real.pi * ‖d‖ * (‖z‖ ^ (a + b + 1) * Real.exp (-(v * ‖z‖ ^ 2))) := by ring

private theorem Gd_integrable (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ d : ℂ) :
    Integrable (fun z : ℂ => phaseC d z * (z ^ a * (starRingEnd ℂ) z ^ b
      * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))) :=
  ((gauss_moment_integrable (a + b + 1) v hv).const_mul (4 * Real.pi * ‖d‖)).mono'
    ((phaseC_continuous d).mul (Gint_continuous a b v ζ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => norm_Gd_le a b v ζ d z)

private theorem char_line (ζ₀ d z : ℂ) (x : ℝ) :
    (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I))
      = (-(((4 * Real.pi * (ζ₀ * z).re : ℝ) : ℂ) * Complex.I)) + (x : ℂ) * phaseC d z := by
  unfold phaseC
  simp only [add_mul, Complex.add_re, mul_assoc, Complex.re_ofReal_mul]
  push_cast
  ring

private theorem line_hasDerivAt (ζ₀ d z A : ℂ) (x : ℝ) :
    HasDerivAt
      (fun x : ℝ => A * Complex.exp (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I)))
      (phaseC d z * (A * Complex.exp (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I))))
      x := by
  simp only [char_line]
  have hlin : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  exact ((((hlin.mul_const (phaseC d z)).const_add
    (-(((4 * Real.pi * (ζ₀ * z).re : ℝ) : ℂ) * Complex.I))).cexp).const_mul A).congr_deriv (by ring)

private theorem kernelG_hasDerivAt_line (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ₀ d : ℂ) :
    HasDerivAt (fun x : ℝ => kernelG a b v (ζ₀ + x * d)) (kernelGd a b v ζ₀ d) 0 := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
    (F := fun (x : ℝ) (z : ℂ) => z ^ a * (starRingEnd ℂ) z ^ b
      * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I)))
    (F' := fun (x : ℝ) (z : ℂ) => phaseC d z * (z ^ a * (starRingEnd ℂ) z ^ b
      * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
      * Complex.exp (-(((4 * Real.pi * ((ζ₀ + x * d) * z).re : ℝ) : ℂ) * Complex.I))))
    (bound := fun z : ℂ => 4 * Real.pi * ‖d‖ * (‖z‖ ^ (a + b + 1) * Real.exp (-(v * ‖z‖ ^ 2))))
    Filter.univ_mem
    (Filter.Eventually.of_forall fun x => (Gint_continuous a b v (ζ₀ + x * d)).aestronglyMeasurable)
    (Gint_integrable a b v hv (ζ₀ + (0 : ℝ) * d))
    (Gd_integrable a b v hv (ζ₀ + (0 : ℝ) * d) d).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z x _ => norm_Gd_le a b v (ζ₀ + x * d) d z)
    ((gauss_moment_integrable (a + b + 1) v hv).const_mul (4 * Real.pi * ‖d‖))
    (Filter.Eventually.of_forall fun z x _ => line_hasDerivAt ζ₀ d z _ x)
  unfold kernelG kernelGd
  exact key.2.congr_deriv (by simp only [Complex.ofReal_zero, zero_mul, add_zero])

private theorem conj_eq (z : ℂ) : (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

private theorem kernelGd_sub (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ : ℂ) :
    kernelGd a b v ζ 1 - Complex.I * kernelGd a b v ζ Complex.I
      = -(4 * (Real.pi : ℂ) * Complex.I) * kernelG (a + 1) b v ζ := by
  unfold kernelGd kernelG
  rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (Gd_integrable a b v hv ζ 1)
    ((Gd_integrable a b v hv ζ Complex.I).const_mul Complex.I)]
  congr 1
  funext z
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  have key : ∀ w : ℂ, phaseC 1 z * w - Complex.I * (phaseC Complex.I z * w)
      = -(4 * (Real.pi : ℂ) * Complex.I) * (z * w) := by
    intro w
    unfold phaseC
    simp only [one_mul, Complex.I_mul_re]
    push_cast
    linear_combination (4 * (Real.pi : ℂ) * Complex.I * w) * hz
  rw [key]
  ring

private theorem kernelGd_add (a b : ℕ) (v : ℝ) (hv : 0 < v) (ζ : ℂ) :
    kernelGd a b v ζ 1 + Complex.I * kernelGd a b v ζ Complex.I
      = -(4 * (Real.pi : ℂ) * Complex.I) * kernelG a (b + 1) v ζ := by
  unfold kernelGd kernelG
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (Gd_integrable a b v hv ζ 1)
    ((Gd_integrable a b v hv ζ Complex.I).const_mul Complex.I)]
  congr 1
  funext z
  have hzc := conj_eq z
  have key : ∀ w : ℂ, phaseC 1 z * w + Complex.I * (phaseC Complex.I z * w)
      = -(4 * (Real.pi : ℂ) * Complex.I) * ((starRingEnd ℂ) z * w) := by
    intro w
    unfold phaseC
    simp only [one_mul, Complex.I_mul_re]
    push_cast
    linear_combination (4 * (Real.pi : ℂ) * Complex.I * w) * hzc
  rw [key]
  ring

private noncomputable def kernelThol (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d u : ℂ) : ℂ :=
  γ * (ζ₀ + u * d) ^ p * ((starRingEnd ℂ) ζ₀ + u * (starRingEnd ℂ) d) ^ q * ((v : ℂ) ^ (m + 1))⁻¹
    * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (((ζ₀.re : ℂ) + u * (d.re : ℂ)) ^ 2
        + ((ζ₀.im : ℂ) + u * (d.im : ℂ)) ^ 2) / (v : ℂ))

private theorem kernelT_line_eq (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d : ℂ) (x : ℝ) :
    kernelT γ p q m v (ζ₀ + x * d) = kernelThol γ p q m v ζ₀ d x := by
  simp only [kernelT, kernelE, kernelThol, map_add, map_mul, Complex.conj_ofReal, Complex.add_re, Complex.add_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.ofReal_add, Complex.ofReal_mul]

private noncomputable def kernelTder (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d : ℂ) : ℂ :=
  kernelT (γ * p * d) (p - 1) q m v ζ₀ + kernelT (γ * q * (starRingEnd ℂ) d) p (q - 1) m v ζ₀
    + kernelT (γ * (-(8 * (Real.pi : ℂ) ^ 2)) * ((ζ₀.re : ℂ) * (d.re : ℂ) + (ζ₀.im : ℂ) * (d.im : ℂ)))
        p q (m + 1) v ζ₀

private theorem kernelThol_hasDerivAt (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d : ℂ) :
    HasDerivAt (fun u : ℂ => kernelThol γ p q m v ζ₀ d u) (kernelTder γ p q m v ζ₀ d) ((0 : ℝ) : ℂ) := by
  simp only [kernelThol]
  have h1 : HasDerivAt (fun u : ℂ => ζ₀ + u * d) (1 * d) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' _).mul_const d).const_add ζ₀
  have h2 : HasDerivAt (fun u : ℂ => (starRingEnd ℂ) ζ₀ + u * (starRingEnd ℂ) d)
      (1 * (starRingEnd ℂ) d) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' _).mul_const _).const_add _
  have h3 : HasDerivAt (fun u : ℂ => (ζ₀.re : ℂ) + u * (d.re : ℂ)) (1 * (d.re : ℂ)) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' _).mul_const _).const_add _
  have h4 : HasDerivAt (fun u : ℂ => (ζ₀.im : ℂ) + u * (d.im : ℂ)) (1 * (d.im : ℂ)) ((0 : ℝ) : ℂ) :=
    ((hasDerivAt_id' _).mul_const _).const_add _
  have hQ := (((h3.fun_pow 2).fun_add (h4.fun_pow 2)).const_mul
    (-(4 * (Real.pi : ℂ) ^ 2))).div_const (v : ℂ)
  have h := ((((h1.fun_pow p).const_mul γ).fun_mul (h2.fun_pow q)).mul_const
    ((v : ℂ) ^ (m + 1))⁻¹).fun_mul hQ.cexp
  refine h.congr_deriv ?_
  simp only [kernelTder, kernelT, kernelE, Complex.ofReal_zero, zero_mul, add_zero, Nat.cast_ofNat, Nat.reduceSub,
    pow_one]
  ring

private theorem kernelT_line_hasDerivAt (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ d : ℂ) :
    HasDerivAt (fun x : ℝ => kernelT γ p q m v (ζ₀ + x * d)) (kernelTder γ p q m v ζ₀ d) 0 :=
  (kernelThol_hasDerivAt γ p q m v ζ₀ d).comp_ofReal.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun x => kernelT_line_eq γ p q m v ζ₀ d x)

private theorem kernelT_mul_left (c γ : ℂ) {p q m : ℕ} {v : ℝ} {ζ : ℂ} :
    kernelT (c * γ) p q m v ζ = c * kernelT γ p q m v ζ := by
  unfold kernelT
  ring

private theorem kernelTder_sub (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ : ℂ) :
    kernelTder γ p q m v ζ₀ 1 - Complex.I * kernelTder γ p q m v ζ₀ Complex.I
      = kernelT (γ * (2 * p)) (p - 1) q m v ζ₀
        + kernelT (γ * (-(8 * (Real.pi : ℂ) ^ 2))) p (q + 1) (m + 1) v ζ₀ := by
  have hC := conj_eq ζ₀
  simp only [kernelTder, kernelT, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, map_one,
    Complex.conj_I, Complex.ofReal_one, Complex.ofReal_zero]
  linear_combination
    (-(γ * p) * ζ₀ ^ (p - 1) * (starRingEnd ℂ) ζ₀ ^ q * ((v : ℂ) ^ (m + 1))⁻¹ * kernelE v ζ₀
        + γ * q * ζ₀ ^ p * (starRingEnd ℂ) ζ₀ ^ (q - 1) * ((v : ℂ) ^ (m + 1))⁻¹ * kernelE v ζ₀)
      * Complex.I_sq
    + (8 * (Real.pi : ℂ) ^ 2 * γ * ζ₀ ^ p * (starRingEnd ℂ) ζ₀ ^ q * ((v : ℂ) ^ (m + 1 + 1))⁻¹
        * kernelE v ζ₀) * hC

private theorem kernelTder_add (γ : ℂ) (p q m : ℕ) (v : ℝ) (ζ₀ : ℂ) :
    kernelTder γ p q m v ζ₀ 1 + Complex.I * kernelTder γ p q m v ζ₀ Complex.I
      = kernelT (γ * (2 * q)) p (q - 1) m v ζ₀
        + kernelT (γ * (-(8 * (Real.pi : ℂ) ^ 2))) (p + 1) q (m + 1) v ζ₀ := by
  have hz : ζ₀ = (ζ₀.re : ℂ) + (ζ₀.im : ℂ) * Complex.I := (Complex.re_add_im ζ₀).symm
  simp only [kernelTder, kernelT, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, map_one,
    Complex.conj_I, Complex.ofReal_one, Complex.ofReal_zero]
  linear_combination
    (γ * p * ζ₀ ^ (p - 1) * (starRingEnd ℂ) ζ₀ ^ q * ((v : ℂ) ^ (m + 1))⁻¹ * kernelE v ζ₀
        - γ * q * ζ₀ ^ p * (starRingEnd ℂ) ζ₀ ^ (q - 1) * ((v : ℂ) ^ (m + 1))⁻¹ * kernelE v ζ₀)
      * Complex.I_sq
    + (8 * (Real.pi : ℂ) ^ 2 * γ * ζ₀ ^ p * (starRingEnd ℂ) ζ₀ ^ q * ((v : ℂ) ^ (m + 1 + 1))⁻¹
        * kernelE v ζ₀) * hz

private theorem family_left (a b : ℕ)
    (h : ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      kernelG a b v ζ = ∑ i, kernelT (γ i) (p i) (q i) (m i) v ζ) :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      kernelG (a + 1) b v ζ = ∑ i, kernelT (γ i) (p i) (q i) (m i) v ζ := by
  obtain ⟨n, γ, p, q, m, hfam⟩ := h
  have hκ : (-(4 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  refine ⟨n + n,
    Fin.append (fun i => (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (2 * (p i : ℂ))))
      (fun i => (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (-(8 * (Real.pi : ℂ) ^ 2)))),
    Fin.append (fun i => p i - 1) (fun i => p i),
    Fin.append (fun i => q i) (fun i => q i + 1),
    Fin.append (fun i => m i) (fun i => m i + 1), fun v hv ζ₀ => ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  have hD : ∀ d : ℂ, kernelGd a b v ζ₀ d = ∑ i, kernelTder (γ i) (p i) (q i) (m i) v ζ₀ d := by
    intro d
    have hG := kernelG_hasDerivAt_line a b v hv ζ₀ d
    have hfun : (fun x : ℝ => kernelG a b v (ζ₀ + x * d))
        = fun x : ℝ => ∑ i, kernelT (γ i) (p i) (q i) (m i) v (ζ₀ + x * d) :=
      funext fun x => hfam v hv _
    rw [hfun] at hG
    exact hG.unique
      (HasDerivAt.fun_sum fun i _ => kernelT_line_hasDerivAt (γ i) (p i) (q i) (m i) v ζ₀ d)
  have hmain : -(4 * (Real.pi : ℂ) * Complex.I) * kernelG (a + 1) b v ζ₀
      = ∑ i, (kernelT (γ i * (2 * (p i : ℂ))) (p i - 1) (q i) (m i) v ζ₀
          + kernelT (γ i * (-(8 * (Real.pi : ℂ) ^ 2))) (p i) (q i + 1) (m i + 1) v ζ₀) := by
    rw [← kernelGd_sub a b v hv ζ₀, hD 1, hD Complex.I, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => kernelTder_sub (γ i) (p i) (q i) (m i) v ζ₀
  calc kernelG (a + 1) b v ζ₀
      = (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹
          * (-(4 * (Real.pi : ℂ) * Complex.I) * kernelG (a + 1) b v ζ₀) := by
        rw [← mul_assoc, inv_mul_cancel₀ hκ, one_mul]
    _ = ∑ i, (kernelT ((-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (2 * (p i : ℂ))))
            (p i - 1) (q i) (m i) v ζ₀
          + kernelT ((-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (-(8 * (Real.pi : ℂ) ^ 2))))
            (p i) (q i + 1) (m i + 1) v ζ₀) := by
        rw [hmain, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_add, ← kernelT_mul_left (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ (γ i * (2 * (p i : ℂ))),
          ← kernelT_mul_left (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ (γ i * (-(8 * (Real.pi : ℂ) ^ 2)))]

private theorem family_right (a b : ℕ)
    (h : ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      kernelG a b v ζ = ∑ i, kernelT (γ i) (p i) (q i) (m i) v ζ) :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      kernelG a (b + 1) v ζ = ∑ i, kernelT (γ i) (p i) (q i) (m i) v ζ := by
  obtain ⟨n, γ, p, q, m, hfam⟩ := h
  have hκ : (-(4 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
    simp [Real.pi_ne_zero]
  refine ⟨n + n,
    Fin.append (fun i => (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (2 * (q i : ℂ))))
      (fun i => (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (-(8 * (Real.pi : ℂ) ^ 2)))),
    Fin.append (fun i => p i) (fun i => p i + 1),
    Fin.append (fun i => q i - 1) (fun i => q i),
    Fin.append (fun i => m i) (fun i => m i + 1), fun v hv ζ₀ => ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  have hD : ∀ d : ℂ, kernelGd a b v ζ₀ d = ∑ i, kernelTder (γ i) (p i) (q i) (m i) v ζ₀ d := by
    intro d
    have hG := kernelG_hasDerivAt_line a b v hv ζ₀ d
    have hfun : (fun x : ℝ => kernelG a b v (ζ₀ + x * d))
        = fun x : ℝ => ∑ i, kernelT (γ i) (p i) (q i) (m i) v (ζ₀ + x * d) :=
      funext fun x => hfam v hv _
    rw [hfun] at hG
    exact hG.unique
      (HasDerivAt.fun_sum fun i _ => kernelT_line_hasDerivAt (γ i) (p i) (q i) (m i) v ζ₀ d)
  have hmain : -(4 * (Real.pi : ℂ) * Complex.I) * kernelG a (b + 1) v ζ₀
      = ∑ i, (kernelT (γ i * (2 * (q i : ℂ))) (p i) (q i - 1) (m i) v ζ₀
          + kernelT (γ i * (-(8 * (Real.pi : ℂ) ^ 2))) (p i + 1) (q i) (m i + 1) v ζ₀) := by
    rw [← kernelGd_add a b v hv ζ₀, hD 1, hD Complex.I, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => kernelTder_add (γ i) (p i) (q i) (m i) v ζ₀
  calc kernelG a (b + 1) v ζ₀
      = (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹
          * (-(4 * (Real.pi : ℂ) * Complex.I) * kernelG a (b + 1) v ζ₀) := by
        rw [← mul_assoc, inv_mul_cancel₀ hκ, one_mul]
    _ = ∑ i, (kernelT ((-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (2 * (q i : ℂ))))
            (p i) (q i - 1) (m i) v ζ₀
          + kernelT ((-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ * (γ i * (-(8 * (Real.pi : ℂ) ^ 2))))
            (p i + 1) (q i) (m i + 1) v ζ₀) := by
        rw [hmain, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_add, ← kernelT_mul_left (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ (γ i * (2 * (q i : ℂ))),
          ← kernelT_mul_left (-(4 * (Real.pi : ℂ) * Complex.I))⁻¹ (γ i * (-(8 * (Real.pi : ℂ) ^ 2)))]

private theorem family_zero_zero :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      kernelG 0 0 v ζ = ∑ i, kernelT (γ i) (p i) (q i) (m i) v ζ :=
  ⟨1, fun _ => (Real.pi : ℂ), fun _ => 0, fun _ => 0, fun _ => 0, fun v hv ζ => by
    rw [Fin.sum_univ_one, kernelG_zero_zero v hv ζ]⟩

private theorem family_zero (b : ℕ) :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      kernelG 0 b v ζ = ∑ i, kernelT (γ i) (p i) (q i) (m i) v ζ := by
  induction b with
  | zero => exact family_zero_zero
  | succ b ih => exact family_right 0 b ih

private theorem family (a b : ℕ) :
    ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      kernelG a b v ζ = ∑ i, kernelT (γ i) (p i) (q i) (m i) v ζ := by
  induction a with
  | zero => exact family_zero b
  | succ a ih => exact family_left a b ih

private theorem norm_pow_le (z : ℂ) (n : ℕ) : ‖z‖ ^ n ≤ (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
  have h1 : ‖z‖ ^ n = (‖z‖ ^ 2) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast ‖z‖ n, ← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    push_cast
    ring
  rw [h1]
  exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)

private theorem majorant_integrable (n : ℕ) (σ : ℝ) (hσ : (n : ℝ) / 2 + 1 < σ) :
    Integrable (fun z : ℂ => ‖z‖ ^ n * (1 + ‖z‖ ^ 2) ^ (-σ)) := by
  have hnr : (Module.finrank ℝ ℂ : ℝ) < 2 * σ - n := by
    rw [Complex.finrank_real_complex]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hnr).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (by fun_prop : Measurable fun z : ℂ => ‖z‖ ^ n * (1 + ‖z‖ ^ 2) ^ (-σ)).aestronglyMeasurable
  · have hpos : 0 < 1 + ‖z‖ ^ 2 := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖z‖ ^ n * (1 + ‖z‖ ^ 2) ^ (-σ)
        ≤ (1 + ‖z‖ ^ 2) ^ ((n : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (norm_pow_le z n) (by positivity)
      _ = (1 + ‖z‖ ^ 2) ^ (-(2 * σ - n) / 2) := by
          rw [← Real.rpow_add hpos]
          congr 1
          ring

private theorem norm_char (ζ z : ℂ) : ‖Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))‖ = 1 := by
  rw [← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]

private theorem laplace_complex (X : ℝ) (hX : 0 < X) (w : ℂ) (hw : 0 < w.re) :
    ((X : ℂ)) ^ (-w) * Complex.Gamma w
      = ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-((X : ℂ) * v)) := by
  have harg : ((X : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hX.le]
    exact Real.pi_ne_zero.symm
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hX, one_div, Complex.inv_cpow _ _ harg,
    Complex.cpow_neg]

private theorem laplaceKernel_integrableOn_real (X σ : ℝ) (hX : 0 < X) (hσ : 0 < σ) :
    IntegrableOn (fun v : ℝ => v ^ (σ - 1) * Real.exp (-(X * v))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ - 1) (p := 1) (b := X)
    (by linarith) one_pos hX
  refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
  dsimp only
  rw [Real.rpow_one, neg_mul]

private theorem laplaceKernel_integrableOn (X : ℝ) (hX : 0 < X) (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (w - 1) * Complex.exp (-((X : ℂ) * v))) (Ioi 0) := by
  refine Integrable.mono' (laplaceKernel_integrableOn_real X w.re hX hw) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun v hv => ?_) measurableSet_Ioi
    exact (ContinuousAt.mul
      (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Complex.ofReal_mem_slitPlane.mpr (mem_Ioi.mp hv)))
      (Complex.continuous_exp.comp (by fun_prop)).continuousAt).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun v hv => le_of_eq ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hv), Complex.sub_re,
      Complex.one_re, Complex.norm_exp, Complex.neg_re, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem joint_integrable (a b : ℕ) (w ζ : ℂ) (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) :
    Integrable (Function.uncurry fun (z : ℂ) (v : ℝ) =>
        z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))))
      ((volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hσ : 0 < w.re := by
    have h0 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) / 2 := by positivity
    linarith

  have hmeas : AEStronglyMeasurable (Function.uncurry fun (z : ℂ) (v : ℝ) =>
        z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))))
      ((volume : Measure ℂ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hc : ContinuousOn (fun p : ℂ × ℝ =>
        p.1 ^ a * (starRingEnd ℂ) p.1 ^ b * Complex.exp (-(((4 * Real.pi * (ζ * p.1).re : ℝ) : ℂ) * Complex.I)) * ((p.2 : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖p.1‖ ^ 2 : ℝ) : ℂ) * p.2)))) (univ ×ˢ Ioi (0 : ℝ)) := by
      refine ContinuousOn.mul (Continuous.continuousOn ?_)
        (ContinuousOn.mul ?_ (Continuous.continuousOn ?_))
      · exact ((continuous_fst.pow a).mul
          ((Complex.continuous_conj.comp continuous_fst).pow b)).mul
          (Complex.continuous_exp.comp (by fun_prop))
      · intro p hp
        exact (ContinuousAt.cpow (Complex.continuous_ofReal.comp continuous_snd).continuousAt
          continuousAt_const
          (Complex.ofReal_mem_slitPlane.mpr (mem_Ioi.mp (Set.mem_prod.mp hp).2))).continuousWithinAt
      · exact Complex.continuous_exp.comp (by fun_prop)
    have h := hc.aestronglyMeasurable (μ := (volume : Measure ℂ).prod (volume : Measure ℝ))
      (MeasurableSet.univ.prod measurableSet_Ioi)
    rw [← Measure.prod_restrict, Measure.restrict_univ] at h
    exact h

  have h5 : ∀ z : ℂ, ∫ v in Ioi (0 : ℝ), ‖z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v)))‖
      = Real.Gamma w.re * (‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-w.re)) := by
    intro z
    have hX : 0 < 1 + ‖z‖ ^ 2 := by positivity
    have hnorm : ∀ v ∈ Ioi (0 : ℝ), ‖z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v)))‖
        = ‖z‖ ^ (a + b) * (v ^ (w.re - 1) * Real.exp (-((1 + ‖z‖ ^ 2) * v))) := by
      intro v hv
      rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_char ζ z,
        mul_one, ← pow_add, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hv),
        Complex.sub_re, Complex.one_re, Complex.norm_exp, Complex.neg_re, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    rw [setIntegral_congr_fun measurableSet_Ioi hnorm, integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi hσ hX, one_div, Real.inv_rpow hX.le,
      ← Real.rpow_neg hX.le]
    ring
  rw [integrable_prod_iff hmeas]
  refine ⟨Filter.Eventually.of_forall fun z => ?_, ?_⟩
  · show Integrable (fun v : ℝ => z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
        * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v)))) (volume.restrict (Ioi (0 : ℝ)))
    exact Integrable.const_mul (laplaceKernel_integrableOn (1 + ‖z‖ ^ 2) (by positivity) w hσ)
      (z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
  · exact ((majorant_integrable (a + b) w.re hw).const_mul (Real.Gamma w.re)).congr
      (Filter.Eventually.of_forall fun z => (h5 z).symm)

private theorem transform_eq_laplace (a b : ℕ) (w ζ : ℂ)
    (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) :
    Complex.Gamma w * (∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
      = ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
          ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
            * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) := by
  have hσ : 0 < w.re := by
    have h0 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) / 2 := by positivity
    linarith

  have h1 : ∀ z : ℂ, Complex.Gamma w * (z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
        * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
      = ∫ v in Ioi (0 : ℝ), z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))) := by
    intro z
    rw [integral_const_mul, ← laplace_complex (1 + ‖z‖ ^ 2) (by positivity) w hσ]
    ring

  have h2 : ∀ v : ℝ, (∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))))
      = (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
          ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
            * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) := by
    intro v
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v)))
      = (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
          (z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
            * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
    have hsplit : Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))
        = Complex.exp (-(v : ℂ)) * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hsplit]
    ring
  calc Complex.Gamma w * (∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
      = ∫ z : ℂ, Complex.Gamma w * (z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) := (integral_const_mul _ _).symm
    _ = ∫ z : ℂ, ∫ v in Ioi (0 : ℝ), z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))) :=
          integral_congr_ae (Filter.Eventually.of_forall h1)
    _ = ∫ v in Ioi (0 : ℝ), ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) * ((v : ℂ) ^ (w - 1) * Complex.exp (-(((1 + ‖z‖ ^ 2 : ℝ) : ℂ) * v))) :=
          integral_integral_swap (joint_integrable a b w ζ hw)
    _ = ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
          ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
            * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)) :=
          integral_congr_ae (Filter.Eventually.of_forall h2)

private theorem re_sq_add_im_sq (ζ : ℂ) :
    ((ζ.re : ℝ) : ℂ) ^ 2 + ((ζ.im : ℝ) : ℂ) ^ 2 = ((‖ζ‖ : ℝ) : ℂ) ^ 2 := by
  have h : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  exact_mod_cast h.symm

private theorem expKernel_integrableOn_real (σ t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => u ^ σ * Real.exp (-(u + t / u))) (Ioi 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-1 - σ)
  have hg : IntegrableOn
      (fun u : ℝ => (Nat.factorial N : ℝ) / t ^ N * (u ^ (σ + N) * Real.exp (-u))) (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    have h := Real.GammaIntegral_convergent (s := σ + N + 1) (by linarith)
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    show Real.exp (-u) * u ^ (σ + N + 1 - 1) = u ^ (σ + N) * Real.exp (-u)
    rw [add_sub_cancel_right, mul_comm]
  refine Integrable.mono' hg ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
    have hu : 0 < u := mem_Ioi.mp hu
    have h1 : ContinuousAt (fun u : ℝ => -(u + t / u)) u := by fun_prop (disch := exact hu.ne')
    exact ((Real.continuousAt_rpow_const u σ (Or.inl hu.ne')).mul
      (Real.continuous_exp.continuousAt.comp h1)).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => ?_
    have hu : 0 < u := mem_Ioi.mp hu
    have hx : 0 < t / u := div_pos ht hu
    have hbound : Real.exp (-(t / u)) ≤ (Nat.factorial N : ℝ) * u ^ N / t ^ N := by
      calc Real.exp (-(t / u)) = (Real.exp (t / u))⁻¹ := Real.exp_neg _
        _ ≤ ((t / u) ^ N / (Nat.factorial N : ℝ))⁻¹ :=
            inv_anti₀ (by positivity) (Real.pow_div_factorial_le_exp (t / u) hx.le N)
        _ = (Nat.factorial N : ℝ) * u ^ N / t ^ N := by
            rw [inv_div, div_pow, div_div_eq_mul_div]
    show ‖u ^ σ * Real.exp (-(u + t / u))‖
      ≤ (Nat.factorial N : ℝ) / t ^ N * (u ^ (σ + N) * Real.exp (-u))
    calc ‖u ^ σ * Real.exp (-(u + t / u))‖ = u ^ σ * Real.exp (-u) * Real.exp (-(t / u)) := by
          rw [Real.norm_of_nonneg (by positivity), neg_add, Real.exp_add, mul_assoc]
      _ ≤ u ^ σ * Real.exp (-u) * ((Nat.factorial N : ℝ) * u ^ N / t ^ N) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = (Nat.factorial N : ℝ) / t ^ N * (u ^ (σ + N) * Real.exp (-u)) := by
          rw [Real.rpow_add_natCast hu.ne']
          ring

private theorem archKernel_integrableOn (z : ℂ) (r : ℝ) (hr : r ≠ 0) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ z
      * Complex.exp (-(1 : ℂ) * ((u : ℂ) + (r : ℂ) ^ 2 / (u : ℂ)))) (Ioi 0) := by
  refine Integrable.mono' (expKernel_integrableOn_real z.re (r ^ 2) (by positivity)) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (mem_Ioi.mp hu))
    have h1 : ContinuousAt (fun u : ℝ => -(1 : ℂ) * ((u : ℂ) + (r : ℂ) ^ 2 / (u : ℂ))) u := by
      fun_prop (disch := exact hu0)
    exact (ContinuousAt.mul
      (ContinuousAt.cpow Complex.continuous_ofReal.continuousAt continuousAt_const
        (Complex.ofReal_mem_slitPlane.mpr (mem_Ioi.mp hu)))
      (Complex.continuous_exp.continuousAt.comp h1)).continuousWithinAt
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun u hu => le_of_eq ?_
    have hu : 0 < u := mem_Ioi.mp hu
    have hcast : -(1 : ℂ) * ((u : ℂ) + (r : ℂ) ^ 2 / (u : ℂ)) = ((-(u + r ^ 2 / u) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, hcast, Complex.norm_exp_ofReal]

private theorem head_of_family (a b : ℕ)
    (hfam : ∃ (n : ℕ) (γ : Fin n → ℂ) (p q m : Fin n → ℕ), ∀ v : ℝ, 0 < v → ∀ ζ : ℂ,
      kernelG a b v ζ = ∑ i, kernelT (γ i) (p i) (q i) (m i) v ζ) :
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 →
        J w ζ = ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w ζ : ℂ), ‖w‖ ≤ R → ζ ≠ 0 →
        ‖J w ζ‖ ≤ C * max 1 (‖ζ‖ ^ (-(N : ℝ))) * Real.exp (-c' * ‖ζ‖)) := by
  obtain ⟨n, γ, p, q, m, hfam⟩ := hfam

  have ha : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Differentiable ℂ ((fun (i : Fin n) (w : ℂ) => γ i * (Complex.Gamma w)⁻¹) i) :=
    fun i _ => Complex.differentiable_one_div_Gamma.const_mul (γ i)

  have hβ : ∀ ζ : ℂ, ∀ i ∈ (Finset.univ : Finset (Fin n)),
      ‖ζ ^ p i * (starRingEnd ℂ) ζ ^ q i / ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i)‖ ≤ 1 := by
    intro ζ i _
    have hle : ‖ζ‖ ≤ 2 * Real.pi * ‖ζ‖ := by nlinarith [Real.two_le_pi, norm_nonneg ζ]
    rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_conj, ← pow_add, norm_pow,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ‖ζ‖)]
    exact div_le_one_of_le₀ (pow_le_pow_left₀ (norm_nonneg _) hle _) (by positivity)
  refine ⟨fun w ζ => ∑ i : Fin n, (γ i * (Complex.Gamma w)⁻¹)
      * (ζ ^ p i * (starRingEnd ℂ) ζ ^ q i / ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i))
      * ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i)
      * ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w + (-2 - (m i : ℂ))) * Complex.exp (-(1 : ℂ) * ((u : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (u : ℂ))),
    fun ζ hζ => ?_, fun w ζ hw hζ => ?_, fun R => ?_⟩
  ·
    have hr : 2 * Real.pi * ‖ζ‖ ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (norm_ne_zero_iff.mpr hζ)
    try dsimp only
    exact differentiable_sum_archIntegral (Finset.univ : Finset (Fin n))
      (fun (i : Fin n) (w : ℂ) => γ i * (Complex.Gamma w)⁻¹) ha
      (fun i => ζ ^ p i * (starRingEnd ℂ) ζ ^ q i / ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i))
      (fun i => -2 - (m i : ℂ)) (fun i => p i + q i) 1 (by norm_num) (2 * Real.pi * ‖ζ‖) hr
  ·
    have hσ : 0 < w.re := by
      have h0 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) / 2 := by positivity
      linarith
    have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hσ
    have hr : 2 * Real.pi * ‖ζ‖ ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (norm_ne_zero_iff.mpr hζ)
    have hrC : ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr

    have hterm : ∀ i : Fin n, ∀ v ∈ Ioi (0 : ℝ),
        (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) * kernelT (γ i) (p i) (q i) (m i) v ζ
          = (γ i * ζ ^ p i * (starRingEnd ℂ) ζ ^ q i)
            * ((v : ℂ) ^ (w + (-2 - (m i : ℂ))) * Complex.exp (-(1 : ℂ) * ((v : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (v : ℂ)))) := by
      intro i v hv
      have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (mem_Ioi.mp hv))
      have hpow : (v : ℂ) ^ (w - 1) * ((v : ℂ) ^ (m i + 1))⁻¹ = (v : ℂ) ^ (w + (-2 - (m i : ℂ))) := by
        rw [← Complex.cpow_natCast, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hv0]
        congr 1
        push_cast
        ring
      have hexp : Complex.exp (-(v : ℂ)) * kernelE v ζ
          = Complex.exp (-(1 : ℂ) * ((v : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (v : ℂ))) := by
        rw [kernelE, ← Complex.exp_add]
        congr 1
        rw [re_sq_add_im_sq ζ]
        push_cast
        ring
      rw [kernelT]
      calc _ = (γ i * ζ ^ p i * (starRingEnd ℂ) ζ ^ q i)
            * (((v : ℂ) ^ (w - 1) * ((v : ℂ) ^ (m i + 1))⁻¹) * (Complex.exp (-(v : ℂ)) * kernelE v ζ)) := by
              ring
        _ = _ := by rw [hpow, hexp]

    have hint : ∀ i : Fin n, IntegrableOn (fun v : ℝ =>
        (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) * kernelT (γ i) (p i) (q i) (m i) v ζ) (Ioi 0) :=
      fun i => IntegrableOn.congr_fun
        (Integrable.const_mul (archKernel_integrableOn (w + (-2 - (m i : ℂ))) (2 * Real.pi * ‖ζ‖) hr)
          (γ i * ζ ^ p i * (starRingEnd ℂ) ζ ^ q i))
        (fun v hv => (hterm i v hv).symm) measurableSet_Ioi

    have hG : ∀ v ∈ Ioi (0 : ℝ),
        (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) *
            (∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * Complex.exp (-(v : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)
              * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I)))
          = ∑ i, (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) * kernelT (γ i) (p i) (q i) (m i) v ζ := by
      intro v hv
      have hfam' := hfam v (mem_Ioi.mp hv) ζ
      simp only [kernelG] at hfam'
      rw [hfam', Finset.mul_sum]
    have hI : ∀ i : Fin n,
        (∫ v in Ioi (0 : ℝ),
            (v : ℂ) ^ (w - 1) * Complex.exp (-(v : ℂ)) * kernelT (γ i) (p i) (q i) (m i) v ζ)
          = (γ i * ζ ^ p i * (starRingEnd ℂ) ζ ^ q i)
            * ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w + (-2 - (m i : ℂ))) * Complex.exp (-(1 : ℂ) * ((v : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (v : ℂ))) := by
      intro i
      rw [setIntegral_congr_fun measurableSet_Ioi (hterm i), integral_const_mul]
    try dsimp only
    apply mul_left_cancel₀ hΓ
    rw [transform_eq_laplace a b w ζ hw, setIntegral_congr_fun measurableSet_Ioi hG,
      integral_finsetSum _ (fun i _ => hint i), Finset.sum_congr rfl (fun i _ => hI i),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← mul_div_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hrC)]
    calc _ = (Complex.Gamma w * (Complex.Gamma w)⁻¹) * (γ i * (ζ ^ p i * (starRingEnd ℂ) ζ ^ q i)
            * ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w + (-2 - (m i : ℂ))) * Complex.exp (-(1 : ℂ) * ((v : ℂ) + ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ 2 / (v : ℂ)))) := by
          ring
      _ = _ := by
          rw [mul_inv_cancel₀ hΓ]
          ring
  ·
    obtain ⟨C, c', N, hC, hc', hB⟩ := exists_norm_sum_archIntegral_le
      (Finset.univ : Finset (Fin n)) (fun (i : Fin n) (w : ℂ) => γ i * (Complex.Gamma w)⁻¹) ha
      (fun i => -2 - (m i : ℂ)) (fun i => p i + q i) 1 (by norm_num) R
    refine ⟨C, 2 * Real.pi * c', N, hC, by positivity, fun w ζ hwR hζ => ?_⟩
    have hr : 2 * Real.pi * ‖ζ‖ ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (norm_ne_zero_iff.mpr hζ)
    have h := hB (fun i => ζ ^ p i * (starRingEnd ℂ) ζ ^ q i
        / ((2 * Real.pi * ‖ζ‖ : ℝ) : ℂ) ^ (p i + q i)) (hβ ζ) w (2 * Real.pi * ‖ζ‖) hwR hr
    try dsimp only
    refine h.trans ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ‖ζ‖)]
    have hmax : max 1 ((2 * Real.pi * ‖ζ‖) ^ (-(N : ℝ))) ≤ max 1 (‖ζ‖ ^ (-(N : ℝ))) := by
      refine max_le_max le_rfl ?_
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2 * Real.pi * ‖ζ‖), Real.rpow_neg (norm_nonneg ζ)]
      refine inv_anti₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr hζ) _) ?_
      exact Real.rpow_le_rpow (norm_nonneg ζ) (by nlinarith [Real.two_le_pi, norm_nonneg ζ])
        (Nat.cast_nonneg N)
    have hexp : Real.exp (-c' * (2 * Real.pi * ‖ζ‖)) = Real.exp (-(2 * Real.pi * c') * ‖ζ‖) := by
      congr 1
      ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hC.le) (Real.exp_pos _).le

theorem exists_complexKType (a b : ℕ) :
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → Differentiable ℂ (fun w : ℂ => J w ζ)) ∧
      (∀ (w ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 →
        J w ζ = ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w ζ : ℂ), ‖w‖ ≤ R → ζ ≠ 0 →
        ‖J w ζ‖ ≤ C * max 1 (‖ζ‖ ^ (-(N : ℝ))) * Real.exp (-c' * ‖ζ‖)) := by
  exact head_of_family a b (family a b)

/-! ### The `GL₂(ℝ)`-type -/

private noncomputable def kernelK (z : ℂ) (t : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ z * Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u))

private def IsComb (Φ : ℂ → ℝ → ℂ) : Prop :=
  ∃ (κ : Type) (T : Finset κ) (a : κ → ℂ → ℂ) (β b : κ → ℂ) (l : κ → ℕ),
    (∀ i ∈ T, Differentiable ℂ (a i)) ∧ (∀ i ∈ T, ‖β i‖ ≤ 1) ∧
      ∀ (w : ℂ) (t : ℝ), t ≠ 0 → Φ w t = ∑ i ∈ T, a i w * β i * (t : ℂ) ^ l i *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w + b i) * Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u))

private theorem isComb_congr {Φ Ψ : ℂ → ℝ → ℂ} (h : IsComb Φ)
    (hΨ : ∀ (w : ℂ) (t : ℝ), t ≠ 0 → Ψ w t = Φ w t) : IsComb Ψ := by
  obtain ⟨κ, T, a, β, b, l, ha, hβ, hΦ⟩ := h
  exact ⟨κ, T, a, β, b, l, ha, hβ, fun w t ht => (hΨ w t ht).trans (hΦ w t ht)⟩

private theorem isComb_term (a : ℂ → ℂ) (ha : Differentiable ℂ a) (l : ℕ) (b : ℂ) :
    IsComb (fun w t => a w * (t : ℂ) ^ l * kernelK (w + b) t) := by
  refine ⟨Unit, {()}, fun _ => a, fun _ => 1, fun _ => b, fun _ => l, fun _ _ => ha,
    fun _ _ => by simp, fun w t _ => ?_⟩
  rw [Finset.sum_singleton]
  show a w * (t : ℂ) ^ l * kernelK (w + b) t = a w * 1 * (t : ℂ) ^ l * kernelK (w + b) t
  rw [mul_one]

private theorem isComb_add {Φ Ψ : ℂ → ℝ → ℂ} (hΦ : IsComb Φ) (hΨ : IsComb Ψ) :
    IsComb (fun w t => Φ w t + Ψ w t) := by
  obtain ⟨κ₁, T₁, a₁, β₁, b₁, l₁, ha₁, hβ₁, h₁⟩ := hΦ
  obtain ⟨κ₂, T₂, a₂, β₂, b₂, l₂, ha₂, hβ₂, h₂⟩ := hΨ
  refine ⟨κ₁ ⊕ κ₂, T₁.disjSum T₂, Sum.elim a₁ a₂, Sum.elim β₁ β₂, Sum.elim b₁ b₂, Sum.elim l₁ l₂,
    ?_, ?_, fun w t ht => ?_⟩
  · rintro (i | i) hi
    · exact ha₁ i (Finset.inl_mem_disjSum.mp hi)
    · exact ha₂ i (Finset.inr_mem_disjSum.mp hi)
  · rintro (i | i) hi
    · exact hβ₁ i (Finset.inl_mem_disjSum.mp hi)
    · exact hβ₂ i (Finset.inr_mem_disjSum.mp hi)
  · show Φ w t + Ψ w t = _
    rw [h₁ w t ht, h₂ w t ht, Finset.sum_disjSum]
    simp only [Sum.elim_inl, Sum.elim_inr]

private theorem isComb_const_mul {Φ : ℂ → ℝ → ℂ} (hΦ : IsComb Φ) (c : ℂ) :
    IsComb (fun w t => c * Φ w t) := by
  obtain ⟨κ, T, a, β, b, l, ha, hβ, h⟩ := hΦ
  refine ⟨κ, T, fun i w => c * a i w, β, b, l, fun i hi => (ha i hi).const_mul c, hβ,
    fun w t ht => ?_⟩
  show c * Φ w t = _
  rw [h w t ht, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc]

private theorem isComb_shift {Φ : ℂ → ℝ → ℂ} (hΦ : IsComb Φ) (s : ℂ) :
    IsComb (fun w t => Φ (w + s) t) := by
  obtain ⟨κ, T, a, β, b, l, ha, hβ, h⟩ := hΦ
  refine ⟨κ, T, fun i w => a i (w + s), β, fun i => b i + s, l,
    fun i hi => (ha i hi).comp (differentiable_id.add_const s), hβ, fun w t ht => ?_⟩
  show Φ (w + s) t = _
  rw [h (w + s) t ht]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [add_assoc, add_comm s (b i)]

private noncomputable def gammaFactor (w : ℂ) : ℂ := (Real.pi : ℂ) ^ w * (Complex.Gamma w)⁻¹

private theorem differentiable_gammaFactor : Differentiable ℂ gammaFactor := by
  show Differentiable ℂ fun w => (Real.pi : ℂ) ^ w * (Complex.Gamma w)⁻¹
  refine Differentiable.mul (fun w => ?_) Complex.differentiable_one_div_Gamma
  exact differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

private noncomputable def termFamily (ε : ℝ) : ℕ → ℂ → ℝ → ℂ
  | 0 => fun w t => gammaFactor w * kernelK (w - 3 / 2) t
  | 1 => fun w t => -Complex.I * gammaFactor w * t * kernelK (w - 5 / 2) t
      + ε * Complex.I * (gammaFactor w * kernelK (w - 3 / 2) t)
  | m + 2 => fun w t => termFamily ε m (w - 1) t + 2 * ε * Complex.I * termFamily ε (m + 1) w t

private theorem isComb_termFamily (ε : ℝ) (m : ℕ) : IsComb (termFamily ε m) := by
  have h0 : IsComb (termFamily ε 0) := by
    refine isComb_congr (isComb_term gammaFactor differentiable_gammaFactor 0 (-(3 / 2))) ?_
    intro w t _
    show gammaFactor w * kernelK (w - 3 / 2) t = gammaFactor w * (t : ℂ) ^ 0 * kernelK (w + -(3 / 2)) t
    rw [pow_zero, mul_one, sub_eq_add_neg]
  have h1 : IsComb (termFamily ε 1) := by
    refine isComb_congr (isComb_add (isComb_term (fun w => -Complex.I * gammaFactor w)
      (differentiable_gammaFactor.const_mul _) 1 (-(5 / 2))) (isComb_const_mul h0 (ε * Complex.I))) ?_
    intro w t _
    show -Complex.I * gammaFactor w * t * kernelK (w - 5 / 2) t + ε * Complex.I * (gammaFactor w * kernelK (w - 3 / 2) t)
      = -Complex.I * gammaFactor w * (t : ℂ) ^ 1 * kernelK (w + -(5 / 2)) t + ε * Complex.I * termFamily ε 0 w t
    rw [pow_one, sub_eq_add_neg]
    rfl
  have hstep : ∀ m, IsComb (termFamily ε m) → IsComb (termFamily ε (m + 1)) →
      IsComb (termFamily ε (m + 2)) := by
    intro m hm hm1
    refine isComb_congr (isComb_add (isComb_shift hm (-1))
      (isComb_const_mul hm1 (2 * ε * Complex.I))) ?_
    intro w t _
    show termFamily ε m (w - 1) t + 2 * ε * Complex.I * termFamily ε (m + 1) w t
      = termFamily ε m (w + -1) t + 2 * ε * Complex.I * termFamily ε (m + 1) w t
    rw [sub_eq_add_neg]
  have key : ∀ m, IsComb (termFamily ε m) ∧ IsComb (termFamily ε (m + 1)) := by
    intro m
    induction m with
    | zero => exact ⟨h0, h1⟩
    | succ m ih => exact ⟨ih.2, hstep m ih.1 ih.2⟩
  exact (key m).1

private noncomputable def signWeight (k : ℤ) : ℝ := if 0 ≤ k then -1 else 1

private theorem signWeight_cases (k : ℤ) : signWeight k = 1 ∨ signWeight k = -1 := by
  unfold signWeight
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

private noncomputable def realJ (k : ℤ) (w : ℂ) (t : ℝ) : ℂ :=
  termFamily (signWeight k) k.natAbs (w + (k.natAbs : ℂ) / 2) t

private theorem isComb_realJ (k : ℤ) : IsComb (realJ k) :=
  isComb_shift (isComb_termFamily (signWeight k) k.natAbs) ((k.natAbs : ℂ) / 2)

private noncomputable def charFn (t x : ℝ) : ℂ := Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I)

private noncomputable def realG (ε : ℝ) (m : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ, ((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x

private theorem integrableOn_laplace (w : ℂ) (hw : 0 < w.re) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun v : ℝ => (v : ℂ) ^ (w - 1) * Complex.exp (-((r : ℂ) * v))) (Ioi 0) := by
  by_contra h
  have key := Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hr
  rw [integral_undef h] at key
  refine (mul_ne_zero ?_ (Complex.Gamma_ne_zero_of_re_pos hw)) key.symm
  rw [Complex.cpow_def_of_ne_zero (one_div_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'))]
  exact Complex.exp_ne_zero _

private theorem laplace_real (w : ℂ) (hw : 0 < w.re) (x : ℝ) :
    (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) = gammaFactor w *
      ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v)) := by
  have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hr : (0 : ℝ) < Real.pi * (1 + x ^ 2) := mul_pos Real.pi_pos hq
  have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hQ : (((1 + x ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hπw : ((Real.pi : ℝ) : ℂ) ^ w ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]
    exact Complex.exp_ne_zero _
  have hQw : (((1 + x ^ 2 : ℝ) : ℂ)) ^ w ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hQ]
    exact Complex.exp_ne_zero _
  have h1 : (1 / ((Real.pi * (1 + x ^ 2) : ℝ) : ℂ)) ^ w
      = (((Real.pi : ℝ) : ℂ) ^ w)⁻¹ * ((((1 + x ^ 2 : ℝ)) : ℂ) ^ w)⁻¹ := by
    rw [one_div, Complex.inv_cpow _ _
        (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le hq.le, mul_inv]
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hr, h1, Complex.cpow_neg]
  unfold gammaFactor
  field_simp

private theorem integrable_weight (g : ℝ → ℂ) (hg : Continuous g) (p : ℕ)
    (hgb : ∀ x, ‖g x‖ ≤ (1 + x ^ 2) ^ ((p : ℝ) / 2)) (w : ℂ) (hw : ((p : ℝ) + 1) / 2 < w.re)
    (t : ℝ) :
    Integrable (fun x : ℝ => g x * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x) := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * w.re - p := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hr).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine (hg.mul ?_).mul ?_
    · exact Continuous.cpow (by fun_prop) continuous_const
        (fun x => Complex.ofReal_mem_slitPlane.mpr (by positivity))
    · unfold charFn
      fun_prop
  · have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
    rw [norm_mul, norm_mul, charFn, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re, Real.norm_eq_abs, sq_abs]
    calc ‖g x‖ * (1 + x ^ 2) ^ (-w.re)
        ≤ (1 + x ^ 2) ^ ((p : ℝ) / 2) * (1 + x ^ 2) ^ (-w.re) := by
          gcongr
          exact hgb x
      _ = (1 + x ^ 2) ^ (-(2 * w.re - p) / 2) := by
          rw [← Real.rpow_add hq]
          congr 1
          ring

private theorem fubini (g : ℝ → ℂ) (hg : Continuous g) (p : ℕ)
    (hgb : ∀ x, ‖g x‖ ≤ (1 + x ^ 2) ^ ((p : ℝ) / 2)) (w : ℂ) (hw : ((p : ℝ) + 1) / 2 < w.re)
    (t : ℝ) :
    ∫ x : ℝ, g x * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x
      = gammaFactor w * ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ (w - 1) * Complex.exp (-((Real.pi * v : ℝ) : ℂ)) *
          ∫ x : ℝ, charFn t x * (g x * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hw0 : 0 < w.re := by linarith
  have hL : ∀ x : ℝ, g x * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x
      = gammaFactor w * ∫ v in Ioi (0 : ℝ), g x * charFn t x *
          ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v))) := by
    intro x
    rw [laplace_real w hw0 x, integral_const_mul]
    ring
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x v : ℝ) => g x * charFn t x *
      ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v))))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    refine Measurable.aestronglyMeasurable ?_
    show Measurable fun q : ℝ × ℝ => g q.1 * charFn t q.1 *
      ((q.2 : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + q.1 ^ 2) : ℝ) : ℂ) * q.2)))
    have hgm : Measurable g := hg.measurable
    unfold charFn
    fun_prop
  have hInt : Integrable (Function.uncurry fun (x v : ℝ) => g x * charFn t x *
      ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v))))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair]
      exact (integrableOn_laplace w hw0 _ (mul_pos Real.pi_pos (by positivity))).const_mul _
    · simp only [Function.uncurry_apply_pair]
      have hnorm : ∀ x : ℝ, ∫ v in Ioi (0 : ℝ), ‖g x * charFn t x *
          ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v)))‖
            = ‖g x‖ * ((1 / (Real.pi * (1 + x ^ 2))) ^ w.re * Real.Gamma w.re) := by
        intro x
        have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
        rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hw0 (mul_pos Real.pi_pos hq),
          ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
        have hv : (0 : ℝ) < v := hv
        have hre : (-((((Real.pi * (1 + x ^ 2) : ℝ) : ℂ)) * v)).re
            = -(Real.pi * (1 + x ^ 2) * v) := by
          rw [← Complex.ofReal_mul, Complex.neg_re, Complex.ofReal_re]
        rw [norm_mul, norm_mul, norm_mul, charFn, Complex.norm_exp_ofReal_mul_I, mul_one,
          Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.sub_re, Complex.one_re, Complex.norm_exp,
          hre]
      simp_rw [hnorm]
      have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * w.re - p := by
        rw [Module.finrank_self]
        push_cast
        linarith
      refine ((integrable_rpow_neg_one_add_norm_sq hr).const_mul
        (Real.Gamma w.re * Real.pi ^ (-w.re))).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
      · refine Continuous.aestronglyMeasurable (hg.norm.mul (Continuous.mul ?_ continuous_const))
        exact (continuous_const.div (by fun_prop)
          (fun x => (mul_pos Real.pi_pos (by positivity)).ne')).rpow_const
          (fun x => Or.inr hw0.le)
      · have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs, sq_abs]
        calc ‖g x‖ * ((1 / (Real.pi * (1 + x ^ 2))) ^ w.re * Real.Gamma w.re)
            ≤ (1 + x ^ 2) ^ ((p : ℝ) / 2) * ((1 / (Real.pi * (1 + x ^ 2))) ^ w.re * Real.Gamma w.re) := by
              gcongr
              exact hgb x
          _ = Real.Gamma w.re * Real.pi ^ (-w.re) * ((1 : ℝ) + x ^ 2) ^ (-(2 * w.re - p) / 2) := by
              rw [one_div, Real.inv_rpow (mul_pos Real.pi_pos hq).le, Real.mul_rpow Real.pi_pos.le hq.le,
                Real.rpow_neg Real.pi_pos.le,
                show (-(2 * w.re - (p : ℝ)) / 2) = (p : ℝ) / 2 + -w.re by ring,
                Real.rpow_add hq, Real.rpow_neg hq.le]
              ring
  simp_rw [hL]
  rw [integral_const_mul]
  congr 1
  rw [integral_integral_swap hInt]
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hsplit : ∀ x : ℝ, g x * charFn t x *
      ((v : ℂ) ^ (w - 1) * Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v)))
        = (v : ℂ) ^ (w - 1) * Complex.exp (-((Real.pi * v : ℝ) : ℂ)) *
          (charFn t x * (g x * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2))) := by
    intro x
    have hexp : Complex.exp (-(((Real.pi * (1 + x ^ 2) : ℝ) : ℂ) * v))
        = Complex.exp (-((Real.pi * v : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    ring
  simp_rw [hsplit]
  rw [integral_const_mul]

private theorem gaussFT (v : ℝ) (hv : 0 < v) (t : ℝ) :
    FourierTransform.fourier (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) t
      = 1 / (v : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2) := by
  have hb : 0 < (v : ℂ).re := by rwa [Complex.ofReal_re]
  rw [fourier_gaussian_pi hb]

private theorem xgaussFT (v : ℝ) (hv : 0 < v) (t : ℝ) :
    ∫ x : ℝ, charFn t x * ((x : ℂ) * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2))
      = 1 / (v : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2)
          * (-Complex.I * t / v) := by
  have hb : 0 < ((Real.pi : ℂ) * v).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_pos Real.pi_pos hv
  have hfi : Integrable (fun x : ℝ => Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) := by
    simpa only [neg_mul] using integrable_cexp_neg_mul_sq hb
  have hfi' : Integrable (fun x : ℝ => x • Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) := by
    simpa only [neg_mul, Complex.real_smul] using integrable_mul_cexp_neg_mul_sq hb
  have hD := Real.hasDerivAt_fourier hfi hfi' t
  rw [fourier_gaussian_pi (by rwa [Complex.ofReal_re] : 0 < (v : ℂ).re)] at hD
  have hD' : HasDerivAt (fun s : ℝ => 1 / (v : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / v * s ^ 2))
      (1 / (v : ℂ) ^ (1 / 2 : ℂ) * (Complex.exp (-(Real.pi : ℂ) / v * t ^ 2)
        * (-(Real.pi : ℂ) / v * (2 * t)))) t := by
    refine HasDerivAt.const_mul _ (HasDerivAt.cexp ?_)
    have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2) (2 * (t : ℂ)) t := by
      simpa using (hasDerivAt_pow 2 t).ofReal_comp
    exact h2.const_mul _
  have huniq := hD.unique hD'
  rw [Real.fourier_real_eq_integral_exp_smul] at huniq
  simp only [smul_eq_mul] at huniq
  have hlin : ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * t) * Complex.I)
      * (-2 * (Real.pi : ℂ) * Complex.I * x * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2))
      = (-2 * (Real.pi : ℂ) * Complex.I)
        * ∫ x : ℝ, charFn t x * ((x : ℂ) * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2)) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    unfold charFn
    ring
  rw [hlin] at huniq
  have hc : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  apply mul_left_cancel₀ hc
  rw [huniq]
  set c : ℂ := 1 / (v : ℂ) ^ (1 / 2 : ℂ)
  set E : ℂ := Complex.exp (-(Real.pi : ℂ) / v * t ^ 2)
  linear_combination (-2 * (Real.pi : ℂ) * c * E * t / v) * Complex.I_sq

private theorem coe_bound (x : ℝ) : ‖((x : ℝ) : ℂ)‖ ≤ (1 + x ^ 2) ^ (((1 : ℕ) : ℝ) / 2) := by
  rw [Complex.norm_real, Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs, Nat.cast_one, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt (by nlinarith)

private theorem base0 (w : ℂ) (hw : 1 / 2 < w.re) (t : ℝ) :
    gammaFactor w * kernelK (w - 3 / 2) t
      = ∫ x : ℝ, 1 * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x := by
  rw [fubini (fun _ : ℝ => (1 : ℂ)) continuous_const 0 (fun x => by simp) w
    (by push_cast; linarith) t]
  congr 1
  unfold kernelK
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hv : (0 : ℝ) < v := hv
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hinner : ∫ x : ℝ, charFn t x * (1 * Complex.exp (-(Real.pi : ℂ) * v * x ^ 2))
      = 1 / (v : ℂ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2) := by
    simp_rw [one_mul]
    rw [← gaussFT v hv t, Real.fourier_real_eq_integral_exp_smul]
    simp_rw [smul_eq_mul]
    rfl
  rw [hinner]
  have h1 : (v : ℂ) ^ (w - 3 / 2) = (v : ℂ) ^ (w - 1) * (v : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [← Complex.cpow_add _ _ hv0]
    congr 1
    ring
  have h2 : Complex.exp (-(Real.pi : ℂ) * (v + t ^ 2 / v))
      = Complex.exp (-((Real.pi * v : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2, one_div ((v : ℂ) ^ (1 / 2 : ℂ)), ← Complex.cpow_neg]
  ring

private theorem base1 (w : ℂ) (hw : 1 < w.re) (t : ℝ) :
    -Complex.I * gammaFactor w * t * kernelK (w - 5 / 2) t
      = ∫ x : ℝ, (x : ℂ) * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x := by
  rw [fubini (fun x : ℝ => ((x : ℝ) : ℂ)) Complex.continuous_ofReal 1 coe_bound w
    (by push_cast; linarith) t]
  unfold kernelK
  rw [show -Complex.I * gammaFactor w * t * (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w - 5 / 2) *
        Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u)))
      = gammaFactor w * ∫ u in Ioi (0 : ℝ), -Complex.I * t * ((u : ℂ) ^ (w - 5 / 2) *
        Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u))) by rw [integral_const_mul]; ring]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
  have hv : (0 : ℝ) < v := hv
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [xgaussFT v hv t]
  have h1 : (v : ℂ) ^ (w - 5 / 2) = (v : ℂ) ^ (w - 1) * (v : ℂ) ^ (-(1 / 2 : ℂ)) * (v : ℂ)⁻¹ := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hv0, ← Complex.cpow_add _ _ hv0]
    congr 1
    ring
  have h2 : Complex.exp (-(Real.pi : ℂ) * (v + t ^ 2 / v))
      = Complex.exp (-((Real.pi * v : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) / v * t ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, h2, one_div ((v : ℂ) ^ (1 / 2 : ℂ)), ← Complex.cpow_neg]
  ring

private theorem realG_zero (ε : ℝ) (w : ℂ) (t : ℝ) (hw : 1 / 2 < w.re) :
    termFamily ε 0 w t = realG ε 0 w t := by
  show gammaFactor w * kernelK (w - 3 / 2) t
    = ∫ x : ℝ, ((x : ℂ) + ε * Complex.I) ^ 0 * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x
  simp_rw [pow_zero]
  exact base0 w hw t

private theorem realG_one (ε : ℝ) (w : ℂ) (t : ℝ) (hw : 1 < w.re) :
    termFamily ε 1 w t = realG ε 1 w t := by
  have hw' : 1 / 2 < w.re := by linarith
  have hX := integrable_weight (fun x : ℝ => ((x : ℝ) : ℂ)) Complex.continuous_ofReal 1
    coe_bound w (by push_cast; linarith) t
  have h0 := integrable_weight (fun _ : ℝ => (1 : ℂ)) continuous_const 0 (fun x => by simp) w
    (by push_cast; linarith) t
  show -Complex.I * gammaFactor w * t * kernelK (w - 5 / 2) t + ε * Complex.I * (gammaFactor w * kernelK (w - 3 / 2) t)
    = realG ε 1 w t
  rw [base1 w hw t, base0 w hw' t]
  unfold realG
  rw [← integral_const_mul, ← integral_add hX (h0.const_mul _)]
  congr 1
  funext x
  ring

private theorem norm_integrand (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (m : ℕ) (w : ℂ) (t x : ℝ) :
    ‖((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x‖
      = (1 + x ^ 2) ^ ((m : ℝ) / 2 - w.re) := by
  have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hε2 : ε ^ 2 = 1 := by rcases hε with h | h <;> simp [h]
  have hroot : Real.sqrt (x ^ 2 + ε ^ 2) = (1 + x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [hε2, add_comm, Real.sqrt_eq_rpow]
  have hpow : ((1 + x ^ 2) ^ (1 / 2 : ℝ)) ^ m = (1 + x ^ 2) ^ ((1 / 2 : ℝ) * m) := by
    rw [Real.rpow_mul hq.le, Real.rpow_natCast]
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_add_mul_I, hroot, hpow, charFn,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re,
    ← Real.rpow_add hq]
  congr 1
  ring

private theorem integrable_termFamily (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (m : ℕ) (w : ℂ) (t : ℝ)
    (hw : ((m : ℝ) + 1) / 2 < w.re) :
    Integrable (fun x : ℝ =>
      ((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x) := by
  have hr : (Module.finrank ℝ ℝ : ℝ) < 2 * w.re - m := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq hr).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine ((Continuous.pow (by fun_prop) m).mul ?_).mul ?_
    · exact Continuous.cpow (by fun_prop) continuous_const
        (fun x => Complex.ofReal_mem_slitPlane.mpr (by positivity))
    · unfold charFn
      fun_prop
  · rw [norm_integrand ε hε m w t x, Real.norm_eq_abs, sq_abs]
    apply le_of_eq
    congr 1
    ring

private theorem realG_rec (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (m : ℕ) (w : ℂ) (t : ℝ)
    (hw : ((m : ℝ) + 3) / 2 < w.re) :
    realG ε (m + 2) w t = realG ε m (w - 1) t + 2 * ε * Complex.I * realG ε (m + 1) w t := by
  have hε2 : (ε : ℂ) ^ 2 = 1 := by rcases hε with h | h <;> simp [h]
  have hpt : ∀ x : ℝ,
      ((x : ℂ) + ε * Complex.I) ^ (m + 2) * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x
        = ((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(w - 1)) * charFn t x
          + 2 * ε * Complex.I
            * (((x : ℂ) + ε * Complex.I) ^ (m + 1) * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x) := by
    intro x
    have hq : (((1 + x ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
    have hshift : (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(w - 1))
        = (((1 + x ^ 2 : ℝ) : ℂ)) * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) := by
      rw [show -(w - 1) = 1 + -w by ring, Complex.cpow_add _ _ hq, Complex.cpow_one]
    have hQ : (((1 + x ^ 2 : ℝ) : ℂ))
        = ((x : ℂ) + ε * Complex.I) ^ 2 - 2 * ε * Complex.I * ((x : ℂ) + ε * Complex.I) := by
      push_cast
      linear_combination (ε : ℂ) ^ 2 * Complex.I_sq - hε2
    rw [hshift]
    linear_combination
      (-(((x : ℂ) + ε * Complex.I) ^ m * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w) * charFn t x)) * hQ
  have h1 := integrable_termFamily ε hε m (w - 1) t (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have h2 := (integrable_termFamily ε hε (m + 1) w t (by push_cast; linarith)).const_mul
    (2 * ε * Complex.I)
  unfold realG
  simp_rw [hpt]
  rw [integral_add h1 h2, integral_const_mul]

private theorem termFamily_eq_realG (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (m : ℕ) (w : ℂ) (t : ℝ)
    (hw : ((m : ℝ) + 1) / 2 < w.re) : termFamily ε m w t = realG ε m w t := by
  have key : ∀ (n : ℕ) (w : ℂ), ((n : ℝ) + 1) / 2 < w.re →
      termFamily ε n w t = realG ε n w t ∧
        (((n : ℝ) + 2) / 2 < w.re → termFamily ε (n + 1) w t = realG ε (n + 1) w t) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      refine ⟨realG_zero ε w t (by norm_num at hw; linarith), fun hw' => ?_⟩
      exact realG_one ε w t (by norm_num at hw'; linarith)
    | succ n ih =>
      intro w hw
      push_cast at hw ih
      refine ⟨(ih w (by linarith)).2 (by linarith), fun hw' => ?_⟩
      push_cast at hw'
      show termFamily ε n (w - 1) t + 2 * ε * Complex.I * termFamily ε (n + 1) w t = realG ε (n + 2) w t
      have hw1 : ((n : ℝ) + 1) / 2 < (w - 1).re := by
        rw [Complex.sub_re, Complex.one_re]
        linarith
      rw [(ih (w - 1) hw1).1, (ih w (by linarith)).2 (by linarith),
        realG_rec ε hε n w t (by linarith)]
  exact (key m w hw).1

private theorem weight_eq (k : ℤ) (x : ℝ) :
    ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
      = (((x : ℝ) : ℂ) + (signWeight k : ℝ) * Complex.I) ^ k.natAbs
        * (((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ k.natAbs)⁻¹ := by
  have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hS : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq).ne'
  have hS2 : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ 2 = (x : ℂ) ^ 2 + 1 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq.le]
    push_cast
    ring
  have hxI : (x : ℂ) - Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  rcases le_or_gt 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have hsgn : signWeight (n : ℤ) = -1 := ite_eq_left hk
    rw [hsgn, Int.natAbs_natCast, zpow_natCast, div_pow, div_eq_mul_inv]
    push_cast
    ring
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -(n : ℤ) := ⟨k.natAbs, by omega⟩
    have hsgn : signWeight (-(n : ℤ)) = 1 := ite_eq_right (not_le.mpr hk)
    have hflip : ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) / ((x : ℂ) - Complex.I)
        = ((x : ℂ) + Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) := by
      rw [div_eq_div_iff hxI hS, ← sq, hS2]
      linear_combination Complex.I_sq
    rw [hsgn, Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast, ← inv_pow, inv_div, hflip,
      div_pow, div_eq_mul_inv]
    push_cast
    ring

private theorem realG_eq_head (k : ℤ) (w : ℂ) (t : ℝ) :
    realG (signWeight k) k.natAbs (w + (k.natAbs : ℂ) / 2) t
      = ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I)) := by
  unfold realG
  congr 1
  funext x
  have hq : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hQ : (((1 + x ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have hkey : (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-((k.natAbs : ℂ) / 2))
      = (((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ) ^ k.natAbs)⁻¹ := by
    rw [Complex.cpow_neg, show ((k.natAbs : ℂ) / 2) = (((1 / 2 : ℝ) * (k.natAbs : ℝ) : ℝ) : ℂ) by
        push_cast; ring,
      ← Complex.ofReal_cpow hq.le, Real.rpow_mul hq.le, ← Real.sqrt_eq_rpow, Real.rpow_natCast,
      Complex.ofReal_pow]
  have hchr : charFn t x = Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I)) := by
    unfold charFn
    congr 1
    push_cast
    ring
  rw [weight_eq k x, neg_add, Complex.cpow_add _ _ hQ, hkey, hchr]
  ring

theorem exists_realKType (k : ℤ) :
    ∃ J : ℂ → ℝ → ℂ,
      (∀ t : ℝ, t ≠ 0 → Differentiable ℂ (fun w : ℂ => J w t)) ∧
      (∀ (w : ℂ) (t : ℝ), 1 / 2 < w.re → t ≠ 0 →
        J w t = ∫ x : ℝ, ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))) ∧
      (∀ R : ℝ, ∃ C c' : ℝ, ∃ N : ℕ, 0 < C ∧ 0 < c' ∧ ∀ (w : ℂ) (t : ℝ), ‖w‖ ≤ R → t ≠ 0 →
        ‖J w t‖ ≤ C * max 1 (|t| ^ (-(N : ℝ))) * Real.exp (-c' * |t|)) := by
  have hπ : 0 < ((Real.pi : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact Real.pi_pos
  obtain ⟨κ, T, a, β, b, l, ha, hβ, hJ⟩ := isComb_realJ k
  refine ⟨realJ k, fun t ht => ?_, fun w t hw ht => ?_, fun R => ?_⟩
  · have hfun : (fun w : ℂ => realJ k w t) = fun w => ∑ i ∈ T, a i w * β i * (t : ℂ) ^ l i *
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w + b i) * Complex.exp (-(Real.pi : ℂ) * (u + t ^ 2 / u)) :=
      funext fun w => hJ w t ht
    rw [hfun]
    exact differentiable_sum_archIntegral T a ha β b l (Real.pi : ℂ) hπ t ht
  · have hre : (w + (k.natAbs : ℂ) / 2).re = w.re + (k.natAbs : ℝ) / 2 := by simp
    show termFamily (signWeight k) k.natAbs (w + (k.natAbs : ℂ) / 2) t = _
    rw [termFamily_eq_realG (signWeight k) (signWeight_cases k) k.natAbs _ t (by rw [hre]; linarith)]
    exact realG_eq_head k w t
  · obtain ⟨C, c', N, hC, hc', hB⟩ := exists_norm_sum_archIntegral_le T a ha b l (Real.pi : ℂ) hπ R
    refine ⟨C, c', N, hC, hc', fun w t hw ht => ?_⟩
    rw [hJ w t ht]
    exact hB β hβ w t hw ht

end EisensteinGeneral.Arch
