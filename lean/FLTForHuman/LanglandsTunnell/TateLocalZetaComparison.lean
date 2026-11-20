/-
  The archimedean zeta integrals agree with the local zeta functions.

  Tate's local zeta function is an integral against the *multiplicative* Haar measure
  `d^×x = |x|^{-1} d x`, while the pin's `ArchPlace.complexZeta`/`realZeta` are the same integrals
  written against the *additive* Lebesgue measure with the factor `|x|^{s-1}` resp. `|z|^{2s-2}`
  carrying the normalisation by hand. The two rows of this module say the two are the same
  function of `s`, for every measure `μ`, every `f` and every multiplicative character `χ` :

    `realZeta μ f χ s = localZeta μ f χ s`,      `complexZeta μ f χ s = localZeta μ f χ s`,

  where `localZeta μ f χ s = ∫ x, f x * charExt χ x * (modulus x : ℝ) ^ s ∂(mulMeasure μ)` is the
  port's `TateLocal.localZeta` and `mulMeasure μ = (modulus ·)⁻¹ · (μ|_{≠0})`. Nothing about the
  Fourier transform enters: this is the change of variables `d^× = |·|^{-1} d` together with the
  archimedean identity `modulus a = distribHaarChar K (a : Kˣ)`, and it is the dictionary every
  later computation of a local zeta integral (and hence of a local gamma factor) goes through.

  The proof is the pin's, in four layers, and the four layers are what the module's declaration
  list is:

  * the two Haar characters, computed from `distribHaarChar_eq_of_measure_smul_eq_mul` on the unit
    ball: `distribHaarChar ℝ x = ‖x‖` and `distribHaarChar ℂ z = ‖z‖²` (the exponent `2` is
    `[ℂ : ℝ]`, i.e. `Complex.finrank_real_complex`), and the resulting
    `modulus_real_eq_nnnorm`/`modulus_complex_eq_nnnorm_sq` after `modulus_of_ne_zero`;
  * `integral_mulMeasure`: an integral against `mulMeasure μ` is `∫ x in {0}ᶜ, (modulus x)⁻¹ • F x ∂μ`
    — `withDensity` plus `integral_withDensity_eq_integral_smul₀`, the `{0}ᶜ` restriction being
    where the two sides' behaviour at `0` is settled (`charExt χ 0 = 0` on both);
  * the pointwise computation `(modulus x)⁻¹ • (f x χ(x) |x|^{s-1}) = f x χ(x) |x|^{s}` on `{0}ᶜ`,
    a `cpow` identity: `(|x|²)^{-1} · (|x|²)^s = |x|^{2s-2}` on `ℂ`, `|x|^{-1} · |x|^s = |x|^{s-1}` on
    `ℝ`, via `Complex.cpow_add` at `‖x‖ ≠ 0`;
  * and the removal of the hypothesis: `modulus` is measurable (indeed `‖·‖₊` raised to a fixed
    power), so the `hm` hypothesis of the `_impl` bridge is free (`hm_*_any`), giving the
    unconditional `_unc` forms, which are the two rows.

  Transcribed from the two 166-line pins (pinned `aa2d8b3`) — identical to each other except in
  the name of their `solution` row and its last three lines, so the shared prelude is written
  once here, at the pins' own names, and each row is the corresponding `_unc` engine applied.

  spec-pin: P2M/Sol/S_LanglandsTunnell_TateLocal_realZeta_eq_localZeta.lean
  spec-pin: P2M/Sol/S_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta.lean

  ## Port deltas

  - Imports: the scaffold's `import Mathlib` is replaced by the pins' own three mathlib
    dependencies — `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar` (for
    `Measure.addHaar_closedBall_mul`) and `Mathlib.LinearAlgebra.Complex.FiniteDimensional` (for
    `Complex.finrank_real_complex`) — plus the two port modules the rows are stated with. With
    `import Mathlib` this module did not finish elaborating inside 115 s on this box (a 6.1 GB
    olean closure against 7 GB of RAM); with the narrow list the module elaborates in 5.8 s and
    its `lake build` takes 6 s.
  - Body of `integral_mulMeasure`: the pin's proof is the pin's, including its `withDensity`
    congruence; no name or transparency workaround was needed (the FR-0238/FR-0245/FR-0249 class
    of `def`-abbreviation failures does not reach this module — everything here is stated about
    `modulus`, which is a `def` that the pin's proofs only ever unfold by `modulus_of_ne_zero`).
  - Pin structure: the pins wrap the prelude in `namespace P7Rows.ArchBridge` and five `section`s
    (`ArchE1`, `BR`, `BridgeComplex`, `BridgeReal`, `HmDerived`) and put the row at the top level
    as `solution`. The port flattens that namespace into `LanglandsTunnell.TateLocal` (the
    module's own namespace, so every name is the pin's last name) and drops the section names;
    the row is declared at the pin's `solution` *statement* under the name the wire carries.
    The `variable {K} [Field K] …` block of the `BR` section is kept verbatim.
  - `distribHaarChar`, the duplication decision (FR: `port_advise` flagged it). The port already
    has, in `NumberTheory/NumberField/TateGlobal/ArchMulHaar.lean`,
    `NumberField.TateGlobal.ArchMulHaarReal.distribHaarChar_real (t : ℝˣ) :
    distribHaarChar ℝ t = ‖(t : ℝ)‖₊` and
    `NumberField.TateGlobal.ArchMulHaarComplex.distribHaarChar_complex (t : ℂˣ) :
    distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ 2` — the same two propositions under other names, proved
    there from other measure sets (`Icc 0 1` and `Metric.ball 0 1` rather than `closedBall 0 1`)
    and with the binder named `t`. **Kept the pins' local copies**, for two reasons: (i) the two
    local lemmas are *wire declarations* of this module's two pins (the module's surface is 13
    declarations and `check_port` reads 13 ok — deleting them to import the port's namesakes
    would drop two pin public declarations the audit counts and would rename what the pins state);
    (ii) the pins' proofs call `distribHaarChar_eq_of_measure_smul_eq_mul` directly with their own
    argument order and never call a `distribHaarChar_*_eq_nnnorm*` lemma, so no call site prefers
    the port's binder skeleton. The two copies are therefore the same proposition proved twice,
    in two different modules. They cannot silently diverge: this module's copies are the only
    facts the two rows use about `distribHaarChar`, and the statements are `=` to `‖·‖₊` and
    `‖·‖₊ ^ 2` on the nose — if `ArchMulHaar`'s pair ever changes statement, this pair and the
    four `modulus_*`/`hm_*` decls resting on it are wrong together, and `check_port`'s statement
    hash for this module is the tripwire.
  - The two `_impl`/`_unc` levels and `hm_*_any` are the pins', kept as declarations (not
    inlined into the rows): they are the pin's public surface, and `_impl` is the form a caller
    with its own measurability proof wants.

  ## Deferred pin surface

  None. The two pins each declare the same eleven prelude declarations plus their `solution`;
  the port declares the prelude once (eleven) and the two rows, 13 declarations.
  `scaffold_audit` reads **complete** with both `solution`s FOLDED into their rows (their
  statements *are* the rows'), `move_dead.py` reads 0 declarations / 0 lines, and the only
  `dedup` clusters are the pins' own two `_unc`/row pairs, recorded below.

  ## Gates

  - `check_port --force` — 13 ok, 0 mismatch, 0 missing, 0 own, 0 kw (both pins wired, tier 2).
  - `scaffold_audit` — **complete**: 24 pin public declarations on the wire (the shared prelude
    counted once per pin), 13 declared here, 0 satisfied from the import closure; the two
    `solution`s read FOLDED.
  - `lake env lean -DautoImplicit=false` — no output at all (project cap
    `maxHeartbeats = 4000000`, 5.8 s warm); `flock … lake build
    FLTForHuman.LanglandsTunnell.TateLocalZetaComparison` — built on the final source, 6 s
    (2 656 jobs, `ArchPlace` and all mathlib dependencies already up to date).
  - `#print axioms` on all thirteen declarations — `[propext, Classical.choice, Quot.sound]` on
    every one, both rows included (probe `lean/tmp/af96/axioms_probe.lean`); no `sorryAx`.
  - `dedup --within` — 2 clusters, both the pins' own pairs and kept for the pins' reason:
    `realZeta_eq_localZeta_unc`/`realZeta_eq_localZeta` and
    `complexZeta_eq_localZeta_unc`/`complexZeta_eq_localZeta` have the same statement by
    construction (a row is its `_unc` engine applied to nothing), 8 removable lines that the
    wire requires: dropping either `_unc` would drop a pin public declaration. The pins carry the
    identical pair, so this is the pin's own duplication, not the port's.
    `move_dead --dry-run` — 0 declarations, 0 lines.
  - Heartbeat probe (stated, never installed — FR-0225): silent at `maxHeartbeats = 1000`, fails
    at `500` (a `whnf` timeout inside `distribHaarChar_complex_eq_nnnorm_sq`), so the pair to quote
    is 1 000 / 500. The full ladder measured, for the record: silent at 20000, 8000, 4000, 1000;
    fails at 2000 (`simp` timeout, line of the same declaration) and at 500. The 2000 reading is
    *not* monotone in the 1000 one — worth knowing for FR-0225's "silent at N, fails at N/2"
    convention: a `simp`-heavy declaration can fail at a cap twice the one it succeeds at, so a
    single failing probe above a silent one is not a contradiction, and the quoted pair here is
    the tight one.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import FLTForHuman.LanglandsTunnell.TateLocal.ArchPlace
import FLTForHuman.LanglandsTunnell.TateLocalZeta

set_option autoImplicit false

noncomputable section

open MeasureTheory LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace Metric
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell.TateLocal


theorem distribHaarChar_complex_eq_nnnorm_sq (z : ℂˣ) :
    distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := closedBall (0:ℂ) 1) (μ := volume)
    (measure_closedBall_pos volume (0:ℂ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' z.ne_zero, smul_zero, mul_one,
    show ‖(z:ℂ)‖ = ‖(z:ℂ)‖ * 1 from (mul_one _).symm,
    Measure.addHaar_closedBall_mul volume (0:ℂ) (norm_nonneg _) zero_le_one,
    Complex.finrank_real_complex]
  simp [ENNReal.ofReal_pow (norm_nonneg _), enorm_eq_nnnorm]

theorem modulus_complex_eq_nnnorm_sq : ∀ (z : ℂ), modulus z = ‖z‖₊ ^ 2 := by
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [modulus_of_ne_zero hz, distribHaarChar_complex_eq_nnnorm_sq]
    simp

theorem distribHaarChar_real_eq_nnnorm (x : ℝˣ) :
    distribHaarChar ℝ x = ‖(x : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := closedBall (0:ℝ) 1) (μ := volume)
    (measure_closedBall_pos volume (0:ℝ) one_pos).ne'
    measure_closedBall_lt_top.ne ?_
  rw [Units.smul_def, smul_closedBall' x.ne_zero, smul_zero, mul_one,
    show ‖(x:ℝ)‖ = ‖(x:ℝ)‖ * 1 from (mul_one _).symm,
    Measure.addHaar_closedBall_mul volume (0:ℝ) (norm_nonneg _) zero_le_one,
    Module.finrank_self, pow_one]
  simp only [ofReal_norm, enorm_eq_nnnorm]

theorem modulus_real_eq_nnnorm : ∀ (x : ℝ), modulus x = ‖x‖₊ := by
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [modulus_of_ne_zero hx, distribHaarChar_real_eq_nnnorm]
    simp

section
variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

theorem integral_mulMeasure (μ : Measure K) (F : K → ℂ)
    (hm : AEMeasurable (fun x : K => (modulus x)⁻¹) (μ.restrict {0}ᶜ)) :
    ∫ x, F x ∂(mulMeasure μ) = ∫ x in ({0}ᶜ : Set K), ((modulus x)⁻¹ : ℝ≥0) • F x ∂μ := by
  have hae : (fun x : K => ((modulus x : ℝ≥0∞))⁻¹)
      =ᵐ[μ.restrict {0}ᶜ] fun x : K => (((modulus x)⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    refine (MeasureTheory.ae_restrict_iff' (MeasurableSet.singleton (0 : K)).compl).mpr ?_
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : x ≠ 0 := by simpa using hx
    show ((modulus x : ℝ≥0∞))⁻¹ = (((modulus x)⁻¹ : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_inv (modulus_ne_zero hx0)]
  rw [mulMeasure, MeasureTheory.withDensity_congr_ae hae,
    integral_withDensity_eq_integral_smul₀ hm]

end

theorem complexZeta_eq_localZeta_impl (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ)
    (hm : AEMeasurable (fun z : ℂ => (modulus z)⁻¹) (μ.restrict {0}ᶜ)) :
    complexZeta μ f χ s = localZeta μ f χ s := by
  rw [localZeta, integral_mulMeasure μ _ hm, complexZeta]
  rw [← MeasureTheory.integral_indicator (MeasurableSet.singleton (0:ℂ)).compl]
  congr 1
  funext z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [Set.indicator_of_mem (show z ∈ ({0}ᶜ : Set ℂ) by simpa using hz)]
    have hmz : modulus z = ‖z‖₊ ^ 2 := modulus_complex_eq_nnnorm_sq z
    have hnz : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    simp only [NNReal.smul_def, Complex.real_smul, hmz]
    rw [show (f z * charExt χ z * (‖z‖ : ℂ) ^ (2 * s - 2) : ℂ)
          = (f z * charExt χ z) * ((‖z‖ : ℂ) ^ (2 * s - 2)) from by ring,
       show ((((‖z‖₊ ^ 2)⁻¹ : ℝ≥0) : ℝ) : ℂ) * (f z * charExt χ z * ((((‖z‖₊^2 : ℝ≥0) : ℝ) : ℂ)) ^ s)
          = (f z * charExt χ z) * (((((‖z‖₊^2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) : ℂ)
              * ((((‖z‖₊^2 : ℝ≥0) : ℝ) : ℂ)) ^ s) from by ring]
    congr 1
    have hsq : ((((‖z‖₊^2 : ℝ≥0) : ℝ) : ℂ)) = ((‖z‖ * ‖z‖ : ℝ) : ℂ) := by
      push_cast; ring
    have h1 : ((((‖z‖₊^2 : ℝ≥0) : ℝ) : ℂ))^s = (‖z‖ : ℂ)^((2:ℂ)*s) := by
      rw [hsq, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
        ← Complex.cpow_add _ _ hnz]; ring_nf
    have h2 : ((((‖z‖₊^2 : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) : ℂ) = (‖z‖ : ℂ)^(-(2:ℂ)) := by
      rw [show (-(2:ℂ)) = (-1) + (-1) from by ring, Complex.cpow_add _ _ hnz,
        Complex.cpow_neg_one]
      push_cast; ring
    rw [h1, h2, ← Complex.cpow_add _ _ hnz]
    ring_nf

theorem realZeta_eq_localZeta_impl (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ)
    (hm : AEMeasurable (fun x : ℝ => (modulus x)⁻¹) (μ.restrict {0}ᶜ)) :
    realZeta μ f χ s = localZeta μ f χ s := by
  rw [localZeta, integral_mulMeasure μ _ hm, realZeta]
  rw [← MeasureTheory.integral_indicator (MeasurableSet.singleton (0:ℝ)).compl]
  congr 1
  funext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Set.indicator_of_mem (show x ∈ ({0}ᶜ : Set ℝ) by simpa using hx)]
    have hmx : modulus x = ‖x‖₊ := modulus_real_eq_nnnorm x
    have hnz : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
    simp only [NNReal.smul_def, Complex.real_smul, hmx]
    rw [show (f x * charExt χ x * (‖x‖ : ℂ) ^ (s - 1) : ℂ)
          = (f x * charExt χ x) * ((‖x‖ : ℂ) ^ (s - 1)) from by ring,
       show ((((‖x‖₊)⁻¹ : ℝ≥0) : ℝ) : ℂ) * (f x * charExt χ x * (((‖x‖₊ : ℝ) : ℂ)) ^ s)
          = (f x * charExt χ x) * ((((‖x‖₊⁻¹ : ℝ≥0) : ℝ) : ℂ) * (((‖x‖₊ : ℝ) : ℂ)) ^ s) from by ring]
    congr 1
    have h2 : ((((‖x‖₊)⁻¹ : ℝ≥0) : ℝ) : ℂ) = (‖x‖ : ℂ)^(-(1:ℂ)) := by
      push_cast; rw [Complex.cpow_neg, Complex.cpow_one]
    rw [h2, show (((‖x‖₊ : ℝ) : ℂ)) = (‖x‖ : ℂ) from by push_cast; ring,
      ← Complex.cpow_add _ _ hnz]
    ring_nf

theorem hm_complex_any (μ : Measure ℂ) :
    AEMeasurable (fun z : ℂ => (modulus z)⁻¹) (μ.restrict {0}ᶜ) := by
  have heq : (fun z : ℂ => (modulus z)⁻¹) = fun z => (‖z‖₊ ^ 2)⁻¹ :=
    funext fun z => by rw [modulus_complex_eq_nnnorm_sq]
  rw [heq]
  exact ((measurable_nnnorm.pow_const 2).inv).aemeasurable

theorem hm_real_any (μ : Measure ℝ) :
    AEMeasurable (fun x : ℝ => (modulus x)⁻¹) (μ.restrict {0}ᶜ) := by
  have heq : (fun x : ℝ => (modulus x)⁻¹) = fun x => (‖x‖₊)⁻¹ :=
    funext fun x => by rw [modulus_real_eq_nnnorm]
  rw [heq]
  exact (measurable_nnnorm.inv).aemeasurable

theorem complexZeta_eq_localZeta_unc (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) :
    complexZeta μ f χ s = localZeta μ f χ s :=
  complexZeta_eq_localZeta_impl μ f χ s (hm_complex_any μ)

theorem realZeta_eq_localZeta_unc (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) :
    realZeta μ f χ s = localZeta μ f χ s :=
  realZeta_eq_localZeta_impl μ f χ s (hm_real_any μ)

theorem realZeta_eq_localZeta (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) :
    realZeta μ f χ s = localZeta μ f χ s :=
  realZeta_eq_localZeta_unc μ f χ s

theorem complexZeta_eq_localZeta (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) :
    complexZeta μ f χ s = localZeta μ f χ s :=
  complexZeta_eq_localZeta_unc μ f χ s

end LanglandsTunnell.TateLocal

end
