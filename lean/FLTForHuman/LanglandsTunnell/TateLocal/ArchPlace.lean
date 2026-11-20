/-
  The archimedean local data: the additive characters, the characters of `ℂˣ`/`ℝˣ`,
  the test functions, and the real/complex zeta integrals.

  Tate's local theory at the archimedean place of `ℚ` runs on the two local fields `ℝ` and `ℂ`,
  and the local functional equation is stated with four pieces of vocabulary per field: an
  additive character, a multiplicative (quasi-)character, a test function with a Gaussian decay,
  and the zeta integral. This module is that vocabulary for the pair `(ℝ, ℂ)`, transcribed whole
  from the pin; it proves nothing about the integrals, so every declaration here is either a
  definition or the one-line lemma that a definition is *used* through. It is the definition gate
  of `LanglandsTunnell/TateLocalZetaComparison.lean`, whose two rows compare the integrals below
  with `TateLocal.localZeta`.

  * `psiComplex z = exp (-(2 * π * I * (z + starRingEnd ℂ z)))` and
    `psiReal x = exp (-(2 * π * I * x))`: the additive characters of `ℂ` and of `ℝ`, in the pin's
    sign convention. On `ℂ` the argument `z + z̄ = 2 Re z` is real, so the character is trivial on
    the imaginary direction and is really a character of `Re z ∈ ℝ` — the trace of the quadratic
    extension. `psiComplex_apply`/`psiReal_apply` are the defining equation (`rfl`), and
    `psiComplex_mul_eq` says `psiComplex` is trivial on the products of the diagonal `ℂ → ℂ`,
    which is the form the Fourier transform's covariance is used in.
  * `anglePhase z = z / ‖z‖`: the circle coordinate of `z ∈ ℂˣ`, i.e. the `U(1)` component of the
    polar decomposition `ℂˣ ≃ ℝ_{>0} × U(1)`. `norm_anglePhase` (unit modulus),
    `anglePhase_ne_zero` and `anglePhase_mul` (it is a monoid homomorphism) are what makes
    `anglePhase z ^ k` a well-defined character for `k ∈ ℤ`.
  * `complexCharFun u k z = ‖z‖ ^ (2 * u) * anglePhase z ^ k` and
    `realCharFun u a x = ‖x‖ ^ u * realSign x ^ a`: the continuous quasi-characters of `ℂˣ`
    (exponent `u ∈ ℂ`, weight `k ∈ ℤ`) and of `ℝˣ` (exponent `u ∈ ℂ`, parity `a ∈ ZMod 2`), with
    `realSign x = x / ‖x‖ : ℂˣ` the sign character (`realSign_mul`). These are the characters the
    local zeta functions are evaluated at; `complexCharFun_apply` is the coercion to `ℂ`.
  * `complexTestFun k z = z̄ ^ k⁺ * z ^ k⁻ * exp (-(2 * π * ‖z‖ ^ 2))` and
    `realTestFun a x = x ^ a * exp (-(π * x ^ 2))`: the pin's test functions — a monomial times
    the standard Gaussian, so that `k` (resp. `a`) picks the `L²`-weight on which the Fourier
    transform acts by a scalar. The three `complexTestFun_zero_*`/`realTestFun_zero_*` lemmas
    record the `k = 0`/`a = 0` case: the Gaussian itself, its value `1` at the origin, and the
    fact that it is not the zero function.
  * `complexZeta μ f χ s = ∫ z, f z * charExt χ z * ‖z‖ ^ (2 * s - 2) ∂μ` and
    `realZeta μ f χ s = ∫ x, f x * charExt χ x * ‖x‖ ^ (s - 1) ∂μ`: Tate's local zeta integrals,
    integrated against the *additive* measure `μ` (Lebesgue, in the application) with the factor
    `‖z‖ ^ (2 * s - 2)` resp. `‖x‖ ^ (s - 1)` carrying the normalisation `d^× = ‖·‖^{-1} d` and
    the degree `[ℂ : ℝ] = 2`.
  * `complexGammaAt μ ψ f₀ χ s = complexZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) /
    complexZeta μ f₀ χ s` and `realGammaAt` likewise: the local gamma factor as the ratio of the
    zeta integral of the Fourier transform at `χ⁻¹, 1 - s` to the zeta integral at `χ, s`.

  spec-pin: Definitions/Def_LanglandsTunnell_ArchPlace.lean

  ## Port deltas

  - Imports: the pin's single import `Definitions.Def_LanglandsTunnell_TateLocalZeta` is the
    port's `FLTForHuman.LanglandsTunnell.TateLocalZeta`, and the scaffold's `import Mathlib` is
    dropped: the whole pin is proved from that one dependency (which itself imports only
    `Mathlib.MeasureTheory.Measure.Haar.DistribChar` and
    `Mathlib.Topology.LocallyConstant.Basic`), so the narrow list is the pin's own. It is also
    what keeps the module inside the gates' time budget: a bare `import Mathlib` on this box
    loads a 6.1 GB olean closure against 7 GB of RAM and one elaboration did not finish in
    115 s, while with the narrow closure the module elaborates in 2.5 s on a warm cache (36 s
    cold) and its `lake build` takes 24 s cold / 5.7 s on a warm one. Same substitution as the
    port's other definition-layer modules (cf. `RepTheory/LocalLanglands/IntegralSubgroup.lean`).
  - Bodies: the scaffold carried `sorry` in all fourteen theorem bodies — `psiComplex_apply`,
    `norm_anglePhase`, `anglePhase_ne_zero`, `anglePhase_mul`, `complexCharFun_apply`,
    `complexTestFun_zero_apply`/`_at_zero`/`_ne_zero`, `psiComplex_mul_eq`, `psiReal_apply`,
    `realSign_mul`, `realTestFun_zero_apply`/`_at_zero`/`_ne_zero` — and every one now carries
    the pin's own body (`rfl` where the pin writes `rfl`, `simp [def]` where it writes that,
    `intro h; have := congrFun h 0; simp at this` for the two `_ne_zero` rows). No statement,
    name, visibility, `def` body, binder or section changed: the two `AddChar` structures,
    `anglePhase`, `complexCharFun`, `realCharFun`, `realSign`, `complexTestFun`, `realTestFun`,
    the zeta integrals and the gamma factors are byte-identical to the pin.
  - One consequence worth naming: `psiComplex_apply`, `psiReal_apply` and `complexCharFun_apply`
    are `rfl` *because* the `def`s are the pin's — they are the statements the two rows of
    `TateLocalZetaComparison.lean` unfold through (`psiComplex_apply` at the Fourier transform,
    `complexCharFun_apply`/`realSign` at the characters), so a `sorry`-bodied `def` here would
    have changed what those rows mean (FR-0232).

  ## Deferred pin surface

  None. The pin is 120 lines / 26 declarations and the module declares exactly those
  twenty-six, at the pin's names, statements and bodies; `move_dead.py` reads 0 declarations /
  0 lines and `dedup.py --within` reads 0 clusters.

  ## Gates

  - `check_port --force` — 26 ok, 0 mismatch, 0 missing, 0 own, 0 kw.
  - `scaffold_audit` — **complete**: 26 pin public declarations on the wire, 26 declared here,
    0 satisfied from the import closure (nothing credited to a namesake, FR-0237).
  - `lake env lean -DautoImplicit=false` — no output at all (project cap
    `maxHeartbeats = 4000000`, 2.5 s warm); `flock … lake build
    FLTForHuman.LanglandsTunnell.TateLocal.ArchPlace` — built on the final source, 5.7 s
    (2 648 jobs, all dependencies up to date).
  - `#print axioms` on all twenty-six declarations — `[propext, Classical.choice, Quot.sound]`
    on every one (probe `lean/tmp/af96/axioms_probe_arch.lean`, 26 lines out, nothing filtered);
    no `sorryAx`.
  - `dedup --within` — 0 clusters. `move_dead --dry-run` — 0 declarations, 0 lines.
  - Heartbeat probe (stated, never installed — FR-0225): silent at `maxHeartbeats = 1000`, fails
    at `500` (a nested `isDefEq` timeout inside `simp` at `complexCharFun`'s `map_one'`). The
    natural cost of the module is therefore ~600 heartbeats; the project cap is 4 000 000.
-/

import FLTForHuman.LanglandsTunnell.TateLocalZeta

set_option autoImplicit false

noncomputable section

open Complex Real MeasureTheory LanglandsTunnell.TateLocal

namespace LanglandsTunnell.ArchPlace


def psiComplex : AddChar ℂ ℂ where
  toFun z := Complex.exp (-(2 * π * Complex.I * (z + starRingEnd ℂ z)))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [← Complex.exp_add, map_add]; ring_nf

theorem psiComplex_apply (z : ℂ) :
    psiComplex z = Complex.exp (-(2 * π * Complex.I * (z + starRingEnd ℂ z))) := rfl

def anglePhase (z : ℂˣ) : ℂ := (z : ℂ) / (‖(z : ℂ)‖ : ℂ)

@[simp] theorem norm_anglePhase (z : ℂˣ) : ‖anglePhase z‖ = 1 := by
  rw [anglePhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr z.ne_zero)]

theorem anglePhase_ne_zero (z : ℂˣ) : anglePhase z ≠ 0 := fun h => by
  have := norm_anglePhase z; rw [h, norm_zero] at this; exact one_ne_zero this.symm

theorem anglePhase_mul (z w : ℂˣ) : anglePhase (z * w) = anglePhase z * anglePhase w := by
  simp only [anglePhase, Units.val_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv]
  ring

def complexCharFun (u : ℂ) (k : ℤ) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 (((‖(z : ℂ)‖ : ℂ) ^ (2 * u)) * anglePhase z ^ k)
    (mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero))))
      (zpow_ne_zero _ (anglePhase_ne_zero z)))
  map_one' := by ext; simp [anglePhase]
  map_mul' z w := by
    ext
    simp only [Units.val_mul, Units.val_mk0]
    push_cast [norm_mul, anglePhase_mul, mul_zpow]
    rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
    ring

theorem complexCharFun_apply (u : ℂ) (k : ℤ) (z : ℂˣ) :
    ((complexCharFun u k z : ℂˣ) : ℂ) = (‖(z : ℂ)‖ : ℂ) ^ (2 * u) * anglePhase z ^ k := rfl

def complexTestFun (k : ℤ) : ℂ → ℂ :=
  fun z => (starRingEnd ℂ z) ^ k.toNat * z ^ (-k).toNat * Complex.exp (-(2 * π * ‖z‖ ^ 2))

@[simp] theorem complexTestFun_zero_apply (z : ℂ) :
    complexTestFun 0 z = Complex.exp (-(2 * π * ‖z‖ ^ 2)) := by
  simp [complexTestFun]

theorem complexTestFun_zero_at_zero : complexTestFun 0 0 = 1 := by simp

theorem complexTestFun_zero_ne_zero : complexTestFun 0 ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

def complexZeta (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ z, f z * charExt χ z * ((‖z‖ : ℂ) ^ ((2 : ℂ) * s - 2)) ∂μ

def complexGammaAt (μ : Measure ℂ) (ψ : AddChar ℂ ℂ) (f₀ : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) : ℂ :=
  complexZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / complexZeta μ f₀ χ s

theorem psiComplex_mul_eq (z w : ℂ) :
    psiComplex (z * w)
      = Complex.exp (-(2 * π * Complex.I * (z * w + starRingEnd ℂ z * starRingEnd ℂ w))) := by
  rw [psiComplex_apply, map_mul]

def psiReal : AddChar ℝ ℂ where
  toFun x := Complex.exp (-(2 * π * Complex.I * x))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by push_cast; rw [← Complex.exp_add]; ring_nf

theorem psiReal_apply (x : ℝ) : psiReal x = Complex.exp (-(2 * π * Complex.I * x)) := rfl

def realSign (x : ℝˣ) : ℂˣ :=
  Units.mk0 ((x : ℝ) / (‖(x : ℝ)‖ : ℝ) : ℂ) (by
    have hx : (x : ℝ) ≠ 0 := x.ne_zero
    simp only [ne_eq, Complex.ofReal_eq_zero, div_eq_zero_iff, hx, norm_eq_zero, or_self,
      not_false_eq_true])

theorem realSign_mul (x y : ℝˣ) : realSign (x * y) = realSign x * realSign y := by
  ext
  simp only [realSign, Units.val_mk0, Units.val_mul, norm_mul]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring

def realCharFun (u : ℂ) (a : ZMod 2) : ℝˣ →* ℂˣ where
  toFun x := Units.mk0 ((‖(x : ℝ)‖ : ℂ) ^ u)
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))))
    * realSign x ^ (a.val : ℕ)
  map_one' := by ext; simp [realSign]
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, Units.val_pow_eq_pow_val, realSign_mul, mul_pow]
    push_cast [norm_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
    ring

def realTestFun (a : ZMod 2) : ℝ → ℂ :=
  fun x => ((x : ℂ) ^ (a.val : ℕ)) * Complex.exp (-(π * x ^ 2))

@[simp] theorem realTestFun_zero_apply (x : ℝ) :
    realTestFun 0 x = Complex.exp (-(π * x ^ 2)) := by simp [realTestFun]

theorem realTestFun_zero_at_zero : realTestFun 0 0 = 1 := by simp

theorem realTestFun_zero_ne_zero : realTestFun 0 ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

def realZeta (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * ((‖x‖ : ℂ) ^ (s - 1)) ∂μ

def realGammaAt (μ : Measure ℝ) (ψ : AddChar ℝ ℂ) (f₀ : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) : ℂ :=
  realZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / realZeta μ f₀ χ s

end LanglandsTunnell.ArchPlace

end
