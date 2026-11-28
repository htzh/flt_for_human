/-
The entire partial Euler product is the Whittaker coefficient, with a locally bounded majorant.

`EisensteinGeneral.Piece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant`
(2,468 pin `S_` lines, 104 pin declarations, 17 premises — the shelf's largest row by a factor of three):
for a global additive character `ψ` with local factors `ψv` of exponent `nψ`, Hecke character `χ`, a
finite place set `S`, a uniformiser family `ϖ`, an induced-section family `Ψ` and a factorization datum
`D`, the Whittaker coefficient of `Ψ s + ∑' ξ', Ψ s (w · n(ξ') · g)` at `ξ` equals the *entire* partial
Euler product `∏'_{v ∉ S} (1 - χ_v(ϖ_v) · |N v|^{-(2s+1)})` times a function `Q ξ` which is entire in
`s` and whose growth in `s` is locally bounded by a summable majorant `M` on `{ξ : F // ξ ≠ 0}`.

The proof is the adelic unfolding computation, in four layers that the pin's 104 declarations follow:

* **archimedean** — the Möbius-weight integrals `∫ ‖z‖^n (1 + ‖z‖²)^(-σ)`, their differentiability and
  their majorants (`ch_*`, `integrable_*WeightIntegrand`), the differentiability and the norm bounds of
  the Hecke-coefficient factors `pc_geom`/`pc_ram`, the two ideal lemmas
  `exists_fractionalIdeal_ne_zero_mem_of_forall_valued_le` /
  `exists_pos_finprod_absNorm_pow_toNat_neg_le_mul_abs_norm` (`EisensteinGeneral.WeylGlue`), and the
  integrability in the archimedean and mixed variables;
* **finite places** — the local/finite Borel structures `pc_locBorel`, `pc_finBorel` and their Haar
  measures, the depth calculus `pc_exp` … `pc_integrableOn_integers_of_depth_const`, the on/off-`S`
  corrections `pc_corrOff`/`pc_corrOn`/`pc_corr`, the Euler product `pc_euler` and the local excess
  bound `pc_excess_bounds_local`;
* **the adeles** — the tensor/finite-product integrability `pc_tensor`, `pc_integrable_finprod`,
  `pc_term_integrable`, `pc_fourierIntegral_eq_integral_mul`, `pc_fin_fourier_eq`, the value
  computation `pc_term_value`, `pc_arch_value`, `pc_unit_*`, and the Euler-product gluing
  `pc_multipliable_euler`/`pc_hoff_one`;
* **the assembly** — `pc_norm_corrOff_le`, `pc_exists_norm_corrOn_le`, the shell estimates
  (`pc_measurableSet_shell` … `pc_norm_shell_le`), `pc_prod_corr_eq_zero`, `pc_finite_value` and
  `pc_finite_half`, then the headline.

Its home is new: no existing module is above all seventeen premise modules (the piece layer, the
factorization layer, the unfolding lemma and the archimedean bounds), and the subject — the product over
the places outside `S` — is the composition the previous sets left without a home.

## The rows

* `EisensteinGeneral.Piece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant` — 2,468 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_EisensteinGeneral_Piece_exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_EisensteinGeneral_Piece_exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant.lean>

## Surface (order AF109A)

**90 declarations: 1 public + 89 `private`.** The pin's file is one public row over a 103-declaration
`private` engine, and the engine is transcribed at the pin's own names, `private` as in the pin; its
`EgenGlue`/`EgenPiece` label namespaces become the subject namespaces `EisensteinGeneral.WeylGlue` /
`EisensteinGeneral.Piece`. No statement is rewritten: the checker's statement diff is **90/90 `ok`**
when the `private` is dropped (see "Surface promotion measurement").

## Engine diff and substitutions (measured)

Pin-vs-module declaration diff (by statement hash, over `spec/statement_db`): pin rows **104**, module
declarations **90**; **87 rows by name and hash, 0 by name with a different hash, 17 not declared here,
3 declarations outside the pin's row list** (the two renames below and the headline, which is the pin's
`solution` row restated at the wrapper's name).

| pin row | line | status |
|---|---|---|
| `ch_norm_realWeightIntegrand` … `integrable_mixedSpace_prod` (6 rows) | 55–179 | **promoted** — public in `EisensteinGeneral/PieceWeylIntegrability.lean` (`EisensteinGeneral.WeylGlue`), statement-hash-identical |
| `pc_integrable_realWeight`, `pc_integrable_complexWeight`, `pc_integrable_comp_smul`, `pc_integrable_arch`, `pc_integrable_affine` (5 rows) | 1003–1068 | **promoted** — public there (`EisensteinGeneral.Piece`), statement-hash-identical |
| `pc_isCompact_integers` | 469 | **promoted**, statement-identical modulo binder spelling: the pin writes `(F : Type) [Field F] [NumberField F]` explicitly, the promoted copy has `F` implicit. Call sites drop the `F` (FR-0321) |
| `ch_norm_pow_le` | 121 | substituted: `AutomorphicForm.LocalIntertwining.ComplexAtomLimit.norm_pow_le` (`AutomorphicForm/Adelic/ArchAtomValues.lean:502`) |
| `pc_isOpen_integers` | 473 | substituted: `EisensteinGeneral.FiniteAdelicFactorization.isOpen_adicCompletionIntegers` (`EisensteinGeneral/Factorization/Stratum.lean:72`) |
| `solution` | 2229 | the headline, at the wrapper's name |

### Two rows renamed — the pin's own cross-file name reuse

**This is the one item the manager must rule on.** Three of the fourteen rows the order lists as
"already promoted" are *not* this pin's rows. The promotion was made against the sibling file
`P2M/Sol/S_EisensteinGeneral_Piece_integrable_weyl_unipotent_mul_of_factorization.lean`, and the two
files reuse three generic helper names for *different* lemmas:

| name | this pin (`S_…_Piece_exists_entire_…`) | the sibling pin (`S_…_Piece_integrable_weyl_…`) |
|---|---|---|
| `pc_isCompact_integers` | `:469`, explicit `(F : Type) [Field F] [NumberField F]` | `:285`, `F` implicit — **same lemma**, so the promoted copy is used |
| `pc_norm_mul_cpow_lt_one` | `:663`, `{χϖ : ℂ} (hχ) {N : ℕ} (hN : 1 < N) {s} (hs) : ‖χϖ * (N : ℂ) ^ (-(2s))‖ < 1` | `:195`, `(v : HeightOneSpectrum) (c) (hc) (s) (hs)` over `Ideal.absNorm v.asIdeal` — **different lemma** |
| `pc_excess_bounds` | `:775`, the analytic bound `0 ≤ (μ.real 𝒪)⁻¹ * ∫ ‖…‖ ∂μ - 1 ∧ … ≤ 2 * |N v| ^ (-(2·s.re))` | `:206`, the arithmetic `0 ≤ M⁻¹ * I - 1 ∧ … ≤ 2 * q ^ (-t)` — **different lemma** |

In the pin these are `private` in two different modules, so the reuse is invisible. In a single-module
port it is a hard collision: Lean rejects a `private` declaration whose full name is already taken by an
imported public one (`a non-private declaration … has already been declared`), and FR-0274 forbids the
public route. The two lemmas genuinely differ from the promoted ones, so they are transcribed here at
`private` names qualified by subject:

* `pc_norm_mul_cpow_lt_one` (`:663`) → `pc_norm_mul_cpow_lt_one_nat` (the `ℕ`-form; 3 call sites),
* `pc_excess_bounds` (`:775`) → `pc_excess_bounds_local` (the place-local bound; 2 call sites).

Both read `ok` under the checker's content-hash tier (measured: 90/90 `ok` in the surface run), i.e. the
statements are the pin's even though the last names differ. The alternative the manager may prefer is
renaming the *promoted* copies; that is an edit to `PieceWeylIntegrability.lean`, which this order does
not own.

## Local departures from the pin's text (all forced by v4.34/the port, none semantic)

* the pin's `attribute [-instance]` / `attribute [-simp]` walls (`:42-43`) are **dropped**: they name the
  pin's own re-declarations of instances and simp lemmas that the port carries once under its own names
  (the same call `EisensteinGeneral/PieceFactorizationDatum.lean` recorded). The pin's
  `attribute [local instance] NumberField.AdelicHaar.adeleBorel / borelSpace_adeleBorel` (`:51`, `:307`,
  `:2223`) **is** carried — the same spelling the port's `PieceWeylIntegrability.lean` uses.
* `Finset.prod_le_prod` (`:2094`, `:2108` in the port): mathlib v4.34 replaced the
  `(h0 : ∀ i ∈ s, 0 ≤ f i) (h : …)` form by `[MulLeftMono N]`, which no ordered field satisfies, and
  moved the `0 ≤` form to `Finset.prod_le_prod₀` (`GroupWithZero`); the two call sites use it, one for
  one, with the pin's own arguments in the pin's own order.
* `rw [AddChar.compAddMonoidHom_apply]` (pin `:931`, `:1001`) is dropped at two sites: the lemma is a
  `rfl`-unfolding of the `AddChar.compAddMonoidHom` `def`, and under this port's `AdeleRing`-defeq
  spelling the `rw` runs into an `implicit`-transparency type mismatch; the `show` that the pin writes
  on the next line does the same job at `default` transparency.
* the premise's port name: `NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar` →
  `AutomorphicForm.norm_apply_eq_one_of_isGlobalAddChar` (the port's landing of that pin row).
* `Piece.integrable_weyl_unipotent_mul_of_factorization`: the port's row is declared with the pin's
  full dotted name (`EisensteinGeneral.Piece.…`, at the file's root), so the pin's `Piece.` prefix
  resolves as written (SET-AF113 aligned the declaration with its own module header).
* deprecated names updated, one for one: `Set.mem_setOf_eq ↦ Set.mem_ofPred_eq` (12),
  `if_pos ↦ ite_eq_left` (3), `if_neg ↦ ite_eq_right` (6).
* `haveI`/`letI` → `have`/`let` (43 sites): FR-0323 — a local hypothesis of class type is already an
  instance, so the `I`-flavoured binder is redundant and `linter.style.haveILetI` fires on every one of
  them. **No linter is silenced anywhere in this module**, module-wide or declaration-scoped.
* the pin's `open scoped Classical in` on `integrable_mixedSpace_prod` (`:177`) goes with the promoted
  row; the file-scope `open scoped Classical` covers the rest.

## Gates (order AF109A)

* `spec/check_port.py --force` — **`1 ok, 0 mismatch, 0 missing, 0 own, 0 kw`** (the 89 helpers are
  `private`, which the checker skips; the headline is the checked row).
* **Surface promotion measurement** (for the manager): with `private` dropped from all 89 helpers the
  checker reads **90 ok, 0 mismatch, 0 missing, 0 own, 0 kw** — every transcribed row is at a pin
  statement, so promotion is safe on statement grounds. It is left `private` because the pin says
  `private`.
* edit loop (`-DautoImplicit=false -DmaxHeartbeats=200000`) — **silent** (0 lines, 17.7 s).
* locked `lake build FLTForHuman.EisensteinGeneral.PiecePartialEulerProduct` under
  `flock /tmp/flt-build.lock` — **`Build completed successfully (4270 jobs)`**, 0 warning lines from this
  file; **no import was added** to the scaffold's list.
* `#print axioms` on the headline — **`[propext, Classical.choice, Quot.sound]`**, no `sorryAx`.
* `dedup.py --within --module '*EisensteinGeneral/PiecePartialEulerProduct*'` — **0 duplicate clusters**,
  0 removable lines (90 declarations, 1 module).
* `move_dead.py --dry-run` — **3 declarations, 37 lines**, and this reading is **the pin's own**:
  `pc_ram_norm_le` (`:374`, 28 lines), `pc_tprod_mul_finprod` (`:425`, 4) and `pc_fin_one_apply`
  (`:1089`, 2) occur exactly once each in the pin's `S_` file — its own proof never uses them — and they
  are three of the 104 engine rows, so they are transcribed rather than shelved; shelving them would also
  strand `pc_ram` and `pc_norm_cpow_neg_two_mul_add_one_le` (`move_dead`'s "live private helpers needed: 2").
* order-scoped collision probe (`tmp/af109/probe-A.lean`, `import` only, `-DautoImplicit=false`) —
  **prints nothing**, exit 0. This module declares exactly **one** public full name, the headline; the 89
  helpers are `private` and so cannot collide (FR-0274).
* **Heartbeat probe pair (recorded, never installed).** Ladder on the module, one run per value:
  200 000 ✓, 100 000 ✓, 60 000 ✓, 50 000 ✓, **45 000 ✓, 40 000 ✗** (two errors, both at `:2120`: a
  `whnf` timeout and a `«synthesize pending MVars»` timeout on the `rw [mul_pow]; ring` that closes
  `pc_finite_half`'s last `calc`), 20 000 ✗ (6 errors), 10 000 ✗ (14 errors). The **module floor** (every
  proof `sorry`, 1 125 lines) reads ✓ at 20 000, 10 000 and **5 000** and ✗ at 1 000 (15 errors), so the
  cost is in the proofs, not in the types; the lowest passing cap is between 40 000 and 45 000, i.e. ≈4.4×
  under the project cap, and no cap is installed.
spec-pin: Theorems/Thm_EisensteinGeneral_Piece_exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant.lean
spec-pin: P2M/Sol/S_EisensteinGeneral_Piece_exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.EisensteinGeneral.ArchIntegralBound
import FLTForHuman.EisensteinGeneral.ArchKType
import FLTForHuman.EisensteinGeneral.Factorization
import FLTForHuman.EisensteinGeneral.Factorization.BoxFourier
import FLTForHuman.EisensteinGeneral.FactorizationDatum
import FLTForHuman.EisensteinGeneral.LocalRam
import FLTForHuman.EisensteinGeneral.LocalUnr
import FLTForHuman.EisensteinGeneral.PieceLatticeMajorant
import FLTForHuman.EisensteinGeneral.PieceWeylIntegrability
import FLTForHuman.EisensteinGeneral.Unfolding
import FLTForHuman.NumberTheory.AdelicFourier.IntegrableTensor
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar.Circle
import FLTForHuman.NumberTheory.NumberField.HeightOneSpectrumSummable
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox
  NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
open scoped Classical

noncomputable section
section GlueHeads

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace EisensteinGeneral.WeylGlue

theorem tprod_mul_eq_tprod_subtype_mul_prod {ι : Type} (S : Finset ι) (a : ι → ℂ) (ha : ∀ i ∈ S, a i = 1)
    (ham : Multipliable (fun i : {i : ι // i ∉ S} => a i)) (T : Finset ι) (b : ι → ℂ)
    (hb : ∀ i, i ∉ T → b i = 1) :
    ∏' i : ι, a i * b i = (∏' i : {i : ι // i ∉ S}, a i) * ∏ i ∈ T, b i := by
  have hinj : Function.Injective (Subtype.val : {i : ι // i ∉ S} → ι) := Subtype.val_injective
  have hr : ∀ i : ι, i ∉ Set.range (Subtype.val : {i : ι // i ∉ S} → ι) → a i = 1 := fun i hi =>
    ha i (of_not_not fun hiS => hi ⟨⟨i, hiS⟩, rfl⟩)
  have hA : ∏' i : {i : ι // i ∉ S}, a i = ∏' i : ι, a i :=
    hinj.tprod_eq fun i hi => ⟨⟨i, fun hiS => hi (ha i hiS)⟩, rfl⟩
  have haM : Multipliable a := (hinj.multipliable_iff hr).mp ham
  have hbM : Multipliable b := multipliable_of_ne_finset_one hb
  rw [haM.tprod_mul hbM, tprod_eq_prod hb, hA]

theorem multipliable_one_sub_of_summable_norm {ι : Type} (u : ι → ℂ) (hu : Summable (fun i : ι => ‖u i‖)) :
    Multipliable (fun i : ι => 1 - u i) := by
  have h : Multipliable (fun i : ι => 1 + -u i) :=
    _root_.multipliable_one_add_of_summable (by simpa only [norm_neg] using hu)
  exact h.congr fun i => (sub_eq_add_neg (1 : ℂ) (u i)).symm

private theorem exists_fractionalIdeal_ne_zero_mem_of_forall_valued_le (F : Type) [Field F] [NumberField F]
    (N : HeightOneSpectrum (𝓞 F) → ℤ) (hN : (Function.support N).Finite) :
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F, I ≠ 0 ∧ ∀ ξ : F,
      (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ξ ≤ WithZero.exp (N v)) → ξ ∈ I := by
  have hJ : (∏ v ∈ hN.toFinset, v.asIdeal ^ (N v).toNat) ≠ ⊥ :=
    Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ v.ne_bot
  obtain ⟨d, hdJ, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hd0
  refine ⟨FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (algebraMap (𝓞 F) F d)⁻¹,
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hdF), fun ξ hξ => ?_⟩
  have hdvd : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ (N v).toNat ∣ Ideal.span {d} := by
    intro v
    by_cases hv : v ∈ hN.toFinset
    · exact (Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal ^ (N v).toNat) hv).trans
        (Ideal.dvd_span_singleton.mpr hdJ)
    · have h0 : N v = 0 := by
        by_contra h
        exact hv (hN.mem_toFinset.mpr (Function.mem_support.mpr h))
      rw [h0, Int.toNat_zero, pow_zero]
      exact one_dvd _
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (algebraMap (𝓞 F) F d * ξ) ≤ 1 := by
    intro v
    have h1 : v.valuation F (algebraMap (𝓞 F) F d) = v.intValuation d := v.valuation_of_algebraMap d
    have h2 : v.intValuation d ≤ WithZero.exp (-((N v).toNat : ℤ)) :=
      (v.intValuation_le_pow_iff_dvd d _).mpr (hdvd v)
    calc v.valuation F (algebraMap (𝓞 F) F d * ξ)
        = v.intValuation d * v.valuation F ξ := by rw [Valuation.map_mul, h1]
      _ ≤ WithZero.exp (-((N v).toNat : ℤ)) * WithZero.exp (N v) := mul_le_mul' h2 (hξ v)
      _ = WithZero.exp (-((N v).toNat : ℤ) + N v) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.mpr (by omega)
      _ = 1 := WithZero.exp_zero
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp
    (IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hint)
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨z, ?_⟩
  rw [Algebra.smul_def, hz, mul_comm (algebraMap (𝓞 F) F d) ξ, mul_inv_cancel_right₀ hdF]

private theorem exists_pos_finprod_absNorm_pow_toNat_neg_le_mul_abs_norm (F : Type) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ξ : F, ξ ∈ I → ξ ≠ 0 → ∀ e : HeightOneSpectrum (𝓞 F) → ℤ,
      (∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ξ = WithZero.exp (e v)) →
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat
        ≤ c₀ * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
  obtain ⟨a, aI, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have haF : algebraMap (𝓞 F) F a ≠ 0 := NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ha
  have hNa : (0 : ℚ) < |Algebra.norm ℚ (algebraMap (𝓞 F) F a)| :=
    abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr haF)
  refine ⟨((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ), Rat.cast_pos.mpr hNa,
    fun ξ hξ hξ0 e he => ?_⟩
  rw [hI, FractionalIdeal.mem_singleton_mul] at hξ
  obtain ⟨y, hy, hξy⟩ := hξ
  obtain ⟨b, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
  have hab : algebraMap (𝓞 F) F a * ξ = algebraMap (𝓞 F) F b := by
    rw [hξy, mul_inv_cancel_left₀ haF]
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    exact mul_ne_zero haF hξ0 hab
  have hdvd : ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal ^ (-(e v)).toNat ∣ Ideal.span {b} := by
    intro v
    by_cases hv : 0 ≤ e v
    · rw [Int.toNat_eq_zero.mpr (by omega), pow_zero]
      exact one_dvd _
    · have h1 : v.valuation F (algebraMap (𝓞 F) F b) = v.intValuation b := v.valuation_of_algebraMap b
      have h2 : v.valuation F (algebraMap (𝓞 F) F a) = v.intValuation a := v.valuation_of_algebraMap a
      have h3 : v.intValuation b ≤ WithZero.exp (e v) := by
        rw [← h1, ← hab, Valuation.map_mul, h2, he v]
        exact mul_le_of_le_one_left' (v.intValuation_le_one a)
      refine (v.intValuation_le_pow_iff_dvd b _).mp ?_
      rwa [Int.toNat_of_nonneg (by omega), neg_neg]
  have hNb : Algebra.norm ℚ (algebraMap (𝓞 F) F b) = ((Algebra.norm ℤ b : ℤ) : ℚ) :=
    (Algebra.coe_norm_int b).symm
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 F)),
      ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat
        ≤ ((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
    intro T
    have hT : (∏ v ∈ T, v.asIdeal ^ (-(e v)).toNat) ∣ Ideal.span {b} :=
      Finset.prod_dvd_of_coprime
        (fun v _ w _ hvw => IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne v w hvw _ _)
        (fun v _ => hdvd v)
    have hT' := map_dvd (Ideal.absNorm (S := 𝓞 F)) hT
    simp only [map_prod, map_pow, Ideal.absNorm_span_singleton] at hT'
    have hle : (∏ v ∈ T, Ideal.absNorm v.asIdeal ^ (-(e v)).toNat) ≤ (Algebra.norm ℤ b).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hb0)) hT'
    have hcast : (∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat)
        = ((∏ v ∈ T, Ideal.absNorm v.asIdeal ^ (-(e v)).toNat : ℕ) : ℝ) := by
      simp only [Nat.cast_prod, Nat.cast_pow]
    have hR : (((Algebra.norm ℤ b).natAbs : ℕ) : ℝ)
        = ((|Algebra.norm ℚ (algebraMap (𝓞 F) F a)| : ℚ) : ℝ) * ((|Algebra.norm ℚ ξ| : ℚ) : ℝ) := by
      rw [Nat.cast_natAbs, ← Rat.cast_intCast, Int.cast_abs, ← hNb, ← hab, map_mul, abs_mul, Rat.cast_mul]
    rw [hcast, ← hR]
    exact Nat.cast_le.mpr hle
  by_cases hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(e v)).toNat
  · rw [finprod_eq_prod _ hfin]
    exact key _
  · rw [finprod_of_infinite_mulSupport hfin]
    have h := key ∅
    rwa [Finset.prod_empty] at h

end EisensteinGeneral.WeylGlue

end GlueHeads

section PieceLayer

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier NumberField.AdelicHaar IsDedekindDomain AutomorphicForm

open scoped NNReal
open EisensteinGeneral

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace EisensteinGeneral.Piece

noncomputable def pc_geom (χϖ : ℂ) (N : ℕ) (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (M + 1), (χϖ * ((N : ℕ) : ℂ) ^ (-(2 * s))) ^ k

noncomputable def pc_ram (N : ℕ) (K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ) : ℂ :=
  c₀ + ∑ k ∈ Finset.Icc 1 K, (((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k

theorem pc_differentiable_cpow_neg_two_mul {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => ((N : ℕ) : ℂ) ^ (-(2 * s))) :=
  Differentiable.const_cpow (differentiable_id.const_mul (2 : ℂ)).neg
    (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))

theorem pc_differentiable_cpow_neg_two_mul_add_one {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (fun s : ℂ => ((N : ℕ) : ℂ) ^ (-(2 * s + 1))) :=
  Differentiable.const_cpow ((differentiable_id.const_mul (2 : ℂ)).add (differentiable_const 1)).neg
    (Or.inl (Nat.cast_ne_zero.mpr hN.ne'))

theorem pc_geom_differentiable (χϖ : ℂ) {N : ℕ} (hN : 0 < N) (M : ℕ) :
    Differentiable ℂ (pc_geom χϖ N M) := by
  unfold pc_geom
  exact Differentiable.fun_sum fun k _ => ((pc_differentiable_cpow_neg_two_mul hN).const_mul χϖ).pow k

theorem pc_ram_differentiable {N : ℕ} (hN : 0 < N) (K : ℕ) (c₀ : ℂ) (sh : ℕ → ℂ) :
    Differentiable ℂ (pc_ram N K c₀ sh) := by
  unfold pc_ram
  exact (differentiable_const c₀).add
    (Differentiable.fun_sum fun k _ => ((pc_differentiable_cpow_neg_two_mul_add_one hN).pow k).mul_const (sh k))

theorem pc_norm_cpow_neg_two_mul_le {N : ℕ} (hN : 1 ≤ N) {R : ℝ} {s : ℂ} (hs : ‖s‖ ≤ R) :
    ‖((N : ℕ) : ℂ) ^ (-(2 * s))‖ ≤ (N : ℝ) ^ (2 * R) := by
  rw [Complex.norm_natCast_cpow_of_pos hN]
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) ?_
  have h := Complex.abs_re_le_norm s
  have h' := neg_abs_le s.re
  simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  linarith

theorem pc_norm_cpow_neg_two_mul_add_one_le {N : ℕ} (hN : 1 ≤ N) {R : ℝ} {s : ℂ} (hs : ‖s‖ ≤ R) :
    ‖((N : ℕ) : ℂ) ^ (-(2 * s + 1))‖ ≤ (N : ℝ) ^ (2 * R + 1) := by
  rw [Complex.norm_natCast_cpow_of_pos hN]
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) ?_
  have h := Complex.abs_re_le_norm s
  have h' := neg_abs_le s.re
  simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, Complex.one_re]
  linarith

theorem pc_geom_norm_le {χϖ : ℂ} (hχ : ‖χϖ‖ = 1) {N : ℕ} (hN : 1 ≤ N) (M : ℕ) {R : ℝ} {s : ℂ}
    (hs : ‖s‖ ≤ R) : ‖pc_geom χϖ N M s‖ ≤ ((M : ℝ) + 1) * ((N : ℝ) ^ (2 * R)) ^ M := by
  have hR : (0 : ℝ) ≤ R := (norm_nonneg s).trans hs
  have hb1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * R) := Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hterm : ∀ k ∈ Finset.range (M + 1),
      ‖(χϖ * ((N : ℕ) : ℂ) ^ (-(2 * s))) ^ k‖ ≤ ((N : ℝ) ^ (2 * R)) ^ M := by
    intro k hk
    rw [norm_pow, norm_mul, hχ, one_mul]
    calc ‖((N : ℕ) : ℂ) ^ (-(2 * s))‖ ^ k ≤ ((N : ℝ) ^ (2 * R)) ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) (pc_norm_cpow_neg_two_mul_le hN hs) k
      _ ≤ ((N : ℝ) ^ (2 * R)) ^ M :=
          pow_le_pow_right₀ hb1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  unfold pc_geom
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [Finset.card_range, nsmul_eq_mul, Nat.cast_succ]

private theorem pc_ram_norm_le {N : ℕ} (hN : 1 ≤ N) (K : ℕ) {c₀ : ℂ} {c₀' : ℝ} (hc₀ : ‖c₀‖ ≤ c₀')
    {sh : ℕ → ℂ} {b : ℝ} (hsh : ∀ k, ‖sh k‖ ≤ b * (N : ℝ) ^ k) {R : ℝ} {s : ℂ} (hs : ‖s‖ ≤ R) :
    ‖pc_ram N K c₀ sh s‖ ≤ c₀' + (K : ℝ) * (b * ((N : ℝ) ^ (2 * R + 1) * N) ^ K) := by
  have hR : (0 : ℝ) ≤ R := (norm_nonneg s).trans hs
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb : (0 : ℝ) ≤ b := by
    have h0 := hsh 0
    simp only [pow_zero, mul_one] at h0
    exact (norm_nonneg _).trans h0
  have hb1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * R + 1) * N :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN' (by positivity)) hN'
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      ‖(((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k‖ ≤ b * ((N : ℝ) ^ (2 * R + 1) * N) ^ K := by
    intro k hk
    have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
    rw [norm_mul, norm_pow]
    calc ‖((N : ℕ) : ℂ) ^ (-(2 * s + 1))‖ ^ k * ‖sh k‖
        ≤ ((N : ℝ) ^ (2 * R + 1)) ^ k * (b * (N : ℝ) ^ k) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (pc_norm_cpow_neg_two_mul_add_one_le hN hs) k) (hsh k)
            (norm_nonneg _) (by positivity)
      _ = b * ((N : ℝ) ^ (2 * R + 1) * N) ^ k := by rw [mul_pow]; ring
      _ ≤ b * ((N : ℝ) ^ (2 * R + 1) * N) ^ K :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 hkK) hb
  unfold pc_ram
  refine (norm_add_le _ _).trans (add_le_add hc₀ ?_)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

theorem pc_norm_localChar_eq_one (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) : ‖ψv v y‖ = 1 := by
  classical
  obtain ⟨x, hxv, hxw⟩ : ∃ x : FiniteAdeleRing (𝓞 F) F, x v = y ∧ ∀ w, w ≠ v → x w = 0 :=
    ⟨(RestrictedProduct.single (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v y :
        FiniteAdeleRing (𝓞 F) F),
      Pi.single_eq_same v y, fun w hw => Pi.single_eq_of_ne hw y⟩
  have h1 : ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x) = ψv v y := by
    rw [hψfin x, finprod_eq_single _ v]
    · show ψv v (x v) = ψv v y
      rw [hxv]
    · intro w hw
      show ψv w (x w) = 1
      rw [hxw w hw, AddChar.map_zero_eq_one]
  rw [← h1]
  exact norm_apply_eq_one_of_isGlobalAddChar F hψ _

private theorem pc_tprod_mul_finprod {ι : Type} (a b : ι → ℂ) (ha : Multipliable a)
    (hb : Function.HasFiniteMulSupport b) :
    ∏' i, (a i * b i) = (∏' i, a i) * ∏ᶠ i, b i := by
  rw [Multipliable.tprod_mul ha (multipliable_of_hasFiniteMulSupport hb), tprod_eq_finprod hb]

@[reducible] noncomputable def pc_locBorel (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

theorem pc_locBorelSpace (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    @BorelSpace (v.adicCompletion F) _ (pc_locBorel F v) :=
  @BorelSpace.mk _ _ (pc_locBorel F v) rfl

noncomputable def pc_locHaar (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    @Measure (v.adicCompletion F) (pc_locBorel F v) := by
  let := pc_locBorel F v
  have := pc_locBorelSpace F v
  exact Measure.addHaar

theorem pc_isAddHaarMeasure_locHaar (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    @Measure.IsAddHaarMeasure (v.adicCompletion F) _ _ (pc_locBorel F v) (pc_locHaar F v) := by
  let := pc_locBorel F v
  have := pc_locBorelSpace F v
  exact Measure.isAddHaarMeasure_addHaarMeasure _

@[reducible] noncomputable def pc_finBorel (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _

theorem pc_finBorelSpace (F : Type) [Field F] [NumberField F] :
    @BorelSpace (FiniteAdeleRing (𝓞 F) F) _ (pc_finBorel F) :=
  @BorelSpace.mk _ _ (pc_finBorel F) rfl

noncomputable def pc_finHaar (F : Type) [Field F] [NumberField F] :
    @Measure (FiniteAdeleRing (𝓞 F) F) (pc_finBorel F) := by
  let := pc_finBorel F
  have := pc_finBorelSpace F
  exact Measure.addHaar

theorem pc_isAddHaarMeasure_finHaar (F : Type) [Field F] [NumberField F] :
    @Measure.IsAddHaarMeasure (FiniteAdeleRing (𝓞 F) F) _ _ (pc_finBorel F) (pc_finHaar F) := by
  let := pc_finBorel F
  have := pc_finBorelSpace F
  exact Measure.isAddHaarMeasure_addHaarMeasure _

theorem pc_measureReal_integers_pos (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] :
    0 < μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos ((EisensteinGeneral.FiniteAdelicFactorization.isOpen_adicCompletionIntegers F v).measure_pos μ ⟨0, Subring.zero_mem _⟩).ne'
    (pc_isCompact_integers v).measure_lt_top.ne

noncomputable def pc_exp {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    (x : v.adicCompletion F) : ℤ :=
  WithZero.log (Valued.v x)

theorem pc_valued_eq_exp {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {x : v.adicCompletion F} (hx : x ≠ 0) : Valued.v x = WithZero.exp (pc_exp x) :=
  (WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hx)).symm

theorem pc_indicator_depth_const {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {m : ℕ} (hm : 1 ≤ m) {A : v.adicCompletion F → ℂ}
    (hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x) :
    ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) →
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A y
        = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x := by
  intro x y hxy
  have hle1 : ((Multiplicative.ofAdd (-(m : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    omega
  have hmem : y - x ∈ v.adicCompletionIntegers F :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hxy.trans hle1)
  by_cases hx : x ∈ v.adicCompletionIntegers F
  · have hy : y ∈ v.adicCompletionIntegers F := by
      have := Subring.add_mem _ hmem hx
      rwa [sub_add_cancel] at this
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    exact hA x hx y hy hxy
  · have hy : y ∉ v.adicCompletionIntegers F := fun hy => hx (by
      have := Subring.sub_mem _ hy hmem
      rwa [sub_sub_cancel] at this)
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem pc_valued_pow_uniformizer {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : (v.adicCompletion F)ˣ} (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (m : ℕ) : Valued.v ((ϖ : v.adicCompletion F) ^ m) = Multiplicative.ofAdd (-(m : ℤ)) := by
  rw [map_pow, hϖ, ← WithZero.coe_pow, ← ofAdd_nsmul]
  congr 2
  simp

theorem pc_continuous_of_depth_const {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : (v.adicCompletion F)ˣ} (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (m : ℕ) {A : v.adicCompletion F → ℂ}
    (hA : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x) :
    Continuous A := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  refine (continuousAt_const : ContinuousAt (fun _ => A x) x).congr ?_
  have hr : (0 : ℝ) < ‖(ϖ : v.adicCompletion F) ^ m‖ :=
    norm_pos_iff.mpr (pow_ne_zero m ϖ.ne_zero)
  filter_upwards [Metric.closedBall_mem_nhds x hr] with y hy
  have hval : Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) := by
    rw [← pc_valued_pow_uniformizer hϖ m]
    exact Valued.toNormedField.norm_le_iff.mp (by simpa [dist_eq_norm] using hy)
  exact (hA x y hval).symm

theorem pc_integrableOn_integers_of_depth_const {F : Type} [Field F] [NumberField F]
    {v : HeightOneSpectrum (𝓞 F)} [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    {ϖ : (v.adicCompletion F)ˣ} (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (m : ℕ) {A : v.adicCompletion F → ℂ}
    (hA : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x) :
    IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ :=
  (pc_continuous_of_depth_const hϖ m hA).continuousOn.integrableOn_compact (pc_isCompact_integers v)

noncomputable def pc_corrOff (χϖ : ℂ) (N : ℕ) (e : ℤ) (s : ℂ) : ℂ :=
  if e ≤ 0 then pc_geom χϖ N (-e).toNat s else 0

noncomputable def pc_corrOn (N : ℕ) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ) (sh : ℕ → ℂ)
    (s : ℂ) : ℂ :=
  if e ≤ n + (max m c : ℕ) then
    (μ𝒪 : ℂ)⁻¹ * pc_ram N (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat c₀ sh s
  else 0

theorem pc_corrOff_differentiable (χϖ : ℂ) {N : ℕ} (hN : 0 < N) (e : ℤ) :
    Differentiable ℂ (pc_corrOff χϖ N e) := by
  unfold pc_corrOff
  by_cases he : e ≤ 0
  · simp only [he, ↓reduceIte]
    exact pc_geom_differentiable χϖ hN _
  · simp only [he, ↓reduceIte]
    exact differentiable_const 0

theorem pc_corrOn_differentiable {N : ℕ} (hN : 0 < N) (n : ℤ) (c m : ℕ) (e : ℤ) (μ𝒪 : ℝ) (c₀ : ℂ)
    (sh : ℕ → ℂ) : Differentiable ℂ (pc_corrOn N n c m e μ𝒪 c₀ sh) := by
  unfold pc_corrOn
  by_cases he : e ≤ n + (max m c : ℕ)
  · simp only [he, ↓reduceIte]
    exact (pc_ram_differentiable hN _ c₀ sh).const_mul _
  · simp only [he, ↓reduceIte]
    exact differentiable_const 0

theorem pc_corrOff_spec (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ)
    (hψ0 : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (0 : ℤ) → ψ x = 1)
    (hψ0' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp ((0 : ℤ) + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (hξ : ξ ≠ 0) :
    (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
        * (∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
          * ψ (-(ξ * x))) ∂μ)
      = (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * pc_corrOff ((χ ϖ : ℂˣ) : ℂ) (Ideal.absNorm v.asIdeal) (pc_exp ξ) s := by
  have hμ : ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pc_measureReal_integers_pos F v μ).ne'
  unfold pc_corrOff
  split_ifs with he
  · have hM : Valued.v ξ = WithZero.exp ((0 : ℤ) - (((-pc_exp ξ).toNat : ℕ) : ℤ)) := by
      rw [pc_valued_eq_exp hξ]
      congr 1
      omega
    rw [LocalUnr.integral_twisted_eq F v μ ϖ hϖ χ hχ s hs ψ 0 hψ0 hψ0' ξ _ hM]
    unfold pc_geom
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul]
  · have hlt : WithZero.exp (0 : ℤ) < Valued.v ξ := by
      rw [pc_valued_eq_exp hξ, WithZero.exp_lt_exp]
      omega
    rw [LocalUnr.integral_twisted_eq_zero_of_exp_lt F v μ ϖ hϖ χ hχ s hs ψ 0 hψ0 hψ0' ξ hlt,
      mul_zero, mul_zero]

theorem pc_corrOn_spec (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A₀ : v.adicCompletion F → ℂ)
    (hA₀ : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A₀ y = A₀ x)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (hξ : ξ ≠ 0) :
    (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)⁻¹
        * (∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀ x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x))) ∂μ)
      = pc_corrOn (Ideal.absNorm v.asIdeal) n c m (pc_exp ξ)
          (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
          (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
            (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀ x * ψ (-(ξ * x)) ∂μ)
          (fun k : ℕ => ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
            LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψ (-(ξ * x)) ∂μ) s := by
  have hA' := pc_indicator_depth_const hm hA₀
  have hAint : IntegrableOn ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ :=
    pc_integrableOn_integers_of_depth_const μ hϖ m hA'
  unfold pc_corrOn
  split_ifs with he
  · have h := LocalRam.integral_twisted_smooth_eq F v μ ϖ hϖ χ c hc hχ m hm _ hAint B hB s hs ψ n
      hψn hψn' ξ (pc_exp ξ) (pc_valued_eq_exp hξ)
    simp only [Set.indicator_indicator, Set.inter_self] at h
    rw [h]
    rfl
  · have hlt : WithZero.exp (n + (max m c : ℕ)) < Valued.v ξ := by
      rw [pc_valued_eq_exp hξ, WithZero.exp_lt_exp]
      omega
    have h := LocalRam.integral_twisted_smooth_eq_zero_of_exp_lt F v μ ϖ hϖ χ c hc hχ m hm _ hAint B
      hB s hs hA' ψ n hψn hψn' ξ hlt
    simp only [Set.indicator_indicator, Set.inter_self] at h
    rw [h, mul_zero]

theorem pc_one_lt_absNorm (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    1 < Ideal.absNorm v.asIdeal :=
  NumberField.HeightOneSpectrum.one_lt_absNorm v

private theorem pc_norm_mul_cpow_lt_one_nat {χϖ : ℂ} (hχ : ‖χϖ‖ = 1) {N : ℕ} (hN : 1 < N) {s : ℂ} (hs : 0 < s.re) :
    ‖χϖ * ((N : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 := by
  rw [norm_mul, hχ, one_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
  refine Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hN) ?_
  simp only [Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
  linarith

open scoped Classical in

noncomputable def pc_euler {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  if v ∈ S then 1
  else 1 - ((χv v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))

open scoped Classical in

noncomputable def pc_corr (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (mS : ℕ)
    (A₀ B : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (w : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) : ℂ :=
  if v ∈ S then
    pc_corrOn (Ideal.absNorm v.asIdeal) (nψ v) (cS v) mS (pc_exp (w v))
      ((pc_locHaar F v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A₀ v) x * ψv v (-(w v * x))
          ∂(pc_locHaar F v))
      (fun k : ℕ => ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
        LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ x * B v x⁻¹ * ψv v (-(w v * x)) ∂(pc_locHaar F v)) s
  else pc_corrOff ((χv v (ϖ v) : ℂˣ) : ℂ) (Ideal.absNorm v.asIdeal) (pc_exp (w v)) s

private theorem pc_corr_differentiable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (mS : ℕ)
    (A₀ B : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (w : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    Differentiable ℂ (pc_corr F S χv ϖ ψv nψ cS mS A₀ B w v) := by
  have hN : 0 < Ideal.absNorm v.asIdeal := by have := pc_one_lt_absNorm F v; omega
  unfold pc_corr
  by_cases hv : v ∈ S
  · simp only [hv, ↓reduceIte]
    exact pc_corrOn_differentiable hN _ _ _ _ _ _ _
  · simp only [hv, ↓reduceIte]
    exact pc_corrOff_differentiable _ hN _

theorem pc_corr_eq_one (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (mS : ℕ)
    (A₀ B : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (w : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) (hw : pc_exp (w v) = 0) (s : ℂ) :
    pc_corr F S χv ϖ ψv nψ cS mS A₀ B w v s = 1 := by
  simp only [pc_corr, hv, ↓reduceIte, pc_corrOff, hw, le_refl, neg_zero, Int.toNat_zero, pc_geom, zero_add,
    Finset.range_one, Finset.sum_singleton, pow_zero]

theorem pc_euler_eq_one_of_mem (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) (v : HeightOneSpectrum (𝓞 F)) (hv : v ∈ S)
    (s : ℂ) : pc_euler S χv ϖ v s = 1 := by
  simp only [pc_euler, hv, ↓reduceIte]

theorem pc_integrable_off (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (ξ : v.adicCompletion F) :
    Integrable (fun x => (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
          * ψ (-(ξ * x)))) μ :=
  (LocalUnr.integrable_twisted_and_integral_norm_eq F v μ ϖ hϖ χ hχ s hs ψ n hψn ξ).1

theorem pc_integrable_on (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A₀ : v.adicCompletion F → ℂ)
    (hA₀ : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A₀ y = A₀ x)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (ξ : v.adicCompletion F) :
    Integrable (fun x => (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀ x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x)))) μ := by
  have hAint : IntegrableOn ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ :=
    pc_integrableOn_integers_of_depth_const μ hϖ m (pc_indicator_depth_const hm hA₀)
  have h := LocalRam.integrable_twisted_smooth F v μ ϖ hϖ χ c hc hχ m hm _ hAint B hB s hs ψ n hψn ξ
  simpa only [Set.indicator_indicator, Set.inter_self] using h

private theorem pc_excess_bounds_local (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (hχϖ : ‖((χ ϖ : ℂˣ) : ℂ)‖ = 1)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : 1 ≤ s.re)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (ξ : v.adicCompletion F) :
    0 ≤ (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
        * (∫ x, ‖(((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
            * ψ (-(ξ * x)))‖ ∂μ) - 1 ∧
      (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))⁻¹
        * (∫ x, ‖(((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
            + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                  * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
            * ψ (-(ξ * x)))‖ ∂μ) - 1
        ≤ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) := by
  have hN : (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by exact_mod_cast pc_one_lt_absNorm F v
  have hs' : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 :=
    pc_norm_mul_cpow_lt_one_nat hχϖ (pc_one_lt_absNorm F v) (by linarith)
  rw [(LocalUnr.integrable_twisted_and_integral_norm_eq F v μ ϖ hϖ χ hχ s hs' ψ n hψn ξ).2, hχϖ,
    one_mul, one_mul]
  have hμ : 0 < μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := pc_measureReal_integers_pos F v μ
  set N : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) with hNdef
  have hNpos : 0 < N := by linarith
  have hy : N ^ (-(2 * s.re + 1)) = N ^ (-(2 * s.re)) / N := by
    rw [show -(2 * s.re + 1) = -(2 * s.re) + (-1 : ℝ) by ring, Real.rpow_add hNpos, Real.rpow_neg_one,
      div_eq_mul_inv]
  have hx0 : 0 < N ^ (-(2 * s.re)) := Real.rpow_pos_of_pos hNpos _
  have hx4 : N ^ (-(2 * s.re)) ≤ 1 / 4 := by
    have h1 : N ^ (-(2 * s.re)) ≤ N ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : N ^ (-(2 : ℝ)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by norm_num)
    have h3 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_two]
      norm_num
    exact h1.trans (h2.trans h3.le)
  set x : ℝ := N ^ (-(2 * s.re)) with hx
  have hxN : x / N ≤ x / 2 := div_le_div_of_nonneg_left hx0.le (by norm_num) hN
  have hxN0 : 0 ≤ x / N := div_nonneg hx0.le hNpos.le
  have h1x : 0 < 1 - x := by linarith
  have hkey : 0 ≤ x * (1 - 2 * x) := mul_nonneg hx0.le (by linarith)
  rw [hy, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hμ.ne', one_mul]
  constructor
  · rw [sub_nonneg, ← div_eq_mul_inv, le_div_iff₀ h1x]
    linarith
  · rw [← div_eq_mul_inv, div_sub_one h1x.ne', div_le_iff₀ h1x]
    nlinarith [hkey, hxN0, hxN, hx0]

theorem pc_fac_hint (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχϖ : ∀ v, ‖((χv v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χv v u = 1)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (hcS : ∀ v ∈ S, 1 ≤ cS v)
    (hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v), χv v u = 1)
    (mS : ℕ) (hmS : 1 ≤ mS)
    (A₀ B : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hA₀ : ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A₀ v y = A₀ v x)
    (hB : ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B v y = B v x)
    (s : ℂ) (hs : 1 < s.re)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hoff : ∀ v ∉ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
    (hon : ∀ v ∈ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A₀ v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B v y⁻¹) x)
    (w : FiniteAdeleRing (𝓞 F) F) :
    Integrable (fun y => h v y * ψv v (-(w v * y))) μ := by
  have hsv : ‖((χv v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 :=
    pc_norm_mul_cpow_lt_one_nat (hχϖ v) (pc_one_lt_absNorm F v) (by linarith)
  by_cases hv : v ∈ S
  · simp only [hon v hv]
    exact pc_integrable_on F v μ (ϖ v) (hϖ v) (χv v) (cS v) (hcS v hv) (hχc v hv) mS hmS (A₀ v)
      (hA₀ v hv) (B v) (hB v hv) s hsv (ψv v) (nψ v) (hψv v) (w v)
  · simp only [hoff v hv]
    exact pc_integrable_off F v μ (ϖ v) (hϖ v) (χv v) (hχS v hv) s hsv (ψv v) (nψ v) (hψv v) (w v)

theorem pc_fac_hsum (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχϖ : ∀ v, ‖((χv v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χv v u = 1)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (s : ℂ) (hs : 1 < s.re)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hoff : ∀ v ∉ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
    (w : FiniteAdeleRing (𝓞 F) F) (S' : Finset (HeightOneSpectrum (𝓞 F))) (hS'S : ∀ v, v ∉ S' → v ∉ S) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S'} =>
      ((pc_locHaar F v.1).real (v.1.adicCompletionIntegers F : Set (v.1.adicCompletion F)))⁻¹
          * (∫ y, ‖h v.1 y * ψv v.1 (-(w v.1 * y))‖ ∂(pc_locHaar F v.1)) - 1 := by
  let : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v => pc_locBorel F v
  have : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v => pc_locBorelSpace F v
  have : ∀ v : HeightOneSpectrum (𝓞 F), (pc_locHaar F v).IsAddHaarMeasure :=
    fun v => pc_isAddHaarMeasure_locHaar F v
  have hbound : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S'} =>
      2 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 * s.re)) :=
    ((summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt F (by linarith : (1 : ℝ) < 2 * s.re)).mul_left
      2).subtype _
  refine Summable.of_nonneg_of_le (fun v => ?_) (fun v => ?_) hbound
  · simp only [hoff v.1 (hS'S v.1 v.2)]
    exact (pc_excess_bounds_local F v.1 (pc_locHaar F v.1) (ϖ v.1) (hϖ v.1) (χv v.1) (hχϖ v.1) (hχS v.1 (hS'S v.1 v.2))
      s hs.le (ψv v.1) (nψ v.1) (hψv v.1) (w v.1)).1
  · simp only [hoff v.1 (hS'S v.1 v.2)]
    exact (pc_excess_bounds_local F v.1 (pc_locHaar F v.1) (ϖ v.1) (hϖ v.1) (χv v.1) (hχϖ v.1) (hχS v.1 (hS'S v.1 v.2))
      s hs.le (ψv v.1) (nψ v.1) (hψv v.1) (w v.1)).2

private theorem pc_finite_value (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχϖ : ∀ v, ‖((χv v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χv v u = 1)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
    (hnψ : ∀ v ∉ S, nψ v = 0)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (hcS : ∀ v ∈ S, 1 ≤ cS v)
    (hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v), χv v u = 1)
    (mS : ℕ) (hmS : 1 ≤ mS)
    (A₀ B : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hA₀ : ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A₀ v y = A₀ v x)
    (hB : ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B v y = B v x)
    (s : ℂ) (hs : 1 < s.re)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hoff : ∀ v ∉ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
    (hon : ∀ v ∈ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A₀ v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B v y⁻¹) x)
    (w : FiniteAdeleRing (𝓞 F) F) (hw0 : ∀ v, w v ≠ 0)
    (hwfin : {v : HeightOneSpectrum (𝓞 F) | pc_exp (w v) ≠ 0}.Finite) :
    ((pc_finHaar F).real (integralFiniteAdeles (𝓞 F) F) : ℂ)⁻¹
        * ∫ x, ∏ᶠ v : HeightOneSpectrum (𝓞 F), (h v (x v) * ψv v (-(w v * x v))) ∂(pc_finHaar F)
      = ∏' v : HeightOneSpectrum (𝓞 F), (pc_euler S χv ϖ v s * pc_corr F S χv ϖ ψv nψ cS mS A₀ B w v s) := by
  classical
  let : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v => pc_locBorel F v
  have : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v => pc_locBorelSpace F v
  have : ∀ v : HeightOneSpectrum (𝓞 F), (pc_locHaar F v).IsAddHaarMeasure :=
    fun v => pc_isAddHaarMeasure_locHaar F v
  let : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := pc_finBorel F
  have : BorelSpace (FiniteAdeleRing (𝓞 F) F) := pc_finBorelSpace F
  have : (pc_finHaar F).IsAddHaarMeasure := pc_isAddHaarMeasure_finHaar F
  have hs0 : 0 < s.re := by linarith
  have hsv : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((χv v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1 :=
    fun v => pc_norm_mul_cpow_lt_one_nat (hχϖ v) (pc_one_lt_absNorm F v) hs0

  set S' : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hwfin.toFinset with hS'
  have hS'S : ∀ v, v ∉ S' → v ∉ S := fun v hv hvS => hv (Finset.mem_union_left _ hvS)
  have hS'e : ∀ v, v ∉ S' → pc_exp (w v) = 0 := by
    intro v hv
    by_contra hne
    exact hv (Finset.mem_union_right _ (hwfin.mem_toFinset.mpr hne))

  have h₁ : ∀ v ∉ S', ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F →
      h v y * ψv v (-(w v * y)) = 1 := by
    intro v hv y hy
    have hvS := hS'S v hv
    have hy' : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
    have hy'' : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := fun h' => h' hy'
    rw [hoff v hvS y, Set.indicator_of_mem hy', Set.indicator_of_notMem hy'', add_zero, one_mul]
    refine hψv v _ ?_
    rw [hnψ v hvS, WithZero.exp_zero, Valuation.map_neg, Valuation.map_mul, pc_valued_eq_exp (hw0 v), hS'e v hv,
      WithZero.exp_zero, one_mul]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hy
  have hint : ∀ v : HeightOneSpectrum (𝓞 F), Integrable (fun y => h v y * ψv v (-(w v * y))) (pc_locHaar F v) :=
    fun v => pc_fac_hint F v (pc_locHaar F v) S χv ϖ hϖ hχϖ hχS ψv nψ hψv cS hcS hχc mS hmS A₀ B hA₀ hB s hs h hoff
      hon w
  have hsum := pc_fac_hsum F S χv ϖ hϖ hχϖ hχS ψv nψ hψv s hs h hoff w S' hS'S

  rw [(Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod F (pc_finHaar F) S'
    (fun v => pc_locHaar F v) (fun v y => h v y * ψv v (-(w v * y))) h₁ hint hsum).2]
  refine tprod_congr fun v => ?_
  by_cases hv : v ∈ S
  · rw [pc_euler_eq_one_of_mem F S χv ϖ v hv, one_mul]
    simp only [pc_corr, hv, ↓reduceIte, hon v hv]
    exact pc_corrOn_spec F v (pc_locHaar F v) (ϖ v) (hϖ v) (χv v) (cS v) (hcS v hv) (hχc v hv) mS hmS (A₀ v)
      (hA₀ v hv) (B v) (hB v hv) s (hsv v) (ψv v) (nψ v) (hψv v) (hψv' v) (w v) (hw0 v)
  · simp only [pc_corr, pc_euler, hv, ↓reduceIte, hoff v hv]
    have hψ0 := hψv v
    rw [hnψ v hv] at hψ0
    have hψ0' := hψv' v
    rw [hnψ v hv] at hψ0'
    exact pc_corrOff_spec F v (pc_locHaar F v) (ϖ v) (hϖ v) (χv v) (hχS v hv) s (hsv v) (ψv v) hψ0 hψ0' (w v) (hw0 v)

theorem pc_fin_mul_apply {F : Type} [Field F] [NumberField F] (x w : FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) : (x * w) v = x v * w v := rfl

theorem pc_fin_neg_apply {F : Type} [Field F] [NumberField F] (x : FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) : (-x) v = -(x v) := rfl

private theorem pc_fin_one_apply {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := rfl

theorem pc_fin_integral_cofinite {F : Type} [Field F] [NumberField F] (x : FiniteAdeleRing (𝓞 F) F) :
    {v : HeightOneSpectrum (𝓞 F) | x v ∉ v.adicCompletionIntegers F}.Finite :=
  Filter.eventually_cofinite.mp x.2

theorem pc_twist_eq_one {F : Type} [Field F] [NumberField F]
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hn : nψ v = 0) (w : v.adicCompletion F) (hw0 : w ≠ 0) (hw : pc_exp w = 0)
    (y : v.adicCompletion F) (hy : y ∈ v.adicCompletionIntegers F) : ψv v (-(w * y)) = 1 := by
  refine hψv v _ ?_
  rw [hn, WithZero.exp_zero, Valuation.map_neg, Valuation.map_mul, pc_valued_eq_exp hw0, hw, WithZero.exp_zero,
    one_mul]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hy

theorem pc_fin_fourier_eq (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hnψ : ∀ v ∉ S, nψ v = 0)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hone : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1)
    (w : FiniteAdeleRing (𝓞 F) F) (hw0 : ∀ v, w v ≠ 0)
    (hwfin : {v : HeightOneSpectrum (𝓞 F) | pc_exp (w v) ≠ 0}.Finite)
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] (ν : Measure (FiniteAdeleRing (𝓞 F) F)) :
    fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        ν (fun x => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)) w
      = ∫ x, ∏ᶠ v : HeightOneSpectrum (𝓞 F), (h v (x v) * ψv v (-(w v * x v))) ∂ν := by
  rw [fourierIntegral_def]
  congr 1
  funext x
  show ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) (-(x * w)))
      * (∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)) = _
  rw [hψfin, mul_comm]
  have hT : (((S : Set (HeightOneSpectrum (𝓞 F))) ∪ {v | x v ∉ v.adicCompletionIntegers F})
      ∪ {v | pc_exp (w v) ≠ 0}).Finite :=
    (S.finite_toSet.union (pc_fin_integral_cofinite x)).union hwfin
  have hfh : Function.HasFiniteMulSupport fun v => h v (x v) := by
    refine hT.subset fun v hv => ?_
    by_contra hvT
    simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, not_or, not_not] at hvT
    exact hv (hone v hvT.1.1 _ hvT.1.2)
  have hfψ : Function.HasFiniteMulSupport fun v => ψv v ((-(x * w)) v) := by
    refine hT.subset fun v hv => ?_
    by_contra hvT
    simp only [Set.mem_union, Set.mem_ofPred_eq, Finset.mem_coe, not_or, not_not] at hvT
    simp only [Function.mem_mulSupport, pc_fin_neg_apply, pc_fin_mul_apply, mul_comm (x v) (w v)] at hv
    exact hv (pc_twist_eq_one ψv nψ hψv v (hnψ v hvT.1.1) (w v) (hw0 v) hvT.2 (x v) hvT.1.2)
  rw [← finprod_mul_distrib hfh hfψ]
  refine finprod_congr fun v => ?_
  simp only [pc_fin_neg_apply, pc_fin_mul_apply, mul_comm (x v) (w v)]

theorem pc_fourierIntegral_eq_integral_mul {A : Type} [CommRing A] [MeasurableSpace A]
    (ψ : AddChar A ℂ) (μ : Measure A) (f : A → ℂ) (w : A) :
    fourierIntegral ψ μ f w = ∫ z, f z * ψ (-(w * z)) ∂μ := by
  rw [fourierIntegral_def]
  congr 1
  funext z
  rw [mul_comm (ψ _) (f z), mul_comm z w]

theorem pc_integral_prod_pi {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] (A : ι₁ → ℝ → ℂ) (B : ι₂ → ℂ → ℂ) :
    ∫ p : (ι₁ → ℝ) × (ι₂ → ℂ), (∏ i, A i (p.1 i)) * ∏ w, B w (p.2 w)
      = (∏ i, ∫ x : ℝ, A i x) * ∏ w, ∫ z : ℂ, B w z := by
  rw [MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.integral_prod_mul (fun x : ι₁ → ℝ => ∏ i, A i (x i)) (fun z : ι₂ → ℂ => ∏ w, B w (z w)),
    MeasureTheory.integral_fintype_prod_volume_eq_prod A, MeasureTheory.integral_fintype_prod_volume_eq_prod B]

open scoped Classical in

theorem pc_arch_value (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hψarch : ∀ p : mixedEmbedding.mixedSpace F,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
              Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
              Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
    (fr : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ) (fc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ)
    (q : mixedEmbedding.mixedSpace F) :
    fourierIntegral
        (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
        MeasureTheory.volume
        (fun p : mixedEmbedding.mixedSpace F =>
          (∏ i : {w : InfinitePlace F // w.IsReal}, fr i (p.1 i))
            * ∏ w : {w : InfinitePlace F // w.IsComplex}, fc w (p.2 w)) q
      = (∏ i : {w : InfinitePlace F // w.IsReal}, ∫ x : ℝ, fr i x
            * Complex.exp (-(((2 * Real.pi * (-(θr i * q.1 i)) * x : ℝ) : ℂ) * Complex.I)))
        * ∏ w : {w : InfinitePlace F // w.IsComplex}, ∫ z : ℂ, fc w z
            * Complex.exp (-(((4 * Real.pi * ((-(θc w * q.2 w)) * z).re : ℝ) : ℂ) * Complex.I)) := by
  rw [fourierIntegral_def]
  have hchar : ∀ p : mixedEmbedding.mixedSpace F,
      (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom)) (-(p * q))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
              Complex.exp (-(((2 * Real.pi * (-(θr i * q.1 i)) * p.1 i : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
              Complex.exp (-(((4 * Real.pi * ((-(θc w * q.2 w)) * p.2 w).re : ℝ) : ℂ) * Complex.I)) := by
    intro p
    show ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (-(p * q)))) = _
    rw [hψarch]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp only [Prod.fst_neg, Prod.fst_mul, Pi.neg_apply, Pi.mul_apply]
      push_cast
      ring_nf
    · refine Finset.prod_congr rfl fun w _ => ?_
      simp only [Prod.snd_neg, Prod.snd_mul, Pi.neg_apply, Pi.mul_apply]
      push_cast
      ring_nf
  have hsplit : ∀ p : mixedEmbedding.mixedSpace F,
      (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom)) (-(p * q))
        * ((∏ i : {w : InfinitePlace F // w.IsReal}, fr i (p.1 i))
            * ∏ w : {w : InfinitePlace F // w.IsComplex}, fc w (p.2 w))
      = (fun x : {w : InfinitePlace F // w.IsReal} → ℝ => ∏ i : {w : InfinitePlace F // w.IsReal}, (fr i (x i)
            * Complex.exp (-(((2 * Real.pi * (-(θr i * q.1 i)) * x i : ℝ) : ℂ) * Complex.I)))) p.1
        * (fun z : {w : InfinitePlace F // w.IsComplex} → ℂ => ∏ w : {w : InfinitePlace F // w.IsComplex},
            (fc w (z w)
              * Complex.exp (-(((4 * Real.pi * ((-(θc w * q.2 w)) * z w).re : ℝ) : ℂ) * Complex.I)))) p.2 := by
    intro p
    rw [hchar p]
    simp only [Finset.prod_mul_distrib]
    ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hsplit)]
  exact pc_integral_prod_pi
    (fun i (x : ℝ) => fr i x * Complex.exp (-(((2 * Real.pi * (-(θr i * q.1 i)) * x : ℝ) : ℂ) * Complex.I)))
    (fun w (z : ℂ) => fc w z * Complex.exp (-(((4 * Real.pi * ((-(θc w * q.2 w)) * z).re : ℝ) : ℂ) * Complex.I)))

theorem pc_unit_fin_ne_zero {F : Type} [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) : (U : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  have h : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v * (U : AdeleRing (𝓞 F) F).2 v = 1 :=
    congrArg (fun z : AdeleRing (𝓞 F) F => z.2 v) (Units.inv_mul U)
  exact right_ne_zero_of_mul_eq_one h

theorem pc_unit_fin_exp_finite {F : Type} [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ) :
    {v : HeightOneSpectrum (𝓞 F) | pc_exp ((U : AdeleRing (𝓞 F) F).2 v) ≠ 0}.Finite := by
  refine ((pc_fin_integral_cofinite (U : AdeleRing (𝓞 F) F).2).union
    (pc_fin_integral_cofinite ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2)).subset ?_
  intro v hv
  by_contra hmem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hmem
  apply hv
  have hx := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem.1
  have hy := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem.2
  have hm : (U : AdeleRing (𝓞 F) F).2 v * ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 :=
    congrArg (fun z : AdeleRing (𝓞 F) F => z.2 v) (Units.mul_inv U)
  have hxy : Valued.v ((U : AdeleRing (𝓞 F) F).2 v) * Valued.v (((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) :
      AdeleRing (𝓞 F) F).2 v) = 1 := by
    rw [← Valuation.map_mul, hm, Valuation.map_one]
  have h1 : Valued.v ((U : AdeleRing (𝓞 F) F).2 v) = 1 := by
    refine le_antisymm hx ?_
    have := mul_le_mul' (le_refl (Valued.v ((U : AdeleRing (𝓞 F) F).2 v))) hy
    rwa [hxy, mul_one] at this
  have h2 := pc_valued_eq_exp (pc_unit_fin_ne_zero U v)
  rw [h1] at h2
  exact WithZero.exp_eq_one.mp h2.symm

private theorem pc_unit_real_ne_zero {F : Type} [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ)
    (i : {w : InfinitePlace F // w.IsReal}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (U : AdeleRing (𝓞 F) F).1).1 i ≠ 0 := by
  have hm : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 * (U : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.inv_mul U)
  have h : (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i
      * (InfiniteAdeleRing.ringEquiv_mixedSpace F (U : AdeleRing (𝓞 F) F).1).1 i = 1 := by
    have h2 := congrArg (fun z => (InfiniteAdeleRing.ringEquiv_mixedSpace F z).1 i) hm
    simpa only [map_mul, map_one, Prod.fst_mul, Pi.mul_apply, Prod.fst_one, Pi.one_apply] using h2
  exact right_ne_zero_of_mul_eq_one h

private theorem pc_unit_complex_ne_zero {F : Type} [Field F] [NumberField F] (U : (AdeleRing (𝓞 F) F)ˣ)
    (w : {w : InfinitePlace F // w.IsComplex}) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace F (U : AdeleRing (𝓞 F) F).1).2 w ≠ 0 := by
  have hm : ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 * (U : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.inv_mul U)
  have h : (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w
      * (InfiniteAdeleRing.ringEquiv_mixedSpace F (U : AdeleRing (𝓞 F) F).1).2 w = 1 := by
    have h2 := congrArg (fun z => (InfiniteAdeleRing.ringEquiv_mixedSpace F z).2 w) hm
    simpa only [map_mul, map_one, Prod.snd_mul, Pi.mul_apply, Prod.snd_one, Pi.one_apply] using h2
  exact right_ne_zero_of_mul_eq_one h

private theorem pc_differentiable_prod {ι : Type} (T : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ T, Differentiable ℂ (f i)) : Differentiable ℂ (fun s => ∏ i ∈ T, f i s) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a T)).mul (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem pc_hoff_one {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hoff : ∀ v ∉ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) (y : v.adicCompletion F) (hy : y ∈ v.adicCompletionIntegers F) :
    h v y = 1 := by
  have hy' : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hy
  have hy'' : y ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := fun h' => h' hy'
  rw [hoff v hv y, Set.indicator_of_mem hy', Set.indicator_of_notMem hy'', add_zero]

theorem pc_multipliable_euler (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ) (hχϖ : ∀ v, ‖((χv v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (s : ℂ) (hs : 0 < s.re) :
    Multipliable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} => pc_euler S χv ϖ v.1 s := by
  have hsum : Summable fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      ‖((χv v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))‖ := by
    have hre : (-(2 * s + 1)).re = -(2 * s.re + 1) := by
      simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
        sub_zero, Complex.one_re]
    refine ((summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt F
      (by linarith : (1 : ℝ) < 2 * s.re + 1)).subtype {v : HeightOneSpectrum (𝓞 F) | v ∉ S}).congr fun v => ?_
    have hN : 0 < Ideal.absNorm v.1.asIdeal := by have := pc_one_lt_absNorm F v.1; omega
    rw [Function.comp_apply, norm_mul, hχϖ, one_mul, Complex.norm_natCast_cpow_of_pos hN, hre]
  refine (EisensteinGeneral.WeylGlue.multipliable_one_sub_of_summable_norm _ hsum).congr fun v => ?_
  simp only [pc_euler, v.2, ↓reduceIte]

open scoped Classical in
noncomputable def pc_tensor (F : Type) [Field F] [NumberField F]
    (Wr' : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ) (Wc' : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ)
    (h' : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ) (z : AdeleRing (𝓞 F) F) : ℂ :=
  ((∏ i : {w : InfinitePlace F // w.IsReal}, Wr' i ((InfiniteAdeleRing.ringEquiv_mixedSpace F z.1).1 i))
      * ∏ w : {w : InfinitePlace F // w.IsComplex}, Wc' w ((InfiniteAdeleRing.ringEquiv_mixedSpace F z.1).2 w))
    * ∏ᶠ v : HeightOneSpectrum (𝓞 F), h' v (z.2 v)

theorem pc_fin_zero_apply {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (0 : FiniteAdeleRing (𝓞 F) F) v = 0 := rfl

theorem pc_integrable_finprod (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχϖ : ∀ v, ‖((χv v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χv v u = 1)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (hcS : ∀ v ∈ S, 1 ≤ cS v)
    (hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v), χv v u = 1)
    (mS : ℕ) (hmS : 1 ≤ mS)
    (A₀ B : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hA₀ : ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A₀ v y = A₀ v x)
    (hB : ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B v y = B v x)
    (s : ℂ) (hs : 1 < s.re)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hoff : ∀ v ∉ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
    (hon : ∀ v ∈ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A₀ v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B v y⁻¹) x)
    :
    Integrable (fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)) ν := by
  let : ∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F) := fun v => pc_locBorel F v
  have : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F) := fun v => pc_locBorelSpace F v
  have : ∀ v : HeightOneSpectrum (𝓞 F), (pc_locHaar F v).IsAddHaarMeasure :=
    fun v => pc_isAddHaarMeasure_locHaar F v
  have h₁ : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F →
      h v y * ψv v (-((0 : FiniteAdeleRing (𝓞 F) F) v * y)) = 1 := by
    intro v hv y hy
    rw [pc_hoff_one S χv s h hoff v hv y hy, pc_fin_zero_apply, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
  have hint : ∀ v : HeightOneSpectrum (𝓞 F),
      Integrable (fun y => h v y * ψv v (-((0 : FiniteAdeleRing (𝓞 F) F) v * y))) (pc_locHaar F v) :=
    fun v => pc_fac_hint F v (pc_locHaar F v) S χv ϖ hϖ hχϖ hχS ψv nψ hψv cS hcS hχc mS hmS A₀ B hA₀ hB s hs h hoff
      hon 0
  have hsum := pc_fac_hsum F S χv ϖ hϖ hχϖ hχS ψv nψ hψv s hs h hoff 0 S (fun _ hv => hv)
  have hI := (Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod F ν S
    (fun v => pc_locHaar F v) (fun v y => h v y * ψv v (-((0 : FiniteAdeleRing (𝓞 F) F) v * y))) h₁ hint hsum).1
  refine hI.congr (MeasureTheory.ae_of_all _ fun x => ?_)
  refine finprod_congr fun v => ?_
  simp only [pc_fin_zero_apply, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]

open scoped Classical in
theorem pc_term_integrable (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψ : IsGlobalAddChar F ψ)
    (kdat : {w : InfinitePlace F // w.IsReal} → ℤ) (τr : {w : InfinitePlace F // w.IsReal} → ℝ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ) (τc : {w : InfinitePlace F // w.IsComplex} → ℝ)
    (habm : ∀ w : {w : InfinitePlace F // w.IsComplex}, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2)
    (Wr : {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ)
    (hWr : ∀ (i : {w : InfinitePlace F // w.IsReal}) (s : ℂ) (x : ℝ),
      Wr i s x = ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τr i : ℝ) : ℂ) * Complex.I / 2)))
    (Wc : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ)
    (hWc : ∀ (w : {w : InfinitePlace F // w.IsComplex}) (s z : ℂ),
      Wc w s z = z ^ (abm w).1 * (starRingEnd ℂ) z ^ (abm w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + ((abm w).2.2 : ℂ) / 2 + ((τc w : ℝ) : ℂ) * Complex.I / 2)))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχϖ : ∀ v, ‖((χv v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χv v u = 1)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (hcS : ∀ v ∈ S, 1 ≤ cS v)
    (hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v), χv v u = 1)
    (mS : ℕ) (hmS : 1 ≤ mS)
    (A₀ B : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hA₀ : ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A₀ v y = A₀ v x)
    (hB : ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B v y = B v x)
    (s : ℂ) (hs : 1 < s.re)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hoff : ∀ v ∉ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
    (hon : ∀ v ∈ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A₀ v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B v y⁻¹) x)
    (c : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) (u ξ' : AdeleRing (𝓞 F) F) :
    Integrable (fun y => c * pc_tensor F (fun i => Wr i s) (fun w => Wc w s) h (a • (y + u)) * ψ (-(ξ' * y)))
      (adelicAddHaar (𝓞 F) F) := by
  let : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := pc_finBorel F
  have : BorelSpace (FiniteAdeleRing (𝓞 F) F) := pc_finBorelSpace F
  have : (pc_finHaar F).IsAddHaarMeasure := pc_isAddHaarMeasure_finHaar F
  have hT : Integrable (fun y => pc_tensor F (fun i => Wr i s) (fun w => Wc w s) h (a • (y + u)))
      (adelicAddHaar (𝓞 F) F) :=
    pc_integrable_affine (fun p : mixedEmbedding.mixedSpace F =>
        (∏ i : {w : InfinitePlace F // w.IsReal}, Wr i s (p.1 i))
          * ∏ w : {w : InfinitePlace F // w.IsComplex}, Wc w s (p.2 w))
      (pc_integrable_arch kdat τr abm τc habm Wr hWr Wc hWc s hs) (pc_finHaar F)
      (fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v))
      (pc_integrable_finprod F (pc_finHaar F) S χv ϖ hϖ hχϖ hχS ψv nψ hψv cS hcS hχc mS hmS A₀ B hA₀ hB s hs h hoff
        hon) a u
  have hψc : Continuous fun y : AdeleRing (𝓞 F) F => ψ (-(ξ' * y)) :=
    hψ.continuous.comp (continuous_const.mul continuous_id).neg
  have hTψ : Integrable (fun y => pc_tensor F (fun i => Wr i s) (fun w => Wc w s) h (a • (y + u)) * ψ (-(ξ' * y)))
      (adelicAddHaar (𝓞 F) F) :=
    hT.mul_bdd (c := 1) hψc.aestronglyMeasurable
      (MeasureTheory.ae_of_all _ fun y => (AutomorphicForm.norm_apply_eq_one_of_isGlobalAddChar F hψ _).le)
  exact (hTψ.const_mul c).congr (MeasureTheory.ae_of_all _ fun y => (mul_assoc _ _ _).symm)

open scoped Classical in

theorem pc_term_value (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hψarch : ∀ p : mixedEmbedding.mixedSpace F,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
              Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
              Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχϖ : ∀ v, ‖((χv v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (hχS : ∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χv v u = 1)
    (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
    (hnψ : ∀ v ∉ S, nψ v = 0)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (hcS : ∀ v ∈ S, 1 ≤ cS v)
    (hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v), χv v u = 1)
    (mS : ℕ) (hmS : 1 ≤ mS)
    (A₀ B : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hA₀ : ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A₀ v y = A₀ v x)
    (hB : ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B v y = B v x)
    (s : ℂ) (hs : 1 < s.re)
    (h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hoff : ∀ v ∉ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
    (hon : ∀ v ∈ S, ∀ x : v.adicCompletion F,
      h v x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A₀ v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (χv v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B v y⁻¹) x)
    (Wr' : {w : InfinitePlace F // w.IsReal} → ℝ → ℂ) (Wc' : {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ)
    (c : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) (u ξ' : AdeleRing (𝓞 F) F) (U : (AdeleRing (𝓞 F) F)ˣ)
    (hU : (U : AdeleRing (𝓞 F) F) = ξ' * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) :
    ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)⁻¹
        * ∫ y, c * pc_tensor F Wr' Wc' h (a • (y + u)) * ψ (-(ξ' * y)) ∂(adelicAddHaar (𝓞 F) F)
      = c * ((((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
            * ((((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (ξ' * u)))
        * ((∏ i : {w : InfinitePlace F // w.IsReal}, ∫ x : ℝ, Wr' i x
            * Complex.exp (-(((2 * Real.pi * (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                (U : AdeleRing (𝓞 F) F).1).1 i)) * x : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex}, ∫ z : ℂ, Wc' w z
            * Complex.exp (-(((4 * Real.pi * ((-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                (U : AdeleRing (𝓞 F) F).1).2 w)) * z).re : ℝ) : ℂ) * Complex.I)))
        * ((∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pc_euler S χv ϖ v.1 s)
          * ∏ v ∈ S ∪ (pc_unit_fin_exp_finite U).toFinset,
              pc_corr F S χv ϖ ψv nψ cS mS A₀ B (U : AdeleRing (𝓞 F) F).2 v s) := by
  have := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  let : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := pc_finBorel F
  have : BorelSpace (FiniteAdeleRing (𝓞 F) F) := pc_finBorelSpace F
  have : (pc_finHaar F).IsAddHaarMeasure := pc_isAddHaarMeasure_finHaar F

  have ha : ∫ y, c * pc_tensor F Wr' Wc' h (a • (y + u)) * ψ (-(ξ' * y)) ∂(adelicAddHaar (𝓞 F) F)
      = c * ∫ y, pc_tensor F Wr' Wc' h (a • (y + u)) * ψ (-(ξ' * y)) ∂(adelicAddHaar (𝓞 F) F) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext y
    ring
  have hb : ∫ y, pc_tensor F Wr' Wc' h (a • (y + u)) * ψ (-(ξ' * y)) ∂(adelicAddHaar (𝓞 F) F)
      = (((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (ξ' * u)
        * fourierIntegral ψ (adelicAddHaar (𝓞 F) F) (pc_tensor F Wr' Wc' h) (U : AdeleRing (𝓞 F) F) := by
    rw [Piece.integral_smul_add_mul_addChar_neg_mul_eq F ψ (pc_tensor F Wr' Wc' h) a u ξ',
      pc_fourierIntegral_eq_integral_mul, hU]

  have hd : ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)⁻¹
      * fourierIntegral ψ (adelicAddHaar (𝓞 F) F) (pc_tensor F Wr' Wc' h) (U : AdeleRing (𝓞 F) F) = _ :=
    Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq F (adelicAddHaar (𝓞 F) F)
      (pc_finHaar F) ψ
      (fun p : mixedEmbedding.mixedSpace F =>
        (∏ i : {w : InfinitePlace F // w.IsReal}, Wr' i (p.1 i))
          * ∏ w : {w : InfinitePlace F // w.IsComplex}, Wc' w (p.2 w))
      (fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v : HeightOneSpectrum (𝓞 F), h v (x v)) (U : AdeleRing (𝓞 F) F)

  rw [pc_arch_value F ψ θr θc hψarch Wr' Wc'] at hd

  have hone : ∀ v ∉ S, ∀ y : v.adicCompletion F, y ∈ v.adicCompletionIntegers F → h v y = 1 :=
    fun v hv y hy => pc_hoff_one S χv s h hoff v hv y hy
  rw [pc_fin_fourier_eq F ψ ψv hψfin nψ hψv S hnψ h hone _ (pc_unit_fin_ne_zero U) (pc_unit_fin_exp_finite U)
      (pc_finHaar F),
    ← MeasureTheory.measureReal_def (μ := pc_finHaar F),
    pc_finite_value F S χv ϖ hϖ hχϖ hχS ψv nψ hψv hψv' hnψ cS hcS hχc mS hmS A₀ B hA₀ hB s hs h hoff hon _
      (pc_unit_fin_ne_zero U) (pc_unit_fin_exp_finite U)] at hd
  have hsplit : (∏' v : HeightOneSpectrum (𝓞 F), pc_euler S χv ϖ v s
        * pc_corr F S χv ϖ ψv nψ cS mS A₀ B (U : AdeleRing (𝓞 F) F).2 v s)
      = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pc_euler S χv ϖ v.1 s)
        * ∏ v ∈ S ∪ (pc_unit_fin_exp_finite U).toFinset,
            pc_corr F S χv ϖ ψv nψ cS mS A₀ B (U : AdeleRing (𝓞 F) F).2 v s :=
    EisensteinGeneral.WeylGlue.tprod_mul_eq_tprod_subtype_mul_prod S _ (fun v hv => pc_euler_eq_one_of_mem F S χv ϖ v hv s)
      (pc_multipliable_euler F S χv ϖ hχϖ s (by linarith)) _ _ (fun v hv => by
        rw [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
        exact pc_corr_eq_one F S χv ϖ ψv nψ cS mS A₀ B _ v hv.1 hv.2 s)
  rw [hsplit] at hd

  rw [ha, hb, show ((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)⁻¹
      * (c * ((((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (ξ' * u)
        * fourierIntegral ψ (adelicAddHaar (𝓞 F) F) (pc_tensor F Wr' Wc' h) (U : AdeleRing (𝓞 F) F)))
      = c * ((((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (ξ' * u))
        * (((adelicAddHaar (𝓞 F) F (adelicBox F)).toReal : ℂ)⁻¹
          * fourierIntegral ψ (adelicAddHaar (𝓞 F) F) (pc_tensor F Wr' Wc' h) (U : AdeleRing (𝓞 F) F)) by ring,
    hd]
  ring

section MajorantFinite

theorem pc_succ_le_two_pow (M : ℕ) : M + 1 ≤ 2 ^ M := by
  induction M with
  | zero => simp
  | succ M ih => rw [pow_succ]; omega

theorem pc_ram_norm_le' {N : ℕ} (hN : 1 ≤ N) (K : ℕ) {c₀ : ℂ} {c₀' : ℝ} (hc₀ : ‖c₀‖ ≤ c₀')
    {sh : ℕ → ℂ} {b d : ℝ} (hb : 0 ≤ b) (hd : 1 ≤ d) (hsh : ∀ k, 1 ≤ k → ‖sh k‖ ≤ b * d ^ k) {R : ℝ} {s : ℂ}
    (hs : ‖s‖ ≤ R) : ‖pc_ram N K c₀ sh s‖ ≤ c₀' + (K : ℝ) * (b * ((N : ℝ) ^ (2 * R + 1) * d) ^ K) := by
  have hR : (0 : ℝ) ≤ R := (norm_nonneg s).trans hs
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hb1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 * R + 1) * d :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN' (by positivity)) hd
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      ‖(((N : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k * sh k‖ ≤ b * ((N : ℝ) ^ (2 * R + 1) * d) ^ K := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
    rw [norm_mul, norm_pow]
    calc ‖((N : ℕ) : ℂ) ^ (-(2 * s + 1))‖ ^ k * ‖sh k‖
        ≤ ((N : ℝ) ^ (2 * R + 1)) ^ k * (b * d ^ k) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (pc_norm_cpow_neg_two_mul_add_one_le hN hs) k)
            (hsh k hk1) (norm_nonneg _) (by positivity)
      _ = b * ((N : ℝ) ^ (2 * R + 1) * d) ^ k := by rw [mul_pow]; ring
      _ ≤ b * ((N : ℝ) ^ (2 * R + 1) * d) ^ K :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 hkK) hb
  unfold pc_ram
  refine (norm_add_le _ _).trans (add_le_add hc₀ ?_)
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]

theorem pc_norm_corrOff_le {χϖ : ℂ} (hχ : ‖χϖ‖ = 1) {N : ℕ} (hN : 2 ≤ N) (e : ℤ) {R : ℝ} (k' : ℕ)
    (hk' : 2 * R ≤ k') {s : ℂ} (hs : ‖s‖ ≤ R) :
    ‖pc_corrOff χϖ N e s‖ ≤ ((N : ℝ) ^ (-e).toNat) ^ (k' + 1) := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  unfold pc_corrOff
  split_ifs with he
  · calc ‖pc_geom χϖ N (-e).toNat s‖ ≤ (((-e).toNat : ℝ) + 1) * ((N : ℝ) ^ (2 * R)) ^ (-e).toNat :=
          pc_geom_norm_le hχ hN1 (-e).toNat hs
      _ ≤ (N : ℝ) ^ (-e).toNat * ((N : ℝ) ^ k') ^ (-e).toNat := by
          refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
          · calc (((-e).toNat : ℝ) + 1) = (((-e).toNat + 1 : ℕ) : ℝ) := by push_cast; ring
              _ ≤ ((2 ^ (-e).toNat : ℕ) : ℝ) := by exact_mod_cast pc_succ_le_two_pow (-e).toNat
              _ = (2 : ℝ) ^ (-e).toNat := by push_cast; ring
              _ ≤ (N : ℝ) ^ (-e).toNat := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hN) _
          · refine pow_le_pow_left₀ (by positivity) ?_ _
            calc (N : ℝ) ^ (2 * R) ≤ (N : ℝ) ^ ((k' : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1' hk'
              _ = (N : ℝ) ^ k' := Real.rpow_natCast _ _
      _ = ((N : ℝ) ^ (-e).toNat) ^ (k' + 1) := by ring
  · rw [norm_zero]; positivity

theorem pc_exists_norm_corrOn_le {N : ℕ} (hN : 2 ≤ N) (n : ℤ) (c m : ℕ) {μ𝒪 : ℝ} (hμ : 0 < μ𝒪)
    (c₀' b d R : ℝ) (hc₀' : 0 ≤ c₀') (hb : 0 ≤ b) (hd : 1 ≤ d) (hR : 0 ≤ R) :
    ∃ E : ℝ, ∃ κ : ℕ, 0 ≤ E ∧ ∀ (e : ℤ) (c₀ : ℂ) (sh : ℕ → ℂ) (s : ℂ), ‖c₀‖ ≤ c₀' →
      (∀ k, 1 ≤ k → ‖sh k‖ ≤ b * d ^ k) → ‖s‖ ≤ R →
        ‖pc_corrOn N n c m e μ𝒪 c₀ sh s‖ ≤ E * ((N : ℝ) ^ (-e).toNat) ^ κ := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set D : ℝ := (N : ℝ) ^ (2 * R + 1) * d with hD
  have hD1 : 1 ≤ D := one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hN1' (by positivity)) hd
  obtain ⟨κ, hκ⟩ := pow_unbounded_of_one_lt (2 * D) (by norm_num : (1 : ℝ) < 2)
  have h2D : 2 * D ≤ (N : ℝ) ^ κ := hκ.le.trans (pow_le_pow_left₀ (by norm_num) hN2 κ)
  set K₀ : ℕ := m + n.toNat + c with hK₀
  refine ⟨μ𝒪⁻¹ * ((c₀' + b) * (2 * D) ^ K₀), κ, by positivity, fun e c₀ sh s hc₀ hsh hs => ?_⟩
  unfold pc_corrOn
  split_ifs with he
  · set K := (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat with hK
    have hKle : K ≤ K₀ + (-e).toNat := by
      rw [hK, hK₀]; omega
    have hram : ‖pc_ram N K c₀ sh s‖ ≤ c₀' + (K : ℝ) * (b * D ^ K) := pc_ram_norm_le' hN1 K hc₀ hb hd hsh hs
    have hK2 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast (Nat.le_succ K).trans (pc_succ_le_two_pow K)
    have h1 : (K : ℝ) * (b * D ^ K) ≤ b * (2 * D) ^ K := by
      calc (K : ℝ) * (b * D ^ K) = b * (K * D ^ K) := by ring
        _ ≤ b * (2 ^ K * D ^ K) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK2 (by positivity)) hb
        _ = b * (2 * D) ^ K := by ring
    have h1le : (1 : ℝ) ≤ (2 * D) ^ K := one_le_pow₀ (by linarith)
    have h2 : c₀' + b * (2 * D) ^ K ≤ (c₀' + b) * (2 * D) ^ K := by
      have h := mul_le_mul_of_nonneg_left h1le hc₀'
      rw [mul_one] at h
      linarith
    have h3 : (2 * D) ^ K ≤ (2 * D) ^ K₀ * ((N : ℝ) ^ (-e).toNat) ^ κ := by
      calc (2 * D) ^ K ≤ (2 * D) ^ (K₀ + (-e).toNat) := pow_le_pow_right₀ (by linarith) hKle
        _ = (2 * D) ^ K₀ * (2 * D) ^ (-e).toNat := pow_add _ _ _
        _ ≤ (2 * D) ^ K₀ * ((N : ℝ) ^ κ) ^ (-e).toNat :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2D _) (by positivity)
        _ = (2 * D) ^ K₀ * ((N : ℝ) ^ (-e).toNat) ^ κ := by ring
    calc ‖(μ𝒪 : ℂ)⁻¹ * pc_ram N K c₀ sh s‖ = μ𝒪⁻¹ * ‖pc_ram N K c₀ sh s‖ := by
          rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hμ.le]
      _ ≤ μ𝒪⁻¹ * ((c₀' + b) * (2 * D) ^ K₀ * ((N : ℝ) ^ (-e).toNat) ^ κ) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hμ.le)
          calc ‖pc_ram N K c₀ sh s‖ ≤ c₀' + (K : ℝ) * (b * D ^ K) := hram
            _ ≤ c₀' + b * (2 * D) ^ K := by linarith
            _ ≤ (c₀' + b) * (2 * D) ^ K := h2
            _ ≤ (c₀' + b) * ((2 * D) ^ K₀ * ((N : ℝ) ^ (-e).toNat) ^ κ) :=
                mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = _ := by ring
      _ = _ := by ring
  · rw [norm_zero]; positivity

variable {F : Type} [Field F] [NumberField F]

theorem pc_norm_integral_integers_le (v : HeightOneSpectrum (𝓞 F)) (A₀ : v.adicCompletion F → ℂ)
    (ψv : AddChar (v.adicCompletion F) ℂ) (hψv1 : ∀ y, ‖ψv y‖ = 1) (w : v.adicCompletion F) :
    ‖∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀ x * ψv (-(w * x))
          ∂(pc_locHaar F v)‖
      ≤ ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖A₀ x‖ ∂(pc_locHaar F v) := by
  let := pc_locBorel F v
  have := pc_locBorelSpace F v
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine setIntegral_congr_fun (EisensteinGeneral.FiniteAdelicFactorization.isOpen_adicCompletionIntegers F v).measurableSet fun x hx => ?_
  show ‖(v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀ x * ψv (-(w * x))‖ = ‖A₀ x‖
  rw [norm_mul, Set.indicator_of_mem hx, hψv1, mul_one]

theorem pc_valued_inv_pow_uniformizer {v : HeightOneSpectrum (𝓞 F)} {ϖ : (v.adicCompletion F)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℕ) :
    Valued.v (((ϖ : v.adicCompletion F) ^ k)⁻¹) = WithZero.exp (k : ℤ) := by
  rw [map_inv₀, pc_valued_pow_uniformizer hϖ k, ← WithZero.coe_inv, ← ofAdd_neg, neg_neg]
  rfl

theorem pc_measurableSet_shell {v : HeightOneSpectrum (𝓞 F)} [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] {ϖ : (v.adicCompletion F)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (k : ℕ) :
    MeasurableSet {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)} := by
  have hz := pc_valued_inv_pow_uniformizer hϖ k
  have hz0 : Valued.v (((ϖ : v.adicCompletion F) ^ k)⁻¹) ≠ 0 := by
    rw [hz]; exact WithZero.coe_ne_zero
  have hr : Valued.v.restrict (((ϖ : v.adicCompletion F) ^ k)⁻¹) ≠ 0 := fun h =>
    hz0 ((Valuation.restrict_eq_zero_iff _).mp h)
  have hset : {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)}
      = {x : v.adicCompletion F | Valued.v.restrict x = Valued.v.restrict (((ϖ : v.adicCompletion F) ^ k)⁻¹)} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Valuation.restrict_inj, hz]
  rw [hset]
  exact (Valued.isClopen_sphere (R := v.adicCompletion F) hr).isOpen.measurableSet

open scoped Pointwise in

theorem pc_modulus_le_one (v : HeightOneSpectrum (𝓞 F)) (u : v.adicCompletion F)
    (hu : Valued.v u ≤ 1) : (LanglandsTunnell.TateLocal.modulus u : ℝ) ≤ 1 := by
  let := pc_locBorel F v
  have := pc_locBorelSpace F v
  have := pc_isAddHaarMeasure_locHaar F v
  have : (pc_locHaar F v).Regular := by
    show (Measure.addHaar : Measure (v.adicCompletion F)).Regular
    infer_instance
  by_cases h0 : u = 0
  · rw [h0, LanglandsTunnell.TateLocal.modulus_zero]; simp
  rw [LanglandsTunnell.TateLocal.modulus_of_ne_zero h0]
  have hO0 : pc_locHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ 0 :=
    ((EisensteinGeneral.FiniteAdelicFactorization.isOpen_adicCompletionIntegers F v).measure_pos (pc_locHaar F v) ⟨0, Subring.zero_mem _⟩).ne'
  have hOtop : pc_locHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ :=
    (pc_isCompact_integers v).measure_lt_top.ne
  have hsub : (Units.mk0 u h0) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rintro _ ⟨y, hy, rfl⟩
    show (Units.mk0 u h0 : v.adicCompletion F) • y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
    rw [smul_eq_mul, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul]
    exact mul_le_one' hu ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hy)
  have h := distribHaarChar_mul (pc_locHaar F v) (Units.mk0 u h0)
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hle : (distribHaarChar (v.adicCompletion F) (Units.mk0 u h0) : ENNReal)
        * pc_locHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      ≤ 1 * pc_locHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rw [h, one_mul]; exact measure_mono hsub
  have h1 : (distribHaarChar (v.adicCompletion F) (Units.mk0 u h0) : ENNReal) ≤ 1 :=
    (ENNReal.mul_le_mul_iff_left hO0 hOtop).mp hle
  exact_mod_cast h1

open scoped Pointwise in

theorem pc_one_le_modulus_inv_uniformizer (v : HeightOneSpectrum (𝓞 F)) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) :
    (1 : ℝ) ≤ (LanglandsTunnell.TateLocal.modulus ((ϖ : v.adicCompletion F)⁻¹) : ℝ) := by
  let := pc_locBorel F v
  have := pc_locBorelSpace F v
  have := pc_isAddHaarMeasure_locHaar F v
  have : (pc_locHaar F v).Regular := by
    show (Measure.addHaar : Measure (v.adicCompletion F)).Regular
    infer_instance
  have h0 : (ϖ : v.adicCompletion F)⁻¹ ≠ 0 := inv_ne_zero ϖ.ne_zero
  rw [LanglandsTunnell.TateLocal.modulus_of_ne_zero h0]
  have hO0 : pc_locHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ 0 :=
    ((EisensteinGeneral.FiniteAdelicFactorization.isOpen_adicCompletionIntegers F v).measure_pos (pc_locHaar F v) ⟨0, Subring.zero_mem _⟩).ne'
  have hOtop : pc_locHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ :=
    (pc_isCompact_integers v).measure_lt_top.ne
  have hϖ1 : Valued.v (ϖ : v.adicCompletion F) ≤ 1 := by
    rw [hϖ, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]; omega
  have hsub : (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      ⊆ (Units.mk0 _ h0) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro y hy
    refine ⟨(ϖ : v.adicCompletion F) * y, ?_, ?_⟩
    · rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul]
      exact mul_le_one' hϖ1 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hy)
    · show (Units.mk0 _ h0 : v.adicCompletion F) • ((ϖ : v.adicCompletion F) * y) = y
      rw [smul_eq_mul, Units.val_mk0, ← mul_assoc, inv_mul_cancel₀ ϖ.ne_zero, one_mul]
  have h := distribHaarChar_mul (pc_locHaar F v) (Units.mk0 _ h0)
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hle : 1 * pc_locHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      ≤ (distribHaarChar (v.adicCompletion F) (Units.mk0 _ h0) : ENNReal)
        * pc_locHaar F v (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    rw [h, one_mul]; exact measure_mono hsub
  have h1 : (1 : ENNReal) ≤ (distribHaarChar (v.adicCompletion F) (Units.mk0 _ h0) : ENNReal) :=
    (ENNReal.mul_le_mul_iff_left hO0 hOtop).mp hle
  exact_mod_cast h1

theorem pc_modulus_le_pow (v : HeightOneSpectrum (𝓞 F)) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) (x : v.adicCompletion F) (k : ℕ)
    (hx : Valued.v x = WithZero.exp (k : ℤ)) :
    (LanglandsTunnell.TateLocal.modulus x : ℝ)
      ≤ (LanglandsTunnell.TateLocal.modulus ((ϖ : v.adicCompletion F)⁻¹) : ℝ) ^ k := by
  have hpow : ∀ j : ℕ, LanglandsTunnell.TateLocal.modulus (((ϖ : v.adicCompletion F)⁻¹) ^ j)
      = LanglandsTunnell.TateLocal.modulus ((ϖ : v.adicCompletion F)⁻¹) ^ j := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, LanglandsTunnell.TateLocal.modulus_one]
    | succ j ih => rw [pow_succ, pow_succ, LanglandsTunnell.TateLocal.modulus_mul, ih]
  have hx' : x = (x * (ϖ : v.adicCompletion F) ^ k) * ((ϖ : v.adicCompletion F)⁻¹) ^ k := by
    rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero k ϖ.ne_zero), mul_one]
  have hu : Valued.v (x * (ϖ : v.adicCompletion F) ^ k) ≤ 1 := by
    rw [map_mul, hx, pc_valued_pow_uniformizer hϖ k]
    show ((Multiplicative.ofAdd (k : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      * (Multiplicative.ofAdd (-(k : ℤ)) : Multiplicative ℤ) ≤ 1
    rw [← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_add, ← ofAdd_zero,
      Multiplicative.ofAdd_le]
    omega
  calc (LanglandsTunnell.TateLocal.modulus x : ℝ)
      = (LanglandsTunnell.TateLocal.modulus (x * (ϖ : v.adicCompletion F) ^ k) : ℝ)
          * (LanglandsTunnell.TateLocal.modulus ((ϖ : v.adicCompletion F)⁻¹) : ℝ) ^ k := by
        conv_lhs => rw [hx']
        rw [LanglandsTunnell.TateLocal.modulus_mul, hpow]; push_cast; ring
    _ ≤ 1 * (LanglandsTunnell.TateLocal.modulus ((ϖ : v.adicCompletion F)⁻¹) : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (pc_modulus_le_one v _ hu) (by positivity)
    _ = _ := one_mul _

theorem pc_norm_shell_le (v : HeightOneSpectrum (𝓞 F)) (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ) (A₀ B : v.adicCompletion F → ℂ)
    (ψv : AddChar (v.adicCompletion F) ℂ) (hψv1 : ∀ y, ‖ψv y‖ = 1)
    (hint : Integrable (fun x => (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * (1 : ℂ) + 1)) * B y⁻¹) x)
          * ψv (-(0 * x)))) (pc_locHaar F v))
    (w : v.adicCompletion F) (k : ℕ) (hk : 1 ≤ k) :
    ‖∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
        LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψv (-(w * x)) ∂(pc_locHaar F v)‖
      ≤ (∫ x, ‖((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * (1 : ℂ) + 1)) * B y⁻¹) x)
          * ψv (-(0 * x))‖ ∂(pc_locHaar F v))
        * ((LanglandsTunnell.TateLocal.modulus ((ϖ : v.adicCompletion F)⁻¹) : ℝ) ^ 3) ^ k := by
  let := pc_locBorel F v
  have := pc_locBorelSpace F v
  have := pc_isAddHaarMeasure_locHaar F v
  set d : ℝ := (LanglandsTunnell.TateLocal.modulus ((ϖ : v.adicCompletion F)⁻¹) : ℝ) with hd
  set I₁ : v.adicCompletion F → ℂ := fun x => (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * (1 : ℂ) + 1)) * B y⁻¹) x)
          * ψv (-(0 * x))) with hI₁
  set g : v.adicCompletion F → ℂ := fun x =>
    LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψv (-(w * x)) with hg
  set T : Set (v.adicCompletion F) := {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)} with hT
  have hTmeas : MeasurableSet T := pc_measurableSet_shell hϖ k
  have hIpos : 0 ≤ ∫ x, ‖I₁ x‖ ∂(pc_locHaar F v) := integral_nonneg fun x => norm_nonneg _
  have hd1 : 1 ≤ d := pc_one_le_modulus_inv_uniformizer v ϖ hϖ

  have hpt : ∀ x ∈ T, ‖g x‖ ≤ ‖I₁ x‖ * (d ^ 3) ^ k := by
    intro x hx
    rw [hT, Set.mem_ofPred_eq] at hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, map_zero] at hx; exact WithZero.coe_ne_zero hx.symm
    have hxO : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, hx, not_le, ← WithZero.exp_zero,
        WithZero.exp_lt_exp]
      exact_mod_cast hk
    have hmpos : 0 < (LanglandsTunnell.TateLocal.modulus x : ℝ) := by
      exact_mod_cast LanglandsTunnell.TateLocal.modulus_pos hx0
    have hm3 : ‖((LanglandsTunnell.TateLocal.modulus x : ℝ) : ℂ) ^ (-(2 * (1 : ℂ) + 1))‖
        = (LanglandsTunnell.TateLocal.modulus x : ℝ) ^ (-(3 : ℝ)) := by
      have h3 : (-(2 * (1 : ℂ) + 1)) = ((-3 : ℝ) : ℂ) := by push_cast; ring
      rw [h3, Complex.norm_cpow_eq_rpow_re_of_pos hmpos, Complex.ofReal_re]
    have hI₁x : ‖I₁ x‖ = ‖LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹‖
        * (LanglandsTunnell.TateLocal.modulus x : ℝ) ^ (-(3 : ℝ)) := by
      rw [hI₁]
      show ‖((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A₀) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * (1 : ℂ) + 1)) * B y⁻¹) x)
          * ψv (-(0 * x))‖ = _
      rw [Set.indicator_of_notMem hxO, Set.indicator_of_mem (Set.mem_compl hxO), zero_add, zero_mul, neg_zero,
        AddChar.map_zero_eq_one, mul_one, norm_mul, norm_mul, hm3, norm_mul]
      ring
    have hgx : ‖g x‖ = ‖LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹‖ := by
      rw [hg]
      show ‖LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψv (-(w * x))‖ = _
      rw [norm_mul, hψv1, mul_one]
    have hmk : (LanglandsTunnell.TateLocal.modulus x : ℝ) ^ 3 ≤ (d ^ 3) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact pow_le_pow_left₀ hmpos.le (pc_modulus_le_pow v ϖ hϖ x k hx) 3
    calc ‖g x‖ = ‖I₁ x‖ * (LanglandsTunnell.TateLocal.modulus x : ℝ) ^ 3 := by
          rw [hgx, hI₁x, mul_assoc, ← Real.rpow_natCast _ 3, ← Real.rpow_add hmpos]
          norm_num
      _ ≤ ‖I₁ x‖ * (d ^ 3) ^ k := mul_le_mul_of_nonneg_left hmk (norm_nonneg _)
  by_cases hgi : IntegrableOn g T (pc_locHaar F v)
  · calc ‖∫ x in T, g x ∂(pc_locHaar F v)‖ ≤ ∫ x in T, ‖g x‖ ∂(pc_locHaar F v) := norm_integral_le_integral_norm _
      _ ≤ ∫ x in T, ‖I₁ x‖ * (d ^ 3) ^ k ∂(pc_locHaar F v) :=
          setIntegral_mono_on hgi.norm (hint.norm.mul_const _).integrableOn hTmeas hpt
      _ ≤ ∫ x, ‖I₁ x‖ * (d ^ 3) ^ k ∂(pc_locHaar F v) :=
          setIntegral_le_integral (hint.norm.mul_const _) (ae_of_all _ fun x => by positivity)
      _ = (∫ x, ‖I₁ x‖ ∂(pc_locHaar F v)) * (d ^ 3) ^ k := integral_mul_const _ _
  · rw [integral_undef hgi, norm_zero]
    positivity

end MajorantFinite

section MajorantBundle

variable {F : Type} [Field F] [NumberField F]

private theorem pc_exp_mul {v : HeightOneSpectrum (𝓞 F)} {x y : v.adicCompletion F} (hx : x ≠ 0) (hy : y ≠ 0) :
    pc_exp (x * y) = pc_exp x + pc_exp y := by
  unfold pc_exp
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]

private theorem pc_coe_ne_zero (v : HeightOneSpectrum (𝓞 F)) {ξ : F} (hξ : ξ ≠ 0) : (ξ : v.adicCompletion F) ≠ 0 := by
  have h : Valued.v (ξ : v.adicCompletion F) ≠ 0 := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (Valuation.ne_zero_iff _).mpr hξ
  exact (Valuation.ne_zero_iff _).mp h

private theorem pc_valuation_eq_exp (v : HeightOneSpectrum (𝓞 F)) {ξ : F} (hξ : ξ ≠ 0) :
    v.valuation F ξ = WithZero.exp (pc_exp (ξ : v.adicCompletion F)) := by
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ξ]
  exact pc_valued_eq_exp (pc_coe_ne_zero v hξ)

private theorem pc_freq_snd_apply (a : (AdeleRing (𝓞 F) F)ˣ) (ξ : {ξ : F // ξ ≠ 0}) (v : HeightOneSpectrum (𝓞 F)) :
    ((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 ξ.1 ξ.2) * a⁻¹ :
        (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v
      = (ξ.1 : v.adicCompletion F) * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v := by
  rfl

private theorem pc_exp_freq (a : (AdeleRing (𝓞 F) F)ˣ) (ξ : {ξ : F // ξ ≠ 0}) (v : HeightOneSpectrum (𝓞 F)) :
    pc_exp (((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 ξ.1 ξ.2) * a⁻¹ :
        (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v)
      = pc_exp (ξ.1 : v.adicCompletion F) + pc_exp (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) := by
  rw [pc_freq_snd_apply, pc_exp_mul (pc_coe_ne_zero v ξ.2) (pc_unit_fin_ne_zero a⁻¹ v)]

open scoped Classical in

private theorem pc_prod_corr_eq_zero (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χv : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ →* ℂˣ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (mS : ℕ)
    (A₀ B : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (U : (AdeleRing (𝓞 F) F)ˣ) (v₀ : HeightOneSpectrum (𝓞 F))
    (h : (v₀ ∈ S ∧ nψ v₀ + ((max mS (cS v₀) : ℕ) : ℤ) < pc_exp ((U : AdeleRing (𝓞 F) F).2 v₀))
      ∨ (v₀ ∉ S ∧ 0 < pc_exp ((U : AdeleRing (𝓞 F) F).2 v₀))) (s : ℂ) :
    ∏ v ∈ S ∪ (pc_unit_fin_exp_finite U).toFinset,
      pc_corr F S χv ϖ ψv nψ cS mS A₀ B ((U : AdeleRing (𝓞 F) F).2) v s = 0 := by
  have hmem : v₀ ∈ S ∪ (pc_unit_fin_exp_finite U).toFinset := by
    rcases h with ⟨hS, _⟩ | ⟨_, hpos⟩
    · exact Finset.mem_union_left _ hS
    · refine Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr ?_)
      rw [Set.mem_ofPred_eq]
      exact ne_of_gt hpos
  refine Finset.prod_eq_zero hmem ?_
  unfold pc_corr
  rcases h with ⟨hS, hlt⟩ | ⟨hS, hpos⟩
  · rw [ite_eq_left hS]
    unfold pc_corrOn
    rw [ite_eq_right (not_le.mpr hlt)]
  · rw [ite_eq_right hS]
    unfold pc_corrOff
    rw [ite_eq_right (not_le.mpr hpos)]

open scoped Classical in

private theorem pc_finite_half
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ) (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (hψv1 : ∀ (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F), ‖ψv v y‖ = 1)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (hχϖ : ∀ v, ‖((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)‖ = 1)
    (cS : HeightOneSpectrum (𝓞 F) → ℕ) (hcS : ∀ v ∈ S, 1 ≤ cS v)
    (hχc : ∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v),
      NumberField.TateGlobal.localChar χ v u = 1)
    (mS : ℕ) (hmS : 1 ≤ mS) (n : ℕ)
    (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
    (hA : ∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A j v y = A j v x)
    (hB : ∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B j v y = B j v x)
    (a : (AdeleRing (𝓞 F) F)ˣ) (R : ℝ) :
    ∃ (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) (P : ℝ) (k : ℕ),
      (∀ (j : Fin n) (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ξ.1 ∉ I →
        ∏ v ∈ S ∪ (pc_unit_fin_exp_finite (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom
            (Units.mk0 ξ.1 ξ.2) * a⁻¹)).toFinset,
          pc_corr F S (NumberField.TateGlobal.localChar χ) ϖ ψv nψ cS mS (A j) (B j)
            ((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 ξ.1 ξ.2) * a⁻¹ :
              (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v s = 0) ∧
      (∀ (j : Fin n) (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R → ξ.1 ∈ I →
        ‖∏ v ∈ S ∪ (pc_unit_fin_exp_finite (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom
            (Units.mk0 ξ.1 ξ.2) * a⁻¹)).toFinset,
          pc_corr F S (NumberField.TateGlobal.localChar χ) ϖ ψv nψ cS mS (A j) (B j)
            ((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 ξ.1 ξ.2) * a⁻¹ :
              (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v s‖
          ≤ P * (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ k) := by

  have hb0 : ∀ v : HeightOneSpectrum (𝓞 F), ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ≠ 0 :=
    fun v => pc_unit_fin_ne_zero a⁻¹ v

  set Nf : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    (if v ∈ S then nψ v + ((max mS (cS v) : ℕ) : ℤ) else 0)
      - pc_exp (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) with hNf
  have hNfin : (Function.support Nf).Finite := by
    refine (S.finite_toSet.union (pc_unit_fin_exp_finite a⁻¹)).subset fun v hv => ?_
    by_contra hv'
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, not_or, not_not] at hv'
    apply hv
    show Nf v = 0
    simp only [hNf]
    rw [ite_eq_right hv'.1, hv'.2, sub_zero]
  obtain ⟨I, -, hI⟩ := EisensteinGeneral.WeylGlue.exists_fractionalIdeal_ne_zero_mem_of_forall_valued_le F Nf hNfin

  set R' : ℝ := max R 0 with hR'
  have hR'0 : 0 ≤ R' := le_max_right _ _

  have hN2 : ∀ v : HeightOneSpectrum (𝓞 F), 2 ≤ Ideal.absNorm v.asIdeal := fun v => pc_one_lt_absNorm F v
  have hN1' : ∀ v : HeightOneSpectrum (𝓞 F), (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℕ) := fun v => by
    exact_mod_cast le_trans (by norm_num) (hN2 v)
  have hμ : ∀ v : HeightOneSpectrum (𝓞 F),
      0 < (pc_locHaar F v).real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    let := pc_locBorel F v
    have := pc_locBorelSpace F v
    have := pc_isAddHaarMeasure_locHaar F v
    exact pc_measureReal_integers_pos F v (pc_locHaar F v)
  set c₀' : Fin n → HeightOneSpectrum (𝓞 F) → ℝ := fun j v =>
    ∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖A j v x‖ ∂(pc_locHaar F v) with hc₀'
  have hc₀'0 : ∀ j v, 0 ≤ c₀' j v := fun j v => integral_nonneg fun x => norm_nonneg _
  set bI : Fin n → HeightOneSpectrum (𝓞 F) → ℝ := fun j v =>
    ∫ x, ‖((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator
          ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * (1 : ℂ) + 1)) * B j v y⁻¹) x)
          * ψv v (-(0 * x))‖ ∂(pc_locHaar F v) with hbI
  have hbI0 : ∀ j v, 0 ≤ bI j v := fun j v => integral_nonneg fun x => norm_nonneg _
  set d : HeightOneSpectrum (𝓞 F) → ℝ := fun v =>
    (LanglandsTunnell.TateLocal.modulus ((ϖ v : v.adicCompletion F)⁻¹) : ℝ) ^ 3 with hd
  have hd1 : ∀ v, 1 ≤ d v := fun v => one_le_pow₀ (pc_one_le_modulus_inv_uniformizer v (ϖ v) (hϖ v))
  choose E κ hE0 hE using fun (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) =>
    pc_exists_norm_corrOn_le (hN2 v) (nψ v) (cS v) mS (hμ v) (c₀' j v) (bI j v) (d v) R'
      (hc₀'0 j v) (hbI0 j v) (hd1 v) hR'0

  set k' : ℕ := ⌈2 * R'⌉₊ with hk'
  have hk'R : 2 * R' ≤ k' := Nat.le_ceil _
  set kk : ℕ := max (k' + 1) ((Finset.univ ×ˢ S).sup fun p : Fin n × HeightOneSpectrum (𝓞 F) => κ p.1 p.2)
    with hkk
  have hκle : ∀ j, ∀ v ∈ S, κ j v ≤ kk := by
    intro j v hv
    have h1 : (fun p : Fin n × HeightOneSpectrum (𝓞 F) => κ p.1 p.2) (j, v)
        ≤ (Finset.univ ×ˢ S).sup (fun p : Fin n × HeightOneSpectrum (𝓞 F) => κ p.1 p.2) :=
      Finset.le_sup (f := fun p : Fin n × HeightOneSpectrum (𝓞 F) => κ p.1 p.2)
        (Finset.mem_product.mpr ⟨Finset.mem_univ j, hv⟩)
    exact h1.trans (le_max_right _ _)
  set G : Fin n → ℝ := fun j => ∏ v ∈ S, max 1 (E j v) with hG
  have hG0 : ∀ j, 0 ≤ G j := fun j => Finset.prod_nonneg fun v _ => by positivity

  set Cb : ℝ := ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)
    ^ (-(pc_exp (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v))).toNat with hCb
  have hCb0 : 0 ≤ Cb := finprod_nonneg fun v => by positivity
  obtain ⟨c₄, hc₄, hS4⟩ := EisensteinGeneral.WeylGlue.exists_pos_finprod_absNorm_pow_toNat_neg_le_mul_abs_norm F I
  refine ⟨I, (∑ j : Fin n, G j) * (c₄ * Cb) ^ kk, kk, fun j ξ s hξ => ?_, fun j ξ s hs hξI => ?_⟩
  ·
    obtain ⟨v₀, hv₀⟩ : ∃ v₀ : HeightOneSpectrum (𝓞 F), ¬ v₀.valuation F ξ.1 ≤ WithZero.exp (Nf v₀) :=
      not_forall.mp fun hall => hξ (hI ξ.1 hall)
    rw [not_le, pc_valuation_eq_exp v₀ ξ.2, WithZero.exp_lt_exp] at hv₀
    refine pc_prod_corr_eq_zero S _ ϖ ψv nψ cS mS (A j) (B j) _ v₀ ?_ s
    rw [pc_exp_freq]
    by_cases hS : v₀ ∈ S
    · left
      refine ⟨hS, ?_⟩
      have h := hv₀
      simp only [hNf, ite_eq_left hS] at h
      linarith
    · right
      refine ⟨hS, ?_⟩
      have h := hv₀
      simp only [hNf, ite_eq_right hS] at h
      linarith
  ·
    have hsR' : ‖s‖ ≤ R' := hs.trans (le_max_left _ _)
    set U : (AdeleRing (𝓞 F) F)ˣ :=
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 ξ.1 ξ.2) * a⁻¹ with hU
    set w : FiniteAdeleRing (𝓞 F) F := (U : AdeleRing (𝓞 F) F).2 with hw
    set T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ (pc_unit_fin_exp_finite U).toFinset with hT
    have hw0 : ∀ v, w v ≠ 0 := fun v => pc_unit_fin_ne_zero U v
    have hwexp : ∀ v, pc_exp (w v) = pc_exp (ξ.1 : v.adicCompletion F)
        + pc_exp (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) := fun v => pc_exp_freq a ξ v

    have hplace : ∀ v ∈ T, ‖pc_corr F S (NumberField.TateGlobal.localChar χ) ϖ ψv nψ cS mS (A j) (B j) w v s‖
        ≤ (if v ∈ S then max 1 (E j v) else 1)
          * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat) ^ kk := by
      intro v _
      have hpow1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat := one_le_pow₀ (hN1' v)
      unfold pc_corr
      split_ifs with hvS
      ·
        let := pc_locBorel F v
        have := pc_locBorelSpace F v
        have := pc_isAddHaarMeasure_locHaar F v
        have hc₀ := pc_norm_integral_integers_le v (A j v) (ψv v) (hψv1 v) (w v)
        have hAint : IntegrableOn ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v))
            (v.adicCompletionIntegers F : Set (v.adicCompletion F)) (pc_locHaar F v) :=
          pc_integrableOn_integers_of_depth_const (pc_locHaar F v) (hϖ v) mS
            (pc_indicator_depth_const hmS (hA j v hvS))
        have hs1 : ‖((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * (1 : ℂ)))‖ < 1 :=
          pc_norm_mul_cpow_lt_one_nat (hχϖ v) (hN2 v) (by norm_num)
        have hint := LocalRam.integrable_twisted_smooth F v (pc_locHaar F v) (ϖ v) (hϖ v)
          (NumberField.TateGlobal.localChar χ v) (cS v) (hcS v hvS) (hχc v hvS) mS hmS _ hAint (B j v)
          (hB j v hvS) 1 hs1 (ψv v) (nψ v) (hψv v) 0
        have hsh := fun (k : ℕ) (hk : 1 ≤ k) =>
          pc_norm_shell_le v (ϖ v) (hϖ v) (NumberField.TateGlobal.localChar χ v) (A j v) (B j v) (ψv v) (hψv1 v)
            hint (w v) k hk
        calc _ ≤ E j v * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat) ^ κ j v :=
              hE j v (pc_exp (w v)) _ _ s hc₀ hsh hsR'
          _ ≤ max 1 (E j v) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat) ^ kk :=
              mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hpow1 (hκle j v hvS)) (by positivity)
                (by positivity)
          _ = _ := rfl
      ·
        calc _ ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat) ^ (k' + 1) :=
              pc_norm_corrOff_le (hχϖ v) (hN2 v) _ k' hk'R hsR'
          _ ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat) ^ kk :=
              pow_le_pow_right₀ hpow1 (le_max_left _ _)
          _ = _ := (one_mul _).symm

    have hGprod : ∏ v ∈ T, (if v ∈ S then max 1 (E j v) else 1) = G j := by
      have hTS : T = S ∪ ((pc_unit_fin_exp_finite U).toFinset \ S) := by
        rw [hT, Finset.union_sdiff_self_eq_union]
      rw [hTS, Finset.prod_union Finset.disjoint_sdiff, hG]
      have h1 : ∏ v ∈ (pc_unit_fin_exp_finite U).toFinset \ S, (if v ∈ S then max 1 (E j v) else (1 : ℝ)) = 1 :=
        Finset.prod_eq_one fun v hv => by rw [ite_eq_right (Finset.mem_sdiff.mp hv).2]
      rw [h1, mul_one]
      exact Finset.prod_congr rfl fun v hv => by rw [ite_eq_left hv]

    have hfin : ∏ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat := by
      refine (finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_).symm
      rw [Finset.mem_coe, hT, Finset.mem_union]
      right
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      intro h0
      apply hv
      show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat = 1
      rw [h0, neg_zero, Int.toNat_zero, pow_zero]

    have hsplit : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat
        ≤ (∏ᶠ v : HeightOneSpectrum (𝓞 F),
              ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (ξ.1 : v.adicCompletion F))).toNat) * Cb := by
      set T₂ : Finset (HeightOneSpectrum (𝓞 F)) :=
        (pc_unit_fin_exp_finite (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom
          (Units.mk0 ξ.1 ξ.2))).toFinset ∪ (pc_unit_fin_exp_finite a⁻¹).toFinset with hT₂
      have hξexp : ∀ v, pc_exp (((Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 ξ.1 ξ.2)
          : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) = pc_exp (ξ.1 : v.adicCompletion F) := fun v => rfl
      have hmem : ∀ v, v ∉ T₂ → pc_exp (ξ.1 : v.adicCompletion F) = 0
          ∧ pc_exp (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v) = 0 := by
        intro v hv
        rw [hT₂, Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
          Set.mem_ofPred_eq, not_not, not_not, hξexp] at hv
        exact hv
      have e1 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat
          = ∏ v ∈ T₂, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat := by
        refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
        by_contra hv'
        apply hv
        show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat = 1
        rw [hwexp, (hmem v hv').1, (hmem v hv').2, add_zero, neg_zero, Int.toNat_zero, pow_zero]
      have e2 : ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (ξ.1 : v.adicCompletion F))).toNat
          = ∏ v ∈ T₂, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (ξ.1 : v.adicCompletion F))).toNat := by
        refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
        by_contra hv'
        apply hv
        show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (ξ.1 : v.adicCompletion F))).toNat = 1
        rw [(hmem v hv').1, neg_zero, Int.toNat_zero, pow_zero]
      have e3 : Cb = ∏ v ∈ T₂, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)
          ^ (-(pc_exp (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v))).toNat := by
        refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
        by_contra hv'
        apply hv
        show ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)
          ^ (-(pc_exp (((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v))).toNat = 1
        rw [(hmem v hv').2, neg_zero, Int.toNat_zero, pow_zero]
      rw [e1, e2, e3, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod₀ (fun v _ => by positivity) fun v _ => ?_
      rw [← pow_add]
      refine pow_le_pow_right₀ (hN1' v) ?_
      rw [hwexp]
      omega

    have hS4' := hS4 ξ.1 hξI ξ.2 (fun v => pc_exp (ξ.1 : v.adicCompletion F)) fun v => pc_valuation_eq_exp v ξ.2

    have hNξ0 : 0 ≤ ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ) := by exact_mod_cast abs_nonneg _
    calc ‖∏ v ∈ T, pc_corr F S (NumberField.TateGlobal.localChar χ) ϖ ψv nψ cS mS (A j) (B j) w v s‖
        = ∏ v ∈ T, ‖pc_corr F S (NumberField.TateGlobal.localChar χ) ϖ ψv nψ cS mS (A j) (B j) w v s‖ :=
          norm_prod _ _
      _ ≤ ∏ v ∈ T, (if v ∈ S then max 1 (E j v) else 1)
            * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat) ^ kk :=
          Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) hplace
      _ = G j * (∏ᶠ v : HeightOneSpectrum (𝓞 F),
            ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(pc_exp (w v))).toNat) ^ kk := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, hGprod, hfin]
      _ ≤ G j * ((c₄ * ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) * Cb) ^ kk := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (finprod_nonneg fun v => by positivity)
            (hsplit.trans (mul_le_mul_of_nonneg_right hS4' hCb0)) kk) (hG0 j)
      _ ≤ G j * ((c₄ * Cb) * max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ kk := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ kk) (hG0 j)
          calc c₄ * ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ) * Cb = (c₄ * Cb) * ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ) := by ring
            _ ≤ (c₄ * Cb) * max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ) :=
                mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ = G j * (c₄ * Cb) ^ kk * (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ kk := by rw [mul_pow]; ring
      _ ≤ (∑ j' : Fin n, G j') * (c₄ * Cb) ^ kk * (max 1 ((|Algebra.norm ℚ ξ.1| : ℚ) : ℝ)) ^ kk := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)
          exact Finset.single_le_sum (fun j' _ => hG0 j') (Finset.mem_univ j)

end MajorantBundle

end EisensteinGeneral.Piece

end PieceLayer


section Solution

open NumberField IsDedekindDomain AutomorphicForm MeasureTheory
open NumberField.InfinitePlace NumberField.AdelicBox NumberField.AdelicFourier
  NumberField.AdelicHaar
open scoped NNReal
open EisensteinGeneral EisensteinGeneral.Piece EisensteinGeneral.WeylGlue

open scoped Classical in
theorem EisensteinGeneral.Piece.exists_entire_partialEulerProduct_mul_eq_whittakerCoefficient_and_summable_majorant
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hψ : IsGlobalAddChar F ψ)
    (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
    (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
    (hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
      ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
    (hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
    (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
    (hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
    (hθc : ∀ w, θc w ≠ 0)
    (hψarch : ∀ p : mixedEmbedding.mixedSpace F,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
              Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
          * ∏ w : {w : InfinitePlace F // w.IsComplex},
              Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∀ s, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ s))
    (g : AdelicGL2 (𝓞 F) F)
    (D : FactorizationDatum F ψv nψ χ ϖ Ψ g S) :
    ∃ Q : {ξ : F // ξ ≠ 0} → ℂ → ℂ,
      (∀ ξ : {ξ : F // ξ ≠ 0}, Differentiable ℂ (Q ξ)) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), 1 < s.re →
        whittakerCoefficient F (productionPins F) ψ
            (fun g' => Ψ s g' + ∑' ξ' : F, Ψ s (adelicWeyl (𝓞 F) F
                * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g
          = (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Q ξ s) ∧
      (∀ R : ℝ, ∃ M : {ξ : F // ξ ≠ 0} → ℝ, Summable M ∧
        ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R → ‖Q ξ s‖ ≤ M ξ) := by
  have hP1 := EisensteinGeneral.Piece.integrable_weyl_unipotent_mul_of_factorization F ψv nψ χ S ϖ hϖ Ψ g D
  obtain ⟨cS, mS, n, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C,
    hχϖ, hχS, hnψ, hcS, hχc, hmS, hA, hB, hoff, hon, habm, hWr, hWc, hC, hfac⟩ := D
  classical
  have := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  choose Jr hJr using fun (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) => Arch.exists_realKType (kdat j i)
  choose Jc hJc using fun (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) =>
    Arch.exists_complexKType (abm j w).1 (abm j w).2.1

  let U : {ξ : F // ξ ≠ 0} → (AdeleRing (𝓞 F) F)ˣ := fun ξ =>
    Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom (Units.mk0 (ξ : F) ξ.2) * a⁻¹
  have hU : ∀ ξ : {ξ : F // ξ ≠ 0}, ((U ξ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
      = algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := by
    intro ξ
    simp only [U, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_mk0]

  have htR : ∀ (ξ : {ξ : F // ξ ≠ 0}) (i : {w : InfinitePlace F // w.IsReal}), -(θr i
      * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i) ≠ 0 :=
    fun ξ i => neg_ne_zero.mpr (mul_ne_zero (hθr i) (pc_unit_real_ne_zero (U ξ) i))
  have htC : ∀ (ξ : {ξ : F // ξ ≠ 0}) (w : {w : InfinitePlace F // w.IsComplex}), -(θc w
      * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w) ≠ 0 :=
    fun ξ w => neg_ne_zero.mpr (mul_ne_zero (hθc w) (pc_unit_complex_ne_zero (U ξ) w))
  refine ⟨fun ξ s => ∑ j : Fin n, C j s
        * ((((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
          * ((((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹ * ψ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F)
          * u)))
        * (∏ i : {w : InfinitePlace F // w.IsReal}, Jr j i (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2) (-(θr i
        * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i)))
        * (∏ w : {w : InfinitePlace F // w.IsComplex}, Jc j w (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 +
        ((τc j w : ℝ) : ℂ) * Complex.I / 2) (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing
        (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w)))
        * ∏ v ∈ S ∪ (pc_unit_fin_exp_finite (U ξ)).toFinset,
            pc_corr F S (NumberField.TateGlobal.localChar χ) ϖ ψv nψ cS mS (A j) (B j) ((U ξ : (AdeleRing
                (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v s, ?_, ?_, ?_⟩
  ·
    intro ξ
    refine Differentiable.fun_sum fun j _ => ?_
    refine ((((hC j).mul_const _).mul ?_).mul ?_).mul ?_
    · refine pc_differentiable_prod Finset.univ _ fun i _ => ?_
      exact ((hJr j i).1 _ (htR ξ i)).comp ((differentiable_id.add_const _).add_const _)
    · refine pc_differentiable_prod Finset.univ _ fun w _ => ?_
      exact ((hJc j w).1 _ (htC ξ w)).comp
        ((((differentiable_id.const_mul _).add_const _).add_const _).add_const _)
    · refine pc_differentiable_prod _ _ fun v _ => ?_
      exact pc_corr_differentiable F S (NumberField.TateGlobal.localChar χ) ϖ ψv nψ cS mS (A j) (B j) _ v
  ·
    intro ξ s hs
    obtain ⟨χ₁, χ₂, hind⟩ := hΨ s
    have hint := hP1 s hs
    refine (Unfolding.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection hψ hind ξ.2 g hint).trans ?_

    have hΨ' : ∀ y : AdeleRing (𝓞 F) F, Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
        * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * y))
        = ∑ j : Fin n, C j s * pc_tensor F (fun i => Wr j i s) (fun w => Wc j w s) (fun v => h j v s) (a • (y + u))
            * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * y)) := by
      intro y
      simp only [hfac s, Finset.sum_mul, pc_tensor]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hsum : (∫ y, Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
        * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * y)) ∂(adelicAddHaar (𝓞 F) F))
        = ∑ j : Fin n, ∫ y, C j s * pc_tensor F (fun i => Wr j i s) (fun w => Wc j w s) (fun v => h j v s) (a •
            (y + u)) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * y)) ∂(adelicAddHaar (𝓞 F) F) := by
      rw [← MeasureTheory.integral_finsetSum _ fun j _ => pc_term_integrable F ψ hψ (kdat j) (τr j) (abm j) (τc j)
        (habm j) (Wr j) (hWr j) (Wc j) (hWc j) S
        (NumberField.TateGlobal.localChar χ) ϖ hϖ hχϖ hχS ψv nψ hψv cS hcS hχc mS hmS
        (A j) (B j) (hA j) (hB j) s hs (fun v => h j v s) (fun v hv x => hoff j v hv s x)
        (fun v hv x => hon j v hv s x)
        (C j s) a u (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F))]
      exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hΨ')

    have hArchR : ∀ j : Fin n,
        (∏ i : {w : InfinitePlace F // w.IsReal}, ∫ x : ℝ, Wr j i s x
            * Complex.exp (-(((2 * Real.pi * (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing
            (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i)) * x : ℝ) : ℂ) * Complex.I)))
          = ∏ i : {w : InfinitePlace F // w.IsReal}, Jr j i (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2) (-(θr i
              * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i))
              := by
      intro j
      refine Finset.prod_congr rfl fun i _ => ?_
      have hre : (1 : ℝ) / 2 < ((s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)).re := by
        have : ((s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)).re = s.re + 1 / 2 := by norm_num [Complex.mul_re]
        rw [this]
        linarith
      rw [(hJr j i).2.1 _ _ hre (htR ξ i)]
      congr 1
      funext x
      rw [hWr]
    have hArchC : ∀ j : Fin n,
        (∏ w : {w : InfinitePlace F // w.IsComplex}, ∫ z : ℂ, Wc j w s z
            * Complex.exp (-(((4 * Real.pi * ((-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing
            (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w)) * z).re : ℝ) : ℂ) * Complex.I)))
          = ∏ w : {w : InfinitePlace F // w.IsComplex}, Jc j w (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 +
              ((τc j w : ℝ) : ℂ) * Complex.I / 2) (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ :
              (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w)) := by
      intro j
      refine Finset.prod_congr rfl fun w _ => ?_
      have hre : (((abm j w).1 + (abm j w).2.1 : ℕ) : ℝ) / 2 + 1 < ((2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 +
          ((τc j w : ℝ) : ℂ) * Complex.I / 2)).re := by
        have h1 : ((2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)).re = 2 * s.re + 1 +
            ((abm j w).2.2 : ℝ) / 2 := by norm_num [Complex.mul_re]
        have h2 : (((abm j w).1 + (abm j w).2.1 : ℕ) : ℝ) ≤ ((abm j w).2.2 : ℝ) := by exact_mod_cast habm j w
        rw [h1]
        linarith
      rw [(hJc j w).2.1 _ _ hre (htC ξ w)]
      congr 1
      funext z
      rw [hWc]

    have hEp : (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}, pc_euler S
        (NumberField.TateGlobal.localChar χ) ϖ v.1 s)
        = ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
            (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (-(2 * s + 1))) :=
      tprod_congr fun v => by simp only [pc_euler, v.2, ↓reduceIte]
    rw [hsum, ENNReal.toReal_inv, Complex.real_smul, Complex.ofReal_inv, Finset.mul_sum,
      Finset.sum_congr rfl fun j _ => pc_term_value F ψ ψv hψfin θr θc hψarch S
          (NumberField.TateGlobal.localChar χ) ϖ hϖ hχϖ hχS nψ hψv hψv'
        hnψ cS hcS hχc mS hmS (A j) (B j) (hA j) (hB j) s hs (fun v => h j v s) (fun v hv x => hoff j v hv s x)
        (fun v hv x => hon j v hv s x) (fun i => Wr j i s) (fun w => Wc j w s) (C j s) a u (algebraMap F (AdeleRing
        (𝓞 F) F) (ξ : F)) (U ξ) (hU ξ)]
    simp only [hArchR, hArchC]
    rw [hEp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  ·
    intro R

    have hq₁ : ∀ (ξ : {ξ : F // ξ ≠ 0}) (i : {w : InfinitePlace F // w.IsReal}),
        (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i
          = (mixedEmbedding F ξ.1).1 i
            * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).1 i := by
      intro ξ i
      rw [hU ξ]
      have h1 : (algebraMap F (AdeleRing (𝓞 F) F) ξ.1 * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1
          = algebraMap F (InfiniteAdeleRing F) ξ.1 * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 := rfl
      rw [h1, map_mul, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      simp only [Prod.fst_mul, Pi.mul_apply]
    have hq₂ : ∀ (ξ : {ξ : F // ξ ≠ 0}) (w : {w : InfinitePlace F // w.IsComplex}),
        (InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w
          = (mixedEmbedding F ξ.1).2 w
            * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1).2 w := by
      intro ξ w
      rw [hU ξ]
      have h1 : (algebraMap F (AdeleRing (𝓞 F) F) ξ.1 * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1
          = algebraMap F (InfiniteAdeleRing F) ξ.1 * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 := rfl
      rw [h1, map_mul, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      simp only [Prod.snd_mul, Pi.mul_apply]

    have hK : ∀ ξ : {ξ : F // ξ ≠ 0},
        ‖(((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
            * ((((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹
              * ψ (algebraMap F (AdeleRing (𝓞 F) F) (ξ : F) * u))‖
          ≤ ‖(((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)‖
            * ‖(((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹‖ := by
      intro ξ
      rw [norm_mul, norm_mul, norm_apply_eq_one_of_isGlobalAddChar F hψ, mul_one]

    obtain ⟨I, P, k, hΦ0, hΦ⟩ := pc_finite_half ψv nψ hψv (pc_norm_localChar_eq_one F ψ hψ ψv hψfin) χ S ϖ hϖ hχϖ
      cS hcS hχc mS hmS n A B hA hB a R

    have hJr' : ∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}), ∃ C₁ c₁ : ℝ, ∃ N₁ : ℕ,
        0 < C₁ ∧ 0 < c₁ ∧ ∀ (s : ℂ) (t : ℝ), ‖s‖ ≤ R → t ≠ 0 →
          ‖Jr j i (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2) t‖
            ≤ C₁ * max 1 (|t| ^ (-(N₁ : ℝ))) * Real.exp (-c₁ * |t|) := by
      intro j i
      obtain ⟨C₁, c₁, N₁, hC₁, hc₁, hb⟩ := (hJr j i).2.2 (R + ‖(1 / 2 : ℂ) + ((τr j i : ℝ) : ℂ) * Complex.I / 2‖)
      refine ⟨C₁, c₁, N₁, hC₁, hc₁, fun s t hs ht => hb _ t ?_ ht⟩
      calc ‖s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2‖
          = ‖s + (1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)‖ := by rw [add_assoc]
        _ ≤ ‖s‖ + ‖(1 / 2 : ℂ) + ((τr j i : ℝ) : ℂ) * Complex.I / 2‖ := norm_add_le _ _
        _ ≤ R + ‖(1 / 2 : ℂ) + ((τr j i : ℝ) : ℂ) * Complex.I / 2‖ := by linarith
    have hJc' : ∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), ∃ C₁ c₁ : ℝ, ∃ N₁ : ℕ,
        0 < C₁ ∧ 0 < c₁ ∧ ∀ (s ζ : ℂ), ‖s‖ ≤ R → ζ ≠ 0 →
          ‖Jc j w (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2) ζ‖
            ≤ C₁ * max 1 (‖ζ‖ ^ (-(N₁ : ℝ))) * Real.exp (-c₁ * ‖ζ‖) := by
      intro j w
      obtain ⟨C₁, c₁, N₁, hC₁, hc₁, hb⟩ := (hJc j w).2.2
        (2 * R + ‖(1 : ℂ) + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2‖)
      refine ⟨C₁, c₁, N₁, hC₁, hc₁, fun s ζ hs hζ => hb _ ζ ?_ hζ⟩
      have h2 : ‖(2 : ℂ) * s‖ = 2 * ‖s‖ := by rw [norm_mul, Complex.norm_two]
      calc ‖2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2‖
          = ‖2 * s + (1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)‖ := by congr 1; ring
        _ ≤ ‖(2 : ℂ) * s‖ + ‖(1 : ℂ) + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2‖ :=
            norm_add_le _ _
        _ ≤ 2 * R + ‖(1 : ℂ) + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2‖ := by
            rw [h2]; linarith
    exact EisensteinGeneral.Piece.exists_summable_majorant_of_lattice_vanishing F n R C (fun j => (hC j).continuous)
      _ _ hK (fun j i s t => Jr j i (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2) t) hJr'
      (fun j w s ζ => Jc j w (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2) ζ) hJc'
      θr hθr θc hθc
      (fun ξ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((U ξ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1)
      _ (pc_unit_real_ne_zero a⁻¹) _ (pc_unit_complex_ne_zero a⁻¹) hq₁ hq₂ I _ hΦ0 P k hΦ



end Solution
