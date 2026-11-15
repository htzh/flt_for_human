/-
  SET-AF82B consumer: the three unipotent–Haar rows, spent.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/RationalCentreHaar.lean` carries

  * `AutomorphicForm.lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` —
    the conjugation by `heckeGen v * centralScalar u` multiplies the centre-unipotent Haar
    integral by the absolute norm of `v`;
  * `AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup` — the adèlic
    constant term at `globalPoints γ * g` equals the one at `g` for a Borelíser rational `γ`;
  * `AutomorphicForm.isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf` — the Hecke-isotypic
    cuspidal submodule of the production pins at `levelOne ⊓ K_f` is trivial over a finite
    exceptional set.

  **What is new here.** The first row's `hb` (that `Z(𝔸_K)·Kˣ·U(𝔸_K)` is normalized by
  `heckeGen v * centralScalar u`) is a *hypothesis* of the pin — its own `S_` file does not prove
  it. Zone 1 supplies it, so the row becomes unconditional. The engine is two facts: the rational
  centre is scalar hence central (`ratCentral_comm`, read off the row's
  `ratCentral_eq_centralScalar` and `centralScalar_mul_comm'`), and a unipotent element is carried
  to the shifted one by the diagonal factor (the row's `conj_ratCentral_mul_unipotentGL2`).

  **The readings.**

  * Zone 1 — the headline **with `hb` discharged**, over any number field `K`.
  * Zone 2 — the row's scaling at the identity idèle: the modulus character of `1` is `1`, so the
    additive Haar integral of `𝔸_K` is unchanged under `y ↦ 1 · y`.
  * Zone 3 — every rational scalar lies in `Z·U` (the row's `ratCentral_mul_unipotentGL2_mem` at
    `y = 0`), cross-module with `globalPoints`/`centralScalar` (`Adelic/Basic.lean`).
  * Zone 4 — the second row at the zero form, for every Borelíser `γ` and every `g`.
  * Zone 5 — the second row's matrix engine at `γ = 1`, where the shift is trivial.
  * Zone 6 — the third row's engine at `F = ℚ`: a nonarchimedean place outside any finite `S`.
  * Zone 7 — the third row at `F = ℚ`, the trivial eigensystem and the empty exceptional set.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF82BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.RationalCentreHaar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
  IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open AutomorphicForm

open scoped ENNReal NNReal

noncomputable section

namespace AutomorphicFormSetAF82BConsumer

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

/-! ### Zone 1 — the first row with its normalization hypothesis discharged -/

/-- The rational centre is scalar, hence fixed by conjugation: the row's
`ratCentral_eq_centralScalar` composed with `centralScalar_mul_comm'`. -/
private theorem ratCentral_comm (K : Type) [Field K] [NumberField K]
    (a : Kˣ) (g : AdelicGL2 (𝓞 K) K) : ratCentral K a * g = g * ratCentral K a := by
  rw [ratCentral_eq_centralScalar, centralScalar_mul_comm']

/-- `ratCentral` is a monoid hom, so it sends `1` to `1`. -/
private theorem ratCentral_one (K : Type) [Field K] [NumberField K] :
    ratCentral K (1 : Kˣ) = 1 := by
  show globalPoints (𝓞 K) K (Units.map _ (1 : Kˣ)) = 1
  simp

/-- **Zone 1, engine.** `Z(𝔸_K)·Kˣ·U(𝔸_K)` is normalized by `diagOne τ * centralScalar u`: the
scalar factor is central, and the diagonal factor shifts the unipotent parameter by `τ`. -/
private theorem conj_mem_rationalCentreUnipotent (K : Type) [Field K] [NumberField K]
    (τ : (AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ) {y : AdelicGL2 (𝓞 K) K}
    (hy : y ∈ rationalCentreUnipotent K) :
    (diagOne τ * centralScalar (𝓞 K) K u) * y * (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ ∈
      rationalCentreUnipotent K := by
  rw [rationalCentreUnipotent, Subgroup.sup_eq_closure] at hy
  have key : ((rationalCentre K : Set (AdelicGL2 (𝓞 K) K)) ∪ (adelicUnipotent K : Set _)) ⊆
      (rationalCentreUnipotent K).comap
        (MulAut.conj (diagOne τ * centralScalar (𝓞 K) K u)).toMonoidHom := by
    intro z hz
    rw [Set.mem_union] at hz
    change (diagOne τ * centralScalar (𝓞 K) K u) * z *
      (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ ∈ rationalCentreUnipotent K
    rcases hz with hz | hz
    · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hz
      change (diagOne τ * centralScalar (𝓞 K) K u) * ratCentral K a *
        (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ ∈ rationalCentreUnipotent K
      rw [← ratCentral_comm K a, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.mem_sup_left ⟨a, rfl⟩
    · obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hz
      show (diagOne τ * centralScalar (𝓞 K) K u) * unipotentGL2 m.toAdd *
        (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ ∈ _
      have hc := conj_ratCentral_mul_unipotentGL2 K τ u (1 : Kˣ) m.toAdd
      rw [ratCentral_one, one_mul] at hc
      rw [hc, one_mul]
      exact Subgroup.mem_sup_right ⟨Multiplicative.ofAdd ((τ : AdeleRing (𝓞 K) K) * m.toAdd), rfl⟩
  have h := (Subgroup.closure_le (K := (rationalCentreUnipotent K).comap
    (MulAut.conj (diagOne τ * centralScalar (𝓞 K) K u)).toMonoidHom)).mpr key hy
  change (diagOne τ * centralScalar (𝓞 K) K u) * y *
    (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ ∈ rationalCentreUnipotent K at h
  exact h

/-- The pin's hypothesis `hb` of the first row, proved: `diagOne τ * centralScalar u` normalizes
`Z·Kˣ·U` in both directions (its inverse has the same shape, by `centralScalar_mul_comm'`). -/
private theorem conj_mem_iff (K : Type) [Field K] [NumberField K]
    (τ : (AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ) (y : AdelicGL2 (𝓞 K) K) :
    y ∈ rationalCentreUnipotent K ↔
      (diagOne τ * centralScalar (𝓞 K) K u) * y * (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ ∈
        rationalCentreUnipotent K := by
  constructor
  · exact conj_mem_rationalCentreUnipotent K τ u
  · intro hy
    have hb' : (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ =
        diagOne τ⁻¹ * centralScalar (𝓞 K) K u⁻¹ := by
      simp only [mul_inv_rev, ← map_inv]
      rw [centralScalar_mul_comm']
    have h := conj_mem_rationalCentreUnipotent K τ⁻¹ u⁻¹ hy
    rw [← hb', inv_inv] at h
    rwa [show (diagOne τ * centralScalar (𝓞 K) K u)⁻¹ *
        ((diagOne τ * centralScalar (𝓞 K) K u) * y * (diagOne τ * centralScalar (𝓞 K) K u)⁻¹) *
        (diagOne τ * centralScalar (𝓞 K) K u) = y from by group] at h

/-- **Zone 1, the row.** The first headline with its `hb` discharged, over any number field: the
conjugation by `heckeGen v * centralScalar u` multiplies the centre-unipotent Haar integral by the
absolute norm of `v`. The `hb` supplied is the normalization proved above, and
`heckeGen (𝓞 K) K v` *is* `diagOne (uniformizerIdele K v)`. -/
theorem lintegral_conj_heckeGen_centralScalar (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (F : rationalCentreUnipotent K → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F ⟨(heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u) * (x : AdelicGL2 (𝓞 K) K) *
        (heckeGen (𝓞 K) K v * centralScalar (𝓞 K) K u)⁻¹,
        (conj_mem_iff K (uniformizerIdele K v) u (x : AdelicGL2 (𝓞 K) K)).mp x.2⟩
      ∂(rationalCentreUnipotentHaar K) =
      (Ideal.absNorm v.asIdeal : ℝ≥0∞) * ∫⁻ x, F x ∂(rationalCentreUnipotentHaar K) :=
  lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj K v u
    (fun y => conj_mem_iff K (uniformizerIdele K v) u y) F hF

/-! ### Zone 2 — the row's scaling at the identity idèle -/

/-- **Zone 2.** The modulus character of the identity idèle is `1`, so the row's scaling leaves the
additive Haar integral of `𝔸_K` fixed: the `τ = 1` reading of
`lintegral_comp_mul_adelicAddHaar`. -/
theorem lintegral_comp_mul_one (K : Type) [Field K] [NumberField K]
    (φ : AdeleRing (𝓞 K) K → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ y, φ ((1 : (AdeleRing (𝓞 K) K)ˣ) * y) ∂(adelicAddHaar (𝓞 K) K) =
      ∫⁻ y, φ y ∂(adelicAddHaar (𝓞 K) K) := by
  rw [lintegral_comp_mul_adelicAddHaar K 1 φ hφ]
  simp

/-! ### Zone 3 — every rational scalar lies in `Z·U` -/

/-- **Zone 3.** The row's `ratCentral_mul_unipotentGL2_mem` at the trivial unipotent: every
rational scalar `ratCentral a` is already in `Z(𝔸_K)·Kˣ·U(𝔸_K)` — the subgroup the measure
`rationalCentreUnipotentHaar` lives on. -/
theorem ratCentral_mem_rationalCentreUnipotent (K : Type) [Field K] [NumberField K] (a : Kˣ) :
    ratCentral K a ∈ rationalCentreUnipotent K := by
  simpa using ratCentral_mul_unipotentGL2_mem K a 0

/-! ### Zone 4 — the second row at the zero form -/

/-- **Zone 4.** The second headline at the zero form, at every Borelíser rational point and every
`g`: the constant term of the zero function is `0`, so the row's invariance reads `0 = 0`. -/
theorem constantTerm_zero_comp_globalPoints (K : Type) [Field K] [NumberField K]
    {γ : Matrix.GeneralLinearGroup (Fin 2) K} (hγ : γ ∈ borelSubgroup K) (g : AdelicGL2 (𝓞 K) K) :
    constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
        (fun x => unipotentGL2 x) (fun _ => (0 : ℂ)) (globalPoints (𝓞 K) K γ * g) = 0 := by
  rw [constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup K (fun _ _ _ => rfl) hγ g,
    constantTerm_zero]

/-! ### Zone 5 — the second row's matrix engine at the trivial Borel element -/

/-- **Zone 5.** `unipotentGL2_mul_globalPoints` at `γ = 1`: the trivial Borelíser point shifts the
unipotent parameter by `1`, so the two sides agree. -/
theorem unipotentGL2_mul_globalPoints_one (K : Type) [Field K] [NumberField K]
    (x : AdeleRing (𝓞 K) K) :
    unipotentGL2 x * globalPoints (𝓞 K) K (1 : Matrix.GeneralLinearGroup (Fin 2) K) =
      globalPoints (𝓞 K) K 1 * unipotentGL2 x := by
  rw [unipotentGL2_mul_globalPoints K 1 (one_mem _)]
  simp

/-! ### Zone 6 — a place of `ℚ` outside any finite set -/

/-- **Zone 6.** The third row's engine at `F = ℚ`: the nonarchimedean places of `ℚ` are infinite,
so any finite exceptional set misses one — the step the row's own proof takes. -/
theorem exists_heightOneSpectrum_notMem (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S :=
  @Infinite.exists_notMem_finset _ (infinite_heightOneSpectrum ℚ) S

/-! ### Zone 7 — the third row at `F = ℚ` -/

/-- The production pins of `ℚ` at `levelOne ⊓ K_f`, as the third row uses them. -/
private abbrev ratPins : CarrierPins ℚ :=
  productionPinsOf ℚ ∅ (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
    (fun v => heckeGen (𝓞 ℚ) ℚ v) ∅

/-- The trivial Hecke eigensystem of `ℚ`: top level, zero eigenvalues. -/
private def trivialEigensystem : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := by
    intro h
    have h1 : (1 : 𝓞 ℚ) ∈ (⊥ : Ideal (𝓞 ℚ)) :=
      h.le (show (1 : 𝓞 ℚ) ∈ (⊤ : Ideal (𝓞 ℚ)) from trivial)
    exact one_ne_zero (Ideal.mem_bot.mp h1)
  a := fun _ => 0
  b := fun _ => 0

/-- **Zone 7.** The third headline at `F = ℚ`, `D = B = ∅`, the trivial character, the trivial
eigensystem and the empty exceptional set: the Hecke-isotypic cuspidal submodule of the production
pins at `levelOne ⊓ K_f` is trivial. -/
theorem isotypicCuspSubmodule_bot_eq_bot_rat :
    isotypicCuspSubmodule ℚ ratPins (1 : ratPins.Z →* ℂˣ) ⊥ ∅ trivialEigensystem = ⊥ :=
  isotypicCuspSubmodule_bot_eq_bot_of_productionPinsOf ℚ ∅ ∅ (1 : ratPins.Z →* ℂˣ) ∅
    trivialEigensystem

end AutomorphicFormSetAF82BConsumer
