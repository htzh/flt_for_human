/-
  The balanced-compact decomposition of the idèles.

  `NumberField.TateGlobal.exists_isCompact_forall_eq_principal_mul_balanced_mul`: there is a compact set
  `U` of norm-one idèles (the Haar character `α` is `1` on it) such that every idèle `y` factors as

    `y = η · z · u`,  `η ∈ Fˣ`, `u ∈ U`,  `z` with trivial finite part and *balanced* archimedean part
    `z w = r` for one real `r > 0` at every infinite place, and `α z = r ^ [F : ℚ]`.

  That is the Minkowski/Dirichlet form of the norm-one compactness: `z` is the single archimedean
  dilation that makes the norm one, so the compactness statement for `𝔸_F^1 / F^×` reads as a
  decomposition of the whole idèle group.

  The compact set is `NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul`
  (`NumberTheory/NumberField/TateGlobalCompactness.lean`), and the norm bookkeeping is the product
  formula for the Haar character
  `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm`
  (`NumberTheory/AdelicModulus.lean`).

  Transcribed from the `S_` file below (pinned `aa2d8b3`, 120 lines): the pin's one public headline
  (its `solution`) over its ten public helpers. The pin's helpers live in a search-stage namespace
  `B2aDilation`; the port keeps every last name and gives the namespace the subject name `Dilation`
  (`NumberField.TateGlobal.Dilation`), so `coordOf` and `dil` read as what they are: the coordinate
  realizing a prescribed archimedean value, and the idèle that is that coordinate at every infinite
  place and `1` at every finite one. The pin's `solution` folds into the row (same statement), which is
  why `scaffold_audit` reads `FOLDED` and `check_port` counts 11 declarations against 11 pin publics.

  Both premises are in the closure, measured by the proof rather than by recollection (FR-0229): the
  compact norm-one set and the product formula are the two imports, and `ideleNorm`,
  `normOneIdeles`, `mem_normOneIdeles_iff`, `distribHaarChar_pos` and `sum_mult_eq` all resolve from
  them — no import was added.

  Gates for the module as landed (11 declarations, all public, no `private` engine):
  `check_port --force` 11 ok / 0 mismatch / 0 missing / 0 own / 0 kw; `scaffold_audit` complete (also
  at the end of step 1, the ten helpers with `sorry` bodies: 11 declarations on the wire, `complete`);
  silent at `-DautoImplicit=false -DmaxHeartbeats=200000`; `#print axioms` on all 11 declarations gives
  `[propext, Classical.choice, Quot.sound]`; `dedup.py --within` 0 clusters; `move_dead.py` 0
  declarations / 0 lines.

  Heartbeat probe: silent at 10000, aborts at 5000 (`lake env lean -DautoImplicit=false
  -DmaxHeartbeats=N`), and the peak is the row itself — at 5000 the abort is at the row's
  `set r`/statement (`:143`, `isDefEq`; `:111`, `whnf`), not in a helper. No in-file cap is carried
  (playbook §3.5, FR-0225).

  Proof-side deviations from the pin, statements untouched:
  * `dif_pos` / `dif_neg` → `dite_eq_left` / `dite_eq_right` (v4.34 deprecations; the port's recorded
    practice for `if_pos`/`if_neg`).
  * `omit [NumberField F] in` on the five helpers whose statement does not mention it
    (`extensionEmbedding_eq_ofReal_of_isReal`, `extensionEmbedding_coordOf`,
    `norm_eq_of_extensionEmbedding`, `norm_coordOf`, `coordOf_ne_zero`) — the linter's own
    `Try this:` block for `linter.unusedSectionVars`, not a silencer. It is a command prefix, so the
    statement text is unchanged: `check_port` reads 11 ok with and without the lines (measured).
  * the pin's `attribute [-instance]` / `attribute [-simp]` walls are dropped.

  spec-pin: P2M/Sol/S_NumberField_TateGlobal_exists_isCompact_forall_eq_principal_mul_balanced_mul.lean
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobalCompactness
import FLTForHuman.NumberTheory.AdelicModulus

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NNReal Classical

namespace NumberField.TateGlobal

namespace Dilation

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in
theorem extensionEmbedding_eq_ofReal_of_isReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    Completion.extensionEmbedding w x = ((Completion.extensionEmbeddingOfIsReal hw x : ℝ) : ℂ) := by
  have h1 : Continuous fun x : w.Completion => Completion.extensionEmbedding w x :=
    (Completion.isometry_extensionEmbedding w).continuous
  have h2 : Continuous fun x : w.Completion => ((Completion.extensionEmbeddingOfIsReal hw x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  refine NumberField.InfinitePlace.Completion.induction_on _
    (p := fun x : w.Completion =>
      Completion.extensionEmbedding w x = ((Completion.extensionEmbeddingOfIsReal hw x : ℝ) : ℂ))
    x (isClosed_eq h1 h2) fun y => ?_
  rw [Completion.extensionEmbedding_coe, Completion.extensionEmbeddingOfIsReal_coe, embedding_of_isReal_apply]

noncomputable def coordOf (w : InfinitePlace F) (r : ℝ) : w.Completion :=
  if hw : w.IsReal then (Completion.ringEquivRealOfIsReal hw).symm r
  else (Completion.ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (r : ℂ)

omit [NumberField F] in
theorem extensionEmbedding_coordOf (w : InfinitePlace F) (r : ℝ) :
    Completion.extensionEmbedding w (coordOf F w r) = (r : ℂ) := by
  by_cases hw : w.IsReal
  · rw [coordOf, dite_eq_left hw, extensionEmbedding_eq_ofReal_of_isReal F hw]
    exact congrArg (fun s : ℝ => (s : ℂ)) ((Completion.ringEquivRealOfIsReal hw).apply_symm_apply r)
  · rw [coordOf, dite_eq_right hw]
    exact (Completion.ringEquivComplexOfIsComplex _).apply_symm_apply (r : ℂ)

omit [NumberField F] in
theorem norm_eq_of_extensionEmbedding (w : InfinitePlace F) (x : w.Completion) :
    ‖x‖ = ‖Completion.extensionEmbedding w x‖ := by
  have := (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  exact this.symm

omit [NumberField F] in
theorem norm_coordOf (w : InfinitePlace F) (r : ℝ) (hr : 0 < r) : ‖coordOf F w r‖ = r := by
  rw [norm_eq_of_extensionEmbedding, extensionEmbedding_coordOf, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

omit [NumberField F] in
theorem coordOf_ne_zero (w : InfinitePlace F) (r : ℝ) (hr : 0 < r) : coordOf F w r ≠ 0 := by
  intro h
  have := norm_coordOf F w r hr
  rw [h, norm_zero] at this
  exact hr.ne this

noncomputable def dil (r : ℝ) (hr : 0 < r) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))
    (MulEquiv.piUnits.symm fun w : InfinitePlace F => Units.mk0 (coordOf F w r) (coordOf_ne_zero F w r hr))

theorem dil_fst (r : ℝ) (hr : 0 < r) (w : InfinitePlace F) : ((dil F r hr : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = coordOf F w r := by
  rfl

theorem dil_snd (r : ℝ) (hr : 0 < r) : ((dil F r hr : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  rfl

theorem distribHaarChar_dil (r : ℝ) (hr : 0 < r) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (dil F r hr) : ℝ) = r ^ Module.finrank ℚ F := by
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm]
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ‖((dil F r hr : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    intro v
    rw [dil_snd]
    show ‖(1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v‖ = 1
    rw [show (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) v = 1 from rfl, norm_one]
  rw [finprod_eq_one_of_forall_eq_one h2, mul_one]
  simp_rw [dil_fst, norm_coordOf F _ r hr]
  rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq]

end Dilation

open NumberField.TateGlobal.Dilation

/-- **The balanced-compact decomposition.** Every idèle is a principal idèle times a balanced
archimedean dilation times an element of one compact norm-one set. -/
theorem exists_isCompact_forall_eq_principal_mul_balanced_mul
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∃ U : Set (AdeleRing (𝓞 F) F)ˣ, IsCompact U ∧ (∀ u ∈ U, ((α u : ℝˣ) : ℝ) = 1) ∧
      ∀ y : (AdeleRing (𝓞 F) F)ˣ, ∃ (η : Fˣ) (z u : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ),
        u ∈ U ∧ 0 < r ∧
        y = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * z * u ∧
        (z : AdeleRing (𝓞 F) F).2 = 1 ∧
        (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) ∧
        ((α z : ℝˣ) : ℝ) = r ^ Module.finrank ℚ F := by
  intro α
  have hα : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((α x : ℝˣ) : ℝ) = (distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ) := fun x => rfl
  have hαn : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ((α x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm F x := fun x => rfl
  obtain ⟨K, hKc, hK1, hKrep⟩ := NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul F
  refine ⟨K, hKc, fun u hu => ?_, fun y => ?_⟩
  · rw [hαn]
    exact (NumberField.TateGlobal.mem_normOneIdeles_iff u).mp (hK1 hu)

  set n : ℕ := Module.finrank ℚ F with hn
  have hn0 : n ≠ 0 := Module.finrank_pos.ne'
  have hy0 : 0 < ((α y : ℝˣ) : ℝ) := by rw [hα]; exact_mod_cast distribHaarChar_pos
  set r : ℝ := ((α y : ℝˣ) : ℝ) ^ ((n : ℝ)⁻¹) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hy0 _
  have hrn : r ^ n = ((α y : ℝˣ) : ℝ) := by rw [hr, Real.rpow_inv_natCast_pow hy0.le hn0]
  set z := dil F r hr0 with hz
  have hαz : ((α z : ℝˣ) : ℝ) = r ^ n := by rw [hα, hz, distribHaarChar_dil]

  have hx : y * z⁻¹ ∈ NumberField.TateGlobal.normOneIdeles F := by
    rw [NumberField.TateGlobal.mem_normOneIdeles_iff, ← hαn, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
      hαz, hrn, mul_inv_cancel₀ hy0.ne']
  obtain ⟨η, κ, hκ, hxeq⟩ := hKrep _ hx
  refine ⟨η, z, κ, r, hκ, hr0, ?_, dil_snd F r hr0, fun w => ?_, hαz⟩
  · calc y = (y * z⁻¹) * z := by rw [inv_mul_cancel_right]
      _ = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * κ * z := by rw [hxeq]; rfl
      _ = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * z * κ := by rw [mul_assoc, mul_comm κ z, ← mul_assoc]
  · rw [hz, dil_fst, extensionEmbedding_coordOf]

end NumberField.TateGlobal
