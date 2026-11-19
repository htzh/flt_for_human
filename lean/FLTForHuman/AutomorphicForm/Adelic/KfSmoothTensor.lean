/-
  `Kf`-smooth test functions, their conjugates, and the pure-tensor set.

  Four rows: `Kf`-smoothness giving a level ideal, conjugation preserving factorizability and
  archimedean bi-finiteness, the splitting of an integral element modulo the level subgroup, and the
  pure-tensor set being preserved by the unipotent translate.

  **Route.** All four pins are *flattened* `S_` files: every declaration is public and the row is
  the file's `solution`.  Each pin's body is transcribed verbatim — statements *and* proofs — with
  only the pin's search-stage namespace renamed to a subject name and the pin's imports, wrapper
  namespace, `p2m_*` macros and `solution` dropped:

  * pin 1, `KfLevelSol` -> `KfLevel` (the level ideal of a `Kf`-smooth function);
  * pin 2, no rename (the pin already writes the port's own `AutomorphicForm.CuspidalConstituent.Conj`);
  * pin 3, `RS11SURG` -> `LevelSplit` (splitting an integral element off the level);
  * pin 4, `M4aP3B.Rows.SliceTensor` -> `SliceTensor` (pure tensors under the unipotent translate).

  The four rows come last, after the engines they consume; each row's proof is the pin's `solution`
  body with the engines qualified by their new namespace.  Each pin's `solution` is *not* declared —
  the row is that statement, so `check_port` reports the four `solution`s as `FOLDED` into the rows,
  and every other public declaration of the four pins (25 + 25 + 16 + 20 = 86, minus the one `_impl`
  folded onto its row) is here at the pin's name: 85 ok / 0 mismatch / 0 missing / 0 own / 0 kw, and
  `tools/deps/scaffold_audit.py` complete.

  **The one duplicate pair, declared once (gate 4).** Pin 4's `comp_mul_unipotentGL2_mul_mem_pureTensorSet_impl`
  (`S_…pureTensorSet.lean:158`) and the row `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet`
  state the same thing — the pin's `solution` is that `_impl` applied (`:181-189`) — so the port declares
  it **once**, at the row's name, with the pin's `_impl` body as the row's proof. That is the port's rule
  for a pin that states one result twice (`AutomorphicForm/Adelic/Siegel/FiniteCover.lean` records the same
  decision for its `_impl`), and it keeps `dedup --within` at **0 clusters**; the price is that
  `check_port` reads `85 ok` and `scaffold_audit` classifies the un-declared `_impl` as `RENAMED?` (same
  statement, different last name) while still reading `complete`.

  **`continuous_unipotentGL2`.** The pin's copy (`S_…pureTensorSet.lean:41`) is transcribed in
  `SliceTensor` even though `AutomorphicForm.continuous_unipotentGL2`
  (`AutomorphicForm/Adelic/RightConvDerivatives.lean:162`) is already public in this module's import
  closure: it is part of the flattened pin's public surface.  The row does not use it.

  **v4.34 drift** (the only edits to the pins' text, all proof-side):
  * `levelParam_zero`: the pin's `simp only [levelParam, Matrix.of_apply, …]` no longer reduces the
    entry.  `Matrix.of` is the `Equiv.refl` of v4.34's `Matrix.of`/`of_apply`, and the term `simp`
    leaves is not reducible at `implicit` transparency, so `Matrix.of_apply` finds no occurrence.
    Restated with a `show` at the explicit entry, then `Matrix.of_apply`, `Matrix.one_apply`, an
    `if` split and `rfl`.
  * `if_true`/`if_false`/`if_pos`/`if_neg` -> `ite_true`/`ite_false`/`ite_eq_left`/`ite_eq_right`,
    `zero_le'` -> `zero_le`: all deprecated at v4.34 and gate 2 is silence.
  * a bare `end` does not close a `namespace` at v4.34 (the pins close their wrapper that way), so
    the block closures are spelled `end Conj` / `end CuspidalConstituent`.
  * pin 4's `first | exact … | (apply … <;> assumption)` is written as its first branch: the second
    is never executed and `linter.unreachableTactic` fires on it.

  **Premises (FR-0229, measured).** All four rows are graph leaves:
  `tools/deps/premise_imports.py --nodes … --missing-from … --olean` reports nothing to add.  The
  engines' proofs are served by this module's existing imports (`NumberTheory/AdelicDock/
  LocalEmbedding` for `finEmbed`/`localEmbed`/`matrix_eq_of_mapMatrix_arch_fin_eq`,
  `NumberTheory/AdelicLevel/Projections` for `finAdeleEval`, `NumberField.AdelicBox` for the
  `archEntries` coordinates, `NumberField.AdelicFourier` for `pureTensorSet`); the four `open` lines
  below are what the pins needed, and no import line was added.

  **Heartbeat probe (FR-0225: recorded, never installed).** `lake env lean -DautoImplicit=false
  -DmaxHeartbeats=10000` on this module is silent; at `-DmaxHeartbeats=5000` it fails with six
  deterministic timeouts (`whnf`/`isDefEq` at the proofs of `exists_ideal_level_subset_of_mem_nhds_one`,
  `isArchTestFactor_conj`, `contDiff_archFactor` and the second row).  The module's per-declaration
  floor is therefore ~5-10 k, far inside the playbook's 200 k edit-loop cap; no `set_option
  maxHeartbeats` is carried in the file.

  spec-pin: P2M/Sol/S_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.LocalOrbitalBase
import FLTForHuman.RepTheory.LocalLanglands.UnramifiedWhittaker
import FLTForHuman.NumberTheory.AdelicFourier
import FLTForHuman.NumberTheory.AdelicLevel.Level

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open NumberField.AdelicBox NumberField.AdelicFourier AdelicDock
open FLT.SmoothVectors
open AutomorphicForm
open scoped Classical ENNReal NNReal BigOperators Matrix ComplexConjugate SchwartzMap Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

namespace KfLevel

section NumberFieldAdelic

variable (F : Type) [Field F] [NumberField F]

variable {F} in
theorem idealBound_span_singleton {r : 𝓞 F} (hr : r ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) (Ideal.span {r}) v = v.intValuation r := by
  rw [idealBound_of_ne_bot (fun h => hr (Ideal.span_singleton_eq_bot.mp h)) v, v.intValuation_if_neg hr]

theorem exp_neg_one_pow (e : ℕ) :
    (WithZero.exp (-1 : ℤ)) ^ e = WithZero.exp (-(e : ℤ)) := by
  induction e with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

variable {F} in
theorem neg_mem_idealBall {N : Ideal (𝓞 F)} {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ idealBall (𝓞 F) F N) :
    -y ∈ idealBall (𝓞 F) F N := fun v => by
  rw [coe_neg_apply, Valuation.map_neg]; exact hy v

def sm (z : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite z

theorem sm_apply (z : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) (v : HeightOneSpectrum (𝓞 F)) :
    sm F z v = (z v : v.adicCompletion F) := rfl

theorem sm_zero : sm F 0 = 0 := RestrictedProduct.ext _ _ fun _ => rfl

theorem nhds_zero_eq_map_sm : 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) = Filter.map (sm F) (𝓝 0) := by
  have hopen : ∀ v : HeightOneSpectrum (𝓞 F), IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun v => Valued.isOpen_valuationSubring _
  rw [← sm_zero F]
  exact RestrictedProduct.nhds_zero_eq_map_structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (B := fun v => v.adicCompletionIntegers F) hopen

theorem exists_exp_neg_ball_subset (v : HeightOneSpectrum (𝓞 F)) {U : Set (v.adicCompletionIntegers F)}
    (hU : U ∈ 𝓝 (0 : v.adicCompletionIntegers F)) :
    ∃ e : ℕ, ∀ y : v.adicCompletionIntegers F,
      Valued.v (y : v.adicCompletion F) ≤ WithZero.exp (-(e : ℤ)) → y ∈ U := by
  obtain ⟨u, hu, huU⟩ := (mem_nhds_subtype _ _ _).mp hU
  change u ∈ 𝓝 (0 : v.adicCompletion F) at hu
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hu
  obtain ⟨t, ht⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
    (MonoidWithZeroHom.ofClass (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))) γ.1
  have hvt : Valued.v t ≠ 0 := by
    intro h
    apply γ.ne_zero
    rw [← ht, MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff]
    exact h
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v t = WithZero.exp m := ⟨_, (WithZero.exp_log hvt).symm⟩
  refine ⟨(-m).toNat + 1, fun y hy => huU ?_⟩
  show (y : v.adicCompletion F) ∈ u
  apply hγ
  show Valued.v.restrict (y : v.adicCompletion F) < γ.1
  have hlt : Valued.v (y : v.adicCompletion F) < Valued.v t := by
    refine lt_of_le_of_lt hy ?_
    rw [hm, WithZero.exp_lt_exp]
    have := Int.self_le_toNat (-m)
    omega
  have h2 : Valued.v.restrict (y : v.adicCompletion F) < Valued.v.restrict t :=
    Valued.v.restrict_lt_iff.mpr hlt
  rw [← ht]
  exact h2

theorem exists_idealBall_subset_of_mem_nhds_zero {B : Set (FiniteAdeleRing (𝓞 F) F)}
    (hB : B ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) : ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ idealBall (𝓞 F) F N ⊆ B := by
  classical
  rw [nhds_zero_eq_map_sm F, Filter.mem_map, nhds_pi, Filter.mem_pi'] at hB
  obtain ⟨I, t, ht, hIB⟩ := hB
  choose e he using fun v : HeightOneSpectrum (𝓞 F) => exists_exp_neg_ball_subset F v (ht v)
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F) => v.intValuation_exists_uniformizer
  have hπ0 : ∀ v, π v ≠ 0 := fun v h => by
    have h1 := hπ v
    rw [h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  have hr0 : (∏ v ∈ I, π v ^ e v) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ (hπ0 v)
  refine ⟨Ideal.span {∏ v ∈ I, π v ^ e v}, fun h => hr0 (Ideal.span_singleton_eq_bot.mp h), fun x hx => ?_⟩
  have hxint : x ∈ integralFiniteAdeles (𝓞 F) F := idealBall_subset_integralFiniteAdeles _ hx
  let y : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F := fun v => ⟨x v, hxint v⟩
  have hyx : sm F y = x := RestrictedProduct.ext _ _ fun _ => rfl
  have hy : y ∈ Set.pi (↑I) t := by
    intro w hw
    apply he w
    show Valued.v (x w) ≤ WithZero.exp (-(e w : ℤ))
    have hxw : Valued.v (x w) ≤ idealBound (𝓞 F) (Ideal.span {∏ v ∈ I, π v ^ e v}) w := hx w
    rw [idealBound_span_singleton hr0] at hxw
    refine hxw.trans ?_
    rw [← Finset.mul_prod_erase I (fun v => π v ^ e v) (Finset.mem_coe.mp hw), map_mul, map_pow, hπ w,
      exp_neg_one_pow]
    calc WithZero.exp (-(e w : ℤ)) * w.intValuation (∏ v ∈ I.erase w, π v ^ e v)
        ≤ WithZero.exp (-(e w : ℤ)) * 1 := mul_le_mul_right (w.intValuation_le_one _) _
      _ = WithZero.exp (-(e w : ℤ)) := mul_one _
  have hmem : sm F y ∈ B := hIB hy
  rwa [hyx] at hmem

noncomputable def levelParam (f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F) (b : Bool) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j + f (b, i, j)) : AdeleRing (𝓞 F) F)

theorem continuous_levelParam (b : Bool) :
    Continuous fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F => levelParam F f b := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
    ((((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j + f (b, i, j)) : AdeleRing (𝓞 F) F))
  have h1 : Continuous fun _ : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := continuous_const
  have h2 : Continuous fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j + f (b, i, j) :=
    continuous_const.add
      (continuous_apply (b, i, j) : Continuous fun p : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F => p (b, i, j))
  exact h1.prodMk h2

theorem continuous_levelParamPair : Continuous fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
    (levelParam F f true, MulOpposite.op (levelParam F f false)) :=
  (continuous_levelParam F true).prodMk (MulOpposite.continuous_op.comp (continuous_levelParam F false))

theorem levelParam_zero (b : Bool) : levelParam F 0 b = 1 := by
  refine Matrix.ext fun i j => ?_
  show Matrix.of (fun i j => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j +
      (0 : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F) (b, i, j)) : AdeleRing (𝓞 F) F)) i j =
    (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
  rw [Matrix.of_apply, Matrix.one_apply, Matrix.one_apply, Matrix.one_apply, Pi.zero_apply, add_zero]
  split_ifs with h
  · rfl
  · rfl

theorem exists_ideal_level_subset_of_mem_nhds_one {W : Set (GL (Fin 2) (AdeleRing (𝓞 F) F))}
    (hW : W ∈ 𝓝 (1 : GL (Fin 2) (AdeleRing (𝓞 F) F))) :
    ∃ N : Ideal (𝓞 F), N ≠ ⊥ ∧ ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), glArch (𝓞 F) F g = 1 →
      (∀ i j, (glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F N) →
      (∀ i j, (((glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F N) →
      g ∈ W := by
  classical
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨O, hO, hOW⟩ := hW
  rw [map_one] at hO
  have h1 : ((levelParam F 0 true, MulOpposite.op (levelParam F 0 false)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) × (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))ᵐᵒᵖ) = 1 := by
    rw [levelParam_zero, levelParam_zero, MulOpposite.op_one]; rfl
  have hO' : (fun f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F =>
      (levelParam F f true, MulOpposite.op (levelParam F f false))) ⁻¹' O ∈
        𝓝 (0 : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F) := by
    refine (continuous_levelParamPair F).continuousAt.preimage_mem_nhds ?_
    show O ∈ 𝓝 ((levelParam F 0 true, MulOpposite.op (levelParam F 0 false)))
    rw [h1]; exact hO
  rw [nhds_pi, Filter.mem_pi'] at hO'
  obtain ⟨I, t, ht, hIO⟩ := hO'
  have hD : (⋂ k, t k) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.mpr fun k => ht k
  obtain ⟨N, hN, hNB⟩ := exists_idealBall_subset_of_mem_nhds_zero F hD
  refine ⟨N, hN, fun g hg hg1 hg2 => ?_⟩
  let f : Bool × Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F := fun k => match k with
    | (true, i, j) => (glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
    | (false, i, j) => (((glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
  have hf : f ∈ Set.pi (↑I) t := fun k _ => by
    have hk : f k ∈ idealBall (𝓞 F) F N := by
      obtain ⟨b, i, j⟩ := k
      cases b
      · exact hg2 i j
      · exact hg1 i j
    exact Set.mem_iInter.mp (hNB hk) k
  have hmem := hIO hf
  apply hOW
  show Units.embedProduct _ g ∈ O
  rw [Units.embedProduct_apply]
  have hval : (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = levelParam F f true := by
    refine Matrix.ext fun i j => Prod.ext ?_ ?_
    · show ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
        = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
      rw [← glArch_apply, hg, Units.val_one]
    · show ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
        = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
          + ((glFin (𝓞 F) F g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
            - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
      rw [← glFin_apply, add_sub_cancel]
  have hinv : ((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = levelParam F f false := by
    refine Matrix.ext fun i j => Prod.ext ?_ ?_
    · show (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
        = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
      rw [← glArch_apply, map_inv, hg, inv_one, Units.val_one]
    · show (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
        = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
          + ((((glFin (𝓞 F) F g)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
            - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
      rw [← glFin_apply, map_inv, add_sub_cancel]
  rw [hval, hinv]
  exact hmem

section Conj

variable {A : Type*} [CommRing A]

theorem unipotentGL2_inv_eq (y : A) : (unipotentGL2 y)⁻¹ = unipotentGL2 (-y) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

theorem conj_unipotentGL2_inv (k : GL (Fin 2) A) (y : A) :
    (k⁻¹ * unipotentGL2 y * k)⁻¹ = k⁻¹ * unipotentGL2 (-y) * k := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, unipotentGL2_inv_eq, mul_assoc]

theorem coe_conj_unipotentGL2_sub_one (k : GL (Fin 2) A) (y : A) :
    ((k⁻¹ * unipotentGL2 y * k : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) - 1
      = ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) * (!![1, y; 0, 1] - 1)
          * (k : Matrix (Fin 2) (Fin 2) A) := by
  rw [Units.val_mul, Units.val_mul, unipotentGL2_coe, mul_sub, sub_mul, mul_one, Units.inv_mul]

theorem conj_unipotentGL2_sub_one_apply (k : GL (Fin 2) A) (y : A) (i j : Fin 2) :
    ((k⁻¹ * unipotentGL2 y * k : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j
        - (1 : Matrix (Fin 2) (Fin 2) A) i j
      = ((k⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i 0 * y * (k : Matrix (Fin 2) (Fin 2) A) 1 j := by
  have h := congrFun (congrFun (coe_conj_unipotentGL2_sub_one k y) i) j
  rw [Matrix.sub_apply] at h
  rw [h]
  have hE : (!![1, y; 0, 1] - 1 : Matrix (Fin 2) (Fin 2) A) = !![0, y; 0, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp
  rw [hE]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one] <;> ring

end Conj

theorem glArch_unipotentGL2 (t : AdeleRing (𝓞 F) F) :
    glArch (𝓞 F) F (unipotentGL2 t) = unipotentGL2 (adeleArch (𝓞 F) F t) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_unipotentGL2 (t : AdeleRing (𝓞 F) F) :
    glFin (𝓞 F) F (unipotentGL2 t) = unipotentGL2 (adeleFin (𝓞 F) F t) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

variable {F}

theorem glArch_conj_unipotentGL2 (x : GL (Fin 2) (AdeleRing (𝓞 F) F)) {t : AdeleRing (𝓞 F) F}
    (ht : adeleArch (𝓞 F) F t = 0) : glArch (𝓞 F) F (x⁻¹ * unipotentGL2 t * x) = 1 := by
  rw [map_mul, map_mul, map_inv, glArch_unipotentGL2, ht, unipotentGL2_zero, mul_one, inv_mul_cancel]

theorem glFin_conj_unipotentGL2_sub_one_mem {N : Ideal (𝓞 F)} (x : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (hx : glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F) {t : AdeleRing (𝓞 F) F} (ht : adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F N)
    (i j : Fin 2) :
    (glFin (𝓞 F) F (x⁻¹ * unipotentGL2 t * x) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F N := by
  rw [map_mul, map_mul, map_inv, glFin_unipotentGL2, conj_unipotentGL2_sub_one_apply]
  exact mul_mem_idealBall_right (mul_mem_idealBall_left ((mem_finiteIntegralGL2_iff.mp hx).2 i 0) ht)
    ((mem_finiteIntegralGL2_iff.mp hx).1 1 j)

theorem glFin_conj_unipotentGL2_inv_sub_one_mem {N : Ideal (𝓞 F)} (x : GL (Fin 2) (AdeleRing (𝓞 F) F))
    (hx : glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F) {t : AdeleRing (𝓞 F) F} (ht : adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F N)
    (i j : Fin 2) :
    (((glFin (𝓞 F) F (x⁻¹ * unipotentGL2 t * x))⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F N := by
  rw [map_mul, map_mul, map_inv, glFin_unipotentGL2, conj_unipotentGL2_inv, conj_unipotentGL2_sub_one_apply]
  exact mul_mem_idealBall_right
    (mul_mem_idealBall_left ((mem_finiteIntegralGL2_iff.mp hx).2 i 0) (neg_mem_idealBall ht))
    ((mem_finiteIntegralGL2_iff.mp hx).1 1 j)

end NumberFieldAdelic

section Row

variable {F : Type} [Field F] [NumberField F]

theorem exists_ideal_forall_apply_mul_eq_of_level {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧ ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 →
      (∀ i j, (glFin (𝓞 F) F k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F 𝔫) →
      (∀ i j, (((glFin (𝓞 F) F k)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
        - (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j ∈ idealBall (𝓞 F) F 𝔫) →
      ∀ g : AdelicGL2 (𝓞 F) F, φ (g * k) = φ g := by
  have hopen : IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := hφ
  obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp hopen
  have h1W : (1 : AdelicGL2 (𝓞 F) F) ∈ W := by
    have h1 : (1 : finiteAdelicGL2Subgroup F) ∈ Subtype.val ⁻¹' W := by
      rw [hWeq]; exact Subgroup.one_mem _
    exact h1
  obtain ⟨𝔫, h𝔫, hlevel⟩ := exists_ideal_level_subset_of_mem_nhds_one F (hWo.mem_nhds h1W)
  refine ⟨𝔫, h𝔫, fun k hk hk1 hk2 g => ?_⟩
  have hkW : k ∈ W := hlevel k hk hk1 hk2
  have hkfin : k ∈ finiteAdelicGL2Subgroup F := (mem_finiteAdelicGL2Subgroup_iff F k).mpr hk
  have hstab : (⟨k, hkfin⟩ : finiteAdelicGL2Subgroup F) ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) := by
    rw [← SetLike.mem_coe, ← hWeq]; exact hkW
  have h := congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ => RightTranslationFn.toFun f g)
    (MulAction.mem_stabilizer_iff.mp hstab)
  rw [Subgroup.smul_def, RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at h
  exact h

end Row

end KfLevel

namespace CuspidalConstituent
namespace Conj
section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def rT (a : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u x := u (x * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lT (a : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u x := u (a * x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rT_apply (a : G) (u : G → ℂ) (x : G) : rT a u x = u (x * a) := rfl
@[scoped simp] theorem lT_apply (a : G) (u : G → ℂ) (x : G) : lT a u x = u (a * x) := rfl

theorem rT_mul (a b : G) (u : G → ℂ) : rT (a * b) u = rT a (rT b u) := by
  funext x; simp [mul_assoc]

theorem lT_mem_typeSubmodule {ι : H →* G} {ρ : Representation ℂ H W} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) (a : G) : lT a f ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun f _ => lT a f ∈ typeSubmodule ι ρ) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hS : IsRightEquivariant ι ρ ((lT a) ∘ₗ T) := by
      intro k' v' x
      show T (ρ k' v') (a * x) = T v' (a * (x * ι k'))
      rw [hT k' v' (a * x), mul_assoc]
    exact mem_typeSubmodule_of_isRightEquivariant hS v
  · show lT a 0 ∈ typeSubmodule ι ρ
    rw [map_zero]; exact (typeSubmodule ι ρ).zero_mem
  · intro u₁ u₂ _ _ hu hw
    show lT a (u₁ + u₂) ∈ typeSubmodule ι ρ
    rw [map_add]; exact (typeSubmodule ι ρ).add_mem hu hw
  · intro c u₁ _ hu
    show lT a (c • u₁) ∈ typeSubmodule ι ρ
    rw [map_smul]; exact (typeSubmodule ι ρ).smul_mem c hu

theorem rT_mem_typeSubmodule_of_commute {ι : H →* G} {ρ : Representation ℂ H W} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) (g : G) (hg : ∀ k : H, Commute g (ι k)) : rT g f ∈ typeSubmodule ι ρ :=
  comp_mul_mem_typeSubmodule_of_commute hf g hg

theorem rT_mem_typeSubmodule_self {ι : H →* G} {ρ : Representation ℂ H W} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) (k : H) : rT (ι k) f ∈ typeSubmodule ι ρ :=
  comp_mul_mem_typeSubmodule hf k

end TypePiece

section Adelic

open NumberField IsDedekindDomain NumberField.AdelicLevel

variable (F : Type) [Field F] [NumberField F]

theorem map_mem_iSup_of_forall {M : Type*} [AddCommGroup M] [Module ℂ M] {ι₀ : Type*}
    (Λ : M →ₗ[ℂ] M) (S : ι₀ → Submodule ℂ M) (h : ∀ i, ∀ u ∈ S i, Λ u ∈ S i) {u : M}
    (hu : u ∈ ⨆ i, S i) : Λ u ∈ ⨆ i, S i := by
  have hle : (⨆ i, S i) ≤ (⨆ i, S i).comap Λ :=
    iSup_le fun i => fun v hv => Submodule.mem_comap.mpr (le_iSup S i (h i v hv))
  exact hle hu

theorem commute_of_glArch_eq_one_of_glFin_eq_one {a b : AdelicGL2 (𝓞 F) F}
    (ha : glArch (𝓞 F) F a = 1) (hb : glFin (𝓞 F) F b = 1) : Commute a b := by
  have h1 : glArch (𝓞 F) F (a * b) = glArch (𝓞 F) F (b * a) := by rw [map_mul, map_mul, ha, one_mul, mul_one]
  have h2 : glFin (𝓞 F) F (a * b) = glFin (𝓞 F) F (b * a) := by rw [map_mul, map_mul, hb, one_mul, mul_one]
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · show (((a * b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 =
      (((b * a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
    rw [← glArch_apply, ← glArch_apply, h1]
  · show (((a * b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 =
      (((b * a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
    rw [← glFin_apply, ← glFin_apply, h2]

def StabilisesPieces (c : AdelicGL2 (𝓞 F) F) : Prop :=
  ∀ (w : InfinitePlace F) (τ : ArchRepAt F w),
    (∀ u ∈ archTypeSubmoduleAt F w τ, rT c u ∈ archTypeSubmoduleAt F w τ) ∧
    (∀ u ∈ archDualTypeSubmoduleAt F w τ, rT c u ∈ archDualTypeSubmoduleAt F w τ)

theorem rT_one_eq (u : AdelicGL2 (𝓞 F) F → ℂ) : rT (1 : AdelicGL2 (𝓞 F) F) u = u :=
  funext fun x => by rw [rT_apply, mul_one]

theorem stabilisesPieces_one : StabilisesPieces F 1 := fun w τ =>
  ⟨fun u hu => by rw [rT_one_eq]; exact hu, fun u hu => by rw [rT_one_eq]; exact hu⟩

theorem StabilisesPieces.mul {a b : AdelicGL2 (𝓞 F) F} (ha : StabilisesPieces F a) (hb : StabilisesPieces F b) :
    StabilisesPieces F (a * b) := fun w τ =>
  ⟨fun u hu => by rw [rT_mul]; exact (ha w τ).1 _ ((hb w τ).1 u hu),
   fun u hu => by rw [rT_mul]; exact (ha w τ).2 _ ((hb w τ).2 u hu)⟩

theorem stabilisesPieces_of_mem_finiteAdelic {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    StabilisesPieces F g := by
  have hc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), Commute g (rowIsometryInclAt₀ F w k) :=
    fun w k => commute_of_glArch_eq_one_of_glFin_eq_one F hg (glFin_rowIsometryInclAt₀ F w k)
  intro w τ
  exact ⟨fun u hu => rT_mem_typeSubmodule_of_commute hu g (hc w),
    fun u hu => rT_mem_typeSubmodule_of_commute hu g (hc w)⟩

theorem stabilisesPieces_rowIsometryInclAt₀ (w' : InfinitePlace F) (k : rowIsometrySubgroup₀ w'.Completion) :
    StabilisesPieces F (rowIsometryInclAt₀ F w' k) := by
  intro w τ
  by_cases hw : w = w'
  · subst hw
    exact ⟨fun u hu => rT_mem_typeSubmodule_self hu k, fun u hu => rT_mem_typeSubmodule_self hu k⟩
  · have hc : ∀ k'' : rowIsometrySubgroup₀ w.Completion, Commute (rowIsometryInclAt₀ F w' k) (rowIsometryInclAt₀ F w k'') :=
      fun k'' => commute_adelicArchGLInclAt_of_ne F (fun h => hw h.symm) _ _
    exact ⟨fun u hu => rT_mem_typeSubmodule_of_commute hu _ hc, fun u hu => rT_mem_typeSubmodule_of_commute hu _ hc⟩

theorem stabilisesPieces_of_mem_iSup {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    StabilisesPieces F k ∧ glFin (𝓞 F) F k = 1 := by
  refine Subgroup.iSup_induction (fun w : InfinitePlace F => (rowIsometryInclAt₀ F w).range)
    (C := fun k => StabilisesPieces F k ∧ glFin (𝓞 F) F k = 1) hk ?_ ?_ ?_
  · rintro w _ ⟨k', rfl⟩
    exact ⟨stabilisesPieces_rowIsometryInclAt₀ F w k', glFin_rowIsometryInclAt₀ F w k'⟩
  · exact ⟨stabilisesPieces_one F, map_one _⟩
  · rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    exact ⟨ha.mul F hb, by rw [map_mul, ha1, hb1, one_mul]⟩

theorem StabilisesPieces.rT_mem_archCutSubmodule {c : AdelicGL2 (𝓞 F) F} (hc : StabilisesPieces F c)
    (tys : ArchTypeFamily F) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archCutSubmodule F tys) :
    rT c u ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hu ⊢
  exact fun w => map_mem_iSup_of_forall (rT c) _ (fun i v hv => (hc w (tys.rep w i)).1 v hv) (hu w)

theorem StabilisesPieces.rT_mem_archDualCutSubmodule {c : AdelicGL2 (𝓞 F) F} (hc : StabilisesPieces F c)
    (tys : ArchTypeFamily F) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archDualCutSubmodule F tys) :
    rT c u ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hu ⊢
  exact fun w => map_mem_iSup_of_forall (rT c) _ (fun i v hv => (hc w (tys.rep w i)).2 v hv) (hu w)

theorem lT_mem_archCutSubmodule (a : AdelicGL2 (𝓞 F) F) (tys : ArchTypeFamily F)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archCutSubmodule F tys) : lT a u ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hu ⊢
  exact fun w => map_mem_iSup_of_forall (lT a) _ (fun i v hv => lT_mem_typeSubmodule hv a) (hu w)

theorem lT_mem_archDualCutSubmodule (a : AdelicGL2 (𝓞 F) F) (tys : ArchTypeFamily F)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archDualCutSubmodule F tys) : lT a u ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hu ⊢
  exact fun w => map_mem_iSup_of_forall (lT a) _ (fun i v hv => lT_mem_typeSubmodule hv a) (hu w)

omit [NumberField F] in
open scoped Classical in

theorem archEntries_conj (c a : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (c * a * c⁻¹) = fun i j => ∑ l, (∑ m, archEntries F c i m * archEntries F a m l) *
      archEntries F (c⁻¹) l j := by
  funext i j
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

open scoped Classical in

theorem isArchTestFactor_conj {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    (c : GL (Fin 2) (InfiniteAdeleRing F)) : IsArchTestFactor F (fun a => fa (c * a * c⁻¹)) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨⟨fun E => Φ (fun i j => ∑ l, (∑ m, archEntries F c i m * E m l) * archEntries F (c⁻¹) l j), ?_, ?_⟩, ?_⟩
  · refine hΦ.comp ?_
    refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
    refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun m _ => ?_) contDiff_const
    exact contDiff_const.mul (contDiff_apply_apply ℝ (mixedEmbedding.mixedSpace F) m l)
  · intro a
    show fa (c * a * c⁻¹) = Φ _
    rw [hfaΦ, archEntries_conj]
  ·
    have heq : (fun a => fa (c * a * c⁻¹)) = fa ∘ ((Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)) := by
      funext a; rfl
    rw [heq]
    exact hsupp.comp_homeomorph _

theorem isFinTestFactor_conj {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} (hff : IsFinTestFactor F ff)
    (c : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : IsFinTestFactor F (fun b => ff (c * b * c⁻¹)) := by
  obtain ⟨hlc, hsupp⟩ := hff
  have heq : (fun b => ff (c * b * c⁻¹)) = ff ∘ ((Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)) := by
    funext b; rfl
  rw [heq]
  exact ⟨hlc.comp_continuous (Homeomorph.continuous _), hsupp.comp_homeomorph _⟩

end Adelic

end Conj

end CuspidalConstituent

namespace LevelSplit

open scoped Classical

variable {K : Type} [Field K] [NumberField K]

def cut (S : Finset (HeightOneSpectrum (𝓞 K))) (x : FiniteAdeleRing (𝓞 K) K)
    (c : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) : FiniteAdeleRing (𝓞 K) K :=
  ⟨fun v => if v ∈ S then ((c v : v.adicCompletionIntegers K) : v.adicCompletion K) else x v, by
    filter_upwards [x.2] with v hv
    by_cases h : v ∈ S
    · simp only [h, ite_true]; exact SetLike.coe_mem _
    · simp only [h, ite_false]; exact hv⟩

theorem cut_apply_of_mem {S : Finset (HeightOneSpectrum (𝓞 K))} (x : FiniteAdeleRing (𝓞 K) K)
    (c : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    cut S x c v = c v := by
  show (if v ∈ S then ((c v : v.adicCompletionIntegers K) : v.adicCompletion K) else x v) = _
  rw [ite_eq_left hv]

theorem cut_apply_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 K))} (x : FiniteAdeleRing (𝓞 K) K)
    (c : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    cut S x c v = x v := by
  show (if v ∈ S then ((c v : v.adicCompletionIntegers K) : v.adicCompletion K) else x v) = _
  rw [ite_eq_right hv]

def deltaInt (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletionIntegers K :=
  if i = j then 1 else 0

theorem coe_deltaInt (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)) :
    ((deltaInt (K := K) i j v : v.adicCompletionIntegers K) : v.adicCompletion K) =
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
  unfold deltaInt
  by_cases h : i = j
  · subst h; rw [ite_eq_left rfl, Matrix.one_apply_eq]; rfl
  · rw [ite_eq_right h, Matrix.one_apply_ne h]; rfl

def offS (S : Finset (HeightOneSpectrum (𝓞 K))) (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
  fun i j => cut S (M i j) (deltaInt i j)

theorem mapMatrix_offS_of_mem {S : Finset (HeightOneSpectrum (𝓞 K))} (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    (finAdeleEval (𝓞 K) K v).mapMatrix (offS S M) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, offS, finAdeleEval_apply]
  rw [cut_apply_of_mem _ _ hv, coe_deltaInt]

theorem mapMatrix_offS_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 K))}
    (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    (finAdeleEval (𝓞 K) K v).mapMatrix (offS S M) = (finAdeleEval (𝓞 K) K v).mapMatrix M := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, offS, finAdeleEval_apply]
  rw [cut_apply_of_not_mem _ _ hv]

theorem offS_mul_offS_inv (S : Finset (HeightOneSpectrum (𝓞 K))) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    offS S (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) *
      offS S ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) = 1 := by
  refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K fun v => ?_
  rw [map_mul, map_one]
  by_cases hv : v ∈ S
  · rw [mapMatrix_offS_of_mem _ hv, mapMatrix_offS_of_mem _ hv, one_mul]
  · rw [mapMatrix_offS_of_not_mem _ hv, mapMatrix_offS_of_not_mem _ hv, ← map_mul,
      ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, map_one]

theorem offS_inv_mul_offS (S : Finset (HeightOneSpectrum (𝓞 K))) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    offS S ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) *
      offS S (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) = 1 := by
  have := offS_mul_offS_inv S g⁻¹
  rwa [inv_inv] at this

def offSGL (S : Finset (HeightOneSpectrum (𝓞 K))) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) where
  val := offS S (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
  inv := offS S ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
  val_inv := offS_mul_offS_inv S g
  inv_val := offS_inv_mul_offS S g

theorem finComponent_offSGL_of_mem {S : Finset (HeightOneSpectrum (𝓞 K))} (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : finComponent (𝓞 K) K v (offSGL S g) = 1 := by
  refine Units.ext ?_
  show (finAdeleEval (𝓞 K) K v).mapMatrix (offS S (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) = _
  rw [mapMatrix_offS_of_mem _ hv, Matrix.GeneralLinearGroup.coe_one]

theorem finComponent_offSGL_of_not_mem {S : Finset (HeightOneSpectrum (𝓞 K))} (g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) : finComponent (𝓞 K) K v (offSGL S g) = finComponent (𝓞 K) K v g := by
  refine Units.ext ?_
  show (finAdeleEval (𝓞 K) K v).mapMatrix (offS S (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))) =
    (finAdeleEval (𝓞 K) K v).mapMatrix (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
  rw [mapMatrix_offS_of_not_mem _ hv]

theorem isLevelOneMatrix_offS (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (M : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    (hint : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ i j, (M i j) v ∈ v.adicCompletionIntegers K) :
    IsLevelOneMatrix (𝓞 K) K N (offS S M) := by

  have hbound : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → idealBound (𝓞 K) N v = 1 := by
    intro v hv
    have hndvd : ¬ v.asIdeal ∣ N := fun h => hv (hNS v h)
    have hN : N ≠ ⊥ := by
      rintro rfl
      exact hndvd (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
    exact idealBound_eq_one_of_not_dvd hN hndvd
  have hentry : ∀ (i j : Fin 2) (v : HeightOneSpectrum (𝓞 K)), (offS S M i j) v ∈ v.adicCompletionIntegers K := by
    intro i j v
    by_cases hv : v ∈ S
    · show cut S (M i j) (deltaInt i j) v ∈ _
      rw [cut_apply_of_mem _ _ hv]; exact SetLike.coe_mem _
    · show cut S (M i j) (deltaInt i j) v ∈ _
      rw [cut_apply_of_not_mem _ _ hv]; exact hint v hv i j
  refine ⟨⟨fun i j v => hentry i j v, fun v => ?_⟩, fun v => ?_⟩
  · by_cases hv : v ∈ S
    · show Valued.v (cut S (M 1 0) (deltaInt 1 0) v) ≤ _
      rw [cut_apply_of_mem _ _ hv, coe_deltaInt, Matrix.one_apply_ne (by decide), map_zero]
      exact zero_le
    · rw [hbound v hv]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hentry 1 0 v)
  · rw [coe_sub_apply, coe_one_apply]
    by_cases hv : v ∈ S
    · show Valued.v (cut S (M 1 1) (deltaInt 1 1) v - 1) ≤ _
      rw [cut_apply_of_mem _ _ hv, coe_deltaInt, Matrix.one_apply_eq, sub_self, map_zero]
      exact zero_le
    · rw [hbound v hv]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (sub_mem (hentry 1 1 v) (one_mem _))

theorem gl_ext {a b : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K a = glArch (𝓞 K) K b)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 K),
      finComponent (𝓞 K) K w (glFin (𝓞 K) K a) = finComponent (𝓞 K) K w (glFin (𝓞 K) K b)) : a = b := by
  refine Units.ext (matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 K) K ?_ ?_)
  · exact congrArg (fun u : GL (Fin 2) (InfiniteAdeleRing K) => (u : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) h₁
  · refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 K) K fun w => ?_
    exact congrArg (fun u : GL (Fin 2) (w.adicCompletion K) => (u : Matrix (Fin 2) (Fin 2) (w.adicCompletion K))) (h₂ w)

end LevelSplit

namespace SliceTensor



section Generic

variable {A : Type*} [CommRing A]

theorem mul_unipotent_mul_apply (M₁ M₂ : Matrix (Fin 2) (Fin 2) A) (τ : A) (i j : Fin 2) :
    (M₁ * !![1, τ; 0, 1] * M₂) i j = (M₁ * M₂) i j + M₁ i 0 * τ * M₂ 1 j := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem coe_mul_unipotentGL2_mul (G₁ G₂ : GL (Fin 2) A) (τ : A) :
    ((G₁ * unipotentGL2 τ * G₂ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
      = (G₁ : Matrix (Fin 2) (Fin 2) A) * !![1, τ; 0, 1] * (G₂ : Matrix (Fin 2) (Fin 2) A) := by
  rw [Units.val_mul, Units.val_mul, unipotentGL2_coe]

theorem retract_apply (G₁ G₂ : GL (Fin 2) A) (τ : A) :
    ((G₁⁻¹ * (G₁ * unipotentGL2 τ * G₂) * G₂⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1 = τ := by
  have h : G₁⁻¹ * (G₁ * unipotentGL2 τ * G₂) * G₂⁻¹ = unipotentGL2 τ := by group
  rw [h, unipotentGL2_coe]
  rfl

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_unipotentGL2 : Continuous (unipotentGL2 : A → GL (Fin 2) A) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun τ : A => ((unipotentGL2 τ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
    simp only [unipotentGL2_coe]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · show Continuous fun τ : A => (((unipotentGL2 τ)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A)
    have h : (fun τ : A => (((unipotentGL2 τ)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A))
        = fun τ => !![1, -τ; 0, 1] := rfl
    rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_mul_unipotentGL2_mul (G₁ G₂ : GL (Fin 2) A) :
    Continuous fun τ : A => G₁ * unipotentGL2 τ * G₂ :=
  (continuous_const.mul continuous_unipotentGL2).mul continuous_const

theorem continuous_retract (G₁ G₂ : GL (Fin 2) A) :
    Continuous fun M : GL (Fin 2) A => ((G₁⁻¹ * M * G₂⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1 :=
  (Units.continuous_val.comp ((continuous_const.mul continuous_id).mul continuous_const)).matrix_elem 0 1

theorem hasCompactSupport_comp_mul_unipotentGL2_mul [T2Space A] {φ : GL (Fin 2) A → ℂ}
    (hφ : HasCompactSupport φ) (G₁ G₂ : GL (Fin 2) A) :
    HasCompactSupport fun τ : A => φ (G₁ * unipotentGL2 τ * G₂) := by
  refine HasCompactSupport.intro
    ((hφ.isCompact).image (continuous_retract G₁ G₂)) fun τ hτ => ?_
  by_contra hne
  refine hτ ⟨G₁ * unipotentGL2 τ * G₂, subset_tsupport _ (Function.mem_support.2 hne), ?_⟩
  exact retract_apply G₁ G₂ τ

end Generic

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "e" => InfiniteAdeleRing.ringEquiv_mixedSpace F

theorem glArch_unipotentGL2 (s : 𝔸) :
    AdelicLevel.glArch (𝓞 F) F (unipotentGL2 s) = unipotentGL2 s.1 := by
  apply Units.ext
  ext i j
  rw [AdelicLevel.glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_unipotentGL2 (s : 𝔸) :
    AdelicLevel.glFin (𝓞 F) F (unipotentGL2 s) = unipotentGL2 s.2 := by
  apply Units.ext
  ext i j
  rw [AdelicLevel.glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

omit [NumberField F] in

theorem archEntries_mul_unipotentGL2_mul (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F))
    (σ : mixedEmbedding.mixedSpace F) :
    archEntries F (G₁ * unipotentGL2 ((e).symm σ) * G₂)
      = fun i j => e (((G₁ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
            * (G₂ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) i j)
          + e ((G₁ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i 0) * σ
            * e ((G₂ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 j) := by
  funext i j
  rw [archEntries_apply, coe_mul_unipotentGL2_mul, mul_unipotent_mul_apply, map_add, map_mul, map_mul,
    RingEquiv.apply_symm_apply]

theorem contDiff_archFactor {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F)) :
    ContDiff ℝ (⊤ : ℕ∞) fun σ : mixedEmbedding.mixedSpace F => fa (G₁ * unipotentGL2 ((e).symm σ) * G₂) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩ := hfa
  have h : (fun σ : mixedEmbedding.mixedSpace F => fa (G₁ * unipotentGL2 ((e).symm σ) * G₂))
      = Φ ∘ fun σ => fun i j => e (((G₁ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
            * (G₂ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) i j)
          + e ((G₁ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i 0) * σ
            * e ((G₂ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 j) := by
    funext σ
    rw [hfaΦ, archEntries_mul_unipotentGL2_mul]
    rfl
  rw [h]
  refine hΦ.comp ?_
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  exact contDiff_const.add ((contDiff_const.mul contDiff_id).mul contDiff_const)

theorem hasCompactSupport_archFactor {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : IsArchTestFactor F fa) (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F)) :
    HasCompactSupport fun σ : mixedEmbedding.mixedSpace F => fa (G₁ * unipotentGL2 ((e).symm σ) * G₂) := by

  have h1 : HasCompactSupport fun τ : InfiniteAdeleRing F => fa (G₁ * unipotentGL2 τ * G₂) :=
    hasCompactSupport_comp_mul_unipotentGL2_mul hfa.2 G₁ G₂
  refine HasCompactSupport.intro ((h1.isCompact).image (continuous_ringEquiv_mixedSpace F)) fun σ hσ => ?_
  by_contra hne
  refine hσ ⟨(e).symm σ, subset_tsupport _ (Function.mem_support.2 hne), ?_⟩
  exact RingEquiv.apply_symm_apply _ _

def archFactorSchwartz {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F)) : 𝓢(mixedEmbedding.mixedSpace F, ℂ) :=
  (hasCompactSupport_archFactor F hfa G₁ G₂).toSchwartzMap (contDiff_archFactor F hfa G₁ G₂)

theorem archFactorSchwartz_apply {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    (G₁ G₂ : GL (Fin 2) (InfiniteAdeleRing F)) (σ : mixedEmbedding.mixedSpace F) :
    archFactorSchwartz F hfa G₁ G₂ σ = fa (G₁ * unipotentGL2 ((e).symm σ) * G₂) := rfl

theorem isLocallyConstant_finFactor {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hff : IsFinTestFactor F ff) (G₁ G₂ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    IsLocallyConstant fun τ : FiniteAdeleRing (𝓞 F) F => ff (G₁ * unipotentGL2 τ * G₂) :=
  hff.1.comp_continuous (continuous_mul_unipotentGL2_mul G₁ G₂)

theorem hasCompactSupport_finFactor {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hff : IsFinTestFactor F ff) (G₁ G₂ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    HasCompactSupport fun τ : FiniteAdeleRing (𝓞 F) F => ff (G₁ * unipotentGL2 τ * G₂) :=
  hasCompactSupport_comp_mul_unipotentGL2_mul hff.2 G₁ G₂

theorem gate_unipotentGL2_one_ne_one : (unipotentGL2 (1 : F) : GL (Fin 2) F) ≠ 1 := by
  intro h
  have h01 := congrArg (fun M : GL (Fin 2) F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp [unipotentGL2_coe] at h01

theorem gate_zero (g₁ g₂ : GL (Fin 2) 𝔸) :
    (fun s : 𝔸 => (fun _ : GL (Fin 2) 𝔸 => (0 : ℂ)) (g₁ * unipotentGL2 s * g₂)) ∈ pureTensorSet F :=
  zero_mem_pureTensorSet

end SliceTensor

/-- **`Kf`-smoothness propagates along the level.** A `Kf`-smooth function has a level ideal beyond which
the conjugate-unipotent translate acts trivially. -/
theorem IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
    {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) :
    ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ (g x : AdelicGL2 (𝓞 F) F), glFin (𝓞 F) F x ∈ finiteIntegralGL2 (𝓞 F) F →
      ∀ (t : AdeleRing (𝓞 F) F), adeleArch (𝓞 F) F t = 0 →
        adeleFin (𝓞 F) F t ∈ idealBall (𝓞 F) F 𝔫 →
          φ (g * (x⁻¹ * unipotentGL2 t * x)) = φ g := by
  obtain ⟨𝔫, h𝔫, hlevel⟩ := KfLevel.exists_ideal_forall_apply_mul_eq_of_level hφ
  exact ⟨𝔫, h𝔫, fun g x hx t ht0 htN => hlevel _ (KfLevel.glArch_conj_unipotentGL2 x ht0)
    (KfLevel.glFin_conj_unipotentGL2_sub_one_mem x hx htN)
    (KfLevel.glFin_conj_unipotentGL2_inv_sub_one_mem x hx htN) g⟩

open CuspidalConstituent.Conj in
/-- **Conjugation preserves the test-function class.** A conjugated factorizable, archimedean-bi-finite
test function is again one. -/
theorem CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj
    (F : Type) [Field F] [NumberField F]
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F)
    (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ tys' : ArchTypeFamily F,
      IsFactorizableTestFn F (fun y => f ((g * k) * y * (g * k)⁻¹)) ∧
      IsArchBiFinite F tys' (fun y => f ((g * k) * y * (g * k)⁻¹)) := by
  classical
  generalize hc : g * k = c
  have hstab : StabilisesPieces F c⁻¹ := by
    rw [← hc, mul_inv_rev]
    exact (stabilisesPieces_of_mem_iSup F ((⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range).inv_mem hk)).1.mul F
      (stabilisesPieces_of_mem_finiteAdelic F ((finiteAdelicGL2Subgroup F).inv_mem hg))
  refine ⟨tys, ?_, ?_⟩
  ·
    obtain ⟨fa, ff, hfa, hff, hfact⟩ := hf
    refine ⟨fun a => fa (glArch (𝓞 F) F c * a * (glArch (𝓞 F) F c)⁻¹),
      fun b => ff (glFin (𝓞 F) F c * b * (glFin (𝓞 F) F c)⁻¹),
      isArchTestFactor_conj F hfa _, isFinTestFactor_conj F hff _, fun y => ?_⟩
    simp only [hfact, map_mul, map_inv]
  ·
    obtain ⟨hL, hR⟩ := hbf
    constructor
    · have heq : (fun x => (fun y => f (c * y * c⁻¹)) x⁻¹) = lT c (rT c⁻¹ (fun x => f x⁻¹)) := by
        funext x
        show f (c * x⁻¹ * c⁻¹) = f (c * x * c⁻¹)⁻¹
        congr 1; group
      show (fun x => (fun y => f (c * y * c⁻¹)) x⁻¹) ∈ archCutSubmodule F tys
      rw [heq]
      exact lT_mem_archCutSubmodule F c tys (hstab.rT_mem_archCutSubmodule F tys hL)
    · have heq : (fun y => f (c * y * c⁻¹)) = lT c (rT c⁻¹ f) := funext fun y => rfl
      rw [heq]
      exact lT_mem_archDualCutSubmodule F c tys (hstab.rT_mem_archDualCutSubmodule F tys hR)

/-- **Factoring off the level.** An element that is integral at a chosen place is, up to the level-one and
finite-`K` subgroup, a matrix that commutes with the local embedding there. -/
theorem exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (z : AdelicGL2 (𝓞 K) K)
    (hz : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) :
    ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
      z₂ ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
        z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁ := by
  classical
  refine ⟨z * (finEmbed (𝓞 K) K (LevelSplit.offSGL S (glFin (𝓞 K) K z)))⁻¹,
    finEmbed (𝓞 K) K (LevelSplit.offSGL S (glFin (𝓞 K) K z)), by rw [inv_mul_cancel_right], ?_, ?_⟩
  ·
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · show glFin (𝓞 K) K (finEmbed (𝓞 K) K (LevelSplit.offSGL S (glFin (𝓞 K) K z))) ∈ finiteLevelOne (𝓞 K) K N
      rw [glFin_finEmbed, mem_finiteLevelOne_iff]
      have hint : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ i j,
          ((glFin (𝓞 K) K z : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) v ∈ v.adicCompletionIntegers K := by
        intro v hv i j
        have h := ((mem_localIntegralSet K v).mp (hz v hv)).1 i j
        rwa [finComponent_apply] at h
      have hint' : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ i j,
          ((((glFin (𝓞 K) K z)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
              Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) v ∈ v.adicCompletionIntegers K := by
        intro v hv i j
        have h := ((mem_localIntegralSet K v).mp (hz v hv)).2 i j
        rwa [← map_inv, finComponent_apply] at h
      exact ⟨LevelSplit.isLevelOneMatrix_offS N S hNS _ hint, LevelSplit.isLevelOneMatrix_offS N S hNS _ hint'⟩
    · rw [mem_finiteAdelicGL2Subgroup_iff, glArch_finEmbed]
  ·
    intro v hv xv
    have hP : UnramifiedWhittaker.placeEmbed K v xv = finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v xv) := rfl
    refine LevelSplit.gl_ext ?_ fun w => ?_
    · simp only [map_mul, map_inv, hP, glArch_finEmbed, inv_one, mul_one, one_mul]
    · simp only [map_mul, map_inv, hP, glFin_finEmbed]
      by_cases hw : w = v
      · subst hw
        rw [LevelSplit.finComponent_offSGL_of_not_mem _ hv, finComponent_localEmbed_self, mul_inv_cancel, one_mul,
          mul_one]
      · rw [finComponent_localEmbed_of_ne _ _ _ _ hw, mul_one, one_mul]

/-- **Pure tensors under the unipotent translate.** A factorizable test function composed with a
unipotent translate stays in the pure-tensor set. -/
theorem IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet
    (F : Type) [Field F] [NumberField F]
    {f : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → ℂ}
    (hf : AutomorphicForm.IsFactorizableTestFn F f)
    (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
    (fun s => f (g₁ * AutomorphicForm.unipotentGL2 s * g₂)) ∈ NumberField.AdelicFourier.pureTensorSet F := by
  classical
  obtain ⟨fa, ff, hfa, hff, hprod⟩ := hf
  refine ⟨SliceTensor.archFactorSchwartz F hfa (AdelicLevel.glArch (𝓞 F) F g₁) (AdelicLevel.glArch (𝓞 F) F g₂),
    fun τ => ff (AdelicLevel.glFin (𝓞 F) F g₁ * unipotentGL2 τ * AdelicLevel.glFin (𝓞 F) F g₂),
    SliceTensor.isLocallyConstant_finFactor F hff _ _, SliceTensor.hasCompactSupport_finFactor F hff _ _, ?_⟩
  funext s
  rw [hprod, map_mul, map_mul, map_mul, map_mul, SliceTensor.glArch_unipotentGL2,
    SliceTensor.glFin_unipotentGL2, SliceTensor.archFactorSchwartz_apply, RingEquiv.symm_apply_apply]

end AutomorphicForm
