/-
  The right-translate span and what it implies.

  Three rows on the span of the right translates of a function and its consequences, from the generic
  to the adelic:

  * `exists_sum_prod_mul_of_rightTranslatesSpanFinite` is generic group theory: for finitely many
    pairwise-commuting subgroups `Kᵢ`, a function whose right translates by every `Kᵢ` lie in a
    finite-dimensional span splits as a finite sum `∑ m, (∏ i, a m i (k i)) * b m x` — the tensor split
    the adelic arguments use to move a product of level conditions off the argument;
  * `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` turns a finite sum of right
    translates of a level-invariant function into a *depth*: invariance under `lowerUnipotentGL2 γ` for
    every `γ` integral outside `S` and deep enough inside it;
  * `exists_isArchBiFinite_rightConv_comp_inv` keeps archimedean bi-finiteness under the reflexion
    convolution `f' * (x ↦ f x⁻¹)`.

  The three pins are *flattened* files whose declarations are all public (24, 34, 23 of them); the
  subject namespaces of the pins are search-stage labels and are renamed to subject names here:
  `RightFiniteTensorSplit` → `TensorSplit`, `RS24` → `UnipotentDepth`, `BIFIN` → `ArchBiFinite`.
  Every engine is transcribed at the pin's last name; the three rows are the pins' `solution`s.

  Build record (AF88A).

  * Imports: **no line was added** to the scaffold's five. The rows are leaves (0 graph premises;
    `tools/deps/premise_imports.py --nodes <the three rows> --missing-from this module --olean` →
    "nothing to add"), and the proofs' needs — `diagOne`/`finIncl`/`localUnit`
    (`NumberTheory/AdelicLevel/HeckeGen.lean`) and `finAdeleEval`/`adeleArch`/`adeleFin`
    (`…/Projections.lean`) — are already in the closure through `NumberTheory/AdelicLevel/Level.lean`.
  * Heartbeat probe, **never installed** (FR-0225): silent at `12000`, fails at `11000`
    (and at `6000`); the cost is the pin's `tensor_split` (`whnf`/`isDefEq` timeouts inside it).
    Measured with the edit loop, `lake env lean -DautoImplicit=false -DmaxHeartbeats=<cap>`; the
    module is silent at the project's own `200000`, a ~17× margin, so no floor is carried.
  * v4.34 proof-side drift in the pins' bodies: `continuous_mul_right` → `continuous_mul_const`
    (pin 3 `:194`), `zero_le'` → `zero_le`, `if_pos`/`if_neg`/`dif_pos` →
    `ite_eq_left`/`ite_eq_right`/`dite_eq_left`, `haveI`/`letI` → `have`/`let` (FR-0223), and one
    dead `first | … | simp […]` branch removed in each of
    `glArch_lowerUnipotentGL2_eq_one`/`glArch_diagOne_eq_one` (pin 2 `:101`/`:206`). No statement was
    touched.
  * Two declaration-scoped lint silencers are carried, both for the pin's own unused binders, which
    the call sites use and which renaming would re-spell (FR-0218): `linter.unusedVariables false`
    on `UnipotentDepth.translateFamily_apply_mul_lowerUnipotentGL2` (pin 2 `:160`, the unused `S`) and
    `linter.unusedVariables`/`linter.unusedSectionVars` on `ArchBiFinite.exists_linear_right`/
    `exists_linear_left` (pin 3 `:210`/`:241`, the unused `w` and the `include hfc hfs` the pin carries).

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_sum_prod_mul_of_rightTranslatesSpanFinite.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isArchBiFinite_rightConv_comp_inv.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.NumberTheory.AdelicLevel.Level

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm
open scoped Classical ENNReal NNReal Matrix BigOperators ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

/-! ### The tensor split (pin `RightFiniteTensorSplit`) -/

namespace TensorSplit

variable {G : Type*} [Group G]

def rt (h : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun v := fun x => v (x * h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rt_apply (h : G) (v : G → ℂ) (x : G) : rt h v x = v (x * h) := rfl

theorem rt_mul (h k : G) (v : G → ℂ) : rt (h * k) v = rt h (rt k v) := by
  funext x
  simp [mul_assoc]

theorem rt_one (v : G → ℂ) : rt (1 : G) v = v := by
  funext x
  simp

theorem rt_comm {h k : G} (hc : Commute h k) (v : G → ℂ) : rt h (rt k v) = rt k (rt h v) := by
  rw [← rt_mul, ← rt_mul, hc.eq]

def lt (x : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun v := fun g => v (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem lt_apply (x : G) (v : G → ℂ) (g : G) : lt x v g = v (x * g) := rfl

def RFin (K : Subgroup G) (f : G → ℂ) : Prop :=
  ∃ s : Finset (G → ℂ), ∀ k ∈ K, (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))

theorem RFin.rt_mem {K : Subgroup G} {f : G → ℂ} {s : Finset (G → ℂ)}
    (hs : ∀ k ∈ K, (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ)))
    {k : G} (hk : k ∈ K) : rt k f ∈ Submodule.span ℂ (s : Set (G → ℂ)) :=
  hs k hk

def prodSet {n : ℕ} (K : Fin n → Subgroup G) : Set G :=
  {x | ∃ k : Fin n → G, (∀ i, k i ∈ K i) ∧ x = (List.ofFn k).prod}

theorem prod_mem_prodSet {n : ℕ} (K : Fin n → Subgroup G) {k : Fin n → G} (hk : ∀ i, k i ∈ K i) :
    (List.ofFn k).prod ∈ prodSet K :=
  ⟨k, hk, rfl⟩

theorem one_mem_prodSet {n : ℕ} (K : Fin n → Subgroup G) : (1 : G) ∈ prodSet K := by
  refine ⟨fun _ => 1, fun i => (K i).one_mem, ?_⟩
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ]

theorem single_mem_prodSet :
    ∀ {n : ℕ} (K : Fin n → Subgroup G) (i : Fin n) {κ : G}, κ ∈ K i → κ ∈ prodSet K := by
  intro n
  induction n with
  | zero => intro K i; exact i.elim0
  | succ n ih =>
    intro K i κ hκ
    induction i using Fin.cases with
    | zero =>
      refine ⟨Fin.cons κ (fun _ => (1 : G)), ?_, ?_⟩
      · intro j
        induction j using Fin.cases with
        | zero => simpa using hκ
        | succ j => simp [(K j.succ).one_mem]
      · rw [List.ofFn_succ, List.prod_cons]
        simp only [Fin.cons_zero, Fin.cons_succ]
        rw [List.prod_eq_one, mul_one]
        intro x hx
        rw [List.mem_ofFn] at hx
        obtain ⟨_, rfl⟩ := hx
        rfl
    | succ j =>
      obtain ⟨k', hk', hprod⟩ := ih (fun i => K i.succ) j hκ
      refine ⟨Fin.cons (1 : G) k', ?_, ?_⟩
      · intro l
        induction l using Fin.cases with
        | zero => simp [(K 0).one_mem]
        | succ l => simpa using hk' l
      · rw [List.ofFn_succ, List.prod_cons]
        simp only [Fin.cons_zero, Fin.cons_succ, one_mul]
        exact hprod

theorem prodSet_subset_iSup {n : ℕ} (K : Fin n → Subgroup G) :
    prodSet K ⊆ ((⨆ i, K i : Subgroup G) : Set G) := by
  rintro x ⟨k, hk, rfl⟩
  refine Subgroup.list_prod_mem _ ?_
  intro y hy
  rw [List.mem_ofFn] at hy
  obtain ⟨i, rfl⟩ := hy
  exact Subgroup.mem_iSup_of_mem i (hk i)

theorem commute_head_tail {n : ℕ} (K : Fin (n + 1) → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y)
    {κ : G} (hκ : κ ∈ K 0) {k : Fin n → G} (hk : ∀ i, k i ∈ K i.succ) :
    Commute κ (List.ofFn k).prod := by
  refine Commute.list_prod_right _ _ ?_
  intro y hy
  rw [List.mem_ofFn] at hy
  obtain ⟨i, rfl⟩ := hy
  exact hcomm 0 i.succ (Fin.succ_ne_zero i).symm κ hκ (k i) (hk i)

theorem exists_finset_span_prod :
    ∀ (n : ℕ) (K : Fin n → Subgroup G)
      (_hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y)
      (f : G → ℂ) (_hf : ∀ i, RFin (K i) f),
      ∃ S : Finset (G → ℂ), ∀ k : Fin n → G, (∀ i, k i ∈ K i) →
        rt (List.ofFn k).prod f ∈ Submodule.span ℂ (S : Set (G → ℂ)) := by
  intro n
  induction n with
  | zero =>
    intro K _ f _
    refine ⟨{f}, fun k _ => ?_⟩
    have : (List.ofFn k).prod = 1 := by simp
    rw [this, rt_one]
    exact Submodule.subset_span (by simp)
  | succ n ih =>
    intro K hcomm f hf
    classical

    obtain ⟨s0, hs0⟩ := hf 0
    let T0 : Set (G → ℂ) := {v | ∃ κ ∈ K 0, v = rt κ f}
    let V0 : Submodule ℂ (G → ℂ) := Submodule.span ℂ T0
    have hV0le : V0 ≤ Submodule.span ℂ (s0 : Set (G → ℂ)) := by
      refine Submodule.span_le.2 ?_
      rintro v ⟨κ, hκ, rfl⟩
      exact hs0 κ hκ
    have : FiniteDimensional ℂ V0 := by
      have : FiniteDimensional ℂ (Submodule.span ℂ (s0 : Set (G → ℂ))) :=
        FiniteDimensional.span_of_finite ℂ s0.finite_toSet
      exact Submodule.finiteDimensional_of_le hV0le
    let d := Module.finrank ℂ V0
    let bs : Module.Basis (Fin d) ℂ V0 := Module.finBasis ℂ V0

    have hrep : ∀ p : Fin d, ∃ (m : ℕ) (c : Fin m → ℂ) (κ : Fin m → G),
        (∀ l, κ l ∈ K 0) ∧ ((bs p : V0) : G → ℂ) = ∑ l, c l • rt (κ l) f := by
      intro p
      have hmem : ((bs p : V0) : G → ℂ) ∈ Submodule.span ℂ T0 := (bs p).2
      rw [Submodule.mem_span_set'] at hmem
      obtain ⟨m, c, g, hg⟩ := hmem
      have hg' : ∀ l, ∃ κ ∈ K 0, ((g l : T0) : G → ℂ) = rt κ f := fun l => (g l).2
      choose κ hκK hκeq using hg'
      refine ⟨m, c, κ, hκK, ?_⟩
      rw [← hg]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hκeq l]
    choose m c κ hκK hκeq using hrep

    have hbs_fin : ∀ p : Fin d, ∀ i : Fin n, RFin (K i.succ) ((bs p : V0) : G → ℂ) := by
      intro p i
      obtain ⟨si, hsi⟩ := hf i.succ
      refine ⟨Finset.univ.biUnion (fun l : Fin (m p) => si.image (rt (κ p l))), ?_⟩
      intro k hk
      change rt k ((bs p : V0) : G → ℂ) ∈ _
      rw [hκeq p, map_sum]
      refine Submodule.sum_mem _ (fun l _ => ?_)
      rw [LinearMap.map_smul]
      refine Submodule.smul_mem _ _ ?_
      have hc : Commute k (κ p l) :=
        hcomm i.succ 0 (Fin.succ_ne_zero i) k hk (κ p l) (hκK p l)
      rw [rt_comm hc]

      have h1 : rt k f ∈ Submodule.span ℂ (si : Set (G → ℂ)) := hsi k hk
      have h2 : rt (κ p l) (rt k f) ∈ (Submodule.span ℂ (si : Set (G → ℂ))).map (rt (κ p l)) :=
        Submodule.mem_map_of_mem h1
      rw [Submodule.map_span] at h2
      refine Submodule.span_mono ?_ h2
      intro v hv
      obtain ⟨w, hw, rfl⟩ := hv
      simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion,
        Finset.coe_image]
      exact ⟨l, Set.mem_image_of_mem _ hw⟩

    have htail : ∀ p : Fin d, ∃ S : Finset (G → ℂ), ∀ k : Fin n → G, (∀ i, k i ∈ K i.succ) →
        rt (List.ofFn k).prod ((bs p : V0) : G → ℂ) ∈ Submodule.span ℂ (S : Set (G → ℂ)) := by
      intro p
      refine ih (fun i => K i.succ) ?_ _ (hbs_fin p)
      intro i j hij x hx y hy
      exact hcomm i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) x hx y hy
    choose S hS using htail
    refine ⟨Finset.univ.biUnion S, ?_⟩
    intro k hk

    rw [List.ofFn_succ, List.prod_cons]
    have hc : Commute (k 0) (List.ofFn (fun i => k i.succ)).prod :=
      commute_head_tail K hcomm (hk 0) (fun i => hk i.succ)
    rw [hc.eq, rt_mul]

    have hmemV0 : rt (k 0) f ∈ V0 := Submodule.subset_span ⟨k 0, hk 0, rfl⟩
    have hexp : rt (k 0) f = ∑ p, (bs.repr ⟨rt (k 0) f, hmemV0⟩ p) • ((bs p : V0) : G → ℂ) := by
      have hsum := bs.sum_repr (⟨rt (k 0) f, hmemV0⟩ : V0)
      have hval := congrArg (fun w : V0 => (w : G → ℂ)) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hval
      exact hval.symm
    rw [hexp, map_sum]
    refine Submodule.sum_mem _ (fun p _ => ?_)
    rw [LinearMap.map_smul]
    refine Submodule.smul_mem _ _ ?_
    have := hS p (fun i => k i.succ) (fun i => hk i.succ)
    refine Submodule.span_mono ?_ this
    intro v hv
    simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true, Set.mem_iUnion]
    exact ⟨p, hv⟩

section Coeff

variable {n : ℕ} (K : Fin n → Subgroup G)
  (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y)
  (f : G → ℂ) (hf : ∀ i, RFin (K i) f)

def W : Submodule ℂ (G → ℂ) := Submodule.span ℂ {v | ∃ h ∈ prodSet K, v = rt h f}

theorem f_mem_W : f ∈ W K f :=
  Submodule.subset_span ⟨1, one_mem_prodSet K, by rw [rt_one]⟩

include hcomm hf in
theorem finiteDimensional_W : FiniteDimensional ℂ (W K f) := by
  obtain ⟨S, hS⟩ := exists_finset_span_prod n K hcomm f hf
  have hle : W K f ≤ Submodule.span ℂ (S : Set (G → ℂ)) := by
    refine Submodule.span_le.2 ?_
    rintro v ⟨h, ⟨k, hk, rfl⟩, rfl⟩
    exact hS k hk
  have : FiniteDimensional ℂ (Submodule.span ℂ (S : Set (G → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ S.finite_toSet
  exact Submodule.finiteDimensional_of_le hle

end Coeff

omit [Group G] in

theorem exists_eval_combination (W : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ W]
    (φ : Module.Dual ℂ W) :
    ∃ (m : ℕ) (e : Fin m → ℂ) (x : Fin m → G), ∀ w : W, φ w = ∑ l, e l * (w : G → ℂ) (x l) := by
  classical
  let ev : G → Module.Dual ℂ W := fun x => (LinearMap.proj x).comp W.subtype
  have hev : ∀ x (w : W), ev x w = (w : G → ℂ) x := fun x w => rfl
  let Φ : Submodule ℂ (Module.Dual ℂ W) := Submodule.span ℂ (Set.range ev)
  have hco : Φ.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    rw [Submodule.mem_bot]
    apply Subtype.ext
    funext x
    have := hw (ev x) (Submodule.subset_span ⟨x, rfl⟩)
    rw [hev] at this
    simpa using this
  have hΦ : Φ = ⊤ := by
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := Φ)
    rw [hco, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  have hφ : φ ∈ Φ := by rw [hΦ]; exact Submodule.mem_top
  rw [Submodule.mem_span_set'] at hφ
  obtain ⟨m, e, g, hg⟩ := hφ
  have hg' : ∀ l, ∃ x, ev x = ((g l : Set.range ev) : Module.Dual ℂ W) := fun l => (g l).2
  choose x hx using hg'
  refine ⟨m, e, x, fun w => ?_⟩
  rw [← hg]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [LinearMap.smul_apply, ← hx l, hev, smul_eq_mul]

def iterMulVec {d : ℕ} : (n : ℕ) → (Fin n → Matrix (Fin d) (Fin d) ℂ) → (Fin d → ℂ) → (Fin d → ℂ)
  | 0, _, c => c
  | n + 1, M, c => Matrix.mulVec (M 0) (iterMulVec n (fun i => M i.succ) c)

theorem iterMulVec_eq_sum_paths {d : ℕ} :
    ∀ (n : ℕ) (M : Fin n → Matrix (Fin d) (Fin d) ℂ) (c : Fin d → ℂ) (p : Fin d),
      iterMulVec n M c p
        = ∑ r : Fin n → Fin d,
            (∏ i : Fin n, M i ((Fin.cons p r : Fin (n + 1) → Fin d) (Fin.castSucc i))
                ((Fin.cons p r : Fin (n + 1) → Fin d) i.succ))
              * c ((Fin.cons p r : Fin (n + 1) → Fin d) (Fin.last n)) := by
  intro n
  induction n with
  | zero =>
    intro M c p
    simp [iterMulVec]
  | succ n ih =>
    intro M c p
    classical
    simp only [iterMulVec, Matrix.mulVec, dotProduct]
    simp_rw [ih (fun i => M i.succ) c]

    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']

    refine Finset.sum_bij' (fun qr _ => Fin.cons qr.1 qr.2) (fun r _ => (r 0, fun i => r i.succ))
      ?_ ?_ ?_ ?_ ?_
    · intro qr _; exact Finset.mem_univ _
    · intro r _; exact Finset.mem_univ _
    · intro qr _; ext <;> simp
    · intro r _; funext i; refine Fin.cases ?_ ?_ i <;> simp
    · intro qr _
      obtain ⟨q, r'⟩ := qr

      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero]
      have e1 : ∀ i : Fin n, (Fin.cons p (Fin.cons q r' : Fin (n + 1) → Fin d) : Fin (n + 2) → Fin d)
          (Fin.castSucc i.succ) = (Fin.cons q r' : Fin (n + 1) → Fin d) (Fin.castSucc i) := by
        intro i
        rw [← Fin.succ_castSucc, Fin.cons_succ]
      have e2 : (Fin.cons p (Fin.cons q r' : Fin (n + 1) → Fin d) : Fin (n + 2) → Fin d) (Fin.last (n + 1))
          = (Fin.cons q r' : Fin (n + 1) → Fin d) (Fin.last n) := by
        rw [← Fin.succ_last, Fin.cons_succ]
      simp_rw [e1]
      rw [e2]
      ring

theorem tensor_split {n : ℕ} (K : Fin n → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y)
    (f : G → ℂ)
    (hf : ∀ i, ∃ s : Finset (G → ℂ), ∀ k ∈ K i,
      (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))) :
    ∃ (N : ℕ) (a : Fin N → Fin n → G → ℂ) (b : Fin N → G → ℂ),
      (∀ m i, a m i ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ x h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun g => f (x * g * h)}) ∧
      (∀ m i, ∃ t : Finset (G → ℂ), ∀ k' ∈ K i,
          (fun g => a m i (g * k')) ∈ Submodule.span ℂ (t : Set (G → ℂ))) ∧
      (∀ m, b m ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun x => f (x * h)}) ∧
      ∀ (x : G) (k : Fin n → G), (∀ i, k i ∈ K i) →
        f (x * (List.ofFn k).prod) = ∑ m, (∏ i, a m i (k i)) * b m x := by
  classical
  have hf' : ∀ i, RFin (K i) f := hf
  have : FiniteDimensional ℂ (W K f) := finiteDimensional_W K hcomm f hf'

  let d := Module.finrank ℂ (W K f)
  let bs : Module.Basis (Fin d) ℂ (W K f) := Module.finBasis ℂ (W K f)
  have hcoord := fun p : Fin d => exists_eval_combination (W K f) (bs.coord p)
  choose mC e xs hxs using hcoord

  let α : Fin d → Fin d → G → ℂ := fun p q g => ∑ l, e p l * ((bs q : W K f) : G → ℂ) (xs p l * g)

  have hstab : ∀ {h : G}, h ∈ prodSet K → ∀ w : W K f, rt h (w : G → ℂ) ∈ W K f := by
    intro h hh w
    obtain ⟨k, hk, rfl⟩ := hh
    have : (w : G → ℂ) ∈ W K f := w.2
    refine Submodule.span_induction (p := fun v _ => rt (List.ofFn k).prod v ∈ W K f) ?_ ?_ ?_ ?_ this
    · rintro v ⟨h', ⟨k', hk', rfl⟩, rfl⟩

      rw [← rt_mul]
      refine Submodule.subset_span ⟨_, ?_, rfl⟩

      suffices hmul : ∀ (n : ℕ) (K : Fin n → Subgroup G),
          (∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y) →
          ∀ k k' : Fin n → G, (∀ i, k i ∈ K i) → (∀ i, k' i ∈ K i) →
            (List.ofFn k).prod * (List.ofFn k').prod = (List.ofFn (fun i => k i * k' i)).prod by
        rw [hmul n K hcomm k k' hk hk']
        exact prod_mem_prodSet K (fun i => (K i).mul_mem (hk i) (hk' i))
      intro n
      induction n with
      | zero => intro K _ k k' _ _; simp
      | succ n ihn =>
        intro K hK k k' hk hk'
        rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
          List.prod_cons]
        have hc : Commute (k' 0) (List.ofFn (fun i => k i.succ)).prod :=
          commute_head_tail K hK (hk' 0) (fun i => hk i.succ)
        have ih' := ihn (fun i => K i.succ)
          (fun i j hij x hx y hy => hK i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) x hx y hy)
          (fun i => k i.succ) (fun i => k' i.succ) (fun i => hk i.succ) (fun i => hk' i.succ)
        calc k 0 * (List.ofFn fun i => k i.succ).prod * (k' 0 * (List.ofFn fun i => k' i.succ).prod)
            = k 0 * ((List.ofFn fun i => k i.succ).prod * k' 0)
                * (List.ofFn fun i => k' i.succ).prod := by simp [mul_assoc]
          _ = k 0 * (k' 0 * (List.ofFn fun i => k i.succ).prod)
                * (List.ofFn fun i => k' i.succ).prod := by rw [hc.eq]
          _ = k 0 * k' 0 * ((List.ofFn fun i => k i.succ).prod
                * (List.ofFn fun i => k' i.succ).prod) := by simp [mul_assoc]
          _ = k 0 * k' 0 * (List.ofFn fun i => k i.succ * k' i.succ).prod := by rw [ih']
    · simp
    · intro v w _ _ hv hw
      rw [map_add]
      exact Submodule.add_mem _ hv hw
    · intro c v _ hv
      rw [LinearMap.map_smul]
      exact Submodule.smul_mem _ _ hv

  have hco : ∀ p (w : W K f), bs.coord p w = ∑ l, e p l * (w : G → ℂ) (xs p l) := hxs

  have hα : ∀ p q {h : G} (hh : h ∈ prodSet K),
      α p q h = bs.coord p ⟨rt h ((bs q : W K f) : G → ℂ), hstab hh (bs q)⟩ := by
    intro p q h hh
    rw [hco p]
    rfl

  have hstep : ∀ q {h : G} (hh : h ∈ prodSet K) (y : G),
      ((bs q : W K f) : G → ℂ) (y * h) = ∑ p, α p q h * ((bs p : W K f) : G → ℂ) y := by
    intro q h hh y
    have hsum := bs.sum_repr (⟨rt h ((bs q : W K f) : G → ℂ), hstab hh (bs q)⟩ : W K f)
    have hval := congrArg (fun w : W K f => (w : G → ℂ) y) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hval
    rw [rt_apply] at hval
    rw [← hval]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hα p q hh]
    rfl

  have hfmem : f ∈ W K f := f_mem_W K f
  let cf : Fin d → ℂ := fun q => bs.repr ⟨f, hfmem⟩ q
  have hfexp : ∀ y : G, f y = ∑ q, cf q * ((bs q : W K f) : G → ℂ) y := by
    intro y
    have hsum := bs.sum_repr (⟨f, hfmem⟩ : W K f)
    have hval := congrArg (fun w : W K f => (w : G → ℂ) y) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hval
    exact hval.symm

  have hiter : ∀ (m : ℕ) (k : Fin m → G), (∀ i, k i ∈ prodSet K) → ∀ (c : Fin d → ℂ) (y : G),
      (∑ q, c q * ((bs q : W K f) : G → ℂ) (y * (List.ofFn k).prod))
        = ∑ p, iterMulVec m (fun i => Matrix.of (fun p' q' => α p' q' (k i))) c p
            * ((bs p : W K f) : G → ℂ) y := by
    intro m
    induction m with
    | zero =>
      intro k _ c y
      simp [iterMulVec]
    | succ m ihm =>
      intro k hk c y
      rw [List.ofFn_succ, List.prod_cons, ← mul_assoc]
      rw [ihm (fun i => k i.succ) (fun i => hk i.succ) c (y * k 0)]
      simp_rw [hstep _ (hk 0) y]
      simp only [iterMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun p' _ => ?_))
      ring

  let ι := Fin d × (Fin n → Fin d)
  let N := Fintype.card ι
  let eqv : ι ≃ Fin N := Fintype.equivFin ι
  let sP : ι → Fin (n + 1) → Fin d := fun t => Fin.cons t.1 t.2
  let aι : ι → Fin n → G → ℂ := fun t i g => α (sP t (Fin.castSucc i)) (sP t i.succ) g
  let bι : ι → G → ℂ := fun t y => cf (sP t (Fin.last n)) * ((bs t.1 : W K f) : G → ℂ) y

  let Tgt : Submodule ℂ (G → ℂ) := Submodule.span ℂ
      {ψ : G → ℂ | ∃ x h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun g => f (x * g * h)}
  have key : ∀ (x : G) (w : G → ℂ), w ∈ W K f → (fun g => w (x * g)) ∈ Tgt := by
    intro x w hw
    refine Submodule.span_induction (p := fun v _ => (fun g => v (x * g)) ∈ Tgt) ?_ ?_ ?_ ?_ hw
    · rintro v ⟨h, hh, rfl⟩
      refine Submodule.subset_span ⟨x, h, prodSet_subset_iSup K hh, ?_⟩
      funext g
      simp [mul_assoc]
    · show (fun g : G => (0 : G → ℂ) (x * g)) ∈ Tgt
      have h0 : (fun g : G => (0 : G → ℂ) (x * g)) = 0 := by funext g; rfl
      rw [h0]
      exact Tgt.zero_mem
    · intro v w _ _ hv hw
      show (fun g : G => (v + w) (x * g)) ∈ Tgt
      have hadd : (fun g : G => (v + w) (x * g)) = (fun g => v (x * g)) + (fun g => w (x * g)) := by
        funext g; rfl
      rw [hadd]
      exact Tgt.add_mem hv hw
    · intro c v _ hv
      show (fun g : G => (c • v) (x * g)) ∈ Tgt
      have hsm : (fun g : G => (c • v) (x * g)) = c • (fun g => v (x * g)) := by
        funext g; rfl
      rw [hsm]
      exact Tgt.smul_mem c hv
  refine ⟨N, fun m => aι (eqv.symm m), fun m => bι (eqv.symm m), ?_, ?_, ?_, ?_⟩
  ·
    intro m i
    change (fun g => ∑ l, e (sP (eqv.symm m) (Fin.castSucc i)) l
        * ((bs (sP (eqv.symm m) i.succ) : W K f) : G → ℂ) (xs (sP (eqv.symm m) (Fin.castSucc i)) l * g))
      ∈ _
    have hsum : (fun g => ∑ l, e (sP (eqv.symm m) (Fin.castSucc i)) l
        * ((bs (sP (eqv.symm m) i.succ) : W K f) : G → ℂ) (xs (sP (eqv.symm m) (Fin.castSucc i)) l * g))
        = ∑ l, e (sP (eqv.symm m) (Fin.castSucc i)) l
          • (fun g => ((bs (sP (eqv.symm m) i.succ) : W K f) : G → ℂ)
              (xs (sP (eqv.symm m) (Fin.castSucc i)) l * g)) := by
      funext g
      simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsum]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (key _ _ (bs _).2))
  ·
    intro m i
    show ∃ t : Finset (G → ℂ), ∀ k' ∈ K i,
      (fun g => aι (eqv.symm m) i (g * k')) ∈ Submodule.span ℂ (t : Set (G → ℂ))
    refine ⟨Finset.univ.image (fun p' => α (sP (eqv.symm m) (Fin.castSucc i)) p'), ?_⟩
    intro k' hk'
    have hk'P : k' ∈ prodSet K := single_mem_prodSet K i hk'
    have hfun : (fun g => aι (eqv.symm m) i (g * k'))
        = ∑ p', α p' (sP (eqv.symm m) i.succ) k' • α (sP (eqv.symm m) (Fin.castSucc i)) p' := by
      funext g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      change (∑ l, e (sP (eqv.symm m) (Fin.castSucc i)) l
          * ((bs (sP (eqv.symm m) i.succ) : W K f) : G → ℂ)
              (xs (sP (eqv.symm m) (Fin.castSucc i)) l * (g * k'))) = _
      have hb : ∀ l, ((bs (sP (eqv.symm m) i.succ) : W K f) : G → ℂ)
          (xs (sP (eqv.symm m) (Fin.castSucc i)) l * (g * k'))
          = ∑ p', α p' (sP (eqv.symm m) i.succ) k'
              * ((bs p' : W K f) : G → ℂ) (xs (sP (eqv.symm m) (Fin.castSucc i)) l * g) := by
        intro l
        rw [← mul_assoc]
        exact hstep _ hk'P _
      simp_rw [hb, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p' _ => ?_)
      change _ = α p' (sP (eqv.symm m) i.succ) k'
          * ∑ l, e (sP (eqv.symm m) (Fin.castSucc i)) l
              * ((bs p' : W K f) : G → ℂ) (xs (sP (eqv.symm m) (Fin.castSucc i)) l * g)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
    rw [hfun]
    refine Submodule.sum_mem _ (fun p' _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    exact ⟨p', rfl⟩
  ·
    intro m
    have hb : ((bs (eqv.symm m).1 : W K f) : G → ℂ) ∈ W K f := (bs _).2
    have hW : W K f ≤ Submodule.span ℂ
        {ψ : G → ℂ | ∃ h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun x => f (x * h)} := by
      refine Submodule.span_mono ?_
      rintro v ⟨h, hh, rfl⟩
      exact ⟨h, prodSet_subset_iSup K hh, rfl⟩
    have hsm := Submodule.smul_mem _ (cf (sP (eqv.symm m) (Fin.last n))) (hW hb)
    have heq : bι (eqv.symm m) = cf (sP (eqv.symm m) (Fin.last n))
        • ((bs (eqv.symm m).1 : W K f) : G → ℂ) := by
      funext y
      simp [bι, Pi.smul_apply, smul_eq_mul]
    show bι (eqv.symm m) ∈ _
    rw [heq]
    exact hsm
  ·
    intro x k hk
    have hkP : ∀ i, k i ∈ prodSet K := fun i => single_mem_prodSet K i (hk i)
    show f (x * (List.ofFn k).prod) = ∑ t : Fin N, (∏ i, aι (eqv.symm t) i (k i)) * bι (eqv.symm t) x
    rw [show (∑ t : Fin N, (∏ i, aι (eqv.symm t) i (k i)) * bι (eqv.symm t) x)
        = ∑ t : ι, (∏ i, aι t i (k i)) * bι t x from
      Equiv.sum_comp eqv.symm (fun t => (∏ i, aι t i (k i)) * bι t x)]
    rw [hfexp, hiter n k hkP cf x]
    simp_rw [iterMulVec_eq_sum_paths]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [sP, aι, bι, Matrix.of_apply]
    ring

end TensorSplit

/-! ### The depth of a sum of right translates (pin `RS24`) -/

namespace UnipotentDepth

variable (K : Type) [Field K] [NumberField K]

theorem exists_le_exp_nat (x : WithZero (Multiplicative ℤ)) : ∃ k : ℕ, x ≤ WithZero.exp (k : ℤ) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx]; exact zero_le⟩
  · obtain ⟨u, rfl⟩ : ∃ u : Multiplicative ℤ, (u : WithZero (Multiplicative ℤ)) = x :=
      ⟨_, WithZero.coe_unzero hx⟩
    refine ⟨(Multiplicative.toAdd u).toNat, ?_⟩
    show (u : WithZero (Multiplicative ℤ)) ≤
      ((Multiplicative.ofAdd ((Multiplicative.toAdd u).toNat : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    conv_lhs => rw [← ofAdd_toAdd u]
    rw [Multiplicative.ofAdd_le]
    exact Int.self_le_toNat _

def ordAt (N : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk N).factors

theorem idealBound_eq_exp_neg_ordAt {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    idealBound (𝓞 K) N v = WithZero.exp (-(ordAt K N v : ℤ)) :=
  idealBound_of_ne_bot hN v

theorem exists_forall_mul_mem_idealBall {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (b : FiniteAdeleRing (𝓞 K) K) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ c : FiniteAdeleRing (𝓞 K) K,
      (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → c w = 0) →
      (∀ v ∈ S, Valued.v (c v) ≤ WithZero.exp (-(n : ℤ))) →
      c * b ∈ idealBall (𝓞 K) K N := by
  choose k hk using fun v : HeightOneSpectrum (𝓞 K) => exists_le_exp_nat (Valued.v (b v))
  refine ⟨∑ v ∈ S, (k v + ordAt K N v), fun n hn c hc0 hcS w => ?_⟩
  rw [coe_mul_apply, map_mul]
  by_cases hw : w ∈ S
  · have hkle : k w + ordAt K N w ≤ n :=
      (Finset.single_le_sum (f := fun v => k v + ordAt K N v) (fun _ _ => Nat.zero_le _) hw).trans hn
    calc Valued.v (c w) * Valued.v (b w)
        ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (k w : ℤ) := mul_le_mul' (hcS w hw) (hk w)
      _ = WithZero.exp (-(n : ℤ) + k w) := (WithZero.exp_add _ _).symm
      _ ≤ WithZero.exp (-(ordAt K N w : ℤ)) := by
          rw [WithZero.exp_le_exp]; omega
      _ = idealBound (𝓞 K) N w := (idealBound_eq_exp_neg_ordAt K hN w).symm
  · rw [hc0 w hw, map_zero, zero_mul]
    exact zero_le

def E21 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) := !![0, 0; 1, 0]

theorem lowerUnipotentGL2_val_eq (γ : AdeleRing (𝓞 K) K) :
    ((lowerUnipotentGL2 γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + γ • E21 K := by
  rw [lowerUnipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E21]

theorem lowerUnipotentGL2_inv (γ : AdeleRing (𝓞 K) K) :
    (lowerUnipotentGL2 γ : GL (Fin 2) (AdeleRing (𝓞 K) K))⁻¹ = lowerUnipotentGL2 (-γ) := by
  rw [inv_eq_iff_mul_eq_one, ← lowerUnipotentGL2_add, add_neg_cancel, lowerUnipotentGL2_zero]

def Bmat (A : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  ((A⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * E21 K *
    (A : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))

theorem conj_lowerUnipotentGL2_val (A : GL (Fin 2) (AdeleRing (𝓞 K) K)) (γ : AdeleRing (𝓞 K) K) :
    ((A⁻¹ * lowerUnipotentGL2 γ * A : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + γ • Bmat K A := by
  rw [Units.val_mul, Units.val_mul, lowerUnipotentGL2_val_eq, Bmat, Matrix.mul_add, Matrix.mul_one,
    Matrix.add_mul, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_lowerUnipotentGL2_inv_val (A : GL (Fin 2) (AdeleRing (𝓞 K) K)) (γ : AdeleRing (𝓞 K) K) :
    (((A⁻¹ * lowerUnipotentGL2 γ * A)⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + (-γ) • Bmat K A := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, lowerUnipotentGL2_inv, conj_lowerUnipotentGL2_val]

theorem glFin_apply_of_val_eq_one_add_smul (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) (γ : AdeleRing (𝓞 K) K)
    (B : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
    (hg : (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = 1 + γ • B) (p q : Fin 2) :
    (glFin (𝓞 K) K g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p q =
      (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p q + γ.2 * (B p q).2 := by
  rw [glFin_apply, hg, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem glArch_lowerUnipotentGL2_eq_one (γ : AdeleRing (𝓞 K) K) (hγ : γ.1 = 0) :
    glArch (𝓞 K) K (lowerUnipotentGL2 γ) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, lowerUnipotentGL2_coe, Units.val_one]
  fin_cases i <;> fin_cases j <;> first | rfl | simp [hγ]

theorem isLevelOneMatrix_of_entries {N : Ideal (𝓞 K)}
    (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) (c : FiniteAdeleRing (𝓞 K) K)
    (b : Fin 2 → Fin 2 → FiniteAdeleRing (𝓞 K) K)
    (hm : ∀ p q, m p q = (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) p q + c * b p q)
    (hb : ∀ p q, c * b p q ∈ idealBall (𝓞 K) K N) :
    IsLevelOneMatrix (𝓞 K) K N m where
  integral p q := by
    rw [hm]
    refine add_mem_integralFiniteAdeles ?_ (idealBall_subset_integralFiniteAdeles N (hb p q))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
  lowerLeft := by
    rw [hm, Matrix.one_apply_ne (by decide), zero_add]
    exact hb 1 0
  lowerRight := by
    rw [hm, Matrix.one_apply_eq, add_sub_cancel_left]
    exact hb 1 1

theorem exists_depth_conj_lowerUnipotentGL2_mem_levelOne
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    {r : ℕ} (A : Fin r → AdelicGL2 (𝓞 K) K) :
    ∃ nS : ℕ, 0 < nS ∧ ∀ γ : AdeleRing (𝓞 K) K, γ.1 = 0 →
      (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → γ.2 w = 0) →
      (∀ v ∈ S, Valued.v (γ.2 v) ≤ WithZero.exp (-(nS : ℤ))) →
      ∀ i, (A i)⁻¹ * lowerUnipotentGL2 γ * A i ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by

  choose n₀ hn₀ using fun s : Fin r × Fin 2 × Fin 2 × Bool =>
    exists_forall_mul_mem_idealBall K hN S
      (if s.2.2.2 then ((Bmat K (A s.1)) s.2.1 s.2.2.1).2 else (-(Bmat K (A s.1)) s.2.1 s.2.2.1).2)
  refine ⟨1 + ∑ s, n₀ s, by omega, fun γ hγ1 hγ0 hγS i => ?_⟩
  have hle : ∀ s, n₀ s ≤ 1 + ∑ s, n₀ s := fun s => by
    have := Finset.single_le_sum (f := n₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    omega
  have key : ∀ (p q : Fin 2) (sgn : Bool),
      γ.2 * (if sgn then ((Bmat K (A i)) p q).2 else (-(Bmat K (A i)) p q).2) ∈ idealBall (𝓞 K) K N :=
    fun p q sgn => hn₀ (i, p, q, sgn) _ (hle _) γ.2 hγ0 hγS
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    constructor
    · refine isLevelOneMatrix_of_entries K _ γ.2 (fun p q => ((Bmat K (A i)) p q).2)
        (glFin_apply_of_val_eq_one_add_smul K _ γ _ (conj_lowerUnipotentGL2_val K (A i) γ)) fun p q => ?_
      simpa using key p q true
    · rw [← map_inv]
      refine isLevelOneMatrix_of_entries K _ (-γ).2 (fun p q => ((Bmat K (A i)) p q).2)
        (glFin_apply_of_val_eq_one_add_smul K _ (-γ) _ (conj_lowerUnipotentGL2_inv_val K (A i) γ)) fun p q => ?_
      have h := key p q false
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      have e : (-γ).2 * ((Bmat K (A i)) p q).2 = γ.2 * ((-(Bmat K (A i))) p q).2 := by
        show -γ.2 * (Bmat K (A i) p q).2 = γ.2 * -((Bmat K (A i) p q).2)
        ring
      rw [e]
      exact h
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_lowerUnipotentGL2_eq_one K γ hγ1,
      mul_one, inv_mul_cancel]

set_option linter.unusedVariables false in
theorem translateFamily_apply_mul_lowerUnipotentGL2
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)
    {r : ℕ} (A : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * A i))
    (γ : AdeleRing (𝓞 K) K)
    (hγ : ∀ i, (A i)⁻¹ * lowerUnipotentGL2 γ * A i ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (g : AdelicGL2 (𝓞 K) K) :
    x (g * lowerUnipotentGL2 γ) = x g := by
  rw [hxsum, hxsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have h := hx₀lev (g * A i) _ (hγ i)
  rw [show g * A i * ((A i)⁻¹ * lowerUnipotentGL2 γ * A i) = g * lowerUnipotentGL2 γ * A i from by group] at h
  exact h

section LCover

def E11 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) := !![1, 0; 0, 0]

theorem diagOne_val_eq (s : (AdeleRing (𝓞 K) K)ˣ) :
    ((diagOne s : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + ((s : AdeleRing (𝓞 K) K) - 1) • E11 K := by
  ext i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [E11]

def Cmat (κ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  ((κ⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * E11 K *
    (κ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))

theorem conj_diagOne_val (κ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (s : (AdeleRing (𝓞 K) K)ˣ) :
    ((κ⁻¹ * diagOne s * κ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      1 + ((s : AdeleRing (𝓞 K) K) - 1) • Cmat K κ := by
  rw [Units.val_mul, Units.val_mul, diagOne_val_eq, Cmat, Matrix.mul_add, Matrix.mul_one,
    Matrix.add_mul, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_diagOne_inv (κ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (s : (AdeleRing (𝓞 K) K)ˣ) :
    (κ⁻¹ * diagOne s * κ : GL (Fin 2) (AdeleRing (𝓞 K) K))⁻¹ = κ⁻¹ * diagOne s⁻¹ * κ := by
  rw [mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, map_inv]

theorem glArch_diagOne_eq_one (s : (AdeleRing (𝓞 K) K)ˣ) (hs : ((s : AdeleRing (𝓞 K) K)).1 = 1) :
    glArch (𝓞 K) K (diagOne s) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicLevel.glArch_apply, diagOne_coe_apply, Units.val_one]
  fin_cases i <;> fin_cases j <;> first | rfl | simp [hs]

theorem units_inv_snd_apply (s : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 w = (((s : AdeleRing (𝓞 K) K)).2 w)⁻¹ := by
  have h : ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 w * ((s : AdeleRing (𝓞 K) K)).2 w = 1 := by
    have := congrArg (fun x : AdeleRing (𝓞 K) K => x.2 w) s.inv_mul
    exact this
  exact eq_inv_of_mul_eq_one_left h

theorem units_inv_fst (s : (AdeleRing (𝓞 K) K)ˣ) (hs : ((s : AdeleRing (𝓞 K) K)).1 = 1) :
    ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).1 = 1 := by
  have h : ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).1 * ((s : AdeleRing (𝓞 K) K)).1 = 1 :=
    congrArg Prod.fst s.inv_mul
  rwa [hs, mul_one] at h

theorem valued_inv_sub_one {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (hx : Valued.v x = 1) :
    Valued.v (x⁻¹ - 1) = Valued.v (x - 1) := by
  have hx0 : x ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  have : x⁻¹ - 1 = x⁻¹ * (1 - x) := by field_simp
  rw [this, map_mul, map_inv₀, hx, inv_one, one_mul, Valuation.map_sub_swap]

theorem exists_threshold_conj_diagOne_mem_levelOne
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (κ : AdelicGL2 (𝓞 K) K) :
    ∃ n₁ : ℕ, 0 < n₁ ∧ ∀ s : (AdeleRing (𝓞 K) K)ˣ, ((s : AdeleRing (𝓞 K) K)).1 = 1 →
      (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ((s : AdeleRing (𝓞 K) K)).2 w = 1) →
      (∀ v ∈ S, Valued.v (((s : AdeleRing (𝓞 K) K)).2 v) = 1) →
      (∀ v ∈ S, Valued.v (((s : AdeleRing (𝓞 K) K)).2 v - 1) ≤ WithZero.exp (-(n₁ : ℤ))) →
      κ⁻¹ * diagOne s * κ ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  choose n₀ hn₀ using fun s : Fin 2 × Fin 2 => exists_forall_mul_mem_idealBall K hN S ((Cmat K κ) s.1 s.2).2
  refine ⟨1 + ∑ s, n₀ s, by omega, fun s hs1 hsS hsv hclose => ?_⟩
  have hle : ∀ pq, n₀ pq ≤ 1 + ∑ s, n₀ s := fun pq => by
    have := Finset.single_le_sum (f := n₀) (fun _ _ => Nat.zero_le _) (Finset.mem_univ pq)
    omega

  have hc0 : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (((s : AdeleRing (𝓞 K) K)) - 1).2 w = 0 := fun w hw => by
    show ((s : AdeleRing (𝓞 K) K)).2 w - 1 = 0
    rw [hsS w hw, sub_self]
  have hcS : ∀ v ∈ S, Valued.v ((((s : AdeleRing (𝓞 K) K)) - 1).2 v) ≤ WithZero.exp (-((1 + ∑ s, n₀ s : ℕ) : ℤ)) :=
    fun v hv => hclose v hv
  have hc0' : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → (((↑(s⁻¹) : AdeleRing (𝓞 K) K)) - 1).2 w = 0 := fun w hw => by
    show ((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 w - 1 = 0
    rw [units_inv_snd_apply, hsS w hw, inv_one, sub_self]
  have hcS' : ∀ v ∈ S, Valued.v ((((↑(s⁻¹) : AdeleRing (𝓞 K) K)) - 1).2 v) ≤
      WithZero.exp (-((1 + ∑ s, n₀ s : ℕ) : ℤ)) := fun v hv => by
    show Valued.v (((↑(s⁻¹) : AdeleRing (𝓞 K) K)).2 v - 1) ≤ _
    rw [units_inv_snd_apply, valued_inv_sub_one K _ (hsv v hv)]
    exact hclose v hv
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    constructor
    · exact isLevelOneMatrix_of_entries K _ _ (fun p q => ((Cmat K κ) p q).2)
        (glFin_apply_of_val_eq_one_add_smul K _ _ _ (conj_diagOne_val K κ s))
        fun p q => hn₀ (p, q) _ (hle _) _ hc0 hcS
    · rw [← map_inv, conj_diagOne_inv]
      exact isLevelOneMatrix_of_entries K _ _ (fun p q => ((Cmat K κ) p q).2)
        (glFin_apply_of_val_eq_one_add_smul K _ _ _ (conj_diagOne_val K κ s⁻¹))
        fun p q => hn₀ (p, q) _ (hle _) _ hc0' hcS'
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv, glArch_diagOne_eq_one K s hs1, mul_one,
      inv_mul_cancel]

end LCover

section LCoverFinite

theorem exists_finset_sphere_mulCover (v : HeightOneSpectrum (𝓞 K)) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    ∃ Z : Finset (v.adicCompletion K), (∀ z ∈ Z, Valued.v z = WithZero.exp a) ∧
      ∀ u : v.adicCompletion K, Valued.v u = WithZero.exp a →
        ∃ z ∈ Z, Valued.v (z⁻¹ * u - 1) ≤ WithZero.exp (-(n : ℤ)) := by
  by_cases hne : ∃ u₀ : v.adicCompletion K, Valued.v u₀ = WithZero.exp a
  swap
  · refine ⟨∅, by simp, fun u hu => (hne ⟨u, hu⟩).elim⟩
  obtain ⟨u₀, hu₀⟩ := hne
  have hu₀0 : u₀ ≠ 0 := fun h => by rw [h, map_zero] at hu₀; exact WithZero.exp_ne_zero hu₀.symm

  obtain ⟨tn, htn0, htn⟩ := exists_valued_eq_exp_neg (K := K) v n

  have : CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have hO : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr inferInstance

  let B : v.adicCompletion K → Set (v.adicCompletion K) := fun z => {u | Valued.v (u - z) ≤ Valued.v tn}
  have hBopen : ∀ z, IsOpen (B z) := fun z =>
    (isOpen_setOf_valued_le v tn htn0).preimage (continuous_id.sub continuous_const)
  have hcover : (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ⊆ ⋃ z, B z := fun u _ =>
    Set.mem_iUnion.mpr ⟨u, by show Valued.v (u - u) ≤ _; rw [sub_self, map_zero]; exact zero_le⟩
  obtain ⟨T, hT⟩ := hO.elim_finite_subcover B hBopen hcover
  refine ⟨(T.filter fun z => Valued.v z = 1).image (fun z => u₀ * z), ?_, ?_⟩
  · intro z hz
    obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.mp hz
    rw [map_mul, hu₀, (Finset.mem_filter.mp hz₁).2, mul_one]
  · intro u hu

    have hu' : Valued.v (u₀⁻¹ * u) = 1 := by
      rw [map_mul, map_inv₀, hu₀, hu, inv_mul_cancel₀ WithZero.exp_ne_zero]
    have hu'O : u₀⁻¹ * u ∈ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, hu']
    obtain ⟨z, hzT, hz⟩ : ∃ z ∈ T, u₀⁻¹ * u ∈ B z := by
      simpa only [Set.mem_iUnion, exists_prop] using hT hu'O
    have hzclose : Valued.v (u₀⁻¹ * u - z) ≤ WithZero.exp (-(n : ℤ)) := by rw [← htn]; exact hz

    have hlt : Valued.v (z - u₀⁻¹ * u) < Valued.v (u₀⁻¹ * u) := by
      rw [Valuation.map_sub_swap, hu']
      refine lt_of_le_of_lt hzclose ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    have hz1 : Valued.v z = 1 := by
      rw [← hu']
      exact Valuation.map_eq_of_sub_lt Valued.v hlt
    have hz0 : z ≠ 0 := fun h => by rw [h, map_zero] at hz1; exact zero_ne_one hz1
    refine ⟨u₀ * z, Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨hzT, hz1⟩, rfl⟩, ?_⟩
    have e : (u₀ * z)⁻¹ * u - 1 = z⁻¹ * (u₀⁻¹ * u - z) := by field_simp
    rw [e, map_mul, map_inv₀, hz1, inv_one, one_mul]
    exact hzclose

end LCoverFinite

section LCoverMain

variable {K}

def unitOf {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) : (v.adicCompletion K)ˣ :=
  if h : x = 0 then 1 else Units.mk0 x h

theorem unitOf_coe {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (hx : x ≠ 0) :
    (unitOf x : v.adicCompletion K) = x := by
  simp [unitOf, hx]

variable (K)

def shellIdele (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) :
    (AdeleRing (𝓞 K) K)ˣ :=
  ∏ v ∈ S, Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (unitOf (z v)))

theorem finAdele_prod_apply {ι : Type*} (s : Finset ι) (f : ι → FiniteAdeleRing (𝓞 K) K)
    (w : HeightOneSpectrum (𝓞 K)) : (∏ i ∈ s, f i) w = ∏ i ∈ s, f i w :=
  map_prod (finAdeleEval (𝓞 K) K w) f s

theorem shellIdele_fst (S : Finset (HeightOneSpectrum (𝓞 K))) (z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) :
    ((shellIdele K S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := by
  rw [shellIdele, Units.coe_prod]
  change adeleArch (𝓞 K) K (∏ i ∈ S, ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K i (unitOf (z i))) :
    (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) = 1
  rw [map_prod]
  exact Finset.prod_eq_one fun v _ => rfl

theorem shellIdele_snd_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (z : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K) (w : HeightOneSpectrum (𝓞 K)) :
    ((shellIdele K S z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w =
      if w ∈ S then ((unitOf (z w) : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := by
  rw [shellIdele, Units.coe_prod]
  change ((finAdeleEval (𝓞 K) K w).comp (adeleFin (𝓞 K) K))
    (∏ i ∈ S, ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K i (unitOf (z i))) :
      (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) = _
  rw [map_prod]
  have h : ∀ v ∈ S, ((finAdeleEval (𝓞 K) K w).comp (adeleFin (𝓞 K) K))
      (((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v (unitOf (z v))) :
        (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) =
        if v = w then ((unitOf (z w) : (w.adicCompletion K)ˣ) : w.adicCompletion K) else 1 := by
    intro v _
    show ((localUnit (𝓞 K) K v (unitOf (z v)) : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) w = _
    by_cases hvw : v = w
    · subst hvw
      rw [ite_eq_left rfl]
      exact localUnit_apply_self _ _ _ _
    · rw [ite_eq_right hvw]
      exact localUnit_apply_of_ne _ _ _ _ (Ne.symm hvw)
  rw [Finset.prod_congr rfl h, Finset.prod_ite_eq']

theorem exists_finset_diagOne_mul_mem_mul_levelOne
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (κ : AdelicGL2 (𝓞 K) K)
    (a : HeightOneSpectrum (𝓞 K) → ℤ) :
    ∃ G : Finset (AdelicGL2 (𝓞 K) K), (∀ g ∈ G, glArch (𝓞 K) K g = glArch (𝓞 K) K κ) ∧
      ∀ t : (AdeleRing (𝓞 K) K)ˣ,
      ((t : AdeleRing (𝓞 K) K)).1 = 1 →
      (∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ((t : AdeleRing (𝓞 K) K)).2 w = 1) →
      (∀ v ∈ S, Valued.v (((t : AdeleRing (𝓞 K) K)).2 v) = WithZero.exp (a v)) →
      ∃ g ∈ G, g⁻¹ * (diagOne t * κ) ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  obtain ⟨n₁, hn₁, hcrit⟩ := exists_threshold_conj_diagOne_mem_levelOne K N hN S κ
  choose Z hZval hZcov using fun v : HeightOneSpectrum (𝓞 K) => exists_finset_sphere_mulCover K v (a v) n₁ hn₁
  refine ⟨(S.pi Z).image fun f =>
    diagOne (shellIdele K S (fun v => if h : v ∈ S then f v h else 0)) * κ, ?_, ?_⟩
  · intro g hg
    obtain ⟨f, -, rfl⟩ := Finset.mem_image.mp hg
    rw [map_mul, glArch_diagOne_eq_one K _ (shellIdele_fst K S _), one_mul]
  intro t ht1 htS htv
  choose z hzZ hzclose using fun (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) =>
    hZcov v (((t : AdeleRing (𝓞 K) K)).2 v) (htv v hv)
  have hzpi : z ∈ S.pi Z := Finset.mem_pi.mpr fun v hv => hzZ v hv
  set t₀ : (AdeleRing (𝓞 K) K)ˣ := shellIdele K S (fun v => if h : v ∈ S then z v h else 0) with ht₀
  refine ⟨diagOne t₀ * κ, Finset.mem_image.mpr ⟨z, hzpi, rfl⟩, ?_⟩
  have hrw : (diagOne t₀ * κ)⁻¹ * (diagOne t * κ) = κ⁻¹ * diagOne (t₀⁻¹ * t) * κ := by
    rw [map_mul, map_inv]; group
  rw [hrw]

  have hz0 : ∀ v (hv : v ∈ S), z v hv ≠ 0 := fun v hv h => by
    have h1 := hZval v _ (hzZ v hv)
    rw [h, map_zero] at h1
    exact WithZero.exp_ne_zero h1.symm
  have ht₀1 : ((t₀ : AdeleRing (𝓞 K) K)).1 = 1 := shellIdele_fst K S _
  have ht₀S : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 w = 1 := fun w hw => by
    rw [ht₀, shellIdele_snd_apply, ite_eq_right hw]
  have ht₀v : ∀ v (hv : v ∈ S), ((t₀ : AdeleRing (𝓞 K) K)).2 v = z v hv := fun v hv => by
    rw [ht₀, shellIdele_snd_apply, ite_eq_left hv, dite_eq_left hv, unitOf_coe _ (hz0 v hv)]
  apply hcrit
  · show ((↑(t₀⁻¹) : AdeleRing (𝓞 K) K)).1 * ((t : AdeleRing (𝓞 K) K)).1 = 1
    rw [units_inv_fst K t₀ ht₀1, ht1, one_mul]
  · intro w hw
    show ((↑(t₀⁻¹) : AdeleRing (𝓞 K) K)).2 w * ((t : AdeleRing (𝓞 K) K)).2 w = 1
    rw [units_inv_snd_apply, ht₀S w hw, htS w hw, inv_one, one_mul]
  · intro v hv
    show Valued.v (((↑(t₀⁻¹) : AdeleRing (𝓞 K) K)).2 v * ((t : AdeleRing (𝓞 K) K)).2 v) = 1
    rw [map_mul, units_inv_snd_apply, map_inv₀, ht₀v v hv, hZval v _ (hzZ v hv), htv v hv,
      inv_mul_cancel₀ WithZero.exp_ne_zero]
  · intro v hv
    show Valued.v (((↑(t₀⁻¹) : AdeleRing (𝓞 K) K)).2 v * ((t : AdeleRing (𝓞 K) K)).2 v - 1) ≤ _
    rw [units_inv_snd_apply, ht₀v v hv]
    exact hzclose v hv

end LCoverMain

end UnipotentDepth

/-! ### Archimedean bi-finiteness under the reflexion convolution (pin `BIFIN`) -/

namespace ArchBiFinite

section Generic

variable {H G : Type*} [Group H] [Group G] (ι : H →* G)

def rTrans (g : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u x := u (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rTrans_apply (g : G) (u : G → ℂ) (x : G) : rTrans g u x = u (x * g) := rfl

theorem rTrans_one (u : G → ℂ) : rTrans (1 : G) u = u := by
  funext x; simp

theorem rTrans_rTrans (a b : G) (u : G → ℂ) : rTrans a (rTrans b u) = rTrans (a * b) u := by
  funext x; simp [mul_assoc]

def Stable (V : Submodule ℂ (G → ℂ)) : Prop := ∀ k : H, ∀ u ∈ V, rTrans (ι k) u ∈ V

def trSpan (φ : G → ℂ) : Submodule ℂ (G → ℂ) := Submodule.span ℂ (Set.range fun k : H => rTrans (ι k) φ)

theorem mem_trSpan (φ : G → ℂ) : φ ∈ trSpan ι φ :=
  Submodule.subset_span ⟨1, by show rTrans (ι 1) φ = φ; rw [map_one, rTrans_one]⟩

theorem rTrans_mem_trSpan (φ : G → ℂ) (k : H) : rTrans (ι k) φ ∈ trSpan ι φ :=
  Submodule.subset_span ⟨k, rfl⟩

theorem stable_trSpan (φ : G → ℂ) : Stable ι (trSpan ι φ) := by
  intro k u hu
  have hmap : Submodule.map (rTrans (ι k)) (trSpan ι φ) ≤ trSpan ι φ := by
    rw [trSpan, Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨_, ⟨k', rfl⟩, rfl⟩
    exact ⟨k * k', by show rTrans (ι (k * k')) φ = rTrans (ι k) (rTrans (ι k') φ); rw [map_mul, rTrans_rTrans]⟩
  exact hmap (Submodule.mem_map_of_mem hu)

theorem trSpan_le {φ : G → ℂ} {V : Submodule ℂ (G → ℂ)} (hV : Stable ι V) (hφ : φ ∈ V) : trSpan ι φ ≤ V := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, rfl⟩
  exact hV k φ hφ

theorem exists_fd_stable_of_mem_typeSubmodule {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ H W) {g : G → ℂ} (hg : g ∈ typeSubmodule ι ρ) :
    ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U := by
  refine Submodule.span_induction (p := fun g _ => ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U)
    ?_ ?_ ?_ ?_ hg
  · rintro _ ⟨T, hT, v, rfl⟩
    refine ⟨LinearMap.range T, inferInstance, LinearMap.mem_range_self T v, ?_⟩
    rintro k _ ⟨v', rfl⟩
    refine ⟨ρ k v', ?_⟩
    funext x
    exact hT k v' x
  · exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun k u hu => by
      rw [(Submodule.mem_bot ℂ).1 hu, map_zero]; exact Submodule.zero_mem _⟩
  · rintro a b - - ⟨U₁, hU₁, ha, hs₁⟩ ⟨U₂, hU₂, hb, hs₂⟩
    have := hU₁; have := hU₂
    refine ⟨U₁ ⊔ U₂, inferInstance, Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb), ?_⟩
    intro k u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hs₁ k u₁ hu₁)) (Submodule.mem_sup_right (hs₂ k u₂ hu₂))
  · rintro c a - ⟨U, hU, ha, hs⟩
    exact ⟨U, hU, Submodule.smul_mem _ c ha, hs⟩

theorem exists_fd_stable_of_mem_iSup {ι₀ : Type*} (S : ι₀ → Submodule ℂ (G → ℂ))
    (hS : ∀ i, ∀ g ∈ S i, ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U)
    {g : G → ℂ} (hg : g ∈ ⨆ i, S i) :
    ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U := by
  refine Submodule.iSup_induction _ (motive := fun g => ∃ U : Submodule ℂ (G → ℂ), FiniteDimensional ℂ U ∧ g ∈ U ∧ Stable ι U)
    hg hS ?_ ?_
  · exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun k u hu => by
      rw [(Submodule.mem_bot ℂ).1 hu, map_zero]; exact Submodule.zero_mem _⟩
  · rintro a b ⟨U₁, hU₁, ha, hs₁⟩ ⟨U₂, hU₂, hb, hs₂⟩
    have := hU₁; have := hU₂
    refine ⟨U₁ ⊔ U₂, inferInstance, Submodule.add_mem _ (Submodule.mem_sup_left ha) (Submodule.mem_sup_right hb), ?_⟩
    intro k u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.1 hu
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (hs₁ k u₁ hu₁)) (Submodule.mem_sup_right (hs₂ k u₂ hu₂))

theorem exists_rep_of_fd_stable (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] (hV : Stable ι V)
    {φ : G → ℂ} (hφ : φ ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)) (T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι ρ T ∧ φ ∈ LinearMap.range T := by

  let ρV : Representation ℂ H V :=
    { toFun := fun k => (rTrans (ι k)).restrict (hV k)
      map_one' := by
        refine LinearMap.ext fun u => Subtype.ext ?_
        show rTrans (ι 1) (u : G → ℂ) = u
        rw [map_one, rTrans_one]
      map_mul' := fun a b => by
        refine LinearMap.ext fun u => Subtype.ext ?_
        show rTrans (ι (a * b)) (u : G → ℂ) = rTrans (ι a) (rTrans (ι b) (u : G → ℂ))
        rw [map_mul, rTrans_rTrans] }
  have hρV : ∀ (k : H) (u : V), ((ρV k u : V) : G → ℂ) = rTrans (ι k) (u : G → ℂ) := fun _ _ => rfl
  set n := Module.finrank ℂ V
  let L : V ≃ₗ[ℂ] (Fin n → ℂ) := (Module.finBasis ℂ V).equivFun
  let ρ : Representation ℂ H (Fin n → ℂ) :=
    { toFun := fun k => L.toLinearMap ∘ₗ ρV k ∘ₗ L.symm.toLinearMap
      map_one' := by
        refine LinearMap.ext fun v => ?_
        simp [map_one]
      map_mul' := fun a b => by
        refine LinearMap.ext fun v => ?_
        simp [map_mul] }
  have hρ : ∀ (k : H) (v : Fin n → ℂ), ρ k v = L (ρV k (L.symm v)) := fun _ _ => rfl
  let T : (Fin n → ℂ) →ₗ[ℂ] (G → ℂ) := V.subtype ∘ₗ L.symm.toLinearMap
  have hT : ∀ v : Fin n → ℂ, T v = ((L.symm v : V) : G → ℂ) := fun _ => rfl
  refine ⟨n, ρ, T, ?_, ⟨L ⟨φ, hφ⟩, ?_⟩⟩
  · intro k v x
    rw [hT, hT, hρ, LinearEquiv.symm_apply_apply, hρV, rTrans_apply]
  · rw [hT, LinearEquiv.symm_apply_apply]

theorem exists_rep_mem_typeSubmodule (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] (hV : Stable ι V)
    {φ : G → ℂ} (hφ : φ ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), φ ∈ typeSubmodule ι ρ := by
  obtain ⟨n, ρ, T, hT, v, rfl⟩ := exists_rep_of_fd_stable ι V hV hφ
  exact ⟨n, ρ, mem_typeSubmodule_of_isRightEquivariant hT v⟩

theorem basisFun_toDual_apply (n : ℕ) (v w : Fin n → ℂ) :
    (Pi.basisFun ℂ (Fin n)).toDual v w = v ⬝ᵥ w := by
  conv_lhs => rw [← (Pi.basisFun ℂ (Fin n)).sum_repr w]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, Module.Basis.toDual_apply_left, Pi.basisFun_repr, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem exists_rep_mem_typeSubmodule_dual (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] (hV : Stable ι V)
    {φ : G → ℂ} (hφ : φ ∈ V) :
    ∃ (n : ℕ) (σ : Representation ℂ H (Fin n → ℂ)), φ ∈ typeSubmodule ι σ.dual := by
  obtain ⟨n, ρ, T, hT, v₀, rfl⟩ := exists_rep_of_fd_stable ι V hV hφ

  let σ : Representation ℂ H (Fin n → ℂ) :=
    { toFun := fun k => Matrix.toLin' (LinearMap.toMatrix' (ρ k⁻¹))ᵀ
      map_one' := by
        rw [inv_one, map_one]
        show Matrix.toLin' (LinearMap.toMatrix' (LinearMap.id : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))ᵀ = 1
        rw [LinearMap.toMatrix'_id, Matrix.transpose_one, Matrix.toLin'_one]
        rfl
      map_mul' := fun a b => by
        rw [mul_inv_rev, map_mul, LinearMap.toMatrix'_mul, Matrix.transpose_mul, Matrix.toLin'_mul]
        rfl }
  have hσ : ∀ k : H, σ k = Matrix.toLin' (LinearMap.toMatrix' (ρ k⁻¹))ᵀ := fun _ => rfl
  let D : (Fin n → ℂ) ≃ₗ[ℂ] Module.Dual ℂ (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).toDualEquiv
  have hD : ∀ v w : Fin n → ℂ, D v w = v ⬝ᵥ w := basisFun_toDual_apply n

  have hkey : ∀ (k : H) (v : Fin n → ℂ), (D v) ∘ₗ σ k⁻¹ = D (ρ k v) := by
    intro k v
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, hσ, inv_inv, Matrix.toLin'_apply, hD, hD, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
    congr 1
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  let T' : Module.Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (G → ℂ) := T ∘ₗ D.symm.toLinearMap
  have hT' : IsRightEquivariant ι σ.dual T' := by
    intro k f x
    obtain ⟨v, rfl⟩ : ∃ v, D v = f := ⟨D.symm f, D.apply_symm_apply f⟩
    show T (D.symm (σ.dual k (D v))) x = T (D.symm (D v)) (x * ι k)
    rw [Representation.dual_apply, Module.Dual.transpose_apply, hkey, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
    exact hT k v x
  refine ⟨n, σ, ?_⟩
  have : T v₀ = T' (D v₀) := by
    show T v₀ = T (D.symm (D v₀)); rw [LinearEquiv.symm_apply_apply]
  rw [this]
  exact mem_typeSubmodule_of_isRightEquivariant hT' _

end Generic

section Adelic

variable (F : Type) [Field F] [NumberField F]

theorem continuous_and_hasCompactSupport_of_mem_trSpan (w : InfinitePlace F) {φ : (AdelicGL2 (𝓞 F) F) → ℂ}
    (hc : Continuous φ) (hs : HasCompactSupport φ) {ψ : (AdelicGL2 (𝓞 F) F) → ℂ} (hψ : ψ ∈ trSpan (rowIsometryInclAt₀ F w) φ) :
    Continuous ψ ∧ HasCompactSupport ψ := by
  refine Submodule.span_induction (p := fun ψ _ => Continuous ψ ∧ HasCompactSupport ψ) ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨k, rfl⟩
    exact ⟨hc.comp (continuous_mul_const _), hs.comp_homeomorph (Homeomorph.mulRight _)⟩
  · exact ⟨continuous_const, HasCompactSupport.zero⟩
  · rintro a b - - ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨ha.add hb, ha'.add hb'⟩
  · rintro c a - ⟨ha, ha'⟩
    refine ⟨continuous_const.mul ha, ?_⟩
    exact ha'.mul_left

variable (f f' : (AdelicGL2 (𝓞 F) F) → ℂ) (hfc : Continuous f) (hfs : HasCompactSupport f)
  (hfc' : Continuous f') (hfs' : HasCompactSupport f')

theorem kernel_apply (z : (AdelicGL2 (𝓞 F) F)) : rightConv F f' (fun x => f x⁻¹) z = ∫ y, f' (z * y) * f y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  rw [rightConv_apply]

include hfc hfs hfc' in

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
theorem exists_linear_right (w : InfinitePlace F) (W : Submodule ℂ ((AdelicGL2 (𝓞 F) F) → ℂ))
    (hW : ∀ ψ ∈ W, Continuous ψ ∧ HasCompactSupport ψ) :
    ∃ B : W →ₗ[ℂ] ((AdelicGL2 (𝓞 F) F) → ℂ), ∀ ψ : W, (B ψ : (AdelicGL2 (𝓞 F) F) → ℂ) = fun x => ∫ y, f' (x * y) * (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hInt : ∀ ψ : W, ∀ x : (AdelicGL2 (𝓞 F) F), Integrable (fun y => f' (x * y) * (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro ψ x
    obtain ⟨hψc, hψs⟩ := hW ψ ψ.2
    exact ((hfc'.comp (continuous_const_mul x)).mul (hψc.comp continuous_inv)).integrable_of_hasCompactSupport
      ((hψs.comp_homeomorph (Homeomorph.inv _)).mul_left)
  let Bf : W → ((AdelicGL2 (𝓞 F) F) → ℂ) := fun ψ x => ∫ y, f' (x * y) * (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  have hadd : ∀ ψ₁ ψ₂ : W, Bf (ψ₁ + ψ₂) = Bf ψ₁ + Bf ψ₂ := by
    intro ψ₁ ψ₂
    funext x
    show (∫ y, f' (x * y) * ((ψ₁ : (AdelicGL2 (𝓞 F) F) → ℂ) + (ψ₂ : (AdelicGL2 (𝓞 F) F) → ℂ)) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (∫ y, f' (x * y) * (ψ₁ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) + ∫ y, f' (x * y) * (ψ₂ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    rw [← integral_add (hInt ψ₁ x) (hInt ψ₂ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply, mul_add]
  have hsmul : ∀ (c : ℂ) (ψ : W), Bf (c • ψ) = c • Bf ψ := by
    intro c ψ
    funext x
    show (∫ y, f' (x * y) * (c • (ψ : (AdelicGL2 (𝓞 F) F) → ℂ)) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) = c • ∫ y, f' (x * y) * (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    rw [smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨{ toFun := Bf, map_add' := hadd, map_smul' := hsmul }, fun ψ => rfl⟩

include hfc hfs hfc' in

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
theorem exists_linear_left (w : InfinitePlace F) (W : Submodule ℂ ((AdelicGL2 (𝓞 F) F) → ℂ))
    (hW : ∀ ψ ∈ W, Continuous ψ ∧ HasCompactSupport ψ) :
    ∃ C : W →ₗ[ℂ] ((AdelicGL2 (𝓞 F) F) → ℂ), ∀ ψ : W, (C ψ : (AdelicGL2 (𝓞 F) F) → ℂ) = fun x => ∫ v, (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hInt : ∀ ψ : W, ∀ x : (AdelicGL2 (𝓞 F) F), Integrable (fun v => (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹)) (NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro ψ x
    obtain ⟨hψc, hψs⟩ := hW ψ ψ.2
    exact ((hψc.comp continuous_inv).mul (hfc.comp (continuous_inv.mul continuous_const))).integrable_of_hasCompactSupport
      ((hψs.comp_homeomorph (Homeomorph.inv _)).mul_right)
  let Cf : W → ((AdelicGL2 (𝓞 F) F) → ℂ) := fun ψ x => ∫ v, (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  have hadd : ∀ ψ₁ ψ₂ : W, Cf (ψ₁ + ψ₂) = Cf ψ₁ + Cf ψ₂ := by
    intro ψ₁ ψ₂
    funext x
    show (∫ v, ((ψ₁ : (AdelicGL2 (𝓞 F) F) → ℂ) + (ψ₂ : (AdelicGL2 (𝓞 F) F) → ℂ)) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
      (∫ v, (ψ₁ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) + ∫ v, (ψ₂ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    rw [← integral_add (hInt ψ₁ x) (hInt ψ₂ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Pi.add_apply, add_mul]
  have hsmul : ∀ (c : ℂ) (ψ : W), Cf (c • ψ) = c • Cf ψ := by
    intro c ψ
    funext x
    show (∫ v, (c • (ψ : (AdelicGL2 (𝓞 F) F) → ℂ)) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) = c • ∫ v, (ψ : (AdelicGL2 (𝓞 F) F) → ℂ) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    rw [smul_eq_mul, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact ⟨{ toFun := Cf, map_add' := hadd, map_smul' := hsmul }, fun ψ => rfl⟩

theorem kernel_mul_right (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : (AdelicGL2 (𝓞 F) F)) :
    rightConv F f' (fun x => f x⁻¹) (x * rowIsometryInclAt₀ F w k) =
      ∫ y, f' (x * y) * (rTrans (rowIsometryInclAt₀ F w k) f) y⁻¹ ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set t : (AdelicGL2 (𝓞 F) F) := rowIsometryInclAt₀ F w k
  rw [kernel_apply]
  rw [← integral_mul_left_eq_self (fun y => f' (x * t * y) * f y⁻¹) t⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [rTrans_apply, mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]

theorem kernel_inv_mul_right (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : (AdelicGL2 (𝓞 F) F)) :
    rightConv F f' (fun x => f x⁻¹) (x * rowIsometryInclAt₀ F w k)⁻¹ =
      ∫ v, (rTrans (rowIsometryInclAt₀ F w k) (fun u => f' u⁻¹)) v⁻¹ * f (v⁻¹ * x⁻¹) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have : BorelSpace (AdelicGL2 (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  have := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set t : (AdelicGL2 (𝓞 F) F) := rowIsometryInclAt₀ F w k
  rw [kernel_apply]
  rw [← integral_mul_left_eq_self (fun y => f' ((x * t)⁻¹ * y) * f y⁻¹) (x * t)]
  rw [← integral_mul_left_eq_self (fun v => f' ((x * t)⁻¹ * ((x * t) * v)) * f ((x * t) * v)⁻¹) t⁻¹]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [rTrans_apply, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]

end Adelic

end ArchBiFinite

/-! ### The three rows -/

/-- **The tensor split.** For a function `f : G → ℂ` whose right translates by each of finitely many
pairwise-commuting subgroups lie in a finite-dimensional span, `f` itself is a finite sum of products
of one `Kᵢ`-right-invariant factor and one `⨆ K`-right-invariant factor. -/
theorem exists_sum_prod_mul_of_rightTranslatesSpanFinite
    {G : Type*} [Group G] {n : ℕ} (K : Fin n → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y)
    (f : G → ℂ)
    (hf : ∀ i, ∃ s : Finset (G → ℂ), ∀ k ∈ K i,
      (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))) :
    ∃ (N : ℕ) (a : Fin N → Fin n → G → ℂ) (b : Fin N → G → ℂ),
      (∀ m i, a m i ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ x h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun g => f (x * g * h)}) ∧
      (∀ m i, ∃ t : Finset (G → ℂ), ∀ k' ∈ K i,
          (fun g => a m i (g * k')) ∈ Submodule.span ℂ (t : Set (G → ℂ))) ∧
      (∀ m, b m ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun x => f (x * h)}) ∧
      ∀ (x : G) (k : Fin n → G), (∀ i, k i ∈ K i) →
        f (x * (List.ofFn k).prod) = ∑ m, (∏ i, a m i (k i)) * b m x := by
  exact TensorSplit.tensor_split K hcomm f hf

/-- **The depth.** A finite sum of right translates of a level-`N`-invariant function is invariant under
`lowerUnipotentGL2 γ` for every `γ` that is integral at the places outside `S` and divisible by a
sufficiently high power of the places in `S`. -/
theorem exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)
    (r : ℕ) (A : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * A i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
      (∀ v ∈ S, Valued.v (γ.2 v) ≤
        ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      x (g * lowerUnipotentGL2 γ) = x g := by
  obtain ⟨n, hn, hconj⟩ :=
    UnipotentDepth.exists_depth_conj_lowerUnipotentGL2_mem_levelOne K N _hN S A
  refine ⟨n, hn, fun γ g h1 h2 h3 => ?_⟩
  exact UnipotentDepth.translateFamily_apply_mul_lowerUnipotentGL2 K N S x₀ _hx₀lev A cs x _hxsum γ
    (hconj γ h1 h2 h3) g

/-- **Archimedean bi-finiteness of the reflexion convolution.** The right convolution of `f'` with
`x ↦ f x⁻¹` of two archimedean-bi-finite, continuous, compactly supported functions is again
archimedean-bi-finite, for some type family `tys''`. -/
theorem exists_isArchBiFinite_rightConv_comp_inv
    (F : Type) [Field F] [NumberField F]
    (f f' : AdelicGL2 (𝓞 F) F → ℂ) (tys tys' : ArchTypeFamily F)
    (hfc : Continuous f) (hfs : HasCompactSupport f) (hbf : IsArchBiFinite F tys f)
    (hfc' : Continuous f') (hfs' : HasCompactSupport f') (hbf' : IsArchBiFinite F tys' f') :
    ∃ tys'' : ArchTypeFamily F, IsArchBiFinite F tys'' (rightConv F f' (fun x => f x⁻¹)) := by
  classical
  set h : AdelicGL2 (𝓞 F) F → ℂ := rightConv F f' (fun x => f x⁻¹) with hh

  have hleft : ∀ w : InfinitePlace F, ∃ (n : ℕ) (ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin n → ℂ)),
      (fun x => h x⁻¹) ∈ typeSubmodule (rowIsometryInclAt₀ F w) ρ := by
    intro w
    set ι := rowIsometryInclAt₀ F w

    have hmem : (fun x => f' x⁻¹) ∈ ⨆ i, archTypeSubmoduleAt F w (tys'.rep w i) :=
      (mem_archCutSubmodule_iff F tys' _).1 hbf'.1 w
    obtain ⟨U, hU, hgU, hsU⟩ := ArchBiFinite.exists_fd_stable_of_mem_iSup ι _
      (fun i g hg => ArchBiFinite.exists_fd_stable_of_mem_typeSubmodule ι (tys'.rep w i).ρ hg) hmem
    have := hU
    set W := ArchBiFinite.trSpan ι (fun x => f' x⁻¹)
    have : FiniteDimensional ℂ W :=
      Submodule.finiteDimensional_of_le (ArchBiFinite.trSpan_le ι hsU hgU)
    have hW : ∀ ψ ∈ W, Continuous ψ ∧ HasCompactSupport ψ := fun ψ hψ =>
      ArchBiFinite.continuous_and_hasCompactSupport_of_mem_trSpan F w (hfc'.comp continuous_inv)
        (hfs'.comp_homeomorph (Homeomorph.inv _)) hψ
    obtain ⟨C, hC⟩ := ArchBiFinite.exists_linear_left F f f' hfc hfs hfc' w W hW

    set V := ArchBiFinite.trSpan ι (fun x => h x⁻¹)
    have hVle : V ≤ LinearMap.range C := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨⟨ArchBiFinite.rTrans (ι k) (fun u => f' u⁻¹),
        ArchBiFinite.rTrans_mem_trSpan ι _ k⟩, ?_⟩
      rw [hC]
      funext x
      show _ = ArchBiFinite.rTrans (ι k) (fun x => h x⁻¹) x
      rw [ArchBiFinite.rTrans_apply]
      exact (ArchBiFinite.kernel_inv_mul_right F f f' w k x).symm
    have : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVle
    exact ArchBiFinite.exists_rep_mem_typeSubmodule ι V
      (ArchBiFinite.stable_trSpan ι _) (ArchBiFinite.mem_trSpan ι _)

  have hright : ∀ w : InfinitePlace F, ∃ (n : ℕ) (σ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin n → ℂ)),
      h ∈ typeSubmodule (rowIsometryInclAt₀ F w) σ.dual := by
    intro w
    set ι := rowIsometryInclAt₀ F w
    have hmem : f ∈ ⨆ i, archDualTypeSubmoduleAt F w (tys.rep w i) :=
      (mem_archDualCutSubmodule_iff F tys _).1 hbf.2 w
    obtain ⟨U, hU, hgU, hsU⟩ := ArchBiFinite.exists_fd_stable_of_mem_iSup ι _
      (fun i g hg => ArchBiFinite.exists_fd_stable_of_mem_typeSubmodule ι (tys.rep w i).ρ.dual hg) hmem
    have := hU
    set W := ArchBiFinite.trSpan ι f
    have : FiniteDimensional ℂ W :=
      Submodule.finiteDimensional_of_le (ArchBiFinite.trSpan_le ι hsU hgU)
    have hW : ∀ ψ ∈ W, Continuous ψ ∧ HasCompactSupport ψ := fun ψ hψ =>
      ArchBiFinite.continuous_and_hasCompactSupport_of_mem_trSpan F w hfc hfs hψ
    obtain ⟨B, hB⟩ := ArchBiFinite.exists_linear_right F f f' hfc hfs hfc' w W hW
    set V := ArchBiFinite.trSpan ι h
    have hVle : V ≤ LinearMap.range B := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨k, rfl⟩
      refine ⟨⟨ArchBiFinite.rTrans (ι k) f, ArchBiFinite.rTrans_mem_trSpan ι _ k⟩, ?_⟩
      rw [hB]
      funext x
      show _ = ArchBiFinite.rTrans (ι k) h x
      rw [ArchBiFinite.rTrans_apply]
      exact (ArchBiFinite.kernel_mul_right F f f' w k x).symm
    have : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le hVle
    exact ArchBiFinite.exists_rep_mem_typeSubmodule_dual ι V
      (ArchBiFinite.stable_trSpan ι _) (ArchBiFinite.mem_trSpan ι _)

  choose nL ρL hρL using hleft
  choose nR σR hσR using hright
  refine ⟨⟨fun _ => 2, fun w => ![⟨nL w, ρL w⟩, ⟨nR w, σR w⟩]⟩, ?_, ?_⟩
  · rw [mem_archCutSubmodule_iff]
    intro w
    exact Submodule.mem_iSup_of_mem (0 : Fin 2) (hρL w)
  · rw [mem_archDualCutSubmodule_iff]
    intro w
    exact Submodule.mem_iSup_of_mem (1 : Fin 2) (hσR w)

end AutomorphicForm
