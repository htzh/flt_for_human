/-
  The Whittaker coefficient at `diagOne`.

  The Whittaker coefficient `W φ` of an automorphic function is a function of the diagonal torus; at
  the point `diagOne` its value is what the cuspidal-spectrum analysis reads. Three statements:

  * `exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt`:
    for a vector of circle weight `m`, the value at `diagOne` is the value at the split-torus point
    `splitTorusGL2Complex` times the character factor — the weight decomposition of the diagonal;
  * `CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent`:
    on a cusp constituent, any Whittaker coefficient of a member is a finite sum of coefficients at
    `diagOne` against a separating family — the finite-dimensionality of the `diagOne` line;
  * its `…_norm_infinitePlace_eq_one` companion: the same expansion with the coefficient normalized at
    the infinite places.

  The first is the archimedean algebra of `HasCircleWeightAt` (SET-AF24's predicate) against the
  split torus; the last two are the cuspidal-constituent engine, whose 514-line prelude (36
  declarations: `exists_fd_stable`, `exists_factor`, `exists_eval_coords`, `exists_finset_separating`,
  …) is shared by the two pin files and written once here.

  Transcribed from the pin's three `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`,
  913 + 716 + 714 lines).

  **Shape.** One module in the pin's order: the 913 archimedean development (its engine namespaces
  `DCFN`, `IFC`), then the cuspidal-constituent prelude written **once** at the pin's last names
  (`EvalCoords`, `KUNIFPlace`, `KUNIFAdelic`, `KUNIFCut`), then the 716 expansion and its 714
  companion. The two cusp proofs are the same body; the companion differs only in the one extra
  conjunct `∀ w, ‖ε.1 w‖ = 1`, supplied at the final `refine` (pin 714:680 = 716:680–681), so the
  second row reuses the first one's development. The two shape clusters `dedup.py` reports
  (`centralScalar_comm`/`mul_centralScalar_comm`, `archComplexGLAt_mul_g0`/`g0_comm`) are the pin's
  own duplicates, one per source file; they are kept.

  **Drift** (mathlib `v4.34.0`; statements frozen, proofs adapted, pin line numbers of the `S_` file):
  * `NumberField.InfinitePlace.Completion` is a *structure* here (a type synonym at the pin), so every
    `show … Function.update (1 : InfiniteAdeleRing K) …` of the pin's proofs (`:73`, `:87`, `:292`,
    `:295`, `:330`, `:344`, `:374`, `:379`, `:384`, `:389`, `:428`, `:433`, `:568`, `:574`, `:688`,
    `:694`) spells the pi type `(v : InfinitePlace K) → v.Completion`, and the pin's
    `attribute [-ext] NumberField.InfinitePlace.Completion.ext` (`:11`) is kept, so that `ext i j` on
    `GL (Fin 2) w.Completion` stops at the matrix entries.
  * `dif_pos`/`dif_neg`/`if_pos`/`if_neg` are deprecated: `dite_eq_left`/`dite_eq_right`/`ite_eq_left`/
    `ite_eq_right` (`:524`, `:637`, `:834`, `:836`, `:837`, `:843`, `:880`; 714 `:105`).
  * `Finset.noncommProd` now takes its commutativity datum as `(s : Set α).Pairwise (Commute on f)`, and
    a `fun _ _ _ _ h ↦ …` proof of that datum does not re-check at `implicit` transparency downstream.
    `archProd` states the datum through `Set.Pairwise.of_forall₂` (`:346`–`:348`), and its two readers
    `glFin_archProd`/`archComponent_archProd` (`:350`, `:356`) go through
    `Finset.noncommProd_induction` / `Finset.mul_noncommProd_erase` instead of
    `Finset.map_noncommProd` (`:351`, `:360`).
  * `ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` (`:189`) is reached through
    `TateGlobal.IdeleNormValues`, a new import: the pin imported its `Theorems/` wrapper instead (`:9`).
  * `omit [NumberField K] in` where `v4.34.0`'s `unusedSectionVars` linter fires (`:244`, `:247`,
    `:252`, `:532`, `:784`, `:787`, `:794`).
  * The pin's `set_option linter.unusedVariables false in` on `solution` (714 `:576`) has no port
    counterpart; the bindings it silenced (`hw`, `hb` of `large`, and `hc`, `hd₁`, `hd`, `hcov`, `hN`
    of the two headlines) are referenced explicitly instead.
  * `haveI`/`letI` → `have`/`let` inside proofs (714 `:440`, `:470`, `:477`, `:508`, `:521`, `:646`).
  * `p2m_export` (714 `:248`, `:411`) is dropped and the two `private` `exists_factor`s (714 `:208`,
    `:398`) are public here, as the port's policy requires. The pin's pipeline ids are stripped from the
    engine namespaces (`E40DCFN` → `DCFN`, `E40IFC` → `IFC`); `KUNIFPlace`, `KUNIFAdelic`, `KUNIFCut`
    and `EvalCoords` are kept as they stand. `import Mathlib` (714 `:1`) and
    `attribute [-instance] instCountableOfNumberField_definitions` (913 `:13`) are dropped.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent.lean
  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightCharTransport
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.Siegel.Covering
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSet
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues
import FLTForHuman.NumberTheory.NumberField.FiniteIdeles

set_option autoImplicit false

attribute [-ext] NumberField.InfinitePlace.Completion.ext

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.CuspidalConstituent AutomorphicForm.SiegelCovering
open AutomorphicForm.WindowedSiegel MeasureTheory
open IsDedekindDomain Filter
open scoped ENNReal Topology Matrix

namespace AutomorphicForm

open scoped Classical

/-! ## Part 1 (pin 913): the archimedean algebra of `HasCircleWeightAt` against the split torus

`DCFN` is the pin's engine (`E40DCFN` with its pipeline id stripped): the ideles `bprime`/`iotaW` and
the maximal-compact point `g0` that move the `diagOne` point into the split torus times the circle,
the circle-weight factorization `Fstr_mul_circleGL2`, the norm row `norm_W_diagOne_eq_rpow_mul_norm_fstr`
and the boundedness reads `large`/`bounded`. `IFC` (`E40IFC`) carries the `g0`-commutation wrapper and
the three norm readers, `hM_string`/`twist`/`bounded`. -/

namespace DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

abbrev eC {w : InfinitePlace K} (hw : w.IsComplex) : w.Completion ≃+* ℂ := ringEquivComplexOfIsComplex hw

def iotaW {w : InfinitePlace K} (hw : w.IsComplex) : ℂˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  (archUnitHom w).comp (Units.map (eC hw).symm.toRingHom.toMonoidHom)

def bprime (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) : (AdeleRing (𝓞 K) K)ˣ :=
  b * (archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹

def g0 (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) : AdelicGL2 (𝓞 K) K := diagOne (bprime w b)

abbrev W (D : Set (AdelicGL2 (𝓞 K) K)) (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  whittakerCoefficient K (productionPinsOf K D
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
    (NumberField.StandardAddChar.stdAddChar K) φ 1 g

def Fstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (h : GL (Fin 2) ℂ) : ℂ :=
  W D (x p) (g0 w b * archComplexGLAt hw h)

def DFstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (d : ArchDirComplex) (h : GL (Fin 2) ℂ) : ℂ :=
  W D (archDerivAtComplex hw d (x p)) (g0 w b * archComplexGLAt hw h)

def DDstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (p : Fin (n + 1)) (d' d : ArchDirComplex) (h : GL (Fin 2) ℂ) : ℂ :=
  W D (archDerivAtComplex hw d' (archDerivAtComplex hw d (x p))) (g0 w b * archComplexGLAt hw h)

def fstr (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ)) (m : ℕ) (y : ℝ) : ℂ :=
  if hm : m < n + 1 then Fstr D hw b x ⟨m, hm⟩ (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)) else 0

theorem bprime_fst_self (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) :
    ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := by
  have hne : ((b : AdeleRing (𝓞 K) K)).1 w ≠ 0 := by
    intro h
    have h1 : (((b * b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by rw [mul_inv_cancel]; rfl
    have : (((b * b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w =
        ((b : AdeleRing (𝓞 K) K)).1 w * (((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w := rfl
    rw [this, h, zero_mul] at h1; exact zero_ne_one h1
  rw [bprime]
  show ((b : AdeleRing (𝓞 K) K)).1 w * ((((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K)).1 w = 1
  rw [← map_inv, archUnitHom_apply]
  show ((b : AdeleRing (𝓞 K) K)).1 w * Function.update (1 : (v : InfinitePlace K) → v.Completion) w _ w = 1
  rw [Function.update_self]
  show ((b : AdeleRing (𝓞 K) K)).1 w * (((infiniteUnitsComponent (𝓞 K) K w b)⁻¹ : (w.Completion)ˣ) : w.Completion) = 1
  rw [← map_inv]
  show ((b : AdeleRing (𝓞 K) K)).1 w * (((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1
  have : (((b * b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 := by rw [mul_inv_cancel]; rfl
  exact this

theorem bprime_fst_of_ne {w w' : InfinitePlace K} (hne : w' ≠ w) (b : (AdeleRing (𝓞 K) K)ˣ) :
    ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w' := by
  rw [bprime]
  show ((b : AdeleRing (𝓞 K) K)).1 w' * ((((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K)).1 w' = _
  rw [← map_inv, archUnitHom_apply]
  show ((b : AdeleRing (𝓞 K) K)).1 w' * Function.update (1 : (v : InfinitePlace K) → v.Completion) w _ w' = _
  rw [Function.update_of_ne hne]
  show ((b : AdeleRing (𝓞 K) K)).1 w' * 1 = _
  rw [mul_one]

theorem bprime_snd (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) :
    ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = ((b : AdeleRing (𝓞 K) K)).2 := by
  rw [bprime]
  show ((b : AdeleRing (𝓞 K) K)).2 * ((((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹ : (AdeleRing (𝓞 K) K)ˣ) :
    AdeleRing (𝓞 K) K)).2 = _
  rw [← map_inv, archUnitHom_apply]
  show ((b : AdeleRing (𝓞 K) K)).2 * 1 = _
  rw [mul_one]

end DCFN

namespace DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
theorem glInf_ext {a b : GL (Fin 2) (InfiniteAdeleRing K)}
    (h : ∀ v : InfinitePlace K, archComponent K v a = archComponent K v b) : a = b := by
  apply Units.ext
  ext i j
  funext v
  have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (v.Completion) =>
    (m : Matrix (Fin 2) (Fin 2) (v.Completion))) (h v)) i) j
  rwa [archComponent_apply, archComponent_apply] at this

theorem archComplexGLAt_mul_comm_of_archComponent_eq_one {w : InfinitePlace K} (hw : w.IsComplex) (m : GL (Fin 2) ℂ)
    {k : AdelicGL2 (𝓞 K) K} (hk : archComponent K w (glArch (𝓞 K) K k) = 1) :
    archComplexGLAt hw m * k = k * archComplexGLAt hw m := by
  have hfin : glFin (𝓞 K) K (archComplexGLAt hw m) = 1 := glFin_adelicArchGLIncl K _
  have harch : glArch (𝓞 K) K (archComplexGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) := glArch_adelicArchGLIncl K _
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, harch]
    refine glInf_ext K fun v => ?_
    rw [map_mul, map_mul]
    by_cases hv : v = w
    · subst hv; rw [hk, mul_one, one_mul, archComponent_archGLIncl_self]
    · rw [archComponent_archGLIncl_of_ne K hv, one_mul, mul_one]
  · rw [map_mul, map_mul, hfin, mul_one, one_mul]

theorem archComponent_glArch_g0 (w : InfinitePlace K) (b : (AdeleRing (𝓞 K) K)ˣ) :
    archComponent K w (glArch (𝓞 K) K (g0 w b)) = 1 := by
  ext i j
  rw [archComponent_apply, glArch_apply]
  show ((Matrix.diagonal ![((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), 1] i j).1 w) =
    (1 : Matrix (Fin 2) (Fin 2) (w.Completion)) i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, bprime_fst_self] <;> rfl

theorem archComplexGLAt_mul_g0 {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ) (m : GL (Fin 2) ℂ) :
    archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m :=
  archComplexGLAt_mul_comm_of_archComponent_eq_one K hw m (archComponent_glArch_g0 K w b)

section Wlemmas
variable (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)

theorem whittakerCoefficient_mul_right (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g k : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (fun y => φ (y * k)) α g := by
  unfold whittakerCoefficient
  congr 1
  funext u
  simp only [mul_assoc]

theorem whittakerCoefficient_const_mul (φ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) (α : K) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ (fun y => c * φ y) α g = c * whittakerCoefficient K pins ψ φ α g := by
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext u
  ring

end Wlemmas

theorem Fstr_mul_circleGL2 (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p)) :
    ∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      Fstr D hw b x p (h * circleGL2 ζ) = (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * Fstr D hw b x p h := by
  intro p ζ hζ h
  unfold Fstr W
  rw [map_mul, ← mul_assoc, whittakerCoefficient_mul_right]
  have hfun : (fun y => x p (y * archComplexGLAt hw (circleGL2 ζ))) = fun y => (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * x p y :=
    funext fun y => hwt p ζ hζ y
  rw [hfun, whittakerCoefficient_const_mul]

theorem det_diagOne (a : (AdeleRing (𝓞 K) K)ˣ) : Matrix.GeneralLinearGroup.det (diagOne a : AdelicGL2 (𝓞 K) K) = a := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(a : AdeleRing (𝓞 K) K), 1]).det = a
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem ideleNorm_eq_norm_pow_mul_of_eq_off (w : InfinitePlace K) (b a : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') :
    ideleNorm K a = ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult *
      ∏ w' ∈ Finset.univ.erase w, ‖((b : AdeleRing (𝓞 K) K)).1 w'‖ ^ w'.mult := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K a ha,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  congr 1
  refine Finset.prod_congr rfl fun w' hw' => ?_
  rw [hab w' (Finset.mem_erase.1 hw').1]

theorem exists_norm_W_diagOne_le_norm_rpow_of_gr (D : Set (AdelicGL2 (𝓞 K) K)) (w₀ : ℝ) (w : InfinitePlace K)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (b : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
          (diagOne a)‖ ≤ C * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) := by
  choose C₀ hC₀ using hgr
  set Pb : ℝ := ∏ w' ∈ Finset.univ.erase w, ‖((b : AdeleRing (𝓞 K) K)).1 w'‖ ^ w'.mult with hPb
  have hbpos : ∀ w' : InfinitePlace K, 0 < ‖((b : AdeleRing (𝓞 K) K)).1 w'‖ := by
    intro w'
    have h := congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w') b.mul_inv
    change ((b : AdeleRing (𝓞 K) K)).1 w' * (((b⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w' = 1 at h
    exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
  have hPb0 : 0 < Pb := Finset.prod_pos fun w' _ => pow_pos (hbpos w') _
  refine ⟨(∑ p, |C₀ p|) * Pb ^ (w₀ / 2), mul_nonneg (Finset.sum_nonneg fun p _ => abs_nonneg _) (Real.rpow_nonneg hPb0.le _), ?_⟩
  intro p a ha hab
  have hr0 : 0 < ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := by
    have h := congrArg (fun z : AdeleRing (𝓞 K) K => z.1 w) a.mul_inv
    change ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 at h
    exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
  have hN : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (diagOne a : AdelicGL2 (𝓞 K) K)) ^ (w₀ / 2) =
      ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * Pb ^ (w₀ / 2) := by
    rw [det_diagOne, ideleNorm_eq_norm_pow_mul_of_eq_off K w b a ha hab, Real.mul_rpow (pow_nonneg hr0.le _) hPb0.le,
      ← Real.rpow_natCast_mul hr0.le]
    congr 2
    ring
  calc ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
          (diagOne a)‖
      ≤ C₀ p * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (diagOne a : AdelicGL2 (𝓞 K) K)) ^ (w₀ / 2) := hC₀ p _
    _ = C₀ p * Pb ^ (w₀ / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) := by rw [hN]; ring
    _ ≤ (∑ p, |C₀ p|) * Pb ^ (w₀ / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (Real.rpow_nonneg hPb0.le _))
          (Real.rpow_nonneg hr0.le _)
        exact Finset.single_le_sum (fun q _ => abs_nonneg (C₀ q)) (Finset.mem_univ p)

end DCFN

namespace DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
theorem mult_eq_two_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) : w.mult = 2 :=
  NumberField.InfinitePlace.mult_isComplex ⟨w, hw⟩

omit [NumberField K] in
theorem norm_eC {w : InfinitePlace K} (hw : w.IsComplex) (x : w.Completion) : ‖eC hw x‖ = ‖x‖ := by
  show ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖
  rw [ringEquivComplexOfIsComplex_apply]
  exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

omit [NumberField K] in
theorem norm_eC_symm {w : InfinitePlace K} (hw : w.IsComplex) (z : ℂ) : ‖(eC hw).symm z‖ = ‖z‖ := by
  conv_rhs => rw [← (eC hw).apply_symm_apply z]
  rw [norm_eC]

def diagGL (z₁ z₂ : ℂˣ) : GL (Fin 2) ℂ where
  val := !![(z₁ : ℂ), 0; 0, (z₂ : ℂ)]
  inv := !![((z₁⁻¹ : ℂˣ) : ℂ), 0; 0, ((z₂⁻¹ : ℂˣ) : ℂ)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagGL_eq_scalar_mul_split_mul_circle (z t ζ : ℂˣ) (u : ℝ) (ht : (t : ℂ) ^ 2 = z)
    (huζ : Complex.exp (u : ℂ) * (ζ : ℂ) = t) :
    diagGL z 1 = diagGL t t * (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ) := by
  have ht0 : (t : ℂ) ≠ 0 := t.ne_zero
  have h11 : (t : ℂ) * (Complex.exp (-(u : ℂ)) * ((ζ : ℂ))⁻¹) = 1 := by
    rw [Complex.exp_neg, ← mul_inv, huζ, mul_inv_cancel₀ ht0]
  have h11' : (t : ℂ) * (Complex.exp (-(u : ℂ)) * ((ζ⁻¹ : ℂˣ) : ℂ)) = 1 := by
    rw [Units.val_inv_eq_inv_val]; exact h11
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, Units.val_mul]
  fin_cases i <;> fin_cases j <;>
    simp [diagGL, splitTorusGL2Complex, circleGL2, Matrix.mul_apply, Fin.sum_univ_two, ← ht, sq]
  · exact huζ.symm
  · exact h11.symm

theorem eq_bprime_mul_archUnitHom (w : InfinitePlace K) (b a : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') :
    a = bprime w b * archUnitHom w (infiniteUnitsComponent (𝓞 K) K w a) := by
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) ?_
  · show ((a : AdeleRing (𝓞 K) K)).1 v = ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v *
      ((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w a) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v
    rw [archUnitHom_apply]
    by_cases hv : v = w
    · subst hv
      rw [bprime_fst_self, one_mul]
      show _ = Function.update (1 : (v : InfinitePlace K) → v.Completion) v _ v
      rw [Function.update_self]; rfl
    · rw [bprime_fst_of_ne hv, hab v hv]
      show _ = _ * Function.update (1 : (v : InfinitePlace K) → v.Completion) w _ v
      rw [Function.update_of_ne hv]
      exact (mul_one _).symm
  · show ((a : AdeleRing (𝓞 K) K)).2 = ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 *
      ((archUnitHom w (infiniteUnitsComponent (𝓞 K) K w a) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2
    rw [bprime_snd, hb, ha, archUnitHom_apply]
    exact (mul_one _).symm

theorem glFin_diagOne_of_snd_eq_one (t : (AdeleRing (𝓞 K) K)ˣ) (ht : ((t : AdeleRing (𝓞 K) K)).2 = 1) :
    glFin (𝓞 K) K (diagOne t) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glFin_apply]
  change ((Matrix.diagonal ![(t : AdeleRing (𝓞 K) K), 1] i j).2) = ((1 : Matrix (Fin 2) (Fin 2) _) i j)
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ht] <;> rfl

theorem diagOne_archUnitHom_eq_archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) (c : (w.Completion)ˣ) :
    (diagOne (archUnitHom w c) : AdelicGL2 (𝓞 K) K) =
      archComplexGLAt hw (diagGL (Units.map (eC hw).toRingHom.toMonoidHom c) 1) := by
  set m : GL (Fin 2) ℂ := diagGL (Units.map (eC hw).toRingHom.toMonoidHom c) 1 with hm
  have hfin : glFin (𝓞 K) K (archComplexGLAt hw m) = 1 := glFin_adelicArchGLIncl K _
  have harch : glArch (𝓞 K) K (archComplexGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) := glArch_adelicArchGLIncl K _
  have hsnd : (((archUnitHom w c : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K).2 = 1 := by rw [archUnitHom_apply]; rfl
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [harch]
    refine glInf_ext K fun v => ?_
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self]
      ext i j
      rw [archComponent_apply, glArch_apply, glEquivOfRingEquiv_apply_entry]
      change ((Matrix.diagonal ![(((archUnitHom v c : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K), 1] i j).1 v) = _
      rw [archUnitHom_apply]
      fin_cases i <;> fin_cases j
      · simp [Matrix.diagonal, hm, diagGL]
        show Function.update (1 : (v : InfinitePlace K) → v.Completion) v (c : v.Completion) v = _
        rw [Function.update_self]
        exact ((eC hw).symm_apply_apply _).symm
      · simp [Matrix.diagonal, hm, diagGL]; rfl
      · simp [Matrix.diagonal, hm, diagGL]; rfl
      · simp [Matrix.diagonal, hm, diagGL]; rfl
    · rw [archComponent_archGLIncl_of_ne K hv]
      ext i j
      rw [archComponent_apply, glArch_apply]
      change ((Matrix.diagonal ![(((archUnitHom w c : (AdeleRing (𝓞 K) K)ˣ)) : AdeleRing (𝓞 K) K), 1] i j).1 v) =
        (1 : Matrix (Fin 2) (Fin 2) _) i j
      rw [archUnitHom_apply]
      fin_cases i <;> fin_cases j
      · simp [Matrix.diagonal]
        show Function.update (1 : (v : InfinitePlace K) → v.Completion) w (c : w.Completion) v = 1
        rw [Function.update_of_ne hv]; rfl
      · simp [Matrix.diagonal]; rfl
      · simp [Matrix.diagonal]; rfl
      · simp [Matrix.diagonal]; rfl
  · rw [hfin, glFin_diagOne_of_snd_eq_one K _ hsnd]

theorem centralScalar_iotaW_eq_archComplexGLAt {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂˣ) :
    centralScalar (𝓞 K) K (iotaW hw t) = archComplexGLAt hw (diagGL t t) := by
  set m : GL (Fin 2) ℂ := diagGL t t with hm
  have hfin : glFin (𝓞 K) K (archComplexGLAt hw m) = 1 := glFin_adelicArchGLIncl K _
  have harch : glArch (𝓞 K) K (archComplexGLAt hw m) =
      archGLIncl K w (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m) := glArch_adelicArchGLIncl K _
  have hι : iotaW hw t = archUnitHom w (Units.map (eC hw).symm.toRingHom.toMonoidHom t) := rfl
  have hmat : ((centralScalar (𝓞 K) K (iotaW hw t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      Matrix.diagonal ![((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K), ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)] := by
    ext i j
    change (Matrix.scalar (Fin 2) ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j = _
    rw [Matrix.scalar_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [harch]
    refine glInf_ext K fun v => ?_
    ext i j
    rw [archComponent_apply, glArch_apply, hmat, hι, archUnitHom_apply]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archGLIncl_self, glEquivOfRingEquiv_apply_entry]
      fin_cases i <;> fin_cases j
      · simp [Matrix.diagonal, hm, diagGL]
        show Function.update (1 : (v : InfinitePlace K) → v.Completion) v _ v = _
        rw [Function.update_self]; rfl
      · simp [Matrix.diagonal, hm, diagGL]; rfl
      · simp [Matrix.diagonal, hm, diagGL]; rfl
      · simp [Matrix.diagonal, hm, diagGL]
        show Function.update (1 : (v : InfinitePlace K) → v.Completion) v _ v = _
        rw [Function.update_self]; rfl
    · rw [archComponent_archGLIncl_of_ne K hv]
      fin_cases i <;> fin_cases j
      · simp [Matrix.diagonal]
        show Function.update (1 : (v : InfinitePlace K) → v.Completion) w _ v = 1
        rw [Function.update_of_ne hv]; rfl
      · simp [Matrix.diagonal]; rfl
      · simp [Matrix.diagonal]; rfl
      · simp [Matrix.diagonal]
        show Function.update (1 : (v : InfinitePlace K) → v.Completion) w _ v = 1
        rw [Function.update_of_ne hv]; rfl
  · rw [hfin]
    ext i j
    rw [glFin_apply, hmat, hι, archUnitHom_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal] <;> rfl

end DCFN

namespace DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

theorem centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    g * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  change (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K)) =
    Matrix.scalar (Fin 2) ((z : AdeleRing (𝓞 K) K)) * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
  exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm

theorem whittakerCoefficient_centralScalar_mul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (z : (AdeleRing (𝓞 K) K)ˣ) (c : ℂ)
    (hZ : ∀ g, φ (centralScalar (𝓞 K) K z * g) = c * φ g) (g : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (centralScalar (𝓞 K) K z * g) = c * whittakerCoefficient K pins ψ φ α g := by
  unfold whittakerCoefficient
  rw [← integral_const_mul]
  congr 1
  funext u
  rw [← mul_assoc, centralScalar_comm, mul_assoc, hZ]
  ring

theorem iotaW_snd {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂˣ) :
    ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem iotaW_fst_self {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂˣ) :
    ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = (eC hw).symm t := by
  show Function.update (1 : (v : InfinitePlace K) → v.Completion) w _ w = _
  rw [Function.update_self]; rfl

theorem iotaW_fst_of_ne {w v : InfinitePlace K} (hw : w.IsComplex) (hv : v ≠ w) (t : ℂˣ) :
    ((iotaW hw t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v = ((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v := by
  show Function.update (1 : (v : InfinitePlace K) → v.Completion) w _ v = _
  rw [Function.update_of_ne hv]; rfl

theorem ideleNorm_iotaW {w : InfinitePlace K} (hw : w.IsComplex) (t : ℂˣ) :
    ideleNorm K (iotaW hw t) = ‖(t : ℂ)‖ ^ 2 := by
  rw [ideleNorm_eq_norm_pow_mul_of_eq_off K w 1 (iotaW hw t) (iotaW_snd K hw t) (fun v hv => iotaW_fst_of_ne K hw hv t),
    iotaW_fst_self, norm_eC_symm, mult_eq_two_of_isComplex K hw]
  have : ∏ w' ∈ Finset.univ.erase w, ‖(((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w'‖ ^ w'.mult = 1 :=
    Finset.prod_eq_one fun w' _ => by
      have : (((1 : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w' = 1 := rfl
      rw [this, norm_one, one_pow]
  rw [this, mul_one]

theorem diagOne_eq_central_mul_g0_mul (w : InfinitePlace K) (hw : w.IsComplex) (b a : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w')
    (t ζ : ℂˣ) (u : ℝ) (ht : (t : ℂ) ^ 2 = eC hw (((a : AdeleRing (𝓞 K) K)).1 w))
    (huζ : Complex.exp (u : ℂ) * (ζ : ℂ) = t) :
    (diagOne a : AdelicGL2 (𝓞 K) K) =
      centralScalar (𝓞 K) K (iotaW hw t) * (g0 w b * archComplexGLAt hw (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ)) := by
  set c : (w.Completion)ˣ := infiniteUnitsComponent (𝓞 K) K w a with hc
  set z : ℂˣ := Units.map (eC hw).toRingHom.toMonoidHom c with hz
  have hz' : (z : ℂ) = eC hw (((a : AdeleRing (𝓞 K) K)).1 w) := rfl
  have hdec := diagGL_eq_scalar_mul_split_mul_circle z t ζ u (by rw [ht, hz']) huζ
  calc (diagOne a : AdelicGL2 (𝓞 K) K)
      = diagOne (bprime w b) * diagOne (archUnitHom w c) := by
          rw [← map_mul, ← eq_bprime_mul_archUnitHom K w b a ha hb hab]
    _ = g0 w b * archComplexGLAt hw (diagGL z 1) := by rw [diagOne_archUnitHom_eq_archComplexGLAt K hw c]; rfl
    _ = g0 w b * (centralScalar (𝓞 K) K (iotaW hw t) * archComplexGLAt hw (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ)) := by
          rw [hdec, map_mul, centralScalar_iotaW_eq_archComplexGLAt]
    _ = centralScalar (𝓞 K) K (iotaW hw t) * (g0 w b * archComplexGLAt hw (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ)) := by
          rw [← mul_assoc, centralScalar_comm, mul_assoc]

theorem norm_W_diagOne_eq_rpow_mul_norm_fstr (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') :
    ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
        (diagOne a)‖ =
      ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ w₀ * ‖fstr D hw b x p ‖((a : AdeleRing (𝓞 K) K)).1 w‖‖ := by

  set r : ℝ := ‖((a : AdeleRing (𝓞 K) K)).1 w‖ with hr
  have hzr : ‖eC hw (((a : AdeleRing (𝓞 K) K)).1 w)‖ = r := norm_eC K hw _
  have hr0 : 0 < r := by
    have h := congrArg (fun q : AdeleRing (𝓞 K) K => q.1 w) a.mul_inv
    change ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 at h
    exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
  have hz0 : eC hw (((a : AdeleRing (𝓞 K) K)).1 w) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hzr; exact hr0.ne' hzr.symm
  set t₀ : ℂ := (eC hw (((a : AdeleRing (𝓞 K) K)).1 w)) ^ ((2 : ℂ)⁻¹) with ht₀
  have ht₀sq : t₀ ^ 2 = eC hw (((a : AdeleRing (𝓞 K) K)).1 w) := by
    rw [ht₀]
    exact_mod_cast Complex.cpow_nat_inv_pow _ two_ne_zero
  have ht₀0 : t₀ ≠ 0 := fun h0 => hz0 (by rw [← ht₀sq, h0]; norm_num)
  have hnt : ‖t₀‖ ^ 2 = r := by rw [← norm_pow, ht₀sq, hzr]
  have hnt0 : 0 < ‖t₀‖ := norm_pos_iff.2 ht₀0
  set t : ℂˣ := Units.mk0 t₀ ht₀0 with htdef
  set ζ₀ : ℂ := t₀ / (‖t₀‖ : ℂ) with hζ₀
  have hζ₀0 : ζ₀ ≠ 0 := div_ne_zero ht₀0 (by exact_mod_cast hnt0.ne')
  have hζ₀1 : ‖ζ₀‖ = 1 := by rw [hζ₀, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnt0, div_self hnt0.ne']
  set ζ : ℂˣ := Units.mk0 ζ₀ hζ₀0 with hζdef
  set u : ℝ := Real.log r / 2 with hu
  have hexp : Real.exp u = ‖t₀‖ := by
    have h1 : Real.exp u = r ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos hr0, hu]; congr 1; ring
    rw [h1, ← hnt, ← Real.sqrt_eq_rpow, Real.sqrt_sq hnt0.le]
  have huζ : Complex.exp (u : ℂ) * (ζ : ℂ) = t := by
    show Complex.exp (u : ℂ) * ζ₀ = t₀
    rw [← Complex.ofReal_exp, hexp, hζ₀, mul_div_cancel₀ _ (by exact_mod_cast hnt0.ne')]

  have hgeo := diagOne_eq_central_mul_g0_mul K w hw b a ha hb hab t ζ u ht₀sq huζ
  have hval : whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1
        (diagOne a) = ((ξ ⟨iotaW hw t, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * ((ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * fstr D hw b x p r) := by
    rw [hgeo, whittakerCoefficient_centralScalar_mul K _ _ (x p) 1 (iotaW hw t) _ (hxZ p (iotaW hw t))]
    congr 1
    have h5 := Fstr_mul_circleGL2 K D hw b x hwt p ζ hζ₀1 (splitTorusGL2Complex (u : ℂ))
    unfold Fstr W at h5
    rw [h5]
    congr 1
    unfold fstr
    rw [dite_eq_left p.2]
    rfl

  have hNι : NumberField.TateGlobal.ideleNorm K (iotaW hw t) = r := by
    rw [ideleNorm_iotaW K hw t]; exact hnt
  have hζ1 : ‖(ζ : ℂ)‖ = 1 := hζ₀1
  rw [hval, norm_mul, norm_mul, hξ, hNι, norm_zpow, hζ1, one_zpow, one_mul]

omit [NumberField K] in
theorem rpow_eq_rpow_mult {w : InfinitePlace K} (hw : w.IsComplex) (r w₀ : ℝ) :
    r ^ w₀ = r ^ ((w.mult : ℝ) * w₀ / 2) := by
  rw [mult_eq_two_of_isComplex K hw]; congr 1; push_cast; ring

theorem exists_norm_fstr_le (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (hgr : ∀ p, ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (x p) 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Fin (n + 1)) (y : ℝ), 0 < y → ‖fstr D hw b x p y‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_W_diagOne_le_norm_rpow_of_gr K D w₀ w x hgr b
  refine ⟨C, hC0, fun p y hy => ?_⟩

  have hy0 : (eC hw).symm (y : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (eC hw) h0
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact hy.ne' (by exact_mod_cast this)
  set cy : (w.Completion)ˣ := Units.mk0 ((eC hw).symm (y : ℂ)) hy0 with hcy
  set a : (AdeleRing (𝓞 K) K)ˣ := bprime w b * archUnitHom w cy with hadef
  have ha2 : ((a : AdeleRing (𝓞 K) K)).2 = 1 := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1
    rw [bprime_snd, hb, archUnitHom_apply, one_mul]; rfl
  have haw : ((a : AdeleRing (𝓞 K) K)).1 w = (eC hw).symm (y : ℂ) := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = _
    rw [bprime_fst_self, one_mul, archUnitHom_apply]
    show Function.update (1 : (v : InfinitePlace K) → v.Completion) w (cy : w.Completion) w = _
    rw [Function.update_self]; rfl
  have hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w' := by
    intro w' hw'
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = _
    rw [bprime_fst_of_ne hw', archUnitHom_apply]
    show _ * Function.update (1 : (v : InfinitePlace K) → v.Completion) w (cy : w.Completion) w' = _
    rw [Function.update_of_ne hw']; exact mul_one _
  have hnorm : ‖((a : AdeleRing (𝓞 K) K)).1 w‖ = y := by
    rw [haw, norm_eC_symm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  have h7 := norm_W_diagOne_eq_rpow_mul_norm_fstr K D ξ w₀ hξ w hw n x hxZ hwt b hb p a ha2 hab
  have h8 := hC p a ha2 hab
  rw [h7, hnorm, ← rpow_eq_rpow_mult K hw] at h8

  have hyw : 0 < y ^ w₀ := Real.rpow_pos_of_pos hy _
  rw [mul_comm C] at h8
  exact le_of_mul_le_mul_left h8 hyw

end DCFN

namespace IFC

open DCFN NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K]

theorem g0_comm {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ) (m : GL (Fin 2) ℂ) :
    archComplexGLAt hw m * g0 w b = g0 w b * archComplexGLAt hw m :=
  archComplexGLAt_mul_g0 K hw b m

theorem hM_string (D : Set (AdelicGL2 (𝓞 K) K)) {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p)) :
    ∀ (p : Fin (n + 1)) (ζ : ℂˣ), ‖(ζ : ℂ)‖ = 1 → ∀ h : GL (Fin 2) ℂ,
      whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (h * circleGL2 ζ)) =
        (ζ : ℂ) ^ ((n : ℤ) - 2 * (p : ℕ)) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw h) := by
  intro p ζ hζ h
  have h5 := Fstr_mul_circleGL2 K D hw b x hwt p ζ hζ h
  unfold Fstr W at h5
  exact h5

theorem twist (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    {n : ℕ} (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p))
    (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') :
    ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a)‖ =
      ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) *
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log ‖((a : AdeleRing (𝓞 K) K)).1 w‖ / 2 : ℝ) : ℂ)))‖ := by
  have h7 := norm_W_diagOne_eq_rpow_mul_norm_fstr K D ξ w₀ hξ w hw n x hxZ hwt b hb p a ha hab
  rw [h7, ← rpow_eq_rpow_mult K hw]
  congr 2
  unfold fstr
  rw [dite_eq_left p.2]
  rfl

theorem large (D : Set (AdelicGL2 (𝓞 K) K)) (w₀ : ℝ) {w : InfinitePlace K} (hw : w.IsComplex)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hgr : ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) :
    ∃ B : ℝ, ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
      (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (diagOne a)‖ ≤ B * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) := by
  have _ := hw
  have _ := hb
  obtain ⟨C, -, hC⟩ := exists_norm_W_diagOne_le_norm_rpow_of_gr K D w₀ w (n := 0) (fun _ => φ) (fun _ => hgr) b
  exact ⟨C, fun a ha hab => hC 0 a ha hab⟩

theorem bounded (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    {w : InfinitePlace K} (hw : w.IsComplex) (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      φ (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g)
    (hgr : ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 g‖ ≤ C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) :
    ∃ B : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ)))‖ ≤ B := by
  obtain ⟨B, hB⟩ := large D w₀ hw b hb φ hgr
  refine ⟨B, fun y hy _ => ?_⟩

  have hy0 : (eC hw).symm (y : ℂ) ≠ 0 := by
    intro h0
    have := congrArg (eC hw) h0
    rw [RingEquiv.apply_symm_apply, map_zero] at this
    exact hy.ne' (by exact_mod_cast this)
  set cy : (w.Completion)ˣ := Units.mk0 ((eC hw).symm (y : ℂ)) hy0 with hcy
  set a : (AdeleRing (𝓞 K) K)ˣ := bprime w b * archUnitHom w cy with hadef
  have ha2 : ((a : AdeleRing (𝓞 K) K)).2 = 1 := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1
    rw [bprime_snd, hb, archUnitHom_apply, one_mul]; rfl
  have haw : ((a : AdeleRing (𝓞 K) K)).1 w = (eC hw).symm (y : ℂ) := by
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = _
    rw [bprime_fst_self, one_mul, archUnitHom_apply]
    show Function.update (1 : (v : InfinitePlace K) → v.Completion) w (cy : w.Completion) w = _
    rw [Function.update_self]; rfl
  have hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w' := by
    intro w' hw'
    show ((bprime w b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' * ((archUnitHom w cy : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w' = _
    rw [bprime_fst_of_ne hw', archUnitHom_apply]
    show _ * Function.update (1 : (v : InfinitePlace K) → v.Completion) w (cy : w.Completion) w' = _
    rw [Function.update_of_ne hw']; exact mul_one _
  have heCa : eC hw (((a : AdeleRing (𝓞 K) K)).1 w) = (y : ℂ) := by rw [haw, RingEquiv.apply_symm_apply]
  have hnorm : ‖((a : AdeleRing (𝓞 K) K)).1 w‖ = y := by
    rw [haw, norm_eC_symm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]

  have hsy0 : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have ht0 : ((Real.sqrt y : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsy0.ne'
  set t : ℂˣ := Units.mk0 ((Real.sqrt y : ℝ) : ℂ) ht0 with htdef
  have htsq : (t : ℂ) ^ 2 = eC hw (((a : AdeleRing (𝓞 K) K)).1 w) := by
    rw [heCa]; show ((Real.sqrt y : ℝ) : ℂ) ^ 2 = (y : ℂ)
    rw [← Complex.ofReal_pow, Real.sq_sqrt hy.le]
  have huζ : Complex.exp (((Real.log y / 2 : ℝ)) : ℂ) * ((1 : ℂˣ) : ℂ) = t := by
    rw [Units.val_one, mul_one, ← Complex.ofReal_exp]
    show ((Real.exp (Real.log y / 2) : ℝ) : ℂ) = ((Real.sqrt y : ℝ) : ℂ)
    congr 1
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]; congr 1; ring
  have hgeo := diagOne_eq_central_mul_g0_mul K w hw b a ha2 hb hab t 1 (Real.log y / 2) htsq huζ
  rw [circleGL2_one, mul_one] at hgeo
  have hval : whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) φ 1
        (diagOne a) = ((ξ ⟨iotaW hw t, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) φ 1 (g0 w b * archComplexGLAt hw (splitTorusGL2Complex ((Real.log y / 2 : ℝ) : ℂ))) := by
    rw [hgeo, whittakerCoefficient_centralScalar_mul K _ _ φ 1 (iotaW hw t) _ (hφZ (iotaW hw t))]
  have hNι : NumberField.TateGlobal.ideleNorm K (iotaW hw t) = y := by
    rw [ideleNorm_iotaW K hw t]
    show ‖((Real.sqrt y : ℝ) : ℂ)‖ ^ 2 = y
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsy0, Real.sq_sqrt hy.le]
  have h8 := hB a ha2 hab
  rw [hval, norm_mul, hξ, hNι, hnorm, ← rpow_eq_rpow_mult K hw, mul_comm B] at h8
  exact le_of_mul_le_mul_left h8 (Real.rpow_pos_of_pos hy _)

end IFC

namespace DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

theorem diagOne_eq_centralScalar_mul_diagOne_mul_archComplexGLAt
    (w : InfinitePlace K) (hw : w.IsComplex)
    (a b' z : (AdeleRing (𝓞 K) K)ˣ)
    (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) (hb' : ((b' : AdeleRing (𝓞 K) K)).2 = 1) (hz : ((z : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b' : AdeleRing (𝓞 K) K)).1 w')
    (hbw : ((b' : AdeleRing (𝓞 K) K)).1 w = 1)
    (t ζ : ℂˣ) (u : ℝ)
    (ht : (t : ℂ) ^ 2 = InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (((a : AdeleRing (𝓞 K) K)).1 w))
    (huζ : Complex.exp (u : ℂ) * (ζ : ℂ) = t)
    (hzw' : ∀ w' : InfinitePlace K, w' ≠ w → ((z : AdeleRing (𝓞 K) K)).1 w' = 1)
    (hzw : InfinitePlace.Completion.ringEquivComplexOfIsComplex hw (((z : AdeleRing (𝓞 K) K)).1 w) = t) :
    diagOne a = centralScalar (𝓞 K) K z * (diagOne b' * archComplexGLAt hw (splitTorusGL2Complex (u : ℂ) * circleGL2 ζ)) ∧
      archComponent K w (glArch (𝓞 K) K (diagOne b')) = 1 := by

  have hb'eq : b' = bprime w a := by
    apply Units.ext
    refine Prod.ext (funext fun v => ?_) ?_
    · by_cases hv : v = w
      · subst hv; rw [bprime_fst_self, hbw]
      · rw [bprime_fst_of_ne hv, hab v hv]
    · rw [bprime_snd, hb', ha]
  have hzeq : z = iotaW hw t := by
    apply Units.ext
    refine Prod.ext (funext fun v => ?_) ?_
    · by_cases hv : v = w
      · subst hv
        rw [iotaW_fst_self]
        apply (eC hw).injective
        rw [RingEquiv.apply_symm_apply]
        exact hzw
      · rw [iotaW_fst_of_ne K hw hv, hzw' v hv]; rfl
    · rw [iotaW_snd, hz]
  have haa : ∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((a : AdeleRing (𝓞 K) K)).1 w' :=
    fun _ _ => rfl
  have hgeo := diagOne_eq_central_mul_g0_mul K w hw a a ha ha haa t ζ u ht huζ
  refine ⟨?_, ?_⟩
  · rw [hgeo, hzeq, hb'eq]; rfl
  · rw [hb'eq]; exact archComponent_glArch_g0 K w a

end DCFN

namespace DCFN

open NumberField.TateGlobal NumberField.AdeleRing NumberField.InfinitePlace.Completion

variable (K : Type) [Field K] [NumberField K]

def sqrtC {w : InfinitePlace K} (hw : w.IsComplex) (tw : w.Completion) : ℂ := (eC hw tw) ^ ((2 : ℂ)⁻¹)

omit [NumberField K] in
theorem sqrtC_sq {w : InfinitePlace K} (hw : w.IsComplex) (tw : w.Completion) : sqrtC K hw tw ^ 2 = eC hw tw := by
  unfold sqrtC; exact_mod_cast Complex.cpow_nat_inv_pow _ two_ne_zero

omit [NumberField K] in
theorem sqrtC_ne_zero {w : InfinitePlace K} (hw : w.IsComplex) {tw : w.Completion} (htw : tw ≠ 0) : sqrtC K hw tw ≠ 0 := by
  intro h0
  have h := sqrtC_sq K hw tw
  rw [h0] at h
  have : eC hw tw = 0 := by rw [← h]; norm_num
  exact htw ((eC hw).injective (by rw [this, map_zero]))

omit [NumberField K] in
theorem norm_sqrtC_sq {w : InfinitePlace K} (hw : w.IsComplex) (tw : w.Completion) : ‖sqrtC K hw tw‖ ^ 2 = ‖tw‖ := by
  rw [← norm_pow, sqrtC_sq, norm_eC]

def muC (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    {w : InfinitePlace K} (hw : w.IsComplex) (w₀' : ℝ) (n : ℕ) (p : Fin (n + 1)) (tw : w.Completion) : ℂ :=
  if htw : tw = 0 then (if (w.mult : ℝ) * w₀' / 2 = 0 then 1 else 0) else
    ((ξ ⟨iotaW hw (Units.mk0 (sqrtC K hw tw) (sqrtC_ne_zero K hw htw)), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
      (sqrtC K hw tw / (‖sqrtC K hw tw‖ : ℂ)) ^ ((n : ℤ) - 2 * (p : ℕ))

theorem exists_mu_whittakerCoefficient_diagOne_eq (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p)) :
    ∃ μ : Fin (n + 1) → w.Completion → ℂ,
      (∀ (p : Fin (n + 1)) (t : w.Completion), ‖μ p t‖ = ‖t‖ ^ ((w.mult : ℝ) * w₀ / 2)) ∧
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
        ∀ (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K D
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
            (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a) =
          μ p (((a : AdeleRing (𝓞 K) K)).1 w) *
            whittakerCoefficient K (productionPinsOf K D
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) (x p) 1
              (diagOne (b * (archUnitHom w (infiniteUnitsComponent (𝓞 K) K w b))⁻¹) *
                archComplexGLAt hw (splitTorusGL2Complex ((Real.log ‖((a : AdeleRing (𝓞 K) K)).1 w‖ / 2 : ℝ) : ℂ))) := by
  refine ⟨muC K D ξ hw w₀ n, ?_, ?_⟩
  · intro p tw
    by_cases htw : tw = 0
    · unfold muC
      rw [dite_eq_left htw, htw, norm_zero]
      by_cases he : (w.mult : ℝ) * w₀ / 2 = 0
      · rw [ite_eq_left he, he, Real.rpow_zero, norm_one]
      · rw [ite_eq_right he, Real.zero_rpow he, norm_zero]
    have ht0 := sqrtC_ne_zero K hw htw
    have hnt0 : 0 < ‖sqrtC K hw tw‖ := norm_pos_iff.2 ht0
    have hζ1 : ‖sqrtC K hw tw / (‖sqrtC K hw tw‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnt0, div_self hnt0.ne']
    unfold muC
    rw [dite_eq_right htw, norm_mul, norm_zpow, hζ1, one_zpow, mul_one, hξ, ideleNorm_iotaW, ← rpow_eq_rpow_mult K hw]
    show (‖sqrtC K hw tw‖ ^ 2) ^ w₀ = ‖tw‖ ^ w₀
    rw [norm_sqrtC_sq]
  · intro b hb p a ha hab

    set tw : w.Completion := ((a : AdeleRing (𝓞 K) K)).1 w with htw
    set r : ℝ := ‖tw‖ with hr
    have hr0 : 0 < r := by
      have h := congrArg (fun q : AdeleRing (𝓞 K) K => q.1 w) a.mul_inv
      change ((a : AdeleRing (𝓞 K) K)).1 w * (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w = 1 at h
      exact norm_pos_iff.2 (left_ne_zero_of_mul_eq_one h)
    have htw0 : tw ≠ 0 := norm_pos_iff.1 hr0
    set t₀ : ℂ := sqrtC K hw tw with ht₀
    have ht₀0 : t₀ ≠ 0 := sqrtC_ne_zero K hw htw0
    have hnt : ‖t₀‖ ^ 2 = r := norm_sqrtC_sq K hw tw
    have hnt0 : 0 < ‖t₀‖ := norm_pos_iff.2 ht₀0
    set t : ℂˣ := Units.mk0 t₀ ht₀0 with htdef
    set ζ₀ : ℂ := t₀ / (‖t₀‖ : ℂ) with hζ₀
    have hζ₀0 : ζ₀ ≠ 0 := div_ne_zero ht₀0 (by exact_mod_cast hnt0.ne')
    have hζ₀1 : ‖ζ₀‖ = 1 := by rw [hζ₀, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hnt0, div_self hnt0.ne']
    set ζ : ℂˣ := Units.mk0 ζ₀ hζ₀0 with hζdef
    set u : ℝ := Real.log r / 2 with hu
    have hexp : Real.exp u = ‖t₀‖ := by
      have h1 : Real.exp u = r ^ ((1 : ℝ) / 2) := by
        rw [Real.rpow_def_of_pos hr0, hu]; congr 1; ring
      rw [h1, ← hnt, ← Real.sqrt_eq_rpow, Real.sqrt_sq hnt0.le]
    have huζ : Complex.exp (u : ℂ) * (ζ : ℂ) = t := by
      show Complex.exp (u : ℂ) * ζ₀ = t₀
      rw [← Complex.ofReal_exp, hexp, hζ₀, mul_div_cancel₀ _ (by exact_mod_cast hnt0.ne')]
    have hgeo := diagOne_eq_central_mul_g0_mul K w hw b a ha hb hab t ζ u (sqrtC_sq K hw tw) huζ
    have hζ1 : ‖(ζ : ℂ)‖ = 1 := hζ₀1
    rw [hgeo, whittakerCoefficient_centralScalar_mul K _ _ (x p) 1 (iotaW hw t) _ (hxZ p (iotaW hw t))]
    have h5 := Fstr_mul_circleGL2 K D hw b x hwt p ζ hζ1 (splitTorusGL2Complex (u : ℂ))
    unfold Fstr W at h5
    rw [h5, ← mul_assoc]
    congr 1
    unfold muC
    rw [dite_eq_right htw0]
    rfl

end DCFN

theorem exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (w : InfinitePlace K) (hw : w.IsComplex)
    (n : ℕ) (x : Fin (n + 1) → (AdelicGL2 (𝓞 K) K → ℂ))
    (hxZ : ∀ p (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x p (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x p g)
    (hwt : ∀ p : Fin (n + 1), HasCircleWeightAt hw ((n : ℤ) - 2 * (p : ℕ)) (x p)) :
    ∃ μ : Fin (n + 1) → w.Completion → ℂ,
      (∀ (p : Fin (n + 1)) (t : w.Completion), ‖μ p t‖ = ‖t‖ ^ ((w.mult : ℝ) * w₀ / 2)) ∧
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
        ∀ (p : Fin (n + 1)) (a : (AdeleRing (𝓞 K) K)ˣ), ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ w → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne a) =
            μ p (((a : AdeleRing (𝓞 K) K)).1 w) *
              whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
        (NumberField.StandardAddChar.stdAddChar K) (x p) 1 (diagOne (b * (NumberField.TateGlobal.archUnitHom w (NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w b))⁻¹) *
                archComplexGLAt hw (splitTorusGL2Complex ((Real.log ‖((a : AdeleRing (𝓞 K) K)).1 w‖ / 2 : ℝ) : ℂ)))
    := DCFN.exists_mu_whittakerCoefficient_diagOne_eq K D ξ w₀ hξ w hw n x hxZ hwt

/-! ## Part 2 (pin 714:21–568 = pin 716:21–568): the cuspidal-constituent prelude

The 514-line prelude the two cusp files share, written once here: the coordinate/evaluation engine
`EvalCoords`, the place decomposition `KUNIFPlace` (the `GL₂(w.Completion)` factor into a diagonal, a
row isometry and a scalar), the adèlic reassembly `KUNIFAdelic` (`archIdele`, `archProd`, and the
`exists_factor` of a row-isometry-invariant compact point), and the cut engine `KUNIFCut`
(`exists_fd_stable`, `whittakerCoefficient_mul`, `exists_bound`). -/

open MeasureTheory Complex
open scoped Real Classical

namespace EvalCoords

variable {X : Type*}

def vanishingOn (E : Submodule ℂ (X → ℂ)) (s : Finset X) : Submodule ℂ E where
  carrier := {e | ∀ x ∈ s, (e : X → ℂ) x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb x hx => by
    simp only [Submodule.coe_add, Pi.add_apply, ha x hx, hb x hx, add_zero]
  smul_mem' := fun c {a} ha x hx => by
    simp only [Submodule.coe_smul, Pi.smul_apply, ha x hx, smul_zero]

theorem vanishingOn_mono (E : Submodule ℂ (X → ℂ)) {s t : Finset X} (h : s ⊆ t) :
    vanishingOn E t ≤ vanishingOn E s := fun _ he x hx => he x (h hx)

theorem exists_finset_separating (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ s : Finset X, ∀ e ∈ E, (∀ x ∈ s, e x = 0) → e = 0 := by
  classical

  have key : ∀ k : ℕ, k ≤ Module.finrank ℂ E →
      ∃ s : Finset X, Module.finrank ℂ (vanishingOn E s) ≤ Module.finrank ℂ E - k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨∅, (Submodule.finrank_le _).trans le_rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨s, hs⟩ := ih (Nat.le_of_succ_le hk)
      by_cases hbot : vanishingOn E s = ⊥
      · refine ⟨s, ?_⟩
        rw [hbot, finrank_bot]
        exact Nat.zero_le _
      · obtain ⟨e, he, hne⟩ := (Submodule.ne_bot_iff _).mp hbot
        have hne' : (e : X → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
        obtain ⟨x, hx⟩ := Function.ne_iff.mp hne'
        refine ⟨insert x s, ?_⟩
        have hlt : vanishingOn E (insert x s) < vanishingOn E s := by
          refine lt_of_le_of_ne (vanishingOn_mono E (Finset.subset_insert x s)) fun h => ?_
          have : e ∈ vanishingOn E (insert x s) := h ▸ he
          exact hx (this x (Finset.mem_insert_self x s))
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
  obtain ⟨s, hs⟩ := key (Module.finrank ℂ E) le_rfl
  rw [Nat.sub_self, Nat.le_zero] at hs
  refine ⟨s, fun e he h0 => ?_⟩
  have hmem : (⟨e, he⟩ : E) ∈ vanishingOn E s := h0
  rw [Submodule.finrank_eq_zero.mp hs, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem exists_eval_coords (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ (s : Finset X) (b : X → X → ℂ), (∀ x, b x ∈ E) ∧ ∀ e ∈ E, e = ∑ x ∈ s, e x • b x := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_separating E

  let res : E →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun e x => (e : X → ℂ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker res = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun e he => ?_
    rw [LinearMap.mem_ker] at he
    apply Subtype.ext
    exact hs e e.2 fun x hx => congrFun he ⟨x, hx⟩
  obtain ⟨g, hg⟩ := res.exists_leftInverse_of_injective hker
  let b : X → X → ℂ := fun x => if hx : x ∈ s then ((g (Pi.single (⟨x, hx⟩ : s) 1) : E) : X → ℂ) else 0
  refine ⟨s, b, fun x => ?_, fun e he => ?_⟩
  · simp only [b]
    split_ifs
    · exact Submodule.coe_mem _
    · exact E.zero_mem
  · have h1 : (⟨e, he⟩ : E) = g (res ⟨e, he⟩) := (LinearMap.congr_fun hg ⟨e, he⟩).symm
    have h2 : res ⟨e, he⟩ = ∑ x : s, e x • (Pi.single x (1 : ℂ) : s → ℂ) := by
      ext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single y]
      · simp [res]
      · intro z _ hzy; simp [Ne.symm hzy]
      · intro hy; exact absurd (Finset.mem_univ y) hy
    have h3 : e = ((g (res ⟨e, he⟩) : E) : X → ℂ) := congrArg Subtype.val h1
    conv_lhs => rw [h3, h2, map_sum]
    rw [Submodule.coe_sum, Finset.univ_eq_attach, ← Finset.sum_attach s (fun x => e x • b x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, Submodule.coe_smul]
    simp only [b, dite_eq_left x.2]

end EvalCoords



namespace KUNIFPlace

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable {L : Type*} [NormedField L]

theorem diagOne_coe (t : Lˣ) :
    ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = Matrix.diagonal ![(t : L), 1] := rfl

theorem isRowIsometry_diagOne (t : Lˣ) (ht : ‖(t : L)‖ = 1) : IsRowIsometry (diagOne t) := by
  have h00 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = t := by simp [diagOne_coe]
  have h01 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by simp [diagOne_coe]
  have h10 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by simp [diagOne_coe]
  have h11 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by simp [diagOne_coe]
  refine ⟨?_, fun x y => ?_⟩
  · rw [diagOne_coe, Matrix.det_diagonal]
    simp [ht]
  · rw [h00, h01, h10, h11, mul_zero, add_zero, mul_zero, zero_add, mul_one, norm_mul, ht, mul_one]

theorem scalar_coe (u : Lˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      Matrix.diagonal fun _ => (u : L) := by
  show Matrix.scalar (Fin 2) (u : L) = _
  exact Matrix.scalar_apply _

theorem isRowIsometry_scalar (u : Lˣ) (hu : ‖(u : L)‖ = 1) :
    IsRowIsometry (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
  have h00 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = u := by
    simp
  have h01 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
    simp
  have h10 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    simp
  have h11 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = u := by
    simp
  refine ⟨?_, fun x y => ?_⟩
  · rw [scalar_coe, Matrix.det_diagonal]
    simp [hu]
  · rw [h00, h01, h10, h11, mul_zero, add_zero, mul_zero, zero_add, norm_mul, norm_mul, hu, mul_one, mul_one]

theorem det_scalar_two (u : Lˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = (u : L) * u := by
  rw [scalar_coe, Matrix.det_diagonal, Fin.prod_univ_two]

theorem det_diagOne (t : Lˣ) : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = t := by
  rw [diagOne_coe, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

variable {K : Type*} [Field K] [NumberField K]

theorem exists_sq_eq_of_norm_eq_one (c : ℂ) (hc : ‖c‖ = 1) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ * ζ = c := by
  refine ⟨Complex.exp (((Complex.arg c / 2 : ℝ) : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_add]
  have : ((Complex.arg c / 2 : ℝ) : ℂ) * Complex.I + ((Complex.arg c / 2 : ℝ) : ℂ) * Complex.I = Complex.arg c * Complex.I := by
    push_cast; ring
  rw [this]
  have h := Complex.norm_mul_exp_arg_mul_I c
  rwa [hc, Complex.ofReal_one, one_mul] at h

omit [NumberField K] in
theorem norm_extensionEmbedding (w : InfinitePlace K) (x : w.Completion) : ‖extensionEmbedding w x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

omit [NumberField K] in

theorem sq_eq_one_or_exists_sqrt (w : InfinitePlace K) (δ : w.Completion) (hδ : ‖δ‖ = 1) :
    δ * δ = 1 ∨ ∃ ζ : w.Completion, ‖ζ‖ = 1 ∧ ζ * ζ = δ := by
  by_cases hw : w.IsReal
  · left
    set e := ringEquivRealOfIsReal hw
    have hr : ‖e δ‖ = 1 := by
      rw [ringEquivRealOfIsReal_apply]
      rw [← hδ]
      exact (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) δ
    have hsq : e δ * e δ = 1 := by
      rcases (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp (by rw [← Real.norm_eq_abs]; exact hr) with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    apply e.injective
    rw [map_mul, map_one, hsq]
  · right
    have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    set e := ringEquivComplexOfIsComplex hw'
    have hc : ‖e δ‖ = 1 := by rw [ringEquivComplexOfIsComplex_apply, norm_extensionEmbedding, hδ]
    obtain ⟨ζ, hζ, hζζ⟩ := exists_sq_eq_of_norm_eq_one (e δ) hc
    refine ⟨e.symm ζ, ?_, ?_⟩
    · have := norm_extensionEmbedding w (e.symm ζ)
      rw [← ringEquivComplexOfIsComplex_apply hw', RingEquiv.apply_symm_apply] at this
      rw [← this, hζ]
    · apply e.injective
      rw [map_mul, RingEquiv.apply_symm_apply, hζζ]

omit [NumberField K] in

theorem exists_factor (w : InfinitePlace K) (κ : GL (Fin 2) w.Completion) (hκ : IsRowIsometry κ) :
    ∃ (s ζ : (w.Completion)ˣ) (κ' : rowIsometrySubgroup₀ w.Completion),
      ‖(s : w.Completion)‖ = 1 ∧ ‖(ζ : w.Completion)‖ = 1 ∧
      κ = diagOne s * (κ' : GL (Fin 2) w.Completion) * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ := by
  set δ := ((κ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det with hδ
  have hδ1 : ‖δ‖ = 1 := hκ.1
  have hδ0 : δ ≠ 0 := fun h => by rw [h, norm_zero] at hδ1; exact zero_ne_one hδ1
  rcases sq_eq_one_or_exists_sqrt w δ hδ1 with hsq | ⟨ζ, hζ1, hζζ⟩
  ·
    let s : (w.Completion)ˣ := ⟨δ, δ, hsq, hsq⟩
    have hs : ‖(s : w.Completion)‖ = 1 := hδ1
    have hiso : IsRowIsometry ((diagOne s)⁻¹ * κ) := (isRowIsometry_diagOne s hs).inv.mul hκ
    have hdet : ((((diagOne s)⁻¹ * κ : GL (Fin 2) w.Completion)) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, ← map_inv, det_diagOne, ← hδ]
      show ((s⁻¹ : (w.Completion)ˣ) : w.Completion) * δ = 1
      rw [Units.val_inv_eq_inv_val]
      exact inv_mul_cancel₀ hδ0
    refine ⟨s, 1, ⟨(diagOne s)⁻¹ * κ, (mem_rowIsometrySubgroup₀_iff _).mpr ⟨hdet, hiso⟩⟩, hs, by simp, ?_⟩
    rw [map_one, mul_one]
    show κ = diagOne s * ((diagOne s)⁻¹ * κ)
    rw [mul_inv_cancel_left]
  ·
    have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
    let u : (w.Completion)ˣ := Units.mk0 ζ hζ0
    have hu : ‖(u : w.Completion)‖ = 1 := hζ1
    have hiso : IsRowIsometry (κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹) :=
      hκ.mul (isRowIsometry_scalar u hu).inv
    have hdet : (((κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ : GL (Fin 2) w.Completion)) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, ← map_inv, det_scalar_two, ← hδ, ← hζζ]
      show ζ * ζ * (((u⁻¹ : (w.Completion)ˣ) : w.Completion) * ((u⁻¹ : (w.Completion)ˣ) : w.Completion)) = 1
      rw [Units.val_inv_eq_inv_val]
      show ζ * ζ * (ζ⁻¹ * ζ⁻¹) = 1
      field_simp
    refine ⟨1, u, ⟨κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹, (mem_rowIsometrySubgroup₀_iff _).mpr ⟨hdet, hiso⟩⟩,
      by simp, hu, ?_⟩
    rw [map_one, one_mul]
    show κ = κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u
    rw [inv_mul_cancel_right]

end KUNIFPlace



namespace KUNIFAdelic

open scoped Classical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable (K : Type) [Field K] [NumberField K]

noncomputable def archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((fun w => ((t w : (w.Completion)ˣ) : w.Completion)), 1)
  inv := ((fun w => (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion)), 1)
  val_inv := by
    refine Prod.ext ?_ ?_
    · funext w
      change ((t w : (w.Completion)ˣ) : w.Completion) * (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.mul_inv _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1
  inv_val := by
    refine Prod.ext ?_ ?_
    · funext w
      change (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion) * ((t w : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.inv_mul _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1

theorem archIdele_fst (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).1 w = t w := rfl

theorem archIdele_snd (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).2 = 1 := rfl

theorem gl_ext {g h : AdelicGL2 (𝓞 K) K} (h₁ : glFin (𝓞 K) K g = glFin (𝓞 K) K h)
    (h₂ : ∀ w : InfinitePlace K, archComponent K w (glArch (𝓞 K) K g) = archComponent K w (glArch (𝓞 K) K h)) :
    g = h := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  apply Prod.ext
  · funext w
    exact congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h₂ w)
  · exact congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h₁

theorem glFin_diagOne_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    glFin (𝓞 K) K (diagOne (archIdele K t)) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show (((diagOne (archIdele K t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 =
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem archComponent_diagOne_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (diagOne (archIdele K t))) = diagOne (t w) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show (((diagOne (archIdele K t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w =
    ((diagOne (t w) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_centralScalar_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    glFin (𝓞 K) K (centralScalar (𝓞 K) K (archIdele K t)) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show ((Matrix.scalar (Fin 2) ((archIdele K t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j).2 =
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem archComponent_centralScalar_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K (archIdele K t))) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (t w) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show ((Matrix.scalar (Fin 2) ((archIdele K t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j).1 w =
    (Matrix.scalar (Fin 2) ((t w : (w.Completion)ˣ) : w.Completion)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_adelicArchGLInclAt (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 K) K (adelicArchGLInclAt K w k) = 1 :=
  glFin_adelicArchGLIncl K _

theorem archComponent_adelicArchGLInclAt_self (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    archComponent K w (glArch (𝓞 K) K (adelicArchGLInclAt K w k)) = k := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archComponent_adelicArchGLInclAt_of_ne {v w : InfinitePlace K} (hvw : v ≠ w) (k : GL (Fin 2) w.Completion) :
    archComponent K v (glArch (𝓞 K) K (adelicArchGLInclAt K w k)) = 1 := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne K hvw]

def archProd (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) : AdelicGL2 (𝓞 K) K :=
  (Finset.univ : Finset (InfinitePlace K)).noncommProd (fun w => adelicArchGLInclAt K w (κ w))
    (Set.Pairwise.of_forall₂ fun x _ y _ =>
      if hxy : x = y then hxy ▸ Commute.refl _ else commute_adelicArchGLInclAt_of_ne K hxy _ _)

theorem glFin_archProd (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) : glFin (𝓞 K) K (archProd K κ) = 1 := by
  rw [archProd]
  refine Finset.noncommProd_induction _ _ _ (fun g : AdelicGL2 (𝓞 K) K => glFin (𝓞 K) K g = 1) ?_ ?_ ?_
  · intro a b ha hb
    rw [map_mul, ha, hb, one_mul]
  · exact map_one _
  · intro v _
    exact glFin_adelicArchGLInclAt K v (κ v)

theorem archComponent_archProd (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (archProd K κ)) = κ w := by
  let A : AdelicGL2 (𝓞 K) K →* GL (Fin 2) w.Completion := (archComponent K w).comp (glArch (𝓞 K) K)
  show A (archProd K κ) = κ w
  rw [archProd, ← Finset.mul_noncommProd_erase (s := Finset.univ)
    (a := w) (f := fun v => adelicArchGLInclAt K v (κ v)) (Finset.mem_univ w)]
  rw [map_mul]
  let comm : (((Finset.univ.erase w : Finset (InfinitePlace K)) : Set (InfinitePlace K))).Pairwise
      (fun a b => Commute (adelicArchGLInclAt K a (κ a)) (adelicArchGLInclAt K b (κ b))) :=
    Set.Pairwise.of_forall₂ fun x _ y _ =>
      if hxy : x = y then hxy ▸ Commute.refl _ else commute_adelicArchGLInclAt_of_ne K hxy _ _
  have h1 : A ((Finset.univ.erase w).noncommProd (fun v => adelicArchGLInclAt K v (κ v)) comm) = 1 := by
    refine Finset.noncommProd_induction _ _ _ (fun g => A g = 1) ?_ ?_ ?_
    · intro a b ha hb
      rw [map_mul, ha, hb, one_mul]
    · exact map_one A
    · intro v hv
      exact archComponent_adelicArchGLInclAt_of_ne K (Finset.ne_of_mem_erase hv).symm (κ v)
  rw [h1, mul_one]
  exact archComponent_adelicArchGLInclAt_self K w (κ w)

theorem archProd_induction (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) (p : AdelicGL2 (𝓞 K) K → Prop)
    (hone : p 1) (hmul : ∀ a b, p a → p b → p (a * b)) (hbase : ∀ w, p (adelicArchGLInclAt K w (κ w))) :
    p (archProd K κ) :=
  Finset.noncommProd_induction _ _ _ p hmul hone fun w _ => hbase w

theorem adelicArchGLInclAt_mem_adelicMaximalCompact (w : InfinitePlace K) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) : adelicArchGLInclAt K w k ∈ adelicMaximalCompact K := by
  refine mem_adelicMaximalCompact_iff.mpr ⟨?_, fun v => ?_⟩
  · rw [glFin_adelicArchGLInclAt]; exact Subgroup.one_mem _
  · by_cases hvw : v = w
    · subst hvw; rw [archComponent_adelicArchGLInclAt_self]; exact hk
    · rw [archComponent_adelicArchGLInclAt_of_ne K hvw]; exact isRowIsometry_one

theorem archProd_mem_adelicMaximalCompact (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion)
    (hκ : ∀ w, IsRowIsometry (κ w)) : archProd K κ ∈ adelicMaximalCompact K :=
  archProd_induction K κ (fun g => g ∈ adelicMaximalCompact K) (Subgroup.one_mem _)
    (fun _ _ ha hb => Subgroup.mul_mem _ ha hb) fun w => adelicArchGLInclAt_mem_adelicMaximalCompact K w _ (hκ w)

theorem ideleNorm_archIdele_eq_one (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (ht : ∀ w, ‖((t w : (w.Completion)ˣ) : w.Completion)‖ = 1) :
    NumberField.TateGlobal.ideleNorm K (archIdele K t) = 1 := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (archIdele_snd K t)]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [archIdele_fst, ht w, one_pow]

theorem mul_centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    g * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * g := by
  apply Units.ext
  show (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) =
    Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) * g
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 K) K) (fun _ => Commute.all _ _) _).symm.eq

theorem exists_factor (k : AdelicGL2 (𝓞 K) K) (hk1 : glFin (𝓞 K) K k = 1)
    (hk2 : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) :
    ∃ (s ζ : ∀ w : InfinitePlace K, (w.Completion)ˣ) (κ' : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion),
      (∀ w, ‖((s w : (w.Completion)ˣ) : w.Completion)‖ = 1) ∧ (∀ w, ‖((ζ w : (w.Completion)ˣ) : w.Completion)‖ = 1) ∧
      k = diagOne (archIdele K s) * archProd K (fun w => (κ' w : GL (Fin 2) w.Completion)) *
        centralScalar (𝓞 K) K (archIdele K ζ) := by
  choose s ζ κ' hs hζ hfac using fun w => KUNIFPlace.exists_factor w _ (hk2 w)
  refine ⟨s, ζ, κ', hs, hζ, gl_ext K ?_ fun w => ?_⟩
  · rw [hk1, map_mul, map_mul, glFin_diagOne_archIdele, glFin_archProd, glFin_centralScalar_archIdele, one_mul, one_mul]
  · rw [map_mul, map_mul, map_mul, map_mul, archComponent_diagOne_archIdele, archComponent_archProd,
      archComponent_centralScalar_archIdele]
    exact hfac w

end KUNIFAdelic



namespace KUNIFCut

open scoped Classical
open NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent NumberField.InfinitePlace IsDedekindDomain NumberField.AdelicLevel MeasureTheory

variable (K : Type) [Field K] [NumberField K]

theorem continuous_of_mem_cuspKFiniteSubmodule {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ cuspKFiniteSubmodule K pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ h
  · rintro φ ⟨_, hc, _⟩; exact hc
  · exact continuous_const
  · intro _ _ _ _ hu hv; exact hu.add hv
  · intro c _ _ hu; exact hu.const_smul c

theorem central_of_mem_cuspKFiniteSubmodule {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ cuspKFiniteSubmodule K pins ξ) (z : pins.Z) (g : AdelicGL2 (𝓞 K) K) :
    φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g := by
  revert g
  refine Submodule.span_induction (p := fun φ _ => ∀ g, φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) =
    ((ξ z : ℂˣ) : ℂ) * φ g) ?_ ?_ ?_ ?_ h
  · rintro φ ⟨hsat, -, -⟩ g
    let := pins.mS
    have h1 : IsAutomorphicFnAt K pins ξ (rightTranslate K 1 φ) := (hsat 1).1.1
    have h2 := ((lsXiMemberAt_iff (𝓞 K) K pins.μ pins.Z ξ pins.D (rightTranslate K 1 φ)).mp h1).1.central_transform z g
    simpa [rightTranslate] using h2
  · intro g; simp
  · intro u v _ _ hu hv g
    simp only [Pi.add_apply, hu g, hv g, mul_add]
  · intro c u _ hu g
    simp only [Pi.smul_apply, hu g, smul_eq_mul]
    ring

theorem exists_finiteDimensional_of_mem_archCutSubmodule (tys : ArchTypeFamily K) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ archCutSubmodule K tys) (w : InfinitePlace K) :
    ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W := by
  have hw := (mem_archCutSubmodule_iff K tys φ).mp hφ w
  refine Submodule.iSup_induction _
    (motive := fun φ => ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W) hw ?_ ?_ ?_
  · intro i φ hφi
    refine Submodule.span_induction (p := fun φ _ => ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ),
      FiniteDimensional ℂ W ∧ ∀ k : rowIsometrySubgroup₀ w.Completion,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W) ?_ ?_ ?_ ?_ hφi
    · rintro _ ⟨T, hT, v, rfl⟩
      refine ⟨LinearMap.range T, inferInstance, fun k => ?_⟩
      have : rightTranslate K (rowIsometryInclAt₀ K w k) (T v) = T ((tys.rep w i).ρ k v) := by
        funext x; exact (hT k v x).symm
      rw [this]; exact LinearMap.mem_range_self T _
    · exact ⟨⊥, inferInstance, fun k => by rw [rightTranslate_zero]; exact Submodule.zero_mem _⟩
    · rintro φ ψ - - ⟨W₁, hW₁, h₁⟩ ⟨W₂, hW₂, h₂⟩
      have := hW₁; have := hW₂
      exact ⟨W₁ ⊔ W₂, inferInstance, fun k => by
        rw [rightTranslate_add]; exact Submodule.add_mem_sup (h₁ k) (h₂ k)⟩
    · rintro c φ - ⟨W, hW, h⟩
      exact ⟨W, hW, fun k => by rw [rightTranslate_smul]; exact W.smul_mem c (h k)⟩
  · exact ⟨⊥, inferInstance, fun k => by rw [rightTranslate_zero]; exact Submodule.zero_mem _⟩
  · rintro φ ψ ⟨W₁, hW₁, h₁⟩ ⟨W₂, hW₂, h₂⟩
    have := hW₁; have := hW₂
    exact ⟨W₁ ⊔ W₂, inferInstance, fun k => by
      rw [rightTranslate_add]; exact Submodule.add_mem_sup (h₁ k) (h₂ k)⟩

variable {K}

theorem map_map_rightRegular (a b : AdelicGL2 (𝓞 K) K) (p : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) :
    (p.map (rightRegular K a)).map (rightRegular K b) = p.map (rightRegular K (b * a)) := by
  rw [← Submodule.map_comp, map_mul, Module.End.mul_eq_comp]

theorem exists_fd_stable (C : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hC_stab : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ C)
    (hC_fd : ∀ φ ∈ C, ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W)
    {x : AdelicGL2 (𝓞 K) K → ℂ} (hx : x ∈ C) :
    ∃ E : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ), FiniteDimensional ℂ E ∧ E ≤ C ∧ x ∈ E ∧
      ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ E,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ E := by
  suffices H : ∀ P : Finset (InfinitePlace K), ∃ E : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ),
      FiniteDimensional ℂ E ∧ E ≤ C ∧ x ∈ E ∧
      ∀ w ∈ P, ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ E, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ E by
    obtain ⟨E, h1, h2, h3, h4⟩ := H Finset.univ
    exact ⟨E, h1, h2, h3, fun w k φ hφ => h4 w (Finset.mem_univ w) k φ hφ⟩
  intro P
  induction P using Finset.induction_on with
  | empty =>
    exact ⟨ℂ ∙ x, inferInstance, (Submodule.span_singleton_le_iff_mem _ _).mpr hx, Submodule.mem_span_singleton_self x,
      fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w P hwP ih =>
    obtain ⟨E, hEfd, hEC, hxE, hEstab⟩ := ih
    have := hEfd
    let R : rowIsometrySubgroup₀ w.Completion → (AdelicGL2 (𝓞 K) K → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun k => rightRegular K (rowIsometryInclAt₀ K w k)
    let E' : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) := ⨆ k, E.map (R k)
    have hEE' : E ≤ E' := by
      have h1 : E.map (R 1) = E := by
        simp only [R, map_one, Module.End.one_eq_id, Submodule.map_id]
      calc E = E.map (R 1) := h1.symm
        _ ≤ E' := le_iSup (fun k => E.map (R k)) 1

    obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional E).mpr hEfd
    have hSE : ∀ s ∈ S, (s : AdelicGL2 (𝓞 K) K → ℂ) ∈ E := fun s hs => hS ▸ Submodule.subset_span hs
    choose W hWfd hW using fun s : S => hC_fd s (hEC (hSE s s.2)) w
    have : ∀ s : S, FiniteDimensional ℂ (W s) := hWfd
    have hE'le : E' ≤ ⨆ s : S, W s := by
      refine iSup_le fun k => ?_
      rw [← hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨s, hs⟩ (hW ⟨s, hs⟩ k)
    refine ⟨E', Submodule.finiteDimensional_of_le hE'le, ?_, hEE' hxE, ?_⟩
    · exact iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun φ hφ => hC_stab w k φ (hEC hφ)
    · intro v hv k φ hφ
      rcases Finset.mem_insert.mp hv with rfl | hvP
      ·
        have hle : E'.map (R k) ≤ E' := by
          rw [Submodule.map_iSup]
          refine iSup_le fun k' => ?_
          rw [show (E.map (R k')).map (R k) = E.map (R (k * k')) by
            simp only [R, map_map_rightRegular, ← map_mul]]
          exact le_iSup (fun k => E.map (R k)) (k * k')
        exact hle (Submodule.mem_map_of_mem hφ)
      ·
        have hvw : v ≠ w := fun h => hwP (h ▸ hvP)
        have hle : E'.map (rightRegular K (rowIsometryInclAt₀ K v k)) ≤ E' := by
          rw [Submodule.map_iSup]
          refine iSup_le fun k' => ?_
          have hcomm : rowIsometryInclAt₀ K v k * rowIsometryInclAt₀ K w k' =
              rowIsometryInclAt₀ K w k' * rowIsometryInclAt₀ K v k := by
            rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
            exact (commute_adelicArchGLInclAt_of_ne K hvw _ _).eq
          rw [show (E.map (R k')).map (rightRegular K (rowIsometryInclAt₀ K v k)) =
              (E.map (rightRegular K (rowIsometryInclAt₀ K v k))).map (R k') by
            simp only [R, map_map_rightRegular, hcomm]]
          refine (Submodule.map_mono ?_).trans (le_iSup (fun k => E.map (R k)) k')
          exact Submodule.map_le_iff_le_comap.mpr fun ψ hψ => hEstab v hvP k ψ hψ
        exact hle (Submodule.mem_map_of_mem hφ)

variable (K)

theorem whittakerCoefficient_mul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (α : K) (g k : AdelicGL2 (𝓞 K) K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (rightTranslate K k φ) α g := by
  simp only [whittakerCoefficient, rightTranslate, mul_assoc]

theorem exists_bound {x : AdelicGL2 (𝓞 K) K → ℂ} (hx : Continuous x) (g : AdelicGL2 (𝓞 K) K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ adelicMaximalCompact K, ‖x (g * k)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_adelicMaximalCompact K).exists_bound_of_continuousOn
    (f := fun k => x (g * k)) ((hx.comp (continuous_const.mul continuous_id)).continuousOn)
  exact ⟨max B 0, le_max_right _ _, fun k hk => (hB k hk).trans (le_max_left _ _)⟩

end KUNIFCut

/-! ## Part 3 (pins 716 and 714): the cusp-constituent expansion and its normalized companion -/

theorem CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ (m : ℕ) (ys : Fin m → (AdelicGL2 (𝓞 K) K → ℂ)) (M : ℝ),
      (∀ i, ys i ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) ∧
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∃ (cs : Fin m → ℂ) (ε : (AdeleRing (𝓞 K) K)ˣ),
          ((ε : AdeleRing (𝓞 K) K)).2 = 1 ∧ NumberField.TateGlobal.ideleNorm K ε = 1 ∧
          (∀ i, ‖cs i‖ ≤ M) ∧
          ∀ g : AdelicGL2 (𝓞 K) K,
            whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (g * k) =
              ∑ i, cs i * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys i) 1
              (g * diagOne ε)
    := by
  classical
  have _ := hc
  have _ := hd₁
  have _ := hd
  have _ := hcov
  have _ := hN
  set C : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys with hC

  have hC_cont : ∀ φ ∈ C, Continuous φ := fun φ hφ =>
    KUNIFCut.continuous_of_mem_cuspKFiniteSubmodule K (hV.1.le hφ.1.1)
  have hU : ∀ u' ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, AdelicLevel.glArch (𝓞 K) K u' = 1 :=
    fun u' hu' => hu'.2
  have hC_stab : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ C := by
    intro w k φ hφ
    refine ⟨⟨hV.1.rightTranslate_arch_mem w k φ hφ.1.1, ?_⟩,
      rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule K tys hφ.2 w k⟩
    intro g u' hu'
    show φ (g * u' * rowIsometryInclAt₀ K w k) = φ (g * rowIsometryInclAt₀ K w k)
    have hcomm : u' * rowIsometryInclAt₀ K w k = rowIsometryInclAt₀ K w k * u' := by
      rw [rowIsometryInclAt₀_apply]
      refine KUNIFAdelic.gl_ext K ?_ fun v => ?_
      · rw [map_mul, map_mul, KUNIFAdelic.glFin_adelicArchGLInclAt, mul_one, one_mul]
      · rw [map_mul, map_mul, map_mul, map_mul, hU u' hu', map_one, mul_one, one_mul]
    rw [mul_assoc, hcomm, ← mul_assoc]
    exact hφ.1.2 _ u' hu'
  have hC_fd : ∀ φ ∈ C, ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ),
      FiniteDimensional ℂ W ∧ ∀ k : rowIsometrySubgroup₀ w.Completion,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W := fun φ hφ w =>
    KUNIFCut.exists_finiteDimensional_of_mem_archCutSubmodule K tys hφ.2 w

  obtain ⟨E, hEfd, hEC, hxE, hEstab⟩ := KUNIFCut.exists_fd_stable C hC_stab hC_fd hx
  have := hEfd

  obtain ⟨S, b, hb, hcoord⟩ := EvalCoords.exists_eval_coords E
  let eS : S ≃ Fin S.card := S.equivFin
  let pt : Fin S.card → AdelicGL2 (𝓞 K) K := fun i => ((eS.symm i : S) : AdelicGL2 (𝓞 K) K)
  let ys : Fin S.card → AdelicGL2 (𝓞 K) K → ℂ := fun i => b (pt i)

  have hxcont : Continuous x := hC_cont x hx
  choose B hB0 hB using fun g : AdelicGL2 (𝓞 K) K => KUNIFCut.exists_bound K hxcont g
  refine ⟨S.card, ys, ∑ i, B (pt i), fun i => hEC (hb _), ?_⟩
  intro k hk1 hk2

  obtain ⟨s, ζ, κ', hs, hζ, hfac⟩ := KUNIFAdelic.exists_factor K k hk1 hk2
  set ε := KUNIFAdelic.archIdele K s with hε
  set z := KUNIFAdelic.archIdele K ζ with hz
  set k₁ := KUNIFAdelic.archProd K (fun w => (κ' w : GL (Fin 2) w.Completion)) with hk₁
  have hk₁K : k₁ ∈ adelicMaximalCompact K :=
    KUNIFAdelic.archProd_mem_adelicMaximalCompact K _ fun w => ((mem_rowIsometrySubgroup₀_iff _).mp (κ' w).2).2
  have hk₁E : ∀ φ ∈ E, rightTranslate K k₁ φ ∈ E := by
    refine KUNIFAdelic.archProd_induction K _ (fun h => ∀ φ ∈ E, rightTranslate K h φ ∈ E) ?_ ?_ ?_
    · intro φ hφ
      have : rightTranslate K 1 φ = φ := by funext y; simp [rightTranslate]
      rw [this]; exact hφ
    · intro a a' ha ha' φ hφ
      rw [← rightTranslate_rightTranslate]
      exact ha _ (ha' φ hφ)
    · intro w φ hφ
      exact hEstab w (κ' w) φ hφ

  have hξz : ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1 := by
    rw [hξ, KUNIFAdelic.ideleNorm_archIdele_eq_one K ζ hζ, Real.one_rpow]

  let cs : Fin S.card → ℂ := fun i => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (pt i * k₁)
  refine ⟨cs, ε, KUNIFAdelic.archIdele_snd K s, KUNIFAdelic.ideleNorm_archIdele_eq_one K s hs, fun i => ?_, fun g => ?_⟩
  · calc ‖cs i‖ = ‖x (pt i * k₁)‖ := by
          show ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (pt i * k₁)‖ = _
          rw [norm_mul, hξz, one_mul]
      _ ≤ B (pt i) := hB _ k₁ hk₁K
      _ ≤ ∑ j, B (pt j) := Finset.single_le_sum (fun j _ => hB0 _) (Finset.mem_univ i)
  ·
    have hcentral : ∀ y, x (centralScalar (𝓞 K) K z * y) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x y :=
      fun y => KUNIFCut.central_of_mem_cuspKFiniteSubmodule K (hV.1.le hx.1.1) ⟨z, Subgroup.mem_top z⟩ y
    have hpt : ∀ y, x (y * k) = ∑ i, cs i * ys i (y * diagOne ε) := by
      intro y
      have e1 : x (y * k) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (y * diagOne ε * k₁) := by
        rw [hfac, ← mul_assoc, ← mul_assoc, KUNIFAdelic.mul_centralScalar_comm, hcentral]
      have e2 : x (y * diagOne ε * k₁) = ∑ g' ∈ S, x (g' * k₁) * b g' (y * diagOne ε) := by
        have h := congrFun (hcoord _ (hk₁E x hxE)) (y * diagOne ε)
        simpa only [rightTranslate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
      rw [e1, e2, Finset.mul_sum, ← Finset.sum_coe_sort S, ← eS.symm.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [cs, ys, pt]
      ring

    have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
      (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
    have hcontys : ∀ i, Continuous (rightTranslate K (diagOne ε) (ys i)) := fun i =>
      continuous_rightTranslate K (hC_cont _ (hEC (hb _))) _
    have hfun : rightTranslate K k x = fun y => ∑ i, cs i * rightTranslate K (diagOne ε) (ys i) y := by
      funext y
      exact hpt y
    rw [KUNIFCut.whittakerCoefficient_mul, hfun]
    have hW := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (NumberField.StandardAddChar.stdAddChar K) hψ S.card (fun i => rightTranslate K (diagOne ε) (ys i)) hcontys cs 1 g
    rw [hW]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [KUNIFCut.whittakerCoefficient_mul]

theorem CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ (m : ℕ) (ys : Fin m → (AdelicGL2 (𝓞 K) K → ℂ)) (M : ℝ),
      (∀ i, ys i ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) ∧
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∃ (cs : Fin m → ℂ) (ε : (AdeleRing (𝓞 K) K)ˣ),
          ((ε : AdeleRing (𝓞 K) K)).2 = 1 ∧ (∀ w : InfinitePlace K, ‖((ε : AdeleRing (𝓞 K) K)).1 w‖ = 1) ∧
          NumberField.TateGlobal.ideleNorm K ε = 1 ∧
          (∀ i, ‖cs i‖ ≤ M) ∧
          ∀ g : AdelicGL2 (𝓞 K) K,
            whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (g * k) =
              ∑ i, cs i * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (ys i) 1
              (g * diagOne ε)
    := by
  classical
  have _ := hc
  have _ := hd₁
  have _ := hd
  have _ := hcov
  have _ := hN
  set C : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys with hC

  have hC_cont : ∀ φ ∈ C, Continuous φ := fun φ hφ =>
    KUNIFCut.continuous_of_mem_cuspKFiniteSubmodule K (hV.1.le hφ.1.1)
  have hU : ∀ u' ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, AdelicLevel.glArch (𝓞 K) K u' = 1 :=
    fun u' hu' => hu'.2
  have hC_stab : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ C := by
    intro w k φ hφ
    refine ⟨⟨hV.1.rightTranslate_arch_mem w k φ hφ.1.1, ?_⟩,
      rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule K tys hφ.2 w k⟩
    intro g u' hu'
    show φ (g * u' * rowIsometryInclAt₀ K w k) = φ (g * rowIsometryInclAt₀ K w k)
    have hcomm : u' * rowIsometryInclAt₀ K w k = rowIsometryInclAt₀ K w k * u' := by
      rw [rowIsometryInclAt₀_apply]
      refine KUNIFAdelic.gl_ext K ?_ fun v => ?_
      · rw [map_mul, map_mul, KUNIFAdelic.glFin_adelicArchGLInclAt, mul_one, one_mul]
      · rw [map_mul, map_mul, map_mul, map_mul, hU u' hu', map_one, mul_one, one_mul]
    rw [mul_assoc, hcomm, ← mul_assoc]
    exact hφ.1.2 _ u' hu'
  have hC_fd : ∀ φ ∈ C, ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ),
      FiniteDimensional ℂ W ∧ ∀ k : rowIsometrySubgroup₀ w.Completion,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W := fun φ hφ w =>
    KUNIFCut.exists_finiteDimensional_of_mem_archCutSubmodule K tys hφ.2 w

  obtain ⟨E, hEfd, hEC, hxE, hEstab⟩ := KUNIFCut.exists_fd_stable C hC_stab hC_fd hx
  have := hEfd

  obtain ⟨S, b, hb, hcoord⟩ := EvalCoords.exists_eval_coords E
  let eS : S ≃ Fin S.card := S.equivFin
  let pt : Fin S.card → AdelicGL2 (𝓞 K) K := fun i => ((eS.symm i : S) : AdelicGL2 (𝓞 K) K)
  let ys : Fin S.card → AdelicGL2 (𝓞 K) K → ℂ := fun i => b (pt i)

  have hxcont : Continuous x := hC_cont x hx
  choose B hB0 hB using fun g : AdelicGL2 (𝓞 K) K => KUNIFCut.exists_bound K hxcont g
  refine ⟨S.card, ys, ∑ i, B (pt i), fun i => hEC (hb _), ?_⟩
  intro k hk1 hk2

  obtain ⟨s, ζ, κ', hs, hζ, hfac⟩ := KUNIFAdelic.exists_factor K k hk1 hk2
  set ε := KUNIFAdelic.archIdele K s with hε
  set z := KUNIFAdelic.archIdele K ζ with hz
  set k₁ := KUNIFAdelic.archProd K (fun w => (κ' w : GL (Fin 2) w.Completion)) with hk₁
  have hk₁K : k₁ ∈ adelicMaximalCompact K :=
    KUNIFAdelic.archProd_mem_adelicMaximalCompact K _ fun w => ((mem_rowIsometrySubgroup₀_iff _).mp (κ' w).2).2
  have hk₁E : ∀ φ ∈ E, rightTranslate K k₁ φ ∈ E := by
    refine KUNIFAdelic.archProd_induction K _ (fun h => ∀ φ ∈ E, rightTranslate K h φ ∈ E) ?_ ?_ ?_
    · intro φ hφ
      have : rightTranslate K 1 φ = φ := by funext y; simp [rightTranslate]
      rw [this]; exact hφ
    · intro a a' ha ha' φ hφ
      rw [← rightTranslate_rightTranslate]
      exact ha _ (ha' φ hφ)
    · intro w φ hφ
      exact hEstab w (κ' w) φ hφ

  have hξz : ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1 := by
    rw [hξ, KUNIFAdelic.ideleNorm_archIdele_eq_one K ζ hζ, Real.one_rpow]

  let cs : Fin S.card → ℂ := fun i => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (pt i * k₁)
  refine ⟨cs, ε, KUNIFAdelic.archIdele_snd K s, fun w => hs w, KUNIFAdelic.ideleNorm_archIdele_eq_one K s hs,
    fun i => ?_, fun g => ?_⟩
  · calc ‖cs i‖ = ‖x (pt i * k₁)‖ := by
          show ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (pt i * k₁)‖ = _
          rw [norm_mul, hξz, one_mul]
      _ ≤ B (pt i) := hB _ k₁ hk₁K
      _ ≤ ∑ j, B (pt j) := Finset.single_le_sum (fun j _ => hB0 _) (Finset.mem_univ i)
  ·
    have hcentral : ∀ y, x (centralScalar (𝓞 K) K z * y) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x y :=
      fun y => KUNIFCut.central_of_mem_cuspKFiniteSubmodule K (hV.1.le hx.1.1) ⟨z, Subgroup.mem_top z⟩ y
    have hpt : ∀ y, x (y * k) = ∑ i, cs i * ys i (y * diagOne ε) := by
      intro y
      have e1 : x (y * k) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (y * diagOne ε * k₁) := by
        rw [hfac, ← mul_assoc, ← mul_assoc, KUNIFAdelic.mul_centralScalar_comm, hcentral]
      have e2 : x (y * diagOne ε * k₁) = ∑ g' ∈ S, x (g' * k₁) * b g' (y * diagOne ε) := by
        have h := congrFun (hcoord _ (hk₁E x hxE)) (y * diagOne ε)
        simpa only [rightTranslate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
      rw [e1, e2, Finset.mul_sum, ← Finset.sum_coe_sort S, ← eS.symm.sum_comp]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [cs, ys, pt]
      ring

    have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
      (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
    have hcontys : ∀ i, Continuous (rightTranslate K (diagOne ε) (ys i)) := fun i =>
      continuous_rightTranslate K (hC_cont _ (hEC (hb _))) _
    have hfun : rightTranslate K k x = fun y => ∑ i, cs i * rightTranslate K (diagOne ε) (ys i) y := by
      funext y
      exact hpt y
    rw [KUNIFCut.whittakerCoefficient_mul, hfun]
    have hW := AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
      (NumberField.StandardAddChar.stdAddChar K) hψ S.card (fun i => rightTranslate K (diagOne ε) (ys i)) hcontys cs 1 g
    rw [hW]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [KUNIFCut.whittakerCoefficient_mul]

end AutomorphicForm
