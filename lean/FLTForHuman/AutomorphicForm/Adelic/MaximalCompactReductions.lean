/-
  Two reductions to the maximal compact.

  * `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` — a Whittaker function that
    is a `ψ`-eigenfunction and `ω`-equivariant under the centre, non-zero at a point `g₀` that is trivial
    off a finite set `S`, does not vanish at `diagOne t * k` for some idele `t` (also trivial off `S`) and
    some `k ∈ maximalCompactAt F S`. The `diagOne` reduction moves the diagonal part into the idele
    variable and leaves the compact factor to be killed.
  * `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2` — the points
    of `GL₂(𝔸)` that are `b * k` with `k` integral and of bounded archimedean height form a compact set,
    which is the Siegel-set compactness the centre-cut estimates quantify over.

  Both use the same three ingredients: the Borel decomposition, the one-place factors of the adelic
  maximal compact, and the algebra of the adelic height.

  Transcribed from two pin `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero.lean`
  * `P2M/Sol/S_AutomorphicForm_exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2.lean`

  The pin's file-level labels (`NondegKit`, `B3Translate`) become the subject namespaces below.

  **Visibility follows the pin's**: row 1 has a six-declaration `private` prelude and one public
  headline; row 2 is a flat public surface of thirteen declarations.

  **Wiring.** `spec/check_port.py` owns every public declaration here: the two wrappers and the two `S_`
  files are the wire.
  spec-pin: Theorems/Thm_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Set
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Topology
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry
import FLTForHuman.AutomorphicForm.Adelic.AdelicIwasawa
import FLTForHuman.NumberTheory.AdelicHeight
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.InfinitePlace NumberField.AdelicLevel NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel AdelicDock
open scoped NNReal

namespace AutomorphicForm

namespace LocalIntertwining

namespace DiagOneReduction

section LocalEmbeddingKit

variable {F : Type} [Field F] [NumberField F]

private theorem exists_truncation (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ adelicMaximalCompact F)
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ m : AdelicGL2 (𝓞 F) F, m ∈ adelicMaximalCompact F ∧ glArch (𝓞 F) F m = 1 ∧
      (∀ v ∈ T, finComponent (𝓞 F) F v (glFin (𝓞 F) F m) = finComponent (𝓞 F) F v (glFin (𝓞 F) F k)) ∧
      (∀ v ∉ T, finComponent (𝓞 F) F v (glFin (𝓞 F) F m) = 1) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, map_one _, fun v hv => absurd hv (Finset.notMem_empty v),
      fun v _ => by rw [map_one, map_one]⟩
  | insert u T hu ih =>
    obtain ⟨m, hmK, hma, hmon, hmoff⟩ := ih
    refine ⟨m * atPlace u (finComponent (𝓞 F) F u (glFin (𝓞 F) F k)), mul_mem hmK (atPlace_mem u hk), ?_, ?_, ?_⟩
    · rw [map_mul, hma, glArch_atPlace, one_mul]
    · intro v hv
      rw [map_mul, map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hvT
      · rw [hmoff v hu, finComponent_atPlace_self, one_mul]
      · have hvu : v ≠ u := fun h => hu (h ▸ hvT)
        rw [hmon v hvT, finComponent_atPlace_of_ne _ _ hvu, mul_one]
    · intro v hv
      have hvu : v ≠ u := fun h => hv (h ▸ Finset.mem_insert_self u T)
      have hvT : v ∉ T := fun h => hv (Finset.mem_insert_of_mem h)
      rw [map_mul, map_mul, hmoff v hvT, finComponent_atPlace_of_ne _ _ hvu, one_mul]

end LocalEmbeddingKit

theorem _root_.AutomorphicForm.exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (W : AdelicGL2 (𝓞 F) F → ℂ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hN : ∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), W (unipotentGL2 u * g) = ψ u * W g)
    (hZ : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      W (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * W g)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (hW : W g₀ ≠ 0) :
    ∃ (t : (AdeleRing (𝓞 F) F)ˣ) (k : AdelicGL2 (𝓞 F) F),
      k ∈ maximalCompactAt F S ∧
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) ∧
      W (diagOne t * k) ≠ 0 := by
  classical

  obtain ⟨b, k₁, hb, hk1f, hk1a, hg0⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g₀
  have hk1K : k₁ ∈ adelicMaximalCompact F := ⟨hk1f, hk1a⟩

  have hg0v : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → finComponent (𝓞 F) F v (glFin (𝓞 F) F g₀) = 1 := by
    intro v hv
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [finComponent_apply, glFin_apply, hg₀ v hv i j]
    change ((finComponent (𝓞 F) F v (glFin (𝓞 F) F 1) : GL (Fin 2) (v.adicCompletion F)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j = _
    rw [map_one, map_one]

  obtain ⟨m, hmK, hma, hmon, hmoff⟩ := exists_truncation k₁ hk1K S
  set kf : AdelicGL2 (𝓞 F) F := finEmbed (𝓞 F) F (glFin (𝓞 F) F k₁) with hkf
  have hkfK : kf ∈ adelicMaximalCompact F :=
    ⟨by rw [hkf, glFin_finEmbed]; exact hk1f,
     fun w => by rw [hkf, glArch_finEmbed, map_one]; exact isRowIsometry_one⟩
  set k : AdelicGL2 (𝓞 F) F := k₁ * kf⁻¹ * m with hkdef
  have hkK : k ∈ adelicMaximalCompact F := mul_mem (mul_mem hk1K (inv_mem hkfK)) hmK
  have hka : glArch (𝓞 F) F k = glArch (𝓞 F) F k₁ := by
    rw [hkdef, map_mul, map_mul, map_inv, hkf, glArch_finEmbed, inv_one, mul_one, hma, mul_one]
  have hkS : ∀ v ∈ S, finComponent (𝓞 F) F v (glFin (𝓞 F) F k) = finComponent (𝓞 F) F v (glFin (𝓞 F) F k₁) := by
    intro v hv
    simp only [hkdef, map_mul, map_inv, hkf, glFin_finEmbed, mul_inv_cancel, one_mul]
    exact hmon v hv
  have hkoff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → finComponent (𝓞 F) F v (glFin (𝓞 F) F k) = 1 := by
    intro v hv
    simp only [hkdef, map_mul, map_inv, hkf, glFin_finEmbed, mul_inv_cancel, one_mul]
    exact hmoff v hv
  have hkmem : k ∈ maximalCompactAt F S := mem_maximalCompactAt_iff.2 ⟨hkK, hkoff⟩

  set b' : AdelicGL2 (𝓞 F) F := g₀ * k⁻¹ with hb'def
  have hb'S : ∀ v ∈ S, finComponent (𝓞 F) F v (glFin (𝓞 F) F b') = finComponent (𝓞 F) F v (glFin (𝓞 F) F b) := by
    intro v hv
    rw [hb'def, map_mul, map_mul, map_inv, map_inv, hkS v hv, hg0, map_mul, map_mul, mul_inv_cancel_right]
  have hb'off : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → finComponent (𝓞 F) F v (glFin (𝓞 F) F b') = 1 := by
    intro v hv
    rw [hb'def, map_mul, map_mul, map_inv, map_inv, hkoff v hv, hg0v v hv, inv_one, mul_one]
  have hb'a : glArch (𝓞 F) F b' = glArch (𝓞 F) F b := by
    rw [hb'def, map_mul, map_inv, hka, hg0, map_mul, mul_inv_cancel_right]
  have hb10 : ((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := hb
  have hb' : b' ∈ adelicBorel (𝓞 F) F := by
    show ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
    apply Prod.ext
    · change ((glArch (𝓞 F) F b' : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0
      rw [hb'a]
      change (((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).1 = 0
      rw [hb10]
      rfl
    · apply Subtype.ext
      funext v
      change ((finComponent (𝓞 F) F v (glFin (𝓞 F) F b') : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0
      by_cases hv : v ∈ S
      · rw [hb'S v hv]
        change (((b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 v = 0
        rw [hb10]
        rfl
      · rw [hb'off v hv, Units.val_one, Matrix.one_apply_ne (by decide)]

  set Bel : ↥(adelicBorel (𝓞 F) F) := ⟨b', hb'⟩ with hBel
  set t₁ : (AdeleRing (𝓞 F) F)ˣ := borelDiagFst Bel with ht₁
  set t₂ : (AdeleRing (𝓞 F) F)ˣ := borelDiagSnd Bel with ht₂
  set β : AdeleRing (𝓞 F) F :=
    ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    with hβ
  have h00 : ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = (t₁ : AdeleRing (𝓞 F) F) := rfl
  have h11 : ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = (t₂ : AdeleRing (𝓞 F) F) := rfl
  have hb'10 : ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := hb'
  have ht2inv : ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * (t₂ : AdeleRing (𝓞 F) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hcs : ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₂ : AdeleRing (𝓞 F) F), 0; 0, (t₂ : AdeleRing (𝓞 F) F)] := by
    change Matrix.scalar (Fin 2) (t₂ : AdeleRing (𝓞 F) F) = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hdo : ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₁ : AdeleRing (𝓞 F) F) * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 0; 0, 1] := by
    change Matrix.diagonal ![((t₁ * t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1] = _
    rw [Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hx00 : (t₂ : AdeleRing (𝓞 F) F) * ((t₁ : AdeleRing (𝓞 F) F) * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
      = (t₁ : AdeleRing (𝓞 F) F) := by
    rw [mul_left_comm, Units.mul_inv, mul_one]
  have hβ01 : β * (t₂ : AdeleRing (𝓞 F) F)
      = ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 := by
    rw [hβ, mul_assoc, ht2inv, mul_one]
  have hR : ((unipotentGL2 β : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![(t₁ : AdeleRing (𝓞 F) F), β * (t₂ : AdeleRing (𝓞 F) F); 0, (t₂ : AdeleRing (𝓞 F) F)] := by
    rw [hcs, hdo, unipotentGL2_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hx00]
  have hdecomp : b' = unipotentGL2 β * centralScalar (𝓞 F) F t₂ * diagOne (t₁ * t₂⁻¹) := by
    apply Units.ext
    change ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = ((unipotentGL2 β : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((centralScalar (𝓞 F) F t₂ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
        * ((diagOne (t₁ * t₂⁻¹) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
    rw [hR, hβ01]
    conv_lhs => rw [Matrix.eta_fin_two ((b' : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))]
    rw [h00, h11, hb'10]

  have hg0' : g₀ = b' * k := by rw [hb'def, inv_mul_cancel_right]
  have hWval : W g₀ = ψ β * ((((ω t₂ : ℂˣ) : ℂ)) * W (diagOne (t₁ * t₂⁻¹) * k)) := by
    rw [hg0', hdecomp, mul_assoc, mul_assoc, hN, hZ]
  refine ⟨t₁ * t₂⁻¹, k, hkmem, fun v hv => ?_, fun h0 => hW ?_⟩
  ·
    have h1 : ((t₁ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
      change ((finComponent (𝓞 F) F v (glFin (𝓞 F) F b') : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 0 0 = 1
      rw [hb'off v hv, Units.val_one, Matrix.one_apply_eq]
    have h2 : ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
      change ((finComponent (𝓞 F) F v (glFin (𝓞 F) F (b'⁻¹)) : GL (Fin 2) (v.adicCompletion F)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 1
      rw [map_inv, map_inv, hb'off v hv, inv_one, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul]
    change ((t₁ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v * ((t₂⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1
    rw [h1, h2, mul_one]
  · rw [hWval, h0, mul_zero, mul_zero]

end DiagOneReduction

namespace BorelHeightCompact

variable (F : Type) [Field F] [NumberField F]

local notation "G" => AdelicGL2 (𝓞 F) F
local notation "𝔸" => AdeleRing (𝓞 F) F

theorem continuous_entry (i j : Fin 2) : Continuous fun g : G => ((g : G) : Matrix (Fin 2) (Fin 2) 𝔸) i j :=
  (Units.continuous_val.matrix_elem i j)

theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 F) F : Set G) := by
  have : (adelicBorel (𝓞 F) F : Set G) = (fun g : G => ((g : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 0) ⁻¹' {0} := by
    ext g; rfl
  rw [this]
  exact isClosed_singleton.preimage (continuous_entry F 1 0)

noncomputable def hgt (b : ↥(adelicBorel (𝓞 F) F)) : ℝ :=
  NumberField.TateGlobal.ideleNorm F (borelDiagFst b) / NumberField.TateGlobal.ideleNorm F (borelDiagSnd b)

theorem hgt_mul (b c : ↥(adelicBorel (𝓞 F) F)) : hgt F (b * c) = hgt F b * hgt F c := by
  simp only [hgt, map_mul, NumberField.TateGlobal.ideleNorm_mul]
  rw [mul_div_mul_comm]

theorem hgt_pos (b : ↥(adelicBorel (𝓞 F) F)) : 0 < hgt F b :=
  div_pos (NumberField.TateGlobal.ideleNorm_pos _) (NumberField.TateGlobal.ideleNorm_pos _)

theorem continuous_borelDiagFst : Continuous (borelDiagFst : ↥(adelicBorel (𝓞 F) F) → 𝔸ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_entry F 0 0).comp continuous_subtype_val
  · have : (fun b : ↥(adelicBorel (𝓞 F) F) => ((borelDiagFst b)⁻¹ : 𝔸ˣ).val)
        = fun b => ((b⁻¹ : ↥(adelicBorel (𝓞 F) F)) : G).val 0 0 := by
      funext b; rw [← map_inv]; rfl
    rw [this]
    exact (continuous_entry F 0 0).comp (continuous_subtype_val.comp continuous_inv)

theorem continuous_borelDiagSnd : Continuous (borelDiagSnd : ↥(adelicBorel (𝓞 F) F) → 𝔸ˣ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_entry F 1 1).comp continuous_subtype_val
  · have : (fun b : ↥(adelicBorel (𝓞 F) F) => ((borelDiagSnd b)⁻¹ : 𝔸ˣ).val)
        = fun b => ((b⁻¹ : ↥(adelicBorel (𝓞 F) F)) : G).val 1 1 := by
      funext b; rw [← map_inv]; rfl
    rw [this]
    exact (continuous_entry F 1 1).comp (continuous_subtype_val.comp continuous_inv)

theorem continuous_hgt : Continuous (hgt F) :=
  ((NumberField.TateGlobal.continuous_ideleNorm F).comp (continuous_borelDiagFst F)).div
    ((NumberField.TateGlobal.continuous_ideleNorm F).comp (continuous_borelDiagSnd F))
    fun _ => (NumberField.TateGlobal.ideleNorm_pos _).ne'

theorem norm_snd_eq_one_of_integral (x : 𝔸ˣ)
    (h1 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (x : 𝔸).2 v ∈ v.adicCompletionIntegers F)
    (h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ((x⁻¹ : 𝔸ˣ) : 𝔸).2 v ∈ v.adicCompletionIntegers F)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ‖(x : 𝔸).2 v‖ = 1 := by
  have ha : ‖(x : 𝔸).2 v‖ ≤ 1 := NumberField.AdelicHeight.norm_le_one_of_mem_adicCompletionIntegers (h1 v)
  have hb : ‖((x⁻¹ : 𝔸ˣ) : 𝔸).2 v‖ ≤ 1 := NumberField.AdelicHeight.norm_le_one_of_mem_adicCompletionIntegers (h2 v)
  have hprod : ‖(x : 𝔸).2 v‖ * ‖((x⁻¹ : 𝔸ˣ) : 𝔸).2 v‖ = 1 := by
    rw [← norm_mul]
    have := congrArg (fun y : 𝔸 => y.2 v) x.mul_inv
    change ((x : 𝔸).2 * ((x⁻¹ : 𝔸ˣ) : 𝔸).2) v = (1 : 𝔸).2 v at this
    rw [show ((x : 𝔸).2 * ((x⁻¹ : 𝔸ˣ) : 𝔸).2) v = (x : 𝔸).2 v * ((x⁻¹ : 𝔸ˣ) : 𝔸).2 v from rfl] at this
    rw [this]
    exact norm_one
  refine le_antisymm ha ?_
  calc (1 : ℝ) = ‖(x : 𝔸).2 v‖ * ‖((x⁻¹ : 𝔸ˣ) : 𝔸).2 v‖ := hprod.symm
    _ ≤ ‖(x : 𝔸).2 v‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := mul_one _

theorem ideleNorm_eq_prod_of_integral (x : 𝔸ˣ)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ‖(x : 𝔸).2 v‖ = 1) :
    NumberField.TateGlobal.ideleNorm F x = ∏ w : InfinitePlace F, ‖(x : 𝔸).1 w‖ ^ w.mult := by
  show ((distribHaarChar 𝔸 x : ℝ≥0) : ℝ) = _
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm,
    finprod_eq_one_of_forall_eq_one h, mul_one]

theorem archComponent_glArch_apply (w : InfinitePlace F) (g : G) (i j : Fin 2) :
    ((archComponent F w (glArch (𝓞 F) F g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = (((g : G) : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w := by
  rw [archComponent_apply, glArch_apply]

theorem localHeight_archComponent_borel (w : InfinitePlace F) (b : ↥(adelicBorel (𝓞 F) F)) :
    localHeight (archComponent F w (glArch (𝓞 F) F (b : G)))
      = ‖(((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).1 w‖ / ‖(((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w‖ := by
  set M := ((archComponent F w (glArch (𝓞 F) F (b : G)) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)
    with hM
  have h10 : M 1 0 = 0 := by
    rw [hM, archComponent_glArch_apply, borel_entry_one_zero]; rfl
  have h00 : M 0 0 = (((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 0 0).1 w := by rw [hM, archComponent_glArch_apply]
  have h11 : M 1 1 = (((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w := by rw [hM, archComponent_glArch_apply]

  have hne : M 1 1 ≠ 0 := by
    rw [h11]
    have hu : IsUnit ((((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w) := by
      have := (borelDiagSnd b).isUnit
      have hmap := this.map ((Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) w).comp
        (RingHom.fst (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))
      exact hmap
    exact hu.ne_zero
  unfold localHeight rowNormSq
  rw [← hM, Matrix.det_fin_two, h10, mul_zero, sub_zero, norm_mul, norm_zero, h00, h11]
  have hpos : 0 < ‖(((b : G) : Matrix (Fin 2) (Fin 2) 𝔸) 1 1).1 w‖ := norm_pos_iff.mpr (by rwa [h11] at hne)
  field_simp
  ring

theorem hgt_eq_archHeight {g b k : G} (hb : b ∈ adelicBorel (𝓞 F) F) (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F)
    (hkf : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F)
    (hka : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) (hgeq : g = b * k) :
    hgt F ⟨b, hb⟩ = archHeight F (glArch (𝓞 F) F g) := by

  have hbf : glFin (𝓞 F) F b ∈ finiteIntegralGL2 (𝓞 F) F := by
    have : b = g * k⁻¹ := by rw [hgeq, mul_inv_cancel_right]
    rw [this, map_mul, map_inv]
    exact (finiteIntegralGL2 (𝓞 F) F).mul_mem hg ((finiteIntegralGL2 (𝓞 F) F).inv_mem hkf)
  obtain ⟨hint, hint'⟩ := mem_finiteIntegralGL2_iff.mp hbf
  set bb : ↥(adelicBorel (𝓞 F) F) := ⟨b, hb⟩ with hbb

  have hfst : ∀ v, ‖((borelDiagFst bb : 𝔸ˣ) : 𝔸).2 v‖ = 1 := by
    refine norm_snd_eq_one_of_integral F _ (fun v => hint 0 0 v) (fun v => ?_)
    rw [← map_inv]
    have := (mem_finiteIntegralGL2_iff.mp ((finiteIntegralGL2 (𝓞 F) F).inv_mem hbf)).1 0 0 v
    rw [← map_inv] at this
    exact this
  have hsnd : ∀ v, ‖((borelDiagSnd bb : 𝔸ˣ) : 𝔸).2 v‖ = 1 := by
    refine norm_snd_eq_one_of_integral F _ (fun v => hint 1 1 v) (fun v => ?_)
    rw [← map_inv]
    have := (mem_finiteIntegralGL2_iff.mp ((finiteIntegralGL2 (𝓞 F) F).inv_mem hbf)).1 1 1 v
    rw [← map_inv] at this
    exact this

  have hH : archHeight F (glArch (𝓞 F) F g) = archHeight F (glArch (𝓞 F) F b) := by
    rw [hgeq, map_mul]
    unfold archHeight
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_mul, localHeight_mul_rowIsometry _ (hka w)]
  rw [hH, hgt, ideleNorm_eq_prod_of_integral F _ hfst, ideleNorm_eq_prod_of_integral F _ hsnd, ← Finset.prod_div_distrib]
  unfold archHeight
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← div_pow]
  congr 1
  exact (localHeight_archComponent_borel F w bb).symm

theorem _root_.AutomorphicForm.exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∀ t : AdelicGL2 (𝓞 F) F,
      ∃ (k₁ k₂ : ℝ) (Ω : Set (AdelicGL2 (𝓞 F) F)), 0 < k₁ ∧ k₁ ≤ k₂ ∧ IsCompact Ω ∧
        ∀ g : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F →
          ∃ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F), ω ∈ Ω ∧
            g * t = (b : AdelicGL2 (𝓞 F) F) * ω ∧
            k₁ * archHeight F (glArch (𝓞 F) F g) ≤ hgt b ∧
            hgt b ≤ k₂ * archHeight F (glArch (𝓞 F) F g) := by
  intro α hgt t
  have hhgt : ∀ b, hgt b = BorelHeightCompact.hgt F b := fun b => rfl
  set K : Subgroup (AdelicGL2 (𝓞 F) F) := adelicMaximalCompact F with hK
  have hKc : IsCompact (K : Set (AdelicGL2 (𝓞 F) F)) := isCompact_adelicMaximalCompact F
  have hmemK : ∀ {k : AdelicGL2 (𝓞 F) F}, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) → k ∈ K :=
    fun h1 h2 => ⟨h1, h2⟩

  set KtK : Set (AdelicGL2 (𝓞 F) F) :=
    (fun p : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => p.1 * t * p.2) '' ((K : Set (AdelicGL2 (𝓞 F) F)) ×ˢ (K : Set (AdelicGL2 (𝓞 F) F)))
    with hKtK
  have hKtKc : IsCompact KtK :=
    (hKc.prod hKc).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  set S : Set ↥(adelicBorel (𝓞 F) F) := Subtype.val ⁻¹' KtK with hS
  have hSc : IsCompact S := (isClosed_adelicBorel F).isClosedEmbedding_subtypeVal.isCompact_preimage hKtKc

  obtain ⟨b₀, k₀, hb₀, hk₀f, hk₀a, ht⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F t
  have hb₀S : (⟨b₀, hb₀⟩ : ↥(adelicBorel (𝓞 F) F)) ∈ S := by
    refine ⟨(1, k₀⁻¹), ⟨K.one_mem, K.inv_mem (hmemK hk₀f hk₀a)⟩, ?_⟩
    show 1 * t * k₀⁻¹ = b₀
    rw [one_mul, ht, mul_inv_cancel_right]

  obtain ⟨bmin, hbminS, hmin⟩ := hSc.exists_isMinOn ⟨_, hb₀S⟩ (continuous_hgt F).continuousOn
  obtain ⟨bmax, hbmaxS, hmax⟩ := hSc.exists_isMaxOn ⟨_, hb₀S⟩ (continuous_hgt F).continuousOn
  refine ⟨BorelHeightCompact.hgt F bmin, BorelHeightCompact.hgt F bmax, K, hgt_pos F bmin, hmin hbmaxS, hKc, fun g hg => ?_⟩

  obtain ⟨bg, kg, hbg, hkgf, hkga, hgeq⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  obtain ⟨b', k', hb', hk'f, hk'a, heq'⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F (kg * t)
  have hb'S : (⟨b', hb'⟩ : ↥(adelicBorel (𝓞 F) F)) ∈ S := by
    refine ⟨(kg, k'⁻¹), ⟨hmemK hkgf hkga, K.inv_mem (hmemK hk'f hk'a)⟩, ?_⟩
    show kg * t * k'⁻¹ = b'
    rw [heq', mul_inv_cancel_right]
  have hH : BorelHeightCompact.hgt F ⟨bg, hbg⟩ = archHeight F (glArch (𝓞 F) F g) := hgt_eq_archHeight F hbg hg hkgf hkga hgeq
  have hHnn : 0 ≤ archHeight F (glArch (𝓞 F) F g) := by rw [← hH]; exact (hgt_pos F _).le
  refine ⟨⟨bg, hbg⟩ * ⟨b', hb'⟩, k', hmemK hk'f hk'a, ?_, ?_, ?_⟩
  · show g * t = bg * b' * k'
    rw [hgeq, mul_assoc, heq', mul_assoc]
  · rw [hhgt, hgt_mul, hH, mul_comm]
    exact mul_le_mul_of_nonneg_left (hmin hb'S) hHnn
  · rw [hhgt, hgt_mul, hH, mul_comm (BorelHeightCompact.hgt F bmax)]
    exact mul_le_mul_of_nonneg_left (hmax hb'S) hHnn

end BorelHeightCompact

end LocalIntertwining

end AutomorphicForm
