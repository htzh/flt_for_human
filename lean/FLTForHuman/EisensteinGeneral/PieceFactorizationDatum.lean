/-
  Every Eisenstein section admits a factorization datum on a large enough set of places.

  `exists_forall_nonempty_factorizationDatum` is the headline of the Bruhat-cell
  decomposition of an induced section: for an induced section `Ψ` that is `K`-finite,
  archimedean-`K`-finite, jointly continuous and holomorphic in the spectral variable,
  flat along the finite level, and nontrivial somewhere, there is a finite set `S₀` of
  finite places such that for every `S ⊇ S₀` and every `g` the datum
  `EisensteinGeneral.Piece.FactorizationDatum F ψv nψ χ ϖ Ψ g S` is inhabited — the
  restriction of `Ψ` to the Bruhat cell `w · n(y) · g` is a finite sum of products of one
  holomorphic coefficient, one archimedean factor per real/complex place and one
  finite-adelic factor that is the integer ring's indicator outside `S`.

  The pin is one public statement over a 25-declaration private engine (`EgenPiece`: the
  explicit Weyl/unipotent matrix identities, the Bruhat cell parametrization, and the
  construction of the datum's fields), so this module is the engine and the headline.

  Transcribed from `P2M/Sol/S_EisensteinGeneral_Piece_exists_forall_nonempty_factorizationDatum.lean`
  (pinned `aa2d8b3`, 890 lines), the pin's `EgenPiece` label namespace dropped — no tokens
  in names.

  **The pin's two `attribute` walls are dropped** (pin `:11-12`). They name the pin's own
  re-declarations of instances (`instCountableOfNumberField_definitions`, the adic-completion
  instances, the `HeckePair`/`FixedPoints` instances) and of simp lemmas (`LocalGL2.coe_*`,
  `FixedPoints.coe_*`, the `AdeleRing.val_*` component lemmas) that this port carries once
  under its own names; restating the wall is not a transcription. This follows the port's
  recorded practice (`AlgebraicCurve/ResidueTheorem/TraceSum.lean` and
  `AlgebraicCurve/Differential/CorrespondenceRegular.lean`, both of which drop the same
  kind of wall with the same reason). The engine below is transcribed against the port's
  simp set as it stands; no file-scope `attribute [-simp]` is needed.

  **Four private helpers of the pin are dropped, not renamed** — the pin never uses them
  (`dt_continuous_rightTranslate` `:210`, `dt_flat_rightTranslate` `:215`,
  `dt_ne_zero_rightTranslate` `:237`, `dt_ofReal_rpow_cpow` `:288`); their content is
  inlined in the pin's own `exists_sum_factorization_weyl_unipotent_mul_of_flat`, so
  nothing is lost. The remaining 21 pin helpers are all transcribed.

  **Local departures from the pin's text** (all forced by `v4.34`/the port, none semantic):

  * `import Mathlib.Topology.Homotopy.Lifting` is added (the pin imports it at `:11`): the
    `ℝ>0`-character lemma needs `IsCoveringMap.existsUnique_continuousMap_lifts`, which no
    module of this one's import closure provides.
  * the pin's `attribute [local instance] NumberField.AdelicHaar.adeleBorel /
    borelSpace_adeleBorel` (`:26`) is not carried — the engine states no measurability
    property, so the local instances have no consumer here.
  * the pin's per-declaration `open scoped Classical in` (`:156`, `:268`, `:276`, `:285`,
    `:301`, `:340`, `:362`, `:549-550`) are replaced by one file-scope `open scoped
    Classical`; the statements do not depend on which of the two forms is used, and the
    products over `{w // w.IsReal}` need the scope in every statement of the engine.
  * `classical` inside two proofs — `isArchKFinite_rightTranslate` (`Finset.image` needs a
    `DecidableEq` for a function type) and `continuous_archUnitHom` (`Function.update` needs
    `DecidableEq (InfinitePlace F)`); neither is available as a global instance here.
  * deprecated names updated, one for one: `dif_pos ↦ dite_eq_left`, `dif_neg ↦
    dite_eq_right`, `if_pos ↦ ite_eq_left`, `if_neg ↦ ite_eq_right`, `Set.mem_setOf_eq ↦
    Set.mem_ofPred_eq`, `continuousOn_iff_continuous_restrict ↦
    continuousOn_iff_continuous_domRestrict`.

  spec-pin: P2M/Sol/S_EisensteinGeneral_Piece_exists_forall_nonempty_factorizationDatum.lean
-/
import FLTForHuman.EisensteinGeneral.FactorizationDatum
import FLTForHuman.AutomorphicForm.Adelic.BigCellExpansion
import FLTForHuman.AutomorphicForm.Adelic.AdelicIwasawa
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

-- Heartbeat probe (recorded, **not installed**): playbook §3.5 says no module carries a
-- `set_option maxHeartbeats` — an in-file cap is a defect marker, not a budget, and `lake build`
-- runs at the project cap anyway. The measurement is kept for the next reader: this module's
-- per-declaration proof cost at this spelling is below 25 000 heartbeats (probe: the file is silent
-- at `-DmaxHeartbeats=25000` and aborts at 12 500), i.e. ≈8× under the edit loop's 200 000.

noncomputable section

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped NNReal
open scoped Classical

namespace EisensteinGeneral.Piece

open NumberField.InfinitePlace NumberField.AdelicLevel AutomorphicForm.WindowedSiegel

/-! ### The Weyl/unipotent matrix identities -/

private theorem weyl_mul_unipotent_mul_eq_of_matrix_form {A : Type*} [CommRing A] (w b : GL (Fin 2) A)
    (hw : (w : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) (p r : Aˣ) (q : A)
    (hbm : (b : Matrix (Fin 2) (Fin 2) A) = !![(p : A), q; 0, (r : A)]) (y : A) :
    ∃ T : GL (Fin 2) A, (T : Matrix (Fin 2) (Fin 2) A) = !![(r : A), 0; 0, (p : A)] ∧
      w * unipotentGL2 y * b
        = T * (w * unipotentGL2 ((r * p⁻¹) • (y + q * ((r⁻¹ : Aˣ) : A)))) := by
  refine ⟨⟨!![(r : A), 0; 0, (p : A)], !![((r⁻¹ : Aˣ) : A), 0; 0, ((p⁻¹ : Aˣ) : A)], ?_, ?_⟩, rfl, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have hp : (p : A) * ((p⁻¹ : Aˣ) : A) = 1 := Units.mul_inv p
    have hr : (r : A) * ((r⁻¹ : Aˣ) : A) = 1 := Units.mul_inv r
    have hL : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) A) * !![1, y; 0, 1] * !![(p : A), q; 0, (r : A)]
        = !![0, (r : A); (p : A), q + y * r] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hR : (!![(r : A), 0; 0, (p : A)] : Matrix (Fin 2) (Fin 2) A)
          * (!![0, 1; 1, 0] * !![1, (r * p⁻¹) • (y + q * ((r⁻¹ : Aˣ) : A)); 0, 1])
        = !![0, (r : A); (p : A), q + y * r] := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
      · simp [Matrix.mul_apply, Fin.sum_univ_two]
      · simp [Matrix.mul_apply, Fin.sum_univ_two, Units.smul_def]
        linear_combination ((r : A) * y + (r : A) * ((r⁻¹ : Aˣ) : A) * q) * hp + q * hr
    apply Units.ext
    simp only [Units.val_mul, hw, hbm, unipotentGL2_coe]
    rw [hL]
    exact hR.symm

private theorem adelicWeyl_inv (F : Type) [Field F] [NumberField F] :
    (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  unfold adelicWeyl
  rw [← map_inv, gl2Weyl_inv]

private theorem adelicWeyl_coe (F : Type) [Field F] [NumberField F] :
    ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adelicWeyl, globalPoints]

private theorem exists_borel_mul_weyl_mul_unipotentGL2_eq (F : Type) [Field F] [NumberField F]
    (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (y : AdeleRing (𝓞 F) F) :
    ∃ (T : AdelicGL2 (𝓞 F) F) (hT : T ∈ adelicBorel (𝓞 F) F),
      borelDiagFst (⟨T, hT⟩ : ↥(adelicBorel (𝓞 F) F)) = borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) ∧
      borelDiagSnd (⟨T, hT⟩ : ↥(adelicBorel (𝓞 F) F)) = borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) ∧
      adelicWeyl (𝓞 F) F * unipotentGL2 y * b
        = T * (adelicWeyl (𝓞 F) F * unipotentGL2
            ((borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))
                * (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹)
              • (y + (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1
                  * (((borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
                      : AdeleRing (𝓞 F) F)))) := by
  have hb10 : (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0 := hb
  have hbm : (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = !![((borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F),
            (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1;
          0, ((borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb10]
  obtain ⟨T, hTm, hrel⟩ := weyl_mul_unipotent_mul_eq_of_matrix_form (adelicWeyl (𝓞 F) F) b (adelicWeyl_coe F)
    (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))
    ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1) hbm y
  have hT : T ∈ adelicBorel (𝓞 F) F := by
    show (T : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0
    rw [hTm]
    simp
  refine ⟨T, hT, ?_, ?_, hrel⟩
  · apply Units.ext
    rw [borelDiagFst_apply_val]
    show (T : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = _
    rw [hTm]
    simp
  · apply Units.ext
    rw [borelDiagSnd_apply_val]
    show (T : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = _
    rw [hTm]
    simp

/-! ### Extensionality of adelic `GL₂` and right translation -/

private theorem adelicGL2_ext (F : Type) [Field F] [NumberField F] {X Y : AdelicGL2 (𝓞 F) F}
    (harch : glArch (𝓞 F) F X = glArch (𝓞 F) F Y)
    (hfin : glFin (𝓞 F) F X = glFin (𝓞 F) F Y) : X = Y := by
  apply Units.ext
  ext i j
  have h1 : ((glArch (𝓞 F) F X : GL (Fin 2) (InfiniteAdeleRing F))
        : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
      = ((glArch (𝓞 F) F Y : GL (Fin 2) (InfiniteAdeleRing F))
        : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j := by rw [harch]
  have h2 : ((glFin (𝓞 F) F X : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      = ((glFin (𝓞 F) F Y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
        : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j := by rw [hfin]
  rw [glArch_apply, glArch_apply] at h1
  rw [glFin_apply, glFin_apply] at h2
  exact Prod.ext h1 h2

private theorem archGL2_ext (F : Type) [Field F] [NumberField F] {X Y : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w X = archComponent F w Y) : X = Y := by
  apply Units.ext
  ext i j
  refine funext fun w => ?_
  have h1 : ((archComponent F w X : GL (Fin 2) w.Completion)
        : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = ((archComponent F w Y : GL (Fin 2) w.Completion)
        : Matrix (Fin 2) (Fin 2) w.Completion) i j := by rw [h w]
  rwa [archComponent_apply, archComponent_apply] at h1

private theorem inv_mul_adelicArchGLInclAt_mul (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (k : AdelicGL2 (𝓞 F) F) (ρ : GL (Fin 2) w.Completion) :
    k⁻¹ * adelicArchGLInclAt F w ρ * k
      = adelicArchGLInclAt F w
          ((archComponent F w (glArch (𝓞 F) F k))⁻¹ * ρ
            * archComponent F w (glArch (𝓞 F) F k)) := by
  apply adelicGL2_ext F
  · simp only [adelicArchGLInclAt, MonoidHom.comp_apply, map_mul, map_inv, glArch_adelicArchGLIncl]
    apply archGL2_ext F
    intro v
    by_cases hvw : v = w
    · subst hvw
      simp [archComponent_archGLIncl_self]
    · simp [archComponent_archGLIncl_of_ne F hvw]
  · simp [adelicArchGLInclAt, glFin_adelicArchGLIncl]

private theorem isArchKFinite_rightTranslate (F : Type) [Field F] [NumberField F]
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchKFinite F φ) (k : AdelicGL2 (𝓞 F) F)
    (hk : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) :
    IsArchKFinite F (fun g => φ (g * k)) := by
  classical
  unfold IsArchKFinite IsArchKFiniteAt RightTranslatesSpanFinite at hφ ⊢
  intro w
  obtain ⟨s, hs⟩ := hφ w
  let L : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := LinearMap.funLeft ℂ ℂ (fun g => g * k)
  refine ⟨s.image L, fun k' hk' => ?_⟩
  obtain ⟨ρ, hρ, rfl⟩ := Subgroup.mem_map.mp hk'
  have hconj : k⁻¹ * adelicArchGLInclAt F w ρ * k ∈ archRowIsometrySubgroup F w := by
    rw [inv_mul_adelicArchGLInclAt_mul]
    exact Subgroup.mem_map_of_mem _ (mem_rowIsometrySubgroup_iff.mpr
      (((hk w).inv.mul (mem_rowIsometrySubgroup_iff.mp hρ)).mul (hk w)))
  have hmem := hs _ hconj
  have hL : (fun x => (fun g => φ (g * k)) (x * adelicArchGLInclAt F w ρ))
      = L (fun x => φ (x * (k⁻¹ * adelicArchGLInclAt F w ρ * k))) := by
    funext x
    simp only [L, LinearMap.funLeft_apply]
    congr 1
    group
  rw [hL, Finset.coe_image, ← Submodule.map_span]
  exact Submodule.mem_map_of_mem hmem

private theorem isKfSmooth_rightTranslate (F : Type) [Field F] [NumberField F]
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (k : AdelicGL2 (𝓞 F) F) :
    IsKfSmooth F (fun g => φ (g * k)) := by
  rw [isKfSmooth_iff] at hφ ⊢
  rw [FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer] at hφ ⊢
  have hmem : ∀ u : ↥(finiteAdelicGL2Subgroup F), k⁻¹ * (u : AdelicGL2 (𝓞 F) F) * k ∈ finiteAdelicGL2Subgroup F := by
    intro u
    rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_mul, map_inv,
      (mem_finiteAdelicGL2Subgroup_iff F (u : AdelicGL2 (𝓞 F) F)).mp u.2, mul_one, inv_mul_cancel]
  let c : ↥(finiteAdelicGL2Subgroup F) → ↥(finiteAdelicGL2Subgroup F) := fun u => ⟨_, hmem u⟩
  have hc : Continuous c :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hφ.preimage hc).mem_nhds ?_) ?_)
  · have h1 : c 1 = 1 := Subtype.ext (by simp [c])
    rw [Set.mem_preimage, h1, SetLike.mem_coe]
    exact Subgroup.one_mem _
  · intro u hu
    have hu' : c u • FLT.SmoothVectors.RightTranslationFn.mk φ = FLT.SmoothVectors.RightTranslationFn.mk φ :=
      MulAction.mem_stabilizer_iff.mp hu
    refine MulAction.mem_stabilizer_iff.mpr (FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_)
    have hx := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f (x * k)) hu'
    simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul] at hx ⊢
    show φ (x * (u : AdelicGL2 (𝓞 F) F) * k) = φ (x * k)
    have hxk : x * (u : AdelicGL2 (𝓞 F) F) * k = x * k * (k⁻¹ * (u : AdelicGL2 (𝓞 F) F) * k) := by group
    rw [hxk]
    exact hx


/-! ### Characters of `ℝ>0` are complex powers -/

private theorem exists_forall_eq_cpow_of_continuousOn_of_norm_eq_one {χ : ℝ → ℂ}
    (hcont : ContinuousOn χ (Set.Ioi 0))
    (hmul : ∀ x y : ℝ, 0 < x → 0 < y → χ (x * y) = χ x * χ y)
    (hnorm : ∀ x : ℝ, 0 < x → ‖χ x‖ = 1) :
    ∃ t : ℝ, ∀ x : ℝ, 0 < x → χ x = (x : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hχc : Continuous fun u : ℝ => χ (Real.exp u) :=
    hcont.comp_continuous Real.continuous_exp fun u => Real.exp_pos u
  have h1 : χ 1 = 1 := by
    have hsq : χ 1 * χ 1 = χ 1 := by rw [← hmul 1 1 one_pos one_pos, one_mul]
    have hne : χ 1 ≠ 0 := fun h => by simpa [h] using hnorm 1 one_pos
    exact (mul_eq_left₀ hne).1 hsq
  let f : C(ℝ, Circle) :=
    ⟨fun u => ⟨χ (Real.exp u), mem_sphere_zero_iff_norm.2 (hnorm _ (Real.exp_pos u))⟩, hχc.subtype_mk _⟩
  have hf : ∀ u, ((f u : Circle) : ℂ) = χ (Real.exp u) := fun _ => rfl
  have hf0 : f 0 = 1 := Circle.ext (by rw [hf, Real.exp_zero, h1, Circle.coe_one])
  have hfadd : ∀ u v, f (u + v) = f u * f v := fun u v =>
    Circle.ext (by rw [Circle.coe_mul, hf, hf, hf, Real.exp_add, hmul _ _ (Real.exp_pos u) (Real.exp_pos v)])
  obtain ⟨Fl, ⟨hF0, hFlift⟩, huniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0 0 (by rw [hf0]; exact Circle.exp_zero)
  have hFl : ∀ u, Circle.exp (Fl u) = f u := fun u => congrFun hFlift u

  have hadd : ∀ u v, Fl (u + v) = Fl u + Fl v := by
    intro u v
    let G : C(ℝ, ℝ) := ⟨fun w => Fl (w + v) - Fl v, by fun_prop⟩
    have hG : G = Fl := huniq G ⟨by simp [G], funext fun w => by
      show Circle.exp (Fl (w + v) - Fl v) = f w
      rw [Circle.exp_sub, hFl, hFl, hfadd, mul_div_cancel_right]⟩
    have := congrArg (fun H : C(ℝ, ℝ) => H u) hG
    simp only [G, ContinuousMap.coe_mk] at this
    linarith
  let Fa : ℝ →+ ℝ := { toFun := Fl, map_zero' := hF0, map_add' := hadd }
  have hlin : ∀ u, Fl u = u * Fl 1 := fun u => by
    have := map_real_smul Fa Fl.continuous u 1
    simpa [Fa, smul_eq_mul] using this
  refine ⟨Fl 1, fun x hx => ?_⟩
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  calc χ x = χ (Real.exp (Real.log x)) := by rw [Real.exp_log hx]
    _ = ((f (Real.log x) : Circle) : ℂ) := (hf _).symm
    _ = ((Circle.exp (Fl (Real.log x)) : Circle) : ℂ) := by rw [hFl]
    _ = Complex.exp (((Real.log x * Fl 1 : ℝ) : ℂ) * Complex.I) := by rw [Circle.coe_exp, hlin]
    _ = (x : ℂ) ^ ((Fl 1 : ℂ) * Complex.I) := by
      rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hx.le]
      push_cast
      ring_nf

private theorem continuous_archUnitHom (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    Continuous (NumberField.TateGlobal.archUnitHom (F := F) w) := by
  classical
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous (fun a : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion), (1 : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F))
    exact (continuous_const.update w Units.continuous_val).prodMk continuous_const
  · show Continuous (fun a : (w.Completion)ˣ =>
      ((Function.update (1 : InfiniteAdeleRing F) w ((a⁻¹ : (w.Completion)ˣ) : w.Completion),
          (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F))
    exact (continuous_const.update w (Units.continuous_val.comp continuous_inv)).prodMk continuous_const

private theorem exists_tau_of_forall_eq_char (F : Type) [Field F] [NumberField F]
    (χ₀ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ₀ : IsUnitaryChar (𝓞 F) F χ₀) (hχ₀c : Continuous χ₀)
    (R : ℝ → ℂ) (e : ℝ → (AdeleRing (𝓞 F) F)ˣ) (he : ContinuousOn e (Set.Ioi 0))
    (hmul : ∀ x y : ℝ, 0 < x → 0 < y → e (x * y) = e x * e y)
    (hR : ∀ x : ℝ, 0 < x → R x = ((χ₀ (e x) : ℂˣ) : ℂ)) :
    ∃ τ : ℝ, ∀ x : ℝ, 0 < x → R x = (x : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  refine exists_forall_eq_cpow_of_continuousOn_of_norm_eq_one ?_ ?_ ?_
  · refine ContinuousOn.congr ((Units.continuous_val.comp hχ₀c).comp_continuousOn he) ?_
    intro x hx
    exact hR x hx
  · intro x y hx hy
    rw [hR _ (mul_pos hx hy), hR _ hx, hR _ hy, hmul x y hx hy, map_mul, Units.val_mul]
  · intro x hx
    rw [hR x hx]
    exact hχ₀ _

private theorem exists_tau_real (F : Type) [Field F] [NumberField F]
    (χ₀ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ₀ : IsUnitaryChar (𝓞 F) F χ₀) (hχ₀c : Continuous χ₀)
    (i : {w : InfinitePlace F // w.IsReal}) (R : ℝ → ℂ)
    (hR : ∀ u : (i.1.Completion)ˣ,
      0 < Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion) →
      R (Completion.extensionEmbeddingOfIsReal i.2 (u : i.1.Completion))
        = ((χ₀ (NumberField.TateGlobal.archUnitHom i.1 u) : ℂˣ) : ℂ)) :
    ∃ τ : ℝ, ∀ x : ℝ, 0 < x → R x = (x : ℂ) ^ ((τ : ℂ) * Complex.I) := by

  let sec : ℝ → i.1.Completion := fun x => (Completion.ringEquivRealOfIsReal i.2).symm x
  have hsec : ∀ x : ℝ, Completion.extensionEmbeddingOfIsReal i.2 (sec x) = x := fun x =>
    (Completion.ringEquivRealOfIsReal i.2).apply_symm_apply x
  have hsec_cont : Continuous sec := by
    have heq : sec = fun x => (Completion.isometryEquivRealOfIsReal i.2).symm x := by
      funext x
      apply (Completion.ringEquivRealOfIsReal i.2).injective
      show (Completion.ringEquivRealOfIsReal i.2) ((Completion.ringEquivRealOfIsReal i.2).symm x) = _
      rw [RingEquiv.apply_symm_apply]
      exact ((Completion.isometryEquivRealOfIsReal i.2).apply_symm_apply x).symm
    rw [heq]
    exact (Completion.isometryEquivRealOfIsReal i.2).symm.isometry.continuous
  have hsec_ne : ∀ x : ℝ, 0 < x → sec x ≠ 0 := by
    intro x hx h0
    have := hsec x
    rw [h0, map_zero] at this
    exact hx.ne this
  let ux : ℝ → (i.1.Completion)ˣ := fun x =>
    if hx : 0 < x then Units.mk0 (sec x) (hsec_ne x hx) else 1
  have hux : ∀ x : ℝ, 0 < x → ((ux x : (i.1.Completion)ˣ) : i.1.Completion) = sec x := by
    intro x hx
    simp only [ux, dite_eq_left hx, Units.val_mk0]
  have hux_cont : ContinuousOn ux (Set.Ioi 0) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have : ((↑) : (i.1.Completion)ˣ → i.1.Completion) ∘ (Set.Ioi (0 : ℝ)).domRestrict ux
          = fun x : Set.Ioi (0 : ℝ) => sec x := by
        funext x
        exact hux x x.2
      rw [this]
      exact hsec_cont.comp continuous_subtype_val
    · refine ((hsec_cont.comp continuous_subtype_val : Continuous fun x : Set.Ioi (0 : ℝ) => sec x).inv₀
        fun x => hsec_ne x x.2).congr fun x => ?_
      rw [Units.val_inv_eq_inv_val]
      exact congrArg Inv.inv (hux x x.2).symm
  refine exists_tau_of_forall_eq_char F χ₀ hχ₀ hχ₀c R
    (fun x => NumberField.TateGlobal.archUnitHom i.1 (ux x))
    ((continuous_archUnitHom F i.1).comp_continuousOn hux_cont) ?_ ?_
  · intro x y hx hy
    show NumberField.TateGlobal.archUnitHom i.1 (ux (x * y))
      = NumberField.TateGlobal.archUnitHom i.1 (ux x) * NumberField.TateGlobal.archUnitHom i.1 (ux y)
    rw [← map_mul]
    congr 1
    apply Units.ext
    rw [Units.val_mul, hux _ (mul_pos hx hy), hux _ hx, hux _ hy]
    simp only [sec, map_mul]
  · intro x hx
    have h1 := hR (ux x) (by rw [hux x hx, hsec]; exact hx)
    rw [hux x hx, hsec] at h1
    exact h1

private theorem exists_tau_complex (F : Type) [Field F] [NumberField F]
    (χ₀ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ₀ : IsUnitaryChar (𝓞 F) F χ₀) (hχ₀c : Continuous χ₀)
    (w : {w : InfinitePlace F // w.IsComplex}) (R : ℝ → ℂ)
    (hR : ∀ (u : (w.1.Completion)ˣ) (r : ℝ), 0 < r →
      Completion.extensionEmbedding w.1 (u : w.1.Completion) = (r : ℂ) →
      R r = ((χ₀ (NumberField.TateGlobal.archUnitHom w.1 u) : ℂˣ) : ℂ)) :
    ∃ τ : ℝ, ∀ x : ℝ, 0 < x → R x = (x : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  let sec : ℝ → w.1.Completion := fun x => (Completion.ringEquivComplexOfIsComplex w.2).symm (x : ℂ)
  have hsec : ∀ x : ℝ, Completion.extensionEmbedding w.1 (sec x) = (x : ℂ) := fun x =>
    (Completion.ringEquivComplexOfIsComplex w.2).apply_symm_apply (x : ℂ)
  have hsec_cont : Continuous sec := by
    have heq : sec = fun x : ℝ => (Completion.isometryEquivComplexOfIsComplex w.2).symm (x : ℂ) := by
      funext x
      apply (Completion.ringEquivComplexOfIsComplex w.2).injective
      show (Completion.ringEquivComplexOfIsComplex w.2) ((Completion.ringEquivComplexOfIsComplex w.2).symm (x : ℂ)) = _
      rw [RingEquiv.apply_symm_apply]
      exact ((Completion.isometryEquivComplexOfIsComplex w.2).apply_symm_apply (x : ℂ)).symm
    rw [heq]
    exact (Completion.isometryEquivComplexOfIsComplex w.2).symm.isometry.continuous.comp
      Complex.continuous_ofReal
  have hsec_ne : ∀ x : ℝ, 0 < x → sec x ≠ 0 := by
    intro x hx h0
    have := hsec x
    rw [h0, map_zero] at this
    exact Complex.ofReal_ne_zero.mpr hx.ne' this.symm
  let ux : ℝ → (w.1.Completion)ˣ := fun x =>
    if hx : 0 < x then Units.mk0 (sec x) (hsec_ne x hx) else 1
  have hux : ∀ x : ℝ, 0 < x → ((ux x : (w.1.Completion)ˣ) : w.1.Completion) = sec x := by
    intro x hx
    simp only [ux, dite_eq_left hx, Units.val_mk0]
  have hux_cont : ContinuousOn ux (Set.Ioi 0) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · have : ((↑) : (w.1.Completion)ˣ → w.1.Completion) ∘ (Set.Ioi (0 : ℝ)).domRestrict ux
          = fun x : Set.Ioi (0 : ℝ) => sec x := by
        funext x
        exact hux x x.2
      rw [this]
      exact hsec_cont.comp continuous_subtype_val
    · refine ((hsec_cont.comp continuous_subtype_val : Continuous fun x : Set.Ioi (0 : ℝ) => sec x).inv₀
        fun x => hsec_ne x x.2).congr fun x => ?_
      rw [Units.val_inv_eq_inv_val]
      exact congrArg Inv.inv (hux x x.2).symm
  refine exists_tau_of_forall_eq_char F χ₀ hχ₀ hχ₀c R
    (fun x => NumberField.TateGlobal.archUnitHom w.1 (ux x))
    ((continuous_archUnitHom F w.1).comp_continuousOn hux_cont) ?_ ?_
  · intro x y hx hy
    show NumberField.TateGlobal.archUnitHom w.1 (ux (x * y))
      = NumberField.TateGlobal.archUnitHom w.1 (ux x) * NumberField.TateGlobal.archUnitHom w.1 (ux y)
    rw [← map_mul]
    congr 1
    apply Units.ext
    rw [Units.val_mul, hux _ (mul_pos hx hy), hux _ hx, hux _ hy]
    simp only [sec, Complex.ofReal_mul, map_mul]
  · intro x hx
    exact hR (ux x) x hx (by rw [hux x hx, hsec])

private theorem real_factor_eq (R : ℝ → ℂ) (t : ℝ)
    (hR : ∀ r : ℝ, 0 < r → R r = ((r : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I))
    (E : ℝ) (k : ℤ) (s : ℂ) :
    R ((1 + E ^ 2) ^ (-(1 / 2 : ℝ)))
        * ((((E : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + E ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + E ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))
      = ((((E : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + E ^ 2) : ℝ) : ℂ)) ^ k
        * (((1 + E ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((t : ℝ) : ℂ) * Complex.I / 2)) := by
  have hq : (0 : ℝ) < 1 + E ^ 2 := by positivity
  have hq0 : (((1 + E ^ 2 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have him : (Complex.log (((1 + E ^ 2 : ℝ)) : ℂ) * (((-(1 / 2 : ℝ)) : ℝ) : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hq.le, ← Complex.ofReal_mul, Complex.ofReal_im]
  have hmul : (((1 + E ^ 2 : ℝ)) : ℂ) ^ ((((-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((t : ℝ) : ℂ) * Complex.I))
      = ((((1 + E ^ 2 : ℝ)) : ℂ) ^ (((-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ (((t : ℝ) : ℂ) * Complex.I) :=
    Complex.cpow_mul _ (by rw [him]; exact neg_lt_zero.mpr Real.pi_pos) (by rw [him]; exact Real.pi_pos.le)
  have hAC : (((1 + E ^ 2 : ℝ)) : ℂ) ^ ((((-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((t : ℝ) : ℂ) * Complex.I))
        * (((1 + E ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2))
      = (((1 + E ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((t : ℝ) : ℂ) * Complex.I / 2)) := by
    rw [← Complex.cpow_add _ _ hq0]
    congr 1
    push_cast
    ring
  rw [hR _ (Real.rpow_pos_of_pos hq _), Complex.ofReal_cpow hq.le, ← hmul,
    show ∀ p q r : ℂ, p * q * r = q * (p * r) from fun _ _ _ => by ring, hAC]

private theorem complex_factor_eq (R : ℝ → ℂ) (t : ℝ)
    (hR : ∀ r : ℝ, 0 < r → R r = ((r : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I))
    (z : ℂ) (p q m : ℕ) (s : ℂ) :
    R ((1 + ‖z‖ ^ 2) ^ (-(1 / 2 : ℝ))) * z ^ p * (starRingEnd ℂ) z ^ q
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - (m : ℂ) / 2)
      = z ^ p * (starRingEnd ℂ) z ^ q
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + (m : ℂ) / 2 + ((t : ℝ) : ℂ) * Complex.I / 2)) := by
  have hq : (0 : ℝ) < 1 + ‖z‖ ^ 2 := by positivity
  have hq0 : (((1 + ‖z‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq.ne'
  have him : (Complex.log (((1 + ‖z‖ ^ 2 : ℝ)) : ℂ) * (((-(1 / 2 : ℝ)) : ℝ) : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hq.le, ← Complex.ofReal_mul, Complex.ofReal_im]
  have hmul : (((1 + ‖z‖ ^ 2 : ℝ)) : ℂ) ^ ((((-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((t : ℝ) : ℂ) * Complex.I))
      = ((((1 + ‖z‖ ^ 2 : ℝ)) : ℂ) ^ (((-(1 / 2 : ℝ)) : ℝ) : ℂ)) ^ (((t : ℝ) : ℂ) * Complex.I) :=
    Complex.cpow_mul _ (by rw [him]; exact neg_lt_zero.mpr Real.pi_pos) (by rw [him]; exact Real.pi_pos.le)
  have hAC : (((1 + ‖z‖ ^ 2 : ℝ)) : ℂ) ^ ((((-(1 / 2 : ℝ)) : ℝ) : ℂ) * (((t : ℝ) : ℂ) * Complex.I))
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1) - (m : ℂ) / 2)
      = (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + (m : ℂ) / 2 + ((t : ℝ) : ℂ) * Complex.I / 2)) := by
    rw [← Complex.cpow_add _ _ hq0]
    congr 1
    push_cast
    ring
  rw [hR _ (Real.rpow_pos_of_pos hq _), Complex.ofReal_cpow hq.le, ← hmul,
    show ∀ e f g i : ℂ, e * f * g * i = f * g * (e * i) from fun _ _ _ _ => by ring, hAC]

/-! ### The finite-adelic bookkeeping -/

private theorem prod_mul_finprod_subtype {ι M : Type*} [CommMonoid M] (S₁ : Finset ι) (G : ι → M)
    (hfin : (Function.mulSupport G).Finite) :
    (∏ v ∈ S₁, G v) * ∏ᶠ v : {v // v ∉ S₁}, G v.1 = ∏ᶠ v, G v := by
  have hG : ∀ v, G v = Set.mulIndicator (↑S₁) G v * Set.mulIndicator (↑S₁ : Set ι)ᶜ G v := by
    intro v
    by_cases hv : v ∈ S₁
    · rw [Set.mulIndicator_of_mem (Finset.mem_coe.mpr hv),
        Set.mulIndicator_of_notMem (Set.notMem_compl_iff.mpr (Finset.mem_coe.mpr hv)), mul_one]
    · rw [Set.mulIndicator_of_notMem (fun h => hv (Finset.mem_coe.mp h)),
        Set.mulIndicator_of_mem (Set.mem_compl fun h => hv (Finset.mem_coe.mp h)), one_mul]
  have h1 : (Function.mulSupport fun v => Set.mulIndicator (↑S₁) G v).Finite :=
    (S₁.finite_toSet).subset Set.mulSupport_mulIndicator_subset
  have h2 : (Function.mulSupport fun v => Set.mulIndicator (↑S₁ : Set ι)ᶜ G v).Finite := by
    rw [Set.mulSupport_mulIndicator]
    exact hfin.subset Set.inter_subset_right
  rw [finprod_congr hG, finprod_mul_distrib h1 h2, ← finprod_mem_def, ← finprod_mem_def, finprod_mem_coe_finset,
    finprod_subtype_eq_finprod_cond]
  rfl

private theorem off_param_eq_one {F : Type} [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) (y : v.adicCompletion F)
    (hy : y ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) y
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
              * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) y = 1 := by
  rw [Set.indicator_of_mem hy, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hy), add_zero]

private theorem differentiable_etaFst (F : Type) [Field F] [NumberField F]
    (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    Differentiable ℂ (fun s : ℂ => ((etaFst μ α hα s x : ℂˣ) : ℂ)) := by
  have h0 : ((((α x : ℝˣ) : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα x).ne'
  have : (fun s : ℂ => ((etaFst μ α hα s x : ℂˣ) : ℂ))
      = fun s => ((μ x : ℂˣ) : ℂ) * ((((α x : ℝˣ) : ℝ)) : ℂ) ^ (s + 1 / 2) := by
    funext s
    rw [etaFst_apply, Units.val_mul, cpowChar_apply_val]
  rw [this]
  exact (differentiable_const _).mul ((differentiable_id.add_const _).const_cpow (Or.inl h0))

private theorem differentiable_etaSnd (F : Type) [Field F] [NumberField F]
    (ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    Differentiable ℂ (fun s : ℂ => ((etaSnd ν α hα s x : ℂˣ) : ℂ)) := by
  have h0 : ((((α x : ℝˣ) : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hα x).ne'
  have : (fun s : ℂ => ((etaSnd ν α hα s x : ℂˣ) : ℂ))
      = fun s => ((ν x : ℂˣ) : ℂ) * ((((α x : ℝˣ) : ℝ)) : ℂ) ^ (-(s + 1 / 2)) := by
    funext s
    rw [etaSnd_apply, Units.val_mul, cpowChar_apply_val]
  rw [this]
  exact (differentiable_const _).mul ((differentiable_id.add_const _).neg.const_cpow (Or.inl h0))


/-! ### The datum, from the Bruhat-cell expansion of a flat family -/

private theorem exists_sum_factorization_weyl_unipotent_mul_of_flat
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμc : Continuous μ) (_hνc : Continuous ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
      (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
      (_hnψfin : (Function.support nψ).Finite)
      (_hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
      (_hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
        ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
      (_hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
        ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
      (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
      (_hθr : ∀ i, θr i ≠ 0)
      (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
      (_hθc : ∀ w, θc w ≠ 0)
      (_hψarch : ∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
        Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
        * ∏ w : {w : InfinitePlace F // w.IsComplex},
        Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
      (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχ : χ = μ * ν⁻¹)
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
      (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hΨ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (Ψ s))
      (_hΨK : ∀ s, IsArchKFinite F (Ψ s))
      (_hΨf : ∀ s, IsKfSmooth F (Ψ s))
      (_hΨjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ψ p.1 p.2))
      (_hΨhol : ∀ g, Differentiable ℂ (fun s => Ψ s g))
      (_hΨflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          Ψ s k = Ψ s' k)
      (_hΨne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), Ψ s g ≠ 0)
      (g : AdelicGL2 (𝓞 F) F),
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S →
      ∃ (cS : HeightOneSpectrum (𝓞 F) → ℕ)
        (mS : ℕ)
        (n : ℕ)
        (A B : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ)
        (h : Fin n → (v : HeightOneSpectrum (𝓞 F)) → ℂ → v.adicCompletion F → ℂ)
        (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
        (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
        (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
        (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
        (Wr : Fin n → {w : InfinitePlace F // w.IsReal} → ℂ → ℝ → ℂ)
        (Wc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℂ → ℂ → ℂ)
        (a : (AdeleRing (𝓞 F) F)ˣ)
        (u : AdeleRing (𝓞 F) F)
        (C : Fin n → ℂ → ℂ),
      (∀ v, ‖((NumberField.TateGlobal.localChar χ v (ϖ v) : ℂˣ) : ℂ)‖ = 1) ∧
      (∀ v ∉ S, ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 →
        NumberField.TateGlobal.localChar χ v u = 1) ∧
      (∀ v ∉ S, nψ v = 0) ∧
      (∀ v ∈ S, 1 ≤ cS v) ∧
      (∀ v ∈ S, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (cS v),
        NumberField.TateGlobal.localChar χ v u = 1) ∧
      (1 ≤ mS) ∧
      (∀ (j : Fin n), ∀ v ∈ S, ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → A j v y = A j v x) ∧
      (∀ (j : Fin n), ∀ v ∈ S, ∀ x y : v.adicCompletion F,
        Valued.v (y - x) ≤ Multiplicative.ofAdd (-(mS : ℤ)) → B j v y = B j v x) ∧
      (∀ (j : Fin n), ∀ v ∉ S, ∀ (s : ℂ) (x : v.adicCompletion F),
        h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
        * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x) ∧
      (∀ (j : Fin n), ∀ v ∈ S, ∀ (s : ℂ) (x : v.adicCompletion F),
        h j v s x = (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A j v) x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
        (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar χ v)⁻¹ y
        * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B j v y⁻¹) x) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}), (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
      (∀ (j : Fin n) (i : {w : InfinitePlace F // w.IsReal}) (s : ℂ) (x : ℝ),
        Wr j i s x = ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat j i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2))) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}) (s z : ℂ),
        Wc j w s z = z ^ (abm j w).1 * (starRingEnd ℂ) z ^ (abm j w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2))) ∧
      (∀ j, Differentiable ℂ (C j)) ∧
      (∀ s, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ s)) ∧
      ∀ (s : ℂ) (y : AdeleRing (𝓞 F) F),
        Ψ s (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)
        = ∑ j : Fin n, C j s
        * (∏ i : {w : InfinitePlace F // w.IsReal},
        Wr j i s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).1 i))
        * (∏ w : {w : InfinitePlace F // w.IsComplex},
        Wc j w s ((InfiniteAdeleRing.ringEquiv_mixedSpace F (a • (y + u)).1).2 w))
        * ∏ᶠ v : HeightOneSpectrum (𝓞 F), h j v s ((a • (y + u)).2 v) := by
  intro α hα μ ν hμ hν hμc hνc _ _ _ nψ hnψfin _ _ _ _ _ _ _ _ χ hχ ϖ _ Ψ hΨ hΨK hΨf hΨjc _ hΨflat hΨne g
  subst hχ

  obtain ⟨b, k, hb, hkfin, hkarch, rfl⟩ := exists_mem_adelicBorel_mul_eq F g

  have hΦind : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (fun x => Ψ s (x * k)) :=
    fun s => (hΨ s).rightTranslate k
  have hΦK : ∀ s, IsArchKFinite F (fun x => Ψ s (x * k)) :=
    fun s => isArchKFinite_rightTranslate F (hΨK s) k hkarch
  have hΦf : ∀ s, IsKfSmooth F (fun x => Ψ s (x * k)) := fun s => isKfSmooth_rightTranslate F (hΨf s) k
  have hΦc : ∀ s, Continuous (fun x => Ψ s (x * k)) :=
    fun s => (hΨjc.comp (Continuous.prodMk_right s)).comp (continuous_id.mul continuous_const)
  have hΦflat : ∀ (s s' : ℂ) (k' : AdelicGL2 (𝓞 F) F),
      glFin (𝓞 F) F k' ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k'))) →
      Ψ s (k' * k) = Ψ s' (k' * k) := by
    intro s s' k' hk'f hk'a
    refine hΨflat s s' (k' * k) ?_ ?_
    · rw [map_mul]
      exact Subgroup.mul_mem _ hk'f hkfin
    · intro w
      rw [map_mul, map_mul]
      exact (hk'a w).mul (hkarch w)
  have hΦne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), Ψ s (g * k) ≠ 0 := by
    obtain ⟨s, g₀, hg₀⟩ := hΨne
    exact ⟨s, g₀ * k⁻¹, by rwa [inv_mul_cancel_right]⟩

  obtain ⟨S₁, n, c, kdat, abm, m, A, B, Rr, Rc, habm, hm, hA, hB, hχS₁, hχc₁, hRr, hRc, hbig⟩ :=
    bigCell_eq_sum_pureTensor_of_flat_family F hα μ ν (fun s x => Ψ s (x * k))
      hΦind hΦK hΦf hΦc hΦflat hΦne
  rw [adelicWeyl_inv F] at hbig

  have hχu : IsUnitaryChar (𝓞 F) F (μ * ν⁻¹) := fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv, hμ x, hν x, inv_one, mul_one]
  have hχcont : Continuous ⇑(μ * ν⁻¹) := by
    show Continuous fun x => (μ * ν⁻¹) x
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply]
    exact hμc.mul hνc.inv
  choose tr htr using fun i => exists_tau_real F (μ * ν⁻¹) hχu hχcont i (Rr i) (hRr i)
  choose tc htc using fun w => exists_tau_complex F (μ * ν⁻¹) hχu hχcont w (Rc w) (hRc w)

  choose cN hcN using hχc₁

  refine ⟨S₁ ∪ hnψfin.toFinset, fun S hS => ?_⟩
  have hS₁ : S₁ ⊆ S := Finset.union_subset_left hS
  have hSψ : hnψfin.toFinset ⊆ S := Finset.union_subset_right hS

  let cS' : HeightOneSpectrum (𝓞 F) → ℕ := fun v => if hv : v ∈ S₁ then max 1 (cN v hv) else 1
  let A' : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ :=
    fun j v => if v ∈ S₁ then A j v else fun _ => 1
  let B' : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ :=
    fun j v => if v ∈ S₁ then B j v else fun _ => 1
  let P : Fin n → (v : HeightOneSpectrum (𝓞 F)) → ℂ → v.adicCompletion F → ℂ := fun j v s x =>
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (A' j v) x
      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B' j v y⁻¹) x
  let Q : (v : HeightOneSpectrum (𝓞 F)) → ℂ → v.adicCompletion F → ℂ := fun v s x =>
    (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
      + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
          (fun y => LanglandsTunnell.TateLocal.charExt (NumberField.TateGlobal.localChar (μ * ν⁻¹) v)⁻¹ y
            * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x
  let h' : Fin n → (v : HeightOneSpectrum (𝓞 F)) → ℂ → v.adicCompletion F → ℂ :=
    fun j v s x => if v ∈ S then P j v s x else Q v s x

  let a : (AdeleRing (𝓞 F) F)ˣ :=
    borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)) * (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹
  let u : AdeleRing (𝓞 F) F :=
    (b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1
      * (((borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F)))⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
  refine ⟨cS', m, n, A', B', h', kdat, fun _ i => tr i, abm, fun _ w => tc w,
    fun j i s x => ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ (kdat j i)
        * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-(s + 1 / 2 + ((tr i : ℝ) : ℂ) * Complex.I / 2)),
    fun j w s z => z ^ (abm j w).1 * (starRingEnd ℂ) z ^ (abm j w).2.1
        * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ))
            ^ (-(2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((tc w : ℝ) : ℂ) * Complex.I / 2)),
    a, u,
    fun j s => c j
      * (((etaFst μ α hα s (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)
        * ((etaSnd ν α hα s (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 F) F))) : ℂˣ) : ℂ)),
    ?_, ?_, ?_, ?_, ?_, hm, ?_, ?_, ?_, ?_, habm, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, ?_,
    fun s => ⟨_, _, hΨ s⟩, ?_⟩
  ·
    intro v
    rw [NumberField.TateGlobal.localChar_apply]
    exact hχu _
  ·
    intro v hv w hw
    exact hχS₁ v (fun h => hv (hS₁ h)) w hw
  ·
    intro v hv
    by_contra hne
    exact hv (hSψ (hnψfin.mem_toFinset.mpr (Function.mem_support.mpr hne)))
  ·
    intro v _
    show 1 ≤ cS' v
    simp only [cS']
    split_ifs with h1
    · exact le_max_left _ _
    · exact le_rfl
  ·
    intro v _ w hw
    by_cases h1 : v ∈ S₁
    · have hw' : w ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v (max 1 (cN v h1)) := by
        simpa only [cS', dite_eq_left h1] using hw
      exact hcN v h1 w (LanglandsTunnell.TateLocal.higherUnitsAt_antitone F v (le_max_right 1 (cN v h1)) hw')
    · have hw' : w ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v 1 := by
        simpa only [cS', dite_eq_right h1] using hw
      exact hχS₁ v h1 w ((LanglandsTunnell.TateLocal.mem_higherUnitsAt_iff F v).mp hw').1
  ·
    intro j v _ x hx y hy hle
    by_cases h1 : v ∈ S₁
    · simp only [A', ite_eq_left h1]
      exact hA j v h1 x hx y hy hle
    · simp only [A', ite_eq_right h1]
  ·
    intro j v _ x y hle
    by_cases h1 : v ∈ S₁
    · simp only [B', ite_eq_left h1]
      exact hB j v h1 x y hle
    · simp only [B', ite_eq_right h1]
  ·
    intro j v hv s x
    simp only [h', ite_eq_right hv, Q]
  ·
    intro j v hv s x
    simp only [h', ite_eq_left hv, P]
  ·
    intro j
    exact (differentiable_const (c j)).mul
      ((differentiable_etaFst F μ α hα _).mul (differentiable_etaSnd F ν α hα _))
  ·
    intro s y
    obtain ⟨T, hT, hT1, hT2, hwd⟩ := exists_borel_mul_weyl_mul_unipotentGL2_eq F b hb y
    have e1 : adelicWeyl (𝓞 F) F * unipotentGL2 y * (b * k)
        = T * (adelicWeyl (𝓞 F) F * unipotentGL2 (a • (y + u)) * k) := by
      rw [← mul_assoc, hwd, mul_assoc]
    rw [e1, hΨ s T hT, hT1, hT2, hbig s (a • (y + u)), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hfinj : (Function.mulSupport fun v => h' j v s ((a • (y + u)).2 v)).Finite := by
      have hxO := Filter.eventually_cofinite.mp (RestrictedProduct.eventually _ _ (a • (y + u)).2)
      refine (S.finite_toSet.union hxO).subset (fun v hv => ?_)
      by_contra hv'
      simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, not_or, not_not] at hv'
      refine hv ?_
      show h' j v s ((a • (y + u)).2 v) = 1
      simp only [h', ite_eq_right hv'.1, Q]
      exact off_param_eq_one (μ * ν⁻¹) v s _ hv'.2
    rw [Finset.prod_congr rfl (fun i _ => real_factor_eq (Rr i) (tr i) (htr i) _ (kdat j i) s),
      Finset.prod_congr rfl (fun w _ =>
        complex_factor_eq (Rc w) (tc w) (htc w) _ (abm j w).1 (abm j w).2.1 (abm j w).2.2 s),
      show ∀ e f g i l o : ℂ, e * (f * g * i * l * o) = f * e * g * i * (l * o) from
        fun _ _ _ _ _ _ => by ring]
    conv_lhs =>
      arg 2
      equals ∏ᶠ v, h' j v s ((a • (y + u)).2 v) =>
        rw [← prod_mul_finprod_subtype S₁ (fun v => h' j v s ((a • (y + u)).2 v)) hfinj]
        congr 1
        · refine Finset.prod_congr rfl (fun v hv => ?_)
          simp only [h', ite_eq_left (hS₁ hv), P, A', B', ite_eq_left hv]
        · refine finprod_congr (fun v => ?_)
          by_cases hvS : (v : HeightOneSpectrum (𝓞 F)) ∈ S
          · simp only [h', ite_eq_left hvS, P, A', B', ite_eq_right v.2, mul_one]
          · simp only [h', ite_eq_right hvS, Q]
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]

end EisensteinGeneral.Piece

open EisensteinGeneral.Piece in
open NumberField.AdelicLevel AutomorphicForm.WindowedSiegel in
open scoped Classical in
theorem EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμc : Continuous μ) (_hνc : Continuous ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
      (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
      (_hnψfin : (Function.support nψ).Finite)
      (_hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
      (_hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
        ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
      (_hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
        ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
      (θr : {w : InfinitePlace F // w.IsReal} → ℝ)
      (_hθr : ∀ i, θr i ≠ 0)
      (θc : {w : InfinitePlace F // w.IsComplex} → ℂ)
      (_hθc : ∀ w, θc w ≠ 0)
      (_hψarch : ∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
        Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
        * ∏ w : {w : InfinitePlace F // w.IsComplex},
        Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
      (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (_hχ : χ = μ * ν⁻¹)
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
      (Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hΨ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (Ψ s))
      (_hΨK : ∀ s, IsArchKFinite F (Ψ s))
      (_hΨf : ∀ s, IsKfSmooth F (Ψ s))
      (_hΨjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => Ψ p.1 p.2))
      (_hΨhol : ∀ g, Differentiable ℂ (fun s => Ψ s g))
      (_hΨflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          Ψ s k = Ψ s' k)
      (_hΨne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), Ψ s g ≠ 0)
      (g : AdelicGL2 (𝓞 F) F),
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S →
      Nonempty (FactorizationDatum F ψv nψ χ ϖ Ψ g S) := by
  intro _ hα μ ν hμ hν hμc hνc ψ hψ ψv nψ hnψfin hψv hψv' hψfin θr hθr θc hθc hψarch χ hχ ϖ hϖ Ψ hΨ hΨK hΨf hΨjc
    hΨhol hΨflat hΨne g
  obtain ⟨S₀, hS₀⟩ := exists_sum_factorization_weyl_unipotent_mul_of_flat F hα μ ν hμ hν hμc hνc ψ hψ ψv nψ
    hnψfin hψv hψv' hψfin θr hθr θc hθc hψarch χ hχ ϖ hϖ Ψ hΨ hΨK hΨf hΨjc hΨhol hΨflat hΨne g
  refine ⟨S₀, fun S hS => ?_⟩
  obtain ⟨cS, mS, n, A, B, h, kdat, τr, abm, τc, Wr, Wc, a, u, C,
    hχϖ, hχS, hnψ, hcS, hχc, hmS, hA, hB, hoff, hon, habm, hWr, hWc, hC, -, hfac⟩ := hS₀ S hS
  exact ⟨{ cS := cS, mS := mS, n := n, A := A, B := B, h := h, kdat := kdat, τr := τr, abm := abm,
           τc := τc, Wr := Wr, Wc := Wc, a := a, u := u, C := C, hχϖ := hχϖ, hχS := hχS, hnψ := hnψ,
           hcS := hcS, hχc := hχc, hmS := hmS, hA := hA, hB := hB, hoff := hoff, hon := hon, habm := habm,
           hWr := hWr, hWc := hWc, hC := hC, hfac := hfac }⟩
