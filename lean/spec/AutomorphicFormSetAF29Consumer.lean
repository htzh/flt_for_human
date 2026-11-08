/-
  Cross-module wire test for SET-AF29 (the Whittaker coefficient at `diagOne`).

  A `spec/` probe, not a library module. Three composition zones, each one *consuming* a headline of
  `AutomorphicForm/Adelic/WhittakerDiagOne.lean` rather than restating it:

  * **Zone 1 (pin 913 at the trivial weight).** The circle-weight row is instantiated at `n = 0`,
    `w₀ = 0`, the trivial central character and the constant vector `1`. The only weight left is
    `(0 : ℤ) - 2 * 0 = 0`, which every constant vector has, so all three hypotheses are discharged
    concretely. The phase `μ` the row produces satisfies `‖μ p t‖ = ‖t‖ ^ 0 = 1`, and the read-off is
    that the coefficient of a constant vector at `diagOne a` has the same modulus as at the
    split-torus point: at trivial weight the circle direction no longer moves the modulus.

  * **Zone 2 (pin 716 at `k = 1`, and the degenerate separating family).** The cusp-constituent
    expansion is consumed at `k = 1` (`glFin 1 = 1` and every archimedean component of `1` is a row
    isometry), which drops the `k`-parameter, and then read as a *vanishing criterion*: if the
    separating family does not see the coefficient — every `diagOne` value vanishes — the coefficient
    itself vanishes. That is the degenerate family; at `m = 0` (the empty family) the same expansion
    is the bare statement `W = 0`.

  * **Zone 3 (pin 714 ⇒ pin 716).** The `…_norm_infinitePlace_eq_one` companion carries one extra
    conjunct in the existential (`∀ w, ‖ε.1 w‖ = 1`); dropping it yields the plain expansion. This
    zone composes the two cusp rows against each other, so deleting either headline breaks the file.

  Every proof below is an application of one of the three headlines; the file has no `#check`s.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerDiagOne

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.CuspidalConstituent AutomorphicForm.SiegelCovering
open AutomorphicForm.WindowedSiegel MeasureTheory IsDedekindDomain
open scoped ENNReal Topology Matrix

namespace SetAF29Consumer

/-- The carrier of the 913 headline at a carrier `D`. -/
abbrev pinsOf (K : Type) [Field K] [NumberField K] (D : Set (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

/-- The carrier of the two cusp-constituent headlines. -/
abbrev cuspPins (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K)

/-- The coefficient at parameter `1` of a carrier. -/
abbrev WAt (K : Type) [Field K] [NumberField K] (pins : CarrierPins K)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  whittakerCoefficient K pins (NumberField.StandardAddChar.stdAddChar K) φ 1 g

/-! ## Zone 1: pin 913 at the trivial weight, read on the constant vector -/

/-- **Zone 1.** Pin 913 at `n = 0` (the only weight is `0`), the trivial central character
(`w₀ = 0`) and the constant vector `1`: `hξ`, `hxZ` and `hwt` are discharged concretely, and the
consequence read off is that the modulus of the `diagOne` value of a constant vector is the modulus
of its split-torus value. -/
theorem norm_WAt_one_diagOne_eq_norm_split
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (b : (AdeleRing (𝓞 K) K)ˣ) (hb : ((b : AdeleRing (𝓞 K) K)).2 = 1)
    (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1)
    (hab : ∀ w' : InfinitePlace K, w' ≠ w →
      ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') :
    ‖WAt K (pinsOf K D) (fun _ => (1 : ℂ)) (diagOne a)‖ =
      ‖WAt K (pinsOf K D) (fun _ => (1 : ℂ))
        (diagOne (b * (NumberField.TateGlobal.archUnitHom w
            (NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w b))⁻¹) *
          archComplexGLAt hw
            (splitTorusGL2Complex ((Real.log ‖((a : AdeleRing (𝓞 K) K)).1 w‖ / 2 : ℝ) : ℂ)))‖ := by
  obtain ⟨μ, hμ, hval⟩ :=
    exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt
      K D 1 0 (fun z => by
        show ‖(((1 : (pinsOf K D).Z →* ℂˣ) ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ =
          NumberField.TateGlobal.ideleNorm K z ^ (0 : ℝ)
        rw [Real.rpow_zero]
        norm_num) w hw 0 (fun _ _ => 1)
      (fun _ z _ => by
        show (1 : ℂ) = ((1 : (pinsOf K D).Z →* ℂˣ) ⟨z, Subgroup.mem_top z⟩ : ℂˣ).val * 1
        rw [MonoidHom.one_apply, Units.val_one, one_mul])
      (fun p => by
        have hp : (p : ℕ) = 0 := by omega
        show HasCircleWeightAt hw ((0 : ℤ) - 2 * (p : ℕ)) (fun _ : AdelicGL2 (𝓞 K) K => (1 : ℂ))
        rw [hp]
        intro ζ _
        norm_num)
  have hμ1 : ‖μ 0 (((a : AdeleRing (𝓞 K) K)).1 w)‖ = 1 := by
    have h := hμ 0 (((a : AdeleRing (𝓞 K) K)).1 w)
    have h0 : (w.mult : ℝ) * 0 / 2 = 0 := by ring
    rw [h0, Real.rpow_zero] at h
    exact h
  have h := hval b hb 0 a ha hab
  unfold WAt pinsOf
  rw [h, norm_mul, hμ1, one_mul]

/-! ## Zone 2: pin 716 at `k = 1`, and the degenerate separating family -/

/-- **Zone 2, first read.** Pin 716 consumed at `k = 1`: the `k`-parameter drops out and the
expansion becomes a plain identity in `g`. -/
theorem exists_forall_WAt_eq_sum_WAt_diagOne
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (cuspPins K c u d₁ d₂ T).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (cuspPins K c u d₁ d₂ T) ξ V)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : x ∈ V ⊓ levelInvariantSubmodule K (cuspPins K c u d₁ d₂ T) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ (m : ℕ) (ys : Fin m → (AdelicGL2 (𝓞 K) K → ℂ)) (M : ℝ),
      (∀ i, ys i ∈ V ⊓ levelInvariantSubmodule K (cuspPins K c u d₁ d₂ T) N ⊓
        archCutSubmodule K tys) ∧
      ∃ (cs : Fin m → ℂ) (ε : (AdeleRing (𝓞 K) K)ˣ),
        ((ε : AdeleRing (𝓞 K) K)).2 = 1 ∧ NumberField.TateGlobal.ideleNorm K ε = 1 ∧
        (∀ i, ‖cs i‖ ≤ M) ∧
        ∀ g : AdelicGL2 (𝓞 K) K,
          WAt K (cuspPins K c u d₁ d₂ T) x g =
            ∑ i, cs i * WAt K (cuspPins K c u d₁ d₂ T) (ys i) (g * diagOne ε) := by
  obtain ⟨m, ys, M, hys, hexp⟩ :=
    CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV x hx w₀ hξ
  refine ⟨m, ys, M, hys, ?_⟩
  obtain ⟨cs, ε, hε1, hε2, hcs, hval⟩ :=
    hexp 1 (map_one _) (fun w => by
      show IsRowIsometry (archComponent K w (glArch (𝓞 K) K 1))
      rw [map_one, map_one]
      exact isRowIsometry_one)
  exact ⟨cs, ε, hε1, hε2, hcs, fun g => by simpa only [WAt, cuspPins, mul_one] using hval g⟩

/-- **Zone 2, second read (the degenerate separating family).** If the separating family of the
expansion does not see the coefficient — all of its `diagOne` values vanish — then the coefficient
vanishes. The empty family (`m = 0`) is the extreme case, where the expansion is `W = 0`. -/
theorem exists_forall_WAt_eq_zero_of_forall_WAt_diagOne_eq_zero
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (cuspPins K c u d₁ d₂ T).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (cuspPins K c u d₁ d₂ T) ξ V)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : x ∈ V ⊓ levelInvariantSubmodule K (cuspPins K c u d₁ d₂ T) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (k : AdelicGL2 (𝓞 K) K) (hk1 : glFin (𝓞 K) K k = 1)
    (hk2 : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) :
    ∃ (m : ℕ) (ys : Fin m → (AdelicGL2 (𝓞 K) K → ℂ)) (cs : Fin m → ℂ)
        (ε : (AdeleRing (𝓞 K) K)ˣ),
      (∀ i, ys i ∈ V ⊓ levelInvariantSubmodule K (cuspPins K c u d₁ d₂ T) N ⊓
        archCutSubmodule K tys) ∧
      ((ε : AdeleRing (𝓞 K) K)).2 = 1 ∧ NumberField.TateGlobal.ideleNorm K ε = 1 ∧
      (∀ g : AdelicGL2 (𝓞 K) K,
        WAt K (cuspPins K c u d₁ d₂ T) x (g * k) =
          ∑ i, cs i * WAt K (cuspPins K c u d₁ d₂ T) (ys i) (g * diagOne ε)) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        (∀ i, WAt K (cuspPins K c u d₁ d₂ T) (ys i) (g * diagOne ε) = 0) →
          WAt K (cuspPins K c u d₁ d₂ T) x (g * k) = 0 := by
  obtain ⟨m, ys, M, hys, hexp⟩ :=
    CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV x hx w₀ hξ
  obtain ⟨cs, ε, hε1, hε2, hcs, hval⟩ := hexp k hk1 hk2
  refine ⟨m, ys, cs, ε, hys, hε1, hε2, fun g => ?_, fun g hzero => ?_⟩
  · unfold WAt cuspPins
    rw [hval g]
  · have hexpansion : WAt K (cuspPins K c u d₁ d₂ T) x (g * k) =
        ∑ i, cs i * WAt K (cuspPins K c u d₁ d₂ T) (ys i) (g * diagOne ε) := by
      unfold WAt cuspPins
      rw [hval g]
    rw [hexpansion]
    exact Finset.sum_eq_zero fun i _ => by
      have hz : WAt K (cuspPins K c u d₁ d₂ T) (ys i) (g * diagOne ε) = 0 := hzero i
      rw [hz, mul_zero]

/-! ## Zone 3: pin 714 implies pin 716 -/

/-- **Zone 3.** The `…_norm_infinitePlace_eq_one` companion (pin 714) has one extra conjunct,
`∀ w, ‖ε.1 w‖ = 1`, in its existential. Dropping it gives the plain expansion (pin 716), so the
normalized row is *stronger* than the un-normalized one. -/
theorem cuspExpansion_of_cuspExpansion_norm_infinitePlace_eq_one
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (cuspPins K c u d₁ d₂ T).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (cuspPins K c u d₁ d₂ T) ξ V)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hx : x ∈ V ⊓ levelInvariantSubmodule K (cuspPins K c u d₁ d₂ T) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ (m : ℕ) (ys : Fin m → (AdelicGL2 (𝓞 K) K → ℂ)) (M : ℝ),
      (∀ i, ys i ∈ V ⊓ levelInvariantSubmodule K (cuspPins K c u d₁ d₂ T) N ⊓
        archCutSubmodule K tys) ∧
      ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
        (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
        ∃ (cs : Fin m → ℂ) (ε : (AdeleRing (𝓞 K) K)ˣ),
          ((ε : AdeleRing (𝓞 K) K)).2 = 1 ∧ NumberField.TateGlobal.ideleNorm K ε = 1 ∧
          (∀ i, ‖cs i‖ ≤ M) ∧
          ∀ g : AdelicGL2 (𝓞 K) K,
            whittakerCoefficient K (cuspPins K c u d₁ d₂ T)
                (NumberField.StandardAddChar.stdAddChar K) x 1 (g * k) =
              ∑ i, cs i * whittakerCoefficient K (cuspPins K c u d₁ d₂ T)
                (NumberField.StandardAddChar.stdAddChar K) (ys i) 1 (g * diagOne ε) := by
  obtain ⟨m, ys, M, hys, hexp⟩ :=
    CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV x hx w₀ hξ
  refine ⟨m, ys, M, hys, fun k hk1 hk2 => ?_⟩
  obtain ⟨cs, ε, hε1, -, hε2, hcs, hval⟩ := hexp k hk1 hk2
  exact ⟨cs, ε, hε1, hε2, hcs, hval⟩

end SetAF29Consumer
