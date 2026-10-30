/-
  Consumer specification for **ready shelf 1, wave 1** — the `ModularCurve` successor shelf's
  first three orders (MS-1 Fricke–Galois, MS-2 Hecke–diamond laws, MS-3 j-order / coset /
  diffQExp). Written-down *uses* of the wave's headlines, composed across modules. Not part of any
  library; run by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveReady1Consumer.lean 2>&1 | grep -c error

  ZONES
  -----
    [fricke]  ZONE A — MS-1's Fricke/Galois law unpacked to its second clause alone (the shape the
              successor rows `exists_frickeAlgEquiv_xHFunctionFieldBar*` consume), and the
              identity-Galois corollary: the trivial diamond index fixes the image of `w`.
    [tail]    ZONE C — MS-3's three insertions consumed: the `diffQExp`/`qExpansionDiffAlong` glue in
              the direction the `Period` rows want, and the trivial coset translate (`a = d = 1,
              b = 0`), which says the level-1 q-expansion is fixed by `cosetSubst ζ 1 0`.
    [ratio]   ZONE E — MS-6's ratio dictionary: `166` (every element of the base-changed field is a
              modular-form ratio) fed to `442` (the adjoin is finite-dimensional with finrank
              bounded by `Γ'.index`), both at `Γ' = Γ`.
    [decay]   ZONE F — MS-6's `734`: the cusp decay of `g(E₄²E₆)^m` against `hΔ^m`, instantiated at
              the trivial `A = 1` and with the integrality hypothesis supplied by `1`.
    [toric]   ZONE D — MS-7's Γ_H toric row at `t = 1`: the two Tate-slot coordinates as elements of
              `qExpFunctionFieldC K (Γ_H M ⊥)`, with the diamond index normalised to the identity.
    [diamond] ZONE B — the diamond action read functionally, and the 28-line `HeckeDiamondCommuteBar`
              row used as the *hypothesis* of the ported `heckeEvalOneBar`:
              the evaluation of the polynomial Hecke algebra into `End (J₁(M))` becomes a ring map,
              and its images of two arbitrary elements commute.
-/

import FLTForHuman.ModularCurve.XH.FrickeGalois
import FLTForHuman.ModularCurve.HeckeDiamondCommute
import FLTForHuman.ModularCurve.Period.QExpansionDiff
import FLTForHuman.ModularCurve.ModularPolynomialCoset
import FLTForHuman.ModularCurve.TateSlots.ToricPointDictionary
import FLTForHuman.ModularCurve.X1.FunctionFieldIndex
import FLTForHuman.ModularCurve.Analytic.CuspDecay
import FLTForHuman.ModularCurve.SiegelUnit.BernoulliWeight

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open scoped MatrixGroups ModularForm

namespace Ready1Consumer


/-! ## Zone A — `[fricke]` the Galois twist of the Fricke pull-back -/

/-- MS-1's headline with its first conjunct dropped and its second kept: this is the existential
plus the Galois-twist law that the successor rows `exists_frickeAlgEquiv_xHFunctionFieldBar`,
`…_galois_smul` and `heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke`
consume (each of them restates the first conjunct for its own `f`, `g`, `W`). -/
theorem exists_fricke_algEquiv_galois_twist (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hin : ∀ d : (ZMod M)ˣ, ∃ σ : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
      ModularCurve.xHFunctionFieldBar M H, ModularCurve.IsDiamondAutHBar M H d σ)
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) :
    ∃ w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.xHFunctionFieldBar M H,
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : ModularCurve.xHFunctionFieldBar M H,
          w (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ • x) =
            ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ •
              ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x) := by
  obtain ⟨w, -, hw⟩ :=
    ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul M H hin ι W hW
  exact ⟨w, hw⟩

/-- The law at the identity Galois element: `w` carries the trivial Galois twist to the trivial
diamond index, i.e. `⟨1⟩` fixes the image of the Fricke pull-back. This is the corollary the
`J_H`-side rows need when they normalise a diamond index to `1`. -/
theorem diamondAutHBar_one_fixes_fricke_image (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (w : ModularCurve.xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ]
      ModularCurve.xHFunctionFieldBar M H)
    (hw : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ x : ModularCurve.xHFunctionFieldBar M H,
        w (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ • x) =
          ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ •
            ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x))
    (x : ModularCurve.xHFunctionFieldBar M H) :
    ModularCurve.diamondAutHBar M H (ZMod.unitOfCoprime 1 (Nat.coprime_one_left M)) (w x) = w x := by
  have h := hw 1 1 (Nat.coprime_one_left M) (by intro ζ _; simp) x
  simpa using h.symm

/-! ## Zone D — `[toric]` the Γ_H toric dictionary, unpacked -/

open ModularCurve in
/-- MS-7's Γ_H row with the existential unpacked to its two *coordinate* clauses and its third
(the `ρ`-equivariance) dropped: this is the form the successor dictionary rows
(`exists_algHom_qExpFunctionFieldC_gammaH_bot_comp_eq_iff_and_comp_diamondPullbackModL_…`) consume,
since they restate the equivariance for their own `ρ`. -/
theorem toric_coords_unpacked (K : Type*) [Field K] (M : ℕ) (hM : 2 ≤ M) (ζ : K)
    (hζ : IsPrimitiveRoot ζ M) :
    ∃ w₁ w₂ : (ZMod M)ˣ → qExpFunctionFieldC K (CohCarrier.GammaH M ⊥),
      (∀ t : (ZMod M)ˣ, (w₁ t : LaurentSeries K) =
        (tateLaurent K).c₄ * (1 + 12 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1) /
          (tateLaurent K).c₆) ∧
      (∀ t : (ZMod M)ˣ, (w₂ t : LaurentSeries K) =
        ((toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 +
            6 * (toricPoint K 1 (ζ ^ (t : ZMod M).val)).1 ^ 2 + 2 * (tateLaurent K).a₄) /
          (tateLaurent K).c₄) := by
  obtain ⟨w₁, w₂, h₁, h₂, -⟩ :=
    exists_qExpFunctionFieldC_gammaH_bot_coe_eq_toricPoint_pow_and_diamondPullbackModL_apply_eq
      K M hM ζ hζ
  exact ⟨w₁, w₂, h₁, h₂⟩

/-! ## Zone E — `[ratio]` the ratio dictionary and the index bound -/

open ModularCurve in
/-- MS-6's `442` at `Γ' = Γ` (`hΓ' := le_rfl`, the `±1` condition from `Γ` itself): the adjoin of the
`j`-expansion is finite-dimensional over `qExpFunctionFieldC K Γ` with finrank at most `Γ.index`. The
successor rows consume the *bound*, never the general `Γ'`. -/
theorem finrank_adjoin_jqModC_le_index (K : Type*) [Field K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hT : ModularGroup.T ∈ Γ) (x : qExpFunctionFieldC K Γ)
    (hx : (x : LaurentSeries K) = jqModC K) :
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
        (qExpFunctionFieldC K Γ) ∧
      Module.finrank (IntermediateField.adjoin K ({x} : Set (qExpFunctionFieldC K Γ)))
        (qExpFunctionFieldC K Γ) ≤ Γ.index :=
  ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
    K Γ hT Γ le_rfl (fun γ hγ => Or.inl hγ) x hx

open ModularCurve in
/-- MS-6's `166` with its existential unpacked and the level-one specialisation made explicit: any
`x` in the base-changed field is the ratio of the `q`-expansions of two weight-`k` forms on the
`GL`-coerced `Γ`. This is the shape every `Period`/`CoeffMap` consumer restates. -/
theorem ratio_of_mem_laurentBaseChange (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (x : LaurentSeries ℂ)
    (hx : x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.qExpFunctionFieldC ℚ Γ)) :
    ∃ (k : ℤ) (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k), h ≠ 0 ∧
      x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
        ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
  ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange_qExpFunctionFieldC
    Γ hT x hx

open ModularCurve in
/-- MS-6's `734` at the trivial twist `A = 1`: the slash comparison at `i∞` is the comparison of the
raw functions, which is the form the level-one Sturm/peaked-form rows use. -/
theorem eventually_norm_le_of_isIntegral (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hT : ModularGroup.T ∈ Γ) {k : ℤ} (m : ℕ) (hm : 1 ≤ m)
    (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0) (X : LaurentSeries ℂ)
    (hX : X * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) (M : ℕ)
    (h₂ : IsIntegral (Algebra.adjoin ℂ ({(jqModC ℂ)⁻¹} : Set (LaurentSeries ℂ)))
      (X ^ (2 * M) * jqModC ℂ ^ (m * M + 1) *
        (jqModC ℂ - algebraMap ℂ (LaurentSeries ℂ) 1728) ^ (m * M)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
      ‖g τ * (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ) ^ m‖ ≤
        ε * ‖h τ * ModularForm.discriminant τ ^ m‖ := by
  have h := ModularCurve.eventually_norm_slash_le_of_isIntegral_adjoin_jqModC_inv_pow
    Γ hT m hm g h hh X hX M h₂ (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ε hε
  simpa using h

/-! ## Zone C — `[tail]` the two small rows, consumed in the direction their consumers use -/

open ModularCurve in
/-- MS-3's `qExpansionDiffAlong_val_eq_diffQExp` in the direction a `Period` consumer wants it: the
algebraic engine speaks `qExpansionDiffAlong`, the analytic rows are stated with `diffQExp`. -/
theorem diffQExp_eq_qExpansionDiffAlong {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) (ω : Ω[F⁄L]) :
    diffQExp F ω = qExpansionDiffAlong F.val ω :=
  (ModularCurve.qExpansionDiffAlong_val_eq_diffQExp F ω).symm

open ModularCurve UpperHalfPlane in
/-- MS-3's coset-translate row at the trivial translate `(a, b, d) = (1, 0, 1)`: every periodic
holomorphic bounded `F` is its own coset translate, and its level-1 `q`-expansion is fixed by
`cosetSubst ζ 1 0`. This is the normalisation the `Φ_N`/coset rows need at the level-1 end. -/
theorem cosetSubst_one_zero_fixes (ζ : ℂˣ)
    (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / ((1 : ℕ) : ℂ)))
    (F : ℍ → ℂ) (hFper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hFhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F)
    (hFbd : UpperHalfPlane.IsBoundedAtImInfty F) :
    ((qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) =
      ModularCurve.cosetSubst ζ 1 0 ((qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have h := ModularCurve.qExpansion_cosetTranslate_eq_cosetSubst (N := 1) (a := 1) (b := 0) (d := 1)
    (by norm_num) (by norm_num) ζ hζ F F hFper hFhol hFbd
    (by
      intro τ τ' h
      have h' : τ' = τ := UpperHalfPlane.coe_injective (by simpa using h)
      subst h'
      rfl)
  simpa using h.2.2.2

/-! ## Zone B — `[diamond]` the diamond law, functionally, and the commute bar at work -/

/-- `⟨dd'⟩` as an endomorphism of `J_H` is the composite `⟨d⟩ ∘ ⟨d'⟩` — the headline of MS-2's
410-line row in the form a Hecke-algebra consumer uses it (no `x` in the statement). -/
theorem diamondHBar_mul_comp (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (d d' : (ZMod M)ˣ) :
    ModularCurve.diamondHBar M H (d * d') =
      (ModularCurve.diamondHBar M H d) ∘ (ModularCurve.diamondHBar M H d') := by
  funext x
  exact ModularCurve.diamondHBar_mul M H d d' x

/-- The same law iterated: a triple product acts by the triple composite. -/
theorem diamondHBar_mul_three (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (d₁ d₂ d₃ : (ZMod M)ˣ) (x : ModularCurve.JH M H) :
    ModularCurve.diamondHBar M H (d₁ * d₂ * d₃) x =
      ModularCurve.diamondHBar M H d₁
        (ModularCurve.diamondHBar M H d₂ (ModularCurve.diamondHBar M H d₃ x)) := by
  rw [ModularCurve.diamondHBar_mul, ModularCurve.diamondHBar_mul]

/-- MS-2's 28-line row consumed for its purpose: `HeckeDiamondCommuteBar M` is exactly the
hypothesis of `heckeEvalOneBar`, so the row turns the polynomial Hecke algebra `HeckeAlgOne` into a
ring map into `End ℤ (J₁(M))` — with no commuting hypothesis left in the statement. -/
def heckeEvalOne (M : ℕ) [NeZero M] :
    ModularCurve.HeckeAlgOne →+* Module.End ℤ (ModularCurve.JOne M) :=
  ModularCurve.heckeEvalOneBar (ModularCurve.heckeDiamondCommuteBar M)

/-- … and the map's value at the Hecke generator is `T_ℓ`. -/
theorem heckeEvalOne_heckeGen (M : ℕ) [NeZero M] (ℓ : Nat.Primes) :
    heckeEvalOne M (ModularCurve.heckeGenOne ℓ) = ModularCurve.heckeOperatorOneBar M ℓ :=
  ModularCurve.heckeEvalOneBar_heckeGenOne (ModularCurve.heckeDiamondCommuteBar M) ℓ

/-- … at a diamond generator it is `⟨d⟩`. -/
theorem heckeEvalOne_diamondGen (M : ℕ) [NeZero M] (d : ℕ) :
    heckeEvalOne M (MvPolynomial.X (Sum.inr d)) = ModularCurve.diamondOneBar M d :=
  ModularCurve.heckeEvalOneBar_X (ModularCurve.heckeDiamondCommuteBar M) (Sum.inr d)

/-- … and, because the row makes the generated subalgebra commutative, the images of any two
elements of the Hecke algebra commute as endomorphisms. -/
theorem heckeEvalOne_comm (M : ℕ) [NeZero M] (t t' : ModularCurve.HeckeAlgOne) :
    heckeEvalOne M t * heckeEvalOne M t' = heckeEvalOne M t' * heckeEvalOne M t := by
  haveI := ModularCurve.isMulCommutative_adjoin_heckeDiamondGenBar
    (ModularCurve.heckeDiamondCommuteBar M)
  have h : ModularCurve.heckeEvalOneBarAux (ModularCurve.heckeDiamondCommuteBar M) t *
      ModularCurve.heckeEvalOneBarAux (ModularCurve.heckeDiamondCommuteBar M) t' =
      ModularCurve.heckeEvalOneBarAux (ModularCurve.heckeDiamondCommuteBar M) t' *
        ModularCurve.heckeEvalOneBarAux (ModularCurve.heckeDiamondCommuteBar M) t :=
    mul_comm' _ _
  simpa only [heckeEvalOne, ModularCurve.heckeEvalOneBar_apply, Subalgebra.coe_mul] using
    congrArg Subtype.val h

end Ready1Consumer
