/-
  Cross-module wire test for SET-AF68A (the Atkin--Lehner--Li basis for `Γ_H`, and the five
  commutation laws).

  A `spec/` probe, not a library module. One zone per headline of
  `ModularForms/PrimitiveFormBasis.lean`, each *consuming* the headline rather than restating it:
  the rows are fired at concrete data and the conclusion is read in the shape the downstream cone
  will read it. No primitive form is constructed anywhere in the corpus, so wherever an
  `IsPrimitiveForm` hypothesis is needed it is carried, not discharged.

  * **Zone A, row `CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus`
    at `M = 2`.** The row is fired at the prime level `2` with the nebentypus a variable `ε`, and
    with a primitive form `g'` of a level `L' ∣ 2` and of character `ε'` with
    `changeLevel hL' ε' = ε` carried as hypotheses — that is the row's coverage conjunct, read at
    the carried package. The degeneracy conjunct is read at `d = 1`: the identity dilation
    `heckeDiagMatrix 1` is the row's own `d = 1` wire, so `G i 1` is the underlying primitive form.

  * **Zone B, row `CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply`
    at `M = 2`, `H = ⊤`, `k = 2`.** The row's datum is fired at the full modular group's `Γ_H` (so
    `Γ_H(2) = Γ₁(2)`) in weight two, and the four action fields are read at `d = 1`: `G i 1` is the
    primitive form, `T_ℓ` acts by `a_ℓ`, the diamond `⟨u⟩` by the level-`2` character value, and
    `U_2` is split along the row's own two live branches (`2 ∣ L i` and `¬ 2 ∣ L i`; the third,
    `2 ∣ d`, is vacuous at `d = 1`).

  * **Zone C, row `CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm` at `M = 2`, `H = ⊤`, `k = 2`.**
    One conjunct each, at concrete operators: `T_3` with `T_5`, `T_3` with `U_2`, `T_3` with the
    diamond `⟨u⟩`, `U_2` with `⟨u⟩`, and `⟨u⟩` with `⟨v⟩`.

  The file contains no `#check`s, no `sorry`s and no placeholder proofs.
-/
import FLTForHuman.ModularForms.PrimitiveFormBasis

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularFormClass
open scoped MatrixGroups ModularForm

namespace SetAF68AConsumer

/-! ## Zone A — the `277` at `M = 2`, the carried primitive form, and the `d = 1` degeneracy -/

/-- Zone A: the row at `M = 2`, with the primitive-form package `g'` of level `L' ∣ 2` and
character `ε'` carried, and the degeneracy read at `d = 1`. -/
theorem zoneA_two {k : ℤ} {ε : DirichletCharacter ℂ 2} {L' : ℕ} [NeZero L'] (hL' : L' ∣ 2)
    {ε' : DirichletCharacter ℂ L'} {g' : CuspForm (CongruenceSubgroup.Gamma1 L') k}
    (hprim : CuspForm.IsPrimitiveForm ε' g') (hch : DirichletCharacter.changeLevel hL' ε' = ε) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (_hL : ∀ i, L i ∣ 2)
      (_εL : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 2) k),
      (∃ i, L i = L' ∧ ∀ m : ℕ,
        ModularFormClass.qCoeff (g i) m = ModularFormClass.qCoeff g' m) ∧
      (∀ (i : Fin n) (τ : UpperHalfPlane),
        G i 1 τ = g i (ModularForm.heckeDiagMatrix 1 • τ)) := by
  obtain ⟨n, L, hL, εL, g, G, -, -, -, hcov, hG, -, -⟩ :=
    CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus 2 k ε
  exact ⟨n, L, hL, εL, g, G, hcov L' hL' ε' g' hprim hch,
    fun i τ => (hG i 1 (one_dvd _)).1 τ⟩

/-- Zone A, the `d = 1` wire spent on the coordinate: the degenerate image at `d = 1` is the
primitive form's own slash value. -/
theorem zoneA_two_at_one {k : ℤ} {ε : DirichletCharacter ℂ 2} :
    ∃ (n : ℕ) (L : Fin n → ℕ) (_hL : ∀ i, L i ∣ 2)
      (_εL : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 2) k),
      ∀ (i : Fin n), ⇑(G i 1) = ⇑(g i) := by
  obtain ⟨n, L, hL, εL, g, G, -, -, -, -, hG, -, -⟩ :=
    CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus 2 k ε
  refine ⟨n, L, hL, εL, g, G, fun i => ?_⟩
  funext τ
  rw [(hG i 1 (one_dvd _)).1 τ, LiCaseOne.heckeDiagMatrix_one_smul]

/-! ## Zone B — the `492` at `M = 2`, `H = ⊤`, `k = 2` -/

/-- Zone B: the row at `M = 2`, `H = ⊤`, `k = 2`, with the four action conjuncts read at `d = 1`. -/
theorem zoneB_two :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ 2)
      (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) 2)
      (G : Fin n → ℕ → CuspForm (CohCarrier.GammaH 2 ⊤) 2),
      (∀ (i : Fin n) (τ : UpperHalfPlane),
        G i 1 τ = g i (ModularForm.heckeDiagMatrix 1 • τ)) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ¬ ℓ ∣ 2) (i : Fin n),
        CuspForm.heckeTLinH 2 hℓ hℓ2 (G i 1) = qCoeff (g i) ℓ • G i 1) ∧
      (∀ (u : (ZMod 2)ˣ) (i : Fin n),
        CuspForm.diamondLinH 2 u (G i 1) =
          DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod 2) • G i 1) ∧
      (∀ (i : Fin n), 2 ∣ L i →
        CuspForm.heckeULinH 2 2 (G i 1) = qCoeff (g i) 2 • G i 1) ∧
      (∀ (i : Fin n), ¬ 2 ∣ L i →
        CuspForm.heckeULinH 2 2 (G i 1) =
          qCoeff (g i) 2 • G i 1 -
            (ε i (2 : ZMod (L i)) * (2 : ℂ) ^ (2 - 1)) • G i (1 * 2)) := by
  obtain ⟨n, L, hL, ε, g, G, -, -, -, hsh, -, -, hT, hD, hU⟩ :=
    CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply 2 ⊤ 2
  refine ⟨n, L, hL, ε, g, G, fun i τ => hsh i 1 (one_dvd _) τ, ?_, ?_, ?_, ?_⟩
  · intro ℓ hℓ hℓ2 i
    exact hT ℓ hℓ hℓ2 i 1 (one_dvd _)
  · intro u i
    exact hD u i 1 (one_dvd _)
  · intro i h2L
    exact (hU 2 (by norm_num) (by norm_num) i 1 (one_dvd _)).2.1 (by norm_num) h2L
  · intro i h2L
    exact (hU 2 (by norm_num) (by norm_num) i 1 (one_dvd _)).2.2 (by norm_num) h2L

/-! ## Zone C — the `176` at `M = 2`, `H = ⊤`, `k = 2`, one conjunct each -/

/-- Zone C, first conjunct: `T_3` commutes with `T_5`. -/
theorem zoneC_TT (f : CuspForm (CohCarrier.GammaH 2 ⊤) 2) :
    CuspForm.heckeTLinH 2 (ℓ := 3) (by norm_num) (by norm_num)
        (CuspForm.heckeTLinH 2 (ℓ := 5) (by norm_num) (by norm_num) f) =
      CuspForm.heckeTLinH 2 (ℓ := 5) (by norm_num) (by norm_num)
        (CuspForm.heckeTLinH 2 (ℓ := 3) (by norm_num) (by norm_num) f) :=
  (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm 2 ⊤ 2).1 3 5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) f

/-- Zone C, second conjunct: `T_3` commutes with `U_2`. -/
theorem zoneC_TU (f : CuspForm (CohCarrier.GammaH 2 ⊤) 2) :
    CuspForm.heckeTLinH 2 (ℓ := 3) (by norm_num) (by norm_num) (CuspForm.heckeULinH 2 2 f) =
      CuspForm.heckeULinH 2 2 (CuspForm.heckeTLinH 2 (ℓ := 3) (by norm_num) (by norm_num) f) :=
  (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm 2 ⊤ 2).2.1 3
    (by norm_num) (by norm_num) 2 (by norm_num) (by norm_num) f

/-- Zone C, third conjunct: `T_3` commutes with the diamond `⟨u⟩`. -/
theorem zoneC_TD (u : (ZMod 2)ˣ) (f : CuspForm (CohCarrier.GammaH 2 ⊤) 2) :
    CuspForm.heckeTLinH 2 (ℓ := 3) (by norm_num) (by norm_num) (CuspForm.diamondLinH 2 u f) =
      CuspForm.diamondLinH 2 u (CuspForm.heckeTLinH 2 (ℓ := 3) (by norm_num) (by norm_num) f) :=
  (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm 2 ⊤ 2).2.2.1 3
    (by norm_num) (by norm_num) u f

/-- Zone C, fourth conjunct: `U_2` commutes with the diamond `⟨u⟩`. -/
theorem zoneC_UD (u : (ZMod 2)ˣ) (f : CuspForm (CohCarrier.GammaH 2 ⊤) 2) :
    CuspForm.heckeULinH 2 2 (CuspForm.diamondLinH 2 u f) =
      CuspForm.diamondLinH 2 u (CuspForm.heckeULinH 2 2 f) :=
  (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm 2 ⊤ 2).2.2.2.1 2
    (by norm_num) (by norm_num) u f

/-- Zone C, fifth conjunct: `⟨u⟩` commutes with `⟨v⟩`. -/
theorem zoneC_DD (u v : (ZMod 2)ˣ) (f : CuspForm (CohCarrier.GammaH 2 ⊤) 2) :
    CuspForm.diamondLinH 2 u (CuspForm.diamondLinH 2 v f) =
      CuspForm.diamondLinH 2 v (CuspForm.diamondLinH 2 u f) :=
  (CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm 2 ⊤ 2).2.2.2.2 u v f

end SetAF68AConsumer
