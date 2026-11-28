/-
A diamond-fixed `q`-expansion lies in the full level-`M` function field.

`ModularCurve.coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq` (299 pin lines,
7 declarations): in characteristic `ℓ ∤ M`, for a diamond action `ρ` on the Γ_H-level `q`-expansion
field that is a diamond pullback and fixes the full level-`M` function field pointwise, every `ρ`-fixed
element lies in `modularFunctionFieldFullC K M`.

This is the *membership* direction of the full-level dictionary whose finrank half SET-AF108D landed
(`Degree/FinrankDedekindPsi.lean`): it combines the diamond pullback's fixed-point criterion
(`IsDiamondPullbackModL.apply_eq_one_iff_gamma0Units_mem`), the index comparisons
(`CohCarrier.index_gammaH_eq_index_gamma0_mul_index`, `Gamma0DedekindPsi.card_quotient_gamma0_le_dedekindPsi`),
the full-level finrank `ψ(N)` and the two function-field inclusions. No existing module is above all six
of its premise modules — `X1/FunctionFieldInclusion` and `X0/FunctionFieldFull` are both below
`Degree/FinrankDedekindPsi` — so the home is new.

## The rows

* `ModularCurve.coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq` — 299 pin `S_` lines.
* `ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC` — 25 pin `S_` lines (SET-AF110E).

## Port notes

* **Declaration surface.** The whole `S_` block is ported: four new helpers at the pin's names
  (`relfinrank_lift_eq_finrank`, `gamma0Units_surjective'`, `Gamma1_le_GammaH'`,
  `translation_mem_GammaH'`) plus the headline. The pin's generated label namespace `IgusaGammaH` is
  kept as the subject namespace `ModularCurve.IgusaGammaH`; the `CohCarrier` block is at the root
  `CohCarrier` (the port's home for the `Γ_H` vocabulary), as in the pin after its `p2m_open`.
* **The two measured substitutions are imported, not restated**: `finrank_adjoin_eq_relfinrank`
  (`ModularCurve/X1/FunctionFieldConstExt.lean`, byte-identical) and
  `mem_or_neg_mem_of_mem_sup_zpowers_neg_one` (`ModularCurve/IsDiamondPullbackModL.lean`, byte-identical),
  so the module declares 5 of the wire's 7 `S_` rows and the wire leaves no `MISSING`.
* **`translation_mem_GammaH'` is transcribed.** `ModularCurve/HeckeCompositum.lean`'s private copy is
  `T_mem_GammaH` (`:298`), a one-line wrapper of the *public* `CohCarrier.translation_mem_GammaH`; the
  pin's primed row does not exist in the port (`rg "translation_mem_GammaH'"` → nothing), so the pin's
  own text is used.
* **The pin's `set_option synthInstance.maxHeartbeats 1600000` / `set_option maxHeartbeats 3200000` are
  not installed.** The one instance site the pin's `synthInstance` bump covers is the
  `Module.IsTorsionFree ↥K⟮⟨jqModC K, hjE⟩⟯ ↥(qExpFunctionFieldC …)` search behind
  `Module.finrank_pos` (in `hJEpos`); it is supplied by the **direct term**
  `DivisionSemiring.to_moduleIsTorsionFree` — the same fix as
  `ModularCurve/X1/IntegralityDifferential.lean` — so the default `synthInstance` cap (20 000) holds.
  The pin's `mapGL`-injectivity `simpa` is replaced by `Matrix.SpecialLinearGroup.mapGL_injective`
  (this mathlib's `mapGL` is `toGL.comp (map …)`, so the pin's simp set no longer closes it); that and
  the `haveI`→`have` spelling are the only proof adaptations.
* **Heartbeat probe pair** (recorded, never installed). `-DmaxHeartbeats=200000` (the edit-loop cap)
  and `50000`: silent. `40000`: deterministic timeout, first at the headline's `by` (`S_` row, 299
  lines). The module floor is in `(40000, 50000]`; nothing is installed.
* **Gate readings.** `check_port --force` → **5 ok, 0 mismatch, 0 missing, 0 own, 0 kw**; engine diff
  (pin sources 2) pin decls 8, module decls 5, **5 by hash, 0 by name, 0 unaccounted** (the pin-side
  names not declared here are the two substituted rows and the pin's `solution`); every public
  declaration's `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`; `dedup --within` → 0
  clusters; `move_dead --dry-run` → `0 declarations, 0 lines`; the order-scoped collision probe
  (`tmp/af109/probe-E.lean`, both modules of the order) prints nothing.
* **Linters.** None silenced.

## Landing (SET-AF110E, same pin and mathlib)

* **Surface.** One insertion, **6 lines / 1 declaration** (the module moves from 331 to 337 lines); the
  pin's `S_` block is 25 lines and 1 declaration. `check_port`: **6 ok / 0 mismatch / 0 missing / 0 own
  / 0 kw** (6 before, the scaffold's headline already reading `ok`).
* **It is the two-case wrapper and nothing else.** `ℓ = 0` → `CharP.charP_to_charZero` (a `CharZero K`
  from `[CharP K 0]`) and `X1/FunctionFieldInclusion.lean:80`'s `…_of_charZero` row; `ℓ ≠ 0` →
  `[NeZero ℓ]` and `Degree/FinrankDedekindPsi.lean:340`'s `…_of_charP_pos` row (SET-AF109E's). Neither
  case is re-proved here and both were already in this module's import closure.
* **Drift (two sites).** (i) The pin's `haveI`s become `have`s: on a proposition goal
  `linter.style.haveILetI` warns, and a local hypothesis of class type is already an instance, so
  `have hK : CharZero K` / `have hne : NeZero ℓ` serve as instances (measured: silent). (ii) The pin's
  `attribute [-instance] …` / `attribute [-simp] …` walls are **dropped** — the proof elaborates
  without them, as this order's brief allows.
* **Engine gate**: pin sources **4**, pin decls **10**, module public decls **6** — **6 by hash**, 0 by
  name, **0 unaccounted**, 6 distinct wire rows.
* **Axioms**: all 6 public declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe** (recorded, **never installed**; the pin's `synthInstance`/`maxHeartbeats` bumps are
  absent): **silent at 50000, fails at 40000** (`whnf`, first at `:298`, i.e. SET-AF109E's headline
  proof) — unchanged from that set's record, so the new row adds nothing to the floor. The module floor
  is in `(40000, 50000]`.
* **Linters**: none silenced; the locked `lake build` logs no warning line of this file.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq.lean>

spec-pin: Theorems/Thm_ModularCurve_coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq.lean
spec-pin: P2M/Sol/S_ModularCurve_coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq.lean
spec-pin: Theorems/Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC.lean
spec-pin: P2M/Sol/S_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC.lean
spec-pin: Theorems/Thm_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental.lean
spec-pin: P2M/Sol/S_ModularCurve_exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental.lean
spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero.lean
spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_irreducible_map_ratFunc_of_natCast_ne_zero.lean
-/
import FLTForHuman.ModularCurve.Degree.FinrankDedekindPsi
import FLTForHuman.ModularCurve.Gamma0DedekindPsi
import FLTForHuman.ModularCurve.IsDiamondPullbackModL
import FLTForHuman.ModularCurve.X0.FunctionFieldFull
import FLTForHuman.ModularCurve.X1.FunctionFieldConstExt
import FLTForHuman.ModularCurve.X1.FunctionFieldFinrankIsAlgClosed
import FLTForHuman.ModularCurve.X1.FunctionFieldInclusion
import FLTForHuman.ModularForms.CohCarrier.GammaHAlgebra
import Mathlib.Tactic

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

namespace ModularCurve.IgusaGammaH

open IntermediateField

theorem relfinrank_lift_eq_finrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : IntermediateField K E) (L : IntermediateField K F) :
    (IntermediateField.lift L).relfinrank F = Module.finrank L F := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (IntermediateField.lift_le L)]
  let i : L ≃+* (IntermediateField.lift L) := (IntermediateField.liftAlgEquiv L).toRingEquiv
  let j : F ≃+* (IntermediateField.extendScalars (IntermediateField.lift_le L)) := RingEquiv.refl _
  refine (Algebra.finrank_eq_of_equiv_equiv i j ?_).symm
  ext a
  rfl

end ModularCurve.IgusaGammaH

namespace CohCarrier

open CongruenceSubgroup
open scoped MatrixGroups

theorem gamma0Units_surjective' (M : ℕ) [NeZero M] : Function.Surjective (gamma0Units M) := by
  intro u
  have hAD : (((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) * ((u : ZMod M).val : ℤ) - 1 : ℤ) : ZMod M) = 0 := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAD
  let γ : SL(2, ℤ) := ⟨!![(((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ), k; (M : ℤ), ((u : ZMod M).val : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hγ0 : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [γ]
  refine ⟨⟨γ, hγ0⟩, Units.ext ?_⟩
  simp only [val_gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Gamma0Map]
  simp [γ]

theorem Gamma1_le_GammaH' (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨_, h11, h10⟩ := hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA0 : A ∈ Gamma0 M := Gamma0_mem.mpr h10
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    simp only [CohCarrier.gamma0Units, Units.val_one]
    exact h11
  rw [this]
  exact one_mem H

theorem translation_mem_GammaH' (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    ModularGroup.T ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    simp [CohCarrier.gamma0Units, Gamma0Map, ModularGroup.T]
  rw [this]
  exact one_mem H

end CohCarrier

open _root_.ModularCurve ModularCurve.IgusaGammaH IntermediateField in
theorem ModularCurve.coe_mem_modularFunctionFieldFullC_of_forall_diamondPullbackModL_apply_eq
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)))
    (hρ : ModularCurve.IsDiamondPullbackModL K M H ρ)
    (hfix : ∀ (γ : CongruenceSubgroup.Gamma0 M)
      (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)),
      (x : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldFullC K M → ρ γ x = x)
    (u : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hu : ∀ γ : CongruenceSubgroup.Gamma0 M, ρ γ u = u) :
    (u : LaurentSeries K) ∈ ModularCurve.modularFunctionFieldFullC K M := by
  classical

  have hMK : (M : K) ≠ 0 := by
    intro h
    exact hℓM ((CharP.cast_eq_zero_iff K ℓ M).mp h)

  have hker : ρ.ker = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).comap (CohCarrier.gamma0Units M) := by
    ext γ
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact hρ.apply_eq_one_iff_gamma0Units_mem γ

  have hidx : ρ.ker.index = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
    rw [hker]; exact Subgroup.index_comap_of_surjective _ (CohCarrier.gamma0Units_surjective' M)
  have hFI : (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).FiniteIndex := inferInstance
  have hFIker : ρ.ker.FiniteIndex := ⟨by rw [hidx]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  have hFinQ : Finite (↥(CongruenceSubgroup.Gamma0 M) ⧸ ρ.ker) := Subgroup.finite_quotient_of_finiteIndex
  have hFinR : Finite ρ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ρ).toEquiv
  have hFint : Fintype ρ.range := Fintype.ofFinite _
  have hcard : Fintype.card ρ.range = (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv,
      ← Subgroup.index_eq_card, hidx]
  have hn_pos : 0 < (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

  have hartin : Module.finrank (IntermediateField.fixedField ρ.range)
      (qExpFunctionFieldC K (CohCarrier.GammaH M H)) = Fintype.card ρ.range :=
    FixedPoints.finrank_eq_card _ _

  set L : IntermediateField K (LaurentSeries K) :=
    IntermediateField.lift (IntermediateField.fixedField ρ.range) with hLdef
  have hLE : L ≤ qExpFunctionFieldC K (CohCarrier.GammaH M H) := IntermediateField.lift_le _
  have hΓ : CohCarrier.GammaH M H ≤ CongruenceSubgroup.Gamma0 M := CohCarrier.GammaH_le_Gamma0 H
  have hF0E : modularFunctionFieldFullC K M ≤ qExpFunctionFieldC K (CohCarrier.GammaH M H) :=
    (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 K M).trans
      (ModularCurve.qExpFunctionFieldC_mono K hΓ)
  have hF0L : modularFunctionFieldFullC K M ≤ L := by
    intro y hy
    have hyE : y ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) := hF0E hy
    have hfy : (⟨y, hyE⟩ : qExpFunctionFieldC K (CohCarrier.GammaH M H)) ∈
        IntermediateField.fixedField ρ.range := by
      rw [IntermediateField.mem_fixedField_iff]
      rintro _ ⟨γ, rfl⟩
      exact hfix γ ⟨y, hyE⟩ hy
    exact (IntermediateField.mem_lift ⟨y, hyE⟩).mpr hfy
  have eLE : L.relfinrank (qExpFunctionFieldC K (CohCarrier.GammaH M H)) =
      (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index :=
    (relfinrank_lift_eq_finrank _ _).trans (hartin.trans hcard)

  have hFI1 : (CongruenceSubgroup.Gamma1 M).FiniteIndex :=
    (CongruenceSubgroup.Gamma1_is_congruence M).finiteIndex
  have hfiH : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (CohCarrier.Gamma1_le_GammaH' M H)
  have hjF0 : jqModC K ∈ modularFunctionFieldFullC K M := jqModC_mem_full K M
  have hjE : jqModC K ∈ qExpFunctionFieldC K (CohCarrier.GammaH M H) := hF0E hjF0
  have hneg' : ∀ γ ∈ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)),
      γ ∈ CohCarrier.GammaH M H ∨ -γ ∈ CohCarrier.GammaH M H := by
    intro γ hγ
    obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    rcases CohCarrier.mem_or_neg_mem_of_mem_sup_zpowers_neg_one H hd with h | h
    · exact Or.inl (CohCarrier.mem_GammaH_iff.mpr ⟨hγ0, h⟩)
    · right
      have hneg0 : (-γ) ∈ CongruenceSubgroup.Gamma0 M := by
        have := CongruenceSubgroup.Gamma0_mem.mp hγ0
        rw [CongruenceSubgroup.Gamma0_mem]
        simp [Matrix.SpecialLinearGroup.coe_neg, this]
      have hunits : CohCarrier.gamma0Units M ⟨-γ, hneg0⟩ = -CohCarrier.gamma0Units M ⟨γ, hγ0⟩ := by
        ext
        simp [CohCarrier.gamma0Units, CongruenceSubgroup.Gamma0Map, Matrix.SpecialLinearGroup.coe_neg]
      exact CohCarrier.mem_GammaH_iff.mpr ⟨hneg0, by rw [hunits]; exact h⟩
  have hHH' : CohCarrier.GammaH M H ≤ CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)) := by
    intro γ hγ
    obtain ⟨hγ0, hd⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    exact CohCarrier.mem_GammaH_iff.mpr ⟨hγ0, Subgroup.mem_sup_left hd⟩
  obtain ⟨hfin, hdeg⟩ :=
    ModularCurve.finrank_adjoin_jqModC_qExpFunctionFieldC_le_index_of_isAlgClosed K
      (CohCarrier.GammaH M H) (CohCarrier.translation_mem_GammaH' M H)
      (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ))) hHH' hneg'
      ⟨jqModC K, hjE⟩ rfl

  have hIDX := CohCarrier.index_gammaH_eq_index_gamma0_mul_index M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ))
  have hidx0 : (CongruenceSubgroup.Gamma0 M).index ≤ dedekindPsi M := by
    have hc := ModularCurve.card_quotient_gamma0_le_dedekindPsi M
    set f : SL(2, ℤ) →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ with hfdef
    have hinj : Function.Injective f :=
      Matrix.SpecialLinearGroup.mapGL_injective
    have hcomp : f.range.subtype.comp f.rangeRestrict = f := by ext; rfl
    have e : ((Subgroup.map f (CongruenceSubgroup.Gamma0 M)).subgroupOf f.range).index =
        (CongruenceSubgroup.Gamma0 M).index := by
      rw [← Subgroup.index_comap_of_surjective _ (MonoidHom.rangeRestrict_surjective f),
        Subgroup.subgroupOf, Subgroup.comap_comap, hcomp, Subgroup.comap_map_eq_self_of_injective hinj]
    rw [← e, Subgroup.index_eq_card]
    exact hc

  set J : IntermediateField K (LaurentSeries K) :=
    IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) with hJdef
  have hJF0 : J ≤ modularFunctionFieldFullC K M :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hjF0)
  have eJE : J.relfinrank (qExpFunctionFieldC K (CohCarrier.GammaH M H)) =
      Module.finrank (IntermediateField.adjoin K ({(⟨jqModC K, hjE⟩ : qExpFunctionFieldC K (CohCarrier.GammaH M H))} :
        Set (qExpFunctionFieldC K (CohCarrier.GammaH M H)))) (qExpFunctionFieldC K (CohCarrier.GammaH M H)) :=
    (ModularCurve.FullnessGamma1.finrank_adjoin_eq_relfinrank (qExpFunctionFieldC K (CohCarrier.GammaH M H)) ⟨jqModC K, hjE⟩).symm
  have eJF0 : J.relfinrank (modularFunctionFieldFullC K M) = dedekindPsi M :=
    (ModularCurve.FullnessGamma1.finrank_adjoin_eq_relfinrank (modularFunctionFieldFullC K M) ⟨jqModC K, jqModC_mem_full K M⟩).symm.trans
      (ModularCurve.finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K M hMK)
  have t1 := IntermediateField.relfinrank_mul_relfinrank hJF0 hF0E
  have t2 := IntermediateField.relfinrank_mul_relfinrank hF0L hLE
  have hJEpos : 0 < J.relfinrank (qExpFunctionFieldC K (CohCarrier.GammaH M H)) := by
    have hfinh := hfin
    have hTF : Module.IsTorsionFree
        ↥(IntermediateField.adjoin K ({(⟨jqModC K, hjE⟩ : qExpFunctionFieldC K (CohCarrier.GammaH M H))} :
          Set (qExpFunctionFieldC K (CohCarrier.GammaH M H))))
        ↥(qExpFunctionFieldC K (CohCarrier.GammaH M H)) :=
      DivisionSemiring.to_moduleIsTorsionFree
    rw [eJE]; exact Module.finrank_pos
  have hJE_eq : J.relfinrank (qExpFunctionFieldC K (CohCarrier.GammaH M H)) =
      dedekindPsi M * ((modularFunctionFieldFullC K M).relfinrank L *
        (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index) := by
    rw [← t1, ← t2, eJF0, eLE]
  have hbound : J.relfinrank (qExpFunctionFieldC K (CohCarrier.GammaH M H)) ≤
      dedekindPsi M * (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := by
    rw [eJE]
    calc _ ≤ (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ))).index := hdeg
      _ = (CongruenceSubgroup.Gamma0 M).index * (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := hIDX
      _ ≤ dedekindPsi M * (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index := Nat.mul_le_mul_right _ hidx0
  have hpsi : 0 < dedekindPsi M := by
    rcases Nat.eq_zero_or_pos (dedekindPsi M) with h0 | h0
    · rw [hJE_eq, h0, zero_mul] at hJEpos; exact absurd hJEpos (lt_irrefl 0)
    · exact h0

  have hr : (modularFunctionFieldFullC K M).relfinrank L = 1 := by
    have hprod : dedekindPsi M * ((modularFunctionFieldFullC K M).relfinrank L *
        (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index) ≤
        dedekindPsi M * (1 * (H ⊔ Subgroup.zpowers (-1 : (ZMod M)ˣ)).index) := by
      rw [one_mul, ← hJE_eq]; exact hbound
    have h2 : (modularFunctionFieldFullC K M).relfinrank L ≤ 1 :=
      Nat.le_of_mul_le_mul_right (Nat.le_of_mul_le_mul_left hprod hpsi) hn_pos
    have h3 : (modularFunctionFieldFullC K M).relfinrank L ≠ 0 := by
      intro h0
      rw [hJE_eq, h0, zero_mul, mul_zero] at hJEpos
      exact absurd hJEpos (lt_irrefl 0)
    omega

  have hLF0 : L ≤ modularFunctionFieldFullC K M := by
    rw [IntermediateField.relfinrank_eq_finrank_of_le hF0L] at hr
    have hbot := IntermediateField.finrank_eq_one_iff.mp hr
    intro y hy
    have hy' : y ∈ IntermediateField.extendScalars hF0L := hy
    rw [hbot, IntermediateField.mem_bot] at hy'
    obtain ⟨z, rfl⟩ := hy'
    exact z.2

  have huFix : u ∈ IntermediateField.fixedField ρ.range := by
    rw [IntermediateField.mem_fixedField_iff]
    rintro _ ⟨γ, rfl⟩
    exact hu γ
  have huL : (u : LaurentSeries K) ∈ L := (IntermediateField.mem_lift u).mpr huFix
  exact hLF0 huL
/-
## SET-AF110 insertion: ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC

The two full-level function fields coincide.

`ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC` (25 pin lines): for `K` of
characteristic `ℓ` with `ℓ ∤ N` the `q`-expansion function field and the divisor-generated one are
equal — **without** the `[NeZero ℓ]` hypothesis SET-AF109E's row carries. Its pin proof is a two-case
wrapper (`ℓ = 0` → `modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero`, which is ported in
`ModularCurve/X1/FunctionFieldInclusion.lean:80`; `ℓ ≠ 0` → AF109E's `charP` row), so the row is a
*generalisation* of a port row, not a new engine.
-/
theorem ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC (K : Type*) [Field K]
    (ℓ : ℕ) [CharP K ℓ] (N : ℕ) [NeZero N] (hlN : ¬ ℓ ∣ N) :
    modularFunctionFieldC K N = modularFunctionFieldFullC K N := by
  rcases eq_or_ne ℓ 0 with hℓ | hℓ
  · subst hℓ
    have hK : CharZero K := CharP.charP_to_charZero K
    exact modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero K N
  · have hne : NeZero ℓ := ⟨hℓ⟩
    exact modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charP_pos K ℓ N hlN

/-!
## SET-AF111 insertion: the root half of the full-level dictionary

Two rows of one subject — what a root of the `N`-th modular polynomial is in the full-level function
field:

* `ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental` (309 pin
  lines, 46 declarations): for a transcendental `j₀`, the `K`-algebra homomorphisms
  `modularFunctionFieldFullC K N →ₐ[K] Ω` carrying `jqModC` to `j₀` are equivalent to the roots of
  `Φ` at `j₀`, the equivalence reading `ψ ↦ ψ (qExpand K N (jqModC K))`;
* `ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero` (189, 34): the image
  of `Φ` in `K(j)` is irreducible when `(N : K) ≠ 0`.

## Port notes

* **One block, two wires.** Both `S_` blocks open with the *same* 26 declarations (identical text,
  only the pin's generated label `P2MKcKron` / `P2MKcIgusaIrr` differs), so the port declares that
  prefix **once**, in `ModularCurve.FullLevelRoot`. The engine diff then reads **46/46** (26 + 9 + 9 +
  1 + 1) and **34/34** (26 + 7 + 1) by hash against the one copy; a second copy would be a
  `dedup --within` cluster and a FR-0274 collision.
* **The pin's attribute walls are dropped.** `attribute [-instance]
  ModularCurve.PhiGen.instNeZeroPhiGenCosetA` and the two `attribute [-simp] …` lines exist to steer
  the pin corpus's global simp set; this module's proofs are the pin's own and elaborate without them
  (measured: silent).
* **The four `scoped instance` caches are transcribed as in the pin and are inert** — the pin's
  `p2m_open` activates the scopes `Polynomial` and `IntermediateField`, never the block's own, and the
  house policy forbids installing the pin's `set_option synthInstance.maxHeartbeats 1600000`. The
  generic `IntermediateField` instances are what `synthInstance` finds.
* **Names.** Pin names; the generated namespaces `P2MW.S_…`, `P2MKcKron`, `P2MKcIgusaIrr` become the
  subject namespace `ModularCurve.FullLevelRoot`, and the two headlines keep their scaffold placement
  at root (`ModularCurve.…`). `coeffMap_injective` is **transcribed**: the port's same-named row
  (`ModularCurve/Defs/Laurent.lean:385`) binds `f` *implicitly*, which is a different statement (the
  pin's `f` is explicit, FR-0321), so it cannot be substituted.
-/

namespace ModularCurve.FullLevelRoot

open Polynomial IntermediateField
open scoped Polynomial IntermediateField

noncomputable section RootBlock

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

abbrev FF : Type _ := ↥(modularFunctionFieldFullC K N)

def jF : FF K N := ⟨jqModC K, jqModC_mem_full K N⟩

def jNF : FF K N := ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩

set_option linter.unusedSectionVars false in
@[scoped simp] theorem coe_jF : ((jF K N : FF K N) : LaurentSeries K) = jqModC K := rfl

@[scoped simp] theorem coe_jNF : ((jNF K N : FF K N) : LaurentSeries K) = jqNModC K N := rfl

abbrev Kj : IntermediateField K (FF K N) := K⟮jF K N⟯

scoped instance instAlgebraKj : Algebra K (Kj K N) := inferInstance
scoped instance instModuleKjFF : Module (Kj K N) (FF K N) := inferInstance
scoped instance instAlgebraKjFF : Algebra (Kj K N) (FF K N) := inferInstance
scoped instance instTowerKj : IsScalarTower K (Kj K N) (FF K N) := inferInstance

abbrev jKj : Kj K N := AdjoinSimple.gen K (jF K N)

abbrev PhiAt {N : ℕ} [NeZero N] (data : ModularPolynomialData N) {R : Type*} [CommRing R]
    (j₀ : R) : Polynomial R :=
  data.Φ.map (eval₂RingHom (Int.castRingHom R) j₀)

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  have := congrArg (fun z : LaurentSeries S => z.coeff k) h
  simpa using this

abbrev evalJ (R : Type*) [CommRing R] : Polynomial ℤ →+* LaurentSeries R :=
  eval₂RingHom (Int.castRingHom (LaurentSeries R)) (jqModC R)

theorem coeffMap_comp_evalJ {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (coeffMap f).comp (evalJ R) = evalJ S := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp [coeffMap_jqModC]

theorem eval₂_Phi_int (data : ModularPolynomialData N) :
    data.Φ.eval₂ (evalJ ℤ) (jqNModC ℤ N) = 0 := by
  apply coeffMap_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [Polynomial.hom_eval₂, coeffMap_comp_evalJ, coeffMap_jqNModC, map_zero]
  have hev : evalJ ℚ = evalAtJ :=
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simp [evalAtJ_X, jqModC_rat])
  rw [hev, jqNModC_rat]
  exact data.eval_eq_zero

theorem eval₂_Phi (data : ModularPolynomialData N) (R : Type*) [CommRing R] :
    data.Φ.eval₂ (evalJ R) (jqNModC R N) = 0 := by
  have h := congrArg (coeffMap (Int.castRingHom R)) (eval₂_Phi_int N data)
  rwa [Polynomial.hom_eval₂, coeffMap_comp_evalJ, coeffMap_jqNModC, map_zero] at h

theorem adjoin_pair_eq_top (hN : (N : K) ≠ 0) :
    IntermediateField.adjoin K {jF K N, jNF K N} = (⊤ : IntermediateField K (FF K N)) := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have hlN : ¬ ℓ ∣ N := fun h => hN ((CharP.cast_eq_zero_iff K ℓ N).2 h)
  have hCF := modularFunctionFieldC_eq_modularFunctionFieldFullC K ℓ N hlN
  apply IntermediateField.lift_injective
  refine (IntermediateField.lift_adjoin K _ _).trans
    (Eq.trans ?_ (IntermediateField.lift_top K _).symm)
  rw [Set.image_pair, coe_jF, coe_jNF, ← hCF]
  rfl

theorem adjoin_jNF_eq_top (hN : (N : K) ≠ 0) :
    (Kj K N)⟮jNF K N⟯ = (⊤ : IntermediateField (Kj K N) (FF K N)) := by
  apply restrictScalars_injective K
  rw [adjoin_simple_adjoin_simple, restrictScalars_top]
  exact adjoin_pair_eq_top K N hN

def adjoinEquivTop (hN : (N : K) ≠ 0) : (Kj K N)⟮jNF K N⟯ ≃ₐ[Kj K N] FF K N :=
  (equivOfEq (adjoin_jNF_eq_top K N hN)).trans topEquiv

theorem adjoinEquivTop_gen (hN : (N : K) ≠ 0) :
    adjoinEquivTop K N hN (AdjoinSimple.gen (Kj K N) (jNF K N)) = jNF K N := rfl

set_option linter.unusedSectionVars false in
theorem transcendental_jF : Transcendental K (jF K N) := by
  rw [← transcendental_algebraMap_iff
    (FaithfulSMul.algebraMap_injective (FF K N) (LaurentSeries K))]
  exact transcendental_jqModC K

abbrev PhiKj (data : ModularPolynomialData N) : Polynomial (Kj K N) := PhiAt data (jKj K N)

theorem monic_PhiKj (data : ModularPolynomialData N) : (PhiKj K N data).Monic := data.monic.map _

theorem natDegree_PhiKj (data : ModularPolynomialData N) :
    (PhiKj K N data).natDegree = dedekindPsi N := by
  rw [PhiKj, data.monic.natDegree_map, data.natDegree_eq]

set_option linter.unusedSectionVars false in
theorem algebraMap_comp_eq_evalJ :
    (algebraMap (FF K N) (LaurentSeries K)).comp ((algebraMap (Kj K N) (FF K N)).comp
        (eval₂RingHom (Int.castRingHom (Kj K N)) (jKj K N))) = evalJ K := by
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X]
  rfl

theorem aeval_jNF_PhiKj (data : ModularPolynomialData N) : aeval (jNF K N) (PhiKj K N data) = 0 := by
  apply FaithfulSMul.algebraMap_injective (FF K N) (LaurentSeries K)
  rw [map_zero, PhiKj, aeval_def, eval₂_map, Polynomial.hom_eval₂, algebraMap_comp_eq_evalJ]
  exact eval₂_Phi N data K

theorem isIntegral_jNF (data : ModularPolynomialData N) : IsIntegral (Kj K N) (jNF K N) :=
  ⟨PhiKj K N data, monic_PhiKj K N data, by rw [← aeval_def]; exact aeval_jNF_PhiKj K N data⟩

theorem finrank_Kj_FF (hN : (N : K) ≠ 0) :
    Module.finrank (Kj K N) (FF K N) = dedekindPsi N :=
  finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi K N hN

theorem minpoly_jNF (hN : (N : K) ≠ 0) (data : ModularPolynomialData N) :
    minpoly (Kj K N) (jNF K N) = PhiKj K N data := by
  have hint := isIntegral_jNF K N data
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
    (monic_PhiKj K N data) (minpoly.dvd _ _ (aeval_jNF_PhiKj K N data)) ?_).symm
  rw [natDegree_PhiKj, ← adjoin.finrank hint,
    (adjoinEquivTop K N hN).toLinearEquiv.finrank_eq, finrank_Kj_FF K N hN]

section Phi0

open scoped IntermediateField.algebraAdjoinAdjoin

def adjoinEquivPoly : Algebra.adjoin K {(jF K N)} ≃ₐ[K] K[X] :=
  ((Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval K (jF K N))).trans
    (AlgEquiv.ofInjective (aeval (jF K N))
      (transcendental_iff_injective.1 (transcendental_jF K N))).symm)

theorem adjoinEquivPoly_symm_apply (p : K[X]) :
    (((adjoinEquivPoly K N).symm p : Algebra.adjoin K {(jF K N)}) : FF K N) = aeval (jF K N) p := by
  simp [adjoinEquivPoly]

theorem adjoinEquivPoly_gen :
    adjoinEquivPoly K N ⟨jF K N, Algebra.self_mem_adjoin_singleton K _⟩ = X := by
  apply (adjoinEquivPoly K N).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  ext1
  rw [adjoinEquivPoly_symm_apply, aeval_X]

theorem adjoinEquivPoly_symm_X :
    (adjoinEquivPoly K N).symm X = ⟨jF K N, Algebra.self_mem_adjoin_singleton K _⟩ := by
  rw [← adjoinEquivPoly_gen K N, AlgEquiv.symm_apply_apply]

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

def g₀ (j₀ : Ω) : Algebra.adjoin K {(jF K N)} →ₐ[K] Ω :=
  (aeval j₀).comp (adjoinEquivPoly K N).toAlgHom

variable {j₀ : Ω}

theorem g₀_injective (hj₀ : Transcendental K j₀) : Function.Injective (g₀ K N j₀) :=
  (transcendental_iff_injective.1 hj₀).comp (adjoinEquivPoly K N).injective

def φ₀ (hj₀ : Transcendental K j₀) : Kj K N →ₐ[K] Ω :=
  IsFractionRing.liftAlgHom (g₀_injective K N hj₀)

theorem φ₀_gen (hj₀ : Transcendental K j₀) : φ₀ K N hj₀ (jKj K N) = j₀ := by
  rw [φ₀, IsFractionRing.liftAlgHom_apply, jKj, ← algebraAdjoinAdjoin.algebraMap_eq_gen_self,
    IsFractionRing.lift_algebraMap]
  show aeval j₀ (adjoinEquivPoly K N ⟨jF K N, _⟩) = j₀
  rw [adjoinEquivPoly_gen, aeval_X]

theorem algHom_Kj_ext {f g : Kj K N →ₐ[K] Ω} (h : f (jKj K N) = g (jKj K N)) : f = g := by
  apply AlgHom.coe_ringHom_injective
  refine IsFractionRing.ringHom_ext (A := Algebra.adjoin K {(jF K N)}) (fun x => ?_)
  have key : (f.comp (IsScalarTower.toAlgHom K _ (Kj K N))).comp
      ((adjoinEquivPoly K N).symm : K[X] →ₐ[K] Algebra.adjoin K {(jF K N)}) =
      (g.comp (IsScalarTower.toAlgHom K _ (Kj K N))).comp
      ((adjoinEquivPoly K N).symm : K[X] →ₐ[K] Algebra.adjoin K {(jF K N)}) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgEquiv.coe_toAlgHom,
      adjoinEquivPoly_symm_X, IsScalarTower.coe_toAlgHom',
      algebraAdjoinAdjoin.algebraMap_eq_gen_self]
    exact h
  have := congrArg (fun φ => φ (adjoinEquivPoly K N x)) key
  simpa using this

end Phi0

section Equivs

variable {Ω : Type*} [Field Ω] [Algebra K Ω] {j₀ : Ω}

@[reducible] def algebraKjΩ (hj₀ : Transcendental K j₀) : Algebra (Kj K N) Ω :=
  (φ₀ K N hj₀).toRingHom.toAlgebra

theorem algebraMap_KjΩ (hj₀ : Transcendental K j₀) (z : Kj K N) :
    @algebraMap (Kj K N) Ω _ _ (algebraKjΩ K N hj₀) z = φ₀ K N hj₀ z := rfl

theorem isScalarTower_KjΩ (hj₀ : Transcendental K j₀) : @IsScalarTower K (Kj K N) Ω _
    (algebraKjΩ K N hj₀).toSMul _ :=
  @IsScalarTower.of_algebraMap_eq K (Kj K N) Ω _ _ _ _ (algebraKjΩ K N hj₀) _
    (fun x => ((φ₀ K N hj₀).commutes x).symm)

def embEquivAlgHomKj (hj₀ : Transcendental K j₀) :
    {ψ : FF K N →ₐ[K] Ω // ψ (jF K N) = j₀} ≃
      @AlgHom (Kj K N) (FF K N) Ω _ _ _ _ (algebraKjΩ K N hj₀) :=
  letI := algebraKjΩ K N hj₀
  haveI := isScalarTower_KjΩ K N hj₀
  { toFun := fun ψ =>
      { (ψ.1 : FF K N →+* Ω) with
        commutes' := fun z => by
          have hres : ψ.1.comp (IsScalarTower.toAlgHom K (Kj K N) (FF K N)) = φ₀ K N hj₀ :=
            algHom_Kj_ext K N (by
              rw [φ₀_gen, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', jKj,
                AdjoinSimple.algebraMap_gen]
              exact ψ.2)
          exact DFunLike.congr_fun hres z }
    invFun := fun χ => ⟨χ.restrictScalars K, by
        have h := χ.commutes (jKj K N)
        rw [jKj, AdjoinSimple.algebraMap_gen] at h
        rw [AlgHom.restrictScalars_apply, h]
        exact φ₀_gen K N hj₀⟩
    left_inv := fun ψ => by ext; rfl
    right_inv := fun χ => by ext; rfl }

theorem embEquivAlgHomKj_apply (hj₀ : Transcendental K j₀)
    (ψ : {ψ : FF K N →ₐ[K] Ω // ψ (jF K N) = j₀}) (x : FF K N) :
    embEquivAlgHomKj K N hj₀ ψ x = ψ.1 x := rfl

theorem PhiKj_map (data : ModularPolynomialData N) (hj₀ : Transcendental K j₀) :
    (PhiKj K N data).map (φ₀ K N hj₀ : Kj K N →+* Ω) = PhiAt data j₀ := by
  rw [PhiKj, PhiAt, PhiAt, Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, coe_eval₂RingHom, eval₂_X]
  exact φ₀_gen K N hj₀

set_option linter.style.haveILetI false in
theorem mem_aroots_minpoly_iff (hN : (N : K) ≠ 0) (data : ModularPolynomialData N)
    (hj₀ : Transcendental K j₀) (y : Ω) :
    letI := algebraKjΩ K N hj₀
    y ∈ (minpoly (Kj K N) (jNF K N)).aroots Ω ↔ (PhiAt data j₀).IsRoot y := by
  letI := algebraKjΩ K N hj₀
  rw [minpoly_jNF K N hN data, mem_aroots', aeval_def, eval₂_eq_eval_map,
    show algebraMap (Kj K N) Ω = (φ₀ K N hj₀ : Kj K N →+* Ω) from rfl, PhiKj_map]
  exact ⟨fun h => h.2, fun h => ⟨(data.monic.map _).ne_zero, h⟩⟩

set_option linter.style.haveILetI false in
def embEquivRoots (hN : (N : K) ≠ 0) (data : ModularPolynomialData N)
    (hj₀ : Transcendental K j₀) :
    {ψ : FF K N →ₐ[K] Ω // ψ (jF K N) = j₀} ≃ {y : Ω // (PhiAt data j₀).IsRoot y} :=
  letI := algebraKjΩ K N hj₀
  (embEquivAlgHomKj K N hj₀).trans <|
    ((AlgEquiv.arrowCongr (adjoinEquivTop K N hN)
        (AlgEquiv.refl : Ω ≃ₐ[Kj K N] Ω)).symm.trans <|
      (algHomAdjoinIntegralEquiv (Kj K N) (isIntegral_jNF K N data)).trans <|
        Equiv.subtypeEquivRight (mem_aroots_minpoly_iff K N hN data hj₀))

set_option linter.style.haveILetI false in
theorem embEquivRoots_apply (hN : (N : K) ≠ 0) (data : ModularPolynomialData N)
    (hj₀ : Transcendental K j₀) (ψ : {ψ : FF K N →ₐ[K] Ω // ψ (jF K N) = j₀}) :
    ((embEquivRoots K N hN data hj₀ ψ : {y : Ω // (PhiAt data j₀).IsRoot y}) : Ω) =
      ψ.1 (jNF K N) := by
  letI := algebraKjΩ K N hj₀
  simp only [embEquivRoots, Equiv.trans_apply, Equiv.subtypeEquivRight_apply_coe]
  set E3 := algHomAdjoinIntegralEquiv (K := Ω) (Kj K N) (isIntegral_jNF K N data) with hE3
  set χ' := (AlgEquiv.arrowCongr (adjoinEquivTop K N hN)
        (AlgEquiv.refl : Ω ≃ₐ[Kj K N] Ω)).symm (embEquivAlgHomKj K N hj₀ ψ) with hχ'
  have h1 : ((E3 χ' : { x // x ∈ (minpoly (Kj K N) (jNF K N)).aroots Ω }) : Ω) =
      χ' (AdjoinSimple.gen (Kj K N) (jNF K N)) := by
    conv_rhs => rw [← E3.symm_apply_apply χ']
    rw [hE3, algHomAdjoinIntegralEquiv_symm_apply_gen]
  rw [h1, hχ']
  rfl

end Equivs

theorem exists_equiv (hN : (N : K) ≠ 0) (data : ModularPolynomialData N)
    (Ω : Type*) [Field Ω] [Algebra K Ω] (j₀ : Ω) (hj₀ : Transcendental K j₀) :
    ∃ e : {ψ : modularFunctionFieldFullC K N →ₐ[K] Ω // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = j₀} ≃
        {y : Ω // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) j₀)).IsRoot y},
      ∀ ψ, ((e ψ : {y : Ω //
          (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) j₀)).IsRoot y}) : Ω) =
        ψ.1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩ :=
  ⟨embEquivRoots K N hN data hj₀, embEquivRoots_apply K N hN data hj₀⟩

def phi0 : RatFunc K →ₐ[K] FF K N :=
  RatFunc.liftAlgHom (Polynomial.aeval (jF K N)) fun _ hp =>
    mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero hp
      (transcendental_iff_injective.1 (transcendental_jF K N) (h.trans (map_zero _).symm))

private theorem phi0_apply_div (f : RatFunc K) :
    phi0 K N f = aeval (jF K N) (RatFunc.num f) / aeval (jF K N) (RatFunc.denom f) :=
  RatFunc.liftAlgHom_apply _ _ f

theorem phi0_algebraMap (p : K[X]) : phi0 K N (algebraMap K[X] (RatFunc K) p) = aeval (jF K N) p := by
  rw [phi0]
  exact RatFunc.liftRingHom_algebraMap _ _ p

theorem phi0_X : phi0 K N (algebraMap K[X] (RatFunc K) X) = jF K N := by
  rw [phi0_algebraMap, aeval_X]

theorem fieldRange_phi0 : (phi0 K N).fieldRange = Kj K N := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    change phi0 K N f ∈ Kj K N
    rw [phi0_apply_div]
    refine div_mem ?_ ?_ <;>
      exact algebra_adjoin_le_adjoin K _ (Polynomial.aeval_mem_adjoin_singleton K _)
  · rw [adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨_, phi0_X K N⟩

def ratFuncEquiv : RatFunc K ≃ₐ[K] Kj K N :=
  (AlgEquiv.ofInjectiveField (phi0 K N)).trans (equivOfEq (fieldRange_phi0 K N))

theorem ratFuncEquiv_apply_coe (f : RatFunc K) : ((ratFuncEquiv K N f : Kj K N) : FF K N) = phi0 K N f :=
  rfl

theorem ratFuncEquiv_X : ratFuncEquiv K N (algebraMap K[X] (RatFunc K) X) = jKj K N := by
  ext1
  rw [ratFuncEquiv_apply_coe, phi0_X]
  rfl

end RootBlock

end ModularCurve.FullLevelRoot

open ModularCurve.FullLevelRoot in
/-
## SET-AF111 insertion: ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental

Every root of the `j`-polynomial is the `q`-expansion of a function-field homomorphism.

`ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental` (309 pin lines):
for a transcendental `j`-invariant and a root of its `N`-th modular polynomial, there is a `K`-algebra
homomorphism from the full-level function field into `LaurentSeries K` sending `jqModC` to it — the *root*
half of the full-level slot dictionary whose slot half order B lands.
-/
theorem ModularCurve.exists_equiv_algHom_modularFunctionFieldFullC_isRoot_of_transcendental
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) (data : ModularPolynomialData N)
    (Ω : Type*) [Field Ω] [Algebra K Ω] (j₀ : Ω) (hj₀ : Transcendental K j₀) :
    ∃ e : {ψ : modularFunctionFieldFullC K N →ₐ[K] Ω // ψ ⟨jqModC K, jqModC_mem_full K N⟩ = j₀} ≃
        {y : Ω // (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) j₀)).IsRoot y},
      ∀ ψ, ((e ψ : {y : Ω //
          (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) j₀)).IsRoot y}) : Ω) =
        ψ.1 ⟨qExpand K N (jqModC K), jqModCd_mem_full K N dvd_rfl⟩ :=
  exists_equiv K N hN data Ω j₀ hj₀

open ModularCurve.FullLevelRoot in
/-
## SET-AF111 insertion: ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero

The modular polynomial's image in the rational function field is irreducible.

`ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero` (189 pin lines, 34
declarations): for a `ModularPolynomialData ℓ` with `(ℓ : K) ≠ 0`, the image of `Φ` in `K(j)` is
irreducible — the separability form the full-level dictionary needs, and the `ℓ`-general companion of the
`ℓ = 2` fibre module.
-/
theorem ModularCurve.ModularPolynomialData.irreducible_map_ratFunc_of_natCast_ne_zero
    (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (hNK : (N : K) ≠ 0) :
    Irreducible ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))) := by
  have hirr : Irreducible (PhiKj K N data) := by
    rw [← minpoly_jNF K N hNK data]
    exact minpoly.irreducible (isIntegral_jNF K N data)
  set e := ratFuncEquiv K N
  rw [← MulEquiv.irreducible_iff (Polynomial.mapEquiv (e : RatFunc K ≃+* Kj K N))]
  convert hirr using 1
  rw [Polynomial.mapEquiv_apply, Polynomial.map_map, Polynomial.map_map]
  refine congrArg (fun f => data.Φ.map f) (Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.map_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  exact ratFuncEquiv_X K N

