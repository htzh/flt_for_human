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

