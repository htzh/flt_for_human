/-
  The local constants at a place: conductor, `L`-factor and epsilon factor.

  `higherUnitsAt K v n` is the `n`-th higher unit group `1 + ϖⁿ𝒪` of the completion,
  `HasConductorExponentAt χ c` says the character `χ` is trivial on `1 + ϖᶜ𝒪` and
  non-trivial on every smaller one, and `conductorExponentAt χ` is the (unique) `c`;
  `localLFactorAt` is `1` for a ramified character and `(1 - χ(ϖ) q^{-s})⁻¹` for an
  unramified one, and `localEpsilonAt` is `localGammaAt · L(χ) / L(χ⁻¹)`.

  Transcribed whole from `Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean`
  (pinned `aa2d8b3`, 155 lines, 18 declarations), which has no `Theorems/` wrapper, so
  the module is its own statement authority and is listed in the checker for a
  whole-module diff. It is the definition gate of the local twisted-integral set
  (`topics/numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md`): the
  `EisensteinGeneral.LocalRam`/`LocalUnr` statements quantify over
  `higherUnitsAt F v c`.

  The pin's two imports are the port's `LanglandsTunnell/TateLocalZeta.lean`
  (`modulus`, `charExt`, `localZeta`, `localGammaAt`, …) and
  `NumberField/AdelicLevel/HeckeGen.lean` (`uniformizerUnit`, from the pin's
  `Def_NumberField_AdelicLevel`); the pin's file-level `namespace`, `variable (K v)`
  block and `section Epsilon` are kept verbatim. No statement is changed.
-/
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.TateLocal

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

-- pin: higherUnitsAt (Def_LanglandsTunnell_TateLocalConstantsAt.lean:15)
def higherUnitsAt (n : ℕ) : Set (v.adicCompletion K)ˣ :=
  {u | Valued.v (u : v.adicCompletion K) = 1 ∧
    (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)))}

-- pin: mem_higherUnitsAt_iff (Def_LanglandsTunnell_TateLocalConstantsAt.lean:19)
theorem mem_higherUnitsAt_iff {n : ℕ} {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v n ↔ Valued.v (u : v.adicCompletion K) = 1 ∧
      (n = 0 ∨ Valued.v ((u : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ))) :=
  Iff.rfl

-- pin: mem_higherUnitsAt_zero_iff (Def_LanglandsTunnell_TateLocalConstantsAt.lean:24)
theorem mem_higherUnitsAt_zero_iff {u : (v.adicCompletion K)ˣ} :
    u ∈ higherUnitsAt K v 0 ↔ Valued.v (u : v.adicCompletion K) = 1 := by
  simp [mem_higherUnitsAt_iff]

-- pin: one_mem_higherUnitsAt (Def_LanglandsTunnell_TateLocalConstantsAt.lean:28)
theorem one_mem_higherUnitsAt (n : ℕ) : (1 : (v.adicCompletion K)ˣ) ∈ higherUnitsAt K v n := by
  refine ⟨by simp, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl h
  · right
    simp only [Units.val_one, sub_self, map_zero]
    exact zero_le

-- pin: higherUnitsAt_antitone (Def_LanglandsTunnell_TateLocalConstantsAt.lean:36)
theorem higherUnitsAt_antitone : Antitone (higherUnitsAt K v) := by
  intro m n hmn u hu
  obtain ⟨hval, hball⟩ := hu
  refine ⟨hval, ?_⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · exact Or.inl hm
  · right
    rcases hball with hn0 | hle
    · omega
    · exact hle.trans (WithZero.exp_le_exp.mpr (by omega))

-- pin: HasConductorExponentAt (Def_LanglandsTunnell_TateLocalConstantsAt.lean:47)
def HasConductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (c : ℕ) : Prop :=
  (∀ u ∈ higherUnitsAt K v c, χ u = 1) ∧ ∀ m < c, ∃ u ∈ higherUnitsAt K v m, χ u ≠ 1

-- pin: hasConductorExponentAt_zero_iff (Def_LanglandsTunnell_TateLocalConstantsAt.lean:50)
theorem hasConductorExponentAt_zero_iff {χ : (v.adicCompletion K)ˣ →* ℂˣ} :
    HasConductorExponentAt K v χ 0 ↔
      ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 → χ u = 1 := by
  constructor
  · intro h u hu
    exact h.1 u ((mem_higherUnitsAt_zero_iff K v).mpr hu)
  · intro h
    exact ⟨fun u hu => h u ((mem_higherUnitsAt_zero_iff K v).mp hu),
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩

-- pin: hasConductorExponentAt_unique (Def_LanglandsTunnell_TateLocalConstantsAt.lean:60)
theorem hasConductorExponentAt_unique {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c c' : ℕ}
    (h : HasConductorExponentAt K v χ c) (h' : HasConductorExponentAt K v χ c') : c = c' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨u, hu, hne1⟩ := h'.2 c hlt
    exact hne1 (h.1 u hu)
  · obtain ⟨u, hu, hne1⟩ := h.2 c' hgt
    exact hne1 (h'.1 u hu)

-- pin: hasConductorExponentAt_one_zero (Def_LanglandsTunnell_TateLocalConstantsAt.lean:69)
theorem hasConductorExponentAt_one_zero :
    HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) 0 :=
  (hasConductorExponentAt_zero_iff K v).mpr fun _ _ => rfl

-- pin: not_hasConductorExponentAt_one_succ (Def_LanglandsTunnell_TateLocalConstantsAt.lean:73)
theorem not_hasConductorExponentAt_one_succ (c : ℕ) :
    ¬ HasConductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) (c + 1) := by
  rintro ⟨-, hmin⟩
  obtain ⟨u, -, hne⟩ := hmin c (Nat.lt_succ_self c)
  exact hne rfl

-- pin: conductorExponentAt (Def_LanglandsTunnell_TateLocalConstantsAt.lean:79)
def conductorExponentAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) : ℕ :=
  sInf {c | HasConductorExponentAt K v χ c}

-- pin: conductorExponentAt_eq_of_hasConductorExponentAt (Def_LanglandsTunnell_TateLocalConstantsAt.lean:82)
theorem conductorExponentAt_eq_of_hasConductorExponentAt {χ : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ}
    (h : HasConductorExponentAt K v χ c) : conductorExponentAt K v χ = c := by
  have hmem : c ∈ {c' | HasConductorExponentAt K v χ c'} := h
  have hle : conductorExponentAt K v χ ≤ c := Nat.sInf_le hmem
  have hge : c ≤ conductorExponentAt K v χ := by
    have hne : {c' | HasConductorExponentAt K v χ c'}.Nonempty := ⟨c, h⟩
    have hmemInf := Nat.sInf_mem hne
    exact (hasConductorExponentAt_unique K v hmemInf h).ge
  omega

-- pin: conductorExponentAt_one (Def_LanglandsTunnell_TateLocalConstantsAt.lean:92)
@[simp] theorem conductorExponentAt_one :
    conductorExponentAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) = 0 :=
  conductorExponentAt_eq_of_hasConductorExponentAt K v (hasConductorExponentAt_one_zero K v)

open Classical in

-- pin: localLFactorAt (Def_LanglandsTunnell_TateLocalConstantsAt.lean:98)
def localLFactorAt (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  if HasConductorExponentAt K v χ 0 then
    (1 - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹
  else 1

-- pin: localLFactorAt_of_hasConductorExponentAt_zero (Def_LanglandsTunnell_TateLocalConstantsAt.lean:103)
theorem localLFactorAt_of_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : HasConductorExponentAt K v χ 0) (s : ℂ) :
    localLFactorAt K v χ s
      = (1 - (χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt, ite_eq_left hχ]

-- pin: localLFactorAt_of_not_hasConductorExponentAt_zero (Def_LanglandsTunnell_TateLocalConstantsAt.lean:109)
theorem localLFactorAt_of_not_hasConductorExponentAt_zero {χ : (v.adicCompletion K)ˣ →* ℂˣ}
    (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) : localLFactorAt K v χ s = 1 := by
  rw [localLFactorAt, ite_eq_right hχ]

-- pin: localLFactorAt_one (Def_LanglandsTunnell_TateLocalConstantsAt.lean:113)
theorem localLFactorAt_one (s : ℂ) :
    localLFactorAt K v (1 : (v.adicCompletion K)ˣ →* ℂˣ) s
      = (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹ := by
  rw [localLFactorAt_of_hasConductorExponentAt_zero K v (hasConductorExponentAt_one_zero K v),
    MonoidHom.one_apply, Units.val_one, one_mul]

section Epsilon

variable [MeasurableSpace (v.adicCompletion K)]

-- pin: localEpsilonAt (Def_LanglandsTunnell_TateLocalConstantsAt.lean:123)
def localEpsilonAt (μ : Measure (v.adicCompletion K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localGammaAt μ ψ f χ s * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s)

-- pin: localEpsilonAt_def (Def_LanglandsTunnell_TateLocalConstantsAt.lean:127)
theorem localEpsilonAt_def (μ : Measure (v.adicCompletion K)) (ψ : AddChar (v.adicCompletion K) ℂ)
    (f : v.adicCompletion K → ℂ) (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) :
    localEpsilonAt K v μ ψ f χ s
      = localGammaAt μ ψ f χ s * localLFactorAt K v χ s / localLFactorAt K v χ⁻¹ (1 - s) :=
  rfl

-- pin: localEpsilonAt_of_not_hasConductorExponentAt_zero (Def_LanglandsTunnell_TateLocalConstantsAt.lean:133)
theorem localEpsilonAt_of_not_hasConductorExponentAt_zero (μ : Measure (v.adicCompletion K))
    (ψ : AddChar (v.adicCompletion K) ℂ) (f : v.adicCompletion K → ℂ)
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hχ : ¬ HasConductorExponentAt K v χ 0) (s : ℂ) :
    localEpsilonAt K v μ ψ f χ s = localGammaAt μ ψ f χ s := by
  have hχ' : ¬ HasConductorExponentAt K v χ⁻¹ 0 := fun h => hχ <| by
    rw [hasConductorExponentAt_zero_iff] at h ⊢
    intro u hu
    have := h u hu
    rwa [MonoidHom.inv_apply, inv_eq_one] at this
  rw [localEpsilonAt, localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ,
    localLFactorAt_of_not_hasConductorExponentAt_zero K v hχ', mul_one, div_one]

-- pin: localEpsilonAt_eq_zero_of_localZeta_eq_zero (Def_LanglandsTunnell_TateLocalConstantsAt.lean:145)
theorem localEpsilonAt_eq_zero_of_localZeta_eq_zero {μ : Measure (v.adicCompletion K)}
    {ψ : AddChar (v.adicCompletion K) ℂ} {f : v.adicCompletion K → ℂ}
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} {s : ℂ} (h : localZeta μ f χ s = 0) :
    localEpsilonAt K v μ ψ f χ s = 0 := by
  rw [localEpsilonAt, localGammaAt_eq_zero_of_localZeta_eq_zero h, zero_mul, zero_div]

end Epsilon

end LanglandsTunnell.TateLocal

end
