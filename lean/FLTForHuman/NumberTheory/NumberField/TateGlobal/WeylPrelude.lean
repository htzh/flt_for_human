/-
  The shared Weyl-integrand prelude: the pieces of the pin's `LocalZetaUnramified` /
  `ValuedOrdBridge` / `WeylGK` sections that the `AutomorphicForm.LocalIntertwining`
  files re-carry and the T1 port did not need.

  These declarations are shared by the two `S_` files
  `S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean`
  and `S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean`
  (and by the rest of that 19-node cluster), and every one of them is written once here
  rather than per consumer. Pin provenance is on each declaration; the port's names are
  kept (`ValuationOrd.ord` is `IsDiscreteValuationRing.ord`).

  Tier 3 for now: the module is built and verified by `lake`, but it is not in the
  checker's `PORT_FILES` until the pin `S_` files that carry these names join `SOURCES`
  (that happens with the first `LocalIntertwining` set).
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.MulHaar
import FLTForHuman.NumberTheory.NumberField.TateGlobal.ValuedOrdBridge
import FLTForHuman.NumberTheory.NumberField.TateGlobal.DistribHaarChar
import FLTForHuman.LanglandsTunnell.TateLocalZeta
import FLTForHuman.NumberTheory.FrobeniusDensity.PrimeSums

set_option autoImplicit false

noncomputable section

namespace NumberField

namespace TateGlobal

namespace WeylPrelude

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open scoped NNReal ENNReal Pointwise
open LocalZetaUnramified MulHaarFromAdditive ValuedOrdBridge
open LanglandsTunnell.TateLocal

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

-- pin: normQ (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:592)
abbrev normQ (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0)

-- pin: modulus_coe_units_adicCompletion (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:595)
theorem modulus_coe_units_adicCompletion (u : (v.adicCompletion F)ˣ) :
    modulus (u : v.adicCompletion F)
      = normQ v ^ (-(IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)
          (Additive.ofMul u))) := by
  rw [modulus_coe_units]
  exact LocalHaarModulus.distribHaarChar_adicCompletion u

-- pin: modulus_of_ne_zero_adicCompletion (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:600)
theorem modulus_of_ne_zero_adicCompletion {x : v.adicCompletion F} (hx : x ≠ 0) :
    modulus x = normQ v ^ (-(IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)
      (Additive.ofMul (Units.mk0 x hx)))) := by
  rw [modulus_of_ne_zero hx]
  exact LocalHaarModulus.distribHaarChar_adicCompletion (Units.mk0 x hx)

variable {ϖ : v.adicCompletionIntegers F}

-- pin: shellSet_subset_compl_zero (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:772)
theorem shellSet_subset_compl_zero (hϖ : Irreducible ϖ) (k : ℕ) :
    shellSet hϖ k ⊆ ({0}ᶜ : Set (v.adicCompletion F)) :=
  fun _ hx hx0 => zero_notMem_shellSet hϖ k ((Set.mem_singleton_iff.mp hx0) ▸ hx)

-- pin: shellSet_disjoint (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:776)
theorem shellSet_disjoint (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint (shellSet hϖ)) := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun x hx hx' => hkk' ?_
  have hx0 : x ≠ 0 := fun h => zero_notMem_shellSet hϖ k (h ▸ hx)
  have h1 := (mem_shellSet_iff_ord_eq hϖ k hx0).mp hx
  have h2 := (mem_shellSet_iff_ord_eq hϖ k' hx0).mp hx'
  exact_mod_cast h1.symm.trans h2

-- pin: one_le_normQ (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:811)
theorem one_le_normQ : (1 : ℝ≥0) ≤ normQ v := by
  have h1 : 1 ≤ Ideal.absNorm v.asIdeal := FrobeniusDensity.one_le_absNorm v.ne_bot
  exact_mod_cast h1

-- pin: modulus_of_mem_shellSet (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:860)
theorem modulus_of_mem_shellSet (hϖ : Irreducible ϖ) {k : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ shellSet hϖ k) : modulus x = (normQ v ^ (-(k : ℤ)) : ℝ≥0) := by
  have hx0 : x ≠ 0 := fun h => zero_notMem_shellSet hϖ k (h ▸ hx)
  rw [modulus_of_ne_zero_adicCompletion hx0, (mem_shellSet_iff_ord_eq hϖ k hx0).mp hx]

-- pin: coe_mem_integers_iff_ord_nonneg (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1698)
theorem coe_mem_integers_iff_ord_nonneg (x : (v.adicCompletion F)ˣ) :
    ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      ↔ 0 ≤ IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul x) := by
  rw [mem_adicCompletionIntegers, valued_coe_units_eq_exp_neg_ord, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

-- pin: valued_eq_one_of_ord_eq_zero (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1725)
theorem valued_eq_one_of_ord_eq_zero (u : (v.adicCompletion F)ˣ)
    (hu : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul u) = 0) :
    Valued.v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
  rw [valued_coe_units_eq_exp_neg_ord, hu, neg_zero, WithZero.exp_zero]

-- pin: ord_eq_one_of_valued (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1730)
theorem ord_eq_one_of_valued (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v ((ϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = Multiplicative.ofAdd (-1 : ℤ)) :
    IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul ϖ) = 1 := by
  have h := valued_coe_units_eq_exp_neg_ord ϖ
  rw [hϖ] at h
  have h' : WithZero.exp (-1 : ℤ)
      = WithZero.exp (-(IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)
          (Additive.ofMul ϖ))) := h
  have h'' := WithZero.exp_injective h'
  omega

variable {χ : (v.adicCompletion F)ˣ →* ℂˣ}

-- pin: char_eq_one_of_ord_eq_zero (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1744)
theorem char_eq_one_of_ord_eq_zero
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (u : (v.adicCompletion F)ˣ)
    (hu : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul u) = 0) :
    χ u = 1 :=
  hχ u (valued_eq_one_of_ord_eq_zero u hu)

variable {π : v.adicCompletionIntegers F}

-- pin: char_eq_zpow_of_ord (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1751)
theorem char_eq_zpow_of_ord (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (x : (v.adicCompletion F)ˣ) (k : ℤ)
    (hk : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul x) = k) :
    χ x = χ (piUnit hπ) ^ k := by
  have hu : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)
      (Additive.ofMul ((piUnit hπ ^ k)⁻¹ * x)) = 0 := by
    rw [ord_ofMul_mul, show ((piUnit hπ ^ k)⁻¹ : (v.adicCompletion F)ˣ) = piUnit hπ ^ (-k) from
      (zpow_neg _ _).symm, ord_ofMul_zpow_piUnit hπ, hk]
    ring
  have hx : x = piUnit hπ ^ k * ((piUnit hπ ^ k)⁻¹ * x) := by rw [mul_inv_cancel_left]
  calc χ x = χ (piUnit hπ ^ k * ((piUnit hπ ^ k)⁻¹ * x)) := by rw [← hx]
    _ = χ (piUnit hπ) ^ k * 1 := by rw [map_mul, map_zpow, char_eq_one_of_ord_eq_zero hχ _ hu]
    _ = χ (piUnit hπ) ^ k := mul_one _

-- pin: char_eq_char_piUnit (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1770)
theorem char_eq_char_piUnit (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (ϖ : (v.adicCompletion F)ˣ)
    (hϖ : Valued.v ((ϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = Multiplicative.ofAdd (-1 : ℤ)) :
    χ ϖ = χ (piUnit hπ) := by
  rw [char_eq_zpow_of_ord hπ hχ ϖ 1 (ord_eq_one_of_valued ϖ hϖ), zpow_one]

-- pin: negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1785)
def negShell (hπ : Irreducible π) (m : ℕ) : Set (v.adicCompletion F) :=
  genShell hπ (-((m : ℤ) + 1))

-- pin: ne_zero_of_mem_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1788)
theorem ne_zero_of_mem_negShell (hπ : Irreducible π) {m : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ negShell hπ m) : x ≠ 0 := by
  have h : x ∈ ⋃ k : ℤ, genShell hπ k := Set.mem_iUnion.mpr ⟨_, hx⟩
  rw [iUnion_genShell hπ] at h
  exact h

-- pin: ord_of_mem_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1794)
theorem ord_of_mem_negShell (hπ : Irreducible π) {m : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ negShell hπ m) (hx0 : x ≠ 0) :
    IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul (Units.mk0 x hx0))
      = -((m : ℤ) + 1) :=
  (mem_genShell_iff hπ hx0).mp hx

-- pin: compl_integers_eq_iUnion_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1798)
theorem compl_integers_eq_iUnion_negShell (hπ : Irreducible π) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ = ⋃ m : ℕ, negShell hπ m := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · intro hxO
    have hx0 : x ≠ 0 := by
      intro h0
      exact hxO (h0 ▸ (v.adicCompletionIntegers F).zero_mem)
    have hord : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)
        (Additive.ofMul (Units.mk0 x hx0)) < 0 := by
      by_contra hge
      exact hxO ((coe_mem_integers_iff_ord_nonneg (Units.mk0 x hx0)).mpr (not_lt.mp hge))
    refine ⟨(-(IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)
        (Additive.ofMul (Units.mk0 x hx0))) - 1).toNat,
      (mem_genShell_iff hπ hx0).mpr ?_⟩
    omega
  · rintro ⟨m, hm⟩ hxO
    have hx0 : x ≠ 0 := ne_zero_of_mem_negShell hπ hm
    have h1 := ord_of_mem_negShell hπ hm hx0
    have h2 := (coe_mem_integers_iff_ord_nonneg (Units.mk0 x hx0)).mp hxO
    omega

-- pin: negShell_disjoint (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1820)
theorem negShell_disjoint (hπ : Irreducible π) :
    Pairwise (Function.onFun Disjoint (negShell hπ)) := by
  intro m m' hmm'
  have h : (-((m : ℤ) + 1)) ≠ (-((m' : ℤ) + 1)) := by
    intro h
    apply hmm'
    omega
  exact genShell_disjoint hπ h

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

-- pin: measurableSet_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1831)
theorem measurableSet_negShell (hπ : Irreducible π) (m : ℕ) : MeasurableSet (negShell hπ m) :=
  measurableSet_genShell hπ _

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in
-- pin: modulus_of_mem_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1835)
theorem modulus_of_mem_negShell (hπ : Irreducible π) {m : ℕ} {x : v.adicCompletion F}
    (hx : x ∈ negShell hπ m) : modulus x = normQ v ^ (m + 1) := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_negShell hπ hx
  rw [modulus_of_ne_zero_adicCompletion hx0, ord_of_mem_negShell hπ hx hx0, neg_neg,
    show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

-- pin: eulerVar (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:921)
def eulerVar (ϖ : v.adicCompletionIntegers F) (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  charExt χ ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
    * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ (-s)

end WeylPrelude

end TateGlobal

end NumberField
