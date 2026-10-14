/-
  The `IsInducedSection` pair: the adelic-height power section and its pointwise form.

  Two pin nodes, one story. Node 7248, the headline
  `AutomorphicForm.isInducedSection_adelicHeight_cpow`: the modulus character
  `α = distribHaarChar` is positive, the trivial character is unitary, and for every
  positivity witness `hα` and `s : ℂ` the function `g ↦ adelicHeight F g ^ (s + 1/2)` is a
  Borel-induced flat section for the character pair `(etaFst 1 α hα s, etaSnd 1 α hα s)`.
  Node 7220, the headline
  `AutomorphicForm.IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul`:
  the induced-section law evaluated at global Borel points and at unipotents.

  The pin `S_` files are transcribed whole, in the pin's namespace shape: the outer mangled
  `P2MW.S_<stem>` chapters become `AutomorphicForm` (node 1) and
  `AutomorphicForm.IsInducedSection` (node 2), and the inner `P6B.JE2aFlat` chapters are kept.
  Node 1 keeps all of its pin-public helpers (they are the checker's surface); only its
  one `private` local lemma `coe_mul` stays `private`.

  Reuse, do not re-prove (`FLTForHuman/NumberTheory/AdelicHaar/AdelicModulus.lean`, tier 3):
  `P6B.JE2aFlat.{norm_finComp_eventually_eq_one, finComp_ne_zero, finComp_mul_finComp_inv}`
  and `P6B.JE2aFlat.hasFiniteMulSupport_norm_finComp`; the pin's four local copies are dropped.
  `placeModulus` is kept as a local `def` — the pin's explicit product over the places, equal
  to the already-homed copy (and to `ideleNorm`) only by
  `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm`, never
  definitionally — so it is *not* replaced by an import.

  Everything else is homed and imported: `IsInducedSection`/`isInducedSection_unipotent_mul`
  (`AutomorphicForm/Adelic/InducedSection.lean`), `etaFst`/`etaSnd` and their class-character
  lemmas (`AutomorphicForm/Adelic/EtaFamily.lean`), `IsUnitaryChar`
  (`AutomorphicForm/Adelic/LsXi.lean`), `HasArchType`/`adelicArchGLInclAt`/`archGLIncl` and the
  component receipts (`AutomorphicForm/Adelic/ArchType.lean`), `rowIsometrySubgroup`/
  `archHeight_mul_rowIsometry` (`AutomorphicForm/Adelic/WindowedSiegel/RowIsometry.lean`), the
  upper-triangular coordinate lemmas (`AutomorphicForm/Adelic/WindowedSiegel/Coordinates.lean`),
  `isArchKFinite_of_hasArchType` (`AutomorphicForm/Adelic/ArchKFinite.lean`), the heights
  (`NumberTheory/AdelicHeight.lean`), `adelicBorel`/`globalPoints` (`AutomorphicForm/Adelic/BorelSubgroup.lean`),
  and the modulus product formula (`NumberTheory/AdelicModulus.lean`).

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`);
  port mathlib `v4.34.0`.
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul.lean
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Coordinates
import FLTForHuman.NumberTheory.AdelicHaar.AdelicModulus
import FLTForHuman.NumberTheory.AdelicHeight
import FLTForHuman.NumberTheory.AdelicModulus

set_option autoImplicit false

open NumberField IsDedekindDomain
open NumberField.AdelicHeight NumberField.AdelicLevel
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates

namespace AutomorphicForm

section RINHFold_JE2aFlatLocal

noncomputable section

namespace P6B
namespace JE2aFlat

section Local

variable {K : Type*} [NormedField K]

-- pin: coe_mul (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:28)
private theorem coe_mul (γ g : GL (Fin 2) K) :
    ((γ * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (γ : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl

-- pin: upper_mul_apply_one (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:32)
theorem upper_mul_apply_one {s : GL (Fin 2) K} (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (g : GL (Fin 2) K) (j : Fin 2) :
    ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j
      = (s : Matrix (Fin 2) (Fin 2) K) 1 1 * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
  rw [coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h10, zero_mul, zero_add]

-- pin: rowMaxNorm_upper_mul (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:38)
theorem rowMaxNorm_upper_mul {s : GL (Fin 2) K} (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (g : GL (Fin 2) K) :
    rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖(s : Matrix (Fin 2) (Fin 2) K) 1 1‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowMaxNorm
  rw [upper_mul_apply_one h10 g 0, upper_mul_apply_one h10 g 1, norm_mul, norm_mul,
    mul_max_of_nonneg _ _ (norm_nonneg _)]

-- pin: finLocalHeight_upper_entries_mul (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:46)
theorem finLocalHeight_upper_entries_mul {s : GL (Fin 2) K} {a t : K} (ht : t ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = a)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t)
    (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = ‖a‖ / ‖t‖ * finLocalHeight g := by
  have ht0 : (0 : ℝ) < ‖t‖ := norm_pos_iff.2 ht
  have hr0 : (0 : ℝ) < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := rowMaxNorm_pos g
  unfold finLocalHeight
  rw [AutomorphicForm.SiegelCoordinates.det_upper_entries_mul h00 h10 h11 g,
    rowMaxNorm_upper_mul h10 g, h11, norm_mul, norm_mul, mul_pow]
  field_simp

variable [IsUltrametricDist K]

-- pin: rowMaxNorm_mul_le (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:61)
theorem rowMaxNorm_mul_le (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hentry : ∀ j : Fin 2,
      ‖((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 j‖
        ≤ rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    intro j
    rw [coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 0 j)).trans (le_max_left _ _)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 1 j)).trans (le_max_right _ _)
  exact max_le (hentry 0) (hentry 1)

-- pin: rowMaxNorm_mul_integral (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:77)
theorem rowMaxNorm_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  refine le_antisymm (rowMaxNorm_mul_le g k hk) ?_
  have h := rowMaxNorm_mul_le (g * k) k⁻¹ hk'
  rwa [mul_inv_cancel_right] at h

-- pin: norm_det_eq_one_of_integral (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:86)
theorem norm_det_eq_one_of_integral (k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖
      * ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← coe_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      norm_one]
  refine le_antisymm hd ?_
  by_contra hlt
  push Not at hlt
  have := (mul_le_of_le_one_right (norm_nonneg _) hd').trans_lt hlt
  rw [hprod] at this
  exact lt_irrefl _ this

-- pin: finLocalHeight_mul_integral (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:103)
theorem finLocalHeight_mul_integral (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  unfold finLocalHeight
  rw [rowMaxNorm_mul_integral g k hk hk', coe_mul, Matrix.det_mul, norm_mul,
    norm_det_eq_one_of_integral k hk hk', mul_one]

end Local

end P6B.JE2aFlat

end

end RINHFold_JE2aFlatLocal

section RINHFold_JE2aFlatAdelic

noncomputable section

namespace P6B
namespace JE2aFlat

variable (F : Type) [Field F] [NumberField F]

-- pin: placeModulus (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:133)
def placeModulus (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  (∏ w : InfinitePlace F, ‖(x : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult)
    * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : AdeleRing (𝓞 F) F).2 v‖

variable {F}

-- pin: archComp_ne_zero (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:152)
theorem archComp_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (x : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  intro h0
  have h : ((x : AdeleRing (𝓞 F) F) * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 w = 1 := by
    rw [x.mul_inv]; rfl
  rw [show ((x : AdeleRing (𝓞 F) F) * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 w
      = (x : AdeleRing (𝓞 F) F).1 w * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      from rfl, h0, zero_mul] at h
  exact zero_ne_one h

-- pin: placeModulus_pos (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:184)
theorem placeModulus_pos (x : (AdeleRing (𝓞 F) F)ˣ) : 0 < placeModulus F x := by
  unfold placeModulus
  refine mul_pos (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (archComp_ne_zero x w)) _) ?_
  exact finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos)
    fun v => norm_pos_iff.mpr (P6B.JE2aFlat.finComp_ne_zero x v)

-- pin: finHeight_upper_mul (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:190)
theorem finHeight_upper_mul (s g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (h10 : (s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = 0)
    (ht : ∀ v : HeightOneSpectrum (𝓞 F),
      (s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v ≠ 0) :
    finHeight F (s * g)
      = (∏ᶠ v : HeightOneSpectrum (𝓞 F),
          ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 v‖
            / ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v‖)
        * finHeight F g := by
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      finLocalHeight (finComponent (𝓞 F) F v (s * g))
        = ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 v‖
            / ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v‖
          * finLocalHeight (finComponent (𝓞 F) F v g) := by
    intro v
    rw [map_mul]
    exact finLocalHeight_upper_entries_mul (ht v) (finComponent_apply _ _ v s 0 0)
      (by rw [finComponent_apply, h10]; rfl) (finComponent_apply _ _ v s 1 1) _
  have hg := hasFiniteMulSupport_finLocalHeight g
  have hsg := hasFiniteMulSupport_finLocalHeight (s * g)
  have hc : (fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 0 0 v‖
        / ‖(s : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v‖).HasFiniteMulSupport := by
    refine (hsg.union hg).subset fun v hv => ?_
    by_contra hv'
    simp only [Set.mem_union, Function.mem_mulSupport, not_or, not_not] at hv'
    have := hloc v
    rw [hv'.1, hv'.2, mul_one] at this
    exact hv this.symm
  unfold finHeight
  rw [← finprod_mul_distrib hc hg]
  exact finprod_congr hloc

-- pin: archHeight_upper_mul (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:225)
theorem archHeight_upper_mul (s g : GL (Fin 2) (InfiniteAdeleRing F))
    (h10 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0)
    (ht : ∀ w : InfinitePlace F, (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1 w ≠ 0) :
    archHeight F (s * g)
      = (∏ w : InfinitePlace F,
          (‖(s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0 w‖
            / ‖(s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1 w‖) ^ w.mult)
        * archHeight F g := by
  unfold archHeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_mul, localHeight_upper_entries_mul (ht w) (archComponent_apply F w s 0 0)
    (by rw [archComponent_apply, h10]; rfl) (archComponent_apply F w s 1 1) _, mul_pow]

-- pin: adelicHeight_borel_mul (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:239)
theorem adelicHeight_borel_mul (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F)
    (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (b * g)
      = placeModulus F (borelDiagFst ⟨b, hb⟩) / placeModulus F (borelDiagSnd ⟨b, hb⟩)
        * adelicHeight F g := by
  have h10 : ((b : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0
      = 0 := hb

  set x : (AdeleRing (𝓞 F) F)ˣ := borelDiagFst ⟨b, hb⟩ with hx
  set y : (AdeleRing (𝓞 F) F)ˣ := borelDiagSnd ⟨b, hb⟩ with hy
  have hx0 : (x : AdeleRing (𝓞 F) F)
      = ((b : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 := rfl
  have hy0 : (y : AdeleRing (𝓞 F) F)
      = ((b : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 := rfl

  have hfin := finHeight_upper_mul (glFin (𝓞 F) F b) (glFin (𝓞 F) F g)
    (by rw [glFin_apply, h10]; rfl) (fun v => by rw [glFin_apply, ← hy0]; exact P6B.JE2aFlat.finComp_ne_zero y v)

  have harch := archHeight_upper_mul (glArch (𝓞 F) F b) (glArch (𝓞 F) F g)
    (by rw [glArch_apply, h10]; rfl) (fun w => by rw [glArch_apply, ← hy0]; exact archComp_ne_zero y w)
  unfold adelicHeight
  rw [map_mul, map_mul, hfin, harch]
  simp only [glFin_apply, glArch_apply, ← hx0, ← hy0]
  have hy1 : ∀ w : InfinitePlace F, ‖(y : AdeleRing (𝓞 F) F).1 w‖ ≠ 0 :=
    fun w => norm_ne_zero_iff.mpr (archComp_ne_zero y w)
  have hy2 : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : AdeleRing (𝓞 F) F).2 v‖) ≠ 0 :=
    (finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos)
      fun v => norm_pos_iff.mpr (P6B.JE2aFlat.finComp_ne_zero y v)).ne'
  unfold placeModulus
  rw [finprod_div_distrib (P6B.JE2aFlat.hasFiniteMulSupport_norm_finComp x)
    (P6B.JE2aFlat.hasFiniteMulSupport_norm_finComp y)]
  simp only [div_pow]
  rw [Finset.prod_div_distrib]
  have hA : (∏ w : InfinitePlace F, ‖(y : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => pow_ne_zero _ (hy1 w)
  field_simp

-- pin: finHeight_mul_integral (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:276)
theorem finHeight_mul_integral (g k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (hk : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1)
    (hk' : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v k⁻¹ : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1) :
    finHeight F (g * k) = finHeight F g := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_integral _ _ (hk v) fun i j => ?_
  rw [← map_inv]
  exact hk' v i j

-- pin: adelicHeight_mul_of_integral_of_rowIsometry (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:289)
theorem adelicHeight_mul_of_integral_of_rowIsometry (g k : AdelicGL2 (𝓞 F) F)
    (hk : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v (glFin (𝓞 F) F k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖
        ≤ 1)
    (hk' : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      ‖(finComponent (𝓞 F) F v (glFin (𝓞 F) F k)⁻¹ :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1)
    (hka : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) :
    adelicHeight F (g * k) = adelicHeight F g := by
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_mul_rowIsometry F _ hka, finHeight_mul_integral _ _ hk hk']

end P6B.JE2aFlat

end

end RINHFold_JE2aFlatAdelic

section RINHFold_JE2aFlatFamily

noncomputable section

namespace P6B
namespace JE2aFlat

variable (F : Type) [Field F] [NumberField F]

section HeightOne

variable {K : Type*} [NormedField K]

-- pin: finLocalHeight_one (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:323)
theorem finLocalHeight_one : finLocalHeight (1 : GL (Fin 2) K) = 1 := by
  unfold finLocalHeight rowMaxNorm
  rw [show ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, Matrix.det_one,
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq, norm_one, norm_zero,
    max_eq_right zero_le_one]
  norm_num

end HeightOne

-- pin: finHeight_one (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:334)
theorem finHeight_one : finHeight F 1 = 1 := by
  unfold finHeight
  simp only [map_one, finLocalHeight_one, finprod_one]

-- pin: adelicHeight_one (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:338)
theorem adelicHeight_one : adelicHeight F 1 = 1 := by
  unfold adelicHeight
  rw [map_one, map_one, archHeight_one, finHeight_one, mul_one]

-- pin: flatOne (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:342)
def flatOne (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)

-- pin: flatOne_apply_one (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:345)
theorem flatOne_apply_one (s : ℂ) : flatOne F s 1 = 1 := by
  unfold flatOne
  rw [adelicHeight_one, Complex.ofReal_one, Complex.one_cpow]

variable {F}

-- pin: flatOne_ne_zero (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:351)
theorem flatOne_ne_zero (s : ℂ) (g : AdelicGL2 (𝓞 F) F) : flatOne F s g ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (adelicHeight_pos g).ne'))

-- pin: flatOne_eq_exp (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:354)
theorem flatOne_eq_exp (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    flatOne F s g = Complex.exp ((Real.log (adelicHeight F g) : ℂ) * (s + 1 / 2)) := by
  unfold flatOne
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (adelicHeight_pos g).ne'),
    Complex.ofReal_log (adelicHeight_pos g).le]

-- pin: differentiable_flatOne (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:360)
theorem differentiable_flatOne (g : AdelicGL2 (𝓞 F) F) : Differentiable ℂ fun s => flatOne F s g := by
  have h : (fun s => flatOne F s g)
      = fun s => Complex.exp ((Real.log (adelicHeight F g) : ℂ) * (s + 1 / 2)) :=
    funext fun s => flatOne_eq_exp s g
  rw [h]
  fun_prop

-- pin: continuous_flatOne_uncurry (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:367)
theorem continuous_flatOne_uncurry (hH : Continuous (adelicHeight F)) :
    Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => flatOne F p.1 p.2 := by
  have h : (fun p : ℂ × AdelicGL2 (𝓞 F) F => flatOne F p.1 p.2)
      = fun p => Complex.exp ((Real.log (adelicHeight F p.2) : ℂ) * (p.1 + 1 / 2)) :=
    funext fun p => flatOne_eq_exp p.1 p.2
  rw [h]
  have hlog : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => Real.log (adelicHeight F p.2) :=
    (hH.comp continuous_snd).log fun p => (adelicHeight_pos p.2).ne'
  fun_prop

-- pin: continuous_flatOne (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:377)
theorem continuous_flatOne (hH : Continuous (adelicHeight F)) (s : ℂ) : Continuous (flatOne F s) := by
  have h : flatOne F s = fun g => Complex.exp ((Real.log (adelicHeight F g) : ℂ) * (s + 1 / 2)) :=
    funext fun g => flatOne_eq_exp s g
  rw [h]
  have hlog : Continuous fun g : AdelicGL2 (𝓞 F) F => Real.log (adelicHeight F g) :=
    hH.log fun g => (adelicHeight_pos g).ne'
  fun_prop

-- pin: adelicHeight_mul_adelicArchGLInclAt (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:385)
theorem adelicHeight_mul_adelicArchGLInclAt (w : InfinitePlace F)
    (k : rowIsometrySubgroup w.Completion) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)) = adelicHeight F g := by
  unfold adelicHeight
  rw [map_mul, map_mul, show adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)
      = adelicArchGLIncl F (archGLIncl F w (k : GL (Fin 2) w.Completion)) from rfl,
    glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, mul_one,
    archHeight_mul_rowIsometry F _ (fun v => ?_)]
  by_cases hvw : v = w
  · subst hvw
    rw [archComponent_archGLIncl_self]
    exact k.2
  · rw [archComponent_archGLIncl_of_ne F hvw]
    exact isRowIsometry_one

-- pin: flatOne_mul_adelicArchGLInclAt (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:400)
theorem flatOne_mul_adelicArchGLInclAt (s : ℂ) (w : InfinitePlace F)
    (k : rowIsometrySubgroup w.Completion) (g : AdelicGL2 (𝓞 F) F) :
    flatOne F s (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)) = flatOne F s g := by
  unfold flatOne
  rw [adelicHeight_mul_adelicArchGLInclAt]

-- pin: hasArchType_flatOne (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:406)
theorem hasArchType_flatOne (s : ℂ) : HasArchType F (fun _ => 1) (flatOne F s) := by
  intro w k g
  rw [flatOne_mul_adelicArchGLInclAt, MonoidHom.one_apply, Units.val_one, one_mul]

-- pin: isArchKFinite_flatOne (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:410)
theorem isArchKFinite_flatOne (s : ℂ) : IsArchKFinite F (flatOne F s) :=
  isArchKFinite_of_hasArchType F _ _ (hasArchType_flatOne s)

-- pin: ofReal_div_mul_cpow (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:413)
theorem ofReal_div_mul_cpow {a c h : ℝ} (ha : 0 < a) (hc : 0 < c) (hh : 0 < h) (z : ℂ) :
    (((a / c * h : ℝ)) : ℂ) ^ z = ((a : ℂ) ^ z) * ((c : ℂ) ^ (-z)) * ((h : ℂ) ^ z) := by
  rw [div_eq_mul_inv, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (mul_nonneg ha.le (inv_nonneg.mpr hc.le)) hh.le, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (inv_nonneg.mpr hc.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ ?_, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hc.le]
  exact Real.pi_ne_zero.symm

-- pin: isInducedSection_flatOne (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:422)
theorem isInducedSection_flatOne (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαmod : ∀ x, ((α x : ℝˣ) : ℝ) = placeModulus F x) (s : ℂ) :
    IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (flatOne F s) := by
  intro b hb g
  unfold flatOne
  rw [adelicHeight_borel_mul b hb g,
    ofReal_div_mul_cpow (placeModulus_pos _) (placeModulus_pos _) (adelicHeight_pos g)]
  simp only [etaFst, etaSnd, MonoidHom.mul_apply, MonoidHom.one_apply, one_mul, cpowChar_apply_val, hαmod]

end P6B.JE2aFlat

end

end RINHFold_JE2aFlatFamily

open MeasureTheory NumberField NumberField.AdelicHeight AutomorphicForm
open scoped NNReal

-- pin: isInducedSection_adelicHeight_cpow (S_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean:440)
theorem isInducedSection_adelicHeight_cpow
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    (∀ x, 0 < ((α x : ℝˣ) : ℝ)) ∧
    IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) ∧
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ),
      IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s)
        (fun g : AdelicGL2 (𝓞 F) F => ((adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)) :=
  ⟨fun x => by rw [MonoidHom.coe_toHomUnits]; exact MeasureTheory.distribHaarChar_pos,
    fun x => by rw [MonoidHom.one_apply, Units.val_one, norm_one],
    fun hα s => P6B.JE2aFlat.isInducedSection_flatOne _ hα
      (fun x => NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F x) s⟩

-- pin: IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul (S_AutomorphicForm_IsInducedSection_apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul.lean:15)
-- The two local instances are the pin's: `distribHaarChar_algebraMap` pins the `adeleBorel`
-- measurable space, so the ambient instances must be them. Narrow suppression of the
-- `haveI`/`letI` style linter on this one declaration (house style).
set_option linter.style.haveILetI false in
theorem IsInducedSection.apply_globalPoints_mul_of_mem_borelSubgroup_and_apply_unipotentGL2_mul
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ),
    (∀ b : Matrix.GeneralLinearGroup (Fin 2) F, b ∈ borelSubgroup F →
      ∀ g : AdelicGL2 (𝓞 F) F, φ (globalPoints (𝓞 F) F b * g) = φ g) ∧
    (∀ (u : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F), φ (unipotentGL2 u * g) = φ g) := by
  intro α hα μ ν hμF hνF s φ hφ

  have hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α := by
    intro u
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    haveI : BorelSpace (AdeleRing (𝓞 F) F) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
    have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
    have key : (Units.map (↑(algebraMap F (AdeleRing (𝓞 F) F)) : F →* AdeleRing (𝓞 F) F)) u =
        Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom u := by ext; rfl
    ext
    simp only [α, MonoidHom.coe_toHomUnits, MonoidHom.coe_comp, Function.comp_apply, Units.val_one]
    rw [key, h]
    simp
  have h1 : IsIdeleClassChar (𝓞 F) F (etaFst μ α hα s) := etaFst_isIdeleClassChar hμF hprin s
  have h2 : IsIdeleClassChar (𝓞 F) F (etaSnd ν α hα s) := etaSnd_isIdeleClassChar hνF hprin s
  refine ⟨?_, ?_⟩
  · intro b hb g
    have hmem : globalPoints (𝓞 F) F b ∈ adelicBorel (𝓞 F) F := globalPoints_mem_adelicBorel (𝓞 F) F hb
    rw [hφ _ hmem g, borelDiagFst_globalPoints (𝓞 F) F hb hmem, borelDiagSnd_globalPoints (𝓞 F) F hb hmem,
      h1, h2]
    simp
  · intro u g
    exact isInducedSection_unipotent_mul hφ u g

end AutomorphicForm
