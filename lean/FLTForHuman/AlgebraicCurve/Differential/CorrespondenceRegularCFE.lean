/-
The correspondence commutes with a constant field extension, on regular differentials.

Under a constant field extension `K ⊆ E`, `F ⊆ FE`, `F' ⊆ F'E` — `FE` the compositum of
`E` and `F`, `F'E` that of `E` and `F'` (`hgen`/`hgen'`: the `E`-span of `F`, resp. `F'`,
is everything) — and two `K`-algebra maps `φ, ψ : F →ₐ[K] F'` lifted to `φE, ψE : FE →ₐ[E] F'E`
along the two inclusions (`hφcomm`, `hψcomm`), four conjuncts hold for the Kähler map
`κ := KaehlerDifferential.map K E F FE : Ω[F⁄K] →ₗ[F] Ω[FE⁄E]`:

* `κ` commutes with the correspondence: `κ (correspondence φ ψ ω) =
  correspondence φE ψE (κ ω)` — the naturality of the trace/differential-square;
* `κ` is injective;
* `κ` carries regular differentials to regular differentials;
* the regular differentials of `FE/E` are spanned over `E` by the image of those of `F/K`.

The last two are what makes the constant-field extension an isomorphism on the
differential space of the curve: injectivity plus the equality of genera
(`genus_eq_of_constantFieldExtension_of_isAlgClosed`) and of the two finranks
(`finite_and_finrank_regularDifferentials_eq_genus`) upgrades "the image is contained" to
"the image spans", through `linearIndependent_of_constantFieldExtension` (a `K`-linearly
independent family of `F` stays `E`-linearly independent in `FE`).

The mathematics is local where it must be: a regular differential is, at each place `P`,
an integral multiple of `dCoord` (`mem_regularDifferentials_iff`), so the first-order claim
is the coefficient engine `exists_smul_D_eq_smul_dCoord` — at a place of `FE` either all of
`F` is integral (and the coefficient is integral by
`ord_diffCoeff_D_nonneg_of_perfectField`), or the comap of `P` to `F` is a proper valuation
subring, a place `v'` of `F` whose place is `P`, at which the hypothesis on `ω` is read.
The one place where the char-0 development is needed rather than the char-free one is the
lift `Place.exists_comap_algebraMap_eq_of_constantFieldExtension`.

Statements are the wrapper's character for character; proofs are the pin's `S_` file's,
adapted to mathlib `v4.34.0` and the port's names. The pin's global
`attribute [-instance]`/`attribute [-simp]` walls are dropped (they exist only because the
pin's `S_` files re-declare instances and simp lemmas the port carries once), and two of its
prelude lemmas `ord_nonneg_of_mem` / `mem_of_ord_nonneg` are the port's public
`Place.ord_nonneg_of_mem` / `Place.mem_of_ord_nonneg` (`AlgebraicCurve/Defs/PushPull.lean`),
imported, not restated. The two helpers written here (`ord_coe_nonneg` — the pin's
unguarded, `Place/LaurentSeriesModel.lean`'s private homonym carries `y ≠ 0` and is a
different statement — and `mem_of_ord_nonneg'`, the unguarded variant of
`Place.mem_of_ord_nonneg`) are public in the pin's `S_` file and stay public.

Role: tier 1. One public headline at the wrapper's name and text, over the local blocks
`AlgebraicCurve.OmegaBaseChangeProof` (the three `ord`/coefficient helpers).

<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension.lean>.

spec-pin: Theorems/Thm_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Differential_map_correspondence_regularDifferentials_of_constantFieldExtension.lean
-/
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegular
import FLTForHuman.AlgebraicCurve.Differential.Coefficient
import FLTForHuman.AlgebraicCurve.Differential.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionSpan
import FLTForHuman.AlgebraicCurve.IsCurveOver.FinitenessTransfer
import FLTForHuman.AlgebraicCurve.Canonical.RegularDifferentialsFinrank
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.TranscendentalOfOrdNeZero
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport

set_option autoImplicit false

-- The pin's `haveI`/`letI` instance walls are load-bearing (SET-1 §3): the along-level
-- `Algebra F F'`, the `SMulCommClass E F' F'E` for `KaehlerDifferential.map`, and the
-- characteristic-zero instances of the constant extension are local. Keep them literal.
set_option linter.style.haveILetI false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

namespace OmegaBaseChangeProof

section PlaceFacts

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The pin's `ord_coe_nonneg`: an element of the valuation ring has nonnegative order.
The unguarded form — `0` is the valuation subring's own zero, and `v.ord 0 = 0` — so this is
literally `Place.ord_nonneg_of_mem` at the coercion. -/
theorem ord_coe_nonneg (v : Place K F) (f : v.toValuationSubring) : 0 ≤ v.ord (f : F) := by
  by_cases hf : f = 0
  · simp [hf]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf hπ
  have : (f : F) = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    rw [hu, zpow_natCast]; push_cast; rfl
  rw [this, v.ord_unit_smul_zpow u hπ]
  exact Int.natCast_nonneg n

/-- The pin's `mem_of_ord_nonneg'`, the unguarded variant of `Place.mem_of_ord_nonneg`:
the `f = 0` case, then the public lemma. -/
theorem mem_of_ord_nonneg' (v : Place K F) {f : F} (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  · exact v.mem_of_ord_nonneg hf h

/-- The coefficient engine: at a place `P` of a constant-field extension `F/E`, for an
integral `a` and an integral `t` there is an integral `f` with `a • d t = f • dCoord`. Over a
perfect `K` the coefficient of `d t` against a uniformiser is integral, and `dCoord` is the
differential of a uniformiser. -/
theorem exists_smul_D_eq_smul_dCoord [PerfectField K] [CharZero K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (P : Place K F) {a t : F} (ha : a ∈ P.toValuationSubring) (ht : t ∈ P.toValuationSubring) :
    ∃ f ∈ P.toValuationSubring, a • D K F t = f • P.dCoord := by
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  obtain ⟨π₀, hπ₀, hdc⟩ := P.exists_ord_eq_one_and_dCoord_eq
  have hπ₀' : P.ord π₀ ≠ 0 := by rw [hπ₀]; exact one_ne_zero
  obtain ⟨c, hc⟩ := AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero x P hπ₀' (D K F t)
  have hcoef : AlgebraicCurve.Place.diffCoeff π₀ (D K F t) = c := by
    rw [hc]
    exact AlgebraicCurve.Place.diffCoeff_smul_D_eq x P hπ₀' c
  have hord : 0 ≤ P.ord c := by
    rw [← hcoef]
    exact AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_perfectField x P hπ₀
      (Place.ord_nonneg_of_mem P ht)
  refine ⟨a * c, mul_mem ha (mem_of_ord_nonneg' P hord), ?_⟩
  rw [hc, hdc, smul_smul]

end PlaceFacts

end OmegaBaseChangeProof

namespace Differential

-- `hψ`/`hψE` are the pin's binders and part of the wrapper's statement; the proof reads
-- only the `φ`-side integrality.
set_option linter.unusedVariables false in
open OmegaBaseChangeProof in
/-- **The correspondence commutes with a constant field extension**: the Kähler map
`KaehlerDifferential.map K E F FE` is a morphism of correspondences, is injective, preserves
regular differentials, and its image spans them. Verbatim from the pin's `Theorems/`
wrapper; the proof is its `S_` file's `solution`. -/
theorem map_correspondence_regularDifferentials_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [SMulCommClass E F FE] [IsAlgClosed E]
    [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE ψE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral) :
    (∀ ω : Ω[F⁄K], KaehlerDifferential.map K E F FE (Differential.correspondence φ ψ ω) =
        Differential.correspondence φE ψE (KaehlerDifferential.map K E F FE ω)) ∧
    Function.Injective (KaehlerDifferential.map K E F FE) ∧
    (∀ ω ∈ regularDifferentials K F,
        KaehlerDifferential.map K E F FE ω ∈ regularDifferentials E FE) ∧
    (∀ η ∈ regularDifferentials E FE,
        η ∈ Submodule.span E
          (KaehlerDifferential.map K E F FE '' (regularDifferentials K F : Set (Ω[F⁄K])))) := by
  classical

  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : CharZero FE := charZero_of_injective_algebraMap (algebraMap E FE).injective
  haveI : CharZero F' := charZero_of_injective_algebraMap (algebraMap K F').injective
  haveI : SMulCommClass E F' F'E := ⟨fun e f y => by simp only [Algebra.smul_def]; ring⟩
  set κ : Ω[F⁄K] →ₗ[F] Ω[FE⁄E] := KaehlerDifferential.map K E F FE with hκdef
  set κ' : Ω[F'⁄K] →ₗ[F'] Ω[F'E⁄E] := KaehlerDifferential.map K E F' F'E with hκ'def

  obtain ⟨x, hx, hxfin⟩ := hfg
  haveI := hxfin
  have hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F := ⟨x, hx, hxfin⟩
  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_ord_neg_of_transcendental x hx
  have hvx : v.ord x ≠ 0 := hv.ne
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _

  set x' : FE := algebraMap F FE x with hx'def
  obtain ⟨P₁, -, hP₁ord, -⟩ :=
    AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension K F E FE hfg hfgE hgen v
  have hP₁x : P₁.ord x' ≠ 0 := by rw [hx'def, hP₁ord]; exact hvx
  have hx' : Transcendental E x' := AlgebraicCurve.Place.transcendental_of_ord_ne_zero P₁ hP₁x
  obtain ⟨y, hy, hyfin⟩ := hfgE
  have hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE := ⟨y, hy, hyfin⟩
  haveI := hyfin
  haveI hx'fin : FiniteDimensional (IntermediateField.adjoin E ({x'} : Set FE)) FE :=
    AlgebraicCurve.finiteDimensional_adjoin_of_transcendental y hx'
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin E ({x'} : Set FE)) FE :=
    Algebra.IsAlgebraic.of_finite _ _
  have hDx' : D E FE x' ≠ 0 := AlgebraicCurve.Place.D_ne_zero_of_ord_ne_zero x' P₁ hP₁x

  have hrep : ∀ ω : Ω[F⁄K], ∃ g : F, ω = g • D K F x := fun ω =>
    AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero x v hvx ω
  have hκ : ∀ g : F, κ (g • D K F x) = algebraMap F FE g • D E FE x' := fun g => by
    rw [LinearMap.map_smul, hκdef, KaehlerDifferential.map_D, algebraMap_smul]
  have hκ' : ∀ (g t : F'), κ' (g • D K F' t) = algebraMap F' F'E g • D E F'E (algebraMap F' F'E t) :=
    fun g t => by rw [LinearMap.map_smul, hκ'def, KaehlerDifferential.map_D, algebraMap_smul]

  have hinj : Function.Injective κ := by
    intro ω₁ ω₂ h
    obtain ⟨g₁, rfl⟩ := hrep ω₁
    obtain ⟨g₂, rfl⟩ := hrep ω₂
    rw [hκ, hκ] at h
    have h' : (algebraMap F FE g₁ - algebraMap F FE g₂) • D E FE x' = 0 := by
      rw [sub_smul, h, sub_self]
    have h'' : algebraMap F FE g₁ = algebraMap F FE g₂ :=
      sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right hDx')
    rw [(algebraMap F FE).injective h'']

  have hreg : ∀ ω ∈ regularDifferentials K F, κ ω ∈ regularDifferentials E FE := by
    intro ω hω
    rw [mem_regularDifferentials_iff]
    intro P
    by_cases hall : ∀ f : F, algebraMap F FE f ∈ P.toValuationSubring
    ·
      obtain ⟨g, rfl⟩ := hrep ω
      rw [hκ]
      exact exists_smul_D_eq_smul_dCoord x' P (hall g) (hall x)
    ·
      set A : ValuationSubring F := P.toValuationSubring.comap (algebraMap F FE) with hAdef
      have hAK : ∀ a : K, algebraMap K F a ∈ A := fun a => by
        show algebraMap F FE (algebraMap K F a) ∈ P.toValuationSubring
        rw [← IsScalarTower.algebraMap_apply K F FE a, IsScalarTower.algebraMap_apply K E FE a]
        exact P.algebraMap_mem' _
      have hA : A ≠ ⊤ := by
        intro htop
        exact hall fun f => (show f ∈ A from htop ▸ trivial)
      obtain ⟨v', hv'⟩ := AlgebraicCurve.Place.exists_of_valuationSubring x A hAK hA
      obtain ⟨h, hh, hωh⟩ := (mem_regularDifferentials_iff (K := K) (F := F)).1 hω v'
      obtain ⟨πv, hπv, hdcv⟩ := v'.exists_ord_eq_one_and_dCoord_eq
      have hπvmem : πv ∈ v'.toValuationSubring :=
        mem_of_ord_nonneg' v' (by rw [hπv]; exact zero_le_one)
      have hh' : algebraMap F FE h ∈ P.toValuationSubring := by
        have : h ∈ A := by rw [hv'] at hh; exact hh
        exact this
      have hπv' : algebraMap F FE πv ∈ P.toValuationSubring := by
        have : πv ∈ A := by rw [hv'] at hπvmem; exact hπvmem
        exact this
      rw [hωh, hdcv, LinearMap.map_smul, hκdef, KaehlerDifferential.map_D,
        ← algebraMap_smul FE h (D E FE (algebraMap F FE πv))]
      exact exists_smul_D_eq_smul_dCoord x' P hh' hπv'

  have hspan : ∀ η ∈ regularDifferentials E FE,
      η ∈ Submodule.span E (κ '' (regularDifferentials K F : Set (Ω[F⁄K]))) := by
    haveI : Algebra.EssFiniteType K F :=
      AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hxfin
    haveI : HasCanonicalDivisor (K := K) (F := F) :=
      AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := K) (F := F)
    haveI : Algebra.EssFiniteType E FE :=
      AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hy hyfin
    haveI : HasCanonicalDivisor (K := E) (F := FE) :=
      AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver (K := E) (F := FE)
    obtain ⟨hfinK, hrankK⟩ :=
      AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := K) (F := F)
    obtain ⟨hfinE, hrankE⟩ :=
      AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := E) (F := FE)
    have hgenus : genus E FE = genus K F :=
      AlgebraicCurve.genus_eq_of_constantFieldExtension_of_isAlgClosed K F E FE hfg hfgE hgen
    haveI := hfinK
    haveI := hfinE
    set bK := Module.finBasis K ↥(regularDifferentials K F) with hbK

    choose f hf using fun i => hrep (bK i : Ω[F⁄K])
    have hfli : LinearIndependent K f := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hsum : ((∑ j, c j • bK j : ↥(regularDifferentials K F)) : Ω[F⁄K]) = 0 := by
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul, hf, ← smul_assoc, ← Finset.sum_smul]
        rw [show (∑ j, c j • f j) = 0 from hc, zero_smul]
      have h0 : ∑ j, c j • bK j = 0 := Subtype.ext (by simpa using hsum)
      exact Fintype.linearIndependent_iff.1 bK.linearIndependent c h0 i
    have hfli' : LinearIndependent E (fun i => algebraMap F FE (f i)) :=
      AlgebraicCurve.linearIndependent_of_constantFieldExtension K F E FE hfg hfgE hgen hfli

    set w : Fin (Module.finrank K ↥(regularDifferentials K F)) → Ω[FE⁄E] :=
      fun i => κ (bK i : Ω[F⁄K]) with hw
    have hw' : ∀ i, w i = algebraMap F FE (f i) • D E FE x' := fun i => by
      simp only [hw]; rw [hf i, hκ]
    have hwli : LinearIndependent E w := by
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have hsum : (∑ j, c j • algebraMap F FE (f j)) • D E FE x' = 0 := by
        rw [Finset.sum_smul]
        simp only [smul_assoc]
        simpa only [hw'] using hc
      have h0 := (smul_eq_zero.1 hsum).resolve_right hDx'
      exact Fintype.linearIndependent_iff.1 hfli' c h0 i
    have hwmem : ∀ i, w i ∈ regularDifferentials E FE := fun i => hreg _ (bK i).2
    set W : Submodule E (Ω[FE⁄E]) := Submodule.span E (Set.range w) with hW
    have hWle : W ≤ regularDifferentials E FE :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hwmem i)
    have hWrank : Module.finrank E W = Module.finrank E ↥(regularDifferentials E FE) := by
      rw [hW, finrank_span_eq_card hwli, Fintype.card_fin, hrankE, hgenus, ← hrankK]
    have hWeq : W = regularDifferentials E FE := Submodule.eq_of_le_of_finrank_eq hWle hWrank
    intro η hη
    have hηW : η ∈ W := by rw [hWeq]; exact hη
    refine Submodule.span_mono ?_ hηW
    rintro _ ⟨i, rfl⟩
    exact ⟨bK i, (bK i).2, rfl⟩

  have hint : ∀ ω : Ω[F⁄K],
      κ (Differential.correspondence φ ψ ω) = Differential.correspondence φE ψE (κ ω) := by
    obtain ⟨hfinφ, hfinφE, -, htr⟩ :=
      AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension K F hfg F' hfg' φ hφ
        E FE hfgE hgen F'E hfgE' hgen' φE hφcomm hφE
    have hsep : SeparableAlong K φ := AlgebraicCurve.separableAlong_of_charZero φ hφ
    have hsepE : SeparableAlong E φE := AlgebraicCurve.separableAlong_of_charZero φE hφE

    have hpull : ∀ (σ : F →ₐ[K] F') (σE : FE →ₐ[E] F'E),
        (∀ f : F, σE (algebraMap F FE f) = algebraMap F' F'E (σ f)) →
        ∀ ω : Ω[F⁄K], κ' (Differential.pullbackAlong σ ω) = Differential.pullbackAlong σE (κ ω) := by
      intro σ σE hcomm ω
      obtain ⟨g, rfl⟩ := hrep ω
      rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_D, hκ', hκ,
        Differential.pullbackAlong_smul, Differential.pullbackAlong_D, hcomm, hx'def, hcomm]

    have hφx : Transcendental K (φ x) := fun h =>
      hx ((isAlgebraic_algHom_iff φ φ.toRingHom.injective).mp h)
    obtain ⟨x₁, hx₁, hx₁fin⟩ := hfg'
    haveI := hx₁fin
    haveI : FiniteDimensional (IntermediateField.adjoin K ({φ x} : Set F')) F' :=
      AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x₁ hφx
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({φ x} : Set F')) F' :=
      Algebra.IsAlgebraic.of_finite _ _
    obtain ⟨v₁, hv₁⟩ := AlgebraicCurve.Place.exists_ord_neg_of_transcendental (φ x) hφx
    have hrep' : ∀ η : Ω[F'⁄K], ∃ u : F', η = u • D K F' (φ x) := fun η =>
      AlgebraicCurve.Place.exists_eq_smul_D_of_ord_ne_zero (φ x) v₁ hv₁.ne η
    intro ω
    obtain ⟨u, hu⟩ := hrep' (Differential.pullbackAlong ψ ω)

    rw [Differential.correspondence_apply, Differential.correspondence_apply, hu,
      ← Differential.pullbackAlong_D, Differential.traceAlong_smul_pullbackAlong φ hsep u, hκ]

    rw [← hpull ψ ψE hψcomm, hu, hκ']
    have hDφ : D E F'E (algebraMap F' F'E (φ x)) = Differential.pullbackAlong φE (D E FE x') := by
      rw [Differential.pullbackAlong_D, hx'def, hφcomm]
    rw [hDφ, Differential.traceAlong_smul_pullbackAlong φE hsepE, htr u, algebraMap_smul]
  exact ⟨hint, hinj, hreg, hspan⟩

end Differential

end AlgebraicCurve
