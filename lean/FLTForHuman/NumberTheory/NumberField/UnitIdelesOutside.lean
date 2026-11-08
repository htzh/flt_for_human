/-
  The unit idèles outside a set of finite places.

  `unitIdelesOutside S` is the subgroup of the unit idèles that are integral (in both directions) at every
  finite place **outside** `S` — the `S`-relaxed version of `unitIdeles`, and the domain on which the
  product-measure decomposition of the idèle Haar measure is stated. `mem_unitIdelesOutside_iff` is the
  pointwise reading, `unitIdelesOutside_empty` recovers `unitIdeles`, and the two order lemmas
  `unitIdelesOutside_mono`/`unitIdeles_le_unitIdelesOutside` are the monotonicity the decomposition uses.

  Transcribed whole from `Definitions/Def_IsDedekindDomain_FiniteUnitIdelesOutside.lean`
  (pinned `aa2d8b3`, 62 lines / 6 declarations): the finite-adèle subgroup and its four lemmas, then the
  idèle-level `unitIdelesOutside` (the comap along the finite part) and its `mem_` lemma. The pin's
  `import Mathlib` is replaced by the port modules below.

  spec-pin: Definitions/Def_IsDedekindDomain_FiniteUnitIdelesOutside.lean
-/
import FLTForHuman.NumberTheory.NumberField.FiniteIdeles

set_option autoImplicit false

namespace IsDedekindDomain.FiniteAdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

def unitIdelesOutside (S : Set (HeightOneSpectrum R)) : Subgroup (FiniteAdeleRing R K)ˣ where
  carrier := {δ | ∀ v : HeightOneSpectrum R, v ∉ S →
    (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
      ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K}
  one_mem' v _ := ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩
  mul_mem' := by
    rintro x y hx hy v hv
    obtain ⟨hx1, hx2⟩ := hx v hv
    obtain ⟨hy1, hy2⟩ := hy v hv
    exact ⟨by rw [Units.val_mul]; exact mul_mem hx1 hy1, by rw [mul_inv, Units.val_mul]; exact mul_mem hx2 hy2⟩
  inv_mem' := by
    rintro x hx v hv
    obtain ⟨hx1, hx2⟩ := hx v hv
    exact ⟨hx2, by rw [inv_inv]; exact hx1⟩

variable {R K} in
theorem mem_unitIdelesOutside_iff (S : Set (HeightOneSpectrum R)) (δ : (FiniteAdeleRing R K)ˣ) :
    δ ∈ unitIdelesOutside R K S ↔
      ∀ v : HeightOneSpectrum R, v ∉ S →
        (δ : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K ∧
          ((δ⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem unitIdelesOutside_empty : unitIdelesOutside R K (∅ : Set (HeightOneSpectrum R)) = unitIdeles R K :=
  Subgroup.ext fun _ =>
    ⟨fun h => ⟨fun v => (h v fun hv => hv).1, fun v => (h v fun hv => hv).2⟩, fun h v _ => ⟨h.1 v, h.2 v⟩⟩

theorem unitIdelesOutside_mono {S T : Set (HeightOneSpectrum R)} (h : S ⊆ T) :
    unitIdelesOutside R K S ≤ unitIdelesOutside R K T :=
  fun _ hx v hv => hx v fun hvS => hv (h hvS)

theorem unitIdeles_le_unitIdelesOutside (S : Set (HeightOneSpectrum R)) :
    unitIdeles R K ≤ unitIdelesOutside R K S :=
  fun _ hx v _ => ⟨hx.1 v, hx.2 v⟩

end IsDedekindDomain.FiniteAdeleRing

namespace NumberField.AdeleRing

variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

noncomputable def unitIdelesOutside (S : Set (IsDedekindDomain.HeightOneSpectrum R)) : Subgroup (AdeleRing R K)ˣ :=
  (IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S).comap
    (Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom)

variable {R K} in
theorem mem_unitIdelesOutside_iff (S : Set (IsDedekindDomain.HeightOneSpectrum R)) (x : (AdeleRing R K)ˣ) :
    x ∈ unitIdelesOutside R K S ↔
      Units.map (RingHom.snd (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing R K)).toMonoidHom x ∈
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K S :=
  Iff.rfl

end NumberField.AdeleRing
