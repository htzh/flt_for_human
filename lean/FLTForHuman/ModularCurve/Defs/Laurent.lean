/-
  Layer 0a — the `q`-substitution and the coefficient change.

  This module holds the two ring maps that every later module composes:
  `qExpand`, which sends `q ↦ q ^ N` on exponents, and `coeffMap` / `coeffEmb`,
  which extend a coefficient map `R →+* S` coefficientwise. Both are `def`s
  returning ring homs. The predicted rewrite-search gap (a `def`-as-ring-hom
  that a generic `map_mul` will not match) did **not** appear in this layer:
  every lemma is proved coefficientwise through the `[simp]` coefficient lemmas
  below (`qExpand_coeff_mul`, `coeffMap_coeff`, …), so no monomorphic `*_mul`
  bridge had to be named. See the friction list in the consumer.

  FLT provenance (source of truth for correctness), pinned `aa2d8b3`:

  * `Definitions/Def_ModularCurve_X0.lean` lines 25–105 —
    `qExpand`, its coefficient lemmas, `qExpandₐ`, `qExpandₐ_apply`;
    and line 340 for `qExpandₐ_comp`.
    https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean
  * `Definitions/Def_ModularCurve_LaurentCoeff.lean` lines 16–123 —
    `coeffMap`, `coeffEmb`, `laurentBaseChange` and their lemmas.
    https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_LaurentCoeff.lean

  `LaurentSeries`, `HahnSeries` and `IntermediateField` are mathlib's names;
  every other declaration here keeps FLT's name verbatim so that a `#check`
  against the pinned source is mechanical.

  The tail of the module carries the part of the cone's **outbound interface**
  stated over these two maps: `coeffMap_qExpand` (indeg 194 in FLT's graph, the
  most-shared declaration in the cone), `coeffEmb_qExpand` (66),
  `coeffMap_injective` (32) and `coeffEmb_injective` (19). They are transcribed
  verbatim from their `Theorems/Thm_ModularCurve_*` wrappers in the pin and are
  public. See `logs/ffg-port.md` §2e.

  Assumes nothing from earlier 0a modules; this is the first one.
-/
import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

section QExpand

variable {R : Type*} [CommRing R]

variable (R) in

/-- The `q`-substitution `q ↦ q ^ N`, as a ring endomorphism of Laurent series:
on a monomial `q ^ k` it is `q ^ (N * k)`, and coefficients are unchanged. -/
def qExpand (N : ℕ) [NeZero N] : LaurentSeries R →+* LaurentSeries R :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne N))
    (fun g g' => mul_le_mul_iff_of_pos_left
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))

variable (N : ℕ) [NeZero N]

@[simp]
theorem qExpand_coeff_mul (f : LaurentSeries R) (k : ℤ) :
    (qExpand R N f).coeff ((N : ℤ) * k) = f.coeff k :=
  HahnSeries.embDomain_coeff

theorem qExpand_coeff_of_not_dvd (f : LaurentSeries R) {k : ℤ} (hk : ¬ (N : ℤ) ∣ k) :
    (qExpand R N f).coeff k = 0 := by
  refine HahnSeries.embDomain_of_notMem_range ?_
  rintro ⟨m, rfl⟩
  exact hk ⟨m, rfl⟩

@[simp]
theorem qExpand_single (k : ℤ) (r : R) :
    qExpand R N (HahnSeries.single k r) = HahnSeries.single ((N : ℤ) * k) r :=
  HahnSeries.embDomain_single

@[simp]
theorem qExpand_C (r : R) : qExpand R N (HahnSeries.C r) = HahnSeries.C r :=
  HahnSeries.embDomainRingHom_C

/-- `qExpand` changes no exponent to `0` from a nonzero one, so it is injective. -/
theorem qExpand_injective : Function.Injective (qExpand R N) :=
  HahnSeries.embDomain_injective

theorem qExpand_one_apply (f : LaurentSeries R) : qExpand R 1 f = f := by
  ext k
  have h : ((1 : ℕ) : ℤ) * k = k := by simp
  conv_lhs => rw [← h]
  rw [qExpand_coeff_mul]

theorem qExpand_congr {M K : ℕ} [NeZero M] [NeZero K] (h : M = K) (f : LaurentSeries R) :
    qExpand R M f = qExpand R K f := by
  subst h; rfl

/-- `qExpand` is a substitution: expanding by `M` after `N` is expanding by `M * N`. -/
theorem qExpand_qExpand (M : ℕ) [NeZero M] (f : LaurentSeries R) :
    qExpand R M (qExpand R N f) = qExpand R (M * N) f := by
  ext k
  by_cases hk : ((M : ℤ) * N) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    trans f.coeff m
    · rw [show (M : ℤ) * N * m = (M : ℤ) * ((N : ℤ) * m) by ring, qExpand_coeff_mul,
        qExpand_coeff_mul]
    · rw [show (M : ℤ) * N * m = (((M * N : ℕ) : ℤ)) * m by push_cast; ring,
        qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd (M * N) f (by push_cast; exact hk)]
    by_cases hkM : (M : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hkM
      rw [qExpand_coeff_mul M _ m]
      refine qExpand_coeff_of_not_dvd N _ ?_
      rintro ⟨c, hc⟩
      exact hk ⟨c, by rw [hc]; ring⟩
    · exact qExpand_coeff_of_not_dvd M _ hkM

end QExpand

section RatAlgebra

variable (N : ℕ) [NeZero N]

/-- The rational constant `c` is the Laurent series `c q ^ 0`. -/
theorem algebraMap_apply_eq_single (c : ℚ) :
    algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.single 0 c := by
  have h1 : algebraMap ℚ (PowerSeries ℚ) c = PowerSeries.C c := by
    simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

/-- `qExpand` as a `ℚ`-algebra map, so that it can act on `IntermediateField`s.
It is `qExpand ℚ N` with the same underlying function. -/
def qExpandₐ : LaurentSeries ℚ →ₐ[ℚ] LaurentSeries ℚ where
  __ := qExpand ℚ N
  commutes' r := by
    show qExpand ℚ N (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℚ (LaurentSeries ℚ) r
    rw [algebraMap_apply_eq_single, qExpand_single, mul_zero]

@[simp]
theorem qExpandₐ_apply (f : LaurentSeries ℚ) : qExpandₐ N f = qExpand ℚ N f := rfl

/-- `qExpandₐ` is a substitution: expanding by `ℓ` after `ℓ'` is expanding by `ℓ * ℓ'`. -/
theorem qExpandₐ_comp (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] :
    (qExpandₐ ℓ).comp (qExpandₐ ℓ') = qExpandₐ (ℓ * ℓ') := by
  refine AlgHom.ext fun f => ?_
  simp only [AlgHom.comp_apply, qExpandₐ_apply]
  exact qExpand_qExpand ℓ' ℓ f

end RatAlgebra

section CoeffMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Extend a coefficient map `f : R →+* S` coefficientwise to Laurent series. -/
def coeffMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := by
    ext k
    simp
  map_one' := by
    ext k
    simp [HahnSeries.coeff_one, apply_ite f]
  map_add' x y := by
    ext k
    simp
  map_mul' x y := by
    have h := HahnSeries.map_mul (f := (f : R →ₙ+* S)) (x := x) (y := y)
    have hx : ∀ z : LaurentSeries R, z.map (f : R →ₙ+* S) = z.map f := fun z =>
      HahnSeries.ext rfl
    rwa [hx, hx, hx] at h

/-- `coeffMap` acts on coefficients by `f`. Named so a rewrite can fire on the
`def`-as-ring-hom, where the generic `map_mul` cannot. -/
@[simp]
theorem coeffMap_coeff (f : R →+* S) (x : LaurentSeries R) (k : ℤ) :
    (coeffMap f x).coeff k = f (x.coeff k) :=
  rfl

@[simp]
theorem coeffMap_single (f : R →+* S) (k : ℤ) (r : R) :
    coeffMap f (HahnSeries.single k r) = HahnSeries.single k (f r) := by
  ext m
  rcases eq_or_ne m k with rfl | hm
  · simp [HahnSeries.coeff_single_same]
  · simp [HahnSeries.coeff_single_of_ne hm]

/-- `coeffMap` is functorial: composing the maps composes the extensions. -/
theorem coeffMap_coeffMap (g : S →+* T) (f : R →+* S) (x : LaurentSeries R) :
    coeffMap g (coeffMap f x) = coeffMap (g.comp f) x := by
  ext k
  simp

@[simp]
theorem coeffMap_id (x : LaurentSeries R) : coeffMap (RingHom.id R) x = x := by
  ext k
  simp

theorem coeffMap_congr {f g : R →+* S} (h : f = g) (x : LaurentSeries R) :
    coeffMap f x = coeffMap g x := by
  subst h; rfl

end CoeffMap

section Constants

variable (L : Type*) [Field L]

/-- The constant `c` of `L` is the Laurent series `c q ^ 0`. -/
theorem algebraMap_laurentSeries_eq_single (c : L) :
    algebraMap L (LaurentSeries L) c = HahnSeries.single 0 c := by
  have h1 : algebraMap L (PowerSeries L) c = PowerSeries.C c := by
    simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

variable {L} in

theorem coeffMap_algebraMap (φ : L →+* L) (c : L) :
    coeffMap φ (algebraMap L (LaurentSeries L) c) = algebraMap L (LaurentSeries L) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

variable [Algebra ℚ L]

/-- The coefficient embedding `ℚ → K` extended coefficientwise to Laurent
series: the way the base field `ℚ` sits inside `LaurentSeries K`. -/
def coeffEmb : LaurentSeries ℚ →+* LaurentSeries L :=
  coeffMap (algebraMap ℚ L)

@[simp]
theorem coeffEmb_coeff (x : LaurentSeries ℚ) (k : ℤ) :
    (coeffEmb L x).coeff k = algebraMap ℚ L (x.coeff k) :=
  rfl

variable {L} in

/-- A `ℚ`-algebra automorphism of `L` fixes the image of `coeffEmb`. -/
theorem coeffMap_coeffEmb (σ : L ≃ₐ[ℚ] L) (x : LaurentSeries ℚ) :
    coeffMap (σ : L →+* L) (coeffEmb L x) = coeffEmb L x := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun c => σ.commutes c) x

end Constants

section BaseChange

variable (L : Type*) [Field L] [Algebra ℚ L]
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))

/-- Base change of an intermediate field of `LaurentSeries ℚ` to `L`, generated
by the coefficientwise image of `F₀`. -/
def laurentBaseChange : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))

variable {F₀} in

theorem coeffEmb_mem_laurentBaseChange {x : LaurentSeries ℚ} (hx : x ∈ F₀) :
    coeffEmb L x ∈ laurentBaseChange L F₀ :=
  IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩

variable {L F₀} in

theorem mem_laurentBaseChange_iff {x : LaurentSeries L} :
    x ∈ laurentBaseChange L F₀ ↔
      x ∈ Subfield.closure
        (Set.range (algebraMap L (LaurentSeries L)) ∪
          (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))) :=
  Iff.rfl

variable {L F₀} in

theorem coeffMap_mem_laurentBaseChange (σ : L ≃ₐ[ℚ] L) {x : LaurentSeries L}
    (hx : x ∈ laurentBaseChange L F₀) :
    coeffMap (σ : L →+* L) x ∈ laurentBaseChange L F₀ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [coeffMap_algebraMap]
        exact (laurentBaseChange L F₀).algebraMap_mem _
      · rw [coeffMap_coeffEmb]
        exact coeffEmb_mem_laurentBaseChange L hz
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end BaseChange

/-! ## The outbound interface

The rest of FLT reaches this segment through a handful of small declarations
rather than the headline theorem. The four below are the ones stated over
`coeffMap` / `coeffEmb`; their indegrees in FLT's dependency graph are 194
(`coeffMap_qExpand`, the most-shared declaration in the cone), 66, 32 and 19.
They are transcribed from their `Theorems/Thm_ModularCurve_*` wrappers in the pin
and deliberately **public**. -/

/-- `coeffMap` commutes with the `q`-substitution: extending coefficients and
substituting `q ↦ q ^ n` commute. -/
theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

/-- `coeffEmb` commutes with the `q`-substitution. -/
theorem coeffEmb_qExpand (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpand (algebraMap ℚ L) n x

/-- `coeffMap` preserves injectivity. -/
theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (coeffMap f) :=
  fun x y hxy => by
    ext k
    exact hf (by simpa using congrArg (fun z => HahnSeries.coeff z k) hxy)

/-- `coeffEmb` preserves injectivity: a Laurent series over `ℚ` is determined by
its coefficients, and `ℚ → L` is injective. -/
theorem coeffEmb_injective (L : Type*) [Field L] [Algebra ℚ L] :
    Function.Injective (coeffEmb L) :=
  coeffMap_injective (FaithfulSMul.algebraMap_injective ℚ L)

end ModularCurve

end
