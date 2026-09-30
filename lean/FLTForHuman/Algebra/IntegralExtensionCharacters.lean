/-
  Extending characters along an integral extension, the `ℤ̄`-valued
  characters of a finite `ℤ`-algebra, and the Galois conjugation of those
  characters over `ℂ`.

  Three generic algebra facts that the T-side eigenform extraction consumes:

  * `RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed` — a ring
    hom `χ : A →+* K` into an algebraically closed field whose kernel contains
    `ker (algebraMap A B)` extends along an integral extension `A → B`.
  * `Ideal.exists_ringHom_integralClosure_ker_eq` — every prime `𝔓` of a finite
    `ℤ`-algebra `T` whose contraction to `ℤ` is `⊥` is the kernel of a ring hom
    `T →+* integralClosure ℤ ℂ`.
  * `integralClosure.exists_complex_ringEquiv_apply_eq` — any two ring homs out
    of `integralClosure ℤ ℂ` differ by the action of a ring automorphism of `ℂ`.

  All three statements are the pin's `Theorems/` wrappers verbatim; the proofs
  are transcribed from the `P2M/Sol/S_*` files, pinned `aa2d8b3`:

  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Ideal_exists_ringHom_integralClosure_ker_eq.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_integralClosure_exists_complex_ringEquiv_apply_eq.lean

  The pin's blanket `import Mathlib` and the `P2M.Util` shims are replaced by the
  specific mathlib modules actually used; all of the S4b file's declarations
  except the target are `private`.
-/
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.IsGaloisGroup.Basic
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Algebra.Polynomial.Splits

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing; keep them literal (port convention).
set_option linter.style.haveILetI false

noncomputable section

open Ideal

/-- **Extending a character along an integral extension.** Stated verbatim from
`Theorems/Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed.lean`. -/
theorem RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed {A B K : Type*}
    [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] [Field K] [IsAlgClosed K]
    (χ : A →+* K) (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker χ) :
    ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = χ := by
  haveI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨Q, -, hQ, hQP⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker χ) (⊥ : Ideal B) hker
  haveI := hQ
  have hPker : ∀ a : A, a ∈ Q.comap (algebraMap A B) → χ a = 0 := fun a ha => by
    change a ∈ Ideal.under A Q at ha
    rw [hQP] at ha
    exact RingHom.mem_ker.mp ha
  let χbar : A ⧸ Q.comap (algebraMap A B) →+* K := Ideal.Quotient.lift _ χ hPker
  have hχbar_inj : Function.Injective χbar :=
    RingHom.lift_injective_of_ker_le_ideal _ hPker (le_of_eq hQP.symm)
  letI : Algebra (A ⧸ Q.comap (algebraMap A B)) K := χbar.toAlgebra
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : IsDomain (A ⧸ Q.comap (algebraMap A B)) := Ideal.Quotient.isDomain _
  haveI : Module.IsTorsionFree (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (A ⧸ Q.comap (algebraMap A B)) K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hχbar_inj
  let ψbar : (B ⧸ Q) →ₐ[A ⧸ Q.comap (algebraMap A B)] K := IsAlgClosed.lift
  refine ⟨ψbar.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun a => ?_⟩
  have h1 : Ideal.Quotient.mk Q (algebraMap A B a) =
      algebraMap (A ⧸ Q.comap (algebraMap A B)) (B ⧸ Q) (Ideal.Quotient.mk _ a) := rfl
  show ψbar (Ideal.Quotient.mk Q (algebraMap A B a)) = χ a
  rw [h1, ψbar.commutes]
  rfl

/-- **Primes of a finite `ℤ`-algebra as kernels of `ℤ̄`-valued characters.** Stated
verbatim from `Theorems/Thm_Ideal_exists_ringHom_integralClosure_ker_eq.lean`. -/
theorem Ideal.exists_ringHom_integralClosure_ker_eq {T : Type*} [CommRing T]
    [Module.Finite ℤ T] (𝔓 : Ideal T) (h𝔓 : 𝔓.IsPrime)
    (hint : ∀ n : ℤ, (n : T) ∈ 𝔓 → n = 0) :
    ∃ f : T →+* integralClosure ℤ ℂ, RingHom.ker f = 𝔓 := by
  classical
  haveI := h𝔓

  set D := T ⧸ 𝔓 with hD
  haveI : IsDomain D := Ideal.Quotient.isDomain 𝔓
  have hinjD : Function.Injective (algebraMap ℤ D) := by
    intro a b hab
    have h : ((a - b : ℤ) : T) ∈ 𝔓 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, Int.cast_sub, sub_eq_zero]
      simpa [Algebra.algebraMap_eq_smul_one] using hab
    exact sub_eq_zero.mp (hint _ h)
  haveI : CharZero D := by
    refine ⟨fun a b hab => ?_⟩
    have := hinjD (show algebraMap ℤ D (a : ℤ) = algebraMap ℤ D (b : ℤ) by simpa using hab)
    exact_mod_cast this
  haveI : @Module.IsTorsionFree ℤ D _ _ Algebra.toModule := by
    refine ⟨fun n hn => ?_⟩
    intro a b hab
    have hn0 : algebraMap ℤ D n ≠ 0 := (map_ne_zero_iff _ hinjD).mpr hn.ne_zero
    have h' : algebraMap ℤ D n * a = algebraMap ℤ D n * b := by
      simpa only [Algebra.smul_def] using hab
    exact mul_left_cancel₀ hn0 h'
  haveI : Module.Finite ℤ D :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ 𝔓).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ 𝔓)
  haveI : Algebra.IsIntegral ℤ D := inferInstance
  haveI : Algebra.IsAlgebraic ℤ D := ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩

  let φ : D →ₐ[ℤ] ℂ := IsAlgClosed.lift
  have hφker : RingHom.ker φ.toRingHom = ⊥ := by
    refine Ideal.eq_bot_of_under_eq_bot (R := ℤ) ?_
    refine eq_bot_iff.mpr fun n hn => ?_
    rw [Ideal.mem_under, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes] at hn
    simpa using hn
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro d hd
    have : d ∈ RingHom.ker φ.toRingHom := hd
    rw [hφker, Ideal.mem_bot] at this
    exact this

  have hmem : ∀ t : T, (φ.toRingHom.comp (Ideal.Quotient.mk 𝔓)) t ∈ integralClosure ℤ ℂ := by
    intro t
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) (Ideal.Quotient.mk 𝔓 t)).map φ
  refine ⟨(φ.toRingHom.comp (Ideal.Quotient.mk 𝔓)).codRestrict (integralClosure ℤ ℂ) hmem, ?_⟩
  ext t
  rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    apply hφinj
    rw [map_zero]
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    show φ (Ideal.Quotient.mk 𝔓 t) = 0
    rw [h, map_zero]

/-! ## Galois conjugation of the `ℤ̄`-valued characters

The pin's `S_integralClosure_exists_complex_ringEquiv_apply_eq.lean` (277 lines,
16 declarations): every two ring homs out of `integralClosure ℤ ℂ` differ by the
action of a ring automorphism of `ℂ`. The whole block above the target is
`private` here; the public surface is the single statement
`integralClosure.exists_complex_ringEquiv_apply_eq`. -/

namespace ZbarHomsConj

private theorem exists_ringEquiv_comp_eq {R S : Type*} [CommRing R] [Ring S]
    (φ ψ : R →+* S) (hker : RingHom.ker ψ = RingHom.ker φ)
    (hrange : Set.range ψ = Set.range φ) :
    ∃ τ : R ⧸ RingHom.ker φ ≃+* R ⧸ RingHom.ker φ,
      ∀ b : R, RingHom.kerLift φ (τ (Ideal.Quotient.mk _ b)) = ψ b := by

  let φb : R ⧸ RingHom.ker φ →+* S := RingHom.kerLift φ
  let ψb : R ⧸ RingHom.ker φ →+* S := Ideal.Quotient.lift _ ψ (fun a ha => by
    rw [← hker] at ha; exact (RingHom.mem_ker).mp ha)
  have hφb_inj : Function.Injective φb := RingHom.kerLift_injective φ
  have hψb_inj : Function.Injective ψb := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.lift_mk] at hq
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hker]
    exact (RingHom.mem_ker).mpr hq
  have hmem : ∀ q, ψb q ∈ φb.range := by
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [Ideal.Quotient.lift_mk]
    obtain ⟨c, hc⟩ : ψ b ∈ Set.range φ := hrange ▸ ⟨b, rfl⟩
    exact ⟨Ideal.Quotient.mk _ c, by rw [RingHom.kerLift_mk]; exact hc⟩
  let e₁ : R ⧸ RingHom.ker φ ≃+* φb.range :=
    RingEquiv.ofBijective (ψb.codRestrict φb.range hmem)
      ⟨fun x y hxy => hψb_inj (congrArg Subtype.val hxy), by
        rintro ⟨_, q, rfl⟩
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
        obtain ⟨c, hc⟩ : φ b ∈ Set.range ψ := hrange.symm ▸ ⟨b, rfl⟩
        refine ⟨Ideal.Quotient.mk _ c, Subtype.ext ?_⟩
        change ψb _ = φb _
        rw [Ideal.Quotient.lift_mk, RingHom.kerLift_mk]
        exact hc⟩
  let e₂ : R ⧸ RingHom.ker φ ≃+* φb.range :=
    RingEquiv.ofBijective φb.rangeRestrict
      ⟨fun x y hxy => hφb_inj (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective _⟩
  refine ⟨e₁.trans e₂.symm, fun b => ?_⟩
  have h2 : ∀ z, RingHom.kerLift φ z = (e₂ z : S) := fun z => rfl
  rw [h2, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  change ψb _ = _
  rw [Ideal.Quotient.lift_mk]

private theorem splits_map_int (B F : Type*) [CommRing B] [Field F] [IsAlgClosed F]
    [Algebra B F] [IsIntegralClosure B ℤ F] {p : Polynomial ℤ} (hp : p.Monic) :
    (p.map (algebraMap ℤ B)).Splits := by
  haveI : IsDomain B :=
    (IsIntegralClosure.algebraMap_injective B ℤ F).isDomain (algebraMap B F)
  refine Polynomial.Splits.of_splits_map_of_injective
    (IsIntegralClosure.algebraMap_injective B ℤ F) ?_ ?_
  · exact IsAlgClosed.splits _
  · intro a ha
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at ha
    have hne : p.map (algebraMap ℤ F) ≠ 0 := (hp.map _).ne_zero
    rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_map] at ha
    have hint : IsIntegral ℤ a := ⟨p, hp, ha⟩
    obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp hint
    exact ⟨b, hb⟩

private theorem range_eq_setOf_isIntegral {B : Type*} (F : Type*) [CommRing B] [Field F]
    [IsAlgClosed F] [Algebra B F] [IsIntegralClosure B ℤ F] {k : Type*} [Field k]
    (χ : B →+* k) :
    Set.range χ = {t | IsIntegral ℤ t} := by
  haveI : Algebra.IsIntegral ℤ B := IsIntegralClosure.isIntegral_algebra ℤ F
  haveI : IsDomain B :=
    (IsIntegralClosure.algebraMap_injective B ℤ F).isDomain (algebraMap B F)
  ext t
  constructor
  · rintro ⟨b, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) b).map χ.toIntAlgHom
  · rintro ⟨p, hp, hpt⟩
    have hs := splits_map_int B F hp
    have hq := hs.eq_prod_roots_of_monic (hp.map _)
    have hcomp : χ.comp (algebraMap ℤ B) = algebraMap ℤ k := RingHom.ext_int _ _
    have h0 : Polynomial.eval t ((p.map (algebraMap ℤ B)).map χ) = 0 := by
      rw [Polynomial.map_map, hcomp, Polynomial.eval_map]; exact hpt
    rw [hq, Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod,
      Multiset.prod_eq_zero_iff] at h0
    simp only [Multiset.map_map, Function.comp, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Multiset.mem_map] at h0
    obtain ⟨b, -, hb⟩ := h0
    exact ⟨b, (sub_eq_zero.mp hb).symm⟩

private theorem isAlgClosure_rat (F : Type*) [Field F] [CharZero F] [IsAlgClosed F]
    [Algebra.IsAlgebraic ℚ F] : IsAlgClosure ℚ F := ⟨‹_›, ‹_›⟩

private theorem isFractionRing_aux (B F : Type*) [CommRing B] [IsDomain B] [Field F]
    [CharZero F] [Algebra B F] [Algebra.IsAlgebraic ℚ F] [IsIntegralClosure B ℤ F] :
    IsFractionRing B F :=
  haveI : Algebra.IsAlgebraic ℤ F := IsFractionRing.comap_isAlgebraic_iff (K := ℚ) |>.mpr ‹_›
  IsIntegralClosure.isFractionRing_of_algebraic ℤ B
    (fun x hx => by simpa using hx)

private theorem core {B F : Type*} [CommRing B] [IsDomain B] [Field F] [CharZero F]
    [IsAlgClosed F] [Algebra B F] [Algebra.IsAlgebraic ℚ F] [IsIntegralClosure B ℤ F]
    {k : Type*} [Field k] (φ ψ : B →+* k) :
    ∃ σ : F ≃+* F, ∀ x y : B, algebraMap B F y = σ (algebraMap B F x) → φ x = ψ y := by
  haveI : IsAlgClosure ℚ F := isAlgClosure_rat F
  haveI : IsGalois ℚ F := IsAlgClosure.isGalois ℚ F
  haveI : IsFractionRing B F := isFractionRing_aux B F
  letI : MulSemiringAction Gal(F/ℚ) B := IsIntegralClosure.MulSemiringAction ℤ ℚ F B
  haveI : Algebra.IsIntegral ℤ B := IsIntegralClosure.isIntegral_algebra ℤ F
  haveI : SMulDistribClass Gal(F/ℚ) B F := inferInstance
  haveI : IsGaloisGroup Gal(F/ℚ) ℤ B := IsGaloisGroup.of_isFractionRing Gal(F/ℚ) ℤ B ℚ F
  haveI : Algebra.IsInvariant ℤ B Gal(F/ℚ) := inferInstance
  haveI : SMulCommClass Gal(F/ℚ) ℤ B := inferInstance
  have hinj : Function.Injective (algebraMap B F) := IsIntegralClosure.algebraMap_injective B ℤ F
  have hact : ∀ (g : Gal(F/ℚ)) (b : B), algebraMap B F (g • b) = g (algebraMap B F b) :=
    fun g b => algebraMap_galRestrict_apply ℤ g b

  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  haveI : ContinuousSMul Gal(F/ℚ) B := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro b
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {algebraMap B F b}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {algebraMap B F b}))
    intro g hg
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    rw [MulAction.mem_stabilizer_iff]
    apply hinj
    rw [hact]
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ _)

  set P : Ideal B := RingHom.ker φ with hP
  set Q : Ideal B := RingHom.ker ψ with hQ
  haveI hPp : P.IsPrime := RingHom.ker_isPrime φ
  haveI hQp : Q.IsPrime := RingHom.ker_isPrime ψ
  have hunder : P.under ℤ = Q.under ℤ := by
    simp only [Ideal.under, hP, hQ, RingHom.comap_ker]
    rw [RingHom.ext_int (φ.comp (algebraMap ℤ B)) (ψ.comp (algebraMap ℤ B))]
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := ℤ) (G := Gal(F/ℚ)) P Q hunder

  let ψ' : B →+* k := ψ.comp (MulSemiringAction.toRingHom Gal(F/ℚ) B g)
  have hψ' : ∀ b, ψ' b = ψ (g • b) := fun b => rfl
  have hker : RingHom.ker ψ' = RingHom.ker φ := by
    ext b
    rw [RingHom.mem_ker, hψ', ← RingHom.mem_ker, ← hQ, ← hP, hg]
    exact Ideal.smul_mem_pointwise_smul_iff
  have hrange : Set.range ψ' = Set.range φ := by
    rw [range_eq_setOf_isIntegral F ψ', range_eq_setOf_isIntegral F φ]

  obtain ⟨τ, hτ⟩ := exists_ringEquiv_comp_eq φ ψ' hker hrange
  have hτcomm : ∀ a : ℤ ⧸ P.under ℤ,
      τ (algebraMap (ℤ ⧸ P.under ℤ) (B ⧸ P) a) = algebraMap (ℤ ⧸ P.under ℤ) (B ⧸ P) a := by
    intro a
    obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hn : (Ideal.Quotient.mk (P.under ℤ)) n = ((n : ℤ) : ℤ ⧸ P.under ℤ) := by
      rw [← map_intCast (Ideal.Quotient.mk (P.under ℤ)) n, Int.cast_id]
    rw [hn, map_intCast, map_intCast]
  let τa : (B ⧸ P) ≃ₐ[ℤ ⧸ P.under ℤ] (B ⧸ P) := AlgEquiv.ofRingEquiv (f := τ) hτcomm
  obtain ⟨h, hh⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Gal(F/ℚ)) (P.under ℤ) P τa
  have hhb : ∀ b : B, φ ((h : Gal(F/ℚ)) • b) = ψ (g • b) := by
    intro b
    have h1 : Ideal.Quotient.mk P ((h : Gal(F/ℚ)) • b) = τ (Ideal.Quotient.mk P b) := by
      have := congrArg (fun f => f (Ideal.Quotient.mk P b)) hh
      exact this
    calc φ ((h : Gal(F/ℚ)) • b)
        = RingHom.kerLift φ (Ideal.Quotient.mk _ ((h : Gal(F/ℚ)) • b)) :=
          (RingHom.kerLift_mk φ _).symm
      _ = RingHom.kerLift φ (τ (Ideal.Quotient.mk P b)) := congrArg (RingHom.kerLift φ) h1
      _ = ψ' b := hτ b
      _ = ψ (g • b) := hψ' b

  refine ⟨((g * (h : Gal(F/ℚ))⁻¹ : Gal(F/ℚ)) : F ≃ₐ[ℚ] F).toRingEquiv, fun x y hxy => ?_⟩
  have hy : y = (g * (h : Gal(F/ℚ))⁻¹) • x := by
    apply hinj
    rw [hact, hxy]
    rfl
  rw [hy, mul_smul, ← hhb, smul_inv_smul]

private abbrev Qbar : Type := ↥(algebraicClosure ℚ ℂ)

private abbrev Zbar : Type := ↥(integralClosure ℤ ℂ)

private theorem mem_Qbar_of_mem_Zbar {x : ℂ} (hx : x ∈ integralClosure ℤ ℂ) :
    x ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  rw [mem_integralClosure_iff] at hx
  exact (hx.tower_top (A := ℚ)).isAlgebraic

private def zbarToQbar : Zbar →+* Qbar where
  toFun b := ⟨(b : ℂ), mem_Qbar_of_mem_Zbar b.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private instance algebraZbarQbar : Algebra Zbar Qbar := zbarToQbar.toAlgebra

@[simp] private theorem algebraMap_Zbar_Qbar_apply (b : Zbar) :
    ((algebraMap Zbar Qbar b : Qbar) : ℂ) = (b : ℂ) := rfl

private instance : IsScalarTower Zbar Qbar ℂ :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

private theorem isIntegralClosure_Zbar_Qbar :
    @IsIntegralClosure Zbar ℤ Qbar _ _ _ (Ring.toIntAlgebra Qbar) _ where
  algebraMap_injective := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : Qbar => (z : ℂ)) hxy
  isIntegral_iff := by
    intro x
    rw [← isIntegral_algHom_iff (algebraMap Qbar ℂ).toIntAlgHom (algebraMap Qbar ℂ).injective]
    constructor
    · intro hx
      refine ⟨⟨(x : ℂ), hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2

private theorem isAlgClosed_Qbar : IsAlgClosed Qbar := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed

private theorem isAlgebraic_Qbar : @Algebra.IsAlgebraic ℚ Qbar _ _ DivisionRing.toRatAlgebra := by
  convert algebraicClosure.isAlgebraic ℚ ℂ

private theorem exists_ringEquiv_extend (σ : Qbar ≃+* Qbar) :
    ∃ Sg : ℂ ≃+* ℂ, ∀ x : Qbar, Sg (x : ℂ) = (σ x : ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis Qbar ℂ
  haveI : IsAlgClosure (Algebra.adjoin Qbar (Set.range ((↑) : s → ℂ))) ℂ :=
    IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  set R := Algebra.adjoin Qbar (Set.range ((↑) : s → ℂ)) with hR
  let e : R ≃+* R :=
    (hs.1.aevalEquiv.symm.toRingEquiv.trans (MvPolynomial.mapEquiv s σ)).trans
      hs.1.aevalEquiv.toRingEquiv
  have he : ∀ x : Qbar, e (algebraMap Qbar R x) = algebraMap Qbar R (σ x) := by
    intro x
    simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes, MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply,
      MvPolynomial.map_C]
    rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rfl
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, fun x => ?_⟩
  have h1 : (x : ℂ) = algebraMap R ℂ (algebraMap Qbar R x) := by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  rw [h1, IsAlgClosure.equivOfEquiv_algebraMap, he, ← IsScalarTower.algebraMap_apply]
  rfl

private theorem main (k : Type*) [Field k] (φ ψ : integralClosure ℤ ℂ →+* k) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x y : integralClosure ℤ ℂ, (y : ℂ) = σ (x : ℂ) → φ x = ψ y := by
  haveI : IsAlgClosed Qbar := isAlgClosed_Qbar
  haveI : @Algebra.IsAlgebraic ℚ Qbar _ _ DivisionRing.toRatAlgebra := isAlgebraic_Qbar
  haveI : @IsIntegralClosure Zbar ℤ Qbar _ _ _ (Ring.toIntAlgebra Qbar) _ :=
    isIntegralClosure_Zbar_Qbar
  obtain ⟨σ, hσ⟩ := core (B := Zbar) (F := Qbar) φ ψ
  obtain ⟨Sg, hSg⟩ := exists_ringEquiv_extend σ
  refine ⟨Sg, fun x y hxy => hσ x y ?_⟩
  apply Subtype.ext
  change (y : ℂ) = ((σ (algebraMap Zbar Qbar x) : Qbar) : ℂ)
  rw [hxy, ← hSg]
  rfl

end ZbarHomsConj

/-- **Galois conjugation of the `ℤ̄`-valued characters.** Stated verbatim from
`Theorems/Thm_integralClosure_exists_complex_ringEquiv_apply_eq.lean`. -/
theorem integralClosure.exists_complex_ringEquiv_apply_eq (k : Type*) [Field k]
    (φ ψ : integralClosure ℤ ℂ →+* k) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x y : integralClosure ℤ ℂ, (y : ℂ) = σ (x : ℂ) → φ x = ψ y :=
  ZbarHomsConj.main k φ ψ

end
