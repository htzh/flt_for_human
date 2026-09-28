/-
  Three commutative-algebra facts over a complete local Noetherian base: finite
  modules are adically complete, finite local algebras are complete for their
  maximal-adic topology, and a finite algebra over a complete local Noetherian
  base is the product of its localisations at maximal ideals (each a finite,
  hence complete, module).

  The three public statements are the pin's `Theorems/` wrappers verbatim —
  `IsAdicComplete.of_module_finite`,
  `IsLocalRing.isAdicComplete_of_module_finite` and
  `Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite`.
  The proofs are ported from the pin's `P2M/Sol/S_IsAdicComplete_of_module_finite`,
  `P2M/Sol/S_IsLocalRing_isAdicComplete_of_module_finite` and
  `P2M/Sol/S_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite`
  (pinned `aa2d8b3`). The first two share a 100-line `Compare`/`ModuleFinite`
  prelude; it is written **once** here, `private`, as are the `Row5Aux`/`Row5`
  helpers of the third (playbook §7.1), so the checker's public-surface diff
  stays exact.

  The mathematics is math/018 §6.
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

-- The pin's proofs use `haveI`/`letI` in `Prop` goals; the port transcribes them
-- verbatim, so the style linter is off here as in the other ported proof files
-- (playbook §4).
set_option linter.style.haveILetI false

open IsLocalRing

universe u v w

section Compare

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I J : Ideal R}

private theorem smul_top_pow_le_of_le (hIJ : I ≤ J) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
  Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)

private theorem smul_top_pow_mul_le_of_pow_le {N : ℕ} (hJI : J ^ N ≤ I) (n : ℕ) :
    (J ^ (N * n) • ⊤ : Submodule R M) ≤ I ^ n • ⊤ := by
  rw [pow_mul]
  exact Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)

private theorem isHausdorff_of_le (hIJ : I ≤ J) [h : IsHausdorff J M] : IsHausdorff I M :=
  ⟨fun x hx => h.haus x fun n => (hx n).mono (smul_top_pow_le_of_le hIJ n)⟩

private theorem isHausdorff_of_pow_le {N : ℕ} (hJI : J ^ N ≤ I) [h : IsHausdorff I M] :
    IsHausdorff J M :=
  ⟨fun x hx => h.haus x fun n => (hx (N * n)).mono (smul_top_pow_mul_le_of_pow_le hJI n)⟩

private theorem isPrecomplete_of_le_of_pow_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I)
    [h : IsPrecomplete I M] : IsPrecomplete J M := by
  set N' := max N 1 with hN'
  have hJI' : J ^ N' ≤ I := (Ideal.pow_le_pow_right (le_max_left N 1)).trans hJI
  have hN1 : 1 ≤ N' := le_max_right N 1
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := h.prec (f := fun n => f (N' * n)) fun {m n} hmn =>
    (hf (Nat.mul_le_mul_left N' hmn)).mono (smul_top_pow_mul_le_of_pow_le hJI' m)
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n hN1)).trans ((hL n).mono (smul_top_pow_le_of_le hIJ n))

private theorem isPrecomplete_of_pow_le_of_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I)
    [h : IsPrecomplete J M] : IsPrecomplete I M := by
  set N' := max N 1 with hN'
  have hJI' : J ^ N' ≤ I := (Ideal.pow_le_pow_right (le_max_left N 1)).trans hJI
  have hN1 : 1 ≤ N' := le_max_right N 1
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := h.prec (f := f) fun {m n} hmn => (hf hmn).mono (smul_top_pow_le_of_le hIJ m)
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n hN1)).trans
    ((hL (N' * n)).mono (smul_top_pow_mul_le_of_pow_le hJI' n))

private theorem isAdicComplete_iff_of_le_of_pow_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by
  constructor
  · intro h
    haveI := isHausdorff_of_pow_le (M := M) hJI
    haveI := isPrecomplete_of_le_of_pow_le (M := M) hIJ hJI
    exact ⟨⟩
  · intro h
    haveI := isHausdorff_of_le (M := M) hIJ
    haveI := isPrecomplete_of_pow_le_of_le (M := M) hIJ hJI
    exact ⟨⟩

end Compare

section ModuleFinite

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

open AdicCompletion

private theorem isPrecomplete_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [IsPrecomplete I M] : IsPrecomplete I N := by
  rw [← of_surjective_iff]
  intro z
  obtain ⟨w, rfl⟩ := map_surjective I hf z
  obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I M w
  exact ⟨f x, (map_of I f x).symm⟩

private theorem isPrecomplete_pi (ι : Type*) [Fintype ι] [DecidableEq ι] [IsPrecomplete I R] :
    IsPrecomplete I (ι → R) := by
  rw [← of_surjective_iff]
  intro z
  choose x hx using fun j =>
    AdicCompletion.of_surjective I R (piEquivOfFintype I (fun _ : ι => R) z j)
  refine ⟨x, (piEquivOfFintype I (fun _ : ι => R)).injective ?_⟩
  funext j
  rw [piEquivOfFintype_apply, ← hx j]
  change map I (LinearMap.proj j) (of I (ι → R) x) = _
  rw [map_of]
  rfl

private theorem isPrecomplete_of_module_finite [IsPrecomplete I R] [Module.Finite R M] :
    IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I (Fin n)
  exact isPrecomplete_of_surjective I f hf

private theorem isAdicComplete_of_module_finite [IsNoetherianRing R] [IsAdicComplete I R]
    [Module.Finite R M] : IsAdicComplete I M :=
  haveI := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  haveI := isPrecomplete_of_module_finite I (M := M)
  ⟨⟩

end ModuleFinite

/-- Finite modules over a complete Noetherian ring are adically complete. Stated
verbatim from `Theorems/Thm_IsAdicComplete_of_module_finite.lean`. -/
theorem IsAdicComplete.of_module_finite {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsAdicComplete I M :=
  isAdicComplete_of_module_finite I

section Local

variable {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing T] [Algebra 𝒪 T]
  [Module.Finite 𝒪 T] [IsLocalRing T]

private theorem exists_maximalIdeal_pow_le_map :
    ∃ N, IsLocalRing.maximalIdeal T ^ N ≤ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 T) := by
  letI : Field (𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪) := Ideal.Quotient.field _
  haveI : Module.Finite (𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪)
      (T ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 T)) :=
    Module.Finite.of_restrictScalars_finite 𝒪 _ _
  haveI : IsArtinianRing (T ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 T)) :=
    IsArtinianRing.of_finite (𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪) _
  exact exists_maximalIdeal_pow_le_of_isArtinianRing_quotient _

private theorem isAdicComplete_maximalIdeal_of_module_finite [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [IsLocalHom (algebraMap 𝒪 T)] :
    IsAdicComplete (IsLocalRing.maximalIdeal T) T := by
  haveI h1 : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) T :=
    IsAdicComplete.of_module_finite (IsLocalRing.maximalIdeal 𝒪) T
  haveI h2 : IsAdicComplete ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 T)) T :=
    (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal 𝒪) T).mpr h1
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map (𝒪 := 𝒪) (T := T)
  exact (isAdicComplete_iff_of_le_of_pow_le (map_maximalIdeal_le (algebraMap 𝒪 T)) hN).mp h2

end Local

/-- A finite local algebra over a complete local Noetherian ring is complete for
its maximal-adic topology. Stated verbatim from
`Theorems/Thm_IsLocalRing_isAdicComplete_of_module_finite.lean`. -/
theorem IsLocalRing.isAdicComplete_of_module_finite {𝒪 : Type u} {T : Type v} [CommRing 𝒪]
    [IsNoetherianRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsLocalRing T]
    [IsLocalHom (algebraMap 𝒪 T)] : IsAdicComplete (IsLocalRing.maximalIdeal T) T :=
  isAdicComplete_maximalIdeal_of_module_finite (𝒪 := 𝒪) (T := T)

section Row5Aux

private lemma row5_idem_eq_of_isNilpotent_sub {B : Type} [CommRing B] {x y : B}
    (hx : IsIdempotentElem x) (hy : IsIdempotentElem y) (hd : IsNilpotent (x - y)) :
    x = y := by
  obtain ⟨m, hm⟩ := hd
  have hx2 : x * x = x := hx
  have hy2 : y * y = y := hy
  have h3 : (x - y) ^ 3 = x - y := by
    linear_combination (1 + x - 3 * y) * hx2 + (3 * x - 1 - y) * hy2
  have hodd : ∀ j : ℕ, (x - y) ^ (2 * j + 1) = x - y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h21 : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by ring
      calc (x - y) ^ (2 * (j + 1) + 1) = (x - y) ^ ((2 * j + 1) + 2) := by rw [h21]
        _ = (x - y) ^ (2 * j + 1) * (x - y) ^ 2 := by rw [pow_add]
        _ = (x - y) * (x - y) ^ 2 := by rw [ih]
        _ = (x - y) ^ 3 := by ring
        _ = x - y := h3
  have hz : x - y = 0 := by
    have h1 : x - y = (x - y) ^ (2 * m + 1) := (hodd m).symm
    have h2 : (x - y) ^ (2 * m + 1) = (x - y) ^ m * (x - y) ^ (m + 1) := by
      rw [← pow_add]
      congr 1
      ring
    rw [h1, h2, hm, zero_mul]
  exact sub_eq_zero.mp hz

private lemma row5_exists_completeOrthogonalIdempotents
    (R : Type) [CommRing R] [IsArtinianRing R] [Fintype (MaximalSpectrum R)] :
    ∃ e : MaximalSpectrum R → R, CompleteOrthogonalIdempotents e ∧
      (∀ P : MaximalSpectrum R, e P ∉ P.asIdeal) ∧
      (∀ P Q : MaximalSpectrum R, Q ≠ P → e P ∈ Q.asIdeal) := by
  classical
  have hsingle : ∀ P : MaximalSpectrum R,
      ∃ e : R, IsIdempotentElem e ∧ e ∉ P.asIdeal ∧
        ∀ Q : MaximalSpectrum R, Q ≠ P → e ∈ Q.asIdeal := by
    intro P
    have hclopen : IsClopen ({⟨P.asIdeal, P.isMaximal.isPrime⟩} : Set (PrimeSpectrum R)) :=
      isClopen_discrete _
    obtain ⟨e, he, hbo⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hclopen
    have hPbo : (⟨P.asIdeal, P.isMaximal.isPrime⟩ : PrimeSpectrum R) ∈
        (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) := by
      rw [← hbo]
      exact Set.mem_singleton _
    refine ⟨e, he, ?_, ?_⟩
    · exact (PrimeSpectrum.mem_basicOpen e _).mp hPbo
    · intro Q hQ
      by_contra hmem
      have hQbo : (⟨Q.asIdeal, Q.isMaximal.isPrime⟩ : PrimeSpectrum R) ∈
          (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R)) :=
        (PrimeSpectrum.mem_basicOpen e _).mpr hmem
      rw [← hbo] at hQbo
      have hQP : Q.asIdeal = P.asIdeal :=
        congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp hQbo)
      exact hQ (MaximalSpectrum.ext hQP)
  choose e hidem hnot hmem using hsingle
  have hprime_to_max : ∀ (I : Ideal R), I.IsPrime → ∃ Q : MaximalSpectrum R, Q.asIdeal = I := by
    intro I hI
    haveI := hI
    exact ⟨⟨I, IsArtinianRing.isMaximal_of_isPrime I⟩, rfl⟩
  have horth : ∀ P Q : MaximalSpectrum R, P ≠ Q → e P * e Q = 0 := by
    intro P Q hPQ
    have hid : IsIdempotentElem (e P * e Q) :=
      (hidem P).mul_of_commute (Commute.all _ _) (hidem Q)
    refine hid.eq_zero_of_isNilpotent ?_
    rw [nilpotent_iff_mem_prime]
    intro I hI
    obtain ⟨QI, rfl⟩ := hprime_to_max I hI
    by_cases h : QI = P
    · have hQne : QI ≠ Q := fun hq => hPQ (h.symm.trans hq)
      exact Ideal.mul_mem_left _ _ (hmem Q QI hQne)
    · exact Ideal.mul_mem_right _ _ (hmem P QI h)
  have horthS : OrthogonalIdempotents e := ⟨hidem, horth⟩
  have hsum : IsIdempotentElem (∑ P, e P) := horthS.isIdempotentElem_sum
  have hone : IsIdempotentElem (1 - ∑ P, e P) := hsum.one_sub
  have hnil : IsNilpotent (1 - ∑ P, e P) := by
    rw [nilpotent_iff_mem_prime]
    intro I hI
    obtain ⟨QI, rfl⟩ := hprime_to_max I hI
    have hsummem : (∑ P, e P) - e QI ∈ QI.asIdeal := by
      have hsplit : ∑ P, e P = e QI + ∑ P ∈ Finset.univ.erase QI, e P := by
        rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ QI)]
      rw [hsplit, add_sub_cancel_left]
      refine Ideal.sum_mem _ fun Q hQ => ?_
      exact hmem Q QI fun h => (Finset.mem_erase.mp hQ).1 h.symm
    have h1e : (1 : R) - e QI ∈ QI.asIdeal := by
      have h0 : e QI * (1 - e QI) ∈ QI.asIdeal := by
        rw [mul_sub, mul_one, (hidem QI).eq, sub_self]
        exact Ideal.zero_mem _
      rcases hI.mem_or_mem h0 with h | h
      · exact absurd h (hnot QI)
      · exact h
    have hrw : (1 : R) - ∑ P, e P = ((1 : R) - e QI) - ((∑ P, e P) - e QI) := by ring
    rw [hrw]
    exact Ideal.sub_mem _ h1e hsummem
  have hcomplete : ∑ P, e P = 1 := by
    have h0 := hone.eq_zero_of_isNilpotent hnil
    exact (sub_eq_zero.mp h0).symm
  exact ⟨e, ⟨horthS, hcomplete⟩, hnot, hmem⟩

end Row5Aux

section Row5

variable {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
  [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A]

omit [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in

private lemma row5_mapMax_le (P : Ideal A) [P.IsMaximal] :
    (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A) ≤ P := by
  have hint : Algebra.IsIntegral 𝒪 A := Algebra.IsIntegral.of_finite 𝒪 A
  have hmax : (P.comap (algebraMap 𝒪 A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap 𝒪 A) hint.isIntegral P
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal hmax]

omit [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
  [Module.Finite 𝒪 A] in

private lemma row5_mem_pow_iff (x : A) (n : ℕ) :
    x ∈ ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) ^ n ↔
      x ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ n • ⊤ : Submodule 𝒪 A) := by
  rw [Ideal.smul_top_eq_map, ← Ideal.map_pow, Submodule.restrictScalars_mem]

omit [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in

private lemma row5_isArtinian_quotient :
    IsArtinianRing (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) := by
  set 𝔪 := IsLocalRing.maximalIdeal 𝒪 with h𝔪
  set J := 𝔪.map (algebraMap 𝒪 A) with hJ
  letI : Field (𝒪 ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  letI : Algebra (𝒪 ⧸ 𝔪) (A ⧸ J) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  haveI : IsScalarTower 𝒪 (𝒪 ⧸ 𝔪) (A ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : Module.Finite 𝒪 (A ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒪 J).toLinearMap
      (Ideal.Quotient.mkₐ_surjective 𝒪 J)
  haveI : Module.Finite (𝒪 ⧸ 𝔪) (A ⧸ J) := Module.Finite.of_restrictScalars_finite 𝒪 _ _
  exact isArtinian_of_tower (𝒪 ⧸ 𝔪) inferInstance

private noncomputable def row5_maxSpecEquiv :
    MaximalSpectrum A ≃
      MaximalSpectrum (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) where
  toFun P :=
    ⟨P.asIdeal.map (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))), by
      haveI := P.isMaximal
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)))
          Ideal.Quotient.mk_surjective P.isMaximal with h | h
      · exfalso
        have hcm := Ideal.comap_map_of_surjective
          (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)))
          Ideal.Quotient.mk_surjective P.asIdeal
        rw [h, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
          sup_eq_left.mpr (row5_mapMax_le A P.asIdeal)] at hcm
        exact P.isMaximal.ne_top hcm.symm
      · exact h⟩
  invFun Q :=
    ⟨Q.asIdeal.comap (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))), by
      haveI := Q.isMaximal
      exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective⟩
  left_inv P := by
    haveI := P.isMaximal
    refine MaximalSpectrum.ext ?_
    have hcm := Ideal.comap_map_of_surjective
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)))
      Ideal.Quotient.mk_surjective P.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (row5_mapMax_le A P.asIdeal)] at hcm
    exact hcm
  right_inv Q := by
    haveI := Q.isMaximal
    refine MaximalSpectrum.ext ?_
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q.asIdeal

private lemma row5_lift_idempotent (J : Ideal A)
    (hJpow : ∀ (y : A) (n : ℕ), y ∈ J ^ n ↔
      y ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ n • ⊤ : Submodule 𝒪 A))
    (ē : A ⧸ J) (hē : IsIdempotentElem ē) :
    ∃ e : A, IsIdempotentElem e ∧ Ideal.Quotient.mk J e = ē := by
  classical
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) A :=
    IsAdicComplete.of_module_finite (IsLocalRing.maximalIdeal 𝒪) A
  have hlift : ∀ n : ℕ, ∃ x : A,
      IsIdempotentElem (Ideal.Quotient.mk (J ^ (n + 1)) x) ∧ Ideal.Quotient.mk J x = ē := by
    intro n
    have hle : J ^ (n + 1) ≤ J := Ideal.pow_le_self (Nat.succ_ne_zero n)
    have hker : ∀ x ∈ RingHom.ker (Ideal.Quotient.factor hle), IsNilpotent x := by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hy : y ∈ J := by
        rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
        exact hx
      exact ⟨n + 1, by
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_mem_pow hy (n + 1)⟩
    obtain ⟨y₀, hy₀⟩ := Ideal.Quotient.mk_surjective (I := J) ē
    obtain ⟨etil, hetil, hetil_eq⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent
      (f := Ideal.Quotient.factor hle) hker ē
      ⟨Ideal.Quotient.mk (J ^ (n + 1)) y₀, by rw [Ideal.Quotient.factor_mk, hy₀]⟩ hē
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := J ^ (n + 1)) etil
    refine ⟨x, by rw [hx]; exact hetil, ?_⟩
    rw [← Ideal.Quotient.factor_mk hle, hx, hetil_eq]
  choose f hfidem hfē using hlift
  have hsub : ∀ {m n : ℕ}, m ≤ n → f n - f m ∈ J ^ (m + 1) := by
    intro m n hmn
    have hle : J ^ (n + 1) ≤ J ^ (m + 1) := Ideal.pow_le_pow_right (by omega)
    have h1 : IsIdempotentElem (Ideal.Quotient.mk (J ^ (m + 1)) (f n)) := by
      have := (hfidem n).map (Ideal.Quotient.factor hle)
      rwa [Ideal.Quotient.factor_mk] at this
    have h2 : IsIdempotentElem (Ideal.Quotient.mk (J ^ (m + 1)) (f m)) := hfidem m
    have hdJ : f n - f m ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hfē n, hfē m, sub_self]
    have hnil : IsNilpotent
        (Ideal.Quotient.mk (J ^ (m + 1)) (f n) - Ideal.Quotient.mk (J ^ (m + 1)) (f m)) := by
      refine ⟨m + 1, ?_⟩
      rw [← map_sub, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hdJ (m + 1)
    have heq := row5_idem_eq_of_isNilpotent_sub h1 h2 hnil
    rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at heq
  have hconsist : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD ((IsLocalRing.maximalIdeal 𝒪) ^ m • ⊤ : Submodule 𝒪 A)] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have hJm : f n - f m ∈ J ^ m := Ideal.pow_le_pow_right (Nat.le_succ m) (hsub hmn)
    have : f m - f n ∈ J ^ m := by
      simpa using (neg_mem hJm : -(f n - f m) ∈ J ^ m)
    exact (hJpow _ m).mp this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete)
    fun {m n} hmn => hconsist hmn
  have hLn : ∀ n : ℕ, L - f n ∈ J ^ n := by
    intro n
    have hmem := (hJpow _ n).mpr (SModEq.sub_mem.mp (hL n))
    simpa using (neg_mem hmem : -(f n - L) ∈ J ^ n)
  refine ⟨L, ?_, ?_⟩
  · have hmem : ∀ n : ℕ, L * L - L ∈ J ^ n := by
      intro n
      have h1 : L * L - f n * f n ∈ J ^ n := by
        have hdecomp : L * L - f n * f n = (L - f n) * L + f n * (L - f n) := by ring
        rw [hdecomp]
        exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (hLn n))
          (Ideal.mul_mem_left _ _ (hLn n))
      have h2 : f n * f n - f n ∈ J ^ n := by
        have := hfidem n
        rw [IsIdempotentElem, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at this
        exact Ideal.pow_le_pow_right (Nat.le_succ n) this
      have h3 : f n - L ∈ J ^ n := by
        simpa using (neg_mem (hLn n) : -(L - f n) ∈ J ^ n)
      have hdecomp : L * L - L = (L * L - f n * f n) + (f n * f n - f n) + (f n - L) := by ring
      rw [hdecomp]
      exact Ideal.add_mem _ (Ideal.add_mem _ h1 h2) h3
    have := IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal 𝒪)
      (M := A)) (L * L - L) fun n => SModEq.zero.mpr ((hJpow _ n).mp (hmem n))
    exact sub_eq_zero.mp this
  · have h1 : L - f 1 ∈ J := by
      have := hLn 1
      rwa [pow_one] at this
    rw [← hfē 1, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact h1

private lemma row5_idem_eq_zero_of_mem (J : Ideal A)
    (hJpow : ∀ (y : A) (n : ℕ), y ∈ J ^ n ↔
      y ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ n • ⊤ : Submodule 𝒪 A))
    (x : A) (hx : IsIdempotentElem x) (hxJ : x ∈ J) : x = 0 := by
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) A :=
    IsAdicComplete.of_module_finite (IsLocalRing.maximalIdeal 𝒪) A
  have hxn : ∀ n : ℕ, x ∈ J ^ n := by
    intro n
    have hidem : IsIdempotentElem (Ideal.Quotient.mk (J ^ n) x) := hx.map _
    have hnil : IsNilpotent (Ideal.Quotient.mk (J ^ n) x) := ⟨n, by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hxJ n⟩
    have := hidem.eq_zero_of_isNilpotent hnil
    rwa [Ideal.Quotient.eq_zero_iff_mem] at this
  exact IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal 𝒪)
    (M := A)) x fun n => SModEq.zero.mpr ((hJpow x n).mp (hxn n))

include 𝒪 in
omit [IsNoetherianRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] in

private lemma row5_finite_maxSpec : Finite (MaximalSpectrum A) := by
  haveI : IsArtinianRing (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :=
    row5_isArtinian_quotient A
  haveI : Finite
      (MaximalSpectrum (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))) := by
    haveI : Finite {I : Ideal (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) //
        I.IsMaximal} := (IsArtinianRing.setOfPred_isMaximal_finite
      (A ⧸ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A))).to_subtype
    exact Finite.of_equiv _ (MaximalSpectrum.equivSubtype _).symm
  exact Finite.of_equiv _ (row5_maxSpecEquiv (𝒪 := 𝒪) A).symm

include 𝒪 in

private lemma row5_lifted_idempotents [Fintype (MaximalSpectrum A)] :
    ∃ e : MaximalSpectrum A → A, CompleteOrthogonalIdempotents e ∧
      (∀ P : MaximalSpectrum A, e P ∉ P.asIdeal) ∧
      (∀ P Q : MaximalSpectrum A, Q ≠ P → e P ∈ Q.asIdeal) := by
  classical
  set J := (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A) with hJdef
  have hJpow : ∀ (y : A) (n : ℕ), y ∈ J ^ n ↔
      y ∈ ((IsLocalRing.maximalIdeal 𝒪) ^ n • ⊤ : Submodule 𝒪 A) := row5_mem_pow_iff A
  haveI hart : IsArtinianRing (A ⧸ J) := row5_isArtinian_quotient (𝒪 := 𝒪) A
  letI : Fintype (MaximalSpectrum (A ⧸ J)) :=
    Fintype.ofEquiv _ (row5_maxSpecEquiv (𝒪 := 𝒪) A)
  obtain ⟨ē, hēco, hēnot, hēmem⟩ := row5_exists_completeOrthogonalIdempotents (A ⧸ J)
  set Φ := row5_maxSpecEquiv (𝒪 := 𝒪) A with hΦdef
  have hlift : ∀ P : MaximalSpectrum A, ∃ x : A, IsIdempotentElem x ∧
      Ideal.Quotient.mk J x = ē (Φ P) := fun P =>
    row5_lift_idempotent A J hJpow (ē (Φ P)) (hēco.idem _)
  choose e heidem hemk using hlift
  have horth : ∀ P Q : MaximalSpectrum A, P ≠ Q → e P * e Q = 0 := by
    intro P Q hPQ
    refine row5_idem_eq_zero_of_mem A J hJpow _
      ((heidem P).mul_of_commute (Commute.all _ _) (heidem Q)) ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, hemk, hemk]
    exact hēco.ortho fun h => hPQ (Φ.injective h)
  have horthS : OrthogonalIdempotents e := ⟨heidem, horth⟩
  have hcomplete : ∑ P, e P = 1 := by
    have hsum : IsIdempotentElem (∑ P, e P) := horthS.isIdempotentElem_sum
    have hone : IsIdempotentElem (1 - ∑ P, e P) := hsum.one_sub
    have hmem1 : (1 : A) - ∑ P, e P ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_sum]
      have hre : ∑ P : MaximalSpectrum A, Ideal.Quotient.mk J (e P) = ∑ P, ē (Φ P) :=
        Finset.sum_congr rfl fun P _ => hemk P
      rw [hre, Equiv.sum_comp Φ ē, hēco.complete, sub_self]
    have := row5_idem_eq_zero_of_mem A J hJpow _ hone hmem1
    exact (sub_eq_zero.mp this).symm
  refine ⟨e, ⟨horthS, hcomplete⟩, ?_, ?_⟩
  · intro P hP
    refine hēnot (Φ P) ?_
    rw [← hemk P]
    exact Ideal.mem_map_of_mem _ hP
  · intro P Q hQP
    have hΦne : Φ Q ≠ Φ P := fun h => hQP (Φ.injective h)
    have hmem' : ē (Φ P) ∈ (Φ Q).asIdeal := hēmem (Φ P) (Φ Q) hΦne
    have hmk : Ideal.Quotient.mk J (e P) ∈ Q.asIdeal.map (Ideal.Quotient.mk J) := by
      rw [hemk P]
      exact hmem'
    have hcm : e P ∈ (Q.asIdeal.map (Ideal.Quotient.mk J)).comap (Ideal.Quotient.mk J) :=
      Ideal.mem_comap.mpr hmk
    haveI := Q.isMaximal
    rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (row5_mapMax_le A Q.asIdeal)] at hcm

private lemma row5_isLocalization (P : MaximalSpectrum A) (e : A) (he : IsIdempotentElem e)
    (hnot : e ∉ P.asIdeal) (hmem : ∀ Q : MaximalSpectrum A, Q ≠ P → e ∈ Q.asIdeal) :
    IsLocalization P.asIdeal.primeCompl (A ⧸ Ideal.span {1 - e}) := by
  haveI := P.isMaximal
  have h1eP : 1 - e ∈ P.asIdeal := by
    have h0 : e * (1 - e) ∈ P.asIdeal := by
      rw [mul_sub, mul_one, he.eq, sub_self]
      exact Ideal.zero_mem _
    rcases P.isMaximal.isPrime.mem_or_mem h0 with h | h
    · exact absurd h hnot
    · exact h
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, hs⟩
    by_contra hunit
    obtain ⟨M, hM, hsM⟩ := Ideal.exists_le_maximal
      (Ideal.span {Ideal.Quotient.mk (Ideal.span {1 - e}) s})
      (fun htop => hunit (by
        rw [Ideal.span_singleton_eq_top] at htop
        exact htop))
    have hsM' : Ideal.Quotient.mk (Ideal.span {1 - e}) s ∈ M :=
      hsM (Ideal.subset_span rfl)
    haveI := hM
    have hQmax : (M.comap (Ideal.Quotient.mk (Ideal.span {1 - e}))).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    set Q : MaximalSpectrum A := ⟨M.comap (Ideal.Quotient.mk (Ideal.span {1 - e})), hQmax⟩
    have h1eQ : 1 - e ∈ Q.asIdeal := by
      show 1 - e ∈ M.comap (Ideal.Quotient.mk (Ideal.span {1 - e}))
      rw [Ideal.mem_comap]
      have hz : Ideal.Quotient.mk (Ideal.span {1 - e}) (1 - e) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
      rw [hz]
      exact M.zero_mem
    have hQP : Q = P := by
      by_contra hQP
      have heQ : e ∈ Q.asIdeal := hmem Q hQP
      have : (1 : A) ∈ Q.asIdeal := by
        have := Ideal.add_mem Q.asIdeal h1eQ heQ
        simpa using this
      exact Q.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr this)
    have hsP : s ∈ P.asIdeal := by
      rw [← hQP]
      exact Ideal.mem_comap.mpr hsM'
    exact hs hsP
  · intro z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨a, 1⟩, by simpa using ha.symm⟩
  · intro x y hxy
    have hsub : x - y ∈ Ideal.span {1 - e} := by
      rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      exact hxy
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hsub
    refine ⟨⟨e, hnot⟩, ?_⟩
    have h0 : e * (1 - e) = 0 := by
      rw [mul_sub, mul_one, he.eq, sub_self]
    have hxy0 : e * (x - y) = 0 := by
      rw [ht, ← mul_assoc, h0, zero_mul]
    have : e * x - e * y = 0 := by
      rw [← mul_sub]
      exact hxy0
    exact sub_eq_zero.mp this

end Row5

/-- The structure theorem for finite algebras over a complete local Noetherian
base. Stated verbatim from
`Theorems/Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite.lean`. -/
theorem Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] :
    Finite (MaximalSpectrum A) ∧
    Function.Bijective
      (RingHom.pi fun I : MaximalSpectrum A =>
        algebraMap A (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A, Module.Finite 𝒪 (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A,
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime I.asIdeal))
        (Localization.AtPrime I.asIdeal)) := by
  classical
  have hfin : Finite (MaximalSpectrum A) := row5_finite_maxSpec (𝒪 := 𝒪) A
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  obtain ⟨e, heco, henot, hemem⟩ := row5_lifted_idempotents (𝒪 := 𝒪) A
  have hloc : ∀ P : MaximalSpectrum A,
      IsLocalization P.asIdeal.primeCompl (A ⧸ Ideal.span {1 - e P}) := fun P =>
    row5_isLocalization A P (e P) (heco.idem P) (henot P) fun Q hQ => hemem P Q hQ
  have ψ : ∀ P : MaximalSpectrum A,
      (A ⧸ Ideal.span {1 - e P}) ≃ₐ[A] Localization.AtPrime P.asIdeal := fun P =>
    haveI := hloc P
    IsLocalization.algEquiv P.asIdeal.primeCompl _ _
  have hsurjloc : ∀ P : MaximalSpectrum A,
      Function.Surjective (algebraMap A (Localization.AtPrime P.asIdeal)) := by
    intro P z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective ((ψ P).symm z)
    refine ⟨a, ?_⟩
    have hψ := congrArg (ψ P) ha
    rwa [← Ideal.Quotient.algebraMap_eq, AlgEquiv.commutes,
      AlgEquiv.apply_symm_apply] at hψ
  have hfinloc : ∀ P : MaximalSpectrum A,
      Module.Finite 𝒪 (Localization.AtPrime P.asIdeal) := fun P =>
    Module.Finite.of_surjective (IsScalarTower.toAlgHom 𝒪 A _).toLinearMap (hsurjloc P)
  refine ⟨hfin, ?_, hfinloc, ?_⟩
  · have hΨ := heco.bijective_pi
    have hcomp : ⇑(RingHom.pi fun P : MaximalSpectrum A =>
        algebraMap A (Localization.AtPrime P.asIdeal)) =
        ⇑(RingEquiv.piCongrRight fun P => (ψ P).toRingEquiv) ∘
          ⇑(RingHom.pi fun P : MaximalSpectrum A =>
            Ideal.Quotient.mk (Ideal.span {1 - e P})) := by
      funext a
      funext P
      show algebraMap A (Localization.AtPrime P.asIdeal) a =
        ψ P (Ideal.Quotient.mk (Ideal.span {1 - e P}) a)
      rw [← Ideal.Quotient.algebraMap_eq, AlgEquiv.commutes]
    rw [hcomp]
    exact (RingEquiv.piCongrRight fun P => (ψ P).toRingEquiv).bijective.comp hΨ
  · intro P
    haveI := hfinloc P
    haveI : IsLocalHom (algebraMap 𝒪 (Localization.AtPrime P.asIdeal)) := by
      constructor
      intro a ha
      by_contra hna
      have hm : a ∈ IsLocalRing.maximalIdeal 𝒪 := hna
      have h1 : algebraMap 𝒪 A a ∈ P.asIdeal :=
        row5_mapMax_le (𝒪 := 𝒪) A P.asIdeal (Ideal.mem_map_of_mem _ hm)
      have h2 : algebraMap A (Localization.AtPrime P.asIdeal) (algebraMap 𝒪 A a) ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P.asIdeal _).mpr h1
      rw [← IsScalarTower.algebraMap_apply] at h2
      exact h2 ha
    exact IsLocalRing.isAdicComplete_of_module_finite (𝒪 := 𝒪)
      (T := Localization.AtPrime P.asIdeal)
