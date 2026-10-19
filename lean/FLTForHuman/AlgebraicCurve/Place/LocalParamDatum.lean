/-
The local parameter at a complex place, and the meromorphic-order dictionary: the
third and last `localParam` leaf of the Deligne–Serre cone. The `LocalParam` block of
the pin first rewrites the place calculus it needs (imported here, see below), then
builds the `WithTop ℤ`-valued order `τ` with its six laws, packages the chart data of
the engine (`MeroRealize.main`) as `structure Datum` with its order `n`, its valuation
`val`, its place `place` and the dictionary `ord_place : (D.place z).ord f = D.n z f`,
and lands the chart `Datum.γ : ℂ → Place ℂ F`. The headline
`exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex` assembles `main` and
`Datum.γ` into the wrapper's statement: a disc on which `γ 0 = v`,
`ord_{γ z}(t - z) = 1`, and the meromorphic reading of `evalAt` has order `(γ z).ord f`.
Statements are transcribed verbatim from the pinned FLT proof
(`anthropics/fermats-last-theorem`, `aa2d8b3`); only proof bodies are adapted to
mathlib `v4.34.0`.

The pin's second prelim copy (pin lines 625–694, ten declarations) is imported, not
reproduced: nine are `Place.*` in `Place/OrdCalculus.lean`, `Defs/PushPull.lean`,
`Defs/Repartitions.lean` and `Defs/PlaceCalculus.lean`, and the tenth,
`eq_of_forall_ord_eq`, is `Place.eq_of_forall_ord_eq` in `Place/OrdCalculus.lean` as
well. The module therefore declares only the `Datum` layer: 39 declarations and the
headline, 40 checked statements. The one linter narrowing is
`set_option linter.style.haveILetI false` on `Datum.place`, whose instance wall the pin
needs literal. Role: tier 1, the `Datum` layer over `Place/MeroRealize.lean`.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean
-/
import FLTForHuman.AlgebraicCurve.Place.MeroRealize
import FLTForHuman.AlgebraicCurve.Place.OrdCalculus
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.RingTheory.Algebraic.Basic

set_option autoImplicit false

noncomputable section

open Filter Topology Metric FormalMultilinearSeries Polynomial

namespace AlgebraicCurve

namespace Place

namespace LocalParam

section Tau

open WithZero

def τ (a : WithTop ℤ) : WithZero (Multiplicative ℤ) :=
  WithTop.recTopCoe (C := fun _ => WithZero (Multiplicative ℤ)) 0 (fun k : ℤ => exp (-k)) a

@[scoped simp] theorem τ_top : τ ⊤ = 0 := rfl

@[scoped simp] theorem τ_coe (k : ℤ) : τ k = exp (-k) := rfl

theorem τ_add (a b : WithTop ℤ) : τ (a + b) = τ a * τ b := by
  induction a with
  | top => simp
  | coe a =>
    induction b with
    | top => simp
    | coe b => rw [← WithTop.coe_add, τ_coe, τ_coe, τ_coe, neg_add, exp_add]

theorem τ_anti {a b : WithTop ℤ} (h : a ≤ b) : τ b ≤ τ a := by
  induction b with
  | top => simp
  | coe b =>
    induction a with
    | top => exact absurd h (by simp)
    | coe a =>
      rw [τ_coe, τ_coe, exp_le_exp]
      have : a ≤ b := by exact_mod_cast h
      omega

theorem τ_le_one_iff {a : WithTop ℤ} : τ a ≤ 1 ↔ 0 ≤ a := by
  induction a with
  | top => simp
  | coe a =>
    rw [τ_coe, ← exp_zero, exp_le_exp, WithTop.coe_nonneg]
    omega

theorem τ_eq_zero_iff {a : WithTop ℤ} : τ a = 0 ↔ a = ⊤ := by
  induction a with
  | top => simp
  | coe a => simp [τ_coe, exp_ne_zero]

end Tau

section Main

variable {F : Type*} [Field F] [Algebra ℂ F]

structure Datum (F : Type*) [Field F] [Algebra ℂ F] where

  t : F

  ρ : ℝ

  G : F → ℂ → ℂ
  hG : ∀ f : F, MeromorphicOn (G f) (ball (0 : ℂ) ρ)
  hadd : ∀ z ∈ ball (0 : ℂ) ρ, ∀ f g : F, G (f + g) =ᶠ[𝓝[≠] z] G f + G g
  hmul : ∀ z ∈ ball (0 : ℂ) ρ, ∀ f g : F, G (f * g) =ᶠ[𝓝[≠] z] G f * G g
  hC : ∀ z ∈ ball (0 : ℂ) ρ, ∀ c : ℂ, G (algebraMap ℂ F c) =ᶠ[𝓝[≠] z] fun _ => c
  ht : ∀ z ∈ ball (0 : ℂ) ρ, G t =ᶠ[𝓝[≠] z] fun u => u

namespace Datum

variable (D : Datum F)

def n (z : ℂ) (f : F) : WithTop ℤ := meromorphicOrderAt (D.G f) z

section AtPoint

variable {z : ℂ} (hz : z ∈ ball (0 : ℂ) D.ρ)
include hz

theorem meromorphicAt (f : F) : MeromorphicAt (D.G f) z := D.hG f z hz

theorem n_mul (f g : F) : D.n z (f * g) = D.n z f + D.n z g := by
  unfold n
  rw [meromorphicOrderAt_congr (D.hmul z hz f g),
    meromorphicOrderAt_mul (D.meromorphicAt hz f) (D.meromorphicAt hz g)]

theorem min_le_n_add (f g : F) : min (D.n z f) (D.n z g) ≤ D.n z (f + g) := by
  unfold n
  rw [meromorphicOrderAt_congr (D.hadd z hz f g)]
  exact meromorphicOrderAt_add (D.meromorphicAt hz f) (D.meromorphicAt hz g)

theorem n_algebraMap (c : ℂ) : D.n z (algebraMap ℂ F c) = if c = 0 then ⊤ else 0 := by
  classical
  unfold n
  rw [meromorphicOrderAt_congr (D.hC z hz c), meromorphicOrderAt_const]

theorem n_one : D.n z 1 = 0 := by
  simpa using D.n_algebraMap hz 1

theorem n_zero : D.n z 0 = ⊤ := by
  simpa using D.n_algebraMap hz 0

theorem n_ne_top {f : F} (hf : f ≠ 0) : D.n z f ≠ ⊤ := by
  intro h
  have := D.n_mul hz f f⁻¹
  rw [mul_inv_cancel₀ hf, D.n_one hz, h, top_add] at this
  exact WithTop.zero_ne_top this

theorem n_pow (f : F) (m : ℕ) : D.n z (f ^ m) = m • D.n z f := by
  induction m with
  | zero => rw [pow_zero, zero_smul]; exact D.n_one hz
  | succ m ih => rw [pow_succ, D.n_mul hz, ih, succ_nsmul]

theorem n_t_sub : D.n z (D.t - algebraMap ℂ F z) = 1 := by
  unfold n
  have h : D.G (D.t - algebraMap ℂ F z) =ᶠ[𝓝[≠] z] fun u => u - z := by
    have h1 := D.hadd z hz D.t (algebraMap ℂ F (-z))
    have e : D.t - algebraMap ℂ F z = D.t + algebraMap ℂ F (-z) := by
      rw [map_neg, sub_eq_add_neg]
    rw [e]
    filter_upwards [h1, D.ht z hz, D.hC z hz (-z)] with u hu1 hu2 hu3
    rw [hu1, Pi.add_apply, hu2, hu3]
    ring
  rw [meromorphicOrderAt_congr h, meromorphicOrderAt_id_sub_const]

theorem t_sub_ne_zero : D.t - algebraMap ℂ F z ≠ 0 := by
  intro h
  have h1 := D.n_t_sub hz
  rw [h, D.n_zero hz] at h1
  exact WithTop.top_ne_one h1

def val : Valuation F (WithZero (Multiplicative ℤ)) where
  toFun f := τ (D.n z f)
  map_zero' := by simp only [D.n_zero hz, τ_top]
  map_one' := by simp only [D.n_one hz]; rfl
  map_mul' f g := by simp only [D.n_mul hz, τ_add]
  map_add_le_max' f g := by
    refine (τ_anti (D.min_le_n_add hz f g)).trans ?_
    rcases min_choice (D.n z f) (D.n z g) with h | h <;> rw [h]
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem val_apply (f : F) : D.val hz f = τ (D.n z f) := rfl

theorem val_le_one_iff (f : F) : D.val hz f ≤ 1 ↔ 0 ≤ D.n z f := by
  rw [val_apply, τ_le_one_iff]

theorem isNontrivial_val : (D.val hz).IsNontrivial := by
  refine ⟨D.t - algebraMap ℂ F z, ?_, ?_⟩
  · rw [val_apply, D.n_t_sub hz]
    exact WithZero.exp_ne_zero
  · rw [val_apply, D.n_t_sub hz]
    show WithZero.exp (-(1 : ℤ)) ≠ 1
    rw [← WithZero.exp_zero, Ne, WithZero.exp_inj]
    decide

theorem n_t_sub_inv : D.n z (D.t - algebraMap ℂ F z)⁻¹ = (-1 : ℤ) := by
  have h := D.n_mul hz (D.t - algebraMap ℂ F z) (D.t - algebraMap ℂ F z)⁻¹
  rw [mul_inv_cancel₀ (D.t_sub_ne_zero hz), D.n_one hz, D.n_t_sub hz] at h
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
    (D.n_ne_top hz (inv_ne_zero (D.t_sub_ne_zero hz)))
  rw [← hk] at h ⊢
  have h' : (0 : ℤ) = 1 + k := by exact_mod_cast h
  congr 1
  omega

set_option linter.style.haveILetI false in
def place : Place ℂ F where
  toValuationSubring := (D.val hz).valuationSubring
  algebraMap_mem' c := by
    rw [Valuation.mem_valuationSubring_iff, val_le_one_iff, D.n_algebraMap hz]
    split_ifs <;> simp
  ne_top' := by
    intro h
    have hmem : (D.t - algebraMap ℂ F z)⁻¹ ∈ (D.val hz).valuationSubring := by
      rw [h]; trivial
    rw [Valuation.mem_valuationSubring_iff, val_le_one_iff, D.n_t_sub_inv hz] at hmem
    exact absurd (WithTop.coe_nonneg.mp hmem) (by decide)
  isPrincipalIdealRing' := by
    haveI : (D.val hz).IsNontrivial := D.isNontrivial_val hz
    exact Valuation.valuationSubring_isPrincipalIdealRing _

theorem mem_place_iff (f : F) : f ∈ (D.place hz).toValuationSubring ↔ 0 ≤ D.n z f := by
  show f ∈ (D.val hz).valuationSubring ↔ _
  rw [Valuation.mem_valuationSubring_iff, val_le_one_iff]

theorem n_eq_zero_of_isUnit {f : F} (hf : f ∈ (D.place hz).toValuationSubring)
    (hu : IsUnit (⟨f, hf⟩ : (D.place hz).toValuationSubring)) : D.n z f = 0 := by
  obtain ⟨u, hu⟩ := hu
  have hinv : ((u⁻¹ : ((D.place hz).toValuationSubring)ˣ) : (D.place hz).toValuationSubring).1
      = f⁻¹ := by
    have h1 : ((u : (D.place hz).toValuationSubring) : F) *
        ((u⁻¹ : ((D.place hz).toValuationSubring)ˣ) : (D.place hz).toValuationSubring) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1).trans rfl
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h1 := hinv
    simp only [inv_zero] at h1
    have h2 : ((u : (D.place hz).toValuationSubring) : F) *
        ((u⁻¹ : ((D.place hz).toValuationSubring)ˣ) : (D.place hz).toValuationSubring) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
    rw [h1, mul_zero] at h2
    exact zero_ne_one h2
  have h0 : 0 ≤ D.n z f := (D.mem_place_iff hz f).mp hf
  have h0' : 0 ≤ D.n z f⁻¹ :=
    (D.mem_place_iff hz f⁻¹).mp (hinv ▸ ((u⁻¹ : ((D.place hz).toValuationSubring)ˣ) :
      (D.place hz).toValuationSubring).2)
  have hsum := D.n_mul hz f f⁻¹
  rw [mul_inv_cancel₀ hf0, D.n_one hz] at hsum
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (D.n_ne_top hz hf0)
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp (D.n_ne_top hz (inv_ne_zero hf0))
  rw [← ha, ← hb] at hsum
  rw [← ha] at h0 ⊢
  rw [← hb] at h0'
  have h1 : (0 : ℤ) = a + b := by exact_mod_cast hsum
  have h2 : (0 : ℤ) ≤ a := by exact_mod_cast h0
  have h3 : (0 : ℤ) ≤ b := by exact_mod_cast h0'
  have : a = 0 := by omega
  rw [this]
  rfl

theorem not_isUnit_of_n_pos {f : F} (hf : f ∈ (D.place hz).toValuationSubring)
    (hp : 0 < D.n z f) : ¬IsUnit (⟨f, hf⟩ : (D.place hz).toValuationSubring) := fun hu => by
  have := D.n_eq_zero_of_isUnit hz hf hu
  rw [this] at hp
  exact lt_irrefl _ hp

theorem n_eq_one_of_irreducible {π : (D.place hz).toValuationSubring} (hπ : Irreducible π) :
    D.n z (π : F) = 1 := by
  have hπ0 : (π : F) ≠ 0 := by
    intro h
    exact hπ.ne_zero (Subtype.ext h)
  have hπmem : (π : F) ∈ (D.place hz).toValuationSubring := π.2
  have h0 : 0 ≤ D.n z (π : F) := (D.mem_place_iff hz _).mp hπmem
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (D.n_ne_top hz hπ0)
  rw [← hk] at h0 ⊢
  have hk0 : (0 : ℤ) ≤ k := by exact_mod_cast h0

  have hk1 : k ≠ 0 := by
    intro hk1
    apply hπ.not_isUnit

    have hsum := D.n_mul hz (π : F) (π : F)⁻¹
    rw [mul_inv_cancel₀ hπ0, D.n_one hz, ← hk, hk1] at hsum
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp (D.n_ne_top hz (inv_ne_zero hπ0))
    have hinvmem : (π : F)⁻¹ ∈ (D.place hz).toValuationSubring := by
      rw [D.mem_place_iff hz, ← hb]
      rw [← hb] at hsum
      have : (0 : ℤ) = 0 + b := by exact_mod_cast hsum
      exact_mod_cast (show (0 : ℤ) ≤ b by omega)
    refine ⟨⟨π, ⟨(π : F)⁻¹, hinvmem⟩, Subtype.ext (mul_inv_cancel₀ hπ0),
      Subtype.ext (inv_mul_cancel₀ hπ0)⟩, rfl⟩

  have hk2 : k ≤ 1 := by
    by_contra hlt
    push Not at hlt
    set s := D.t - algebraMap ℂ F z with hs
    have hsmem : s ∈ (D.place hz).toValuationSubring := by
      rw [D.mem_place_iff hz, D.n_t_sub hz]; exact zero_le_one
    have hq : D.n z (s⁻¹ * (π : F)) = ((k - 1 : ℤ) : WithTop ℤ) := by
      rw [D.n_mul hz, D.n_t_sub_inv hz, ← hk, ← WithTop.coe_add]
      congr 1; omega
    have hqmem : s⁻¹ * (π : F) ∈ (D.place hz).toValuationSubring := by
      rw [D.mem_place_iff hz, hq]
      exact_mod_cast (show (0 : ℤ) ≤ k - 1 by omega)
    have hprod : π = ⟨s, hsmem⟩ * ⟨s⁻¹ * (π : F), hqmem⟩ := by
      apply Subtype.ext
      show (π : F) = s * (s⁻¹ * (π : F))
      rw [← mul_assoc, mul_inv_cancel₀ (D.t_sub_ne_zero hz), one_mul]
    rcases hπ.isUnit_or_isUnit hprod with hu | hu
    · exact D.not_isUnit_of_n_pos hz hsmem (by rw [D.n_t_sub hz]; exact zero_lt_one) hu
    · refine D.not_isUnit_of_n_pos hz hqmem ?_ hu
      rw [hq]
      exact_mod_cast (show (0 : ℤ) < k - 1 by omega)
  have : k = 1 := by omega
  rw [this]
  rfl

theorem ord_place {f : F} (hf : f ≠ 0) : ((D.place hz).ord f : WithTop ℤ) = D.n z f := by
  set w := D.place hz with hw
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  have hnu : D.n z ((u : w.toValuationSubring) : F) = 0 :=
    D.n_eq_zero_of_isUnit hz (u : w.toValuationSubring).2 (by simp)
  have hnπ : D.n z (π : F) = 1 := D.n_eq_one_of_irreducible hz hπ
  have hπ0 : (π : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  set k := w.ord f with hk
  rcases le_or_gt 0 k with hk0 | hk0
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hk0
    have hf' : f = ((u : w.toValuationSubring) : F) * (π : F) ^ m := by
      rw [hu, hm, zpow_natCast]
    rw [hf', D.n_mul hz, hnu, D.n_pow hz, hnπ, zero_add, hm]
    simp
  · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hk0.le)
    have hf' : f * (π : F) ^ m = ((u : w.toValuationSubring) : F) := by
      rw [hu, mul_assoc, ← zpow_natCast, ← zpow_add₀ hπ0, ← hm, add_neg_cancel, zpow_zero,
        mul_one]
    have h := D.n_mul hz f ((π : F) ^ m)
    rw [hf', hnu, D.n_pow hz, hnπ] at h
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (D.n_ne_top hz hf)
    rw [← ha] at h ⊢
    have h' : (0 : ℤ) = a + m := by
      have h2 : (m • (1 : WithTop ℤ)) = ((m : ℤ) : WithTop ℤ) := by simp
      rw [h2, ← WithTop.coe_add] at h
      exact_mod_cast h
    congr 1
    omega

theorem ord_place_t_sub : (D.place hz).ord (D.t - algebraMap ℂ F z) = 1 := by
  have h := D.ord_place hz (D.t_sub_ne_zero hz)
  rw [D.n_t_sub hz] at h
  exact_mod_cast h

theorem mem_place_iff_ord {f : F} (hf : f ≠ 0) :
    f ∈ (D.place hz).toValuationSubring ↔ 0 ≤ (D.place hz).ord f := by
  rw [D.mem_place_iff hz, ← D.ord_place hz hf, WithTop.coe_nonneg]

theorem tendsto_evalAt [IsCurveOver ℂ F] {f : F} (hf : f ∈ (D.place hz).toValuationSubring) :
    Tendsto (D.G f) (𝓝[≠] z) (𝓝 ((D.place hz).evalAt f)) := by
  set w := D.place hz with hw
  set c := w.evalAt f with hc
  have hrat : w.IsRational := isRational_of_isCurveOver w
  have hval : w.evalAt (f - algebraMap ℂ F c) = 0 := by
    rw [evalAt_sub_algebraMap w hrat hf c, sub_self]

  have hlim : Tendsto (fun u => D.G f u + -c) (𝓝[≠] z) (𝓝 0) := by
    have heq : D.G (f - algebraMap ℂ F c) =ᶠ[𝓝[≠] z] fun u => D.G f u + -c := by
      have h1 := D.hadd z hz f (algebraMap ℂ F (-c))
      have e : f - algebraMap ℂ F c = f + algebraMap ℂ F (-c) := by
        rw [map_neg, sub_eq_add_neg]
      rw [e]
      filter_upwards [h1, D.hC z hz (-c)] with u hu1 hu2
      rw [hu1, Pi.add_apply, hu2]
    refine Tendsto.congr' heq ?_
    by_cases hfc : f - algebraMap ℂ F c = 0
    · rw [hfc]
      refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
      filter_upwards [D.hC z hz 0] with u hu
      rw [map_zero] at hu
      exact hu.symm
    · apply tendsto_zero_of_meromorphicOrderAt_pos
      have hpos : 0 < w.ord (f - algebraMap ℂ F c) :=
        ord_pos_of_evalAt_eq_zero w hrat hfc (sub_mem hf (w.algebraMap_mem' c)) hval
      have h := D.ord_place hz hfc
      show 0 < D.n z (f - algebraMap ℂ F c)
      rw [← h]
      exact_mod_cast hpos
  have := hlim.add_const c
  simpa using this

end AtPoint

open Classical in

def γ (v₀ : Place ℂ F) (u : ℂ) : Place ℂ F :=
  if hu : u ∈ ball (0 : ℂ) D.ρ then D.place hu else v₀

variable (v₀ : Place ℂ F)

theorem γ_eq {u : ℂ} (hu : u ∈ ball (0 : ℂ) D.ρ) : D.γ v₀ u = D.place hu := dite_eq_left hu

variable [IsCurveOver ℂ F] {z : ℂ} (hz : z ∈ ball (0 : ℂ) D.ρ)
include hz

theorem evalAt_eventuallyEq (f : F) :
    (fun u => (D.γ v₀ u).evalAt f) =ᶠ[𝓝[≠] z] D.G f := by
  filter_upwards [(D.hG f z hz).eventually_analyticAt,
    mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz)] with u hua hub
  rw [D.γ_eq v₀ hub]
  have hmem : f ∈ (D.place hub).toValuationSubring := by
    rw [D.mem_place_iff hub]
    exact hua.meromorphicOrderAt_nonneg
  exact tendsto_nhds_unique (D.tendsto_evalAt hub hmem) hua.continuousAt.continuousWithinAt.tendsto

theorem meromorphicAt_evalAt (f : F) : MeromorphicAt (fun u => (D.γ v₀ u).evalAt f) z :=
  (D.hG f z hz).congr (D.evalAt_eventuallyEq v₀ hz f).symm

theorem meromorphicOrderAt_evalAt {f : F} (hf : f ≠ 0) :
    meromorphicOrderAt (fun u => (D.γ v₀ u).evalAt f) z = ((D.γ v₀ z).ord f : WithTop ℤ) := by
  rw [meromorphicOrderAt_congr (D.evalAt_eventuallyEq v₀ hz f), D.γ_eq v₀ hz, D.ord_place hz hf]
  rfl

theorem analyticAt_evalAt {f : F} (hf : f ≠ 0) (h0 : 0 ≤ (D.γ v₀ z).ord f) :
    AnalyticAt ℂ (fun u => (D.γ v₀ u).evalAt f) z := by
  refine (D.meromorphicAt_evalAt v₀ hz f).analyticAt ?_
  rw [continuousAt_iff_punctured_nhds]
  have hmem : f ∈ (D.place hz).toValuationSubring := by
    rw [D.mem_place_iff_ord hz hf, ← D.γ_eq v₀ hz]
    exact h0
  have h := D.tendsto_evalAt hz hmem
  rw [← D.γ_eq v₀ hz] at h
  exact h.congr' (D.evalAt_eventuallyEq v₀ hz f).symm

end Datum

end Main

end LocalParam

end Place

namespace Place

-- pin: AlgebraicCurve.Place.exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex (Theorems/Thm_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex.lean:13)
theorem exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] (v : Place ℂ F) (t : F) (ht : v.ord t = 1) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ F), 0 < ρ ∧ γ 0 = v ∧
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, (γ z).ord (t - algebraMap ℂ F z) = 1) ∧
      ∀ f : F, f ≠ 0 → ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        MeromorphicAt (fun u : ℂ => (γ u).evalAt f) z ∧
        meromorphicOrderAt (fun u : ℂ => (γ u).evalAt f) z = ((γ z).ord f : WithTop ℤ) ∧
        (0 ≤ (γ z).ord f → AnalyticAt ℂ (fun u : ℂ => (γ u).evalAt f) z) := by
  obtain ⟨ρ, G, hρ, hG, hcomp, hord⟩ := MeroRealize.main F hfg v t ht
  let D : LocalParam.Datum F :=
    { t := t, ρ := ρ, G := G, hG := hG
      hadd := fun z hz => (hcomp z hz).1
      hmul := fun z hz => (hcomp z hz).2.1
      hC := fun z hz => (hcomp z hz).2.2.1
      ht := fun z hz => (hcomp z hz).2.2.2 }
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) D.ρ := Metric.mem_ball_self hρ
  refine ⟨ρ, D.γ v, hρ, ?_, fun z hz => ?_, fun f hf z hz => ⟨?_, ?_, ?_⟩⟩
  · rw [D.γ_eq v h0]
    refine eq_of_forall_ord_eq fun f hf => ?_
    have h1 := D.ord_place h0 hf
    have h2 : D.n 0 f = (v.ord f : WithTop ℤ) := hord f hf
    rw [h2] at h1
    exact_mod_cast h1
  · rw [D.γ_eq v hz]
    exact D.ord_place_t_sub hz
  · exact D.meromorphicAt_evalAt v hz f
  · exact D.meromorphicOrderAt_evalAt v hz hf
  · exact D.analyticAt_evalAt v hz hf

end Place

end AlgebraicCurve
