/-
The box measure and the integral finite adèles.

Seven rows on the box `adelicBox F = infiniteBox F × integralFiniteAdeles` and the
integral finite adèles: an indicator decomposition over the box, the measure scaling
`absNorm * measure (a • integralFiniteAdeles)`, the additive-character density, the
closure of `𝓞 F`, the denominator lemma for compactly supported functions, and the two
local-constancy/support and membership criteria.

  ## Port deltas

  * `import Mathlib.Topology.LocallyConstant.Algebra` — added.  The D6 row is proved through
    `LocallyConstant.charFn`, and `coe_charFn` (D6's pin `:43`) lives only there; the scaffold's
    four imports do not reach it.
  * Two `open` additions the pins carry and the scaffold dropped: `open Filter Topology
    MonoidWithZeroHom` and `open IsDedekindDomain.HeightOneSpectrum` (a bare `valuedAdicCompletion_
    eq_valuation'` in the D4/D5 proofs) plus `open scoped Classical nonZeroDivisors Topology`
    (`𝓝` is `scoped[Topology]`).
  * The pin's three label namespaces are renamed to subject names: `LatKer0` → `BoxKernel`,
    `LatIdx` → `BoxIndex`, `LatDec` → `BoxDecomposition`.  The D1 statements of
    `BoxDecomposition.coset_eq_image_dBox` and `BoxDecomposition.coset_eq_of_mem` name
    `LatIdx.dBox` *in the statement text*, which `check_port` hashes (FR-0224 trap 1), so those two
    lines keep the pin's spelling through a `local notation "LatIdx.dBox" => BoxIndex.dBox` inside
    the block — a checker accommodation, not a statement change (the AF89 `Faithful.lean` device).
  * Declaration count: the wire carries 70 pin publics, but the three `S_` files repeat one engine
    block each (`BoxKernel` in D1 and D3, the first `BoxIndex` block in D1 and D2) and fold their seven
    `solution`s into the rows, so the port declares **44** declarations (all public), not ≈66.  The
    repeats are the pin's own (`dBox` D1:204/D3:91, `mul_mem_integralFiniteAdeles` D1:101 /
    `mul_integer_mem` D1:228, `add_mem_integralFiniteAdeles` D1:106 / `add_mem'` D1:232,
    `isCompact_dBox` D1:115/246, `algebraMap_integer_apply` D1:97/D1:208), declared once per pin
    namespace because both copies are public on the wire.
  * D1's `BoxKernel.dBox` is `private` in D1 but public in D3; it is declared **public** here, at the
    pin's D3 statement (its last name is a `dBox` the wire needs).

  ## Heartbeat probe (measured, never installed — FR-0225)

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/NumberTheory/AdelicBox/Measure.lean`:
  silent at **200 000** (the playbook cap, which is the gate), silent at 8 000, **fails at 6 000**
  (five `deterministic timeout at whnf`, the first at `BoxKernel.eq_one_of_forall_re_pow_two_pow_gt`)
  and at 4 000.  Natural cost ≈ 6–8 k.  No in-file `set_option maxHeartbeats` anywhere in the file.

  spec-pin: P2M/Sol/S_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicBox_absNorm_mul_measure_image_integralFiniteAdeles.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicBox_exists_ne_zero_forall_addChar_mul_eq_one.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicBox_integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicBox_exists_denom_of_hasCompactSupport.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicBox_isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles.lean
  spec-pin: P2M/Sol/S_NumberField_AdelicBox_algebraMap_mem_image_integralFiniteAdeles_iff.lean
-/
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.AutomorphicForm.Adelic.FiniteIntegralConjugation
import FLTForHuman.AutomorphicForm.Adelic.Siegel.CentreCutCover
import Mathlib.Topology.LocallyConstant.Algebra

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open Filter Topology MonoidWithZeroHom
open IsDedekindDomain.HeightOneSpectrum
open scoped ENNReal BigOperators Classical nonZeroDivisors Topology



namespace NumberField.AdelicBox

namespace BoxKernel

open IsDedekindDomain Filter Topology

theorem re_sq_of_norm_eq_one {w : ℂ} (hw : ‖w‖ = 1) : (w ^ 2).re = 2 * w.re ^ 2 - 1 := by
  have h : w.re * w.re + w.im * w.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw, one_pow]
  rw [sq, Complex.mul_re]
  nlinarith

theorem norm_le_one_of_forall_pow_mem {H : Set ℂ} (hbdd : Bornology.IsBounded H) {a : ℂ}
    (ha : ∀ n : ℕ, a ^ (n + 1) ∈ H) : ‖a‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  obtain ⟨M, hM⟩ := hbdd.exists_norm_le
  obtain ⟨n, hn⟩ := (tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop M |>.exists
  have h1 : ‖a‖ ^ n ≤ ‖a‖ ^ (n + 1) := pow_le_pow_right₀ h.le (Nat.le_succ n)
  have h2 : ‖a ^ (n + 1)‖ ≤ M := hM _ (ha n)
  rw [norm_pow] at h2
  linarith

theorem eq_one_of_forall_re_pow_two_pow_gt {a : ℂ} (ha : ‖a‖ = 1)
    (h : ∀ n : ℕ, 1 / 2 < (a ^ (2 ^ n)).re) : a = 1 := by

  set c : ℕ → ℝ := fun n => (a ^ (2 ^ n)).re with hc
  have hnorm : ∀ n : ℕ, ‖a ^ (2 ^ n)‖ = 1 := fun n => by rw [norm_pow, ha, one_pow]
  have hrec : ∀ n : ℕ, c (n + 1) = 2 * c n ^ 2 - 1 := fun n => by
    simp only [hc]
    rw [pow_succ, pow_mul, re_sq_of_norm_eq_one (hnorm n)]
  have hc0 : c 0 = a.re := by simp [hc]
  have hgt : ∀ n, 1 / 2 < c n := fun n => h n

  by_cases hre : a.re = 1
  · apply Complex.ext
    · simpa using hre
    · have : a.re * a.re + a.im * a.im = 1 := by
        rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, ha, one_pow]
      rw [hre] at this
      simpa using (by nlinarith : a.im * a.im = 0)

  have hre1 : a.re < 1 := lt_of_le_of_ne (by simpa [ha] using Complex.re_le_norm a) hre
  set δ : ℝ := 2 * (1 - a.re) with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hstep : ∀ n : ℕ, c n ≤ c 0 - n * δ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : 1 / 2 < c n := hgt n
      have h2 : c n ≤ a.re := by
        have := ih; rw [hc0] at this
        have : (n : ℝ) * δ ≥ 0 := by positivity
        linarith
      rw [hrec n, Nat.cast_succ]
      nlinarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((c 0 - 1 / 2) / δ)
  have h1 := hstep n
  have h2 := hgt n
  have h3 : (c 0 - 1 / 2) < n * δ := by rwa [div_lt_iff₀ hδpos] at hn
  linarith

theorem eq_one_of_mem {H : Set ℂ} (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H) (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hbdd : Bornology.IsBounded H) (hre : ∀ a ∈ H, 1 / 2 < a.re) {a : ℂ} (ha : a ∈ H) : a = 1 := by
  have hpow : ∀ b ∈ H, ∀ n : ℕ, b ^ (n + 1) ∈ H := fun b hb n => by
    induction n with
    | zero => simpa using hb
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hb
  have ha0 : a ≠ 0 := fun h0 => by have := hre a ha; rw [h0] at this; norm_num at this
  have hle : ‖a‖ ≤ 1 := norm_le_one_of_forall_pow_mem hbdd (hpow a ha)
  have hge : 1 ≤ ‖a‖ := by
    have := norm_le_one_of_forall_pow_mem hbdd (hpow a⁻¹ (hinv a ha))
    rwa [norm_inv, inv_le_one₀ (norm_pos_iff.mpr ha0)] at this
  refine eq_one_of_forall_re_pow_two_pow_gt (le_antisymm hle hge) fun n => hre _ ?_
  have := hpow a ha (2 ^ n - 1)
  rwa [Nat.sub_add_cancel Nat.one_le_two_pow] at this

variable (F : Type) [Field F] [NumberField F]

def dBox (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
    integralFiniteAdeles (𝓞 F) F

theorem algebraMap_integer_apply (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

theorem mul_mem_integralFiniteAdeles (a : 𝓞 F) {z : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) * z ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  mul_mem (algebraMap_mem_adicCompletionIntegers v a) (hz v)

theorem add_mem_integralFiniteAdeles {z w : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) (hw : w ∈ integralFiniteAdeles (𝓞 F) F) :
    z + w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  add_mem (hz v) (hw v)

theorem neg_mem_integralFiniteAdeles {z : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) : -z ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  neg_mem (hz v)

theorem isCompact_dBox (d : 𝓞 F) : IsCompact (dBox F d) :=
  (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

theorem dBox_mul_subset (d e : 𝓞 F) : dBox F (d * e) ⊆ dBox F d := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (e : F) * z, mul_mem_integralFiniteAdeles F e hz, ?_⟩
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, mul_assoc]

theorem eq_zero_of_forall_mem_dBox {x : FiniteAdeleRing (𝓞 F) F}
    (hx : ∀ d : 𝓞 F, d ≠ 0 → x ∈ dBox F d) : x = 0 := by
  refine FiniteAdeleRing.ext F fun v => ?_
  rw [show (0 : FiniteAdeleRing (𝓞 F) F) v = 0 from rfl]

  have hle : ∀ n : ℕ, Valued.v (x v) ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    have hI : (v.asIdeal ^ n : Ideal (𝓞 F)) ≠ ⊥ := pow_ne_zero _ v.ne_bot
    obtain ⟨d, hdI, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨z, hz, hxz⟩ := hx d hd0
    rw [← hxz, show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) v
        = (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v * z v from rfl, map_mul,
      algebraMap_integer_apply,
      show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F d)
        = ((algebraMap (𝓞 F) F d : F) : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    have hz1 : Valued.v (z v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hz v)
    calc v.intValuation d * Valued.v (z v) ≤ v.intValuation d * 1 := by gcongr
      _ ≤ WithZero.exp (-(n : ℤ)) := by
          rw [mul_one]; exact (HeightOneSpectrum.intValuation_le_pow_iff_mem v d n).mpr hdI
  by_contra hne
  have hne' : Valued.v (x v) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v (x v) = WithZero.exp m :=
    ⟨WithZero.log (Valued.v (x v)), (WithZero.exp_log hne').symm⟩
  have := hle ((-m).toNat + 1)
  rw [hm, WithZero.exp_le_exp] at this
  omega

theorem exists_dBox_subset {U : Set (FiniteAdeleRing (𝓞 F) F)} (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ dBox F d ⊆ U := by
  have : Nonempty {d : 𝓞 F // d ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  have hdir : Directed (· ⊇ ·) (fun d : {d : 𝓞 F // d ≠ 0} => dBox F d.1) := by
    rintro ⟨d, hd⟩ ⟨e, he⟩
    have h2 : dBox F (d * e) ⊆ dBox F e := by rw [mul_comm]; exact dBox_mul_subset F e d
    exact ⟨⟨d * e, mul_ne_zero hd he⟩, dBox_mul_subset F d e, h2⟩
  have hInter : (⋂ d : {d : 𝓞 F // d ≠ 0}, dBox F d.1) = {0} := by
    ext x
    constructor
    · intro hx
      have hx0 : x = 0 := eq_zero_of_forall_mem_dBox F fun d hd =>
        Set.mem_iInter.mp hx ⟨d, hd⟩
      simp [hx0]
    · rintro rfl
      exact Set.mem_iInter.mpr fun d => ⟨0, zero_mem_integralFiniteAdeles, by simp⟩
  obtain ⟨⟨d, hd⟩, h⟩ := exists_subset_nhds_of_isCompact' hdir (fun d => isCompact_dBox F d.1)
    (fun d => (isCompact_dBox F d.1).isClosed) (U := U) (by
      rw [hInter, nhdsSet_singleton]; exact hU)
  exact ⟨d, hd, h⟩

theorem exists_ne_zero_forall_eq_one
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) = 1 := by

  set U : Set (FiniteAdeleRing (𝓞 F) F) := {x | 1 / 2 < (ψf x).re} with hU
  have hU0 : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := by
    refine (isOpen_lt continuous_const (Complex.continuous_re.comp hψf)).mem_nhds ?_
    show 1 / 2 < (ψf 0).re
    rw [AddChar.map_zero_eq_one, Complex.one_re]; norm_num
  obtain ⟨d, hd, hdU⟩ := exists_dBox_subset F hU0
  refine ⟨d, hd, fun z hz => ?_⟩

  set H : Set ℂ := ψf '' dBox F d with hH
  have hmem : ∀ {x}, x ∈ dBox F d ↔ ∃ w ∈ integralFiniteAdeles (𝓞 F) F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w = x := fun {x} => Iff.rfl
  refine eq_one_of_mem (H := H) ?_ ?_ ?_ ?_ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  · rintro _ ⟨x, ⟨w₁, hw₁, rfl⟩, rfl⟩ _ ⟨y, ⟨w₂, hw₂, rfl⟩, rfl⟩
    refine ⟨_, ⟨w₁ + w₂, add_mem_integralFiniteAdeles F hw₁ hw₂, rfl⟩, ?_⟩
    dsimp only
    rw [mul_add, AddChar.map_add_eq_mul]
  · rintro _ ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨_, ⟨-w, neg_mem_integralFiniteAdeles F hw, rfl⟩, ?_⟩
    dsimp only
    rw [mul_neg]
    apply eq_inv_of_mul_eq_one_left
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  · exact ((isCompact_dBox F d).image hψf).isBounded
  · rintro _ ⟨x, hx, rfl⟩
    exact hdU hx

end BoxKernel

namespace BoxIndex

open IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]

def dBox (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
    integralFiniteAdeles (𝓞 F) F

theorem algebraMap_integer_apply (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v
      = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) := rfl

theorem valued_algebraMap_integer (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v) = v.intValuation a := by
  rw [algebraMap_integer_apply, show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)
        = ((algebraMap (𝓞 F) F a : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]

theorem mul_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x * y) v = x v * y v := rfl

theorem sub_apply' (x y : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (x - y) v = x v - y v := rfl

theorem algebraMap_integer_mem (a : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  algebraMap_mem_adicCompletionIntegers v a

theorem mul_integer_mem (a : 𝓞 F) {z : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) * z ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  mul_mem (algebraMap_mem_adicCompletionIntegers v a) (hz v)

theorem add_mem' {z w : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ integralFiniteAdeles (𝓞 F) F) : z + w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  add_mem (hz v) (hw v)

theorem sub_mem' {z w : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ integralFiniteAdeles (𝓞 F) F) : z - w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  sub_mem (hz v) (hw v)

theorem dBox_sub_mem {d : 𝓞 F} {y y' : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ dBox F d) (hy' : y' ∈ dBox F d) :
    y - y' ∈ dBox F d := by
  obtain ⟨w, hw, rfl⟩ := hy
  obtain ⟨w', hw', rfl⟩ := hy'
  exact ⟨w - w', sub_mem' F hw hw', by simp only [mul_sub]⟩

theorem isCompact_dBox (d : 𝓞 F) : IsCompact (dBox F d) :=
  (isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)

variable {F}

theorem exists_sub_mem_dBox {d : 𝓞 F} (hd : d ≠ 0) {z : FiniteAdeleRing (𝓞 F) F}
    (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    ∃ a : 𝓞 F, z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ dBox F d := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le (𝓞 F) F hz hd
  refine ⟨a, algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)), fun v => ?_, ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, mul_apply', map_mul, sub_apply']
    have hdv : Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) ≠ 0 := by
      rw [valued_algebraMap_integer]; exact v.intValuation_ne_zero d hd
    have hinv : Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹) v)
        = (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹ := by
      rw [show (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹) v
          = algebraMap F (v.adicCompletion F) (d : F)⁻¹ from rfl, map_inv₀, Valuation.map_inv]
      rfl
    have ha' : Valued.v (z v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v)
        ≤ Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) := ha v
    rw [hinv]
    calc (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹
          * Valued.v (z v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)) v)
        ≤ (Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v))⁻¹
          * Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)) v) := by gcongr
      _ = 1 := inv_mul_cancel₀ hdv
  · show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F))) = z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F)
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, one_mul]

theorem sub_mem_span_of_sub_mem_dBox {d a a' : 𝓞 F} (hd : d ≠ 0)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a' : F)
      ∈ dBox F d) : a - a' ∈ Ideal.span {d} := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  obtain ⟨w, hw, hw'⟩ := h
  set y : F := (d : F)⁻¹ * ((a : F) - (a' : F)) with hy
  have hwy : w = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
    have h1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((a : F) - (a' : F)) := by rw [map_sub]; exact hw'
    calc w = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹ * (d : F)) * w := by
            rw [inv_mul_cancel₀ hd', map_one, one_mul]
      _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * w) := by
            rw [map_mul, mul_assoc]
      _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by rw [h1, ← map_mul]
  have hyint : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := fun v => by
    have hv : (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v ∈ v.adicCompletionIntegers F := by
      rw [← hwy]; exact hw v
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v = (y : v.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F y hyint
  rw [Ideal.mem_span_singleton']
  refine ⟨b, RingOfIntegers.coe_injective ?_⟩
  have hb' : (b : F) = y := hb
  show ((b * d : 𝓞 F) : F) = ((a - a' : 𝓞 F) : F)
  have e1 : ((b * d : 𝓞 F) : F) = (b : F) * (d : F) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul]
  have e2 : ((a - a' : 𝓞 F) : F) = (a : F) - (a' : F) := by
    simp only [RingOfIntegers.coe_eq_algebraMap, map_sub]
  rw [e1, e2, hb', hy, mul_comm, ← mul_assoc, mul_inv_cancel₀ hd', one_mul]

end BoxIndex

namespace BoxIndex

open IsDedekindDomain MeasureTheory

variable {F : Type} [Field F] [NumberField F]

theorem image_coset_eq (d : 𝓞 F) (x : FiniteAdeleRing (𝓞 F) F) :
    (fun z : FiniteAdeleRing (𝓞 F) F ↦ x + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
        integralFiniteAdeles (𝓞 F) F
      = (fun y : FiniteAdeleRing (𝓞 F) F ↦ x + y) '' dBox F d := by
  rw [dBox, Set.image_image]

theorem measure_image_add_left [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)]
    [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (x : FiniteAdeleRing (𝓞 F) F) (s : Set (FiniteAdeleRing (𝓞 F) F)) :
    ν ((fun y ↦ x + y) '' s) = ν s := by
  rw [Set.image_add_left, measure_preimage_add]

theorem main [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    (Ideal.absNorm (Ideal.span {d}) : ENNReal) *
        ν ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
      = ν (integralFiniteAdeles (𝓞 F) F) := by
  classical

  rw [image_coset_eq, measure_image_add_left]

  set I : Ideal (𝓞 F) := Ideal.span {d} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, ne_eq, Ideal.span_singleton_eq_bot]; exact hd
  have : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let : Fintype (𝓞 F ⧸ I) := Fintype.ofFinite _
  set r : 𝓞 F ⧸ I → 𝓞 F := Function.surjInv Ideal.Quotient.mk_surjective with hrdef
  have hr : ∀ q, Ideal.Quotient.mk I (r q) = q := Function.surjInv_eq Ideal.Quotient.mk_surjective
  set T : 𝓞 F ⧸ I → Set (FiniteAdeleRing (𝓞 F) F) :=
    fun q ↦ (fun y ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q : F) + y) '' dBox F d with hTdef
  have hcover : integralFiniteAdeles (𝓞 F) F = ⋃ q, T q := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha⟩ := exists_sub_mem_dBox hd hz
      refine Set.mem_iUnion.mpr ⟨Ideal.Quotient.mk I a, ?_⟩
      have hra : r (Ideal.Quotient.mk I a) - a ∈ I := Ideal.Quotient.eq.mp (hr _)
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hra
      refine ⟨z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r (Ideal.Quotient.mk I a) : F), ?_,
        add_sub_cancel _ _⟩
      have : z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r (Ideal.Quotient.mk I a) : F)
          = (z - algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F))
            - algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F) := by
        have e : ((r (Ideal.Quotient.mk I a) : 𝓞 F) : F) = (a : F) + (d : F) * (b : F) := by
          have hb2 : (r (Ideal.Quotient.mk I a) : 𝓞 F) = a + d * b := by rw [mul_comm, hb]; abel
          rw [hb2]; simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_mul]
        rw [e, map_add, map_mul]
        abel
      rw [this]
      exact dBox_sub_mem F ha ⟨_, algebraMap_integer_mem F b, rfl⟩
    · intro hz
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hz
      obtain ⟨y, ⟨w, hw, rfl⟩, rfl⟩ := hq
      exact add_mem' F (algebraMap_integer_mem F _) (mul_integer_mem F d hw)
  have hdisj : Pairwise (Function.onFun Disjoint T) := by
    intro q q' hqq'
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨y, hy, rfl⟩ ⟨y', hy', hxy⟩
    dsimp only at hxy
    apply hqq'
    have hsub : algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q' : F)
        - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q : F) ∈ dBox F d := by
      have : algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q' : F)
          - algebraMap F (FiniteAdeleRing (𝓞 F) F) (r q : F) = y - y' := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm y, hxy]
      rw [this]
      exact dBox_sub_mem F hy hy'
    have hmem := sub_mem_span_of_sub_mem_dBox hd hsub
    rw [← hr q, ← hr q', Ideal.Quotient.eq]

    rw [← neg_sub]
    exact I.neg_mem hmem
  have hmeas : ∀ q, MeasurableSet (T q) := fun q =>
    ((isCompact_dBox F d).image (continuous_const.add continuous_id)).isClosed.measurableSet
  have hcard : (Ideal.absNorm I : ENNReal) = (Finset.univ : Finset (𝓞 F ⧸ I)).card := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, Finset.card_univ]
  calc (Ideal.absNorm I : ENNReal) * ν (dBox F d)
      = ∑ q : 𝓞 F ⧸ I, ν (dBox F d) := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    _ = ∑ q : 𝓞 F ⧸ I, ν (T q) := Finset.sum_congr rfl fun q _ => (measure_image_add_left ν _ _).symm
    _ = ∑' q : 𝓞 F ⧸ I, ν (T q) := (tsum_fintype _).symm
    _ = ν (⋃ q, T q) := (measure_iUnion hdisj hmeas).symm
    _ = ν (integralFiniteAdeles (𝓞 F) F) := by rw [← hcover]

end BoxIndex

namespace BoxDecomposition

open IsDedekindDomain Filter Topology

variable {F : Type} [Field F] [NumberField F]

/-- The pin spells the index box `LatIdx.dBox` in the two statements below; the declaration is
renamed to the subject namespace, and this local notation keeps the wire's statement text (the
same device as `NumberTheory/AdelicFourier/Faithful.lean`'s slice notation). -/
local notation "LatIdx.dBox" => BoxIndex.dBox

def coset (k : F) (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
    + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F

theorem coset_eq_image_dBox (k : F) (d : 𝓞 F) :
    coset k d = (fun y ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k + y) '' LatIdx.dBox F d := by
  rw [coset, BoxIndex.dBox, Set.image_image]

theorem coset_eq_of_mem {k : F} {d : 𝓞 F} {x : FiniteAdeleRing (𝓞 F) F} (hx : x ∈ coset k d) :
    coset k d = (fun y ↦ x + y) '' LatIdx.dBox F d := by
  rw [coset_eq_image_dBox] at hx ⊢
  obtain ⟨y₀, hy₀, rfl⟩ := hx
  dsimp only
  ext w
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y - y₀, BoxIndex.dBox_sub_mem F hy hy₀, ?_⟩
    show algebraMap F (FiniteAdeleRing (𝓞 F) F) k + y₀ + (y - y₀)
      = algebraMap F (FiniteAdeleRing (𝓞 F) F) k + y
    rw [add_assoc, add_sub_cancel]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y₀ + y, ?_, ?_⟩
    · obtain ⟨w, hw, rfl⟩ := hy; obtain ⟨w₀, hw₀, rfl⟩ := hy₀
      exact ⟨w₀ + w, BoxIndex.add_mem' F hw₀ hw, by simp only [mul_add]⟩
    · show algebraMap F (FiniteAdeleRing (𝓞 F) F) k + (y₀ + y)
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) k + y₀ + y
      rw [add_assoc]

theorem isOpen_coset (k : F) {d : 𝓞 F} (hd : d ≠ 0) : IsOpen (coset k d) := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hS : coset k d = (fun y : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) ⁻¹' integralFiniteAdeles (𝓞 F) F := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) k
        + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)
        ∈ integralFiniteAdeles (𝓞 F) F
      rwa [add_sub_cancel_left, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul]
    · intro hy
      refine ⟨_, hy, ?_⟩
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)
        * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) = y
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, one_mul, add_sub_cancel]
  rw [hS]
  exact (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul (continuous_id.sub continuous_const))

theorem exists_mem_coset {d : 𝓞 F} (hd : d ≠ 0) (x : FiniteAdeleRing (𝓞 F) F) :
    ∃ k : F, x ∈ coset k d := by
  obtain ⟨k₀, hk₀⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F x
  obtain ⟨a, ⟨z, hz, hz'⟩⟩ := BoxIndex.exists_sub_mem_dBox hd hk₀
  refine ⟨(a : F) - k₀, z, hz, ?_⟩
  dsimp only at hz'
  show algebraMap F (FiniteAdeleRing (𝓞 F) F) ((a : F) - k₀)
    + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z = x
  rw [hz', map_sub]
  abel

theorem exists_nhds_forall_add_eq {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {h : G → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ W ∈ 𝓝 (0 : G), ∀ x, ∀ w ∈ W, h (x + w) = h x := by

  have key : ∀ x : G, ∃ V W : Set G, IsOpen V ∧ x ∈ V ∧ W ∈ 𝓝 (0 : G) ∧ ∀ v ∈ V, ∀ w ∈ W, h (v + w) = h x := by
    intro x
    obtain ⟨U, hU, hxU, hUc⟩ := (IsLocallyConstant.iff_exists_open h).mp hlc x
    have hcont : ContinuousAt (fun p : G × G => p.1 + p.2) (x, 0) := continuous_add.continuousAt
    have hmem : (fun p : G × G => p.1 + p.2) ⁻¹' U ∈ 𝓝 ((x, 0) : G × G) :=
      hcont.preimage_mem_nhds (by simpa using hU.mem_nhds hxU)
    obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.mp hmem
    obtain ⟨V', hV'V, hV'o, hxV'⟩ := mem_nhds_iff.mp hV
    exact ⟨V', W, hV'o, hxV', hW, fun v hv w hw => hUc _ (hVW (Set.mk_mem_prod (hV'V hv) hw))⟩
  choose V W hVo hxV hW hVW using key

  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover V hVo (fun x _ => Set.mem_iUnion.mpr ⟨x, hxV x⟩)

  set W₀ : Set G := ⋂ x ∈ t, W x with hW₀
  have hW₀ : W₀ ∈ 𝓝 (0 : G) := (Filter.biInter_finset_mem t).mpr fun x _ => hW x
  refine ⟨W₀ ∩ (fun w => -w) ⁻¹' W₀, Filter.inter_mem hW₀ ?_, ?_⟩
  · exact (continuous_neg.tendsto' 0 0 neg_zero) hW₀

  have hK : ∀ x ∈ tsupport h, ∀ w ∈ W₀, h (x + w) = h x := by
    intro x hx w hw
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hw' : w ∈ W i := Set.mem_iInter₂.mp hw i hi
    rw [hVW i x hxi w hw', ← hVW i x hxi 0 (mem_of_mem_nhds (hW i)), add_zero]
  intro x w hw
  obtain ⟨hw1, hw2⟩ := hw
  by_cases hx : x ∈ tsupport h
  · exact hK x hx w hw1
  by_cases hxw : x + w ∈ tsupport h
  · have := hK (x + w) hxw (-w) hw2
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxw]

theorem main {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ (s : Finset F) (c : F → ℂ),
      h = ∑ k ∈ s, c k • (coset k d).indicator 1 := by
  classical

  obtain ⟨W, hW, hWh⟩ := exists_nhds_forall_add_eq hlc hcs
  obtain ⟨d, hd, hdW⟩ := BoxKernel.exists_dBox_subset F hW
  have hper : ∀ x, ∀ y ∈ BoxIndex.dBox F d, h (x + y) = h x := fun x y hy => hWh x y (hdW hy)
  have hconst : ∀ {k : F} {x}, x ∈ coset k d → h x = h (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) := by
    intro k x hx
    rw [coset_eq_image_dBox] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hper _ y hy
  refine ⟨d, hd, ?_⟩

  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover (fun k : F => coset k d)
    (fun k => isOpen_coset k hd) (fun x _ => by
      obtain ⟨k, hk⟩ := exists_mem_coset hd x
      exact Set.mem_iUnion.mpr ⟨k, hk⟩)
  set C : Finset (Set (FiniteAdeleRing (𝓞 F) F)) := t.image fun k => coset k d with hC
  have hCrep : ∀ c ∈ C, ∃ k : F, coset k d = c := fun c hc => by
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hc; exact ⟨k, rfl⟩
  set rep : Set (FiniteAdeleRing (𝓞 F) F) → F := fun c =>
    if hc : c ∈ C then (hCrep c hc).choose else 0 with hrep
  have hrep_spec : ∀ c ∈ C, coset (rep c) d = c := fun c hc => by
    simp only [hrep, dite_eq_left hc]; exact (hCrep c hc).choose_spec
  set s : Finset F := C.image rep with hs
  refine ⟨s, fun k => h (algebraMap F (FiniteAdeleRing (𝓞 F) F) k), ?_⟩

  have hinj : ∀ c ∈ C, ∀ c' ∈ C, rep c = rep c' → c = c' := fun c hc c' hc' e => by
    rw [← hrep_spec c hc, ← hrep_spec c' hc', e]
  have hs_mem : ∀ {k}, k ∈ s → coset k d ∈ C ∧ rep (coset k d) = k := by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
    rw [hrep_spec c hc]; exact ⟨hc, rfl⟩
  have hdisj : ∀ {k k' : F} {x}, k ∈ s → k' ∈ s → x ∈ coset k d → x ∈ coset k' d → k = k' := by
    intro k k' x hk hk' hx hx'
    have e : coset k d = coset k' d := by rw [coset_eq_of_mem hx, coset_eq_of_mem hx']
    rw [← (hs_mem hk).2, ← (hs_mem hk').2, e]

  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Set.indicator_apply, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hx : ∃ k ∈ s, x ∈ coset k d
  · obtain ⟨k₀, hk₀, hxk₀⟩ := hx
    rw [Finset.sum_eq_single k₀, ite_eq_left hxk₀, hconst hxk₀]
    · intro k hk hne
      rw [ite_eq_right]
      intro hxk
      exact hne (hdisj hk hk₀ hxk hxk₀)
    · intro h0; exact absurd hk₀ h0
  · simp only [not_exists, not_and] at hx
    rw [Finset.sum_eq_zero fun k hk => ite_eq_right (hx k hk)]

    by_contra hne
    have hxK : x ∈ tsupport h := subset_tsupport _ (Function.mem_support.mpr hne)
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp (ht hxK)
    have hc : coset k d ∈ C := Finset.mem_image.mpr ⟨k, hk, rfl⟩
    have hrs : rep (coset k d) ∈ s := Finset.mem_image.mpr ⟨_, hc, rfl⟩
    apply hx _ hrs
    rw [hrep_spec _ hc]; exact hxk

end BoxDecomposition

theorem exists_eq_sum_indicator_image_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F]
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ (s : Finset F) (c : F → ℂ),
      h = ∑ k ∈ s, c k •
        ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator 1
  :=
  BoxDecomposition.main hlc hcs

end NumberField.AdelicBox

namespace NumberField.AdelicBox

theorem absNorm_mul_measure_image_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    (Ideal.absNorm (Ideal.span {d}) : ENNReal) *
        ν ((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F)
      = ν (integralFiniteAdeles (𝓞 F) F)
  :=
  BoxIndex.main ν d hd k

end NumberField.AdelicBox

namespace NumberField.AdelicBox

theorem exists_ne_zero_forall_addChar_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    {ψf : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ} (hψf : Continuous ψf) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ z ∈ integralFiniteAdeles (𝓞 F) F,
      ψf (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) = 1
  :=
  BoxKernel.exists_ne_zero_forall_eq_one F hψf

end NumberField.AdelicBox

namespace NumberField.AdelicBox

theorem integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers
    (F : Type) [Field F] [NumberField F] :
    integralFiniteAdeles (𝓞 F) F
      ⊆ closure (Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)))
  := by
  intro z hz
  rw [mem_closure_iff_nhds]
  intro U hU
  have hUS : U ∩ integralFiniteAdeles (𝓞 F) F ∈ 𝓝 z :=
    Filter.inter_mem hU ((isOpen_integralFiniteAdeles F).mem_nhds hz)
  obtain ⟨z', hz'⟩ := RestrictedProduct.exists_structureMap_eq_of_forall
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hz
  have hemb := RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)
  have hpull : RestrictedProduct.structureMap _ _ _ ⁻¹' (U ∩ integralFiniteAdeles (𝓞 F) F)
      ∈ 𝓝 z' := by
    rw [hemb.nhds_eq_comap, hz']; exact Filter.preimage_mem_comap hUS
  rw [nhds_pi, Filter.mem_pi] at hpull
  obtain ⟨T, hTfin, W, hW, hWsub⟩ := hpull

  have hWγ : ∀ v ∈ T, ∃ γ : WithZero (Multiplicative ℤ), γ ≠ 0 ∧
      ∀ w : v.adicCompletionIntegers F,
        Valued.v ((w : v.adicCompletion F) - (z' v : v.adicCompletion F)) < γ → w ∈ W v := by
    intro v _
    have hWv : W v ∈ 𝓝 (z' v) := hW v
    rw [nhds_subtype] at hWv
    obtain ⟨O, hO, hOW⟩ := hWv
    obtain ⟨γ₀, hγ₀⟩ := Valued.mem_nhds.mp hO
    refine ⟨ValueGroup₀.embedding γ₀.1, ValueGroup₀.embedding_unit_ne_zero γ₀, fun w hw => ?_⟩
    refine hOW (hγ₀ ?_)
    simp only [Set.mem_ofPred_eq]
    rwa [Valuation.restrict_lt_iff_lt_embedding]
  choose γ hγne hγ using hWγ

  have hNv : ∀ v (hv : v ∈ T), ∃ r : 𝓞 F, r ≠ 0 ∧ v.intValuation r < γ v hv := by
    intro v hv
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp (hγne v hv)
    obtain ⟨π, hπI, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.mp (v.intValuation_ne_zero π hπ0)
    have hk_le : Multiplicative.toAdd k ≤ -1 := by
      have hlt : v.intValuation π < 1 :=
        (HeightOneSpectrum.intValuation_lt_one_iff_mem v π).mpr hπI
      rw [← hk, ← WithZero.coe_one, WithZero.coe_lt_coe] at hlt
      have := Multiplicative.toAdd_lt.mpr hlt
      rw [toAdd_one] at this; omega
    let N : ℕ := (1 - Multiplicative.toAdd m).toNat + 1
    refine ⟨π ^ N, pow_ne_zero _ hπ0, ?_⟩
    rw [map_pow, ← hk, ← WithZero.coe_pow, ← hm, WithZero.coe_lt_coe,
      ← Multiplicative.toAdd_lt, toAdd_pow, nsmul_eq_mul]
    have hN1 : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _)
    have hNm : (N : ℤ) ≥ 1 - Multiplicative.toAdd m := by
      simp only [N]; push_cast
      rcases le_or_gt (1 - Multiplicative.toAdd m) 0 with hle | hgt
      · simp only [Int.toNat_of_nonpos hle]; omega
      · rw [Int.toNat_of_nonneg hgt.le]; omega
    calc (N : ℤ) * Multiplicative.toAdd k
        ≤ (N : ℤ) * (-1) := by nlinarith [hk_le, hN1]
      _ = -(N : ℤ) := by ring
      _ ≤ Multiplicative.toAdd m - 1 := by linarith [hNm]
      _ < Multiplicative.toAdd m := by omega
  choose r hr0 hrval using hNv
  let Tf := hTfin.toFinset
  have hTmem : ∀ v ∈ Tf, v ∈ T := fun v hv => hTfin.mem_toFinset.mp hv
  set s : 𝓞 F := ∏ v ∈ Tf.attach, r v.1 (hTmem v.1 v.2) with hs_def
  have hs_ne : s ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => hr0 v.1 (hTmem v.1 v.2))
  have hsval : ∀ v (hv : v ∈ T), v.intValuation s < γ v hv := by
    intro v hv
    have hvTf : v ∈ Tf := hTfin.mem_toFinset.mpr hv
    rw [hs_def, map_prod]
    have hmem : (⟨v, hvTf⟩ : {x // x ∈ Tf}) ∈ Tf.attach := Finset.mem_attach _ _
    calc (∏ w ∈ Tf.attach, v.intValuation (r w.1 (hTmem w.1 w.2)))
        ≤ v.intValuation (r v (hTmem v hvTf)) := by
          rw [← Finset.mul_prod_erase _ _ hmem]
          exact mul_le_of_le_one_right zero_le
            (Finset.prod_le_one (fun w _ => v.intValuation_le_one _))
      _ < γ v hv := hrval v (hTmem v hvTf)

  obtain ⟨a, ha⟩ := exists_forall_valued_sub_le (R := 𝓞 F) (K := F) hz hs_ne
  refine ⟨algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a, ?_, a, rfl⟩
  have hιa_S : ∀ w : HeightOneSpectrum (𝓞 F),
      (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a) w ∈
        (w.adicCompletionIntegers F : Set (w.adicCompletion F)) :=
    fun w => algebraMap_mem_adicCompletionIntegers w a
  obtain ⟨a', ha'⟩ := RestrictedProduct.exists_structureMap_eq_of_forall
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) hιa_S
  suffices h : a' ∈ T.pi W by
    have := hWsub h; rw [Set.mem_preimage, ha'] at this; exact this.1
  intro v hv
  apply hγ v hv
  have ha'v : (a' v : v.adicCompletion F)
      = (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a) v := by rw [← ha']; rfl
  have hz'v : (z' v : v.adicCompletion F) = z v := by rw [← hz']; rfl
  rw [ha'v, hz'v]
  calc Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a) v - z v)
      = Valued.v (z v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
        rw [Valuation.map_sub_swap]; congr 2
    _ ≤ Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) := ha v
    _ < γ v hv := by rw [valued_algebraMap]; exact hsval v hv

end NumberField.AdelicBox

namespace NumberField.AdelicBox

theorem exists_denom_of_hasCompactSupport
    {F : Type*} [Field F] [NumberField F]
    {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hcs : HasCompactSupport h) :
    ∃ d : 𝓞 F, d ≠ 0 ∧ ∀ κ : F, h (algebraMap F (FiniteAdeleRing (𝓞 F) F) κ) ≠ 0 →
      ∃ a : 𝓞 F, (d : F) * κ = a
  := by
  classical

  have hC : IsCompact (tsupport h) := hcs

  let U : {s : 𝓞 F // s ≠ 0} → Set (FiniteAdeleRing (𝓞 F) F) := fun s =>
    {z | algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s * z ∈ integralFiniteAdeles (𝓞 F) F}
  have hU_open : ∀ s, IsOpen (U s) := fun s =>
    (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul continuous_id)
  have hU_cover : tsupport h ⊆ ⋃ s, U s := fun y _ => by
    obtain ⟨s, hs_ne, hs⟩ := exists_mul_mem_integralFiniteAdeles (𝓞 F) F y
    exact Set.mem_iUnion.mpr ⟨⟨s, hs_ne⟩, hs⟩

  obtain ⟨T, hT⟩ := hC.elim_finite_subcover U hU_open hU_cover

  by_cases hTne : T.Nonempty
  ·
    refine ⟨∏ s ∈ T, (s : 𝓞 F), Finset.prod_ne_zero_iff.mpr fun s _ => s.2, fun κ hκ => ?_⟩

    have hκ_supp : algebraMap F (FiniteAdeleRing (𝓞 F) F) κ ∈ tsupport h :=
      subset_tsupport h hκ

    have hκcov := hT hκ_supp
    simp only [Set.mem_iUnion, exists_prop] at hκcov
    obtain ⟨s₀, hs₀T, hκU⟩ := hκcov

    have hd_mul : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) (∏ s ∈ T, (s : 𝓞 F))
        * algebraMap F (FiniteAdeleRing (𝓞 F) F) κ ∈ integralFiniteAdeles (𝓞 F) F := by
      rw [← Finset.prod_erase_mul T _ hs₀T, map_mul, mul_assoc]
      intro v
      exact mul_mem (algebraMap_mem_adicCompletionIntegers v _) (hκU v)

    have heq : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) (∏ s ∈ T, (s : 𝓞 F))
        * algebraMap F (FiniteAdeleRing (𝓞 F) F) κ
        = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((∏ s ∈ T, ((s : 𝓞 F) : F)) * κ) := by
      rw [map_mul]
      congr 1
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F), map_prod]
    rw [heq] at hd_mul
    have hval : ∀ v : HeightOneSpectrum (𝓞 F),
        v.valuation F ((∏ s ∈ T, ((s : 𝓞 F) : F)) * κ) ≤ 1 := by
      intro v
      have hv := hd_mul v
      rw [← valuedAdicCompletion_eq_valuation' v]
      exact hv
    obtain ⟨a, ha⟩ := mem_integers_of_valuation_le_one (R := 𝓞 F) F _ hval
    refine ⟨a, ?_⟩
    have hcoe : ((∏ s ∈ T, (s : 𝓞 F) : 𝓞 F) : F) = ∏ s ∈ T, ((s : 𝓞 F) : F) := by
      push_cast; ring
    rw [hcoe, ← ha]
  ·
    refine ⟨1, one_ne_zero, fun κ hκ => absurd ?_ hκ⟩
    have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
    have hsupp_empty : tsupport h ⊆ ∅ := by
      intro y hy
      have := hT hy
      simp only [hTempty, Finset.notMem_empty, Set.mem_iUnion, exists_prop,
        false_and, exists_false] at this
    exact image_eq_zero_of_notMem_tsupport (fun hmem => hsupp_empty hmem)

end NumberField.AdelicBox

namespace NumberField.AdelicBox

theorem isLocallyConstant_and_hasCompactSupport_indicator_image_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (hd : d ≠ 0) (k : F) :
    IsLocallyConstant (((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
      ∧ HasCompactSupport (((fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F).indicator
        (1 : FiniteAdeleRing (𝓞 F) F → ℂ))
  := by
  set S := (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F with hSdef
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  have hS : S = (fun y : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
      * (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) ⁻¹' integralFiniteAdeles (𝓞 F) F := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (algebraMap F (FiniteAdeleRing (𝓞 F) F) k
        + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)
        ∈ integralFiniteAdeles (𝓞 F) F
      rwa [add_sub_cancel_left, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul]
    · intro hy
      refine ⟨_, hy, ?_⟩
      show algebraMap F (FiniteAdeleRing (𝓞 F) F) k + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)
        * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹ * (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) k)) = y
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hd', map_one, one_mul, add_sub_cancel]
  have hopen : IsOpen S := by
    rw [hS]
    exact (isOpen_integralFiniteAdeles F).preimage (continuous_const.mul (continuous_id.sub continuous_const))
  have hcpt : IsCompact S :=
    (isCompact_integralFiniteAdeles F).image (continuous_const.add (continuous_const.mul continuous_id))
  have hclopen : IsClopen S := ⟨hcpt.isClosed, hopen⟩
  refine ⟨?_, HasCompactSupport.intro hcpt fun x hx => Set.indicator_of_notMem hx _⟩
  rw [← LocallyConstant.coe_charFn ℂ hclopen]
  exact (LocallyConstant.charFn ℂ hclopen).isLocallyConstant

end NumberField.AdelicBox

namespace NumberField.AdelicBox

theorem algebraMap_mem_image_integralFiniteAdeles_iff
    (F : Type) [Field F] [NumberField F] (d : 𝓞 F) (hd : d ≠ 0) (k ξ : F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈
        (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
          + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F
      ↔ ∃ a : 𝓞 F, ξ = k + (d : F) * (a : F)
  := by
  have hd' : (d : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr hd
  constructor
  · rintro ⟨z, hz, h⟩
    set y : F := (d : F)⁻¹ * (ξ - k) with hy
    have hz' : z = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by
      have h1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z
          = algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ - k) := by
        rw [map_sub, ← h]; ring
      calc z = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((d : F)⁻¹ * (d : F)) * z := by
              rw [inv_mul_cancel₀ hd', map_one, one_mul]
        _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F)⁻¹
              * (algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) := by rw [map_mul, mul_assoc]
        _ = algebraMap F (FiniteAdeleRing (𝓞 F) F) y := by rw [h1, ← map_mul]
    have hyint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), v.valuation F y ≤ 1 := fun v => by
      have hv : (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v ∈ v.adicCompletionIntegers F := by
        rw [← hz']; exact hz v
      rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        show (algebraMap F (FiniteAdeleRing (𝓞 F) F) y) v = (y : v.adicCompletion F) from rfl,
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F y hyint
    refine ⟨a, ?_⟩
    rw [RingOfIntegers.coe_eq_algebraMap a, ha, hy, mul_inv_cancel_left₀ hd', add_sub_cancel]
  · rintro ⟨a, rfl⟩
    refine ⟨algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F), fun v => ?_, by simp only [map_add, map_mul]⟩
    rw [RingOfIntegers.coe_eq_algebraMap]
    exact algebraMap_mem_adicCompletionIntegers v a

end NumberField.AdelicBox

end
