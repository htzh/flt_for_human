/-
Tate agreement — the finiteness half: `tateCommFinite` and its discharge chain, after
FLT's `P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean` (1,257 ln, 53 declarations)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean>).

This is set 3.3a's theory module.  It proves `ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite`
(the Tate commutator is finite-dimensional over the constant field) through the pin's
chain `clearPole → poleWindowFinite → DVRQuotPowKFinite → DVRCotangentKFinite`, and
exposes the pin's public surface at its own names.  The shared API definitions live in
`AlgebraicCurve/Defs/TateResidueCurrency.lean`; later row-3.3 sets import that home,
not this proof theory.

Assumes: the port's `Defs/TateResidueCurrency.lean` (the `tateComm` vocabulary and the
Tate atoms), `Defs/PlaceCompletion.lean` (the adic completion, its integers and the
`kwHgfV352_*` residue rows), `Defs/PushPull.lean` (`Place.fiber`) and the `Defs` layer
under them.

The pin's `p2m_*` scaffolding is dropped.  Two classes of declaration are resolved
locally:
* the pin's `Def_DedekindDomain_AdicValuation_InlineSpecific.lean` is not ported, so
  its `completionIdeal` and the private uniformizer chain it needs are transcribed
  `private` at the pin's names (pin 299/430/438/447/455/474/513/525).  This is
  **promotion debt**: they belong in a future `Place/Completion.lean` home (see the
  friction log).
* `Place.ord_nonneg_of_mem`/`Place.mem_of_ord_nonneg` are the port's public
  `Defs/PushPull.lean` lemmas (they already match the pin wrappers), so the pin's
  section-local copies at pin 258/273 are not re-proved.

The pin's local `maxHeartbeats` raises are not transcribed (the project cap is
4,000,000); the two heavy quotient steps are the only places this could bite.
-/
import FLTForHuman.AlgebraicCurve.Defs.TateResidueCurrency
import Mathlib.Algebra.Group.Int.TypeTags
import FLTForHuman.AlgebraicCurve.Place.Completion

set_option autoImplicit false
set_option linter.unusedSectionVars false

open LinearMap Submodule IsLocalRing IsDedekindDomain WithZero Multiplicative
open AlgebraicCurve AlgebraicCurve.Place

noncomputable section

namespace IsLocalRing

/-- A proper ideal containing the maximal ideal is the maximal ideal. -/
theorem maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R

end IsLocalRing


/-! ### The unported `InlineSpecific` uniformizer chain (private)

`Def_DedekindDomain_AdicValuation_InlineSpecific.lean` (pin 299–551) supplies
`completionIdeal` and the uniformizer facts the pin's `kwF4R1V410a_*` block uses.
The port did not port that module (it was not needed by set 3.1a), so the pieces
reached here are transcribed `private` at the pin's names.  Promotion debt. -/


/-! ### The `tateProj` projection -/

namespace ModularCurve.KwF4gRRTate

section TateProj

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem mem_adicIntegersKSubmod_iff (x : u.adicCompletion) :
    x ∈ adicIntegersKSubmod u ↔ x ∈ u.adicCompletionIntegers := Iff.rfl

theorem tateProj_mem_integers (x : u.adicCompletion) :
    tateProj u x ∈ u.adicCompletionIntegers :=
  (mem_adicIntegersKSubmod_iff u _).mp
    (Submodule.coe_mem
      (Submodule.projectionOnto (adicIntegersKSubmod u) _
        (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u))) x))

theorem tateProj_of_mem {x : u.adicCompletion} (hx : x ∈ u.adicCompletionIntegers) :
    tateProj u x = x := by
  have h := Submodule.projectionOnto_apply_left
    (Classical.choose_spec (Submodule.exists_isCompl (adicIntegersKSubmod u)))
    (⟨x, (mem_adicIntegersKSubmod_iff u x).mpr hx⟩ : adicIntegersKSubmod u)
  have hcoe := congrArg (Subtype.val (p := fun y => y ∈ adicIntegersKSubmod u)) h
  exact hcoe

theorem range_tateProj : LinearMap.range (tateProj u) = adicIntegersKSubmod u := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact tateProj_mem_integers u y
  · intro x hx
    exact ⟨x, tateProj_of_mem u hx⟩

end TateProj

/-! ### The pole window -/

section PoleWindow

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

def poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletion where
  carrier := {x | (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, mul_add] at ha hb ⊢; exact add_mem ha hb
  zero_mem' := by simp only [Set.mem_ofPred_eq, mul_zero]; exact zero_mem _
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply K L u.adicCompletion, mul_left_comm]
    exact mul_mem ((kwHgfV352_algebraMap_mem_adicCompletionIntegers_iff u _).mpr
      (u.algebraMap_mem' c)) hx

theorem mem_poleWindowKSubmod_iff (πh : u.adicCompletionIntegers) (M : ℕ)
    (x : u.adicCompletion) :
    x ∈ poleWindowKSubmod u πh M ↔ (πh : u.adicCompletion)^M * x ∈ u.adicCompletionIntegers :=
  Iff.rfl

theorem adicIntegersKSubmod_le_poleWindowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    adicIntegersKSubmod u ≤ poleWindowKSubmod u πh M :=
  fun _ hx => mul_mem (pow_mem πh.2 M) hx

theorem kwF4gRRTate_clearPole (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (fh : u.adicCompletion) :
    ∃ M : ℕ, (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers := by
  obtain ⟨a, b, hb, hfh⟩ := IsFractionRing.div_surjective
    (A := u.adicCompletionIntegers) (K := u.adicCompletion) fh
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨M, ub, hbeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπh
  refine ⟨M, ?_⟩

  have hcoe : ∀ x : u.adicCompletionIntegers,
      (x : u.adicCompletion) = algebraMap _ u.adicCompletion x := fun _ => rfl
  have hbK0 : (b : u.adicCompletion) ≠ 0 := by
    rw [hcoe]; exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb0
  have hbfh : (b : u.adicCompletion) * fh = (a : u.adicCompletion) := by
    rw [← hfh, hcoe b, hcoe a, mul_div_cancel₀ _ (hcoe b ▸ hbK0)]

  have hπheq : ((ub⁻¹ : u.adicCompletionIntegersˣ) : u.adicCompletionIntegers) * b = πh ^ M := by
    rw [hbeq, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

  have hπheqK : ((((ub⁻¹ : u.adicCompletionIntegersˣ) : u.adicCompletionIntegers)
        : u.adicCompletion)) * (b : u.adicCompletion)
      = (πh : u.adicCompletion)^M := by
    have := congrArg (algebraMap u.adicCompletionIntegers u.adicCompletion) hπheq
    simp only [map_mul, map_pow] at this
    exact this

  rw [← hπheqK, mul_assoc, hbfh]
  exact mul_mem (Subtype.coe_prop _) a.2

variable (K L) in

def KwF4gRRTateClearPole : Prop :=
  ∀ (u : Place K L) (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (fh : u.adicCompletion),
    ∃ M : ℕ, (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers

theorem kwF4gRRTate_clearPole_discharged : KwF4gRRTateClearPole K L :=
  fun u πh hπh fh => kwF4gRRTate_clearPole u πh hπh fh

theorem lmul_mem_poleWindow (πh : u.adicCompletionIntegers) (M : ℕ) (fh : u.adicCompletion)
    (hM : (πh : u.adicCompletion)^M * fh ∈ u.adicCompletionIntegers)
    {a : u.adicCompletion} (ha : a ∈ u.adicCompletionIntegers) :
    fh * a ∈ poleWindowKSubmod u πh M := by
  rw [mem_poleWindowKSubmod_iff, ← mul_assoc]; exact mul_mem hM ha

variable (K L) in

def KwF4gRRTatePoleWindowFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K
      (poleWindowKSubmod u πh M ⧸
        (adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)

theorem ker_tateProj_inf_integers :
    LinearMap.ker (tateProj u) ⊓ adicIntegersKSubmod u = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hker, hint⟩ := Submodule.mem_inf.mp hx
  have h0 : tateProj u x = 0 := LinearMap.mem_ker.mp hker
  rw [Submodule.mem_bot, ← tateProj_of_mem u hint, h0]

theorem finiteDimensional_ker_inf_poleWindow [u.FiniteResidue]
    (hPW : KwF4gRRTatePoleWindowFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K
      ((LinearMap.ker (tateProj u) ⊓ poleWindowKSubmod u πh M : Submodule K _)) := by
  haveI := hPW u πh hπh M
  set A := adicIntegersKSubmod u
  set P := poleWindowKSubmod u πh M
  let A' : Submodule K P := A.comap P.subtype
  let ι : (LinearMap.ker (tateProj u) ⊓ P : Submodule K _) →ₗ[K] P ⧸ A' :=
    (A'.mkQ).comp (Submodule.inclusion inf_le_right)
  refine FiniteDimensional.of_injective ι ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro xh hxker
  obtain ⟨x, hxkp⟩ := xh
  obtain ⟨hxk, hxp⟩ := Submodule.mem_inf.mp hxkp
  simp only [ι, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Submodule.inclusion_apply] at hxker
  have hxA : x ∈ A := hxker
  have hx0 : x = 0 := by
    have hbot : x ∈ (⊥ : Submodule K u.adicCompletion) := by
      rw [← ker_tateProj_inf_integers u]; exact Submodule.mem_inf.mpr ⟨hxk, hxA⟩
    exact (Submodule.mem_bot K).mp hbot
  exact Subtype.ext hx0

theorem finiteDimensional_principalPart_range [u.FiniteResidue]
    (hCP : KwF4gRRTateClearPole K L) (hPW : KwF4gRRTatePoleWindowFinite K L)
    (fh : u.adicCompletion) :
    FiniteDimensional K
      (LinearMap.range
        ((LinearMap.id - tateProj u) ∘ₗ lmulK u fh ∘ₗ (adicIntegersKSubmod u).subtype)) := by
  obtain ⟨πh, hπh⟩ := IsDiscreteValuationRing.exists_irreducible u.adicCompletionIntegers
  obtain ⟨M, hM⟩ := hCP u πh hπh fh
  haveI := finiteDimensional_ker_inf_poleWindow u hPW πh hπh M
  refine Submodule.finiteDimensional_of_le
    (S₂ := LinearMap.ker (tateProj u) ⊓ poleWindowKSubmod u πh M) ?_
  rintro y ⟨⟨a, ha⟩, rfl⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.sub_apply,
    LinearMap.id_apply]
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [LinearMap.mem_ker, map_sub, tateProj_of_mem u (tateProj_mem_integers u _), sub_self]
  · exact sub_mem (lmul_mem_poleWindow u πh M fh hM ha)
      (adicIntegersKSubmod_le_poleWindowKSubmod u πh M (tateProj_mem_integers u _))

theorem tateComm_target_le_range (pA φ ψ : u.adicCompletion →ₗ[K] u.adicCompletion)
    (Rf Rg : Submodule K u.adicCompletion) :
    Submodule.map (pA ∘ₗ ψ) Rf ⊔ Submodule.map (pA ∘ₗ φ) Rg ≤ LinearMap.range pA := by
  refine sup_le ?_ ?_ <;>
  · rintro y ⟨x, _, rfl⟩; exact LinearMap.mem_range_self pA _

theorem kwF4gRRTate_commFinite_of_clearPole_of_poleWindowFinite
    [∀ u : Place K L, u.FiniteResidue]
    (hCP : KwF4gRRTateClearPole K L) (hPW : KwF4gRRTatePoleWindowFinite K L) :
    KwF4gRRTateCommFinite K L := by
  intro u fh gh
  have hcomm : lmulK u fh ∘ₗ lmulK u gh = lmulK u gh ∘ₗ lmulK u fh := by
    ext x
    simp only [LinearMap.comp_apply, lmulK, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
    simp only [IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_mul]
    ring
  haveI hRf := finiteDimensional_principalPart_range u hCP hPW fh
  haveI hRg := finiteDimensional_principalPart_range u hCP hPW gh
  set pA := tateProj u
  set A := adicIntegersKSubmod u
  set Rf := LinearMap.range ((LinearMap.id - pA) ∘ₗ lmulK u fh ∘ₗ A.subtype)
  set Rg := LinearMap.range ((LinearMap.id - pA) ∘ₗ lmulK u gh ∘ₗ A.subtype)
  set S : Submodule K u.adicCompletion :=
    Submodule.map (pA ∘ₗ lmulK u gh) Rf ⊔ Submodule.map (pA ∘ₗ lmulK u fh) Rg

  haveI : FiniteDimensional K (Submodule.map (pA ∘ₗ lmulK u gh) Rf) := Module.Finite.map _ _
  haveI : FiniteDimensional K (Submodule.map (pA ∘ₗ lmulK u fh) Rg) := Module.Finite.map _ _
  haveI hSfin : FiniteDimensional K S := Submodule.finiteDimensional_sup _ _

  have hSle : S ≤ LinearMap.range pA :=
    tateComm_target_le_range u pA (lmulK u fh) (lmulK u gh) Rf Rg
  haveI : FiniteDimensional K (S.comap (LinearMap.range pA).subtype) := by
    have e := Submodule.comapSubtypeEquivOfLe hSle
    exact FiniteDimensional.of_injective e.toLinearMap e.injective

  refine Submodule.finiteDimensional_of_le (S₂ := S.comap (LinearMap.range pA).subtype) ?_
  rintro y ⟨⟨a, haR⟩, rfl⟩
  have haA : a ∈ adicIntegersKSubmod u := range_tateProj u ▸ haR
  rw [Submodule.mem_comap, Submodule.subtype_apply, tateCommRestrict_apply,
    tateComm_eq_of_commute hcomm a]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · exact ⟨(lmulK u fh) a - pA ((lmulK u fh) a), ⟨⟨a, haA⟩, rfl⟩, rfl⟩
  · exact ⟨(lmulK u gh) a - pA ((lmulK u gh) a), ⟨⟨a, haA⟩, rfl⟩, rfl⟩

theorem kwF4gRRTate_commFinite_of_poleWindowFinite [∀ u : Place K L, u.FiniteResidue]
    (hPW : KwF4gRRTatePoleWindowFinite K L) :
    KwF4gRRTateCommFinite K L :=
  kwF4gRRTate_commFinite_of_clearPole_of_poleWindowFinite
    kwF4gRRTate_clearPole_discharged hPW

end PoleWindow

end ModularCurve.KwF4gRRTate

/-! ### The open valuation ball -/

namespace IsDedekindDomain.HeightOneSpectrum

namespace adicCompletion

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

theorem isOpen_setOf_valued_le {γ : ℤᵐ⁰} (hγ : γ ≠ 0) :
    IsOpen {y : v.adicCompletion K | Valued.v y ≤ γ} := by

  obtain ⟨z, hz⟩ := valuedAdicCompletion_surjective K v γ
  have hz0 : vK z ≠ 0 := by rw [hz]; exact hγ
  have hr0 : (vK).restrict z ≠ 0 := fun h =>
    hz0 ((Valuation.restrict_eq_zero_iff vK).mp h)
  have hset : {y : v.adicCompletion K | Valued.v y ≤ γ}
      = {y : v.adicCompletion K | (vK).restrict y ≤ (vK).restrict z} := by
    ext y
    simp only [Set.mem_ofPred_eq, Valuation.restrict_le_iff, hz]
  rw [hset]
  exact Valued.isOpen_closedBall _ hr0

end adicCompletion

end IsDedekindDomain.HeightOneSpectrum

/-! ### The `kwF4R1V410a` quotient bridge -/

namespace ModularCurve

namespace KwF4R1V410a

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

scoped instance kwF4R1V410a_subsingletonHeightOneSpectrumDVR :
    Subsingleton (HeightOneSpectrum O) :=
  ⟨fun a b => IsDedekindDomain.HeightOneSpectrum.ext
    (((IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime O).mp
      inferInstance).2.unique ⟨a.3, a.2⟩ ⟨b.3, b.2⟩)⟩

section Bridge

open IsDedekindDomain.HeightOneSpectrum

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

local notation "O_w" => w.toValuationSubring
local notation "𝔪_w" => IsLocalRing.maximalIdeal w.toValuationSubring
local notation "O_W" => w.adicCompletionIntegers
local notation "𝔪_W" => w.heightOneSpectrum.completionIdeal F

theorem kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff (n : ℕ) (x : O_w) :
    algebraMap (O_w) (O_W) x ∈ (𝔪_W) ^ n ↔ x ∈ (𝔪_w) ^ n := by
  have hval : Valued.v (algebraMap (O_w) (O_W) x).val
      = w.heightOneSpectrum.intValuation x := by
    have h1 : (algebraMap (O_w) (O_W) x).val
        = ((algebraMap (O_w) F x : F) : w.adicCompletion) := rfl
    rw [h1, valuedAdicCompletion_eq_valuation' (K := F) w.heightOneSpectrum,
      valuation_of_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow, hval,
    ← WithZero.exp_eq_coe_ofAdd, intValuation_le_pow_iff_mem, w.heightOneSpectrum_asIdeal]

theorem kwF4R1V410a_exists_sub_mem_completionIdeal_pow (n : ℕ) (y : O_W) :
    ∃ x : O_w, y - algebraMap (O_w) (O_W) x ∈ (𝔪_W) ^ n := by

  have hball_open : IsOpen {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} :=
    (IsDedekindDomain.HeightOneSpectrum.adicCompletion.isOpen_setOf_valued_le F
      w.heightOneSpectrum WithZero.exp_ne_zero).preimage (continuous_sub_right y.val)
  have hy_mem : y.val ∈ {z : w.adicCompletion |
      Valued.v (z - y.val) ≤ WithZero.exp (-(n : ℤ))} := by
    simp only [Set.mem_ofPred_eq, sub_self, _root_.map_zero]; exact zero_le
  have hmeet := mem_closure_iff.mp
    ((denseRange_algebraMap F w.heightOneSpectrum) y.val) _ hball_open hy_mem

  have hexists : ∃ z : F, Valued.v (algebraMap F w.adicCompletion z - y.val)
      ≤ WithZero.exp (-(n : ℤ)) := by
    rcases hmeet with ⟨z₀, hz₀_ball, z, hz_eq⟩
    exact ⟨z, hz_eq ▸ hz₀_ball⟩
  obtain ⟨z, hz⟩ := hexists
  rw [show algebraMap F w.adicCompletion z = ((z : F) : w.adicCompletion) from rfl] at hz

  have hz_val_le : w.heightOneSpectrum.valuation F z ≤ 1 := by
    have hzhat : Valued.v ((z : w.adicCompletion)) ≤ (1 : ℤᵐ⁰) := by
      calc Valued.v ((z : w.adicCompletion))
          = Valued.v (((z : w.adicCompletion) - y.val) + y.val) := by ring_nf
        _ ≤ max (Valued.v ((z : w.adicCompletion) - y.val)) (Valued.v y.val) :=
            Valuation.map_add _ _ _
        _ ≤ (1 : ℤᵐ⁰) := max_le
            (hz.trans (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by omega)))
            y.2
    rwa [valuedAdicCompletion_eq_valuation'] at hzhat
  have hz_mem : z ∈ (O_w : ValuationSubring F) := by
    obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one F z
      (fun v' => by
        obtain rfl : v' = w.heightOneSpectrum := Subsingleton.elim _ _
        exact hz_val_le)
    exact hr ▸ r.2
  refine ⟨⟨z, hz_mem⟩, ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletion.mem_completionIdeal_pow,
    ← WithZero.exp_eq_coe_ofAdd]
  have hsub : (y - algebraMap (O_w) (O_W) ⟨z, hz_mem⟩ : O_W).val
      = y.val - ((z : F) : w.adicCompletion) := rfl
  rw [hsub, Valuation.map_sub_swap]
  exact hz

def kwF4R1V410a_quotientEquiv (n : ℕ) :
    (O_w) ⧸ (𝔪_w) ^ n ≃+* (O_W) ⧸ (𝔪_W) ^ n := by
  let hIJ : (𝔪_w) ^ n ≤ (𝔪_W ^ n).comap (algebraMap (O_w) (O_W)) :=
    fun x hx => (kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff w n x).mpr hx
  let hJI : ((𝔪_W) ^ n).comap (algebraMap (O_w) (O_W)) ≤ (𝔪_w) ^ n :=
    fun x hx => (kwF4R1V410a_algebraMap_mem_completionIdeal_pow_iff w n x).mp
      (Ideal.mem_comap.mp hx)
  exact RingEquiv.ofBijective (Ideal.quotientMap _ _ hIJ)
    ⟨Ideal.quotientMap_injective' (H := hIJ) hJI,
    fun y => by
      obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨x, hx⟩ := kwF4R1V410a_exists_sub_mem_completionIdeal_pow w n y'
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      simp only [Ideal.quotientMap_mk]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (by
        rw [← neg_sub, neg_mem_iff]; exact hx)⟩

theorem kwF4R1V410a_quotientEquiv_mk (n : ℕ) (x : O_w) :
    kwF4R1V410a_quotientEquiv w n (Ideal.Quotient.mk _ x)
      = Ideal.Quotient.mk _ (algebraMap (O_w) (O_W) x) := rfl

end Bridge

end KwF4R1V410a

end ModularCurve

/-! ### The pole-window shift -/

namespace ModularCurve.KwF4gRRTate

section PoleWindowShift

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem coe_smul_K (c : K) (x : u.adicCompletionIntegers) :
    ((c • x : u.adicCompletionIntegers) : u.adicCompletion) = c • (x : u.adicCompletion) := by
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

def poleWindowShift (πh : u.adicCompletionIntegers) (M : ℕ) :
    poleWindowKSubmod u πh M →ₗ[K] u.adicCompletionIntegers where
  toFun x := ⟨(πh : u.adicCompletion)^M * (x : u.adicCompletion), x.2⟩
  map_add' x y := by apply Subtype.ext; push_cast; ring
  map_smul' c x := by
    apply Subtype.ext
    rw [coe_smul_K]
    show (πh : u.adicCompletion)^M * (c • (x : u.adicCompletion))
        = c • ((πh : u.adicCompletion)^M * (x : u.adicCompletion))
    rw [mul_smul_comm]

theorem poleWindowShift_injective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Injective (poleWindowShift u πh M) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz
    exact hπh.ne_zero (Subtype.ext hz)
  have hx0 : (x : u.adicCompletion) = 0 := by
    have := congrArg Subtype.val hx
    exact (mul_eq_zero.mp this).resolve_left hπhM0
  exact Subtype.ext hx0

theorem poleWindowShift_surjective (πh : u.adicCompletionIntegers) (hπh : Irreducible πh)
    (M : ℕ) : Function.Surjective (poleWindowShift u πh M) := by
  intro y
  have hπhM0 : (πh : u.adicCompletion)^M ≠ 0 := by
    refine pow_ne_zero M ?_
    intro hz; exact hπh.ne_zero (Subtype.ext hz)
  refine ⟨⟨(y : u.adicCompletion) / (πh : u.adicCompletion)^M, ?_⟩, ?_⟩
  · rw [mem_poleWindowKSubmod_iff, mul_div_cancel₀ _ hπhM0]; exact y.2
  · apply Subtype.ext
    show (πh : u.adicCompletion)^M * ((y : u.adicCompletion) / (πh : u.adicCompletion)^M)
        = (y : u.adicCompletion)
    rw [mul_div_cancel₀ _ hπhM0]

def poleWindowShiftEquiv (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    poleWindowKSubmod u πh M ≃ₗ[K] u.adicCompletionIntegers :=
  LinearEquiv.ofBijective (poleWindowShift u πh M)
    ⟨poleWindowShift_injective u πh hπh M, poleWindowShift_surjective u πh hπh M⟩

def piPowKSubmod (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule K u.adicCompletionIntegers where
  carrier := {y | ∃ x : u.adicCompletionIntegers, y = πh^M * x}
  add_mem' := by rintro a b ⟨xa, rfl⟩ ⟨xb, rfl⟩; exact ⟨xa + xb, by ring⟩
  zero_mem' := ⟨0, by ring⟩
  smul_mem' c y := by
    rintro ⟨x, rfl⟩
    exact ⟨c • x, by rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]⟩

theorem poleWindowShift_image_integers (πh : u.adicCompletionIntegers) (M : ℕ) :
    Submodule.map (poleWindowShift u πh M)
        ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
      = piPowKSubmod u πh M := by
  ext y
  constructor
  · rintro ⟨⟨x, hxP⟩, hxA, rfl⟩
    refine ⟨⟨(x : u.adicCompletion), hxA⟩, ?_⟩
    apply Subtype.ext; push_cast; rfl
  · rintro ⟨x, rfl⟩
    refine ⟨⟨(x : u.adicCompletion),
      adicIntegersKSubmod_le_poleWindowKSubmod u πh M x.2⟩, x.2, ?_⟩
    apply Subtype.ext; push_cast; rfl

variable (K L) in

def KwF4gRRTateDVRQuotPowKFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh)
    (M : ℕ),
    FiniteDimensional K (u.adicCompletionIntegers ⧸ piPowKSubmod u πh M)

theorem kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite
    (hDVR : KwF4gRRTateDVRQuotPowKFinite K L) :
    KwF4gRRTatePoleWindowFinite K L := by
  intro u _ πh hπh M
  haveI := hDVR u πh hπh M

  let e' := Submodule.Quotient.equiv
    ((adicIntegersKSubmod u).comap (poleWindowKSubmod u πh M).subtype)
    (piPowKSubmod u πh M)
    (poleWindowShiftEquiv u πh hπh M)
    (poleWindowShift_image_integers u πh M)
  exact FiniteDimensional.of_injective e'.toLinearMap e'.injective

theorem kwF4gRRTate_commFinite_of_DVRQuotPowKFinite [∀ u : Place K L, u.FiniteResidue]
    (hDVR : KwF4gRRTateDVRQuotPowKFinite K L) :
    KwF4gRRTateCommFinite K L :=
  kwF4gRRTate_commFinite_of_poleWindowFinite
    (kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite hDVR)

end PoleWindowShift

/-! ### The DVR-quotient discharge -/

section DVRQuotDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

theorem piPowKSubmod_eq_restrictScalars (πh : u.adicCompletionIntegers) (M : ℕ) :
    piPowKSubmod u πh M
      = (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  rw [Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => ⟨x, h⟩⟩

def quotPiPowEquivIdealQuot (πh : u.adicCompletionIntegers) (M : ℕ) :
    (u.adicCompletionIntegers ⧸ piPowKSubmod u πh M)
      ≃ₗ[K] (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) :=
  (Submodule.quotEquivOfEq _ _ (piPowKSubmod_eq_restrictScalars u πh M)).trans
    (Submodule.Quotient.restrictScalarsEquiv K _)

variable (K L) in

def KwF4gRRTateDVRCotangentKFinite : Prop :=
  ∀ (u : Place K L) [u.FiniteResidue] (πh : u.adicCompletionIntegers) (_ : Irreducible πh),
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))

theorem range_mulLeft_eq_restrictScalars_span (a : u.adicCompletionIntegers) :
    LinearMap.range (LinearMap.mulLeft K a)
      = (Ideal.span {a} : Ideal u.adicCompletionIntegers).restrictScalars K := by
  ext y
  simp only [LinearMap.mem_range, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩

theorem finiteDimensional_restrictScalarsQuot_pow [u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K (u.adicCompletionIntegers ⧸
      (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
  induction M with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one, Submodule.restrictScalars_top]
    infer_instance
  | succ M ih =>
    have hle : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)
        ≤ Ideal.span {πh^M} := by
      rw [Ideal.span_singleton_le_span_singleton, pow_succ]; exact ⟨πh, rfl⟩
    have hle' : (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K
        ≤ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers).restrictScalars K :=
      Submodule.restrictScalars_mono K hle

    set N : Submodule K (u.adicCompletionIntegers ⧸
        (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
      (Submodule.restrictScalars K (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)).map
        (Submodule.restrictScalars K (Ideal.span {πh^(M+1)} : Ideal _)).mkQ with hN_def

    haveI hquot : FiniteDimensional K
        ((u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal _).restrictScalars K) ⧸ N) := by
      haveI := ih
      exact Module.Finite.equiv
        (Submodule.quotientQuotientEquivQuotient _ _ hle').symm

    haveI hN : FiniteDimensional K N := by
      set φ : u.adicCompletionIntegers →ₗ[K] (u.adicCompletionIntegers ⧸
          (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers).restrictScalars K) :=
        (Submodule.restrictScalars K
            (Ideal.span {πh^(M+1)} : Ideal u.adicCompletionIntegers)).mkQ ∘ₗ
          LinearMap.mulLeft K (πh^M) with hφ_def
      have hrange : LinearMap.range φ = N := by
        rw [hφ_def, LinearMap.range_comp, range_mulLeft_eq_restrictScalars_span, hN_def]
      have hker : LinearMap.ker φ
          = (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K := by
        simp only [hφ_def, LinearMap.ker_comp, Submodule.ker_mkQ]
        ext x
        simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.restrictScalars_mem,
          Ideal.mem_span_singleton]
        have hπM : (πh : u.adicCompletionIntegers)^M ≠ 0 := pow_ne_zero M hπh.ne_zero
        constructor
        · rintro ⟨c, hc⟩
          exact ⟨c, mul_left_cancel₀ hπM (by rw [hc, pow_succ, mul_assoc])⟩
        · rintro ⟨c, hc⟩
          exact ⟨c, by rw [hc, pow_succ, mul_assoc]⟩

      let e₁ : (u.adicCompletionIntegers ⧸
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K)
          ≃ₗ[K] (u.adicCompletionIntegers ⧸ LinearMap.ker φ) :=
        Submodule.quotEquivOfEq _ _ hker.symm
      let e₂ : (u.adicCompletionIntegers ⧸ LinearMap.ker φ) ≃ₗ[K] LinearMap.range φ :=
        φ.quotKerEquivRange
      let e₃ : (LinearMap.range φ : Submodule K _) ≃ₗ[K] N := LinearEquiv.ofEq _ _ hrange
      haveI hCK : FiniteDimensional K (u.adicCompletionIntegers ⧸
          (Ideal.span {πh} : Ideal u.adicCompletionIntegers).restrictScalars K) := by
        haveI := hCot u πh hπh
        exact Module.Finite.equiv
          (Submodule.Quotient.restrictScalarsEquiv K
            (Ideal.span {πh} : Ideal u.adicCompletionIntegers)).symm
      exact Module.Finite.equiv ((e₁.trans e₂).trans e₃)
    exact Module.Finite.of_submodule_quotient N

theorem finiteDimensional_idealQuot_pow [u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L)
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) (M : ℕ) :
    FiniteDimensional K
      (u.adicCompletionIntegers ⧸ (Ideal.span {πh^M} : Ideal u.adicCompletionIntegers)) := by
  haveI := finiteDimensional_restrictScalarsQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv K _)

theorem kwF4gRRTate_DVRQuotPowKFinite_of_cotangent
    (hCot : KwF4gRRTateDVRCotangentKFinite K L) :
    KwF4gRRTateDVRQuotPowKFinite K L := by
  intro u _ πh hπh M
  haveI := finiteDimensional_idealQuot_pow u hCot πh hπh M
  exact Module.Finite.equiv (quotPiPowEquivIdealQuot u πh M).symm

theorem kwF4gRRTate_commFinite_of_cotangent [∀ u : Place K L, u.FiniteResidue]
    (hCot : KwF4gRRTateDVRCotangentKFinite K L) :
    KwF4gRRTateCommFinite K L :=
  kwF4gRRTate_commFinite_of_DVRQuotPowKFinite
    (kwF4gRRTate_DVRQuotPowKFinite_of_cotangent hCot)

end DVRQuotDischarge

/-! ### The cotangent discharge -/

section DVRCotangentDischarge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (u : Place K L)

scoped instance instIsScalarTower_K_toValuationSubring_adicCompletionIntegers :
    IsScalarTower K u.toValuationSubring u.adicCompletionIntegers := by
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  apply Subtype.ext
  show algebraMap K u.adicCompletion k
    = (algebraMap u.toValuationSubring u.adicCompletionIntegers (algebraMap K _ k)).val
  rw [IsScalarTower.algebraMap_apply K L u.adicCompletion]
  rfl

theorem span_irreducible_eq_completionIdeal_pow_one
    (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (Ideal.span {πh} : Ideal u.adicCompletionIntegers)
      = (u.heightOneSpectrum.completionIdeal L) ^ 1 := by
  rw [pow_one, ← hπh.maximalIdeal_eq]

def quotientEquivKAlg (n : ℕ) :
    (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n)
      ≃ₐ[K] (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n) :=
  { ModularCurve.KwF4R1V410a.kwF4R1V410a_quotientEquiv u n with
    commutes' := fun k => by
      show ModularCurve.KwF4R1V410a.kwF4R1V410a_quotientEquiv u n (algebraMap K _ k)
        = algebraMap K _ k
      rw [IsScalarTower.algebraMap_apply K u.toValuationSubring
          (u.toValuationSubring ⧸ (IsLocalRing.maximalIdeal u.toValuationSubring) ^ n),
        Ideal.Quotient.algebraMap_eq, ModularCurve.KwF4R1V410a.kwF4R1V410a_quotientEquiv_mk,
        IsScalarTower.algebraMap_apply K u.adicCompletionIntegers
          (u.adicCompletionIntegers ⧸ (u.heightOneSpectrum.completionIdeal L) ^ n),
        Ideal.Quotient.algebraMap_eq,
        IsScalarTower.algebraMap_apply K u.toValuationSubring u.adicCompletionIntegers] }

def quotSpanIrreducibleEquivResidueField (πh : u.adicCompletionIntegers) (hπh : Irreducible πh) :
    (u.adicCompletionIntegers ⧸ (Ideal.span {πh} : Ideal u.adicCompletionIntegers))
      ≃ₗ[K] u.ResidueField :=
  (Ideal.quotientEquivAlgOfEq K
      (span_irreducible_eq_completionIdeal_pow_one u πh hπh)).toLinearEquiv.trans
    ((quotientEquivKAlg u 1).symm.toLinearEquiv.trans
      (Ideal.quotientEquivAlgOfEq K
        (pow_one (IsLocalRing.maximalIdeal u.toValuationSubring))).toLinearEquiv)

theorem kwF4gRRTate_DVRCotangentKFinite : KwF4gRRTateDVRCotangentKFinite K L := by
  intro u _ πh hπh
  haveI : Module.Finite K u.ResidueField := FiniteResidue.finite
  exact Module.Finite.equiv (quotSpanIrreducibleEquivResidueField u πh hπh).symm

theorem kwF4gRRTate_commFinite [∀ u : Place K L, u.FiniteResidue] :
    KwF4gRRTateCommFinite K L :=
  kwF4gRRTate_commFinite_of_cotangent kwF4gRRTate_DVRCotangentKFinite

end DVRCotangentDischarge

end ModularCurve.KwF4gRRTate

/-! ### The wrapper target -/

namespace AlgebraicCurve

theorem tateCommFinite {K L : Type*} [Field K] [Field L] [Algebra K L]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue] :
    ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L :=
  ModularCurve.KwF4gRRTate.kwF4gRRTate_commFinite

end AlgebraicCurve

end
