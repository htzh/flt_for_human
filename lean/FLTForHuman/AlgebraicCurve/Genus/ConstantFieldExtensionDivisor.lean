/-
The order of a divisor under a constant field extension: the residue degree divides the difference.

For `F'/K'` a constant field extension of `F/K` and a divisor `D` of `F`, there is a finite set of places
outside which the orders of the extended divisor at the places over a fixed point differ from the orders
of `D` by a multiple of the residue degree `[K' : K]` — the arithmetic statement of the `mapDomain`
dictionary that SET-AF107B's Riemann–Roch inequality and SET-AF107C's correspondence are the two *other*
directions of.  It is the shelf's largest row (729 pin `S_` lines over **ten** premises) and it sits above
all of them:

* the constant-field-extension place calculus (`Place/ConstantFieldExtension`,
  `Place/FromValuationSubring`), the curve structure (`IsCurveOver/{ConstantFieldExtension,
  EssFiniteType,Transcendental}`), the reduction correspondence (`ConstantReductionCorrespondence`) and
  AF106C's retraction (`RegularProlongationRetraction`);
* the genus/assembly layers (`Genus/ConstantFieldExtensionConsequences`, `RiemannRoch/Assembly`).

No existing module imports all nine premise modules, which is why this is a new module rather than an
insertion: the empty cell is the *composition* of the reduction dictionary with the Riemann–Roch assembly,
and that composition had no home.

## The rows

* `AlgebraicCurve.Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension` — 729 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_exists_natCast_dvd_ord_sub_of_constantFieldExtension.lean

PORT NOTES (SET-AF108, order A).

* **Engine diff.** The two wires (`Theorems/Thm_…` and `P2M/Sol/S_…`) carry **26 declarations**
  (1 wrapper row + 25 `S_` rows).  This module declares **16** of them — the 15 `S_` engine rows this
  order is the first to place plus the headline at the wrapper's name, which is what the pin's
  `solution` row exports — and **substitutes 10**.  The diff reads: *pin sources 2, pin decls 26,
  module decls 16; 16 by hash, 0 by name, 0 unaccounted.*
* **Namespaces.** The pin's `P2MW.S_…` label is dropped; `AlgebraicCurve.DivisibilityDescent` is the
  pin's own subject namespace and is kept, so the engine reads
  `AlgebraicCurve.DivisibilityDescent.*` and the row keeps the wrapper's
  `AlgebraicCurve.Divisor.*` name.  The pin's `p2m_open`/`p2m_export` staging, its
  `attribute [-instance]`/`[-simp]` walls and its `import Mathlib` are not transcribed.
* **Substitutions taken (10, all public in the port, imported and never re-proved).**
  `linearIndependent_adjoin_simple_of_pow_mul`, `algebraMap_mem_adjoin_simple`,
  `finrank_adjoin_algebraMap_eq` and `transfer_fg` are
  `AlgebraicCurve.PlaceReductionRiemannRoch.LowerSemicontinuity.*`
  (`Genus/PlaceReductionRiemannRoch.lean`) — byte-identical to the pin's rows, as that module's own
  diff records; `mem_of_isRoot_monic` and `isAlgClosed_residueField` are
  `AlgebraicCurve.RegularProlongation.ResidueIntegralClosure.*`
  (`RegularProlongationResidueIntegralClosure.lean`); `ord_algebraMap_base` is
  `AlgebraicCurve.Place.ord_algebraMap_base` (`P1/EnginePrelude.lean`); `ord_eq_zero_of_mem_of_inv_mem`
  is `AlgebraicCurve.ConstantFieldPlaceLift.ord_eq_zero_of_mem_of_inv_mem`
  (`Place/ConstantFieldExtension.lean`, same statement up to the binder names `k L` / `K F`, which is
  why `port_advise` did not pair it); `linearIndependent_pow_of_transcendental` is
  `AlgebraicCurve.linearIndependent_pow_of_transcendental` (`Genus/Stichtenoth.lean`); and the pin's
  `solution` row is the headline itself.
* **One substitution is *weaker* than the pin, and it is enough here.**
  `AlgebraicCurve.linearIndependent_pow_of_transcendental` is stated for `[CommRing A]` where the pin's
  `S_` row has `[Ring A]`.  Every use in this row's slice is at a field, so the substitution carries; it
  is recorded because a later consumer at a non-commutative `Ring` would have to transcribe the pin's
  row instead.
* **Substitutions rejected — the order's headline finding.** `port_advise` pairs nine of the pin's rows
  with `AlgebraicCurve.W7XL2.*` / `AlgebraicCurve.TorsionDescentDeriv.*` in
  `Genus/ConstantFieldExtension.lean` and reports them `byte-identical`: `liftPlace`, `liftPlace_spec`,
  `liftPlace_comap`, `ord_liftPlace`, `eq_liftPlace`, `liftPlace_injective`,
  `ord_algebraMap_eq_zero_of_forall_ne`, `constantsAreBase_of_isAlgClosed`,
  `exists_riemann_inequality`.  **All nine are `private` there** (`port_private: true` in the advise
  JSON, `port_public_count: 0`), so none of them is importable: they are **transcribed here** at the
  pin's names and *public*, which is what the pin's `S_` file does.  The order's table lists them as
  substitutions; they cannot be, and this is the one place the order does not hold.
* **Bodies that depart from the pin.** The nine transcribed rows keep the pin's statements *and* the
  pin's proof text where the port's private proof is reusable; the port's `TorsionDescentDeriv` proofs
  of `constantsAreBase_of_isAlgClosed` / `exists_riemann_inequality` go through the `private` `divOf`
  helper and are not reusable, so the pin's own route (`HasPrincipalDivisors.exists_divisor`, which the
  port has) is the one taken.  `mem_range_of_forall_ord_nonneg`,
  `exists_ord_neg_and_forall_ord_nonneg`, `dvd_ord_algebraMap`, `rebase`, `ord_rebase` and
  `exists_of_conorm` are the pin's text.
* **Adaptations forced by this mathlib (statements unmoved).**
  `Finsupp.mapDomain_apply` is `Finsupp.mapDomain_apply_of_injective` here, and
  `Finsupp.mapDomain_notin_range` is the deprecated alias of `Finsupp.mapDomain_of_notMem_range` —
  the new name is used so the module stays silent (FR-0319).  `isAlgClosed_residueField` is called
  qualified (`RegularProlongation.ResidueIntegralClosure.…`) because the pin's bare name relies on the
  `S_` file's own namespace.  `Module.finrank` is written out rather than `open Module`, and
  `open IsLocalRing` supplies `ResidueField` / `residue` / `maximalIdeal`.
* **`haveI`/`letI` are written `have`/`let` (18 sites).** The pin's `haveI`/`letI` are instance
  introductions inside `Prop` goals, which `linter.style.haveILetI` flags; per the set's house policy
  they are rewritten rather than silenced, and in this Lean a `have`/`let` whose type is a class is
  still a local instance for instance resolution.  **No linter is silenced in this module** — neither
  module-wide nor per declaration — and the module elaborates with no output at all at the edit loop's
  200 k cap.
* **Heartbeat probe pair, recorded and NOT installed.** The whole module is silent at
  `-DmaxHeartbeats=40000` and first fails at `20000`, on `exists_of_conorm` (`:284`), whose failure also
  produces the kernel's `unknown constant …exists_of_conorm` at the headline (`:513`).  Down the ladder
  the same declaration is the first over budget at `10000`; at `5000` its own `hφA` step
  (`obtain ⟨c₀, hc₀⟩ := hconstK a …`, `:344`) goes first, and at `1000` the pole lemma
  `mem_range_of_forall_ord_nonneg` (`:86`, inner `simp` at `:105`) goes too.  So no single subterm
  dominates: the conorm assembly — the residue-field change of base and the
  `exists_constantReduction` section — carries the top cost, the pole/divisor numerics the rest.  The
  module needs ≤ 40 k, five times under the edit loop's 200 k cap and a hundred under the lakefile's
  4 M.  No `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` is installed; the pin carries
  none either.
* **Gates measured on this module.** `check_port --force`: 16 `ok`, 0 mismatch, 0 missing, 0 own, 0 kw.
  Edit loop at `-DmaxHeartbeats=200000`: silent (no output at all).  Locked `lake build`: 0 warning
  lines naming this file.  `#print axioms` on all 16 public declarations: a subset of
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.  `dedup --within`: 0 duplicate clusters, 0
  removable lines.  `move_dead --dry-run`: 0 declarations, 0 lines.  Collision probe (this module plus
  the insertion's, imported together over the whole tree): silent — no public full name of this module
  exists elsewhere in the port.
-/

import FLTForHuman.AlgebraicCurve.ConstantReductionCorrespondence
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences
import FLTForHuman.AlgebraicCurve.Genus.PlaceReductionRiemannRoch
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.FromValuationSubring
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueIntegralClosure
import FLTForHuman.AlgebraicCurve.RegularProlongationRetraction
import FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

open AlgebraicCurve
open IsLocalRing

set_option autoImplicit false

namespace AlgebraicCurve

namespace DivisibilityDescent

/-! ## The place `rebase`

An order-compatible re-reading of a `Place K L` as a `Place k L` along a second base field `k → L`.  The
pin's `rebase`/`ord_rebase`; no other port module carries it, so it is transcribed. -/

/-- The same valuation subring, read against the smaller base field `k`. -/
def rebase {k K L : Type*} [Field k] [Field K] [Field L] [Algebra K L] [Algebra k L]
    (v : Place K L) (h : ∀ a : k, algebraMap k L a ∈ v.toValuationSubring) : Place k L where
  toValuationSubring := v.toValuationSubring
  algebraMap_mem' := h
  ne_top' := v.ne_top'
  isPrincipalIdealRing' := v.isPrincipalIdealRing'

/-- `rebase` keeps the order, definitionally. -/
theorem ord_rebase {k K L : Type*} [Field k] [Field K] [Field L] [Algebra K L] [Algebra k L]
    (v : Place K L) (h : ∀ a : k, algebraMap k L a ∈ v.toValuationSubring) (f : L) :
    (rebase v h).ord f = v.ord f := rfl

/-! ## The pole toolkit

`Pole` in the pin: a function whose order is non-negative everywhere is a constant, the constants are the
base field, Riemann's inequality `deg D + 1 - γ ≤ ell D`, and the existence of a function with a pole
exactly at one prescribed place. -/

section Pole

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A non-zero function with non-negative order everywhere is a constant. -/
theorem mem_range_of_forall_ord_nonneg [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    {f : F} (hf0 : f ≠ 0) (hord : ∀ v : Place K F, 0 ≤ v.ord f) :
    f ∈ (algebraMap K F).range := by
  classical
  obtain ⟨Df, hDf, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hzero : ∀ v : Place K F, v.ord f = 0 := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum] at hdeg
    have hnonneg : ∀ v ∈ Df.support,
        (0 : ℤ) ≤ (AddMonoidHom.mulRight (v.deg : ℤ)) (Df v) := by
      intro v _
      simp only [AddMonoidHom.coe_mulRight, IsCurveOver.deg_eq_one_of_isAlgClosed v,
        Nat.cast_one, mul_one, hDf]
      exact hord v
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hdeg
    intro v
    by_cases hv : v ∈ Df.support
    · have := hall v hv
      simpa [IsCurveOver.deg_eq_one_of_isAlgClosed v, hDf] using this
    · have : Df v = 0 := Finsupp.notMem_support_iff.mp hv
      rwa [hDf] at this
  exact Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hj hzero

/-- Over an algebraically closed field the constants are exactly the base field. -/
theorem constantsAreBase_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ConstantsAreBase K F := by
  refine le_antisymm ?_ ?_
  · intro f hf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact zero_mem _
    have hord : ∀ v : Place K F, 0 ≤ v.ord f := fun v => by
      simpa using ((mem_lSpace_iff_ord.mp hf).resolve_left hf0) v
    obtain ⟨c, hc⟩ := mem_range_of_forall_ord_nonneg j hj hf0 hord
    exact ⟨c, hc⟩
  · rintro _ ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c

/-- Riemann's inequality. -/
theorem exists_riemann_inequality [IsAlgClosed K] [IsCurveOver K F]
    (j : F) (hj : Transcendental K j)
    [hfd : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] :
    ∃ γ : ℤ, ∀ D : Divisor K F, Divisor.degree D + 1 - γ ≤ (ell D : ℤ) := by
  have : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hj hfd
  obtain ⟨γ, hγ⟩ :=
    exists_genus_riemannIndex_of_isCurveOver (K := K) (F := F) (constantsAreBase_of_isAlgClosed j hj)
  refine ⟨γ, fun D => ?_⟩
  have h := (hγ D).2
  have h0 : (0 : ℤ) ≤ (indexOfSpecialty D : ℤ) := Int.natCast_nonneg _
  linarith

/-- A function with a pole at `v` and nowhere else. -/
theorem exists_ord_neg_and_forall_ord_nonneg [IsAlgClosed K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (v : Place K F) :
    ∃ t : F, t ≠ 0 ∧ v.ord t < 0 ∧ ∀ w : Place K F, w ≠ v → 0 ≤ w.ord t := by
  classical
  obtain ⟨j, hj, hfd⟩ := hfg
  have := hfd
  obtain ⟨γ, hγ⟩ := exists_riemann_inequality (K := K) (F := F) j hj

  obtain ⟨m, hm⟩ : ∃ m : ℕ, γ + 1 ≤ (m : ℤ) := ⟨(γ + 1).toNat, Int.self_le_toNat _⟩
  have hell : (2 : ℤ) ≤ (ell (Finsupp.single v (m : ℤ) : Divisor K F) : ℤ) := by
    have h := hγ (Finsupp.single v (m : ℤ))
    rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed v, Nat.cast_one,
      mul_one] at h
    linarith

  have hnot : ¬ (LSpace (Finsupp.single v (m : ℤ) : Divisor K F) ≤
      LinearMap.range (Algebra.linearMap K F)) := by
    intro hle
    have h1 : Module.finrank K (LSpace (Finsupp.single v (m : ℤ) : Divisor K F)) ≤ 1 := by
      calc Module.finrank K (LSpace (Finsupp.single v (m : ℤ) : Divisor K F))
          ≤ Module.finrank K (LinearMap.range (Algebra.linearMap K F)) :=
            Submodule.finrank_mono hle
        _ = 1 := by
            rw [LinearMap.finrank_range_of_inj (f := Algebra.linearMap K F)
              (algebraMap K F).injective, Module.finrank_self]
    have : (ell (Finsupp.single v (m : ℤ) : Divisor K F) : ℤ) ≤ 1 := by exact_mod_cast h1
    linarith
  obtain ⟨t, htD, htc⟩ := SetLike.not_le_iff_exists.mp hnot
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htc (zero_mem _)
  have hordD := (mem_lSpace_iff_ord.mp htD).resolve_left ht0
  have hw : ∀ w : Place K F, w ≠ v → 0 ≤ w.ord t := fun w hwv => by
    have := hordD w
    rwa [Finsupp.single_eq_of_ne hwv, neg_zero] at this
  refine ⟨t, ht0, ?_, hw⟩
  by_contra hv
  push Not at hv
  have hall : ∀ w : Place K F, 0 ≤ w.ord t := fun w => by
    by_cases hwv : w = v
    · rw [hwv]; exact hv
    · exact hw w hwv
  obtain ⟨c, hc⟩ := mem_range_of_forall_ord_nonneg j hj ht0 hall
  exact htc ⟨c, hc⟩

end Pole

/-! ## The assembly

The pin's `Main` section: the lift of places along the constant extension, the divisibility transport, and
the conorm descent that produces the numerator. -/

section Main

variable {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']

section Lift

variable [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
  (hfg : ∃ x : F, Transcendental K x ∧
    FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
  (hfg' : ∃ x : F', Transcendental K' x ∧
    FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
  (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)

/-- The place of `F'` over `P`. -/
noncomputable def liftPlace (P : Place K F) : Place K' F' :=
  Classical.choose
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

theorem liftPlace_spec (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
        P.toValuationSubring ∧
      (∀ f : F, (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f) ∧
      ∀ Q' : Place K' F', Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring →
        Q' = liftPlace hfg hfg' hgen P :=
  Classical.choose_spec
    (AlgebraicCurve.Place.exists_comap_algebraMap_eq_of_constantFieldExtension
      K F K' F' hfg hfg' hgen P)

theorem liftPlace_comap (P : Place K F) :
    (liftPlace hfg hfg' hgen P).toValuationSubring.comap (algebraMap F F') =
      P.toValuationSubring :=
  (liftPlace_spec hfg hfg' hgen P).1

theorem ord_liftPlace (P : Place K F) (f : F) :
    (liftPlace hfg hfg' hgen P).ord (algebraMap F F' f) = P.ord f :=
  (liftPlace_spec hfg hfg' hgen P).2.1 f

theorem eq_liftPlace {P : Place K F} {Q' : Place K' F'}
    (h : Q'.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring) :
    Q' = liftPlace hfg hfg' hgen P :=
  (liftPlace_spec hfg hfg' hgen P).2.2 Q' h

theorem liftPlace_injective :
    Function.Injective (liftPlace (K := K) (F := F) (K' := K') (F' := F') hfg hfg' hgen) := by
  intro P Q h
  apply Place.ext
  rw [← liftPlace_comap hfg hfg' hgen P, h, liftPlace_comap]

theorem ord_algebraMap_eq_zero_of_forall_ne (w : Place K' F')
    (hw : ∀ P : Place K F, w ≠ liftPlace hfg hfg' hgen P) (f : F) :
    w.ord (algebraMap F F' f) = 0 := by
  by_contra hne
  obtain ⟨x, hx, hfin⟩ := id hfg
  have := hfin
  have hwK : ∀ a : K, algebraMap F F' (algebraMap K F a) ∈ w.toValuationSubring := fun a => by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K K' F']
    exact w.algebraMap_mem' _
  have hwx : ∃ y : F, algebraMap F F' y ∉ w.toValuationSubring := by
    by_contra hall
    push Not at hall
    exact hne (ConstantFieldPlaceLift.ord_eq_zero_of_mem_of_inv_mem w (hall f)
      (by rw [← map_inv₀]; exact hall _))
  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom
    (K := K) x (algebraMap F F') w.toValuationSubring hwK hwx
  exact hw v (eq_liftPlace hfg hfg' hgen hv.symm)

end Lift

/-- Divisibility of the order transports along the constant extension. -/
theorem dvd_ord_algebraMap [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    {n : ℤ} {g : F} (hg : ∀ v : Place K F, n ∣ v.ord g)
    (v' : Place K' F') : n ∣ v'.ord (algebraMap F F' g) := by
  by_cases hv : ∃ v : Place K F, v' = liftPlace hfg hfg' hgen v
  · obtain ⟨v, rfl⟩ := hv
    rw [ord_liftPlace]
    exact hg v
  · push Not at hv
    rw [ord_algebraMap_eq_zero_of_forall_ne hfg hfg' hgen v' hv]
    exact dvd_zero _

/-- The conorm descent: a solution on the extension produces one on the base. -/
theorem exists_of_conorm [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (_hn : n ≠ 0) (D : Divisor K F) (D' : Divisor K' F')
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        D' v' = 0)
    (f' : F') (hf'0 : f' ≠ 0) (hdiv' : ∀ v' : Place K' F', (n : ℤ) ∣ v'.ord f' - D' v') :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) ∣ v.ord f - D v := by
  classical
  have : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  obtain ⟨x₀, hx₀, hfin₀⟩ := id hfg

  obtain ⟨O, ρ, hρF, hker, hreg, hconstK⟩ :=
    AlgebraicCurve.exists_constantReduction_of_constantFieldExtension K F K' F' hfg hfg' hgen
  have hFO : ∀ f : F, algebraMap F F' f ∈ O := fun f => by
    obtain ⟨h, -⟩ := hρF f; exact h
  have hρF' : ∀ (f : F) (h : algebraMap F F' f ∈ O), ρ ⟨algebraMap F F' f, h⟩ = f := fun f h => by
    obtain ⟨h', e⟩ := hρF f; exact e
  have hsurj : Function.Surjective ρ := fun f => ⟨_, hρF' f (hFO f)⟩
  have hres_unit : ∀ y : O, IsUnit y → ρ y ≠ 0 := fun y hy h0 => by
    have hmem : y ∈ RingHom.ker ρ := RingHom.mem_ker.mpr h0
    rw [hker] at hmem
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hy
  have hunit : ∀ y : O, ρ y ≠ 0 → IsUnit y := fun y hy => by
    by_contra h
    have hmem : y ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr h
    rw [← hker] at hmem
    exact hy (RingHom.mem_ker.mp hmem)

  set A' : ValuationSubring K' := O.comap (algebraMap K' F') with hA'
  have hOA : ∀ c : K', algebraMap K' F' c ∈ O ↔ c ∈ A' := fun c => Iff.rfl
  let ι : A' →+* O :=
    ((algebraMap K' F').comp A'.subtype).codRestrict O (fun a => (hOA a).mpr a.2)
  let ρA : A' →+* F := ρ.comp ι
  have hmax : ∀ a : A', ρA a = 0 → a ∈ IsLocalRing.maximalIdeal A' := fun a ha => by
    by_contra hna
    have hu : IsUnit a := by
      by_contra hnu
      exact hna ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    exact hres_unit (ι a) (hu.map ι) ha
  have hKA : ∀ c : K, algebraMap K K' c ∈ A' := fun c => by
    show algebraMap K' F' (algebraMap K K' c) ∈ O
    rw [← IsScalarTower.algebraMap_apply K K' F' c, IsScalarTower.algebraMap_apply K F F' c]
    exact hFO _
  let ιK : K →+* A' := (algebraMap K K').codRestrict A' hKA
  have hρK : ∀ c : K, ρA (ιK c) = algebraMap K F c := fun c => by
    have : (ι (ιK c) : O) = ⟨algebraMap F F' (algebraMap K F c), hFO _⟩ := Subtype.ext (by
      show algebraMap K' F' (algebraMap K K' c) = algebraMap F F' (algebraMap K F c)
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])
    show ρ (ι (ιK c)) = _
    rw [this, hρF']
  have hφA : ∀ a : A', ∃ c₀ : K, algebraMap K F c₀ = ρA a ∧
      IsLocalRing.residue A' a = IsLocalRing.residue A' (ιK c₀) := fun a => by
    obtain ⟨c₀, hc₀⟩ := hconstK a ((hOA a).mpr a.2)
    refine ⟨c₀, hc₀, ?_⟩
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    refine hmax _ ?_
    rw [map_sub, hρK, sub_eq_zero]
    exact hc₀.symm
  let φ : K →+* ResidueField A' := (IsLocalRing.residue A').comp ιK
  have hφ : Function.Bijective φ := by
    refine ⟨φ.injective, fun r => ?_⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨c₀, -, hc₀⟩ := hφA a
    exact ⟨c₀, hc₀.symm⟩
  let e : K ≃+* ResidueField A' := RingEquiv.ofBijective φ hφ

  let iK : Algebra (ResidueField A') K := e.symm.toRingHom.toAlgebra
  let iF : Algebra (ResidueField A') F := ((algebraMap K F).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower (ResidueField A') K F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let iK' : Algebra (ResidueField A') K' := ((algebraMap K K').comp e.symm.toRingHom).toAlgebra
  let iF' : Algebra (ResidueField A') F' := ((algebraMap K F').comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower (ResidueField A') K' F' :=
    IsScalarTower.of_algebraMap_eq (fun c => IsScalarTower.algebraMap_apply K K' F' (e.symm c))
  have : IsScalarTower (ResidueField A') F F' :=
    IsScalarTower.of_algebraMap_eq (fun c => IsScalarTower.algebraMap_apply K F F' (e.symm c))
  have hconst : ∀ a : A', ρ ⟨algebraMap K' F' a, (hOA a).mpr a.2⟩ =
      algebraMap (ResidueField A') F (IsLocalRing.residue A' a) := fun a => by
    obtain ⟨c₀, hc₀, hres⟩ := hφA a
    have h1 : IsLocalRing.residue A' a = e c₀ := hres
    show ρA a = algebraMap K F (e.symm (IsLocalRing.residue A' a))
    rw [h1, RingEquiv.symm_apply_apply, hc₀]
  have : IsAlgClosed (ResidueField A') :=
    RegularProlongation.ResidueIntegralClosure.isAlgClosed_residueField
  have : CharZero (ResidueField A') := e.symm.toRingHom.charZero
  have hkK : Function.Surjective (algebraMap (ResidueField A') K) := e.symm.surjective
  obtain ⟨hx₀k, hfink, hfinrk⟩ :=
    PlaceReductionRiemannRoch.LowerSemicontinuity.transfer_fg hkK hx₀ hfin₀
  have : IsCurveOver (ResidueField A') F := by
    have := hfink
    have : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
    have : CharZero (IntermediateField.adjoin (ResidueField A') ({x₀} : Set F)) :=
      (algebraMap (IntermediateField.adjoin (ResidueField A') ({x₀} : Set F)) F).charZero
    exact AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable (ResidueField A') F x₀
      hx₀k hfink inferInstance
  have hfgk : ∃ x : F, Transcendental (ResidueField A') x ∧
      FiniteDimensional (IntermediateField.adjoin (ResidueField A') ({x} : Set F)) F :=
    ⟨x₀, hx₀k, hfink⟩

  have hgood : genusFF (ResidueField A') F = genusFF K' F' :=
    (AlgebraicCurve.genusFF_eq_of_constantFieldExtension_of_isAlgClosed (ResidueField A') F K' F'
      hfgk hfg' hgen).symm

  have hreg' : ∃ x : O, Transcendental (ResidueField A') (ρ x) ∧
      0 < Module.finrank (IntermediateField.adjoin (ResidueField A') ({ρ x} : Set F)) F ∧
      Module.finrank (IntermediateField.adjoin K' ({(x : F')} : Set F')) F' =
        Module.finrank (IntermediateField.adjoin (ResidueField A') ({ρ x} : Set F)) F := by
    refine ⟨⟨algebraMap F F' x₀, hFO x₀⟩, ?_, ?_, ?_⟩
    · rw [hρF']; exact hx₀k
    · rw [hρF']; have := hfink; exact Module.finrank_pos
    · rw [hρF']
      show Module.finrank (IntermediateField.adjoin K' ({algebraMap F F' x₀} : Set F')) F' = _
      rw [PlaceReductionRiemannRoch.LowerSemicontinuity.finrank_adjoin_algebraMap_eq
        hfg hfg' hgen hx₀ hfin₀, hfinrk]

  obtain ⟨r, hr⟩ :=
    AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
      A' O ρ hOA hsurj hker hconst hreg hreg' hgood

  let rb : Place K F → Place (ResidueField A') F := fun v =>
    rebase v (fun a => v.algebraMap_mem' (e.symm a))
  have hrb_inj : Function.Injective rb := fun v w h => by
    apply Place.ext
    have h' := congrArg Place.toValuationSubring h
    exact h'

  have hcon : ∀ (t : F) (Dt : Divisor K' F') (Dt₀ : Divisor K F),
      (∀ v', Dt v' = v'.ord (algebraMap F F' t)) → (∀ w, Dt₀ w = w.ord t) →
        Dt = Finsupp.mapDomain (liftPlace hfg hfg' hgen) Dt₀ := by
    intro t Dt Dt₀ hDt hDt₀
    ext v'
    rw [hDt]
    by_cases hv : ∃ w, v' = liftPlace hfg hfg' hgen w
    · obtain ⟨w, rfl⟩ := hv
      rw [Finsupp.mapDomain_apply_of_injective (liftPlace_injective hfg hfg' hgen), hDt₀,
        ord_liftPlace]
    · push Not at hv
      rw [Finsupp.mapDomain_of_notMem_range _ _ (fun ⟨w, hw⟩ => hv w hw.symm),
        ord_algebraMap_eq_zero_of_forall_ne hfg hfg' hgen v' hv]
  have hsec : ∀ v : Place K F, r (liftPlace hfg hfg' hgen v) = rb v := by
    intro v
    obtain ⟨t, ht0, htv, htw⟩ :=
      exists_ord_neg_and_forall_ord_nonneg (K := K) (F := F) hfg v
    have halgt : algebraMap F F' t ≠ 0 := (map_ne_zero _).mpr ht0
    obtain ⟨Dt, hDt, -⟩ := HasPrincipalDivisors.exists_divisor (K := K') (algebraMap F F' t) halgt
    obtain ⟨Dt₀, hDt₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) t ht0
    have hrest : ρ ⟨algebraMap F F' t, hFO t⟩ ≠ 0 := by rw [hρF']; exact ht0
    have hrt := hr ⟨algebraMap F F' t, hFO t⟩ hrest Dt hDt (rb v)
    rw [hρF', hcon t Dt Dt₀ hDt hDt₀, ← Finsupp.mapDomain_comp] at hrt
    by_contra hne
    have hlhs : 0 ≤ Finsupp.mapDomain (r ∘ liftPlace hfg hfg' hgen) Dt₀ (rb v) := by
      rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
      refine Finset.sum_nonneg fun w _ => ?_
      rw [Finsupp.single_apply]
      split_ifs with h
      · have hwv : w ≠ v := by
          rintro rfl
          exact hne h
        rw [hDt₀]
        exact htw w hwv
      · exact le_refl _
    rw [hrt] at hlhs
    have : (rb v).ord t = v.ord t := rfl
    rw [this] at hlhs
    exact absurd htv (not_lt.mpr hlhs)
  have hcomp : r ∘ liftPlace hfg hfg' hgen = rb := funext fun v => hsec v

  have hD'eq : D' = Finsupp.mapDomain (liftPlace hfg hfg' hgen) D := by
    ext v'
    by_cases hv : ∃ v, v' = liftPlace hfg hfg' hgen v
    · obtain ⟨v, rfl⟩ := hv
      rw [Finsupp.mapDomain_apply_of_injective (liftPlace_injective hfg hfg' hgen),
        hD'over _ v (liftPlace_comap hfg hfg' hgen v)]
    · push Not at hv
      rw [Finsupp.mapDomain_of_notMem_range _ _ (fun ⟨w, hw⟩ => hv w hw.symm)]
      exact hD'off v' fun v h => hv v (eq_liftPlace hfg hfg' hgen h)

  obtain ⟨c, hcO, hcres⟩ := hreg f' hf'0
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hcres
    have : (⟨(0 : K') • f', hcO⟩ : O) = 0 := Subtype.ext (by simp)
    rw [this, map_zero]
  have hc' : algebraMap K' F' c ≠ 0 := (map_ne_zero _).mpr hc0
  set u : O := ⟨c • f', hcO⟩ with hu_def
  have hu0 : (u : F') ≠ 0 := smul_ne_zero hc0 hf'0
  have hu_ord : ∀ v' : Place K' F', v'.ord (u : F') = v'.ord f' := fun v' => by
    show v'.ord (c • f') = _
    rw [Algebra.smul_def, Place.ord_mul _ hc' hf'0, Place.ord_algebraMap_base, zero_add]
  set f : F := ρ u with hf_def
  have hf0 : f ≠ 0 := hcres

  obtain ⟨Du, hDu, -⟩ := HasPrincipalDivisors.exists_divisor (K := K') (u : F') hu0
  let E' : Divisor K' F' :=
    Finsupp.mapRange (fun z => z / (n : ℤ)) (Int.zero_ediv _) (Du - D')
  have hE' : Du = D' + (n : ℤ) • E' := by
    ext v'
    have hdvd : (n : ℤ) ∣ (Du - D') v' := by
      rw [Finsupp.sub_apply, hDu, hu_ord]
      exact hdiv' v'
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, E', Finsupp.mapRange_apply]
    rw [Int.mul_ediv_cancel' hdvd, Finsupp.sub_apply]
    ring

  have hru := hr u hcres Du hDu
  refine ⟨f, hf0, fun v => ⟨Finsupp.mapDomain r E' (rb v), ?_⟩⟩
  have h := hru (rb v)
  rw [hE', Finsupp.mapDomain_add, Finsupp.mapDomain_smul, hD'eq, ← Finsupp.mapDomain_comp, hcomp,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.mapDomain_apply_of_injective hrb_inj] at h
  have hrbo : (rb v).ord (ρ u) = v.ord f := rfl
  rw [hrbo] at h
  linarith

end Main

end DivisibilityDescent

end AlgebraicCurve

/-! ## The row -/

theorem AlgebraicCurve.Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [CharZero K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (n : ℕ) (hn : n ≠ 0) (D : Divisor K F) (D' : Divisor K' F')
    (hD'over : ∀ (v' : Place K' F') (v : Place K F),
      v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring → D' v' = D v)
    (hD'off : ∀ v' : Place K' F',
      (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
        D' v' = 0)
    (hdiv' : ∃ f' : F', f' ≠ 0 ∧ ∀ v' : Place K' F', (n : ℤ) ∣ v'.ord f' - D' v') :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, (n : ℤ) ∣ v.ord f - D v := by
  obtain ⟨f', hf'0, hdiv'⟩ := hdiv'
  exact AlgebraicCurve.DivisibilityDescent.exists_of_conorm hfg hfg' hgen n hn D D' hD'over hD'off
    f' hf'0 hdiv'
