/-
The valued field: transcendence degree, residue field and normal forms over a valuation ring.

Five rows of the general valued-field toolbox that the `j`-integrality and good-reduction arguments
use:

* `ringKrullDim_le_ringKrullDim_comap_add_trdeg` — `dim A ≤ dim (A.comap K) + trdeg K L` for a
  valuation subring `A` of `L`;
* `exists_smul_mem_of_transcendental_residue` — a transcendental residue yields a scaling of a
  nonzero `h` into the valuation ring;
* `natDegree_map_eq_card_roots_of_splits` — for a polynomial over `A` whose reduction is nonzero and
  whose base change splits, `natDegree` of the reduction equals the number of roots;
* `tensorProduct_exists_primitive_factor` — a primitive element for the tensor product `F ⊗[K] A`
  when `A` is a valuation ring over `K` with a section;
* `exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero` — every nonzero `q₁/L` is `C c⁻¹` times
  the image of a polynomial over `A` whose reduction is nonzero.

All five are `Mathlib`-only (the `ValuationSubring` API, `ringKrullDim`, `Algebra.trdeg`,
`Module.Finite`, `IsLocalRing.ResidueField`); none needs a pin `Definitions` module.  They are the
statement layer under `AlgebraicCurve/Place/*` and `ModularCurve/X1/*` and were the `ValuationSubring`
leaves of the D–S shelf.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ValuationSubring_exists_smul_mem_of_transcendental_residue.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ValuationSubring_natDegree_map_eq_card_roots_of_splits.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ValuationSubring_tensorProduct_exists_primitive_factor.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero.lean>

spec-pin: Theorems/Thm_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg.lean
spec-pin: Theorems/Thm_ValuationSubring_exists_smul_mem_of_transcendental_residue.lean
spec-pin: Theorems/Thm_ValuationSubring_natDegree_map_eq_card_roots_of_splits.lean
spec-pin: Theorems/Thm_ValuationSubring_tensorProduct_exists_primitive_factor.lean
spec-pin: Theorems/Thm_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero.lean
spec-pin: P2M/Sol/S_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg.lean
spec-pin: P2M/Sol/S_ValuationSubring_exists_smul_mem_of_transcendental_residue.lean
spec-pin: P2M/Sol/S_ValuationSubring_natDegree_map_eq_card_roots_of_splits.lean
spec-pin: P2M/Sol/S_ValuationSubring_tensorProduct_exists_primitive_factor.lean
spec-pin: P2M/Sol/S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero.lean

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.lean>
spec-pin: Theorems/Thm_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.lean
spec-pin: P2M/Sol/S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.lean

**Landing (AF103E).**  All five rows transcribed in full: **29 public declarations**, 0 private, one
declaration per pin row.  Names are the pin's, except for the three generated namespace labels, which
come off in favour of subject namespaces — `ValuationSubring.KrullDimTranscendence` (row 269's
Krull-dimension-vs-transcendence-degree engine), `ValuationSubring.TranscendentalResidue` (row 262's
residue-field engine) and `ValuationSubring.RootCount` (row 174's root count) — and the five `solution`
rows, which are this module's five headlines at the wrappers' published names.  (The neighbouring
`ValuationSubring*` modules still carry `ZfSol`/`E1Sol`/`W7XK3A`; that is legacy debt there, not the
rule for a new module: no pipeline token in a name.)

Engine gate — the pin-vs-module declaration diff over the module's ten `spec-pin:` files (five
wrappers + five `S_` files, so 34 pin rows of which 29 are `S_` rows):

* pin `S_` rows `11 + 10 + 6 + 1 + 1 = 29`; module public declarations **29**;
* **24 exact** last-name matches + **5** headline↔`solution` pairs (the published wrapper name
  replaces the pin's `solution`, as in every landed row of the port): **29 / 29, 0 missing, 0 extra**.
  The harness reports `28 by hash, 1 by name (hash differs), 0 unaccounted`; the name-match is
  `tensorProduct_exists_primitive_factor`, whose statement carries one renamed dead binder (below).

Other gates: `check_port` **29 ok / 0 mismatch / 0 missing / 0 own / 0 kw**; `#print axioms` on all
29 public declarations gives `[propext, Classical.choice, Quot.sound]` and no `sorryAx`;
`dedup.py --within` **0 duplicate clusters**; `move_dead.py --dry-run` **0 declarations, 0 lines**;
the module's own `lake env lean` and its locked `lake build` print no warning line.

Mathlib modules added: **one** — `Mathlib.RingTheory.Polynomial.Subring`, for row 57's
`Polynomial.toSubring` / `Polynomial.map_toSubring`, which the scaffold's list reached only
transitively.  Everything else the five rows use is already covered by the scaffold's twelve imports:
`ValuationSubring.{valuation, valuation_le_one_iff, valuation_eq_one_iff, mem_or_inv_mem, zero_mem,
subtype, ofPrime, le_ofPrime, ofPrime_valuation_eq_one_iff_mem_primeCompl, mapOfLE_valuation_apply}`,
`Valuation.map_sum_lt`/`map_add_eq_of_lt_left`/`ne_zero_iff`, `ringKrullDim` with `Order.krullDim`
and `RelSeries`/`LTSeries` (`Order.LTSeries.length_le_krullDim`), `AlgebraicIndependent` +
`lift_cardinalMk_le_trdeg`, `Transcendental`, `IntermediateField.mem_adjoin_simple_iff`,
`Module.Basis.ofVectorSpace`, `TensorProduct.finsuppScalarLeft`, `ValuationRing.dvd_total`,
`IsLocalRing.mem_maximalIdeal`/`mem_nonunits_iff`.  Neither of the two module names that do not exist
in this toolchain (`Mathlib.FieldTheory.Transcendental.Basic`,
`Mathlib.RingTheory.KrullDimension.ValuationSubring`) is needed.

Drift (mathlib `v4.34.0` against the pin's `v4.33.0`), statements frozen, proofs adapted:

* `tensorProduct_exists_primitive_factor`: `Algebra.TensorProduct.lift`'s commutativity binder is
  `∀ x y, Commute (f x) (g y)`, and `Commute` is a semireducible `def` — a tactic that rebuilds the
  goal at `implicit` transparency cannot read the pin's `(fun f a ↦ mul_comm _ _)` as a `Commute`
  proof, so the pin's closing `simp only […, lift_tmul, …]` no longer fires (it silently leaves the
  `⊗ₜ` folded).  The tensor-product computation is factored out once, at default transparency, as
  `hΨtmul` and never unfolded again.  Deprecated `LinearEquiv.rTensor_symm_tmul` →
  `LinearEquiv.symm_rTensor` + `LinearEquiv.rTensor_tmul`.
* `tensorProduct_exists_primitive_factor` has dead binders.  The `Ψ`-line's `f`/`a` are part of the
  wire statement and cannot be `_`-prefixed (that is a `check_port` MISMATCH), so the declaration
  carries `set_option linter.unusedVariables false in` — the pin is silent only because
  `P2M/Util.lean` turns the linter off globally; the hypothesis is `_hker`-prefixed as usual
  (`alpha_stmt` accepts it; it is the one name-match above).
* `natDegree_map_eq_card_roots_of_splits`: inside `namespace ValuationSubring`, `mem_nonunits_iff`
  resolves to `ValuationSubring.mem_nonunits_iff` (a different, valuation-valued statement), so the
  engine spells `_root_.mem_nonunits_iff`.
* `ringKrullDim_le_ringKrullDim_comap_add_trdeg`: deprecated `pow_lt_one₀ (zero_le')` →
  `pow_lt_one₀ zero_le`.
* `exists_smul_mem_of_transcendental_residue`'s proof opens by restating the statement's `letI`
  (`Algebra K A`), which instance search needs; `set_option linter.style.haveILetI false` at module
  level lets the pin's `letI` stand verbatim.

**Heartbeat probe** (FR-0225, recorded and **never installed**): on a scratch copy of the whole module
(`tmp/af103/probe-E-heartbeat.lean`, one extra `set_option maxHeartbeats` line) the pair is **silent
at `20000`** and **deterministic timeout at `15000`**, at `RootCount.main`'s roots bookkeeping
(`have hroots : p.roots = q.roots`, `have hc' := ((mem_roots hlin0).mp hc)`, `have hsplit₁ :
Multiset.card (q.map (algebraMap A E)).roots = q.natDegree`) and at the
`tensorProduct_exists_primitive_factor` header.  No `set_option maxHeartbeats` is installed.

**Landing (AF107H) — the `ℚ`-scale dimension row.**  A sixth row joins the five above:
`ringKrullDim_le_toENat_trdeg_rat_add_one`, `ringKrullDim A ≤ toENat (trdeg ℚ L) + 1` for a valuation
subring `A` of a `ℚ`-algebra field.  Its one premise is the module's own
`ringKrullDim_le_ringKrullDim_comap_add_trdeg`, so the row is placed immediately **below** that
premise (adjacency is after, not before: Lean has no forward references — the order's "right above its
premise" is read as "in the premise's own section").  The pin's generated `AbhRatSol` label comes off
for `ValuationSubring.KrullDimRat`, and its six helper rows there (`unitInts`, `mem_unitInts`,
`unitInts_le_nonZeroDivisors`, `isUnit_den`, `isLocalization`, `ringKrullDim_le_one`) are transcribed
at those same names and are `private` — the pin has them public, the house default is `private`, and
the surface probe below shows they promote cleanly.  No `WithBot ℕ∞` cast helper was needed: the pin's
`calc` closes with `add_le_add` and `add_comm` as written.

* Engine gate over the same twelve `spec-pin:` files (the five wrappers, the five `S_` files, and the
  new row's wrapper + `S_` pair): pin decls **41**, module decls **35** (30 public + 5 parsed private
  — the `scoped instance isLocalization` is not a parsed row), **34 by hash**, **1 by name (hash
  differs)** — the pre-existing `tensorProduct_exists_primitive_factor` — **0 unaccounted**.  The new
  row and all five of its parsed private helpers match **by hash**.
* `check_port` **30 ok / 0 mismatch / 0 missing / 0 own / 0 kw** — 29 before this row, the order's 30.
* **Surface probe** (`tmp/af107/probe-surface-VSF.lean`, the module with `private` dropped from the
  five new helpers): **35 ok / 0 mismatch / 0 missing / 0 own**.  All five are pin rows; promotion is
  the manager's call.
* `#print axioms` on all **30** public declarations: `[propext, Classical.choice, Quot.sound]`, no
  `sorryAx` (`tmp/af107/ax-vsf.out`).
* `dedup --within --module '*FieldTheory/ValuationSubringValuedField*'`: **0 duplicate clusters**;
  `move_dead --dry-run`: **0 declarations, 0 lines**.
* Heartbeat probe pair (measured, **never installed**): the module is **silent at
  `-DmaxHeartbeats=20000`** and **first fails at `15000`**, again at `RootCount.main`'s roots
  bookkeeping (lines 875, 879, 889) and the `tensorProduct_exists_primitive_factor` header (919) — the
  same pair AF103E recorded, so the new row is not the module's tightest declaration.  5000 fails with
  63 lines, 1000 with 182.  No `set_option maxHeartbeats` is installed.
* Drift (mathlib `v4.34.0` against the pin's `v4.33.0`), statements frozen, proof adapted: the pin's
  `B.intCast_mem u` is `v4.34`'s `SubringClass`-generic root lemma `intCast_mem`
  (`Subring.intCast_mem` no longer exists), so it is written `intCast_mem B u`; `isLocalization_iff`
  and the `Rat`/`Int` denominator-coprimality API are unchanged.

Set-level note: `tmp/af103/collision-probe.lean` (the FR-0274 probe over all five AF103 modules)
cannot be run from this order yet — the other four modules' `.olean`s are not built, so the probe
stops at `object file … EquivariantTorsion.olean does not exist`.  The three namespaces above and the
five headline names occur in no other module of `FLTForHuman/` (`rg` over the tree).
-/
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.ExtendToLocalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.Tactic

set_option autoImplicit false

-- `tensorProduct_exists_primitive_factor` opens its proof by restating the statement's `letI` (the
-- `Algebra K A` instance built from the section `σ`): that instance is load-bearing — it feeds every
-- `⊗ₜ[K]`, `LinearEquiv.rTensor` and `Module.Basis` below — so the pin's `letI` is kept as written.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial IsLocalRing

namespace ValuationSubring

/- The dimension inequality `dim A ≤ dim (A.comap K) + trdeg K L` for a valuation subring `A` of `L`:
the engine is a lifting of a strict chain of primes of `A` to a chain of `A.comap (algebraMap K L)`
plus a `ValIndep` family, which is algebraically independent and so bounded by the transcendence
degree.  (The pin's generated `AbhSol` label is dropped: subject namespace.) -/
namespace KrullDimTranscendence

section General

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

lemma zpow_eq_one_imp {γ : Γ₀} (h1 : γ < 1) {m : ℤ} (hm : γ ^ m = 1) : m = 0 := by
  have key : ∀ n : ℕ, γ ^ (n : ℤ) = 1 → n = 0 := by
    intro n hn
    by_contra hne
    rw [zpow_natCast] at hn
    exact absurd hn (pow_lt_one₀ zero_le h1 hne).ne
  rcases le_or_gt 0 m with hpos | hneg
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    have := key n hm
    simp [this]
  · have hm' : γ ^ (-m) = 1 := by rw [zpow_neg, hm, inv_one]
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hneg.le)
    rw [hn] at hm'
    have := key n hm'
    omega

lemma exists_ne_map_eq_of_sum_eq_zero {R : Type*} [CommRing R] (v : Valuation R Γ₀)
    {ι : Type*} (s : Finset ι) (t : ι → R) (hs : s.Nonempty) (ht : ∀ i ∈ s, v (t i) ≠ 0)
    (hsum : ∑ i ∈ s, t i = 0) : ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ v (t i) = v (t j) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀, hmax⟩ := s.exists_max_image (fun i => v (t i)) hs
  have hlt : ∀ j ∈ s.erase i₀, v (t j) < v (t i₀) := by
    intro j hj
    obtain ⟨hji, hjs⟩ := Finset.mem_erase.mp hj
    exact lt_of_le_of_ne (hmax j hjs) (hcon j hjs i₀ hi₀ hji)
  have hrest : v (∑ j ∈ s.erase i₀, t j) < v (t i₀) := v.map_sum_lt (ht i₀ hi₀) hlt
  have hsplit : ∑ i ∈ s, t i = t i₀ + ∑ j ∈ s.erase i₀, t j := (Finset.add_sum_erase s t hi₀).symm
  have h : v (∑ i ∈ s, t i) = v (t i₀) := by rw [hsplit, v.map_add_eq_of_lt_left hrest]
  rw [hsum, map_zero] at h
  exact ht i₀ hi₀ h.symm

end General

section Main

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

def resHom : A.comap (algebraMap K L) →+* A :=
  (algebraMap K L).restrict (A.comap (algebraMap K L)).toSubring A.toSubring (fun _ hx => hx)

@[scoped simp] lemma coe_resHom_apply (c : A.comap (algebraMap K L)) :
    ((resHom K A c : A) : L) = algebraMap K L c := rfl

def ValIndep {b : ℕ} (x : Fin b → L) : Prop :=
  ∀ (c : K) (m : Fin b → ℤ), A.valuation (algebraMap K L c * ∏ k, x k ^ m k) = 1 → m = 0

variable {K A}

lemma valuation_eq_one_of_le {S : ValuationSubring L} (h : A ≤ S) {y : L}
    (hy : A.valuation y = 1) : S.valuation y = 1 := by
  rw [← mapOfLE_valuation_apply A S h, hy, map_one]

lemma dagger {P Q : Ideal A} [P.IsPrime] [Q.IsPrime]
    (hinv : Ideal.comap (resHom K A) P = Ideal.comap (resHom K A) Q) (c : K)
    (h0 : (ofPrime A P).valuation (algebraMap K L c) = 1) :
    (ofPrime A Q).valuation (algebraMap K L c) = 1 := by
  have key : ∀ c : K, ∀ hc : algebraMap K L c ∈ A,
      (ofPrime A P).valuation (algebraMap K L c) = 1 →
      (ofPrime A Q).valuation (algebraMap K L c) = 1 := by
    intro c hc hP
    have hP' : (⟨algebraMap K L c, hc⟩ : A) ∈ P.primeCompl :=
      (ofPrime_valuation_eq_one_iff_mem_primeCompl A P ⟨_, hc⟩).mp hP
    have hQ' : (⟨algebraMap K L c, hc⟩ : A) ∈ Q.primeCompl := by
      rw [Ideal.mem_primeCompl_iff] at hP' ⊢
      intro hQ
      apply hP'
      have h1 : (⟨c, hc⟩ : A.comap (algebraMap K L)) ∈ Ideal.comap (resHom K A) Q := hQ
      rw [← hinv] at h1
      exact h1
    exact (ofPrime_valuation_eq_one_iff_mem_primeCompl A Q ⟨_, hc⟩).mpr hQ'
  rcases A.mem_or_inv_mem (algebraMap K L c) with hc | hc
  · exact key c hc h0
  · have hc' : algebraMap K L c⁻¹ ∈ A := by rwa [map_inv₀]
    have h0' : (ofPrime A P).valuation (algebraMap K L c⁻¹) = 1 := by
      rw [map_inv₀, map_inv₀, h0, inv_one]
    have h1 := key c⁻¹ hc' h0'
    rwa [map_inv₀, map_inv₀, inv_eq_one] at h1

lemma valIndep_cons {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q)
    (hinv : Ideal.comap (resHom K A) P = Ideal.comap (resHom K A) Q)
    (f : A) (hfQ : f ∈ Q) (hfP : f ∉ P) {b : ℕ} (x : Fin b → A) (hx : ∀ k, x k ∉ Q)
    (hVI : ValIndep K A (fun k => (x k : L))) :
    ValIndep K A (Fin.cons (f : L) (fun k => (x k : L)) : Fin (b + 1) → L) := by
  intro c m hm
  set O₀ := ofPrime A P
  set O₁ := ofPrime A Q
  have hA0 : A ≤ O₀ := le_ofPrime A P
  have hA1 : A ≤ O₁ := le_ofPrime A Q
  rw [Fin.prod_univ_succ] at hm
  simp only [Fin.cons_zero, Fin.cons_succ] at hm
  have hf0 : O₀.valuation (f : L) = 1 :=
    (ofPrime_valuation_eq_one_iff_mem_primeCompl A P f).mpr hfP
  have hx0 : ∀ k, O₀.valuation (x k : L) = 1 := fun k =>
    (ofPrime_valuation_eq_one_iff_mem_primeCompl A P (x k)).mpr (fun h => hx k (hPQ h))
  have hx1 : ∀ k, O₁.valuation (x k : L) = 1 := fun k =>
    (ofPrime_valuation_eq_one_iff_mem_primeCompl A Q (x k)).mpr (hx k)
  have hf1 : O₁.valuation (f : L) < 1 := by
    have hle : O₁.valuation (f : L) ≤ 1 := (O₁.valuation_le_one_iff _).mpr (hA1 f.2)
    have hne : O₁.valuation (f : L) ≠ 1 := fun h =>
      (Ideal.mem_primeCompl_iff.mp
        ((ofPrime_valuation_eq_one_iff_mem_primeCompl A Q f).mp h)) hfQ
    exact lt_of_le_of_ne hle hne

  have h0 : O₀.valuation (algebraMap K L c) = 1 := by
    have h := valuation_eq_one_of_le hA0 hm
    rw [map_mul, map_mul, map_prod, map_zpow₀, hf0, one_zpow, one_mul] at h
    simp_rw [map_zpow₀, hx0, one_zpow, Finset.prod_const_one, mul_one] at h
    exact h

  have h1 : O₁.valuation (algebraMap K L c) = 1 := dagger hinv c h0

  have hm0 : m 0 = 0 := by
    have h := valuation_eq_one_of_le hA1 hm
    rw [map_mul, map_mul, map_prod, map_zpow₀, h1, one_mul] at h
    simp_rw [map_zpow₀, hx1, one_zpow, Finset.prod_const_one, mul_one] at h
    exact zpow_eq_one_imp hf1 h

  have hrest : (fun k : Fin b => m k.succ) = 0 := by
    apply hVI c
    rw [hm0, zpow_zero, one_mul] at hm
    exact hm
  funext i
  refine Fin.cases ?_ ?_ i
  · exact hm0
  · intro j; exact congr_fun hrest j

variable (K A)

lemma extraction (s : LTSeries (PrimeSpectrum A)) :
    ∃ (s₀ : LTSeries (PrimeSpectrum (A.comap (algebraMap K L)))) (b : ℕ) (x : Fin b → A),
      s₀.head = PrimeSpectrum.comap (resHom K A) s.head ∧
      (∀ k, x k ∉ s.head.asIdeal) ∧
      ValIndep K A (fun k => (x k : L)) ∧
      s.length ≤ s₀.length + b := by
  induction s using RelSeries.inductionOn with
  | singleton P =>
    refine ⟨RelSeries.singleton _ (PrimeSpectrum.comap (resHom K A) P), 0, Fin.elim0, ?_, ?_, ?_, ?_⟩
    · simp
    · intro k; exact k.elim0
    · intro c m _; funext k; exact k.elim0
    · simp
  | cons p P hP ih =>
    obtain ⟨s₀, b, x, hhead, hx, hVI, hlen⟩ := ih
    have hlt : P < p.head := hP
    have hle : P.asIdeal ≤ p.head.asIdeal := (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hlt.le
    have hcomap_le :
        PrimeSpectrum.comap (resHom K A) P ≤ PrimeSpectrum.comap (resHom K A) p.head :=
      (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp (Ideal.comap_mono hle)
    by_cases hvis : PrimeSpectrum.comap (resHom K A) P < PrimeSpectrum.comap (resHom K A) p.head
    ·
      have hrel : PrimeSpectrum.comap (resHom K A) P < s₀.head := by rwa [hhead]
      refine ⟨s₀.cons _ hrel, b, x, ?_, ?_, hVI, ?_⟩
      · simp only [RelSeries.head_cons]
      · intro k hk
        rw [RelSeries.head_cons] at hk
        exact hx k (hle hk)
      · simp only [RelSeries.cons_length]; omega
    ·
      have heq : PrimeSpectrum.comap (resHom K A) P = PrimeSpectrum.comap (resHom K A) p.head :=
        eq_of_le_of_not_lt hcomap_le hvis
      have hne : P.asIdeal ≠ p.head.asIdeal := fun h => hlt.ne (PrimeSpectrum.ext h)
      obtain ⟨f, hfQ, hfP⟩ : ∃ f, f ∈ p.head.asIdeal ∧ f ∉ P.asIdeal :=
        SetLike.exists_of_lt (hle.lt_of_ne hne)
      have hinv : Ideal.comap (resHom K A) P.asIdeal = Ideal.comap (resHom K A) p.head.asIdeal := by
        have h := congrArg PrimeSpectrum.asIdeal heq
        simpa using h
      refine ⟨s₀, b + 1, Fin.cons f x, ?_, ?_, ?_, ?_⟩
      · rw [RelSeries.head_cons, heq]; exact hhead
      · intro k
        rw [RelSeries.head_cons]
        refine Fin.cases ?_ ?_ k
        · simpa using hfP
        · intro j; simp only [Fin.cons_succ]; exact fun h => hx j (hle h)
      · have h := valIndep_cons hle hinv f hfQ hfP x hx hVI
        have hfun : (fun k => ((Fin.cons f x : Fin (b + 1) → A) k : L)) =
            (Fin.cons (f : L) (fun k => (x k : L)) : Fin (b + 1) → L) := by
          funext k
          refine Fin.cases ?_ ?_ k
          · simp
          · intro j; simp
        rw [hfun]; exact h
      · simp only [RelSeries.cons_length]; omega

variable {K A}

lemma algebraicIndependent_of_valIndep {b : ℕ} (x : Fin b → L) (hx0 : ∀ k, x k ≠ 0)
    (hVI : ValIndep K A x) : AlgebraicIndependent K x := by
  classical
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp0
  set t : (Fin b →₀ ℕ) → L := fun μ => algebraMap K L (p.coeff μ) * ∏ k, x k ^ (μ k) with ht
  have hsum : ∑ μ ∈ p.support, t μ = 0 := by
    have h := hp
    rw [p.as_sum, map_sum] at h
    simp_rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero (x i))] at h
    exact h
  have hsupp : p.support.Nonempty := MvPolynomial.support_nonempty.mpr hp0
  have htne : ∀ μ ∈ p.support, A.valuation (t μ) ≠ 0 := by
    intro μ hμ
    rw [Valuation.ne_zero_iff]
    refine mul_ne_zero ?_ ?_
    · exact (map_ne_zero (algebraMap K L)).mpr (MvPolynomial.mem_support_iff.mp hμ)
    · exact Finset.prod_ne_zero_iff.mpr (fun k _ => pow_ne_zero _ (hx0 k))
  obtain ⟨μ, hμ, ν, hν, hμν, hval⟩ :=
    exists_ne_map_eq_of_sum_eq_zero A.valuation p.support t hsupp htne hsum
  have htν : t ν ≠ 0 := (Valuation.ne_zero_iff _).mp (htne ν hν)
  set c : K := p.coeff μ / p.coeff ν with hc
  set m : Fin b → ℤ := fun k => (μ k : ℤ) - (ν k : ℤ) with hm_def
  have hquot : algebraMap K L c * ∏ k, x k ^ m k = t μ / t ν := by
    simp only [ht, hc, hm_def, map_div₀]
    rw [Finset.prod_congr rfl (fun k _ => zpow_sub₀ (hx0 k) _ _), Finset.prod_div_distrib]
    simp_rw [zpow_natCast]
    rw [div_mul_div_comm]
  have hone : A.valuation (algebraMap K L c * ∏ k, x k ^ m k) = 1 := by
    rw [hquot, map_div₀, hval, div_self (htne ν hν)]
  have hm := hVI c m hone
  apply hμν
  ext k
  have h := congr_fun hm k
  simp only [hm_def, Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at h
  exact h

end Main

end KrullDimTranscendence

theorem ringKrullDim_le_ringKrullDim_comap_add_trdeg
    {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L) :
    ringKrullDim A ≤ ringKrullDim (A.comap (algebraMap K L)) +
      (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) 
:= by
  classical
  change Order.krullDim (PrimeSpectrum A) ≤
    Order.krullDim (PrimeSpectrum (A.comap (algebraMap K L))) + _
  refine iSup_le fun s => ?_
  obtain ⟨s₀, b, x, -, hx, hVI, hlen⟩ := KrullDimTranscendence.extraction K A s
  have hx0 : ∀ k, ((x k : A) : L) ≠ 0 := by
    intro k h
    apply hx k
    have h' : x k = 0 := Subtype.ext h
    rw [h']; exact Ideal.zero_mem _
  have hind : AlgebraicIndependent K (fun k => (x k : L)) :=
    KrullDimTranscendence.algebraicIndependent_of_valIndep _ hx0 hVI
  have hcard : (b : ℕ∞) ≤ Cardinal.toENat (Algebra.trdeg K L) := by
    have h := OrderHomClass.mono Cardinal.toENat hind.lift_cardinalMk_le_trdeg
    simpa using h
  have h1 : (s₀.length : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum (A.comap (algebraMap K L))) :=
    Order.LTSeries.length_le_krullDim s₀
  have h2 : ((b : ℕ∞) : WithBot ℕ∞) ≤ (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) := by
    exact_mod_cast hcard
  calc (s.length : WithBot ℕ∞) ≤ ((s₀.length + b : ℕ) : WithBot ℕ∞) := by exact_mod_cast hlen
    _ = (s₀.length : WithBot ℕ∞) + ((b : ℕ∞) : WithBot ℕ∞) := by push_cast; rfl
    _ ≤ _ := add_le_add h1 h2

/- The dimension bound at the bottom of the scale: a valuation subring of a `ℚ`-algebra field has
`dim A ≤ trdeg ℚ L + 1`.  The engine is the `ℚ`-case `dim B ≤ 1`: a valuation subring `B` of `ℚ`
localizes `ℤ` (at the submonoid of integers whose image in `B` is a unit), so it is a localization of
the Dedekind domain `ℤ` and hence of dimension at most one; the comap-plus-transcendence-degree
inequality above then costs exactly the `+ 1`.  (The pin's generated `AbhRatSol` label is dropped:
subject namespace.) -/
namespace KrullDimRat

open ValuationSubring

private def unitInts (B : ValuationSubring ℚ) : Submonoid ℤ :=
  (IsUnit.submonoid B).comap (algebraMap ℤ B)

private lemma mem_unitInts {B : ValuationSubring ℚ} {n : ℤ} :
    n ∈ unitInts B ↔ IsUnit (algebraMap ℤ B n) := Iff.rfl

private lemma unitInts_le_nonZeroDivisors (B : ValuationSubring ℚ) :
    unitInts B ≤ nonZeroDivisors ℤ := by
  intro n hn
  rw [mem_nonZeroDivisors_iff_ne_zero]
  rintro rfl
  rw [mem_unitInts, map_zero] at hn
  exact not_isUnit_zero hn

private lemma isUnit_den (B : ValuationSubring ℚ) (x : B) :
    IsUnit (algebraMap ℤ B ((x : ℚ).den : ℤ)) := by
  set r : ℚ := (x : ℚ) with hr
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact r.reduced
  obtain ⟨u, v, huv⟩ := hcop
  have hden0 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hinv : ((r.den : ℚ))⁻¹ = u * r + v := by
    have h1 : (u : ℚ) * r.num + v * r.den = 1 := by exact_mod_cast huv
    have h2 : (r.num : ℚ) = r * r.den := by rw [Rat.mul_den_eq_num]
    rw [h2] at h1
    field_simp
    linarith [h1]
  have hmem : ((r.den : ℚ))⁻¹ ∈ B := by
    rw [hinv]
    exact B.add_mem _ _ (B.mul_mem _ _ (intCast_mem B u) x.2) (intCast_mem B v)
  refine ⟨⟨algebraMap ℤ B (r.den : ℤ), ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    simp [hden0]
  · apply Subtype.ext
    simp [hden0]

private scoped instance isLocalization (B : ValuationSubring ℚ) : IsLocalization (unitInts B) B := by
  rw [isLocalization_iff]
  refine ⟨fun n => n.2, fun z => ?_, fun {a b} h => ⟨1, by
    have : (a : ℚ) = b := by
      have h' := congrArg (fun t : B => (t : ℚ)) h
      simpa using h'
    exact_mod_cast congrArg (fun t => 1 * t) (show a = b by exact_mod_cast this)⟩⟩
  refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ), isUnit_den B z⟩⟩, ?_⟩
  apply Subtype.ext
  simp [Rat.mul_den_eq_num]

private theorem ringKrullDim_le_one (B : ValuationSubring ℚ) : ringKrullDim B ≤ 1 := by
  have h : Ring.DimensionLEOne B :=
    Ring.DimensionLEOne.localization B (unitInts_le_nonZeroDivisors B)
  have : Ring.KrullDimLE 1 B := inferInstance
  exact (Ring.krullDimLE_iff).mp this

end KrullDimRat

open KrullDimRat in
theorem ringKrullDim_le_toENat_trdeg_rat_add_one
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) :
    ringKrullDim A ≤ (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) + 1 := by
  have h := ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg (K := ℚ) A
  have h0 := ringKrullDim_le_one (A.comap (algebraMap ℚ L))
  calc ringKrullDim A ≤ ringKrullDim (A.comap (algebraMap ℚ L)) +
        (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) := h
    _ ≤ 1 + (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) := add_le_add h0 le_rfl
    _ = _ := add_comm _ _

/- The residue-field engine of `exists_smul_mem_of_transcendental_residue`: an element of `F` whose
residue class is transcendental over the residue field of `A` is, after a scaling by `L`, a unit of
`O`.  (The pin's generated `A36FE` label is dropped: subject namespace.) -/
namespace TranscendentalResidue

theorem aeval_eq_linearCombination {K B : Type*} [CommRing K] [Ring B] [Algebra K B]
    (x : B) (p : Polynomial K) :
    Polynomial.aeval x p = Finsupp.linearCombination K (fun j : ℕ => x ^ j) p.toFinsupp.coeff := by
  rcases p with ⟨q⟩
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Polynomial.support_ofFinsupp, Polynomial.coeff_ofFinsupp, Finsupp.linearCombination_apply,
    Finsupp.sum, Algebra.smul_def]

theorem linearIndependent_pow_of_transcendental {K B : Type*} [Field K] [Ring B] [Algebra K B]
    {x : B} (hx : Transcendental K x) : LinearIndependent K (fun j : ℕ => x ^ j) := by
  rw [linearIndependent_iff]
  rw [transcendental_iff] at hx
  intro l hl
  have := hx ⟨.ofCoeff l⟩ (by rw [aeval_eq_linearCombination]; exact hl)
  exact AddMonoidAlgebra.ofCoeff_eq_zero.mp (Polynomial.ofFinsupp_eq_zero.mp this)

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {O : ValuationSubring F} (hO : ∀ x : L, algebraMap L F x ∈ O ↔ x ∈ A)
  {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
  {ρ : O →+* Fbar} (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
  (hρ : ∀ a : A, ρ ⟨algebraMap L F a, (hO a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a))
  {f : F} {hf : f ∈ O}
  (htr : Transcendental (IsLocalRing.ResidueField A) (ρ ⟨f, hf⟩))

include hker in
theorem valuation_eq_one_of_residue_ne_zero (x : O) (hx : ρ x ≠ 0) :
    O.valuation (x : F) = 1 := by
  have hu : IsUnit x := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← hker, RingHom.mem_ker]
    exact hx
  exact (O.valuation_eq_one_iff x).mp hu

include hker in
theorem residue_ne_zero_of_valuation_eq_one (x : O) (hx : O.valuation (x : F) = 1) :
    ρ x ≠ 0 := by
  have hu : IsUnit x := (O.valuation_eq_one_iff x).mpr hx
  rw [← IsLocalRing.notMem_maximalIdeal, ← hker, RingHom.mem_ker] at hu
  exact hu

include hO in
theorem algebraMap_mem_of_valuation_le {x y : L} (hy : y ≠ 0)
    (hle : O.valuation (algebraMap L F x) ≤ O.valuation (algebraMap L F y)) :
    y⁻¹ * x ∈ A := by
  rw [← hO, ← O.valuation_le_one_iff, map_mul, map_inv₀, map_mul, map_inv₀]
  have hy' : O.valuation (algebraMap L F y) ≠ 0 := by
    rw [ne_eq, map_eq_zero, map_eq_zero]; exact hy
  calc (O.valuation (algebraMap L F y))⁻¹ * O.valuation (algebraMap L F x)
      ≤ (O.valuation (algebraMap L F y))⁻¹ * O.valuation (algebraMap L F y) :=
        mul_le_mul_right hle _
    _ = 1 := inv_mul_cancel₀ hy'

include hO hker hρ htr in
theorem exists_valuation_aeval_eq (r : L[X]) (hr : r ≠ 0) :
    ∃ d : L, d ≠ 0 ∧ O.valuation (aeval f r) = O.valuation (algebraMap L F d) := by
  classical
  set v := O.valuation with hv
  set n := r.natDegree + 1 with hn
  obtain ⟨i₀, hi₀, hmax⟩ := (Finset.range n).exists_max_image
    (fun i => v (algebraMap L F (r.coeff i))) ⟨0, by simp [hn]⟩
  set d := r.coeff i₀ with hd

  have hd0 : d ≠ 0 := by
    intro h0
    apply hr
    ext i
    rw [Polynomial.coeff_zero]
    by_cases hi : i < n
    · have hle := hmax i (Finset.mem_range.mpr hi)
      have h0' : v (algebraMap L F (r.coeff i₀)) = 0 := by
        rw [map_eq_zero, map_eq_zero]; exact h0
      rw [h0', le_zero_iff, map_eq_zero, map_eq_zero] at hle
      exact hle
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

  have hq : ∀ i, d⁻¹ * r.coeff i ∈ A := by
    intro i
    by_cases hi : i < n
    · exact algebraMap_mem_of_valuation_le hO hd0 (hmax i (Finset.mem_range.mpr hi))
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
      exact zero_mem _
  let a : ℕ → A := fun i => ⟨d⁻¹ * r.coeff i, hq i⟩
  have hai₀ : a i₀ = 1 := Subtype.ext (by
    change d⁻¹ * r.coeff i₀ = 1
    rw [← hd]; exact inv_mul_cancel₀ hd0)

  let cO : A → O := fun b => ⟨algebraMap L F b, (hO b).mpr b.2⟩
  let fO : O := ⟨f, hf⟩
  let G : O := ∑ i ∈ Finset.range n, cO (a i) * fO ^ i

  have hρG : ρ G = ∑ i ∈ Finset.range n,
      (IsLocalRing.residue A (a i)) • (ρ fO) ^ i := by
    simp only [G, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, ← hρ (a i)]
  have hρG0 : ρ G ≠ 0 := by
    intro h0
    have hli := linearIndependent_pow_of_transcendental htr
    rw [linearIndependent_iff'] at hli
    have := hli (Finset.range n) (fun i => IsLocalRing.residue A (a i)) (by rw [← hρG, h0]) i₀ hi₀
    rw [hai₀, map_one] at this
    exact one_ne_zero this
  have hvG : v (G : F) = 1 := valuation_eq_one_of_residue_ne_zero hker G hρG0

  have hcoeG : ((G : O) : F) = ∑ i ∈ Finset.range n, algebraMap L F (d⁻¹ * r.coeff i) * f ^ i := by
    change O.subtype G = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
    rfl
  have haeval : aeval f r = algebraMap L F d * (G : F) := by
    rw [hcoeG, Finset.mul_sum, Polynomial.aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, mul_inv_cancel_left₀ hd0]
  refine ⟨d, hd0, ?_⟩
  rw [haeval, map_mul, hvG, mul_one]

include hO hker hρ htr in
theorem exists_valuation_eq_of_mem_adjoin {y : F}
    (hy : y ∈ IntermediateField.adjoin L ({f} : Set F)) (hy0 : y ≠ 0) :
    ∃ d : L, d ≠ 0 ∧ O.valuation y = O.valuation (algebraMap L F d) := by
  rw [IntermediateField.mem_adjoin_simple_iff] at hy
  obtain ⟨r, s, rfl⟩ := hy
  have hr0 : aeval f r ≠ 0 := by
    intro h0; apply hy0; rw [h0, zero_div]
  have hs0 : aeval f s ≠ 0 := by
    intro h0; apply hy0; rw [h0, div_zero]
  have hr : r ≠ 0 := by rintro rfl; exact hr0 (map_zero _)
  have hs : s ≠ 0 := by rintro rfl; exact hs0 (map_zero _)
  obtain ⟨dr, hdr0, hdr⟩ := exists_valuation_aeval_eq hO hker hρ htr r hr
  obtain ⟨ds, hds0, hds⟩ := exists_valuation_aeval_eq hO hker hρ htr s hs
  refine ⟨dr / ds, div_ne_zero hdr0 hds0, ?_⟩
  rw [map_div₀, hdr, hds, ← map_div₀, ← map_div₀]

include hO hker hρ htr in
theorem exists_smul_of_valuation_eq [IsAlgClosed L] {h : F} (hh : h ≠ 0) {i j : ℕ} (hij : i < j)
    {ci cj : F} (hci : ci ∈ IntermediateField.adjoin L ({f} : Set F))
    (hcj : cj ∈ IntermediateField.adjoin L ({f} : Set F)) (hci0 : ci ≠ 0) (hcj0 : cj ≠ 0)
    (heq : O.valuation (ci * h ^ i) = O.valuation (cj * h ^ j)) :
    ∃ c : L, ∃ hc : c • h ∈ O, ρ ⟨c • h, hc⟩ ≠ 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hij

  set m := n + 1 with hm
  have hm0 : m ≠ 0 := by omega
  have hvh : O.valuation h ≠ 0 := by rwa [ne_eq, map_eq_zero]
  have hvcj : O.valuation cj ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨di, hdi0, hdi⟩ := exists_valuation_eq_of_mem_adjoin hO hker hρ htr hci hci0
  obtain ⟨dj, hdj0, hdj⟩ := exists_valuation_eq_of_mem_adjoin hO hker hρ htr hcj hcj0

  have hpow : O.valuation h ^ m = O.valuation (algebraMap L F (dj⁻¹ * di)) := by
    have e1 : O.valuation ci * O.valuation h ^ i =
        (O.valuation cj * O.valuation h ^ m) * O.valuation h ^ i := by
      have e0 := heq
      rw [map_mul, map_pow, map_mul, map_pow, show i + n + 1 = i + m by omega, pow_add] at e0
      rw [e0, mul_assoc, mul_comm (O.valuation h ^ i) (O.valuation h ^ m)]
    have e2 : O.valuation ci = O.valuation cj * O.valuation h ^ m :=
      mul_right_cancel₀ (pow_ne_zero _ hvh) e1
    rw [map_mul, map_inv₀, map_mul, map_inv₀, ← hdi, ← hdj, e2, inv_mul_cancel_left₀ hvcj]
  set e : L := dj⁻¹ * di with he
  have he0 : e ≠ 0 := mul_ne_zero (inv_ne_zero hdj0) hdi0
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq e⁻¹ (Nat.pos_of_ne_zero hm0)

  have hone : O.valuation (c • h) ^ m = 1 := by
    rw [Algebra.smul_def, map_mul, mul_pow, hpow, ← map_pow, ← map_pow, hc, ← map_mul,
      ← map_mul, inv_mul_cancel₀ he0, map_one, map_one]
  have hone' : O.valuation (c • h) = 1 :=
    le_antisymm ((pow_le_one_iff hm0).mp hone.le) ((one_le_pow_iff hm0).mp hone.ge)
  have hmem : c • h ∈ O := (O.valuation_le_one_iff _).mp hone'.le
  exact ⟨c, hmem, residue_ne_zero_of_valuation_eq_one hker ⟨c • h, hmem⟩ hone'⟩

include hO hker hρ htr in
theorem exists_smul_mem [IsAlgClosed L]
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (h : F) (hh : h ≠ 0) :
    ∃ c : L, ∃ hc : c • h ∈ O, ρ ⟨c • h, hc⟩ ≠ 0 := by
  classical
  set K := IntermediateField.adjoin L ({f} : Set F) with hK
  set v := O.valuation with hv
  obtain ⟨p, hp0, hp⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := K) h)
  set N := p.natDegree + 1 with hN

  let t : ℕ → F := fun i => ((p.coeff i : K) : F) * h ^ i
  have hsum : ∑ i ∈ Finset.range N, t i = 0 := by
    have e : aeval h p = ∑ i ∈ Finset.range N, t i := by
      rw [Polynomial.aeval_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, IntermediateField.algebraMap_apply]
    rw [← e, hp]

  have hlead : t p.natDegree ≠ 0 := by
    have h1 : ((p.coeff p.natDegree : K) : F) ≠ 0 := by
      have : p.coeff p.natDegree ≠ 0 := by
        rw [Polynomial.coeff_natDegree]; exact Polynomial.leadingCoeff_ne_zero.mpr hp0
      exact_mod_cast this
    exact mul_ne_zero h1 (pow_ne_zero _ hh)
  have hleadmem : p.natDegree ∈ Finset.range N := Finset.mem_range.mpr (by omega)

  obtain ⟨j₀, hj₀, hmax⟩ := (Finset.range N).exists_max_image (fun i => v (t i))
    ⟨p.natDegree, hleadmem⟩
  have hvj₀ : v (t j₀) ≠ 0 := by
    intro h0
    have := hmax p.natDegree hleadmem
    rw [h0, le_zero_iff, map_eq_zero] at this
    exact hlead this

  have hex : ∃ i₁ ∈ Finset.range N \ {j₀}, ¬ v (t i₁) < v (t j₀) := by
    by_contra hall
    push Not at hall
    have := Valuation.map_sum_eq_of_lt v hj₀ hall
    rw [hsum, map_zero] at this
    exact hvj₀ this.symm
  obtain ⟨i₁, hi₁, hnot⟩ := hex
  rw [Finset.mem_sdiff, Finset.mem_singleton] at hi₁
  have hEq : v (t i₁) = v (t j₀) := le_antisymm (hmax i₁ hi₁.1) (not_lt.mp hnot)
  have hvi₁ : v (t i₁) ≠ 0 := hEq ▸ hvj₀

  have hc0 : ∀ i, v (t i) ≠ 0 → ((p.coeff i : K) : F) ≠ 0 := by
    intro i hi h0
    apply hi
    show v (((p.coeff i : K) : F) * h ^ i) = 0
    rw [h0, zero_mul, map_zero]

  rcases lt_or_gt_of_ne hi₁.2 with hlt | hgt
  · exact exists_smul_of_valuation_eq hO hker hρ htr hh hlt (p.coeff i₁).2 (p.coeff j₀).2
      (hc0 i₁ hvi₁) (hc0 j₀ hvj₀) hEq
  · exact exists_smul_of_valuation_eq hO hker hρ htr hh hgt (p.coeff j₀).2 (p.coeff i₁).2
      (hc0 j₀ hvj₀) (hc0 i₁ hvi₁) hEq.symm

end TranscendentalResidue

theorem exists_smul_mem_of_transcendental_residue
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (O : ValuationSubring F) (hO : ∀ x : L, algebraMap L F x ∈ O ↔ x ∈ A)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (ρ : O →+* Fbar) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ a : A, ρ ⟨algebraMap L F a, (hO a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a))
    (f : F) (hf : f ∈ O)
    (htr : Transcendental (IsLocalRing.ResidueField A) (ρ ⟨f, hf⟩))
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (h : F) (hh : h ≠ 0) :
    ∃ c : L, ∃ hc : c • h ∈ O, ρ ⟨c • h, hc⟩ ≠ 0 
:= by
  exact TranscendentalResidue.exists_smul_mem hO hker hρ htr h hh

open scoped Polynomial

/- The root count of a polynomial over a valuation subring: the reduction `p.map σ` has as many
roots as the base change `p.map (algebraMap A E)` splits into.  The pin's engine, transcribed with its
section variables, under a subject namespace. -/
namespace RootCount

variable {E k : Type*} [Field E] [Field k] (A : ValuationSubring E) (σ : A →+* k)
  (hσ : RingHom.ker σ = IsLocalRing.maximalIdeal A)

theorem algebraMap_injective : Function.Injective (algebraMap A E) := Subtype.val_injective

theorem isUnit_iff_inv_mem (z : A) (hz : (z : E) ≠ 0) : IsUnit z ↔ (z : E)⁻¹ ∈ A := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 := congrArg (fun w : A => (w : E)) u.mul_inv
    simp only [Subring.coe_one, hu] at h1
    push_cast at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact SetLike.coe_mem _
  · intro h
    exact ⟨⟨z, ⟨(z : E)⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ hz), Subtype.ext (inv_mul_cancel₀ hz)⟩,
      rfl⟩

theorem inv_mem_maximalIdeal {α : E} (hα : α ∉ A) :
    ∃ h : α⁻¹ ∈ A, (⟨α⁻¹, h⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  have hα0 : α ≠ 0 := fun h => hα (h ▸ A.zero_mem)
  have hβA : α⁻¹ ∈ A := (A.mem_or_inv_mem α).resolve_left hα
  refine ⟨hβA, (IsLocalRing.mem_maximalIdeal _).mpr (_root_.mem_nonunits_iff.mpr fun hu => hα ?_)⟩
  have := (isUnit_iff_inv_mem A ⟨α⁻¹, hβA⟩ (inv_ne_zero hα0)).mp hu
  simpa using this

theorem coeff_mem_of_one_sub_mul (β : E) (hβ : β ∈ A) (q : E[X])
    (h : ∀ n, ((1 - C β * X) * q).coeff n ∈ A) (n : ℕ) : q.coeff n ∈ A := by
  induction n with
  | zero =>
    have := h 0
    rwa [sub_mul, one_mul, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul_zero, mul_zero,
      sub_zero] at this
  | succ n ih =>
    have := h (n + 1)
    rw [sub_mul, one_mul, coeff_sub, mul_assoc, coeff_C_mul, coeff_X_mul] at this
    have e : q.coeff (n + 1) = (q.coeff (n + 1) - β * q.coeff n) + β * q.coeff n := by ring
    rw [e]
    exact A.add_mem _ _ this (A.mul_mem _ _ hβ ih)

include hσ in
theorem main (n : ℕ) : ∀ p : A[X], p.natDegree = n → p.map σ ≠ 0 →
    Multiset.card (p.map (algebraMap A E)).roots = p.natDegree →
    (p.map σ).natDegree = Multiset.card p.roots := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp hsplit
  have hp0 : p ≠ 0 := fun h => hp (by rw [h, Polynomial.map_zero])
  have hinj := algebraMap_injective A
  have hpE0 : p.map (algebraMap A E) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp0
  by_cases h0 : p.natDegree = 0
  · obtain ⟨a, ha⟩ : ∃ a, p = C a := ⟨_, eq_C_of_natDegree_eq_zero h0⟩
    rw [ha, map_C, natDegree_C, roots_C, Multiset.card_zero]

  have hcard : 0 < Multiset.card (p.map (algebraMap A E)).roots := by
    rw [hsplit]; exact Nat.pos_of_ne_zero h0
  obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  have hroot : (p.map (algebraMap A E)).IsRoot α := (mem_roots hpE0).mp hα
  by_cases hαA : α ∈ A
  ·
    set a : A := ⟨α, hαA⟩ with ha_def
    have ha : p.IsRoot a := by
      apply hinj
      have : (p.map (algebraMap A E)).eval (algebraMap A E a) = 0 := hroot
      rw [map_zero]; rwa [eval_map, eval₂_at_apply] at this
    have hfac : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    set p₁ := p /ₘ (X - C a) with hp₁_def
    have hp₁0 : p₁ ≠ 0 := fun h => hp0 (by rw [← hfac, h, mul_zero])
    have hdeg : p.natDegree = p₁.natDegree + 1 := by
      rw [← hfac, natDegree_mul (X_sub_C_ne_zero a) hp₁0, natDegree_X_sub_C, add_comm]
    have hmapσ : p.map σ = (X - C (σ a)) * p₁.map σ := by
      rw [← hfac, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
    have hp₁σ : p₁.map σ ≠ 0 := fun h => hp (by rw [hmapσ, h, mul_zero])
    have hdegσ : (p.map σ).natDegree = (p₁.map σ).natDegree + 1 := by
      rw [hmapσ, natDegree_mul (X_sub_C_ne_zero _) hp₁σ, natDegree_X_sub_C, add_comm]
    have hroots : p.roots = a ::ₘ p₁.roots := by
      rw [← hfac, roots_mul (hfac.symm ▸ hp0), roots_X_sub_C, Multiset.singleton_add]
    have hmapE : p.map (algebraMap A E) = (X - C α) * p₁.map (algebraMap A E) := by
      rw [← hfac, Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]
      rfl
    have hp₁E0 : p₁.map (algebraMap A E) ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hp₁0
    have hsplit₁ : Multiset.card (p₁.map (algebraMap A E)).roots = p₁.natDegree := by
      have := hsplit
      rw [hmapE, roots_mul (hmapE ▸ hpE0), roots_X_sub_C, Multiset.card_add,
        Multiset.card_singleton, hdeg] at this
      omega
    have := ih p₁.natDegree (by omega) p₁ rfl hp₁σ hsplit₁
    rw [hdegσ, hroots, Multiset.card_cons, this]
  ·
    obtain ⟨hβA, hβmax⟩ := inv_mem_maximalIdeal A hαA
    have hα0 : α ≠ 0 := fun h => hαA (h ▸ A.zero_mem)
    set β : A := ⟨α⁻¹, hβA⟩ with hβ_def
    have hσβ : σ β = 0 := by rw [← RingHom.mem_ker, hσ]; exact hβmax

    set qE : E[X] := C (-α) * (p.map (algebraMap A E) /ₘ (X - C α)) with hqE_def
    have hfacE : (1 - C (α⁻¹) * X) * qE = p.map (algebraMap A E) := by
      have h1 : (1 - C (α⁻¹) * X : E[X]) * C (-α) = X - C α := by
        have h2 : C (α⁻¹) * C (-α) = (-1 : E[X]) := by
          rw [← C_mul, mul_neg, inv_mul_cancel₀ hα0, map_neg, C_1]
        calc (1 - C (α⁻¹) * X : E[X]) * C (-α) = C (-α) - (C α⁻¹ * C (-α)) * X := by ring
          _ = X - C α := by rw [h2, map_neg]; ring
      rw [hqE_def, ← mul_assoc, h1]
      exact mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hqcoeff : ∀ m, qE.coeff m ∈ A := coeff_mem_of_one_sub_mul A α⁻¹ hβA qE (fun m => by
      rw [hfacE, coeff_map]; exact SetLike.coe_mem _)
    obtain ⟨q, hq⟩ : ∃ q : A[X], q.map (algebraMap A E) = qE := by
      rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
      exact fun m => ⟨⟨_, hqcoeff m⟩, rfl⟩
    have hfac : (1 - C β * X) * q = p := by
      apply Polynomial.map_injective _ hinj
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_C,
        map_X, hq, ← hfacE]
      rfl
    have hq0 : q ≠ 0 := fun h => hp0 (by rw [← hfac, h, mul_zero])
    have hlin : (1 - C β * X : A[X]) = C (-β) * X + C 1 := by rw [map_neg, C_1]; ring
    have hβ0 : β ≠ 0 := fun h => by
      have := congrArg (fun z : A => (z : E)) h
      simp only [hβ_def, ZeroMemClass.coe_zero, inv_eq_zero] at this
      exact hα0 this
    have hlin0 : (1 - C β * X : A[X]) ≠ 0 := fun h => by
      have := congrArg natDegree h
      rw [hlin, natDegree_linear (neg_ne_zero.mpr hβ0), natDegree_zero] at this
      exact one_ne_zero this
    have hdeg : p.natDegree = q.natDegree + 1 := by
      rw [← hfac, natDegree_mul hlin0 hq0, hlin, natDegree_linear (neg_ne_zero.mpr hβ0), add_comm]
    have hmapσ : p.map σ = q.map σ := by
      rw [← hfac, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
        map_C, map_X, hσβ, C_0, zero_mul, sub_zero, one_mul]
    have hqσ : q.map σ ≠ 0 := hmapσ ▸ hp
    have hroots : p.roots = q.roots := by
      rw [← hfac, roots_mul (hfac.symm ▸ hp0)]
      have : (1 - C β * X : A[X]).roots = 0 := by
        refine Multiset.eq_zero_of_forall_notMem fun c hc => ?_
        have hc' := ((mem_roots hlin0).mp hc)
        have he : (1 - C β * X : A[X]).eval c = 1 - β * c := by
          simp [eval_sub, eval_one, eval_mul, eval_C, eval_X]
        rw [IsRoot.def, he, sub_eq_zero] at hc'
        have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
          rw [hc']; exact Ideal.mul_mem_right _ _ hβmax
        exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
          ((Ideal.eq_top_iff_one _).mpr h1)
      rw [this, zero_add]
    have hqE0 : qE ≠ 0 := by rw [← hq]; exact (Polynomial.map_ne_zero_iff hinj).mpr hq0
    have hsplit₁ : Multiset.card (q.map (algebraMap A E)).roots = q.natDegree := by
      have := hsplit
      have hlinE : (1 - C α⁻¹ * X : E[X]) = C (-α⁻¹) * (X - C α) := by
        have h2 : C (α⁻¹) * C α = (1 : E[X]) := by rw [← C_mul, inv_mul_cancel₀ hα0, C_1]
        calc (1 - C α⁻¹ * X : E[X]) = C α⁻¹ * C α - C α⁻¹ * X := by rw [h2]
          _ = C (-α⁻¹) * (X - C α) := by rw [map_neg]; ring
      rw [← hfacE, roots_mul (hfacE.symm ▸ hpE0), hlinE, roots_C_mul _ (neg_ne_zero.mpr
        (inv_ne_zero hα0)), roots_X_sub_C, Multiset.card_add, Multiset.card_singleton, hdeg]
        at this
      rw [hq]; omega
    have := ih q.natDegree (by omega) q rfl hqσ hsplit₁
    rw [hmapσ, hroots, this]

end RootCount

theorem natDegree_map_eq_card_roots_of_splits
    {E k : Type*} [Field E] [Field k] (A : ValuationSubring E) (σ : A →+* k)
    (hσ : RingHom.ker σ = IsLocalRing.maximalIdeal A)
    (p : A[X]) (hp : p.map σ ≠ 0)
    (hsplit : Multiset.card (p.map (algebraMap A E)).roots = p.natDegree) :
    (p.map σ).natDegree = Multiset.card p.roots 
:= by
  exact RootCount.main A σ hσ p.natDegree p rfl hp hsplit

open IsLocalRing TensorProduct

-- The `Ψ` line of this row's *statement* binds `f`/`a` and only uses them through `mul_comm _ _`;
-- the wire spells them `f`/`a` (they cannot be `_`-prefixed without a `check_port` mismatch), and the
-- pin is silent only because `P2M/Util.lean` turns this linter off globally.
set_option linter.unusedVariables false in
theorem tensorProduct_exists_primitive_factor
    (K F K' : Type*) [Field K] [CommRing F] [Nontrivial F] [NoZeroDivisors F]
    [Field K'] [Algebra K F] [Algebra K K']
    (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K)
    (_hker : RingHom.ker σ = maximalIdeal A)
    (hsec : ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c) :
    letI : Algebra K A := ((algebraMap K K').codRestrict A.toSubring hK).toAlgebra
    let hσAlg : A →ₐ[K] F :=
      { toRingHom := (algebraMap K F).comp σ
        commutes' := fun c ↦ congrArg (algebraMap K F) (hsec c) }
    let Ψ : TensorProduct K F A →ₐ[K] F :=
      Algebra.TensorProduct.lift (AlgHom.id K F) hσAlg (fun f a ↦ mul_comm _ _)
    ∀ z : TensorProduct K F A, z ≠ 0 →
      ∃ a : A, a ≠ 0 ∧ ∃ z' : TensorProduct K F A,
        z = ((1 : F) ⊗ₜ[K] a) * z' ∧ Ψ z' ≠ 0 
:= by
  classical
  letI : Algebra K A := ((algebraMap K K').codRestrict A.toSubring hK).toAlgebra
  intro hσAlg Ψ z hz
  let e := Module.Basis.ofVectorSpace K F
  let eqv : TensorProduct K F A ≃ₗ[K] _ →₀ A :=
    (LinearEquiv.rTensor A e.repr).trans (TensorProduct.finsuppScalarLeft K A _)
  have hsingle : ∀ i a, eqv.symm (Finsupp.single i a) = e i ⊗ₜ[K] a := by
    intro i a
    simp only [eqv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      TensorProduct.finsuppScalarLeft_symm_apply_single]
    change (LinearEquiv.rTensor A e.repr).symm _ = _
    rw [LinearEquiv.symm_rTensor, LinearEquiv.rTensor_tmul, Module.Basis.repr_symm_single_one]
  have hMinDvd : ∀ (s : Finset (Module.Basis.ofVectorSpaceIndex K F))
      (f : Module.Basis.ofVectorSpaceIndex K F → A), s.Nonempty →
      ∃ j ∈ s, ∀ i ∈ s, f j ∣ f i := by
    intro s f hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton j => exact ⟨j, Finset.mem_singleton_self j,
        fun i hi ↦ (Finset.mem_singleton.mp hi) ▸ dvd_refl _⟩
    | cons j s hjs hs' ih =>
      obtain ⟨k, hks, hk⟩ := ih
      rcases ValuationRing.dvd_total (R := A) (f j) (f k) with hjk | hkj
      · exact ⟨j, Finset.mem_cons_self _ _, fun i hi ↦
          (Finset.mem_cons.mp hi).elim (· ▸ dvd_refl _) (fun hi' ↦ hjk.trans (hk i hi'))⟩
      · exact ⟨k, Finset.mem_cons.mpr (Or.inr hks), fun i hi ↦
          (Finset.mem_cons.mp hi).elim (· ▸ hkj) (hk i)⟩
  set g := eqv z with hg_def
  have hg0 : g ≠ 0 := fun h ↦ hz (by rw [← eqv.symm_apply_apply z, ← hg_def, h, map_zero])
  have hne := Finsupp.support_nonempty_iff.mpr hg0
  obtain ⟨j, hj, hjdvd⟩ := hMinDvd g.support g hne
  have hjdvd' : ∀ i, g j ∣ g i := fun i ↦
    if hi : i ∈ g.support then hjdvd i hi else (Finsupp.notMem_support_iff.mp hi) ▸ dvd_zero _
  have ha0 : g j ≠ 0 := Finsupp.mem_support_iff.mp hj
  choose b hb using hjdvd'
  have hbj : b j = 1 := mul_left_cancel₀ ha0 ((hb j).symm.trans (mul_one _).symm)
  let z' : TensorProduct K F A := g.support.sum fun i ↦ e i ⊗ₜ[K] b i
  have hzeq : z = ((1 : F) ⊗ₜ[K] g j) * z' := by
    have hzg : z = g.support.sum fun i ↦ e i ⊗ₜ[K] g i := by
      conv_lhs => rw [show z = eqv.symm g from (eqv.symm_apply_apply z).symm,
        show g = g.sum Finsupp.single from (Finsupp.sum_single g).symm, map_finsuppSum]
      simp only [hsingle, Finsupp.sum]
    rw [hzg]
    simp only [z', Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hb i]
  refine ⟨g j, ha0, z', hzeq, ?_⟩
  -- `Algebra.TensorProduct.lift`'s commutativity binder is `Commute`, a semireducible `def`, so
  -- the pin's `simp only [… lift_tmul …]` cannot fire under the tactic's `implicit` transparency
  -- in this toolchain; the tensor-product computation is factored out once, at default
  -- transparency, and never unfolded again.
  have hΨtmul : ∀ (x : F) (y : A), Ψ (x ⊗ₜ[K] y) = x * hσAlg y := fun x y ↦
    Algebra.TensorProduct.lift_tmul (AlgHom.id K F) hσAlg (fun f a ↦ mul_comm _ _) x y
  have hσAlg_apply : ∀ a : A, hσAlg a = algebraMap K F (σ a) := fun a ↦ rfl
  have hz'sum : Ψ z' = g.support.sum (fun i ↦ e i * algebraMap K F (σ (b i))) := by
    simp only [z', map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hΨtmul, hσAlg_apply]
  intro hsum
  rw [hz'sum] at hsum
  have hsum' : g.support.sum (fun i ↦ (σ (b i)) • e i) = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, mul_comm]
  have hli := e.linearIndependent.comp (Subtype.val : g.support → _) Subtype.val_injective
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun i ↦ σ (b i)) (by
    simp only [Function.comp_apply]
    exact (Finset.sum_attach g.support (fun i ↦ σ (b i) • e i)).trans hsum')
  have hj0 : σ (b j) = 0 := hcoef ⟨j, hj⟩
  rw [hbj, map_one] at hj0
  exact one_ne_zero hj0

theorem exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero
    {L : Type*} [Field L] (A : ValuationSubring L)
    (q₁ : Polynomial L) (hq₁ : q₁ ≠ 0) :
    ∃ q : Polynomial A, ∃ c : L, c ≠ 0 ∧
      (q.map A.subtype = Polynomial.C c⁻¹ * q₁) ∧ q.map (IsLocalRing.residue A) ≠ 0 
:= by
  classical
  have hne : q₁.support.Nonempty := Polynomial.support_nonempty.mpr hq₁
  obtain ⟨i₀, hi₀s, hi₀max⟩ :=
    q₁.support.exists_max_image (fun i => A.valuation (q₁.coeff i)) hne
  set c := q₁.coeff i₀ with hc
  have hc0 : c ≠ 0 := Polynomial.mem_support_iff.mp hi₀s

  have hmem : ∀ i, c⁻¹ * q₁.coeff i ∈ A := by
    intro i
    rcases eq_or_ne (q₁.coeff i) 0 with h0 | h0
    · rw [h0, mul_zero]; exact A.zero_mem
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    have hi : i ∈ q₁.support := Polynomial.mem_support_iff.mpr h0
    have hle := hi₀max i hi
    have hvc : A.valuation c ≠ 0 := by simpa using hc0
    calc (A.valuation c)⁻¹ * A.valuation (q₁.coeff i)
        ≤ (A.valuation c)⁻¹ * A.valuation c := mul_le_mul_right hle _
      _ = 1 := inv_mul_cancel₀ hvc

  have hcoeffs : ↑(C c⁻¹ * q₁).coeffs ⊆ (A.toSubring : Set L) := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    rw [coeff_C_mul]
    exact hmem i
  set q : Polynomial A := (C c⁻¹ * q₁).toSubring A.toSubring hcoeffs with hq
  refine ⟨q, c, hc0, ?_, ?_⟩
  ·
    rw [hq]
    exact Polynomial.map_toSubring _ _ hcoeffs
  ·
    have hqmap : q.map A.subtype = C c⁻¹ * q₁ := by
      rw [hq]; exact Polynomial.map_toSubring _ _ hcoeffs
    have hone : q.coeff i₀ = 1 := by
      apply Subtype.ext
      have h2 : A.subtype (q.coeff i₀) = (C c⁻¹ * q₁).coeff i₀ := by
        rw [← Polynomial.coeff_map, hqmap]
      rw [ValuationSubring.subtype_apply] at h2
      rw [show ((1 : A) : L) = 1 from rfl, h2, coeff_C_mul, ← hc, inv_mul_cancel₀ hc0]
    intro hzero
    have h1 : (q.map (IsLocalRing.residue A)).coeff i₀ = 0 := by rw [hzero]; simp
    rw [coeff_map, hone, map_one] at h1
    exact one_ne_zero h1


end ValuationSubring
