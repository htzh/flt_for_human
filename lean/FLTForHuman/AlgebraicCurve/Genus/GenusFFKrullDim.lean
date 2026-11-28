/-
The genus is additive downwards, at Krull dimension one.

`AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one` (216 pin
lines): in the `krullDimLE`-one residue-span setup, the sum of the residue fields' genera is at most
`genusFF L F`. It is the consumer of SET-AF109B/C — the two residue-span rows are its premises, together
with the genus inputs (`Genus/Index`, `Genus/ConstantFieldExtensionConsequences`,
`IsCurveOver/Transcendental`) and `PrincipalDivisors/PoleDivisor` — so the home is a new module above
all ten premise modules.

The pin's proof is the `sum_finrank` count plus the pole divisor's degree bound; the row is the first
of the genus-degree family whose other members are still on the shelf.

## The rows

* `AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one` — 216 pin `S_` lines.

## The declaration surface

The pin's `S_` file is a **surface of 3 declarations**, all public, in the pin's generated namespace
label `KD1` (`ell_add_card_le` `:35`, `main` `:118`) plus the headline `solution` `:200` outside it.
The generated label `KD1` is a stage/order tag, not a subject: it comes off, and the two helpers sit
directly in the subject namespace `AlgebraicCurve.RegularProlongation`. The engine diff is **3/3 by
statement hash** (pin sources 2, pin declarations 4 counting the `Theorems/` wrapper's copy of the
headline, module declarations 3, 0 unaccounted). The pin has **no `private` declaration** in this file
(all three rows of the parse read `private = 0`), so no surface-gate question arises.

* `ell_add_card_le` — the counting estimate: for the pole divisor `D` of `f` and the residue pole
  divisors `Db i`, `ell (M • D) + card ι ≤ ∑ i, ell (M • Db i) + 1` for all large `M`. Proved by
  capping `L(M • D)` into `ST ⊓ STM`, bounding that intersection by `ST ⊓ ST0` (a `finrank ≤ 1`
  span of the constant `1`), and `omega`.
* `main` — the degree count: `ell (M • D) = M * deg D + 1 - genusFF L F` and the per-`i` Riemann–Roch
  asymptotics for `Db i` at the same `M` give the inequality after cancelling `M * deg D` (`linarith`
  over `ℤ`, then `exact_mod_cast`).
* the headline is the pin's `solution`: `KD1.main` applied to the identity.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_RegularProlongation_sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one.lean

## What the transcription measured

* **The scaffold's import list was already complete.** The proof is the pin's text and elaborates
  against exactly these eleven imports; nothing was added (no `Mathlib` module was needed beyond
  `Mathlib.Tactic`, and no premise module was missing).
* **Statement text is verbatim** (`check_port` 3 `ok`). The proof text drifts in three places, none of
  which touches a statement:
  1. `ResidueField A` → `IsLocalRing.ResidueField A` in the two proof bodies (the pin opens
     `IsLocalRing`; the port writes the qualification, as the scaffold's statements already did);
  2. seven class-typed `haveI` → `have` — `linter.style.haveILetI` (an *info* line counts as a warning
     for the silent-module gate). A local hypothesis of class type is already an instance (FR-0323), so
     the substitution is behaviour-preserving; measured silent after the change;
  3. the unused `with hST` / `with hSTM` / `with hST0` binder names of the three `set`s are dropped.
* **Dedup** (`dedup.py --within`): **1 intra-module `shape` cluster, 19 lines**, between `main` and
  the headline. That pair is the **pin's own headline↔engine pair** (`solution` is `KD1.main` applied
  to the identity, and the pin states both with the same binder block, binder for binder), so it is kept,
  not merged: collapsing it would delete the pin's `solution` row and change the engine diff from 3/3
  to 2/3. No cross-module cluster.
* **`move_dead --dry-run`**: `0 declarations, 0 lines` — no dead surface.
* **Axioms**: `ell_add_card_le`, `main`, and the headline each read
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **The heartbeat probe** (recorded, never installed). Downward ladder at the edit-loop settings, one
  run per value:

  | cap | 40000 | 20000 | 10000 | 5000 | 1000 |
  |---|---|---|---|---|---|
  | module | **pass** | **pass** | fail | fail | fail |
  | first failure | — | — | `whnf` in `main` and in `ell_add_card_le` | `whnf` in the `ell_add_card_le` statement; `isDefEq` in the headline's `calc` | `isDefEq` in the statements of `ell_add_card_le` and `main` |

  **Module floor** (all three proofs `sorry`, one run): passes at **10000**, the lowest cap at which the
  real module fails — so the cost is in the proofs, not in the types. The probe is a bisector and no cap
  is installed.
-/
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.IsCurveOver.Transcendental
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.PoleDivisor
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueBasis
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueFinrank
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueIntegralClosure
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueKrullDim
import FLTForHuman.AlgebraicCurve.RegularProlongationResidueSpan
import FLTForHuman.FieldTheory.ValuationSubringResidueField
import Mathlib.Tactic

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.ell_add_card_le
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (D : Divisor L F) (hD : ∀ v : Place L F, D v = max 0 (-v.ord f))
    (Db : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fb i))
    (hDb : ∀ i, ∀ w : Place (IsLocalRing.ResidueField A) (Fb i),
      Db i w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩))) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ell (M • D) + Fintype.card ι ≤ (∑ i, ell (M • Db i)) + 1 := by
  classical
  have := hfd

  have : IsCurveOver L F := isCurveOver_of_isAlgClosed_of_transcendental f htrL
  obtain ⟨hℓ0, -⟩ := exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental f htrL D hD
  have hL0 : FiniteDimensional L ↥(LSpace (0 : Divisor L F)) :=
    Module.finite_of_finrank_pos (by
      change 0 < ell (0 : Divisor L F)
      omega)

  obtain ⟨M₀, hM₀⟩ :=
    RegularProlongation.exists_forall_finrank_residueSpan_inf_add_card_le
      A Fb R hR f hf htrL hfd htr heq Db hDb
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨hfin, hcount⟩ := hM₀ M hM

  set ST : Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
    Submodule.span (IsLocalRing.ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i}
  set STM : Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
    Submodule.span (IsLocalRing.ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
          u * (f ^ M)⁻¹ ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i}
  set ST0 : Submodule (IsLocalRing.ResidueField A) (∀ i, Fb i) :=
    Submodule.span (IsLocalRing.ResidueField A)
      {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
        (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V → u ∈ V) ∧
        ∀ i, (R i).residue ⟨u, hu i⟩ = h i}

  have hlift := RegularProlongation.span_residue_lSpace_le_residueSpan_inf A Fb R f hf hfd D hD M
  have : FiniteDimensional L ↥(LSpace (M • D)) := finiteDimensional_lSpace (M • D)
  have hdim := RegularProlongation.finrank_span_pi_residue_eq_finrank_of_sum_finrank_eq
    A Fb R hR f hf htr heq (LSpace (M • D))
  have h1 : ell (M • D) ≤ Module.finrank (IsLocalRing.ResidueField A) ↥(ST ⊓ STM) := by
    have := Submodule.finrank_mono (R := IsLocalRing.ResidueField A) hlift
    change Module.finrank L ↥(LSpace (M • D)) ≤ _
    rw [← hdim]
    exact this

  have hle : ST ⊓ ST0 ≤ Submodule.span (IsLocalRing.ResidueField A) {(1 : ∀ i, Fb i)} := by
    intro x hx
    obtain ⟨c, hc⟩ :=
      RegularProlongation.exists_forall_residue_eq_algebraMap_of_mem_residueSpan_inf_of_krullDimLE_one
        A Fb R hR f hf htrL hfd htr heq x hx.1 hx.2
    have hx' : x = c • (1 : ∀ i, Fb i) := by
      funext i
      simp [hc i, Algebra.algebraMap_eq_smul_one]
    rw [hx']
    exact Submodule.smul_mem _ c (Submodule.subset_span rfl)
  have h2 : Module.finrank (IsLocalRing.ResidueField A) ↥(ST ⊓ ST0) ≤ 1 := by
    calc Module.finrank (IsLocalRing.ResidueField A) ↥(ST ⊓ ST0)
        ≤ Module.finrank (IsLocalRing.ResidueField A)
            ↥(Submodule.span (IsLocalRing.ResidueField A) {(1 : ∀ i, Fb i)}) :=
          Submodule.finrank_mono hle
      _ ≤ ({(1 : ∀ i, Fb i)} : Set (∀ i, Fb i)).toFinset.card := finrank_span_le_card _
      _ = 1 := by simp
  omega

theorem AlgebraicCurve.RegularProlongation.main
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∑ i, genusFF (IsLocalRing.ResidueField A) (Fb i) ≤ genusFF L F := by
  classical
  have : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F := hfd
  have hfdᵢ : ∀ i, FiniteDimensional
      (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) := fun i =>
    RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq
      A Fb R hR f hf htr heq i

  obtain ⟨D, hD⟩ := exists_poleDivisor_of_transcendental f htrL
  have hDbex : ∀ i, ∃ Db : Divisor (IsLocalRing.ResidueField A) (Fb i),
      ∀ w, Db w = max 0 (-w.ord ((R i).residue ⟨f, hf i⟩)) := fun i =>
    exists_poleDivisor_of_transcendental ((R i).residue ⟨f, hf i⟩) (htr i)
  choose Db hDb using hDbex

  have hdegD : Divisor.degree D =
      (Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F : ℤ) :=
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental f htrL D hD
  have hdegDb : ∀ i, Divisor.degree (Db i) =
      (Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i) : ℤ) := fun i =>
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental
      ((R i).residue ⟨f, hf i⟩) (htr i) (Db i) (hDb i)
  have hsumdeg : ∑ i, Divisor.degree (Db i) = Divisor.degree D := by
    simp_rw [hdegDb, hdegD]
    exact_mod_cast congrArg (Nat.cast (R := ℤ)) heq

  obtain ⟨hℓ0F, M₁, -, hRRF⟩ :=
    exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental f htrL D hD
  have hRRᵢ : ∀ i, ∃ Mi : ℕ, 1 ≤ Mi ∧ ∀ N, Mi ≤ N →
        (ell (N • Db i) : ℤ) =
          N * Divisor.degree (Db i) + 1 - genusFF (IsLocalRing.ResidueField A) (Fb i) := fun i =>
    (exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental
      ((R i).residue ⟨f, hf i⟩) (htr i) (Db i) (hDb i)).2
  choose Mᵢ _hMᵢ hRRbᵢ using hRRᵢ

  obtain ⟨M₀, hM₀⟩ := ell_add_card_le
    A Fb R hR f hf htrL hfd htr heq D hD Db hDb

  let M : ℕ := max (max M₀ M₁) (Finset.univ.sup Mᵢ)
  have hM0 : M₀ ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hM1 : M₁ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hMᵢ : ∀ i, Mᵢ i ≤ M := fun i =>
    (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
  have hmain := hM₀ M hM0
  have hmainZ : (ell (M • D) : ℤ) + Fintype.card ι ≤ (∑ i, (ell (M • Db i) : ℤ)) + 1 := by
    exact_mod_cast hmain
  have hlhs : (ell (M • D) : ℤ) = (M : ℤ) * Divisor.degree D + 1 - genusFF L F := hRRF M hM1
  have hrhs : ∑ i, (ell (M • Db i) : ℤ)
      = (M : ℤ) * Divisor.degree D + Fintype.card ι
          - ∑ i, (genusFF (IsLocalRing.ResidueField A) (Fb i) : ℤ) := by
    calc ∑ i, (ell (M • Db i) : ℤ)
        = ∑ i, ((M : ℤ) * Divisor.degree (Db i) + 1
            - genusFF (IsLocalRing.ResidueField A) (Fb i)) :=
          Finset.sum_congr rfl fun i _ => hRRbᵢ i M (hMᵢ i)
      _ = (M : ℤ) * ∑ i, Divisor.degree (Db i) + ∑ i, (1 : ℤ)
            - ∑ i, (genusFF (IsLocalRing.ResidueField A) (Fb i) : ℤ) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (M : ℤ) * Divisor.degree D + Fintype.card ι
            - ∑ i, (genusFF (IsLocalRing.ResidueField A) (Fb i) : ℤ) := by
          rw [hsumdeg]; simp
  rw [hlhs, hrhs] at hmainZ
  have hZ : (∑ i, (genusFF (IsLocalRing.ResidueField A) (Fb i) : ℤ)) ≤ (genusFF L F : ℤ) := by
    linarith
  exact_mod_cast hZ

theorem AlgebraicCurve.RegularProlongation.sum_genusFF_le_of_sum_finrank_eq_of_krullDimLE_one
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    [Ring.KrullDimLE 1 A]
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (htrL : Transcendental L f)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (htr : ∀ i, Transcendental (IsLocalRing.ResidueField A) ((R i).residue ⟨f, hf i⟩))
    (heq : ∑ i, Module.finrank (IntermediateField.adjoin (IsLocalRing.ResidueField A)
        ({(R i).residue ⟨f, hf i⟩} : Set (Fb i))) (Fb i)
      = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F) :
    ∑ i, genusFF (IsLocalRing.ResidueField A) (Fb i) ≤ genusFF L F :=
  AlgebraicCurve.RegularProlongation.main A Fb R hR f hf htrL hfd htr heq

