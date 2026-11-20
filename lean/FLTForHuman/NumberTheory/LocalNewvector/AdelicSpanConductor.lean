/-
  The `p`-adic `K₁` span rows: a fixed vector of `padicK1 q a` inside the `q`-adic orbit span, and
  the newvector conductor bounded by the level's `q`-factorization.

  **The first row.** Let `φ : AdelicGL₂(𝔸_ℚ) → ℂ` be right-invariant under the level-`N₀`
  congruence subgroup `finiteLevelOne (𝓞 ℚ) ℚ (ratLevel N₀)`. For a prime `q` the `q`-adic
  component of `𝔸_ℚ` carries a copy of `GL₂(ℚ_[q])` via `AdelicDock.padicToAdelic q`, so
  `AdelicSpan φ` carries a `GL₂(ℚ_[q])`-action and the compact open subgroup `padicK1 q a` has
  a fixed submodule in it. The row says: if that fixed submodule is nonzero then it contains a
  **nonzero** element of the `q`-adic orbit span
  `span{x • self φ : x ∈ GL₂(ℚ_[q])}` — the fixed vectors are not only inside the `q`-adic span,
  they are produced from `φ` by `q`-adic translates. This is the local input the weight-one lift
  consumes: a nonzero vector fixed by `K₁(qᵃ)` that is visible to the `q`-adic Hecke action.

  The proof is the pin's: compare `padicK1 q a` with the port's `gl2CongruenceSubgroup q (n+a)`
  (`gl2Congr_le_padicK1`), average over the finite quotient `U ⧸ H` of the compact `U = K₁(qᵃ)` by
  the open finite-index `H = Γ ∩ U` (the operator `P`, the "finite-index average"), and check that
  `P` preserves the `q`-adic span and lands in the fixed vectors. The two engines that make the
  average a `ℂ`-linear endomorphism rather than a formal sum are `smul_mem_qSpan` (`qSpan` is
  stable under `GL₂(ℚ_[q])`) and `mem_span_orbit` (every element of `AdelicSpan φ` is already in the
  span of the full adèlic orbit).

  **The second row.** `HasNewvectorConductor q (AdelicSpan φ) c` says the `padicK1 q c`-fixed
  submodule is nonzero while those of `padicK1 q m`, `m < c`, vanish — so `c` is the local
  conductor of the span at `q`. For `φ ≠ 0` of level `N` and `q` prime, the row produces
  `c ≤ N.factorization q` with this property: the level-`N` invariance already fixes
  `AdelicSpan.self φ` under `K₁(q^{N.factorization q})`, and `Nat.find` on the (nonempty, by that
  witness) set of levels with a nonzero fixed submodule gives the least one. Its companion
  `hasNewvectorConductor_zero_of_not_dvd_impl` reads `c = 0` when `q ∤ N`. Together: the local
  conductor at `q` is bounded by the `q`-part of the global level, and is trivial at primes not
  dividing it.

  **Why one module.** Both rows are statements about the same object —
  `fixedSubmodule (padicK1 q n) (AdelicSpan φ)` as a function of the level `n` — and read the same
  level datum `AdelicDock.ratLevel N` through the same bridge
  `AdelicDock.padicToAdelic`/`padicGL_mem_localLevelOne`. The second row's `Nat.find` runs over the
  family whose nonzero-ness the first row's engines produce (`main` consumes exactly the
  hypothesis `fixedSubmodule (padicK1 q a) … ≠ ⊥` that the second row is about), and both close on
  the `mem_fixedSubmodule_iff`/`padic_smul_def`/`toFn_smul` reduction. They are the two rows of one
  silo and the port transcribes them as one module.

  Transcribed from the pins
  `P2M/Sol/S_LocalNewvector_AdelicSpan_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq.lean`
  (589 lines / 16 declarations) and
  `P2M/Sol/S_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization.lean`
  (58 lines / 3 declarations), both pinned `aa2d8b3`. The pin's stage namespaces `Ws50Y`
  (first pin) and `P63DockRows` (second) are flattened away, so the pins' `Ws50Y.main` is `main`
  here and `P63DockRows.exists_hasNewvectorConductor_le_factorization_impl` is
  `exists_hasNewvectorConductor_le_factorization_impl`; the rows keep the pin's own names at
  `LocalNewvector.AdelicSpan.…`.

  spec-pin: P2M/Sol/S_LocalNewvector_AdelicSpan_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq.lean
  spec-pin: P2M/Sol/S_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization.lean

  ## Port deltas

  * **The fifteen engines are public.** The pin declares its engine family `private`; the scaffold
    emits all fifteen at the same statements with no `private` prefix, and the rows then match the
    pin's statements directly. This is deliberate (manager's ruling for SET-AF96): `check_port`
    reads each of the fifteen `ok` against the pin's own copy, the pin declares the same engine
    family public elsewhere in its `S_` files, and the surface gate treats a pin-faithful statement
    as belonging public. Nothing is renamed and no statement is re-spelled.
  * **Stage namespaces flattened.** The pin wraps the first pin's engines and row in `namespace
    Ws50Y` and the second pin's `_impl` pair in `namespace P63DockRows`; both are gone. The names
    the pin writes through them are re-read at the flat names (`main`, the two `_impl`s), and the
    two rows are at their own `LocalNewvector.AdelicSpan.…` names. `check_port` matches all
    nineteen declarations, so the flattening is statement-neutral here.
  * **Imports.** The pin's thirteen `Definitions/…` stub imports plus `P2M.Util` are replaced by
    the port modules that hold the same vocabulary: `AdelicSpan` (the carrier), `ConductorDatum`
    (`fixedSubmodule`, `HasNewvectorConductor`, `congruenceK1_le_integralSubgroup`),
    `GL2CongruenceSubgroup` (the `gl2CongruenceSubgroup` comparison and its open/neighbourhood
    lemmas), `IntegralSubgroupCompact` (`isCompact_coe_integralSubgroup_padic`, which the average
    `P` needs to be a finite sum), `AdelicLevel/Level` and `AdelicDock/LocalEmbedding`. The
    scaffold's `import Mathlib` is replaced by the eighteen specific mathlib modules the file's
    own proofs use (padic integers/norm, `Mathlib.Topology.Algebra.OpenSubgroup` for the open
    subgroup/finite-quotient facts, `QuotientGroup.Basic` and `GroupAction.Quotient` for the
    average, the big-operators and matrix/GL files): the Mathlib olean closure is 6.1 GB against
    7 GB of RAM on this box, so a whole-`Mathlib` import costs ~100 s wall per elaboration and
    pushes the `timeout 100` build gate over its limit. Statement-neutral (a `read`-only change to
    the elaboration environment). No port import was added beyond the scaffold's list.
  * **Sections.** The scaffold's per-declaration `section`s are kept, so each declaration's
    explicit binder list is the pin's and `check_port` hashes the pin's statement text. The pin's
    `section Main` variable block (`Φ`, `q`, `[Fact q.Prime]`) is what the scaffold's sections for
    `qSpan`, `exists_commute`, `smul_mem_qSpan`, `mem_span_orbit`, `sum_smul_comm`, `decomp`,
    `exists_level` and `main` carry.
  * **`end`s are named.** The pin closes its namespaces with bare `end`s; v4.34 requires the name
    (FR-0233), so the module ends `end LocalNewvector` / `end`. Statement-neutral.
  * **No `#print axioms` lines.** The second pin ends with two `#print axioms` commands; they are
    gate instruments, not declarations, and live in `lean/tmp/af96/` probes instead.
  * **`haveI`/`letI` → `have`/`let` in `main`.** At v4.34 the three local instances `main` needs
    (`CompactSpace U`, `Finite (U ⧸ H)`, `Fintype (U ⧸ H)`, plus the quotient `MulAction`) fire
    `linter.style.haveILetI`; they are written `have`/`let` with the same types and values, which
    still serve as instances (the linter's own suggested form). Body-only, statement-neutral; no
    `set_option` and no silencer (FR-0164).
  * **Unused section variables are not parameters.** `mem_span_orbit`, `exists_commute` and
    `sum_smul_comm` do not mention the section's `q` in their own statements (and `exists_commute`
    does not mention `Φ` either), so Lean does not carry those as arguments; the call sites in
    `decomp` are the pin's own `mem_span_orbit Φ ψ`, `exists_commute q h`, `sum_smul_comm Φ c l`.
    Body-only, and no statement moved (`check_port `19 ok` after the edit).

  ## Deferred pin surface

  None: both pins are transcribed in full (19 of 19 declarations), and `move_dead --dry-run`
  reads `0 declarations, 0 lines`.

  ## Gate readings

  - `check_port --force` reads **19 ok, 0 mismatch, 0 missing, 0 own, 0 kw** — the fifteen engines
    plus the two rows of the first pin and the two `_impl`s plus the row of the second.
  - `scaffold_audit` reads **complete**: 4 pin public declarations on the wire, 19 port
    declarations, 0 satisfied by the import closure, 2 rows FOLDED onto `main` /
    `exists_hasNewvectorConductor_le_factorization_impl`.
  - `lake env lean -DautoImplicit=false` is silent (no output at all), ~12–15 s wall; one
    `flock /tmp/flt-build.lock timeout 100 lake build
    FLTForHuman.NumberTheory.LocalNewvector.AdelicSpanConductor` reads
    `Build completed successfully (3478 jobs)` in 39 s (project cap `maxHeartbeats = 4000000`).
  - `#print axioms` on all nineteen declarations — both rows, both `_impl`s and every engine —
    reads `[propext, Classical.choice, Quot.sound]`; no `sorryAx` (probe:
    `lean/tmp/af96/AF96C_probe_axioms.lean`).
  - `dedup.py --within --module AdelicSpanConductor` reads `19 declarations in 1 module(s);
    0 duplicate clusters`.
  - `move_dead.py … --dry-run` reads `AdelicSpanConductor.lean: 0 declarations, 0 lines`.

  ## Heartbeat probe pair (recorded, never installed — FR-0225)

  No `set_option maxHeartbeats` in this module. The probe, run from `lean/`:

    lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/NumberTheory/LocalNewvector/AdelicSpanConductor.lean

  is **silent at `N = 25000`** and **fails at `N/2 = 12500`** with
  `error: (deterministic) timeout at 'isDefEq', maximum number of heartbeats (12500) has been
  reached` at the `mem_span_orbit` proof (at `N/4 = 6250` the same site times out at `whnf`).
  So the file's natural elaboration cost is a little under 25000 heartbeats, ~1/160 of the
  project cap `4000000`. `-DmaxHeartbeats` is honoured by `lake env lean` here (a cap of `1`
  errors immediately), so the pair is a measured bound, not a default.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import FLTForHuman.NumberTheory.LocalNewvector.AdelicSpan
import FLTForHuman.NumberTheory.LocalNewvector.ConductorDatum
import FLTForHuman.RepTheory.LocalNewvector.GL2CongruenceSubgroup
import FLTForHuman.RepTheory.LocalLanglands.IntegralSubgroupCompact
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

namespace LocalNewvector


theorem isOpen_padicK1 (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsOpen ((_root_.LocalNewvector.padicK1 p n : Subgroup (GL (Fin 2) ℚ_[p])) :
      Set (GL (Fin 2) ℚ_[p])) := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hr1 : (p : ℝ) ^ (-(n : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hp1 (by simp)
  apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
  refine Filter.mem_of_superset
    ((FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup p n).mem_nhds
      (SetLike.mem_coe.mpr (one_mem _))) ?_
  intro g hg
  obtain ⟨hg1, hg2⟩ := (FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff p).mp (SetLike.mem_coe.mp hg)

  have hδ : ∀ i j : Fin 2, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := by
    intro i j
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hint : ∀ (A : Matrix (Fin 2) (Fin 2) ℚ_[p]),
      (∀ i j, ‖(A - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) → ∀ i j, ‖A i j‖ ≤ 1 := by
    intro A hA i j
    have h := Padic.nonarchimedean (A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
      ((1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
    rw [sub_add_cancel] at h
    have hA' : ‖A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
      rw [← Matrix.sub_apply]; exact hA i j
    exact h.trans (max_le (hA'.trans hr1) (hδ i j))

  let A : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j =>
    ⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j, hint _ hg1 i j⟩
  let B : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j =>
    ⟨((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j, hint _ hg2 i j⟩
  have hAmap : A.map (algebraMap ℤ_[p] ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    ext i j; rfl
  have hBmap : B.map (algebraMap ℤ_[p] ℚ_[p]) =
      ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    ext i j; rfl
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b hab => by
    exact Subtype.ext (by simpa [PadicInt.algebraMap_apply] using hab)
  have hAB : A * B = 1 := by
    apply Matrix.map_injective hinj
    change (A * B).map (algebraMap ℤ_[p] ℚ_[p]) =
      (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p])
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.mul_inv g
  have hBA : B * A = 1 := by
    apply Matrix.map_injective hinj
    change (B * A).map (algebraMap ℤ_[p] ℚ_[p]) =
      (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p])
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.inv_mul g
  let y : GL (Fin 2) ℤ_[p] := ⟨A, B, hAB, hBA⟩
  have hy : Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p]) y = g :=
    Units.ext hAmap

  have hnorm : ∀ (z : ℤ_[p]), ‖(z : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) →
      z ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) := by
    intro z hz
    exact (PadicInt.norm_le_pow_iff_mem_span_pow z n).mp (by rw [PadicInt.norm_def]; exact hz)
  refine SetLike.mem_coe.mpr (_root_.LocalNewvector.mem_congruenceK1_iff.mpr ⟨y, hy, ?_, ?_⟩)
  · apply hnorm
    have h10 := hg1 1 0
    rwa [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at h10
  · apply hnorm
    have h11 := hg1 1 1
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at h11
    exact h11

theorem gl2Congr_le_padicK1 (p : ℕ) [Fact p.Prime] (n : ℕ) :
    FLT.SmoothVectors.gl2CongruenceSubgroup p n ≤ _root_.LocalNewvector.padicK1 p n := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hr1 : (p : ℝ) ^ (-(n : ℤ)) ≤ 1 := zpow_le_one_of_nonpos₀ hp1 (by simp)
  intro g hg
  obtain ⟨hg1, hg2⟩ := (FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff p).mp hg

  have hδ : ∀ i j : Fin 2, ‖(1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ 1 := by
    intro i j
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [Matrix.one_apply_ne h]
  have hint : ∀ (A : Matrix (Fin 2) (Fin 2) ℚ_[p]),
      (∀ i j, ‖(A - 1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ))) → ∀ i j, ‖A i j‖ ≤ 1 := by
    intro A hA i j
    have h := Padic.nonarchimedean (A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
      ((1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j)
    rw [sub_add_cancel] at h
    have hA' : ‖A i j - (1 : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
      rw [← Matrix.sub_apply]; exact hA i j
    exact h.trans (max_le (hA'.trans hr1) (hδ i j))

  let A : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j =>
    ⟨(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j, hint _ hg1 i j⟩
  let B : Matrix (Fin 2) (Fin 2) ℤ_[p] := fun i j =>
    ⟨((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) i j, hint _ hg2 i j⟩
  have hAmap : A.map (algebraMap ℤ_[p] ℚ_[p]) = (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    ext i j; rfl
  have hBmap : B.map (algebraMap ℤ_[p] ℚ_[p]) =
      ((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    ext i j; rfl
  have hinj : Function.Injective (algebraMap ℤ_[p] ℚ_[p]) := fun a b hab => by
    exact Subtype.ext (by simpa [PadicInt.algebraMap_apply] using hab)
  have hAB : A * B = 1 := by
    apply Matrix.map_injective hinj
    change (A * B).map (algebraMap ℤ_[p] ℚ_[p]) =
      (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p])
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.mul_inv g
  have hBA : B * A = 1 := by
    apply Matrix.map_injective hinj
    change (B * A).map (algebraMap ℤ_[p] ℚ_[p]) =
      (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map (algebraMap ℤ_[p] ℚ_[p])
    rw [Matrix.map_mul, hAmap, hBmap, Matrix.map_one _ (map_zero _) (map_one _)]
    exact Units.inv_mul g
  let y : GL (Fin 2) ℤ_[p] := ⟨A, B, hAB, hBA⟩
  have hy : Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[p] ℚ_[p]) y = g :=
    Units.ext hAmap

  have hnorm : ∀ (z : ℤ_[p]), ‖(z : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) →
      z ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) := by
    intro z hz
    exact (PadicInt.norm_le_pow_iff_mem_span_pow z n).mp (by rw [PadicInt.norm_def]; exact hz)
  refine SetLike.mem_coe.mpr (_root_.LocalNewvector.mem_congruenceK1_iff.mpr ⟨y, hy, ?_, ?_⟩)
  · apply hnorm
    have h10 := hg1 1 0
    rwa [Matrix.sub_apply, Matrix.one_apply_ne (by decide), sub_zero] at h10
  · apply hnorm
    have h11 := hg1 1 1
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at h11
    exact h11

def padicGLinv (q : ℕ) [Fact q.Prime]
    (C : GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) : GL (Fin 2) ℚ_[q] :=
  ⟨(C.val).map (AdelicDock.padicRingEquiv q).symm,
   (C.inv).map (AdelicDock.padicRingEquiv q).symm,
   by rw [← Matrix.map_mul, C.val_inv,
        Matrix.map_one _ (map_zero (AdelicDock.padicRingEquiv q).symm)
          (map_one (AdelicDock.padicRingEquiv q).symm)],
   by rw [← Matrix.map_mul, C.inv_val,
        Matrix.map_one _ (map_zero (AdelicDock.padicRingEquiv q).symm)
          (map_one (AdelicDock.padicRingEquiv q).symm)]⟩

theorem padicGL_padicGLinv (q : ℕ) [Fact q.Prime]
    (y : GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ)) :
    AdelicDock.padicGL q (padicGLinv q y) = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [AdelicDock.padicGL_apply]
  show (AdelicDock.padicRingEquiv q)
      (((y.val).map (AdelicDock.padicRingEquiv q).symm) i j) = y.val i j
  rw [Matrix.map_apply]
  exact (AdelicDock.padicRingEquiv q).apply_symm_apply _

theorem aux_conj_padicToAdelic (q : ℕ) [Fact q.Prime]
    (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∃ g₀ : GL (Fin 2) ℚ_[q], ∀ k,
      AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹) * x = x * AdelicDock.padicToAdelic q k := by

  refine ⟨padicGLinv q (AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
    (AdelicLevel.glFin (𝓞 ℚ) ℚ x)), fun k => ?_⟩
  set xq : GL (Fin 2) ((AdelicDock.padicPlace q).adicCompletion ℚ) :=
    AdelicLevel.finComponent (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)
      (AdelicLevel.glFin (𝓞 ℚ) ℚ x)
  set g₀ : GL (Fin 2) ℚ_[q] := padicGLinv q xq with hg₀

  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 ℚ) ℚ ?harch ?hfin
  case harch =>

    rw [RingHom.map_mul, RingHom.map_mul]
    have hM1 : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹)).val) = 1 := by
      have := AdelicDock.glArch_padicToAdelic q (g₀ * k * g₀⁻¹)
      calc (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
            (AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹)).val
          = (AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹))).val := rfl
        _ = 1 := by rw [this, Units.val_one]
    have hM2 : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((AdelicDock.padicToAdelic q k).val) = 1 := by
      have := AdelicDock.glArch_padicToAdelic q k
      calc (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (AdelicDock.padicToAdelic q k).val
          = (AdelicLevel.glArch (𝓞 ℚ) ℚ (AdelicDock.padicToAdelic q k)).val := rfl
        _ = 1 := by rw [this, Units.val_one]
    rw [hM1, hM2, one_mul, mul_one]
  case hfin =>
    rw [RingHom.map_mul, RingHom.map_mul]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 ℚ) ℚ fun w => ?_
    rw [RingHom.map_mul, RingHom.map_mul]

    have hL : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
            (AdelicDock.padicToAdelic q (g₀ * k * g₀⁻¹)).val)
        = (AdelicLevel.finComponent (𝓞 ℚ) ℚ w
            (AdelicDock.padicToFinAdelic q (g₀ * k * g₀⁻¹))).val := by
      rw [AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat,
        AdelicDock.padicToFinAdelic_apply]; rfl
    have hR : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ w).mapMatrix
          ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (AdelicDock.padicToAdelic q k).val)
        = (AdelicLevel.finComponent (𝓞 ℚ) ℚ w (AdelicDock.padicToFinAdelic q k)).val := by
      rw [AdelicDock.padicToAdelic_apply, AdelicDock.coe_finEmbed, AdelicDock.mapMatrix_fin_finMat,
        AdelicDock.padicToFinAdelic_apply]; rfl
    rw [hL, hR]
    by_cases hw : w = AdelicDock.padicPlace q
    · subst hw

      rw [AdelicDock.finComponent_padicToFinAdelic_self,
        AdelicDock.finComponent_padicToFinAdelic_self]
      have hxw : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ (AdelicDock.padicPlace q)).mapMatrix
            ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix x.val) = xq.val := rfl
      rw [hxw, ← Units.val_mul, ← Units.val_mul]
      congr 1
      rw [map_mul, map_mul, map_inv, hg₀, padicGL_padicGLinv, inv_mul_cancel_right]
    ·
      rw [AdelicDock.finComponent_padicToFinAdelic_of_ne q _ hw,
        AdelicDock.finComponent_padicToFinAdelic_of_ne q k hw,
        Units.val_one, one_mul, mul_one]

theorem aux_generator_smooth (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) {N₀ : ℕ} (hN₀ : N₀ ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.ratLevel N₀),
      ∀ x, Φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ g) = Φ x)
    (q : ℕ) [Fact q.Prime]
    (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧
      ∀ u ∈ U, (AdelicDock.padicToAdelic q u :
          AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) •
          (x • _root_.LocalNewvector.AdelicFnCarrier.mk Φ) =
        x • _root_.LocalNewvector.AdelicFnCarrier.mk Φ := by
  obtain ⟨g₀, hconj⟩ := aux_conj_padicToAdelic q x
  have hself : ∀ k ∈ _root_.LocalNewvector.padicK1 q (N₀.factorization q),
      (AdelicDock.padicToAdelic q k :
        AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) •
        _root_.LocalNewvector.AdelicFnCarrier.mk Φ = _root_.LocalNewvector.AdelicFnCarrier.mk Φ := by
    intro k hk
    have hlev1 := AdelicDock.padicToAdelic_mem_levelOne q hN₀ le_rfl hk
    have hfin : AdelicDock.padicToFinAdelic q k ∈
        NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ
          (AdelicDock.ratLevel N₀) := by
      have h1 := NumberField.AdelicLevel.mem_levelOne_iff.mp hlev1
      rwa [AdelicDock.glFin_padicToAdelic] at h1
    apply _root_.LocalNewvector.AdelicFnCarrier.ext
    intro y
    rw [_root_.LocalNewvector.AdelicFnCarrier.toFn_smul,
      _root_.LocalNewvector.AdelicFnCarrier.toFn_mk, AdelicDock.padicToAdelic_apply]
    exact hlev _ hfin y
  refine ⟨(_root_.LocalNewvector.padicK1 q (N₀.factorization q)).map
      (MulAut.conj g₀).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    have hfun : ⇑(MulAut.conj g₀).toMonoidHom =
        ⇑((Homeomorph.mulRight g₀⁻¹).trans (Homeomorph.mulLeft g₀)) := by
      funext u
      simp [MulAut.conj_apply, mul_assoc]
    rw [hfun]
    exact ((Homeomorph.mulRight g₀⁻¹).trans (Homeomorph.mulLeft g₀)).isOpenMap _
      (isOpen_padicK1 q (N₀.factorization q))
  · rintro u ⟨k, hk, rfl⟩
    have hc : (MulAut.conj g₀).toMonoidHom k = g₀ * k * g₀⁻¹ := rfl
    rw [hc, smul_smul, hconj k, ← smul_smul, hself k hk]

theorem aux_span_smooth (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) {N₀ : ℕ} (hN₀ : N₀ ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.ratLevel N₀),
      ∀ x, Φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ g) = Φ x)
    (q : ℕ) [Fact q.Prime] :
    ∀ w ∈ (⊤ : Submodule ℂ (_root_.LocalNewvector.AdelicSpan Φ)),
      ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧
        ∀ u ∈ U, u • w = w := by
  intro w _
  have key : ∀ ψ : _root_.LocalNewvector.AdelicFnCarrier ℚ,
      ψ ∈ _root_.LocalNewvector.AdelicSpanSubmodule Φ →
      ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧
        ∀ u ∈ U, (AdelicDock.padicToAdelic q u :
            AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) • ψ = ψ := by
    intro ψ hψ
    refine Submodule.span_induction
      (fun ψ' hmem => ?_) ?_ (fun ψ₁ ψ₂ _ _ ih₁ ih₂ => ?_) (fun c ψ' _ ih => ?_) hψ
    · obtain ⟨x, rfl⟩ := hmem
      exact aux_generator_smooth Φ hN₀ hlev q x
    · exact ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun u _ => smul_zero _⟩
    · obtain ⟨U₁, hU₁o, hU₁⟩ := ih₁
      obtain ⟨U₂, hU₂o, hU₂⟩ := ih₂
      refine ⟨U₁ ⊓ U₂, ?_, fun u hu => ?_⟩
      · rw [Subgroup.coe_inf]
        exact hU₁o.inter hU₂o
      · obtain ⟨h₁, h₂⟩ := Subgroup.mem_inf.mp hu
        rw [smul_add, hU₁ u h₁, hU₂ u h₂]
    · obtain ⟨U, hUo, hU⟩ := ih
      exact ⟨U, hUo, fun u hu => by rw [smul_comm, hU u hu]⟩
  obtain ⟨U, hUo, hU⟩ :=
    key (_root_.LocalNewvector.AdelicSpan.toFn Φ w)
      (w : _root_.LocalNewvector.AdelicSpanSubmodule Φ).2
  refine ⟨U, hUo, fun u hu => ?_⟩
  apply _root_.LocalNewvector.AdelicSpan.ext
  rw [_root_.LocalNewvector.AdelicSpan.padic_smul_def,
    _root_.LocalNewvector.AdelicSpan.toFn_smul]
  exact hU u hu

section
variable (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime]

abbrev qSpan : Submodule ℂ (_root_.LocalNewvector.AdelicSpan Φ) :=
  Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • _root_.LocalNewvector.AdelicSpan.self Φ)

end

section
variable (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime]

theorem exists_commute (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∃ g₀ : GL (Fin 2) ℚ_[q], ∀ k : GL (Fin 2) ℚ_[q],
      x * (AdelicDock.padicToAdelic q g₀)⁻¹ * AdelicDock.padicToAdelic q k =
        AdelicDock.padicToAdelic q k * (x * (AdelicDock.padicToAdelic q g₀)⁻¹) := by
  obtain ⟨g₀, h⟩ := aux_conj_padicToAdelic q x
  refine ⟨g₀, fun k => ?_⟩
  have h1 := h (g₀⁻¹ * k * g₀)
  have e : g₀ * (g₀⁻¹ * k * g₀) * g₀⁻¹ = k := by group
  rw [e] at h1
  simp only [map_mul, map_inv] at h1
  calc x * (AdelicDock.padicToAdelic q g₀)⁻¹ * AdelicDock.padicToAdelic q k
      = x * ((AdelicDock.padicToAdelic q g₀)⁻¹ * AdelicDock.padicToAdelic q k *
          AdelicDock.padicToAdelic q g₀) * (AdelicDock.padicToAdelic q g₀)⁻¹ := by group
    _ = AdelicDock.padicToAdelic q k * x * (AdelicDock.padicToAdelic q g₀)⁻¹ := by rw [← h1]
    _ = AdelicDock.padicToAdelic q k * (x * (AdelicDock.padicToAdelic q g₀)⁻¹) := by group

end

section
variable (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime]

theorem smul_mem_qSpan (x : GL (Fin 2) ℚ_[q]) {w : _root_.LocalNewvector.AdelicSpan Φ}
    (hw : w ∈ qSpan Φ q) : x • w ∈ qSpan Φ q := by
  refine Submodule.span_induction (p := fun w _ => x • w ∈ qSpan Φ q) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨x', rfl⟩
    exact Submodule.subset_span ⟨x * x', by simp only [mul_smul]⟩
  · simp only [smul_zero]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [smul_comm]; exact Submodule.smul_mem _ c ha

end

section
variable (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime]

theorem mem_span_orbit (ψ : _root_.LocalNewvector.AdelicSpan Φ) :
    ψ ∈ Submodule.span ℂ (Set.range fun h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ =>
      h • _root_.LocalNewvector.AdelicSpan.self Φ) := by
  let incl : _root_.LocalNewvector.AdelicSpan Φ →ₗ[ℂ] _root_.LocalNewvector.AdelicFnCarrier ℚ :=
    { toFun := _root_.LocalNewvector.AdelicSpan.toFn Φ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective incl := by
    intro a b h
    apply _root_.LocalNewvector.AdelicSpan.ext
    exact h
  set S := Submodule.span ℂ (Set.range fun h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ =>
      h • _root_.LocalNewvector.AdelicSpan.self Φ) with hS
  have himage : _root_.LocalNewvector.AdelicSpanSubmodule Φ ≤ Submodule.map incl S := by
    rw [hS, Submodule.map_span]
    unfold _root_.LocalNewvector.AdelicSpanSubmodule
    apply Submodule.span_mono
    rintro ψ' ⟨h, rfl⟩
    refine ⟨h • _root_.LocalNewvector.AdelicSpan.self Φ, ⟨h, rfl⟩, ?_⟩
    show _root_.LocalNewvector.AdelicSpan.toFn Φ (h • _root_.LocalNewvector.AdelicSpan.self Φ) = _
    rw [_root_.LocalNewvector.AdelicSpan.toFn_smul, _root_.LocalNewvector.AdelicSpan.toFn_self]
  have hψ : incl ψ ∈ Submodule.map incl S :=
    himage (ψ : _root_.LocalNewvector.AdelicSpanSubmodule Φ).2
  obtain ⟨s, hs, hsi⟩ := Submodule.mem_map.mp hψ
  exact hinj hsi ▸ hs

end

section
variable (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime]

theorem sum_smul_comm (c : ℂ)
    (l : List (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ × _root_.LocalNewvector.AdelicSpan Φ)) :
    ((l.map fun p => (p.1, c • p.2)).map fun p => p.1 • p.2).sum = c • (l.map fun p => p.1 • p.2).sum := by
  induction l with
  | nil => simp
  | cons p t ih =>
    simp only [List.map_cons, List.sum_cons, smul_add, ih]
    rw [smul_comm p.1 c p.2]

end

section
variable (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime]

theorem decomp (ψ : _root_.LocalNewvector.AdelicSpan Φ) :
    ∃ l : List (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ × _root_.LocalNewvector.AdelicSpan Φ),
      (∀ p ∈ l, (∀ k : GL (Fin 2) ℚ_[q],
          p.1 * AdelicDock.padicToAdelic q k = AdelicDock.padicToAdelic q k * p.1) ∧ p.2 ∈ qSpan Φ q) ∧
      (l.map fun p => p.1 • p.2).sum = ψ := by
  refine Submodule.span_induction
    (p := fun ψ _ => ∃ l : List (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ ×
        _root_.LocalNewvector.AdelicSpan Φ),
      (∀ p ∈ l, (∀ k : GL (Fin 2) ℚ_[q],
          p.1 * AdelicDock.padicToAdelic q k = AdelicDock.padicToAdelic q k * p.1) ∧ p.2 ∈ qSpan Φ q) ∧
      (l.map fun p => p.1 • p.2).sum = ψ) ?_ ?_ ?_ ?_ (mem_span_orbit Φ ψ)
  · rintro _ ⟨h, rfl⟩
    obtain ⟨g₀, hcomm⟩ := exists_commute q h
    refine ⟨[(h * (AdelicDock.padicToAdelic q g₀)⁻¹, g₀ • _root_.LocalNewvector.AdelicSpan.self Φ)], ?_, ?_⟩
    · intro p hp
      rw [List.mem_singleton] at hp
      subst hp
      exact ⟨hcomm, Submodule.subset_span ⟨g₀, rfl⟩⟩
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [_root_.LocalNewvector.AdelicSpan.padic_smul_def, ← mul_smul, inv_mul_cancel_right]
  · exact ⟨[], fun p hp => absurd hp List.not_mem_nil, rfl⟩
  · rintro a b _ _ ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
    refine ⟨l₁ ++ l₂, fun p hp => ?_, by rw [List.map_append, List.sum_append]⟩
    rcases List.mem_append.mp hp with hp | hp
    exacts [h₁ p hp, h₂ p hp]
  · rintro c a _ ⟨l, hl, rfl⟩
    refine ⟨l.map fun p => (p.1, c • p.2), fun p hp => ?_, sum_smul_comm Φ c l⟩
    obtain ⟨p', hp', rfl⟩ := List.mem_map.mp hp
    exact ⟨(hl p' hp').1, Submodule.smul_mem _ c (hl p' hp').2⟩

end

section
variable (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime]

theorem exists_level {N₀ : ℕ} (hN₀ : N₀ ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.ratLevel N₀),
      ∀ x, Φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ g) = Φ x)
    (l : List (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ × _root_.LocalNewvector.AdelicSpan Φ)) :
    ∃ n : ℕ, ∀ p ∈ l, ∀ γ ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q n, γ • p.2 = p.2 := by
  have key : ∃ U : Subgroup (GL (Fin 2) ℚ_[q]), IsOpen (U : Set (GL (Fin 2) ℚ_[q])) ∧
      ∀ p ∈ l, ∀ u ∈ U, u • p.2 = p.2 := by
    induction l with
    | nil =>
      exact ⟨⊤, by rw [Subgroup.coe_top]; exact isOpen_univ, fun p hp => absurd hp List.not_mem_nil⟩
    | cons p t ih =>
      obtain ⟨U₁, hU₁o, hU₁⟩ := ih
      obtain ⟨U₂, hU₂o, hU₂⟩ := aux_span_smooth Φ hN₀ hlev q p.2 Submodule.mem_top
      refine ⟨U₁ ⊓ U₂, by rw [Subgroup.coe_inf]; exact hU₁o.inter hU₂o, fun p' hp' u hu => ?_⟩
      obtain ⟨h₁, h₂⟩ := Subgroup.mem_inf.mp hu
      rcases List.mem_cons.mp hp' with rfl | hp'
      · exact hU₂ u h₂
      · exact hU₁ p' hp' u h₁
  obtain ⟨U, hUo, hU⟩ := key
  obtain ⟨n, hn⟩ := FLT.SmoothVectors.exists_gl2CongruenceSubgroup_subset_of_mem_nhds_one q
    (hUo.mem_nhds (SetLike.mem_coe.mpr (one_mem U)))
  exact ⟨n, fun p hp γ hγ => hU p hp γ (hn hγ)⟩

end

section
variable (Φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (q : ℕ) [Fact q.Prime]

theorem main {N₀ : ℕ} (hN₀ : N₀ ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.ratLevel N₀),
      ∀ x, Φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ g) = Φ x) (a : ℕ)
    (hfix : _root_.LocalNewvector.fixedSubmodule (_root_.LocalNewvector.padicK1 q a)
      (_root_.LocalNewvector.AdelicSpan Φ) ≠ ⊥) :
    ∃ y : _root_.LocalNewvector.AdelicSpan Φ,
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • _root_.LocalNewvector.AdelicSpan.self Φ) ∧
      y ≠ 0 ∧
      y ∈ _root_.LocalNewvector.fixedSubmodule (_root_.LocalNewvector.padicK1 q a)
        (_root_.LocalNewvector.AdelicSpan Φ) := by
  classical
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hfix
  have hvU : ∀ k ∈ _root_.LocalNewvector.padicK1 q a, k • v = v :=
    _root_.LocalNewvector.mem_fixedSubmodule_iff.mp hv
  obtain ⟨l, hl, hsum⟩ := decomp Φ q v
  obtain ⟨n, hn⟩ := exists_level Φ q hN₀ hlev l

  set U : Subgroup (GL (Fin 2) ℚ_[q]) := _root_.LocalNewvector.padicK1 q a with hUdef
  set Γ : Subgroup (GL (Fin 2) ℚ_[q]) := FLT.SmoothVectors.gl2CongruenceSubgroup q (n + a) with hΓdef
  have hΓn : Γ ≤ FLT.SmoothVectors.gl2CongruenceSubgroup q n :=
    FLT.SmoothVectors.gl2CongruenceSubgroup_antitone q (Nat.le_add_right n a)
  have hΓU : Γ ≤ U :=
    (FLT.SmoothVectors.gl2CongruenceSubgroup_antitone q (Nat.le_add_left a n)).trans (gl2Congr_le_padicK1 q a)
  have hΓw : ∀ p ∈ l, ∀ γ ∈ Γ, γ • p.2 = p.2 := fun p hp γ hγ => hn p hp γ (hΓn hγ)
  set H : Subgroup U := Γ.subgroupOf U with hHdef

  have hUc : CompactSpace U := by
    refine isCompact_iff_compactSpace.mp ?_
    refine (FLT.SpectralSide.isCompact_coe_integralSubgroup_padic q).of_isClosed_subset
      (U.isClosed_of_isOpen (isOpen_padicK1 q a)) ?_
    intro x hx
    exact _root_.LocalNewvector.congruenceK1_le_integralSubgroup ((q : ℤ_[q])) a hx
  have hHo : IsOpen (H : Set U) := by
    rw [hHdef, Subgroup.coe_subgroupOf, Subgroup.coe_subtype]
    exact (FLT.SmoothVectors.isOpen_coe_gl2CongruenceSubgroup q (n + a)).preimage continuous_subtype_val
  have : Finite (U ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  let : Fintype (U ⧸ H) := Fintype.ofFinite _
  let instQuotAct : MulAction U (U ⧸ H) := MulAction.quotient U H

  let P : _root_.LocalNewvector.AdelicSpan Φ →+ _root_.LocalNewvector.AdelicSpan Φ :=
    ∑ c : U ⧸ H, DistribSMul.toAddMonoidHom (_root_.LocalNewvector.AdelicSpan Φ)
      ((Quotient.out c : U) : GL (Fin 2) ℚ_[q])
  have P_apply : ∀ u : _root_.LocalNewvector.AdelicSpan Φ,
      P u = ∑ c : U ⧸ H, ((Quotient.out c : U) : GL (Fin 2) ℚ_[q]) • u := by
    intro u
    simp only [P, AddMonoidHom.finsetSum_apply, DistribSMul.toAddMonoidHom_apply]

  have P_fixed : ∀ u : _root_.LocalNewvector.AdelicSpan Φ, (∀ γ ∈ Γ, γ • u = u) →
      ∀ k ∈ U, k • P u = P u := by
    intro u hu k hk
    rw [P_apply, Finset.smul_sum]

    have step : ∀ c : U ⧸ H,
        k • (((Quotient.out c : U) : GL (Fin 2) ℚ_[q]) • u) =
          ((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]) • u := by
      intro c
      have hrel : (Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U)⁻¹ * ((⟨k, hk⟩ : U) * Quotient.out c) ∈ H := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
      have hγ : (((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]))⁻¹ *
          (k * ((Quotient.out c : U) : GL (Fin 2) ℚ_[q])) ∈ Γ := by
        have h2 := Subgroup.mem_subgroupOf.mp hrel
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] using h2
      calc k • (((Quotient.out c : U) : GL (Fin 2) ℚ_[q]) • u)
          = (k * ((Quotient.out c : U) : GL (Fin 2) ℚ_[q])) • u := by rw [← mul_smul]
        _ = (((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]) *
              ((((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]))⁻¹ *
                (k * ((Quotient.out c : U) : GL (Fin 2) ℚ_[q])))) • u := by rw [mul_inv_cancel_left]
        _ = ((Quotient.out (((⟨k, hk⟩ : U) • c : U ⧸ H)) : U) : GL (Fin 2) ℚ_[q]) • u := by rw [mul_smul, hu _ hγ]
    rw [Finset.sum_congr rfl fun c _ => step c]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : U)) _ _ fun c => rfl

  have P_self : P v = (Fintype.card (U ⧸ H)) • v := by
    rw [P_apply]
    have : ∀ c : U ⧸ H, ((Quotient.out c : U) : GL (Fin 2) ℚ_[q]) • v = v :=
      fun c => hvU _ (Quotient.out c : U).2
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_const, Finset.card_univ]

  have P_comm : ∀ (b : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
      (w : _root_.LocalNewvector.AdelicSpan Φ),
      (∀ k : GL (Fin 2) ℚ_[q], b * AdelicDock.padicToAdelic q k = AdelicDock.padicToAdelic q k * b) →
      P (b • w) = b • P w := by
    intro b w hb
    rw [P_apply, P_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [_root_.LocalNewvector.AdelicSpan.padic_smul_def, _root_.LocalNewvector.AdelicSpan.padic_smul_def,
      ← mul_smul, ← hb, mul_smul]

  have P_qSpan : ∀ w ∈ qSpan Φ q, P w ∈ qSpan Φ q := by
    intro w hw
    rw [P_apply]
    exact Submodule.sum_mem _ fun c _ => smul_mem_qSpan Φ q _ hw

  have hPv : P v ≠ 0 := by
    rw [P_self, ← Nat.cast_smul_eq_nsmul ℂ]
    intro h0
    apply hv0
    have hN : (Fintype.card (U ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    calc v = ((Fintype.card (U ⧸ H) : ℂ)⁻¹ * (Fintype.card (U ⧸ H) : ℂ)) • v := by
            rw [inv_mul_cancel₀ hN, one_smul]
      _ = 0 := by rw [mul_smul, h0, smul_zero]
  have hPsum : P v = (l.map fun p => p.1 • P p.2).sum := by
    rw [← hsum, map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun p hp => ?_
    simp only [Function.comp_apply]
    exact P_comm p.1 p.2 (hl p hp).1

  have hex : ∃ p ∈ l, P p.2 ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hPv
    rw [hPsum]
    have : (l.map fun p => p.1 • P p.2) = l.map fun _ => (0 : _root_.LocalNewvector.AdelicSpan Φ) := by
      refine List.map_congr_left fun p hp => ?_
      rw [hall p hp, smul_zero]
    rw [this, List.map_const', List.sum_replicate, smul_zero]
  obtain ⟨p, hp, hPp⟩ := hex
  refine ⟨P p.2, P_qSpan p.2 (hl p hp).2, hPp, ?_⟩
  exact _root_.LocalNewvector.mem_fixedSubmodule_iff.mpr (P_fixed p.2 (hΓw p hp))

end

theorem exists_hasNewvectorConductor_le_factorization_impl (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x, φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℕ, c ≤ N.factorization p ∧ LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) c := by
  classical
  have hfix : LocalNewvector.AdelicSpan.self φ ∈
      LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p (N.factorization p)) (LocalNewvector.AdelicSpan φ) := by
    rw [LocalNewvector.mem_fixedSubmodule_iff]
    intro k hk
    rw [LocalNewvector.AdelicSpan.padic_smul_def]
    apply LocalNewvector.AdelicSpan.ext
    rw [LocalNewvector.AdelicSpan.toFn_smul, LocalNewvector.AdelicSpan.toFn_self]
    apply LocalNewvector.AdelicFnCarrier.ext
    intro x
    rw [LocalNewvector.AdelicFnCarrier.toFn_smul, LocalNewvector.AdelicFnCarrier.toFn_mk]
    exact hlev _ ((AdelicDock.localEmbed_mem_finiteLevelOne_iff _ _ _ _).mpr
      (AdelicDock.padicGL_mem_localLevelOne p hN le_rfl hk)) x
  have hne : ∃ n, LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p n) (LocalNewvector.AdelicSpan φ) ≠ ⊥ :=
    ⟨N.factorization p, fun hbot => LocalNewvector.AdelicSpan.self_ne_zero_of_ne_zero φ hφ
      ((Submodule.mem_bot ℂ).mp (hbot ▸ hfix))⟩
  refine ⟨Nat.find hne, Nat.find_min' hne ?_, Nat.find_spec hne, fun m hm => ?_⟩
  · exact fun hbot => LocalNewvector.AdelicSpan.self_ne_zero_of_ne_zero φ hφ ((Submodule.mem_bot ℂ).mp (hbot ▸ hfix))
  · by_contra hmb
    exact Nat.find_min hne hm hmb

theorem hasNewvectorConductor_zero_of_not_dvd_impl (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ x, φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ N) :
    LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) 0 := by
  obtain ⟨c, hc, h⟩ := exists_hasNewvectorConductor_le_factorization_impl φ hφ hN hlev p
  rw [Nat.factorization_eq_zero_of_not_dvd hp, Nat.le_zero] at hc
  exact hc ▸ h

theorem AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
    (φ : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ → ℂ) {N₀ : ℕ} (hN₀ : N₀ ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (𝓞 ℚ) ℚ (AdelicDock.ratLevel N₀),
      ∀ x, φ (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ g) = φ x)
    (q : ℕ) [Fact q.Prime] (a : ℕ)
    (hfix : LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.AdelicSpan φ) ≠ ⊥) :
    ∃ y : LocalNewvector.AdelicSpan φ,
      y ∈ Submodule.span ℂ
        (Set.range fun x : GL (Fin 2) ℚ_[q] => x • LocalNewvector.AdelicSpan.self φ) ∧
      y ≠ 0 ∧
      y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q a) (LocalNewvector.AdelicSpan φ) :=
  main φ q hN₀ hlev a hfix

theorem AdelicSpan.exists_hasNewvectorConductor_le_factorization
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℕ, c ≤ N.factorization p ∧
      LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) c := by
  exact exists_hasNewvectorConductor_le_factorization_impl φ hφ hN hlev p

end LocalNewvector

end
