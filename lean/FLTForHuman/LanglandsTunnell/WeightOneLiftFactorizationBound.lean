/-
  The conductor bound of the weight-one lift: a `padicK1`-fixed vector in the
  `p`-adic span forces `N.factorization q ≤ m`.

  spec-pin: P2M/Sol/S_DihedralWeightOne_factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1.lean
  spec-pin: P2M/Sol/S_DihedralWeightOne_hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne.lean

  The second row.  `hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm`
  (pin `P2M/Sol/S_…hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm.lean`,
  SET-AF98F) states what the first row is *for*: for a primitive `f` and a prime `q`, the local
  newvector conductor of `AdelicSpan (weightOneLift (N) f)` at `q` is exactly
  `N.factorization q`.  The pin is a 41-line file with one declaration, and it is a two-line
  corollary of this module's own first row plus three imported premises: `≤` is
  `LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization`; `≥` is the `exfalso`
  branch — a strictly smaller conductor `c < N.factorization q` would give a nonzero
  `padicK1 q c`-fixed vector in the `q`-adic span
  (`LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq`)
  and then `N.factorization q ≤ c` by
  `factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1`.  Its two new imports
  are `NumberTheory/LocalNewvector/AdelicSpanConductor.lean` (the two `AdelicSpan` rows) and
  `LanglandsTunnell/WeightOneLiftCuspidalRealization.lean`
  (`weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm`); neither imports this
  module, and no public name is shared between them and it, so the additions are cycle- and
  clash-free.

  The row.  Let `N ≥ 1`, `ψ` a Dirichlet character mod `N`, `f` a primitive cusp form of
  weight one on `Γ₁(N)` with Nebentypus `ψ`, `q` a prime and `m ≥ 0`.  If `y ≠ 0` lies in the
  `ℂ`-span of the `GL₂(ℚ_q)`-orbit of `AdelicSpan.self (weightOneLift (N) f)` and is fixed by
  the level-`m` congruence subgroup `padicK1 q m`, then `N.factorization q ≤ m`.  The span is
  the `q`-adic one: `x • AdelicSpan.self Φ` is `g ↦ Φ (g * padicToAdelic q x)`
  (`fn_padic_smul_self`), so the hypothesis only ever sees the `q`-place of the adèle.

  Why it holds.  `factorization_le_of_mem_span_weightOneLift` runs the contradiction for a
  general level `M`; the row is its instance `M := N` (`solution`, pin `:910`).  Assume
  `m < M.factorization q` and put `n = M.factorization q`, `M' = M / q ^ n` and
  `N₀ = q ^ m * M'`.  Then `q ^ n * M' = M`, so `N₀ ∣ M` with `N₀ ≠ M`, `N₀.factorization q = m`
  (`level_ne_zero`, `factorization_level_self`) and `N₀.factorization ℓ = M.factorization ℓ`
  at every other prime (`factorization_level_of_ne`) — hence `ratLevel N₀` and `ratLevel M`
  have the same ideal bound away from `q` (`idealBound_ratLevel_eq_of_factorization_eq`).

  On that level, `fn_mul_finEmbed_eq_inv_mul` is the Nebentypus relation
  `fn y (z * finEmbed u) = ψ (d)⁻¹ * fn y z` for every `u` of level `N₀` whose `(1,1)` entry is
  `d` mod the `N₀`-ball with `d` a `q`-adic unit.  Its proof splits `u` at `q` into
  `centralGL t * k` with `t = d` and `k ∈ padicK1 q m` (`exists_finComponent_eq_centralGL_mul_of_sub_mem`),
  moves `k` past `z` by `hfix` and `centralGL_mul_comm`, and calls
  `fn_mul_finEmbed_eq_of_qcentral` on the level-`M` part, which `mul_padicToFinAdelic_inv_mem_finiteLevelZero`
  transports from level `N₀` to level `M` using the away-from-`q` agreement of the bounds.
  Restricting to `e ≡ 1 (mod N₀)` — so that `e` is a unit at `q` and `d = e` — gives
  `ψ (e) = 1` (`apply_eq_one_of_natCast_eq_one`: the relation at `d = e` and at `d = 1`,
  applied to a `z` with `fn y z ≠ 0` from `exists_fn_ne_zero`, then cancelled).

  That kernel statement descends `ψ` to a character `ψ'` mod `N₀` agreeing with `ψ` on
  integers coprime to `M` (`exists_dirichletCharacter_of_dvd`: the kernel of
  `ZMod.unitsMap` lies in that of `ψ`, and `unitsMap` is surjective).  Adding multiples of
  `N₀` stays inside the `N₀`-ball (`algebraMap_natCast_mul_mem_idealBall`), so the relation
  upgrades to every `d` coprime to `N₀` (`hK0'`), and the prelude's
  `exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul` produces
  a nonzero `F` of level `Γ₁(N₀)` with `HasNebentypus ψ' F` and `fn y = weightOneLift F`.  So
  `h` is an eigenpacket occurring at the proper divisor `N₀` of `M`, contradicting primitivity
  (`hh.not_eigenpacketOccursAt`); the eigenvalues match because for `p ∤ q * M` the Hecke
  eigenrelations of `h` and of `F` agree once `ψ' (p) = ψ (p)` is substituted.  The `p`-adic
  translate sum of that last step is `sum_fn_eq_of_mem_span`, run on the `p + 1`
  representatives `repZ'`/`ρQ'` of `GL₂(ℤ_[p])` modulo the level-one subgroup and fed to the
  prelude's `qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq`.

  The engines.  Four blocks, kept at the pin's names:

  * the `DescentSupportB` level arithmetic — `exists_padicGL_map_eq_finComponent` (integrality
    of `u` at every place gives a `GL₂(ℤ_[q])` model at `q`), `map_algebraMap_scalar_eq_centralGL`,
    `isLevelZeroMatrix_of_finComponent_eq_and` and `mul_padicToFinAdelic_inv_mem_finiteLevelZero`
    (re-levelling a level-`N₀` adèle whose `q`-component is a given `c`);
  * `LevelVector` — the level arithmetic above, `centralGL_mul_comm`, `centralGL_apply_one_one`,
    `isUnit_of_sub_mem` (a `q`-adically integral entry congruent to a unit is a unit),
    `padicToFinAdelic_centralGL_mem_finiteLevelZero`, the `centralGL * padicK1` decomposition
    `exists_finComponent_eq_centralGL_mul_of_sub_mem`, and the two engine steps
    `fn_mul_finEmbed_eq_of_qcentral` / `fn_mul_finEmbed_eq_inv_mul`;
  * `CasselmanBound` — `exists_dirichletCharacter_of_dvd`, the `dvd`-descent of `ψ`, with
    `algebraMap_natCast_mul_mem_idealBall`; the totient and Dirichlet-character facts
    (`dirichlet_pow_totient`, `totient_ne_zero`, `dirichlet_ne_zero`) are imported;
  * `LevelVector.WeightOne` — `factorization_le_of_mem_span_weightOneLift`, the contradiction
    itself, which the row calls.

  ## Port deltas

  - **Imports substituted for pin declarations.**  Eighteen of the pin's 48 declarations are
    imported, not re-declared (the manager promoted them for this order):
    `coe_finComponent`, `glEq_of_forall_finComponent_eq`, `commute_of_finComponent_eq_one`,
    `mapMatrix_injective`, `exists_glMap_eq` (the pin's `DescentSupportA`) from
    `LanglandsTunnell/WeightOneLiftQCoeffConverse`; `fn`, `fn_add`, `fn_csmul`, `fn_zero` (the
    pin's `DescentEngine`) from `LanglandsTunnell/WeightOneLiftNebentypusExists`;
    `natGenerator_padicPlace`, `eq_padicPlace_natGenerator`, `padicPlace_injective`,
    `valued_natCast_eq_of_factorization_eq`, `idealBound_ratLevel_eq_of_factorization_eq`,
    `algebraMap_intCast_apply_padicPlace_eq` (the pin's `DescentSupportB`) from
    `LanglandsTunnell/WeightOneLiftLevel`; `dirichlet_pow_totient`, `totient_ne_zero`,
    `dirichlet_ne_zero` (the pin's `CasselmanBound`) from `LanglandsTunnell/WeightOneLiftQCoeffConverse`.
    All eighteen call sites take the port's form unchanged; the `fn` family is an `abbrev` in
    the port exactly as in the pin, so `rw [fn, …]` still unfolds, and the three Dirichlet
    facts are called with their `M` supplied by the section variable at every site.  The
    remaining pin declarations are here; `repZ'` stays local, as it is the pin's own copy of
    a name the port also has publicly.
  - **Namespaces flattened.**  The pin's `DescentSupportB`, `DescentEngine`, `LevelVector` and
    `LevelVector.WeightOne` blocks are `DihedralWeightOne` here, so the pin's qualified
    references in bodies are unqualified (`DescentSupportA.exists_glMap_eq` → `exists_glMap_eq`,
    `LevelVector.level_ne_zero` → `level_ne_zero`, `DihedralWeightOne.weightOneLift_…` →
    `weightOneLift_…`).  Proof bodies only; no statement re-spelt, and `check_port` is re-run
    on every edit.
  - **`import Mathlib` narrowed.**  The scaffold opened with `import Mathlib`; on this box its
    olean closure costs ≈100 s wall per `lake env lean` run (≈1 s user CPU — the closure is
    6.1 GB against 7 GB of RAM, so it never stays cached).  It is replaced by seven leaf
    modules (the subgroup/`liftOfRightInverse`, `Nat.factorization`, `ZMod.Units`,
    `DirichletCharacter.Basic`, `Coprime`, `Ideal.Span`, `RingTheory.Int.Basic`), which is the
    practice of `RepTheory/LocalLanglands/IntegralSubgroup.lean`; the elaboration cost dropped
    to 17–34 s (17 s warm, 34 s cold).  No statement changed.  Under the narrowed scope the
    elaboration also flags six `zero_le'` sites (deprecated 2026-07-21 for `zero_le`), two
    `if_pos`/`if_neg` sites (`ite_eq_left`/`ite_eq_right`) and five `haveI` sites
    (`linter.style.haveILetI`, which asks for `have`); all three are body-only substitutions and
    the module is silent after them.  `have` still serves as the instance at every one of the
    five sites (`NeZero M`, `NeZero N`, two `Fact …natGenerator….Prime` reached through the
    `set ℓ := …` in the same block, and `Fact p.Prime`).
  - **Body-only substitutions.**  `sum_fn_eq_of_mem_span`'s `Submodule.span_induction` keeps the
    pin's script but drops its `generalizing x`: the statement fixes `x`, so the motive is the
    instance at that `x` and each induction hypothesis is consumed at the same `x` (the pin's
    `ih x` becomes `ih`).  `hK0'`'s `d₀` block, `hde`'s away-from-`q` branch and `hcopM` use the
    pin's own `push_cast`/`set` scripts unchanged.  All of it is statement-neutral.

  ## Deferred pin surface

  Pin `:184`–`:199`, `private theorem isUnit_entry_of_lowerLeft_mem` (17 lines): declared but
  never used in this pin file (`move_dead` reads it dead in the pin too — the only occurrence is
  its own declaration).  It is the shared `DescentSupportB` prelude lemma of several sibling
  pins (`S_CuspForm_IsNewform_…`, `S_CuspForm_IsAdelicLiftOf_…`, `S_CuspForm_IsNormalizedEigenform_…`),
  which declare it privately and use it there; this pin's `exists_finComponent_eq_centralGL_mul_of_sub_mem`
  instead pins the unit entry down by valuation (`hc10`/`hc11`).  Not transcribed here, so that
  `move_dead` reads `0 declarations, 0 lines`; it is not dead because of a port resolution.

  ## Heartbeat probe (recorded, not installed — FR-0225)

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N
  FLTForHuman/LanglandsTunnell/WeightOneLiftFactorizationBound.lean` is silent at `N = 25000`
  and fails at `N = 12500` (deterministic `whnf` timeout, raised in
  `apply_eq_one_of_natCast_eq_one`, `:646`).  No `set_option maxHeartbeats` is installed; the
  project default is `4000000`, so this is an edit-loop headroom note, not a build risk.

  ## Gate readings

  `lake env lean -DautoImplicit=false`: no output.  `check_port --force`: `16 ok, 0 mismatch,
  0 missing, 0 own, 0 kw` — the module is 30 declarations (16 public, 14 `private`); the
  eighteen pin publics it does not carry are the import closure's (see Port deltas), and the
  two pin publics it carries are the row (`solution`, pin `:910`) and SET-AF98F's
  `hasNewvectorConductor_…_of_isPrimitiveForm` row (pin `:23`), both of which `check_port` reads
  as `ok`.  `scaffold_audit`: `complete` — 19 pin public declarations on the wire, 30 port
  declarations, 3 satisfied by the import closure.  `dedup --within`: 1 cluster, and it is the
  pin's own pair — `factorization_le_of_mem_span_weightOneLift` (pin `:768`) and the row (pin
  `:910`) have the same *shape* (`shape` tier, 17 lines) because the row's statement is the
  pin's `solution`, i.e. the engine applied at `M := N`; the pin duplicates them on purpose and
  the row cannot be folded into the engine under `check_port`.  (SET-AF98F's new row is not in a
  cluster: its statement is the `HasNewvectorConductor` form, not the engine's.)  `move_dead
  --dry-run`: `0 declarations, 0 lines` (after the deferral above).  `#print axioms` on all
  sixteen public declarations: `[propext, Classical.choice, Quot.sound]`, none else.  One
  `lake build FLTForHuman.LanglandsTunnell.WeightOneLiftFactorizationBound` under the build
  lock: `Build completed successfully (4832 jobs)`, the module itself in 10 s.
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Int.Basic
import FLTForHuman.LanglandsTunnell.WeightOneLiftLevel
import FLTForHuman.LanglandsTunnell.WeightOneLiftNebentypusExists
import FLTForHuman.LanglandsTunnell.WeightOneLiftQCoeffConverse
import FLTForHuman.NumberTheory.LocalNewvector.AdelicSpan
import FLTForHuman.NumberTheory.LocalNewvector.AdelicSpanConductor
import FLTForHuman.NumberTheory.LocalNewvector.ConductorDatum
import FLTForHuman.LanglandsTunnell.WeightOneLiftCuspidalRealization

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel AdelicDock IsDedekindDomain
open AutomorphicForm LocalNewvector DihedralWeightOne
open CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace DihedralWeightOne


private theorem exists_padicGL_map_eq_finComponent {q : ℕ} [Fact q.Prime] {I : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ I) :
    ∃ c : GL (Fin 2) ℤ_[q],
      padicGL q (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c)
        = finComponent (𝓞 ℚ) ℚ (padicPlace q) u := by
  obtain ⟨hu₁, hu₂⟩ := mem_finiteLevelZero_iff.mp hu
  set cq : GL (Fin 2) ℚ_[q] := Matrix.GeneralLinearGroup.map (n := Fin 2)
    (padicRingEquiv q).symm.toRingHom (finComponent (𝓞 ℚ) ℚ (padicPlace q) u) with hcq
  have hcq_inv : padicGL q cq = finComponent (𝓞 ℚ) ℚ (padicPlace q) u :=
    Matrix.GeneralLinearGroup.ext fun i j => by
      rw [padicGL_apply, hcq, Matrix.GeneralLinearGroup.map_apply]
      exact RingEquiv.apply_symm_apply _ _
  have hex : ∀ (e : GL (Fin 2) ((padicPlace q).adicCompletion ℚ)),
      (∀ i j, (e : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ) →
      ∀ i j, ∃ r : ℤ_[q], algebraMap ℤ_[q] ℚ_[q] r
        = (Matrix.GeneralLinearGroup.map (n := Fin 2) (padicRingEquiv q).symm.toRingHom e
            : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j := fun e he i j => by
    rw [Matrix.GeneralLinearGroup.map_apply]
    exact ⟨⟨_, (norm_le_one_iff_mem q _).mpr
      ((RingEquiv.apply_symm_apply (padicRingEquiv q) _).symm ▸ he i j)⟩,
      (PadicInt.algebraMap_apply _).trans rfl⟩
  have hmem : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace q) u
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₁.integral i j (padicPlace q)
  have hmem' : ∀ i j, (finComponent (𝓞 ℚ) ℚ (padicPlace q) u⁻¹
      : Matrix (Fin 2) (Fin 2) _) i j ∈ (padicPlace q).adicCompletionIntegers ℚ := fun i j => by
    rw [finComponent_apply]; exact hu₂.integral i j (padicPlace q)
  obtain ⟨c, hc⟩ := exists_glMap_eq (algebraMap ℤ_[q] ℚ_[q])
    (IsFractionRing.injective ℤ_[q] ℚ_[q]) cq (hcq ▸ hex _ hmem)
    (by rw [hcq, ← map_inv, ← map_inv]; exact hex _ hmem')
  exact ⟨c, hc ▸ hcq_inv⟩

private theorem map_algebraMap_scalar_eq_centralGL {q : ℕ} [Fact q.Prime] (d : ℤ_[q]ˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q])
        (Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom d)
      = LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom d) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp only [LocalNewvector.centralGL, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, Matrix.algebraMap_matrix_apply,
    apply_ite (algebraMap ℤ_[q] ℚ_[q]), map_zero]
  rfl

private theorem isLevelZeroMatrix_of_finComponent_eq_and {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v)
    {g u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel N)
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)))
    (hgq : finComponent (𝓞 ℚ) ℚ (padicPlace q) g = 1)
    (hgaway : ∀ v ≠ padicPlace q, finComponent (𝓞 ℚ) ℚ v g = finComponent (𝓞 ℚ) ℚ v u) :
    IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel M)
      (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
  refine ⟨fun i j v => ?_, fun v => ?_⟩
  all_goals rcases eq_or_ne v (padicPlace q) with rfl | hv
  · rw [← finComponent_apply, hgq, Units.val_one]
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne hij]; exact zero_mem _
  · rw [← finComponent_apply, hgaway v hv, finComponent_apply]; exact hu.integral i j v
  · rw [← finComponent_apply, hgq, Units.val_one,
      Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), map_zero]
    exact zero_le
  · rw [← finComponent_apply, hgaway v hv, finComponent_apply, ← hsame v hv]
    exact hu.lowerLeft v

private theorem mul_padicToFinAdelic_inv_mem_finiteLevelZero {q : ℕ} [Fact q.Prime] {N M : ℕ}
    (hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N))
    (c : GL (Fin 2) ℚ_[q]) (hc : finComponent (𝓞 ℚ) ℚ (padicPlace q) u = padicGL q c) :
    u * (padicToFinAdelic q c)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) := by
  obtain ⟨hu₁, hu₂⟩ := mem_finiteLevelZero_iff.mp hu
  set g := u * (padicToFinAdelic q c)⁻¹ with hg
  have hgq : finComponent (𝓞 ℚ) ℚ (padicPlace q) g = 1 := by
    rw [hg, map_mul, map_inv, finComponent_padicToFinAdelic_self, hc, mul_inv_cancel]
  have hgaway : ∀ v ≠ padicPlace q,
      finComponent (𝓞 ℚ) ℚ v g = finComponent (𝓞 ℚ) ℚ v u := fun v hv => by
    rw [hg, map_mul, map_inv, finComponent_padicToFinAdelic_of_ne q c hv, inv_one, mul_one]
  rw [mem_finiteLevelZero_iff]
  exact ⟨isLevelZeroMatrix_of_finComponent_eq_and hsame hu₁ hgq hgaway,
    isLevelZeroMatrix_of_finComponent_eq_and hsame hu₂ (g := g⁻¹) (u := u⁻¹)
      (by rw [map_inv, hgq, inv_one])
      (fun v hv => by rw [map_inv, hgaway v hv, map_inv])⟩

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem fn_padic_smul_self {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • AdelicSpan.self φ) z = φ (z * padicToAdelic q x) := by
  rw [fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul, AdelicSpan.toFn_self,
    AdelicFnCarrier.toFn_mk]

end

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem fn_padic_smul {q : ℕ} [Fact q.Prime] (x : GL (Fin 2) ℚ_[q]) (y : AdelicSpan φ) (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn (x • y) z = fn y (z * padicToAdelic q x) := by
  rw [fn, fn, AdelicSpan.padic_smul_def, AdelicSpan.toFn_smul, AdelicFnCarrier.toFn_smul]

end

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}

private theorem exists_fn_ne_zero {y : AdelicSpan φ} (hy : y ≠ 0) : ∃ z, fn y z ≠ 0 := by
  by_contra h
  push Not at h
  exact hy (AdelicSpan.ext _ (AdelicFnCarrier.ext fun z => h z))

end

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (p : ℕ) [hp : Fact p.Prime]

private theorem padicPlace_ne {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) : padicPlace q ≠ padicPlace p := by
  intro h
  unfold padicPlace at h
  exact hqp (congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective h))

end

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (p : ℕ) [hp : Fact p.Prime]

private theorem padicToAdelic_comm {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) (g : GL (Fin 2) ℚ_[q]) (r : GL (Fin 2) ℚ_[p]) :
    padicToAdelic q g * padicToAdelic p r = padicToAdelic p r * padicToAdelic q g := by
  rw [padicToAdelic_apply, padicToAdelic_apply, ← map_mul, ← map_mul]
  congr 1
  exact commute_of_finComponent_eq_one (padicPlace p)
    (finComponent_padicToFinAdelic_of_ne q g (padicPlace_ne p hqp).symm)
    (fun w' hw' => finComponent_padicToFinAdelic_of_ne p r hw')

end

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable def repZ' (i : Fin (p + 1)) : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
  if (i : ℕ) < p then !![1, ((i : ℕ) : ℤ_[p]); 0, (p : ℤ_[p])] else !![(p : ℤ_[p]), 0; 0, 1]

end

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (p : ℕ) [hp : Fact p.Prime]

private theorem det_repZ' (i : Fin (p + 1)) : (repZ' p i).det = (p : ℤ_[p]) := by
  unfold repZ'
  split_ifs <;> simp [Matrix.det_fin_two_of]

end

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (p : ℕ) [hp : Fact p.Prime]

private noncomputable def ρQ' (i : Fin (p + 1)) : GL (Fin 2) ℚ_[p] :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repZ' p i).map (algebraMap ℤ_[p] ℚ_[p])) (by
    rw [show (repZ' p i).map (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap ℤ_[p] ℚ_[p]).mapMatrix (repZ' p i) from rfl,
      ← RingHom.map_det, det_repZ', map_natCast]
    exact_mod_cast hp.out.ne_zero)

end

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (p : ℕ) [hp : Fact p.Prime]

private theorem coe_ρQ' (i : Fin (p + 1)) :
    ((ρQ' p i : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      if (i : ℕ) < p then !![(1 : ℚ_[p]), ((i : ℕ) : ℚ_[p]); 0, (p : ℚ_[p])]
      else !![(p : ℚ_[p]), 0; 0, 1] := by
  change (repZ' p i).map (algebraMap ℤ_[p] ℚ_[p]) = _
  unfold repZ'
  split_ifs
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp

end

section
variable {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
variable (p : ℕ) [hp : Fact p.Prime]

private theorem sum_fn_eq_of_mem_span {q : ℕ} [Fact q.Prime] (hqp : q ≠ p) {c : ℂ}
    (hE : ∀ x, ∑ i : Fin (p + 1), φ (x * padicToAdelic p (ρQ' p i)⁻¹) = c * φ x)
    {y : AdelicSpan φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self φ))
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∑ i : Fin (p + 1), fn y (x * padicToAdelic p (ρQ' p i)⁻¹) = c * fn y x := by
  induction hy using Submodule.span_induction with
  | mem y₁ hy₁ =>
    obtain ⟨g, rfl⟩ := hy₁
    simp only [fn_padic_smul_self, mul_assoc, ← padicToAdelic_comm p hqp g]
    simp only [← mul_assoc]
    exact hE (x * padicToAdelic q g)
  | zero => simp [fn_zero]
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    simp only [fn_add, Finset.sum_add_distrib, ih₁, ih₂, mul_add]
  | smul c' y₁ _ ih =>
    simp only [fn_csmul]
    rw [← Finset.mul_sum, ih]
    ring

end

theorem level_ne_zero {M : ℕ} (hM : M ≠ 0) (q m : ℕ) (hq : q.Prime) :
    q ^ m * (M / q ^ M.factorization q) ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne'

theorem factorization_level_self {M : ℕ} (hM : M ≠ 0) (q m : ℕ) (hq : q.Prime) :
    (q ^ m * (M / q ^ M.factorization q)).factorization q = m := by
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne', Finsupp.coe_add,
    Pi.add_apply, hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_ordCompl,
    Finsupp.erase_same, add_zero]

theorem factorization_level_of_ne {M : ℕ} (hM : M ≠ 0) {q : ℕ} (m : ℕ) (hq : q.Prime) {ℓ : ℕ}
    (hℓq : ℓ ≠ q) : (q ^ m * (M / q ^ M.factorization q)).factorization ℓ = M.factorization ℓ := by
  rw [Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) (Nat.ordCompl_pos q hM).ne', Finsupp.coe_add,
    Pi.add_apply, hq.factorization_pow, Finsupp.single_eq_of_ne hℓq, Nat.factorization_ordCompl,
    Finsupp.erase_ne hℓq, zero_add]

section
variable {q : ℕ} [Fact q.Prime]

theorem centralGL_mul_comm (z : ℚ_[q]ˣ) (g : GL (Fin 2) ℚ_[q]) : centralGL q z * g = g * centralGL q z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact Algebra.commutes (z : ℚ_[q]) (g : Matrix (Fin 2) (Fin 2) ℚ_[q])

end

section
variable {q : ℕ} [Fact q.Prime]

theorem centralGL_apply_one_one (z : ℚ_[q]ˣ) :
    ((centralGL q z : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) 1 1 = (z : ℚ_[q]) := by
  show algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q]) (z : ℚ_[q]) 1 1 = _
  rw [Matrix.algebraMap_matrix_apply, ite_eq_left rfl]
  rfl

end

section
variable {q : ℕ} [Fact q.Prime]

theorem isUnit_of_sub_mem {m : ℕ} (hm : 1 ≤ m) {x y : ℤ_[q]} (hx : IsUnit x)
    (hxy : x - y ∈ Ideal.span {(q : ℤ_[q]) ^ m}) : IsUnit y := by
  by_contra hy
  have hmax : Ideal.span {(q : ℤ_[q]) ^ m} ≤ IsLocalRing.maximalIdeal ℤ_[q] := by
    rw [Ideal.span_singleton_le_iff_mem, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]
    exact dvd_pow_self _ (by omega)
  have hy' : y ∈ IsLocalRing.maximalIdeal ℤ_[q] := (IsLocalRing.mem_maximalIdeal _).mpr hy
  have hx' : x ∈ IsLocalRing.maximalIdeal ℤ_[q] := by
    have : x = (x - y) + y := by ring
    rw [this]; exact add_mem (hmax hxy) hy'
  exact (IsLocalRing.mem_maximalIdeal _).mp hx' hx

end

section
variable {q : ℕ} [Fact q.Prime]

theorem padicToFinAdelic_centralGL_mem_finiteLevelZero (L : ℕ) (u : ℤ_[q]ˣ) :
    padicToFinAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom u))
      ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel L) := by
  have hbody : ∀ u' : ℤ_[q]ˣ, IsLevelZeroMatrix (𝓞 ℚ) ℚ (ratLevel L)
      ((padicToFinAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom u'))).val) := by
    intro u'
    refine ⟨fun i j w => ?_, ?_⟩
    · rw [padicToFinAdelic_apply, coe_localEmbed]
      by_cases hw : w = padicPlace q
      · subst hw
        rw [localMat_apply_self, padicGL_apply]
        show padicRingEquiv q
            ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) ((u' : ℤ_[q]) : ℚ_[q]) i j)
          ∈ (padicPlace q).adicCompletionIntegers ℚ
        rw [Matrix.algebraMap_matrix_apply]
        split_ifs
        · exact padicRingEquiv_coe_mem q (u' : ℤ_[q])
        · rw [map_zero]; exact zero_mem _
      · rw [localMat_apply_of_ne (𝓞 ℚ) ℚ (padicPlace q) _ i j hw, Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · intro w
      rw [padicToFinAdelic_apply, coe_localEmbed]
      by_cases hw : w = padicPlace q
      · subst hw
        rw [localMat_apply_self, padicGL_apply]
        show Valued.v (padicRingEquiv q
            ((algebraMap ℚ_[q] (Matrix (Fin 2) (Fin 2) ℚ_[q])) ((u' : ℤ_[q]) : ℚ_[q]) 1 0)) ≤ _
        rw [Matrix.algebraMap_matrix_apply, ite_eq_right (by decide), map_zero, map_zero]
        exact zero_le
      · rw [localMat_apply_of_ne (𝓞 ℚ) ℚ (padicPlace q) _ 1 0 hw,
          Matrix.one_apply_ne (by decide), map_zero]
        exact zero_le
  refine mem_finiteLevelZero_iff.mpr ⟨hbody u, ?_⟩
  have hinv : (padicToFinAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom u)))⁻¹
      = padicToFinAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom u⁻¹)) := by
    rw [← map_inv, ← map_inv, ← map_inv]
  rw [hinv]
  exact hbody u⁻¹

end

section
variable {q : ℕ} [Fact q.Prime]

theorem exists_finComponent_eq_centralGL_mul_of_sub_mem {N : ℕ} (hN : N ≠ 0)
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N))
    (d : ℤ)
    (hd : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N))
    (hdu : IsUnit (d : ℤ_[q])) :
    ∃ (c : GL (Fin 2) ℤ_[q]) (t : ℤ_[q]ˣ) (k : GL (Fin 2) ℚ_[q]),
      k ∈ LocalNewvector.padicK1 q (N.factorization q) ∧
      (t : ℤ_[q]) = d ∧
      padicGL q (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c)
        = finComponent (𝓞 ℚ) ℚ (padicPlace q) u ∧
      Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c
        = LocalNewvector.centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t) * k := by
  obtain ⟨c, hcfin⟩ := exists_padicGL_map_eq_finComponent (q := q) hu
  have hentry : ∀ i j, padicRingEquiv q (((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j : ℤ_[q]) : ℚ_[q])
      = ((u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) (padicPlace q) := fun i j => by
    rw [← finComponent_apply, ← hcfin, padicGL_apply, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply]
  have hc10 : (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 0 ∈ Ideal.span {(q : ℤ_[q]) ^ N.factorization q} := by
    rw [← valued_coe_le_idealBound_iff q hN, hentry]
    exact (mem_finiteLevelZero_iff.mp hu).1.lowerLeft (padicPlace q)
  have hc11 : (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 - (d : ℤ_[q]) ∈ Ideal.span {(q : ℤ_[q]) ^ N.factorization q} := by
    rw [← valued_coe_le_idealBound_iff q hN, PadicInt.coe_sub, map_sub, hentry, PadicInt.coe_intCast,
      show padicRingEquiv q (d : ℚ_[q]) = (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ)) (padicPlace q) by
        rw [algebraMap_intCast_apply_padicPlace_eq q d, PadicInt.coe_intCast],
      ← coe_sub_apply]
    exact hd (padicPlace q)
  set t : ℤ_[q]ˣ := hdu.unit with htdef
  have ht : (t : ℤ_[q]) = d := hdu.unit_spec
  set sc : GL (Fin 2) ℤ_[q] :=
    Units.map (algebraMap ℤ_[q] (Matrix (Fin 2) (Fin 2) ℤ_[q])).toMonoidHom t with hsc
  set k' : GL (Fin 2) ℤ_[q] := sc⁻¹ * c with hk'
  have hsc_inv_coe : ((sc⁻¹ : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q])
      = (↑t⁻¹ : ℤ_[q]) • (1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) := by
    rw [hsc, ← map_inv]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      Algebra.algebraMap_eq_smul_one]
  have hk'_row1 : ∀ j, (k' : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j
      = (↑t⁻¹ : ℤ_[q]) * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 j := fun j => by
    rw [hk', Units.val_mul, hsc_inv_coe, Matrix.smul_mul, one_mul, Matrix.smul_apply,
      smul_eq_mul]
  refine ⟨c, t, Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) k', ?_, ht, hcfin, ?_⟩
  · rw [LocalNewvector.mem_congruenceK1_iff]
    refine ⟨k', rfl, ?_, ?_⟩
    · rw [hk'_row1 0]; exact Ideal.mul_mem_left _ _ hc10
    · have : (↑t⁻¹ : ℤ_[q]) * (c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 - 1
          = (↑t⁻¹ : ℤ_[q]) * ((c : Matrix (Fin 2) (Fin 2) ℤ_[q]) 1 1 - (d : ℤ_[q])) := by
        rw [mul_sub, ← ht, Units.inv_mul]
      rw [hk'_row1 1, this]; exact Ideal.mul_mem_left _ _ hc11
  · rw [← map_algebraMap_scalar_eq_centralGL t, ← hsc, ← map_mul, hk', mul_inv_cancel_left]

end

section
variable {M : ℕ} {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
variable {q : ℕ} [Fact q.Prime]

set_option quotPrecheck false in
local notation "Φ" => weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)

theorem fn_mul_finEmbed_eq_of_qcentral (hM : M ≠ 0) (hε : CuspForm.HasNebentypus ε h)
    {y : AdelicSpan Φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    {w : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hw : w ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M))
    (hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) w = 1) (t : ℤ_[q]ˣ)
    (d : ℤ)
    (hd : ((w * padicToFinAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel M)) :
    ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ (w * padicToFinAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t))))
      = (ε (d : ZMod M))⁻¹ * fn y z := by
  have : NeZero M := ⟨hM⟩
  set w' := w * padicToFinAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t)) with hw'
  have hw'mem : w' ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) :=
    mul_mem hw (padicToFinAdelic_centralGL_mem_finiteLevelZero M t)
  have hΦ : ∀ x, Φ (x * finEmbed (𝓞 ℚ) ℚ w') = (ε (d : ZMod M))⁻¹ * Φ x := fun x =>
    weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero hε w' hw'mem d hd x

  have hcomm : ∀ x : GL (Fin 2) ℚ_[q], w' * padicToFinAdelic q x = padicToFinAdelic q x * w' := by
    intro x
    rw [hw', mul_assoc, ← map_mul, centralGL_mul_comm, map_mul, ← mul_assoc,
      commute_of_finComponent_eq_one (padicPlace q) hwq
        (fun v hv => finComponent_padicToFinAdelic_of_ne q x hv), mul_assoc]
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    intro z
    rw [fn_padic_smul_self, fn_padic_smul_self, padicToAdelic_apply, mul_assoc, ← map_mul, hcomm, map_mul,
      ← mul_assoc, hΦ]
  | zero => intro z; rw [fn_zero, fn_zero, mul_zero]
  | add y₁ y₂ _ _ ih₁ ih₂ => intro z; rw [fn_add, fn_add, ih₁, ih₂, mul_add]
  | smul c y _ ih => intro z; rw [fn_csmul, fn_csmul, ih]; ring

end

section
variable {M : ℕ} {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
variable {q : ℕ} [Fact q.Prime]

set_option quotPrecheck false in
local notation "Φ" => weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)

theorem fn_mul_finEmbed_eq_inv_mul (hM : M ≠ 0) (hε : CuspForm.HasNebentypus ε h)
    {m : ℕ} {y : AdelicSpan Φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    (hfix : y ∈ fixedSubmodule (padicK1 q m) (AdelicSpan Φ))
    {u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel (q ^ m * (M / q ^ M.factorization q))))
    (d : ℤ)
    (hd : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ)
      ∈ idealBall (𝓞 ℚ) ℚ (ratLevel (q ^ m * (M / q ^ M.factorization q))))
    (hdu : IsUnit (d : ℤ_[q]))
    (z : AdelicGL2 (𝓞 ℚ) ℚ) :
    fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (ε (d : ZMod M))⁻¹ * fn y z := by
  have hqP : q.Prime := Fact.out
  set N : ℕ := q ^ m * (M / q ^ M.factorization q) with hNdef
  have hN : N ≠ 0 := level_ne_zero hM q m hqP
  have hvq : N.factorization q = m := factorization_level_self hM q m hqP
  have hsame : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ≠ padicPlace q →
      idealBound (𝓞 ℚ) (ratLevel N) v = idealBound (𝓞 ℚ) (ratLevel M) v := fun v hv =>
    idealBound_ratLevel_eq_of_factorization_eq hN hM
      (fun ℓ _ hℓq => factorization_level_of_ne hM m hqP hℓq) v hv
  obtain ⟨c, t, k, hk, ht, hcfin, hcdk⟩ :=
    exists_finComponent_eq_centralGL_mul_of_sub_mem (q := q) hN hu d hd hdu
  rw [hvq] at hk
  set cQ : GL (Fin 2) ℚ_[q] := Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) c with hcQ

  have hcy : cQ • y = centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t) • y := by
    rw [hcdk, mul_smul, mem_fixedSubmodule_iff.mp hfix _ hk]

  have hw : u * (padicToFinAdelic q cQ)⁻¹ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel M) :=
    mul_padicToFinAdelic_inv_mem_finiteLevelZero hsame hu cQ hcfin.symm
  have hwq : finComponent (𝓞 ℚ) ℚ (padicPlace q) (u * (padicToFinAdelic q cQ)⁻¹) = 1 := by
    rw [map_mul, map_inv, finComponent_padicToFinAdelic_self q, hcfin, mul_inv_cancel]
  have hwaway : ∀ v ≠ padicPlace q,
      finComponent (𝓞 ℚ) ℚ v (u * (padicToFinAdelic q cQ)⁻¹) = finComponent (𝓞 ℚ) ℚ v u := fun v hv => by
    rw [map_mul, map_inv, finComponent_padicToFinAdelic_of_ne q cQ hv, inv_one, mul_one]
  have hsplit : u = u * (padicToFinAdelic q cQ)⁻¹ * padicToFinAdelic q cQ := by group

  set w' := u * (padicToFinAdelic q cQ)⁻¹ *
      padicToFinAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t)) with hw'
  have hd' : (w' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel M) := by
    intro v
    rw [coe_sub_apply, ← finComponent_apply]
    by_cases hv : v = padicPlace q
    · subst hv
      rw [hw', map_mul, hwq, one_mul, finComponent_padicToFinAdelic_self, padicGL_apply, centralGL_apply_one_one,
        algebraMap_intCast_apply_padicPlace_eq q d]
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      rw [PadicInt.algebraMap_apply, ht, sub_self, Valuation.map_zero]
      exact zero_le
    · rw [hw', map_mul, finComponent_padicToFinAdelic_of_ne q _ hv, mul_one, hwaway v hv, finComponent_apply,
        ← coe_sub_apply, ← hsame v hv]
      exact hd v
  rw [hsplit, map_mul, ← mul_assoc, ← padicToAdelic_apply, ← fn_padic_smul, hcy, fn_padic_smul,
    padicToAdelic_apply, mul_assoc, ← map_mul]
  exact fn_mul_finEmbed_eq_of_qcentral hM hε hy hw hwq t d hd' z

end

section
variable {M : ℕ} {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
variable {q : ℕ} [Fact q.Prime]

set_option quotPrecheck false in
local notation "Φ" => weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)

theorem apply_eq_one_of_natCast_eq_one (hM : M ≠ 0) (hε : CuspForm.HasNebentypus ε h)
    (hqM : q ∣ M) {m : ℕ}
    {y : AdelicSpan Φ}
    (hy : y ∈ Submodule.span ℂ (Set.range fun x : GL (Fin 2) ℚ_[q] => x • AdelicSpan.self Φ))
    (hfix : y ∈ fixedSubmodule (padicK1 q m) (AdelicSpan Φ)) (hy0 : y ≠ 0)
    (e : ℕ) (he : (e : ZMod (q ^ m * (M / q ^ M.factorization q))) = 1) (heM : IsUnit (e : ZMod M)) :
    ε (e : ZMod M) = 1 := by
  have hqP : q.Prime := Fact.out
  set N : ℕ := q ^ m * (M / q ^ M.factorization q) with hNdef
  have hN : N ≠ 0 := level_ne_zero hM q m hqP
  have hvq : N.factorization q = m := factorization_level_self hM q m hqP

  have hNe : (N : ℤ) ∣ (e : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [he, sub_self]

  have hqe : ¬ (q : ℤ) ∣ (e : ℤ) := fun hqe => by
    have hcop : e.Coprime M := (ZMod.isUnit_iff_coprime e M).mp heM
    have hg := Nat.dvd_gcd (Int.natCast_dvd_natCast.mp hqe) hqM
    rw [hcop.gcd_eq_one] at hg
    exact hqP.ne_one (Nat.dvd_one.mp hg)
  have heu : IsUnit ((e : ℤ) : ℤ_[q]) := by
    rw [PadicInt.isUnit_iff]
    exact le_antisymm (PadicInt.norm_le_one _)
      (not_lt.mp fun h => hqe ((PadicInt.norm_int_lt_one_iff_dvd (e : ℤ)).mp h))
  set t : ℤ_[q]ˣ := heu.unit with htdef
  have ht : (t : ℤ_[q]) = ((e : ℤ) : ℤ_[q]) := heu.unit_spec
  set u₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    padicToFinAdelic q (centralGL q (Units.map (algebraMap ℤ_[q] ℚ_[q]).toMonoidHom t)) with hu₀
  have hu₀mem : u₀ ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N) := padicToFinAdelic_centralGL_mem_finiteLevelZero N t

  have h11q : ((u₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1) (padicPlace q)
      = padicRingEquiv q (((e : ℤ) : ℤ_[q]) : ℚ_[q]) := by
    rw [← finComponent_apply, hu₀, finComponent_padicToFinAdelic_self, padicGL_apply, centralGL_apply_one_one]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [PadicInt.algebraMap_apply, ht]
  have h11away : ∀ v ≠ padicPlace q, ((u₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1) v = 1 := by
    intro v hv
    rw [← finComponent_apply, hu₀, finComponent_padicToFinAdelic_of_ne q _ hv, Units.val_one, Matrix.one_apply_eq]

  have hde : (u₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((e : ℤ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) := by
    intro v
    rw [coe_sub_apply]
    by_cases hv : v = padicPlace q
    · subst hv
      rw [h11q, algebraMap_intCast_apply_padicPlace_eq q, sub_self, Valuation.map_zero]
      exact zero_le
    · have hℓp : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
      rw [h11away v hv]
      rw [eq_padicPlace_natGenerator v]
      set ℓ := Rat.HeightOneSpectrum.natGenerator v with hℓ
      have hone : (1 : (padicPlace ℓ).adicCompletion ℚ) = padicRingEquiv ℓ (((1 : ℤ_[ℓ]) : ℚ_[ℓ])) := by
        rw [PadicInt.coe_one, map_one]
      rw [algebraMap_intCast_apply_padicPlace_eq ℓ, hone, ← map_sub, ← PadicInt.coe_sub,
        valued_coe_le_idealBound_iff ℓ hN]
      have hdvd : ((ℓ : ℤ) ^ N.factorization ℓ) ∣ 1 - (e : ℤ) := by
        have h1 : ((ℓ ^ N.factorization ℓ : ℕ) : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd N ℓ)
        have h2 := (h1.trans hNe)
        rw [← dvd_neg, neg_sub] at h2
        exact_mod_cast h2
      obtain ⟨k, hk⟩ := hdvd
      refine Ideal.mem_span_singleton.mpr ⟨(k : ℤ_[ℓ]), ?_⟩
      have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hk
      push_cast at this ⊢
      exact this

  have hd1 : (u₀ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
      - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((1 : ℤ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) := by
    intro v
    rw [coe_sub_apply]
    by_cases hv : v = padicPlace q
    · subst hv
      rw [h11q, algebraMap_intCast_apply_padicPlace_eq q, ← map_sub, ← PadicInt.coe_sub,
        valued_coe_le_idealBound_iff q hN, hvq]
      have hqmN : ((q ^ m : ℕ) : ℤ) ∣ (N : ℤ) := Int.natCast_dvd_natCast.mpr (Dvd.intro _ rfl)
      obtain ⟨k, hk⟩ := hqmN.trans hNe
      refine Ideal.mem_span_singleton.mpr ⟨(k : ℤ_[q]), ?_⟩
      have := congrArg (fun z : ℤ => (z : ℤ_[q])) hk
      push_cast at this ⊢
      exact this
    · rw [h11away v hv, Int.cast_one, map_one, coe_one_apply, sub_self, Valuation.map_zero]
      exact zero_le

  obtain ⟨z, hz⟩ := exists_fn_ne_zero hy0
  have h1 := fn_mul_finEmbed_eq_inv_mul hM hε hy hfix hu₀mem (e : ℤ) hde heu z
  have h2 := fn_mul_finEmbed_eq_inv_mul hM hε hy hfix hu₀mem (1 : ℤ) hd1
    (by rw [Int.cast_one]; exact isUnit_one) z
  rw [h2, Int.cast_one, map_one, inv_one, one_mul, Int.cast_natCast] at h1
  have h3 : (ε (e : ZMod M))⁻¹ * fn y z = 1 * fn y z := by rw [one_mul]; exact h1.symm
  exact inv_eq_one.mp (mul_right_cancel₀ hz h3)

end

theorem exists_dirichletCharacter_of_dvd {M N : ℕ} [NeZero M] (hNM : N ∣ M) (ε : DirichletCharacter ℂ M)
    (hker : ∀ e : ℕ, (e : ZMod N) = 1 → IsUnit (e : ZMod M) → ε (e : ZMod M) = 1) :
    ∃ ε' : DirichletCharacter ℂ N, ∀ d : ℤ, IsCoprime d (M : ℤ) → ε' (d : ZMod N) = ε (d : ZMod M) := by
  set ψ : (ZMod M)ˣ →* (ZMod N)ˣ := ZMod.unitsMap hNM with hψ
  have hsurj : Function.Surjective ψ := ZMod.unitsMap_surjective hNM
  have hle : ψ.ker ≤ (MulChar.toUnitHom ε).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    set e : ℕ := ((x : (ZMod M)ˣ) : ZMod M).val with he
    have hex : ((e : ℕ) : ZMod M) = ((x : (ZMod M)ˣ) : ZMod M) := ZMod.natCast_zmod_val _
    have heN : ((e : ℕ) : ZMod N) = 1 := by
      have h1 := congrArg (fun r : (ZMod N)ˣ => (r : ZMod N)) hx
      simp only [Units.val_one] at h1
      rw [hψ, ZMod.unitsMap_val, ← hex, ZMod.cast_natCast hNM] at h1
      exact h1
    apply Units.ext
    rw [MulChar.coe_toUnitHom, Units.val_one, ← hex]
    exact hker e heN (by rw [hex]; exact Units.isUnit _)
  set θ : (ZMod N)ˣ →* ℂˣ :=
    ψ.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨MulChar.toUnitHom ε, hle⟩
    with hθ
  refine ⟨MulChar.ofUnitHom θ, fun d hd => ?_⟩
  have hdu : IsUnit (d : ZMod M) := (ZMod.coe_int_isUnit_iff_isCoprime d M).mpr hd.symm
  have hψd : ((ψ hdu.unit : (ZMod N)ˣ) : ZMod N) = (d : ZMod N) := by
    rw [hψ, ZMod.unitsMap_val, IsUnit.unit_spec, ZMod.cast_intCast hNM]
  rw [← hψd, MulChar.ofUnitHom_coe, hθ, MonoidHom.liftOfRightInverse_comp_apply, MulChar.coe_toUnitHom,
    IsUnit.unit_spec]

theorem algebraMap_natCast_mul_mem_idealBall {N : ℕ} (hN : N ≠ 0) (k : ℤ) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((N : ℤ) * k : ℤ) : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) := by
  intro v
  have hℓp : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨Rat.HeightOneSpectrum.prime_natGenerator v⟩
  rw [eq_padicPlace_natGenerator v]
  set ℓ := Rat.HeightOneSpectrum.natGenerator v with hℓ
  rw [algebraMap_intCast_apply_padicPlace_eq ℓ, valued_coe_le_idealBound_iff ℓ hN]
  have h1 : ((ℓ ^ N.factorization ℓ : ℕ) : ℤ) ∣ (N : ℤ) * k :=
    dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd N ℓ)) k
  obtain ⟨c, hc⟩ := h1
  refine Ideal.mem_span_singleton.mpr ⟨(c : ℤ_[ℓ]), ?_⟩
  have := congrArg (fun z : ℤ => (z : ℤ_[ℓ])) hc
  push_cast at this ⊢
  exact this

theorem factorization_le_of_mem_span_weightOneLift
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hh : CuspForm.IsPrimitiveForm ε h)
    (q : ℕ) [Fact q.Prime] {m : ℕ}
    (y : LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] =>
        x • LocalNewvector.AdelicSpan.self (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h))))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q m)
      (LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h))))
    (hy0 : y ≠ 0) :
    M.factorization q ≤ m := by
  by_contra hlt
  push Not at hlt
  have hM : M ≠ 0 := NeZero.ne M
  have hqP : q.Prime := Fact.out
  have hε : CuspForm.HasNebentypus ε h := hh.isEigenformWith.hasNebentypus
  set n : ℕ := M.factorization q with hndef
  set M' : ℕ := M / q ^ n with hM'def
  set N : ℕ := q ^ m * M' with hNdef
  have hN : N ≠ 0 := level_ne_zero hM q m hqP
  have : NeZero N := ⟨hN⟩
  have hM'pos : 0 < M' := Nat.ordCompl_pos q hM
  have hMfac : q ^ n * M' = M := Nat.ordProj_mul_ordCompl_eq_self M q
  have hn1 : 1 ≤ n := by omega
  have hqM : q ∣ M := Nat.dvd_of_factorization_pos (by omega)
  have hNM : N ∣ M := by
    rw [← hMfac]
    exact mul_dvd_mul_right (pow_dvd_pow q hlt.le) M'
  have hNne : N ≠ M := by
    intro heq
    have h1 : q ^ m * M' = q ^ n * M' := by rw [← hNdef, heq, hMfac]
    have h2 : q ^ m = q ^ n := Nat.eq_of_mul_eq_mul_right hM'pos h1
    exact hlt.ne (Nat.pow_right_injective hqP.two_le h2)

  have hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ d : ℤ, IsUnit (d : ℤ_[q]) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) →
      ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (ε (d : ZMod M))⁻¹ * fn y z :=
    fun u hu d hdu hd z => fn_mul_finEmbed_eq_inv_mul hM hε hy hfix hu d hd hdu z

  have hdrop : ∀ e : ℕ, (e : ZMod N) = 1 → IsUnit (e : ZMod M) → ε (e : ZMod M) = 1 :=
    fun e he heM => apply_eq_one_of_natCast_eq_one hM hε hqM hy hfix hy0 e he heM
  obtain ⟨ε', hε'⟩ := exists_dirichletCharacter_of_dvd hNM ε hdrop

  have hcopM : ∀ d : ℤ, IsCoprime d (N : ℤ) → ¬ (q : ℤ) ∣ d → IsCoprime d (M : ℤ) := by
    intro d hd hqd
    have hd' : IsCoprime d ((q : ℤ) ^ m * (M' : ℤ)) := by rw [hNdef] at hd; exact_mod_cast hd
    have hqd' : ¬ q ∣ d.natAbs := fun h' => hqd (Int.natCast_dvd.mpr h')
    have hdq : IsCoprime d (q : ℤ) := by
      refine (Int.isCoprime_iff_nat_coprime.mpr ?_).symm
      simpa only [Int.natAbs_natCast] using (Nat.Prime.coprime_iff_not_dvd hqP).mpr hqd'
    have hdM' : IsCoprime d (M' : ℤ) := hd'.of_mul_right_right
    have : IsCoprime d ((q : ℤ) ^ n * (M' : ℤ)) := (hdq.pow_right).mul_right hdM'
    rw [← hMfac]; exact_mod_cast this
  have hε'nat : ∀ p : ℕ, p.Coprime M → ε' (p : ZMod N) = ε (p : ZMod M) := by
    intro p hp
    have := hε' (p : ℤ) (Nat.isCoprime_iff_coprime.mpr hp)
    rwa [Int.cast_natCast, Int.cast_natCast] at this

  have hK0' : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) →
      ∀ z, fn y (z * finEmbed (𝓞 ℚ) ℚ u) = (ε' (d : ZMod N))⁻¹ * fn y z := by
    intro u hu d hd hball z
    obtain ⟨k, hqd₀⟩ : ∃ k : ℤ, ¬ (q : ℤ) ∣ d + (N : ℤ) * k := by
      by_cases hqd : (q : ℤ) ∣ d
      · refine ⟨1, fun h' => ?_⟩
        have hqN : (q : ℤ) ∣ (N : ℤ) := by
          have := dvd_sub h' hqd
          rwa [mul_one, add_sub_cancel_left] at this
        have hqu : IsUnit (q : ℤ) := hd.isUnit_of_dvd' hqd hqN
        rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hqu
        exact hqP.ne_one hqu
      · exact ⟨0, by rwa [mul_zero, add_zero]⟩
    set d₀ : ℤ := d + (N : ℤ) * k with hd₀
    have hd₀u : IsUnit (d₀ : ℤ_[q]) := by
      rw [PadicInt.isUnit_iff]
      exact le_antisymm (PadicInt.norm_le_one _)
        (not_lt.mp fun h' => hqd₀ ((PadicInt.norm_int_lt_one_iff_dvd d₀).mp h'))
    have hball₀ : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d₀ : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (ratLevel N) := by
      have hsplit : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
            - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d₀ : ℚ)
          = ((u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
              - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ))
            - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (((N : ℤ) * k : ℤ) : ℚ) := by
        rw [hd₀, Int.cast_add, map_add, sub_sub]
      rw [hsplit]
      intro v
      rw [coe_sub_apply]
      exact le_trans (Valuation.map_sub _ _ _) (max_le (hball v) (algebraMap_natCast_mul_mem_idealBall hN k v))
    have hdd₀ : ((d₀ : ℤ) : ZMod N) = (d : ZMod N) := by
      rw [hd₀]; push_cast; rw [ZMod.natCast_self, zero_mul, add_zero]
    have hcop₀ : IsCoprime d₀ (N : ℤ) := by rw [hd₀]; exact hd.add_mul_left_left k
    rw [← hdd₀, hε' d₀ (hcopM d₀ hcop₀ hqd₀)]
    exact hK0 u hu d₀ hd₀u hball₀ z

  have hy' : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) • AdelicSpan.self (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h))) := by
    refine Submodule.span_mono ?_ hy
    rintro _ ⟨x, rfl⟩
    exact ⟨padicToFinAdelic q x, by simp only [AdelicSpan.padic_smul_def, padicToAdelic_apply]⟩

  obtain ⟨F, hFε, hFlift, hF0⟩ :=
    exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
      h ε' y hy' hK0'
  have hFne : F ≠ 0 := fun h0 => hy0 (hF0 h0)

  refine hh.not_eigenpacketOccursAt hNM hNne ⟨ε', F, hFne, hFε, (q * M).primeFactors, fun p hp hpS => ?_⟩
  have hpqM : ¬ p ∣ q * M := fun hdvd =>
    hpS (Nat.mem_primeFactors.mpr ⟨hp, hdvd, mul_ne_zero hqP.ne_zero hM⟩)
  have hpM : ¬ p ∣ M := fun h' => hpqM (Dvd.dvd.mul_left h' q)
  have hpq : p ≠ q := fun h' => hpqM (h' ▸ dvd_mul_right p M)
  have hpN : ¬ p ∣ N := fun h' => hpM (h'.trans hNM)
  have hpcop : p.Coprime M := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpM
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨hε'nat p hpcop, fun n' => ?_⟩

  have hE : ∀ x, ∑ i : Fin (p + 1), (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)) (x * padicToAdelic p (ρQ' p i)⁻¹)
      = (ε (p : ZMod M))⁻¹ * (p : ℂ) * ModularFormClass.qCoeff h p * (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)) x := fun x =>
    sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq
      hε p hpM (ρQ' p) (coe_ρQ' p) (ModularFormClass.qCoeff h p) (hh.isEigenformWith.hecke_of_not_dvd hp hpM) x
  have hEy : ∀ x, ∑ i : Fin (p + 1), fn y (x * padicToAdelic p (ρQ' p i)⁻¹)
      = (ε (p : ZMod M))⁻¹ * (p : ℂ) * ModularFormClass.qCoeff h p * fn y x :=
    fun x => sum_fn_eq_of_mem_span p (fun h' => hpq h'.symm) hE hy x
  have hT := qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq
    hFε p hpN (ρQ' p) (coe_ρQ' p) ((ε (p : ZMod M))⁻¹ * (p : ℂ) * ModularFormClass.qCoeff h p)
    (fun x _ _ => by rw [← hFlift]; exact hEy x) n'
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hε0 := dirichlet_ne_zero ε hpcop
  rw [hT, hε'nat p hpcop]
  calc ε (p : ZMod M) * (p : ℂ)⁻¹ * ((ε (p : ZMod M))⁻¹ * (p : ℂ) * ModularFormClass.qCoeff h p)
          * ModularFormClass.qCoeff F n'
        = (ε (p : ZMod M) * (ε (p : ZMod M))⁻¹) * ((p : ℂ)⁻¹ * (p : ℂ))
            * (ModularFormClass.qCoeff h p * ModularFormClass.qCoeff F n') := by ring
    _ = ModularFormClass.qCoeff h p * ModularFormClass.qCoeff F n' := by
          rw [mul_inv_cancel₀ hε0, inv_mul_cancel₀ hp0, one_mul, one_mul]

theorem factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (CongruenceSubgroup.Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f) (q : ℕ) [Fact q.Prime] (m : ℕ)
    (y : LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] =>
        x • LocalNewvector.AdelicSpan.self (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f))))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q m)
      (LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f))))
    (hy0 : y ≠ 0) :
    N.factorization q ≤ m :=
  factorization_le_of_mem_span_weightOneLift hf q y hy hfix hy0

theorem hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f) (q : ℕ) [Fact q.Prime] :
    LocalNewvector.HasNewvectorConductor q
      (LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)))
      (N.factorization q) := by
  obtain ⟨hne, hlev⟩ :=
    DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm N ψ f hf
  obtain ⟨c, hce, hc⟩ :=
    LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization _ hne (NeZero.ne N) hlev q
  rcases Nat.lt_or_eq_of_le hce with hlt | heq
  · exfalso
    obtain ⟨y, hy, hy0, hfix⟩ :=
      LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
        _ (NeZero.ne N) hlev q c hc.1
    have hle :=
      DihedralWeightOne.factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1
        N ψ f hf q c y hy hfix hy0
    exact absurd hle (not_le.mpr hlt)
  · rw [← heq]
    exact hc

theorem exists_heightOneSpectrum_mem (p : ℕ) (hp : p.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal := by
  have hne : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map Rat.ringOfIntegersEquiv.toRingHom
    rw [map_natCast, Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
    exact hp.one_lt.ne' h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hp0 : (p : 𝓞 ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hMne : M ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, Ideal.span_singleton_eq_bot] at hle
    exact hp0 hle
  exact ⟨⟨M, hM.isPrime, hMne⟩, hle (Ideal.subset_span rfl)⟩

end DihedralWeightOne

namespace AutomorphicForm

open AutomorphicForm.SiegelCovering AutomorphicForm.WindowedSiegel NumberField.AdelicBox in
theorem exists_isGenuineCuspRealizationAt_hasNewvectorConductor_adelicSpan_factorization_of_isPrimitiveForm_weightOne
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f)
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ N →
      ∀ v : HeightOneSpectrum (𝓞 ℚ), (p : 𝓞 ℚ) ∈ v.asIdeal →
        ModularFormClass.qCoeff f p = Θ.a v ∧ ψ (p : ZMod N) = Θ.b v) :
    ∃ (Θ' : HeckeEigensystem ℚ ℂ) (_ : Θ'.AgreesAwayFromFinite Θ)
      (R' : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ'.toRawCentral),
      IsGenuineCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ'.toRawCentral R' ∧
      ∀ (q : ℕ) (_ : Fact q.Prime),
        LocalNewvector.HasNewvectorConductor q (LocalNewvector.AdelicSpan R'.toFun) (N.factorization q) := by
  classical

  obtain ⟨Φ, R, hRf, hRg, hRb, S₁, hpk⟩ :=
    DihedralWeightOne.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm N ψ f hf

  obtain ⟨R', hR'⟩ :=
    AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre
      c u d₁ d₂ T hc hd₁ hd hcov Φ.toRawCentral R hRg hRb
  obtain ⟨S₂, hΘ⟩ := hΘ

  have hfin : Set.Finite {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal ∈ S₁ ∪ S₂ ∪ N.primeFactors} := by
    have hsub : {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal ∈ S₁ ∪ S₂ ∪ N.primeFactors} ⊆
        ⋃ n ∈ (↑(S₁ ∪ S₂ ∪ N.primeFactors) : Set ℕ), {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal = n} := by
      intro v hv
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      exact ⟨_, hv, rfl⟩
    refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun n _ => ?_) hsub
    have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 ℚ) => v.asIdeal)
        {v : HeightOneSpectrum (𝓞 ℚ) | Ideal.absNorm v.asIdeal = n} := fun v _ w _ h => HeightOneSpectrum.ext h
    refine Set.Finite.of_finite_image ?_ hinj
    refine (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 ℚ) n).subset ?_
    rintro I ⟨v, hv, rfl⟩
    exact hv
  have hagree : Φ.AgreesAwayFromFinite Θ := by
    refine ⟨hfin.toFinset, fun v hv => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
    obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
    have hnorm : Ideal.absNorm v.asIdeal = p := absNorm_asIdeal_eq hp v hpv
    rw [hnorm] at hv
    have hp1 : p ∉ S₁ := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    have hp2 : p ∉ S₂ := fun h => hv (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    have hpN : ¬ p ∣ N := fun h => hv (Finset.mem_union_right _ (Nat.mem_primeFactors.2 ⟨hp, h, NeZero.ne N⟩))
    obtain ⟨h1, h2⟩ := hpk p hp hp1 hpN v hpv
    obtain ⟨h3, h4⟩ := hΘ p hp hp2 hpN v hpv
    exact ⟨h1.trans h3, h2.trans h4⟩
  refine ⟨Φ, hagree, R', ?_, fun q hq => ?_⟩
  · change Continuous R'.toFun
    rw [hR']
    exact hRg
  · rw [hR', hRf]
    exact DihedralWeightOne.hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm N ψ f hf q


end AutomorphicForm

end
