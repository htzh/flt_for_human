/-
  Fixed vectors of a `GL₂(ℚ_[p])`-representation: `fixedSubmodule`, the
  newvector conductor, and the character vocabulary.

  A smooth `GL₂(ℚ_[p])`-representation is studied through the vectors a congruence subgroup
  fixes, so this module carries the three pieces of vocabulary every later statement in the area
  is written with:

  * `fixedSubmodule U V` — the `U`-fixed vectors of a representation `V` as a `ℂ`-submodule, with
    `mem_fixedSubmodule_iff` its membership form (the pin's `Iff.rfl`). Its `smul_mem'` is where
    `SMulCommClass G ℂ V` is spent: fixed vectors are closed under `ℂ`-scalars exactly because
    scalars commute with `G`.
  * The seam between the port's two congruence-subgroup vocabularies. The `p`-adic levels
    `padicK0 p n`/`padicK1 p n` live in `RepTheory/LocalNewvector/CongruenceSubgroupK1.lean` as
    `congruenceK0`/`congruenceK1` at `ϖ = p`, while `LocalGL2.integralSubgroup R K` lives in
    `RepTheory/LocalLanglands/IntegralSubgroup.lean` as the range of the coefficient map. The four
    `*_eq_integralSubgroup`/`*_le_integralSubgroup` declarations say the two agree: level `0` *is*
    the integral subgroup, and every level sits inside it. Without them a downstream statement
    cannot move between "fixed by `K(pⁿ)`" and "fixed by `GL₂(ℤ_[p])`", which is exactly the move
    the conductor bound makes.
  * The character and irreducibility vocabulary: `centralGL` (the central embedding
    `ℚ_[p]ˣ → GL₂(ℚ_[p])`), `IsCentralCharacterRep` and `centralCharacterRep_unique` (a central
    character is determined by its value on one nonzero vector), `HasNewvectorConductor` and
    `hasNewvectorConductor_unique` (the least level with nonzero fixed vectors, and its
    uniqueness), `IsIrreducibleGLRep`, and `HasFiniteLevelFixed` (every level's fixed space is
    finite-dimensional over `ℂ`).

  Transcribed from `Definitions/Def_LocalNewvector_ConductorDatum.lean` (pinned `aa2d8b3`,
  114 lines / 15 declarations). All fifteen are here at the pin's names and statements, and the
  nine proof bodies are the pin's own.

  spec-pin: Definitions/Def_LocalNewvector_ConductorDatum.lean

  ## Port deltas

  - `import Mathlib` replaced by the four specific mathlib modules this module uses
    (`Algebra.Module.Submodule.Basic` for `Submodule`, `Algebra.Group.Units.Hom` for
    `Units.map`, `Basic.Complex.Basic` for `ℂ`, `RingTheory.Finiteness.Defs` for `Module.Finite`)
    plus `Order.Basic` for `lt_trichotomy`. Same substitution as the port's other definition-layer
    modules (cf. `RepTheory/LocalLanglands/IntegralSubgroup.lean`), and it is what keeps the module
    inside the gates' time budget: a bare `import Mathlib` here loads a 6.1 GB olean closure on a
    7 GB machine, over 100 s per elaboration.
  - `Mathlib.Data.Complex.Basic` would have been the obvious home for `ℂ`, but at mathlib `v4.34`
    it is *deprecated* and importing it emits a deprecation warning, which fails the silence gate.
    The non-deprecated path is `Mathlib.Basic.Complex.Basic`, and that is what is imported.
  - Pin structure: the pin groups these declarations in two `section`s (`IntegralSubgroupSeam`,
    `Padic`); the module opens one `section ... end` per declaration (the scaffold's shape) and the
    pin's section names are dropped. Statements, names, and visibility are unchanged.
  - The seam lemmas are the pin's own one-liners and they consume the port's `congruenceK0_zero`,
    `congruenceK1_zero` and `congruenceK1_le_congruenceK0`, which are already public at the pin's
    names in `RepTheory/LocalNewvector/CongruenceSubgroupK1.lean`, so nothing had to be restated.
    Their conclusions name `LocalGL2.integralSubgroup`, which is a `def` (not an `abbrev`); the
    pin's term-mode bodies still check against it at default transparency, so no `change` or
    unfolding step was needed (contrast FR-0245's `SpecialLinearGroup`).

  ## Deferred pin surface

  None. The pin is 114 lines / 15 declarations and the module declares exactly those fifteen;
  `move_dead.py` reads 0 declarations / 0 lines and `dedup.py --within` reads 0 clusters.

  ## Gates

  - `check_port --force` — 15 ok, 0 mismatch, 0 missing, 0 own, 0 kw (tier 2, wired).
  - `scaffold_audit` — **complete**: 15 pin public on the wire, 15 declared here, 0 satisfied from
    the import closure (nothing is credited to a namesake).
  - `lake env lean -DautoImplicit=false` — no output at all (project cap `maxHeartbeats = 4000000`).
  - `lake build FLTForHuman.NumberTheory.LocalNewvector.ConductorDatum` under the lock — ok.
  - `#print axioms` on all fifteen — `[propext, Classical.choice, Quot.sound]` for each, with no
    proof hole (probe: `lean/tmp/af96/probe_cd_ax.lean`).
  - `dedup --within` — 0 clusters. `move_dead --dry-run` — 0 declarations, 0 lines.
  - Heartbeat probe (stated, never installed, FR-0225): silent at `-DmaxHeartbeats=2000`, first
    failure at `1000` (deterministic timeout at `isDefEq`, in `centralCharacterRep_unique`'s
    `calc`), so the heaviest declaration costs about 1–2 million heartbeats — the instance search
    for `DistribMulAction`/`Module`/`SMulCommClass` over `ℚ_[p]`, not the proofs. No
    `set_option maxHeartbeats` is carried.
-/

import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Order.Basic
import FLTForHuman.RepTheory.LocalNewvector.CongruenceSubgroupK1
import FLTForHuman.RepTheory.LocalNewvector.GL2CongruenceSubgroup
import FLTForHuman.RepTheory.LocalLanglands.IntegralSubgroup

set_option autoImplicit false

noncomputable section


namespace LocalNewvector


def fixedSubmodule {G : Type*} [Group G] (U : Subgroup G) (V : Type*) [AddCommGroup V]
    [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] : Submodule ℂ V where
  carrier := {v | ∀ g ∈ U, g • v = v}
  add_mem' := by
    intro v w hv hw g hg
    rw [smul_add, hv g hg, hw g hg]
  zero_mem' := by
    intro g _
    exact smul_zero g
  smul_mem' := by
    intro c v hv g hg
    rw [smul_comm, hv g hg]

theorem mem_fixedSubmodule_iff {G : Type*} [Group G] {U : Subgroup G} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [DistribMulAction G V] [SMulCommClass G ℂ V] {v : V} :
    v ∈ fixedSubmodule U V ↔ ∀ g ∈ U, g • v = v :=
  Iff.rfl

section
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem congruenceK0_zero_eq_integralSubgroup (ϖ : R) :
    congruenceK0 (K := K) ϖ 0 = LocalGL2.integralSubgroup R K :=
  congruenceK0_zero ϖ

end

section
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem congruenceK1_zero_eq_integralSubgroup (ϖ : R) :
    congruenceK1 (K := K) ϖ 0 = LocalGL2.integralSubgroup R K :=
  congruenceK1_zero ϖ

end

section
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem congruenceK0_le_integralSubgroup (ϖ : R) (n : ℕ) :
    congruenceK0 (K := K) ϖ n ≤ LocalGL2.integralSubgroup R K := by
  rintro x ⟨y, rfl, _⟩
  exact ⟨y, rfl⟩

end

section
variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

theorem congruenceK1_le_integralSubgroup (ϖ : R) (n : ℕ) :
    congruenceK1 (K := K) ϖ n ≤ LocalGL2.integralSubgroup R K :=
  (congruenceK1_le_congruenceK0 _ _).trans (congruenceK0_le_integralSubgroup ϖ n)

end

section
variable (p : ℕ) [Fact p.Prime]

theorem padicK0_zero_eq_integralSubgroup :
    padicK0 p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  congruenceK0_zero_eq_integralSubgroup (p : ℤ_[p])

end

section
variable (p : ℕ) [Fact p.Prime]

theorem padicK1_zero_eq_integralSubgroup :
    padicK1 p 0 = LocalGL2.integralSubgroup ℤ_[p] ℚ_[p] :=
  congruenceK1_zero_eq_integralSubgroup (p : ℤ_[p])

end

section
variable (p : ℕ) [Fact p.Prime]

def centralGL : ℚ_[p]ˣ →* GL (Fin 2) ℚ_[p] :=
  Units.map (algebraMap ℚ_[p] (Matrix (Fin 2) (Fin 2) ℚ_[p])).toMonoidHom

end

section
variable (p : ℕ) [Fact p.Prime]

def IsCentralCharacterRep (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] (ω : ℚ_[p]ˣ →* ℂˣ) : Prop :=
  ∀ (u : ℚ_[p]ˣ) (v : V), centralGL p u • v = (ω u : ℂ) • v

end

section
variable (p : ℕ) [Fact p.Prime]

theorem centralCharacterRep_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] (hV : ∃ v : V, v ≠ 0)
    {ω ω' : ℚ_[p]ˣ →* ℂˣ} (hω : IsCentralCharacterRep p V ω)
    (hω' : IsCentralCharacterRep p V ω') : ω = ω' := by
  obtain ⟨v, hv0⟩ := hV
  have key : ∀ u : ℚ_[p]ˣ, (ω u : ℂ) = (ω' u : ℂ) := by
    intro u
    by_contra hne
    have hcne : (ω u : ℂ) - (ω' u : ℂ) ≠ 0 := sub_ne_zero.mpr hne
    have h3 : ((ω u : ℂ) - (ω' u : ℂ)) • v = 0 := by
      rw [sub_smul, ← hω u v, ← hω' u v, sub_self]
    exact hv0 (by
      calc v = ((ω u : ℂ) - (ω' u : ℂ))⁻¹ • (((ω u : ℂ) - (ω' u : ℂ)) • v) := by
            rw [smul_smul, inv_mul_cancel₀ hcne, one_smul]
        _ = 0 := by rw [h3, smul_zero])
  exact MonoidHom.ext fun u => Units.ext (key u)

end

section
variable (p : ℕ) [Fact p.Prime]

def HasNewvectorConductor (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    (c : ℕ) : Prop :=
  fixedSubmodule (padicK1 p c) V ≠ ⊥ ∧ ∀ m < c, fixedSubmodule (padicK1 p m) V = ⊥

end

section
variable (p : ℕ) [Fact p.Prime]

theorem hasNewvectorConductor_unique {V : Type*} [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V]
    {c c' : ℕ} (h : HasNewvectorConductor p V c) (h' : HasNewvectorConductor p V c') :
    c = c' := by
  rcases lt_trichotomy c c' with hlt | heq | hgt
  · exact absurd (h'.2 c hlt) h.1
  · exact heq
  · exact absurd (h.2 c' hgt) h'.1

end

section
variable (p : ℕ) [Fact p.Prime]

def IsIrreducibleGLRep (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] : Prop :=
  (∃ v : V, v ≠ 0) ∧
  ∀ W : Submodule ℂ V,
    (∀ g : GL (Fin 2) ℚ_[p], ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤

end

section
variable (p : ℕ) [Fact p.Prime]

def HasFiniteLevelFixed (V : Type*) [AddCommGroup V] [Module ℂ V]
    [DistribMulAction (GL (Fin 2) ℚ_[p]) V] [SMulCommClass (GL (Fin 2) ℚ_[p]) ℂ V] : Prop :=
  ∀ n : ℕ, Module.Finite ℂ (fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup p n) V)

end

end LocalNewvector

end
