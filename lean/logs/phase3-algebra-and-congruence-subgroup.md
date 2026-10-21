# The `Algebra` and `CongruenceSubgroup` families — landed (nine of ten nodes)

**Status: landed 2026-10-20.** Two sets, **three modules, zero host edits, zero promotions, zero
marker entries**. Nine graph leaves / **1,161 pin `S_` lines** → **1,363 port lines**, **49
statement-checked declarations**. Checker **3,605 → 3,654 ok / 140 → 143 wired modules**, 0
mismatched / 0 missing / 11 own / 0 kw (corpus `aa2d8b3`). Tier-1 builds 2,194 / 2,026 / 3,581 jobs
at 9.45 / 6.19 / 6.5 s, **0 warnings**; all nine headlines' axioms
`[propext, Classical.choice, Quot.sound]`. Orders:
[topics/deligneSerre/WORKORDER-PH3C-algebra-norm-and-integrality.md](../topics/deligneSerre/WORKORDER-PH3C-algebra-norm-and-integrality.md),
[topics/deligneSerre/WORKORDER-PH3D-congruence-subgroup-lattice.md](../topics/deligneSerre/WORKORDER-PH3D-congruence-subgroup-lattice.md).

| module | lines | public | private | checker | build (jobs / s) |
|---|---:|---:|---:|---|---|
| `RingTheory/IntegralClosure/FunctionField.lean` | 410 | 10 | 0 | 10 ok | 2,194 / 9.45 |
| `RingTheory/Norm/Elementary.lean` | 88 | 3 | 0 | 3 ok | 2,026 / 6.19 |
| `NumberTheory/ModularForms/CongruenceSubgroupLattice.lean` | 865 | 36 | 5 | 36 ok | 3,581 / 6.5 |

The demand falls **1,248 → 1,239 nodes / 476,792 → 475,631 raw `S_` lines** — exactly the nine
files — and the leaf shelf **358 → 349**. The `Algebra.` namespace row is gone. The
`CongruenceSubgroup.` row reads **1 / 242**: its fifth node is a *lift*, not a port, and is deferred
with its price (§3).

## 1. The `Algebra` family (349 pin lines)

Five nodes, one per row of the phase-3 note's `Algebra` entry, which priced it at "5 / 349 / 13
publics, 1 module" — confirmed by measurement, except that the subject splits cleanly in two:

1. **`RingTheory/IntegralClosure/FunctionField.lean`** (rows 1–2) — the integral model of a function
   field: for `k` algebraically closed and `x` transcendental, the integral closure of `k[x]` in a
   finite `F/k(x)` is a finite `k[x]`-module; and for `f` with `F/L(f)` finite, any `z : F` has a
   nonzero `q₀ ∈ L[f]` with `q₀ z` in **every** valuation subring containing `L` and `f`. The pin's
   helper block keeps its own descriptive name `Algebra.FiniteIntegralClosureAdjoinSingleton`.
2. **`RingTheory/Norm/Elementary.lean`** (rows 3–5) — `norm (μ + nilpotent) = μ ^ finrank`,
   `norm (x : A × B) = norm x.1 * norm x.2`, `norm a = 1` on a subsingleton algebra. 34 pin lines,
   three declarations: the block a mathlib PR would append to `RingTheory/Norm/Basic.lean`, which is
   why the module sits in that directory (the port may not add to mathlib; a user looking for
   `Algebra.norm` facts looks there).

**The pin's `set_option maxHeartbeats 9600000` on row 2 is not needed — and that was measured, not
assumed.** The module is green at the 200,000 edit-loop cap *and* at 100,000, and a control at 20,000
fails with deterministic `whnf` timeouts at two sites, which proves the `-D` flag was live during the
passing runs. Largest whole-module elaboration: 11 s.

**One real drift, and it is the shadowing hazard the order predicted at a different name.** The
order warned that inside `namespace Algebra` an unqualified `norm_of_subsingleton` resolves to
mathlib's normed-group lemma. The actual failure came at `IsIntegral.of_finite`, which inside the
namespace resolves to the *instance* `Algebra.IsIntegral.of_finite`; the fix is the explicit
`_root_.IsIntegral.of_finite`. That is a general lesson for any port that states mathlib-subject
facts from inside mathlib's object namespace: the namespace is a resolution context, and
`Algebra.IsIntegral.*` is a class namespace, not just a naming convention.

## 2. The `CongruenceSubgroup` family — an exclusion reversed

The phase-3 note excluded this namespace in its §3 table: "`UpperHalfPlane.qExpansion_*`,
`CongruenceSubgroup.*` (~500 lines) | modular forms — FLT-flavoured subject, test 2". **That
exclusion was wrong, and the note's own caveat is why**: "read each `Theorems/` statement before
believing the namespace-based subject filter". Read against the statements, all five are group
theory of **mathlib's own congruence-subgroup API** — `Gamma`, `Gamma0`, `Gamma1`,
`ModularGroup.S`/`T`, `Subgroup.zpowers`, `Subgroup.relIndex`, `ZMod` — with no Weierstrass, no
modular form, no Hecke operator, no adele. They pass tests 2 (shape), 3 (mathlib-first negative) and
4 (no definition gate). The note also mispriced the row by half: the demand read **5 / 1,054**, not
"~500 lines".

Four of the five landed as `NumberTheory/ModularForms/CongruenceSubgroupLattice.lean` (865 lines,
36 public / 5 private — the pin's own private `Index.*` helpers stay private): the level-lowering
inclusion with a lower unipotent (406 pin lines), the `T`/`S`-adapted coset transversal (179), the
first-column membership criteria (142), and the relative-index formula (85). Test 1 (≤ ~250 pin
lines a node) is broken by the 406-line node; it is taken anyway and recorded as such — the family
is gate-free, the other four are 85–242, and that node is one development, not a gate.

**`det_eq` and `Gamma_le_Gamma1` were imported, not re-proved** (both public in the port, both
matching the pin's statement up to binder spelling). `det_eq` already has **seven** private copies
in the port; this set adds none. `Gamma_le_Gamma1`'s port copy is `CuspForm.LiNormSq.Gamma_le_Gamma1`
with `M` an implicit section variable, so the single call site reads
`CuspForm.LiNormSq.Gamma_le_Gamma1 (M := N) hγ`.

The set's one structural drift is a namespace-scope fact, not a proof: merging four files into one
module means node 3's file-level `open Matrix` shadows the root `zpow_neg`/`zpow_mul`/`zpow_sub` for
nodes 2 and 4 (six ambiguity errors), so it is scoped to `namespace FirstColumn` — the pin's own
file already writes `_root_.zpow_neg` in that spot for the same reason. The rest is 0-warning linter
work: `omit [NeZero N]` ×4, `haveI`→`have` ×4, `letI`→`let` ×2, six unused `simp` arguments, one
`linter.unreachableTactic` `ring`, one renamed unused binder. The pin's `set_option maxHeartbeats
3200000` (row 1) is not needed either.

## 3. The fifth node is a lift, and it is deferred

`CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three` ("`Γ₀(3)` is generated by `T`,
`U = !![1,0;-3,1]` and `-1`", 242 pin lines, 40 declarations) is **35/40 already in the tree**:
`port_advise` matches them byte-identically to the private `FLT.FLT.AnalyticCore.Gamma0Three` block
of `FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean` (two blocks, lines 899–1040 and
1064–1108, ~187 lines — the Schreier-generator / transversal engine ending in
`closure_schreierGens`). Only the `A2Gamma0Three` half (`U₃`, `gens`, `gens_subset_gamma0_three`,
`closure_T_U_neg_one_eq`, `mem_closure_gens`) is new.

So the landing is a **lift + dedup**, and the private copy is in the wrong module: the subject is
congruence-subgroup group theory, the host is an Eisenstein-series silo. The move is the manager's
(homing note §8.1's "touch ⇒ rectify"; playbook §4b–c), and it is deferred because of its price:
`build_ladder.py --edit` measures a **51-module / 30,597-line dependent cascade, ≈413 s to
re-elaborate** — a wave beyond the column's per-call 2-minute bound, which needs the user's explicit
exception. Registered with its trigger in [CARRY-FORWARD.md](../CARRY-FORWARD.md); the order's §8 has
the four steps.

## 4. The import lists (the reusable output)

The `import Mathlib` replacement is now a routine first step, and it is worth restating why: **86 s
to load `import Mathlib` on this checkout, 5–11 s for a targeted list** — a module that keeps the
monolith cannot be edit-looped at all.

* **`FunctionField.lean` (20)** — `Algebra.Algebra.Subalgebra.{Basic,Lattice}`,
  `Algebra.Algebra.Tower`, `Algebra.CharP.{Frobenius,Lemmas}`,
  `Algebra.GCDMonoid.IntegrallyClosed`, `Algebra.Group.Pointwise.Set.Finite`,
  `Algebra.GroupWithZero.NonZeroDivisors`, `Algebra.Ring.Subsemiring.Basic`,
  `FieldTheory.IntermediateField.Adjoin.Basic`, `FieldTheory.IsAlgClosed.Basic`,
  `FieldTheory.PurelyInseparable.{Basic,Exponent}`, `FieldTheory.SeparableClosure`,
  `RingTheory.Algebraic.Basic`, `RingTheory.DedekindDomain.IntegralClosure`,
  `RingTheory.Finiteness.Basic`, `RingTheory.IntegralClosure.IsIntegral.Basic`,
  `RingTheory.Noetherian.Basic`, `RingTheory.Valuation.LocalSubring`.
  Two prune rounds confirmed five more candidates are redundant (`FieldTheory.Separable`,
  `RingTheory.Adjoin.Basic`, `Algebra.CharP.Defs`, `Algebra.Algebra.Subalgebra.Pointwise`,
  `RingTheory.Localization.FractionRing`) — do not add them back.
* **`CongruenceSubgroupLattice.lean` (9 + 2 port)** —
  `Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`,
  `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup` (`ModularGroup.S`/`T` live there, not in the
  congruence-subgroup file), `Mathlib.GroupTheory.Index`, `Mathlib.Algebra.Field.ZMod` (subsumes
  `Data.ZMod.Basic` at `v4.34.0`), `Mathlib.Data.Nat.Factorization.Basic`,
  `Mathlib.Tactic.{FinCases,Linarith,LinearCombination,Ring}`, plus the port's
  `ModularForms.Analytic.NormSqPow` and `ModularForms.Defs.HeckeRepresentatives`.
* **`Elementary.lean` (3)** — the pin's own: `RingTheory.Norm.Basic`,
  `LinearAlgebra.Eigenspace.Zero`, `LinearAlgebra.Charpoly.BaseChange`.

## 5. Residuals

* **`CongruenceSubgroup.closure_T_U_neg_one_eq_Gamma0_three`** — the lift (§3), priced and
  registered, blocked on the user's exception for a >2-minute wave.
* **`CongruenceSubgroupLattice.lean` is 865 lines with one 406-line node**, above the phase-3 note's
  size test. Splitting it would put the level-lowering inclusion in its own module; there is no
  consumer that wants only part of it, so it stays one module until one appears.
* **`Algebra.norm_prod` / `norm_of_subsingleton` are root-`Algebra` names that a *normed-space*
  `norm_prod` / `norm_of_subsingleton` already occupies at root** in mathlib
  (`Analysis/Normed/{Ring,Group}/Basic.lean`). No collision (different namespace), but any future
  proof inside `namespace Algebra` that means the normed one must qualify it — the mirror of the
  `IsIntegral.of_finite` failure in §1.
* **The `CongruenceSubgroup` exclusion in the phase-3 note is corrected there**, with the reason, so
  the next session does not re-derive it. The general lesson is the note's own: a namespace is not a
  subject, and an exclusion by subject must quote the statement it read.
