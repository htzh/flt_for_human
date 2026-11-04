/-
  A hypothesis that is the same fact as a required instance, and is nevertheless
  invisible to instance search: `Fact (Nat.Prime p)`, `NeZero p`, and the composite
  `NeZero (M * p ^ a)`.

  ## Why this file exists

  `FunctionFieldGeneration/Capstone.lean`'s `hall_all` carries, twice, the pair

      have hp : p.Prime := Nat.minFac_prime h1
      have : Fact (Nat.Prime p) := ⟨hp⟩

  The second line reads as a restatement of a fact already on the stack. It is not:
  `Fact` is a *class*, so a `have` of that type registers a **local instance**, while
  `hp : p.Prime` is a hypothesis and instance search never reads hypotheses.
  Deleting the line broke the build — not at the `Fact` binders of the statements
  being called, but at `NeZero (M * p ^ a)`, because the `NeZero` arrives through

      Fact (Nat.Prime p)  --Nat.Prime.one_lt'-->  Fact (1 < p)  --NeZero.of_gt'-->  NeZero p

  and hence at `NeZero (p ^ a)` and `NeZero (M * p ^ a)`.

  ## How to debug this shape

  The error names only the outer class (`failed to synthesize instance of type class
  NeZero p`); the chain is two instances deep and `set_option trace.Meta.synthInstance
  true in` is the only reliable way to see which link is missing. It also shows that the
  chain needs more than `Nat.Prime`: `NeZero.of_gt'` wants `Preorder ℕ` *and*
  `IsBotZeroClass ℕ`, so under `import Mathlib.Data.Nat.Prime.Basic` alone even the
  `[Fact (Nat.Prime p)]` binder form fails — for a reason that has nothing to do with
  `Fact`. The second import below is what supplies it; a reader who hits the error with
  a narrow import should suspect the order instances first, not the primality.

  ## What the examples below are

  Examples 1–2 and 5 are the positive chain; 3–4 are **re-runnable guards**, asserting
  with `fail_if_success` that instance search cannot get there from the hypothesis
  alone. If a future mathlib makes `p.Prime` an instance route to `NeZero`, the guards
  fail loudly instead of silently making the port's `have` lines redundant. Example 6
  shows why the line appears twice in one proof: a local instance is scoped to its
  block, and `hall_all`'s two halves each introduce their own prime.

  Not part of the port: no `spec-pin:` wire, nothing imports it. `Reserve` is built by
  default (`lake build`), so it stays green.

  The refactor's other technical hazards are catalogued in
  `../../topics/functionFieldGeneration/TOPIC-refactor-friction.md` §1.
-/
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Ring.Nat

set_option autoImplicit false

/-! ## 1–2. The local instance is what instance search reads -/

/-- An anonymous `have` of a class type is registered as a local instance. -/
example (p : ℕ) (hp : p.Prime) : NeZero p := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  exact inferInstance

/-- Naming it changes nothing: the registration is by type, not by name. -/
example (p : ℕ) (hp : p.Prime) : NeZero p := by
  have h : Fact (Nat.Prime p) := ⟨hp⟩
  exact inferInstance

/-! ## 3–5. Guards, and the same goal once the instance exists -/

/-- A hypothesis is not an instance: with no local instance, `inferInstance : NeZero p`
fails even though `hp : p.Prime` is in the context. -/
example (p : ℕ) (hp : p.Prime) : NeZero p := by
  fail_if_success exact inferInstance
  exact ⟨hp.ne_zero⟩

/-- The same at the composite side condition, which is the shape `hall_all` needs:
`NeZero (M * p ^ a)` is out of reach until the primality is an instance. -/
example (M a p : ℕ) [NeZero M] (hp : p.Prime) : NeZero (M * p ^ a) := by
  fail_if_success exact inferInstance
  exact ⟨mul_ne_zero (NeZero.ne M) (pow_ne_zero _ hp.ne_zero)⟩

/-- … and in reach as soon as it is one. This is the state the port's proof is in, and
why the proof never mentions `NeZero` explicitly. -/
example (M a p : ℕ) [NeZero M] (hp : p.Prime) : NeZero (M * p ^ a) := by
  have : Fact (Nat.Prime p) := ⟨hp⟩
  exact inferInstance

/-! ## 6. Why the line appears twice in one proof

A local instance is scoped to the block that declares it. `hall_all`'s two halves
each introduce their own prime — one from the `Gen` reduction's hypothesis, one from
`d.minFac` — so each needs its own registration. -/

example (p q : ℕ) (hp : p.Prime) (hq : q.Prime) : NeZero p ∧ NeZero q := by
  constructor
  · have : Fact (Nat.Prime p) := ⟨hp⟩
    exact inferInstance
  · -- `p`'s instance is out of scope in this branch, and `q`'s is not declared yet
    fail_if_success exact inferInstance
    have : Fact (Nat.Prime q) := ⟨hq⟩
    exact inferInstance
