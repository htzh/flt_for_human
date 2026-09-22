/-
Sanity module for the `lean/` study project.

This file has no mathematical content: it only checks that the Lake project,
the pinned mathlib release, and the community-built cache are wired up. The
actual FLT fragments live in sibling modules.
-/
import Mathlib

namespace FLTForHuman

/-- A trivial check that mathlib is importable and the toolchain works. -/
example : (2 : ℕ) + 2 = 4 := rfl

/-- A mathlib lemma is reachable (not just the prelude). -/
example : Nat.Prime 5 := by norm_num

end FLTForHuman
