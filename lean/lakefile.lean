import Lake
open Lake DSL

-- A small study project: self-contained fragments of the FLT formalization,
-- adapted to our own taste. We deliberately do NOT require the FLT project or
-- import its modules -- those builds are enormous -- so this project only
-- depends on mathlib.
package flt_for_human where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`maxHeartbeats, (4000000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib FLTForHuman where
  globs := #[.submodules `FLTForHuman]
