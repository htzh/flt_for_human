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

-- One library holding both efforts, organised by subject:
--   FLTForHuman/Elliptic     -- the `#E[n] = n²` port (verified, no `sorry`)
--   FLTForHuman/ModularCurve -- the `functionFieldGeneration` definitions
-- Layer 0 carried no `sorry`, so the two are no longer separate build targets.
@[default_target]
lean_lib FLTForHuman where
  globs := #[.submodules `FLTForHuman]
