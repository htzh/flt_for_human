/-
  A mathlib supplement: `Gamma1` is antitone along divisibility.

  `mathlib` has `CongruenceSubgroup.Gamma1` and `Gamma1_mem` but no order lemma for it, while the
  level-monotonicity fact `m ∣ n → Gamma1 n ≤ Gamma1 m` is needed by every level-changing
  construction: level restriction and level-raising (`DeligneSerre/Lifting.lean`), the diamond and
  `GammaH` operators (`ModularCurve/{X1,XH,FullLevel}/*`), the integral-weight-one layers
  (`ModularForms/WeightOne/*`) and the nebentypus Hecke bound
  (`ModularForms/Analytic/NormSqLt.lean`).  The pin re-declares it in **12** files and uses it at
  135 sites, and it proves it from `Gamma1_mem` in three lines:

    `A ∈ Gamma1 n` means the three entries below `A 0 0`, `A 1 1` are `1` and `A 1 0` is `0`
    in `ZMod n`; applying `ZMod.castHom h (ZMod m)` (which is available exactly because `m ∣ n`)
    pushes those three equations to `ZMod m`, which is `A ∈ Gamma1 m`.

  This module is therefore a **tier-3 mathlib supplement** (playbook §2.3, §3.1): one mathlib
  import, `namespace CongruenceSubgroup` so that the lemma is found by the `open
  CongruenceSubgroup` that every consumer already has, and no port dependency at all.  Its shape
  is the general one — both indices explicit — so consumers that cannot name it directly (the two
  checker-listed silos, whose declarations must keep the pin's binder spellings) can wrap it in
  one line.

  `Gamma0_le_of_dvd` is the companion fact for `Gamma0` (also absent from mathlib, also re-derived
  in `DeligneSerre/Lifting.lean`).

  Pin provenance: `Definitions/Def_ModularCurve_X1.lean:158` and eleven `P2M/Sol/S_*` files, all
  with the same body; the two spellings in use are `{M' : ℕ} (h : M ∣ M')` (the `ModularCurve`
  side, and this is the one homed here) and `{N : ℕ} (h : M ∣ N)` (the `CuspForm` side), plus
  `{A B : ℕ} (h : A ∣ B)` in `DeligneSerre/Lifting.lean` as `gamma1_le_of_dvd`. A third pin
  spelling, `Gamma1_le_of_dvd' {M' : ℕ}`, is in
  `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean` and is wrapped in
  `ModularForms/WeightOne/RationalityDvd.lean`.

  A good candidate to upstream: with it in mathlib, `CongruenceSubgroup.Gamma1_le_of_dvd` would
  replace this file and the port's four `private` copies disappear for good.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

namespace CongruenceSubgroup

/-- `Gamma1` is antitone in the level: a matrix congruent to the identity modulo `n` is also
congruent to the identity modulo any `m` dividing `n`. -/
theorem Gamma1_le_of_dvd {m n : ℕ} (h : m ∣ n) : Gamma1 n ≤ Gamma1 m := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h00, h11, h10⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod m)) h00
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod m)) h11
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod m)) h10
    rwa [map_intCast, map_zero] at this

/-- `Gamma0` is antitone in the level: a matrix whose three upper entries are `0`/`1` modulo `n`
is so modulo any `m` dividing `n`. -/
theorem Gamma0_le_of_dvd {m n : ℕ} (h : m ∣ n) : Gamma0 n ≤ Gamma0 m := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have := congrArg (ZMod.castHom h (ZMod m)) hA
  rwa [map_zero, map_intCast] at this

end CongruenceSubgroup
