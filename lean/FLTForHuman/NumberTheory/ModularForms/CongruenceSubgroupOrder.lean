/-
  A mathlib supplement: the order structure of the congruence subgroups along divisibility.

  `mathlib` has `CongruenceSubgroup.Gamma`, `Gamma1` and `Gamma0` with their membership lemmas but
  no order lemmas at all, while the two facts every level argument needs are

    `m ∣ n → Gamma n ≤ Gamma m`  and  `Gamma n ≤ Gamma1 n`, `Gamma n ≤ Gamma0 n`

  (the general chain being `Gamma n ≤ Gamma m ≤ Gamma1 m`, `Gamma0 m`).  The pin re-declares the
  monotonicity in **12** files (135 sites) and the inclusions in seven more, each proved from the
  `ZMod` membership in a few lines:

    `A ∈ Gamma n` means `A 0 0`, `A 1 1` are `1` and `A 0 1`, `A 1 0` are `0` in `ZMod n`;
    `ZMod.castHom h (ZMod m)` — available exactly because `m ∣ n` — pushes those entries to
    `ZMod m`; dropping the two upper entries gives the `Gamma1` inclusion, the lower-left one the
    `Gamma0` inclusion.

  This module is therefore a **tier-3 mathlib supplement** (playbook §2.3, §3.1): one mathlib
  import, `namespace CongruenceSubgroup` so that the lemmas are found by the `open
  CongruenceSubgroup` that every consumer already has, and no port dependency at all.  Their shape
  is the general one — both indices explicit — so consumers that cannot name them directly (the
  checker-listed silos, whose declarations must keep the pin's binder spellings) wrap them in one
  line.

  Pin provenance: `Definitions/Def_ModularCurve_X1.lean:158` and eleven `P2M/Sol/S_*` files, all
  with the same body; the two spellings in use are `{M' : ℕ} (h : M ∣ M')` (the `ModularCurve`
  side, and this is the one homed here) and `{N : ℕ} (h : M ∣ N)` (the `CuspForm` side), plus
  `{A B : ℕ} (h : A ∣ B)` in `DeligneSerre/Lifting.lean` as `gamma1_le_of_dvd`. A third pin
  spelling, `Gamma1_le_of_dvd' {M' : ℕ}`, is in
  `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean` and is wrapped in
  `ModularForms/WeightOne/RationalityDvd.lean`.

  A good candidate to upstream: with these in mathlib, the port's four `private` copies of
  `Gamma1_le_of_dvd` and its seven copies of `Gamma_le_Gamma1` disappear for good.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

namespace CongruenceSubgroup

/-- The principal congruence subgroup is `Γ₁`: congruent to the identity modulo `n` forces the
`1 1`-entry to be `1` and the `1 0`-entry to be `0`.  Mathlib has neither inclusion. -/
theorem Gamma_le_Gamma1 {n : ℕ} : Gamma n ≤ Gamma1 n := by
  intro A hA
  rw [Gamma_mem] at hA
  rw [Gamma1_mem]
  exact ⟨hA.1, hA.2.2.2, hA.2.2.1⟩

/-- The principal congruence subgroup is `Γ₀`: congruent to the identity modulo `n` forces the
`1 0`-entry to be `0`. -/
theorem Gamma_le_Gamma0 {n : ℕ} : Gamma n ≤ Gamma0 n := by
  intro A hA
  rw [Gamma_mem] at hA
  rw [Gamma0_mem]
  exact hA.2.2.1

/-- `Gamma` is antitone in the level: the principal congruence subgroup at a multiple of `m` sits
in the one at `m`. -/
theorem Gamma_le_of_dvd {m n : ℕ} (h : m ∣ n) : Gamma n ≤ Gamma m := by
  intro A hA
  rw [Gamma_mem] at hA ⊢
  obtain ⟨h00, h01, h10, h11⟩ := hA
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod m)) h00
    rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod m)) h01
    rwa [map_intCast, map_zero] at this
  · have := congrArg (ZMod.castHom h (ZMod m)) h10
    rwa [map_intCast, map_zero] at this
  · have := congrArg (ZMod.castHom h (ZMod m)) h11
    rwa [map_intCast, map_one] at this

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
