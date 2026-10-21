# The χ₋₃ module's dead declarations — where they are and why

`FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean` used to carry the whole of the
pin's `S_EisensteinWeightOne_e1Chi3IsModular.lean` development. Only the five public headlines are
reachable: `e1Chi3IsModular`, `chiNegThree_mul`, `coeff_e1Chi3`,
`tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal`, `ModularForm.exists_weight_one_gamma1_three_slash_fricke_eq_smul`.

**Everything else (95 declarations, 944 lines) now lives in `ChiNegThreeDead.lean` beside this
note**, moved by `tools/deps/move_dead.py`; the headline module is the live core (2,486 lines,
`check_port.py` verifies 70 of its statements instead of 5, `lake build` 15 s).

## What was dead, and who else had it

`tools/deps/shapes.py` (577 237 shaped declarations, corpus `aa2d8b3`) splits the dead set by
whether any other pin file states the same thing:

| dead declarations | duplicated by | status |
|---|---|---|
| 25 | nowhere — project-unique | moved; these are the pin's only copy of their statements |
| 75 | `S_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal.lean` (B's file, the `S17E1` solution text inlined) | moved |
| 5 | `S_ModularForm_exists_weight_one_gamma1_three_slash_fricke_eq_smul.lean` (C's file, `A2Theta3`) | moved |
| 2 | `S_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.lean` | moved |
| 1 + 1 | LanglandsTunnell and CuspForm files, for `chiNegThree_mod` only | moved |

The split "move the unique ones, leave the B/C-shared ones" is **not separable**: the 8
declarations with outside-pin twins (`chiNegThree_one/three/mod/mul/pow`, `coeff_e1Chi3_of_ne_zero`,
`three_dvd_coeff_e1Chi3_of_ne_zero`, `three_dvd_coeff_e1Chi3_sub_one`) are referenced by the 75 — one
connected component. They all move together, which is harmless: the pin keeps every one of them.

## What the move cost, and the one hand fix

`move_dead.py` carries a declaration's prefixes (`@[...]`, docstring, `open … in`), never crosses a
`section`/`end`, closes the move set under dependencies and dead referrers, emits in dependency
order, and refuses to write a non-nesting result. Three traps it encodes, each found the hard way:
spans run past `end`; `noncomputable section` opens an anonymous scope that must be counted; and
references like `foo.mp` are uses of `foo`.

**One reference had to be qualified by hand** in the shelf:
`reprCountEqCoeffE1Chi3_of_splitPrimePowCount` used to sit inside `namespace HexInt`, so its
`orbitCountMultiplicative_holds` resolved unqualified; on the shelf it is written
`HexInt.orbitCountMultiplicative_holds`. A Lean-native version would get that from the environment
for free — which is the argument for doing this in Lean next time.
