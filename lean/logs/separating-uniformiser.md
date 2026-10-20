# A uniformiser at a place is a separating element — landing record

The D-S demand's ready-shelf leaf `AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one` (455 pin
lines, cited by **23** theorems) **and its exact twin**
`…_of_ord_ne_zero_of_cast_natAbs_ne_zero` (460), landed as **one module, 149 lines, two
statement-checked headlines**, over a **three-declaration promotion in the Frobenius-subfield
engine**. Orders: [topics/algebraicCurve/WORKORDER-SU1-separable-uniformiser.md](../topics/algebraicCurve/WORKORDER-SU1-separable-uniformiser.md).

The statement: for `K` perfect, `F` algebraic over some `K(x)`, and `v` a place of `F` over `K`, an
element `t` of order one at `v` separates `K(t) → F`; more generally an element of nonzero *tame*
order does.

## 1. Measured

```bash
cd lean
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Place/SeparableUniformiser.lean
# [ok]  2 ok, 0 mismatch, 0 missing, 0 own, 0 kw
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean
# [ok]  4 ok, 0 mismatch, 0 missing        (3 promotions + the pre-existing headline)
python3 spec/check_port.py --all
# 1822 ok, 0 mismatch, 0 missing, 4 own, 0 kw — 47 module(s), 583 exempt (PORT_FILES)
python3 spec/unwired_register.py --check
# unwired_register: register is current
```

* Tier-1 build 2,694 jobs / 3.9 s; host 1,975 jobs / 6.5 s; the host edit's **dependent wave**
  4,329 jobs / 42 s, green. The one warning in the wave log is `QExpModL`'s pre-existing
  `unusedSectionVars`, not this set's.
* `#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`.
* Grep sweep clean on both edited modules. One narrow `haveILetI` suppression (the tame helper's
  `haveI := hchar`) and one on the engine's instance walls; no `maxHeartbeats` override — the
  twin's `synthInstance.maxHeartbeats 800000` is **not** inherited.
* `git status`: the two set files, the host module, and one line removed from
  `spec/old_check_stmts.py` (the host's `PORT_FILES` handoff).
* `spec/old_check_stmts.py` is not run (§4).

## 2. What this set is a case of: the twin rule, and a substitution not a re-proof

**The twin rule.** The two pin `S_` files differ by **33 diff lines** (three imports, the namespace,
one `synthInstance.maxHeartbeats`, the order helper, one hypothesis of `solution`); everything else
is byte-identical. Cutting one without the other would pay the same pre-round twice, so both heads
land together — and the two `solution` bodies, identical modulo how "never a `p`-th power" is
obtained, are written **once** as `separable_of_transcendental_of_forall_not_pow`.

**The substitution.** The pin proves a private `isSeparable_of_not_pow_mem_range` in *both* silos,
via `D_pow_eq_zero` (a `p`-th power has vanishing Kähler differential), `Subsingleton Ω[F⁄E]` and
`FormallyUnramified.isSeparable`. The port already has that theorem in general form,
`Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq`
(`Algebra/IsSeparableFrobenius.lean`, from the pin's own
`S_Algebra_IsSeparable_of_finrank_fieldRange_frobenius_eq.lean`); the pin's version is the same
statement with `frobeniusSubfield M p` written out as `(frobenius M p).fieldRange` and
`∀ a, a ^ p ≠ t` in place of `algebraMap y ∉ fieldRange`. So the port **calls** it and ports
neither helper (§3 of the order): 93 net new lines where a literal transcription would have been
≈430.

## 3. The host edit: three promotions and a handoff

`port_advise` found 19 of the 23 pin declarations already byte-identical in the port — 18 of them
**private** in `AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean`, the shared engine the
archimedean-style consumers re-derive across eight pin silos. Private declarations are not
importable, so the pre-round promotes exactly what a consumer *states*:

* `frobeniusSubfield` — the `p`-th-power subfield itself (the object of the subject),
* `finrank_frobeniusSubfield_adjoin_transcendental` — its index for a transcendental simple adjoin,
* `finrank_frobeniusSubfield_eq` — its transport across a finite extension.

The other fifteen stay private: their proofs are internal to the host. Because a promoted
declaration in a frozen-registry module would be verified by nothing under the one-checker
protocol, the same edit **hands the host over**: `spec-pin:` lines in (its wrapper + its `S_` file),
`PORT_FILES` entry out. The checker verifies all four public declarations, including the three
promotions, against the host's own pin files — so nothing about the engine is now unverified.

Priced first (`build_ladder --edit`): 5 dependent modules / 1,752 lines ≈ 26 s; built once, green.

## 4. Checker policy this landing applies

`spec/check_port.py` is the checker. The façade carries four `spec-pin:` lines — the two wrappers
and the two `S_` files — and **no** in-source per-declaration marker: both headlines match their
wrappers by exact name and statement hash, so `spec/decl_markers.tsv` gained nothing. The host's
four declarations match by last name + hash through the checker's pin-private fallback, which is
what a promotion is verified by. `spec/old_check_stmts.py` was not run; the only change to it is
the handoff deletion of the host's entry.

## 5. Step-6 re-read (`frontier.py --ds …`)

* `needed` **1,365 → 1,364** nodes and **506,411 → 505,956** raw `S_` lines in the D-S cone;
  `F` 1,001 → 1,003 nodes. (The twin's own cone is 3 nodes / 555; it was priced outside the D-S
  closure's `needed` before, and both targets now read `needed 0` / "target is ported".)
* The ready shelf reads **89** and this landing created the top four `Place` rows:

| row | silo lines | cone (ported / total) |
|---|---:|---|
| `AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable` | **576** | 5 / 6 nodes, 274 lines |
| `AlgebraicCurve.Place.diffCoeff_smul_D_of_ord_eq_one` | 28 | 4 / 5, 614 |
| `AlgebraicCurve.Place.diffCoeff_smul_D_eq_of_ord_eq_one` | 26 | 4 / 5, 613 |
| `AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable` | 20 | 38 / 39, 2,967 |

The first is the next cut of the family: the `ordDiff`-nonnegativity half of the differential
layer, which the two `diffCoeff` rows then consume.

## 6. Residuals

* The three private helpers of the façade (`not_pow_of_ord_eq_one`, its tame twin, and the engine
  body) are private as in the pin: no other theory states them. If a later silo wants the tame
  helper, the host (`IsCurveOver/FrobeniusSubfield.lean`) is not its home — it is place arithmetic,
  and `Place/OrdCalculus.lean` is.
* The pin's `D_pow_eq_zero` remains unported on purpose: `Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq`
  carries its own copy of the argument, and a second home would be a duplicate, not a dedup.
* The host's other fifteen private declarations stay private; the archTestFactor-style "promote the
  whole engine" move was deliberately *not* taken, because no consumer states them and the checker
  delta would have been +15 with no reader.
