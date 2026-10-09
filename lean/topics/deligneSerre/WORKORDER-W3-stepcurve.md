# WORKORDER-W3 — the odd Vélu step is the Vélu quotient

**Status: ready to dispatch (2026-10-08).** Third set of the `WeierstrassCurve` ready shelf,
scoped in [TOPIC-weierstrass-ready-shelf.md](TOPIC-weierstrass-ready-shelf.md) §2D. **One new
module.** This is the unblocked half of story D: its sibling
(`WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int`,
525 lines) is **blocked** by a co-import collision recorded in the topic's §5 and in
[`CARRY-FORWARD.md`](../../CARRY-FORWARD.md) — do not attempt it. No existing module is
edited; **no promotion, no definition-layer work** (§0).

| order | module | headline | `S_` file |
|---|---|---|---|
| 1 | `FLTForHuman/WeierstrassCurve/Velu/StepCurveSubgroup.lean` | `WeierstrassCurve.stepCurve_stepSubgroup_eq_of_prime_ne_two` | `S_…_stepCurve_stepSubgroup_eq_of_prime_ne_two.lean` (235) |

## 0. What is already in the port

Every definition the statement names is public, and the whole import cone is collision-free
(verified by the reviewer: none of `Velu/CyclicQuotientJ.lean`, `Velu/Defs.lean`,
`Velu/Discriminant.lean` reaches either `IsogenyEndDatum/Engine.lean` or
`Velu/RestrictAlong.lean`):

* `WeierstrassCurve.{stepCurve, stepSubgroup, subgroupOfX, xVeluCurve}` —
  `FLTForHuman/WeierstrassCurve/Velu/CyclicQuotientJ.lean` (defs at lines 142, 168, 165, 93).
* `WeierstrassCurve.{oddOrderSummingSet, veluQuotient, veluX, veluY}` —
  `FLTForHuman/WeierstrassCurve/Velu/Defs.lean` (289, 87, 163, 231).
* The target's **only** premise, `WeierstrassCurve.isOddVeluSet_oddOrderSummingSet` — public
  in `FLTForHuman/WeierstrassCurve/Velu/Discriminant.lean:52`. Import it; do not re-derive.

The pin `S_` file sets **no** `set_option` and carries no `attribute` scaffolding — write
none, and keep the pin's `omit [DecidableEq L] in` where it occurs (it is what keeps the
checker's text matching while the proof has the variable out of scope).

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem` (read-only;
never modify). **Statement = the `Theorems/Thm_…` wrapper**, binders verbatim; proof = the
matching `P2M/Sol/S_…` file (235 lines; `fst_coordsOrZero_neg` et seq. from line 18, `sigma_eq_of_eq`
at 210, `solution` at 218).

Public mirror, pinned:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two.lean>.

## 2. The statement (verbatim from the wrapper)

```lean
universe u in
theorem WeierstrassCurve.stepCurve_stepSubgroup_eq_of_prime_ne_two
    {L : Type u} [Field L] [DecidableEq L] (E : WeierstrassCurve L)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (H : AddSubgroup E.toAffine.Point) [IsAddCyclic H] [Finite H]
    (Q : E.toAffine.Point) (hQH : Q ∈ H) (hQ : addOrderOf Q = ℓ)
    (φ : E.toAffine.Point →+ (E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2))).toAffine.Point)
    (hφker : φ.ker = AddSubgroup.zmultiples Q)
    (hφ : ∀ (x y : L) (h : E.toAffine.Nonsingular x y),
      (.some x y h : E.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
        ∃ h', φ (.some x y h) = .some (E.veluX (E.oddOrderSummingSet Q (ℓ / 2)) x)
          (E.veluY (E.oddOrderSummingSet Q (ℓ / 2)) x y) h') :
    (⟨E.stepCurve H ℓ, E.stepSubgroup H ℓ⟩ : Σ V : WeierstrassCurve L, AddSubgroup V.toAffine.Point) =
      ⟨E.veluQuotient (E.oddOrderSummingSet Q (ℓ / 2)), H.map φ⟩
```

Only this headline is public. The pin's machinery (`fst_coordsOrZero_neg`, `subgroupOfX`
lemmas, the `Setup` block, `sigma_eq_of_eq`) stays `private` at the pin's leaf names.

**`sigma_eq_of_eq` is a recorded re-derivation, not a share.** The pin declares it publicly
(9 lines, `:210`) and `port_advise` matches it to a **port-`private`** declaration in
`WeierstrassCurve/Velu/CyclicQuotientJ.lean`. It is two lines of `Sigma` congruence glue, so
`TOPIC-weierstrass-ready-shelf.md` §4 records the decision: re-derive it `private` here, do
not open the hub to promote it. If you conclude a promotion is genuinely needed, stop and
report instead.

## 3. Route and risks

* The pin's proof is a coordinates-level identification: `stepCurve`/`stepSubgroup` are the
  abscissa-indexed (`xVeluCurve` + `subgroupOfX`) construction, and the statement says the
  `φ`-image of `H` is exactly the subgroup produced by the `oddOrderSummingSet` quotient.
  Keep the pin's `coordsOrZero` computations; they are what makes the two sigma pairs equal.
* `ℓ / 2` is *natural-number* division in the statement — with `hℓ2 : ℓ ≠ 2` and `ℓ` prime,
  it is `(ℓ-1)/2`. Do not replace it with anything else; the statement's text is fixed.
* Section-variable discipline: the pin has `variable {L} [Field L] [DecidableEq L]` and then
  `omit [DecidableEq L] in` before declarations that do not need it. Transcribe both; a
  typeclass moved from the section into a binder changes no elaborated type but does change
  the checker's text (the trap that has fired four times in this project).
* The pin is Lean `v4.33.1` / mathlib `db584cd6`; the port is `v4.34.0`. Expect drift; see
  `porting-playbook.md` §7 (in particular `if_neg` → `ite_eq_right`,
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, and self-base-change not being definitional).

## 4. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` when the file is done; **no
whole-tree build**. Bound everything:
`timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`,
`flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth`; on a timeout quarantine and bisect, and tell a blow-up from
contention by CPU time. Serial builds only. Do not commit. The module is a leaf.

## 5. The hub prohibition

**Do not edit any existing Lean module.** If a needed helper is `private` in a hub, re-derive
it locally as `private` in your module and report it. If a promotion seems genuinely required,
**stop and report** with the declaration, host, reason and
`python3 tools/deps/build_ladder.py --edit <host>` — the manager decides.

## 6. Wiring

In `lean/spec/check_flt_statements.py`, appending **last** so no earlier last-name match can
flip: the target's `Theorems/Thm_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two.lean`
and `P2M/Sol/S_WeierstrassCurve_stepCurve_stepSubgroup_eq_of_prime_ne_two.lean` to `SOURCES`;
`"FLTForHuman/WeierstrassCurve/Velu/StepCurveSubgroup.lean"` to `PORT_FILES`.

Run the checker **as soon as the module is written** (text-only, no build). Baseline:
**7233 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (7269 checked)**;
expected **+1** to 7234 with the one headline as the whole public surface. Any other delta is
statement drift to fix before building. Target **0 mismatched, 0 missing**, then mutation-test
the headline and revert.

## 7. Stop and report

If the statement cannot be matched without moving the pin's text; if the required
`Velu/` import cone turns out to reach `Velu/RestrictAlong.lean` (it should not); if a helper is
genuinely needed publicly and is `private` in a hub; or if a build exceeds its bound and
bisecting does not settle it.

## 8. Completion report

Module path; public/`private` counts; tier-0 warning count (target **0**) and wall/CPU; tier-1
wall/CPU; every local `private` re-derivation with its host; the checker before → after with
the `identical` delta reconciled and the mutation result; `#print axioms` for the headline
(`[propext, Classical.choice, Quot.sound]`); `git status --porcelain` showing only the set's
files; anything you could not match, quoted.

## 9. Outcome (2026-10-08, landed and manager-verified)

One new module, no existing Lean module edited, no promotion, nothing committed.

| module | lines | public / private | tier 0 | tier 1 |
|---|---:|---:|---:|---:|
| `WeierstrassCurve/Velu/StepCurveSubgroup.lean` | 298 | 1 / 13 | 4.0 s (manager re-run 0 warnings / 0 errors) | 5.2 s |

**Checker 7233 → 7234 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own
(7270 checked)** — +1, exactly the headline; the 13 private helpers are invisible. One-token
mutation (`Q (ℓ / 2)` → `Q (ℓ / 3)`) gave 7233/1/0 with the diff printed, reverted to 7234/0/0.
`#print axioms` on the headline: `[propext, Classical.choice, Quot.sound]`. Warning-free.
(The manager's own runs of the checker now read 7233 identical / 37 own — see the refactor
wave below, which removed exactly one declaration from the verified public surface.)

*Section discipline is load-bearing here and was verified:* deleting the pin's
`omit [DecidableEq L] in` before `fst_coordsOrZero_neg` produces exactly one
`unusedSectionVars` warning; keeping it gives none.

### Hub audit (manager, requested)

W3's order §5 forbids editing an existing module. Audited rather than taken on trust:

* **No tracked Lean module was modified by this set** — `git diff --name-only` shows only the
  checker wiring and the note files; the module is untracked-new.
* **12 of the 13 private helpers have no counterpart anywhere in the port**
  (`mem_zmultiples_of_nsmul_eq_zero_fintype`, `mem_zmultiples_of_nsmul_eq_zero`,
  `nsmul_eq_zero_of_mem_zmultiples`, `fst_coordsOrZero_neg`, `isOddVeluSet_S`,
  `exists_mem_S_of_zsmul`, `kernelXSet_eq`, `absSum_kernelXSet`, `stepCurve_eq`, `stepX_eq`,
  `coKernelXSet_eq`, `subgroupOfX_eq`) — searched by declaration pattern over all of
  `FLTForHuman`; nothing to import, correctly private.
* **One duplicate, and it stays private.** `sigma_eq_of_eq` is now a **third**
  port-`private` copy of a *pin-public* declaration (twins at
  `Velu/CyclicQuotientJ.lean:502` and `:747`, which is the pin's own two-copy shape at two
  section-variable spellings `L`/`B`). Per playbook §4(b)/§5 it is two lines of `Sigma`
  congruence glue — nothing another theory states or reuses — so the recorded decision stands:
  re-derive, do not promote. The trigger to revisit is a fourth consumer, or a consumer that
  needs it at a *statement* the pin exposes.
* **No unresolved promotion need.** The two adaptations the set records (`haveI` → an explicit
  `[Fintype H]` core plus a `[Finite H]` wrapper, and `Set.mem_setOf_eq` →
  `Set.mem_ofPred_eq`) are a linter and a mathlib deprecation respectively, neither a hub
  question.

### The sibling, unblocked

`WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int`
(525 lines) was parked on the `Engine`/`RestrictAlong` co-import collision. The refactor wave
of 2026-10-08 (see `PORTING-DeligneSerre.md` §1 and `logs/deligne-serre-friction.md`) renamed
this file's character-free `normFormulaAlong_of_elliptic` to `…_cf`, and **the whole
`zmultiples` premise union now elaborates in one environment** (probed). Nothing in *this*
module changes; the sibling can be ordered.
