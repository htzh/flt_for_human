# SET-AF42 — the Casimir trichotomy and the growth of the torus-system solutions

**Status: LANDED 2026-11-12** — §1–3 the rows, price and manager's layer, §5 the forecast, §6 the landing record. Read off the D–S shelf with
the recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md),
on the read SET-AF41's landing left. Forty-second set of the column; it is the continuation SET-AF41 §7
named by hand.

**4 rows / 1,523 silo / 1,442 net (`port_plan`) in ≈1,400 written lines and 54 declaration groups**, of
which **0 lines are already in the port**: a pure transcription set whose *proofs* consume the four
headlines SET-AF41 landed.

| # | row (`LanglandsTunnell.` dropped) | silo | lev | what it says |
|---|---|---:|---:|---|
| **1** | `casimir_pos_or_discrete_or_zero_of_weightSet` | 139 | 2/2 | a non-empty weight set `S ⊆ ℤ` closed under `±2` where the two Casimir forms are non-negative forces `λ > 0`, or `λ = k(k−2)/4` for some `k ≥ 2` with `S` above `|k|` and of the parity of `k`, or `λ = 0` with `0 ∈ S` |
| **2** | `norm_le_mul_rpow_of_torus_system_of_casimir_ne_of_re_eq` | 377 | 1/1 | if `λ ≠ λ'` or `n` is odd, and `Re λ = Re λ'`, then the string's components grow at most like `y ^ δ` on `(0,1]` |
| **3** | `exists_norm_le_mul_rpow_of_torus_system_even_casimir_real_nonpos_of_bounded` | 508 | 1/1 | for even `n`, real `λ = λ' ≤ 0`, the components are bounded on `(0,1]` |
| **4** | `exists_pos_norm_le_mul_rpow_of_torus_system_casimir_eq_real_pos` | 499 | 1/1 | for real `λ = λ' > 0`, the components grow at most like `y ^ δ`, with the Bessel normal form supplying the exponent |

## 0. The read

The read SET-AF41's landing left (corrected per §0 of the recipe — five `ModularCurve` phi markers
unported, and this set's own scaffolds do not yet exist):

| figure | value |
|---|---|
| `needed [F terminal]` | **737 / 307,988** |
| `needed [literal]` | 753 / 313,407 |
| frontier F | 1,674 / 816,540 |
| ready rows | 53 / 10,555 |
| leaves | 195 / 48,899 |
| `LanglandsTunnell` demand | **28 / 12,132** |
| `AutomorphicForm` demand | 260 / 113,790 |
| withheld | 4 rows |

**The premise audit is the set's whole risk, and it is clean.** The four pin files cite exactly the five
`S_` files of SET-AF41 — `Theorems/Thm_LanglandsTunnell_norm_le_mul_rpow_near_zero_of_first_order_euler_of_forcing`,
`…_of_bessel_ode_of_forcing_of_apriori`, `…_of_first_order_system_of_diag`,
`…_norm_le_mul_rpow_half_sub_abs_re_near_zero_of_whittaker_ode` and
`…_of_whittaker_ode_of_forcing` — all five ported, all five verified by `check_port` in SET-AF41. There is
no other `Theorems/` import in the four files, so the set is a *consumer* set in the AF9 sense: new
mathematics whose glue is already in the tree.

**The definition gate is empty.** The four wrappers import `Mathlib.{Data.Int.Basic, Data.Real.Basic,
Analysis.SpecialFunctions.Pow.{Real,Deriv}, Analysis.SpecialFunctions.Sqrt, Analysis.Calculus.Deriv.Basic,
Analysis.Complex.{Basic,RealDeriv}, Topology.Order.Compact, Algebra.Group.Even}` and `P2M.Util` — not one
`Definitions/Def_*` line (FR-0049's check, run by hand over the wrappers).

## 1. The rows, and why these four

SET-AF41 readied these three growth rows by name and §7 of its brief said they are AF42; the fourth,
`casimir_pos_or_discrete_or_zero_of_weightSet`, is the case split they all follow and is the edge the
`CuspidalConstituent` rows consume. Together they are one statement about one object: **the growth near
`y = 0` of an `n`-step `SU(2)`-string solving the `GL₂(ℂ)` Whittaker system is decided by the Casimir
eigenvalue `λ`**, in its three regimes.

**The return is zero, and the brief says so.** `af24-return.py` over the four: *readied: none*. The torus
rows' consumers (`AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_…`)
each need **two or more** additional premises, so this is a chain head, not a gate — the AF24/AF33 shape,
where the value is the cone movement (1,523 silo) and the fact that the string growth becomes usable, not
an immediate readiness event.

## 2. The price

| figure | value |
|---|---:|
| raw `S_` lines | 1,523 |
| declaration lines | 1,453 |
| — duplicate copies | 11 |
| — boilerplate | 70 |
| distinct declaration groups | 54 |
| once-cost after dedup | 1,442 |
| already in the port | **0** |
| **net new math lines** | **1,442** |
| written (one order) | ≈1,400 |

`port_advise` reports **no substitute, no port-once block, no sibling pair** — the four pin files share no
declaration. One type-only false positive (`G` matched to `ModularCurve.LevelN.CuspVanish.G`) is refused:
the port's `AlphaAux.G` is the string's component functional `G n f i` and keeps the pin's name.

## 3. The manager's layer, landed (do not redo it)

1. **The module exists, elaborates and is checker-green.**
   `FLTForHuman/LanglandsTunnell/TorusSystemGrowth.lean`, 421 lines: the header with its eight
   `spec-pin:` lines, two port imports (`…LanglandsTunnell.ODENearZeroBounds` and
   `…LanglandsTunnell.WhittakerODENearZero`, which is where the five consumed headlines live) plus six
   mathlib imports, and the pin's own structure — the four inner namespaces `UnitClass17`, `AlphaAux`
   (three blocks, as in the pin), `GammaP41`, `RoadBeta40` nested under `LanglandsTunnell`, and the four
   headlines at `LanglandsTunnell.<wrapper name>`.
   `python3 spec/check_port.py --force …TorusSystemGrowth.lean` reads **54 ok / 0 mismatch / 0 missing**
   and `lake build` succeeds: **every public statement of the four pin files is verified verbatim**, and
   41 declarations still carry `sorry`. The fourteen data definitions (`qR`, `G`, `aC`, `uC`, `vC`, `αC`,
   `βC`, `δ`, `χ`, `Bn`, `HSys`, `K`, `Kc` and `Kc_nonneg`) are already transcribed.
2. **No `own:` row, no marker, no `set_option` beyond `autoImplicit false`.** The pin's
   `set_option maxHeartbeats` (one file carries one) is **not** carried: the order must fit the default
   200,000 budget or report its measured cost.
3. **What the worker owns**: the 41 `sorry` bodies, and nothing else — no statement, no import, no
   namespace and no `spec-pin:` line may change.

## 4. Orders and gates

`tmp/af42/WORKORDER-AF42-torus-system.md`. One order, one module, no insertion. The standard gates:
`check_port --force` at **54 ok / 0 mismatch / 0 missing**, axioms clean on the four headlines, the
module's own `lake build` under `flock`/`timeout` with no tree build, silence and zero warnings,
`dedup --within --module TorusSystemGrowth` and `move_dead`, and one `spec/` consumer zone with a real
composition.

## 5. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 737 / 307,988 | **733 / 306,465** |
| `needed [literal]` | 753 / 313,407 | **749 / 311,884** |
| frontier F | 1,674 / 816,540 | **1,678 / 818,063** |
| ready rows | 53 / 10,555 | **50 / 9,171** |
| leaves | 195 / 48,899 | **194 / 48,760** |
| `LanglandsTunnell` demand | 28 / 12,132 | **24 / 10,609** |
| rows readied | — | **0** (measured, §1) |

## 6. The landing (2026-11-12)

One order, one module, all gates green, nothing left undone.

| order | module | lines | proofs | `check_port` | build | axioms |
|---|---|---:|---:|---|---:|---|
| **42** | `LanglandsTunnell/TorusSystemGrowth.lean` | 421 → **1,561** (1,179 proof-body lines) | 41 | **54 ok / 0 / 0** | 18 s, silent | 4/4 clean |

**What it consumed**: 4 rows / 1,523 silo in 1,179 written proof lines over the verified 421-line
scaffold — 1,561 module lines for 1,523 silo, 1.03 lines per silo line, the highest ratio of the column
and exactly what a pure transcription with no composition should cost.

**The composition worked as designed.** The set's four pin files cite the five `S_` files of SET-AF41, and
`AlphaAux.main` composes them unchanged: one call to AF41's `norm_le_mul_rpow_near_zero_of_first_order_system_of_diag`
(through the port's own `sysN`) with `ha := aC_re`, `hG := G_differentiableOn`, `hrow := row`,
`hB := norm_Bn_le`, then `f_eq` reassembles the string's components from the transformed functional. The
pin's exponent `1 − ε` survived, and `norm_block_le`/`norm_Bn_le` feed the same `hB` slot the pin feeds —
the only change on that path is the deletion of a no-op `beta_reduce`.

### 6.1 Deviations held for review

1. **Three mathlib imports added**: `Mathlib.Tactic.IntervalCases` (`interval_cases`), and
   `Mathlib.FieldTheory.IsAlgClosed.Basic` + `Mathlib.Analysis.Complex.Polynomial.Basic` (the
   `IsAlgClosed ℂ` instance the former needs — verified necessary by dropping it). `P2M.Util` was **not**
   needed: its only role in these files is `p2m_open`/`p2m_export`, and the one premise the pin calls
   already resolves at `LanglandsTunnell.…`.
2. **v4.34 deprecation and linter fixes, all statement-preserving**: `push_neg` → `push Not` (three sites),
   `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` (seven), `beta_reduce` dropped (a no-op under v4.34's
   `unusedTactic`), and six `convert … <;> try rfl`-style trailing blocks shortened because v4.34's
   `convert` already closes the goal (three sites) or because the sequence point is flagged by
   `unnecessarySeqFocus` (two). No `set_option` was needed and **the pin's own heartbeat overrides were
   not carried**: the default 200,000 sufficed (21 s of elaboration for 1,561 lines).
3. **One unused pin binder**: `AlphaAux`'s headline never uses `hκ : κ ≠ 0`, so the port names it once
   (`have hκ₀ : κ ≠ 0 := hκ`) rather than renaming the binder or silencing the linter — the same device as
   SET-AF41B's Bessel headline (FR-0164), now on its second use.
4. **Two of the order's suggested consumer compositions could not be typed, and both are mathematics, not
   errors**: `S = {2}` admits no `λ` at all (the `±2` closure forces `4 ∈ S` while the two Casimir forms
   force `λ = 0`), so the trichotomy was read at `S`'s closure `{n ≥ 2, n even}`, which lands in the
   **discrete** disjunct with `k₀ = 2`; and `λ = λ' = 0` cannot feed the `RoadBeta40` headline (it carries
   `0 < lam.re`), so the two regimes were read at `λ = 0` and `λ = 1` and compared by the meet
   `min δ_G δ_R` — which is the right comparison, because a bound at `β` gives one at every `β' ≤ β` on
   `(0,1]`.
5. **`dedup` 1 cluster, kept**: the pin's own `main`/`solution` pair (a private worker and the public
   headline with the identical statement), 18 removable lines; the checker's 54-name surface needs the
   public headline at the pin's name and the pin marks the worker `private`. `move_dead`: **0 dead**.

### 6.2 The re-read, exact on all six cells

Taken after AF42 landed and before the wave's other two orders landed (their seven rows unported, and the
five `ModularCurve` phi markers of §0 unported, i.e. the corrected reading):

| figure | before | forecast | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 737 / 307,988 | 733 / 306,465 | **733 / 306,465** ✓ |
| `needed [literal]` | 753 / 313,407 | 749 / 311,884 | **749 / 311,884** ✓ |
| frontier F | 1,674 / 816,540 | 1,678 / 818,063 | **1,678 / 818,063** ✓ |
| ready rows | 53 / 10,555 | 50 / 9,171 | **50 / 9,171** ✓ |
| leaves | 195 / 48,899 | 194 / 48,760 | **194 / 48,760** ✓ |
| `LanglandsTunnell` demand | 28 / 12,132 | 24 / 10,609 | **24 / 10,609** ✓ |

**Rows readied: none**, as §1 measured before dispatch — the set is a chain head, and the three torus rows'
consumers each still owe two or more premises.

## 7. What this set does not do

- **The `CuspidalConstituent` consumers** of the trichotomy
  (`casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_exists_isComplex` and its
  `_forall_isReal` sibling) stay: each needs the arch-type lattice rows and the cusp-submodule
  membership facts, so they are their own set.
- **The `gl₂`-complex Whittaker-system rows** the AF36 engine readied are still on the ready block:
  `linearDependent_string_of_gl2Complex_whittaker_system_of_moderateGrowth` (361) and
  `exists_rpow_bound_near_zero_of_whittaker_ode_of_discrete_tower_of_moderateGrowth` (329). They are the
  *system* form of AF36's two engines and feed `exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String`
  (473), which also needs the 681-line hypotheses row — a three-row set of its own.
- **The `TateLocal` ready rows** (305, 128, 100) and the ten `TateLocal` leaves are a different subject
  (the local zeta integral), not this one.
