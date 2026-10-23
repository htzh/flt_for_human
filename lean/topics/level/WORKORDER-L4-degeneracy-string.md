# WORKORDER-L4 — the degeneracy string of a Γ₁ eigenform: its `T_ℓ` and `U_q` action

**Status: landed (2026-10-22)** — see §8. Pure addition: **one** new module, no existing module
edited, one dispatch. The two headlines are the pin's `M4bOld` and `M4cStrings` blocks — one development, cut in
two by the pin's artifact split, with a prelude that is now public in the port (§1), so the order is
one module, not two (§5 of the playbook: a second module is a *subject* decision, and the subject is
one).

> **The shelf was read with `frontier.py --ds --ready --nexus --fanin-min 10` on 2026-10-22.** Both
> nodes are ready, `needed 1` (the node itself), all premises ported, and the port's `twin_scan`
> reports `new` for both (prelude `0/8`, i.e. no port double). They are the top two rows of the
> nexus shelf by the oldform subject.

## 0. The two nodes

| node | pin `S_` | decls in the `S_` file |
|---|---:|---:|
| `CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul` | 193 | 9 (7 helpers + `main` + `solution`) |
| `CuspForm.IsEigenformWith.heckeU_degeneracy_of_dvd_level` | 199 | 9 (7 helpers + `main` + `solution`) |

What they say. Fix `L ∣ M`, `ε_L` a Dirichlet character mod `L`, `g` a Γ₁(L) cusp form of weight `k`
with `IsEigenformWith ε_L g`, and **any** family `G : ℕ → CuspForm (Γ₁(M)) k` whose members are the
degeneracy images `G_d(τ) = g(d τ)` for `d ∣ M/L` (the pin never constructs `G`; it is the
hypothesis pattern `(G, hG)` that the whole oldform theory is phrased on).

* **headline 1** — for `ℓ ∤ M` prime and `d ∣ M/L`, the explicit coset form of `T_ℓ` acts on `G_d` by
  the eigenvalue at level `L`:
  `heckeU k ℓ ⇑(G d) + ε_L (ℓ) • (⇑(G d) ∣[k] heckeDiagMatrix ℓ) = qCoeff g ℓ • ⇑(G d)`.
  (`heckeT` is not used in the statement because only `ε_L`, not `ε_M`, is available — do **not**
  restate the conclusion through `heckeT`.)
* **headline 2** — for `q ∣ M` prime, the three cases of `U_q` on the same string: `q ∣ d` gives
  `U_q G_d = G_{d/q}`; `¬ q ∣ d, q ∣ L` gives `U_q G_d = a_q(g) • G_d`; `¬ q ∣ d, ¬ q ∣ L` gives
  `U_q G_d = a_q(g) • G_d − (ε_L(q) q^{k−1}) • G_{d q}`.

**Readiness (measured 2026-10-22).** `premises_unported = 0` for both; `twin_scan` `new` for both;
`port_advise` on the two `S_` files reports **2 substitutions** (`qCoeff_const_smul`,
`periodic_const_smul`, both `private` in the port until the L3 prelude promotion, now public) and
nothing else importable — the rest of the prelude is the 6 generic helpers promoted in the same pass
(§1), so what remains new is `reg_gamma1` (10 lines) and the two proofs.

**Demand.** Headline 1 is cited by five unported nodes, all of them the oldform/Γ_H theory the D-S
column still owes: `CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne`,
`CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace`,
`CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply`,
`DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm`,
`DihedralWeightOne.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_weightOneLift_of_isPrimitiveForm`.
Headline 2 is cited by two, also unported. So this pair is the **bottom layer of the Γ_H oldform
theory** (Atkin–Lehner–Li basis, `IsNewform`, generalised eigenspace decomposition), not a
self-contained leaf: say so in the record and do not claim it unblocks a landed consumer today.

## 1. Deliverable — one module

`FLTForHuman/ModularForms/Level/DegeneracyString.lean`.

**Public surface: the two headlines only**, verbatim from their `Theorems/` wrappers (the checker
diffs them), both in the pin's namespace `CuspForm.IsEigenformWith`. Everything else in the module is
`private` — and after the L3 promotion pass there is almost nothing left to write privately:

| what the pin proves privately in both `S_` files | port home (import, never re-prove) |
|---|---|
| `qCoeff_add`, `qCoeff_sub`, `qCoeff_const_smul` | `ModularFormClass.qCoeff_{add,sub,const_smul}` in `ModularForms/HeckeQCoeff.lean` (public, pin binders) |
| `periodic_add`, `periodic_sub`, `periodic_const_smul` | `UpperHalfPlane.periodic_{add,sub,smul}` in `ModularForms/HeckeAnalytic.lean` (public, general period) |
| `reg_gamma1` (periodic ∧ `MDiff` ∧ bounded, for a Γ₁ cusp form) | `CuspForm.cusp_periodic`, `cusp_holo`, `cusp_bdd` in `ModularForms/HeckePrelude.lean`; if the `CuspForm (Gamma1 M) k` / `CuspForm (Γ₁ℝ M) k` elaboration does not line up, transcribe the pin's 10-line `reg_gamma1` as a `private` helper (it is generic Γ₁ glue with no public home, so it may stay) |
| the analytic regularity of `U_p`/`T_p` | `ModularForm.periodic_hecke{U,T}_comp_ofComplex`, `mdifferentiable_hecke{U,T}`, `isBoundedAtImInfty_hecke{U,T}` (`HeckeAnalytic`) |
| the `q`-coefficient action | `UpperHalfPlane.qCoeff_heckeU`, `qCoeff_heckeT`, `qCoeff_comp_heckeDiagMatrix_smul`, `eq_of_forall_qCoeff_eq` (`HeckeQCoeff`) |
| `heckeT = heckeU + diag` | `ModularForm.heckeT_eq_heckeU_add`, `coeffHeckeU_apply`, `coeffHeckeT_apply` (`Defs/HeckeOperator`) |
| the eigenform relations at level `L` | `CuspForm.IsEigenformWith.hecke_of_not_dvd`, `.hecke_of_dvd` (`Defs/PrimitiveFormGamma1`, one-line projections of the predicate) |

**Dropped, deliberately (P2M devices, not mathematics):**
`p2m_export` / `p2m_open`, the `M4bOld` / `M4cStrings` inner namespaces, the `solution` copy, and —
this is the point of the order — **`main`**. The pin's `main` has *the same statement* as the
headline (its `solution` is literally `main M k hLM hg G hG …`), so transcribing it would add a
self-consumed 104-line lemma and a second name for one statement (playbook §3.1, "no self-consumed
lemmas"). Write the proof at the headline.

Imports (specific, no `import Mathlib`):

```lean
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.HeckePrelude
```

The module header states the subject (the degeneracy string of a Γ₁ eigenform and its Hecke
action), the pin sources, and that `G` is assumed, never constructed (the Γ₀ construction lives in
`Level/Degeneracy.lean`, a different cut: it builds the map, this module acts on the hypothesised
string). Do **not** edit `Level/Degeneracy.lean` and do not put this in `Defs/PrimitiveFormGamma1.lean`
(a `Defs/` module of one-line projections).

## 2. Source

Pin `anthropics/fermats-last-theorem@aa2d8b3`, the four files below; the statements are §2 of the
wrappers (lines 10–18 and 10–21), transcribed verbatim:

* `Theorems/Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean`
* `P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean`
* `Theorems/Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean`
* `P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean`

The module's wire (the checker reads these; there is no `PORT_FILES` entry — the module is new and
wires itself):

```
  spec-pin: Theorems/Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean
  spec-pin: P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean
  spec-pin: Theorems/Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean
  spec-pin: P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean
```

No `decl_markers.tsv` row is expected (both headlines keep their pin names and statements). If the
checker finds something else public, that is a deviation: stop and report it.

## 3. Route

Both proofs are `q`-coefficient bookkeeping closed by `UpperHalfPlane.eq_of_forall_qCoeff_eq`. The
route below is the pin's, with the port's names.

**Common first moves** (both headlines; the pin repeats them, the port writes them once each where
they are needed):

1. `classical`; `have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero` (resp. `hq0`).
2. `obtain ⟨e, he⟩ := hLM`, `have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)`,
   `have hMLe : M / L = e := by rw [he, Nat.mul_div_cancel_left _ hL0]`,
   `have he0 : e ≠ 0 := by rintro rfl; exact NeZero.ne M (by rw [he, mul_zero])`,
   `have hd0 : d ≠ 0 := fun h0 => he0 (Nat.eq_of_zero_dvd (h0 ▸ hd))` — note the pin's variant uses
   `hMLe`; either works.
3. `ℓ ∤ L` (from `ℓ ∤ M` and `L ∣ M`) and `ℓ ∤ d` (from `d ∣ M/L` and `ℓ ∤ M`), hence
   `Nat.Coprime ℓ d := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓd`.
4. The **string's coefficients** (the mathematical core, one `have` per proof):
   `∀ m, qCoeff ⇑(G d) m = if d ∣ m then qCoeff ⇑g (m / d) else 0`, by
   `show ⇑(G d) = fun τ => g (heckeDiagMatrix d • τ)` from `funext (hG d hd)` then
   `UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul` (with `cusp_periodic/holo/bdd g`, `hd0`).
   In headline 2 it is stated with `{d'}` generalised over `d' ∣ M/L`, `d' ≠ 0` (three cases need it
   at `d`, `d/q` and `d*q`).
5. Regularity of the form the proof works with, from `cusp_periodic/holo/bdd (G d)` and
   `ModularForm.{periodic,mdifferentiable,isBoundedAtImInfty}_hecke{U,T}`.

**Headline 1.** Set `hD : ⇑(G d) ∣[k] heckeDiagMatrix ℓ = heckeT k ℓ ⇑(G d) - heckeU k ℓ ⇑(G d)`
(`ModularForm.heckeT_eq_heckeU_add`, then `add_sub_cancel_left`). Build the left side's
periodicity/holomorphy/boundedness by `periodic_sub`, `MDifferentiable.sub`,
`IsBoundedAtImInfty.sub` of the `T`/`U` facts; the right side is `qCoeff g ℓ • ⇑(G d)` (const-smul of
the three facts of `G d`). Close with `eq_of_forall_qCoeff_eq` and compare coefficients:
`qCoeff_heckeU`/`qCoeff_heckeT` + `coeffHeckeU_apply`/`coeffHeckeT_apply` give the `U`/`T` values,
`qCoeff_sub`+`qCoeff_add`+`qCoeff_const_smul` put them together, and the `diag` coefficient is
`if ℓ ∣ n then ℓ^(k-1) * a_{n/ℓ} else 0` (the `T` minus `U` cancellation). Then split on `d ∣ n`,
rewrite with the string's coefficient formula and apply `hg.hecke_of_not_dvd hℓ hℓL m` (after
`mul_comm ℓ m`); inside `d ∣ n`, split once more on `ℓ ∣ m` because the eigen-relation's middle term
is present only there. In the `¬ d ∣ n` branch every coefficient is `0` and `ring` closes.

**Headline 2.** After the common moves, `hq0`, `hqM`, and the three conjuncts in order:
1. `q ∣ d`: `obtain ⟨d', rfl⟩ := hqd`; `d' ≠ 0`; `q * d' / q = d'`
   (`Nat.mul_div_cancel_left`); `d' ∣ M/L`; close with `eq_of_forall_qCoeff_eq` between
   `U_q G_{q d'}` and `G_{d'}` — the coefficient formula at `d'` and the index arithmetic
   `(d' * m' * q) / (q * d') = m'` (`Nat.mul_div_cancel_left` after `ring`), and in the `¬ d' ∣ m`
   branch the pin's `Nat.eq_of_mul_eq_mul_right` step.
2. `¬ q ∣ d`, `q ∣ L`: `hcop : Nat.Coprime q d`; close between `U_q G_d` and `a_q(g) • G_d`, using
   `qCoeff_const_smul`, the coefficient formula at `d`, `d ∣ m` split, and `hg.hecke_of_dvd hq hqL m'`.
3. `¬ q ∣ d`, `¬ q ∣ L`: `q ∣ e` (`Nat.Prime.dvd_mul` on `q ∣ L * e`, resolving left by `hqL`),
   `d * q ∣ M/L` (`Nat.Coprime.mul_dvd_of_dvd_of_dvd`), `set c : ℂ := εL (q : ZMod L) * (q : ℂ) ^ (k - 1)`,
   close between `U_q G_d` and `a_q(g) • G_d − c • G_{d q}` through `qCoeff_sub` of the two
   const-smuls, using `hg.hecke_of_not_dvd hq hqL m'` and one more `q ∣ m'` split; the `¬ d ∣ m`
   branch is `ring` after the three `if_neg`s.

**Statement gotchas.**
* `hG` is pointwise at `τ : UpperHalfPlane`; the coefficient lemmas want `ℍ → ℂ`, so the `funext`
  rewrite of move 4 is load-bearing (a bare `rw [hG]` will not fire).
* `εL (ℓ : ZMod L)` and `εL (q : ZMod L)` are `ℕ → ZMod` casts; keep them as written.
* `d / q` and `d * q` appear under `if`-guards: `Nat.mul_div_assoc`, `Nat.mul_div_cancel_left`,
  `Nat.mul_div_mul_left` and `Nat.Coprime.dvd_mul_left/right` are the five lemmas the pin uses; do not
  invent `omega`-style alternatives that change the goal shape under `rw`.
* `qCoeff (⇑(G d)) m` never appears with `⇑` twice: the coerced form is already a function.

## 4. Build discipline

* Edit loop: `cd lean && flock .lake/flt_build.lock timeout 110 lake env lean -DmaxHeartbeats=4000000 FLTForHuman/ModularForms/Level/DegeneracyString.lean`.
  If a single declaration needs more than 20,000 hearts, say which and why (the pin sets no bump on
  these two files), and do not add `set_option maxHeartbeats` without recording it.
* Module: `cd lean && flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.ModularForms.Level.DegeneracyString`.
  Every command must finish inside two minutes; never run a whole-tree `lake build`.
* Zero warnings: the module declares `set_option autoImplicit false`, imports specific modules only,
  and must build with no `warning:` line (the pin's `haveI` walls, if any appear, are kept literal and
  the linter switched off in the file, as in `Level/Degeneracy.lean`).

## 5. Verification

* `python3 lean/spec/check_port.py --force lean/FLTForHuman/ModularForms/Level/DegeneracyString.lean`
  must read **`2 ok, 0 mismatch, 0 missing, 0 own, 0 kw`** — that is the whole public surface, and it
  is the evidence that `main` was not needed (a third public name would show up here).
* `#print axioms CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul`
  and `#print axioms CuspForm.IsEigenformWith.heckeU_degeneracy_of_dvd_level`:
  `[propext, Classical.choice, Quot.sound]`.
* `grep -c "sorry\|admit" ` on the module: 0.
* `python3 tools/deps/dedup.py 'ModularForms/Level' --tier name` : no new cluster for the two
  headlines (they are new names, so the expected report is unchanged); also confirm
  `python3 tools/deps/dedup.py 'ModularForms' --tier body --min-cost 0` does not gain a body cluster
  (the two proofs are different statements, so they must not collapse).
* `python3 tools/deps/frontier.py --ds --ready --nexus --fanin-min 10 --top 5`: the first row must no
  longer be headline 1, and both nodes must be reported as ported (`--list` or the node page). Record
  the reading in the report.

## 6. Stop-early conditions

* The port's `qCoeff_comp_heckeDiagMatrix_smul` takes the *bare* three-hypothesis form; if the
  concrete `CuspForm` spelling forces a `reg_gamma1` that is longer than the pin's 10 lines, stop and
  report (it would be a sign that `CuspForm.cusp_*` must be generalised instead).
* If `eq_of_forall_qCoeff_eq` needs a hypothesis the pin's route does not produce for one of the
  three cases in headline 2 (e.g. boundedness of `G (d * q)` at the cusp), stop: that is a missing
  premise, not a proof-engineering problem.
* A `MISMATCH` in the statement check means the transcribed statement drifted from the wrapper.
  Revert to the wrapper's text; do not add a `pin:` marker for a self-inflicted difference.
* Do not touch `Level/Degeneracy.lean`, `HeckeQCoeff.lean`, `HeckeAnalytic.lean`, `HeckePrelude.lean`
  or `Defs/PrimitiveFormGamma1.lean`. If an import or a promotion is genuinely missing, stop and
  report it as a blocker with the exact `#check` that fails.

## 7. What this buys

The two bottom rows of the Γ_H oldform layer, and the **first** module in the port whose statements
are the `(G, hG)` degeneracy-string pattern the rest of that layer (`IsNewform`, the Atkin–Lehner–Li
basis, the independence theorem) is phrased on. Porting it also retires the pin's `M4bOld`/`M4cStrings`
`main`+`solution` duplication into the two headlines, and leaves the module at ~250 lines with a
two-declaration public surface.

## 8. The record

`FLTForHuman/ModularForms/Level/DegeneracyString.lean`, **276 lines**, two public declarations and
nothing else — no `private` helper was needed.

| check | reading |
|---|---|
| `check_port --force` | **2 ok, 0 mismatch, 0 missing, 0 own, 0 kw** (both rows resolve to their `Theorems/` wrapper at line 10) |
| `lake build FLTForHuman.ModularForms.Level.DegeneracyString` | green, **0 warnings**, 3.6 s |
| `#print axioms` on both headlines | `[propext, Classical.choice, Quot.sound]` |
| `grep -c 'sorry\|admit'` | 0 |
| `dedup.py 'ModularForms/Level' --tier name` | 0 clusters (no new one); `--tier body --min-cost 0` over `ModularForms` adds nothing naming the pair |
| `frontier.py --ds --ready --nexus --fanin-min 10 --top 5` | the pair is gone from the shelf and from the `needed` list; the first row is now `ModularCurve.finrankAlong_heckeAlphaOneBar`; the `CuspForm.` unported demand falls to 49 nodes |
| hearts | clean at `-DmaxHeartbeats=20000`, so no declaration needs a bump and the module carries `set_option autoImplicit false` only |

**`reg_gamma1` was not needed.** `CongruenceSubgroup.Gamma1 M` coerces to
`Subgroup (GL (Fin 2) ℝ)` as `Subgroup.map (mapGL ℝ)` (mathlib
`NumberTheory/ModularForms/ArithmeticSubgroups.lean:97`), which is the term `HeckePrelude`'s `Γ₁ℝ M`
abbreviates, so `CuspForm.cusp_periodic`/`cusp_holo`/`cusp_bdd` elaborate directly at
`CuspForm (CongruenceSubgroup.Gamma1 M) k` — the order's §6 stop condition never fired.

**Two deviations, both proof-side and both forced by mathlib v4.34.0:**
`Nat.eq_of_zero_dvd` (named in the order as interchangeable with the pin's
`Nat.eq_zero_of_zero_dvd`) does not exist, so the pin's spelling is used; and `if_pos`/`if_neg` are
deprecated in favour of `ite_eq_left`/`ite_eq_right`, which the module uses at all 28 sites to meet
the no-warning rule. No statement moved.

**What is left of the pin's files.** The two `S_` files (193 + 199 lines, a 74-line prelude shared
verbatim) reduce to the two headline proofs plus their imports: the prelude they duplicated is now
public in `HeckeQCoeff`/`HeckeAnalytic`, and their `main`+`solution` device is retired.
