# Topic: slash-invariance — where `heckeU`/`heckeT` land

**Status: Tier 0 + Tier 1 done (2026-09-23); Tiers 2–4 deferred.** First topic of the Hecke-operator effort. It
ports the survey's §4: the 17 statements saying `heckeU`/`heckeT` (and their
diamond/Atkin–Lehner twists) preserve the level they should. The scouting result
that shapes the topic: **all seven core Γ₀/Γ₁/Γ_H nodes have `cites = 0`** — no
FLT theorem dependencies, only `Def_ModularForm_HeckeOperator` (and
`Def_CohCarrier_Level` for the two Γ_H ones) — yet their `S_` files are
232–489 lines each, because FLT re-inlines the shared Hecke-representative block
(and its Γ_H/Γ₁ variants) into every one of them (the Γ₀ form is public in
`Def_CuspForm_Gamma1HeckeOperators.lean:82–455`). Across the 17
declarations that is **≈11,842 pin lines**; Tier 1 alone is 1,467 pin lines that
collapse to ≈300 port lines once the block is written once. The port already
holds a **weakened** private copy of the block in
`PhiGenDescends.lean:75–293`, so this is a promotion/dedup/complete topic, not a
transcription — and the weakening has to be undone, not inherited (§1).

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured in this checkout with mathlib prebuilt
> (`v4.34.0`, `leanprover/lean4:v4.34.0`):
> `lake env lean FLTForHuman/ModularForms/Defs/HeckeOperator.lean` (114 lines) is
> **~6 s warm** (~20 s on a cold olean cache); the 509-line `PhiGenDescends.lean`
> is **~22 s**; `lake build <module>` with deps cached is **~4–6 s** (the default
> target reports 2908 jobs, nearly all cached). A `whnf`/heartbeat stall at the
> default cap errors in tens of seconds — it does not hang — so a non-return is a
> real blow-up, not patience.
>
> - Run every build under a bound: `timeout 120 lake env lean <file>`,
>   `timeout 180 lake build <module>`. Non-return at 120 s is a blow-up.
> - **Quarantine immediately.** On a timeout, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch.lean` with
>   `set_option diagnostics true`. Do not re-run the same file hoping for a
>   different result.
> - **Never raise `maxHeartbeats`.** The project's global cap is `4000000`
>   (`lakefile.lean`); the pin raises it locally (`3200000`) only in
>   `chain_endgame`, which is out of scope here. The usual stall cause is a
>   `FunLike`-quantified lemma instantiated at a bare function type
>   (`logs/ffg-port.md` §2.2) — restate it over the concrete `ℍ → ℂ`. This topic's
>   likely stall points are the two reindexing workhorses (`heckeU_slash_mapGL`'s
>   `Equiv.sum_comp` over `ZMod p`, `heckeT_slash_mapGL`'s
>   `MulAction.toPerm (redMatrix p g)` over `OnePoint (ZMod p)`) and the
>   `Finset`/`Fintype` sums they rewrite. The pin's lemmas are already stated over
>   `ℍ → ℂ`; keep them that way.

**Audience.** A fresh session taking the first topic of a new effort. Read
[studies/hecke-operator-survey.md](../../../studies/hecke-operator-survey.md)
§§2–4 (the operator block, the bundling, and the §4 inventory this order is
about) and §12–13; [base/014](../../../base/014-hecke-operators.md) §1, §3, §5.1
for the mathematics; [PORTING-FFG.md](../PORTING-FFG.md) to see this effort's
nearest neighbour; and [porting-playbook.md](../../porting-playbook.md) §3–§5
and §7 for the method.

**Goal.** Port the survey's §4 slash-invariance layer in tiers, doing **Tier 1
(Γ₀ + Fricke) in this topic**: the shared Hecke-representative block public once,
the five Γ₀/Fricke statements verbatim from their pin wrappers, and
`PhiGenDescends.lean` rewritten to import the promoted block instead of keeping
its private copy. Tiers 2–4 are scoped and priced here but **not** attempted.

## 1. Why this topic, and what is settled

The operator block of [`Def_ModularForm_HeckeOperator.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularForm_HeckeOperator.lean)
(lines 72–200, 34 declarations) is the direct extension of the port's
matrices-only `Defs/HeckeOperator.lean`; the survey priced it as Stage A. But
`heckeU`/`heckeT` alone are not an API: what makes them *operators*, and what
the bundled `heckeTLin`/`heckeULin` of the survey's §3 consume as their
`slash_action_eq'` field, are two of the §4 facts
(`Def_ModularForm_HeckeOperatorForms.lean:25,38`); the `…_Gamma0_div` one feeds
`heckeULowerLin`, and the Fricke pair feeds the level-one route of the survey's
§12. This topic is the gate to that bundling, and one of the five
(`exists_levelOne_coe_eq_…`) has indeg **8** in the pin.

Three scouting findings drive the order:

- **The proofs are shallow, the files are not.** All seven core Γ₀/Γ₁/Γ_H nodes
  have `cites = 0` (the two Fricke ones too). The three Γ₀ `S_` files (352, 352,
  232 lines) are one ~160-line `heckeU` block plus a ~124-line `heckeT` block
  copied per file; the Γ_H pair repeats its own ~470-line block, and the
  Γ₁/Nebentypus pair a third. This is the interface-tier situation again: the
  work is exposure, not proof.
- **The block already exists in the port, privately and weakened.**
  `PhiGenDescends.lean:75–293` has `det_eq`, the four `_mul_of_eq` lemmas,
  `heckeRep`, `redMatrix`, `heckeRep_mul`, the reindexing helpers and
  `cosetPoly_*` — transcribed for the T8 consumer. The pin's public home is
  `Def_CuspForm_Gamma1HeckeOperators.lean:82–455`.
- **The port's copy dropped a conjunct the lowering needs.** All four pin
  `_mul_of_eq` lemmas return a `g'` *together with* an equation `g' 1 0 = …`
  (`= p * g 1 0`, `= g 1 0`, or `= e`, depending on the lemma); the port's private
  copies return only `∃ g', …`. The Γ₀ proofs need the `heckeMatrix_mul_of_eq`
  conjunct `g' 1 0 = p * g 1 0` to show `g' ∈ Γ₀(N)`
  (`S_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div.lean:204`).
  **Do not promote the private copies as they stand**; port the pin's stronger
  statements.

**Settled: the tiering.** The 17 declarations split by *definitional*
prerequisites, not by proof difficulty:

| tier | declarations | prerequisite | lines (pin) | verdict |
|---|---|---|---|---|
| 0 | the operator block, 34 decls | none (survey Stage A) | 129 | do first if not already done |
| 1 | Γ₀ ×3, Fricke ×2 | mathlib `CongruenceSubgroups` only | 1,467 | **this topic** |
| 2 | Γ₁, Nebentypus | mathlib `Gamma1`, `DirichletCharacter` | 785 | scoped, not attempted |
| 3 | Γ_H ×2 | `Def_CohCarrier_Level` (Γ_H) + `GroupTheory.Transfer` | 970 | blocked on a foreign def module |
| 4 | Atkin–Lehner ×8 | `Def_ModularForm_AtkinLehnerDatum`, `alSlash`, `diamondLinH`, `traceLin` | 8,620 | blocked on a foreign def tree |

**Settled: placement.** A module is a mathematical role in this port. The shared
matrix/permutation block's role is "the Hecke representatives on ℙ¹(𝔽_p)"; it is
not part of the pin's `Def_ModularForm_HeckeOperator`, so it gets its own
definition module. The five Γ₀/Fricke corollaries are results and go in a result
module beside `HeckeQExpansion.lean`. Concretely:

- new `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean` — `det_eq`, the
  four `_mul_of_eq`, `heckeRep`/`redMatrix`/`heckeRep_mul`, and the
  `sum_range_eq_sum_zmod`/`heckeU_eq_sum_zmod`/`affinePerm`/`heckeMatrix_mul_of_dvd`
  helpers plus the two `_slash_mapGL` workhorses;
- new `FLTForHuman/ModularForms/HeckeInvariance.lean` — the five public §4
  statements of Tier 1;
- `PhiGenDescends.lean` loses its private copies and imports the new module.

An alternative (mirroring the pin's `Def_CuspForm_Gamma1HeckeOperators.lean`) is
to grow `Defs/HeckeOperator.lean` instead of adding a module; it is rejected
because that file is the verbatim `Def_ModularForm_HeckeOperator` subset and
should stay so. Decide once in round 1 and record it.

**Settled: statements are FLT's, verbatim.** All 17 have `Theorems/Thm_ModularForm_*.lean`
wrappers, so the checker can *verify* them; add the Tier-1 wrappers to `SOURCES`
and do not restate anything (§5).

## 2. The scouted inventory — all of §4, with tiers and deps

`cites` = FLT theorem nodes the `S_` file imports. Every Tier-0..3 node has
`cites = 0`.

| declaration | tier | `S_` file (lines) | cites | definition deps | target |
|---|---|---|---|---|---|
| (operator block, 34 decls) | 0 | `S_ModularForm_*` — see survey §2 | — | `Def_ModularForm_HeckeOperator` | `Defs/HeckeOperator.lean` |
| `heckeU_slash_eq_self_of_mem_Gamma0` | 1 | `…_Gamma0` (352) | 0 | `Def_ModularForm_HeckeOperator` | `HeckeInvariance.lean` |
| `heckeT_slash_eq_self_of_mem_Gamma0` | 1 | `…_Gamma0` (352) | 0 | same | `HeckeInvariance.lean` |
| `heckeU_slash_eq_self_of_mem_Gamma0_div` | 1 | `…_Gamma0_div` (232) | 0 | same | `HeckeInvariance.lean` |
| `heckeU_add_slash_fricke_eq_zero` | 1 | `…_fricke_eq_zero` (229) | 0 | same | `HeckeInvariance.lean` |
| `exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke` | 1 | `…_slash_fricke` (302) | 0 | same | `HeckeInvariance.lean` |
| `heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1` | 2 | `…_Gamma1` (379) | 0 | mathlib `Gamma1` | deferred |
| `heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0` | 2 | `…_smul_slash…` (406) | 0 | mathlib `DirichletCharacter` | deferred |
| `heckeU_slash_eq_self_of_mem_GammaH` | 3 | `…_GammaH` (481) | 0 | `Def_CohCarrier_Level` | deferred |
| `heckeU_add_slash_slash_eq_self_of_mem_GammaH` | 3 | `…_GammaH` (489) | 0 | `Def_CohCarrier_Level` | deferred |
| `alSlash_add_heckeU_slash_eq_self_of_mem_GammaH` | 4 | (478) | 0 | + `Def_ModularForm_AtkinLehnerDatum` | deferred |
| `alSlash_heckeT_comm` | 4 | (2387) | 0 | same | deferred |
| `add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0` | 4 | (2388) | 0 | same | deferred |
| `alSlash_add_heckeU_alSlash_alSlash` | 4 | (2388) | 0 | same | deferred |
| `heckeU_add_slash_alSlash_eq_alSlash_…_of_not_dvd` | 4 | (674) | 0 | same | deferred |
| `heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div` | 4 | (228) | 0 | same | deferred |
| `alSlash_coe_eq_coe_diamondLinH_slash_heckeDiagMatrix` | 4 | (40) | 1 | `Def_CuspForm_HeckeOperatorFormsGammaH` | deferred |
| `heckeT_trace_alSlash_of_eigen` | 4 | (37) | 3 | `Def_ModularForm_AtkinLehnerDatum`, `Def_ModularForm_HeckeOperatorForms` | deferred |

The statements of Tier 1, verbatim from their wrappers (transcribe these):

```lean
-- Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0
theorem ModularForm.heckeU_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ} (hpN : p ∣ N)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), SlashAction.map k γ f = f)
    (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f

-- Thm_ModularForm_heckeU_slash_eq_self_of_mem_Gamma0_div
theorem ModularForm.heckeU_slash_eq_self_of_mem_Gamma0_div {N : ℕ} (k : ℤ) {p : ℕ} (hp2N : p ^ 2 ∣ N)
    {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), SlashAction.map k γ f = f)
    (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 (N / p) : Subgroup (GL (Fin 2) ℝ))) :
    SlashAction.map k γ (ModularForm.heckeU k p f) = ModularForm.heckeU k p f

-- Thm_ModularForm_heckeT_slash_eq_self_of_mem_Gamma0
theorem ModularForm.heckeT_slash_eq_self_of_mem_Gamma0 {N : ℕ} (k : ℤ) {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)), SlashAction.map k γ f = f)
    (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ))) :
    SlashAction.map k γ (ModularForm.heckeT k p f) = ModularForm.heckeT k p f

-- Thm_ModularForm_heckeU_add_slash_fricke_eq_zero
theorem ModularForm.heckeU_add_slash_fricke_eq_zero (p : ℕ) [Fact p.Prime]
    (f : ModularForm (CongruenceSubgroup.Gamma0 p) 2) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ModularForm.heckeU 2 p ⇑f + ⇑f ∣[(2 : ℤ)] W = 0

-- Thm_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke
theorem ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke (p : ℕ) [Fact p.Prime]
    (k : ℤ) (X : ModularForm (CongruenceSubgroup.Gamma0 p) k) (W : GL (Fin 2) ℝ)
    (hW : ((W : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![0, -1; (p : ℝ), 0]) :
    ∃ Y : ModularForm 𝒮ℒ k, ⇑Y = (p : ℂ) ^ (k - 2) • ⇑X + ModularForm.heckeU k p (⇑X ∣[k] W)
```

Route notes, so none of this has to be rediscovered:

- **Tier 0 first.** The invariance statements mention `heckeU`/`heckeT`, which
  the port does not have. Port `Def_ModularForm_HeckeOperator.lean:72–200` into
  `Defs/HeckeOperator.lean` as the survey's Stage A (34 declarations, mathlib
  only): `σ_hecke*`, `slash_hecke*_apply`, `heckeU`/`heckeT`, the three
  definitional rewrites, `_zero_left`/`_zero`/`_apply`, `add`/`smul`/`neg`/`sub`,
  and `coeffHecke*` with its nine lemmas. If a separate topic has already done
  this, start at Tier 1.
- **Promote, then strengthen.** Move the `det_eq`…`heckeRep_mul` half
  (`PhiGenDescends.lean:75–240`) to `Defs/HeckeRepresentatives.lean`, restoring
  the pin's `g' 1 0 = …` conjunct in all four `_mul_of_eq` lemmas and adding the
  pin's `NeZero p`/`Fact p.Prime` binder discipline. Delete the private copies and
  let `PhiGenDescends` import the module; leave that file's T8 payload
  (`apply_heckeRep_smul_smul`, `prod_range_eq_prod_zmod`/`prod_fin_eq_prod_zmod`,
  `cosetPoly_eq_prod_onePoint`/`cosetPoly_smul'`) in place, and check
  `cosetPoly_smul`/`heckeRep_mul` still elaborate unchanged.
- **The two workhorses** are the pin's `heckeU_slash_mapGL` (the `Finset.sum`
  over `ZMod p` rewritten by `affinePerm` and `Equiv.sum_comp`) and
  `heckeT_slash_mapGL` (the sum over `OnePoint (ZMod p)` rewritten by
  `MulAction.toPerm (redMatrix p g)`). The five corollaries are ~10-line
  `obtain ⟨g, hg, rfl⟩ := hγ` wrappers around them; `p = 0` is the only junk case
  (`rcases Nat.eq_zero_or_pos p`).
- The Γ₀ statements need the extra conjunct: `g' ∈ Γ₀(N)` follows from
  `g' 1 0 = p * g 1 0` and `g ∈ Γ₀(N)` (respectively `g ∈ Γ₀(N/p)`), so that the
  `hf` hypothesis applies. This is why the private port copy must not be promoted
  as-is.
- The two Fricke statements are independent of the Hecke-representative block
  (their `S_` files import `Mathlib` + `Def_ModularForm_HeckeOperator` only, and
  the second re-derives a small analytic package: `traceFun` holomorphy,
  `IsBoundedAtImInfty`, `heckeU_slash_W`, and the `ModularForm` bundle). They can
  be done in parallel with the block; the second is the only Tier-1 piece that
  touches mathlib's bundled `ModularForm` and `𝒮ℒ`.

## 3. What is different about this topic

- **It is promotion, completion and dedup, not transcription.** The interface
  tier is the model: most lines already compile somewhere; the work is deciding
  where the object lives and removing the copy. Budget expectations from the
  first ports (definitions ≈1 round/68 decls) do not apply — this is a proof
  layer, and only the two workhorses are new mathematics.
- **The existing private copy is a *weakening*.** This is the one trap. A
  mechanical "make the private lemmas public" would compile but would not prove
  `…_Gamma0_div`; the conjunct has to be restored from the pin. Record the
  divergence in the module header if any statement is intentionally different.
- **The tier blockers are definitional, not mathematical.** Γ_H needs
  `CohCarrier.GammaH` (`Def_CohCarrier_Level.lean:133`) and mathlib's transfer;
  Atkin–Lehner needs the `AtkinLehnerDatum`/`alSlash`/`diamondLinH` tree. Both
  are whole foreign developments whose 2,388-line `S_` files are mostly
  re-derived AL machinery. Do not open them for a §4 declaration; the cheap
  move is to record the blocker and stop.
- **The checker flips from nothing to verifying.** None of these wrappers is in
  `SOURCES` today. Add the five Tier-1 wrappers; count the verified delta in the
  log.
- **One deliberate divergence is likely: the shared block's home.** FLT keeps it
  public in a *Gamma1 definition* file; the port, which has no Gamma1 yet, puts
  it in a `HeckeRepresentatives` module. That is a naming/placement divergence
  (mathematics unchanged) and belongs in the header, exactly as the `TS` module
  records its own.

## 4. Budget

**2 goal rounds, checkpoint at 1.** Round 1 should reach the two workhorses and
the three Γ₀ corollaries (the block plus the `ZMod`/`OnePoint` reindexings); the
Fricke pair is the checkpoint decision — if the analytic package of
`exists_levelOne_…` is not obviously short, deliver the three Γ₀ statements and
report it rather than push. Nothing here is a research risk; the risk is scope
creep into Tier 2–4.

**Stop early on**: a Tier-1 statement that will not match its wrapper (record the
divergence rather than weaken it); the restored conjunct breaking
`PhiGenDescends`'s `cosetPoly_smul`; or the Fricke package needing the modular-form
q-expansion cluster of the deferred Φ_p subtree.

**Route risks, in the order they will bite.**

- **The two reindexing workhorses.** `heckeU_slash_mapGL` rewrites a
  `∑ x : ZMod p` by `affinePerm` + `Equiv.sum_comp`; `heckeT_slash_mapGL`
  rewrites a `∑ x : OnePoint (ZMod p)` by `MulAction.toPerm (redMatrix p g)`.
  Both consume the four `_mul_of_eq` lemmas of `Defs/HeckeRepresentatives`,
  which must carry the pin's `g' 1 0 = …` conjuncts. If a rewrite stalls it is
  the `Finset`/`Fintype` sum instance or a `FunLike` instantiation, not the
  mathematics — isolate in `Scratch.lean` per the blockquote.
- **The `p = 0` junk case and the wrapper shape.** The pin does
  `rcases Nat.eq_zero_or_pos p` / `obtain ⟨g, hg, rfl⟩ := hγ` in the
  `…_slash_eq_self…` corollaries, not in the `_mapGL` workhorses. Keep the split
  where the pin has it, or the statements drift.
- **The Fricke analytic package.** `exists_levelOne_…` re-derives `traceFun`
  holomorphy, `IsBoundedAtImInfty`, `heckeU_slash_W` and the `ModularForm` bundle
  (302 pin lines). If it resists, ship the three Γ₀ statements and defer it —
  that is the round-1 checkpoint decision above.
- **Statement shape.** All five take an explicit
  `hf : ∀ γ ∈ Γ, SlashAction.map k γ f = f` over a bare `ℍ → ℂ`; do not restate
  over a `FunLike` type variable (`Defs/HeckeRepresentatives`'s helpers likewise),
  both for the stall reason and because the checker diffs the pin's form.

## 5. Definition of done

Tier 1 only; Tiers 2–4 are explicitly out of scope. **All items satisfied
2026-09-23**; measured cost and findings are in
[logs/hecke-port.md](../../logs/hecke-port.md).

- [x] Tier 0: `heckeU`/`heckeT` and the operator block public in
      `Defs/HeckeOperator.lean`, statements verbatim from the pin's
      `Def_ModularForm_HeckeOperator.lean:72–200` (34 declarations; the file is
      now the pin's lines 11–200, 247 port lines).
- [x] `Defs/HeckeRepresentatives.lean`: the shared block public once, with the
      pin's `g' 1 0 = …` conjuncts restored; `heckeRep`, `redMatrix`,
      `heckeRep_mul`, the reindexing helpers and the two `_slash_mapGL`
      workhorses (24 public declarations, 353 lines).
- [x] `HeckeInvariance.lean`: the five Tier-1 statements verbatim from their
      `Theorems/` wrappers (the three Γ₀ statements from the workhorses; the
      Fricke pair re-derives its own analytic package, all helpers `private`).
- [x] `PhiGenDescends.lean` imports the promoted block; its private `det_eq`/
      `_mul_of_eq`/`heckeRep`/`redMatrix`/`heckeRep_mul` copies are gone (0
      occurrences), and `cosetPoly_smul`/`mem_adjoin_jq_of_phiGenDescends` are
      unchanged (the T8 payload calls the shared `heckeRep_mul` at `N := 1`).
- [x] `lake build` green, 0 warnings, no `sorry`.
- [x] `#print axioms` on the five: only `propext, Classical.choice, Quot.sound`.
- [x] `spec/check_flt_statements.py`: the five Tier-1 wrappers added to
      `SOURCES`, verified count 618 → **682**, 0 mismatched, 0 missing. The
      Tier-0 operator declarations are matched by name against
      `Definitions/Def_ModularForm_HeckeOperator.lean` (already in `SOURCES`); no
      special handling was needed. The Γ₀ `S_` carrier was also added, for the
      shared block.
- [x] `logs/hecke-port.md` created with: the measured cost, the pin-vs-port line
      ratio for Tier 1, the weakening finding, and the Tier-2..4 blockers with
      the definition modules each needs.
- [x] README module table gains the two new modules; the `Defs/HeckeOperator.lean`
      row's "the `heckeU`/`heckeT` operator block is not ported" note is updated.

## 6. Verification

1. **`#print axioms`** clean on the five Tier-1 theorems (and on the Tier-0
   operator block): only `propext, Classical.choice, Quot.sound`.
2. **Statement checker.** Append the five Tier-1 `Theorems/Thm_ModularForm_*.lean`
   wrappers to `SOURCES`; they are public wrappers, so they verify by direct name
   match. Report before/after (0 mismatched, 0 missing). The Tier-0 operator
   declarations are `Definitions/` statements — record how the checker handles
   them (name match against `Def_ModularForm_HeckeOperator.lean`) rather than
   leaving them silently unchecked.
3. **`PORT_FILES`** gains the new modules (and `Defs/HeckeOperator.lean` is
   already listed).
4. **Build.** Bounded, per the blockquote: `timeout 120 lake env lean <file>`
   during development, `timeout 300 lake build FLTForHuman.ModularForms.HeckeInvariance`
   at the module seam, then a full `lake build` at the end — green, 0 warnings,
   no `sorry`; library-wide `grep -rn "sorry\|admit" FLTForHuman/`.
5. **Dedup check.** `grep -c` the private names in `PhiGenDescends.lean` before
   and after (they must go to 0) and confirm `cosetPoly_smul` now resolves to the
   imported `Defs/HeckeRepresentatives` block.
6. **README** gains the two modules; `logs/hecke-port.md` records the measured
   cost, the pin-vs-port ratio and the weakening finding.

## 7. Reporting back

Same shape as the FFG topics. Three things specifically:

1. **The measured compression**, not the claim. Tier 1 is 1,467 pin lines; report
   the actual port lines and the ratio, and whether the block was already correct
   in the port or had to be re-derived.
2. **Whether the weakening was the only divergence.** The scouting found the
   dropped `g' 1 0` conjunct; report any other statement that did not match its
   pin wrapper verbatim, so the next topic knows whether the existing private
   copies are trustworthy.
3. **The Tier-2..4 entry cost, scouted but not paid.** For Γ_H and Atkin–Lehner,
   name the definition modules and the S-file lines that are foreign machinery
   (not §4), so the next order can price them without re-reading 2,388-line
   files.
