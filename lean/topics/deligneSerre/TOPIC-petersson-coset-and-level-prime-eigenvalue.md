# The coset-space Petersson pairing and the eigenvalue at a level prime — math, measurement, port plan

**Status: landed 2026-10-18 — P1 (the definition layer), P2 (the sibling silo) and P3 (the `norm_sq_lt` bound) are all green and wired; the column's checker reads 10,478. P3 is §5.3; its record is [logs/normsq-lt.md](../../logs/normsq-lt.md).**

The D-S frontier's `--include-leaves` view surfaces the two `norm_sq` leaves of the
Hecke/nebentypus layer, each one whole pin `S_` file behind one shared definition module:

| node | own `S_` lines | declarations | `used_by` (cone / project) |
|---|---:|---:|---:|
| `CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough` | 979 | 72 | 1 / 3 |
| `CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen` | 893 | 57 | 1 / 4 |

This note is the handoff record for the set: §1 the mathematics, §2 the two pin
modules, §3 the measurements (taken 2026-10-18 — do not re-run), §4 the definition
layer and the 18 shared declarations, §5 the cut plan, §6 wiring and the checker
delta, §7 risks and what not to do, §8 reproduce. Mathematics:
[../../../math/030-petersson-adjointness-of-hecke.md](../../../math/030-petersson-adjointness-of-hecke.md)
§7. Predecessor, and the conventions this set must keep:
[TOPIC-petersson-hecke-adjointness.md](TOPIC-petersson-hecke-adjointness.md) (the
`peterssonOn` adjointness engine). Column record:
[../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md).

## 1. The mathematics

The leaf is the eigenvalue bound at a **level prime**. Let `k ∈ ℤ`, `N ≥ 1`,
`ε` a nebentypus modulo `N`, `ℓ` prime with `ℓ ∣ N`, and `F ∈ S_k(Γ₁(N))`,
`F ≠ 0`, with nebentypus `ε` and `a_{ℓn} = a·a_n` for all `n` (that is,
`U_ℓ F = aF`). If `ε` does **not** factor through `N/ℓ`, then

$$|a|^2 = \ell^{k-1}.$$

The hypothesis says `ε` is not the inflation of a character modulo `N/ℓ` along
`(ℤ/N)^× → (ℤ/(N/ℓ))^×` — the nebentypus is new at `ℓ` — and the conclusion is
the classical statement that a form new at a level prime has
$`|a_\ell| = \ell^{(k-1)/2}`$. It is what makes the primitive-form `q`-coefficient
bound and the level-lowering step of the Deligne–Serre column run: the in-cone
consumer is
`CuspForm.IsPrimitiveForm.pow_dvd_of_pow_dvd_of_sq_dvd_of_factorsThrough_of_forall_coprime_qCoeff_eq`
(802 lines, 31 needed nodes, silo 11,820).

At `ℓ ∣ N` the adjointness of the predecessor does not apply — the `ℓ`-th Hecke
operator is a different double-coset sum — but the same three tools (unfold the
coset sum, transfer the product across a slash, evaluate one character sum),
applied to the **additive** translates `τ ↦ τ + u/ℓ` (`u = 0, …, ℓ-1`), still pin
the eigenvalue. The proof, in the order the pin writes it:

1. **The subgroup.** `Λ₀ ≤ Γ₁(N)`: the matrices of `Γ₁(N)` with
   `(N/ℓ) ∣ b` and `(Nℓ) ∣ c`. Then `Γ(Nℓ) ⊆ Λ₀ ⊆ Γ₁(N)`, and
   `D = diag(ℓ,1)` conjugates `Λ₀` onto `Γ(N)`, so `Λ₀` and `Γ(N)` have the same
   relative index in `Γ₁(N)`.
2. **The `q`-expansion sum.** `∑_{u<ℓ} F∣_k t_u = a·ℓ^{2-k}·(F∣_k D)`, from
   `t_u = [[1,u/ℓ],[0,1]]` (`det = 1`, so it acts by `τ ↦ τ + u/ℓ`), the
   `ℓ`-th roots of unity killing the coefficients not divisible by `ℓ`, and
   `a_{ℓm} = a·a_m`.
3. **The character conjugate.** A unit `x ≡ 1 (mod N/ℓ)` with `ε(x) ≠ 1`, its
   residue `d`, and the lower-unipotent cocycle give
   `Φ(wd) = ε(d)·Φ(w)` for `Φ(w) = ⟨F∣_k t_w, F⟩_{Λ₀}`. Multiplying by `d`
   permutes the nonzero residues and `ε(d) ≠ 1`, so `∑_{w≠0} Φ(w) = 0` and
   `∑_{w} Φ(w) = Φ(0) = P`.
4. **The two values of `⟨V,V⟩`.** For `V = ∑_{u<ℓ} F∣_k t_u`: by steps 3 and the
   slash transfer, `⟨V,V⟩_{Λ₀} = ∑_{w,w'} Φ(w-w') = ℓP`; by step 2 and the
   transfer with `D` (determinant `ℓ`) plus the index comparison,
   `⟨V,V⟩_{Λ₀} = |a|^2·ℓ^{2-k}·P`. Equate and cancel `P ≠ 0`.

The hypothesis enters only in step 3. If `ε` factors through `N/ℓ`, every such
`d` has `ε(d) = 1`, the character sum has no content, and the conclusion is
false — an old form inflated from level `N/ℓ` keeps its lower-level eigenvalue
(Δ inflated from level 1 to level `ℓ` is the standard example). Math note §7 has
the full statements and the display equations; do not re-derive them here.

## 2. The two pin modules

| pin | lines | declarations | options |
|---|---:|---:|---|
| `Definitions/Def_CuspForm_PeterssonCoset.lean` | 744 | 56 public: 49 `theorem`, 6 `def`, 1 `structure`; 48 in `CuspForm.PeterssonCoset`, 8 in `CuspForm.PeterssonCoset.Nice` | `maxHeartbeats 800000` |
| `P2M/Sol/S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean` | 979 | 76 public: 71 checker-visible in `…LiNormSq` + 4 `scoped instance`s, plus the top-level `solution` | `maxHeartbeats 3200000`, `p2m_reactivate` |
| `Theorems/Thm_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean` | 19 | 1 (the headline) | — |

`Def_CuspForm_PeterssonCoset` imports only mathlib and
`Definitions/Def_AutomorphicForm_ModularFundamentalDomain` — the latter is already
ported, with `goodSet`, `tsum_indicator_smul_fd` and `tsum_setLIntegral_fd_smul`
public, so the six-module exact-volume chain deferred in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md) is **not** involved. The silo imports five
definition modules — four of them ported, the fifth the coset module above — mathlib,
and the pin's `P2M.Util` scaffolding, which does not cross the boundary.

The silo's own split (measured by section, the natural wave boundaries):

| section | declarations | lines | content |
|---|---:|---:|---|
| `groups` | 48 (52 with the four `scoped instance`s) | 476 | `Lam0`, `tGL`, `tConj`, `dConj`, `lowSL`, the cocycle and the coset equivalences |
| `qexp` | 7 | 99 | `one_mem_strictPeriods`, `hasSum_F`, `qParam_tGL_smul`, `qParam_heckeDiag_smul`, `geom_sum_root`, `sum_apply_tGL_smul`, `sum_slash_tGL` |
| `main` | 16 | 361 | `dens_slash`, `nice_cuspForm`/`nice_slash_tGL`, `pair_slash_tGL_tGL`, `exists_lowCocycle`, `slash_eq_smul_of_hasNebentypus`, `exists_unit_of_not_factorsThrough`, `charStep_arith`, `phi`/`Φ`, `norm_sq_eq` |
| header + `solution` | 1 | 43 | imports and the `p2m` forwarder |

(The `qexp` section's theorems are `hasSum_F`, `qParam_tGL_smul`,
`qParam_heckeDiag_smul`, `geom_sum_root`, `sum_apply_tGL_smul`, `sum_slash_tGL` —
small statements over mathlib's `qExpansion`, each cheap and each load-bearing for
step 2.)

The silo uses 16 declarations of the coset module, most of them heavily (occurrence
counts in the 979 lines): `val_mapGL_eq` 10, `pair` 8, `Nice` 7 (with `Nice.sum`),
`mapGL_injective` 4, `det_entries` 3, `pair_slash` 3, `petersson_self_eq_dens` 3,
`pair_smul_left` 2, `pair_eq_relIndex_mul` 2, `dens` 2, and once each
`pair_smul_right`, `pair_sum_left`, `pair_sum_right`, `dens_nonneg`,
`eq_zero_of_pair_self_eq_zero`, `card_quotient_eq_of_conj`; from the
fundamental-domain module it takes `goodSet` and `tsum_indicator_smul_fd`.

## 3. The measurements

Already taken; re-running them is wasted work unless the tree has changed.

* **The silo is a graph leaf** — `cites 0` in the docs-site graph, so
  `frontier.py` prices it **1 node / 979 lines** and both `--ready` and `--hops`
  hide it. In the canonical D-S read
  (`python3 frontier.py --ds --include-leaves --rank-by silo --top 0 --list`) it
  is **rank #2 of 464 leaves by silo**, behind only
  `M4aTorus.completedRayL_fe`; the KF1 note recorded 470 for its own read.
* `port_advise` prices it at **72 declarations, 0 helpers, 0 already in the port**
  — a fresh transcription with no private prelude to fold in, not a splice.
* The sibling `norm_sq_lt` (893 lines / 57 declarations, `used_by` 1 / 4) is
  itself in the D-S `needed` set and imports the **same** coset module, so the
  definition layer is paid once for two leaves.

## 4. The definition layer, and the 18 shared declarations

The pin wrote its coset-integral layer twice: once in the `S_` file of the
adjointness (from which our `CuspForm.PetHeckeAdj` engine was transcribed) and
again, whole, in `Def_CuspForm_PeterssonCoset.lean`. **18 of the coset module's
56 declarations are statement-identical to declarations already in the engine**:

`mp_smul_SL`, `mp_smul_GL`, `measurable_smul_SL`, `measurable_smul_GL`,
`splitEquiv`, `tsum_SL_eq`, `tsum_SL_inv`, `tsum_Λ_inv`, `wt`, `measurable_wt`,
`indicator_smul`, `tsum_wt_smul`, `ae_tsum_wt_smul`, `tsum_G_eq`,
`weight_lintegral`, `cvn_lintegral`, `cosum`, `petersson_polarization`.

That is a third of the module and the reason this leaf is not a from-scratch
1.7k-line job. Two organizations were available, and the first was taken:

* **Move.** Put the 18 in the new coset module (they are *definitions* and
  belong to the definition layer, not to a proof engine) and have
  `PeterssonHecke.lean` import it; the engine drops from 118 to 100 registered
  declarations and the 18 keep their statements, with their `-- pin:` markers
  re-pointed at `Def_CuspForm_PeterssonCoset.lean`. Cost: the engine's remaining
  proofs must still compile against the imported names, and the register and the
  checker both need a refresh.
* **Alias.** Leave the engine untouched and restate the 18 in
  `CuspForm.PeterssonCoset` as one-line references to `CuspForm.PetHeckeAdj.*`
  (`theorem cosum := PetHeckeAdj.cosum`). Cheap and local, at the price of the
  same statement living under two namespaces — the duplication the playbook §5
  warns about.

Everything else in the module is new: the pairing API (`Nice` and its eight
`Nice.*` lemmas, `pair`, `pair_slash`, `pair_conj_symm`, `pair_smul_*`,
`pair_sum_*`, `pair_self_eq_lintegral`, `eq_zero_of_pair_self_eq_zero`,
`pair_eq_relIndex_mul`, `cosum_eq_relIndex_mul`), the relative-index machinery
(`eMap`, `eMap_bijective`, `card_quotient_eq_of_conj`), `unfold_sum`, and the
`integral_cosum_*` family whose statements differ from the engine's (`Nice` here,
`Adm` there). Roughly **38 fresh declarations**.

Two conventions the math depends on and a "helpful" rewrite would break:

* `pair` is the **raw** integral `∫_𝒟 cosum Λ 1 (petersson k F G)`: no
  normalization. The index factor appears only in `pair_eq_relIndex_mul`. Math
  note §7.4's two values of `⟨V,V⟩` rely on exactly this.
* The antilinear slot is the **first**; `pair_smul_left` therefore produces
  `conj c`, and step 3's `ε(d)` comes from `conj (ε(d)⁻¹) = ε(d)`.

## 5. The cut plan

Two sets, `P1` the definition layer and `P2` the silo; each wave is one work order
of ~500 content lines or less.

### 5.1 P1 — `ModularForms/Analytic/PeterssonCoset.lean` (landed 2026-10-18)

Namespace `CuspForm.PeterssonCoset`; 744 pin lines, 56 declarations; landed as
**821 lines / 56 declarations**, 0 errors, 0 warnings, module build **7.4 s**
(3,575 jobs, `lake build FLTForHuman.ModularForms.Analytic.PeterssonCoset`), edit
loop at the default 200,000-heartbeat cap — the pin's `800000` was not carried.

* *P1a — the coset-integral core* (18 declarations): exactly the statement-identical
  group — `wt`, `measurable_wt`, `indicator_smul`, `tsum_SL_eq`/`tsum_SL_inv`/
  `tsum_Λ_inv`, `tsum_wt_smul`, `ae_tsum_wt_smul`, `tsum_G_eq`, `weight_lintegral`,
  `cvn_lintegral`, `cosum`, `petersson_polarization`, `splitEquiv`, `mp_smul_SL`/
  `mp_smul_GL`, `measurable_smul_SL`/`measurable_smul_GL` — **moved** out of the
  engine (see below).
* *P1b — the pairing* (38 declarations): `Nice` + `Nice.*`, the `integral_cosum_*`
  family in its `Nice` form (the engine's is stated for `Adm` and does **not**
  carry over), `pair` + `pair_*`, `cosum_eq_relIndex_mul`, `eMap`/`eMap_bijective`,
  `card_quotient_eq_of_conj`, `unfold_sum`, `dens`/`dens_nonneg`/
  `petersson_self_eq_dens`/`continuous_dens`/`norm_petersson_le`.
* The module imports `ModularFundamentalDomain` (ported), the `peterssonOn`
  definition module and mathlib only. It does not import the engine.

**The move, and what it cost.** The 18 went from `PeterssonHecke.lean` into this
module, and the engine now imports and opens `CuspForm.PeterssonCoset`:

| | before | after |
|---|---:|---:|
| `PeterssonHecke.lean` lines / declarations | 1,368 / 118 | 1,150 / 100 |
| `PeterssonCoset.lean` lines / declarations | — | 821 / 56 |
| register (`UNWIRED-PUBLIC.md`) | 3,705 public | 3,687 public |

The engine, its tier-1 façade and this module all build green after the move; the
register was regenerated and `--check` is current. Adaptations, all proof-only (no
statement changed):

1. the pin's `set_option maxHeartbeats 800000` dropped (playbook §3.5);
2. `haveI : Countable (SL(2, ℤ) ⧸ Λ)` dropped from `weight_lintegral` — the port's
   `ModularFundamentalDomain` cut supplies the instance (as it does for the engine);
3. `if_pos` → `ite_eq_left` (two sites, deprecation);
4. one narrow `set_option linter.style.haveILetI false in` on
   `cosum_eq_relIndex_mul`, whose three instance bindings (`FiniteIndex`, `Finite`,
   `Fintype` of `Γ'' ⧸ Λ.subgroupOf Γ''`) are load-bearing for the `tsum`.

**Wiring, already done.** The module is in `PORT_FILES`, its pin source
`Definitions/Def_CuspForm_PeterssonCoset.lean` in `SOURCES` (both appended last),
and the checker reads **9,933 identical (+56), 0 mismatched, 0 missing** with 42
own-proof exemptions.

### 5.2 P2 — `ModularForms/Analytic/NormSqPow.lean` (landed 2026-10-18)

Work order: [WORKORDER-P2-normsq.md](WORKORDER-P2-normsq.md).

New module, namespace `CuspForm.LiNormSq` (the pin's sub-namespace, so the
checker's dotted fallback keeps working); 979 pin lines, 71 declarations + the
headline. **Landed: 1,104 lines, 72 checker-visible declarations, 76 markers** (the extra
four are the pin's `scoped instance`s), 0 errors/0 warnings at the 200k cap, module build 11 s,
`#print axioms` `[propext, Classical.choice, Quot.sound]`.

* *P2a — `groups`* (48 checker-visible / 52 with the four `scoped instance`s; 476 lines):
  **landed 2026-10-18** — 586 lines, 52 markers, 0 errors/0 warnings at 200k, module build 6.1 s;
  the one real drift was `Matrix.SpecialLinearGroup` as a semireducible `def` (playbook §7).
* *P2b — `qexp`* (7 declarations / 99 lines): **landed 2026-10-18** — the `q`-expansion
  identities verbatim, 697 lines / 59 markers, 0 errors/0 warnings at 200k, module build 7.1 s;
  no new drift (three deprecation/linter items only).
* *P2c — `main`* (16 declarations / 361 lines): **landed** — `Nice` slashes,
  `slash_eq_smul_of_hasNebentypus`, `exists_unit_of_not_factorsThrough`, `charStep_arith`,
  `phi`/`Φ`, and the headline `norm_sq_eq`. The heartbeat risk did **not** materialise: the whole
  wave is ≈1.3 s of user CPU, the `hV1`/`hV2` chain is not the hotspot (setup ≈1.1 s, `hV1`
  ≈0.3 s, `hVD`+`hidx`+`hPG`+`hV2` ≈1.0 s), and the single slowest leaf is an 823 ms `congr 2`
  in the final arithmetic (`h2`).
* *P2c — the headline*: `CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough` in
  namespace `CuspForm`, in the same module, proved by `LiNormSq.norm_sq_eq`. The pin's
  `solution` (`p2m_reactivate` forwarder) is **not** ported, and no façade is needed: the module
  is wired whole (unlike the tier-3 engine, which needed `PeterssonHeckeTheorems.lean`).

The sibling `norm_sq_lt` is a third set, taken after P2: it reuses P1 and needs no
new definition layer. It landed as P3 — see §5.3, which also records what it shares
with P2 (24 declarations, not the 18 above: a different overlap, in the two silos'
common prelude, not in the coset module).

### 5.3 P3 — `ModularForms/Analytic/NormSqLt.lean` (landed 2026-10-18)

Work order: [WORKORDER-P3-normsq-lt.md](WORKORDER-P3-normsq-lt.md). Record:
[logs/normsq-lt.md](../../logs/normsq-lt.md).

**The dedup finding.** The two silos share their *prelude*: 24 of P3's 57 declarations are
statement-identical to declarations already ported in P2 (`CuspForm.LiNormSq`: `Lam0`, `mem_Lam0`,
`Lam0_le_Gamma1`, `Gamma_le_Lam0`, `Gamma_le_Gamma1`, `mul_apply'`, `intCast_eq_one_iff`,
`dConj`, `dConjInv`, `dConjMat`/`dConjInvMat` (one port declaration), `det_dConjMat`,
`det_dConjInvMat`, `dvd_10_of_mem_Lam0`, `dvd_01_of_mem_Gamma`, `mapGL_dConj`, `mapGL_dConjInv`,
`heckeDiag_mul_eq`, `heckeDiag_mul_eq'`, `hasSum_F`, `dens_slash`, `nice_cuspForm`,
`slash_eq_smul_of_hasNebentypus`, `one_mem_strictPeriods`, and the four `scoped instance`s). So
the 893-line silo is **≈614 net new lines / 30 new declarations**, not 893.

**Two names that look like variants are subsumed.** `geom_sum_root` and `qParam_heckeDiag_smul`
appear in both silos, over `p` here and over `ℓ` there; but the prime is a *section variable* in
both, so `CuspForm.LiNormSq`'s copies are the same universally quantified statements and serve this
silo at `ℓ := p`. They are not declared here — the consumers in `sum_apply_heckeMatrix_smul` call
the imported lemmas (bare, via `open CuspForm.LiNormSq`, the implicit prime unifying with `p`).
The first landing declared them; the review substituted them at the consumers, which is why the
delta is +31 and not +33, and why the tree has one copy of each rather than two.

**Shape.** One **listed** module, namespace `CuspForm.HeckeBoundGamma1`, importing
`NormSqPow.lean` with `open CuspForm.LiNormSq` and `open scoped CuspForm.LiNormSq` — the pin's
silo has its prelude in the same file, so its proofs use those names unqualified and the two
`open`s reproduce that. Checker **+31** (30 declarations + the headline), 0 mismatched / 0
missing; the whole file (including the 169-line `norm_sq_lt`) fits the 200k heartbeat cap, so
the pin's `3200000` is not carried. `Gamma1_le_of_dvd` was the fourth copy of that fact in the
tree; it is now a one-line wrapper over the homed mathlib supplement
`CongruenceSubgroup.Gamma1_le_of_dvd`, and the three `private` copies elsewhere were deleted in the
same wave ([logs/gamma1-le-of-dvd-home.md](../../logs/gamma1-le-of-dvd-home.md)).

## 6. Wiring and the checker delta

Append last, per the checker's convention:

* `SOURCES`: `Definitions/Def_CuspForm_PeterssonCoset.lean`, then
  `P2M/Sol/S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean`,
  then the wrapper.
* `PORT_FILES`: `ModularForms/Analytic/PeterssonCoset.lean` and
  `ModularForms/Analytic/NormSqPow.lean`, then the façade.

Landed deltas: the coset module **+56** (9,877 → 9,933) and the silo **+72** (71 helpers +
the headline; `solution` skipped), i.e. **+128** for the set, 0 mismatched / 0 missing. (Between
them the checker also moved +8 from the manager's promotion of the `det_*`/`denom_*` family in
`Defs/HeckeOperator.lean`, which is not part of this set.) The current reading is **10,013
identical, 0 mismatched, 0 missing**. If the definition layer is kept tier 3 instead — 56 rows under
`-- pin:` markers in [spec/UNWIRED-PUBLIC.md](../../spec/UNWIRED-PUBLIC.md) —
the silo's helpers still wire as above, and the markers make any unlisted
declaration an `UNWIRED` exemption rather than `MISSING IN FLT` (the checker's
tier-3 fallthrough, 2026-10-18); the delta is then +72 only.

The coset module is **definition-shaped**: its statements are the pin's spellings, so
a mismatch there is a transcription bug, never a legitimate adaptation. The silo's 72
statements are the pin's too — the port adapts proofs, never statements.

## 7. Risks and what not to do

* **The heartbeat budget is the unpriced cost.** The silo carries
  `maxHeartbeats 3200000` and the coset module `800000`; the playbook forbids
  carrying either. The expensive declarations are the coset-sum/integral
  computations — `pair_slash`, `integral_cosum_pair`, and above all the `main`
  section's `hV1`/`hV2` chain (the two computations of `⟨V,V⟩`, math §7.4).
  Bisect a blow-up in a `Scratch.lean` at the default cap; do not raise the cap.
* **Do not re-derive the 18.** They are statement-identical and already built;
  a fresh copy is the failure mode this note exists to prevent (playbook §5).
* **`Lam0` is not the engine's `Lam`.** Measured: **0 statement-identical
  declarations** between the two pin files' `groups` sections (`Lam0 M ℓ` has
  four divisibility conditions, `Lam N p` has `Γ₁(N)` plus `p ∣ b`), so the
  `groups` wave is new mathematics, not a substitution of `Lam`/`gInf`/`sigP`.
* **`Nice` is not `Adm`.** The engine's admissible predicate is `Adm`; the coset
  module's is the `structure Nice` with eight lemmas. No overlap to exploit.
* **The `p2m` scaffolding is dropped.** `p2m_reactivate`, `p2m_exact_reverting`
  and `solution` do not cross the boundary; the façade re-proves the wrapper.
* **Keep the convention.** Raw `pair`, antilinear-first, and the pin's
  `petersson_self_eq_dens` orientation: math §7.4's `ℓ^{k-2}` factor is exactly
  the determinant factor of the transfer, and a normalized re-statement would
  change it.

## 8. Reproduce

```sh
cd tools/deps
# the leaf, its rank and the sibling (already taken; re-run only if the tree moved)
python3 frontier.py --ds --include-leaves --rank-by silo --top 0 --list
python3 frontier.py --target CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough --top 0
# the silo's own pricing
python3 port_advise.py --target \
  P2M/Sol/S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean
```

The 18 shared declarations, against the engine (run from the repository root):

```sh
python3 - <<'EOF'
import importlib.util, sys
from pathlib import Path
from collections import defaultdict
spec = importlib.util.spec_from_file_location("chk", "lean/spec/old_check_stmts.py")
chk = importlib.util.module_from_spec(spec); sys.modules["chk"] = chk; spec.loader.exec_module(chk)
pin = Path.home() / "proj" / "fermats-last-theorem"
eng = chk.raw_declarations(Path("lean/FLTForHuman/ModularForms/Analytic/PeterssonHecke.lean").read_text())
cos = chk.raw_declarations((pin / "Definitions/Def_CuspForm_PeterssonCoset.lean").read_text())
by = defaultdict(list)
for r, k, s in eng:
    by[(k, s)].append(r.rsplit(".", 1)[-1])
same = [(r.rsplit(".", 1)[-1], by[(k, s)][0]) for r, k, s in cos if (k, s) in by]
print(len(same), "statement-identical:", sorted(n for n, _ in same))
EOF
```

Build discipline and closing, per the playbook and the predecessor's §5:

```sh
cd lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/ModularForms/Analytic/PeterssonCoset.lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/ModularForms/Analytic/NormSqPow.lean
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.ModularForms.Analytic.NormSqPow
python3 spec/old_check_stmts.py          # +128 identical, 0 mismatched / 0 missing
python3 tools/deps/unwired_register.py --check
python3 spec/old_check_stmts.py --selftest
```

Closing: `#print axioms CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough`
must be `[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/
`native_decide`; no `import Mathlib`; every public declaration carries its
`-- pin:` comment.
