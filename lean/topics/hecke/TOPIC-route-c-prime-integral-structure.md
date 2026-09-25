# Topic: route C′ — the integral structure from an integral Γ₁-basis

**Status: delivered (2026-09-24).** Executed as SET-5 … SET-11 plus the manager's
capstone; all 11 modules under `FLTForHuman/ModularForms/WeightOne/` are green and
the checker is **1312 identical / 0 mismatched / 0 missing** (15 own proofs, the
trace lemma). `IntegralStructure.lean` proves `HasIntegralStructure` with zero
route-A dependency. Successor of [TOPIC-t10-finite-algebra.md](TOPIC-t10-finite-algebra.md)
§7, where `HasIntegralStructure`'s existence was left out of reach; the scout is
[../../../studies/route-c-prime-scout.md](../../../studies/route-c-prime-scout.md).
This topic ports the **weight-one/Deligne–Serre cone** (which the endgame needs
for `frey_isModular` anyway) and adds one new **trace lemma** that turns its
integral Γ₁-basis into `CuspForm.HasIntegralStructure` — replacing route A's
657-node Eichler–Shimura tower for that target.

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured in this checkout with mathlib prebuilt
> (`v4.34.0`, `leanprover/lean4:v4.34.0`):
> `lake env lean <module>` on a green port module of 200–350 lines is **~4 s**;
> `lake build <module>` with deps cached is **~2–5 s**; a full `lake build` after
> one file edit is **under a minute**; a `whnf`/heartbeat stall at the default cap
> errors in **~15–20 s** — it does not hang.
>
> - Run every build under a bound: `timeout 60 lake env lean <file>`,
>   `timeout 180 lake build <module>`, `timeout 240 lake build`. Non-return at the
>   bound is a blow-up, not patience.
> - **Quarantine immediately.** On a timeout, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch.lean` with
>   `set_option diagnostics true`. Do not re-run hoping for a different result.
> - **Never raise `maxHeartbeats`.** The project cap is `4000000`
>   (`lakefile.lean`). The likely stall points *here* are (a) the four large
>   analytic `S_` files (`EisensteinWeightOne.e1Chi3IsModular` 3,816 lines, the
>   `WLight` frickeFunction/`levelN` block 1,000–1,500 lines each) and (b) the
>   trace lemma's `Fintype`/`Finset` coset sums over `Γ₀ ⧸ Γ₁`, which are exactly
>   the `Finset`-sum reindexing shape that cost `TOPIC-slash-invariance.md` §2.4.
>   Keep the pin's lemmas stated over concrete function types (`ℍ → ℂ`), not a
>   bare `FunLike` variable; port the `WLight` package's own `private` helpers
>   rather than re-deriving them.
> - Tell a blow-up from contention by CPU time: high user CPU + timeout is real;
>   ~0 CPU wall-time is lock contention with another agent's build.

**Audience.** A fresh session taking the successor of T10. Read
[../../../studies/route-c-prime-scout.md](../../../studies/route-c-prime-scout.md)
(all of it — it is the specification of *why* this cone and *what* the lemma is),
the mathematics
[../../../math/013-integral-structure-gamma1-basis.md](../../../math/013-integral-structure-gamma1-basis.md),
then [TOPIC-t10-finite-algebra.md](TOPIC-t10-finite-algebra.md) §7 and
[TOPIC-t9-integral-lattice.md](TOPIC-t9-integral-lattice.md) (the `intLattice`
API this consumes), and [porting-playbook.md](../../porting-playbook.md) §3–§5,
§7 for the method.

**Goal.** Port the C′ cone and prove, in this order:

1. the **53-node cone** of `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`
   (48 new nodes, ≈33.4k raw `S_` lines; five nodes already ported), in
   bottom-up dependency order;
2. the **trace lemma** `CuspForm.hasIntegralStructure_of_basis_gamma1` (§3), ours;
3. the two **corollaries** `CuspForm.hasIntegralStructure_of_two_le` and
   `CuspForm.hasIntegralStructure_two`, statement-verbatim from their wrappers but
   proved through (2) instead of route A.

Route A's `CuspForm.hasIntegralStructure_of_moduleFinite_of_linearIndependent`,
the `HeckeEis.*` Eichler–Shimura comparison and `Def_CuspForm_ModPForms` are **not
ported** — that is the point of the topic.

## 1. Why this topic, and what is settled

- **C′ holds** (scout §2): with `b₁…b_n` a `ℂ`-basis of `S_k(Γ₁(N))` whose every
  `Γ₀(N)`-slash has integral `q`-coefficients, the coset sums
  `P_i = Σ_γ b_i ∣[k] γ` are `Γ₀(N)`-cusp forms with integral `q`-coefficients
  and span, because the trace is `[Γ₀:Γ₁] •` the identity on `S_k(Γ₀(N))`. Hence
  `HasIntegralStructure N k` for all `k` (not only `k ≥ 2`). **No Sturm bound and
  no Eichler–Shimura are involved.**
- **The correct ingredient is the slash form**, not the brief's
  `exists_basis_gamma1_qCoeff_mem_range_intCast` (which does not exist).
  `exists_basis_gamma1_qCoeff_slash_mem_range_intCast` (183 `S_` lines) is the
  general-weight statement; `exists_basis_gamma1_two_qCoeff_mem_range_intCast` is
  its weight-2, `γ = 1` child.
- **The cone is endgame, not throwaway** (scout §4b). BFS gives a shortest premise
  chain of 15 from `FLT.fermatLastTheorem`
  (`… → frey_isModular → No2BridgeWiring → LanglandsTunnell → DeligneSerre →` the
  basis theorem), and a second independent 19-step path through
  `CuspForm.IsPrimitiveForm.*` / Taylor–Wiles. All 53 nodes lie in
  `closure(No2BridgeWiring) ⊂ closure(fermatLastTheorem)`, so porting them is
  required for the endgame's weight-one modularity regardless of this topic.
- **The trace lemma is additive.** It replaces none of the 53 declarations. If the
  weight-one branch is ported anyway, the route-specific cost is the lemma alone;
  standalone the cone is 53 nodes / 33,719 lines against route A's 657 / 263,720.
- **The landed definition modules are prerequisites.** `Defs/EisensteinChiNegThree.lean`
  (`E1Chi3IsModular` as a `Prop`) and `Defs/IntegralLattice.lean` were marked
  "parked for a future congruence topic" in T10; they are in fact the interface of
  the C′ ingredient. Keep them.

## 2. The scouted inventory

Cluster totals from `tools/deps` graph closure + `S_`-file lines (the metric that
reproduces route A's 263,720):

| cluster | nodes | raw `S_` lines | role |
|---|---|---|---|
| `WLight.*` | 17 | 13,941 | level-one Hauptmodul, frickeFunction/LevelN packages |
| `ModularCurve.*` | 10 | 5,773 | Γ₀-slash rationality/integrality, discriminant product |
| `CuspForm.*` | 10 | 4,905 | Γ₁ Galois/q-coefficient basis, span by `E₄ᵃE₆ᵇ` |
| `EisensteinWeightOne.e1Chi3IsModular` | 1 | 3,816 | weight-one χ₋₃ Eisenstein modularity |
| `ModularForm.*` | 5 | 1,921 | `gamma1_qExpansion_coeff_mem_of_frickeRational`, `weierstrassP_torsion_qExpansion_package`, finite-dim |
| `IsIntegral.*` | 2 | 1,036 | monic-relation span transfer |
| `EisensteinSeries.*` | 2 | 753 | `exists_modularForm_coe_eq_eisensteinG`, `qExpansion_eisensteinG_coeff` |
| `ModularFunction.*` | 1 | 739 | `exists_mdifferentiable_sigmaTransport_of_frickeQuotient` |
| `UpperHalfPlane.*` | 2 | 585 | `linearIndependent_complex_of_qExpansion_coeff_mem` |
| `IsAlgClosed.*` | 1 | 151 | `exists_algEquiv_apply_ne_of_notMem_range` |
| `PowerSeries.*` | 1 | 68 | `mem_range_map_of_monic_of_mul_mem_range` |
| **total** | **53** | **33,719** | 48 new; five already ported |

Already ported (`PORT_FILES` hit, keep and import — do not re-port):
`Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj` (31),
`UpperHalfPlane.qExpansion_prod` (35),
`ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic` (56),
`ModularForm.levelOne_eq_zero_of_lt_order_qExpansion` (82),
`ModularCurve.qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit` (76)
(`SturmBound.lean`, `QExpansionOrder.lean`, `JqAnalyticModel.lean`).

The **port order is the closure order**, computed bottom-up by sorting the cone
nodes by their own graph closure size (`tools/deps`). The cone's leaves come
first: `CuspForm.finiteDimensional_of_isArithmetic`,
`ModularForm.finiteDimensional_of_isArithmetic`,
`PowerSeries.mem_range_map_of_monic_of_mul_mem_range`,
`IsIntegral.mem_span_of_adjoin_simple_constants`(+`_transcendental`),
`IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range`,
`UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem`; the slash
basis theorem is the last cone node, just below the trace lemma. The largest
*files* — a cost list, not the order — are
`e1Chi3IsModular` (3,816), `frickeFunction_intBaseChange` (1,500),
`span_frickeRational_E4_pow_E6_pow_eq_top` (1,390),
`exists_monicRel_j_K_of_mdifferentiable_frickeQuotient` (1,388),
`exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant` (1,362),
`exists_levelFraction_of_stable_family` (1,331),
`weierstrassP_torsion_qExpansion_package` (1,317),
`exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0` (1,267),
`levelN_structure_package` (1,239), `levelOne_hauptmodul_package` (1,186).

The `WLight.*` nodes are large *self-contained* files: `levelOne_hauptmodul_package`
is 1,186 lines and cites *no* FLT theorem node (closure 1) — it is level-one
Hauptmodul/`j`-function/q-expansion-principle analysis on top of mathlib, not a
wrapper. Budget it as new analysis, not transcription.

## 3. The trace lemma — the only new mathematics

Target statement (ours; the pin has no analogue, which is why the route was
missed):

```lean
theorem CuspForm.hasIntegralStructure_of_basis_gamma1 {N : ℕ} [NeZero N] {k : ℤ}
    (h : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ m : ℕ,
        ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ)) :
    CuspForm.HasIntegralStructure N k
```

**Proof obligations, in dependency order.**

1. **Normality / subgroup bookkeeping.** `Γ₁(N) ⊴ Γ₀(N)`:
   `CongruenceSubgroup.Gamma1' N = (CongruenceSubgroup.Gamma0Map N).ker` in mathlib
   `CongruenceSubgroups.lean`; `Gamma1_in_Gamma0 N` gives `≤`. Get `Normal` from
   the kernel (or use `Gamma1'` and the subtype equivalence). Needed so
   `b i ∣[k] γ` is again `Γ₁`-invariant for `γ ∈ Γ₀`.
2. **Finite quotient and representatives.** `(CongruenceSubgroup.Gamma1 N).subgroupOf (CongruenceSubgroup.Gamma0 N)`
   has `FiniteIndex` (kernel of a hom into the finite `ZMod N`); mathlib's
   `Subgroup.fintypeQuotientOfFiniteIndex` gives `Fintype (Γ₀ ⧸ Γ₁)` and
   `Quotient.out` chooses representatives. Reuse the port's coset patterns in
   `HeckeRepresentatives.lean` / `HeckeAnalytic.lean` if they fit.
3. **Build `P i`.** `P i = ∑ q : Γ₀ ⧸ Γ₁, (b i) ∣[k] (q.out : SL(2,ℤ))` as a
   function; then a bundled `CuspForm (Gamma0 N) k` via the anonymous structure
   constructor (as `Reserve/ModularForms/CuspFormNorm.lean` does):
   `toSlashInvariantForm` from the function, `slash_action_eq'` from coset-sum
   invariance, `holo'` from finite sums of `MDiff`, `zero_at_cusps'` from finite
   sums of vanishing functions.
4. **Integral members.** Each `P i` has integral `q`-coefficients (finite sum of
   the hypothesis), so `P i ∈ CuspForm.intLattice N k` via
   `Submodule.subset_span` (`Defs/IntegralStructure.lean`) after the
   `qCoeff`-of-a-sum rewrite.
5. **Spanning.** For `w ∈ S_k(Γ₀(N))`, `∑ q, w ∣[k] q.out = (index : ℂ) • w`;
   expand `w = ∑ c_i • b i` and get `w ∈ Submodule.span ℂ {P i}`, hence
   `Submodule.span ℂ (intLattice N k) = ⊤` by `Submodule.span_le` /
   `span_mono`, then `HasIntegralStructure`.

**Shape risks.** (a) The quotient sum: `Quotient.out` choices make `simp` slow —
state the trace identity once as its own helper for an arbitrary representative
system (`hT : ∀ v, ∑ q, v ∣[k] q.out = r • v`), then specialise. (b) The
`CuspForm` constructor's `slash_action_eq'` for `Γ₀` from invariance under
generators is the one place needing care; `Subgroup` membership under
`mapGL`/`subgroupOf` coercion is the usual friction. (c) `S_k(Γ₀) = S_k(Γ₁)^{Γ₀}`
needs only `Gamma1_in_Gamma0`; do not route through `HasNebentypus`.

## 4. Module layout and tier order

One subdirectory for the new theory (`porting-playbook.md` §8), inside
`FLTForHuman/ModularForms/`:

| module | contents |
|---|---|
| `ModularForms/WeightOne/EisensteinSeries.lean` | `EisensteinSeries.exists_modularForm_coe_eq_eisensteinG`, `qExpansion_eisensteinG_coeff` |
| `ModularForms/WeightOne/EisensteinChiNegThree.lean` | `EisensteinWeightOne.e1Chi3IsModular` (imports the existing `Defs/EisensteinChiNegThree.lean`) |
| `ModularForms/WeightOne/LevelOneHauptmodul.lean` | `WLight.levelOne_hauptmodul_package`, `weierstrassP_qExpansion_package`, `isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le`, `linearIndependent_complex_of_qExpansion_rational`, `ModularCurve.qExpansion_discriminant_eq_X_mul_tprod`, `ModularCurve.surjective_specialLinearGroup_map_zmod` |
| `ModularForms/WeightOne/Basic.lean` | `PowerSeries.mem_range_map_of_monic_of_mul_mem_range`, `IsIntegral.mem_span_of_adjoin_simple_constants`(+`_transcendental`), `IsAlgClosed.exists_algEquiv_apply_ne_of_notMem_range`, `UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem`, `ModularForm/CuspForm.finiteDimensional_of_isArithmetic` |
| `ModularForms/WeightOne/FrickePackage.lean` | the nine `WLight.frickeFunction_*` / `levelN_structure_package` / `exists_levelFraction_*` / `exists_monicRel_*` / `qExpansion_sigmaTransport_package` / `exists_qExpansion_coeff_mem_*` / `exists_twist_of_flat` / `span_inter_rational_of_twist_stable` nodes + `ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient` |
| `ModularForms/WeightOne/Gamma0Rationality.lean` | `ModularCurve.exists_ratCast_qExpansion_{comp_smul,slash}_of_mem_Gamma0`, `exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant`, `exists_isIntegralQExp_smul_of_ratCast_qExpansion`, `exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin`, `exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem`, `ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational` |
| `ModularForms/WeightOne/Gamma1Basis.lean` | `CuspForm.exists_gamma1_qCoeff_eq_algEquiv_apply`(+`_of_even`), `CuspForm.exists_gamma1_frickeRational_sigmaTransport`, `CuspForm.exists_mul_E4_pow_mul_E6_pow_eq_iff`, `CuspForm.span_frickeRational_E4_pow_E6_pow_eq_top`, `ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq`, `CuspForm.exists_basis_gamma1_qCoeff_mem_adjoin_exp`(+`_of_even`), `CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` |
| `ModularForms/WeightOne/IntegralStructure.lean` | **ours**: §3's lemma and the two `HasIntegralStructure` corollaries |

Port **tier by tier, build after each module** (playbook §5.5): Basic → EisensteinSeries
→ EisensteinChiNegThree → LevelOneHauptmodul → FrickePackage → Gamma0Rationality →
Gamma1Basis → IntegralStructure. Do not batch; a broken layering here is much
cheaper to bisect than in a 30k-line cone.

## 5. Consumer wiring

- `CuspForm.hasIntegralStructure_of_two_le` (wrapper
  `Theorems/Thm_CuspForm_hasIntegralStructure_of_two_le.lean`) follows by applying
  `CuspForm.hasIntegralStructure_of_basis_gamma1` to
  `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast N' k` — the
  `hk : 2 ≤ k` binder is simply unused, since the lemma gives every `k` — and
  `CuspForm.hasIntegralStructure_two` is the `k = 2` instance. Both statements are
  transcribed, so the checker verifies them; only the lemma is exempted.
- The downstream targets of T10 (`HasIntegralStructure.moduleFinite/Free_heckeAlgebra`,
  `moduleFinite_heckeAlgebra`, `intLattice_fg`) consume these unchanged. **Route A
  declarations are not a prerequisite of any of them.**
- `Defs/IntegralStructure.lean` (`intLattice`, `HasIntegralStructure`) is the only
  port-side interface imported; `Defs/IntegralLattice.lean` is not used by the
  trace lemma (it is the χ₋₃ `HasIntegralBasis` vocabulary).

## 6. Checker, consumer, verification

- **Checker.** Append every ported wrapper (`Theorems/Thm_WLight_*`,
  `Thm_EisensteinWeightOne_e1Chi3IsModular`, `Thm_EisensteinSeries_*`,
  `Thm_ModularCurve_*`, `Thm_CuspForm_*` in the cone — the wrappers exist, checked)
  to `SOURCES`, the eight new modules to `PORT_FILES`, and
  `CuspForm.hasIntegralStructure_of_basis_gamma1` to `OWN_PROOFS` with the reason
  "ours; the pin's two routes to this statement are different". Target
  **0 mismatched, 0 missing**.
- **Spec consumer.** Extend `spec/SturmConsumer.lean`'s Zone E (or add a zone):
  consume `exists_basis_gamma1_qCoeff_slash_mem_range_intCast` at a concrete
  `N, k` and apply the corollary, so the cross-module composition is executed, not
  only `#check`ed.
- **Axioms.** `#print axioms` on the lemma and both corollaries must be
  `[propext, Classical.choice, Quot.sound]`.
- **Build.** `timeout 240 lake build` green, 0 warnings, no `sorry` — but run the
  per-module bound (`timeout 90 lake build <module>`) throughout; the four big
  files are where a blow-up will appear.

## 7. Budget, stop conditions, reporting

**Budget: 4–6 goal rounds.** Tier weights: Basic + Eisenstein 2 rounds; the two
Hauptmodul/Fricke modules 1–2; Γ₀Rationality + Γ₁Basis 1; trace lemma + wiring 1.
The cone is transcription-heavy (`WLight` package files are self-contained), so
the estimate is driven by *shape risks*, not line count.

**Stop and report on:**
- a ported statement that does not match its wrapper (checker mismatch);
- the trace lemma needing a `Γ₀`-invariance input the slash basis does not supply
  (the scout's hypothesis is the only one assumed — if more is needed, C′ is
  weaker than scouted and the study's §9 Q1 must be re-opened);
- any target pulling in `HeckeEis.*`, `Def_CuspForm_ModPForms`, `PeriodPair.*` or
  `sturm_bound` (that is route A bleeding in; the C′ cone has none of them);
- a build past its bound (§2 of the build-discipline header).

**Report back:**
1. the actual module split and any `WLight` file that needed a helper the wrapper
   does not export;
2. whether the trace lemma's coset sum needed a monomorphic helper (playbook §3.5)
   and its shape;
3. the checker counts and the `#print axioms` output;
4. confirmation that `grep -c` of `HeckeEis`/`ModPForms`/`PeriodPair` in the new
   modules is 0.

**Definition of done.**

- [ ] eight modules under `FLTForHuman/ModularForms/WeightOne/`, cone statements
      verbatim from their wrappers;
- [ ] `CuspForm.hasIntegralStructure_of_basis_gamma1` proved, axioms clean;
- [ ] `hasIntegralStructure_of_two_le` / `_two` proved through it;
- [ ] checker **0 mismatched, 0 missing**, the lemma the only new exemption;
- [ ] `timeout 240 lake build` green, 0 warnings, no `sorry`;
- [ ] spec consumer exercises the corollary across modules;
- [ ] `logs/hecke-port.md` (or the successor log) carries the measurements and the
      route-B contrast; `studies/hecke-finiteness-coverage.md` §5/§9 point here.
