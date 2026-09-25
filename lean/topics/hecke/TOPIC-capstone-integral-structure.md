# Capstone — the trace lemma and the integral structure

**Status: done and reviewed (2026-09-24).** `IntegralStructure.lean` landed at
374 lines (the 3 headlines + 33 `private` helpers); the manager's independent
re-run: full build 4332 jobs green, checker **1312 identical / 70 promoted / 0
mismatched / 0 missing / 15 own (1327 checked)**, consumer exit 0, `#print axioms`
clean, and **0 occurrences of `HeckeEis`/`ModPForms`/`PeriodPair`/the route-A
criterion** in the module. One spec correction from the run: the `IsFiniteRelIndex`
witness follows from `Subgroup.relIndex_mul_index` + `index_ne_zero`, not from the
`relIndex_le_index` bound the spec hinted (`relIndex ≤ index` does not give
`relIndex ≠ 0`). This is the manager's capstone, the last declaration block of the
route-C′ effort. The route plan is
[TOPIC-route-c-prime-integral-structure.md](TOPIC-route-c-prime-integral-structure.md);
the mathematics is [../../../math/013-integral-structure-gamma1-basis.md](../../../math/013-integral-structure-gamma1-basis.md) §5.

**Target module:** `FLTForHuman/ModularForms/WeightOne/IntegralStructure.lean`.

**It is the only module that creates the theorem** `CuspForm.HasIntegralStructure`,
replacing route A's 657-node Eichler–Shimura tower. Everything it needs is already
ported: the slash basis `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`
(SET-11 `Gamma1IntegralBasis.lean`), the definitions `CuspForm.intLattice` /
`CuspForm.HasIntegralStructure` (`Defs/IntegralStructure.lean`), and mathlib's
`CuspForm.trace` (see below).

## 1. The mathematics (recap of math/013 §5)

With `Γ₁ = Γ₁(N) ⊴ Γ₀ = Γ₀(N)` of finite index `r`, let `b₁…b_n` be a `ℂ`-basis of
`S_k(Γ₁)` such that every `Γ₀`-translate `bᵢ ∣[k] γ` has integral `q`-coefficients.
Then `Pᵢ = T(bᵢ)` with `T(v) = Σ_{q : Γ₀ ⧸ Γ₁} v ∣[k] q` satisfies:
`Pᵢ ∈ S_k(Γ₀)`, `Pᵢ` has integral `q`-coefficients (finite sum), and `{Pᵢ}` spans
`S_k(Γ₀)` because `T(w) = r · w` for `w ∈ S_k(Γ₀)`. Hence
`span_ℂ (intLattice N k) = ⊤`, for every `k` (no Sturm bound, no `k ≥ 2` needed).

## 2. Manager's API findings (do not re-derive)

- **mathlib already provides the trace map.**
  `CuspForm.trace (ℋ) (f) : CuspForm ℋ k` for `f : CuspForm 𝒢 k`, in
  `Mathlib/NumberTheory/ModularForms/NormTrace.lean`; its `toFun` is
  `∑ q : ℋ ⧸ (𝒢.subgroupOf ℋ), quotientFunc f q`, with
  `quotientFunc f q = (f : ℍ → ℂ) ∣[k] (q.out)⁻¹`.
  So `Pᵢ := CuspForm.trace (CongruenceSubgroup.Gamma0 N) (b i)` is the bundled
  `Pᵢ`, and the Γ₀-invariance/holomorphy/cusp-vanishing are mathlib's.
- **The one gap: `[𝒢.IsFiniteRelIndex ℋ]` is not an instance for `Γ₁ ≤ Γ₀`.**
  `inferInstance` fails (checked). Supply it. Route:
  `(Γ₁ : Subgroup (GL _)).relIndex (Γ₀ : Subgroup (GL _)) ≠ 0`. The coercion is
  `Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)`; use
  `Subgroup.relIndex_comap` + `Subgroup.comap_map_eq_self_of_injective
  Matrix.SpecialLinearGroup.mapGL_injective` to transfer to the `SL(2,ℤ)` relIndex,
  then bound it by the index: `Subgroup.relIndex_le_index` with
  `(CongruenceSubgroup.Gamma1 N).FiniteIndex` (mathlib) giving `index ≠ 0`.
  A local `instance` is acceptable; it is ours (no wrapper) — see §4.
- **Restriction `Γ₀ → Γ₁`.** Needed to apply `T` to a `Γ₀`-form for the spanning
  identity. Build `private def restrictCusp (w : CuspForm Γ₀ k) : CuspForm Γ₁ k`
  with the anonymous constructor: `toFun := w`,
  `slash_action_eq' γ hγ := w.slash_action_eq' γ (CongruenceSubgroup.Gamma1_in_Gamma0 N hγ)`,
  `holo' := w.holo'`, and
  `zero_at_cusps' hc γ hγ := w.zero_at_cusps' ((isCusp_iff_of_relIndex_ne_zero
  (CongruenceSubgroup.Gamma1_in_Gamma0 N) hrel c).mp hc) γ hγ`
  (`hrel` is the instance's `relIndex_ne_zero`; mathlib's cusp sets agree for
  finite-relative-index subgroups).
- **`T(w) = r • w` as bundled forms**, by function extensionality: for
  `g ∈ Γ₀`, `quotientFunc (restrictCusp w) q = w ∣[k] g⁻¹ = w` by `w.slash_action_eq'`
  and `inv_mem`, so the sum is `Fintype.card (Γ₀ ⧸ Γ₁) • w`. `r ≠ 0` as
  `(Fintype.card _ : ℂ)`.
- **`qCoeff` of the trace.** `ModularFormClass.qCoeff` is additive over the finite
  sum (`ModularForm.qExpansion_add`, or a local `qCoeffLin` as in
  `Gamma1Basis.lean`); each `quotientFunc (b i) q = bᵢ ∣[k] g⁻¹` with
  `g = q.out : Γ₀`, and `g` is `mapGL ℝ γ` for some `γ ∈ Γ₀` (extract via
  `Subgroup.mem_map`); `γ⁻¹ ∈ Γ₀`, so the basis hypothesis gives the integrality of
  each summand, hence of `Pᵢ`.

## 3. The declarations

1. `theorem CuspForm.hasIntegralStructure_of_basis_gamma1 {N : ℕ} [NeZero N] {k : ℤ}
   (h : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
     ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ m : ℕ,
       ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ)) :
   CuspForm.HasIntegralStructure N k` — **ours**, the trace lemma of §1. Its whole
   proof is §2; it may use `private` helpers and the local `instance`.
2. `theorem CuspForm.hasIntegralStructure_of_two_le (N' : ℕ) [NeZero N'] (k : ℤ)
   (hk : 2 ≤ k) : HasIntegralStructure N' k` — statement **verbatim** from
   `Theorems/Thm_CuspForm_hasIntegralStructure_of_two_le.lean`; proved by applying
   (1) to `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast N' k`
   (`hk` unused — the lemma gives every `k`).
3. `theorem CuspForm.hasIntegralStructure_two (N : ℕ) [NeZero N] :
   CuspForm.HasIntegralStructure N 2` — statement **verbatim** from its wrapper;
   the `k = 2` instance of (2) (or of (1)).

## 4. Build discipline and checker

- Fixed bounds, never raised/bypassed: `timeout 60 lake env lean <file>`,
  `timeout 180 lake build <module>`, `timeout 240 lake build`. Never raise
  `maxHeartbeats`/`maxRecDepth`; never bump a bound. Diagnose a bound hit as in
  SET-11 §1 (missing opens → PID CPU → bisect); `/usr/bin/time -v` under-attributes
  lake's `lean` child.
- Specific imports (no bare `import Mathlib`); zero warnings; no `sorry`/`admit`;
  copy the pin wrappers' binders exactly.
- Checker: append the two wrappers to `SOURCES` and the module to `PORT_FILES`;
  `CuspForm.hasIntegralStructure_of_basis_gamma1` is **ours** → add its last name
  to `OWN_PROOFS` with the reason "ours; the pin's two routes to this statement are
  the Eichler–Shimura tower". The local `IsFiniteRelIndex` instance and the
  `private` helpers are invisible to the checker. Target **0 mismatched,
  0 missing**.
- Extend `spec/WeightOneConsumer.lean` with the three `#check`s and one executed
  application: apply (2) at a concrete `N', k` and apply (1) to SET-11's basis.
- `#print axioms` on the three headlines: `[propext, Classical.choice, Quot.sound]`.
- `README.md` row; the module header links math/013 §5; remove temp files.
- **No commits; do not touch the pin, FFG, Sturm, or any `WeightOne/*` module
  except by import.**

## 5. Report back

1. Module line count, declaration count, build time, checker before/after.
2. Whether the `IsFiniteRelIndex` instance was needed and how it was proved.
3. The exact shape used for the spanning step (`T(w) = r • w`) and for the
   `qCoeff`-of-trace integrality.
4. Any statement that would not match its wrapper, quoted rather than weakened.
5. Any bound hit, with the diagnosis evidence.
6. Confirmation the pin/FFG/Sturm are untouched and no cap was raised.
