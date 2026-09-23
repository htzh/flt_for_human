# T5 — the generic orbit/index engine and the bifibre count (5 nodes)

**Status (2026-09-23): work order written, not started.** First topic of SET 2;
read [SET-2.md](SET-2.md) first (hand-off surface, zones, build discipline pointer).
Depends on SET 1's **T2, T3, T4**.

**Audience.** A fresh session opening SET 2. The method is
[porting-playbook.md](../../porting-playbook.md) §3–§5; the plan is
[PORTING-AC.md](../PORTING-AC.md) §3.1, §5 (T5's note) and §8 (risk 1). Read the
SET 1 hand-off in [SET-2.md](SET-2.md) §0 — in particular that the pin's
`BifibreDev` prelude is **already public in `WeilExchange/Transport.lean`** and must
be imported, not restated.

**Goal.** Three things:

1. two generic group-theory statements in
   `FLTForHuman/FieldTheory/FiniteGroupAction.lean`, beside `CommonRoot.lean`
   (`MulAction.ncard_orbit_inter_orbit_mul_card` and
   `Subgroup.exists_eq_mul_of_index_inf_eq`);
2. the fibre/cardinality bridge `Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`
   and the surjectivity-of-restriction `Place.exists_restrict_eq`;
3. the bifibre count `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber` in
   `WeilExchange/Bifibre.lean`.

**This is the effort's one genuinely new proof.** Everything SET 1 wrote was
transcription against a mathlib API; here the two generic statements have no
direct mathlib counterpart and the bifibre argument re-derives an orbit–stabiliser
count in a place-theoretic setting. Scout first (§3.0).

## 1. The scouted inventory

| declaration | raw/c | ext | home |
|---|---|---|---|
| `MulAction.ncard_orbit_inter_orbit_mul_card` | 165/134 | 0 | `FieldTheory/FiniteGroupAction.lean` |
| `Subgroup.exists_eq_mul_of_index_inf_eq` | 48/29 | 0 | same |
| `Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` | 47/18 | 6 | `WeilExchange/Bifibre.lean` |
| `Place.exists_restrict_eq` | 41/15 | 34 | same |
| `Place.sum_ramificationIndex_mul_inertiaDeg_bifiber` | 375/269 | 0 | same |

Statements verbatim from the wrappers:

```lean
theorem MulAction.ncard_orbit_inter_orbit_mul_card {G : Type*} [Group G] {X : Type*}
    [MulAction G X] [Finite G] [MulAction.IsPretransitive G X] (H₁ H₂ : Subgroup G)
    (hprod : ∀ g : G, ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂) (x₁ x₂ : X) :
    (MulAction.orbit H₁ x₁ ∩ MulAction.orbit H₂ x₂).ncard * Nat.card X =
      (MulAction.orbit H₁ x₁).ncard * (MulAction.orbit H₂ x₂).ncard

theorem Subgroup.exists_eq_mul_of_index_inf_eq {G : Type*} [Group G] [Finite G]
    (H₁ H₂ : Subgroup G) (h : (H₁ ⊓ H₂).index = H₁.index * H₂.index) (g : G) :
    ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, g = h₁ * h₂

theorem AlgebraicCurve.Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
    {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (w : Place K F') (W : Place K M) (hW : W.restrict F' = w) :
    (w.fiberOver M).card * (W.ramificationIndex F' * W.inertiaDeg F') = Module.finrank F' M

theorem AlgebraicCurve.Place.exists_restrict_eq
    {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [Algebra.IsSeparable F' M]
    (w : Place K F') : ∃ W : Place K M, W.restrict F' = w
```

`Place.sum_ramificationIndex_mul_inertiaDeg_bifiber` is the 5th; its binders are the
long `{K F F₁ F₂ E} (M : Type*) …` list in its wrapper (37 typeclass arguments —
transcribe from the wrapper, not from memory).

## 2. Route notes

### 2.1 The two generic statements — the new mathematics

- **`Subgroup.exists_eq_mul_of_index_inf_eq` is the smaller and cleaner.** The pin
  proves it via the coset action `G ⧸ H₁`: a private `stabilizer_mk_one_eq`
  (`stabilizer H₂ (1 : G ⧸ H₁) = H₁.subgroupOf H₂`), then
  `H₁.relIndex H₂ = H₁.index` from the hypothesis, `MulAction.index_stabilizer`
  (v4.34: `MulAction.index_stabilizer`, **not** root-level) to show the `H₂`-orbit
  of `1` has full `ncard`, `Set.eq_of_subset_of_ncard_le` + `Set.finite_univ` to
  make it `univ`, and `QuotientGroup.eq` to read off the product. It is 29 content
  lines; the only API risks are `QuotientGroup.eq`'s exact form and
  `Subgroup.relIndex`/`index` bookkeeping.
- **`MulAction.ncard_orbit_inter_orbit_mul_card` is the hard one.** The pin's proof
  introduces **six private helpers**, all of which the port should keep `private`:
  `card_eq_mul_of_card_fiber` (a finite-type cardinality lemma: if every fibre of
  `f : α → β` has card `c` then `Nat.card α = Nat.card β * c`, via
  `Equiv.sigmaFiberEquiv`); `card_preimage_eq_mul_of_card_fiber` (the same over a
  subset); `card_fiber_smul_eq` (`Nat.card {g // g • x = g₀ • x} = Nat.card
  (stabilizer G x)`); `card_smul_mem_eq` (`Nat.card {h : H // h • x ∈ B} =
  (orbit H x ∩ B).ncard * Nat.card (stabilizer H x)`, via
  `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`-style ingredients);
  `card_fiber_psi_eq` (`Nat.card {p : H₁ × H₂ // (p.2)⁻¹ * p.1 = g} = Nat.card
  (H₁ ⊓ H₂)`, using the hypothesis `hprod`); then
  `ncard_orbit_inter_orbit_mul_card_eq`, the actual count via a double-fibration
  argument (`Nat.card A` computed two ways and cancelling a positive factor).
  mathlib has the orbit–stabiliser ingredients (`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`,
  `MulAction.index_stabilizer`, `Subgroup.relIndex_mul_index`, `Subgroup.index_inf_le`,
  `Subgroup.card_mul_index`, `Nat.card_prod`) but not these statements. Transcribe
  the pin's proof; the arithmetic is `Nat.eq_of_mul_eq_mul_right` + `ring` on
  `Nat.card`s.

### 2.2 The three `Place` nodes

- **`card_fiberOver_mul_ramificationIndex_mul_inertiaDeg`** is three lines of
  mathematics on top of T2: apply
  `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` to `w`, show every term
  of the fibre sum equals the single term at `W` (via
  `Place.ramificationIndex_eq_of_restrict_eq`/`Place.inertiaDeg_eq_of_restrict_eq`
  from **T3**, using `restrict_eq_of_mem_fiberOver` and `hW`), collapse
  `Finset.sum_const` + `nsmul_eq_mul`, and `exact_mod_cast`.
- **`exists_restrict_eq`** is a `by_contra` + `omega` argument on T2's sum identity:
  if the fibre is empty (`Finset.eq_empty_of_forall_notMem`) the sum is zero but
  `Module.finrank_pos` says the RHS is positive. Note the pin's `push Not at hne`
  is the old `push_neg`; use `push_neg at hne` (or `simp only [not_exists, not_not]
  at hne`).
- **`sum_ramificationIndex_mul_inertiaDeg_bifiber`** is the assembly. It is the
  pin's `BifibreDev` namespace after the prelude:
  1. `resHom (L) : (M ≃ₐ[L] M) →* (M ≃ₐ[F] M)` (`σ ↦ σ.restrictScalars F`);
  2. `galAction : MulAction (M ≃ₐ[F] M) (Place K M)` as
     `MulAction.compHom` along `SemilinearAut.ofAlgAut ∘ resHom` — **keep the
     `@[reducible] noncomputable def`** so `g • W` unfolds;
  3. `gal_smul_def`, `mem_range_resHom_iff`, `card_range_resHom`
     (`MonoidHom.ofInjective`), `index_range_resHom`
     (`Subgroup.card_mul_index` + `IsGalois.card_aut_eq_finrank` +
     `Module.finrank_mul_finrank`), `orbit_range_resHom_eq`
     (`MulAction.orbit … = ↑((P.restrict L).fiberOver M)` via
     `Place.exists_algEquiv_smul_eq_of_restrict_eq`), `orbit_gal_eq`
     (`MulAction.orbit (M ≃ₐ[F] M) P = ↑((P.restrict F).fiberOver M)`);
  4. `image_val_orbit` (a set-image identity on subtype orbits) and
     `forall_apply_algebraMap_eq_of_adjoin_eq_top` (the `Adjoin`-equality descent
     to `E` via `AlgHom.equalizer`);
  5. the assembly: `exists_restrict_eq` twice to lift `w₁`, `w₂` to `M`;
     `card_fiberOver_mul_…` twice; the `T`-indexed bijection
     (`Finset.card_biUnion` + `PairwiseDisjoint`); `Subgroup.exists_eq_mul_of_index_inf_eq`
     for `hprod`; then `MulAction.ncard_orbit_inter_orbit_mul_card` applied to the
     `MulAction.orbit (M ≃ₐ[F] M) P₁` subtype, with the four `ncard` identifications
     (`cX`, `c₁`, `c₂`, `c₁₂`) and the two `Module.finrank_mul_finrank` products
     (`hnn`), finishing by cancelling `Module.finrank F M * Module.finrank E M`.
  Import the T4 prelude for `restrict_restrict`.
  `Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` is **in this same
  module** and is used by the assembly; T6 also uses it.

## 3.0 The route scout (do this first)

Before writing `FiniteGroupAction.lean`, prototype in the gitignored
`Scratch.lean`: state `MulAction.ncard_orbit_inter_orbit_mul_card` and
`Subgroup.exists_eq_mul_of_index_inf_eq` and try the pin's helper route. The point
is to discover, cheaply, whether any of the six helper lemmas needs a mathlib
statement that has moved or is missing. Report in the log:

- which of the six helpers transcribed unchanged;
- any mathlib rename or shape change (with the v4.34 name);
- the scout's wall-clock cost.

If the scout shows the route is blocked, **stop the run** (per SET-2's preface)
rather than porting around it — the reviewer will decide whether to take a
different route or move T8/T9 ahead.

## 4. Named shape risks

| risk | mitigation |
|---|---|
| the orbit-intersection count has no mathlib statement | the six private helpers are the route; transcribe them, do not invent |
| `Subgroup.index`/`relIndex` bookkeeping | `Subgroup.relIndex_mul_index`, `Subgroup.index_inf_le`, `MulAction.index_stabilizer` (note the `MulAction.` namespace) |
| the `resHom`/`MulAction.compHom` packaging | keep `galAction` `@[reducible]`; `gal_smul_def` should be `rfl` |
| the two statements' hypotheses | `[Finite G]` + `[MulAction.IsPretransitive G X]` are the wrappers'; `IsGalois` supplies pretransitivity in the application |
| the long 37-argument bifibre binder list | copy it from the wrapper; the checker is textual |
| the `Finset.card_biUnion` disjointness proof | `Finset.disjoint_left` + `mem_fiberOver` |

## 5. Budget and stop-early

**3 goal rounds, checkpoint at 1.** The generic engine is ~163 content lines of
*new* proof; the bifibre is 269 content lines of assembly; two of the five nodes
are 15–18 lines. Budget three and use the first for the scout.

**Stop early, and report rather than restate, on**: the scout showing a helper's
mathlib ingredient missing; an `ncard` goal where `Set.ncard` and `Nat.card`
diverge (quote it); or the bifibre's `Finset.sum_bij`/`ncard` identifications
needing a statement the T2/T3/T4 surface does not expose.

## 6. Definition of done

- [ ] `FieldTheory/FiniteGroupAction.lean` with the two generic statements public
      (wrappers' binders) and the six/one helpers `private`; a docstring naming each
      principle and pointing at [math/009](../../../math/009-hecke-jacobian-commute.md).
- [ ] `WeilExchange/Bifibre.lean` with the three `Place` nodes public; the T4
      prelude imported, not restated.
- [ ] Consumer **Zone F** at 0 errors, including a **concrete instantiation** of the
      generic orbit-intersection count (the FFG generic-kernel lesson: budget the
      instantiation, not the transcription — a finite group action on a small
      concrete `X`).
- [ ] `spec/check_flt_statements.py`: the five wrappers
      (`Thm_MulAction_ncard_orbit_inter_orbit_mul_card.lean`,
      `Thm_Subgroup_exists_eq_mul_of_index_inf_eq.lean`, the three
      `Thm_AlgebraicCurve_Place_*`) in `SOURCES`; 0 mismatched, 0 missing.
- [ ] `#print axioms` on the bifibre count and the two generic statements clean.
- [ ] `timeout 300 lake build` green, 0 warnings, no `sorry`.
- [ ] `logs/ac-port.md` T5 section (with the scout outcome) and `README.md` rows.
- [ ] The T6/T7 hand-off: `Bifibre.lean` exposes the bifibre count, and its
      `card_fiberOver_…`/`exists_restrict_eq` are public for T6/T7.

## 7. Reporting back

Beyond [SET-2.md](SET-2.md) §3: (1) the scout outcome and the six helpers' fate;
(2) whether `MulAction.index_stabilizer`/`index_stabilizer_of_transitive` were the
right v4.34 names and whether `QuotientGroup.eq` was; (3) the instantiation you
chose for the generic wire test and its cost.
