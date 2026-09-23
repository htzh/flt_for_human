# T6 — the local exchange and the normal closure (1 node)

**Status (2026-09-23): work order written, not started.** Second topic of SET 2;
read [SET-2.md](SET-2.md) first. Depends on **T5** (the bifibre count) and SET 1's
T2/T3/T4.

**Audience.** A fresh session continuing SET 2 after T5's `Bifibre.lean` lands. The
method is [porting-playbook.md](../../porting-playbook.md) §3–§5; the plan is
[PORTING-AC.md](../PORTING-AC.md) §3.1, §3.3 and §8 (risk 3).

**Goal.** Prove `Place.sum_ramificationIndex_mul_inertiaDeg_exchange` in
`FLTForHuman/AlgebraicCurve/WeilExchange/LocalExchange.lean`, by the pin's two-stage
route: prove the Galois case (`exchange_of_isGalois`), then reduce the separable case
to it through the **normal closure** `Env F E`.

This is the local identity T7's divisor exchange reduces to for a single place
`wA` of `A` (see [TOPIC-t7-divisor-exchange.md](TOPIC-t7-divisor-exchange.md) §1),
so its exact statement is what the capstone calls.

## 1. The statement

Wrapper: `Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean`.
Pin: `P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean`
(255 raw / 174 content).

```lean
theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange
    {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E]
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F E]
    [IsScalarTower K F₁ E] [IsScalarTower K F₂ E]
    [IsScalarTower F F₁ E] [IsScalarTower F F₂ E]
    [FiniteDimensional F F₁] [FiniteDimensional F F₂] [FiniteDimensional F E]
    [FiniteDimensional F₁ E] [FiniteDimensional F₂ E] [Algebra.IsSeparable F E]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂)
    (hw₁ : w₁.restrict F = v) (hw₂ : w₂.restrict F = v)
    (T : Finset (Place K E))
    (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ =
      w₁.inertiaDeg F * w₂.ramificationIndex F
```

## 2. The pin's structure, and what to keep public

The pin's `S_` file has four layers, in order:

1. **the shared prelude** (`inertiaDegAlong_congr`, `isIntegral_toAlgHom`,
   `toAlgHom_comp_toAlgHom`, `restrict_restrict`,
   `ramificationIndex_eq_mul_ramificationIndex_restrict`,
   `inertiaDeg_eq_mul_inertiaDeg_restrict`) — **already written once in SET 1's
   `WeilExchange/Transport.lean` as `AlgebraicCurve.BifibreDev.*` / `AlgebraicCurve.Place.*`.
   Import it. Do not reproduce the pin's `BifibreW2` copy.**
2. **the envelope**, `section Envelope` with `variable (F E) [Field F] [Field E]
   [Algebra F E]`:
   - `abbrev Env : Type _ := ↥(IntermediateField.normalClosure F E (AlgebraicClosure E))`;
   - `isGalois_env [FiniteDimensional F E] [Algebra.IsSeparable F E] : IsGalois F (Env F E)`
     — via `IsAlgClosure.normal`, `AlgEquiv.ofInjectiveField`,
     `IntermediateField.isSeparable_iSup`, then `exact ⟨⟩`;
   - `@[reducible] noncomputable def algebraEnv (R) [Field R] [Algebra R E] :
     Algebra R (Env F E) := ((algebraMap E (Env F E)).comp (algebraMap R E)).toAlgebra`;
   - `isScalarTower_env_mid`, `isScalarTower_env_base`, `isScalarTower_env_bot`,
     `isScalarTower_env_const` — the four local `IsScalarTower` instances, each
     `IsScalarTower.of_algebraMap_eq` with a `Subtype.ext` tower proof.
3. **the two mathematical stages**:
   - `exchange_of_isGalois` — the Galois-case exchange: apply T5's
     `sum_ramificationIndex_mul_inertiaDeg_bifiber` to get the `F`-weighted sum,
     rewrite each term by `ramificationIndex_eq_mul_ramificationIndex_restrict`
     (T4) and `inertiaDeg_eq_mul_inertiaDeg_restrict` (T4) using `hT`, and cancel
     `w₁.ramificationIndex F * w₂.inertiaDeg F` (positive: the first from
     `Place.ramificationIndex_pos`, the second from T5's
     `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` + T4's
     `inertiaDeg_eq_mul_inertiaDeg_restrict` + `exists_restrict_eq`).
   - `sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable` — the separable
     case: install `Algebra F₁ (Env F E) := algebraEnv F E F₁`, the same for `F₂`,
     the four `IsScalarTower` instances, `IsGalois F (Env F E) := isGalois_env`,
     and apply `exchange_of_isGalois (Env F E)`.
4. **the public node**, `sum_ramificationIndex_mul_inertiaDeg_exchange`: the same
   `letI`/`haveI` envelope installation, then `exchange_of_isGalois (Env F E)`.

**Keep `Env`/`algebraEnv`/`isScalarTower_env_*` `private`** (instance plumbing, no
wrapper); **keep `exchange_of_isGalois` and
`sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable` public** — they are the
two-stage mathematics the blueprint's clarity argument is about, and the pin has
them public too. Append `P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange.lean`
to the checker's `SOURCES` so their last names are verified; if a name fails to
match, record it in `OWN_PROOFS` with the reason rather than weakening it.

## 3. Route notes and traps

- **The instance block is the topic's named shape risk** (risk 3). Every one of
  the four `isScalarTower_env_*` proofs is `IsScalarTower.of_algebraMap_eq` +
  `Subtype.ext` + a `← IsScalarTower.algebraMap_apply` rewrite. Transcribe
  literally; keep `algebraEnv` `@[reducible]` (the `letI := algebraEnv …`
  installations depend on it unfolding) and keep `isScalarTower_env_mid`'s
  `letI`/`rfl` shape. `isScalarTower_env_const` takes `omit [Algebra R E] in`.
- **The separable reduction reuses the envelope with `R := F₁` and `R := F₂`.**
  The pin installs six local instances in `sum_..._of_isSeparable` and again in
  the public node — the two blocks are identical; write them as the pin does
  (there is no clean way to factor them across the two binder lists, and inventing
  one is scope creep).
- **`hgen` and `hLD` are hypotheses, never discharged.** They are the Hecke roof's
  generation and degree facts.
- **`hf₂ : 0 < w₂.inertiaDeg F`** is the subtle positivity step inside
  `exchange_of_isGalois`: lift `w₂` to `M := Env F E` by `exists_restrict_eq`, use
  `card_fiberOver_mul_ramificationIndex_mul_inertiaDeg` to know
  `(fibre).card * (e * f) = finrank ≠ 0`, and `Nat.pos_of_ne_zero`. Transcribe it;
  it is the only place T5's card lemma and T6's cancellation meet.
- The final cancellation is `Nat.eq_of_mul_eq_mul_right (Nat.mul_pos he₁ hf₂)`;
  `he₁` is `Place.ramificationIndex_pos`.

## 4. Budget and stop-early

**2 goal rounds, checkpoint at 1.** 174 content lines, of which the envelope is
~45 and the two stages ~120. The instance block is the only place it can stall.

**Stop early, and report rather than restate, on**: an `isScalarTower_env_*` proof
needing a different tower lemma; `algebraEnv` needing to stop being `@[reducible]`;
or `exchange_of_isGalois`'s cancellation needing a positivity statement the T5
surface does not expose.

## 5. Definition of done

- [ ] `WeilExchange/LocalExchange.lean` with the public node statement verbatim,
      `exchange_of_isGalois` and `sum_..._of_isSeparable` public, the envelope
      `private`, and the T4 prelude imported (no `BifibreW2` copy).
- [ ] Consumer **Zone G** (`[exchange]`) at 0 errors: the exchange applied to a
      concrete abstract square (this is T7's wire-test rehearsal), with the
      `algebraAlong`/`IsScalarTower` setup itself as the test.
- [ ] `spec/check_flt_statements.py`: the wrapper plus the pin `S_` source in
      `SOURCES`; 0 mismatched, 0 missing.
- [ ] `#print axioms` on the exchange clean.
- [ ] `timeout 300 lake build` green, 0 warnings, no `sorry`.
- [ ] `logs/ac-port.md` T6 section; `README.md` row.
- [ ] The T7 hand-off: the exact name and binders of
      `Place.sum_ramificationIndex_mul_inertiaDeg_exchange` as the capstone calls
      it, and confirmation that the T4 prelude and the T5/T6 facts T7's proof uses
      are public.

## 6. Reporting back

Beyond [SET-2.md](SET-2.md) §3: (1) whether the envelope's four tower instances
needed help and what; (2) whether the pin's two `letI` blocks really are identical
or only propositionally equal; (3) the exact public surface T7 will consume.
