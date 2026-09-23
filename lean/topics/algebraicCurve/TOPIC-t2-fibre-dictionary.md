# T2 — the fibre dictionary, `fiberOver`, `le_finrank` (3 nodes + the promoted block)

**Status (2026-09-22): work order written, not started.** Third topic of SET 1;
read [SET-1.md](SET-1.md) first. Depends on **AC0** and **T1**.

**Audience.** A fresh session continuing the port after T1's interface is public and
consumer Zone B is at 0 errors. The method is
[porting-playbook.md](../../porting-playbook.md) §3–§5 and §7; the plan is
[PORTING-AC.md](../../PORTING-AC.md) §4.1 (the 4-way copy), §5 (T2's note) and §8
(risks 3 and 4).

**Goal.** Two things, in this order:

1. **Promote the shared fibre dictionary into one public module.**
   `Defs/PlaceDictionary.lean`, the 17 declarations that the pin copies (byte for
   byte, modulo `p2m_*`) into `le_finrank`, `fiberOver`,
   `hasPrincipalDivisors_of_transcendental` and `inertiaDeg_pos`. This is the
   largest single simplification the AC port has: **737 content lines never
   written** (`PORTING-AC.md` §4.1).
2. Prove the three public nodes:
   `sum_ramificationIndex_mul_inertiaDeg_fiberOver` (439 raw / 340 content),
   `sum_ramificationIndex_mul_inertiaDeg_le_finrank` (443 / 344) and
   `inertiaDeg_pos` (214 / 150), all in `WeilExchange/FiberOverCount.lean`.

**This is the shared prerequisite of both routes.** `PORTING-AC.md` §3.3: after T2,
Route A (T3–T7) and Route B (T8–T9) share nothing but T1. T9 consumes exactly this
dictionary; so does T5. Write it once.

## 1. Why this topic, and what is settled

- **Settled: the whole dictionary block is public, in one module.** `PORTING-AC.md`
  §10 leaves the surface open (whole block vs the two `_fiberCenter` facts). The
  FFG precedent decides it: `Defs/PhiAtSlot.lean` exposed a whole copied prelude and
  let the checker verify it, and the pin's dictionary is *not* private mathematics —
  it is the dictionary between the fibre-centre ideal and the residue field of a
  place. Expose all 17 declarations at their pinned names under
  `AlgebraicCurve.Place`, and let the checker's **dotted fallback** read the pin's
  `private` originals (they need no `OWN_PROOFS` exemption;
  [SET-1.md](SET-1.md) §5 and `check_flt_statements.py` both describe the fallback).
- **Settled: one copy of the Assembly, not two.** The pin ships the 45-line
  `sum_ramificationIndex_mul_inertiaDeg_fiberOver` assembly **twice** (in the
  `fiberOver` and `le_finrank` files, byte-identical). Write it once, public, in
  `WeilExchange/FiberOverCount.lean`, and have `le_finrank` consume it.
- **Settled: the deprecated `Ideal` aliases are handled by the manager's recon,
  not by the blueprint's risk 4 text** — see [SET-1.md](SET-1.md) §3.1 for the
  measured table. In short: `Ideal.ramificationIdx'` is *not* deprecated;
  `Ideal.inertiaDeg'` is (replacement `Ideal.inertiaDeg`, a different argument
  order); `Ideal.ramificationIdx_spec` → `Ideal.ramificationIdx'_spec`;
  `Ideal.inertiaDeg_algebraMap` → `Ideal.inertiaDeg'_algebraMap`;
  `Ideal.inertiaDeg'_pos` → `Ideal.inertiaDeg_pos`; and the pin's
  `Ideal.sum_ramification_inertia` has **no drop-in replacement** — the v4.34
  `Ideal.sum_ramification_inertia_eq_finrank` sums over `q : p.primesOver S` with
  `Fintype` and has RHS `Module.finrank R S`, not `∑ P ∈ primesOverFinset p S` with
  `Module.finrank K L`. **Statements stay the pin's** (the checker is an exact
  textual diff), the module carries `set_option linter.deprecated false` with a
  one-line reason, and the *proofs* migrate to the new lemmas. Do **not** import
  `Mathlib.NumberTheory.RamificationInertia.Basic`: it is a deprecated *module* and
  the import warning cannot be silenced; use
  `Mathlib.NumberTheory.RamificationInertia.{Inertia,Ramification}` and
  `Mathlib.RingTheory.RamificationInertia.Basic`.
- **Settled: keep the pin's `letI`/`haveI` walls and reducibility attributes.**
  `Place.valuationSubringAlgebra` (`@[reducible]`) and `Place.integralClosureAt`
  (`abbrev`, AC0) are load-bearing for the `IsFractionRing` instance. Expect the
  module-level `linter.style.haveILetI` disable the pin's cone-algebra files also
  use. This is risk 3.

## 2. The scouted inventory

### 2.1 `Defs/PlaceDictionary.lean` — the 17 promoted declarations

They sit at `P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean`
lines 28–378 (identical at `..._le_finrank.lean` 28–378 and at
`S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean` 36–386, and the
ResidueDictionary alone at `S_AlgebraicCurve_Place_inertiaDeg_pos.lean` 32–167).
Statements verbatim (the pin writes them `private`; the port writes them public at
these names):

```lean
theorem Place.eq_ord_of_addHom_of_nonneg_iff (φ : F → ℤ)
    (hmul : ∀ x y, x ≠ 0 → y ≠ 0 → φ (x * y) = φ x + φ y)
    (hone : ∃ t, t ≠ 0 ∧ φ t = 1)
    (hiff : ∀ x, x ≠ 0 → (0 ≤ φ x ↔ x ∈ w.toValuationSubring)) {x : F} (hx : x ≠ 0) :
    φ x = w.ord x

theorem Place.neg_log_valuation_fiberCenter_eq_ord (hw : w.restrict F = v) {x : F'} (hx : x ≠ 0) :
    -log ((fiberCenter F' v hw).valuation F' x) = w.ord x

theorem Place.le_ord_iff_mem_pow_fiberCenter (hw : w.restrict F = v)
    {c : integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) :
    (n : ℤ) ≤ w.ord (algebraMap (integralClosureAt F' v) F' c) ↔
      c ∈ (fiberCenter F' v hw).asIdeal ^ n

theorem Place.ramificationIndex_eq_ramificationIdx_fiberCenter (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal

def Place.toValuationSubringOfRestrictEq (hw : w.restrict F = v) :
    integralClosureAt F' v →+* w.toValuationSubring

theorem Place.coe_toValuationSubringOfRestrictEq (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    (toValuationSubringOfRestrictEq hw c : F') = algebraMap (integralClosureAt F' v) F' c

def Place.residueOfCenter (hw : w.restrict F = v) : integralClosureAt F' v →+* w.ResidueField

theorem Place.residueOfCenter_apply (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    residueOfCenter hw c =
      IsLocalRing.residue w.toValuationSubring (toValuationSubringOfRestrictEq hw c)

theorem Place.ker_residueOfCenter (hw : w.restrict F = v) :
    RingHom.ker (residueOfCenter hw) = (fiberCenter F' v hw).asIdeal

theorem Place.surjective_residueOfCenter (hw : w.restrict F = v) :
    Function.Surjective (residueOfCenter hw)

def Place.residueFieldEquivQuotientCenter (hw : w.restrict F = v) :
    integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal ≃+* w.ResidueField

theorem Place.residueFieldEquivQuotientCenter_mk (hw : w.restrict F = v)
    (c : integralClosureAt F' v) :
    residueFieldEquivQuotientCenter hw (Ideal.Quotient.mk _ c) = residueOfCenter hw c

def Place.placeCongrEquiv {u u' : Place K F} (h : u = u') :
    u.toValuationSubring ≃+* u'.toValuationSubring

theorem Place.coe_placeCongrEquiv {u u' : Place K F} (h : u = u')
    (x : u.toValuationSubring) : (placeCongrEquiv h x : F) = (x : F)

def Place.restrictResidueFieldEquiv (hw : w.restrict F = v) :
    (w.restrict F).ResidueField ≃+* IsLocalRing.ResidueField v.toValuationSubring

theorem Place.restrictResidueFieldEquiv_residue (hw : w.restrict F = v)
    (a : (w.restrict F).toValuationSubring) :
    restrictResidueFieldEquiv hw (IsLocalRing.residue _ a) =
      IsLocalRing.residue _ (placeCongrEquiv hw a)

theorem Place.inertiaDeg_eq_inertiaDeg_fiberCenter (hw : w.restrict F = v) :
    w.inertiaDeg F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
        (fiberCenter F' v hw).asIdeal
```

The section context is the pin's: `{K F F' : Type*} [Field K] [Field F] [Field F']
[Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
[FiniteDimensional F F'] [Algebra.IsSeparable F F']`, with `v : Place K F` and
`w : Place K F'` (note `neg_log_valuation_fiberCenter_eq_ord` has `hw : w.restrict F = v`,
so `w.restrict F = v`). `log` is `WithZero.log` (the pin `open WithZero`).

### 2.2 `WeilExchange/FiberOverCount.lean` — the three public nodes

| node | raw/c | ext | statement (from the wrapper) |
|---|---|---|---|
| `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` | 439/340 | 11 | `∑ w ∈ v.fiberOver F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) = (Module.finrank F F' : ℤ)` |
| `Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank` | 443/344 | 12 | `∑ w ∈ S, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) ≤ (Module.finrank F F' : ℤ)` for `S` with `∀ w ∈ S, w.restrict F = v` |
| `Place.inertiaDeg_pos` | 214/150 | 11 | `0 < w.inertiaDeg F` |

Full binders (wrappers):

```lean
theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) :
    ∑ w ∈ v.fiberOver F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) =
      (Module.finrank F F' : ℤ)

theorem AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (S : Finset (Place K F')) (hS : ∀ w ∈ S, w.restrict F = v) :
    ∑ w ∈ S, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) ≤ (Module.finrank F F' : ℤ)

theorem AlgebraicCurve.Place.inertiaDeg_pos
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (w : Place K F') : 0 < w.inertiaDeg F
```

## 3. Route notes, so none of this has to be rediscovered

- **The Assembly, and the one real shape adaptation of the topic.** The pin calls
  `Ideal.sum_ramification_inertia (integralClosureAt F' v) F F' (p := maximalIdeal
  v.toValuationSubring) (maximalIdeal_ne_bot v)`, whose statement is
  `∑ P ∈ IsDedekindDomain.primesOverFinset p S, p.ramificationIdx' P * p.inertiaDeg' P
  = Module.finrank F F'`. That declaration lives only in the deprecated
  `Mathlib.NumberTheory.RamificationInertia.Basic`, so it cannot be used. Replace it
  with the v4.34 theorem (from `Mathlib.RingTheory.RamificationInertia.Basic`):

  ```lean
  Ideal.sum_ramification_inertia_eq_finrank (p := IsLocalRing.maximalIdeal v.toValuationSubring)
      (integralClosureAt F' v) :
    ∑ q : p.primesOver (integralClosureAt F' v), q.1.ramificationIdx v.toValuationSubring *
      q.1.inertiaDeg v.toValuationSubring = Module.finrank v.toValuationSubring (integralClosureAt F' v)
  ```

  Two bridges are therefore needed, and they are **the topic's shape risk**:
  1. `∑ q : p.primesOver S, f q.1` vs `∑ P ∈ IsDedekindDomain.primesOverFinset p S, f P`:
     use `IsDedekindDomain.mem_primesOverFinset_iff (maximalIdeal_ne_bot v)` to
     identify the element sets (`Finset.sum_subtype`/`Finset.sum_congr`).
  2. `Module.finrank v.toValuationSubring (integralClosureAt F' v)` vs
     `Module.finrank F F'`: `v.toValuationSubring` is a DVR with fraction field `F`
     and `integralClosureAt F' v` has fraction field `F'`. Search mathlib for the
     `IsFractionRing`/`Localization` finrank bridge first (`#check` candidates around
     `Module.finrank`, `IsFractionRing`, `IsLocalization.finrank`); if there is no
     direct lemma, the pin's own `finrank_quotient_map`-style route is in
     `Mathlib/NumberTheory/RamificationInertia/Basic.lean` and can be adapted.
     **If this bridge resists, stop and report** — it is the one place T2 can stall,
     and the fallback (a local `linter.deprecated false` plus a *private* re-proof
     of the pin-shaped sum from the new theorem) is a management decision, not the
     agent's.
  After the bridges, the `Finset.sum_bij` along
  `w ↦ (fiberCenter F' v ((mem_fiberOver v).mp hw)).asIdeal` transcribes as before,
  using `IsDedekindDomain.mem_primesOverFinset_iff`, `eq_of_fiberCenter_eq`,
  `placeOfPrime`/`restrict_placeOfPrime`/`fiberCenter_placeOfPrime`, and the two
  dictionary equalities `ramificationIndex_eq_ramificationIdx_fiberCenter`,
  `inertiaDeg_eq_inertiaDeg_fiberCenter` (whose RHS keeps the pin's primed form;
  `Ideal.ramificationIdx'` is not deprecated, `Ideal.inertiaDeg'` is, hence the
  module-level `linter.deprecated false`).
- **`le_finrank` is one line of mathematics**:
  `Finset.sum_le_sum_of_subset_of_nonneg (subset_fiberOver_of_forall_restrict_eq v hS)`
  (the `subset_` lemma is AC0's, in `Defs/PlacesOverDVR.lean`) with
  `fun _ _ _ => mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)`, then
  rewrite by the `fiberOver` equality. The work is the equality, which is why the
  assembly is written once.
- **`inertiaDeg_pos` is a corollary of the dictionary**: `fiberCenter_liesOver rfl`,
  then `inertiaDeg_eq_inertiaDeg_fiberCenter rfl`, then the **new**
  `Ideal.inertiaDeg_pos (fiberCenter F' v rfl).asIdeal v.toValuationSubring` (the
  pin's `Ideal.inertiaDeg'_pos` is deprecated). Note it needs only the
  **ResidueDictionary**, not the Uniqueness block — but it is a T2 node because it
  consumes the same module.
- **`residueOfCenter`/`surjective_residueOfCenter` are the only substantial proofs
  in the dictionary** (the pin's `surjective_residueOfCenter` is ~70 lines). The
  route is `IsLocalRing.residue` plus the fact that `integralClosureAt F' v` maps
  onto `w.toValuationSubring` modulo the centre.
- **`placeCongrEquiv` is a transport of subrings along an equality of `Place`s**
  (using `Place.ext`/`toValuationSubring_injective`); it exists so that
  `restrictResidueFieldEquiv` can compare `(w.restrict F).ResidueField` with
  `v.ResidueField` definitionally.
- **The pin's `inertiaDeg_eq_inertiaDeg_fiberCenter` proof uses
  `Ideal.inertiaDeg_algebraMap`.** Its documented replacement is
  `Ideal.inertiaDeg'_algebraMap` (still primed, hence still a deprecation warning) —
  so either use it under the module's `linter.deprecated false` or use the new
  `Ideal.inertiaDeg_eq`, which needs the extra
  `[Algebra (Localization.AtPrime p) (Localization.AtPrime P)]`/`IsScalarTower`
  instances. Prefer whichever keeps the proof a transcription; record the choice in
  the friction log.

## 4. What is different about this topic

- **It writes one module that four pin files duplicate.** The measured saving (737
  content lines) is the topic's payload; report the *actual* number, not the
  estimate. The three `S_` files also each carry the dictionary under different
  section variables (`w.restrict F = v` in two, bare `v`/`w` in `hasPrincipalDivisors`),
  so the promoted module must pick one binder style and T9 must be able to
  instantiate it.
- **It is where the port meets mathlib's ramification theory.** The FLT-native
  `Place.ramificationIndex`/`inertiaDeg` are proved equal to `Ideal.ramificationIdx'`/
  `Ideal.inertiaDeg'` of `(fiberCenter F' v hw).asIdeal`, and the Assembly applies
  `Ideal.sum_ramification_inertia_eq_finrank`. If the mathlib statement's shape has
  drifted, **quote the drift and stop** — this is the one declaration the whole
  route hangs on.
- **The instance risk is the highest in SET 1.** `letI`/`haveI` walls inside
  `def`s, `@[reducible] valuationSubringAlgebra`, `abbrev integralClosureAt`, and
  the `IsFractionRing` instance. Transcribe literally; if a `synthInstance` loop
  appears, bound the build and bisect rather than raising the cap.
- **`DecidableEq` is not needed here** (that is T7/T8); but `classical` is used in
  the Assembly, so `open Classical`/`classical` at the proof head.

## 5. Budget and stop-early

**2 goal rounds, checkpoint at 1.** The dictionary is a transcription of a
byte-identical block; the three finals are 45 + 1 + 6 lines of mathematics on top.
Two is the threshold.

**Stop early, and report rather than restate, on**: `Ideal.sum_ramification_inertia_eq_finrank`
having a different argument order than the pin's deprecated alias; the section-variable
choice making the promoted dictionary unusable from T9's context; or a
`synthInstance`/`whnf` timeout that survives bounding and bisection.

## 6. Definition of done

- [ ] `Defs/PlaceDictionary.lean` with the 17 declarations public at their pinned
      names under `AlgebraicCurve.Place`; one home, no copies anywhere else.
- [ ] `WeilExchange/FiberOverCount.lean` with the three nodes public, statements
      verbatim, one copy of the Assembly.
- [ ] Consumer **Zone C** (dictionary facts + `le_finrank` on an abstract separable
      extension) at 0 errors, with a proved composition.
- [ ] `spec/check_flt_statements.py`: the three AC wrappers plus the pin's
      `P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean`
      (for the dotted fallback) in `SOURCES`; 0 mismatched, 0 missing.
- [ ] `timeout 300 lake build` green, 0 warnings, no `sorry`.
- [ ] `#print axioms` on `sum_ramificationIndex_mul_inertiaDeg_fiberOver` is
      `[propext, Classical.choice, Quot.sound]`.
- [ ] `logs/ac-port.md` T2 section: the measured savings (dictionary lines actually
      written vs 737 estimated), the `Ideal` deprecation substitutions, and the
      instance-wall record.

## 7. Reporting back

Beyond the shared report: (1) the **real** dictionary line count vs the 737-line
estimate; (2) the exact `Ideal` API substitutions and whether any changed a
statement; (3) whether the public-whole-block choice forced any declaration to
become `private` (it should not); (4) whether `inertiaDeg_pos` in fact needed only
the ResidueDictionary, and if so whether it is better homed in
`Defs/PlaceDictionary.lean`'s module than in `FiberOverCount.lean`.
