# T4 — along-map transport and `Pic0` descent (16 nodes + the shared prelude)

**Status (2026-09-22): work order written, not started.** Fifth and last topic of
SET 1; read [SET-1.md](SET-1.md) first. Depends on **AC0**, **T1**, **T2**, **T3**.

**Audience.** A fresh session closing SET 1 after T3's Galois lemmas land. The
method is [porting-playbook.md](../../porting-playbook.md) §3–§5; the plan is
[PORTING-AC.md](../PORTING-AC.md) §3.1, §4.1 (the `bifiber`/`exchange`
duplication) and §8 (risk 3).

**Goal.** Two things:

1. Prove the 16 transport nodes — restriction/inertia/ramification are functorial
   along a tower of `Alg`-homs, the pushforward and pullback of divisors are
   functorial, `Pic0` descends the correspondence, and the two along-level
   separability/finiteness inputs (`finiteAlong_comp`, `finiteAlong_of_surjective`,
   `separableAlong_of_charZero`) — in `WeilExchange/Transport.lean`.
2. **Write the shared prelude once.** Five helpers
   (`isIntegral_toAlgHom`, `toAlgHom_comp_toAlgHom`, `restrict_restrict`,
   `ramificationIndex_eq_mul_ramificationIndex_restrict`,
   `inertiaDeg_eq_mul_inertiaDeg_restrict`) plus `inertiaDegAlong_congr` are copied
   into `S_..._bifiber` (as `BifibreDev.*`), `S_..._exchange` (as `BifibreW2.*`) and
   `S_..._divisor_exchange` (as `BifibreWEX.*`). `PORTING-AC.md` §4.1 measures
   `restrict_restrict` ×3 and the others ×2 (≈60 content lines). Write them once as
   public lemmas in `Transport.lean`; T5, T6 and T7 must import them, not restate
   them.

The prelude is public rather than `private` because three later modules consume it;
its declarations are the pin's, so the checker verifies them by last-name match
against the T5 `S_` file (`restrict_restrict`,
`ramificationIndex_eq_mul_ramificationIndex_restrict`,
`inertiaDeg_eq_mul_inertiaDeg_restrict`) or by the dotted fallback
(`BifibreDev.isIntegral_toAlgHom`, `BifibreDev.toAlgHom_comp_toAlgHom`,
`BifibreDev.inertiaDegAlong_congr`). If a name will not match, add it to
`OWN_PROOFS` with the one-line reason.

## 1. Why this topic, and what is settled

- **Settled: statements are the wrappers', verbatim.** All 16 have
  `Theorems/Thm_AlgebraicCurve_*.lean` wrappers.
- **Settled: `algebraAlong` stays an `abbrev`.** `restrictAlong_restrictAlong` and
  the four `eA`/`fB`/`fF`/`eF` bridges in T7 are `rfl` statements that hold only
  while `algebraAlong φ` unfolds to `φ.toRingHom.toAlgebra`. This is risk 3, and it
  is the reason `Defs/Correspondence.lean`'s `abbrev` attribute is load-bearing.
- **Settled: the four `Ideal`-free `Pic0` lemmas are transcribed, not re-derived.**
  `mk_eq_zero_iff`, `zsmul_mk`, `nsmul_mk_eq_zero_of_isPrincipal`,
  `zsmul_mk_eq_zero_of_isPrincipal`, `addOrderOf_mk_dvd_of_isPrincipal` are 3–5
  lines each against mathlib's `QuotientAddGroup` API.
- **Settled: `separableAlong_of_charZero` is the 84-external-citer interface
  leaf.** It is a one-liner (`Algebra.IsSeparable.of_integral F F₁`) but it is the
  free separability input of the hecke theorem's roof square.

## 2. The scouted inventory — all 16, with statements

| declaration | raw/c | ext | pin route |
|---|---|---|---|
| `Place.restrictAlong_restrictAlong` | 10/3 | 19 | `rfl` through `Place.ext` |
| `Place.ramificationIndexAlong_comp` | 24/16 | 19 | an irreducible `π`, `ord_coe_irreducible`, `ord_restrictAlong` twice |
| `Place.inertiaDegAlong_comp` | 35/26 | 2 | residue-field tower + `Module.finrank_mul_finrank` |
| `Divisor.pushforwardAlong_pushforwardAlong` | 23/14 | 23 | `Finsupp.addHom_ext` + `pushforwardAlong_single` + the two prelude lemmas + `ring` |
| `Divisor.pullbackAlong_pullbackAlong` | 17/8 | 14 | `ext W` + `pullbackAlong_apply` + `ring` |
| `Divisor.correspondence_congr` | 12/5 | 4 | `subst; rfl` |
| `Divisor.correspondence_correspondence` | 15/6 | 2 | `rw correspondence_apply` three times + `hex` + the two functorialities |
| `Pic0.correspondence_correspondence_comm` | 12/5 | 2 | `mk_surjective` + `correspondence_mk` + `Subtype.ext` |
| `Pic0.mk_eq_zero_iff` | 12/5 | 7 | `QuotientAddGroup.eq_zero_iff` + `Divisor.mem_principal` |
| `Pic0.zsmul_mk` | 10/3 | 1 | `map_zsmul (QuotientAddGroup.mk' _)` |
| `Pic0.nsmul_mk_eq_zero_of_isPrincipal` | 12/4 | 0 | `nsmul_mk_eq_zero` |
| `Pic0.zsmul_mk_eq_zero_of_isPrincipal` | 13/4 | 10 | `zsmul_mk` + `mk_eq_zero_iff` |
| `Pic0.addOrderOf_mk_dvd_of_isPrincipal` | 11/3 | 9 | `addOrderOf_dvd_of_nsmul_eq_zero` |
| `finiteAlong_comp` | 16/9 | 12 | three `letI`s + `IsScalarTower.of_algebraMap_eq` + `Module.Finite.trans` |
| `finiteAlong_of_surjective` | 11/4 | 6 | `Module.Finite.of_surjective (Algebra.linearMap F F')` |
| `separableAlong_of_charZero` | 12/5 | 84 | `Algebra.IsSeparable.of_integral F F₁` |

Statements verbatim from the wrappers are in §2.1 of the report format; the
load-bearing ones (transcribe these exactly):

```lean
theorem AlgebraicCurve.Place.restrictAlong_restrictAlong
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') :
    (W.restrictAlong χ hχ).restrictAlong φ hφ = W.restrictAlong (χ.comp φ) hχφ

theorem AlgebraicCurve.Place.ramificationIndexAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') :
    Place.ramificationIndexAlong (χ.comp φ) W =
      Place.ramificationIndexAlong χ W * Place.ramificationIndexAlong φ (W.restrictAlong χ hχ)

theorem AlgebraicCurve.Place.inertiaDegAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') :
    W.inertiaDegAlong (χ.comp φ) hχφ =
      W.inertiaDegAlong χ hχ * (W.restrictAlong χ hχ).inertiaDegAlong φ hφ

theorem AlgebraicCurve.Divisor.pushforwardAlong_pushforwardAlong
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F'') :
    Divisor.pushforwardAlong φ hφ (Divisor.pushforwardAlong χ hχ D) =
      Divisor.pushforwardAlong (χ.comp φ) hχφ D

theorem AlgebraicCurve.Divisor.pullbackAlong_pullbackAlong
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    [HasPrincipalDivisors K F'] [HasPrincipalDivisors K F'']
    (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral)
    (hχφ : (χ.comp φ).toRingHom.IsIntegral) (D : Divisor K F) :
    Divisor.pullbackAlong χ hχ (Divisor.pullbackAlong φ hφ D) =
      Divisor.pullbackAlong (χ.comp φ) hχφ D

theorem AlgebraicCurve.separableAlong_of_charZero
    {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁]
    [CharZero F] (φ : F →ₐ[K] F₁) (hφ : φ.toRingHom.IsIntegral) : SeparableAlong K φ

theorem AlgebraicCurve.finiteAlong_of_surjective
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : Function.Surjective φ) : FiniteAlong K φ

theorem AlgebraicCurve.finiteAlong_comp
    {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : FiniteAlong K φ) (hχ : FiniteAlong K χ) : FiniteAlong K (χ.comp φ)
```

`Divisor.correspondence_congr`, `Divisor.correspondence_correspondence` and the five
`Pic0.*` statements are in their wrappers; copy them from there.

## 3. Route notes, so none of this has to be rediscovered

- **`restrictAlong_restrictAlong` is `Place.ext (SetLike.ext fun _ => Iff.rfl)`** —
  no rewriting at all. If it does not close by `rfl`-level `Iff.rfl`, `algebraAlong`
  has stopped being an `abbrev`; that is the topic's canary.
- **`ramificationIndexAlong_comp`** picks an irreducible `π` of
  `(W.restrictAlong (χ.comp φ) hχφ).toValuationSubring`, uses
  `ord_coe_irreducible` to get `ord π = 1`, and compares the two computations of
  `W.ord ((χ.comp φ) f)` via `ord_restrictAlong`, finishing with
  `exact_mod_cast h1.symm.trans h2`.
- **`inertiaDegAlong_comp`** is the residue-field tower proof: three `letI`s, an
  `IsScalarTower v.ResidueField w.ResidueField W.ResidueField` built by
  `IsScalarTower.of_algebraMap_eq` + `IsLocalRing.residue_surjective`, then
  `Module.finrank_mul_finrank` with `mul_comm`.
- **`pushforwardAlong_pushforwardAlong` and `pullbackAlong_pullbackAlong`** are the
  two functorialities the correspondences need; the first is
  `Finsupp.addHom_ext` on `pushforwardAlong_single` with the prelude's
  `restrictAlong_restrictAlong`/`inertiaDegAlong_comp`, the second is `ext W` on
  `pullbackAlong_apply` with `restrictAlong_restrictAlong`/`ramificationIndexAlong_comp`.
- **`Divisor.correspondence_correspondence` has an explicit hypothesis `hex`** (the
  square commutes at the divisor level). It is *not* proved here — T7 produces it.
  Do not try to discharge `hex`.
- **`Pic0.correspondence_correspondence_comm` uses `Pic0.mk_surjective`** (AC0),
  `Pic0.correspondence_mk` (AC0) and `Subtype.ext`; the `hcomm` hypothesis is the
  divisor-level statement.
- **The shared prelude**, to write once in `Transport.lean` (public, in
  `namespace AlgebraicCurve.Place` where the pin so declares it):

```lean
theorem inertiaDegAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ')
    (hφ : φ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = w.inertiaDegAlong φ' hφ' := by subst h; rfl

theorem isIntegral_toAlgHom [Algebra.IsIntegral F F'] :
    (IsScalarTower.toAlgHom K F F').toRingHom.IsIntegral

theorem toAlgHom_comp_toAlgHom :
    (IsScalarTower.toAlgHom K E M).comp (IsScalarTower.toAlgHom K F E) =
      IsScalarTower.toAlgHom K F M

theorem restrict_restrict [Algebra.IsIntegral F E] [Algebra.IsIntegral E M]
    [Algebra.IsIntegral F M] (W : Place K M) : (W.restrict E).restrict F = W.restrict F

theorem Place.ramificationIndex_eq_mul_ramificationIndex_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] (W : Place K M) :
    W.ramificationIndex F = W.ramificationIndex E * (W.restrict E).ramificationIndex F

theorem Place.inertiaDeg_eq_mul_inertiaDeg_restrict
    [Algebra.IsIntegral F E] [Algebra.IsIntegral E M] [Algebra.IsIntegral F M]
    (W : Place K M) : W.inertiaDeg F = W.inertiaDeg E * (W.restrict E).inertiaDeg F
```

  The last two are *specialisations* of this topic's
  `ramificationIndexAlong_comp`/`inertiaDegAlong_comp` at
  `φ := IsScalarTower.toAlgHom K F E`, `χ := IsScalarTower.toAlgHom K E M`, using
  `toAlgHom_comp_toAlgHom` and `isIntegral_toAlgHom`; transcribe the pin's short
  proofs (they are in `S_..._bifiber.lean` lines 40–90, `namespace BifibreDev`).

- **The prelude's section variables.** The pin's helpers take their instances
  explicitly (`{K F E M} [Field …] [Algebra …] [IsScalarTower …]`); keep that shape
  so the checker's textual diff matches. The `Algebra.IsIntegral` hypotheses are
  *not* global instances in `restrict_restrict`.

## 4. What is different about this topic

- **It is the last SET-1 topic and it opens SET 2's dependency.** T5's bifibre proof
  and T6's exchange both begin with the pin's `BifibreDev`/`BifibreW2` prelude; after
  T4 those are imports. The 60-line saving is real but small; the *organizational*
  point is larger: SET 2 reads `Transport.lean`'s prelude instead of re-deriving it.
- **The `rfl` bridges are the shape risk.** The topic is 120 content lines, but four
  of its declarations are `rfl`-level, and a single lost `abbrev`/`reducible`
  attribute turns them into `whnf` blow-ups. Bound every build; if
  `lake env lean` on `Transport.lean` jumps past 60 s, look for an `exact`/`convert`
  against an abstract statement before looking anywhere else.
- **`separableAlong_of_charZero` is disproportionately important** (84 external
  citers, a one-line proof). Give it its own docstring; it is the reason the AC layer
  is usable in characteristic zero without a separability hypothesis at the call
  site.

## 5. Budget and stop-early

**2 goal rounds, checkpoint at 1.** 16 nodes, 120 content lines, one prelude, two
`rfl` canaries. Two is the threshold.

**Stop early, and report rather than restate, on**: a `rfl` bridge that needs
`change`/`simp only [algebraAlong]` (report which attribute was missing); the
`inertiaDegAlong_comp` residue-field tower not synthesizing; or the prelude's
declarations failing the checker with no clean `SOURCES` ordering.

## 6. Definition of done

- [ ] The 16 declarations public in `WeilExchange/Transport.lean`, statements
      verbatim.
- [ ] The 6-declaration shared prelude public in the same module, written once; no
      `BifibreDev`/`BifibreW2`/`BifibreWEX` copies anywhere (T5/T6/T7 import it).
- [ ] Consumer **Zone D** extended: `finiteAlong_comp` + `separableAlong_of_charZero`
      applied to a concrete tower, and a `Pic0` descent check (`mk_eq_zero_iff` or
      `zsmul_mk` composed with a `Divisor` lemma).
- [ ] `spec/check_flt_statements.py`: the 16 AC wrappers in `SOURCES`; the prelude
      matched by last name/dotted fallback or listed in `OWN_PROOFS` with reasons;
      0 mismatched, 0 missing.
- [ ] `timeout 300 lake build` green, 0 warnings, no `sorry`.
- [ ] `logs/ac-port.md` T4 section: cost, the prelude's home and the line saving
      (vs the ≈60+16 estimate), and the `rfl`-bridge record.
- [ ] SET 1 run complete: report the full per-topic table, the checker line and the
      consumer's zone statuses to the reviewer.

## 7. Reporting back

Beyond the shared report: (1) the exact prelude declarations and where the pin's
copies were (three files, three namespaces) with the measured saving; (2) whether
any `rfl` bridge needed help; (3) the `SOURCES`/`OWN_PROOFS` handling of the
prelude — because T7 (the capstone) will import the same prelude and the reviewer
needs the checker to keep verifying it; (4) a one-paragraph **hand-off for SET 2**:
what `Transport.lean`/`PlaceDictionary.lean` expose, and anything the T5/T6 work
orders should assume.
