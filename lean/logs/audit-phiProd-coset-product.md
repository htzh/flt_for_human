# Audit — is `phiProd` identified with the coset product?

Read-only audit. Sources:

- FLT clone `/home/haitao/proj/fermats-last-theorem`, git `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`
  (short `aa2d8b3`, "Lean 4.33.1, Mathlib v4.33.0").
- Port `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean/FLTForHuman/`.

**Verdict in one line.** **No.** Neither the pin nor the port states
`phiProd ℓ (conj ℓ ζ) = cosetTwoVarPoly ζ ℓ (coeffEmb K jq)` (or the analogous
`= minpoly_jqN_map_eq_prod_slots` slot product), and no FLT file even mentions
`phiProd` together with `primCosetReps`, `cosetConj` or `cosetTwoVarPoly`: the
two are **parallel, mutually-ignorant constructions of the same product**. The
identity is nonetheless *true* and cheap — it is a reindexing of literally equal
factors — and the port already carries all but one of its ingredients.

---

## 1. The two objects, verbatim

Pin line numbers are against `aa2d8b3`; port line numbers are current.

### 1a. The `PhiGen` side (prime level)

`Definitions/Def_ModularCurve_PhiGen.lean` = port `ModularCurve/Defs/PhiGen.lean`:

| declaration | FLT | port |
|---|---|---|
| `cosetSubst ζ a b = (qExpand K (a*a)).comp (qTwist (ζ ^ (a*b)))` | `:111` | `:49` |
| `cosetA ℓ i = if i = 0 then ℓ else 1` | `:204` | `:170` |
| `cosetB ℓ i = if i = 0 then 0 else i - 1` | `:206` | `:173` |
| `conj ℓ ζ i = cosetSubst ζ (cosetA ℓ i) (cosetB ℓ i) (coeffEmb K jq)` | `:237` | `:206` |
| `phiProd ℓ conj = ∏ i : Fin (ℓ+1), (X - C (conj i))` | `:257` | `:228` |
| `PhiGenDescends ℓ ζ c := ∀ k, (phiProd ℓ (conj ℓ ζ)).coeff k = coeffEmb K (qExpand ℚ ℓ (c k))` | `:302` | `:480` |

with the two evaluation lemmas `conj_zero : conj ℓ ζ 0 = qExpand K (ℓ*ℓ) (coeffEmb K jq)`
and `conj_succ b : conj ℓ ζ b.succ = qTwist (ζ ^ b) (coeffEmb K jq)`.
Note `conj` needs `[Fact ℓ.Prime]` and `[Algebra ℚ K]`; it does **not** need `ζ`
to be primitive.

### 1b. The coset side (all levels)

`Definitions/Def_ModularCurve_PrimCosetReps.lean` (no port counterpart):

```
def primCosetReps (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.filter (fun t => t.1 * t.2.2 = N ∧ t.2.1 < t.2.2 ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1)
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1) ×ˢ Finset.range (N + 1))          -- :8

theorem mem_primCosetReps (hN : N ≠ 0) :
    (a, b, d) ∈ primCosetReps N ↔ a * d = N ∧ b < d ∧ Nat.gcd a (Nat.gcd b d) = 1    -- :13

noncomputable def cosetConj (ζ : Kˣ) (J : LaurentSeries K) (t : ℕ × ℕ × ℕ) :=
  if h : t.1 = 0 then 0 else cosetSubst ζ t.1 t.2.1 J                                  -- :34

theorem cosetConj_eq (a b d) [NeZero a] : cosetConj ζ J (a, b, d) = cosetSubst ζ a b J -- :39

noncomputable def cosetTwoVarPoly (ζ : Kˣ) (N : ℕ) (J : LaurentSeries K) :=
  (primCosetReps N).prod fun t => Polynomial.X - Polynomial.C (cosetConj ζ J t)       -- :44
```

Because `cosetSubst` is shared, both sides build their factors from the same
three operations.

---

## 2. The candidate identity is true, and why

At a prime `ℓ`, `mem_primCosetReps (NeZero.ne ℓ)` gives

```
primCosetReps ℓ = { (ℓ, 0, 1) } ∪ { (1, b, ℓ) | b < ℓ },
```

that is, exactly `ℓ + 1` triples. The map
`i ↦ (cosetA ℓ i, cosetB ℓ i, if i = 0 then 1 else ℓ)` is a bijection
`Fin (ℓ+1) ≃ primCosetReps ℓ`, and on it the factors agree **definitionally up to
`conj_zero`/`conj_succ` and `cosetConj_eq`**:

```
cosetConj ζ (coeffEmb K jq) (ℓ, 0, 1) = cosetSubst ζ ℓ 0 (coeffEmb K jq)
                                      = qExpand K (ℓ*ℓ) (coeffEmb K jq) = conj ℓ ζ 0
cosetConj ζ (coeffEmb K jq) (1, b, ℓ) = cosetSubst ζ 1 b (coeffEmb K jq)
                                      = qExpand K 1 (qTwist (ζ^b) (coeffEmb K jq))
                                      = qTwist (ζ^b) (coeffEmb K jq)    = conj ℓ ζ b.succ
```

(`qExpand K 1` is the identity and `1 * 1 = 1`; the `[NeZero 1]` instance is
the only friction.) So

$$
\Phi_\ell \\;=\\; \prod_{i : \mathrm{Fin}(\ell+1)} (Y - \mathrm{conj}_i)
\\;=\\; \prod_{t \in \mathrm{primCosetReps}\\,\ell} (Y - \mathrm{cosetConj}\\,t)
\\;=\\; \mathrm{cosetTwoVarPoly}\\,\zeta\\,\ell\\,(\mathrm{coeffEmb}\\,jq)
$$

is a `Finset.prod_bij`/`Fintype.prod_equiv` reindexing. No analysis, no
Galois theory, no primitivity of `ζ`.

The identity is corroborated by the cone's own descent shape: `PhiGenDescends`
feeds `coeffEmb K (qExpand ℚ ℓ (c k))` into `phiProd`'s coefficient, which is
what makes `phiProd` the *period-`ℓ`* evaluation `Φ_ℓ(j(q^ℓ), Y)` — the same
object the coset route produces (`§4c`).

---

## 3. The search: no statement mentions both

File-level co-occurrence over FLT `Definitions/` and `Theorems/`:

```
comm -12 <(grep -rl phiProd  --include=*.lean Definitions/ Theorems/ | sort) \
         <(grep -rl <KEY>   --include=*.lean Definitions/ Theorems/ | sort)
```

is **empty** for `KEY` = `cosetTwoVarPoly`, `primCosetReps`, `cosetConj`,
`heckeRep`, `OnePoint`. The same holds for
`P2M/Sol/S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` (the general slot
product) versus the whole `cosetTwoVarPoly` family: **no file in the pin
mentions both**, so even the two *general* coset products are never bridged to
each other.

Port counts (`grep -rn` over `lean/FLTForHuman`):

| name | occurrences |
|---|---|
| `toJqNField` | 0 |
| `jqNField` | 0 |
| `primCosetReps` | 0 |
| `cosetConj` | 0 |
| `cosetTwoVarPoly` | 0 |

The port therefore cannot state the equivalence at all: it has no coset-index
vocabulary. The `ModularPolynomialData`/`X0` side that FLT builds on
`primCosetReps` has not been ported.

---

## 4. The nearest things that do exist

| # | statement | FLT (`aa2d8b3`) | port |
|---|---|---|---|
| **a** | `phiProd` vs the TS product at prime `p`: `phiProd p (conj p ζ) = (X - C (TS K (p*p) 1)) * ∏_{b<p} (X - C (TS K 1 (ζ^b)))` | `S_…minpoly_jqN_map_eq_prod_slots.lean:157` (private), roots at `:166` | **public** `Defs/PhiAtSlot.lean:91` (`phiProd_conj_eq`), `:102` (`roots_phiProd_conj`), `:121` (nodup) |
| **b** | general slot product: `(minpoly ℚ⟮jq⟯ (jqN M)).map … = ∏_{a ∣ M} ∏_{b < M/a, gcd} (X - C (qExpand K (a*a) (qTwist (ζ^(b*a)) (coeffEmb K jq))))` | `Thm_…minpoly_jqN_map_eq_prod_slots.lean:8`, body `S_…:1999` | **ported** `FunctionFieldGeneration/SlotProduct.lean:1084` |
| **c** | datum vs coset product: `(data.toJqNField K).map = cosetTwoVarPoly ζ M (jqModC K) ∧ Splits ∧ Separable ∧ rootSet = cosetConj ζ (jqModC K) '' primCosetReps M` | `Thm_…ModularPolynomialData_map_adjoin_jqNModC_eq_cosetTwoVarPoly.lean:9` | **absent** |
| **d** | analytic Hecke-coset product: `HasSum (fun m => (c k).coeff m * qParam 1 τ^m) (((X - j(ℓτ)) * ∏_{b<ℓ} (X - j((τ+b)/ℓ))).coeff k)` under `PhiGenDescends ℓ ζ c` | node `PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff` (`Thm_…:11`; body `S_…:255`) | `ModularForms/PhiGenDescends.lean:313` (`hasSum_coeff_of_phiGenDescends`, private), over `:277` (`realL_phiProd_coeff`, private) |
| **e** | invariance / reindex of the analytic coset polynomial `(X - F(ℓτ)) * ∏_{b<ℓ} (X - F((τ+b)/ℓ))` | `S_…cosetPoly_smul.lean:214` (`cosetPoly_eq_prod_onePoint`), `:222` (`cosetPoly_smul'`) | public `ModularForms/PhiGenDescends.lean:143` (`cosetPoly_smul`); the two helpers are private `:118`/`:126` |

Reading the table:

- **(a) is the closest algebraic near-miss.** Its right-hand side is the *same
  `p+1` factors* as `cosetTwoVarPoly ζ p (coeffEmb K jq)`, written with `TS` and
  `Finset.range p` instead of `primCosetReps`/`cosetConj`. A bridge theorem would
  sit immediately on top of it (reindex + `cosetConj_eq`), and would not need to
  re-prove any algebra.
- **(c) is the only FLT theorem that literally equates a modular polynomial with
  `cosetTwoVarPoly`.** It is stated for `data.toJqNField` (any
  `ModularPolynomialData M`), not for `phiProd`. `toJqNField` is
  `Φ.map (X ↦ jqN)` (`Def_ModularCurve_ModularEquationQ.lean:33`), so (c) is the
  coset factorisation of the *sibling* product; it never mentions `phiProd`.
- **(b)** is the general coset product in divisor-index form. It is the port's
  only existing "coset product", and it is disjoint from (c) even in FLT (§3).
- **(d)/(e)** are the analytic face of the same equivalence: they *realize*
  `phiProd`'s coefficients (mapped to `ℂ`, at period `ℓ`) by the analytic Hecke
  coset polynomial. This is the sense in which the port already "has the
  equivalence" — but only privately, and only as a `HasSum` statement, never as a
  polynomial identity, and never against the algebraic `cosetTwoVarPoly`.

**How (c) and the cone agree without a bridge.** FLT's `eq_of_prime`
(`ModularPolynomialData.eq_of_prime`, port `ModularPolynomialUniqueness.lean:115`)
makes all prime-level `ModularPolynomialData ℓ` equal, and the cone's
`exists_modularPolynomialData_coeff_eq` (`ModularPolynomialAssembly.lean:137`)
builds the datum with `evalAtJ (data.Φ.coeff k) = c k` from the same `c` that
`PhiGenDescends` consumes. So the two constructions are provably the same object
*through the datum*, but the identification is implicit: to extract
`phiProd = cosetTwoVarPoly` from it one would still have to unfold `toJqNField`.

---

## 5. What a bridge would cost

A faithful, minimal bridge is one new declaration, roughly:

```
theorem phiProd_eq_cosetTwoVarPoly (p : ℕ) [Fact p.Prime] (ζ : Kˣ) :
    phiProd p (conj p ζ) = cosetTwoVarPoly ζ p (coeffEmb K jq)
```

Its proof is the `Fin (p+1) ≃ primCosetReps p` reindexing of §2 (a
`Finset.prod_bij'` over `primCosetReps` with `mem_primCosetReps` plus
`conj_zero`/`conj_succ`/`cosetConj_eq`), i.e. a `phiProd_conj_eq`-length proof
(≈25–40 lines) plus whatever index-bookkeeping the `Finset.filter`/`range`
normal form demands. It is **not** blocked on anything: all ingredients are
public in the port except the definitions `primCosetReps`/`cosetConj`/
`cosetTwoVarPoly` themselves, which would have to be ported first (a verbatim
`Def_ModularCurve_PrimCosetReps.lean`, 49 lines, plus `mem_primCosetReps`'s
`omega`/`Nat` proof).

Two cautions:

1. **Naming/route risk.** `cosetTwoVarPoly` is general-`N` and only its
   `ℚ`-algebra form is wanted here; porting the definition drags in the
   `ModularPolynomialData`/`X0` vocabulary the port has deliberately not taken
   (no `jqNField`, no `toJqNField`). A cheaper option is to state the bridge
   against the *slot* product (b) — the port already has it publicly — or to
   keep the `TS`/`Finset.range` form (a) and merely record that it is the coset
   product.
2. **The equivalence is not load-bearing.** Everything the cone needs already
   flows through `PhiGenDescends` + (d). The bridge would be documentation
   (making the "two constructions are the same" explicit and letting the
   `cosetTwoVarPoly` route's uniqueness result `eq_cosetTwoVarPoly_of_forall_isRoot`
   be quoted at prime level), not a premise of any current proof. Per
   `PORTING-PhiGen.md` §6's standing rule, count the affected nodes before
   committing if it is ever wanted.

---

## 6. Answer to the research question

- **Does FLT have the equivalence `phiProd` = coset product?** No theorem,
  and no statement that mentions both sides. It has the *one-sided* facts: the
  datum-vs-coset theorem (c) at every level, the general slot product (b), and
  the analytic realization (d)/(e).
- **Does the port have it?** No — the port has (a), (b), (d), (e) but none of
  the `primCosetReps` vocabulary, so the algebraic equivalence is not even
  statable; the analytic equivalence is present only as private lemmas
  `realL_phiProd_coeff` and `hasSum_coeff_of_phiGenDescends`.
- **Is it true?** Yes, by a reindexing of identical factors; the only missing
  ingredient is the `Fin (p+1) ↔ primCosetReps p` bijection.
