# Audit — is `phiProd` identified with the coset product?

Read-only audit. Sources:

- FLT clone `~/proj/fermats-last-theorem`, git `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`
  (short `aa2d8b3`, "Lean 4.33.1, Mathlib v4.33.0").
- Port `lean/FLTForHuman/` (in this repo).

**Verdict in one line.** It depends which "coset product", and there are **two**:

- The **analytic coset polynomial** `(X - F(ℓτ)) · ∏_{b<ℓ} (X - F((τ+b)/ℓ))` is an
  *expression*, **not a `def`** (there is no `def cosetPoly` in the pin or the
  port; `cosetPoly_smul` is the name of a *fact* about it). It **is** bridged to
  `phiProd` in the port, through three lemmas — `map_phiProd` →
  `realL_phiProd_coeff` → `hasSum_coeff_of_phiGenDescends`, joined in
  `mem_adjoin_jq_of_phiGenDescends` (`ModularForms/PhiGenDescends.lean:270,277,313,343`).
  In this sense the answer is **yes, we already have it**.
- FLT's **`cosetTwoVarPoly ζ N J`** (`Def_ModularCurve_PrimCosetReps.lean:44`, a
  real `def` over `primCosetReps`, all levels) is **not** bridged to `phiProd`:
  no file in the pin or the port mentions `phiProd` together with
  `primCosetReps`, `cosetConj` or `cosetTwoVarPoly`. Its prime-level
  specialization is literally the same product, but the reindexing is not stated.

`phiProd` and the analytic coset polynomial are therefore **the same polynomial on
the two sides of the `RealL` realization map** — equal coefficient-by-coefficient
through the bridges, not definitionally — while the algebraic `cosetTwoVarPoly`
equality is true and cheap but unstated (§2, §3).

---

## 1. The objects, verbatim

Pin line numbers are against `aa2d8b3`; port line numbers are current.

### 1a. `phiProd` — a real `def`, prime level

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

### 1b. `cosetTwoVarPoly` — a real `def`, all levels

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

### 1c. the analytic "cosetPoly" — an expression, not a `def`

FLT's `cosetPoly_smul` is a statement *about* the expression

```
(X - C (F (heckeDiagMatrix ℓ • τ))) * ∏ b : Fin ℓ, (X - C (F (heckeMatrix ℓ (b : ℕ) • τ)))
```

over `Polynomial ℂ`, a function of `τ`: the product over the `ℓ+1` Hecke coset
representatives of `Y - F(rep • τ)`. It is never named by a `def` —
`grep -rn "def cosetPoly"` is empty in both trees. `cosetPoly` is the name of the
*fact* (`cosetPoly_smul`, `Theorems/Thm_ModularCurve_cosetPoly_smul.lean:5`; port
public at `ModularForms/PhiGenDescends.lean:143`) and of the expression it is
about. The port's private restatements are `cosetPoly_eq_prod_onePoint`
(`:118`) and `cosetPoly_smul'` (`:126`), and the `ℓ+1` family `rep i` it is built
from is at `:225`. This is the object that §4d bridges to `phiProd`.

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

File-level co-occurrence over the **whole pin tree** (`Definitions/`, `Theorems/`,
`P2M/`):

```
comm -12 <(grep -rl phiProd --include=*.lean . | sort) \
         <(grep -rl <KEY>  --include=*.lean . | sort)
```

is **empty** for `KEY` = `cosetTwoVarPoly`, `primCosetReps`, `cosetConj`,
`heckeRep`, `OnePoint`. (The port's `ModularForms/PhiGenDescends.lean` is the one
file that carries both `phiProd` and `heckeRep`, because it imports the shared
`Defs/HeckeRepresentatives` block and keeps the same two-part factoring in one
module.) The same holds for
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

The port therefore cannot state the **algebraic** `cosetTwoVarPoly` equivalence
at all: it has no coset-index vocabulary, and the `ModularPolynomialData`/`X0`
side FLT builds on `primCosetReps` has not been ported. The **analytic** coset
polynomial is a different matter: that bridge is present (§4d).

---

## 4. The nearest things that do exist

| # | statement | FLT (`aa2d8b3`) | port |
|---|---|---|---|
| **a** | `phiProd` vs the TS product at prime `p`: `phiProd p (conj p ζ) = (X - C (TS K (p*p) 1)) * ∏_{b<p} (X - C (TS K 1 (ζ^b)))` | `S_…minpoly_jqN_map_eq_prod_slots.lean:157` (private), roots at `:166` | **public** `Defs/PhiAtSlot.lean:91` (`phiProd_conj_eq`), `:102` (`roots_phiProd_conj`), `:121` (nodup) |
| **b** | general slot product: `(minpoly ℚ⟮jq⟯ (jqN M)).map … = ∏_{a ∣ M} ∏_{b < M/a, gcd} (X - C (qExpand K (a*a) (qTwist (ζ^(b*a)) (coeffEmb K jq))))` | `Thm_…minpoly_jqN_map_eq_prod_slots.lean:8`, body `S_…:1999` | **ported** `FunctionFieldGeneration/SlotProduct.lean:1084` |
| **c** | datum vs coset product: `(data.toJqNField K).map = cosetTwoVarPoly ζ M (jqModC K) ∧ Splits ∧ Separable ∧ rootSet = cosetConj ζ (jqModC K) '' primCosetReps M` | `Thm_…ModularPolynomialData_map_adjoin_jqNModC_eq_cosetTwoVarPoly.lean:9` | **absent** |
| **d** | analytic Hecke-coset product: `HasSum (fun m => (c k).coeff m * qParam 1 τ^m) (((X - j(ℓτ)) * ∏_{b<ℓ} (X - j((τ+b)/ℓ))).coeff k)` under `PhiGenDescends ℓ ζ c` | node `PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff` (`Thm_…:11`; body `S_…:255`) | **the full chain** `map_phiProd :270` → `realL_phiProd_coeff :277` → `hasSum_coeff_of_phiGenDescends :313`, joined in `mem_adjoin_jq_of_phiGenDescends :343` (`ModularForms/PhiGenDescends.lean`) |
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

**The (d) chain, precisely.** `map_phiProd` (`:270`) pushes `phiProd` through
`coeffMap (σ : ℚ(ζ_ℓ) → ℂ)`, yielding `∏ i, (X - C (conjC i))`;
`realL_phiProd_coeff` (`:277`) realizes that product by the coset polynomial in
`jt (rep i • τ)` via `RealL.coeff_prod_X_sub_C`; `hasSum_coeff_of_phiGenDescends`
(`:313`) rewrites the descent hypothesis `hc` into the realization, reduces period
`ℓ` to `1` (`realL_one_of_realL_qExpand`, `:284`), and lands on the
coset-polynomial coefficient; the public join is
`mem_adjoin_jq_of_phiGenDescends` (`:343`). The two halves are **independent and
complementary**: (e) is pure Hecke-representative group theory and never mentions
`phiProd` or a Laurent series, while (d) needs `phiProd` and the `q`-expansion
dictionary and proves no invariance. The equality they establish is
coefficient-by-coefficient *through* the bridges, not definitional.

*Citation caveat.* An earlier report on this topic gives `298 / 425 / 432 / 468 /
498` for `cosetPoly_smul` / `map_phiProd` / `realL_phiProd_coeff` /
`hasSum_coeff_of_phiGenDescends` / `mem_adjoin_jq_of_phiGenDescends`. Those are
the same declarations in port commit `4cd7b06` (`PhiGenDescends.lean` = 509
lines), which inlined the `RealL` block; commit `c7d668b` ("Hecke operators")
removed it (12 insertions, 167 deletions, net −155) and now imports it from
`Hauptmodul.lean:230`. Against the current file (`c7d668b`, 354 lines) the
corresponding anchors are `143 / 270 / 277 / 313 / 343`; every offset is
uniformly `+155`, so the earlier citations map one-to-one.

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

Split by which "coset product":

- **Analytic coset polynomial** (`cosetPoly_smul`'s expression, not a `def`):
  **yes, we already have the bridge.** `map_phiProd` → `realL_phiProd_coeff` →
  `hasSum_coeff_of_phiGenDescends` (port `ModularForms/PhiGenDescends.lean`
  `:270/:277/:313`) says `phiProd` is `qExpand ℓ` of the coset polynomial's
  `q`-expansion — the same polynomial on the two sides of the `RealL` map, equal
  coefficient-by-coefficient, not definitionally. FLT's exported form is the node
  `PhiGen.PhiGenDescends.hasSum_cosetPoly_coeff`. The invariance half
  (`cosetPoly_smul`) and the realization half are independent, glued once in
  `mem_adjoin_jq_of_phiGenDescends`.
- **Algebraic `cosetTwoVarPoly`** (a real FLT `def`, all levels): **no** theorem
  equates it with `phiProd` in either tree, and no file mentions both sides. FLT
  has the one-sided facts: the datum-vs-coset theorem (c) at every level and the
  general slot product (b).
- **Is the algebraic identity true?** Yes, by a reindexing of identical factors;
  the only missing ingredient is the `Fin (p+1) ↔ primCosetReps p` bijection.
  It is not load-bearing (§5.2).
