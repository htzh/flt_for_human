# SET-AF52 — the ord equality from residue surjectivity, and the residue basis

**Status: LANDED (2026-11-12).** Read off the eleven-marker corrected shelf of SET-AF50 §0
(`needed` **699 / 292,705**, ready 47 / 8,883).

**3 rows / 686 silo / ≈660 net in 26 declarations**: two sibling modules closing the chart's residue
dictionary — the ord equality *given* residue surjectivity, and the residue basis with its finiteness
corollary.

| # | row | silo | lev | what it says |
|---|---|---:|---:|---|
| **A1** | `AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective` | 398 | 1/7 | once the residue map is surjective onto the integral closure, `∑ P.ord f = ∑ Q.ord (R.residue f)` — the equality form of Deuring's inequality |
| **B1** | `AlgebraicCurve.RegularProlongation.exists_basis_mem_integers_piResidue_linearIndependent_of_sum_finrank_eq` | 261 | 1/6 | an `A`-generating family has linearly independent joint residues under the degree hypothesis |
| **B2** | `AlgebraicCurve.RegularProlongation.finiteDimensional_adjoin_residue_of_sum_finrank_eq` | 27 | 3/5 | each residue extension is finite-dimensional (the finiteness the residue-span rows consume — and an ingredient of the Kummer family) |

**Premises**: all ported (A1's three are AF48/AF50's rows; B1's is the residue span's rank equality; B2's is
the `sum_finrank_adjoin_residue_le` bound). **Definition gate**: closed (the three `Def_AlgebraicCurve_*`
modules are ported). **Price**: raw 686 / declaration lines ~660, one dispatch, two modules.

**Homes and manager layer** (landed and measured):

| module | lines | decls | `sorry` | `check_port` |
|---|---:|---:|---:|---|
| `AlgebraicCurve/RegularProlongationOrdResidueEquality.lean` | 192 | 13 | 11 | **12 ok / 0 / 0** |
| `AlgebraicCurve/RegularProlongationResidueBasis.lean` | 179 | 13 | 12 | **13 ok / 0 / 0** |

The pin's labels `AJDM` → `OrdResidueEquality` and `E78MVfree` → `ResidueBasis` are rectified; the data
definitions (`Dom`, `Red`, `constHom`, `jointRes`, …) are transcribed and building; all **25 statements**
are verified before a proof.

**Order**: `tmp/af52/WORKORDER-AF52A-ord-equality-and-residue-basis.md` (one dispatch, both modules).

## 2. The landing (2026-11-12)

| module | lines | `sorry` → | `check_port` | build | axioms |
|---|---|---|---:|---|---|
| `RegularProlongationOrdResidueEquality.lean` | 192 → **428** | 11 → 0 | **12 ok / 0 / 0** | 3,881 jobs, 5.2 s | clean |
| `RegularProlongationResidueBasis.lean` | 179 → **326** | 12 → 0 | **13 ok / 0 / 0** | 3,881 jobs, 5.0 s | clean |
| | **371 → 754** | **23 → 0** | **25 ok, 0 mismatch, 0 missing** | | **3/3** |

Both silent at 200,000 heartbeats with zero warnings (and at 25,000; they fail only at 10,000, so the gate
is live and the worst declaration is under 25k — ≥8× margin), no `set_option` beyond `autoImplicit false`,
no silencer, no import added (every cited ported lemma is reachable from the frozen block — the first set
of the recent run where the manager's cone was actually complete). `dedup` 0 clusters / 0 removable lines on
both; `move_dead` 0 dead declarations, and the worker's clean-rebuild evidence shows the log's 41 warnings
are all replayed from other modules. **A1's `integral_case` is the module's mathematical core** (the unique
reduced place, the `TP`/`TQ`/`TP'` fibres, Deuring's bound and the total identity meeting in
`le_antisymm`); `main` is the rescaling argument. `#check` at the wrapper names (three headlines) resolves
each at `AlgebraicCurve.RegularProlongation.*` with the frozen conclusions.

**One deviation is FR-0187's class again**: pin `:46–52` is a `P.ord` argument mixing a `Subtype` coercion
with a raw term, rewritten through `congrArg Subtype.val` rather than unified. The rest are v4.34 renames
and three lines that *consume* auto-included hypotheses instead of `omit`ting them.

**Forecast**: `needed` 699 / 292,705 → **696 / 292,019**; frontier **+686**; `AlgebraicCurve` demand
36 / 12,510 → **33 / 11,824**. Rows readied are measured at the landing (A1's consumers are the two
`ModularCurve` rows of 1,095 and 1,909 silo, which need much more than this set).

**Not this set**: the `EisensteinGeneral.Piece` factorization (890, six `Def_` modules); the adelic-box
pair (129 + 122 — cut from SET-AF53 at scoping because its statement layer needs a further import
investigation); the Kummer root-lifting family (still two sets away).
