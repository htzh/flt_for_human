# The translation layer — what a merged A–B theory has to identify

Scoping note, 2026-10-26. Parent: [../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md)
(§1 the two uniformizations, §9.4 the two Abel theorems, §9.5 what deriving one from the other takes,
§12.2 order-level vs manifold-level dictionaries). Pin `anthropics/fermats-last-theorem@aa2d8b3`.

**Why this note.** The subject's goal is one uniformization. §10.4 says the way to get there is
simplicity — one definition per object. But the two halves do not share their *objects*: A's are cusp
forms on `ℍ`, functionals on them, and an order-faithful series dictionary; B's are Kähler differentials,
places with charts, and coordinate lattices. Deleting a duplicated definition therefore does not merge
them; a **translation layer** does, and its content is a finite, enumerable list of identifications. This
note is that list, with the status of each, plus the one architectural finding from the W3 scouts that
makes it cheaper than §9.5 priced it.

## 1. The two vocabularies

| object | A (modular) | B (Riemann surface) |
|---|---|---|
| the curve | `ℍ / Γ`; function field `xHFunctionField M H` | `Place ℂ F`, `F` arbitrary with `IsCurveOver` |
| the structure | none — series realization, no charts | `[ChartedSpace ℂ (Place ℂ F)] [IsManifold 𝓘(ℂ,ℂ) ω …]`, from B0 |
| the forms | `CuspForm Γ 2` (mathlib) | `Ω[F⁄ℂ]`, `readDifferential v ω` per chart |
| the integral | `periodAlongOf Γ τ₀ τ₁ f`, an explicit interval integral in `ℍ` | `pathIntegral ω γ`, a choice over `IsPrimitiveAlong` |
| the periods | `periodOf Γ γ f = periodAlongOf Γ I (γ • I) f` | `abelJacobiVec b P₀ v` against a basis of `regularDifferentials` |
| the lattice | `periodLatticeOf Γ : Submodule ℤ (Dual ℂ (CuspForm Γ 2))` — basis-free | `pathPeriodLattice b : Submodule ℤ (Fin n → ℂ)` — coordinates |
| the AJ map | `abelFibreSumOf` (upstairs `c : ℍ →₀ ℤ`, pushed down) | `abelJacobiDiv` (downstairs `Divisor ℂ F`) |
| extra structure | Hecke `T/U`, diamond, Tate, `parabolicHoms` | **none** (§9.1: no Hecke action on any lattice) |

## 2. The seven identifications a merged theory needs

| # | identification | device | status |
|---|---|---|---|
| 1 | the curve/field | A's field `xHFunctionField M H` is a curve: `IsCurveOver` + transcendental generator | **have** |
| 2 | the complex structure on `Place ℂ F` | B0's chart construction, **generic in `F`**: `chart v w = evalAt w (t v)`, `t v` a local parameter | pin: 482 + 369 lines, unported — but it is B's, and generic, so it covers A's field with no second copy |
| 3 | cusp forms ↔ differentials | `CuspForm Γ 2 ≃ regularDifferentials(X_Γ)`, ℂ-linearly | pin at **Γ₀(N) only** (`exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm`, 323); **Γ_H to write** |
| 4 | geodesics ↔ paths | `pt` of the geodesic from `I` to `τ`, closed by `pt_smul` | in A's dictionary (`ComplexPlaceDictionary{,Of}`, unported) |
| 5 | the integrals | A's explicit interval integral = the primitive difference of the image form | **the gate** (§9.5 item 3) — see §3 |
| 6 | the lattices | `periodLatticeOf Γ` = the image of `pathPeriodLattice` under 3 + a basis | §9.5: A ⊆ B free, B ⊆ A ≈4k (spanning) |
| 7 | the divisors | `Finsupp.mapDomain D.pt c` + ramification weights; `Place.deg_eq_one_of_isAlgClosed` (13, **ported**) | in A's `pt`; the weight/degree bookkeeping is A's |

Fields 1, 2, 4, 7 are **ports**; 3 and 5 are the **work**; 6 is a **rewire**.

## 3. The finding: translate pointwise, not globally

§9.5 priced field 5 as "the integral identification — the gate with no node in the pin", and the W3
scouts ([PLAN-W3-honest-integral.md](PLAN-W3-honest-integral.md) §4c) found that the *global* version of
it is expensive: a chart-invariant honest integral on a charted surface needs a chart-change law for
`readDifferential`, and that law is a Kähler dictionary absent from both the pin and the port.

**It is not needed.** A's integral is *explicitly parametrized* in `ℍ`; B's is a primitive difference, and
both notions are chart-free. So the translation never compares two chart expressions of one form. What it
needs is the **pointwise derivative dictionary**:

  `readDifferential (pt τ) ω` at the charted image of `pt τ` `= f τ · (the derivative of τ ↦ pt τ)`,

i.e. *the form's chart reading at the image point is the cusp form times the map's Jacobian*. That is the
order-level dictionary A already has (`meromorphicOrderAt_realizeOf`: the `q`-expansion realization is
order-faithful), differentiated once — one point at a time, no charts compared, no cocycle.

Two consequences, and they are the reason this note exists:

* **The merged theory does not require the honest-integral question to be settled.** Fields 3 and 5 use
  `IsPrimitiveAlong` (local primitives at the moving point), which is exactly the notion both sides
  already have. The landed W3 modules are a *supplement* — the natural home of the derivative facts on B's
  side — not the translator.
* **Field 3 and field 5 are two faces of one lemma.** "The cusp form `f` is the differential `ω` read at
  `pt τ` up to the Jacobian" *is* both the value-level identification and the derivative-level one; a port
  that writes one without the other will write it twice.

## 4. The asymmetry, and the shape it forces

Three asymmetries decide the architecture; none of them is symmetric and none should be forced to be.

1. **Extra structure is A's.** Hecke, diamond, Tate, `parabolicHoms` live only on A's side (§9.1). A merged
   theory is therefore a neutral uniformization interface **plus A's refinements layered on top** — never B
   carrying Hecke, which §9.1 already refuted.
2. **The charted structure is B's, and it is generic.** B0's construction is uniform in `F`, so A's curve
   gets its charts from B, once. That is the merged theory's single complex structure, not a second one.
3. **The lattice is A's; B's is a presentation.** §10.4 item 2: `periodLatticeOf` (basis-free) survives,
   `pathPeriodLattice` (coordinates) is what a computed lattice is *used* through. Merging keeps one
   lattice with two coordinate systems, not two lattices.

So the merged statement is a **quotient with two coordinate systems**: one `(Fin g → ℂ) ⧸ L` under field 3,
with `L` simultaneously the periods of a basis of holomorphic differentials and `periodLatticeOf Γ` — and
one uniformization map, Hecke-equivariant because A's action transports.

## 5. How to land it before both instances exist

The playbook's conditional-capstone device (§2.3), which the parent's P4 already sketches for the two
mouths separately, applies cleanly here *at the level of the translation layer*:

* a structure `TranslationData` whose fields are exactly 2–5 of §2 (charted structure, the
  cusp-form ↔ differential equivalence, the geodesic map, the pointwise derivative identity), plus a basis
  for 6;
* the merged uniformization statement proved **from** it, axiom-free;
* then two instances, filled independently: B's general curve (field 2 from B0, field 3 from `Ω`) and A's
  `Γ_H` (field 3 written, field 4 from `pt`).

The virtue is that the *list* becomes the interface: an instance is fillable by whichever half proves a
field first, the two instances need never be compared, and the merged theory is the structure plus one
derivation rather than two developments plus a bridge.

## 6. What this says to the wave plan

* The merged theory does **not** wait on the honest-integral decision (§4b/§4c of the W3 plan), and it does
  not need the chart-change cocycle.
* Its own first work is **fields 3 + 5 at `Γ_H`** — the differential dictionary — because that is the one
  item that is (a) missing everywhere, (b) needed by both instances, and (c) the same work on two faces.
* Fields 1, 2, 4, 7 are ordinary ports (2 is B0's 851 lines; 4 and 7 are inside A's 16.9k dictionary);
  field 6 is the ≈4k spanning half of §9.5 and should be taken as a rewire, not as a development.

## 7. What the combined theory is, mathematically

Fix the setting: `X` a smooth projective curve over `ℂ` of genus `g`, `V = H⁰(X, Ω¹)` (a `g`-dimensional
`ℂ`-space), `V*` its dual. Both halves prove the same classical statement at two levels of structure:

* **B** chooses a basis `ω₁ … ω_g` of `V`, forms the period vectors `(∫_γ ω_i)_i ∈ ℂ^g` over loops `γ`,
  and concludes `Pic⁰(X) ≅+ ℂ^g ⧸ L`, `L` the `ℤ`-span of those vectors.
* **A** at `X = X_Γ` identifies `V ≅ S₂(Γ)` (`CuspForm Γ 2`), writes `L = periodLatticeOf Γ ⊂ (S₂)*`
  basis-free, and concludes `Pic⁰(X) ≅+ (S₂)* ⧸ L` — with Hecke acting on everything.

So the combined theorem is one statement, for a curve equipped with a form space and an identification of
it with the holomorphic differentials:

> **(C)** there is a free `ℤ`-lattice `L ⊂ V*` of rank `2g`, discrete, with
> `Pic⁰(X) ≅+ V* ⧸ L`,

plus three derived clauses that are *clauses of the same theorem*, not of a second one:

| clause | content | comes from |
|---|---|---|
| **C1** | `L` is free of rank `2g` and discrete (hence `V*/L` is a complex torus) | the period pairing is nondegenerate: the basis theorem, A's 267 / B's mouth's `finrank ℤ L = 2g` |
| **C2** | `#(Pic⁰[n]) = n^{2g}` | **pure lattice algebra**: `Pic⁰[n] = (1/n)L ⧸ L ≅ (ℤ/n)^{2g}` — no Frobenius, no `isAlgebraic` |
| **C3** | modular case only: Hecke `T/U`, diamond act on `V`, hence on `V*/L`, and `T_p(Pic⁰) ≅ ℤ_p ⊗ L` Hecke-equivariantly | A's layer, layered on top |

B's mouth is **(C)** with `V = H⁰(Ω¹)` and a chosen basis (coordinates on `V*`); A's mouth is **(C)** with
`V = S₂(Γ)`, basis-free, plus **C3**. The *only* mathematics that exists in neither half separately is the
identification `V ≅ H⁰(X, Ω¹)` at `Γ_H` together with the pointwise derivative dictionary of §3 — the
rest of "combining" is re-reading one statement in two coordinate systems.

Two consequences are worth stating because they are what the combination is *for*:

* **C1 and C2 become local.** In the separated development the rank is *borrowed*: A's
  `finrank_periodLattice_eq_two_mul_genusFF` (80) takes a premise from each side, pairing A's torus
  cardinality with the *algebraic* count (`natCard_torsion_prime_eq_pow_two_mul_genusFF_of_forall_pow_eq_self`,
  144) — parent §9.2's coupling. In (C) both facts are consequences of `L`'s own freeness, discreteness and
  rank, so the coupling disappears and the algebraic count is no longer on the path.
* **The uniformization is the same theorem**, so the D-S column's reading of the two routes (A's 653
  versus B's 327) stops being a choice between two developments and becomes a choice of *presentation*.

## 8. Consumer demands, and which clause meets each

| consumer | what it needs | met by | status |
|---|---|---|---|
| `CuspForm.exists_padicGaloisModule_heckeRingH_two_frobenius_relation` (859, the D-S column) | A's (C) at `Γ_H` + Hecke + the Tate identification | **C3** on (C) | the one node that needs both halves today; under (C) it needs one theorem and its modular clause |
| `ModularCurve.finite_torsion_jOne` (80) | `Finite (Pic0.torsion … n)` | **C1+C2**: finite index ⇒ finite torsion | already A-only; (C) gives it from the lattice alone |
| `ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH` (327) | `Module.Finite ∧ Module.Free (TateModule …)` | **C1+C3**, or B's hub via C2 | today it reaches B's hub; under (C) it reaches C1 |
| `AlgebraicCurve.Pic0.abelJacobiCard_genus` (113, **fan-in 12**) | `#(Pic⁰.torsion n) = n^{2g}` | **C2** | the biggest arithmetic hub in the subject, and (C) proves it by lattice algebra instead of by the analytic+Frobenius route — the clearest cost win |
| `DrinfeldCurve.abelJacobiCard_drinfeldFunctionField` (288) | the same cardinality for another curve | **C2** at that curve's instance | served by the general (B-shaped) instance of (C) |
| the char-`p` / `q`-expansion column (`abelJacobiCard_genusFF_qExpFunctionFieldC`, 478) | the cardinality for a `q`-expansion function field over an algebraically closed field of any characteristic | **not served** — (C) is analytic over `ℂ` | a real limitation: this consumer keeps the algebraic route, and that route must be ported for it |
| A's own Hecke/Tate column (390, 705, 650, 634) | `V*/L` with Hecke, the char-poly comparison | **C3** | unchanged in scope; only its foundation is now (C) rather than a separate development |

## 9. Assessment — clarity first, cost second, and the cost reduction is modest

**Clarity: a real gain, and it is the main argument.**

1. **One theorem instead of two.** `Pic⁰ ≅ V*/L` with clauses C1–C3 replaces A's mouth, B's mouth, and the
   pair's proof. The subject currently needs an argument (§1, §9.3, §10.3) *that the two are separate
   projects*; under (C) that argument becomes a remark about presentations.
2. **The arithmetic becomes lattice algebra.** C2 is three lines of group theory
   (`(1/n)L/L ≅ (ℤ/n)^{2g}`) where the pin has a route through Frobenius/`isAlgebraic`. This is the one
   place where the combination is *conceptually* cheaper, not just tidier, because it removes a
   cross-foundation dependency rather than relocating it.
3. **The two-route rank coupling dies** (§7, C1), which is parent §9.2's only node that takes a premise
   from each side.
4. **The A-vs-B question stops being load-bearing.** The D-S prune's substitution (A's 653 for B's 327) and
   §9.1's "could B carry A" both presuppose two developments; under (C) they are the same statement with
   different `V`.

**Cost: ≈3k of 74k, about 4%, so this is not a way to make the port smaller — it is a way to make it one
theory.**

*Spend:* the cusp-form ↔ differential identification at `Γ_H` plus the pointwise derivative dictionary —
the only piece in neither half. The pin has the identification at `Γ₀(N)` in 323 lines
(`exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm`); `Γ_H` needs its own, and the dictionary is
new. Estimate **≈500–750 written**, and it is the one item that must exist before either instance is
filled.
*Save:* A's row-2 reciprocity (≈4,025, parent §10.4 item 3) becomes instantiations of B's general form —
≈300–600 of instantiation lemmas, so ≈3,400 net; plus the borrowed-rank route (80 + 144 and the coupling)
is replaced by C1.
*Not saved:* parent §10.4 item 1's ≈8,869. That rewrite needed to replace `pathIntegral`, and the cocycle
scout killed it (§4c of the W3 plan). The combined theory neither needs nor produces that saving — which is
also why it is *robust*: it rests on the pointwise dictionary (§3), not on the unbounded chart-change law.
*Risk:* (C) front-loads the one missing mathematical item, and it is not a transcription — the only such
item on the whole plan. The conditional-capstone route (§5) is what makes that safe: the structure is
written first, the merged statement proved from it axiom-free, and the two instances filled when their
fields land.

**Verdict.** Worth doing, for coherence and for C2's cross-foundation removal, not for line count. On the
numbers it is roughly break-even-to-+3.4k on a 74k programme; on structure it turns "two uniformizations
with a translation layer" into "one uniformization with a modular clause", which is what the subject was
for.
