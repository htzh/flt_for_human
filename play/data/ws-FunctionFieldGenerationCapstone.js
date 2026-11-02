window.PLAY_WORKSHEETS = window.PLAY_WORKSHEETS || {};
window.PLAY_WORKSHEETS["FunctionFieldGenerationCapstone"] = {
  "slug": "FunctionFieldGenerationCapstone",
  "file": "lean/presentation/FunctionFieldGenerationCapstone.lean",
  "title": "the function-field generation capstone",
  "tagline": "the unconditional theorem, and the four statements the rest of FLT consumes",
  "subject": "Function field generation for X₀(N) — the unconditional capstone",
  "intro": "The capstone of the function-field-generation segment, presented mathematics-first. Every definition and statement here is Lean, and is exhibited by `#check` or `#print`; every proof body is a semi-formal argument: what is to be proved, what each hypothesis supplies, and which proven theorem or earlier step meets each premise. Narratives live in comments. The source of this sheet is presentation/function-field-generation/capstone.json.",
  "reads": "the port module FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean and its dependencies (Spine, Descent, DegreeStep, Nonmembership, Generation, SlotProduct); math/010-function-field-generation.md is the mathematical account",
  "pin": "FLT anthropics/fermats-last-theorem@aa2d8b3 — Theorems/Thm_ModularCurve_functionFieldGeneration.lean line 8, and the S_ModularCurve_functionFieldGeneration.lean assembly (lines 614–700)",
  "check": "cd lean && lake env lean presentation/FunctionFieldGenerationCapstone.lean",
  "status": "generated — do not edit; edit presentation/function-field-generation/capstone.json",
  "date": "2026-11-01",
  "imports": ["FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone"],
  "opens": ["Polynomial","HahnSeries","IntermediateField","ModularCurve"],
  "namespace": null,
  "zones": [{"id":"A","title":"the statement, in mathematical form"},{"id":"B","title":"the strong induction and its seven inputs"},{"id":"C","title":"the capstone and its corollary layer"},{"id":"D","title":"integrality — the monic annihilator"},{"id":"E","title":"from the degree count to an irreducible datum"},{"id":"F","title":"references — the proven statements cited"},{"id":"G","title":"formalization notes — the Lean detours"}],
  "blocks": [
    {
      "type": "code",
      "text": "import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone",
      "zone": null
    },
    {
      "type": "code",
      "text": "set_option autoImplicit false",
      "zone": null
    },
    {
      "type": "code",
      "text": "noncomputable section",
      "zone": null
    },
    {
      "type": "code",
      "text": "open Polynomial HahnSeries IntermediateField ModularCurve",
      "zone": null
    },
    {
      "type": "code",
      "text": "open scoped IntermediateField",
      "zone": null
    },
    {
      "type": "prose",
      "md": "\n  ## Conventions\n\n  The notation shared by every proof below.\n\n    - **ℚ((q))** — The field of Laurent series over ℚ. It is the single ambient field in which\n      every function of the theorem lives; there is no upper half-plane and no analytic\n      continuation anywhere. Lean: `LaurentSeries ℚ`.\n\n    - **j(q)** — The classical j-invariant, as the explicit Laurent series q⁻¹ + 744 + 196884\n      q + ⋯ ∈ ℚ((q)). Lean: `ModularCurve.jq`.\n\n    - **j(q^N)** — The nome substitution q ↦ q^N applied to j(q): every exponent is multiplied\n      by N. In Lean this is qExpand ℚ N jq, abbreviated jqN N. Lean: `ModularCurve.jqN`.\n\n    - **F_N** — The two-generator field ℚ(j(q), j(q^N)) ⊂ ℚ((q)). Lean:\n      `ModularCurve.modularFunctionField`.\n\n    - **F_N^full** — The full divisor field ℚ(j(q^d) : d ∣ N) ⊂ ℚ((q)). This is the field the\n      formalization takes as the function field of X₀(N). Lean:\n      `ModularCurve.modularFunctionFieldFull`.\n\n    - **ψ(N)** — The Dedekind psi function Σ_{d ∣ N, d squarefree} N/d = N ∏_{p ∣ N}(1 + 1/p):\n      the index [SL₂(ℤ) : Γ₀(N)], hence the degree of the cover X₀(N) → X(1) and the Y-degree\n      of the modular equation Φ_N. Lean: `ModularCurve.dedekindPsi`.\n\n    - **Φ_N** — The modular polynomial: Φ_N ∈ ℤ[j][Y], monic in Y, of Y-degree ψ(N), vanishing\n      at (X, Y) = (j(q), j(q^N)). Lean packages it with its three facts as\n      ModularPolynomialData N. Lean: `ModularCurve.ModularPolynomialData`.\n\n    - **[L : K]** — The relative degree of a field extension K ⊆ L, with K the base field. In\n      Lean: IntermediateField.relfinrank K L, or Module.finrank K L for a simple extension.\n      Lean: `IntermediateField.relfinrank`.\n\n    - **integral over ℤ[j]** — x is integral over ℤ[j(q)] when there is a monic P ∈ ℤ[j(q)][Y]\n      with P(x) = 0. This is exactly the existence of a monic annihilator, which is what\n      Lean's IsIntegral unpacks to. Lean: `IsIntegral`.\n\n    - **Tight, Gen, Hall** — Tight d: [ℚ(j)(j(q^d)) : ℚ(j)] = ψ(d). Gen d: F_d = F_d^full.\n      Hall N: for every d ∣ N, both Tight d and Gen d. Lean:\n      `ModularCurve.Tight, ModularCurve.Gen, ModularCurve.Hall`.\n\n    - **j(u q^e)** — The composed substitution q ↦ u q^e, for a unit u in a coefficient field\n      K: qExpand K e (qTwist u (coeffEmb K j(q))). It is the nome form of the affine map τ ↦\n      eτ + (const) and is named TS K e u in the port. Lean:\n      `ModularCurve.qExpand, ModularCurve.qTwist, ModularCurve.coeffEmb`.\n",
      "zone": null
    },
    {
      "type": "prose",
      "md": "  F_N, F_N^full, and the collapse\n\n  The theorem is classical: over ℚ, the function field of X₀(N) is generated by the two\n  functions j(q) and j(q^N). The formalization has no Riemann surface; it builds X₀(N) from the\n  divisor field F_N^full, so the theorem is the collapse F_N^full = F_N.\n\n  Two numbers govern the proof. ψ(N) is the degree of the cover X₀(N) → X(1) and the Y-degree of\n  the modular equation Φ_N. The other is the relative degree [ℚ(j)(j(q^N)) : ℚ(j)], which the\n  theorem proves equals ψ(N). Generation and degree are proved together, by one strong induction\n  over the divisor lattice; this presentation starts from the end of that induction (the\n  assembly in Capstone.lean) and then reads the two input-supplying theorems that are proved\n  inside the file.\n\n  Everything lives in the single field ℚ((q)) of Laurent series. The substitutions are ring\n  endomorphisms — q ↦ q^N and q ↦ u q^e — not analytic maps, and no analytic continuation is\n  used anywhere.\n",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": "\n  ### `qExpand` — the q ↦ q^N substitution\n\n  **Lean.** `ModularCurve.qExpand` (def)\n\n  The substitution q ↦ q^N on Laurent series: a monomial q^k becomes q^{Nk}, coefficients\n  unchanged. It is a ring endomorphism, and it is injective because N ≠ 0.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Laurent.lean:80`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.qExpand",
      "zone": "A",
      "name": "ModularCurve.qExpand",
      "display": "ModularCurve.qExpand",
      "card": "ModularCurve.qExpand"
    },
    {
      "type": "prose",
      "md": "\n  ### `qTwist` — the q ↦ u q rescaling\n\n  **Lean.** `ModularCurve.qTwist` (def)\n\n  The rescaling q ↦ u q for a unit u: the coefficient of q^k is multiplied by u^k. Composed with\n  qExpand e it is the substitution q ↦ u q^e, which the port writes TS K e u; this is the nome\n  form of τ ↦ eτ + (const).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Twist.lean:54`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.qTwist",
      "zone": "A",
      "name": "ModularCurve.qTwist",
      "display": "ModularCurve.qTwist",
      "card": "ModularCurve.qTwist"
    },
    {
      "type": "prose",
      "md": "\n  ### `coeffEmb` — coefficient extension\n\n  **Lean.** `ModularCurve.coeffEmb` (def)\n\n  The coefficient extension ℚ → K applied termwise to a Laurent series: the stand-in for 'base\n  change to a field containing the roots of unity'.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Laurent.lean:268`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.coeffEmb",
      "zone": "A",
      "name": "ModularCurve.coeffEmb",
      "display": "ModularCurve.coeffEmb",
      "card": "ModularCurve.coeffEmb"
    },
    {
      "type": "prose",
      "md": "\n  ### `jq` — the j-invariant as a Laurent series\n\n  **Lean.** `ModularCurve.jq` (def)\n\n  j(q) = q⁻¹ · (1 + 744 q + 196884 q² + ⋯), the j-invariant as a Laurent series over ℚ. It has a\n  simple pole at q = 0 with residue 1; that single fact is the source of transcendence and of\n  the triangularity arguments used in the segment.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Jq.lean:111`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.jq",
      "zone": "A",
      "name": "ModularCurve.jq",
      "display": "ModularCurve.jq",
      "card": "ModularCurve.jq"
    },
    {
      "type": "prose",
      "md": "\n  ### `jqN` — the substitution j(q^N)\n\n  **Lean.** `ModularCurve.jqN` (def)\n\n  j(q^N) := qExpand ℚ N j(q): the nome substitution q ↦ q^N applied to j(q).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Jq.lean:194`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.jqN",
      "zone": "A",
      "name": "ModularCurve.jqN",
      "display": "ModularCurve.jqN",
      "card": "ModularCurve.jqN"
    },
    {
      "type": "prose",
      "md": "\n  ### `evalAtJ` — integer polynomial evaluation at j(q)\n\n  **Lean.** `ModularCurve.evalAtJ` (def)\n\n  Evaluation of an integer polynomial at j(q): the ring hom ℤ[X] → ℚ((q)), X ↦ j(q). For a\n  two-variable modular polynomial Φ ∈ ℤ[X][Y], the outer evaluation is done with this map as the\n  coefficient map and Y ↦ j(q^N): that is Φ.eval₂ evalAtJ (jqN N).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Jq.lean:209`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.evalAtJ",
      "zone": "A",
      "name": "ModularCurve.evalAtJ",
      "display": "ModularCurve.evalAtJ",
      "card": "ModularCurve.evalAtJ"
    },
    {
      "type": "prose",
      "md": "\n  ### `modularFunctionField` — the two-generator field F_N\n\n  **Lean.** `ModularCurve.modularFunctionField` (def)\n\n  F_N := ℚ(j(q), j(q^N)), the two-generator field of the theorem.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:42`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.modularFunctionField",
      "zone": "A",
      "name": "ModularCurve.modularFunctionField",
      "display": "ModularCurve.modularFunctionField",
      "card": "ModularCurve.modularFunctionField"
    },
    {
      "type": "prose",
      "md": "\n  ### `modularFunctionFieldFull` — the divisor field F_N^full\n\n  **Lean.** `ModularCurve.modularFunctionFieldFull` (def)\n\n  F_N^full := ℚ(j(q^d) : d ∣ N), the field generated by the divisor substitutions. The inclusion\n  F_N ⊆ F_N^full is immediate (d = 1 and d = N); the theorem is the reverse inclusion.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:137`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.modularFunctionFieldFull",
      "zone": "A",
      "name": "ModularCurve.modularFunctionFieldFull",
      "display": "ModularCurve.modularFunctionFieldFull",
      "card": "ModularCurve.modularFunctionFieldFull"
    },
    {
      "type": "prose",
      "md": "\n  ### `dedekindPsi` — the Dedekind psi function\n\n  **Lean.** `ModularCurve.dedekindPsi` (def)\n\n  ψ(N) = Σ_{d ∣ N, d squarefree} N/d = N ∏_{p ∣ N}(1 + 1/p), the Dedekind psi function: the\n  index of Γ₀(N) in SL₂(ℤ), the degree of X₀(N) → X(1), and the Y-degree of the modular equation\n  Φ_N.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/DedekindPsi.lean:28`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.dedekindPsi",
      "zone": "A",
      "name": "ModularCurve.dedekindPsi",
      "display": "ModularCurve.dedekindPsi",
      "card": "ModularCurve.dedekindPsi"
    },
    {
      "type": "prose",
      "md": "\n  ### `FunctionFieldGeneration` — the pointwise target\n\n  **Lean.** `ModularCurve.FunctionFieldGeneration` (def)\n\n  FunctionFieldGeneration N: for every divisor d ∣ N, the series j(q^d) lies in the field\n  ℚ(j(q), j(q^N)). This is the pointwise form of F_N^full = F_N.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Target.lean:31`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.FunctionFieldGeneration",
      "zone": "A",
      "name": "ModularCurve.FunctionFieldGeneration",
      "display": "ModularCurve.FunctionFieldGeneration",
      "card": "ModularCurve.FunctionFieldGeneration"
    },
    {
      "type": "prose",
      "md": "\n  ### `ModularPolynomialData` — the modular polynomial datum\n\n  **Lean.** `ModularCurve.ModularPolynomialData` (structure)\n\n  A modular polynomial datum at level N: Φ ∈ ℤ[X][Y] (outer variable Y, coefficients in ℤ[X] =\n  ℤ[j]), monic in Y, of Y-degree ψ(N), and vanishing at X = j(q), Y = j(q^N).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Polynomial.lean:35`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.ModularPolynomialData",
      "zone": "A",
      "name": "ModularCurve.ModularPolynomialData",
      "display": "ModularCurve.ModularPolynomialData",
      "card": "ModularCurve.ModularPolynomialData"
    },
    {
      "type": "prose",
      "md": "\n  ### `toAdjoin` — transporting Φ into ℚ(j)[Y]\n\n  **Lean.** `ModularCurve.ModularPolynomialData.toAdjoin` (def)\n\n  The transport of Φ into ℚ(j)[Y]: evaluate every integer coefficient polynomial in ℤ[X] at\n  j(q). This is the polynomial whose irreducibility over ℚ(j) is the content of PhiIrreducible.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:116`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.ModularPolynomialData.toAdjoin",
      "zone": "A",
      "name": "ModularCurve.ModularPolynomialData.toAdjoin",
      "display": "ModularCurve.ModularPolynomialData.toAdjoin",
      "card": "ModularCurve.ModularPolynomialData.toAdjoin"
    },
    {
      "type": "prose",
      "md": "\n  ### `PhiIrreducible` — irreducibility over ℚ(j)\n\n  **Lean.** `ModularCurve.PhiIrreducible` (def)\n\n  The transported modular polynomial is irreducible over ℚ(j).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/PhiGen.lean:121`.\n",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.PhiIrreducible",
      "zone": "A",
      "name": "ModularCurve.PhiIrreducible",
      "display": "ModularCurve.PhiIrreducible",
      "card": "ModularCurve.PhiIrreducible"
    },
    {
      "type": "prose",
      "md": "  Tight, Gen, Hall, and the bundle of significant statements\n\n  The induction carries two invariants at every divisor: Tight (the degree of the modular\n  equation at that level is full) and Gen (the two-generator field is already the whole divisor\n  field). Together they form Hall. The engine is `hall_all`, whose hypotheses are the seven\n  significant statements bundled in `Inputs`.\n\n  T15–T19 proved all seven. `inputs` is therefore the point where the segment stops assuming\n  anything: it is not a mathematical theorem but the seven proofs assembled. The presentation\n  below records, for each field, what the field says mathematically and which theorem discharges\n  it. The proofs of the seven theorems are elsewhere; what matters here is that their statements\n  are the field statements verbatim, so each discharge is a drop-in replacement rather than an\n  adaptation.\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  ### `evalAtJGen` — evaluation into ℚ(j)\n\n  **Lean.** `ModularCurve.evalAtJGen` (def)\n\n  The same evaluation X ↦ j(q), but valued in ℚ(j) rather than in ℚ((q)). It presents ℤ[j(q)] as\n  a subring of ℚ(j(q)); it is injective because j(q) is transcendental, and ℚ(j(q)) is its\n  fraction field.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:94`.\n",
      "zone": "B"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.evalAtJGen",
      "zone": "B",
      "name": "ModularCurve.evalAtJGen",
      "display": "ModularCurve.evalAtJGen",
      "card": "ModularCurve.evalAtJGen"
    },
    {
      "type": "prose",
      "md": "\n  ### `Tight` — the degree invariant\n\n  **Lean.** `ModularCurve.Tight` (abbrev)\n\n  Tight d: the relative degree [ℚ(j)(j(q^d)) : ℚ(j)] equals ψ(d).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:224`.\n",
      "zone": "B"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.Tight",
      "zone": "B",
      "name": "ModularCurve.Tight",
      "display": "ModularCurve.Tight",
      "card": "ModularCurve.Tight"
    },
    {
      "type": "prose",
      "md": "\n  ### `Gen` — the generation invariant\n\n  **Lean.** `ModularCurve.Gen` (abbrev)\n\n  Gen d: the two-generator field is already the full divisor field, F_d = F_d^full.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:229`.\n",
      "zone": "B"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.Gen",
      "zone": "B",
      "name": "ModularCurve.Gen",
      "display": "ModularCurve.Gen",
      "card": "ModularCurve.Gen"
    },
    {
      "type": "prose",
      "md": "\n  ### `Hall` — the strong-induction bundle\n\n  **Lean.** `ModularCurve.Hall` (abbrev)\n\n  Hall N: the strong-induction hypothesis at N — both invariants hold at every divisor of N.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:233`.\n",
      "zone": "B"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.Hall",
      "zone": "B",
      "name": "ModularCurve.Hall",
      "display": "ModularCurve.Hall",
      "card": "ModularCurve.Hall"
    },
    {
      "type": "prose",
      "md": "\n  ### `Inputs` — the seven significant statements\n\n  **Lean.** `ModularCurve.Inputs` (structure)\n\n  The seven significant statements of the segment, bundled as the hypotheses of the strong\n  induction: two generation statements, two non-membership statements, the slot product, the\n  one-prime reduction of Gen, and the prime-power degree step.\n\n  The seven field types are exhibited one by one, through the theorems that discharge them, in\n  the reference zone; this entry only fixes the name and the shape of the bundle.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean:112`.\n",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.Inputs",
      "zone": "B",
      "name": "ModularCurve.Inputs",
      "display": "@ModularCurve.Inputs",
      "card": "ModularCurve.Inputs"
    },
    {
      "type": "prose",
      "md": "\n  ### `inputs` — the seven significant statements, discharged\n\n  **Lean name.** `ModularCurve.inputs` (theorem)\n\n  **Mathematically.** The conjunction of the seven statements bundled in `Inputs` holds.\n  Concretely: (1) one new generator per prime power, F_{Mp^{a+1}}^full = ℚ(F_{Mp^a}^full,\n  j(q^{p^{a+1}})) for p ∤ M; (2) j(q^p) ∉ F_M^full for p ∤ M and Hall M; (3) j(q^{p^{a+2}}) ∉\n  ℚ(F_M^full, j(q^p), …, j(q^{p^{a+1}})) given j(q^p) ∉ F_M^full; (4) the slot product for the\n  conjugates of j(q^M); (5) the one-prime reduction of Gen; (6) descent by one prime, given the\n  two slot hypotheses; (7) the prime-power degree step.\n\n  **Role.** Turns the conditional capstone into an unconditional one. After T15–T19 there is no\n  assumed statement left in the segment.\n\n  **Provenance.** Port assembly only: FLT has no bundled counterpart (hall_all consumes the\n  seven statements directly).\n",
      "zone": "B"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.inputs",
      "zone": "B",
      "name": "ModularCurve.inputs",
      "display": "ModularCurve.inputs",
      "card": "ModularCurve.inputs"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  theorem inputs : Inputs where\n    full_eq_adjoin_full_div_prime := full_eq_adjoin_full_div_prime\n    jqN_prime_not_mem_full := jqN_prime_not_mem_full\n    jqN_pow_not_mem_adjoin_full := jqN_pow_not_mem_adjoin_full\n    minpoly_jqN_map_eq_prod_slots := minpoly_jqN_map_eq_prod_slots\n    modularFunctionField_eq_full_of := modularFunctionField_eq_full_of\n    jqN_div_mem_modularFunctionField := jqN_div_mem_modularFunctionField\n    relfinrank_full_eq_mul := relfinrank_full_eq_mul\n  ```\n\n  **To prove (mathematical restatement).** Produce a term of type `Inputs`: a proof of each of\n  its seven fields.\n\n  **Strategy.** There is no mathematical work left. Each field is the conclusion of a theorem\n  already proved, stated with the same binders and hypotheses so that discharging the field is a\n  drop-in replacement. The Lean term is the structure literal that names the seven theorems.\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (construct).** The field `full_eq_adjoin_full_div_prime` holds.\n\n  For M ≠ 0, p prime, p ∤ M and a ≥ 0: F_{M p^{a+1}}^full = ℚ(F_{M p^a}^full, j(q^{p^{a+1}})).\n\n  *Why.* This is T18. The two-prime descent walks d ∣ M p^{a+1}: if d ∣ M p^a the series is\n  already in the lower field; otherwise peel a prime q ≠ p from the M-part, and the unique\n  common root of Φ_p and Φ_q puts j(q^d) in the target. The field type is the theorem's\n  conclusion verbatim, with the same binders and hypotheses, so no premise needs adaptation;\n  the same holds for the remaining six fields.\n\n  *Cites.*\n      - `full_eq_adjoin_full_div_prime` (ModularCurve.full_eq_adjoin_full_div_prime)\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (construct).** The field `jqN_prime_not_mem_full` holds.\n\n  For p ∤ M and Hall M: j(q^p) ∉ F_M^full.\n\n  *Why.* This is T19. If j(q^p) were in F_M^full, Gen M would put it in ℚ(j)(j(q^M));\n  evaluating at the ψ(M) distinct slots of the minimal polynomial of j(q^M) would force j(q^p)\n  ∈ ℚ(j), contradicting the prime-level degree p + 1.\n\n  *Cites.*\n      - `jqN_prime_not_mem_full` (ModularCurve.jqN_prime_not_mem_full)\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  **Step s3 (construct).** The field `jqN_pow_not_mem_adjoin_full` holds.\n\n  Given j(q^p) ∉ F_M^full: j(q^{p^{a+2}}) ∉ ℚ(F_M^full ∪ {j(q^{p^i}) : 0 ≤ i ≤ a + 1}).\n\n  *Why.* This is T17. The tower of compatible algebra homs and the modular equation Φ_p force\n  j(q^{p^{a+2}}) and j(q^{p^a}) to be the same root; injectivity gives equality of the series,\n  contradicted by the q^{-(p^a)} coefficient.\n\n  *Cites.*\n      - `jqN_pow_not_mem_adjoin_full` (ModularCurve.jqN_pow_not_mem_adjoin_full)\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  **Step s4 (construct).** The field `minpoly_jqN_map_eq_prod_slots` holds.\n\n  For a field K with a ℚ-algebra structure, a primitive M-th root of unity ζ, and Hall M: the\n  transported minimal polynomial of j(q^M) is the ψ(M)-fold product over the slots (a, b), a ∣\n  M, 0 ≤ b < M/a, gcd(gcd(a,b), M/a) = 1, of Y − j(ζ^{ab} q^{a²}).\n\n  *Why.* This is T19. Iterate the prime-level splitting of Φ_p over the prime factorization of\n  M; the exponent a² and the root of unity ζ^{ab} are the coset data.\n\n  *Cites.*\n      - `minpoly_jqN_map_eq_prod_slots` (ModularCurve.minpoly_jqN_map_eq_prod_slots)\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  **Step s5 (construct).** The field `modularFunctionField_eq_full_of` holds.\n\n  If for every factorization N = M·p with p prime one has j(q^M) ∈ F_N and Gen M, then F_N =\n  F_N^full.\n\n  *Why.* This is T15. Take d ∣ N, d ≠ N, write N = d·m, pick a prime p ∣ m and m = p·m′. Then\n  j(q^{d m′}) ∈ F_N and Gen(d m′) give j(q^d) ∈ F_N.\n\n  *Cites.*\n      - `modularFunctionField_eq_full_of` (ModularCurve.modularFunctionField_eq_full_of)\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  **Step s6 (construct).** The field `jqN_div_mem_modularFunctionField` holds.\n\n  For p prime, a primitive (Mp)-th root of unity ζ, and the slot hypotheses htw and hsp:\n  j(q^M) ∈ ℚ(j(q), j(q^{Mp})).\n\n  *Why.* This is T15. The unique-common-root principle applied to A = Φ_p(j(q^{Mp}), Y) and\n  the pushed minimal polynomial of j(q^M); htw and hsp leave j(q^M) as the only common root.\n\n  *Cites.*\n      - `jqN_div_mem_modularFunctionField` (ModularCurve.jqN_div_mem_modularFunctionField)\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  **Step s7 (construct).** The field `relfinrank_full_eq_mul` holds.\n\n  Given the tower equality F_{M p^{a+1}}^full = ℚ(F_{M p^a}^full, j(q^{p^{a+1}})) and the\n  non-membership j(q^{p^{a+1}}) ∉ F_{M p^a}^full: [F_{M p^{a+1}}^full : F_{M p^a}^full] = p +\n  1 if a = 0, else p.\n\n  *Why.* This is T16. The simple-extension reduction, then the degree p + 1 of the first prime\n  power and the degree p of later ones; ψ(p) = p + 1 is the Dedekind value the induction\n  compares against.\n\n  *Cites.*\n      - `relfinrank_full_eq_mul` (ModularCurve.relfinrank_full_eq_mul)\n      - `dedekindPsi_prime` (ModularCurve.dedekindPsi_prime)\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  **Step s8 (close).** The structure literal with these seven proofs is a term of type `Inputs`.\n\n  *Why.* Lean elaborates each field against its stated type; the seven steps fill exactly\n  those types.\n\n  *Cites.*\n      - step s1\n      - step s2\n      - step s3\n      - step s4\n      - step s5\n      - step s6\n      - step s7\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** `inputs : Inputs`.\n\n  **For a regenerating reader.**\n    - Fill each structure field with the theorem of the same name; do not restate or adapt any\n      type.\n    - If a field fails to elaborate, the port's statement has drifted from the theorem's —\n      that is a real bug, not a proof obligation.\n    - The same seven theorems can be passed to `hall_all` directly (FLT's route); the bundle\n      exists so that discharging a field is a one-line change.\n\n  **Formal notes (not mathematics).**\n    - `Inputs` has only proposition-valued fields, so Lean places it in `Prop`; a term of it\n      is a proof of the conjunction.\n    - Inside the structure literal, the right-hand side of each `field := ...` resolves to the\n      namespace-level theorem of the same name (the field name is not a local variable).\n    - The assembly has no pin counterpart: FLT's `hall_all` consumes the seven statements\n      directly, without bundling.\n",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "  one induction, four exports\n\n  With `inputs` in hand the main theorem is a one-liner, and so are the three corollaries the\n  rest of FLT consumes: the field equality, the degree of the modular equation, and the relative\n  degree of the full field. The mathematics is entirely in `hall_all` and in the seven field\n  theorems. What this section presents is the assembly, the orientation of the equalities, and\n  the two bridges that turn `Tight` into a statement about F_N^full.\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  ### `functionFieldGeneration` — the theorem, unconditional\n\n  **Lean name.** `ModularCurve.functionFieldGeneration` (theorem)\n\n  **Mathematically.** For every N ≥ 1 and every divisor d ∣ N, the series j(q^d) lies in ℚ(j(q),\n  j(q^N)). Equivalently, F_N^full = F_N: the two-generator model of the function field of X₀(N)\n  is the whole divisor field.\n\n  **Role.** The segment's target statement, with no hypotheses beyond N ≠ 0.\n\n  **Provenance.** Statement: Theorems/Thm_ModularCurve_functionFieldGeneration.lean; assembly:\n  P2M/Sol/S_ModularCurve_functionFieldGeneration.lean node 728–732.\n\n  **Hypotheses.**\n    - `(N : ℕ)` — the level, a natural number\n    - `[NeZero N]` — N ≠ 0. The substitution q ↦ q^N is the zero map at N = 0, so the level must\n      be positive; this is plumbing, not mathematics.\n",
      "zone": "C"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.functionFieldGeneration",
      "zone": "C",
      "name": "ModularCurve.functionFieldGeneration",
      "display": "ModularCurve.functionFieldGeneration",
      "card": "ModularCurve.functionFieldGeneration"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  theorem functionFieldGeneration (N : ℕ) [NeZero N] : FunctionFieldGeneration N\n  ```\n\n  **To prove (mathematical restatement).** For every N ≥ 1 and every divisor d ∣ N, the series\n  j(q^d) lies in the field generated by j(q) and j(q^N). In Lean this is qExpand ℚ d jq ∈ ℚ(jq,\n  qExpand ℚ N jq), and the definition of FunctionFieldGeneration is exactly that ∀-statement.\n\n  **Strategy.** It is enough to prove the field equality F_N^full = F_N. The strong induction\n  `hall_all` supplies Gen N, which is the equality F_N = F_N^full; the collapse lemma converts\n  between the field equality and the pointwise generation statement.\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (claim).** Hall N holds: both invariants hold at every divisor of N.\n\n  For every d ∣ N, Tight d and Gen d.\n\n  *Why.* `hall_all` applied to the seven inputs at N; the positivity hypothesis N ≠ 0 is the\n  `NeZero N` instance, read as `NeZero.ne N`.\n\n  *Cites.*\n      - `hall_all` (ModularCurve.hall_all)\n\n  *Requires.*\n      - the seven inputs, bundled — met by `ModularCurve.inputs`\n      - N ≠ 0 — met by `[NeZero N]`\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (claim).** Gen N: F_N = F_N^full.\n\n  The two-generator field is already the full divisor field at level N.\n\n  *Why.* Specialize Hall N at d = N, which divides N, and take the second component of the\n  pair.\n\n  *Cites.*\n      - step s1\n\n  *Requires.*\n      - N ∣ N — met by trivial (dvd_rfl)\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s3 (claim).** FunctionFieldGeneration N.\n\n  F_N^full = F_N, i.e. every j(q^d) with d ∣ N is generated by j(q) and j(q^N).\n\n  *Why.* The equivalence `FunctionFieldGeneration N ↔ F_N^full = F_N` is applied in the\n  direction that needs the field equality; Gen N gives the equality with the two sides\n  reversed, so it is used symmetrically.\n\n  *Cites.*\n      - step s2\n      - `iff_full_eq` (ModularCurve.functionFieldGeneration_iff_full_eq)\n      - `functionFieldGeneration_of` (ModularCurve.functionFieldGeneration_of) — the packaged\n        form of s1–s3, which the module's body calls\n\n  *Requires.*\n      - F_N^full = F_N (the right-hand side of the equivalence) — met by step s2\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** `FunctionFieldGeneration N`, and with N arbitrary, the theorem.\n\n  **For a regenerating reader.**\n    - Get Hall N from `hall_all inputs N (NeZero.ne N)`.\n    - Specialize at d = N to obtain Gen N, i.e. modularFunctionField N =\n      modularFunctionFieldFull N.\n    - Apply `functionFieldGeneration_iff_full_eq N` in the `.mpr` direction to the symmetric\n      equality.\n    - The module's own proof calls the packaged `functionFieldGeneration_of inputs N`, which\n      is definitionally this composition.\n    - Orientation matters: `Gen` is F_N = F_N^full, while the equivalence's right side is\n      F_N^full = F_N.\n\n  **Formal notes (not mathematics).**\n    - The body is `functionFieldGeneration_of inputs N`; `#print` shows it as\n      `fun N [NeZero N] => functionFieldGeneration_of inputs N`.\n    - `functionFieldGeneration_of` is\n      `(functionFieldGeneration_iff_full_eq N).mpr (hall_all h N (NeZero.ne N) N dvd_rfl).2.symm`.\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  ### `modularFunctionField_eq_full` — the field equality\n\n  **Lean name.** `ModularCurve.modularFunctionField_eq_full` (corollary)\n\n  **Mathematically.** For every N ≥ 1, F_N = F_N^full: the two-generator field is the whole\n  divisor field.\n\n  **Role.** The field-form corollary consumed by the rest of the modular-curve development.\n\n  **Provenance.** Theorems/Thm_ModularCurve_modularFunctionField_eq_full.lean; FLT corollary\n  node 713–721.\n\n  **Hypotheses.**\n    - `(N : ℕ)` — the level\n    - `[NeZero N]` — N ≠ 0\n",
      "zone": "C"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.modularFunctionField_eq_full",
      "zone": "C",
      "name": "ModularCurve.modularFunctionField_eq_full",
      "display": "ModularCurve.modularFunctionField_eq_full",
      "card": "ModularCurve.modularFunctionField_eq_full"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  theorem modularFunctionField_eq_full (N : ℕ) [NeZero N] :\n      modularFunctionField N = modularFunctionFieldFull N\n  ```\n\n  **To prove (mathematical restatement).** F_N = F_N^full.\n\n  **Strategy.** Read the second component of Hall N at d = N.\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (claim).** Hall N.\n\n  *Why.* `hall_all` at the seven inputs and N ≠ 0.\n\n  *Cites.*\n      - `hall_all` (ModularCurve.hall_all)\n\n  *Requires.*\n      - the seven inputs — met by `ModularCurve.inputs`\n      - N ≠ 0 — met by `[NeZero N]`\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (close).** Gen N, which is the goal.\n\n  *Why.* Specialize s1 at d = N and take the second component.\n\n  *Cites.*\n      - step s1\n\n  *Requires.*\n      - N ∣ N — met by trivial (dvd_rfl)\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** `modularFunctionField N = modularFunctionFieldFull N`.\n\n  **For a regenerating reader.**\n    - This is `(hall_all inputs N (NeZero.ne N) N dvd_rfl).2`.\n    - No unfolding is needed: Gen is an abbreviation for exactly this equality.\n\n  **Formal notes (not mathematics).**\n    - `hall_all` returns `Tight N ∧ Gen N`; `.2` is the equality, in the orientation F_N =\n      F_N^full.\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  ### `finrank_adjoin_jqN_eq_dedekindPsi` — the degree of the modular equation\n\n  **Lean name.** `ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi` (corollary)\n\n  **Mathematically.** For every N ≥ 1, [ℚ(j)(j(q^N)) : ℚ(j)] = ψ(N): the modular equation at\n  level N has full degree — the minimal polynomial of j(q^N) over ℚ(j) has degree ψ(N).\n\n  **Role.** The degree half of Tight, exported for consumers.\n\n  **Provenance.** Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi.lean; FLT\n  corollary node 722–727.\n\n  **Hypotheses.**\n    - `(N : ℕ)` — the level\n    - `[NeZero N]` — N ≠ 0\n",
      "zone": "C"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi",
      "zone": "C",
      "name": "ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi",
      "display": "ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi",
      "card": "ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  theorem finrank_adjoin_jqN_eq_dedekindPsi (N : ℕ) [NeZero N] :\n      Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))\n        (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))\n          ({jqN N} : Set (LaurentSeries ℚ))) = dedekindPsi N\n  ```\n\n  **To prove (mathematical restatement).** [ℚ(j)(j(q^N)) : ℚ(j)] = ψ(N).\n\n  **Strategy.** It is the definition of Tight N, the first component of Hall N at d = N.\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (claim).** Hall N.\n\n  *Why.* `hall_all` at the seven inputs.\n\n  *Cites.*\n      - `hall_all` (ModularCurve.hall_all)\n\n  *Requires.*\n      - the seven inputs — met by `ModularCurve.inputs`\n      - N ≠ 0 — met by `[NeZero N]`\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (close).** Tight N, which is the goal.\n\n  *Why.* Specialize at d = N and take the first component; Tight is an abbreviation for\n  exactly this finrank equality.\n\n  *Cites.*\n      - step s1\n      - `Tight` — the degree invariant\n\n  *Requires.*\n      - N ∣ N — met by trivial (dvd_rfl)\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** `Module.finrank ℚ⟮jq⟯ (adjoin ℚ⟮jq⟯ {jqN N}) = dedekindPsi N`.\n\n  **For a regenerating reader.**\n    - This is `(hall_all inputs N (NeZero.ne N) N dvd_rfl).1`.\n    - Tight d is the finrank of the simple extension adjoin ℚ⟮jq⟯ {jqN d}; the goal is\n      syntactically that definition.\n\n  **Formal notes (not mathematics).**\n    - Tight uses Module.finrank over ℚ⟮jq⟯ (not relfinrank): the adjoin is a simple extension,\n      so the two notions agree.\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  ### `relfinrank_full_eq_dedekindPsi` — the degree of the full field\n\n  **Lean name.** `ModularCurve.relfinrank_full_eq_dedekindPsi` (corollary)\n\n  **Mathematically.** For every N ≥ 1, [F_N^full : ℚ(j)] = ψ(N).\n\n  **Role.** The relative degree of the divisor field, the number the Hecke-correspondence\n  argument matches ranks against.\n\n  **Provenance.** Theorems/Thm_ModularCurve_relfinrank_full_eq_dedekindPsi.lean; FLT corollary\n  node 739–749.\n\n  **Hypotheses.**\n    - `(N : ℕ)` — the level\n    - `[NeZero N]` — N ≠ 0\n",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.relfinrank_full_eq_dedekindPsi",
      "zone": "C",
      "name": "ModularCurve.relfinrank_full_eq_dedekindPsi",
      "display": "@ModularCurve.relfinrank_full_eq_dedekindPsi",
      "card": "ModularCurve.relfinrank_full_eq_dedekindPsi"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  theorem relfinrank_full_eq_dedekindPsi (N : ℕ) [NeZero N] :\n      IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))\n        (modularFunctionFieldFull N) = dedekindPsi N\n  ```\n\n  **To prove (mathematical restatement).** [F_N^full : ℚ(j)] = ψ(N).\n\n  **Strategy.** Replace F_N^full by F_N (the field equality), then replace the relative degree\n  of F_N by the degree of the simple extension ℚ(j)(j(q^N)), and finish with Tight.\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (reduce).** It suffices to show [F_N : ℚ(j)] = ψ(N).\n\n  The left field may be replaced by F_N because F_N^full = F_N.\n\n  *Why.* The field equality of the previous corollary, used in the direction that rewrites\n  F_N^full to F_N.\n\n  *Cites.*\n      - `ModularCurve.modularFunctionField_eq_full`\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (claim).** [F_N : ℚ(j)] = [ℚ(j)(j(q^N)) : ℚ(j)].\n\n  Adjoining j(q^N) to ℚ(j) gives exactly F_N.\n\n  *Why.* The bridge `relfinrank_modularFunctionField`: F_N is the adjoin of j(q^N) over ℚ(j),\n  and relative degree equals the dimension of the simple extension.\n\n  *Cites.*\n      - `relfinrank_modularFunctionField` (ModularCurve.relfinrank_modularFunctionField)\n\n  *Requires.*\n      - N ≠ 0 — met by `[NeZero N]`\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Step s3 (claim).** [ℚ(j)(j(q^N)) : ℚ(j)] = ψ(N).\n\n  Tight N.\n\n  *Why.* The previous corollary, `finrank_adjoin_jqN_eq_dedekindPsi N`.\n\n  *Cites.*\n      - `ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi`\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** [F_N^full : ℚ(j)] = ψ(N).\n\n  **For a regenerating reader.**\n    - Rewrite with `← modularFunctionField_eq_full N` (the arrow points from F_N to F_N^full,\n      so `←` replaces F_N^full by F_N).\n    - Rewrite with `relfinrank_modularFunctionField N` to turn the relative degree into the\n      finrank of the simple extension.\n    - Close with `finrank_adjoin_jqN_eq_dedekindPsi N`.\n\n  **Formal notes (not mathematics).**\n    - The first rewrite is orientation-sensitive: `modularFunctionField_eq_full N` is F_N =\n      F_N^full, and the goal contains F_N^full.\n    - `#print` shows the elaborated proof as nested `Eq.mpr` / `congrArg` terms; the\n      mathematical content is the three rewrites above.\n",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": "  the modular equation as a monic polynomial over ℤ[j]\n\n  Integrality of j(q^N) over ℤ[j(q)] is the existence of the modular equation as a monic\n  polynomial. The proof is an induction on the multiplicative structure of N: at each prime p,\n  the modular polynomial Φ_p supplies a monic annihilator of j(q^{ap}) over ℤ[j][j(q^a)], and\n  integrality is transitive. The only external input is the prime-level existence of Φ_p.\n\n  The three private lemmas at the top of this section are formal bridges, not mathematics: they\n  move a value between ℚ(j) and ℚ((q)), and between integer and rational coefficients. They are\n  stated here because the fraction-field argument in the next section uses them.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  ### `phiAtSeed` — Φ evaluated at X = x\n\n  **Lean.** `ModularCurve.phiAtSeed` (def)\n\n  Φ(x, Y): the modular polynomial with its X-variable evaluated at x. At x = j(q^a) this is the\n  monic polynomial in Y whose root is j(q^{an}).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean:146`.\n",
      "zone": "D"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.phiAtSeed",
      "zone": "D",
      "name": "ModularCurve.phiAtSeed",
      "display": "ModularCurve.phiAtSeed",
      "card": "ModularCurve.phiAtSeed"
    },
    {
      "type": "prose",
      "md": "\n  ### `coe_evalAtJGen` — the ℚ(j) ↪ ℚ((q)) bridge\n\n  **Lean name.** `ModularCurve.coe_evalAtJGen` (bridge)\n\n  **Mathematically.** For every integer polynomial g, viewing its value in ℚ(j) as a Laurent\n  series gives the same series as evaluating g directly at j(q).\n\n  **Role.** A formal bridge used by the fraction-field argument: it lets an equality proved in\n  ℚ(j) be checked in ℚ((q)).\n\n  **Provenance.** Port bridge; no pin counterpart (the pin inlines the composite in the\n  fraction-ring computation).\n\n  **Hypotheses.**\n    - `(g : Polynomial ℤ)` — an integer polynomial\n",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check (fun (g : Polynomial ℤ) => (((evalAtJGen g : ℚ⟮jq⟯) : LaurentSeries ℚ) = evalAtJ g : Prop))",
      "zone": "D",
      "expr": "(fun (g : Polynomial ℤ) => (((evalAtJGen g : ℚ⟮jq⟯) : LaurentSeries ℚ) = evalAtJ g : Prop))"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  private theorem coe_evalAtJGen (g : Polynomial ℤ) :\n      ((evalAtJGen g : ℚ⟮jq⟯) : LaurentSeries ℚ) = evalAtJ g\n  ```\n\n  **To prove (mathematical restatement).** The two evaluations of g agree after the inclusion\n  ℚ(j) ⊂ ℚ((q)).\n\n  **Strategy.** Apply the ring-hom equality `algebraMap_comp_evalAtJGen` to g.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (close).** The composite (inclusion ∘ evalAtJGen) equals evalAtJ.\n\n  *Why.* `algebraMap_comp_evalAtJGen` is exactly that equality of ring homs; evaluating both\n  sides at g is `RingHom.congr_fun`.\n\n  *Cites.*\n      - `algebraMap_comp_evalAtJGen` (ModularCurve.algebraMap_comp_evalAtJGen)\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** The claimed equality of Laurent series.\n\n  **For a regenerating reader.**\n    - This is `RingHom.congr_fun algebraMap_comp_evalAtJGen g`.\n    - It carries no mathematical content: it is the coherence of the two evaluations.\n\n  **Formal notes (not mathematics).**\n    - The theorem is `private` to Capstone.lean; the sheet exhibits its statement through a\n      `#check` of the proposition rather than of the name.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  ### `aeval_map_intCast` — integer and rational evaluation agree\n\n  **Lean name.** `ModularCurve.aeval_map_intCast` (bridge)\n\n  **Mathematically.** Mathlib's ℚ-algebra evaluation of the coefficient-extended polynomial\n  g.map (ℤ → ℚ) at j(q) is the same as the integer evaluation evalAtJ g.\n\n  **Role.** Bridges mathlib's ℚ-algebra API and the port's integer-coefficient evaluation; used\n  to move integer-normalised polynomials between the two worlds.\n\n  **Provenance.** Port bridge; no pin counterpart.\n\n  **Hypotheses.**\n    - `(g : Polynomial ℤ)` — an integer polynomial\n",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check (fun (g : Polynomial ℤ) => (Polynomial.aeval jq (g.map (algebraMap ℤ ℚ)) = evalAtJ g : Prop))",
      "zone": "D",
      "expr": "(fun (g : Polynomial ℤ) => (Polynomial.aeval jq (g.map (algebraMap ℤ ℚ)) = evalAtJ g : Prop))"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  private theorem aeval_map_intCast (g : Polynomial ℤ) :\n      Polynomial.aeval jq (g.map (algebraMap ℤ ℚ)) = evalAtJ g\n  ```\n\n  **To prove (mathematical restatement).** aeval jq (g.map (ℤ → ℚ)) = evalAtJ g.\n\n  **Strategy.** Unfold aeval to eval₂, push the coefficient map through, and note the two maps ℤ\n  → ℚ((q)) agree on integers.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (calculate).** aeval jq (g.map (ℤ → ℚ)) = (g.map (ℤ → ℚ)).eval₂ (algebraMap ℚ ℚ((q))) jq.\n\n  Definition of algebra evaluation.\n\n  *Cites.*\n      - `Polynomial.aeval_def` (Polynomial.aeval_def)\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (calculate).** That equals g.eval₂ ((algebraMap ℚ ℚ((q))) ∘ (ℤ → ℚ)) jq.\n\n  Evaluation with a composite coefficient map is evaluation of the mapped polynomial.\n\n  *Cites.*\n      - `Polynomial.eval₂_eq_eval_map` (Polynomial.eval₂_eq_eval_map)\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s3 (close).** The composite coefficient map is evalAtJ.\n\n  *Why.* Both are ring homs ℤ → ℚ((q)); they agree on ℤ, so they agree ( `RingHom.ext_int`).\n\n  *Cites.*\n      - trivial (RingHom.ext_int) — two ring homs out of ℤ agree if they agree on 1\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** aeval jq (g.map (algebraMap ℤ ℚ)) = evalAtJ g.\n\n  **For a regenerating reader.**\n    - Unfold aeval, use `Polynomial.eval₂_map`, then close the ring-hom equality with\n      `RingHom.ext_int`.\n    - The equality is the formal statement that changing coefficients from ℤ to ℚ does not\n      change the value at a ℚ-algebra element.\n\n  **Formal notes (not mathematics).**\n    - `private` to Capstone.lean; exhibited as a proposition.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  ### `evalAtJ_C` — constants evaluate to constants\n\n  **Lean name.** `ModularCurve.evalAtJ_C` (bridge)\n\n  **Mathematically.** evalAtJ sends the constant polynomial b to the constant series b.\n\n  **Role.** Used in the fraction-ring computation to identify integer scalar factors after\n  denominator clearing.\n\n  **Provenance.** Port bridge; no pin counterpart.\n\n  **Hypotheses.**\n    - `(b : ℤ)` — an integer\n",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check (fun (b : ℤ) => (evalAtJ (Polynomial.C b) = (b : LaurentSeries ℚ) : Prop))",
      "zone": "D",
      "expr": "(fun (b : ℤ) => (evalAtJ (Polynomial.C b) = (b : LaurentSeries ℚ) : Prop))"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  private theorem evalAtJ_C (b : ℤ) : evalAtJ (Polynomial.C b) = (b : LaurentSeries ℚ)\n  ```\n\n  **To prove (mathematical restatement).** evalAtJ (C b) = b.\n\n  **Strategy.** evalAtJ is a ring hom, so it preserves constants; `simp` with its definition.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (close).** evalAtJ (C b) = b.\n\n  *Why.* evalAtJ is the ring hom induced by aeval at jq; a ring hom sends the constant\n  polynomial to the image of b.\n\n  *Cites.*\n      - `evalAtJ` — integer polynomial evaluation at j(q)\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** The claimed equality.\n\n  **For a regenerating reader.**\n    - `simp [evalAtJ]`.\n\n  **Formal notes (not mathematics).**\n    - `private` to Capstone.lean; exhibited as a proposition.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  ### `exists_monic_evalAtJ_jqN_eq_zero` — integrality of j(q^N)\n\n  **Lean name.** `ModularCurve.exists_monic_evalAtJ_jqN_eq_zero` (theorem)\n\n  **Mathematically.** For every N ≥ 1 there is a monic P ∈ ℤ[X][Y] with P(j(q), j(q^N)) = 0. In\n  other words, j(q^N) is integral over ℤ[j(q)].\n\n  **Role.** Supplies the monic annihilator — the integrality half of the modular polynomial —\n  from the prime-level modular equation.\n\n  **Provenance.** Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean.\n\n  **Hypotheses.**\n    - `(N : ℕ)` — the level\n    - `[NeZero N]` — N ≠ 0\n",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.exists_monic_evalAtJ_jqN_eq_zero",
      "zone": "D",
      "name": "ModularCurve.exists_monic_evalAtJ_jqN_eq_zero",
      "display": "@ModularCurve.exists_monic_evalAtJ_jqN_eq_zero",
      "card": "ModularCurve.exists_monic_evalAtJ_jqN_eq_zero"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  theorem exists_monic_evalAtJ_jqN_eq_zero (N : ℕ) [NeZero N] :\n      ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.eval₂ evalAtJ (jqN N) = 0\n  ```\n\n  **To prove (mathematical restatement).** Find a monic P ∈ ℤ[j][Y] with P(j(q), j(q^N)) = 0.\n\n  **Strategy.** Induct on the multiplicative structure of N. The level N = 1 is j(q) itself; the\n  level N = 0 is excluded. The prime step uses the modular equation: for p prime, Φ_p(j(q^a), Y)\n  is a monic polynomial over ℤ[j][j(q^a)] with root j(q^{ap}), and ℤ[j][j(q^a)] is integral over\n  ℤ[j]; integrality is transitive.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s0 (reduce).** It is enough to prove IsIntegral (Polynomial ℤ) (jqN n) for every n with NeZero n.\n\n  Integrality of j(q^n) over ℤ[j] is exactly the existence of a monic annihilator.\n\n  *Why.* `IsIntegral` unfolds to the existential of a monic polynomial; under the algebra\n  structure evalAtJ.toAlgebra, the algebra map is evalAtJ, and the evaluation is eval₂\n  evalAtJ.\n\n  *Cites.*\n      - `evalAtJ` — integer polynomial evaluation at j(q)\n      - trivial (IsIntegral) — ∃ P, P.Monic ∧ P.eval₂ (algebraMap R S) x = 0\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (reduce).** It is enough to prove the base cases 0 and 1 and the prime-multiplication step.\n\n  Every positive integer is reached from 1 by repeated multiplication by primes; the induction\n  is on the multiplicative structure of ℕ.\n\n  *Why.* `induction_on_primes` with motive `fun n => NeZero n → IsIntegral (jqN n)`.\n\n  *Cites.*\n      - `induction_on_primes` (induction_on_primes)\n\n  *Requires.*\n      - the case n = 0 — met by step s2\n      - the case n = 1 — met by step s3\n      - the prime-multiplication step — met by step s9\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (close).** The case n = 0 is vacuous.\n\n  There is no level 0.\n\n  *Why.* NeZero 0 supplies 0 ≠ 0, a contradiction.\n\n  *Cites.*\n      - trivial (NeZero 0) — the instance carries the field out : 0 ≠ 0\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s3 (claim).** The case n = 1 holds, with P = X.\n\n  j(q^1) = j(q), and j(q) is the value of the polynomial X.\n\n  *Why.* jqN 1 = jq, and evalAtJ X = jq. The monic annihilator is the polynomial X over ℤ[X];\n  this is `isIntegral_algebraMap` for the algebra-map element X.\n\n  *Cites.*\n      - `jqN_one` (ModularCurve.jqN_one)\n      - `evalAtJ_X` (ModularCurve.evalAtJ_X)\n      - `isIntegral_algebraMap` (isIntegral_algebraMap)\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s4 (claim).** Prime step, hypothesis: j(q^a) is integral over ℤ[j].\n\n  The induction hypothesis at the level a.\n\n  *Why.* This is the `ih` argument supplied by the `induction_on_primes` step (s1); the NeZero\n  a instance is derived from NeZero (p·a). It is the standing assumption of the whole prime\n  case.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s5 (construct).** Take a modular polynomial datum at p: Φ_p monic, Φ_p(j(q), j(q^p)) = 0.\n\n  At a prime p, the modular polynomial exists, is monic, and vanishes at (j(q), j(q^p)).\n\n  *Why.* `exists_phiIrreducible_evalSymm p`; only monicity and the vanishing are used here\n  (irreducibility and symmetry are needed elsewhere).\n\n  *Cites.*\n      - `exists_phiIrreducible_evalSymm` (ModularCurve.exists_phiIrreducible_evalSymm)\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s6 (claim).** A := ℤ[j][j(q^a)] is an integral extension of ℤ[j].\n\n  A is the subalgebra generated by j(q^a). Since j(q^a) is integral, A is a finitely generated\n  ℤ[j]-module, so every element of A is integral over ℤ[j].\n\n  *Why.* `IsIntegral.fg_adjoin_singleton` makes A finitely generated as a module;\n  `IsIntegral.of_mem_of_fg` then gives integrality of each element. Finally\n  `isIntegral_algHom_iff` transports along the injective inclusion A ↪ ℚ((q)), producing\n  `Algebra.IsIntegral ℤ[j] A`.\n\n  *Cites.*\n      - `IsIntegral.fg_adjoin_singleton` (IsIntegral.fg_adjoin_singleton)\n      - `IsIntegral.of_mem_of_fg` (IsIntegral.of_mem_of_fg)\n      - `isIntegral_algHom_iff` (isIntegral_algHom_iff)\n\n  *Requires.*\n      - j(q^a) is integral over ℤ[j] — met by step s4\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s7 (claim).** j(q^{ap}) is a root of the monic polynomial Φ_p(j(q^a), Y) over A.\n\n  Φ_p(j(q^a), j(q^{ap})) = 0.\n\n  *Why.* Substitute q ↦ q^a into Φ_p(j(q), j(q^p)) = 0. In Lean, `phiAtSeed_jqN_eval p data a`\n  gives the vanishing in ℚ((q)), and `phiAtSeed_map` identifies the evaluation over A with it.\n\n  *Cites.*\n      - `phiAtSeed_jqN_eval` (ModularCurve.phiAtSeed_jqN_eval)\n      - `phiAtSeed_map` (ModularCurve.phiAtSeed_map)\n      - `phiAtSeed_monic` (ModularCurve.phiAtSeed_monic)\n\n  *Requires.*\n      - the datum at p — met by step s5\n      - the level a — met by step s4\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s8 (claim).** j(q^{ap}) is integral over ℤ[j].\n\n  Integral over A, and A integral over ℤ[j], so integral over ℤ[j].\n\n  *Why.* `isIntegral_trans`, with the monic polynomial of s7 over A and the integral extension\n  of s6.\n\n  *Cites.*\n      - `isIntegral_trans` (isIntegral_trans)\n      - step s6\n      - step s7\n\n  *Requires.*\n      - Algebra.IsIntegral ℤ[j] A — met by step s6\n      - IsIntegral A (j(q^{ap})) — met by step s7\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Step s9 (close).** The prime step holds: j(q^{pa}) is integral over ℤ[j].\n\n  j(q^{ap}) = j(q^{pa}).\n\n  *Why.* `jqN_congr` with commutativity of multiplication.\n\n  *Cites.*\n      - `jqN_congr` (ModularCurve.jqN_congr)\n      - step s8\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** By induction, every j(q^n) (n ≠ 0) is integral; unpacking IsIntegral at N\n  gives the monic P.\n\n  **For a regenerating reader.**\n    - State the stronger form `∀ n, NeZero n → IsIntegral (Polynomial ℤ) (jqN n)` and induct\n      with `induction_on_primes`.\n    - Case 0 is `absurd rfl h.out`; case 1 is `isIntegral_algebraMap` after rewriting `jqN 1`\n      and `evalAtJ X`.\n    - In the prime case, let A = Algebra.adjoin (Polynomial ℤ) {jqN a}; get\n      `Algebra.IsIntegral (Polynomial ℤ) A` from `hia.fg_adjoin_singleton`,\n      `IsIntegral.of_mem_of_fg`, and `isIntegral_algHom_iff` along the inclusion into the\n      Laurent series.\n    - The root is `phiAtSeed data ⟨jqN a, hmem⟩` at `jqN (a * p)`: `phiAtSeed_jqN_eval` in the\n      big field, transported by `phiAtSeed_map`.\n    - Close with `isIntegral_trans` and rewrite `jqN (a * p)` to `jqN (p * a)` with\n      `jqN_congr (Nat.mul_comm a p)`.\n\n  **Formal notes (not mathematics).**\n    - The two `NeZero` instances in the prime case (for a and for a·p) are built from\n      `NeZero (p·a)`; this is plumbing around the instance arguments.\n    - `hroot` is stated with `Polynomial.eval₂ (algebraMap A (LaurentSeries ℚ))`;\n      `Polynomial.eval₂_eq_eval_map` plus `phiAtSeed_map` turn the evaluation over A into the\n      evaluation over ℚ((q)).\n    - `IsIntegral` is not a structure but a def: `⟨P, hP, hval⟩` is exactly its constructor,\n      which is why the outer `obtain` works.\n    - The datum's irreducibility and symmetry are discarded ( `obtain ⟨data, -, -⟩`):\n      integrality needs only monicity and vanishing.\n",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "  two minimal polynomials and a fraction field\n\n  The last step turns the degree count into an irreducible modular polynomial. The key is to\n  compare two minimal polynomials: over ℤ[j(q)] (where j(q^N) is integral) and over ℚ(j(q)) (its\n  fraction field). The fraction-field structure is the only technical point; after it, the\n  degree computation and irreducibility are consequences of the minimal-polynomial API.\n\n  The three exports differ only in packaging: the construction with its hypothesis, the\n  hypothesis-free existence of an irreducible datum, and the bare existence of a datum. The last\n  one is a deliberate strengthening over the pin's separate proof.\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  ### `exists_phiIrreducible_of_finrank_eq` — from the degree count to an irreducible datum\n\n  **Lean name.** `ModularCurve.exists_phiIrreducible_of_finrank_eq` (theorem)\n\n  **Mathematically.** Given Tight N — that is, [ℚ(j)(j(q^N)) : ℚ(j)] = ψ(N) — there is a modular\n  polynomial datum at level N whose transport to ℚ(j)[Y] is irreducible. So the degree count\n  produces the irreducible modular polynomial.\n\n  **Role.** The interface between the degree half of the induction and the irreducibility API\n  consumed by the rest of FLT.\n\n  **Provenance.** Theorems/Thm_ModularCurve_exists_phiIrreducible_of_finrank_eq.lean.\n\n  **Hypotheses.**\n    - `(N : ℕ)` — the level\n    - `[NeZero N]` — N ≠ 0\n    - `(h : Module.finrank ℚ⟮jq⟯ (adjoin ℚ⟮jq⟯ {jqN N}) = dedekindPsi N)` — Tight N: the simple\n      extension ℚ(j)(j(q^N)) has degree ψ(N) over ℚ(j).\n",
      "zone": "E"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.exists_phiIrreducible_of_finrank_eq",
      "zone": "E",
      "name": "ModularCurve.exists_phiIrreducible_of_finrank_eq",
      "display": "@ModularCurve.exists_phiIrreducible_of_finrank_eq",
      "card": "ModularCurve.exists_phiIrreducible_of_finrank_eq"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  theorem exists_phiIrreducible_of_finrank_eq (N : ℕ) [NeZero N]\n      (h : Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))\n        (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))\n          ({jqN N} : Set (LaurentSeries ℚ))) = dedekindPsi N) :\n      ∃ data : ModularPolynomialData N, PhiIrreducible data\n  ```\n\n  **To prove (mathematical restatement).** Produce a modular polynomial datum at level N whose\n  transported polynomial is irreducible over ℚ(j): a monic Φ ∈ ℤ[j][Y] of degree ψ(N) vanishing\n  at (j(q), j(q^N)), with Φ.map(evalAtJGen) irreducible.\n\n  **Strategy.** Take Φ = minpoly over ℤ[j(q)] of j(q^N). Compare it with the minimal polynomial\n  over ℚ(j(q)), which by the fraction-field structure is Φ with coefficients evaluated at j(q).\n  The degree of the latter is the hypothesis ψ(N); its degree count gives Φ's degree; its\n  irreducibility gives Φ's transported irreducibility.\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (claim).** The evaluation ℤ[X] → ℚ(j), X ↦ j(q), is injective.\n\n  j(q) is transcendental over ℚ, so no nonzero integer polynomial vanishes at it.\n\n  *Why.* Transcendence of j(q), packaged as `evalAtJGen_injective`.\n\n  *Cites.*\n      - `evalAtJGen_injective` (ModularCurve.evalAtJGen_injective)\n      - `transcendental_jq` (ModularCurve.transcendental_jq)\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (claim).** ℚ(j) is the fraction field of ℤ[j].\n\n  Every element z ∈ ℚ(j) is a quotient r/s of two polynomial expressions in j(q) with rational\n  coefficients; clearing denominators of r and s makes them integer polynomials, and the\n  scalar factors cancel in the quotient.\n\n  *Why.* `mem_adjoin_simple_iff` writes z = aeval jq r / aeval jq s. Apply\n  `integerNormalization_spec` to r and to s: the integer normalisations r′ and s′ satisfy\n  evalAtJ r′ = b_r · aeval jq r and evalAtJ s′ = b_s · aeval jq s. Then z = (b_s · r′)/(b_r ·\n  s′), a fraction of integer polynomials. Injectivity from s1 makes the field structure\n  well-defined.\n\n  *Cites.*\n      - `IntermediateField.mem_adjoin_simple_iff` (IntermediateField.mem_adjoin_simple_iff)\n      - `IsLocalization.integerNormalization_spec` (IsLocalization.integerNormalization_spec)\n      - `ModularCurve.coe_evalAtJGen`\n      - step s1\n\n  *Requires.*\n      - injectivity of the evaluation — met by step s1\n      - the numerator is a polynomial value — met by `IntermediateField.mem_adjoin_simple_iff`\n        (IntermediateField.mem_adjoin_simple_iff)\n      - the denominator is a polynomial value — met by `IntermediateField.mem_adjoin_simple_iff`\n        (IntermediateField.mem_adjoin_simple_iff)\n      - clearing denominators — met by `IsLocalization.integerNormalization_spec`\n        (IsLocalization.integerNormalization_spec)\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s3 (claim).** minpoly_ℚ(j)(j(q^N)) = Φ.map(evalAtJGen), where Φ = minpoly_ℤ[j](j(q^N)).\n\n  Over an integrally closed base ring with fraction field K, the minimal polynomial over K is\n  the image of the minimal polynomial over the base ring. ℤ[j] is a polynomial ring over ℤ,\n  hence integrally closed.\n\n  *Why.* `minpoly.isIntegrallyClosed_eq_field_fractions'` with the fraction-field structure of\n  s2.\n\n  *Cites.*\n      - `minpoly.isIntegrallyClosed_eq_field_fractions'`\n        (minpoly.isIntegrallyClosed_eq_field_fractions')\n      - step s2\n\n  *Requires.*\n      - ℚ(j) is the fraction field of ℤ[j] — met by step s2\n      - j(q^N) is integral over ℤ[j] — met by `ModularCurve.exists_monic_evalAtJ_jqN_eq_zero`\n      - ℤ[j] is integrally closed — met by trivial (IsIntegrallyClosed (Polynomial ℤ))\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s4 (claim).** natDegree Φ = ψ(N).\n\n  deg Φ = deg(minpoly_ℚ(j)(j(q^N))) because Φ is monic; the latter degree is [ℚ(j)(j(q^N)) :\n  ℚ(j)] by the degree–minimal-polynomial identity; the hypothesis identifies it with ψ(N).\n\n  *Why.* `Polynomial.Monic.natDegree_map` preserves the degree under the coefficient map;\n  `IntermediateField.adjoin.finrank` identifies the natDegree of the minimal polynomial of\n  j(q^N) over ℚ(j) with the finrank of the simple extension; the hypothesis h is that finrank.\n\n  *Cites.*\n      - `minpoly.monic` (minpoly.monic)\n      - `Polynomial.Monic.natDegree_map` (Polynomial.Monic.natDegree_map)\n      - `IntermediateField.adjoin.finrank` (IntermediateField.adjoin.finrank)\n      - step s3\n      - `(h : Module.finrank ℚ⟮jq⟯ (adjoin ℚ⟮jq⟯ {jqN N}) = dedekindPsi N)`\n\n  *Requires.*\n      - Φ is monic — met by `minpoly.monic` (minpoly.monic)\n      - j(q^N) is integral over ℤ[j] — met by `ModularCurve.exists_monic_evalAtJ_jqN_eq_zero`\n      - hence integral over ℚ(j) — met by `IsIntegral.tower_top` (IsIntegral.tower_top)\n      - the fraction-field comparison of s3 — met by step s3\n      - the hypothesis [ℚ(j)(j(q^N)) : ℚ(j)] = ψ(N) — met by\n        `(h : Module.finrank ℚ⟮jq⟯ (adjoin ℚ⟮jq⟯ {jqN N}) = dedekindPsi N)`\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s5 (claim).** Φ evaluates to zero at (j(q), j(q^N)).\n\n  Φ is the minimal polynomial of j(q^N) over ℤ[j], so aeval (j(q^N)) Φ = 0.\n\n  *Why.* `minpoly.aeval`, then unfold aeval to eval₂ with the algebra map evalAtJ.\n\n  *Cites.*\n      - `minpoly.aeval` (minpoly.aeval)\n      - `Polynomial.aeval_def` (Polynomial.aeval_def)\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s6 (construct).** data := ⟨Φ, monic, degree, vanishing⟩ is a ModularPolynomialData N.\n\n  *Why.* The structure's four fields are the monicity of minpoly.monic, the degree of s4, and\n  the vanishing of s5.\n\n  *Cites.*\n      - step s4\n      - step s5\n      - `minpoly.monic` (minpoly.monic)\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s7 (claim).** PhiIrreducible data.\n\n  The transport of Φ is minpoly_ℚ(j)(j(q^N)), which is irreducible.\n\n  *Why.* data.toAdjoin is Φ.map(evalAtJGen), equal to minpoly_ℚ(j)(j(q^N)) by s3; a minimal\n  polynomial of an element over a field is irreducible.\n\n  *Cites.*\n      - step s3\n      - `minpoly.irreducible` (minpoly.irreducible)\n\n  *Requires.*\n      - j(q^N) is integral over ℤ[j] — met by `ModularCurve.exists_monic_evalAtJ_jqN_eq_zero`\n      - hence integral over ℚ(j) — met by `IsIntegral.tower_top` (IsIntegral.tower_top)\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** ∃ data : ModularPolynomialData N, PhiIrreducible data.\n\n  **For a regenerating reader.**\n    - Install the algebra structures `evalAtJGen.toAlgebra` and `evalAtJ.toAlgebra`, plus the\n      scalar tower between them.\n    - Build the IsFractionRing instance with the three fields map_units, surj, exists_of_eq;\n      surj is the denominator-clearing argument (integerNormalization for numerator and\n      denominator).\n    - Get `hx : IsIntegral (Polynomial ℤ) (jqN N)` from the previous theorem and\n      `hxQ := hx.tower_top`.\n    - Set Φ := minpoly (Polynomial ℤ) (jqN N) and use\n      `minpoly.isIntegrallyClosed_eq_field_fractions'` to identify its image with minpoly over\n      ℚ⟮jq⟯.\n    - Compute the degree by rewriting the goal with `← hΦm.natDegree_map` and `← hmin`, then\n      close with `h` after `IntermediateField.adjoin.finrank`.\n    - For the vanishing, unfold `minpoly.aeval` with `Polynomial.aeval_def`.\n    - Irreducibility is `minpoly.irreducible hxQ` after rewriting the transport with\n      `hmin.symm`.\n\n  **Formal notes (not mathematics).**\n    - The two `letI : Algebra (Polynomial ℤ) …` lines are not decoration: with them,\n      `algebraMap (Polynomial ℤ) ℚ⟮jq⟯` is definitionally `evalAtJGen`, so `minpoly`,\n      `IsIntegral` and `aeval` are taken over the intended algebra structure.\n    - The IsFractionRing `surj` proof carries an explicit computation ( `key`) identifying the\n      fraction with `z` in ℚ((q)); `Subtype.ext` transports it back to ℚ(j). `coe_evalAtJGen`\n      is used as `hcoe` inside that computation.\n    - `hmin` is an equality of polynomials; `hmin.symm` rewrites `Φ.map evalAtJGen` to\n      `minpoly ℚ⟮jq⟯ (jqN N)`.\n    - The `rw [IntermediateField.adjoin.finrank hxQ] at h` is what turns the hypothesis h into\n      a statement about the natDegree of the minimal polynomial over ℚ(j).\n    - `IsIntegrallyClosed (Polynomial ℤ)` is found by typeclass search; no named premise is\n      needed.\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  ### `exists_phiIrreducible` — an irreducible datum at every level\n\n  **Lean name.** `ModularCurve.exists_phiIrreducible` (corollary)\n\n  **Mathematically.** For every N ≥ 1 there is a modular polynomial datum at level N whose\n  transport to ℚ(j)[Y] is irreducible.\n\n  **Role.** The form the rest of FLT consumes.\n\n  **Provenance.** Theorems/Thm_ModularCurve_exists_phiIrreducible.lean.\n\n  **Hypotheses.**\n    - `(N : ℕ)` — the level\n    - `[NeZero N]` — N ≠ 0\n",
      "zone": "E"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.exists_phiIrreducible",
      "zone": "E",
      "name": "ModularCurve.exists_phiIrreducible",
      "display": "ModularCurve.exists_phiIrreducible",
      "card": "ModularCurve.exists_phiIrreducible"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  theorem exists_phiIrreducible (N : ℕ) [NeZero N] :\n      ∃ data : ModularPolynomialData N, PhiIrreducible data\n  ```\n\n  **To prove (mathematical restatement).** ∃ data : ModularPolynomialData N, PhiIrreducible\n  data.\n\n  **Strategy.** Apply the previous theorem to the degree count Tight N.\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (claim).** Tight N: [ℚ(j)(j(q^N)) : ℚ(j)] = ψ(N).\n\n  *Why.* `finrank_adjoin_jqN_eq_dedekindPsi N`.\n\n  *Cites.*\n      - `ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi`\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (close).** ∃ data, PhiIrreducible data.\n\n  *Why.* `exists_phiIrreducible_of_finrank_eq N` applied to s1.\n\n  *Cites.*\n      - `ModularCurve.exists_phiIrreducible_of_finrank_eq`\n      - step s1\n\n  *Requires.*\n      - Tight N — met by step s1\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** The existential.\n\n  **For a regenerating reader.**\n    - This is `exists_phiIrreducible_of_finrank_eq N (finrank_adjoin_jqN_eq_dedekindPsi N)`.\n\n  **Formal notes (not mathematics).**\n    - Both components are public: `#print` shows the one-line body.\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  ### `nonempty_modularPolynomialData` — the datum exists\n\n  **Lean name.** `ModularCurve.nonempty_modularPolynomialData` (corollary)\n\n  **Mathematically.** For every N ≥ 1 the type of modular polynomial data at level N is\n  inhabited.\n\n  **Role.** The pin's `nonempty_modularPolynomialData`; its consumers use only existence, so the\n  port takes the datum from the stronger irreducible statement.\n\n  **Provenance.** Theorems/Thm_ModularCurve_nonempty_modularPolynomialData.lean; the port\n  derives it from exists_phiIrreducible instead of repeating the minpoly construction.\n\n  **Hypotheses.**\n    - `(N : ℕ)` — the level\n    - `[NeZero N]` — N ≠ 0\n",
      "zone": "E"
    },
    {
      "type": "print",
      "raw": "#print ModularCurve.nonempty_modularPolynomialData",
      "zone": "E",
      "name": "ModularCurve.nonempty_modularPolynomialData",
      "display": "ModularCurve.nonempty_modularPolynomialData",
      "card": "ModularCurve.nonempty_modularPolynomialData"
    },
    {
      "type": "prose",
      "md": "\n  **Lean statement.**\n\n  ```lean\n  theorem nonempty_modularPolynomialData (N : ℕ) [NeZero N] :\n      Nonempty (ModularPolynomialData N)\n  ```\n\n  **To prove (mathematical restatement).** Nonempty (ModularPolynomialData N).\n\n  **Strategy.** Project the datum out of the irreducible existence statement.\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s1 (claim).** There is data with PhiIrreducible data.\n\n  *Why.* `exists_phiIrreducible N`.\n\n  *Cites.*\n      - `ModularCurve.exists_phiIrreducible`\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Step s2 (close).** Nonempty (ModularPolynomialData N).\n\n  *Why.* Eliminate the existential and keep the datum.\n\n  *Cites.*\n      - step s1\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "\n  **Conclusion.** `Nonempty (ModularPolynomialData N)`.\n\n  **For a regenerating reader.**\n    - `(exists_phiIrreducible N).elim fun data _ => ⟨data⟩`.\n    - The pin proves this separately by the same minpoly construction; the port's choice is\n      documented in the declaration's docstring and is safe because the node's consumers use\n      only existence.\n\n  **Formal notes (not mathematics).**\n    - This is a deliberate deviation from the pin: taking the datum from the stronger\n      statement avoids re-deriving the fraction-ring block. The irreducibility is discarded.\n",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "  every citation, with its Lean type\n\n  The statements the proofs above cite or lean on, grouped by origin. The port group contains\n  the seven `Inputs` fields together with the induction engine and the bridges; the mathlib\n  group contains the generic lemmas the two proof-bearing declarations invoke. `#check` shows\n  the type as the compiler sees it; the gloss under each name says what it means mathematically.\n",
      "zone": "F"
    },
    {
      "type": "prose",
      "md": "\n  ### port theorems cited\n\n  The statement below is the compiler's, via `#check`.\n",
      "zone": "F"
    },
    {
      "type": "prose",
      "md": "\n  ### `hall_all` — ModularCurve.hall_all\n\n  From the seven inputs, Tight and Gen hold at every divisor of every N ≠ 0. This is the strong\n  induction over the divisor lattice: the generation half walks down the divisors one prime at a\n  time, and the degree half multiplies the tower law along prime-power levels.\n\n  Its hypothesis is exactly `Inputs`; the proof is math/010 §7. The two halves are\n  interdependent: Gen d needs Gen and the degree facts at proper divisors, Tight d needs Tight\n  below and Gen d just proved.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean:311`.\n\n  Pinned FLT: `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean#614-700`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.hall_all",
      "zone": "F",
      "name": "ModularCurve.hall_all",
      "display": "@ModularCurve.hall_all",
      "card": "ModularCurve.hall_all"
    },
    {
      "type": "prose",
      "md": "\n  ### `functionFieldGeneration_of` — ModularCurve.functionFieldGeneration_of\n\n  From the seven inputs, FunctionFieldGeneration N for every N ≠ 0. It is the packaged\n  composition of `hall_all` at d = N with the collapse equivalence.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean:392`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.functionFieldGeneration_of",
      "zone": "F",
      "name": "ModularCurve.functionFieldGeneration_of",
      "display": "@ModularCurve.functionFieldGeneration_of",
      "card": "ModularCurve.functionFieldGeneration_of"
    },
    {
      "type": "prose",
      "md": "\n  ### `iff_full_eq` — ModularCurve.functionFieldGeneration_iff_full_eq\n\n  The pointwise generation statement is equivalent to the field equality F_N^full = F_N. The\n  forward direction says the field generated by all j(q^d) is contained in ℚ(j(q), j(q^N)); the\n  reverse says every j(q^d) is among its generators.\n\n  The right-hand side is written with F_N^full on the left. `Gen N` is the opposite orientation,\n  F_N = F_N^full, so a proof must use `.symm` — this is the one place where the capstone's\n  one-liners are orientation-sensitive.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Collapse.lean:35`.\n\n  Pinned FLT: `P2M/Sol/S_ModularCurve_functionFieldGeneration_iff_full_eq.lean#11-21`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.functionFieldGeneration_iff_full_eq",
      "zone": "F",
      "name": "ModularCurve.functionFieldGeneration_iff_full_eq",
      "display": "@ModularCurve.functionFieldGeneration_iff_full_eq",
      "card": "ModularCurve.functionFieldGeneration_iff_full_eq"
    },
    {
      "type": "prose",
      "md": "\n  ### `relfinrank_modularFunctionField` — ModularCurve.relfinrank_modularFunctionField\n\n  The relative degree [F_N : ℚ(j)] is the degree of the simple extension ℚ(j)(j(q^N)).\n  Equivalently: adjoining the single element j(q^N) to ℚ(j) gives F_N, so the relative degree is\n  the degree of j(q^N) over ℚ(j).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:73`.\n\n  Pinned FLT: `Theorems/Thm_ModularCurve_relfinrank_modularFunctionField.lean`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.relfinrank_modularFunctionField",
      "zone": "F",
      "name": "ModularCurve.relfinrank_modularFunctionField",
      "display": "@ModularCurve.relfinrank_modularFunctionField",
      "card": "ModularCurve.relfinrank_modularFunctionField"
    },
    {
      "type": "prose",
      "md": "\n  ### `full_eq_adjoin_full_div_prime` — ModularCurve.full_eq_adjoin_full_div_prime\n\n  For p ∤ M, the full field at M p^{a+1} is generated over the full field at M p^a by the single\n  new series j(q^{p^{a+1}}). This is the generation half of one prime-power step (T18).\n\n  Proof: the inclusion ⊇ is immediate because both generators divide M p^{a+1}. For ⊆, take\n  j(q^d) with d ∣ M p^{a+1}. If d ∣ M p^a it is already in the lower field; otherwise d = m\n  p^{a+1} with m ∣ M, p ∤ m. If m = 1 it is the new generator; if m > 1 pick a prime q ∣ m, q ≠\n  p, and apply the two-prime descent: j(q^{d/p}) is in the target by inspection and j(q^{d/q})\n  by strong induction, and the unique common root of Φ_p and Φ_q forces j(q^d) in the target.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Generation.lean:297`.\n\n  Pinned FLT: `Theorems/Thm_ModularCurve_full_eq_adjoin_full_div_prime.lean`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.full_eq_adjoin_full_div_prime",
      "zone": "F",
      "name": "ModularCurve.full_eq_adjoin_full_div_prime",
      "display": "@ModularCurve.full_eq_adjoin_full_div_prime",
      "card": "ModularCurve.full_eq_adjoin_full_div_prime"
    },
    {
      "type": "prose",
      "md": "\n  ### `jqN_prime_not_mem_full` — ModularCurve.jqN_prime_not_mem_full\n\n  For p ∤ M and Hall M, j(q^p) is not in the full field at M. This is one of the two\n  non-membership inputs of the degree half (T19).\n\n  Proof: if j(q^p) were in F_M^full, then by Gen M it would lie in ℚ(j)(j(q^M)), say j(q^p) =\n  g(j(q^M)) with deg g < ψ(M). Evaluating g at the ψ(M) distinct slots of the minimal polynomial\n  of j(q^M) shows g is constant there; a polynomial of degree < ψ(M) constant on ψ(M) points has\n  its value in ℚ(j). Then j(q^p) ∈ ℚ(j), contradicting the prime-level degree [ℚ(j)(j(q^p)) :\n  ℚ(j)] = p + 1. The theorem states the hypothesis as the expanded conjunction ∀ d ∣ M, Tight d\n  ∧ Gen d; that is definitionally `Hall M`, because Hall is an abbreviation, which is why\n  `inputs` can fill the field with it.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProduct.lean:1590`.\n\n  Pinned FLT: `Theorems/Thm_ModularCurve_jqN_prime_not_mem_full.lean`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.jqN_prime_not_mem_full",
      "zone": "F",
      "name": "ModularCurve.jqN_prime_not_mem_full",
      "display": "@ModularCurve.jqN_prime_not_mem_full",
      "card": "ModularCurve.jqN_prime_not_mem_full"
    },
    {
      "type": "prose",
      "md": "\n  ### `jqN_pow_not_mem_adjoin_full` — ModularCurve.jqN_pow_not_mem_adjoin_full\n\n  If j(q^p) is not in F_M^full, then j(q^{p^{a+2}}) is not in the field generated by F_M^full\n  together with the earlier p-power series j(q^p), …, j(q^{p^{a+1}}). This is the prime-power\n  non-membership tower (T17).\n\n  Proof: build the tower of intermediate fields and a compatible family of ℚ-algebra homs σ_i\n  whose images lie in a shrinking qExpand range. The modular equation Φ_p has both\n  j(q^{p^{a+2}}) and j(q^{p^a}) as roots of Φ_p(j(q^{p^{a+1}}), Y); pushing it through σ forces\n  the two to be the same root, and injectivity of σ gives equality of the two series,\n  contradicted by the q^{-(p^a)} coefficient (1 versus 0).\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Nonmembership.lean:615`.\n\n  Pinned FLT: `Theorems/Thm_ModularCurve_jqN_pow_not_mem_adjoin_full.lean`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.jqN_pow_not_mem_adjoin_full",
      "zone": "F",
      "name": "ModularCurve.jqN_pow_not_mem_adjoin_full",
      "display": "@ModularCurve.jqN_pow_not_mem_adjoin_full",
      "card": "ModularCurve.jqN_pow_not_mem_adjoin_full"
    },
    {
      "type": "prose",
      "md": "\n  ### `minpoly_jqN_map_eq_prod_slots` — ModularCurve.minpoly_jqN_map_eq_prod_slots\n\n  The slot description of the conjugates: after the coefficient substitution q ↦ q^M, the\n  minimal polynomial of j(q^M) over ℚ(j) is the product of the linear factors Y − j(ζ^{ab}\n  q^{a²}), over a ∣ M and 0 ≤ b < M/a with gcd(gcd(a,b), M/a) = 1. The pairs number ψ(M).\n\n  Proof (T19): iterate the prime-level splitting Φ_p(j(u^p q^{pe}), Y) = (Y − j(u^{p²}q^{p²e}))\n  ∏_b (Y − j(u ζ_p^b q^e)) over the prime factorization of M. The exponent a² and the root of\n  unity ζ^{ab} are the coset data.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProduct.lean:1246`.\n\n  Pinned FLT: `Theorems/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.minpoly_jqN_map_eq_prod_slots",
      "zone": "F",
      "name": "ModularCurve.minpoly_jqN_map_eq_prod_slots",
      "display": "@ModularCurve.minpoly_jqN_map_eq_prod_slots",
      "card": "ModularCurve.minpoly_jqN_map_eq_prod_slots"
    },
    {
      "type": "prose",
      "md": "\n  ### `modularFunctionField_eq_full_of` — ModularCurve.modularFunctionField_eq_full_of\n\n  The one-prime reduction of Gen N: if every factorization N = M·p with p prime has j(q^M) ∈ F_N\n  and Gen M, then F_N = F_N^full.\n\n  Proof: the reverse inclusion is modularFunctionField_le_full. For the forward one, take j(q^d)\n  with d ∣ N, d ≠ N, write N = d·m, pick a prime p ∣ m and m = p·m′. Then N = (d m′)·p, so\n  j(q^{d m′}) ∈ F_N by hstep and Gen(d m′) is hgen; hence j(q^d) ∈ F_{d m′} ⊆ F_N.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean:220`.\n\n  Pinned FLT: `Theorems/Thm_ModularCurve_modularFunctionField_eq_full_of.lean`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.modularFunctionField_eq_full_of",
      "zone": "F",
      "name": "ModularCurve.modularFunctionField_eq_full_of",
      "display": "@ModularCurve.modularFunctionField_eq_full_of",
      "card": "ModularCurve.modularFunctionField_eq_full_of"
    },
    {
      "type": "prose",
      "md": "\n  ### `jqN_div_mem_modularFunctionField` — ModularCurve.jqN_div_mem_modularFunctionField\n\n  Descent by one prime: under the two slot hypotheses htw and hsp, j(q^M) lies in ℚ(j(q),\n  j(q^{Mp})). The hypotheses say: a common root of the pushed minimal polynomial that has the\n  shape j(w q^{M²p}) has w = 1 (htw), and the extra root j(q^{M²p³}) is not a common root (hsp).\n\n  Proof (T15): the unique-common-root principle. Take A = Φ_p(j(q^{Mp}), Y) and B = the push of\n  minpoly_ℚ(j)(j(q^M)) into F = ℚ(j(q), j(q^{Mp})); x₀ = j(q^M) is a common root by the modular\n  equation and by symmetry. The slot description lists all roots, and htw/hsp leave x₀ as the\n  only common one. Hence x₀ ∈ F. The tail strips the coefficient extension by injectivity of\n  coeffEmb and qExpand. The `lean` field abbreviates the two slot hypotheses with ⋯; the sheet's\n  `#check` is the full type.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean:74`.\n\n  Pinned FLT: `Theorems/Thm_ModularCurve_jqN_div_mem_modularFunctionField.lean`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.jqN_div_mem_modularFunctionField",
      "zone": "F",
      "name": "ModularCurve.jqN_div_mem_modularFunctionField",
      "display": "@ModularCurve.jqN_div_mem_modularFunctionField",
      "card": "ModularCurve.jqN_div_mem_modularFunctionField"
    },
    {
      "type": "prose",
      "md": "\n  ### `relfinrank_full_eq_mul` — ModularCurve.relfinrank_full_eq_mul\n\n  The relative degree of one full prime-power step is p + 1 for the first step (a = 0) and p for\n  later steps. This is the degree half of the induction (T16).\n\n  Proof: by the tower equality the step is a simple extension, so w1_relfinrank_insert reduces\n  to the degree of j(q^{p^{a+1}}) over the lower field. For a = 0 that degree is p + 1 (the\n  degree of Φ_p; irreducibility from a transitive automorphism cycling the p + 1 roots). For a ≥\n  1, Φ_p(j(q^{p^{a+1}}), Y) already has the root j(q^{p^a}) in the lower field, so it factors as\n  (Y − j(q^{p^a}))·P with deg P = p, and P is irreducible by a coefficient automorphism\n  argument.\n\n  Source: `lean/FLTForHuman/ModularCurve/FunctionFieldGeneration/DegreeStep.lean:433`.\n\n  Pinned FLT: `Theorems/Thm_ModularCurve_relfinrank_full_eq_mul.lean`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.relfinrank_full_eq_mul",
      "zone": "F",
      "name": "ModularCurve.relfinrank_full_eq_mul",
      "display": "@ModularCurve.relfinrank_full_eq_mul",
      "card": "ModularCurve.relfinrank_full_eq_mul"
    },
    {
      "type": "prose",
      "md": "\n  ### `exists_phiIrreducible_evalSymm` — ModularCurve.exists_phiIrreducible_evalSymm\n\n  At every prime ℓ there is a modular polynomial datum at level ℓ whose Φ is symmetric in its\n  two variables (and irreducible). Only monicity and the vanishing at (j(q), j(q^ℓ)) are used by\n  the integrality proof; symmetry is used by the descent and the slot product.\n\n  This is the classical prime-level splitting input, read as an existence statement: Φ_ℓ(j(u^ℓ\n  q^{ℓe}), Y) = (Y − j(u^{ℓ²}q^{ℓ²e})) ∏_{b<ℓ}(Y − j(u ζ_ℓ^b q^e)). The proof is in\n  ModularPolynomialProperties.lean (T12).\n\n  Source: `lean/FLTForHuman/ModularCurve/ModularPolynomialProperties.lean:138`.\n\n  Pinned FLT: `Theorems/Thm_ModularCurve_exists_phiIrreducible_evalSymm.lean`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.exists_phiIrreducible_evalSymm",
      "zone": "F",
      "name": "ModularCurve.exists_phiIrreducible_evalSymm",
      "display": "@ModularCurve.exists_phiIrreducible_evalSymm",
      "card": "ModularCurve.exists_phiIrreducible_evalSymm"
    },
    {
      "type": "prose",
      "md": "\n  ### `evalAtJGen_injective` — ModularCurve.evalAtJGen_injective\n\n  Evaluation ℤ[X] → ℚ(j), X ↦ j(q), is injective: j(q) is transcendental over ℚ. This is what\n  lets ℤ[j] be identified with a subring of ℚ(j).\n\n  The port proves it from the q^{-natDegree} coefficient of p(j(q)) being the leading\n  coefficient of p — the simple-pole triangularity — and uses it to transport injectivity from\n  the Laurent series into ℚ(j).\n\n  Source: `lean/FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean:106`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.evalAtJGen_injective",
      "zone": "F",
      "name": "ModularCurve.evalAtJGen_injective",
      "display": "@ModularCurve.evalAtJGen_injective",
      "card": "ModularCurve.evalAtJGen_injective"
    },
    {
      "type": "prose",
      "md": "\n  ### `algebraMap_comp_evalAtJGen` — ModularCurve.algebraMap_comp_evalAtJGen\n\n  The inclusion ℚ(j) ↪ ℚ((q)) composed with the evaluation ℤ[X] → ℚ(j) is exactly the evaluation\n  ℤ[X] → ℚ((q)): evaluating at j(q) and then viewing the result as a series is evaluating at\n  j(q) directly.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Fields.lean:100`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.algebraMap_comp_evalAtJGen",
      "zone": "F",
      "name": "ModularCurve.algebraMap_comp_evalAtJGen",
      "display": "@ModularCurve.algebraMap_comp_evalAtJGen",
      "card": "ModularCurve.algebraMap_comp_evalAtJGen"
    },
    {
      "type": "prose",
      "md": "\n  ### `jqN_one` — ModularCurve.jqN_one\n\n  j(q^1) = j(q).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Jq.lean:197`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.jqN_one",
      "zone": "F",
      "name": "ModularCurve.jqN_one",
      "display": "@ModularCurve.jqN_one",
      "card": "ModularCurve.jqN_one"
    },
    {
      "type": "prose",
      "md": "\n  ### `jqN_congr` — ModularCurve.jqN_congr\n\n  j(q^n) depends only on the level n: equal exponents give equal series.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Jq.lean:201`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.jqN_congr",
      "zone": "F",
      "name": "ModularCurve.jqN_congr",
      "display": "@ModularCurve.jqN_congr",
      "card": "ModularCurve.jqN_congr"
    },
    {
      "type": "prose",
      "md": "\n  ### `evalAtJ_X` — ModularCurve.evalAtJ_X\n\n  The polynomial X evaluates to j(q): X is a monic annihilator of j(q).\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Jq.lean:211`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.evalAtJ_X",
      "zone": "F",
      "name": "ModularCurve.evalAtJ_X",
      "display": "@ModularCurve.evalAtJ_X",
      "card": "ModularCurve.evalAtJ_X"
    },
    {
      "type": "prose",
      "md": "\n  ### `transcendental_jq` — ModularCurve.transcendental_jq\n\n  j(q) is transcendental over ℚ. The reason is the simple pole at q = 0: a nonzero polynomial\n  relation would have a leading coefficient that fails to vanish at the pole.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/Jq.lean:189`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.transcendental_jq",
      "zone": "F",
      "name": "ModularCurve.transcendental_jq",
      "display": "@ModularCurve.transcendental_jq",
      "card": "ModularCurve.transcendental_jq"
    },
    {
      "type": "prose",
      "md": "\n  ### `dedekindPsi_prime` — ModularCurve.dedekindPsi_prime\n\n  ψ(p) = p + 1: the modular equation at a prime has degree p + 1.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/DedekindPsi.lean:34`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.dedekindPsi_prime",
      "zone": "F",
      "name": "ModularCurve.dedekindPsi_prime",
      "display": "@ModularCurve.dedekindPsi_prime",
      "card": "ModularCurve.dedekindPsi_prime"
    },
    {
      "type": "prose",
      "md": "\n  ### `phiAtSeed_monic` — ModularCurve.phiAtSeed_monic\n\n  Φ(x, Y) is monic in Y, because Φ is monic in Y and evaluation of the X-variable preserves\n  monicity.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean:161`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.phiAtSeed_monic",
      "zone": "F",
      "name": "ModularCurve.phiAtSeed_monic",
      "display": "@ModularCurve.phiAtSeed_monic",
      "card": "ModularCurve.phiAtSeed_monic"
    },
    {
      "type": "prose",
      "md": "\n  ### `phiAtSeed_map` — ModularCurve.phiAtSeed_map\n\n  Φ(x, Y) is natural in the coefficient ring: pushing the polynomial along a ring map f is the\n  same as evaluating X at f(x) in the target.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean:151`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.phiAtSeed_map",
      "zone": "F",
      "name": "ModularCurve.phiAtSeed_map",
      "display": "@ModularCurve.phiAtSeed_map",
      "card": "ModularCurve.phiAtSeed_map"
    },
    {
      "type": "prose",
      "md": "\n  ### `phiAtSeed_jqN_eval` — ModularCurve.phiAtSeed_jqN_eval\n\n  Φ(j(q^M), j(q^{Mn})) = 0: substituting q ↦ q^M into the modular equation Φ(j(q), j(q^n)) = 0\n  gives a vanishing at the corresponding pair of levels.\n\n  Source: `lean/FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean:187`.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.phiAtSeed_jqN_eval",
      "zone": "F",
      "name": "ModularCurve.phiAtSeed_jqN_eval",
      "display": "@ModularCurve.phiAtSeed_jqN_eval",
      "card": "ModularCurve.phiAtSeed_jqN_eval"
    },
    {
      "type": "prose",
      "md": "\n  ### mathlib lemmas used\n\n  The statement below is the compiler's, via `#check`.\n",
      "zone": "F"
    },
    {
      "type": "prose",
      "md": "\n  ### `induction_on_primes` — induction_on_primes\n\n  Induction on the multiplicative structure of ℕ: the base cases 0 and 1, and a step that\n  multiplies an arbitrary level by a prime.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/Data/Nat/Factorization/Induction.lean#L84>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @induction_on_primes",
      "zone": "F",
      "name": "induction_on_primes",
      "display": "@induction_on_primes",
      "card": "induction_on_primes"
    },
    {
      "type": "prose",
      "md": "\n  ### `isIntegral_algebraMap` — isIntegral_algebraMap\n\n  Every element of the image of the base ring is integral; X is its own monic annihilator.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean#L33>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @isIntegral_algebraMap",
      "zone": "F",
      "name": "isIntegral_algebraMap",
      "display": "@isIntegral_algebraMap",
      "card": "isIntegral_algebraMap"
    },
    {
      "type": "prose",
      "md": "\n  ### `IsIntegral.fg_adjoin_singleton` — IsIntegral.fg_adjoin_singleton\n\n  Adjoining a single integral element produces a finitely generated module: if x is integral\n  over R, then R[x] is a finite R-module.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean#L104>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @IsIntegral.fg_adjoin_singleton",
      "zone": "F",
      "name": "IsIntegral.fg_adjoin_singleton",
      "display": "@IsIntegral.fg_adjoin_singleton",
      "card": "IsIntegral.fg_adjoin_singleton"
    },
    {
      "type": "prose",
      "md": "\n  ### `IsIntegral.of_mem_of_fg` — IsIntegral.of_mem_of_fg\n\n  If a subalgebra S is finitely generated as an R-module, every element of S is integral over R.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean#L81>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @IsIntegral.of_mem_of_fg",
      "zone": "F",
      "name": "IsIntegral.of_mem_of_fg",
      "display": "@IsIntegral.of_mem_of_fg",
      "card": "IsIntegral.of_mem_of_fg"
    },
    {
      "type": "prose",
      "md": "\n  ### `isIntegral_algHom_iff` — isIntegral_algHom_iff\n\n  An injective R-algebra map reflects integrality: x is integral over R exactly when its image\n  is.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean#L79>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @isIntegral_algHom_iff",
      "zone": "F",
      "name": "isIntegral_algHom_iff",
      "display": "@isIntegral_algHom_iff",
      "card": "isIntegral_algHom_iff"
    },
    {
      "type": "prose",
      "md": "\n  ### `isIntegral_trans` — isIntegral_trans\n\n  Transitivity of integrality: if A is integral over R and x is integral over A, then x is\n  integral over R.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean#L477>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @isIntegral_trans",
      "zone": "F",
      "name": "isIntegral_trans",
      "display": "@isIntegral_trans",
      "card": "isIntegral_trans"
    },
    {
      "type": "prose",
      "md": "\n  ### `IsIntegral.tower_top` — IsIntegral.tower_top\n\n  Enlarging the base ring preserves integrality: integral over R implies integral over any\n  R-algebra A in a scalar tower.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean#L158>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @IsIntegral.tower_top",
      "zone": "F",
      "name": "IsIntegral.tower_top",
      "display": "@IsIntegral.tower_top",
      "card": "IsIntegral.tower_top"
    },
    {
      "type": "prose",
      "md": "\n  ### `minpoly.isIntegrallyClosed_eq_field_fractions'` — minpoly.isIntegrallyClosed_eq_field_fractions'\n\n  Over an integrally closed base ring R with fraction field K, the minimal polynomial over K is\n  the image of the minimal polynomial over R.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/FieldTheory/Minpoly/IsIntegrallyClosed.lean#L57>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @minpoly.isIntegrallyClosed_eq_field_fractions'",
      "zone": "F",
      "name": "minpoly.isIntegrallyClosed_eq_field_fractions'",
      "display": "@minpoly.isIntegrallyClosed_eq_field_fractions'",
      "card": "minpoly.isIntegrallyClosed_eq_field_fractions'"
    },
    {
      "type": "prose",
      "md": "\n  ### `minpoly.monic` — minpoly.monic\n\n  A minimal polynomial of an integral element is monic.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/FieldTheory/Minpoly/Basic.lean#L54>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @minpoly.monic",
      "zone": "F",
      "name": "minpoly.monic",
      "display": "@minpoly.monic",
      "card": "minpoly.monic"
    },
    {
      "type": "prose",
      "md": "\n  ### `minpoly.aeval` — minpoly.aeval\n\n  The defining property of the minimal polynomial: it annihilates its element.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/FieldTheory/Minpoly/Basic.lean#L89>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @minpoly.aeval",
      "zone": "F",
      "name": "minpoly.aeval",
      "display": "@minpoly.aeval",
      "card": "minpoly.aeval"
    },
    {
      "type": "prose",
      "md": "\n  ### `minpoly.irreducible` — minpoly.irreducible\n\n  The minimal polynomial of an element over a field is irreducible.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/FieldTheory/Minpoly/Basic.lean#L269>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @minpoly.irreducible",
      "zone": "F",
      "name": "minpoly.irreducible",
      "display": "@minpoly.irreducible",
      "card": "minpoly.irreducible"
    },
    {
      "type": "prose",
      "md": "\n  ### `IntermediateField.adjoin.finrank` — IntermediateField.adjoin.finrank\n\n  The degree of a simple extension equals the degree of the minimal polynomial: [K(x) : K] =\n  deg(minpoly_K x).\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean#L489>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @IntermediateField.adjoin.finrank",
      "zone": "F",
      "name": "IntermediateField.adjoin.finrank",
      "display": "@IntermediateField.adjoin.finrank",
      "card": "IntermediateField.adjoin.finrank"
    },
    {
      "type": "prose",
      "md": "\n  ### `IsLocalization.integerNormalization_spec` — IsLocalization.integerNormalization_spec\n\n  Denominator clearing: for a localized ring S and a polynomial p over S, some integer multiple\n  of p (by an element b of the localization submonoid) comes from a polynomial over R, namely\n  integerNormalization p.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/RingTheory/Localization/Integral.lean#L53>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @IsLocalization.integerNormalization_spec",
      "zone": "F",
      "name": "IsLocalization.integerNormalization_spec",
      "display": "@IsLocalization.integerNormalization_spec",
      "card": "IsLocalization.integerNormalization_spec"
    },
    {
      "type": "prose",
      "md": "\n  ### `IntermediateField.mem_adjoin_simple_iff` — IntermediateField.mem_adjoin_simple_iff\n\n  Every element of a simple extension F(α) is a quotient of two polynomial expressions in α over\n  F.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean#L61>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @IntermediateField.mem_adjoin_simple_iff",
      "zone": "F",
      "name": "IntermediateField.mem_adjoin_simple_iff",
      "display": "@IntermediateField.mem_adjoin_simple_iff",
      "card": "IntermediateField.mem_adjoin_simple_iff"
    },
    {
      "type": "prose",
      "md": "\n  ### `Polynomial.eval₂_eq_eval_map` — Polynomial.eval₂_eq_eval_map\n\n  Evaluating with a coefficient map f at x is evaluating the mapped polynomial at x.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/Algebra/Polynomial/Eval/Defs.lean#L565>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @Polynomial.eval₂_eq_eval_map",
      "zone": "F",
      "name": "Polynomial.eval₂_eq_eval_map",
      "display": "@Polynomial.eval₂_eq_eval_map",
      "card": "Polynomial.eval₂_eq_eval_map"
    },
    {
      "type": "prose",
      "md": "\n  ### `Polynomial.aeval_def` — Polynomial.aeval_def\n\n  Algebra evaluation is evaluation with the algebra map as coefficient map.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/Algebra/Polynomial/AlgebraMap.lean#L273>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @Polynomial.aeval_def",
      "zone": "F",
      "name": "Polynomial.aeval_def",
      "display": "@Polynomial.aeval_def",
      "card": "Polynomial.aeval_def"
    },
    {
      "type": "prose",
      "md": "\n  ### `Polynomial.Monic.natDegree_map` — Polynomial.Monic.natDegree_map\n\n  Mapping a monic polynomial along a ring hom preserves its degree.\n\n  Source: <https://github.com/leanprover-community/mathlib4/blob/5ed2965/Mathlib/Algebra/Polynomial/Monic.lean#L397>.\n",
      "zone": "F"
    },
    {
      "type": "check",
      "raw": "#check @Polynomial.Monic.natDegree_map",
      "zone": "F",
      "name": "Polynomial.Monic.natDegree_map",
      "display": "@Polynomial.Monic.natDegree_map",
      "card": "Polynomial.Monic.natDegree_map"
    },
    {
      "type": "prose",
      "md": "  what is plumbing and what is mathematics\n\n  Four formal devices recur; none carries mathematical content.\n\n  **Instances and positivity.** Every level is a natural number with a `NeZero` instance. The\n  substitution q ↦ q^0 is the zero map, and j(q^0) is not a q-expansion, so the level must be\n  positive. The `NeZero` arguments are discharged by `NeZero.ne` or built from `NeZero (p·a)`;\n  they are not hypotheses of the mathematics.\n\n  **`eval₂` versus `aeval`.** The port evaluates integer polynomials with `evalAtJ`, a ring hom\n  ℤ[X] → ℚ((q)). Mathlib's `aeval` uses the algebra structure instead. The bridges\n  `aeval_map_intCast` and `algebraMap_comp_evalAtJGen` make the two agree, and the two\n  `letI := ....toAlgebra` lines in the fraction-field proof install the algebra structures that\n  `minpoly` and `IsIntegral` expect.\n\n  **Private helpers.** `coe_evalAtJGen`, `aeval_map_intCast` and `evalAtJ_C` are `private` to\n  Capstone.lean and cannot be `#check` ed from another module. This sheet exhibits their\n  statements as closed Lean propositions ( `#check (… : Prop)`), which typecheck against the\n  public API without naming the private declarations.\n\n  **Orientation.** The two function fields are equated in both orientations in the sources.\n  `Gen d` is F_d = F_d^full; the collapse equivalence is stated with F_N^full on the left.\n  Rewriting the wrong way is the most common failure mode in this file, so each equality above\n  records which orientation the proof uses.\n",
      "zone": "G"
    },
    {
      "type": "prose",
      "md": "\n  End of the presentation.\n\n  Every mathematical claim above is either the statement of a declaration in the\n  imported module (exhibited by #check/#print) or a step of the semi-formal proof\n  that cites such a declaration. The JSON source is the document; this sheet is a\n  projection of it.\n",
      "zone": "G"
    },
    {
      "type": "code",
      "text": "end",
      "zone": "G"
    }
  ],
  "bound": [],
  "seed_cards": ["Eq.mpr","IntermediateField.adjoin.finrank","IntermediateField.mem_adjoin_simple_iff","IntermediateField.relfinrank","IsIntegral","IsIntegral.fg_adjoin_singleton","IsIntegral.of_mem_of_fg","IsIntegral.tower_top","IsLocalization.integerNormalization_spec","ModularCurve.FunctionFieldGeneration","ModularCurve.Gen","ModularCurve.Hall","ModularCurve.Inputs","ModularCurve.ModularPolynomialData","ModularCurve.ModularPolynomialData.toAdjoin","ModularCurve.PhiIrreducible","ModularCurve.Tight","ModularCurve.algebraMap_comp_evalAtJGen","ModularCurve.coeffEmb","ModularCurve.dedekindPsi","ModularCurve.dedekindPsi_prime","ModularCurve.evalAtJ","ModularCurve.evalAtJGen","ModularCurve.evalAtJGen_injective","ModularCurve.evalAtJ_X","ModularCurve.exists_monic_evalAtJ_jqN_eq_zero","ModularCurve.exists_phiIrreducible","ModularCurve.exists_phiIrreducible_evalSymm","ModularCurve.exists_phiIrreducible_of_finrank_eq","ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi","ModularCurve.full_eq_adjoin_full_div_prime","ModularCurve.functionFieldGeneration","ModularCurve.functionFieldGeneration_iff_full_eq","ModularCurve.functionFieldGeneration_of","ModularCurve.hall_all","ModularCurve.inputs","ModularCurve.jq","ModularCurve.jqN","ModularCurve.jqN_congr","ModularCurve.jqN_div_mem_modularFunctionField","ModularCurve.jqN_one","ModularCurve.jqN_pow_not_mem_adjoin_full","ModularCurve.jqN_prime_not_mem_full","ModularCurve.minpoly_jqN_map_eq_prod_slots","ModularCurve.modularFunctionField","ModularCurve.modularFunctionFieldFull","ModularCurve.modularFunctionField_eq_full","ModularCurve.modularFunctionField_eq_full_of","ModularCurve.nonempty_modularPolynomialData","ModularCurve.phiAtSeed","ModularCurve.phiAtSeed_jqN_eval","ModularCurve.phiAtSeed_map","ModularCurve.phiAtSeed_monic","ModularCurve.qExpand","ModularCurve.qTwist","ModularCurve.relfinrank_full_eq_dedekindPsi","ModularCurve.relfinrank_full_eq_mul","ModularCurve.relfinrank_modularFunctionField","ModularCurve.transcendental_jq","NeZero","NeZero.ne","Polynomial.Monic.natDegree_map","Polynomial.aeval","Polynomial.aeval_def","Polynomial.eval₂","Polynomial.eval₂_eq_eval_map","Polynomial.eval₂_map","RingHom.congr_fun","RingHom.ext_int","Subtype.ext","congrArg","dedekindPsi","dedekindPsi_prime","induction_on_primes","isIntegral_algHom_iff","isIntegral_algebraMap","isIntegral_trans","minpoly","minpoly.aeval","minpoly.irreducible","minpoly.isIntegrallyClosed_eq_field_fractions'","minpoly.monic"],
  "card_count": 181,
  "modules": ["FLTForHuman.ModularCurve.Defs.DedekindPsi","FLTForHuman.ModularCurve.Defs.Fields","FLTForHuman.ModularCurve.Defs.Jq","FLTForHuman.ModularCurve.Defs.Laurent","FLTForHuman.ModularCurve.Defs.PhiAtSlot","FLTForHuman.ModularCurve.Defs.PhiGen","FLTForHuman.ModularCurve.Defs.Polynomial","FLTForHuman.ModularCurve.Defs.Twist","FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone","FLTForHuman.ModularCurve.FunctionFieldGeneration.Collapse","FLTForHuman.ModularCurve.FunctionFieldGeneration.DegreeStep","FLTForHuman.ModularCurve.FunctionFieldGeneration.Descent","FLTForHuman.ModularCurve.FunctionFieldGeneration.Generation","FLTForHuman.ModularCurve.FunctionFieldGeneration.Nonmembership","FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct","FLTForHuman.ModularCurve.FunctionFieldGeneration.Spine","FLTForHuman.ModularCurve.FunctionFieldGeneration.Target","FLTForHuman.ModularCurve.ModularPolynomialIrreducible","FLTForHuman.ModularCurve.ModularPolynomialProperties","FLTForHuman.NumberTheory.DedekindPsi","Init.Classical","Init.Core","Init.Data.Cast","Init.Data.Function","Init.Data.Int.Basic","Init.Data.Nat.Gcd","Init.Data.NeZero","Init.Data.Rat.Basic","Init.Data.Zero","Init.Prelude","Mathlib.Algebra.Algebra.Defs","Mathlib.Algebra.Algebra.Hom","Mathlib.Algebra.Algebra.Subalgebra.Basic","Mathlib.Algebra.Algebra.Subalgebra.Lattice","Mathlib.Algebra.BigOperators.Group.Finset.Defs","Mathlib.Algebra.Field.Defs","Mathlib.Algebra.Group.Action.Defs","Mathlib.Algebra.Group.Hom.Defs","Mathlib.Algebra.Group.Irreducible.Defs","Mathlib.Algebra.Group.Submonoid.Defs","Mathlib.Algebra.Group.Units.Defs","Mathlib.Algebra.Module.Submodule.Defs","Mathlib.Algebra.Order.IsBotOne","Mathlib.Algebra.Polynomial.AlgebraMap","Mathlib.Algebra.Polynomial.Basic","Mathlib.Algebra.Polynomial.Degree.Defs","Mathlib.Algebra.Polynomial.Eval.Coeff","Mathlib.Algebra.Polynomial.Eval.Defs","Mathlib.Algebra.Polynomial.Monic","Mathlib.Algebra.Ring.Basic","Mathlib.Algebra.Ring.Defs","Mathlib.Algebra.Ring.Hom.Defs","Mathlib.Algebra.Squarefree.Basic","Mathlib.Basic.Logic.Basic","Mathlib.Basic.Nontrivial.Defs","Mathlib.Data.Finset.Filter","Mathlib.Data.Finset.Range","Mathlib.Data.Int.Cast.Lemmas","Mathlib.Data.Nat.Factorization.Induction","Mathlib.Data.Nat.Prime.Defs","Mathlib.Data.Rat.Defs","Mathlib.Data.Set.Defs","Mathlib.FieldTheory.IntermediateField.Adjoin.Basic","Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","Mathlib.FieldTheory.IntermediateField.Basic","Mathlib.FieldTheory.Minpoly.Basic","Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed","Mathlib.FieldTheory.Relrank","Mathlib.LinearAlgebra.Dimension.Finrank","Mathlib.Logic.Equiv.Defs","Mathlib.NumberTheory.Divisors","Mathlib.Order.Hom.Basic","Mathlib.Order.TypeTags","Mathlib.Order.WellFounded","Mathlib.RingTheory.Algebraic.Defs","Mathlib.RingTheory.Finiteness.Defs","Mathlib.RingTheory.HahnSeries.Basic","Mathlib.RingTheory.HahnSeries.Multiplication","Mathlib.RingTheory.HahnSeries.PowerSeries","Mathlib.RingTheory.IntegralClosure.Algebra.Basic","Mathlib.RingTheory.IntegralClosure.Algebra.Defs","Mathlib.RingTheory.IntegralClosure.IntegrallyClosed","Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic","Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs","Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic","Mathlib.RingTheory.LaurentSeries","Mathlib.RingTheory.Localization.Defs","Mathlib.RingTheory.Localization.FractionRing","Mathlib.RingTheory.Localization.Integral","Mathlib.RingTheory.PowerSeries.Basic","Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots"]
};
