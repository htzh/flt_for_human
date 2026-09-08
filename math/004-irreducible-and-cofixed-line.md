# Irreducibility and the cofixed line — how the mod-$p$ representation is excluded without ever being named

Companion to [note 003](003-galois-rep-irreducible-in-english.md) (the
`GaloisRepIsIrreducible` predicate). The irreducibility leg of the proof,
`FreyPackage.Mazur_Frey`, is proved by contradiction, and the contradiction
is mediated by a second predicate, `HasGaloisStableCofixedLine`. Here:
(1) the two predicates side by side, in English; (2) the exact logical
relationship between them (reducible ⇒ cofixed line, and the contrapositive
the proof actually uses); (3) the details of how the cofixed-line detour lets
this whole step avoid ever referring to a *representation* — no
`Representation` structure, no basis of $`E_P[p]`$, no $\mathrm{GL}_2(\mathbb{F}_p)$ —
continuing the pattern of note 003's GL₂ aside. Line numbers refer to
`anthropics/fermats-last-theorem@aa2d8b3` (main, 2026-09-03); Mathlib line
numbers refer to tag v4.33.0.

## 1. The two predicates, side by side

`GaloisRepIsIrreducible` (note 003,
[Def_FLTPrelim_GaloisRep.lean, lines 74–77](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean))
says the $n$-torsion is nontrivial and has no Galois-stable
$\mathbb{Z}/n$-submodule other than $\bot$ and $\top$. The cofixed-line
predicate lives in its own module
([Def_FLTPrelim_CofixedLine.lean, lines 13–18](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_CofixedLine.lean)):

```lean
variable (S K) in
def HasGaloisStableCofixedLine (W' : Affine R) (n : ℕ) : Prop :=
  ∃ N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n),
    IsGaloisStable S N ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧
      ∀ σ : K ≃ₐ[S] K, ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x - x ∈ N
```

In English: there is a submodule $N$ of the $n$-torsion
$`M = (W'\!\!\mathbin{/}K).Point[n]`$ such that

- $N$ is Galois-stable, proper ($N \neq \top$), and nonzero ($N \neq \bot$); and
- for **every** automorphism $\sigma$ and **every** torsion point $x \in M$
  (not just $x \in N$), $\sigma \cdot x - x \in N$.

The second clause says the action $\sigma$ induces on the quotient $M/N$ is
**trivial**: in $M/N$, $\sigma \cdot \bar x = \bar x$. A "cofixed line" is a
stable submodule with trivially-acted-on quotient.

Three remarks on the shape of this definition (all confirmed by the generated
def page):

1. **The stability clause is redundant.** If $\sigma \cdot x - x \in N$ for
   all $x$, then for $x \in N$ also
   $\sigma \cdot x = x + (\sigma \cdot x - x) \in N$. It is recorded anyway,
   so that a cofixed line is visibly a submodule of the kind
   `GaloisRepIsIrreducible` quantifies over.
2. **"Line" is only a name.** No rank condition is imposed. In the intended
   application $n = p$ is prime and $\operatorname{card} M = p^2$
   (`WeierstrassCurve.card_torsion_of_isAlgClosed`,
   [Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean, line 9](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)),
   and then a proper nonzero $\mathbb{Z}/p$-submodule of a $p^2$-element
   group has order $p$ — literally a line. The definition is stated for
   general $n$ and never uses the count.
3. **The acting group is the full automorphism group** $K \simeq_{\mathrm{alg}[S]} K$,
   with no hypothesis that $K/S$ is Galois. At $S = \mathbb{Q}$,
   $K = \overline{\mathbb{Q}}$ this is the absolute Galois group, acting on
   points by `Point.map` as in note 003.

## 2. The relationship: reducible ⇒ cofixed line (Serre's observation)

The bridge is one theorem,
`FreyPackage.frey_reducible_hasCofixedLine`
([Thm_FreyPackage_frey_reducible_hasCofixedLine.lean, line 15](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_reducible_hasCofixedLine.lean)):

```lean
theorem FreyPackage.frey_reducible_hasCofixedLine (P : FreyPackage)
    (hred : ¬ GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p) :
    HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p
```

and its proof is short enough to quote whole
([S_FreyPackage_frey_reducible_hasCofixedLine.lean, lines 43–52](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_reducible_hasCofixedLine.lean)):

```lean
  unfold GaloisRepIsIrreducible at hred
  push Not at hred
  obtain ⟨N, hN, hbot, htop⟩ := hred hnt
  refine ⟨N, hN, hbot, htop, ?_⟩

  rcases P.frey_stable_submodule_fixed_or_cofixed N hN hbot htop with hfix | hcofix
  · exfalso
    obtain ⟨x, hxN, hx0⟩ := (Submodule.ne_bot_iff N).mp hbot
    exact hx0 (P.frey_torsion_fixed_eq_zero x (fun σ => hfix σ x hxN))
  · exact hcofix
```

Reading it: `push Not` turns "not irreducible" into "a proper nonzero stable
submodule $N$ exists" (the nontriviality half of the predicate holds anyway,
using $\operatorname{card} E_P[p] = p^2$). Then the proof splits on a
**Frey-curve-specific dichotomy**,
`FreyPackage.frey_stable_submodule_fixed_or_cofixed`
([Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean, line 10](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean)):
any proper nonzero stable $N$ in $`E_P[p]`$ is either

- **pointwise fixed** — $\sigma \cdot x = x$ for all $\sigma$ and all $x \in N$; or
- **cofixed** — $\sigma \cdot x - x \in N$ for all $\sigma$ and all $x \in M$.

The fixed branch dies immediately: a fixed nonzero $x \in N$ would be a
rational point of order $p$, and the Frey curve has none
(`FreyPackage.frey_torsion_fixed_eq_zero`,
[Thm_FreyPackage_frey_torsion_fixed_eq_zero.lean, line 8](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_torsion_fixed_eq_zero.lean),
reducing to
[`FreyPackage.freyCurve_rational_p_torsion_eq_zero`, line 7](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean)).
Only the cofixed branch survives — hence `reducible ⇒ cofixed line`.

The dichotomy is where the Frey curve's arithmetic enters: its proof module
imports exactly
([S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean, lines 1–7](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean))
that $`E_P[p]`$ is unramified away from $2p$
(`freyGaloisRep_isUnramifiedAt`), that inertia at $2$ acts trivially on a
stable submodule, that inertia at $p$ acts trivially on the submodule or on
the quotient, and two closure lemmas turning inertia-triviality into global
triviality. Semistability of the Frey curve is what buys these.

## 3. The contrapositive at work: `Mazur_Frey`

What the proof needs is the **contrapositive**: no cofixed line ⇒
irreducible. The main theorem of step 3,
`FreyPackage.Mazur_Frey`
([Thm_FreyPackage_Mazur_Frey.lean, line 70](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_Mazur_Frey.lean)),
is exactly that argument, run in two cases
([S_FreyPackage_Mazur_Frey.lean, lines 77–91](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_Mazur_Frey.lean)):

```lean
private theorem mazurM3asmB_of_no_cofixed (P : FreyPackage) :
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by
  by_contra hred
  have hN : HasGaloisStableCofixedLine (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p :=
    FreyPackage.frey_reducible_hasCofixedLine P hred
  rcases mazurM3asmB_exponent_trichotomy P.p P.pp P.hp5 with hsmall | h11 | h17
  · exact FreyPackage.frey_no_cofixed_small P hsmall hN
  · exact FreyPackage.frey_no_cofixed_eleven P h11 hN
  · exact FreyPackage.frey_no_cofixed_large P h17 hN

theorem solution (P : FreyPackage) :
    GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p := by
  rcases em ((P.a : ZMod 8) = 3) with h8 | _
  · exact FreyPackage.Mazur_Frey_of_a_mod_eight P h8
  · exact mazurM3asmB_of_no_cofixed P
```

So `Mazur_Frey` = "reducible ⇒ cofixed line" followed by "no cofixed line is
possible", with the second half supplied case by case:

| Case | Theorem excluding the cofixed line | Nature of the argument |
|---|---|---|
| $a \equiv 3 \pmod 8$ | `frey_no_cofixed_of_a_mod_eight` ([line 12](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_no_cofixed_of_a_mod_eight.lean)) | its own argument at the prime $2$; the same shape: `by_contra` → cofixed line → contradiction ([S_FreyPackage_Mazur_Frey_of_a_mod_eight.lean, lines 14–19](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_Mazur_Frey_of_a_mod_eight.lean)) |
| $p \in \{5, 7, 13\}$ | `frey_no_cofixed_small` ([line 13](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_no_cofixed_small.lean)) | **vacuous**: FLT for these exponents is already proved, so $P$ cannot exist ([S file, lines 27–29](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_no_cofixed_small.lean)) |
| $p = 11$ | `frey_no_cofixed_eleven` ([line 13](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_no_cofixed_eleven.lean)) | likewise vacuous, via `fermatLastTheoremEleven` |
| $p \geq 17$ | `frey_no_cofixed_large` ([line 70](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_no_cofixed_large.lean)) | the real content: Mazur's Eisenstein-ideal argument (PROOF-PATH.md, step 3) |

## 4. The payoff: no representation, no $\mathrm{GL}_2$

Note 003's aside observed that the *predicate* `GaloisRepIsIrreducible` never
chooses a basis. The cofixed-line detour continues this one level down: the
entire irreducibility step — hypothesis, intermediate objects, and
contradictions — is carried out without ever referring to a representation.

1. **The objects are bare submodules.** `HasGaloisStableCofixedLine`
   quantifies over a submodule $N$ and points $x$, with clauses
   $\sigma \cdot x \in N$ and $\sigma \cdot x - x \in N$. No
   `Representation` structure, no $\mathbb{F}_p$-dimension, no
   $\operatorname{GL}_2$; the module does not even assume
   $\operatorname{card} E[p] = p^2$ (that count enters only at the proof of
   nontriviality, §2). Its imports are just the Frey package and the Galois
   action
   ([Def_FLTPrelim_CofixedLine.lean, lines 1–2](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_CofixedLine.lean)).
2. **The only matrix-like invariant used is $\det$, taken of a module
   endomorphism, never of a matrix.** The Galois action is repackaged as a
   monoid hom into endomorphisms,
   `galoisRepModuleEnd : (K ≃ₐ[S] K) →* Module.End (ZMod n) (torsionBy …)`
   ([Def_EllipticCurve_FrobeniusTrace.lean, lines 25–27](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusTrace.lean),
   built on Mathlib's `DistribMulAction.toModuleEnd`,
   [LinearMap/End.lean, line 250, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/LinearMap/End.lean)).
   Everything the cofixed step needs about "characters" is then extracted
   from `LinearMap.det` of that endomorphism:
   - on a cofixed line, $\sigma$ acts on $N$ **by the scalar $\det \sigma$** —
     `WeierstrassCurve.smul_eq_det_smul_of_cofixed`
     ([Thm_WeierstrassCurve_smul_eq_det_smul_of_cofixed.lean, lines 10–21](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_smul_eq_det_smul_of_cofixed.lean));
   - $\det \sigma$ is the mod-$p$ **cyclotomic character** — on $p$-power
     roots of unity, $\sigma \zeta = \zeta^{\det \sigma}$
     (`WeierstrassCurve.apply_eq_pow_det_galoisRep_of_pow_eq_one`,
     [line 10](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one.lean));
   these are exactly the two inputs the $p \geq 17$ argument imports.
3. **The actual `Representation` lives on the automorphic side.** The
   packaged representation `WeierstrassCurve.residualGaloisRepOf`
   ([Def_GaloisRep_Residual.lean, lines 87–88](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean))
   takes $\operatorname{card} E[p] = p^2$ as an explicit hypothesis `hcard`
   and feeds modularity and level lowering; `GL (Fin 2)` appears only in
   adelic/automorphic files (note 003, §5). The two worlds meet through the
   equivalence
   `ResidualGaloisRep.IsIrreducible ↔ GaloisRepIsIrreducible`, cited in note
   003 — so `Mazur_Frey`, proved entirely in basis-free submodule language,
   still feeds the representation-valued machine downstream.

For a human reader, the matrix picture of a cofixed line is: choose a basis
of $`E[p] \cong \mathbb{F}_p^2`$ whose first vector spans $N$; then "cofixed"
says
$\bar\rho(\sigma) = \begin{pmatrix} \chi(\sigma) & b(\sigma) \\ 0 & 1 \end{pmatrix}$,
i.e. the quotient character is trivial, and on $N$ the action is
$\chi(\sigma) = \det \bar\rho(\sigma) = \chi_p(\sigma)$, the cyclotomic
character. The formalization never chooses this basis: "stable line with
trivial quotient action, scalar $\det$ on the line" is stated and used
directly, so the basis — and with it any explicit
$\mathrm{GL}_2(\mathbb{F}_p)$-valued representation — never has to exist in
the irreducibility step at all.

## 5. Key-point → code map

| Key point | Mathematical content | Where in the code |
|---|---|---|
| cofixed line, in English | proper nonzero stable $\mathbb{Z}/n$-submodule $N \subseteq M = (W'/K).Point[n]$ with $\sigma \cdot x - x \in N$ for all $x \in M$ — trivial action on $M/N$ | [Def_FLTPrelim_CofixedLine.lean:15–18](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_CofixedLine.lean) |
| "line" is only a name | no rank hypothesis; order $p$ follows from $\operatorname{card} M = p^2$ when needed | Def_FLTPrelim_CofixedLine.lean:15–18; [Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean:9](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean) |
| reducible ⇒ cofixed | negating irreducibility gives stable $N$; Frey dichotomy: $N$ fixed or cofixed; fixed dies (no rational $p$-torsion) | [Thm_FreyPackage_frey_reducible_hasCofixedLine.lean:15](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_reducible_hasCofixedLine.lean); [S file:43–52](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_reducible_hasCofixedLine.lean) |
| the dichotomy is Frey-specific | unramified away from $2p$; inertia at $2$ trivial on $N$; inertia at $p$ trivial on $N$ or $M/N$ | [Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean:10](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean); [S file imports:1–7](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean) |
| `Mazur_Frey` = no cofixed line | case split $a \equiv 3 \pmod 8$ (own 2-adic argument) + trichotomy $p \in \{5,7,13\}$ / $11$ (vacuous) / $\geq 17$ (Eisenstein ideal) | [Thm_FreyPackage_Mazur_Frey.lean:70](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_Mazur_Frey.lean); [S file:77–91](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_Mazur_Frey.lean) |
| no representation named | predicates quantify over submodules/points; no `Representation`, no basis, no `hcard` in the cofixed module | [Def_FLTPrelim_CofixedLine.lean:1–2, 15–18](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_CofixedLine.lean) |
| $\det$ as the only "character" | $\sigma\|_N = \det \sigma$; $\det \sigma$ = mod-$p$ cyclotomic; both taken of `galoisRepModuleEnd` (an `End`-hom), never of a matrix | [Thm_WeierstrassCurve_smul_eq_det_smul_of_cofixed.lean:10–21](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_smul_eq_det_smul_of_cofixed.lean); [Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one.lean:10](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one.lean); [Def_EllipticCurve_FrobeniusTrace.lean:25–27](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusTrace.lean) |
| where the real $\bar\rho$ lives | `residualGaloisRepOf` with explicit `hcard`, feeding the automorphic side; `GL (Fin 2)` automorphic only | [Def_GaloisRep_Residual.lean:87–88](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean); note 003, §5 |

## 6. Links

Lean sources (raw; quote line numbers as above):

- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_CofixedLine.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_EllipticCurve_FrobeniusTrace.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_Mazur_Frey.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_Mazur_Frey_of_a_mod_eight.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_reducible_hasCofixedLine.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_torsion_fixed_eq_zero.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_freyCurve_rational_p_torsion_eq_zero.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_no_cofixed_small.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_no_cofixed_eleven.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_no_cofixed_large.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_no_cofixed_of_a_mod_eight.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_smul_eq_det_smul_of_cofixed.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_apply_eq_pow_det_galoisRep_of_pow_eq_one.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_Mazur_Frey.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_reducible_hasCofixedLine.lean>

Annotated docs (viewable):

- [Def page: FLTPrelim_CofixedLine](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_CofixedLine.html)
- [Def page: FLTPrelim_GaloisRep](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_GaloisRep.html)
- [Route §3: irreducibility](https://tianyipeng.github.io/fermats-last-theorem/route/s3.html)
- [PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/PROOF-PATH.md) (step 3)

Mathlib v4.33.0 (the rev pinned in `lake-manifest.json`):

- [`Submodule.torsionBy`, Torsion/Basic.lean (line 178)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Torsion/Basic.lean)
- [`AddCommGroup.zmodModule`, ZMod.lean (line 44)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/ZMod.lean)
- [`Module.End` and `DistribMulAction.toModuleEnd`, LinearMap/End.lean (lines 32, 250)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/LinearMap/End.lean)

Background:

- J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes
  elliptiques*, Invent. Math. 15 (1972), 259–331 (the fixed-or-cofixed
  observation; reference listed on the generated def page).
- H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, Current
  Developments in Mathematics 1995, §2 (the route the proof follows).
- Upstream ICL FLT — the Galois-action and torsion-module setup is ported
  from [FLT/EllipticCurve/Torsion.lean](https://github.com/ImperialCollegeLondon/FLT/blob/main/FLT/EllipticCurve/Torsion.lean)
  (see note 003); `HasGaloisStableCofixedLine` itself is the project's own
  predicate (Mathlib has no notion of stable/cofixed torsion submodule).
