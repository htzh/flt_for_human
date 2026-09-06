# `GaloisRepIsIrreducible` in English — and why the general `Affine R` accepts the Frey curve

Companion to [note 001](001-frey-package-wlog.md) (the WLOG normalization) and
[note 002](002-frey-curve-model-and-discriminant.md) (the curve and its
discriminant). The contradiction that ends the proof is assembled from four
theorems, and the irreducibility leg —
`FreyPackage.Mazur_Frey : GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p`
(PROOF-PATH.md, step 3) — uses a predicate whose signature is *much* more
general than the Frey curve: it is defined for a Weierstrass curve over an
arbitrary commutative ring (`W' : Affine R`). Here: (1) the definition
translated into English; (2) what makes the application to
`P.freyCurve : WeierstrassCurve ℚ` typecheck at all. Line numbers refer to
`anthropics/fermats-last-theorem@aa2d8b3` (main, 2026-09-03); Mathlib line
numbers refer to tag v4.33.0, which is exactly the rev pinned in
`lake-manifest.json` (`db584cd6`).

## 1. The full name, and what `Affine R` actually is

The file
[Def_FLTPrelim_GaloisRep.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_GaloisRep.lean)
opens `namespace WeierstrassCurve.Affine.Point` (line 17), so the
definition's full name is
`WeierstrassCurve.Affine.Point.GaloisRepIsIrreducible`, and the `Affine` in
its binder is `WeierstrassCurve.Affine` — which in Mathlib is **not a new
type** but an abbreviation
([Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean, lines 73–75, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean)):

```lean
/-- An abbreviation for a Weierstrass curve in affine coordinates. -/
abbrev Affine : Type r :=
  WeierstrassCurve R
```

An `abbrev` is reducible by definition, so `Affine R` and `WeierstrassCurve R`
are the same type for elaboration. The generality lives entirely in the
section variables (lines 21–23):

```lean
variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]
```

## 2. The definition in English

**Setup.** Let $R$ be a commutative ring, $W'$ a Weierstrass curve over $R$,
and $R \to S \to K$ a tower of algebras with $S$ a commutative ring and $K$ a
field (with decidable equality — a formality the point group law needs;
§3). Let $n$ be a natural number.

**The objects.**

- $W'⁄K$ — the base change of the curve along $R \to K$ (Mathlib's
  `baseChange` notation,
  [Affine/Basic.lean, line 268](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean)).
  Its points $E(K) := (W'⁄K).\mathrm{Point}$ form an abelian group, the
  chord-and-tangent law with the point at infinity as zero.
- `Submodule.torsionBy ℤ E(K) n` — the **$n$-torsion subgroup**
  $E(K)[n] = \\{\\,P \in E(K) : nP = O\\,\\}$ (mathlib:
  `x ∈ torsionBy R M a ↔ a • x = 0`,
  [Mathlib/Algebra/Module/Torsion/Basic.lean, lines 178, 265](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Torsion/Basic.lean)).
  Since $n$ kills it, it is canonically a $\mathbb{Z}/n$-module
  (`AddCommGroup.zmodModule`,
  [Mathlib/Algebra/Module/ZMod.lean, line 44](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/ZMod.lean);
  applied at Def_FLTPrelim_GaloisRep.lean, lines 60–64).
- $K \simeq_{\mathrm{alg}[S]} K$ — the group of **$S$-algebra automorphisms of
  $K$**. It acts on points by applying $\sigma$ to the coordinates:
  `σ • P = Point.map σ.toAlgHom P` (lines 25–30). The action is by group
  automorphisms (the `DistribMulAction` instance, lines 32–37), so it commutes
  with integer multiples (`algEquiv_smul_zsmul`, lines 39–41) and therefore
  preserves the $n$-torsion (`smul_mem_torsionBy`, lines 43–47; induced
  action on the submodule, lines 49–58).

**The two predicates.**

- `IsGaloisStable S N` (lines 66–70): a $\mathbb{Z}/n$-submodule
  $N \subseteq E(K)[n]$ is **Galois-stable** if $\sigma \cdot P \in N$ for
  every $\sigma \in \mathrm{Aut}_S(K)$ and every $P \in N$.
- `GaloisRepIsIrreducible S W' n` (lines 72–77), the conjunction of:
  1. $E(K)[n]$ is **nontrivial** — it contains a point other than $O$;
  2. the **only** Galois-stable $\mathbb{Z}/n$-submodules of $E(K)[n]$ are
     $\{O\}$ ($\bot$) and all of $E(K)[n]$ ($\top$).

**In one sentence:** *the $`n`$-torsion of the base-changed curve is a nonzero
$`\mathbb{Z}/n`$-module on which $`\mathrm{Aut}_S(K)`$ acts, and that action has
no invariant submodule other than the two trivial ones.*

Three remarks on the deliberate generality:

- The formulation is **basis-free**: no identification
  $E[n] \cong (\mathbb{Z}/n)^2$, no matrices, no $\mathrm{GL}_2$. Irreducibility
  is expressed purely as "no stable submodules."
- Nothing assumes $n$ prime, $K$ algebraically closed, or the torsion free of
  rank 2. In this generality $E(K)[n]$ could be just $\{O\}$ — and the zero
  module, having only one submodule, would satisfy clause 2 vacuously. The
  `Nontrivial` conjunct is exactly what excludes that degenerate case.
- Since $\bot$ and $\top$ are *always* Galois-stable, clause 2's content is
  that there are no **others**. Over $\mathbb{F}_p^2$ a proper stable
  submodule is a stable line — the shape the reducible case takes (§4).

## 3. What makes the application typecheck

The use site is
`GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p`
(e.g. [Thm_FreyPackage_Mazur_Frey.lean, line 70](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_Mazur_Frey.lean)).
After section-variable inclusion the binders are pinned as follows:

| Binder | Kind | How the application discharges it |
|---|---|---|
| `{R : Type r}` | implicit | unification: expected type `Affine ?R` unfolds (abbrev) to `WeierstrassCurve ?R`; the argument `P.freyCurve : WeierstrassCurve ℚ` ([Def_FLTPrelim_FreyPackage.lean, line 90](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_FreyPackage.lean)) forces `?R := ℚ` |
| `(S : Type s)` | explicit, 1st positional (via `variable (S) in`, line 72) | `ℚ` |
| `{K : Type v}` | implicit, named | `(K := AlgebraicClosure ℚ)` |
| `(W' : Affine R)` | explicit, 2nd positional | `P.freyCurve` (no coercion — `Affine R` *is* `WeierstrassCurve R`, §1) |
| `(n : ℕ)` | explicit, 3rd positional | `P.p` |
| `[CommRing R]`, `[CommRing S]`, `[Field K]`, `[Algebra R S]`, `[Algebra R K]`, `[Algebra S K]`, `[IsScalarTower R S K]` | instance-implicit | synthesized: `CommRing ℚ` (twice), `Field (AlgebraicClosure ℚ)`, `Algebra ℚ ℚ`, `Algebra ℚ (AlgebraicClosure ℚ)` (twice), the trivial tower |
| `[DecidableEq K]` | instance-implicit | **the one non-standard instance** — see below |

The `DecidableEq (AlgebraicClosure ℚ)` obligation is real: Mathlib's group
law on points, `instance : AddCommGroup W.Point`
([Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean, line 782](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean)),
sits under `variable [DecidableEq F] [DecidableEq K] [DecidableEq L]`
(line 656) — the addition formula branches on equalities of coordinates — and
`Submodule.torsionBy` needs that `AddCommGroup`. An algebraic closure carries
no constructive decidable equality, so the definition file itself appends the
instance, classically (lines 81–83):

```lean
noncomputable instance instDecEqAlgebraicClosureRat :
    DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _
```

This is inherited from the source material: the Imperial College London FLT
project's `FLT/EllipticCurve/Torsion.lean` (named on the
[annotated doc page](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_GaloisRep.html)
and in the file header) makes the same move — "given that there is no hope of
a constructive one with the current definition of algebraic closure." (The
port otherwise *generalizes* the ICL version: ICL works over a field `k` with
`[E.IsElliptic]` and leaves the `DistribMulAction` fields as `sorry`; here we
get the full tower $R \to S \to K$ and proofs, lines 32–37.)

So the answer to "why does the general signature not break the application"
is: **abbrev-transparency pins `R` by unification, the explicit/implicit
binder discipline pins `S`, `K`, `W'`, `n`, typeclass inference fills the
standard instance tail, and the single non-computable instance is supplied by
hand in the same file.** The generality costs the argument nothing.

## 4. What the instantiated proposition says, and who consumes it

At $R = S = \mathbb{Q}$, $K = \overline{\mathbb{Q}}$, $W' = E_P$ (the Frey
curve), $n = p$: the automorphism group $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$
*is* the absolute Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$,
and $`E_P[p](\overline{\mathbb{Q}}) \cong \mathbb{F}_p^2`$. The proposition
reads:

> The $p$-torsion points of the Frey curve over $\overline{\mathbb{Q}}$ form a
> nonzero group, and the only subgroups stable under
> $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ are $\{O\}$ and the whole
> group

— i.e. the mod-$`p`$ representation
$\bar\rho_{E_P,p} : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{F}_p)$
is irreducible. It is *proved* at exactly this instantiation by
`FreyPackage.Mazur_Frey` (Mazur's Eisenstein-ideal argument in the large
range; PROOF-PATH.md step 3) and *consumed* at the same instantiation by the
level-lowering chain:
`FreyPackage.level_lowering_to_two (hmod : P.freyCurve.IsModular) (hirr : GaloisRepIsIrreducible ...)`
produces a nonzero weight-2 cusp form on $\Gamma_0(2)$
([Thm_FreyPackage_level_lowering_to_two.lean, line 131](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_level_lowering_to_two.lean)),
and there is none. In the reducible direction, a failed clause 2 unfolds
(`unfold GaloisRepIsIrreducible`) to a Galois-stable line —
`FreyPackage.frey_reducible_hasCofixedLine`
([Thm_FreyPackage_frey_reducible_hasCofixedLine.lean, line 15](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_frey_reducible_hasCofixedLine.lean)) —
which is what the Mazur-side arguments rule out.

## 5. Aside: the map into $`\mathrm{GL}_2(\mathbb{F}_p)`$ is three layers away — and never taken

The phrase "the mod-$`p`$ representation
$`\bar\rho_{E_P,p} : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{F}_p)`$"
in §4 is a mathematical gloss of the instantiated proposition, not code:
nothing named `GL₂` appears anywhere on the Galois side. What actually brings
a *representation* into context happens in layers, and the proof stops one
layer short of matrices.

**Layer 1 — the action repackaged as a hom into module automorphisms**
(still basis-free): `galoisRep W' n : (K ≃ₐ[S] K) →* (torsionBy ℤ (W'⁄K).Point n) ≃ₗ[ZMod n] _`
is one line, Mathlib's `DistribMulAction.toModuleAut`
([Def_FreyPackage_GaloisRep.lean, lines 18–21](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FreyPackage_GaloisRep.lean));
`FreyPackage.freyGaloisRep` (lines 38–42) is the §4 instantiation. The
`End`-valued twin `galoisRepModuleEnd`
([Def_EllipticCurve_FrobeniusTrace.lean, line 25](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_EllipticCurve_FrobeniusTrace.lean))
is what Frobenius traces are taken of (`LinearMap.trace`, line 37) — a trace
needs no basis.

**Layer 2 — "2-dimensional" enters as a *cardinality* input, buying
charpoly/det.** The structure `ResidualGaloisRep k`
([Def_GaloisRep_Residual.lean, lines 22–32](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_GaloisRep_Residual.lean))
packages an abstract $`k`$-module $`V`$ with `Module.finrank k V = 2`, a hom
`ρ : Gal(Q̄/Q) →* Module.End k V`, and a factors-through-a-finite-extension
field. Now the GL₂-shaped invariants exist, still basis-free:
`LinearMap.charpoly` in `IsAttachedTo` (line 55 — Frobenius charpoly
$`X^2 - a_\ell X + \ell`$, the eigenform attachment), `LinearMap.det` in
`IsOdd` (line 59), and `IsIrreducible` (lines 61–63) again in
stable-submodule form. The constructor from the curve,
`WeierstrassCurve.residualGaloisRepOf` (lines 87–103), takes the rank-2 fact
as an explicit hypothesis in counting form,
`hcard : Nat.card (torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2`,
converted to `finrank = 2` via `Module.natCard_eq_pow_finrank`. That `hcard`
*is* the formal content of $`E[p](\overline{\mathbb{Q}}) \cong \mathbb{F}_p^2`$
— the fact ICL's `Torsion.lean` still has as `sorry`.

**Layer 3 — actual matrices: available, never taken.** A literal
`Gal(Q̄/Q) →* GL (Fin 2) (ZMod p)` would need a basis
`E[p] ≃ₗ[ZMod p] (Fin 2 → ZMod p)`; the machinery exists from the same
cardinality input (`basisOfCard`, `free`, `finrank_eq_two`,
[Def_EllipticCurve_TateModule.lean, lines 596–630](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_EllipticCurve_TateModule.lean)),
and conjugation by the basis equiv would land in matrix units. Nothing in
the proof does this: `GL (Fin 2)` (= `Matrix.GeneralLinearGroup`) appears in
the repo only on the *automorphic* side — adeles, archimedean factors, local
newvectors
([Def_AdelicDock_LocalEmbedding.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_AdelicDock_LocalEmbedding.lean)).
GL₂ is kept as the automorphic object; the Galois object stays "2-dim module + `End`-hom",
and the two meet only through charpoly/trace/det comparisons.
The worlds are tied by
`WeierstrassCurve.residualGaloisRepOf_isIrreducible_iff`
([S_WeierstrassCurve_residualGaloisRepOf_isIrreducible_iff.lean, line 12](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_WeierstrassCurve_residualGaloisRepOf_isIrreducible_iff.lean)):
`ResidualGaloisRep.IsIrreducible ↔ GaloisRepIsIrreducible` — so `Mazur_Frey`
is proved entirely in the basis-free language yet feeds the `End`-valued
level-lowering machine.

## 6. Key-point → code map

| Key point | Mathematical content | Where in the code |
|---|---|---|
| `Affine R` looks like a new type | it is `WeierstrassCurve.Affine`, an `abbrev` for `WeierstrassCurve R`; elaboration unfolds it, so `P.freyCurve : WeierstrassCurve ℚ` pins `R := ℚ` with no coercion | [Affine/Basic.lean:73–75, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean); [Def_FLTPrelim_FreyPackage.lean:90](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_FreyPackage.lean) |
| Galois group without matrices | the acting group is literally `K ≃ₐ[S] K`, acting by `Point.map`; basis-free irreducibility | [Def_FLTPrelim_GaloisRep.lean:25–37, 68–77](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_GaloisRep.lean) |
| $n$-torsion as a $\mathbb{Z}/n$-module | `Submodule.torsionBy ℤ _ n` plus `AddCommGroup.zmodModule` ($n$ annihilates it) | [Torsion/Basic.lean:178, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Torsion/Basic.lean); [ZMod.lean:44, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/ZMod.lean); Def_FLTPrelim_GaloisRep.lean:60–64 |
| why `[DecidableEq K]` is in the signature | Mathlib's `AddCommGroup W.Point` requires decidable equality of the coordinate field | [Affine/Point.lean:656, 782, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean) |
| who supplies `DecidableEq (AlgebraicClosure ℚ)` | nobody constructibly — the definition file adds a classical instance; same move as ICL FLT | Def_FLTPrelim_GaloisRep.lean:81–83; [FLT/EllipticCurve/Torsion.lean](https://github.com/ImperialCollegeLondon/FLT/blob/main/FLT/EllipticCurve/Torsion.lean) |
| which binders are explicit | `S` (via `variable (S) in`), `W'`, `n` positional; `K` named implicit; `R` implicit pinned by unification | Def_FLTPrelim_GaloisRep.lean:72–77 |
| what it means at $\mathbb{Q}, \overline{\mathbb{Q}}, p$ | $`E_P[p](\overline{\mathbb{Q}})`$ nonzero, no Galois-stable $\mathbb{Z}/p$-submodule besides $\bot, \top$ — $\bar\rho_{E_P,p}$ irreducible; a proper stable submodule is a stable line | [Thm_FreyPackage_Mazur_Frey.lean:70](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_Mazur_Frey.lean); [Thm_FreyPackage_frey_reducible_hasCofixedLine.lean:15](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_frey_reducible_hasCofixedLine.lean) |

## 7. Links

Lean sources (raw; quote line numbers as above):

- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_GaloisRep.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FLTPrelim_FreyPackage.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_Mazur_Frey.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_level_lowering_to_two.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Theorems/Thm_FreyPackage_frey_reducible_hasCofixedLine.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_FreyPackage_GaloisRep.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_GaloisRep_Residual.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_EllipticCurve_FrobeniusTrace.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_EllipticCurve_TateModule.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/Definitions/Def_AdelicDock_LocalEmbedding.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/refs/heads/main/P2M/Sol/S_WeierstrassCurve_residualGaloisRepOf_isIrreducible_iff.lean>

Annotated docs (viewable):

- [Def page: FLTPrelim_GaloisRep](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_GaloisRep.html)
- [Route §3: irreducibility](https://tianyipeng.github.io/fermats-last-theorem/route/s3.html)
- [PROOF-PATH.md](https://github.com/anthropics/fermats-last-theorem/blob/main/PROOF-PATH.md) (step 3)

Mathlib v4.33.0 (the rev pinned in `lake-manifest.json`):

- [`WeierstrassCurve.Affine` abbrev, Affine/Basic.lean (lines 73–75)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean)
- [`AddCommGroup W.Point` under `[DecidableEq ...]`, Affine/Point.lean (lines 656, 782)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean)
- [`Submodule.torsionBy`, Torsion/Basic.lean (line 178)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/Torsion/Basic.lean)
- [`AddCommGroup.zmodModule`, ZMod.lean (line 44)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/ZMod.lean)

Background: the file is ported from the Imperial College London FLT project —
[FLT/EllipticCurve/Torsion.lean](https://github.com/ImperialCollegeLondon/FLT/blob/main/FLT/EllipticCurve/Torsion.lean)
(the $n$-torsion as a $\mathbb{Z}/n$-module, the Galois action by `Point.map`,
and the classical `DecidableEq (AlgebraicClosure ℚ)` instance all originate
there; the port generalizes field `k` to the tower $R \to S \to K$ and
supplies the proofs ICL leaves as `sorry`).
