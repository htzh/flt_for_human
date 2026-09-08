# $`\#E[n](K) = n^2`$ over an algebraically closed field — the foundation of the $\mathrm{GL}_2$ picture

Companion to [note 003](003-galois-rep-irreducible-in-english.md) (the
`GaloisRepIsIrreducible` predicate) and [note 004](004-irreducible-and-cofixed-line.md)
(the basis-free cofixed-line detour). Both of those notes took for granted
that the $`p`$-torsion $`E[p](K)`$ is a **2-dimensional** vector space over
$\mathbb{F}_p$ — the fact that makes the mod-$`p`$ Galois action a
2-dimensional representation (and, after choosing a basis, a map into
$`\mathrm{GL}_2(\mathbb{F}_p)`$). This note covers the theorem that feeds that
fact, `WeierstrassCurve.card_torsion_of_isAlgClosed`: its statement (§1), a
sketch of the proof as carried out in the project (§2), how $\#E[p] = p^2$
becomes "dimension 2 over $\mathbb{F}_p$" (§3), and how the theorem is used
downstream (§4). Line numbers refer to
`anthropics/fermats-last-theorem@aa2d8b3` (main, 2026-09-03); Mathlib line
numbers refer to tag v4.33.0.

## 1. The theorem

The whole theorem file
[Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean, lines 8–9](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)
is one line of real content:

```lean
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
theorem WeierstrassCurve.card_torsion_of_isAlgClosed {F : Type*} {K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) : Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_card_torsion_of_isAlgClosed.solution
```

Unpacking the pieces:

- $`(W⁄K).Point`$ is the Mordell–Weil group of the base change of $`W`$ to
  $`K`$ ($`W⁄K`$ is mathlib's scoped notation for `baseChange`,
  [Affine/Basic.lean, line 268](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean)),
  and `Submodule.torsionBy ℤ … n` is the $`n`$-torsion subgroup
  $`E[n](K) = \{P \mid nP = O\}`$. So the statement is the classical one:
  for an elliptic curve $`E`$ over an algebraically closed field $`K`$ in
  which $`n \neq 0`$,
  $$\mathrm{card}\\,E[n]\\,(K) = n^2 .$$
- `[W.IsElliptic]` is nonsingularity ($`\Delta`$ a unit); `[IsAlgClosed K]`
  supplies the roots; `(n : K) ≠ 0` is "$`\mathrm{char}\\,K \nmid n`$"
  (including $`n = 0`$, which it rules out); `[DecidableEq K]` is the
  technical instance the `AddCommGroup` structure on `Point` sits under —
  the same classical-instance issue as in note 003, discharged for
  $`K = \overline{\mathbb{Q}}`$ by `instDecEqAlgebraicClosureRat`.
- The proof is delegated by `p2m_exact_reverting` to the `solution` theorem
  of the sibling P2M file (below).

Two sibling statements share the name and should not be confused with it:
`card_torsionBy_eq_sq_of_isAlgClosed`
([Thm file](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsionBy_eq_sq_of_isAlgClosed.lean))
is the variant where $`F`$ itself is already algebraically closed (no
separate $`K`$) with an extra $`(2 : F) \neq 0`$ hypothesis, and
`card_torsion_of_isAlgClosed_light`
([Thm file](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed_light.lean))
is the *same* statement as ours re-exported through a 12-line Sol file with
leaner imports — the CuspForm patching solutions cite the `_light` name.

## 2. Proof sketch, as done in the project

The proof lives in
[P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)
(1335 lines, sections named `Port…`). It is the classical
division-polynomial proof (Silverman, *AEC* III.6.4), organized around a
local definition of the torsion subgroup
([line 308](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)):
`nTorsion W n` is the `AddSubgroup` of $`(W⁄K).Point`$ with carrier
$`\\{P \mid n \bullet P = 0\\}`$. The steps:

1. **Division polynomials** (`PortTorsionSmulFormulaEngine`,
   `PortGenNetIdentities`, `PortGenInduction`, `PortGenSmulFormula`, lines
   32–294). Mathlib's `WeierstrassCurve.ψ` / `Φ` / `ΨSq` / `preΨ`
   (`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial`) give the
   multiplication formula on $`x`$-coordinates,
   $`x(nP) = \Phi_n(x(P)) / \Psi_n(x(P))^2`$
   (`smul_x_eq`, line 196), and the vanishing criterion
   $`nP = O \iff \Psi_n^2(x(P)) = 0`$ (`smul_eq_zero_of_ΨSq_eval_eq_zero`,
   line 261, via mathlib's `smul_eq_zero_iff_evalEval_ψ`). Two coprimality
   facts drive everything else: $\Phi_n$ is coprime to $\Psi_n^2$
   (`isCoprime_Φ_ΨSq`, line 213), and the $\Psi^2$ of consecutive
   indices are coprime
   (`isCoprime_ΨSq_succ`, line 77 — a common root would give a finite point
   killed by both $`n`$ and $`n+1`$, hence by 1, contradicting
   $`P \neq O`$).
2. **Separability** (`PortGenCardViaFibers`, lines 296–908). The Wronskian
   of the rational map $`x \circ [n]`$ is nonzero
   (`wronskian_Φ_ΨSq_ne_zero`, line 343) — this is exactly where the
   hypothesis $`(n : K) \neq 0`$ is spent: $`[n]`$ is a separable rational
   map only when $`\mathrm{char}\\,K \nmid n`$. Consequences: all but
   finitely many fibers of $`x \circ [n]`$ have full size
   (`finite_not_squarefree_fiber`, line 397).
3. **Surjectivity of** $`[n]`$ (`smul_surjective`, line 452, for odd $`n`$;
   `smul_surjective_all`, line 955, in general). For $`Q = (x_Q, y_Q)`$ the
   polynomial $`\Phi_n - x_Q \cdot \Psi_n^2`$ has degree $`n^2 > 0`$
   (mathlib's `natDegree_Φ` / `natDegree_ΨSq`), hence a root $`x_0`$ since
   $`K`$ is algebraically closed; coprimality of $`\Phi_n, \Psi_n^2`$ forces
   $`\Psi_n^2(x_0) \neq 0`$, so $`n \cdot (x_0, y_0)`$ is a finite point
   with $`x`$-coordinate $`x_Q`$, i.e. it equals $`\pm Q`$; negate the
   preimage if needed.
4. **All fibers of** $`[n]`$ **have size** $`\#E[n]`$ (`card_smul_fiber`,
   line 533; `card_smul_fiber_all`, line 1035): picking any preimage
   $`P_0`$ of $`Q`$, translation $`P \mapsto P + P_0`$ bijects $`E[n]`$
   with the fiber over $`Q`$.
5. **Odd** $`n`$: **counting via a double fiber**
   (`card_nTorsion_odd_fibers`, line 847). A full-size fiber of
   $`x \circ [n]`$ produces a $`Q`$ with
   $`\#\{P : nP = \pm Q\} = 2n^2`$ (`exists_double_fiber_card`, line 614).
   Since $`n`$ is odd, $`Q \neq -Q`$ — otherwise $`2 \mid \#E[n]`$, giving
   a point of order 2 killed by the odd number $`n`$ (lines 853–873). The
   two fibers are then disjoint, each of size $`\#E[n]`$ by step 4, so
   $`2 \cdot \#E[n] = 2n^2`$.
6. $`n = 2`$ **directly** (`card_nTorsion_two`, line 1054): $`E[2]`$
   consists of $`O`$ and the points $`(x, -(a_1 x + a_3)/2)`$ for $`x`$ a
   root of the two-torsion cubic; the cubic has 3 distinct roots because
   its discriminant is nonzero ($`E`$ nonsingular, $`2 \neq 0`$). Hence
   $`\#E[2] = 4 = 2^2`$.
7. **Prime powers by induction** (`card_nTorsion_prime_pow`, line 1168):
   $`E[p^{k+1}]`$ is the disjoint union over $`Q \in E[p]`$ of the fibers
   $`\{P : p^k P = Q\}`$, each of size $`\#E[p^k]`$ by step 4, so
   $`\#E[p^{k+1}] = \#E[p] \cdot \#E[p^k] = p^2 \cdot p^{2k}`$.
8. **Coprime gluing** (`card_nTorsion_mul_of_coprime`, line 1217): Bézout
   coefficients $`ma + nb = 1`$ give an explicit equivalence
   $`E[mn] \simeq E[m] \times E[n]`$ via
   $`P \mapsto (nb \cdot P,\\, ma \cdot P)`$.
9. **Assembly** (`card_nTorsion`, line 1294) by
   `Nat.recOnPosPrimePosCoprime`: the cases $`n = 1`$, prime powers
   (step 7), and coprime products (step 8) cover every $`n`$ with
   $`(n : K) \neq 0`$.
10. **Wrapper** (`solution`, line 1330): `nTorsion` is identified with
    `Submodule.torsionBy ℤ (W⁄K).Point n` by `Submodule.mem_torsionBy_iff`
    plus `natCast_zsmul`, yielding the stated equation.

## 3. From $\#E[p] = p^2$ to "$`E[p]`$ is 2-dimensional over $\mathbb{F}_p$"

Two abelian-group facts turn the cardinality into linear algebra:

- $`E[p](K)`$ is killed by $`p`$, hence is a module over
  $`\mathbb{Z}/p`$: the instance `instModuleZModTorsionBy`
  ([Def_FLTPrelim_GaloisRep.lean, lines 60–64](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean))
  is mathlib's `AddCommGroup.zmodModule`
  ([ZMod.lean, line 44](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/ZMod.lean)).
  For $`p`$ prime, `ZMod p` is the field $`\mathbb{F}_p`$, so
  $`E[p](K)`$ is an $`\mathbb{F}_p`$-vector space.
- A finite $`\mathbb{F}_p`$-vector space of cardinality $`p^2`$ has
  dimension 2. The repo packages exactly this as
  `WeierstrassCurve.finrank_zmod_torsionBy_point_eq_two`
  ([Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two.lean, lines 10–14](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two.lean)),
  whose entire proof
  ([Sol, lines 22–33](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two.lean))
  is our theorem plus mathlib's
  `Module.card_eq_pow_finrank`
  ([Finiteness.lean, line 91](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Finiteness.lean)):

```lean
  have hcard : Nat.card (Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p) = p ^ 2 :=
    WeierstrassCurve.card_torsion_of_isAlgClosed E (n := p) hpK

  set M := Submodule.torsionBy ℤ (E.baseChange K).toAffine.Point p
  have hne : Nat.card M ≠ 0 := hcard ▸ pow_ne_zero 2 hp.pos.ne'
  haveI : Finite M := Nat.finite_of_card_ne_zero hne
  haveI : Fintype M := Fintype.ofFinite M
  have hceq : Fintype.card M = p ^ Module.finrank (ZMod p) M := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := M)
    rwa [ZMod.card] at h
  rw [← Nat.card_eq_fintype_card, hcard] at hceq
  exact (Nat.pow_right_injective hp.two_le hceq).symm
```

i.e. $`p^{\dim} = p^2 \Rightarrow \dim = 2`$ by injectivity of
$`p^{(\cdot)}`$. There is also a group-structure upgrade,
`WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`
([Thm file, lines 9–12](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean)):
$`E[n](K) \cong \mathbb{Z}/n \times \mathbb{Z}/n`$ as abelian groups. Its
Sol file is a five-line reduction to a generic group lemma
(`AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`),
with the cardinality hypothesis for every $`d \mid n`$ discharged by
`W.card_torsion_of_isAlgClosed` (Sol, line 23).

## 4. How the theorem is used

**The residual representation's dimension.** The mod-$`p`$ representation
is built by `WeierstrassCurve.residualGaloisRepOf`
([Def_GaloisRep_Residual.lean, lines 87–103](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean)),
which takes the cardinality as an explicit hypothesis and converts it into
the dimension field of the representation package:

```lean
def WeierstrassCurve.residualGaloisRepOf (W : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime]
    (hcard : Nat.card (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p)) :
    ResidualGaloisRep (ZMod p) :=
  haveI hfin : Finite (Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p) :=
    Nat.finite_of_card_ne_zero
      (hcard ▸ pow_ne_zero 2 (Fact.out (p := p.Prime)).pos.ne')
  { V := Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p
    finrank_eq := by
      have hp : p.Prime := Fact.out
      have h := Module.natCard_eq_pow_finrank (K := ZMod p)
        (V := Submodule.torsionBy ℤ (W⁄(AlgebraicClosure ℚ)).Point p)
      rw [hcard, Nat.card_zmod] at h
      exact (Nat.pow_right_injective hp.two_le h).symm
    ρ := WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ W p
    factorsThroughFiniteLevel := hker }
```

The representation space $`V`$ **is** $`E[p](\overline{\mathbb{Q}})`$, and
`finrank_eq` — proved from `hcard` by the same $`p^{\dim} = p^2`$
argument — is the formal content of "the residual representation is
2-dimensional". Choosing a basis of $`V`$ would turn
`ρ : Gal(ℚ̄/ℚ) → V ≃ₗ V` into matrices $`\bar\rho : \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(\mathbb{F}_p)`$,
but as documented in note 004 (§4) the project deliberately never chooses
one; `hcard` is the precise point where the $\#E[p] = p^2$ theorem enters
that basis-free picture, and it is discharged at use sites by
`card_torsion_of_isAlgClosed`.

**The Frey line.** Closest to notes 001–004, the theorem supplies
nontriviality of $`E_P[p]`$ whenever the Frey curve's torsion is
manipulated. The cleanest example is the reducible ⇒ cofixed-line step of
note 004
([S_FreyPackage_frey_reducible_hasCofixedLine.lean, lines 29–42](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_reducible_hasCofixedLine.lean)):

```lean
  have hp : ((P.p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast P.hp0
  have hcard := WeierstrassCurve.card_torsion_of_isAlgClosed
    (K := AlgebraicClosure ℚ) P.freyCurve hp
  have hnt : Nontrivial
      (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) := by
    have h1 : 1 < Nat.card
        (Submodule.torsionBy ℤ (P.freyCurve⁄(AlgebraicClosure ℚ)).Point P.p) := by
      rw [hcard]
      have := P.hp5
      nlinarith
```

— $`p \geq 5`$ gives $`1 < p^2 = \#E_P[p]`$, and that `Nontrivial` instance
is the side condition `GaloisRepIsIrreducible` requires before "reducible"
can even be unfolded (note 003). The same one-line justification appears at:

- [S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at.lean, line 26](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at.lean)
  and
  [S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean, line 160](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean)
  (inertia-triviality arguments),
- [S_FreyPackage_frey_no_cofixed_large.lean, line 698](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean),
- [S_FreyPackage_frey_exists_p_torsion_integral_abscissa.lean, line 570](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_exists_p_torsion_integral_abscissa.lean)
  ($`p^2 > 1`$ puts a non-$`O`$ $`p`$-torsion point on the curve, the first
  step toward one with integral $`x`$-coordinate).

**Via the finrank corollary**, e.g. the determinant-of-Frobenius
computation cites `finrank_zmod_torsionBy_point_eq_two` twice
([S_WeierstrassCurve_det_galoisRepModuleEnd_frobenius_eq.lean, lines 218, 233](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_WeierstrassCurve_det_galoisRepModuleEnd_frobenius_eq.lean)).
Further afield, the Cerednik–Drinfeld and CuspForm-patching solutions use
the theorem (and its `_light` re-export) whenever a torsion cardinality
over an algebraically closed residue field is needed.

## 5. Why the hypotheses are necessary

- $`(n : K) \neq 0`$: in characteristic $`\ell \mid n`$ the map $`[n]`$ is
  inseparable and the count drops — famously
  $`\#E[p](\overline{\mathbb{F}}_p) \in \{1, p\}`$ (supersingular vs
  ordinary). In the proof the hypothesis is propagated through every
  lemma, but its mathematical content is consumed at the Wronskian step
  (§2.2).
- $`K`$ algebraically closed: over a general field,
  $`\#E[n](K) \leq n^2`$; equality says all $`n`$-torsion is
  $`K`$-rational. Surjectivity of $`[n]`$ (§2.3) is the step that needs
  roots of degree-$`n^2`$ polynomials.
- $`W`$ nonsingular: the two-torsion count and the division-polynomial
  coprimality lemmas use $`\Delta \neq 0`$; nodal/cuspidal cubics have
  different torsion (their point groups are additive/multiplicative groups
  of the field).

## Key-point → code map

| Mathematical point | Lean declaration (file, line) |
| --- | --- |
| $`\#E[n](K) = n^2`$ | `WeierstrassCurve.card_torsion_of_isAlgClosed` (`Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean:9`) |
| Proof: 1335-line division-polynomial argument | `P2MW.S_WeierstrassCurve_card_torsion_of_isAlgClosed.solution` (`S_…card_torsion_of_isAlgClosed.lean:1330`) |
| Local torsion subgroup | `nTorsion` (`S_…:308`) |
| $x(nP) = \Phi_n/\Psi_n^2$ | `smul_x_eq` (`S_…:196`) |
| $\Phi_n \perp \Psi_n^2$; $\Psi_n^2 \perp \Psi_{n+1}^2$ | `isCoprime_Φ_ΨSq` (`S_…:213`); `isCoprime_ΨSq_succ` (`S_…:77`) |
| $[n]$ separable when $(n:K)\neq 0$ | `wronskian_Φ_ΨSq_ne_zero` (`S_…:343`) |
| $[n]$ surjective over $\bar K$ | `smul_surjective` (`S_…:452`), `smul_surjective_all` (`S_…:955`) |
| All fibers of $[n]$ have size $\#E[n]$ | `card_smul_fiber` (`S_…:533`), `card_smul_fiber_all` (`S_…:1035`) |
| Odd $n$: $\#E[n] = n^2$ | `card_nTorsion_odd_fibers` (`S_…:847`) |
| $n = 2$: $\#E[2] = 4$ | `card_nTorsion_two` (`S_…:1054`) |
| Prime powers / coprime gluing / assembly | `card_nTorsion_prime_pow` (`S_…:1168`), `card_nTorsion_mul_of_coprime` (`S_…:1217`), `card_nTorsion` (`S_…:1294`) |
| $E[p]$ a $\mathbb{Z}/p$-module | `instModuleZModTorsionBy` (`Def_FLTPrelim_GaloisRep.lean:60`) |
| $\dim_{\mathbb{F}_p} E[p] = 2$ | `WeierstrassCurve.finrank_zmod_torsionBy_point_eq_two` (`Thm_…finrank_zmod…:10`) |
| $E[n] \cong \mathbb{Z}/n \times \mathbb{Z}/n$ | `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` (`Thm_…nonempty_torsionBy…:9`) |
| 2-dim residual rep from $\#E[p] = p^2$ | `WeierstrassCurve.residualGaloisRepOf` (`Def_GaloisRep_Residual.lean:87`) |

## Links

- [Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)
  and its
  [P2M solution](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean)
- [Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two.lean)
  and its
  [P2M solution](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_WeierstrassCurve_finrank_zmod_torsionBy_point_eq_two.lean)
- [Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean)
- [Def_GaloisRep_Residual.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_GaloisRep_Residual.lean)
  (`residualGaloisRepOf`, the `hcard` consumer) and
  [Def_FLTPrelim_GaloisRep.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_GaloisRep.lean)
  (the $\mathbb{Z}/n$-module instance)
- [S_FreyPackage_frey_reducible_hasCofixedLine.lean](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_reducible_hasCofixedLine.lean)
  (the Frey-line use site quoted in §4)
- Mathlib at v4.33.0:
  [Module.card_eq_pow_finrank](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/FieldTheory/Finiteness.lean),
  [AddCommGroup.zmodModule](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/Algebra/Module/ZMod.lean),
  [the $W\!\mathbin{/}\!K$ notation](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Basic.lean)
- Def pages:
  [FLTPrelim_GaloisRep](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_GaloisRep.html),
  [GaloisRep_Residual](https://tianyipeng.github.io/fermats-last-theorem/def/GaloisRep_Residual.html)
- Background: Silverman, *The Arithmetic of Elliptic Curves*, III.6.4
  ($`\#E[n] = n^2`$ over $`\bar K`$ with $`\mathrm{char} \nmid n`$),
  proved there via the same division-polynomial/separability route.
