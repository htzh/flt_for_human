# Fixed or cofixed: how the Frey curve's semistability splits every stable line — and why inertia decides

Companion to [note 004](004-irreducible-and-cofixed-line.md), whose §2 quoted
the dichotomy `FreyPackage.frey_stable_submodule_fixed_or_cofixed` as the
Frey-specific input to "reducible ⇒ cofixed line". Here we open up that
dichotomy itself: (1) the theorem and its global assembly; (2) the
linear-algebra core (a stable line vs. an "absorbing" submodule); (3) the
Frey-curve arithmetic that forces the split — semistability at every prime,
with the prime $`p`$ as the only place where anything can happen; (4) the role
of inertia: how it is presented, why it determines the global action, and the
three different ways it is tamed at $`q \neq 2`$, $`q = 2`$, and $`q = p`$.
Line numbers refer to `anthropics/fermats-last-theorem@aa2d8b3` (main,
2026-09-03); the one Mathlib line number refers to tag v4.33.0.

## 1. The theorem, in English

`FreyPackage.frey_stable_submodule_fixed_or_cofixed`
([Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean, line 10](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean)):
let $`P`$ be a Frey package, $`M = E_P[p](\overline{\mathbb{Q}})`$ the
$`p`$-torsion of its Frey curve, and $`N \subseteq M`$ a
$`\mathbb{Z}/p`$-submodule which is Galois-stable (`IsGaloisStable`), nonzero
($`N \neq \bot`$), and proper ($`N \neq \top`$). Then **either**

- **fixed:** $`\sigma \cdot x = x`$ for all
  $`\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})`$ and all
  $`x \in N`$ — i.e. $`N`$ consists of rational points; **or**
- **cofixed:** $`\sigma \cdot x - x \in N`$ for all $`\sigma`$ and all
  $`x \in M`$ — i.e. the induced action on the quotient $`M/N`$ is trivial.

In the matrix picture of note 004 §4 (basis of
$`E_P[p] \cong \mathbb{F}_p^2`$ with first vector spanning $`N`$):
$`\bar\rho(\sigma) = \begin{pmatrix} \lambda(\sigma) & b(\sigma) \\ 0 & \nu(\sigma) \end{pmatrix}`$,
and the dichotomy says the diagonal characters are not just anything —
either $`\lambda = 1`$ globally, or $`\nu = 1`$ globally. There is no
representation-theoretic reason for this to hold for a general elliptic
curve (a general mod-$`p`$ representation can be
$`\begin{pmatrix} \chi_1 & * \\ 0 & \chi_2 \end{pmatrix}`$ with both $`\chi_i`$
nontrivial); it is forced by the Frey curve's arithmetic, §§3–4.

The proof is one screenful and is quoted in full
([S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean, lines 33–55](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean)):

```lean
  rcases P.frey_inertia_at_p_trivial_on_submodule_or_quotient N hN hbot htop with hsub | hquot
  · left
    apply WeierstrassCurve.galois_action_trivial_on_submodule_of_inertia_trivial P.freyCurve N
    intro q hq A hA σ hσ x hxN
    by_cases hq2 : q = 2
    · subst hq2
      exact (P.frey_inertia_at_two_trivial_on_stable_submodule N hN hbot htop A hA σ hσ).1 x hxN
    by_cases hqp : q = P.p
    · subst hqp
      exact hsub A hA σ hσ x hxN
    · exact P.freyGaloisRep_isUnramifiedAt hq hq2 hqp A hA σ hσ x
  · right
    apply WeierstrassCurve.galois_action_trivial_on_quotient_of_inertia_trivial P.freyCurve N hN
    intro q hq A hA σ hσ x
    by_cases hq2 : q = 2
    · subst hq2
      exact (P.frey_inertia_at_two_trivial_on_stable_submodule N hN hbot htop A hA σ hσ).2 x
    by_cases hqp : q = P.p
    · subst hqp
      exact hquot A hA σ hσ x
    · have hfix : σ • x = x := P.freyGaloisRep_isUnramifiedAt hq hq2 hqp A hA σ hσ x
      rw [hfix, sub_self]
      exact N.zero_mem
```

The logical shape is a **branch-and-close**:

1. Branch on a dichotomy <i>localized at the prime $`p`$</i>: inertia at $`p`$ acts
   trivially either on $`N`$ (`hsub`) or on $`M/N`$ (`hquot`)
   (`FreyPackage.frey_inertia_at_p_trivial_on_submodule_or_quotient`,
   [Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean)).
2. In each branch, **close globally**: to show *all* of
   $`\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})`$ acts trivially on $`N`$
   (resp. $`M/N`$), the two closure lemmas reduce to checking
   **inertia-triviality at every prime $`q`$**
   (`galois_action_trivial_on_submodule_of_inertia_trivial`,
   [Thm, line 8](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial.lean);
   `..._on_quotient_of_inertia_trivial`,
   [Thm, line 8](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galois_action_trivial_on_quotient_of_inertia_trivial.lean)).
   The prime-wise check is a three-way split:
   - $`q = 2`$: `frey_inertia_at_two_trivial_on_stable_submodule`
     ([Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean))
     gives *both* trivialities at once — inertia at $`2`$ fixes $`N`$ pointwise
     (`.1`) *and* fixes $`M/N`$ (`.2`), whichever branch we are in;
   - $`q = p`$: exactly the branch hypothesis `hsub` / `hquot`;
   - $`q \neq 2, p`$: `freyGaloisRep_isUnramifiedAt`
     ([Thm, line 15](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_freyGaloisRep_isUnramifiedAt.lean))
     says inertia at $`q`$ fixes *all* of $`M`$ pointwise, which implies both
     trivialities.

So the theorem is true because: **the global action on the flag
$`N \subset M`$ is entirely witnessed by inertia, inertia at every prime other
than $`p`$ is already (at worst unipotently) trivial, and at $`p`$ semistability
supplies the split.** The rest of the note fills in the three clauses.

## 2. The linear-algebra core: a stable line vs. an absorbing submodule

Strip away the arithmetic and the dichotomy at $`p`$ is a lemma about a
group acting on a 2-dimensional $`\mathbb{F}_p`$-space,
`Submodule.stableLine_fixed_or_cofixed_of_absorbing`
([Thm, line 5](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_Submodule_stableLine_fixed_or_cofixed_of_absorbing.lean)).
Hypotheses: $`V`$ a $`\mathbb{Z}/p`$-module with
$`\mathrm{card}\,V = p^2`$; $`S`$ a set of operators; $`N`$ an $`S`$-stable
submodule, $`N \neq \bot, \top`$; and a submodule $`M \neq \top`$ which is
**absorbing**: $`g \cdot y - y \in M`$ for all $`g \in S`$, $`y \in V`$ (trivial
action on $`V/M`$). Conclusion: $`N`$ is pointwise fixed, or cofixed. The proof
([S file, lines 25–46](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_Submodule_stableLine_fixed_or_cofixed_of_absorbing.lean))
is pure dimension counting on lines ($`\mathrm{finrank}\,V = 2`$ from the
cardinality, $`\mathrm{finrank}\,N = 1`$):

- **$`N \leq M`$:** then $`N = M`$ (both of dimension 1), and absorbing reads
  $`g \cdot y - y \in N`$ — cofixed.
- **$`N \nleq M`$:** then $`N \cap M = \bot`$ (a proper subspace of a line is
  zero), and for $`x \in N`$ the difference $`g \cdot x - x`$ lies in $`N`$
  (stability) *and* in $`M`$ (absorbing), hence is zero — fixed.

Matrix picture: in a basis adapted to the flag $`M \subset V`$, every
$`g \in S`$ is $`\begin{pmatrix} * & * \\ 0 & 1 \end{pmatrix}`$. A second stable
line $`N`$ is either the first column's span (cofixed case) or is spanned by
an eigenvector transverse to $`M`$, whose eigenvalue must be $`1`$ (fixed case).
So **the whole content of the local dichotomy is the existence of one
absorbing line** $`M \subsetneq E_P[p]`$ for the inertia group at $`p`$ —
i.e. an invariant filtration with trivial action on the top graded piece.
Semistability at $`p`$ is what supplies it (§3).

## 3. The Frey-curve property that forces the split: semistability at every prime

No structure named "semistable" ever appears in the proof. What appears is a
list of concrete facts about the Frey model
$`y^2 = x(x - a^p)(x + b^p)`$ (note 002) with
$`a \equiv 3 \pmod 4`$, $`b \equiv 0 \pmod 4`$ (note 001), each of which is a
consequence of: **at every prime, the Frey curve has good or multiplicative
reduction — it is semistable — and at multiplicative primes
$`q \neq 2`$ the discriminant valuation is divisible by $`p`$.**
The facts, per prime:

### 3.1. Primes $`q \neq 2, p`$: unramified, no dichotomy needed

`freyGaloisRep_isUnramifiedAt` is proved by a two-case analysis
([S_FreyPackage_freyGaloisRep_isUnramifiedAt.lean, `freyGaloisRep_isUnramifiedAt_of_local_criteria`, lines 146–176](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_freyGaloisRep_isUnramifiedAt.lean))
on the integral model `freyCurveInt`:

- **$`q \nmid abc`$ (good reduction):** then $`q \nmid \Delta`$ and
  `galoisRepUnramifiedAt_of_goodReduction`
  ([Thm, line 12](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_goodReduction.lean))
  applies — the easy direction of Néron–Ogg–Shafarevich: good reduction at
  $`q \neq p`$ makes the $`p`$-torsion unramified at $`q`$.
- **$`q \mid abc`$ (bad reduction):** two Frey-specific computations:
  $`q \nmid c_4`$ (`not_dvd_c₄Int`, line 70 of the same file — from
  $`c_4 = a^{2p} + a^p b^p + b^{2p} = c^{2p} - (ab)^p`$ and the pairwise
  coprimality of $`a, b, c`$), so with $`q \mid \Delta`$ the reduction is
  **multiplicative**; and
  $`v_q(\Delta) = 2p \cdot v_q(abc)`$ (`padicValInt_freyCurveInt_Δ`,
  line 130, from $`\Delta \cdot 2^8 = (abc)^{2p}`$), so
  $`p \mid v_q(\Delta)`$. Then
  `galoisRepUnramifiedAt_of_multiplicativeReduction`
  ([Thm, line 12](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_multiplicativeReduction.lean))
  applies — for a Tate curve, $`E[p]`$ is unramified at $`q`$ exactly when $`p`$
  divides the discriminant valuation (the $`p`$-torsion field is generated by
  a $`p`$-th root of the Tate period $`q_{\mathrm{Tate}}`$, and
  $`p \mid v_q(q_{\mathrm{Tate}})`$ kills the ramification).

The $`p`$-th powers in the Frey construction are doing double duty here:
they make the discriminant a perfect $`2p`$-th power (up to $`2^8`$), which is
also what later forces the mod-$`p`$ representation to have conductor $`2`$.

### 3.2. The prime $`p`$: the absorbing line from the two reduction types

`frey_inertia_at_p_trivial_on_submodule_or_quotient_at`
([Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at.lean))
produces the absorbing $`M`$ of §2 for the inertia group at one fixed place
$`A`$ over $`p`$, again by cases
([S file, lines 32–34](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at.lean)):

- **$`p \nmid abc`$ (good reduction at $`p`$):**
  `frey_inertia_at_p_filtration_of_not_dvd_abc`
  ([Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_filtration_of_not_dvd_abc.lean)).
  All $`a`$-invariants are $`A`$-integral and $`\Delta`$ is a unit in $`A`$ (since
  $`p \nmid 2^8 (abc)^{2p}`$), so reduction modulo the maximal ideal is an
  elliptic curve over the residue field, on which inertia acts trivially.
  Hence $`\sigma \cdot y - y`$ lies in the **reduction kernel**
  $`H = \{y : \tilde y = O\} = \{y : x(y) \notin A\} \cup \{O\}`$ for every
  $`\sigma`$ in inertia
  (`exists_reductionKernel_absorbing_inertia`,
  [Thm, line 8](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.lean));
  take $`M = H \cap E_P[p]`$. To see $`M \neq \top`$ one needs *some*
  $`p`$-torsion point with $`A`$-integral $`x`$-coordinate — produced from the
  stable line $`N`$ itself by
  `frey_exists_p_torsion_integral_abscissa`
  ([Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_exists_p_torsion_integral_abscissa.lean)).
  (Mathematically: $`M`$ is the connected part $`E[p]^0`$ in the
  connected–étale sequence, a line when the reduction is ordinary; the
  exhibited point also rules out the supersingular case $`M = \top`$.)
- **$`p \mid abc`$ (multiplicative reduction at $`p`$):**
  `frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line`
  ([Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line.lean)).
  Here $`p \mid \Delta`$, $`p \nmid c_4`$ (same coprimality computation), and
  $`M`$ is the **zero-component torsion** — the $`p`$-torsion reducing to the
  identity component of the special fiber, i.e. the
  $`\mu_p`$-line in the Tate picture
  (`exists_torsion_zeroComponent_submodule_of_multiplicativeReduction`,
  [Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction.lean);
  `InZeroComponentAt` is $`O`$, or a pole at $`A`$, or a point reducing to the
  node,
  [Def_EllipticCurve_ZeroComponentAt.lean, lines 13–19](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_EllipticCurve_ZeroComponentAt.lean)).
  Inertia preserves the component structure and acts trivially on the
  component group, so $`\sigma \cdot y - y \in M`$
  (`inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn`,
  [Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn.lean));
  and $`M \neq \top`$ because a $`p`$-torsion point in the zero component at
  residue characteristic $`p`$ is $`O`$ or has non-integral abscissa
  (`inZeroComponentAt_torsionBy_residueChar`,
  [Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_torsionBy_residueChar.lean)),
  while the stable line again
  supplies an integral-abscissa point
  (`frey_exists_p_torsion_integral_abscissa_of_stable_line`,
  [Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line.lean)).

Either way, $`M`$ with the absorbing property exists, §2 applies with
$`S = {}`$inertia at $`A`$, and the dichotomy holds at $`A`$. Note the
residue-characteristic twist: at $`q \neq p`$ multiplicative reduction with
$`p \mid v_q(\Delta)`$ made inertia *fully* trivial; at $`q = p`$ the same
Tate/connected–étale filtration only makes inertia *unipotent*, and which
of the two graded pieces is trivial on $`N`$ is exactly the dichotomy.

### 3.3. The prime $`2`$: wild inertia dies, tame inertia is unipotent

At $`2`$ the Frey curve is bad of multiplicative type
($`v_2(\Delta) = 2p\,v_2(abc) - 8 > 0`$ since $`4 \mid b`$), and
`frey_inertia_at_two_trivial_on_stable_submodule`
([Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean))
proves that inertia at $`2`$ is trivial on $`N`$ *and* on $`M/N`$ for the given
stable $`N`$ — i.e. unipotent with respect to any Galois-stable flag. Two
ingredients
([S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean, lines 167–175](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean)):

1. **The tame relation.** Local class field structure: for $`\tau`$ in
   inertia and $`\varphi`$ a Frobenius-like element,
   $`\varphi \tau \varphi^{-1} \equiv \tau^q`$ modulo wild inertia
   ($`q = {}`$residue characteristic, here $`2`$). The formalization obtains a
   global $`\varphi`$ with
   $`\varphi \tau \varphi^{-1} (\tau^2)^{-1} \in {}`$wild inertia at $`A`$
   (`ValuationSubring.exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime`,
   [Thm, line 8](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime.lean)).
2. **Wild inertia acts trivially on $`E_P[p]`$.** Wild inertia is a
   pro-$`2`$ group; $`E_P[p]`$ is an $`\mathbb{F}_p`$-space with $`p`$ odd, and for
   the semistable Frey curve the inertia action factors through the tame
   quotient. The formalization proves this directly
   (`frey_wild_inertia_at_two_trivial`,
   [Thm, line 11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_wild_inertia_at_two_trivial.lean)):
   a wild element $`\sigma`$ — presented concretely by
   $`\sigma z \cdot z^{-1} - 1 \in A.\mathrm{nonunits}`$ for all $`z \neq 0`$ —
   fixes every $`p`$-torsion point, by a 600-line hands-on valuation analysis
   of the explicit model ($`a_1 = 1`$, $`a_3 = a_6 = 0`$, $`a_2, a_4 \in \mathbb{Z}`$
   from the congruences, the node visible in the reduction;
   [S file, solution at line 520](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_wild_inertia_at_two_trivial.lean)).

Combining: $`\omega := \varphi \tau \varphi^{-1} (\tau^2)^{-1}`$ acts
trivially, so $`T := {}`$action of $`\tau`$ satisfies the operator identity
$`\Phi T \Phi^{-1} = T^2`$ on $`E_P[p]`$. Now the purely linear lemma
`LinearMap.eq_id_on_line_of_conj_eq_sq`
([S file, line 18](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean))
takes over: on the stable line $`N`$, $`T`$ is a scalar $`c`$ (dimension 1), and
conjugating by $`\Phi`$ (a scalar $`a`$ there, scalars commute) gives
$`c = c^2`$, so $`c \in \{0, 1\}`$; injectivity rules out $`0`$, hence
$`T|_N = \mathrm{id}`$. The same argument on the 1-dimensional quotient $`M/N`$
gives triviality there. In other words: the tame relation forces both
eigenvalues of $`\tau`$ to satisfy $`\lambda = \lambda^2`$, so inertia at $`2`$
lands in
$`\begin{pmatrix} 1 & * \\ 0 & 1 \end{pmatrix}`$ — trivial on $`N`$ *and* on
$`M/N`$ simultaneously, which is why the $`q = 2`$ case feeds both branches of
the global assembly (the `.1` / `.2` projections in §1).

## 4. How inertia is special in the proof

Inertia is not just one local input among others; the whole architecture of
the proof is "compute inertia everywhere, then appeal to the fact that
inertia sees everything". Four distinct mechanisms make this work.

**4.1. Presentation: inertia as a subgroup of the full Galois group.**
Mathlib's `A.inertiaSubgroup K` lives inside the decomposition subgroup;
the project maps it into $`\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]}
\overline{\mathbb{Q}}`$ itself
(`ValuationSubring.inertiaSubgroupIn`,
[Def_FLTPrelim_Ramification.lean, lines 21–22](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean)),
with `LiesOverPrime A q` just $`q \in A.\mathrm{nonunits}`$ (line 16). This
is what lets inertia elements act on global $`p`$-torsion points — no local
fields, no completions: a "place over $`q`$" is a valuation subring of
$`\overline{\mathbb{Q}}`$ with $`q`$ in its maximal ideal, and its inertia
consists of global automorphisms fixing $`A`$ and acting trivially on its
residue field (`mem_inertiaSubgroupIn_iff`,
[S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean, line 42](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean)).

**4.2. Local-to-global: inertia generates everything (Minkowski).** The
closure lemmas of §1 rest on
`AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le`
([Thm, line 6](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean)):
an **open** subgroup $`H \leq \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})`$
containing every inertia subgroup at every prime is $`\top`$. Proof sketch
from the source: openness in the Krull topology gives a finite Galois
$`L/\mathbb{Q}`$ with $`\mathrm{Gal}(\overline{\mathbb{Q}}/L) \leq H`$; the
image of $`H`$ in $`\mathrm{Gal}(L/\mathbb{Q})`$ still contains all inertia
groups (every inertia group of $`L`$ lifts to one of
$`\overline{\mathbb{Q}}`$); so its fixed field $`F`$ is unramified at every
prime, and Mathlib's
`NumberField.exists_not_isUnramifiedAt_int`
([ExistsRamified.lean, line 41, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/ExistsRamified.lean))
— the Minkowski input: every number field $`\neq \mathbb{Q}`$ ramifies
somewhere — forces $`F = \mathbb{Q}`$ and $`H = \top`$
(`NumberField.subgroup_eq_top_of_forall_inertia_le`,
[Thm, line 5](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_subgroup_eq_top_of_forall_inertia_le.lean);
[S file, lines 36–54](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_subgroup_eq_top_of_forall_inertia_le.lean)).
The openness hypothesis is discharged from the *finiteness* of
$`E_P[p]`$: each point's stabilizer is open (its coordinates are algebraic
numbers), and the fixer of the whole finite module is a finite intersection
(`stabilizer_point_isOpen`, `fixer_torsion_isOpen`,
[S_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial.lean, lines 14–46](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial.lean)).
This is the precise sense in which **inertia determines the global action
on a finite module**: an action trivial under all inertia groups at all
primes factors through the Galois group of an everywhere-unramified
extension of $`\mathbb{Q}`$ — which is trivial.

**4.3. One place per prime is enough.** The $`p`$-dichotomy is proved at a
single valuation subring $`A_0`$ over $`p`$ (§3.2), then transported to all
others: $`\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})`$ acts transitively
on the valuation subrings over $`p`$
(`ValuationSubring.exists_algEquiv_smul_eq_of_liesOverPrime`,
[Thm, line 7](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime.lean)),
inertia is conjugation-covariant
($`\sigma \in (\tau \cdot A_0)\text{-inertia} \Rightarrow
\tau^{-1} \sigma \tau \in A_0\text{-inertia}`$,
`conj_mem_inertiaSubgroupIn`, line 64 of the same S file), and the stable
line $`N`$ is preserved by $`\tau^{-1}`$ — so fixed (resp. cofixed) at $`A_0`$
conjugates to fixed (resp. cofixed) at every $`A`$ over $`p`$
([S file, lines 96–112](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean)).
Crucially the *choice of branch does not depend on the place*: the
dichotomy at $`p`$ is a single global disjunction, which is what the global
assembly of §1 branches on.

**4.4. The division of labor among primes.** Summarizing what inertia does
to the flag $`N \subset E_P[p]`$ at each prime, with
$`\tau \in I_q`$ in matrix form (basis adapted to $`N`$):

| Prime | Input | Action of $`I_q`$ on $`N \subset E_P[p]`$ | Why |
|---|---|---|---|
| $`q \neq 2, p`$, $`q \nmid abc`$ | good reduction | $`\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}`$ | Néron–Ogg–Shafarevich |
| $`q \neq 2, p`$, $`q \mid abc`$ | multiplicative, $`p \mid v_q(\Delta)`$ | $`\begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}`$ | Tate curve unramified criterion |
| $`q = 2`$ | multiplicative type; wild is pro-$`2`$ | $`\begin{pmatrix} 1 & * \\ 0 & 1 \end{pmatrix}`$ | tame relation $`\varphi\tau\varphi^{-1} \equiv \tau^2`$ $`\Rightarrow`$ $`\lambda = \lambda^2`$ on both graded pieces |
| $`q = p`$, $`p \nmid abc`$ | good reduction | unipotent w.r.t. the reduction kernel $`M`$ | inertia trivial on the special fiber |
| $`q = p`$, $`p \mid abc`$ | multiplicative | unipotent w.r.t. the zero component $`M \cong \mu_p`$ | Tate filtration |

Only at $`q = p`$ is the triviality <i>relative to a possibly different line
$`M`$</i>; the stable-line lemma of §2 then decides whether $`N`$ coincides with
$`M`$ (cofixed) or is transverse to it (fixed). Everywhere else inertia is
already trivial on the nose ($`q \neq 2p`$) or on both graded pieces of the
given flag ($`q = 2`$). After the closure lemma, the global dichotomy is
exactly the local one at $`p`$: **$`\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})`$
acts on $`N`$ as scalars with trivial quotient (cofixed) or as the identity
(fixed), according to which graded piece inertia at $`p`$ kills.**

For the human reader this is Serre's observation from note 004 §2 in its
proven form: the representation is
$`\begin{pmatrix} \chi & * \\ 0 & 1 \end{pmatrix}`$ or
$`\begin{pmatrix} 1 & * \\ 0 & \chi \end{pmatrix}`$, and the conductor-2 /
semistable analysis is what excludes the mixed case
$`\begin{pmatrix} \chi_1 & * \\ 0 & \chi_2 \end{pmatrix}`$ with both
characters nontrivial.

## 5. Key-point → code map

| Key point | Mathematical content | Where in the code |
|---|---|---|
| the dichotomy | stable $`N \subset E_P[p]`$, $`N \neq \bot, \top`$ ⇒ pointwise fixed or cofixed | [Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean:10](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean) |
| global assembly | branch on the $`p`$-dichotomy; close by prime-wise inertia check ($`2`$ / $`p`$ / unramified) | [S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean:33–55](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean) |
| linear core | $`\mathrm{card}\,V = p^2`$; absorbing $`M`$; $`N = M`$ ⇒ cofixed, $`N \cap M = \bot`$ ⇒ fixed | [Thm_Submodule_stableLine_fixed_or_cofixed_of_absorbing.lean:5](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_Submodule_stableLine_fixed_or_cofixed_of_absorbing.lean); [S:25–46](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_Submodule_stableLine_fixed_or_cofixed_of_absorbing.lean) |
| unramified away from $`2p`$ | good: NOS; multiplicative: $`q \nmid c_4`$ (coprimality), $`p \mid v_q(\Delta)`$ (the $`p`$-th powers) | [Thm_FreyPackage_freyGaloisRep_isUnramifiedAt.lean:15](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_freyGaloisRep_isUnramifiedAt.lean); [S:146–176 (`not_dvd_c₄Int`:70, `padicValInt_freyCurveInt_Δ`:130)](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_freyGaloisRep_isUnramifiedAt.lean) |
| absorbing line at $`p`$, good case | $`\Delta`$ a unit in $`A`$; reduction kernel absorbs inertia; integral-abscissa point ⇒ $`M \neq \top`$ | [Thm_FreyPackage_frey_inertia_at_p_filtration_of_not_dvd_abc.lean:11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_filtration_of_not_dvd_abc.lean); [Thm_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.lean:8](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.lean) |
| absorbing line at $`p`$, multiplicative case | zero-component ($`\mu_p`$) torsion absorbs inertia; $`p`$-torsion in it is $`O`$ or non-integral ⇒ $`M \neq \top`$ | [Thm_FreyPackage_frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line.lean:11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line.lean); [Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction.lean:11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction.lean); [Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn.lean:11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn.lean) |
| one place ⇒ all places at $`p`$ | $`\Gamma`$ transitive on valuation subrings over $`p`$; inertia conjugation-covariant; branch independent of place | [Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean:11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean); [Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime.lean:7](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime.lean); [S:64, 96–112](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean) |
| inertia at $`2`$ unipotent on any stable flag | wild trivial (pro-$`2`$ on odd torsion; direct 2-adic valuation analysis); tame relation ⇒ $`c = c^2`$ on line and quotient | [Thm_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean:11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean); [Thm_FreyPackage_frey_wild_inertia_at_two_trivial.lean:11](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_wild_inertia_at_two_trivial.lean); [`eq_id_on_line_of_conj_eq_sq`, S:18](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean) |
| inertia generates the Galois group | open subgroup containing all inertia is ⊤; openness from finiteness of $`E[p]`$; Minkowski | [Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean:6](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean); [Thm_NumberField_subgroup_eq_top_of_forall_inertia_le.lean:5](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_subgroup_eq_top_of_forall_inertia_le.lean); [mathlib ExistsRamified.lean:41, v4.33.0](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/ExistsRamified.lean) |
| closure lemmas | inertia-trivial at all primes on $`N`$ (resp. $`M/N`$) ⇒ globally trivial | [Thm_..._on_submodule_of_inertia_trivial.lean:8](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial.lean); [Thm_..._on_quotient_of_inertia_trivial.lean:8](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galois_action_trivial_on_quotient_of_inertia_trivial.lean) |
| where it is used | fixed branch dies (no rational $`p`$-torsion); cofixed branch = `HasGaloisStableCofixedLine` | note 004 §2; [Thm_FreyPackage_frey_reducible_hasCofixedLine.lean:15](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_reducible_hasCofixedLine.lean) |

## 6. Links

Lean sources (raw; quote line numbers as above):

- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_FLTPrelim_Ramification.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Definitions/Def_EllipticCurve_ZeroComponentAt.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_freyGaloisRep_isUnramifiedAt.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_filtration_of_dvd_abc_of_stable_line.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_inertia_at_p_filtration_of_not_dvd_abc.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_wild_inertia_at_two_trivial.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_exists_p_torsion_integral_abscissa.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_Submodule_stableLine_fixed_or_cofixed_of_absorbing.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galois_action_trivial_on_quotient_of_inertia_trivial.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_goodReduction.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_galoisRepUnramifiedAt_of_multiplicativeReduction.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_reductionKernel_absorbing_inertia.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_torsion_zeroComponent_submodule_of_multiplicativeReduction.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_inZeroComponentAt_smul_sub_of_mem_inertiaSubgroupIn.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_subgroup_eq_top_of_forall_inertia_le.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_ValuationSubring_exists_algEquiv_smul_eq_of_liesOverPrime.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_ValuationSubring_exists_algEquiv_conj_mul_pow_inv_wild_of_liesOverPrime.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_stable_submodule_fixed_or_cofixed.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_p_trivial_on_submodule_or_quotient_at.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_inertia_at_two_trivial_on_stable_submodule.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_frey_wild_inertia_at_two_trivial.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_FreyPackage_freyGaloisRep_isUnramifiedAt.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_Submodule_stableLine_fixed_or_cofixed_of_absorbing.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_subgroup_eq_top_of_forall_inertia_le.lean>
- <https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_WeierstrassCurve_galois_action_trivial_on_submodule_of_inertia_trivial.lean>

Annotated docs (viewable):

- [Def page: FLTPrelim_Ramification](https://tianyipeng.github.io/fermats-last-theorem/def/FLTPrelim_Ramification.html)
- [Route §3: irreducibility](https://tianyipeng.github.io/fermats-last-theorem/route/s3.html)

Mathlib v4.33.0:

- [`NumberField.exists_not_isUnramifiedAt_int`, ExistsRamified.lean (line 41)](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/NumberTheory/NumberField/ExistsRamified.lean)
- [`ValuationSubring.inertiaSubgroup`, RamificationGroup.lean](https://github.com/leanprover-community/mathlib4/blob/v4.33.0/Mathlib/RingTheory/Valuation/RamificationGroup.lean)

Background:

- J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes
  elliptiques*, Invent. Math. 15 (1972), 259–331 — §5.4(a) is the
  fixed-or-cofixed observation for the Frey curve (semistable, so inertia
  at $`p`$ acts through the fundamental characters of level 1).
- H. Darmon, F. Diamond, R. Taylor, *Fermat's Last Theorem*, Current
  Developments in Mathematics 1995, §2 — the semistable Frey curve and the
  shape of $`\bar\rho`$ restricted to inertia ($`\begin{pmatrix} \chi & * \\ 0 & 1 \end{pmatrix}`$-type statements).
