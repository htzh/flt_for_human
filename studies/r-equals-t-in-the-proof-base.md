# $`R = T`$ in the FLT proof base

**Status: measured 2026-09-28 against the pin `aa2d8b3` with `tools/deps`.** This
note answers a narrow question: *what does the phrase "$`R = T`$" denote inside the
FLT proof base?* It is the proof-base companion to
[../base/011-deformations-hecke-algebras-and-r-equals-t.md](../base/011-deformations-hecke-algebras-and-r-equals-t.md),
which explains the mathematics; here the subject is the Lean objects, the exact
declarations, and their place in the citation graph. §6 reads the answer for port
scope, which is the part that bears on the Hecke face's T10.

**The short answer.** There is no declaration named `R_eq_T`. The phrase is
docs-site alias metadata hung on four theorem nodes; the actual isomorphism is one
`let` inside a single assembly theorem. What the proof base contains is the *two
halves* — a surjection $`R \twoheadrightarrow T`$ and the patching input that makes
it injective — and the equality is their conjunction. The closest thing to a
standalone statement of the equality is the 3,044-line
`CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd`
(one case), whose conclusion is `Function.Bijective φ` plus a complete-intersection
presentation.

Graph conventions are those of [hecke-finiteness-coverage.md](hecke-finiteness-coverage.md):
"closure" is the number of **theorem nodes** reached through the cites graph, and
the endgame is the 29,488-node closure of `FLT.fermatLastTheorem`. Pin sizes are
`S_`/`Def_` file lines. All citations are public URLs at `aa2d8b3`.

## 0. What names $`R = T`$, and what does not

The docs-site metadata attaches the phrase to **four** nodes — three by an explicit
`R=T; R = T` alias, one by its title. None is a declaration of the equality:

| node | title | alias | role |
|---|---|---|---|
| `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum` | Existence of a surjection R ↠ T | `R=T; R = T; Taylor-Wiles patching; Diamond` | the **first half** only |
| `WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd` | Modularity lifting at p=3 from a prescribed residual level | `…; R=T; …; p = 3` | consumes both halves |
| `WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd` | Modularity lifting at p∈{3,5} for p²∤ M₀ | `…; R=T; …; p = 5` | consumes both halves |
| `CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd` | R=T and complete intersection at cube-free ordinary level | (title says it) | the standalone equality + CI |

The attachments are a heuristic and loose in two ways: the fourth is attached by
title rather than alias, and the third is stated for
$`p \in \{3,5\}`$ although its alias says `p = 5`. The first is the one the alias
table is really about: it is the node the graph reaches for "$`R=T`$".

What this note calls the *R=T problem* is the following four objects:
$`R`$, $`T`$, the comparison map $`\varphi : R \to T`$, and the proof that
$`\varphi`$ is an isomorphism. The proof base formalises $`R`$ and $`T`$ as
structures, the map as an `AlgHom` produced by a universal property, and the
isomorphism as a patching argument.

## 1. The two sides, as Lean structures

### 1.1 $`R`$ — `GaloisRep.DeformationRingData`

`Definitions/Def_GaloisRep_DeformationRingData.lean` is 46 lines and 7
declarations; the structure is lines 8–40
([rendered 8–40](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_DeformationRingData.lean#L8-L40)).
It is the universal deformation ring of a residual representation, with the local
conditions left as a *parameter*:

```lean
structure GaloisRep.DeformationRingData (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop) :
    Type 1 where
  R : Type
  [instCommRing : CommRing R]
  [instIsLocalRing : IsLocalRing R]
  [instIsNoetherianRing : IsNoetherianRing R]
  [instIsAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [instAlgebra : Algebra 𝒪 R]
  [instIsLocalHom : IsLocalHom (algebraMap 𝒪 R)]
  residue_surjective : Function.Surjective (IsLocalRing.residue R ∘ algebraMap 𝒪 R)
  absIrr : ρbar.IsAbsolutelyIrreducible
  ρ : GaloisRepAdic R
  isOfType : 𝒟 ρ
  residual_isEquiv : ρ.residual.IsEquiv
    (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 R)))
  universal : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)],
      Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A) →
      ∀ ρA : GaloisRepAdic A, 𝒟 ρA →
        ρA.residual.IsEquiv
          (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 A))) →
        ∃! φ : R →ₐ[𝒪] A, ∃ hφ : IsLocalHom (φ : R →+* A),
          (ρ.baseChangeAlong (φ : R →+* A) hφ).IsEquiv ρA
```

Read against [base/011 §2](../base/011-deformations-hecke-algebras-and-r-equals-t.md):
the instance fields are "$`R`$ is a complete local Noetherian $`\mathcal{O}`$-algebra",
`ρ` is the universal deformation of type `𝒟`, and `universal` is the
unique-factorisation property. In the R=T application $`\mathcal{D}`$ is
`GaloisRep.ordinaryCondition 𝒪 p S` or `GaloisRep.flatCondition 𝒪 p S` (the
flat/ordinary cases of §3.5), and $`\bar\rho`$ is the mod-$`p`$ representation of
the curve.

### 1.2 $`T`$ — `CuspForm.HeckeGaloisRepDatum`

`Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean` is 38 lines and 6 declarations;
the structure is lines 8–36
([rendered 8–36](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean#L8-L36)).
It does **not** mention $`R`$; it packages a candidate $`T`$ with the Hecke map and
the Galois representation that is supposed to match the universal one:

```lean
structure CuspForm.HeckeGaloisRepDatum (N : ℕ) [NeZero N] (S : Set ℕ)
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (θ : heckeAlgebra N 2 S →+* IsLocalRing.ResidueField 𝒪)
    (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T] [Algebra 𝒪 T] [IsLocalHom (algebraMap 𝒪 T)]
    [Module.Finite 𝒪 T] [Module.Free 𝒪 T] : Type 1 where
  π : heckeAlgebra N 2 S →+* T
  residue_π : ∀ t, IsLocalRing.residue T (π t) =
    IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t)
  adjoin_range_π : Algebra.adjoin 𝒪 (Set.range π) = ⊤
  exists_point : ∀ χ : heckeAlgebra N 2 S →+* 𝒪,
    (∀ t, IsLocalRing.residue 𝒪 (χ t) = θ t) →
      ∃ ψ : T →ₐ[𝒪] 𝒪, ∀ t, ψ (π t) = χ t
  residue_surjective : Function.Surjective (IsLocalRing.residue T ∘ algebraMap 𝒪 T)
  ρ : GaloisRepAdic T
  charpoly_frob : ∀ (ℓ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ, A.IsFrobeniusAt σ ℓ →
        LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C (π (heckeAlgebra.T hℓ hℓN hℓS)) * X + C ((ℓ : T))
  residual_absIrr : ρ.residual.IsAbsolutelyIrreducible
```

Three fields are the mathematical content. `π` is the map from the *abstract*
Hecke algebra $`\mathbb{T}`$; `adjoin_range_π` says $`T`$ is generated over
$`\mathcal{O}`$ by the images of the Hecke operators; `exists_point` is the
interpolation property that turns every $`\mathcal{O}`$-valued eigensystem reducing
to $`\theta`$ into a point of $`T`$; and `charpoly_frob` is Eichler–Shimura: the
Frobenius characteristic polynomial is
$`X^2 - \pi(T_\ell) X + \ell`$. This is the shape the map $`R \to T`$ of
[base/011 §4](../base/011-deformations-hecke-algebras-and-r-equals-t.md) has to
match.

The abstract Hecke algebra itself, `CuspForm.heckeAlgebra N 2 S`, is the ported
`Subalgebra ℤ (Module.End ℂ (CuspForm (Gamma0 N) k))`
([`HeckeAlgebra.lean`](../lean/FLTForHuman/ModularForms/HeckeAlgebra.lean)), a
`Subalgebra` of the endomorphisms rather than the quotient presentation
`MvPolynomial Nat.Primes ℤ` of the deformation side. The pin's own free
presentation is `ModularCurve.HeckeAlg := MvPolynomial Nat.Primes ℤ`
([`Def_HeckeGalois_EichlerShimura.lean` 14](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_HeckeGalois_EichlerShimura.lean#L14)),
with `eigenIdeal` at line 30, `heckeTorsion` at line 49 and `mTorsionGaloisRep` at
line 63 — the eigenideal/Hecke-torsion vocabulary base/011 §6 quotes.

The concrete $`T`$ used in the $`p`$-adic case is the **local Hecke algebra**
`CuspForm.heckeLocal N S 𝒪 θ`, defined as the localisation of the base change to
$`\mathcal{O}`$ of the integral Hecke-lattice algebra `heckeLatticeAlgebra N S`, at
the complement of the character kernel `heckeCharKernel N S 𝒪 θ`
([`Def_CuspForm_HeckeLocal.lean` 128–132](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeLocal.lean#L128-L132));
it is the `T` argument of the CI theorem of §4.

### 1.3 The patching vocabulary

`Definitions/Def_Algebra_PatchingDatum.lean` is 44 lines and 9 declarations;
`Algebra.PatchingLevel` is lines 5–37 and `Algebra.PatchingDatum` lines 39–44
([rendered 5–44](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Algebra_PatchingDatum.lean#L5-L44)).
A `PatchingLevel` is a power-series presentation of a quotient of $`R`$ together
with a compatible lift of the module $`M`$ and a basis `b` whose relations are the
ideal `J`; a `PatchingDatum` is a whole family of levels indexed by $`n`$, with

```lean
level : ∀ n : ℕ, Algebra.PatchingLevel 𝒪 r R M
    (Ideal.span (Set.range fun j : Fin r =>
      ((1 + MvPowerSeries.X j) ^ (ℓ ^ n) - 1 : MvPowerSeries (Fin r) 𝒪)))
```

The `(1 + X_j)^{ℓ^n} - 1` is the classical Taylor–Wiles auxiliary-prime relation.
This is the object the numerical criterion of §4 has to produce.

## 2. The first half: the surjection $`R \twoheadrightarrow T`$

`P2M/Sol/S_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum.lean`
is **9 lines** ([rendered 7–8](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_GaloisRep_DeformationRingData_exists_surjective_algHom_of_heckeGaloisRepDatum.lean#L7-L8))
and is the node the alias table calls `R=T`:

```lean
theorem solution … (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟)
    … (H : CuspForm.HeckeGaloisRepDatum N S 𝒪 θ T) (hS : ∀ q, q.Prime → q ∣ N → q ∈ S)
    (h𝒟 : 𝒟 H.ρ) (hres : H.ρ.residual.IsEquiv (ρbar.baseChangeAlong …)) :
    ∃ φ : D.R →ₐ[𝒪] T, Function.Surjective φ ∧
      ∃ hφ : IsLocalHom (φ : D.R →+* T), (D.ρ.baseChangeAlong (φ : D.R →+* T) hφ).IsEquiv H.ρ := by
  obtain ⟨φ, ⟨hφ, he⟩, -⟩ := D.universal T H.residue_surjective H.ρ h𝒟 hres
  exact ⟨φ, H.surjective_of_isEquiv_baseChangeAlong hS D.ρ φ hφ he, hφ, he⟩
```

So the map exists by *applying $`R`$'s universal property to $`T`$* (`D.universal`,
with the uniqueness clause discarded), and surjectivity is a separate input from
the Hecke side: the premise `CuspForm.HeckeGaloisRepDatum.surjective_of_isEquiv_baseChangeAlong`
("Frobenius traces generate T: surjectivity of φ : R → T", closure 6). Its content
is exactly [base/011 §4](../base/011-deformations-hecke-algebras-and-r-equals-t.md):
$`R`$ is generated by traces of Frobenius and those are the Hecke eigenvalues
$`\pi(T_\ell)`$; the hypothesis `hS` (every prime dividing $`N`$ lies in $`S`$) is
what makes the away-from-$`S`$ traces generate.

Note the conclusion: **`∃`, not `∃!`, and `Surjective`, not `Bijective`.** The
9-line theorem is only half the story.

## 3. The second half: the isomorphism $`R \cong T`$

### 3.1 Where the equality actually is

The isomorphism is not exported. It is the one line

```lean
let e : D.R ≃ₐ[𝒪] T := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
```

at **line 69** of `P2M/Sol/S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean`
([rendered 57–69](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean#L57-L69)),
inside the 145-line assembly that goes from "the curve's $`\ell`$-adic
representation is a deformation of $`\bar\rho`$" to "$`W`$ is modular of an explicit
level". The three preceding steps are the whole R=T argument:

```lean
have hsurj : Function.Surjective φ :=
  H.surjective_of_isEquiv_baseChangeAlong (fun q hq hqN => Finset.mem_coe.mpr (hNS q hq hqN))
    D.ρ φ hφ hφρ                                   -- §2, the Hecke side

obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hp𝒪      -- the Taylor–Wiles level
obtain ⟨hfree, -, -⟩ := L.free_and_ker_eq_span       -- M is free over R, with zero annihilator

have hinj : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hann : x ∈ Module.annihilator D.R M := Module.mem_annihilator.mpr fun m => by
    rw [← hcompat x m, hx, zero_smul]
  rwa [(Module.annihilator_eq_bot (R := D.R) (M := M)).mpr inferInstance] at hann
```

The injectivity is the patching step: if $`\varphi(x) = 0`$ then, by the
compatibility `hcompat` of the two actions on the patched module $`M`$,
$`x`$ annihilates $`M`$; but patching makes $`M`$ free (and nontrivial) over
$`R`$, so its $`R`$-annihilator is $`\bot`$ and $`x = 0`$. Freeness is used
implicitly as a local instance. This is the formal content of "the patched ring's
size is transparent".

### 3.2 The injectivity engine, stated abstractly

The step is packaged as
`RingHom.bijective_of_surjective_of_smul_eq`
([`Theorems/Thm_RingHom_bijective_of_surjective_of_smul_eq.lean` 7](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_RingHom_bijective_of_surjective_of_smul_eq.lean#L7)),
whose auto-generated English is the cleanest statement of what R=T is in this
proof base:

> once the patched module is known to be free and nontrivial over the deformation
> ring, and the deformation ring acts on it through the surjection onto the Hecke
> algebra, that surjection is an isomorphism.

In Lean:

```lean
theorem RingHom.bijective_of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T]
    [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] [Nontrivial N]
    (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) :
    Function.Bijective g
```

Two hypotheses only: a compatible nontrivial free $`S`$-module $`N`$, and
surjectivity of $`g`$. No finiteness, no Noetherian hypothesis. This is the sense
in which R=T is "free": the equality is a consequence of the patching module, not
of a computation inside $`R`$ or $`T`$.

### 3.3 The abstract patching exit

`P2M/Sol/S_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean` (31 lines)
packages §3.1–3.2 for a general $`R, T, M`$:

```lean
theorem solution … (P : Algebra.PatchingDatum 𝒪 ℓ r R M) (RtoT : R →ₐ[𝒪] T)
    (hsurj : Function.Surjective RtoT) (hcompat : ∀ (x : R) (m : M), RtoT x • m = x • m) :
    Function.Bijective RtoT ∧ Module.Free R M ∧ Module.Free T M ∧
      Module.annihilator R M = ⊥ ∧
      ∃ f : Fin r → MvPowerSeries (Fin r) 𝒪,
        Nonempty ((MvPowerSeries (Fin r) 𝒪 ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪] T)
```

([rendered 12–31](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean#L12-L31)).
This is the node titled *Patching exit: R ≅ T, M free, T a power-series quotient*.
The proof is four lines:

```lean
obtain ⟨L⟩ := P.nonempty_patchingLevel_bot hℓ
obtain ⟨hfree, hann, hker⟩ := L.free_and_ker_eq_span
have hbij := (RtoT : R →+* T).bijective_of_surjective_of_smul_eq hcompat hsurj
exact ⟨hbij, hfree, Module.Free.of_surjective_of_smul_eq (RtoT : R →+* T) hcompat hsurj, hann, _,
  ⟨((Ideal.quotientEquivAlgOfEq 𝒪 hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective L.ψ_surjective)).trans (AlgEquiv.ofBijective RtoT hbij)⟩⟩
```

So the same two-line argument appears twice: bundled here, and inline in the
assembly §3.1.

### 3.4 The patching input

The free-and-annihilator half comes from `Algebra.PatchingLevel.free_and_ker_eq_span`
(310-line file, statement at
[301–310](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Algebra_PatchingLevel_free_and_ker_eq_span.lean#L301-L310)):

```lean
theorem solution … (L : Algebra.PatchingLevel 𝒪 r R M ⊥) :
    Module.Free R M ∧ Module.annihilator R M = ⊥ ∧
      RingHom.ker L.ψ = Ideal.span (Set.range fun i : Fin r => L.φ (MvPowerSeries.X i))
```

and the family of levels comes from `Algebra.PatchingDatum.nonempty_patchingLevel_bot`
(*Taylor–Wiles patching: a patched level with zero relation ideal*). The level `n`
of the datum carries the ideal $`J_n = ((1+X_j)^{\ell^n} - 1)`$; taking the
$`n \to \infty`$ limit (the `bot` ideal) is what gives freeness with zero
relations, i.e. the power-series presentation of $`T`$ and the freeness of $`M`$.

### 3.5 What the equality is used for

Once $`e : D.R \cong T`$ exists, the assembly (§3.1, lines 71–104) applies
$`R`$'s universal property a second time at $`A = \mathcal{O}`$ to the curve's
$`\ell`$-adic representation $`\rho_W`$, transports the resulting point across
$`e`$ to a map $`\psi_W : T \to \mathcal{O}`$, and compares Frobenius
characteristic polynomials via `GaloisRepAdic.charpoly_baseChangeAlong` and
`GaloisRepAdic.charpoly_eq_of_isEquiv` to identify $`\psi_W(\pi(T_\ell))`$ with
$`a_\ell(W)`$. Then the composite $`\chi = \psi_W \circ \pi`$ is a character of
$`\mathbb{T}`$ whose kernel is prime; the finiteness of the Hecke algebra plus
`Ideal.exists_ringHom_integralClosure_ker_eq` converts it into a complex-valued
character, and `CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq`
produces the eigenform. **This is where the Hecke port's T10 finiteness enters**:
line 107–108

```lean
haveI : Module.Finite ℤ (CuspForm.heckeAlgebra N 2 (S : Set ℕ)) :=
  CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hN one_le_two _
```

is the only use of `hN : CuspForm.HasIntegralStructure N 2` in the whole assembly.
The eigenform step is *downstream* of the isomorphism, not part of it.

## 4. The numerical criterion — why patching data exists at all

The other half of Wiles's proof — the half that is *not* the patching exit — is the
size comparison that produces the patching datum. Its vocabulary is the 24-lemma
`GaloisRep.DeformationRingData.*` family; two endpoints:

- `GaloisRep.DeformationRingData.exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses`
  (*Tangent space bound on generators of the deformation ring*, closure 7) is
  Mazur's identification of the reduced Zariski tangent space with a Selmer-type
  subspace of $`H^1(\mathbb{Q}, \mathrm{ad}^0\bar\rho)`$: it bounds the number of
  generators of $`\mathfrak{m}_R`$ by a cohomological dimension.
- `GaloisRep.DeformationRingData.length_cotangent_le_of_level_bounds`
  (*Cotangent length bound along a surjection of deformation rings*) is the
  length-counting form, referenced to Darmon–Diamond–Taylor §2.7.

The criterion is *applied* not in `GaloisRep` but in `CuspForm.heckeLocal`: the
nodes `CuspForm.heckeLocal.exists_algHom_length_cotangent_le_of_…` supply the
length inequality at the localised Hecke algebra, and the consumer
`WeierstrassCurve.exists_finite_extension_heckeGaloisRepDatum_patchingDatum_of_isResiduallyModular_of_level_…`
(*Hecke–Galois datum and patching datum at p=3, cube-free level*) turns it into
`Algebra.PatchingDatum 𝒪' p r D.R M`. Its English proof idea names the chain
exactly: the level-choice theorem produces $`S, N`$, `θ` and the integral
structure; the cotangent-length inequality gives the finite extension
$`\mathcal{O}'`$ and the patching data; then §3 concludes.

The one case where the *whole* R=T+CI statement is bundled is
`CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd`
(ordinary, $`p \parallel N`$, cubefree away from $`p`$; 3,044 lines, 75 cites,
closure 12,168). Its conclusion is

```lean
Function.Bijective φ ∧
  ∃ (n : ℕ) (f : Fin n → MvPowerSeries (Fin n) 𝒪'),
    Nonempty ((MvPowerSeries (Fin n) 𝒪' ⧸ Ideal.span (Set.range f)) ≃ₐ[𝒪'] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪' θ₁)
```

which is R=T plus the complete-intersection presentation, for
$`T =`$ `CuspForm.heckeLocal N S 𝒪' θ₁`. Its 12,168-node closure is the price of
the Selmer-side criterion; the *patching exit alone* is closure 13 (§6).

## 5. The route into `fermatLastTheorem`

Graph-exact shortest premise chain (each step cites the next):

```text
FLT.fermatLastTheorem
  FreyPackage.fermatLastTheoremFor_of_five_le
    FreyPackage.no_frey_package
      FreyPackage.frey_isModular
        WeierstrassCurve.modularity_of_semistableModel
          WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd
            GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum   (R ↠ T, §2)
            WeierstrassCurve.isModularModelOfLevel_of_patchingDatum                          (R ≅ T, §3.1)
```

`FreyPackage.no_frey_package` cites four inputs — `FreyPackage.Mazur_Frey`,
`FreyPackage.frey_isModular`, `FreyPackage.level_lowering_to_two`,
`ModularForm.S2_Gamma0_2_eq_zero` — i.e. the R=T leg is one of the four
contradiction legs, as base/011 §5 describes. `modularity_of_semistableModel`
cites both lifting theorems (p=3 and p∈{3,5}) plus `threeFiveSwitchCurve`; the
p=3 theorem's proof has the two cases of §4 inlined at lines 335–352 of its
[384-line source](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd.lean#L335-L352),
one for the flat condition and one for the ordinary condition:

```lean
obtain ⟨D⟩ := WeierstrassCurve.nonempty_deformationRingData_flatCondition_of_isSemistableModel …
obtain ⟨φ, -, hφ, hφρ⟩ :=
  GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum D HD hNS' (hflatT …) hresT
obtain ⟨M, …, hcompat, r, ⟨P⟩⟩ := hPflat … D φ hφ hφρ
exact ⟨_, WeierstrassCurve.isModularModelOfLevel_of_patchingDatum p W hΔ hp𝒪' D hS hNS hN HD
  φ hφ hφρ hcompat P _ (hEflat …) hWres hWfrob, …⟩
```

The `∃ φ` from §2 is fed straight into the assembly of §3.1, which internally
upgrades it to $`\cong`$; the equality never appears as a named hypothesis or
conclusion between them. That is the exact sense in which "there is no single
declaration named after the equality": it is a *local* isomorphism in the p=3
proof, and only the CI theorem of §4 exports one.

## 6. Port-scope reading — the T side of $`R = T`$

This section reads the above for the Hecke port's T10 decision. The T side is not
one module; measured against the pin, the R=T neighbourhood is:

| family | nodes | ported? |
|---|---:|---|
| nodes whose statement or proof imports `Def_GaloisRep_DeformationRingData`, `Def_CuspForm_HeckeGaloisRepDatum` or `Def_Algebra_PatchingDatum` | 167 | no |
| `CuspForm.heckeLocal.*` (local Hecke algebra, cotangent inequalities, the CI theorem) | 88 | no |
| `CuspForm.TWLevel.*` (Taylor–Wiles level Hecke rings and modules) | 29 | no |
| union of the above | **266** | — |
| of which use **both** the R datum and the T datum | 28 | — |

All 266 lie inside `fermatLastTheorem`'s closure. What *is* ported:

- the abstract Hecke algebra `CuspForm.heckeAlgebra` and its operators
  ([`HeckeAlgebra.lean`](../lean/FLTForHuman/ModularForms/HeckeAlgebra.lean));
- the T10 finiteness, `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra`
  ([`HeckeFiniteAlgebra.lean` 90](../lean/FLTForHuman/ModularForms/HeckeFiniteAlgebra.lean)),
  which is a premise of the assembly at §3.5 (line 108) — so the Hecke port is
  already **on** the R=T path, not merely adjacent to it.

Nothing of the R=T vocabulary is ported: `DeformationRingData`,
`HeckeGaloisRepDatum` and `PatchingDatum` have **zero** occurrences in
`lean/FLTForHuman/`. So any T-side port starts by writing the three `Def_`
modules (46 + 38 + 44 pin lines, but they pull the `Def_Deformations_*` and
`Def_GaloisRep_Adic` substrate) and then the theorem layers.

Frontier distance (`tools/deps/frontier.py`, `--no-rank`, theorem nodes only;
definition modules are additional) for the three unit targets:

| target | port cone | in frontier | needed | needed lines |
|---|---:|---:|---:|---:|
| `GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum` (§2, R ↠ T) | 7 | 0 | **7** | 610 |
| `Algebra.PatchingDatum.bijective_and_free_of_surjective` (§3.3, the patching exit) | 13 | 0 | **13** | 5,690 |
| `WeierstrassCurve.isModularModelOfLevel_of_patchingDatum` (§3.1, the assembly = R ≅ T) | 65 | 39 | **26** | 7,287 |
| `CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd` (§4, R ≅ T + CI) | 12,168 | — | Selmer-side criterion | — |

The 26 needed nodes for the assembly are, by namespace: `MvPowerSeries` 6,
`CuspForm` 7, `ValuationSubring` 3, `Algebra` 2, `GaloisRepAdic` 2, `Module` 2,
`Ideal`, `IsAdicComplete`, `RingHom`, `WeierstrassCurve` 1 each. The largest
single block is the 310-line `Algebra.PatchingLevel.free_and_ker_eq_span`; the
`MvPowerSeries` block (`isNoetherianRing_of_finite`, `mem_pow_span_X_of_coeff_eq_zero`,
`isAdicComplete_maximalIdeal`, …) is the power-series algebra the patching level
needs; the `CuspForm` block is the eigenform extraction of §3.5, which **consumes
the already-ported T10 finiteness**.

Three readings for T10 scope:

1. **The finiteness half is already the reusable T-side kernel.** T10's
   `HasIntegralStructure.moduleFinite_heckeAlgebra` sits inside the R=T assembly
   (line 108) and is what turns the transported point $`\psi_W`$ into an
   eigenform. It is the one piece of the T side the port owns, and §3.5 is its
   first consumer on the critical path. A future T-side effort inherits it rather
   than re-deriving it.
2. **The *equality* is cheap once the vocabulary exists; the *criterion* is not.**
   The patching exit is 13 nodes / 5,690 lines, and the assembly is 26 needed
   nodes / 7,287 lines — both bounded, mathlib-adjacent (power series, DVRs,
   Frobenius existence). By contrast the Selmer-side cotangent criterion behind
   the standalone CI theorem has a 12,168-node closure. If T10 is ever extended
   toward the T side, the honest unit is "vocabulary + patching exit + assembly",
   not the criterion.
3. **A T-side port is gated on the three `Def_` structures first.** Because the
   theorem layer is *parameterised* by `DeformationRingData` and
   `HeckeGaloisRepDatum`, the port order is forced: write
   `Def_GaloisRep_DeformationRingData`, `Def_CuspForm_HeckeGaloisRepDatum`,
   `Def_Algebra_PatchingDatum` (and their `Def_Deformations_*` substrate), then
   the §2/§3 lemma layer. The statements are stable — the whole R=T content is
   already abstracted into the structures — which is why the assembly's statements
   can be ported verbatim, as the Hecke port has done for the operator layer.

This note does **not** propose taking that port. It records what the target is, so
the T10 scope decision can be made against numbers rather than the alias table.

**Landed (2026-09-28).** The definition layer was ported as topic 11 — 13 modules,
142 public declarations, checker `1623 identical / 0 mismatched / 0 missing`,
`lake build` green, `#print axioms` clean — with work order
[../lean/topics/hecke/TOPIC-t11-t-side-definitions.md](../lean/topics/hecke/TOPIC-t11-t-side-definitions.md)
and record [../lean/logs/t-side-port.md](../lean/logs/t-side-port.md). The theorem
layer above it (the 24 `GaloisRep.DeformationRingData.*` lemmas, the 18
`HeckeGaloisRepDatum.*` lemmas, the patching exit and the assembly) is still
unported.

## 7. Reproduction

Closures, families and the R-vs-T overlap:

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from fltdata import FltData
d = FltData()
def cl(i):
    seen, st = set(), [i]
    while st:
        j = st.pop()
        if j in seen: continue
        seen.add(j); st.extend(d.cites(j))
    return seen
core = set()
for s in ['CuspForm_HeckeGaloisRepDatum', 'GaloisRep_DeformationRingData', 'Algebra_PatchingDatum']:
    di = d.def_index[s]
    core |= {i for i in range(len(d.names)) if di in d.stmt_defs(i) or di in d.proof_defs(i)}
hgd = {i for i in range(len(d.names))
       if d.def_index['CuspForm_HeckeGaloisRepDatum'] in d.stmt_defs(i)
       or d.def_index['CuspForm_HeckeGaloisRepDatum'] in d.proof_defs(i)}
drd = {i for i in range(len(d.names))
       if d.def_index['GaloisRep_DeformationRingData'] in d.stmt_defs(i)
       or d.def_index['GaloisRep_DeformationRingData'] in d.proof_defs(i)}
hl = {i for i, n in enumerate(d.names) if n.startswith('CuspForm.heckeLocal.')}
tw = {i for i, n in enumerate(d.names) if n.startswith('CuspForm.TWLevel.')}
print('core-def users', len(core), '| heckeLocal', len(hl), '| TWLevel', len(tw), '| union', len(core | hl | tw))
print('use both the R datum and the T datum', len(hgd & drd))
end = cl(d.index['FLT.fermatLastTheorem'])
print('endgame', len(end), '| all inside:', (core | hl | tw) <= end)
for n in ['GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum',
          'Algebra.PatchingDatum.bijective_and_free_of_surjective',
          'WeierstrassCurve.isModularModelOfLevel_of_patchingDatum']:
    i = d.index[n]; print(len(cl(i)), n)
PY
```

Frontier distances:

```bash
cd tools/deps
python3 frontier.py --no-rank --target GaloisRep.DeformationRingData.exists_surjective_algHom_of_heckeGaloisRepDatum
python3 frontier.py --no-rank --target Algebra.PatchingDatum.bijective_and_free_of_surjective
python3 frontier.py --no-rank --target WeierstrassCurve.isModularModelOfLevel_of_patchingDatum
```

The single line §3.1 quotes:

```bash
grep -n "AlgEquiv.ofBijective φ" \
  ~/proj/fermats-last-theorem/P2M/Sol/S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean
# 69:  let e : D.R ≃ₐ[𝒪] T := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
```

## 8. Pointers

- [../base/011-deformations-hecke-algebras-and-r-equals-t.md](../base/011-deformations-hecke-algebras-and-r-equals-t.md)
  — the mathematics of $`R`$, $`T`$, the map and the criterion (§§1–5) and the
  declaration table of the pin's deformation vocabulary (§6).
- [../math/018-t-side-definitions.md](../math/018-t-side-definitions.md) — the
  T-side definitions themselves, in mathematical terms: the Galois substrate,
  the universal ring, the Hecke/lattice algebra, $`T_\theta`$, the Hecke–Galois
  datum, and the patching vocabulary, with the module inventory of §7.
- [t-side-driver.md](t-side-driver.md) — which T-side target to port next: the
  $`R \cong T`$ assembly as a conditional capstone, with the C′-adjusted
  frontier estimate.
- [hecke-finiteness-coverage.md](hecke-finiteness-coverage.md) §6 — what the
  T side adds, and the 168-node measurement this note re-measures as 266 under a
  wider definition.
- [flt-non-frey-segments.md](flt-non-frey-segments.md) §3.5 — the R=T machinery
  as one of the seven segments (2,234 nodes / 617,081 lines), with the namespace
  breakdown.
- [eichler-shimura-scout.md](eichler-shimura-scout.md) — the neighbouring
  Eichler–Shimura comparison, the other input to the modularity-lifting leg.
- [../lean/topics/PORTING-Hecke.md](../lean/topics/PORTING-Hecke.md) §3.2 and
  [../lean/logs/hecke-port.md](../lean/logs/hecke-port.md) §T10 — the ported
  finiteness that §3.5 consumes.
- Pin sources: [`Def_GaloisRep_DeformationRingData.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_GaloisRep_DeformationRingData.lean),
  [`Def_CuspForm_HeckeGaloisRepDatum.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_CuspForm_HeckeGaloisRepDatum.lean),
  [`Def_Algebra_PatchingDatum.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Algebra_PatchingDatum.lean),
  [`S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_isModularModelOfLevel_of_patchingDatum.lean),
  [`S_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Algebra_PatchingDatum_bijective_and_free_of_surjective.lean).
