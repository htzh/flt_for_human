/-
  Cross-module wire test for **S-3**, the primitive-coset / `jLattice` column:
  the headline
  `PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic`, the
  `:449–600` transport block, the `hu5c` product-cyclicity/coprimality criterion,
  the `KwSublatticeQuotientZZTransport` class and its `qtzz_*` proof, and the
  generic `ℤ²` block of `FLTForHuman/Algebra/IntPairSubgroup.lean`.

  A `spec/` probe, not a library module: it is outside every lake target and is run
  with `lake env lean`, so a green library build stays meaningful. Deleting either
  `FLTForHuman/Algebra/IntPairSubgroup.lean` or
  `FLTForHuman/Elliptic/PeriodPair/PrimCosetReps.lean` makes it fail (the imports
  and every zone name vanish).

  Executed zones (each a real composition, no `#check`, no `sorry`):

  * zone 1 — the generic `ℤ²` invariants at an **abstract** `H ≤ ℤ × ℤ` and at a
    concrete `latticeOf 3 5 2`: `latticeOf_canonical_eq` reassembles `H`,
    `index_eq_dOf_mul_aOf` reads its index, and `mem_latticeOf_iff` recovers a
    member;
  * zone 2 — the **concrete `ofTau`-style lattice**: `kw_exists_scale_ofTau_lattice_eq`
    at `PeriodPair.ofTau τ`, and `kw_sublattice_eq_span`/`kw_HZZ_index` read the
    sublattice off the HNF triple;
  * zone 3 — the criterion: `hu5c_not_isAddCyclic_zmod_prod` at `ZMod p × ZMod p`
    and `hu5c_gcd_eq_one_of_isAddCyclic` at an arbitrary `H`;
  * zone 4 — the **S-2-shaped hypotheses** (`hsub`/`hidx`/`hcyc`) fed into the
    headline at a concrete `ofTau` pair, plus the transport class at its pin name.
-/
import FLTForHuman.Algebra.IntPairSubgroup
import FLTForHuman.Elliptic.PeriodPair.PrimCosetReps

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open scoped UpperHalfPlane PeriodPair
open UpperHalfPlane PeriodPair

namespace PeriodPairPrimCosetConsumer

/-! ### Zone 1 — the generic `ℤ²` invariants -/

/-- **The structure theorem** at an abstract `H ≤ ℤ × ℤ`: the canonical HNF triple
reassembles `H`. -/
example (H : AddSubgroup (ℤ × ℤ)) :
    IntPairSubgroup.latticeOf (IntPairSubgroup.aOf H) (IntPairSubgroup.dOf H)
        (IntPairSubgroup.bOf H) = H :=
  IntPairSubgroup.latticeOf_canonical_eq H

/-- The index of an abstract `H` is the product `dOf H * aOf H`. -/
example (H : AddSubgroup (ℤ × ℤ)) :
    H.index = IntPairSubgroup.dOf H * IntPairSubgroup.aOf H :=
  IntPairSubgroup.index_eq_dOf_mul_aOf H

/-- The projection exact sequence: `ker fst = range inr` on `ℤ × ℤ`. -/
example : (AddMonoidHom.fst ℤ ℤ).ker = (AddMonoidHom.inr ℤ ℤ).range :=
  IntPairSubgroup.ker_fst_eq_range_inr

/-- `(3, 2)` lies in the concrete HNF lattice `latticeOf 3 5 2` (as `1 • (3, 2)`),
certified through `mem_latticeOf_iff`. -/
example : (3, 2) ∈ IntPairSubgroup.latticeOf 3 5 2 := by
  rw [IntPairSubgroup.mem_latticeOf_iff]
  exact ⟨1, 0, by norm_num⟩

/-- The canonical triple of `latticeOf 3 5 2` reassembles it (a concrete instance of
the structure theorem). -/
example :
    IntPairSubgroup.latticeOf (IntPairSubgroup.aOf (IntPairSubgroup.latticeOf 3 5 2))
        (IntPairSubgroup.dOf (IntPairSubgroup.latticeOf 3 5 2))
        (IntPairSubgroup.bOf (IntPairSubgroup.latticeOf 3 5 2))
      = IntPairSubgroup.latticeOf 3 5 2 :=
  IntPairSubgroup.latticeOf_canonical_eq _

/-! ### Zone 2 — the transport at a concrete `ofTau` lattice -/

/-- Every period pair — here the concrete `ofTau τ` — is a rescaled `ofTau`. -/
example (τ : ℍ) : ∃ (α : ℂˣ) (τ' : ℍ),
    ((PeriodPair.ofTau τ).scale α).lattice = (PeriodPair.ofTau τ').lattice :=
  ModularCurve.kw_exists_scale_ofTau_lattice_eq (PeriodPair.ofTau τ)

/-- The sublattice of `ofTau τ` is spanned by the HNF triple read off
`kw_HZZ τ L'`. -/
example (τ : ℍ) (L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ (PeriodPair.ofTau τ).lattice) :
    L'.lattice = Submodule.span ℤ
      {(IntPairSubgroup.aOf (ModularCurve.kw_HZZ τ L') : ℂ) * (τ : ℂ)
          + (IntPairSubgroup.bOf (ModularCurve.kw_HZZ τ L') : ℂ),
        (IntPairSubgroup.dOf (ModularCurve.kw_HZZ τ L') : ℂ)} :=
  ModularCurve.kw_sublattice_eq_span τ L' hsub

/-- The `ℤ²` model of `L'` has the same index as the sublattice quotient. -/
example (τ : ℍ) (L' : PeriodPair) :
    (ModularCurve.kw_HZZ τ L').index = PeriodPair.sublatticeIndex (PeriodPair.ofTau τ) L' :=
  ModularCurve.kw_HZZ_index τ L'

/-- `ofTau τ` is spanned by its own two periods (the concrete lattice of zone 2). -/
example (τ : ℍ) : (PeriodPair.ofTau τ).lattice = Submodule.span ℤ {(τ : ℂ), 1} :=
  PeriodPair.ofTau_lattice τ

/-- `jLattice` depends only on the lattice. -/
example (L L' : PeriodPair) (h : L.lattice = L'.lattice) : L.jLattice = L'.jLattice :=
  PeriodPair.jLattice_eq_of_lattice_eq h

/-! ### Zone 3 — the product-cyclicity / coprimality criterion -/

/-- `ZMod p × ZMod p` is not cyclic for `p > 1`. -/
example (p : ℕ) (hp : 1 < p) : ¬ IsAddCyclic (ZMod p × ZMod p) :=
  ModularCurve.kw_surgehgf4_hu5c_not_isAddCyclic_zmod_prod hp

/-- A cyclic quotient of `ℤ × ℤ` forces the HNF triple primitive. -/
example (H : AddSubgroup (ℤ × ℤ)) (hN : H.index ≠ 0)
    (hcyc : IsAddCyclic ((ℤ × ℤ) ⧸ H)) :
    Nat.gcd (IntPairSubgroup.aOf H)
      (Nat.gcd (IntPairSubgroup.bOf H).toNat (IntPairSubgroup.dOf H)) = 1 :=
  ModularCurve.kw_surgehgf4_hu5c_gcd_eq_one_of_isAddCyclic hN hcyc

/-! ### Zone 4 — the S-2-shaped hypotheses fed into the headline -/

/-- **The transport class**, proved at its pin name. -/
example : ModularCurve.KwSublatticeQuotientZZTransport :=
  ModularCurve.kw_surgehgf4_qtzz_proved

/-- The transport applied to the S-2 hypothesis shape: cyclicity of the quotient of an
abstract inclusion transports to the `ℤ²` quotient of any scaled `ofTau` model. -/
example (L L' : PeriodPair) (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice)
    (α : ℂˣ) (τ : ℍ) (hlat : (L.scale α).lattice = (PeriodPair.ofTau τ).lattice)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    IsAddCyclic ((ℤ × ℤ) ⧸ ModularCurve.kw_HZZ τ (L'.scale α)) :=
  ModularCurve.kw_surgehgf4_qtzz_proved L L' hsub α τ hlat hcyc

/-- **The headline** at a concrete `ofTau` pair, with the S-2-shaped
`hsub`/`hidx`/`hcyc` hypotheses: it produces the primitive coset triple and the two
`jLattice` equalities. -/
example (τ τ' : ℍ) (N : ℕ) [NeZero N]
    (hsub : ((PeriodPair.ofTau τ').lattice : Set ℂ) ⊆ (PeriodPair.ofTau τ).lattice)
    (hidx : PeriodPair.sublatticeIndex (PeriodPair.ofTau τ) (PeriodPair.ofTau τ') = N)
    (hcyc : IsAddCyclic
      (PeriodPair.sublatticeQuotient (PeriodPair.ofTau τ) (PeriodPair.ofTau τ'))) :
    ∃ (a b d : ℕ) (τ₀ σ : ℍ), (a, b, d) ∈ ModularCurve.primCosetReps N ∧
      (σ : ℂ) = ((a : ℂ) * τ₀ + b) / d ∧
      (PeriodPair.ofTau τ).jLattice = (PeriodPair.ofTau τ₀).jLattice ∧
        (PeriodPair.ofTau τ').jLattice = (PeriodPair.ofTau σ).jLattice :=
  PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
    (PeriodPair.ofTau τ) (PeriodPair.ofTau τ') hsub hidx hcyc

/-- The primitive-coset membership predicate the headline concludes with, at its pin
name. -/
example {N a b d : ℕ} (hN : N ≠ 0) :
    (a, b, d) ∈ ModularCurve.primCosetReps N ↔
      a * d = N ∧ b < d ∧ Nat.gcd a (Nat.gcd b d) = 1 :=
  ModularCurve.mem_primCosetReps hN

end PeriodPairPrimCosetConsumer

end
