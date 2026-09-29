/-
  Consumer specification for T12 SET 4, the patching descent-and-freeness engine.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the SET-4 modules, imported from **three different**
  new modules:

  * `FLTForHuman/Patching/LevelDescent.lean` —
    `Algebra.PatchingLevel.free_and_ker_eq_span`;
  * `FLTForHuman/Algebra/FaithfulFreeness.lean` —
    `RingHom.bijective_of_surjective_of_smul_eq` and
    `Module.Free.of_surjective_of_smul_eq`;
  * `FLTForHuman/Algebra/RegularSequenceFreeness.lean` — the generic freeness
    lemma the descent's `free_N` calls;
  * and (transitively, through `LevelDescent`) the `MvPowerSeries` facts of
    `FLTForHuman/Algebra/MvPowerSeriesRegular.lean`.

  Zone `[descent]` **builds** an `Algebra.PatchingLevel` over a discrete
  valuation ring (at `r = 0`, where the power-series ring is the base ring, so the
  presentation is trivial but every field is discharged) and applies
  `Algebra.PatchingLevel.free_and_ker_eq_span` to it, reading off all three
  outputs.

  Zone `[engine]` is the real cross-module composition (playbook §7.2): it applies
  `free_and_ker_eq_span` to an abstract level `L` and hands the resulting
  `Module.Free R M` instance to `RingHom.bijective_of_surjective_of_smul_eq`, so a
  compatible surjection `g : R →+* T` is bijective. Deleting `LevelDescent.lean`
  or `FaithfulFreeness.lean` fails this file.

  It is deliberately **not part of any library** (nothing globs `spec/`), so it can
  never break a verified build. Run it by hand:

      cd lean
      lake env lean spec/TsideSet4Consumer.lean 2>&1 | grep -c error
-/
import FLTForHuman.Patching.LevelDescent
import FLTForHuman.Algebra.FaithfulFreeness
import FLTForHuman.Algebra.RegularSequenceFreeness
import FLTForHuman.Algebra.MvPowerSeriesRegular
import FLTForHuman.Patching.Defs.PatchingDatum

set_option autoImplicit false

noncomputable section

universe u v

namespace TsideSet4

/-! ## Zone `[descent]` — building a level and reading off the three outputs -/

-- The `r = 0` patching level: the power-series ring on no variables is the base
-- ring, so `φ`, `ψ`, `π` are the identity and the single generator `b = 1`
-- presents it trivially — but the structure is genuinely instantiated.
example (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] :
    Algebra.PatchingLevel 𝒪 0 (MvPowerSeries (Fin 0) 𝒪) (MvPowerSeries (Fin 0) 𝒪)
      (⊥ : Ideal (MvPowerSeries (Fin 0) 𝒪)) :=
  { N := MvPowerSeries (Fin 0) 𝒪
    φ := AlgHom.id 𝒪 (MvPowerSeries (Fin 0) 𝒪)
    ψ := AlgHom.id 𝒪 (MvPowerSeries (Fin 0) 𝒪)
    ψ_surjective := Function.surjective_id
    ψ_φ_X := fun i => i.elim0
    π := AddMonoidHom.id (MvPowerSeries (Fin 0) 𝒪)
    π_smul := fun f x => rfl
    π_surjective := Function.surjective_id
    ker_π := fun x => by simp
    d := 1
    b := fun _ => 1
    b_span := fun x => ⟨fun _ => x, by simp⟩
    b_rel := fun c => by simp }

-- All three outputs of the descent at that level.
example (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] :
    Module.Free (MvPowerSeries (Fin 0) 𝒪) (MvPowerSeries (Fin 0) 𝒪) ∧
      Module.annihilator (MvPowerSeries (Fin 0) 𝒪) (MvPowerSeries (Fin 0) 𝒪) = ⊥ ∧
      RingHom.ker (AlgHom.id 𝒪 (MvPowerSeries (Fin 0) 𝒪)).toRingHom =
        Ideal.span (Set.range fun i : Fin 0 =>
          (AlgHom.id 𝒪 (MvPowerSeries (Fin 0) 𝒪)) (MvPowerSeries.X i)) :=
  Algebra.PatchingLevel.free_and_ker_eq_span
    { N := MvPowerSeries (Fin 0) 𝒪
      φ := AlgHom.id 𝒪 (MvPowerSeries (Fin 0) 𝒪)
      ψ := AlgHom.id 𝒪 (MvPowerSeries (Fin 0) 𝒪)
      ψ_surjective := Function.surjective_id
      ψ_φ_X := fun i => i.elim0
      π := AddMonoidHom.id (MvPowerSeries (Fin 0) 𝒪)
      π_smul := fun f x => rfl
      π_surjective := Function.surjective_id
      ker_π := fun x => by simp
      d := 1
      b := fun _ => 1
      b_span := fun x => ⟨fun _ => x, by simp⟩
      b_rel := fun c => by simp }

/-! ## Zone `[engine]` — the descent's free output feeds the faithful-freeness engine -/

-- The cross-module composition: `free_and_ker_eq_span` supplies `Module.Free R M`,
-- which `RingHom.bijective_of_surjective_of_smul_eq` consumes to upgrade a
-- compatible surjection to a bijection.
example {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (L : Algebra.PatchingLevel 𝒪 r R M ⊥)
    {T : Type} [Ring T] [Module T M]
    (g : R →+* T) (hg : ∀ (s : R) (n : M), g s • n = s • n)
    (hsurj : Function.Surjective g) : Function.Bijective g := by
  have : Module.Free R M := (Algebra.PatchingLevel.free_and_ker_eq_span L).1
  exact RingHom.bijective_of_surjective_of_smul_eq g hg hsurj

-- The second output, `Module.annihilator R M = ⊥`, is what SET 3's capstone takes
-- frozen as `hann`; SET 4 recovers it (as the descent proves it) rather than
-- re-deriving it from freeness.
example {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {r : ℕ} {R : Type} [CommRing R] [Algebra 𝒪 R]
    {M : Type} [AddCommGroup M] [Module R M] [Nontrivial M]
    (L : Algebra.PatchingLevel 𝒪 r R M ⊥) : Module.annihilator R M = ⊥ :=
  (Algebra.PatchingLevel.free_and_ker_eq_span L).2.1

/-! ## Zone `[regular]` — the generic freeness lemma the descent applies -/

-- `LevelDescent.free_N` applies this lemma; exercising it here keeps the
-- `RegularSequenceFreeness` module on the consumer's import path as a live
-- dependency rather than a `#check`.
example {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (xs : List R) (hxs : RingTheory.Sequence.IsRegular R xs)
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal R)
    (s : List R) (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M s) (hlen : s.length = xs.length)
    (hfl : IsFiniteLength R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M))) :
    Module.Free R M :=
  Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
    xs hxs hspan s hs hreg hlen hfl

end TsideSet4

end
