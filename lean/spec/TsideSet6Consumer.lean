/-
  Consumer specification for T12 SET 6, the Taylor–Wiles patching construction.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the SET-6 module
  `FLTForHuman/Patching/PatchingConstruction.lean` (the headline
  `Algebra.PatchingDatum.nonempty_patchingLevel_bot`) composed with SET 4's
  `FLTForHuman/Patching/LevelDescent.lean`
  (`Algebra.PatchingLevel.free_and_ker_eq_span`).

  Zone `[apply]` applies the SET-6 headline to an arbitrary patching datum. Zone
  `[compose]` is the real cross-module composition (playbook §7.2, the
  `Universal.lean` lesson): the level produced by SET 6 is handed to SET 4's
  descent lemma, so the file needs both modules and deleting either fails it.
  Zone `[subsingleton]` exercises the other branch of the theorem's
  `subsingleton_or_nontrivial` split.

  Note on the work order's §4 intent: the zone "builds the
  `Algebra.PatchingDatum` inputs" only as an *arbitrary* datum (the datum's fields
  are the pin's own data, not constructed here); constructing a concrete
  `PatchingLevel`-bearing datum is the job of SET 7's assembly. What is checked
  here is the wire, not a concrete instantiation.

  It is deliberately **not part of any library** (nothing globs `spec/`), so it can
  never break a verified build. Run it by hand:

      cd lean
      lake env lean spec/TsideSet6Consumer.lean 2>&1 | grep -c error
-/
import FLTForHuman.Patching.PatchingConstruction
import FLTForHuman.Patching.LevelDescent

set_option autoImplicit false

noncomputable section

namespace TsideSet6

open MvPowerSeries

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
variable [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
variable {ℓ r : ℕ} (hℓ : (ℓ : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
variable {R : Type} [CommRing R] [Algebra 𝒪 R] {M : Type} [AddCommGroup M] [Module R M]

/-- Zone `[apply]`: the SET-6 headline, applied to an arbitrary patching datum. -/
example (P : Algebra.PatchingDatum 𝒪 ℓ r R M) :
    Nonempty (Algebra.PatchingLevel 𝒪 r R M ⊥) :=
  Algebra.PatchingDatum.nonempty_patchingLevel_bot hℓ P

/-- Zone `[compose]`: the level produced by SET 6 is fed to SET 4's
`free_and_ker_eq_span`. This is the cross-module wire: it needs both modules. -/
example (P : Algebra.PatchingDatum 𝒪 ℓ r R M) [Nontrivial M] :
    ∃ L : Algebra.PatchingLevel 𝒪 r R M ⊥,
      Module.Free R M ∧ Module.annihilator R M = ⊥ ∧
        RingHom.ker L.ψ = Ideal.span (Set.range fun i : Fin r => L.φ (X i)) := by
  obtain ⟨L⟩ := Algebra.PatchingDatum.nonempty_patchingLevel_bot hℓ P
  exact ⟨L, L.free_and_ker_eq_span⟩

/-- Zone `[subsingleton]`: the theorem's other branch still produces a level, and
its module is the zero module; `Module.annihilator` there is `⊤`, so this only
reads the existence off. -/
example (P : Algebra.PatchingDatum 𝒪 ℓ r R M) [Subsingleton M] :
    Nonempty (Algebra.PatchingLevel 𝒪 r R M ⊥) :=
  Algebra.PatchingDatum.nonempty_patchingLevel_bot hℓ P

end TsideSet6
