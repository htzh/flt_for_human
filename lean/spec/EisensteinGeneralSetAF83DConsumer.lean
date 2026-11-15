/-
  SET-AF83D consumer: the Eisenstein piece, read at the empty family and at an unramified place.

  **The rows.** `FLTForHuman/EisensteinGeneral/PieceLatticeMajorant.lean` carries the summable
  majorant of the lattice sum (`exists_summable_majorant_of_lattice_vanishing`), whose hypotheses are
  15 shapes of decay, boundedness and vanishing. `FLTForHuman/EisensteinGeneral/FactorizationDatum.lean`
  carries the datum the other row of the order produces, and
  `FLTForHuman/EisensteinGeneral/PieceFactorizationDatum.lean` the row that produces it.

  **The readings.**

  * Zone 1 — **the majorant row's hypotheses are all satisfiable.** Fifteen hypotheses is enough that
    a statement can be uninstantiable and nobody notice (an over-strong `∀` in a hypothesis, a
    `FractionalIdeal` that no term inhabits, a product over `{w // w.IsReal}` that needs a `Fintype`).
    The consumer instantiates the row at the empty family `n = 0` and reads its bound out: the
    statement accepts an instantiation, and its conclusion projects.
  * Zone 2 — **the datum's unramified factor.** The `hoff` field of `FactorizationDatum` is the local
    factor outside `S`; at `s = 0` it is the indicator of the integer ring. This is the content the
    factorization row's conclusion carries at the places it does not list, made explicit.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/EisensteinGeneralSetAF83DConsumer.lean` and never enters the build.
-/
import FLTForHuman.EisensteinGeneral.PieceLatticeMajorant
import FLTForHuman.EisensteinGeneral.FactorizationDatum

set_option autoImplicit false

noncomputable section

open MeasureTheory IsDedekindDomain NumberField NumberField.InfinitePlace
open AutomorphicForm EisensteinGeneral.Piece
open scoped Classical

namespace EisensteinGeneralSetAF83DConsumer

/-! ### Zone 1 — the majorant row at the empty family -/

/-- **Zone 1.** At `n = 0` the row's fifteen hypothesis shapes are all satisfiable (`Kf = 0` is the
bounded finite-adelic factor, `q` is the mixed embedding itself so that `hq₁`/`hq₂` hold with
`α = 1`, and `I = 1` inhabits the fractional ideal), and the row hands back a summable majorant of
the (empty) sum. -/
theorem exists_summable_majorant_empty (F : Type) [Field F] [NumberField F] (R : ℝ) :
    ∃ M : {ξ : F // ξ ≠ 0} → ℝ, Summable M ∧ ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ), ‖s‖ ≤ R →
      ‖(0 : ℂ)‖ ≤ M ξ := by
  obtain ⟨M, hsum, hbound⟩ :=
    exists_summable_majorant_of_lattice_vanishing F 0 R
      (fun _j => _j.elim0) (fun _j => _j.elim0)
      (fun _ => 0) 0 (by intro ξ; simp)
      (fun _j => _j.elim0) (fun _j => _j.elim0)
      (fun _j => _j.elim0) (fun _j => _j.elim0)
      (fun _ => 1) (by intro _i; norm_num)
      (fun _ => 1) (by intro _w; norm_num)
      (fun ξ => mixedEmbedding F ξ.1)
      (fun _ => 1) (by intro _i; norm_num)
      (fun _ => 1) (by intro _w; norm_num)
      (by intro ξ i; simp) (by intro ξ w; simp)
      1 (fun _j => _j.elim0) (fun _j => _j.elim0) 0 0 (fun _j => _j.elim0)
  exact ⟨M, hsum, fun ξ s hs => by simpa using hbound ξ s hs⟩

/-! ### Zone 2 — the datum's local factor at an unramified place -/

/-- **Zone 2.** The datum's `hoff` field, read at `s = 0` on an integral point: outside `S` the local
factor is `1` on the integer ring. This is the statement the factorization supplies at the places it
does not list, which is what makes the Euler product finite there. -/
theorem h_eq_one_of_mem_adicCompletionIntegers (F : Type) [Field F] [NumberField F]
    {ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ}
    {nψ : HeightOneSpectrum (𝓞 F) → ℤ}
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ}
    {ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ}
    {Ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ} {g : AdelicGL2 (𝓞 F) F}
    {S : Finset (HeightOneSpectrum (𝓞 F))}
    (D : FactorizationDatum F ψv nψ χ ϖ Ψ g S) (j : Fin D.n)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {x : v.adicCompletion F}
    (hx : x ∈ v.adicCompletionIntegers F) :
    D.h j v 0 x = 1 := by
  rw [D.hoff j v hv 0 x, Set.indicator_of_mem hx]
  have hnot : x ∉ (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ := by simpa using hx
  rw [Set.indicator_of_notMem hnot]
  simp

end EisensteinGeneralSetAF83DConsumer
