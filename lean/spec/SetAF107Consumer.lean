import FLTForHuman.FieldTheory.ValuationSubringValuedField
import FLTForHuman.RingTheory.DedekindDomain.HeightOneSpectrumRat
import FLTForHuman.NumberTheory.NumberField.HeightOneSpectrumSummable
import FLTForHuman.ModularCurve.StarBank.StarBank

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain HahnSeries

namespace SetAF107Consumer

/-! ## Zone 1 — the valed-field Krull dimension at a trivial valuation (order H)

Order H's `ringKrullDim_le_toENat_trdeg_rat_add_one` bounds the Krull dimension of a valuation subring
of a `ℚ`-algebra field by the transcendence degree plus one.  The consumer's use is the smallest case:
the trivial valuation subring of `ℚ` itself, where the bound reads `≤ 1` — the row at a `trdeg = 0`
field, which is the form the `ℚ`-side arguments instantiate.  This is the row *plus* mathlib's
`ringKrullDim` API on `⊤`; nothing of order H's proof is visible. -/

theorem ringKrullDim_top_rat : ringKrullDim (⊤ : ValuationSubring ℚ) ≤ 1 := by
  have h := ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one
    (L := ℚ) (⊤ : ValuationSubring ℚ)
  have h0 : Algebra.trdeg ℚ ℚ = 0 := trdeg_eq_zero
  rw [h0] at h
  simpa using h

/-! ## Zone 2 — the height-one spectrum of `ℤ`, prime-indexed (order F)

Two rows of order F composed, and they are the reason the two modules are separate subjects: the
spectrum's **classification** says every height-one prime of `𝓞 ℚ` is `span {p}` for a prime `p`, and
the **summability** row says `∑_{v} |N v.asIdeal|^{-σ}` converges for `σ > 1`.  A consumer that wants
the Euler product at `ℚ` needs both at once — the classification to write each term as `p^{-σ}`, the
summability to justify the rearrangement — so the packaged form below is what it consumes. -/

theorem rat_heightOne_prime_and_summable (σ : ℝ) (hσ : 1 < σ) :
    (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)}) ∧
      Summable (fun v : HeightOneSpectrum (𝓞 ℚ) =>
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)) :=
  ⟨IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat,
    NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ hσ⟩

/-! ## Zone 3 — the star bank over a finite residue field (order D)

Order D's `StarBank.starBank` separates the two level-one `q`-expansions over a field of characteristic
`ℓ`.  Its consumer is the *reduction* situation, where the field is a finite field of characteristic
`ℓ`; the zone instantiates the row at `ZMod ℓ` with `p = 3`, which is what a mod-`ℓ` bank computation
asks for.  It exercises the row's hypotheses (`Fact ℓ.Prime`, `CharP (ZMod ℓ) ℓ`, `3 ≠ ℓ`) and returns
the non-membership statement a downstream `q`-expansion argument consumes. -/

theorem starBank_mod_three (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 3) :
    ModularCurve.jqNModC (ZMod ℓ) 3 ∉
      IntermediateField.adjoin (ZMod ℓ)
        ({ModularCurve.jqModC (ZMod ℓ)} : Set (LaurentSeries (ZMod ℓ))) :=
  ModularCurve.StarBank.starBank (K := ZMod ℓ) (ℓ := ℓ) (p := 3) (Ne.symm hℓ)

end SetAF107Consumer
