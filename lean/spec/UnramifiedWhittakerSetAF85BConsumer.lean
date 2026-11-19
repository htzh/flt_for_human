/-
  SET-AF85B consumer: the unramified Whittaker shell, read at `m = 1` and with the finite set empty.

  **The rows.** `FLTForHuman/RepTheory/LocalLanglands/WhittakerShell.lean` carries
  `UnramifiedWhittaker.mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero` (on the Hecke shell the product
  `W · conj W'` at `heckeGen ^ m · g` is the product of the two Hecke recursion sequences, and the
  negative half of the shell vanishes) and
  `UnramifiedWhittaker.exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero` (a function that is a Hecke
  and central eigenfunction away from a finite `S` does not vanish at `diagOne a₀ * g₀`).

  **The readings.**

  * Zone 1 — **`m = 1`**: the recursion sequence at `1` is `λ / N`, so the row unrolls to the single
    Hecke step `W (G · g) · conj (W' (G · g)) = (λ / N) · (conj λ' / N) · (W g · conj (W' g))`;
  * Zone 2 — **the negative half at `m = 1`**: `W (G⁻¹ · g) = 0` — the first shell step down is already
    zero, which is what makes the Whittaker expansion a finite sum over the positive exponentials;
  * Zone 3 — **`S = ∅`**: every "away from `S`" hypothesis of the second row becomes unconditional, so
    the point it produces has *trivial finite component at every place* and its unit is `1` everywhere.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/UnramifiedWhittakerSetAF85BConsumer.lean` and never enters the build.
-/
import FLTForHuman.RepTheory.LocalLanglands.WhittakerShell

set_option autoImplicit false

noncomputable section

open Matrix
open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock UnramifiedWhittaker
open AutomorphicForm
open scoped Classical

namespace UnramifiedWhittakerSetAF85BConsumer

/-! ### Zones 1 and 2 — one Hecke step and the vanishing of the negative half -/

/-- **Zones 1 and 2.** At `m = 1` the row is the single Hecke step — the recursion sequences read off
at `1` are `λ / N` and `conj λ' / N` — together with the vanishing of the shell's first negative step
`W (G⁻¹ · g) = 0`. -/
theorem shell_step (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψv : AddChar (v.adicCompletion K) ℂ) (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hgen : placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) =
      heckeGen (𝓞 K) K v)
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (W W' : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (lam om lam' om' : ℂ)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent x) * g) = ψv x * W g)
    (hN' : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W' (placeEmbed K v (unipotent x) * g) = ψv x * W' g)
    (hK : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W g)
    (hK' : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W' (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W' g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hT' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W' (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W' (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam' * W' g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    (hZ' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W' (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om' * W' g)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hg : Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) :
        AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2) :
    (W (heckeGen (𝓞 K) K v * g) * (starRingEnd ℂ) (W' (heckeGen (𝓞 K) K v * g))
        = (lam / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) *
            ((starRingEnd ℂ) lam' / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) *
            (W g * (starRingEnd ℂ) (W' g))) ∧
      W ((heckeGen (𝓞 K) K v)⁻¹ * g) = 0 := by
  have h := UnramifiedWhittaker.mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero K v ψv ϖ hπ hgen b hI
    hψ0 hψ1 W W' lam om lam' om' hN hN' hK hK' hT hT' hZ hZ' g hg
  refine ⟨?_, ?_⟩
  · simpa [UnramifiedWhittaker.heckeRecursionSeq, pow_one] using h.1 1
  · simpa [pow_one] using h.2 1 (by norm_num)

/-! ### Zone 3 — the nonvanishing row with the finite set empty -/

/-- **Zone 3.** With `S = ∅` every "away from `S`" hypothesis is unconditional, and the point the row
produces has trivial finite component and unit `1` at *every* place. -/
theorem exists_apply_diagOne_mul_ne_zero_trivial_off_empty (F : Type) [Field F] [NumberField F]
    (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v) ≠ 0)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) =
        WithZero.exp (-1 : ℤ))
    {I : HeightOneSpectrum (𝓞 F) → Type*} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 F), I v → v.adicCompletionIntegers F)
    (lam om : HeightOneSpectrum (𝓞 F) → ℂ)
    (hψ0 : ∀ v : HeightOneSpectrum (𝓞 F), ∀ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) = 1)
    (hψ1 : ∀ v : HeightOneSpectrum (𝓞 F), ∃ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r /
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) ≠ 1)
    (hN : ∀ v : HeightOneSpectrum (𝓞 F), ∀ (x : v.adicCompletion F)
      (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (placeEmbed F v (unipotent x) * g) = ψ v x * W g)
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∑ i, W (g * placeEmbed F v (repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b v i))))) +
        W (g * placeEmbed F v (repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v : HeightOneSpectrum (𝓞 F), ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v (scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        om v * W g)
    (hK : ∀ k : GL (Fin 2) (AdeleRing (𝓞 F) F),
      k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * k) = W g)
    (hW : ∃ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W g ≠ 0) :
    ∃ (g₀ : GL (Fin 2) (AdeleRing (𝓞 F) F)) (a₀ : (AdeleRing (𝓞 F) F)ˣ),
      (∀ v : HeightOneSpectrum (𝓞 F), ∀ i j : Fin 2,
        ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) ∧
      W (diagOne a₀ * g₀) ≠ 0 := by
  have h := UnramifiedWhittaker.exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero F
    (∅ : Finset (HeightOneSpectrum (𝓞 F))) W ψ ϖ hπ (fun v _ => hϖ v) b lam om
    (fun v _ r => hψ0 v r) (fun v _ => hψ1 v) (fun v _ x g => hN v x g) (fun v _ g => hT v g)
    (fun v _ g => hZ v g) (fun k hk _ g => hK k hk g) hW
  simpa using h

end UnramifiedWhittakerSetAF85BConsumer
