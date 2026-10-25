/-
  GS1 — the prime splitting of `Φ_p` over an **arbitrary** field, with the at-slot
  roots API that reads it off.

  `PhiGen.splits_prime_of_isPrimitiveRoot` is `Φ_p(j(q^p), Y) = ∏_i (Y - conj_i)`
  over any field `K` (`[Field K]`, no `ℚ`-algebra structure), the level-`p` datum
  read at the level-`p` nome `jqModC K` splitting into its `p + 1` conjugates.
  `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot` is the same identity at the
  general level datum `(e, u)`, and the roots API reads the root multiset, its
  distinctness and the `IsRoot` membership form off it.

  The proof is one transport engine. It applies the ported char-0 splitting
  `PhiGen.splits_of_prime` at `CyclotomicField p ℚ`, rewrites that statement's `X`
  slot as `phiAtSeed` and its `jq` as `jqModC`, **pulls the identity back** to the
  integral cyclotomic order `cyclRing ℤ p` along the injective
  `cyclRing ℤ p →+* CyclotomicField p ℚ` (injective because the cyclotomic
  polynomial is the minimal polynomial of the chosen primitive root), and **pushes
  it forward** to `K` along `AdjoinRoot.lift (Int.castRingHom K) (ζ : K)`. The
  at-slot form is the first identity pushed through `(qExpand K e).comp (qTwist u)`
  — the same move the char-0 `PhiGenSplits.splits_prime_at_slot` makes — and the
  second headline is its `e = u = 1` case, exactly as the pin proves it.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean` (607 lines)
  and `P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean`
  (607 lines). The two files are **byte-identical except for the 15 lines that
  spell their own name and the final `solution`**: one 607-line development, so
  one module. The declarations transcribed are pin 267–486 (the transport engine),
  426–484 (the two public engine theorems) and 496–589 (the two headlines and the
  roots API).

  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean#L267-L589
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean#L267-L589

  The two headlines are the pin's `Theorems/` wrappers verbatim
  (`Theorems/Thm_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean:9` and
  `Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean:9`);
  the engine theorems and the roots API are the `S_` file's verbatim.

  ## Twins this module is and is not

  It is the **any-field** twin of `PhiGenSplits.lean` (the splitting) and of
  `PhiSlotRoots.lean` (the roots read off it). It is **not** an instance of either:
  both of those spend an `Algebra ℚ K` and read the slot as `coeffEmb K jq`, which
  an arbitrary field does not have — and the pin's own graph makes
  `splits_of_prime` a *premise* of this module, which is exactly what the
  integrality step uses. The statements therefore differ in their slot
  (`jqModC K` here, `coeffEmb K jq` there) and in the `N`/`p ∣ N` bookkeeping of
  the roots API (there the slot is read at an `N`-th primitive root restricted to
  `ζ ^ (N / p)`; here `ζ` is primitive of order `p` outright).

  ## Names — four renames the pin's two namespaces hide

  The pin states the at-slot roots API **twice** (this file's char-`p` spelling at
  level `p`, and `PhiSlotRoots`' char-0 spelling at general `N`), each inside its
  own per-file namespace `P2MW.S_…`, so both keep the plain names. A single
  `ModularCurve` namespace cannot hold two declarations of one name — Lean refuses
  the *import* of both modules (`environment already contains
  'ModularCurve.isRoot_prime_at_slot_iff'`), which would make any module wanting
  both unbuildable. The char-0 copy was landed first and is what five modules call,
  so this module's four at-slot names take the pin's own disambiguator for the
  any-field variants of this development, `_of_isPrimitiveRoot` (the suffix of the
  two headlines and of the pin's file names):

  | ported name | pin name (same statement) |
  |---|---|
  | `roots_prime_at_slot_of_isPrimitiveRoot` | `roots_prime_at_slot` (518) |
  | `roots_prime_at_slot_nodup_of_isPrimitiveRoot` | `roots_prime_at_slot_nodup` (535) |
  | `roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot` | `roots_prime_at_slot_roots_nodup` (558) |
  | `isRoot_prime_at_slot_iff_of_isPrimitiveRoot` | `isRoot_prime_at_slot_iff` (565) |

  The statements are the pin's verbatim, and the checker still verifies them — by
  content, with one `pin:` row each in [spec/decl_markers.tsv](../../spec/decl_markers.tsv).
  `prod_form_ne_zero` (pin 511) is `private` here, as in the pin: its public
  promoted home is `PhiSlotRoots`' more general copy, and `roots_phiAtSeed_TS` (pin
  584) keeps the pin's name because `PhiSlotRoots` has no such declaration.

  ## Layering

  This is the C-layer's entry to the at-slot roots (`roots_phiAtSeed_TS` has five
  consumers there), so it sits beside `PhiGenSplits`/`PhiSlotRoots` in
  `ModularCurve/`; it imports the definition layer and `PhiGenSplits`, and nothing
  imports it but the C layer.

  ## The prelude is imported, not re-written (pin 33–192, 269–281, 296–317, 355–364)

  The pin repeats its `TS`/`coeffMap`/`phiAtSeed` prelude in every `S_` file that
  needs it; the port gives each declaration one home, and this module imports them
  instead of transcribing them. `Defs/TS.lean` has `TS` and its coefficient API at
  `[Field K]` (including `TS_injective`, which `roots_prime_at_slot_nodup` needs,
  and `qTwist_TS`/`qExpand_TS`/`TS_congr`/`qExpand_qTwist_TS`); `Defs/PhiAtSlot.lean`
  has `phiAtSeed` and its API; `Defs/PhiGen.lean` has `conj`, `conj_zero`,
  `conj_succ`, `phiProd`; `Defs/Cyclotomic.lean` has `cycUnit`, `cycUnit_spec` and
  `isPrimitiveRoot_pow_div` (the pin's `ksplit_exists_isPrimitiveRoot`,
  `ksplitCycUnit`, `ksplitCycUnit_spec`); `Defs/KatzLevelPCusps.lean` has
  `cyclRing`, `cyclZeta`, `cyclRing_root_pow`, `val_cyclZeta` and
  `qTwist_qExpand_of_pow_eq_one` (the pin's `ksplit_root_pow`, `ksplitZeta`);
  `Defs/Laurent.lean` has `coeffEmb_qExpand` (the pin's `ksplit_coeffEmb_qExpand`)
  and `coeffMap_injective`; `Defs/JqCoeff.lean` has `coeffEmb_jq` (the pin's
  `ksplit_coeffEmb_jq`); `Defs/Twist.lean` has `coeffMap_qTwist` and
  `qTwistEquiv`; `X0/FunctionFieldFull.lean` has `coeff_jqModC_of_lt` (pin 44–47);
  `Degree/JqCyclotomicConjugates.lean` has `units_pow_eq_one_of_isPrimitiveRoot`
  (pin 189–190).

  Four of the pin's prelude bridges are **not written anywhere in the port yet at
  these statements**, and are not this module's: `jqModC_eq_TS` (pin 105),
  `jqNModC_eq_TS` (108),
  `qExpand_jqNModC` (111) and `qExpand_jqModC_eq_TS` (114). Their consumers are the
  `finrank_adjoin_jqNModC_*` / `jqNModC_*` nodes, which own them; nothing here
  mentions them. `qTwistEquiv_apply` (163) and `coeff_qTwistEquiv` (165) are dead
  in the pin — `coeff_qTwistEquiv` has no consumer anywhere in the pin, and
  `qTwistEquiv`'s only other use is that projection.

  **Dropped, and why.** `roots_nodup_prime_at_slot_of_isPrimitiveRoot`
  (pin 596–598): `private`, a one-line alias of `roots_prime_at_slot_roots_nodup`,
  no consumer in the pin. The prelude above (pin 33–192, 269–281, 296–317,
  355–364), because it is imported. The pin's dead `qTwistEquiv` block
  (pin 151–167), whose one live member `qTwistEquiv` is `Defs/Twist.lean`'s. The
  pin's `ksplit_comp_evalAtJ` (283–290) is **kept** as `comp_evalAtJ`: it is the
  engine's own `evalAtJ` bridge and has no other home.

  ## Assumptions

  `PhiGenSplits.splits_of_prime` (the premise), `Defs/TS`, `Defs/PhiAtSlot`,
  `Defs/PhiGen`, `Defs/Cyclotomic`, `Defs/KatzLevelPCusps`, `Defs/Laurent`,
  `Defs/Twist`, `Defs/JqCoeff`; mathlib's `AdjoinRoot`, the cyclotomic roots API
  (`Polynomial.cyclotomic_eq_minpoly_rat`, `map_cyclotomic_int`,
  `IsPrimitiveRoot.isRoot_cyclotomic`) and `Polynomial.roots_*`.

  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean
  spec-pin: P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot_of_isPrimitiveRoot.lean
-/
import FLTForHuman.ModularCurve.PhiGenSplits
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.KatzLevelPCusps
import FLTForHuman.ModularCurve.Defs.JqCoeff
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries

namespace ModularCurve
namespace PhiGen

variable {K : Type*} [Field K]

/-! ## The transport engine

`integral` is the pin's core: the splitting, pulled back from
`CyclotomicField p ℚ` to the integral cyclotomic order `cyclRing ℤ p` along the
injective `iota`. `zetaLift` then pushes it forward to an arbitrary field along
the chosen primitive root `ζ`. -/

/-- The pin's `KSplit.comp_evalAtJ`: evaluating an integer polynomial at `jq` and
then pushing it through `φ` is evaluating it at `φ jq`. -/
private theorem comp_evalAtJ {L : Type*} [CommRing L] (φ : LaurentSeries ℚ →+* L) :
    φ.comp evalAtJ = Polynomial.eval₂RingHom (Int.castRingHom L) (φ jq) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have h1 : evalAtJ (Polynomial.C a) = ((a : ℤ) : LaurentSeries ℚ) := by
      simp [evalAtJ]
    rw [RingHom.comp_apply, h1, map_intCast, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    simp
  · rw [RingHom.comp_apply, evalAtJ_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

section Engine

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- The map from the integral cyclotomic order to `CyclotomicField p ℚ` sending
the abstract root to the chosen primitive root `cycUnit p`. -/
private def iota : cyclRing ℤ p →+* CyclotomicField p ℚ :=
  AdjoinRoot.lift (Int.castRingHom (CyclotomicField p ℚ))
    ((cycUnit p : (CyclotomicField p ℚ)ˣ) : CyclotomicField p ℚ) (by
      rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int]
      exact Polynomial.IsRoot.eq_zero ((cycUnit_spec p).isRoot_cyclotomic hp.out.pos))

private theorem iota_root :
    iota p (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))
      = ((cycUnit p : (CyclotomicField p ℚ)ˣ) : CyclotomicField p ℚ) :=
  AdjoinRoot.lift_root _

private theorem iota_units_zeta :
    Units.map (iota p).toMonoidHom (cyclZeta ℤ p) = cycUnit p :=
  Units.ext (by rw [Units.coe_map, val_cyclZeta]; exact AdjoinRoot.lift_root _)

/-- `iota` is injective: the cyclotomic polynomial is the minimal polynomial of
the chosen primitive root over `ℚ`, and `map_dvd_map` reflects divisibility along
the injective `ℤ → ℚ`. -/
private theorem iota_injective : Function.Injective (iota p) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [iota, AdjoinRoot.lift_mk] at ha
  rw [AdjoinRoot.mk_eq_zero]
  have hq : Polynomial.aeval ((cycUnit p : (CyclotomicField p ℚ)ˣ) : CyclotomicField p ℚ)
      (g.map (Int.castRingHom ℚ)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap ℚ (CyclotomicField p ℚ)).comp (Int.castRingHom ℚ)
        = Int.castRingHom (CyclotomicField p ℚ) from RingHom.ext_int _ _]
    exact ha
  have hdvd : Polynomial.cyclotomic p ℚ ∣ g.map (Int.castRingHom ℚ) := by
    rw [Polynomial.cyclotomic_eq_minpoly_rat (cycUnit_spec p) hp.out.pos]
    exact minpoly.dvd ℚ _ hq
  rw [← Polynomial.map_cyclotomic_int p ℚ] at hdvd
  exact (Polynomial.map_dvd_map (Int.castRingHom ℚ) Int.cast_injective
    (Polynomial.cyclotomic.monic p ℤ)).mp hdvd

/-- The splitting over the integral cyclotomic order: pull the char-0 identity
back along the injective `iota`. Both the `X` slot and the `jq` slot are read
through `coeffMap (iota p)` and `map_jqModC`, and distinctness of the conjugates is
what makes the pullback legitimate. -/
private theorem integral (data : ModularPolynomialData p) :
    phiAtSeed data (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))
      = (Polynomial.X - Polynomial.C (qExpand (cyclRing ℤ p) (p * p)
          (jqModC (cyclRing ℤ p))))
        * ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist ((cyclZeta ℤ p) ^ (b : ℕ))
            (jqModC (cyclRing ℤ p)))) := by
  classical
  have hK := ModularCurve.PhiGen.splits_of_prime p (cycUnit p) (cycUnit_spec p) data
  have hLK : data.Φ.map (((coeffEmb (CyclotomicField p ℚ)).comp (qExpand ℚ p)).comp evalAtJ)
      = phiAtSeed data (qExpand (CyclotomicField p ℚ) p (jqModC (CyclotomicField p ℚ))) := by
    have hseed : ((coeffEmb (CyclotomicField p ℚ)).comp (qExpand ℚ p)) jq
        = qExpand (CyclotomicField p ℚ) p (jqModC (CyclotomicField p ℚ)) := by
      rw [RingHom.comp_apply, coeffEmb_qExpand, coeffEmb_jq]
    rw [comp_evalAtJ, hseed, phiAtSeed]
  have hseedO : coeffMap (iota p)
      (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))
      = qExpand (CyclotomicField p ℚ) p (jqModC (CyclotomicField p ℚ)) := by
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC (iota p)
  have hmapProd :
      ((Polynomial.X - Polynomial.C (qExpand (cyclRing ℤ p) (p * p)
          (jqModC (cyclRing ℤ p))))
        * ∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist ((cyclZeta ℤ p) ^ (b : ℕ))
            (jqModC (cyclRing ℤ p))))).map (coeffMap (iota p))
      = phiProd p (conj p (cycUnit p)) := by
    rw [phiProd, Fin.prod_univ_succ, Polynomial.map_mul]
    congr 1
    · rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, conj_zero]
      congr 2
      rw [coeffMap_qExpand, coeffEmb_jq]
      congr 1
      exact map_jqModC (iota p)
    · rw [← Polynomial.coe_mapRingHom, map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        conj_succ,
        coeffMap_qTwist (iota p) ((cyclZeta ℤ p) ^ (b : ℕ))
          (Units.map (iota p).toMonoidHom ((cyclZeta ℤ p) ^ (b : ℕ))) rfl,
        map_pow, iota_units_zeta, coeffEmb_jq]
      exact congrArg
        (fun z => Polynomial.X - Polynomial.C (qTwist (cycUnit p ^ (b : ℕ)) z))
        (map_jqModC (iota p))
  apply Polynomial.map_injective (coeffMap (iota p))
    (ModularCurve.coeffMap_injective (iota_injective p))
  rw [phiAtSeed_map, hseedO, hmapProd, ← hLK]
  exact hK

/-- The push-forward: the integral identity transported along the chosen primitive
root `ζ` of an arbitrary field. -/
private def zetaLift (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    cyclRing ℤ p →+* K :=
  AdjoinRoot.lift (Int.castRingHom K) (ζ : K) (by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int]
    exact Polynomial.IsRoot.eq_zero (hζ.isRoot_cyclotomic hp.out.pos))

private theorem zetaLift_root (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    zetaLift p ζ hζ (AdjoinRoot.root (Polynomial.cyclotomic p ℤ)) = ζ :=
  AdjoinRoot.lift_root _

private theorem zetaLift_units_zeta (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) :
    Units.map (zetaLift p ζ hζ).toMonoidHom (cyclZeta ℤ p) = ζ :=
  Units.ext (by rw [Units.coe_map, val_cyclZeta]; exact AdjoinRoot.lift_root _)

/-- The splitting at the level-`p` nome over an arbitrary field: push `integral`
forward along `ζ`. -/
theorem phiAtSeed_qExpand_prime_eq (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) :
    phiAtSeed data (qExpand K p (jqModC K))
      = (Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K)))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) := by
  classical
  have h := congrArg (Polynomial.map (coeffMap (zetaLift p ζ hζ))) (integral p data)
  have hseed : coeffMap (zetaLift p ζ hζ)
      (qExpand (cyclRing ℤ p) p (jqModC (cyclRing ℤ p)))
      = qExpand K p (jqModC K) := by
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC (zetaLift p ζ hζ)
  have hspread : coeffMap (zetaLift p ζ hζ)
      (qExpand (cyclRing ℤ p) (p * p) (jqModC (cyclRing ℤ p)))
      = qExpand K (p * p) (jqModC K) := by
    rw [coeffMap_qExpand]
    congr 1
    exact map_jqModC (zetaLift p ζ hζ)
  have hfac : ∀ b : Fin p,
      (Polynomial.mapRingHom (coeffMap (zetaLift p ζ hζ)))
        (Polynomial.X - Polynomial.C (qTwist ((cyclZeta ℤ p) ^ (b : ℕ))
          (jqModC (cyclRing ℤ p))))
      = Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) (jqModC K)) := by
    intro b
    rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      coeffMap_qTwist (zetaLift p ζ hζ) ((cyclZeta ℤ p) ^ (b : ℕ))
        (Units.map (zetaLift p ζ hζ).toMonoidHom ((cyclZeta ℤ p) ^ (b : ℕ))) rfl,
      map_pow, zetaLift_units_zeta]
    exact congrArg (fun z => Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) z))
      (map_jqModC (zetaLift p ζ hζ))
  rw [phiAtSeed_map, hseed, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    hspread, ← Polynomial.coe_mapRingHom, map_prod, Finset.prod_congr rfl fun b _ => hfac b] at h
  have hr : (∏ b : Fin p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ (b : ℕ)) (jqModC K))))
      = ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) :=
    Fin.prod_univ_eq_prod_range (fun b => Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) p
  rw [hr] at h
  exact h

/-- The splitting at a general slot over an arbitrary field: push the level-`p`
identity through `qExpand K e ∘ qTwist u`. -/
theorem phiAtSeed_slot_prime_eq (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    phiAtSeed data (qExpand K (p * e) (qTwist (u ^ p) (jqModC K)))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) := by
  classical
  set f : LaurentSeries K →+* LaurentSeries K := (qExpand K e).comp (qTwist u) with hf
  have hseed : f (qExpand K p (jqModC K)) = qExpand K (p * e) (qTwist (u ^ p) (jqModC K)) := by
    rw [hf, RingHom.comp_apply, qTwist_qExpand, qExpand_qExpand, zpow_natCast]
    exact qExpand_congr (Nat.mul_comm e p) _
  have hspread : f (qExpand K (p * p) (jqModC K)) = qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)) := by
    rw [hf, RingHom.comp_apply, qTwist_qExpand, qExpand_qExpand, zpow_natCast]
    exact qExpand_congr (by ring) _
  have hfac : ∀ b ∈ Finset.range p,
      (Polynomial.mapRingHom f) (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K)))
        = Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K))) := by
    intro b _
    rw [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hf,
      RingHom.comp_apply, qTwist_qTwist]
  have h := congrArg (Polynomial.map f) (phiAtSeed_qExpand_prime_eq p ζ hζ data)
  rw [phiAtSeed_map, hseed, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    hspread, ← Polynomial.coe_mapRingHom, map_prod, Finset.prod_congr rfl hfac] at h
  exact h

end Engine

/-! ## The two headlines -/

/-- The modular polynomial splits into its `p + 1` conjugates over an arbitrary
field. Verbatim from the pin headline (and its `Theorems/` wrapper); the
`eval₂RingHom` map is `phiAtSeed` by definition. -/
theorem splits_prime_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (qExpand K p (jqModC K)))
      = (Polynomial.X - Polynomial.C (qExpand K (p * p) (jqModC K)))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qTwist (ζ ^ b) (jqModC K))) :=
  phiAtSeed_qExpand_prime_eq p ζ hζ data

/-- The headline at the general slot: the same splitting with the level datum
`(e, u)`. Verbatim from the pin headline (and its `Theorems/` wrapper). -/
theorem splits_prime_at_slot_of_isPrimitiveRoot {K : Type*} [Field K] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))))
        * ∏ b ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) :=
  phiAtSeed_slot_prime_eq p ζ hζ data e u

end PhiGen

/-! ## The at-slot roots API -/

section Roots

variable {K : Type*} [Field K]

/-- The product `(X - j(u ^ p² q ^ p²e)) · ∏_{b < p} (X - j(u ζ^b q^e))` is
nonzero: its factors are `X - C` and a product of monic linear factors. `private`
as in the pin: its public promoted home is the more general
`PhiSlotRoots.prod_form_ne_zero`, and a public copy here would collide with it
(the *Names* paragraph of the header). -/
private theorem prod_form_ne_zero (ζ : Kˣ) (p : ℕ) [NeZero p] (e : ℕ) [NeZero e] (u : Kˣ) :
    (Polynomial.X - Polynomial.C (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)))) *
        ∏ b ∈ Finset.range p,
          (Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))) ≠ 0 :=
  mul_ne_zero (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _).ne_zero

/-- The roots of `data.Φ`, read at the slot `u q ^ e`, are the `p + 1` values
`j(u ^ p² q ^ p²e)` and `j(u ζ^b q^e)` — via the at-slot splitting and
`roots_mul`. -/
theorem roots_prime_at_slot_of_isPrimitiveRoot (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))).roots
      = (qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))) ::ₘ
          (Multiset.range p).map (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K))) := by
  rw [ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u,
    Polynomial.roots_mul (prod_form_ne_zero ζ p e u), Polynomial.roots_X_sub_C,
    Finset.prod_eq_multiset_prod, Finset.range_val,
    show (Multiset.range p).map
          (fun b => Polynomial.X - Polynomial.C (qExpand K e (qTwist (u * ζ ^ b) (jqModC K))))
        = ((Multiset.range p).map (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))).map
            (fun a => Polynomial.X - Polynomial.C a) from
      (Multiset.map_map (fun a => Polynomial.X - Polynomial.C a)
        (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K))) (Multiset.range p)).symm,
    Polynomial.roots_multiset_prod_X_sub_C, Multiset.singleton_add]

/-- Those `p + 1` roots are distinct: the extra root sits at level `p²` while the
others sit at level `e` (separated by `TS_injective`, whose level is the twist
exponent), and the latter are separated by `IsPrimitiveRoot.pow_inj` on `ζ`. -/
theorem roots_prime_at_slot_nodup_of_isPrimitiveRoot (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (e : ℕ) [NeZero e] (u : Kˣ) :
    ((qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K))) ::ₘ
        (Multiset.range p).map (fun b => qExpand K e (qTwist (u * ζ ^ b) (jqModC K)))).Nodup := by
  rw [Multiset.nodup_cons]
  constructor
  · intro hmem
    obtain ⟨b, hb, heq⟩ := Multiset.mem_map.mp hmem
    have h := (TS_injective (K := K) (e := e) (e' := p * (p * e)) (u := u * ζ ^ b) (u' := u ^ (p * p)) heq).1
    have hp2 : 2 ≤ p := hp.out.two_le
    have he1 : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
    have hmono : 2 * (2 * e) ≤ p * (p * e) := Nat.mul_le_mul hp2 (Nat.mul_le_mul hp2 le_rfl)
    rw [← h] at hmono
    omega
  · refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range p)
    intro b hb b' hb' heq
    rw [Multiset.mem_range] at hb hb'
    have h := (TS_injective (K := K) (e := e) (e' := e) (u := u * ζ ^ b) (u' := u * ζ ^ b') heq).2
    have h2 : ζ ^ b = ζ ^ b' := mul_left_cancel h
    have h3 : ((ζ : Kˣ) : K) ^ b = ((ζ : Kˣ) : K) ^ b' := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h2]
    exact hζ.pow_inj hb hb' h3

/-- The packaged distinctness of `data.Φ`'s roots at the slot. -/
theorem roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) p) (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))).roots.Nodup := by
  rw [roots_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u]
  exact roots_prime_at_slot_nodup_of_isPrimitiveRoot p ζ hζ e u

/-- Membership in the root multiset, in iff form: `y` is a root of the slot
polynomial exactly when it is the extra conjugate or one of the `p` finite ones
`j(u ζ^b q^e)`. -/
theorem isRoot_prime_at_slot_iff_of_isPrimitiveRoot (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) (y : LaurentSeries K) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (qExpand K (p * e) (qTwist (u ^ p) (jqModC K))))).IsRoot y ↔
      y = qExpand K (p * (p * e)) (qTwist (u ^ (p * p)) (jqModC K)) ∨
        ∃ b < p, y = qExpand K e (qTwist (u * ζ ^ b) (jqModC K)) := by
  have hne : data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * e) (qTwist (u ^ p) (jqModC K)))) ≠ 0 := by
    rw [ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u]
    exact prod_form_ne_zero ζ p e u
  rw [← Polynomial.mem_roots hne, roots_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u,
    Multiset.mem_cons, Multiset.mem_map]
  constructor
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mp hb, rfl⟩
  · rintro (h | ⟨b, hb, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b, Multiset.mem_range.mpr hb, rfl⟩

/-- The same roots, read as `TS` values (`TS K e u = qExpand K e (qTwist u (jqModC K))`
by definition). Five C-layer consumers. -/
theorem roots_phiAtSeed_TS (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) p)
    (data : ModularPolynomialData p) (e : ℕ) [NeZero e] (u : Kˣ) :
    (phiAtSeed data (TS K (p * e) (u ^ p))).roots
      = TS K (p * (p * e)) (u ^ (p * p)) ::ₘ (Multiset.range p).map (fun b => TS K e (u * ζ ^ b)) :=
  roots_prime_at_slot_of_isPrimitiveRoot p ζ hζ data e u

end Roots

end ModularCurve

end

#print axioms ModularCurve.PhiGen.splits_prime_of_isPrimitiveRoot
#print axioms ModularCurve.PhiGen.splits_prime_at_slot_of_isPrimitiveRoot
