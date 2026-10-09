/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import Mathlib.Algebra.CharP.Frobenius
import Mathlib.FieldTheory.Finite.Basic
import TrustworthyKedlaya

/-!
# Finite coefficient range of algebraic p-adic Hahn series

The canonical coefficients of a `ℚ_[p]`-algebraic p-adic Hahn series lie in a single
finite subfield of `𝔽ᵃ_[p]`. A common positive power of Frobenius fixes every coefficient.
This gives the finite coefficient field `𝔽_{p^r}` of a strict p-adic Puiseux series used in
the proof of Proposition 4.4.

## Main statements

* `PAdicOrderType.exists_hyper_inertia_of_qp_algebraic`: all coefficients are fixed by
  the same positive iterate of Frobenius.
* `PAdicOrderType.finite_range_coeff_of_qp_algebraic`: the coefficient function has finite range.

## Implementation notes

Witt-vector Frobenius preserves null series and descends to a `ℚ_[p]`-algebra endomorphism
of the p-adic Hahn field. The iterates of an algebraic element lie in a finite root set.
Two iterates therefore coincide, and injectivity of Frobenius gives a common period for
all coefficients. The fixed points of this iterate form a finite field.
-/

namespace PAdicOrderType

open TrustworthyKedlaya TrustworthyKedlaya.pAdicHahnSeries WittVector

variable {p : ℕ} [Fact (Nat.Prime p)]

section Frobenius

private theorem frobW_teichmuller (a : 𝔽ᵃ_[p]) :
    WittVector.frobenius (teichmuller p a) = teichmuller p (a ^ p) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

/-- The Witt-vector Frobenius preserves the valuation on `ℤᶜᵘⁿ_[p]`: it maps `u · pⁿ` (with
`u` a unit) to `(WittVector.frobenius u) · pⁿ`, and units have valuation `1`. -/
private theorem valued_frobW_algebraMap (a : ℤᶜᵘⁿ_[p]) :
    Valued.v (algebraMap (OQpCUn p) (QpCUn p) (WittVector.frobenius a))
      = Valued.v (algebraMap (OQpCUn p) (QpCUn p) a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero]
  · obtain ⟨n, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha (WittVector.irreducible p)
    have hu : Valued.v (algebraMap (OQpCUn p) (QpCUn p)
        (WittVector.frobenius (u : ℤᶜᵘⁿ_[p]))) = 1 := by
      simpa using valued_v_algebraMap_unit_one (Units.map WittVector.frobenius.toMonoidHom u)
    simp only [map_mul, map_pow, map_natCast]
    rw [valued_v_algebraMap_unit_one u, hu]

/-- The Frobenius of `ℚᶜᵘⁿ_[p]` preserves the valuation. -/
private theorem valued_frobQpCUn (y : ℚᶜᵘⁿ_[p]) :
    Valued.v (QpCUn.frobenius p y) = Valued.v y := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (OQpCUn p) y
  rw [map_div₀, QpCUn.frobenius_algebraMap, QpCUn.frobenius_algebraMap, Valuation.map_div,
    Valuation.map_div, valued_frobW_algebraMap, valued_frobW_algebraMap]

/-- Preserving the valuation, the Frobenius of `ℚᶜᵘⁿ_[p]` is continuous at `0`. -/
private theorem tendsto_frobQpCUn_zero :
    Filter.Tendsto (QpCUn.frobenius p) (nhds 0) (nhds 0) := by
  rw [Filter.tendsto_def]
  intro U hU
  rw [Valued.mem_nhds] at hU
  obtain ⟨γ, hγ⟩ := hU
  rw [Valued.mem_nhds]
  refine ⟨γ, fun y hy => ?_⟩
  simp only [Set.mem_ofPred_eq] at hy
  refine Set.mem_preimage.mpr (hγ ?_)
  simp only [Set.mem_ofPred_eq]
  rw [sub_zero, Valuation.restrict_lt_iff_lt_embedding] at hy ⊢
  rwa [valued_frobQpCUn]

/-- The coefficientwise Witt-vector Frobenius is a ring endomorphism of the lifted Hahn
series ring. -/
private noncomputable def liftedFrobHom :
    LiftedPAdicHahnSeries p →+* LiftedPAdicHahnSeries p where
  toFun x := x.map WittVector.frobenius
  map_zero' := HahnSeries.map_zero WittVector.frobenius.toZeroHom
  map_add' _ _ := HahnSeries.map_add WittVector.frobenius.toAddMonoidHom
  map_one' :=
    HahnSeries.map_one (WittVector.frobenius : ℤᶜᵘⁿ_[p] →+* ℤᶜᵘⁿ_[p]).toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul WittVector.frobenius.toNonUnitalRingHom

private theorem coeff_liftedFrobHom (x : LiftedPAdicHahnSeries p) (q : ℚ) :
    (liftedFrobHom (p := p) x).coeff q = WittVector.frobenius (x.coeff q) := rfl

/-- The coefficientwise Frobenius preserves null series: on each residue class of `g`
modulo `ℤ` the partial sums of the image are the images of the partial sums under the
valuation-preserving (hence continuous) Frobenius of `ℚᶜᵘⁿ_[p]`. -/
private theorem isNullSeries_liftedFrob {x : LiftedPAdicHahnSeries p} (hx : IsNullSeries x) :
    IsNullSeries (liftedFrobHom (p := p) x) := by
  intro g
  have hSeq : ∀ M : ℕ, (finiteBelow (liftedFrobHom (p := p) x) g M).toFinset
      = (finiteBelow x g M).toFinset := fun M => by
    apply Set.Finite.toFinset_inj.mpr
    ext n
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h0 => h2 ?_⟩
      rw [coeff_liftedFrobHom, h0, map_zero]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h0 => h2 ((QpCUn.frobenius_injective p) ?_)⟩
      rw [map_zero]
      rw [coeff_liftedFrobHom] at h0
      exact h0
  have htend := (tendsto_frobQpCUn_zero (p := p)).comp (hx g)
  refine htend.congr fun M => ?_
  change QpCUn.frobenius p (∑ n : (finiteBelow x g M).toFinset,
      (p : QpCUn p) ^ n.val * algebraMap (OQpCUn p) (QpCUn p) (x.coeff (g + n))) = _
  rw [hSeq M, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_zpow₀, map_natCast, QpCUn.frobenius_algebraMap, coeff_liftedFrobHom]

/-- The Frobenius descends to a ring endomorphism of `𝕃_[p]`. -/
private noncomputable def frobLp : 𝕃_[p] →+* 𝕃_[p] :=
  Ideal.Quotient.lift (NullSeriesIdeal p)
    ((Ideal.Quotient.mk (NullSeriesIdeal p)).comp (liftedFrobHom (p := p)))
    (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact isNullSeries_liftedFrob (show IsNullSeries a from ha))

private theorem frobLp_mk (x : LiftedPAdicHahnSeries p) :
    frobLp (p := p) (Ideal.Quotient.mk (NullSeriesIdeal p) x)
      = Ideal.Quotient.mk (NullSeriesIdeal p) (liftedFrobHom (p := p) x) :=
  Ideal.Quotient.lift_mk _ _ _

/-- The canonical coefficients of the Frobenius image are the `p`-th powers of the canonical
coefficients: the Frobenius of a Teichmüller-coefficient representative is again a
Teichmüller-coefficient representative. -/
private theorem coeff_frobLp (x : 𝕃_[p]) (q : ℚ) :
    (frobLp (p := p) x).coeff q = x.coeff q ^ p := by
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hpwo : (Function.support fun r : ℚ => x.coeff r ^ p).IsPWO :=
    (support_IsPWO x).mono fun r hr => by
      rw [Function.mem_support] at hr ⊢
      exact fun h0 => hr ((pow_eq_zero_iff hp0).mpr h0)
  have hlift : liftedFrobHom (p := p)
        (LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x))
      = LiftedPAdicHahnSeries.fromCoeff (fun r => x.coeff r ^ p) hpwo := by
    apply HahnSeries.ext
    funext r
    exact frobW_teichmuller (x.coeff r)
  conv_lhs => rw [← fromCoeff_of_coeff_eq_self x]
  rw [show pAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x)
        = Ideal.Quotient.mk (NullSeriesIdeal p)
            (LiftedPAdicHahnSeries.fromCoeff x.coeff (support_IsPWO x)) from rfl,
    frobLp_mk, hlift,
    show Ideal.Quotient.mk (NullSeriesIdeal p)
          (LiftedPAdicHahnSeries.fromCoeff (fun r => x.coeff r ^ p) hpwo)
        = pAdicHahnSeries.fromCoeff (fun r => x.coeff r ^ p) hpwo from rfl,
    coeff_of_fromCoeff_eq_self]

private theorem frobLp_zpUn (a : ℤᶜᵘⁿ_[p]) :
    frobLp (p := p) (ZpUn_embd a) = ZpUn_embd (WittVector.frobenius a) := by
  rw [show ZpUn_embd (p := p) a
      = Ideal.Quotient.mk (NullSeriesIdeal p) (HahnSeries.single 0 a) from rfl,
    frobLp_mk,
    show ZpUn_embd (p := p) (WittVector.frobenius a)
      = Ideal.Quotient.mk (NullSeriesIdeal p)
          (HahnSeries.single 0 (WittVector.frobenius a)) from rfl]
  exact congrArg (Ideal.Quotient.mk (NullSeriesIdeal p))
    (HahnSeries.map_single WittVector.frobenius.toZeroHom)

/-- The Frobenius of `𝕃_[p]` fixes the image of `ℚ_[p]` pointwise: on `ℤᶜᵘⁿ_[p]` it acts by
the Witt-vector Frobenius, which is the identity on the image of `ℤ_[p] = W(𝔽_p)` since the
Frobenius of `𝔽_p` is the identity. -/
private theorem frobLp_algebraMap (c : ℚ_[p]) :
    frobLp (p := p) (algebraMap ℚ_[p] 𝕃_[p] c) = algebraMap ℚ_[p] 𝕃_[p] c := by
  have hcomp : (frobLp (p := p)).comp (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p])
      = (algebraMap ℚᶜᵘⁿ_[p] 𝕃_[p]).comp (QpCUn.frobenius p) := by
    refine IsFractionRing.ringHom_ext (A := OQpCUn p) fun a => ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, algebraMap_QpCUn_algebraMap,
      frobLp_zpUn, QpCUn.frobenius_algebraMap, algebraMap_QpCUn_algebraMap]
  have halg : algebraMap ℚ_[p] 𝕃_[p] = (QpCUn_embd (p := p)).comp QpCUn.Qp_embd := rfl
  rw [halg, RingHom.comp_apply]
  have h1 := RingHom.congr_fun hcomp (QpCUn.Qp_embd c)
  rw [RingHom.comp_apply, RingHom.comp_apply] at h1
  rw [QpCUn.frobenius_Qp_embd] at h1
  exact h1

/-- The Frobenius as a `ℚ_[p]`-algebra endomorphism of `𝕃_[p]`. -/
private noncomputable def frobAlgHom : 𝕃_[p] →ₐ[ℚ_[p]] 𝕃_[p] where
  __ := frobLp (p := p)
  commutes' := frobLp_algebraMap

private theorem frobAlgHom_apply (x : 𝕃_[p]) :
    frobAlgHom (p := p) x = frobLp (p := p) x := rfl

end Frobenius

/-- **Finite coefficient field**: all canonical coefficients of a `ℚ_[p]`-algebraic
p-adic Hahn series are fixed by a common positive iterate of Frobenius. Equivalently,
there is an `r > 0` such that every coefficient belongs to the finite field with `p ^ r`
elements inside `𝔽ᵃ_[p]`. -/
theorem exists_hyper_inertia_of_qp_algebraic (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f) :
    ∃ r : ℕ+, ∀ q ∈ f.support, f.coeff q ^ p ^ (r : ℕ) = f.coeff q := by
  classical
  obtain ⟨P, hP0, hPf⟩ := hf
  -- the set of roots of `P` in `𝕃_[p]` is finite
  have hfin : {x : 𝕃_[p] | Polynomial.aeval x P = 0}.Finite := by
    have heq : {x : 𝕃_[p] | Polynomial.aeval x P = 0}
        = {x : 𝕃_[p] | (P.map (algebraMap ℚ_[p] 𝕃_[p])).IsRoot x} := by
      ext x
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_map,
        Polynomial.aeval_def]
    rw [heq]
    exact Polynomial.finite_setOfPred_isRoot (Polynomial.map_ne_zero hP0)
  -- the Frobenius iterates raise every coefficient to `p ^ j`-th powers
  have hcoeff_iter : ∀ (j : ℕ) (q : ℚ),
      ((⇑(frobAlgHom (p := p)))^[j] f).coeff q = f.coeff q ^ p ^ j := by
    intro j
    induction j with
    | zero => intro q; simp
    | succ j ih =>
      intro q
      rw [Function.iterate_succ_apply', frobAlgHom_apply, coeff_frobLp, ih, ← pow_mul,
        ← pow_succ]
  -- the Frobenius iterates of `f` are roots of `P`
  have hroot : ∀ j : ℕ, (⇑(frobAlgHom (p := p)))^[j] f ∈ hfin.toFinset := by
    intro j
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    induction j with
    | zero => simpa using hPf
    | succ j ih => rw [Function.iterate_succ_apply', Polynomial.aeval_algHom_apply, ih, map_zero]
  -- pigeonhole: two of the first `card + 1` iterates coincide
  obtain ⟨j₁, -, j₂, -, hne, hiter⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (hfin.toFinset.card + 1)) (t := hfin.toFinset)
      (by rw [Finset.card_range]; omega) fun j _ => hroot j
  suffices key : ∀ a b : ℕ, a < b →
      (⇑(frobAlgHom (p := p)))^[a] f = (⇑(frobAlgHom (p := p)))^[b] f →
      ∃ r : ℕ+, ∀ q ∈ f.support, f.coeff q ^ p ^ (r : ℕ) = f.coeff q by
    rcases lt_or_gt_of_ne hne with h | h
    · exact key j₁ j₂ h hiter
    · exact key j₂ j₁ h hiter.symm
  intro a b hab hiter
  refine ⟨⟨b - a, by omega⟩, fun q _ => ?_⟩
  change f.coeff q ^ p ^ (b - a) = f.coeff q
  have h1 : f.coeff q ^ p ^ a = f.coeff q ^ p ^ b := by
    rw [← hcoeff_iter a q, ← hcoeff_iter b q, hiter]
  -- cancel the `p ^ a`-th powers by injectivity of the iterated Frobenius of `𝔽ᵃ_[p]`
  apply iterateFrobenius_inj (𝔽ᵃ_[p]) p a
  simp only [iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hab.le]
  exact h1.symm

/-- The canonical coefficient function of a `ℚ_[p]`-algebraic p-adic Hahn series has
finite range. All values are roots of one polynomial `X ^ (p ^ r) - X` with `r > 0`. -/
theorem finite_range_coeff_of_qp_algebraic (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f) :
    (Set.range f.coeff).Finite := by
  obtain ⟨r, hr⟩ := exists_hyper_inertia_of_qp_algebraic f hf
  have := finite_frobeniusFixed p r.pos
  refine (Set.toFinite (frobeniusFixed p (r : ℕ) : Set (𝔽ᵃ_[p]))).subset ?_
  rintro _ ⟨q, rfl⟩
  by_cases hq : q ∈ f.support
  · exact (mem_frobeniusFixed_iff p).2 (hr q hq)
  · have hz : f.coeff q = 0 := by simpa only [mem_support_iff, not_not] using hq
    rw [hz]
    exact (frobeniusFixed p (r : ℕ)).zero_mem

end PAdicOrderType
