-- Locked baseline target statements; retain their theorem headers exactly.
/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Puiseux.FiniteCoeffLaurent
import PAdicOrderType.Puiseux.PuiseuxApproximation
import PAdicOrderType.OrderType.SupportOrderType

/-!
# Support order types, strict Puiseux series, and bialgebraicity

This file states the main results of the paper cited below. For a prime `p`, the support of a
`ℚ_[p]`-algebraic p-adic Hahn series has order type finite, `ω`, or `ω ^ ω` (Theorem A). In
particular, a bounded support is finite (Theorem B). The algebraic series of order type at most
`ω` are exactly the strict p-adic Puiseux series (Theorem C). These results also characterize
simultaneous algebraicity of an ordinary Hahn series and its p-adic shadow (Theorem D).

## Main statements

* `PAdicOrderType.typeLT_support_le_omega0_or_eq_omega0_pow_omega0`: the order-type dichotomy,
  an equivalent form of Theorem A.
* `PAdicOrderType.support_finite_of_isAlgebraic_of_isBounded`: bounded algebraic support is finite
  (Theorem B, Proposition 4.2).
* `PAdicOrderType.typeLT_support_eq_nat_or_eq_omega0_or_eq_omega0_pow_omega0`: the trichotomy
  (Theorem A).
* `PAdicOrderType.typeLT_support_padicAlgCl_le_omega0_or_eq_omega0_pow_omega0`: the dichotomy
  for elements of the chosen algebraic closure.
* `PAdicOrderType.typeLT_support_le_omega0_iff_mem_pAdicStrictPuiseux_range`: the strict
  Puiseux image is characterized by support order type among algebraic Hahn series
  (Theorem C, Proposition 4.3).
* `PAdicOrderType.typeLT_support_padicAlgCl_le_omega0_iff_mem_pAdicStrictPuiseux`: the same
  characterization inside the algebraic closure.
* `PAdicOrderType.bialgebraic_tfae`: bialgebraicity, strict Puiseux membership, algebraicity
  with support order type at most `ω`, and bounded denominators with finite coefficient range
  are equivalent (Theorem D, Proposition 4.4).

## Implementation notes

These declarations provide the baseline statements used for verification.

Kedlaya's upper bound `ω ^ ω` (Proposition 2.11) is combined with finite-rank exclusion
(Theorem 4.1). The latter uses quasi-twist recurrence, separated digit blocks, and a uniform
estimate for interleaving coefficients to contradict an annihilating polynomial at sufficiently
large truncations (Proposition 3.1). The Puiseux characterization uses finite truncations and
Krasner's lemma. Bialgebraicity also uses the strict support bound in characteristic `p`, a
result of Lisinski, and the finite-coefficient criterion.

## References

* S. Wang and Y. Yuan, *The order types of the supports of p-adic algebraic Hahn series*.
  Theorem, proposition, lemma, and definition numbers in this library refer to this paper.
-/

namespace PAdicOrderType

open TrustworthyKedlaya pAdicHahnSeries Ordinal

section SupportOrderType

open Bornology

/-- **Order-type dichotomy** (Theorem A): the support of a `ℚ_[p]`-algebraic p-adic Hahn
series has order type at most `ω` or exactly `ω ^ ω`.

Kedlaya's upper bound (Proposition 2.11) and finite-rank exclusion
`PAdicOrderType.typeLT_support_le_omega0_of_lt_omega0_pow_omega0` (Theorem 4.1) exclude all
intermediate order types. -/
theorem typeLT_support_le_omega0_or_eq_omega0_pow_omega0 {p : ℕ} [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f) :
    typeLT f.support ≤ omega0 ∨ typeLT f.support = omega0 ^ omega0 := by
  rcases (kedlaya_2001b_ordinal_bound p f hf).lt_or_eq with hlt | heq
  · exact Or.inl (typeLT_support_le_omega0_of_lt_omega0_pow_omega0 f hf hlt)
  · exact Or.inr heq

/-- **Bounded-support finiteness** (Theorem B, Proposition 4.2): an algebraic p-adic Hahn
series with bounded support has finite support.

Adding a monomial above the support gives a successor order type. The order-type dichotomy
then forces the enlarged support to be finite. -/
theorem support_finite_of_isAlgebraic_of_isBounded {p : ℕ} [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) (hf1 : IsAlgebraic ℚ_[p] f) (hf2 : IsBounded f.support) :
    f.support.Finite :=
  finite_support_of_isAlgebraic_of_isBounded f hf1 hf2

/-- **Order-type trichotomy** (Theorem A): the support of a `ℚ_[p]`-algebraic p-adic Hahn
series has order type a natural number, `ω`, or `ω ^ ω`. The natural-number case includes the
empty support of the zero series. -/
theorem typeLT_support_eq_nat_or_eq_omega0_or_eq_omega0_pow_omega0 {p : ℕ} [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f) :
    (∃ n : ℕ, typeLT f.support = n) ∨
    typeLT f.support = omega0 ∨
    typeLT f.support = omega0 ^ omega0 := by
  rcases typeLT_support_le_omega0_or_eq_omega0_pow_omega0 f hf with hle | heq
  · exact hle.lt_or_eq.imp lt_omega0.mp Or.inl
  · exact Or.inr (Or.inr heq)

/-- Theorem A in the algebraic closure: the Hahn expansion of an element of `PadicAlgCl p`
has support order type at most `ω` or exactly `ω ^ ω`, using the chosen embedding into
`𝕃_[p]`. -/
theorem typeLT_support_padicAlgCl_le_omega0_or_eq_omega0_pow_omega0
    {p : ℕ} [Fact (Nat.Prime p)] (f : PadicAlgCl p) :
    typeLT (f : 𝕃_[p]).support ≤ omega0 ∨ typeLT (f : 𝕃_[p]).support = omega0 ^ omega0 := by
  apply typeLT_support_le_omega0_or_eq_omega0_pow_omega0 (p := p) f
  exact (isAlgebraic_qp_iff_mem_range_padicAlgCl _).mpr ⟨f, rfl⟩

end SupportOrderType

section PuiseuxOrderType

/-- **Strict Puiseux characterization** (Theorem C, Proposition 4.3): a `ℚ_[p]`-algebraic
p-adic Hahn series has support order type at most `ω` if and only if it lies in the image of
`PAdicOrderType.pAdicStrictPuiseux` under the chosen Hahn embedding. -/
theorem typeLT_support_le_omega0_iff_mem_pAdicStrictPuiseux_range {p : ℕ} [Fact (Nat.Prime p)]
    (f : 𝕃_[p]) (hf : IsAlgebraic ℚ_[p] f) :
    typeLT f.support ≤ omega0 ↔ f ∈ Set.range ((↑) : pAdicStrictPuiseux p → 𝕃_[p]) := by
  constructor
  · intro hord
    obtain ⟨a, ha⟩ := (isAlgebraic_qp_iff_mem_range_padicAlgCl f).mp hf
    have haP : a ∈ pAdicStrictPuiseux p := mem_pAdicStrictPuiseux_of_finite_support_below a (by
      intro r
      rw [ha]
      exact finite_support_inter_Iio_of_typeLT_le_omega0 f hf hord r)
    exact ⟨⟨a, haP⟩, ha⟩
  · rintro ⟨y, hy⟩
    obtain ⟨⟨T, hT⟩, _⟩ := (exists_pAdicStrictPuiseux_iff f).mp ⟨y, hy.symm⟩
    exact typeLT_support_le_omega0_of_finite_below f
      (finite_support_inter_Iio_of_bounded_denominators f T hT)

/-- Theorem C in the algebraic closure: an element of `PadicAlgCl p` belongs to the strict
p-adic Puiseux field if and only if its Hahn expansion has support order type at most `ω`. -/
theorem typeLT_support_padicAlgCl_le_omega0_iff_mem_pAdicStrictPuiseux {p : ℕ} [Fact (Nat.Prime p)]
    (f : PadicAlgCl p) :
    typeLT (f : 𝕃_[p]).support ≤ omega0 ↔ f ∈ pAdicStrictPuiseux p := by
  have hf : IsAlgebraic ℚ_[p] (f : 𝕃_[p]) := by
    rw [coe_coe]
    exact (Algebra.IsAlgebraic.isAlgebraic f).algHom (algClEmbd p)
  rw [typeLT_support_le_omega0_iff_mem_pAdicStrictPuiseux_range _ hf]
  constructor
  · rintro ⟨x, hx⟩
    have heq : f = x.val := algClEmbd_injective (by simpa only [coe_coe] using hx.symm)
    exact heq.symm ▸ x.property
  · intro hfP
    exact ⟨⟨f, hfP⟩, rfl⟩

end PuiseuxOrderType

section Bialgebraicity

open LaurentSeries

/-- **Bialgebraicity criterion** (Theorem D, Proposition 4.4): for a rational-exponent Hahn
series `f` over `𝔽ᵃ_[p]`, the following conditions are equivalent.

* `f` is algebraic over `𝔽_[p]⸨X⸩` and its shadow is algebraic over `ℚ_[p]`.
* The shadow lies in the image of the strict p-adic Puiseux field.
* The shadow is algebraic over `ℚ_[p]` and has support order type at most `ω`.
* The exponents of `f` have a common positive denominator and its coefficient range is finite.

The first three conditions are those of Theorem D, where `shadow` is the shadow map `Θ` of
Definition 2.7. The fourth is an explicit coefficient criterion. The equivalences are packaged
as `List.TFAE`. -/
theorem bialgebraic_tfae {p : ℕ} [Fact (Nat.Prime p)] (f : HahnSeries ℚ 𝔽ᵃ_[p]) :
    List.TFAE [
      IsAlgebraic (𝔽_[p])⸨X⸩ f ∧ IsAlgebraic ℚ_[p] (shadow f),
      shadow f ∈ Set.range ((↑) : pAdicStrictPuiseux p → 𝕃_[p]),
      IsAlgebraic ℚ_[p] (shadow f) ∧ typeLT (shadow f).support ≤ omega0,
      (∃ T : ℕ+, ∀ q ∈ f.support, (T * q).isInt) ∧ (Set.range f.coeff).Finite] := by
  have hs : (shadow f).support = f.support := by
    change Function.support (shadow f).coeff = Function.support f.coeff
    rw [coeff_shadow]
  have hpuiseux : (shadow f ∈ Set.range ((↑) : pAdicStrictPuiseux p → 𝕃_[p])) ↔
      (∃ T : ℕ+, ∀ q ∈ f.support, (T * q).isInt) ∧ (Set.range f.coeff).Finite := by
    rw [← hs, ← coeff_shadow f, ← exists_pAdicStrictPuiseux_iff]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩
  tfae_have 1 → 3 := by
    rintro ⟨hfp, hqp⟩
    refine ⟨hqp, ?_⟩
    have hlt := typeLT_support_lt_omega0_pow_omega0_of_isAlgebraic_laurentSeries f
      (hfp.tower_top (LaurentSeries 𝔽ᵃ_[p]))
    rw [← Ordinal.typeLT_set_congr hs] at hlt
    exact typeLT_support_le_omega0_of_lt_omega0_pow_omega0 (shadow f) hqp hlt
  tfae_have 3 → 2 := by
    rintro ⟨hqp, hle⟩
    exact (typeLT_support_le_omega0_iff_mem_pAdicStrictPuiseux_range _ hqp).mp hle
  tfae_have 2 → 4 := hpuiseux.mp
  tfae_have 4 → 1 := by
    intro h
    obtain ⟨T, hT⟩ := h.1
    have hn : (T : ℚ) ≠ 0 := by exact_mod_cast T.ne_zero
    constructor
    · apply (isIntegral_hahn_of_support_int_div_of_finite_coeff T ?_ h.2).isAlgebraic
      intro q hq
      refine ⟨(T * q).num, (eq_div_iff hn).mpr ?_⟩
      rw [mul_comm]
      exact Rat.eq_num_of_isInt (hT q hq)
    · obtain ⟨x, hx⟩ := hpuiseux.mpr h
      exact (isAlgebraic_qp_iff_mem_range_padicAlgCl _).mpr ⟨x.val, hx⟩
  tfae_finish

end Bialgebraicity

end PAdicOrderType
