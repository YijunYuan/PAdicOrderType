/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.AggregateData
import TrustworthyKedlaya.Kedlaya.SabcOrderType
import TrustworthyKedlaya.Lp.Coeff

/-!
# Valuation facts for the finite-rank exclusion

Elementary valuation bookkeeping in the totally ramified extension
`ℚᶜᵘⁿ_[p,T] = ℚᶜᵘⁿ_[p](p^{1/T})`, with `Valued.v (pInvTQ p T) = ofAdd (-1)`.
The embedding and ramification identities reuse `PAdicOrderType.RamifiedCoefficients`;
the coefficient-bundle valuation follows from `Cs_term_zero_v_eq_one` and
`Cs_diff_alg_v_le` in `PAdicOrderType.CoefficientCosets`. It gives the valuation of the
coefficients `A_d` computed in Section 3.1.

## Main statements

- `PAdicOrderType.valued_cs_eq_one`: the coefficient bundles `C_s` of
  `PAdicOrderType.CoefficientCosets.fhat` are units (their leading term is a Teichmüller
  unit and all later terms are divisible by `p^{1/T}`);
- `PAdicOrderType.RamifiedCoefficients.valued_v_algebraMap_K₀_K`: `v_K (ι z) = (v_{K₀} z) ^ T` for
  the
  inclusion `ι : ℚᶜᵘⁿ_[p] → ℚᶜᵘⁿ_[p,T]` (ramification index `T`);
- `PAdicOrderType.exists_valued_oqpCUn_embd_eq`: a nonzero `a ∈ ℤᶜᵘⁿ_[p]` has
  `v_K (a) = ofAdd (-(T k))` for a natural `k` independent of `T`;
- `PAdicOrderType.exists_shift`: multiplication by `p^k` shifts the support of a `p`-adic
  Hahn series by `k`, preserving algebraicity, and
  `PAdicOrderType.typeLT_image_add_right`: translation preserves order types. These give the
  reduction to integral `f` in the proof of Theorem 4.1.
-/

namespace PAdicOrderType

open RamifiedCoefficients CoefficientCosets TrustworthyKedlaya Ordinal

variable {p : ℕ} [Fact (Nat.Prime p)]

/-! ### Helpers: value-group arithmetic in `WithZero (Multiplicative ℤ)` -/

/-- Taking a natural power in the multiplicative value group multiplies the additive
exponent by that natural number. -/
theorem coe_ofAdd_pow (a : ℤ) (n : ℕ) :
    ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ n =
      ((Multiplicative.ofAdd ((n : ℤ) * a) : Multiplicative ℤ) :
        WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_pow, ← ofAdd_nsmul]
  congr 2

/-- A negative additive exponent gives a multiplicative value strictly below `1`. -/
theorem coe_ofAdd_lt_one {a : ℤ} (ha : a < 0) :
    ((Multiplicative.ofAdd a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
  exact ha

/-! ### Helpers: valuations on `ℚᶜᵘⁿ_[p]` -/

/-- Units of `ℤᶜᵘⁿ_[p]` have valuation `1` in `ℚᶜᵘⁿ_[p]`. -/
theorem valued_algebraMap_oqpCUn_of_isUnit {u : ℤᶜᵘⁿ_[p]} (hu : IsUnit u) :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) u) = 1 :=
  Valuation.Integers.one_of_isUnit' hu
    (fun _ => (IsDiscreteValuationRing.maximalIdeal (ℤᶜᵘⁿ_[p])).valuation_le_one _)

/-- `Valued.v (p : ℚᶜᵘⁿ_[p]) = ofAdd (-1)`. -/
theorem valued_natCast_p_qpCUn :
    Valued.v ((p : ℕ) : ℚᶜᵘⁿ_[p]) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h := valued_v_p_zpow (p := p) 1
  rwa [zpow_one] at h

/-- `v_{K₀}(p) = ofAdd (-1)` for `p` viewed in `ℤᶜᵘⁿ_[p]`. -/
theorem valued_algebraMap_oqpCUn_p :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) ((p : ℕ) : ℤᶜᵘⁿ_[p])) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_natCast]
  exact valued_natCast_p_qpCUn

/-! ### Aggregate coefficients and support translations -/

/-- The coefficient bundles `C_s` are units: `Valued.v (C_s) = 1`. Hence the coefficient
`A_d` has additive valuation `aggExp / T`, as computed in Section 3.1. -/
theorem valued_cs_eq_one {f : 𝕃_[p]} {T : ℕ+} {S : Set DigitSeries}
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (s : ↥(Stilde hf2)) :
    Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)]) (Cs hf2 s)) = 1 := by
  -- The first partial sum is a unit, and the remaining tail has valuation < 1.
  have hfirst : Valued.v
      (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)]) (Cs_partial hf2 s 1)) = 1 := by
    simpa only [Cs_partial, Finset.sum_range_one] using Cs_term_zero_v_eq_one hf2 s
  have htail := Cs_diff_alg_v_le hf2 s 1
  rw [map_sub] at htail
  have hlt := htail.trans_lt (coe_ofAdd_lt_one (by norm_num : -(1 : ℤ) < 0))
  rw [← hfirst] at hlt
  exact (Valuation.map_eq_of_sub_lt _ hlt).trans hfirst

/-- A nonzero `a ∈ ℤᶜᵘⁿ_[p]` has valuation `ofAdd (-(T k))` in `ℚᶜᵘⁿ_[p,T]`, for a natural
`k` (its `p`-adic valuation) independent of `T`. -/
theorem exists_valued_oqpCUn_embd_eq {a : ℤᶜᵘⁿ_[p]} (ha : a ≠ 0) :
    ∃ k : ℕ, ∀ T : ℕ+,
      Valued.v (algebraMap (ℤᶜᵘⁿ_[p,(T : ℕ)]) (ℚᶜᵘⁿ_[p,(T : ℕ)]) (OQpCUn_embd p T a)) =
        ((Multiplicative.ofAdd (-((T : ℤ) * k)) : Multiplicative ℤ) :
          WithZero (Multiplicative ℤ)) := by
  obtain ⟨n, h⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha
    (WittVector.irreducible p)
  obtain ⟨u, hu⟩ := h.symm
  have hK₀ : Valued.v (algebraMap (ℤᶜᵘⁿ_[p]) (ℚᶜᵘⁿ_[p]) a) =
      ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [← hu, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow,
      valued_algebraMap_oqpCUn_of_isUnit u.isUnit, mul_one, valued_algebraMap_oqpCUn_p,
      coe_ofAdd_pow, mul_neg, mul_one]
  refine ⟨n, fun T => ?_⟩
  rw [algebraMap_OQpCUn_embd_compat, valued_v_algebraMap_K₀_K, hK₀, coe_ofAdd_pow]
  congr 2
  ring

/-- **Shift by `p^k`.** For `f ∈ 𝕃_[p]` and `k : ℕ` there is `f' ∈ 𝕃_[p]` with
`f'.coeff r = f.coeff (r - k)`, hence `f'.support = f.support + k`, and `f'` is algebraic over
`ℚ_[p]` whenever `f` is. This is the translation step in the proof of Theorem 4.1. -/
theorem exists_shift (f : 𝕃_[p]) (k : ℕ) :
    ∃ f' : 𝕃_[p], (∀ r : ℚ, f'.coeff r = f.coeff (r - k)) ∧
      f'.support = (fun q : ℚ => q + k) '' f.support ∧
      (IsAlgebraic ℚ_[p] f → IsAlgebraic ℚ_[p] f') := by
  refine ⟨pAdicHahnSeries.single (k : ℚ) 1 * f,
    fun r => pAdicHahnSeries.coeff_ppow_mul _ _ _, ?_, ?_⟩
  · ext q
    simp only [Set.mem_image]
    rw [pAdicHahnSeries.mem_support_iff, pAdicHahnSeries.coeff_ppow_mul]
    constructor
    · intro h
      exact ⟨q - k, (pAdicHahnSeries.mem_support_iff _ _).mpr h, by ring⟩
    · rintro ⟨q', hq', rfl⟩
      rw [add_sub_cancel_right]
      exact (pAdicHahnSeries.mem_support_iff _ _).mp hq'
  · intro hf
    refine IsAlgebraic.mul ?_ hf
    apply pAdicHahnSeries.alg_of_fin_supp
    refine (Set.finite_singleton (k : ℚ)).subset ?_
    intro r hr
    rw [pAdicHahnSeries.mem_support_iff, pAdicHahnSeries.coeff_single] at hr
    by_contra h
    exact hr (if_neg h)

/-- Translation preserves order types of well-ordered subsets of `ℚ`. -/
theorem typeLT_image_add_right (S : Set ℚ) [WellFoundedLT ↥S] (k : ℚ)
    [WellFoundedLT ↥((fun q : ℚ => q + k) '' S)] :
    typeLT ↥((fun q : ℚ => q + k) '' S) = typeLT ↥S := by
  apply le_antisymm
  · refine Ordinal.typeLT_set_le_of_strictMono (γ := ↥S)
      (fun y => ⟨y.1 - k, ?_⟩) ?_
    · obtain ⟨q, hq, hqy⟩ := y.2
      rw [← hqy]; simpa using hq
    · intro y z hyz
      change y.1 - k < z.1 - k
      exact sub_lt_sub_right (Subtype.coe_lt_coe.mpr hyz) k
  · refine Ordinal.typeLT_set_le_of_strictMono (γ := ↥((fun q : ℚ => q + k) '' S))
      (fun x => ⟨x.1 + k, ⟨x.1, x.2, rfl⟩⟩) ?_
    intro x y hxy
    change x.1 + k < y.1 + k
    have := Subtype.coe_lt_coe.mpr hxy
    linarith

end PAdicOrderType
