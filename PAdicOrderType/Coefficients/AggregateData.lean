/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.CarryFreeCoefficients
import PAdicOrderType.Coefficients.CosetSums

/-!
# Aggregate coefficients of support cosets

Let proper digit vectors represent `-T` times the support of a p-adic Hahn series modulo
`ℤ`. Each representative `d` selects a least support exponent `s_d` and an integral
coefficient bundle `C_d`. Rescaling this bundle by the uniformizer to the integer power
`‖d‖ + T * s_d` gives the aggregate coefficient of the coset. These are the coefficients
`A_d` of (3.2) in Section 3.1.

## Main definitions

* `PAdicOrderType.aggExp`: the integer `‖d‖ + T * s_d`.
* `PAdicOrderType.ad`: the aggregate coefficient `π ^ (aggExp hf2 d) * C_d`, where
  `π` is the chosen `T`-th root of `p` in the ramified fraction field, which is the
  coefficient `A_d` of (3.2).
* `PAdicOrderType.adFun`: the aggregate coefficient function, extended by zero off
  the set of representatives.

## Implementation notes

The coefficient bundles are nonzero units. Thus their rescaling records the least
exponent in each coset and supplies the coefficients for the carry-free power expansion.
-/

namespace PAdicOrderType

open RamifiedCoefficients CoefficientCosets

/-- `CharZero ℚᶜᵘⁿ_[p,T]`, via the injective inclusion `ℚᶜᵘⁿ_[p] → ℚᶜᵘⁿ_[p,T]`. -/
instance instCharZeroQpCUnT (p : ℕ) [Fact (Nat.Prime p)] (T : ℕ+) :
    CharZero ℚᶜᵘⁿ_[p, (T : ℕ)] :=
  charZero_of_injective_algebraMap
    (RingHom.injective (algebraMap ℚᶜᵘⁿ_[p] ℚᶜᵘⁿ_[p, (T : ℕ)]))

/-- The uniformizer `p^{1/T}` of `ℚᶜᵘⁿ_[p,T]` is nonzero: its valuation is
`ofAdd(-1) ≠ 0`. -/
lemma pInvTQ_ne_zero (p : ℕ) [Fact (Nat.Prime p)] (T : ℕ+) :
    pInvTQ p (T : ℕ) ≠ 0 := by
  intro h0
  have hv := valued_v_pInvT p (T : ℕ)
  rw [h0, map_zero] at hv
  exact WithZero.zero_ne_coe hv

variable {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+} {S : Set DigitSeries}

/-- The integer exponent `‖d‖ + T * s_d`, where `s_d` is the least support point in
the coset represented by `d`. The residue condition ensures that this rational number
is integral. Divided by `T`, it is the valuation `v_p(A_d)` computed in Section 3.1. -/
noncomputable def aggExp
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : ℤ :=
  ((d.val.norm p : ℚ) + (T : ℚ) * muQ hf2 d).num

/-- The defining property of `aggExp`: as a rational, it is `‖d‖ + T·s_d`. -/
lemma aggExp_cast
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) :
    ((aggExp hf2 d : ℤ) : ℚ) = (d.val.norm p : ℚ) + (T : ℚ) * muQ hf2 d :=
  (Rat.eq_num_of_isInt (muQ_residue hf2 d)).symm

/-- The **aggregate coefficient** of a represented support coset: its integral
coefficient bundle multiplied by `π ^ (aggExp hf2 d)`, where `π` is the chosen `T`-th root
of `p` in the ramified fraction field. It equals the sum `A_d` of (3.2), the coefficients of
the support points `T`-represented by `d` weighted by the corresponding powers of `π`. -/
noncomputable def ad
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d : S) : ℚᶜᵘⁿ_[p, (T : ℕ)] :=
  pInvTQ p (T : ℕ) ^ aggExp hf2 d *
    algebraMap (ℤᶜᵘⁿ_[p, (T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)]) (Cs hf2 (muToStilde hf2 d))

open Classical in
/-- The aggregate coefficient function `DigitSeries → ℚᶜᵘⁿ_[p,T]`: `A_d` on `S`,
`0` elsewhere. This matches (3.2), where `A_d = 0` when no support point is
`T`-represented by `d`. It supplies the coefficients of `coefficientFamily p S (adFun hf2)`
in the carry-free coefficient formula. -/
noncomputable def adFun
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) :
    DigitSeries → ℚᶜᵘⁿ_[p, (T : ℕ)] :=
  fun d => if hd : d ∈ S then ad hf2 ⟨d, hd⟩ else 0

lemma adFun_apply_of_mem
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' S)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {d : DigitSeries} (hd : d ∈ S) :
    adFun hf2 d = ad hf2 ⟨d, hd⟩ := by
  unfold adFun
  exact dif_pos hd

end PAdicOrderType
