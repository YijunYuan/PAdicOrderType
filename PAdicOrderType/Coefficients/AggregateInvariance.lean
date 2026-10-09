/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.AggregateData

/-!
# Invariance of aggregate coefficients

An aggregate coefficient depends only on the integer-indexed coefficient
sequence of its support coset. This includes the zero extension to empty
cosets, and transfers coefficient invariance directly to aggregate data. In the proof of
Lemma 3.12, this reduces the comparison of the coefficients `A_d` to the comparison of the
summands `A_{d,l}`.
-/

namespace PAdicOrderType

open RamifiedCoefficients CoefficientCosets

variable {p : ℕ} [Fact (Nat.Prime p)] {f : 𝕃_[p]} {T : ℕ+}
    {D : Set DigitSeries}

private lemma muQ_eq_aggExp
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x}) (d : D) :
    muQ hf2 d = ((aggExp hf2 d : ℚ) - d.val.norm p) / (T : ℚ) := by
  have hT0 : (T : ℚ) ≠ 0 := by exact_mod_cast T.ne_zero
  rw [eq_div_iff hT0, aggExp_cast]
  ring

private lemma aggExp_le_of_coeff
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d e : D)
    (hcoeff : ∀ l : ℤ,
      f.coeff (((l : ℚ) - d.val.norm p) / (T : ℚ)) =
        f.coeff (((l : ℚ) - e.val.norm p) / (T : ℚ))) :
    aggExp hf2 d ≤ aggExp hf2 e := by
  have hTpos : (0 : ℚ) < (T : ℚ) := by exact_mod_cast T.pos
  have he : f.coeff (((aggExp hf2 e : ℚ) - e.val.norm p) / (T : ℚ)) ≠ 0 := by
    rw [← muQ_eq_aggExp hf2 e]
    exact muQ_mem_support hf2 e
  have hd : ((aggExp hf2 e : ℚ) - d.val.norm p) / (T : ℚ) ∈ f.support := by
    change f.coeff _ ≠ 0
    rw [hcoeff]
    exact he
  have hs : ((aggExp hf2 e : ℚ) - d.val.norm p) / (T : ℚ) ∈ Sd p f T d.val := by
    refine ⟨hd, ?_⟩
    have hint : d.val.norm p + (T : ℚ) *
        (((aggExp hf2 e : ℚ) - d.val.norm p) / (T : ℚ)) = (aggExp hf2 e : ℚ) := by
      field_simp
      ring
    change (d.val.norm p + (T : ℚ) *
      (((aggExp hf2 e : ℚ) - d.val.norm p) / (T : ℚ))).isInt = true
    rw [hint]
    exact isInt_intCast' _
  have hmin := (Sd_isWF f T d.val).min_le (Sd_nonempty hf2 d.property) hs
  change muQ hf2 d ≤ _ at hmin
  have hle : (aggExp hf2 d : ℚ) ≤ (aggExp hf2 e : ℚ) := by
    have hm := (le_div_iff₀ hTpos).mp hmin
    rw [aggExp_cast]
    linarith
  exact_mod_cast hle

/-- Equal coefficient sequences along two cosets give equal aggregate
coefficients. The minimum in each coset is the first nonzero integer index. -/
theorem ad_congr_coeff
    (hf2 : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    (d e : D)
    (hcoeff : ∀ l : ℤ,
      f.coeff (((l : ℚ) - d.val.norm p) / (T : ℚ)) =
        f.coeff (((l : ℚ) - e.val.norm p) / (T : ℚ))) :
    ad hf2 d = ad hf2 e := by
  have hexp : aggExp hf2 d = aggExp hf2 e :=
    le_antisymm (aggExp_le_of_coeff hf2 d e hcoeff)
      (aggExp_le_of_coeff hf2 e d fun l => (hcoeff l).symm)
  have hterms : ∀ w : ℕ,
      Cs_term hf2 (muToStilde hf2 d) w = Cs_term hf2 (muToStilde hf2 e) w := by
    intro w
    have hc := hcoeff (aggExp hf2 d + (w : ℤ))
    have hd : (((aggExp hf2 d + (w : ℤ) : ℤ) : ℚ) - d.val.norm p) / (T : ℚ) =
        muQ hf2 d + (w : ℚ) / (T : ℚ) := by
      push_cast
      rw [aggExp_cast]
      have hT0 : (T : ℚ) ≠ 0 := by exact_mod_cast T.ne_zero
      field_simp
      ring
    have he : (((aggExp hf2 d + (w : ℤ) : ℤ) : ℚ) - e.val.norm p) / (T : ℚ) =
        muQ hf2 e + (w : ℚ) / (T : ℚ) := by
      rw [hexp]
      push_cast
      rw [aggExp_cast]
      have hT0 : (T : ℚ) ≠ 0 := by exact_mod_cast T.ne_zero
      field_simp
      ring
    rw [hd, he] at hc
    simp only [Cs_term, muToStilde, hc]
  have hpartial : ∀ N : ℕ,
      Cs_partial hf2 (muToStilde hf2 d) N = Cs_partial hf2 (muToStilde hf2 e) N := by
    intro N
    unfold Cs_partial
    exact Finset.sum_congr rfl fun w _ => hterms w
  have hlimit : algebraMap (ℤᶜᵘⁿ_[p, (T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
      (Cs hf2 (muToStilde hf2 d)) =
      algebraMap (ℤᶜᵘⁿ_[p, (T : ℕ)]) (ℚᶜᵘⁿ_[p, (T : ℕ)])
      (Cs hf2 (muToStilde hf2 e)) := by
    apply tendsto_nhds_unique (Cs_tendsto hf2 (muToStilde hf2 d))
    simpa only [hpartial] using Cs_tendsto hf2 (muToStilde hf2 e)
  simp only [ad, hexp, hlimit]

/-- The zero-extended aggregate data of canonical representatives inherit
every equality between their integer-indexed coefficient sequences. -/
theorem adFun_congr_coeff
    (hf2 : IsRepModZ ((DigitSeries.norm p) ''
      {d : DigitSeries | d.IsP p ∧ ∃ l : ℤ,
        ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support})
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x})
    {d e : DigitSeries} (hd : d.IsP p) (he : e.IsP p)
    (hcoeff : ∀ l : ℤ,
      f.coeff (((l : ℚ) - d.norm p) / (T : ℚ)) =
        f.coeff (((l : ℚ) - e.norm p) / (T : ℚ))) :
    adFun hf2 d = adFun hf2 e := by
  classical
  have hmem : (d.IsP p ∧ ∃ l : ℤ, ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support) ↔
      (e.IsP p ∧ ∃ l : ℤ, ((l : ℚ) - e.norm p) / (T : ℚ) ∈ f.support) := by
    constructor
    · rintro ⟨_, l, hl⟩
      refine ⟨he, l, ?_⟩
      change f.coeff _ ≠ 0 at hl ⊢
      rwa [hcoeff] at hl
    · rintro ⟨_, l, hl⟩
      refine ⟨hd, l, ?_⟩
      change f.coeff _ ≠ 0 at hl ⊢
      rwa [hcoeff]
  by_cases hdm : d.IsP p ∧ ∃ l : ℤ, ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support
  · rw [adFun_apply_of_mem hf2 hdm, adFun_apply_of_mem hf2 (hmem.mp hdm)]
    exact ad_congr_coeff hf2 _ _ hcoeff
  · simp only [adFun, Set.mem_ofPred_eq, dif_neg hdm, dif_neg (mt hmem.mpr hdm)]

end PAdicOrderType
