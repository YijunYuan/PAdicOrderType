/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.AggregateData
import PAdicOrderType.Digits.WordGapGeometry

/-!
# Tails as representatives

For a `p`-adic Hahn series `f` whose support lies in the slices `S_{a,b,c₀,m}`
(`m₁ ≤ m ≤ m₂`) and for `T = a p^h`, the `h`-tails of the digit vectors of the
elements of the support are exactly the canonical representatives of
`-T·Supp(f)` modulo `ℤ`. This file constructs the representative set
`𝔇_h = {d ∈ ℙ | ∃ l ∈ ℤ, (l - ‖d‖)/T ∈ Supp f}` together with its defining
properties, for an *arbitrary* `h` (no tail threshold, no infinitude, no order
type hypothesis).

In the terminology of Section 2.2, the tails are the digit vectors `T`-representing the
support points. Their identification with tails is the first step of the proof of Lemma 3.8.
-/

namespace PAdicOrderType

open DigitSeries RamifiedCoefficients CoefficientCosets TrustworthyKedlaya

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- A rational with `Rat.isInt` strictly between `-1` and `1` is `0`. -/
private lemma eq_zero_of_isInt_of_neg_one_lt_of_lt_one {x : ℚ} (hx : x.isInt = true)
    (h1 : (-1 : ℚ) < x) (h2 : x < 1) : x = 0 := by
  have hnum : x = (x.num : ℚ) := Rat.eq_num_of_isInt hx
  rw [hnum] at h1 h2 ⊢
  have h1' : (-1 : ℤ) < x.num := by exact_mod_cast h1
  have h2' : x.num < (1 : ℤ) := by exact_mod_cast h2
  rw [show x.num = 0 by omega]
  simp

/-- The tail identity in `qval` form with the scalar written as `a · p^h`:
`a·p^h·q_m(𝐝) = (p^h·m − π_h(𝐛)) − ‖tail_h(𝐛)‖` for `𝐛 = ofFinsupp 𝐝`. -/
private lemma pow_mul_qval_eq_tr {a : ℕ+} (h : ℕ) (m : ℤ) (dv : ℕ →₀ ℕ) :
    (a : ℚ) * (p : ℚ) ^ h * qval p a m dv
      = (((p : ℤ) ^ h * m - (pih p (ofFinsupp dv) h : ℤ) : ℤ) : ℚ)
        - (tailh (ofFinsupp dv) h).norm p := by
  have ha : (a : ℚ) ≠ 0 := by exact_mod_cast a.ne_zero
  have htail := pow_mul_norm_eq_pih_add_norm_tailh p (ofFinsupp dv) h
  have hqval : qval p a m dv
      = 1 / (a : ℚ) * ((m : ℚ) - (ofFinsupp dv).norm p) := by
    rw [ofFinsupp_norm p dv]
    rfl
  rw [hqval]
  have hcalc : (a : ℚ) * (p : ℚ) ^ h
        * (1 / (a : ℚ) * ((m : ℚ) - (ofFinsupp dv).norm p))
      = (p : ℚ) ^ h * (m : ℚ) - (p : ℚ) ^ h * (ofFinsupp dv).norm p := by
    field_simp
  rw [hcalc, htail]
  push_cast
  ring

/-- The tail identity: `T · q_m(𝐝) = (p^h m - π_h(𝐝)) - ‖tail_h 𝐝‖` for `T = a p^h`.
Thus the digit vector `T`-representing `q_m(𝐝)` is `tail_h 𝐝`, as in the proof of
Lemma 3.8. -/
theorem mul_qval_eq_sub_norm_tailh {a : ℕ+} {T : ℕ+} {h : ℕ} (hT : (T : ℕ) = (a : ℕ) * p ^ h)
    (m : ℤ) (dv : ℕ →₀ ℕ) :
    (T : ℚ) * qval p a m dv
      = (((p : ℤ) ^ h * m - (pih p (ofFinsupp dv) h : ℤ) : ℤ) : ℚ)
        - (tailh (ofFinsupp dv) h).norm p := by
  have hT_cast : (T : ℚ) = (a : ℚ) * (p : ℚ) ^ h := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hT
  rw [hT_cast]
  exact pow_mul_qval_eq_tr h m dv

/-- **Tails are the representatives of `-T·Supp(f)`.** For `T = a p^h`, the set
`𝔇_h = {d ∈ ℙ | ∃ l ∈ ℤ, (l - ‖d‖)/T ∈ Supp f}` consists of proper digit series, its norms
represent `-T·Supp(f)` modulo `ℤ`, every `h`-tail of a digit vector of a support element
belongs to it, and every member is such a tail. These are the digit vectors `T`-representing
the support points, as in the proof of Lemma 3.8. -/
theorem tail_rep_data (f : 𝕃_[p]) {a : ℕ+} {c₀ : ℕ} {m₁ m₂ : ℤ}
    (hsub : f.support ⊆ ⋃ m ∈ Set.Icc m₁ m₂, Sabc_m p a c₀ m)
    {T : ℕ+} {h : ℕ} (hT : (T : ℕ) = (a : ℕ) * p ^ h) :
    (∀ d ∈ {d : DigitSeries | d.IsP p ∧ ∃ l : ℤ, ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support},
        d.IsP p) ∧
      IsRepModZ ((DigitSeries.norm p) ''
          {d : DigitSeries | d.IsP p ∧ ∃ l : ℤ, ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support})
        {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x} ∧
      (∀ (m : ℤ) (dv : ℕ →₀ ℕ), (∀ j, dv j < p) → qval p a m dv ∈ f.support →
        tailh (ofFinsupp dv) h ∈
          {d : DigitSeries | d.IsP p ∧ ∃ l : ℤ, ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support}) ∧
      (∀ d ∈ {d : DigitSeries | d.IsP p ∧ ∃ l : ℤ, ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support},
        ∃ (m : ℤ) (dv : ℕ →₀ ℕ), (∀ j, dv j < p) ∧ qval p a m dv ∈ f.support ∧
          d = tailh (ofFinsupp dv) h) := by
  classical
  set D : Set DigitSeries :=
    {d | d.IsP p ∧ ∃ l : ℤ, ((l : ℚ) - d.norm p) / (T : ℚ) ∈ f.support}
    with hD_def
  have hT0 : (T : ℚ) ≠ 0 := by exact_mod_cast T.ne_zero
  -- the tail identity, in terms of `T`
  have hkey : ∀ (m : ℤ) (dv : ℕ →₀ ℕ),
      (T : ℚ) * qval p a m dv
        = (((p : ℤ) ^ h * m - (pih p (ofFinsupp dv) h : ℤ) : ℤ) : ℚ)
          - (tailh (ofFinsupp dv) h).norm p :=
    fun m dv => mul_qval_eq_sub_norm_tailh hT m dv
  -- every support element has a digit-vector representation
  have hrep : ∀ q ∈ f.support, ∃ (m : ℤ) (dv : ℕ →₀ ℕ),
      (∀ j, dv j < p) ∧ q = qval p a m dv := by
    intro q hq
    obtain ⟨m, -, hqm⟩ := Set.mem_iUnion₂.mp (hsub hq)
    obtain ⟨dv, hdig, -, hqval⟩ := hqm
    exact ⟨m, dv, hdig, hqval⟩
  -- tails of digit vectors of support elements belong to `𝔇_h`
  have htail_mem : ∀ (m : ℤ) (dv : ℕ →₀ ℕ), (∀ j, dv j < p) →
      qval p a m dv ∈ f.support → tailh (ofFinsupp dv) h ∈ D := by
    intro m dv hdig hq
    refine ⟨tailh_isP (ofFinsupp_isP p dv hdig) h,
      (p : ℤ) ^ h * m - (pih p (ofFinsupp dv) h : ℤ), ?_⟩
    rw [← hkey m dv, mul_div_cancel_left₀ _ hT0]
    exact hq
  -- conversely, every member of `𝔇_h` is such a tail
  have hD_eq_tail : ∀ d ∈ D, ∃ (m : ℤ) (dv : ℕ →₀ ℕ), (∀ j, dv j < p) ∧
      qval p a m dv ∈ f.support ∧ d = tailh (ofFinsupp dv) h := by
    rintro d ⟨hdP, l, hql⟩
    obtain ⟨m, dv, hdig, hq_eq⟩ := hrep _ hql
    have htP : DigitSeries.IsP (tailh (ofFinsupp dv) h) p :=
      tailh_isP (ofFinsupp_isP p dv hdig) h
    have hkq := hkey m dv
    rw [← hq_eq] at hkq
    have hTq : (T : ℚ) * (((l : ℚ) - d.norm p) / (T : ℚ))
        = (l : ℚ) - d.norm p := by
      rw [mul_comm]
      exact div_mul_cancel₀ _ hT0
    set l' : ℤ := (p : ℤ) ^ h * m - (pih p (ofFinsupp dv) h : ℤ) with hl'_def
    have hcomb : ((l - l' : ℤ) : ℚ)
        = d.norm p - (tailh (ofFinsupp dv) h).norm p := by
      push_cast
      linarith [hkq, hTq]
    have hnd := DigitSeries.norm_mem_Ico p d hdP
    have hnt := DigitSeries.norm_mem_Ico p _ htP
    have hll' : l = l' := by
      have h1 : ((l - l' : ℤ) : ℚ) < 1 := by
        rw [hcomb]; linarith [hnd.2, hnt.1]
      have h2 : (-1 : ℚ) < ((l - l' : ℤ) : ℚ) := by
        rw [hcomb]; linarith [hnd.1, hnt.2]
      have h1' : l - l' < 1 := by exact_mod_cast h1
      have h2' : -1 < l - l' := by exact_mod_cast h2
      omega
    have hnorm_eq : d.norm p = (tailh (ofFinsupp dv) h).norm p := by
      have h0 : ((l - l' : ℤ) : ℚ) = 0 := by rw [hll']; simp
      linarith [hcomb, h0]
    exact ⟨m, dv, hdig, hq_eq ▸ hql,
      DigitSeries.IsP_norm_injective hdP htP hnorm_eq⟩
  -- norms of members of `𝔇_h` lie in `[0, 1)`
  have hnormD_Ico : ∀ d ∈ D, d.norm p ∈ Set.Ico (0 : ℚ) 1 := fun d hd =>
    DigitSeries.norm_mem_Ico p d hd.1
  -- the norms of `𝔇_h` represent `-T·Supp(f)` modulo `ℤ`
  have hrepZ : IsRepModZ ((DigitSeries.norm p) '' D)
      {x | ∃ q ∈ f.support, -1 * (T : ℚ) * q = x} := by
    constructor
    · rintro bq ⟨q, hq, rfl⟩
      obtain ⟨m, dv, hdig, hq_eq⟩ := hrep q hq
      subst hq_eq
      have hkq := hkey m dv
      have htD : tailh (ofFinsupp dv) h ∈ D := htail_mem m dv hdig hq
      have hint : ((tailh (ofFinsupp dv) h).norm p
          - -1 * (T : ℚ) * qval p a m dv).isInt = true := by
        have heq : (tailh (ofFinsupp dv) h).norm p
              - -1 * (T : ℚ) * qval p a m dv
            = (((p : ℤ) ^ h * m - (pih p (ofFinsupp dv) h : ℤ) : ℤ) : ℚ) := by
          linear_combination hkq
        rw [heq]
        exact isInt_intCast' _
      refine ⟨(tailh (ofFinsupp dv) h).norm p, ⟨⟨_, htD, rfl⟩, hint⟩, ?_⟩
      rintro y ⟨⟨d', hd'D, rfl⟩, hy⟩
      have hdiff : (d'.norm p - (tailh (ofFinsupp dv) h).norm p).isInt
          = true := by
        have heq : d'.norm p - (tailh (ofFinsupp dv) h).norm p
            = (d'.norm p - -1 * (T : ℚ) * qval p a m dv)
              - ((tailh (ofFinsupp dv) h).norm p
                  - -1 * (T : ℚ) * qval p a m dv) := by
          ring
        rw [heq]
        exact isInt_sub' hy hint
      have h1 := hnormD_Ico d' hd'D
      have h2 := hnormD_Ico _ htD
      have hz := eq_zero_of_isInt_of_neg_one_lt_of_lt_one hdiff
        (by linarith [h1.1, h2.2]) (by linarith [h1.2, h2.1])
      linarith [hz]
    · rintro y ⟨d, hdD, rfl⟩
      obtain ⟨hdP, l, hql⟩ := hdD
      refine ⟨-1 * (T : ℚ) * (((l : ℚ) - d.norm p) / (T : ℚ)),
        ⟨_, hql, rfl⟩, ?_⟩
      have hTq : (T : ℚ) * (((l : ℚ) - d.norm p) / (T : ℚ))
          = (l : ℚ) - d.norm p := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ hT0
      have heq : d.norm p
          - -1 * (T : ℚ) * (((l : ℚ) - d.norm p) / (T : ℚ)) = ((l : ℤ) : ℚ) := by
        linear_combination hTq
      rw [heq]
      exact isInt_intCast' l
  exact ⟨fun d hd => hd.1, hrepZ, htail_mem, hD_eq_tail⟩

end PAdicOrderType
