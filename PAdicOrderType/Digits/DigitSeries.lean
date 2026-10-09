/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Rat.Star
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Finite digit vectors and their base-p values

This file formalizes the digit vectors of Definition 2.3 and the uniqueness part of
Lemma 2.4. A digit vector is a finitely supported function from positive integers to natural
numbers. Its rational value is the finite sum of its digits weighted by negative powers of `p`.
Proper vectors have all digits below `p`; their values lie in `[0, 1)` and determine them
uniquely, even modulo integer translation.

## Main definitions

* `PAdicOrderType.DigitSeries`: finite digit vectors indexed by `ℕ+`, the direct sum of
  Definition 2.3 (2).
* `PAdicOrderType.DigitSeries.norm`: the additive map sending a vector to its rational value,
  the digit value `‖d‖` of Definition 2.3 (3).
* `PAdicOrderType.DigitSeries.IsP`: the predicate that every digit is strictly below `p`,
  which defines the set `P` of digit vectors in Definition 2.3 (1).

## Main statements

* `PAdicOrderType.DigitSeries.eq_of_norm_sub_isInt`: proper digit vectors whose values differ
  by an integer are equal, the uniqueness assertion of Lemma 2.4.

## Implementation notes

Digits are indexed starting at `1`, so the digit at position `i` has weight `p ^ (-i)`.
The function `PAdicOrderType.DigitSeries.coeffs` reverses a finite prefix for the
least-significant-first convention of `Nat.ofDigits`.
-/

@[expose] public section

namespace PAdicOrderType



/-- Finite digit vectors indexed by the positive integers: the direct sum of copies of `ℕ`
indexed by the positive integers, as in Definition 2.3 (2). -/
abbrev DigitSeries := ℕ+ →₀ ℕ

namespace DigitSeries

/-- The largest position at which a digit series is nonzero (`0` if the series vanishes). -/
noncomputable def maxIndex (f : DigitSeries) : ℕ :=
  f.support.sup fun i => (i : ℕ)

/-- The first `n` values of a digit function, listed as `[f n, …, f 1]`.
This places the least significant digit first, as required by `Nat.ofDigits`. -/
def coeffs (f : ℕ+ → ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => f (Nat.succPNat n) :: coeffs f n

/-- The base-`p` value of the first `n` digits of `f`, i.e. `Nat.ofDigits p (coeffs f n)`. -/
noncomputable def value (p : ℕ) (f : DigitSeries) (n : ℕ) : ℕ :=
  Nat.ofDigits p (coeffs f n)

/-- The first `n` positive-integer positions `{1, 2, …, n}` as a `Finset ℕ+`. -/
def indices (n : ℕ) : Finset ℕ+ :=
  (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩

@[simp] lemma coeffs_length (f : ℕ+ → ℕ) (n : ℕ) :
    (coeffs f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [coeffs, ih]

@[simp] lemma mem_indices (n k : ℕ) :
    Nat.succPNat k ∈ indices n ↔ k < n := by
  simp [indices]

@[simp] lemma indices_succ (n : ℕ) :
    indices (n + 1) = insert (Nat.succPNat n) (indices n) := by
  ext i
  simp [indices, Finset.range_add_one, eq_comm]

lemma le_maxIndex_of_mem_support (f : DigitSeries) {n : ℕ+} (hn : f n ≠ 0) :
    (n : ℕ) ≤ f.maxIndex := by
  classical
  refine Finset.le_sup ?_
  simpa using hn

lemma cast_mul_zpow_neg_succ (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    (p : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ)) = (p : ℚ) ^ (-(n : ℤ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by
    exact_mod_cast (show p ≠ 0 from (Fact.out : Nat.Prime p).ne_zero)
  rw [zpow_neg, zpow_neg]
  norm_num
  field_simp [hp0]
  have hpow : (p : ℚ) ^ (↑n + 1) = (p : ℚ) * (p : ℚ) ^ n := by simpa using (pow_succ' (p : ℚ) n)
  exact hpow.symm

/-- The rational value `∑ i, d i * p⁻ⁱ` of a finite digit vector: the digit value `‖d‖` of
Definition 2.3 (3). -/
noncomputable def norm (p : ℕ) [Fact (Nat.Prime p)] : DigitSeries →+ ℚ :=
  Finsupp.liftAddHom fun i ↦
    { toFun := fun n ↦ (n : ℚ) * (p : ℚ) ^ (-(i : ℤ))
      map_zero' := by simp
      map_add' := fun a b ↦ by simp [add_mul] }

/-- The truncated base-`p` value of `f` at length `n`, rescaled by `p^{-n}`, equals the partial
norm `∑_{i ∈ indices n} (f i) · p^{-i}` over the first `n` positions. -/
lemma value_eq_sum_indices (f : DigitSeries) (p : ℕ) [Fact (Nat.Prime p)] :
    ∀ n,
      ((f.value p n : ℚ) * (p : ℚ) ^ (-(n : ℤ))) =
        Finset.sum (indices n) fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ))
  | 0 => by simp [DigitSeries.value, DigitSeries.coeffs, DigitSeries.indices]
  | n + 1 => by
      rw [DigitSeries.value, DigitSeries.coeffs, Nat.ofDigits_cons, DigitSeries.indices_succ,
        Finset.sum_insert]
      · calc
          (((f (Nat.succPNat n) + p * f.value p n : ℕ) : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ)))
              = (f (Nat.succPNat n) : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))
                + ((f.value p n : ℚ) * (p : ℚ)) * (p : ℚ) ^ (-(n + 1 : ℤ)) := by norm_num; ring
          _ = (f (Nat.succPNat n) : ℚ) * (p : ℚ) ^ (-(n + 1 : ℤ))
                + (f.value p n : ℚ) * (p : ℚ) ^ (-(n : ℤ)) := by
                  rw [mul_assoc, DigitSeries.cast_mul_zpow_neg_succ]
          _ = (f (Nat.succPNat n) : ℚ) * (p : ℚ) ^ (-(Nat.succPNat n : ℤ))
                + Finset.sum (indices n) (fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) := by
                  rw [value_eq_sum_indices (f := f) (p := p) n]
                  simp
      · simp

/-- Once `n` exceeds the largest nonzero position of `f`, the norm is the finite sum
`∑_{i ∈ indices n} (f i) · p^{-i}` — the tail beyond `n` contributes nothing. -/
lemma norm_eq_sum_indices (f : DigitSeries) (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}
    (hn : f.maxIndex < n) :
    f.norm p = Finset.sum (indices n) fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) := by
  classical
  change ∑ i ∈ f.support, (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ)) =
      Finset.sum (indices n) (fun i => (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ)))
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    have hne : f i ≠ 0 := by simpa using hi
    have hi_lt : (i.natPred : ℕ) < n := by
      have hi_lt' : (i : ℕ) < n := lt_of_le_of_lt (f.le_maxIndex_of_mem_support hne) hn
      have hi_succ : i.natPred + 1 < n := by simpa [PNat.natPred_add_one] using hi_lt'
      exact Nat.lt_trans (Nat.lt_succ_self _) hi_succ
    simpa [PNat.succPNat_natPred] using (DigitSeries.mem_indices n i.natPred).2 hi_lt
  · intro i hi his
    have hzero : f i = 0 := by
      by_contra hne
      exact his (by simpa using hne)
    simp [hzero]

/-- Once `n` exceeds the largest nonzero position of `f`, its norm equals the truncated value
`(f.value p n) · p^{-n}`; i.e. `f` is determined by its first `n` digits. -/
lemma norm_eq_value (f : DigitSeries) (p : ℕ) [Fact (Nat.Prime p)] {n : ℕ}
    (hn : f.maxIndex < n) :
    f.norm p = ((f.value p n : ℚ) * (p : ℚ) ^ (-(n : ℤ))) := by
  rw [f.norm_eq_sum_indices p hn, ← f.value_eq_sum_indices p n]

lemma eq_on_of_coeffs_eq : ∀ {f g : ℕ+ → ℕ} {n : ℕ}, coeffs f n = coeffs g n →
    ∀ i : ℕ+, (i : ℕ) ≤ n → f i = g i
  | f, g, 0, h, i, hi => by
      exfalso
      exact (Nat.not_lt_of_ge hi) i.2
  | f, g, n + 1, h, i, hi => by
      have h' : f (Nat.succPNat n) = g (Nat.succPNat n) ∧ coeffs f n = coeffs g n := by
        simpa [coeffs] using h
      rcases Nat.lt_or_eq_of_le hi with hi_lt | hi_eq
      · exact eq_on_of_coeffs_eq h'.2 i (Nat.le_of_lt_succ hi_lt)
      · have : i = Nat.succPNat n := Subtype.ext hi_eq
        simpa [this] using h'.1

/-- The predicate `ℙ` of proper digit vectors: a digit series is a **proper** base-`p` expansion,
i.e. every digit is `< p`. These are the digit vectors of Definition 2.3 (1). -/
def IsP (f : DigitSeries) (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∀ n, f n < p

/-- The first `n` digit values of a proper (`IsP p`) digit series are all `< p`. -/
lemma coeffs_lt {p : ℕ} [Fact (Nat.Prime p)] (f : DigitSeries) (hf : f.IsP p) (n : ℕ) :
    ∀ x ∈ DigitSeries.coeffs f n, x < p := by
  intro x hx
  induction n generalizing x with
  | zero => cases hx
  | succ n ih =>
      simp only [DigitSeries.coeffs, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simpa using hf (Nat.succPNat n)
      · exact ih _ hx

/-- The truncated base-`p` value of a proper digit series at length `n` is `< p^n` (it is an
`n`-digit number in base `p`). -/
lemma value_lt_pow {p : ℕ} [Fact (Nat.Prime p)] (f : DigitSeries) (hf : f.IsP p) (n : ℕ) :
    f.value p n < p ^ n := by
  unfold DigitSeries.value
  simpa [DigitSeries.coeffs_length] using
    Nat.ofDigits_lt_base_pow_length ((Fact.out : Nat.Prime p).one_lt) (f.coeffs_lt hf n)

/-- If two proper (`IsP p`) digit series have norms differing by an integer, they are equal. A
proper base-`p` expansion of a number in `[0, 1)` is unique, so no integer shift can relate two
distinct ones. This is the uniqueness assertion of Lemma 2.4. -/
lemma eq_of_norm_sub_isInt {p : ℕ} [Fact (Nat.Prime p)] {f g : DigitSeries}
    (hf : f.IsP p) (hg : g.IsP p) (hfg : (f.norm p - g.norm p).isInt) : f = g := by
  let n := max f.maxIndex g.maxIndex + 1
  have hfN : f.maxIndex < n := by simp [n]
  have hgN : g.maxIndex < n := by simp [n]
  let q : ℚ := f.norm p - g.norm p
  have hq : q.isInt := by simpa [q] using hfg
  have hq_expr : q = (((f.value p n : ℚ) - g.value p n) * (p : ℚ) ^ (-(n : ℤ))) := by
    simp [q, f.norm_eq_value p hfN, g.norm_eq_value p hgN]
    ring
  have hq_lt : q < 1 := by
    rw [hq_expr]
    have hvf_lt : (f.value p n : ℚ) < (p : ℚ) ^ n := by
      exact_mod_cast f.value_lt_pow hf n
    have hp_pow_pos : 0 < (p : ℚ) ^ n := pow_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _
    have hdiff_lt : (f.value p n : ℚ) - g.value p n < (p : ℚ) ^ n := by nlinarith
    rw [show (p : ℚ) ^ (-(n : ℤ)) = ((p : ℚ) ^ n)⁻¹ by rw [zpow_neg, zpow_natCast]]
    simpa [ne_of_gt hp_pow_pos] using mul_lt_mul_of_pos_right hdiff_lt (inv_pos.mpr hp_pow_pos)
  have hq_gt : (-1 : ℚ) < q := by
    rw [hq_expr]
    have hvg_lt : (g.value p n : ℚ) < (p : ℚ) ^ n := by
      exact_mod_cast g.value_lt_pow hg n
    have hp_pow_pos : 0 < (p : ℚ) ^ n := pow_pos (by exact_mod_cast (Fact.out : Nat.Prime p).pos) _
    have hdiff_gt :
        -((p : ℚ) ^ n) < (f.value p n : ℚ) - g.value p n := by
      nlinarith
    rw [show (p : ℚ) ^ (-(n : ℤ)) = ((p : ℚ) ^ n)⁻¹ by rw [zpow_neg, zpow_natCast]]
    simpa [ne_of_gt hp_pow_pos] using mul_lt_mul_of_pos_right hdiff_gt (inv_pos.mpr hp_pow_pos)
  rw [Rat.eq_num_of_isInt hq] at hq_gt hq_lt
  have hnum_zero : q.num = 0 := by
    have : (-1 : ℤ) < q.num ∧ q.num < 1 := by exact_mod_cast And.intro hq_gt hq_lt
    omega
  have hq_zero : q = 0 := by
    rw [Rat.eq_num_of_isInt hq, hnum_zero]
    simp
  have hpz : (p : ℚ) ^ (-(n : ℤ)) ≠ 0 := by
    exact zpow_ne_zero _ (by exact_mod_cast (show p ≠ 0 from (Fact.out : Nat.Prime p).ne_zero))
  have hval_eq : (f.value p n : ℚ) = g.value p n := by
    apply sub_eq_zero.mp
    apply mul_right_cancel₀ hpz
    simpa [hq_expr] using hq_zero
  have hcoeffs :
      DigitSeries.coeffs f n = DigitSeries.coeffs g n := by
    apply Nat.ofDigits_inj_of_len_eq ((Fact.out : Nat.Prime p).one_lt)
    · simp [DigitSeries.coeffs_length]
    · exact f.coeffs_lt hf n
    · exact g.coeffs_lt hg n
    · exact_mod_cast hval_eq
  ext i
  by_cases hi : (i : ℕ) ≤ n
  · exact DigitSeries.eq_on_of_coeffs_eq hcoeffs i hi
  · have hfi : f i = 0 := by
      by_contra hne
      exact hi (le_trans (f.le_maxIndex_of_mem_support hne) (Nat.le_of_lt hfN))
    have hgi : g i = 0 := by
      by_contra hne
      exact hi (le_trans (g.le_maxIndex_of_mem_support hne) (Nat.le_of_lt hgN))
    simpa using hfi.trans hgi.symm

end DigitSeries

/-- For `f.IsP p`, the norm lies in `[0, 1)`. -/
lemma DigitSeries.norm_mem_Ico (p : ℕ) [Fact (Nat.Prime p)]
    (f : DigitSeries) (hf : f.IsP p) :
    f.norm p ∈ Set.Ico (0 : ℚ) 1 := by
  let n := f.maxIndex + 1
  have hfN : f.maxIndex < n := by simp [n]
  rw [f.norm_eq_value p hfN]
  have hp_pos : 0 < (p : ℚ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hp_pow_pos : 0 < (p : ℚ)^n := pow_pos hp_pos _
  have hval_lt : (f.value p n : ℚ) < (p : ℚ)^n := by
    exact_mod_cast f.value_lt_pow hf n
  have hpow_eq : (p : ℚ)^(-(n : ℤ)) = ((p : ℚ)^n)⁻¹ := by
    rw [zpow_neg, zpow_natCast]
  refine ⟨?_, ?_⟩
  · -- 0 ≤ ↑(f.value p n) * (p : ℚ)^(-(n : ℤ))
    apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · rw [hpow_eq]
      exact inv_nonneg.mpr (le_of_lt hp_pow_pos)
  · -- ↑(f.value p n) * (p : ℚ)^(-(n : ℤ)) < 1
    rw [hpow_eq, ← div_eq_mul_inv, div_lt_one hp_pow_pos]
    exact hval_lt

/-- Two proper digit vectors with the same rational value are equal. -/
lemma DigitSeries.IsP_norm_injective {p : ℕ} [Fact (Nat.Prime p)] {f g : DigitSeries}
    (hf : f.IsP p) (hg : g.IsP p) (h : f.norm p = g.norm p) : f = g := by
  apply DigitSeries.eq_of_norm_sub_isInt hf hg
  rw [h, sub_self]
  simp [Rat.isInt]

end PAdicOrderType
