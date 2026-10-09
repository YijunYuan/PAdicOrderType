/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Digits.LongGaps
import PAdicOrderType.Digits.Markers
import PAdicOrderType.Digits.BlockInterleavings
import PAdicOrderType.Digits.WordGapGeometry
import Mathlib.Data.PNat.Interval

/-!
# Separated placements and tail clusters

This file proves Lemmas 3.8 and 3.9. Let `V = Supp x` be a bounded QTR set with data
`(a, b, c, M, N)` contained in the slices `S_{a,b,c,m}` (`m₁ ≤ m ≤ m₂`), with
`typeLT V < ω ^ (r + 1)` (`r ≥ 1`), and let `U = V ∩ (-∞, R₀]` for an integer `R₀` with
`ω ^ r ≤ typeLT U`. Fix `n ≥ 1`. The lemma produces a threshold `h₀` and, for
every `h ≥ h₀`, marker data `μ` (core blocks `B j`, detection intervals
`I j = [min B j, max B j + H]` with `n ≤ p ^ H`, protective intervals `Bt j`,
`Bt j` pairwise disjoint) such that

1. the `h`-tail of the digit vector of every element of `V` (these tails are
   the canonical representatives of `-a p^h V` modulo `ℤ`) is clustered with at
   most `r` clusters (`MarkerData.IsClustered`), which is Lemma 3.8;
2. there are nonzero valid patterns `α₁, …, α_r` on the common block shape
   such that for all `j₁ < ⋯ < j_r` the placement
   `ρ_{B j₁, α₁} + ⋯ + ρ_{B j_r, α_r}` is the `h`-tail of the digit vector of
   an element of `U`, which is Lemma 3.9.

The long-gap criterion gives at most `r` long gaps at every point and a point
of `U` with exactly `r`. Gaps shorter than `M` bound each surviving cluster's
diameter by `c M`. Independently inserting multiples of `N` into the long gaps
of the distinguished point places its fixed digit patterns on arbitrarily
separated blocks. The resulting marker data combine a uniform cluster bound with
a family of placements that attains that bound.
-/

namespace PAdicOrderType

open DigitSeries Ordinal

/-! ### Digit positions: step and growth lemmas -/

/-- Digit positions step by one plus the next gap (`getI = 0` beyond the list). -/
lemma gapPos_succ (g : List ℕ) (j : ℕ) :
    gapPos g (j + 1) = gapPos g j + 1 + g.getI (j + 1) := by
  unfold gapPos
  rcases lt_or_ge (j + 1) g.length with h | h
  · rw [sum_take_succ_getI g (j + 1) h]
    omega
  · rw [List.take_of_length_le h, List.take_of_length_le (by omega), List.getI_eq_default _ h]
    simp only [Nat.default_eq_zero]
    omega

/-- The first digit position is the first gap. -/
lemma gapPos_zero (g : List ℕ) : gapPos g 0 = g.getI 0 := by
  cases g with
  | nil => rfl
  | cons a l => simp [gapPos, List.getI]

/-- Over a stretch of gaps `≤ L`, digit positions grow by at most `L + 1` per letter. -/
lemma gapPos_le_gapPos_add (g : List ℕ) {i j : ℕ} (hij : i ≤ j) {L : ℕ}
    (hL : ∀ l, i < l → l ≤ j → g.getI l ≤ L) :
    gapPos g j ≤ gapPos g i + (j - i) * (L + 1) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    rw [gapPos_succ]
    have h1 := hL (j + 1) (by omega) le_rfl
    have h2 := ih fun l hl hlj => hL l hl (by omega)
    have h3 : (j + 1 - i) * (L + 1) = (j - i) * (L + 1) + (L + 1) := by
      rw [show j + 1 - i = (j - i) + 1 by omega, Nat.add_mul, one_mul]
    omega

/-- If all gaps up to index `j` are `≤ L`, the `j`-th digit position is `≤ j + (j + 1) L`. -/
lemma gapPos_le_of_forall_le (g : List ℕ) (j : ℕ) {L : ℕ}
    (hL : ∀ l, l ≤ j → g.getI l ≤ L) :
    gapPos g j ≤ j + (j + 1) * L := by
  have h := gapPos_le_gapPos_add g (Nat.zero_le j) fun l _ hlj => hL l hlj
  rw [gapPos_zero, Nat.sub_zero] at h
  have h0 := hL 0 (Nat.zero_le _)
  have h3 : j * (L + 1) = j * L + j := by ring
  have h4 : (j + 1) * L = j * L + L := by ring
  omega

/-! ### Digit positions of pumped gap vectors -/

/-- The pumped gap vector at any index (`getI = 0` beyond the list on both sides). -/
lemma rayGap_getI_of_forall_lt_length (v : List ℕ) (N : ℕ) {r : ℕ} {idx : Fin r → ℕ}
    (hbound : ∀ h, idx h < v.length) (n : Fin r → ℕ) (j : ℕ) :
    (rayGap v N idx n).getI j = v.getI j + N * ∑ h, if idx h = j then n h else 0 := by
  rcases lt_or_ge j v.length with hj | hj
  · exact rayGap_getI v N idx n hj
  · rw [List.getI_eq_default _ (by rw [rayGap_length]; exact hj), List.getI_eq_default _ hj,
      Finset.sum_eq_zero fun h _ => if_neg (by have := hbound h; omega)]
    simp

/-- **Digit positions of a pumped gap vector**: the `j`-th letter is translated by
`N` times the sum of the parameters at the active indices `≤ j`. -/
lemma gapPos_rayGap (v : List ℕ) (N : ℕ) {r : ℕ} {idx : Fin r → ℕ}
    (hbound : ∀ h, idx h < v.length) (n : Fin r → ℕ) (j : ℕ) :
    gapPos (rayGap v N idx n) j = gapPos v j + N * ∑ h, if idx h ≤ j then n h else 0 := by
  induction j with
  | zero =>
    rw [gapPos_zero, gapPos_zero, rayGap_getI_of_forall_lt_length v N hbound n 0]
    congr 2
    exact Finset.sum_congr rfl fun h _ => by simp
  | succ j ih =>
    rw [gapPos_succ, gapPos_succ, ih, rayGap_getI_of_forall_lt_length v N hbound n (j + 1)]
    have hsplit : (∑ h, if idx h ≤ j + 1 then n h else 0)
        = (∑ h, if idx h ≤ j then n h else 0) + ∑ h, if idx h = j + 1 then n h else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases h1 : idx h ≤ j
      · rw [if_pos (by omega), if_pos h1, if_neg (by omega), add_zero]
      · by_cases h2 : idx h = j + 1
        · rw [if_pos (by omega), if_neg h1, if_pos h2, zero_add]
        · rw [if_neg (by omega), if_neg h1, if_neg h2, add_zero]
    rw [hsplit, Nat.mul_add]
    omega

/-! ### Telescoping parameters -/

/-- Telescoping: the increments of a monotone sequence `S` sum back to `S`. -/
lemma sum_range_increments (S : ℕ → ℕ) (hS : Monotone S) (k : ℕ) :
    ∑ l ∈ Finset.range (k + 1), (if l = 0 then S 0 else S l - S (l - 1)) = S k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    have := hS (Nat.le_add_right k 1)
    omega

/-! ### Placements along intervals -/

/-- The rank of an element of a `ℕ+`-interval is its offset from the left endpoint. -/
lemma rankIn_Icc {a b q : ℕ+} (hq : q ∈ Finset.Icc a b) :
    rankIn (Finset.Icc a b) q = (q : ℕ) - a := by
  unfold rankIn
  have hfilter : (Finset.Icc a b).filter (· < q) = Finset.Ico a q := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    rw [Finset.mem_Icc] at hq
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, h3.le.trans hq.2⟩, h3⟩
  rw [hfilter, PNat.card_Ico]

/-- A placement along a `ℕ+`-interval reads the letter at the offset from the left
endpoint. -/
lemma placeAt_Icc_apply_of_mem {s : ℕ} {a b : ℕ+} (hs : (Finset.Icc a b).card = s)
    (c : Fin s → ℕ) {q : ℕ+} (hq : q ∈ Finset.Icc a b) :
    placeAt (Finset.Icc a b) c q
      = c ⟨(q : ℕ) - a, by rw [← rankIn_Icc hq, ← hs]; exact rankIn_lt_card hq⟩ := by
  rw [placeAt_apply_of_mem hq (by rw [← hs]; exact rankIn_lt_card hq)]
  congr 1
  exact Fin.ext (rankIn_Icc hq)

/-! ### Intervals in `ℕ+` via `Nat.succPNat` -/

/-- Membership in an interval of `ℕ+` with endpoints `a + 1`, `b + 1`, in terms of
`natPred`. -/
lemma mem_Icc_succPNat {a b : ℕ} {q : ℕ+} :
    q ∈ Finset.Icc (Nat.succPNat a) (Nat.succPNat b) ↔ a ≤ q.natPred ∧ q.natPred ≤ b := by
  rw [Finset.mem_Icc, ← PNat.coe_le_coe, ← PNat.coe_le_coe, Nat.succPNat_coe, Nat.succPNat_coe]
  have := PNat.natPred_add_one q
  omega

/-- The cardinality of an interval of `ℕ+` with endpoints `a + 1 ≤ b + 1`. -/
lemma card_Icc_succPNat {a b : ℕ} (hab : a ≤ b) :
    (Finset.Icc (Nat.succPNat a) (Nat.succPNat b)).card = b - a + 1 := by
  rw [PNat.card_Icc, Nat.succPNat_coe, Nat.succPNat_coe]
  omega

/-! ### Slice index versus an integer bound -/

/-- A point of the `m`-th slice is `≤ R₀` (an integer) iff `m ≤ a R₀`. -/
lemma qval_le_intCast_iff {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {m : ℤ} {d : ℕ →₀ ℕ}
    (hd : ∀ i, d i < p) (R₀ : ℤ) :
    qval p a m d ≤ (R₀ : ℚ) ↔ m ≤ ((a : ℕ) : ℤ) * R₀ := by
  obtain ⟨hv0, hv1⟩ := digitVal_mem_Ico hd
  set v := d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))
  have ha : (0 : ℚ) < ((a : ℕ) : ℚ) := by exact_mod_cast a.pos
  have hcoe : (a : ℚ) = ((a : ℕ) : ℚ) := rfl
  unfold qval
  rw [hcoe, one_div, inv_mul_le_iff₀ ha]
  constructor
  · intro h
    by_contra hc
    have hc' : ((a : ℕ) : ℤ) * R₀ + 1 ≤ m := by omega
    have : (((a : ℕ) : ℤ) * R₀ + 1 : ℚ) ≤ m := by exact_mod_cast hc'
    push_cast at this
    linarith
  · intro h
    have : (m : ℚ) ≤ ((a : ℕ) : ℚ) * R₀ := by exact_mod_cast h
    linarith

/-! ### Initial segments of a strictly monotone enumeration -/

/-- For a strictly monotone `idx : Fin r → ℕ`, the indices `h` with `idx h ≤ l` form the
initial segment of length `#{h | idx h ≤ l}`. -/
lemma idx_le_iff_lt_card {r : ℕ} {idx : Fin r → ℕ} (hidx : StrictMono idx) (l : ℕ)
    (h : Fin r) :
    idx h ≤ l ↔ (h : ℕ) < (Finset.univ.filter fun h' => idx h' ≤ l).card := by
  constructor
  · intro hl
    have hsub : Finset.Iic h ⊆ Finset.univ.filter fun h' => idx h' ≤ l := by
      intro h' hh'
      rw [Finset.mem_Iic] at hh'
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (hidx.monotone hh').trans hl⟩
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro hc
    by_contra hl
    rw [not_le] at hl
    have hsub : (Finset.univ.filter fun h' => idx h' ≤ l) ⊆ Finset.Iio h := by
      intro h' hh'
      rw [Finset.mem_filter] at hh'
      rw [Finset.mem_Iio]
      by_contra hge
      rw [not_lt] at hge
      have := hidx.monotone hge
      omega
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- The count `#{h | idx h ≤ l}` is at most `r`. -/
lemma card_filter_idx_le {r : ℕ} (idx : Fin r → ℕ) (l : ℕ) :
    (Finset.univ.filter fun h' => idx h' ≤ l).card ≤ r :=
  (Finset.card_filter_le _ _).trans (by simp)

/-- A sum over the active indices `≤ l` is a sum over the initial segment
`range #{h | idx h ≤ l}`. -/
lemma sum_ite_idx_le_eq_sum_range {r : ℕ} {idx : Fin r → ℕ} (hidx : StrictMono idx)
    (f : ℕ → ℕ) (l : ℕ) :
    (∑ h : Fin r, if idx h ≤ l then f h else 0)
      = ∑ t ∈ Finset.range (Finset.univ.filter fun h' => idx h' ≤ l).card, f t := by
  set c := (Finset.univ.filter fun h' => idx h' ≤ l).card with hc
  have hcr : c ≤ r := card_filter_idx_le idx l
  have h1 : (∑ h : Fin r, if idx h ≤ l then f h else 0)
      = ∑ h : Fin r, if (h : ℕ) < c then f h else 0 :=
    Finset.sum_congr rfl fun h _ => by simp only [idx_le_iff_lt_card hidx l h, hc]
  rw [h1, Fin.sum_univ_eq_sum_range (fun t => if t < c then f t else 0) r,
    ← Finset.sum_subset (Finset.range_subset_range.mpr hcr)]
  · exact Finset.sum_congr rfl fun t ht => if_pos (Finset.mem_range.mp ht)
  · intro t ht ht'
    rw [Finset.mem_range] at ht'
    exact if_neg ht'

/-- The prefix sums of the increment sequence of `t ↦ C + Q * jj t`. -/
lemma sum_range_increments_eq (C Q : ℕ) {jj : ℕ → ℕ} (hjj : Monotone jj) (c : ℕ) :
    (∑ t ∈ Finset.range c,
        if t = 0 then C + Q * jj 0 else Q * jj t - Q * jj (t - 1))
      = if c = 0 then 0 else C + Q * jj (c - 1) := by
  rcases c with _ | c
  · simp
  · rw [if_neg (Nat.succ_ne_zero c), Nat.add_sub_cancel]
    have hS : Monotone fun t => C + Q * jj t := fun t t' htt' =>
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (hjj htt')) _
    rw [← sum_range_increments (fun t => C + Q * jj t) hS c]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : t = 0
    · rw [if_pos ht, if_pos ht]
    · rw [if_neg ht, if_neg ht]
      have := hjj (Nat.sub_le t 1)
      have h2 : Q * jj (t - 1) ≤ Q * jj t := Nat.mul_le_mul_left _ this
      omega

/-! ### Interval marker data -/

/-- **Interval marker data**: blocks `B k = [lo + Δ k + 1, lo + Δ k + S]` (as
`ℕ+`-intervals), detection intervals `I k = [min B k, max B k + H]`, and protective
intervals `Bt k = [min B k - W, max B k + H + W]`; for `W < lo` and
`Δ > S + H + 2 W` the protective intervals are pairwise disjoint. These are the blocks `B_j`
of Lemma 3.9 and the enlarged blocks `B_j^+` and `B_j^{++}` of the proof of Lemma 3.11, with
the separation condition corresponding to inequality (3.8). -/
def intervalMarker (lo S H W Δ : ℕ) (hS : 0 < S) (hlo : W < lo)
    (hΔ : S + H + 2 * W < Δ) : MarkerData where
  s := S
  b k := Finset.Icc (Nat.succPNat (lo + Δ * k)) (Nat.succPNat (lo + Δ * k + S - 1))
  i k := Finset.Icc (Nat.succPNat (lo + Δ * k)) (Nat.succPNat (lo + Δ * k + S - 1 + H))
  bt k := Finset.Icc (Nat.succPNat (lo + Δ * k - W))
    (Nat.succPNat (lo + Δ * k + S - 1 + H + W))
  h := H
  card_b k := by
    rw [card_Icc_succPNat (by omega)]
    omega
  b_subset_i k := Finset.Icc_subset_Icc le_rfl (by rw [Nat.succPNat_le_succPNat]; omega)
  i_subset_bt k := Finset.Icc_subset_Icc (by rw [Nat.succPNat_le_succPNat]; omega)
    (by rw [Nat.succPNat_le_succPNat]; omega)
  mem_i_iff k x := by
    simp only [mem_Icc_succPNat]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨Nat.succPNat (lo + Δ * k), ⟨le_rfl, by rw [Nat.natPred_succPNat]; omega⟩, ?_⟩,
        ⟨Nat.succPNat (lo + Δ * k + S - 1), ⟨by rw [Nat.natPred_succPNat]; omega, le_rfl⟩, ?_⟩⟩
      · rw [← PNat.coe_le_coe, Nat.succPNat_coe]
        have := PNat.natPred_add_one x
        omega
      · rw [Nat.succPNat_coe]
        have := PNat.natPred_add_one x
        omega
    · rintro ⟨⟨y, ⟨hy1, hy2⟩, hyx⟩, ⟨y', ⟨hy'1, hy'2⟩, hxy'⟩⟩
      rw [← PNat.coe_le_coe] at hyx
      have := PNat.natPred_add_one x
      have := PNat.natPred_add_one y
      have := PNat.natPred_add_one y'
      constructor <;> omega
  bt_disjoint i j hij := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    rw [mem_Icc_succPNat] at hq hq'
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have : Δ * i + Δ ≤ Δ * j := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ hlt
      omega
    · have : Δ * j + Δ ≤ Δ * i := by
        rw [← Nat.mul_succ]
        exact Nat.mul_le_mul_left _ hlt
      omega

/-- The protective intervals of `intervalMarker` contain the `W`-neighbourhoods of the
detection intervals. -/
lemma intervalMarker_nbhd (lo S H W Δ : ℕ) (hS : 0 < S) (hlo : W < lo)
    (hΔ : S + H + 2 * W < Δ) (k : ℕ) (x x' : ℕ+)
    (hx : x ∈ (intervalMarker lo S H W Δ hS hlo hΔ).i k) (h1 : (x : ℕ) ≤ x' + W)
    (h2 : (x' : ℕ) ≤ x + W) : x' ∈ (intervalMarker lo S H W Δ hS hlo hΔ).bt k := by
  simp only [intervalMarker, mem_Icc_succPNat] at hx ⊢
  have := PNat.natPred_add_one x
  have := PNat.natPred_add_one x'
  omega

/-- Uniqueness of the block index and the offset of a position `lo + Δ k + u`
(`u < S ≤ Δ`). -/
lemma eq_of_block_pos_eq {lo Δ S k k' u u' : ℕ} (hS : S ≤ Δ) (hu : u < S) (hu' : u' < S)
    (h : lo + Δ * k + u = lo + Δ * k' + u') : k = k' ∧ u = u' := by
  rcases lt_trichotomy k k' with hlt | rfl | hlt
  · have : Δ * (k + 1) ≤ Δ * k' := Nat.mul_le_mul_left _ hlt
    rw [Nat.mul_succ] at this
    omega
  · exact ⟨rfl, by omega⟩
  · have : Δ * (k' + 1) ≤ Δ * k := Nat.mul_le_mul_left _ hlt
    rw [Nat.mul_succ] at this
    omega

/-! ### Active counts and ray parameters -/

/-- The number of active indices `≤ j` (for a strictly monotone enumeration `idx`, the
letters with `activeCount idx j = i + 1` form the `i`-th chunk). -/
def activeCount {r : ℕ} (idx : Fin r → ℕ) (j : ℕ) : ℕ :=
  (Finset.univ.filter fun h' => idx h' ≤ j).card

lemma activeCount_le {r : ℕ} (idx : Fin r → ℕ) (j : ℕ) : activeCount idx j ≤ r :=
  card_filter_idx_le idx j

/-- The active count at an active index. -/
lemma activeCount_idx {r : ℕ} {idx : Fin r → ℕ} (hidx : StrictMono idx) (h : Fin r) :
    activeCount idx (idx h) = h + 1 := by
  unfold activeCount
  have : (Finset.univ.filter fun h' => idx h' ≤ idx h) = Finset.Iic h := by
    ext h'
    rw [Finset.mem_filter, Finset.mem_Iic, hidx.le_iff_le]
    simp
  rw [this, Fin.card_Iic]

/-- The active count in position coordinates equals the active count in letter
coordinates. -/
lemma activeCount_gapPos {r : ℕ} (v : List ℕ) (idx : Fin r → ℕ) (j : ℕ) :
    activeCount (fun h => gapPos v (idx h)) (gapPos v j) = activeCount idx j := by
  unfold activeCount
  congr 1
  ext h'
  simp only [Finset.mem_filter, (strictMono_gapPos v).le_iff_le]

/-- A monotone function from a nonempty `Fin r` extends to a monotone function on `ℕ`. -/
lemma exists_monotone_extension {r : ℕ} (hr : 0 < r) {jj : Fin r → ℕ} (hjj : Monotone jj) :
    ∃ jj' : ℕ → ℕ, Monotone jj' ∧ ∀ h : Fin r, jj' h = jj h := by
  refine ⟨fun t => jj ⟨min t (r - 1), by omega⟩, fun t t' htt' => hjj ?_, fun h => ?_⟩
  · rw [Fin.mk_le_mk]
    exact min_le_min_right _ htt'
  · exact congrArg jj (Fin.ext (min_eq_left (Nat.le_sub_one_of_lt h.2)))

/-- Increment parameters for prescribed block indices: the first is `C + Q * jj' 0`,
and each subsequent one is the difference of successive `Q * jj'` values. When `jj'` is
monotone, the prefix sum through index `t` is `C + Q * jj' t`. -/
def rayParam (C Q : ℕ) (jj' : ℕ → ℕ) (r : ℕ) : Fin r → ℕ := fun h =>
  if (h : ℕ) = 0 then C + Q * jj' 0 else Q * jj' h - Q * jj' (h - 1)

/-- **Digit positions of the marker ray element**: the `j`-th letter of the ray element
with parameters `rayParam C Q jj'` is translated by `N (C + Q jj' (i))`, `i + 1` being
the number of active indices `≤ j` (and not at all if there is none). -/
lemma gapPos_rayGap_rayParam {v : List ℕ} {N r : ℕ} {idx : Fin r → ℕ}
    (hidx : StrictMono idx) (hbound : ∀ h, idx h < v.length) {jj' : ℕ → ℕ}
    (hjj' : Monotone jj') (C Q j : ℕ) :
    gapPos (rayGap v N idx (rayParam C Q jj' r)) j
      = gapPos v j + N * (if activeCount idx j = 0 then 0
          else C + Q * jj' (activeCount idx j - 1)) := by
  unfold rayParam
  rw [gapPos_rayGap v N hbound, sum_ite_idx_le_eq_sum_range hidx
    (fun t => if t = 0 then C + Q * jj' 0 else Q * jj' t - Q * jj' (t - 1)) j,
    sum_range_increments_eq C Q hjj']
  rfl

/-! ### The tail of the marker ray element -/

/-- **The tail of the marker ray element**: with
`n₀ + ⋯ + n_t = C + Q jj t`, `lo + h = N C`, `S = gapPos v |w|` (beyond every base
position), `S ≤ h` and `S ≤ N Q`, the `h`-tail of the ray element with parameters
`rayParam C Q jj' r` is the sum of the placements of the chunk patterns
`α t = (chunk t of w along [0, S))` on the blocks `[lo + N Q jj t + 1, lo + N Q jj t + S]`.
This locates the digits of the moved point in the proof of Lemma 3.9. -/
lemma tailh_rayParam_eq {w v : List ℕ} (hw0 : ∀ y ∈ w, y ≠ 0) {r : ℕ} {idx : Fin r → ℕ}
    (hidx : StrictMono idx) (hbound : ∀ h, idx h < v.length)
    {jj : Fin r → ℕ} (hjj : StrictMono jj) {jj' : ℕ → ℕ} (hjj' : Monotone jj')
    (hext : ∀ h : Fin r, jj' h = jj h)
    {N C Q lo S h : ℕ} (hlo : lo + h = N * C) (hS : S = gapPos v w.length) (hSh : S ≤ h)
    (hS0 : 0 < S) (hSΔ : S ≤ N * Q) :
    tailh (ofFinsupp (ofWordGap w (rayGap v N idx (rayParam C Q jj' r)))) h
      = (∑ i, placeAt (Finset.Icc (Nat.succPNat (lo + N * Q * jj i))
          (Nat.succPNat (lo + N * Q * jj i + S - 1)))
          (fun u : Fin S => if activeCount (fun h => gapPos v (idx h)) u = (i : ℕ) + 1
            then ofWordGap w v u else 0)) := by
  classical
  set Δ := N * Q with hΔ
  set g' := rayGap v N idx (rayParam C Q jj' r) with hg'
  set B : ℕ → Finset ℕ+ := fun k =>
    Finset.Icc (Nat.succPNat (lo + Δ * k)) (Nat.succPNat (lo + Δ * k + S - 1)) with hB
  set α : Fin r → Fin S → ℕ := fun i u =>
    if activeCount (fun h => gapPos v (idx h)) u = (i : ℕ) + 1 then ofWordGap w v u else 0
    with hα
  have hcardB : ∀ k, (B k).card = S := fun k => by
    rw [hB, card_Icc_succPNat (by omega)]
    omega
  have hposlt : ∀ j, j < w.length → gapPos v j < S := fun j hj => hS ▸ strictMono_gapPos v hj
  have hac_le : ∀ j, activeCount idx j ≤ r := fun j => activeCount_le idx j
  -- positions of the letters of the ray element
  have hpos0 : ∀ j, activeCount idx j = 0 → gapPos g' j = gapPos v j := by
    intro j h0
    rw [hg', gapPos_rayGap_rayParam hidx hbound hjj', if_pos h0, Nat.mul_zero, Nat.add_zero]
  have hpos : ∀ j (t : Fin r), activeCount idx j = t + 1 →
      gapPos g' j = lo + Δ * jj t + gapPos v j + h := by
    intro j t ht
    rw [hg', gapPos_rayGap_rayParam hidx hbound hjj', if_neg (by omega), ht,
      Nat.add_sub_cancel, hext]
    have : N * (C + Q * jj t) = N * C + Δ * jj t := by
      rw [Nat.mul_add, hΔ, Nat.mul_assoc]
    omega
  -- a nonzero digit of the ray element comes from a letter
  have hletter : ∀ y, ofWordGap w g' y ≠ 0 → ∃ j, j < w.length ∧ gapPos g' j = y := by
    intro y hy
    have hmem := Finsupp.mem_support_iff.mpr hy
    rw [support_ofWordGap w g' hw0] at hmem
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hmem
    exact ⟨j, Finset.mem_range.mp hj, hje⟩
  -- a letter of the tail lies in a chunk, at the corresponding block position
  have hchunk : ∀ y j, j < w.length → gapPos g' j = y + h →
      ∃ t : Fin r, activeCount idx j = t + 1 ∧ y = lo + Δ * jj t + gapPos v j := by
    intro y j hj hje
    by_cases h0 : activeCount idx j = 0
    · rw [hpos0 j h0] at hje
      have := hposlt j hj
      omega
    · refine ⟨⟨activeCount idx j - 1, by have := hac_le j; omega⟩, by simp only; omega, ?_⟩
      rw [hpos j ⟨activeCount idx j - 1, by have := hac_le j; omega⟩ (by simp only; omega)] at hje
      omega
  -- the digit of the tail at a block position
  have hdigit : ∀ (t : Fin r) (u : ℕ), u < S →
      ofWordGap w g' (lo + Δ * jj t + u + h)
        = if activeCount (fun h => gapPos v (idx h)) u = t + 1 then ofWordGap w v u else 0 := by
    intro t u hu
    by_cases hex : ∃ j, j < w.length ∧ gapPos v j = u
    · obtain ⟨j, hj, rfl⟩ := hex
      rw [activeCount_gapPos, ofWordGap_apply_gapPos]
      by_cases ht : activeCount idx j = t + 1
      · rw [if_pos ht, ← hpos j t ht, ofWordGap_apply_gapPos]
      · rw [if_neg ht]
        by_contra hne
        obtain ⟨j', hj', hje⟩ := hletter _ hne
        obtain ⟨t', ht', heq⟩ := hchunk _ j' hj' hje
        obtain ⟨hk, hu'⟩ := eq_of_block_pos_eq hSΔ (hposlt j' hj') (hposlt j hj) heq.symm
        have htt : t' = t := hjj.injective hk
        have hjj'' : j' = j := (strictMono_gapPos v).injective hu'
        subst htt hjj''
        exact ht ht'
    · have hz : ofWordGap w v u = 0 :=
        ofWordGap_apply_eq_zero w v hw0 fun j hj hje => hex ⟨j, hj, hje⟩
      rw [hz, ite_self]
      by_contra hne
      obtain ⟨j', hj', hje⟩ := hletter _ hne
      obtain ⟨t', -, heq⟩ := hchunk _ j' hj' hje
      obtain ⟨-, hu'⟩ := eq_of_block_pos_eq hSΔ (hposlt j' hj') hu heq.symm
      exact hex ⟨j', hj', hu'⟩
  -- the tail vanishes outside the blocks
  have houtside : ∀ y, (∀ t : Fin r, ¬ (lo + Δ * jj t ≤ y ∧ y ≤ lo + Δ * jj t + S - 1)) →
      ofWordGap w g' (y + h) = 0 := by
    intro y hy
    by_contra hne
    obtain ⟨j', hj', hje⟩ := hletter _ hne
    obtain ⟨t', -, heq⟩ := hchunk _ j' hj' hje
    have := hposlt j' hj'
    exact hy t' ⟨by omega, by omega⟩
  -- block membership determines the block index
  have hblock : ∀ (q : ℕ+) (t t' : Fin r), q ∈ B (jj t) → q ∈ B (jj t') → t = t' := by
    intro q t t' hq hq'
    rw [hB] at hq hq'
    simp only [mem_Icc_succPNat] at hq hq'
    have := eq_of_block_pos_eq hSΔ (lo := lo) (k := jj t) (k' := jj t')
      (u := q.natPred - (lo + Δ * jj t))
      (u' := q.natPred - (lo + Δ * jj t')) (by omega) (by omega) (by omega)
    exact hjj.injective this.1
  ext q
  rw [tailh_ofFinsupp_apply, Finsupp.finsetSum_apply]
  change ofWordGap w g' (q.natPred + h) = ∑ i, placeAt (B (jj i)) (α i) q
  by_cases hq : ∃ t : Fin r, q ∈ B (jj t)
  · obtain ⟨t, hqt⟩ := hq
    rw [Finset.sum_eq_single t (fun i _ hi => placeAt_apply_of_notMem
      (fun hqi => hi (hblock q i t hqi hqt)) _) (fun ht => absurd (Finset.mem_univ t) ht)]
    rw [placeAt_Icc_apply_of_mem (hcardB (jj t)) (α t) hqt]
    have hqt' := hqt
    rw [hB, mem_Icc_succPNat] at hqt'
    have hu : (q : ℕ) - (Nat.succPNat (lo + Δ * jj t) : ℕ) = q.natPred - (lo + Δ * jj t) := by
      rw [Nat.succPNat_coe]
      have := PNat.natPred_add_one q
      omega
    have hqn : q.natPred + h = lo + Δ * jj t + (q.natPred - (lo + Δ * jj t)) + h := by omega
    rw [hqn, hdigit t _ (by omega)]
    simp only [hα, hu]
  · rw [Finset.sum_eq_zero fun i _ => placeAt_apply_of_notMem (fun hqi => hq ⟨i, hqi⟩) _]
    exact houtside q.natPred fun t ht => hq ⟨t, by rw [hB, mem_Icc_succPNat]; exact ht⟩

/-! ### Clusters of bounded diameter -/

/-- Clusters of diameter `≤ W` are compatible with marker data whose protective
intervals contain the `W`-neighbourhoods of the detection intervals. -/
lemma MarkerData.isClustered_of_diam (μ : MarkerData) {W r : ℕ}
    (hμ : ∀ j (x x' : ℕ+), x ∈ μ.i j → (x : ℕ) ≤ x' + W → (x' : ℕ) ≤ x + W → x' ∈ μ.bt j)
    {d : DigitSeries} (cl : Finset (Finset ℕ+)) (hcard : cl.card ≤ r)
    (hcov : ∀ i : ℕ+, d i ≠ 0 → ∃ C ∈ cl, i ∈ C)
    (hdiam : ∀ C ∈ cl, ∀ q ∈ C, ∀ q' ∈ C, (q : ℕ) ≤ q' + W) :
    μ.IsClustered r d := by
  refine ⟨cl, hcard, hcov, fun C hC j hne => ?_⟩
  obtain ⟨x, hx⟩ := hne
  rw [Finset.mem_inter] at hx
  intro q' hq'
  exact hμ j x q' hx.2 (hdiam C hC x hx.1 q' hq') (hdiam C hC q' hq' x hx.1)

/-- **Tails are clustered** (cf. Lemma 3.8): if
the word `w` has at most `T` letters, `W = T (L + 1)`, and `h > W`, then the `h`-tail
of `ofWordGap w g` is covered by clusters of diameter `≤ W`, one for each gap of `g`
exceeding `L`. -/
lemma isClustered_tailh_ofWordGap (μ : MarkerData) {W r L T : ℕ}
    (hμ : ∀ j (x x' : ℕ+), x ∈ μ.i j → (x : ℕ) ≤ x' + W → (x' : ℕ) ≤ x + W → x' ∈ μ.bt j)
    {w g : List ℕ} (hw0 : ∀ y ∈ w, y ≠ 0) (hT : w.length ≤ T)
    (hW : W = T * (L + 1)) {h : ℕ} (hh : W < h)
    (hr : ((Finset.range w.length).filter fun i => L < g.getI i).card ≤ r) :
    μ.IsClustered r (tailh (ofFinsupp (ofWordGap w g)) h) := by
  classical
  set Lg := (Finset.range w.length).filter fun i => L < g.getI i with hLg
  set C : ℕ → Finset ℕ+ := fun i =>
    Finset.Icc (Nat.succPNat (gapPos g i - h)) (Nat.succPNat (gapPos g i + W - h)) with hC
  refine μ.isClustered_of_diam hμ (Lg.image C) (Finset.card_image_le.trans hr) ?_ ?_
  · intro q hq
    rw [tailh_ofFinsupp_apply] at hq
    have hmem := Finsupp.mem_support_iff.mpr hq
    rw [support_ofWordGap w g hw0] at hmem
    obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hmem
    rw [Finset.mem_range] at hj
    -- some gap at an index `≤ j` is large
    have hex : ∃ i, i ≤ j ∧ L < g.getI i := by
      by_contra hcon
      have hcon' : ∀ i, i ≤ j → g.getI i ≤ L := fun i hi =>
        not_lt.mp fun hlt => hcon ⟨i, hi, hlt⟩
      have h1 := gapPos_le_of_forall_le g j hcon'
      have h2 : (j + 1) * L ≤ T * L := Nat.mul_le_mul_right _ (by omega)
      have h3 : T * (L + 1) = T * L + T := by ring
      omega
    set i := Nat.findGreatest (fun i => L < g.getI i) j with hi
    have hi_le : i ≤ j := Nat.findGreatest_le j
    have hi_spec : L < g.getI i := by
      obtain ⟨i', hi'j, hi'⟩ := hex
      exact Nat.findGreatest_spec (P := fun i => L < g.getI i) hi'j hi'
    have hi_max : ∀ l, i < l → l ≤ j → g.getI l ≤ L := fun l hl hlj =>
      not_lt.mp (Nat.findGreatest_is_greatest (P := fun i => L < g.getI i) hl hlj)
    have hbound := gapPos_le_gapPos_add g hi_le hi_max
    have hji : (j - i) * (L + 1) ≤ W := by
      rw [hW]
      exact Nat.mul_le_mul_right _ (by omega)
    have hmono : gapPos g i ≤ gapPos g j := (strictMono_gapPos g).monotone hi_le
    refine ⟨C i, Finset.mem_image_of_mem C ?_, ?_⟩
    · rw [hLg, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hi_spec⟩
    · rw [hC]
      simp only [Finset.mem_Icc, ← PNat.coe_le_coe, Nat.succPNat_coe]
      have hq1 : (q : ℕ) = q.natPred + 1 := (PNat.natPred_add_one q).symm
      omega
  · intro C' hC' q hq q' hq'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hC'
    rw [hC] at hq hq'
    simp only [Finset.mem_Icc, ← PNat.coe_le_coe, Nat.succPNat_coe] at hq hq'
    omega

/-- **Separated placements** (Lemmas 3.8 and 3.9): the upper order-type bound on a bounded
QTR support clusters sufficiently deep digit tails into at most `r` groups (Lemma 3.8). A
truncation of order type at least `ω ^ r` supplies `r` fixed nonzero patterns whose placements
on every increasing selection of separated blocks occur as tails of points in that truncation
(Lemma 3.9).

The construction provides core blocks, detection intervals, and disjoint protective
intervals suitable for the carry-free coefficient estimate of Lemma 3.11. -/
theorem exists_ray_marker {p : ℕ} [Fact (Nat.Prime p)] {a : ℕ+} {b c : ℕ} {M N : ℕ+}
    {x : ℚ → 𝔽ᵃ_[p]} (hx : IsQTR x a b c M N) [WellFoundedLT ↥(Function.support x)]
    {m₁ m₂ : ℤ} (hm₁ : -(b : ℤ) ≤ m₁)
    (hsub : Function.support x ⊆ ⋃ m ∈ Set.Icc m₁ m₂, Sabc_m p a c m)
    {r : ℕ} (hr : 0 < r) (hV : typeLT ↥(Function.support x) < omega0 ^ (r + 1))
    {R₀ : ℤ} [WellFoundedLT ↥(Function.support x ∩ Set.Iic (R₀ : ℚ))]
    (hU : omega0 ^ r ≤ typeLT ↥(Function.support x ∩ Set.Iic (R₀ : ℚ)))
    (n : ℕ) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∃ μ : MarkerData, n ≤ p ^ μ.h ∧
      (∃ lo Δ : ℕ, 0 < μ.s ∧ (M : ℕ) ≤ lo ∧ μ.s + (M : ℕ) ≤ Δ ∧
        (N : ℕ) ∣ Δ ∧ ∀ j, μ.b j =
          Finset.Icc (Nat.succPNat (lo + Δ * j))
            (Nat.succPNat (lo + Δ * j + μ.s - 1))) ∧
      (∀ (m : ℤ) (dv : ℕ →₀ ℕ), (∀ j, dv j < p) → qval p a m dv ∈ Function.support x →
        μ.IsClustered r (tailh (ofFinsupp dv) h)) ∧
      ∃ α : Fin r → (Fin μ.s → ℕ), (∀ i, α i ≠ 0) ∧ (∀ i t, α i t < p) ∧
        ∀ jj : Fin r → ℕ, StrictMono jj →
          ∃ (m : ℤ) (dv : ℕ →₀ ℕ), (∀ j, dv j < p) ∧ qval p a m dv ∈ Function.support x ∧
            qval p a m dv ≤ (R₀ : ℚ) ∧
            tailh (ofFinsupp dv) h = (∑ i, placeAt (μ.b (jj i)) (α i)) := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hp0 : 0 < p := hp.pos
  -- A single point with exactly `r` long gaps supplies the movable patterns.
  obtain ⟨m, d, hm, hd, hsum, hdU, hcard⟩ :=
    exists_point_card_longGaps_eq hx hm₁ hsub hV Set.inter_subset_left hU
  let z : ℤ × List ℕ × List ℕ × Finset ℕ :=
    (m, word d, gapVector d, activeFinset M (gapVector d))
  have hzcard : z.2.2.2.card = r := hcard
  have hzlen : z.2.1.length = z.2.2.1.length := word_length_eq_gapVector_length d
  have hzs : ∀ i ∈ z.2.2.2, i < z.2.2.1.length :=
    fun i hi => (mem_activeFinset_iff.mp hi).1
  have hw0 : ∀ y ∈ z.2.1, y ≠ 0 := word_ne_zero d
  have hwp : ∀ y ∈ z.2.1, y < p := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := (PAdicOrderType.DigitEncoding.mem_word d y).mp hy
    exact hd i
  have hzm : z.1 ≤ ((a : ℕ) : ℤ) * R₀ := (qval_le_intCast_iff hd R₀).mp hdU.2
  set e := z.2.2.2.orderIsoOfFin hzcard with he
  set idx : Fin r → ℕ := fun h => (e h : ℕ) with hidx_def
  have hidx_mem : ∀ h, idx h ∈ z.2.2.2 := fun h => (e h).2
  have hidx_lt : ∀ h, idx h < z.2.2.1.length := fun h => hzs _ (hidx_mem h)
  have hidx_mono : StrictMono idx := fun h h' hlt => e.strictMono hlt
  -- Short gaps have length below `M`, so each surviving cluster has diameter at most `c M`.
  set L : ℕ := (M : ℕ) - 1 with hL
  set T : ℕ := c with hT
  set W : ℕ := T * (L + 1) with hW
  set S : ℕ := gapPos z.2.2.1 z.2.1.length with hS
  have hT_bound : z.2.1.length ≤ T := (word_length_le_digit_sum d).trans hsum
  have hT0 : 0 < T := by
    have hi := hidx_lt ⟨0, hr⟩
    omega
  have hM_W : (M : ℕ) ≤ W := by
    have hML : (M : ℕ) ≤ L + 1 := by rw [hL]; omega
    exact hML.trans (Nat.le_mul_of_pos_left _ hT0)
  have hS_ge : z.2.1.length ≤ S := Nat.le_add_right _ _
  have hS0 : 0 < S := by
    have := hidx_lt ⟨0, hr⟩
    omega
  refine ⟨W + S + 1, fun h hh => ?_⟩
  -- (c) the marker data for the tail position `h`
  set C : ℕ := h + W + 1 with hC
  set Q : ℕ := S + n + 2 * W + 1 with hQ
  have hNC : C ≤ (N : ℕ) * C := Nat.le_mul_of_pos_left _ N.pos
  have hNQ : Q ≤ (N : ℕ) * Q := Nat.le_mul_of_pos_left _ N.pos
  set lo : ℕ := (N : ℕ) * C - h with hlo
  have hlo_gt : W < lo := by omega
  have hΔ : S + n + 2 * W < (N : ℕ) * Q := by omega
  set μ := intervalMarker lo S n W ((N : ℕ) * Q) hS0 hlo_gt hΔ with hμ
  have hμnbhd := intervalMarker_nbhd lo S n W ((N : ℕ) * Q) hS0 hlo_gt hΔ
  refine ⟨μ, (Nat.lt_pow_self hp.one_lt).le,
    ⟨lo, (N : ℕ) * Q, hS0, by omega, by change S + (M : ℕ) ≤ (N : ℕ) * Q; omega,
      dvd_mul_right (N : ℕ) Q, fun _ => rfl⟩, ?_, ?_⟩
  · -- (1) every tail is clustered with at most `r` clusters
    intro m dv hdv hmem
    obtain ⟨m', hm', dv', hdv', hsum', heq⟩ := Set.mem_iUnion₂.mp (hsub hmem)
    obtain ⟨rfl, rfl⟩ := eq_of_qval_eq hdv hdv' heq
    have hcard' := card_active_lt hx hV (hm₁.trans hm'.1) hdv hsum'
      (show gapVector dv ∈ gapSet p a (Function.support x) m dv from
        ⟨dv, rfl, rfl, hmem⟩)
    have hcount : ((Finset.range (word dv).length).filter
        fun i => L < (gapVector dv).getI i).card ≤ r := by
      have hM := M.pos
      have hfilters : (Finset.range (word dv).length).filter
          (fun i => L < (gapVector dv).getI i) = activeFinset M (gapVector dv) := by
        ext i
        rw [Finset.mem_filter, Finset.mem_range, mem_activeFinset_iff,
          word_length_eq_gapVector_length]
        dsimp [L]
        omega
      rw [hfilters]
      exact Nat.lt_succ_iff.mp hcard'
    have hcluster := isClustered_tailh_ofWordGap μ (h := h) hμnbhd (word_ne_zero dv)
      ((word_length_le_digit_sum dv).trans hsum') hW (by omega) hcount
    simpa only [ofWordGap_word_gapVector] using hcluster
  · -- (2) the chunk patterns and their placements
    set α : Fin r → Fin S → ℕ := fun i u =>
      if activeCount (fun h => gapPos z.2.2.1 (idx h)) u = (i : ℕ) + 1
        then ofWordGap z.2.1 z.2.2.1 u else 0 with hα
    refine ⟨α, ?_, ?_, ?_⟩
    · -- the patterns are non-zero: the first letter of each chunk
      intro i hzero
      have hlt : idx i < z.2.1.length := by rw [hzlen]; exact hidx_lt i
      have hpos : gapPos z.2.2.1 (idx i) < S := strictMono_gapPos _ hlt
      have h1 : (if activeCount (fun h => gapPos z.2.2.1 (idx h)) (gapPos z.2.2.1 (idx i))
          = (i : ℕ) + 1 then ofWordGap z.2.1 z.2.2.1 (gapPos z.2.2.1 (idx i)) else 0) = 0 :=
        congrFun hzero ⟨gapPos z.2.2.1 (idx i), hpos⟩
      rw [activeCount_gapPos, activeCount_idx hidx_mono, if_pos rfl, ofWordGap_apply_gapPos,
        List.getD_eq_getElem _ _ hlt] at h1
      exact hw0 _ (List.getElem_mem hlt) h1
    · -- the patterns are valid
      intro i t
      simp only [hα]
      split_ifs
      · exact ofWordGap_digit_lt _ _ hp0 hw0 hwp _
      · exact hp0
    · -- the placements are tails of elements of `U`
      intro jj hjj
      obtain ⟨jj', hjj'mono, hext⟩ := exists_monotone_extension hr hjj.monotone
      refine ⟨z.1, ofWordGap z.2.1 (rayGap z.2.2.1 N idx (rayParam C Q jj' r)),
        ofWordGap_digit_lt _ _ hp0 hw0 hwp, ?_, ?_, ?_⟩
      · have hsteps : ∀ i ∈ (List.ofFn fun j =>
            List.replicate (rayParam C Q jj' r j) (idx j)).flatten,
            (M : ℕ) ≤ z.2.2.1.getI i := by
          intro i hi
          obtain ⟨l, hl, hil⟩ := List.mem_flatten.mp hi
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
          rw [List.eq_of_mem_replicate hil]
          exact (mem_activeFinset_iff.mp (hidx_mem j)).2
        have hpump := gapSet_pump hx hm hd hsum
          (show gapVector d ∈ gapSet p a (Function.support x) m d from
            ⟨d, rfl, rfl, hdU.1⟩) _ hsteps
        rw [← rayGap_eq_foldl_pump _ (N : ℕ) hidx_lt] at hpump
        exact (mem_gapSet_iff.mp hpump).2
      · rw [qval_le_intCast_iff (ofWordGap_digit_lt _ _ hp0 hw0 hwp)]
        exact hzm
      · exact tailh_rayParam_eq (S := S) hw0 hidx_mono hidx_lt hjj hjj'mono hext (by omega) rfl
          (by omega) hS0 (by omega)

end PAdicOrderType
