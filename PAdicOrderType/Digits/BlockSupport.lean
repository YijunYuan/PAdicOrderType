/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import PAdicOrderType.Digits.BlockInterleavings

/-!
# Occupied blocks in carry-free products

For pairwise disjoint coordinate blocks, the number of blocks meeting a digit vector
bounds the number that can occur in a carry-free power. When a product attains the
maximum possible count, its factors occupy disjoint sets of blocks and each contributes
whole blocks. This is the final assertion of Lemma 3.11.

## Main definitions

* `PAdicOrderType.hitBlocks`: the finite set of occupied block indices.
* `PAdicOrderType.placedLetters`: the individual digit-vector placements of a word.

## Main statements

* `PAdicOrderType.hitBlocks_power_le`: an `n`-fold power occupies at most `n` times the
  maximum number of blocks of an input.
* `PAdicOrderType.hitBlocks_disjoint_of_maximal`: attaining the maximum forces disjointness.
* `PAdicOrderType.whole_placed_letter`: disjoint occupied blocks make each letter belong
  entirely to one factor.
-/

namespace PAdicOrderType

/-- The occupied indices of a pairwise disjoint family of blocks.
For each nonzero digit lying in a block, choose one containing block. Under pairwise
disjointness this choice is unique, and the result contains exactly the occupied blocks. -/
noncomputable def hitBlocks (B : ℕ → Finset ℕ+) (x : ℕ+ →₀ ℕ) : Finset ℕ := by
  classical
  exact x.support.biUnion fun pos =>
    if h : ∃ j, pos ∈ B j then {h.choose} else ∅

lemma mem_hitBlocks {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
    (x : ℕ+ →₀ ℕ) (j : ℕ) : j ∈ hitBlocks B x ↔ ∃ pos ∈ B j, x pos ≠ 0 := by
  classical
  unfold hitBlocks
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨pos, hpos, hj⟩
    split_ifs at hj with h
    · have hj' : j = h.choose := Finset.mem_singleton.mp hj
      exact ⟨pos, hj' ▸ h.choose_spec, Finsupp.mem_support_iff.mp hpos⟩
    · exact (Finset.notMem_empty _ hj).elim
  · rintro ⟨pos, hpos, hx⟩
    refine ⟨pos, Finsupp.mem_support_iff.mpr hx, ?_⟩
    have h : ∃ i, pos ∈ B i := ⟨j, hpos⟩
    rw [dif_pos h, Finset.mem_singleton]
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne) hpos h.choose_spec

lemma hitBlocks_zero (B : ℕ → Finset ℕ+) : hitBlocks B 0 = ∅ := by
  classical
  simp [hitBlocks]

lemma hitBlocks_add {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
    (x y : ℕ+ →₀ ℕ) : hitBlocks B (x + y) = hitBlocks B x ∪ hitBlocks B y := by
  classical
  ext j
  simp only [mem_hitBlocks hdisj, Finset.mem_union, Finsupp.add_apply]
  constructor
  · rintro ⟨pos, hpos, hne⟩
    by_cases hx : x pos = 0
    · exact Or.inr ⟨pos, hpos, by simpa [hx] using hne⟩
    · exact Or.inl ⟨pos, hpos, hx⟩
  · rintro (⟨pos, hpos, hx⟩ | ⟨pos, hpos, hy⟩)
    · exact ⟨pos, hpos, by omega⟩
    · exact ⟨pos, hpos, by omega⟩

lemma hitBlocks_placeList {s : ℕ} {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
    (hcard : ∀ i, (B i).card = s) (w : List (Fin s → ℕ)) (l : List ℕ)
    (hwnz : ∀ e ∈ w, e ≠ 0) (hlen : l.length = w.length) :
    hitBlocks B (placeList B w l) = l.toFinset := by
  classical
  ext j
  rw [mem_hitBlocks hdisj, List.mem_toFinset]
  constructor
  · rintro ⟨pos, hpos, hx⟩
    by_contra hj
    apply hx
    apply placeList_apply_eq_zero B w l
    intro k hk hpk
    have hne : j ≠ k := by rintro rfl; exact hj hk
    exact Finset.disjoint_left.mp (hdisj hne) hpos hpk
  · intro hj
    exact exists_apply_ne_zero_of_mem hcard w l hwnz hlen j hj

/-- At the maximal total number of occupied blocks, a split cannot share a block. Hence
different factors occupy different blocks, as in Lemma 3.11. -/
lemma hitBlocks_disjoint_of_maximal {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
    {x y : ℕ+ →₀ ℕ} {k l : ℕ}
    (hx : (hitBlocks B x).card ≤ k) (hy : (hitBlocks B y).card ≤ l)
    (hxy : (hitBlocks B (x + y)).card = k + l) :
    Disjoint (hitBlocks B x) (hitBlocks B y) := by
  classical
  rw [hitBlocks_add hdisj] at hxy
  have hc := Finset.card_union_add_card_inter (hitBlocks B x) (hitBlocks B y)
  have hz : (hitBlocks B x ∩ hitBlocks B y).card = 0 := by omega
  exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hz)

/-- A nonzero coefficient of a product comes from a split with both coefficients nonzero. -/
lemma exists_split_of_convolve_ne_zero {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [CommRing K] (A C : DigitCoefficients p K)
    (u : {d : DigitSeries // d.IsP p}) (hu : DigitCoefficients.convolve A C u ≠ 0) :
    ∃ v w : {d : DigitSeries // d.IsP p},
      v.1 + w.1 = u.1 ∧ A v ≠ 0 ∧ C w ≠ 0 := by
  classical
  rw [DigitCoefficients.convolve_apply] at hu
  obtain ⟨z, hz, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  have heq := Finset.mem_antidiagonal.mp hz
  let v : {d : DigitSeries // d.IsP p} :=
    ⟨z.1, DigitCoefficients.isP_of_add_left u.2 heq⟩
  let w : {d : DigitSeries // d.IsP p} :=
    ⟨z.2, DigitCoefficients.isP_of_add_right u.2 heq⟩
  refine ⟨v, w, by simpa only [v, w] using heq, ?_, ?_⟩
  · have h := left_ne_zero_of_mul hn
    rwa [DigitCoefficients.extendMv_apply_of_isP A v.2] at h
  · have h := right_ne_zero_of_mul hn
    rwa [DigitCoefficients.extendMv_apply_of_isP C w.2] at h

/-- Powers multiply the maximum occupied-block count by the exponent.
The base bound is needed only at digit vectors below the specified target. -/
lemma hitBlocks_power_le {p : ℕ} [Fact (Nat.Prime p)] {K : Type*} [CommRing K]
    {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
    (A : DigitCoefficients p K) {r : ℕ} (bound : ℕ+ →₀ ℕ)
    (hA : ∀ v : {d : DigitSeries // d.IsP p}, v.1 ≤ bound → A v ≠ 0 →
      (hitBlocks B (v.1)).card ≤ r)
    (n : ℕ) (u : {d : DigitSeries // d.IsP p}) (hub : u.1 ≤ bound)
    (hu : DigitCoefficients.power A n u ≠ 0) :
    (hitBlocks B (u.1)).card ≤ n * r := by
  classical
  induction n generalizing u with
  | zero =>
      rw [DigitCoefficients.power, DigitCoefficients.unit_apply] at hu
      have huz : u.1 = 0 := by
        by_contra hne
        exact hu (if_neg hne)
      rw [huz, hitBlocks_zero]
      simp
  | succ n ih =>
      obtain ⟨v, w, hvw, hv, hw⟩ := exists_split_of_convolve_ne_zero
        (DigitCoefficients.power A n) A u hu
      have hvle : v.1 ≤ u.1 := by
        rw [← hvw]; exact le_self_add
      have hwle : w.1 ≤ u.1 := by
        rw [← hvw]; exact le_add_self
      have hvb := ih v (hvle.trans hub) hv
      have hwb := hA w (hwle.trans hub) hw
      rw [← hvw, hitBlocks_add hdisj]
      have hc := Finset.card_union_le (hitBlocks B (v.1))
        (hitBlocks B (w.1))
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- The finitely many individual pattern placements of a word. -/
noncomputable def placedLetters {s : ℕ} (B : ℕ → Finset ℕ+)
    (w : List (Fin s → ℕ)) (l : List ℕ) : List (ℕ+ →₀ ℕ) :=
  (w.zip l).map fun ei => placeAt (B ei.2) ei.1

lemma placedLetters_sum {s : ℕ} (B : ℕ → Finset ℕ+)
    (w : List (Fin s → ℕ)) (l : List ℕ) :
    (placedLetters B w l).sum = placeList B w l := by
  induction w generalizing l with
  | nil => simp [placedLetters]
  | cons e w ih =>
      cases l with
      | nil => rfl
      | cons j l => simp [placedLetters, placeList, ← ih l]

lemma placedLetters_ne_zero {s : ℕ} {B : ℕ → Finset ℕ+}
    (hcard : ∀ i, (B i).card = s)
    (w : List (Fin s → ℕ)) (l : List ℕ) (hwnz : ∀ e ∈ w, e ≠ 0) :
    ∀ v ∈ placedLetters B w l, v ≠ 0 := by
  intro v hv
  obtain ⟨⟨e, j⟩, hej, rfl⟩ := List.mem_map.mp hv
  exact placeAt_ne_zero (hcard j) (hwnz e (List.of_mem_zip hej).1)

lemma placedLetters_pairwise_disjoint {s : ℕ} {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
    (w : List (Fin s → ℕ)) (l : List ℕ) (hl : l.Pairwise (· < ·)) :
    (placedLetters B w l).Pairwise (fun x y => Disjoint x.support y.support) := by
  induction w generalizing l with
  | nil => simp [placedLetters]
  | cons e w ih =>
      cases l with
      | nil => simp [placedLetters]
      | cons j l =>
          obtain ⟨hjl, hl⟩ := List.pairwise_cons.mp hl
          change (placeAt (B j) e :: placedLetters B w l).Pairwise _
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih l hl⟩
          intro v hv
          obtain ⟨⟨e', k⟩, hek, rfl⟩ := List.mem_map.mp hv
          have hne : j ≠ k := (hjl k (List.of_mem_zip hek).2).ne
          exact (hdisj hne).mono support_placeAt_subset support_placeAt_subset

/-- Disjoint occupied-block sets ensure that every placed letter belongs wholly to one factor,
as at the end of the proof of Lemma 3.11. -/
lemma whole_placed_letter {s : ℕ} {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
    {x y : ℕ+ →₀ ℕ} (hxy : Disjoint (hitBlocks B x) (hitBlocks B y))
    (w : List (Fin s → ℕ)) (l : List ℕ) :
    ∀ v ∈ placedLetters B w l,
      (∀ i ∈ v.support, x i = 0) ∨ (∀ i ∈ v.support, y i = 0) := by
  classical
  intro v hv
  obtain ⟨⟨e, j⟩, _, rfl⟩ := List.mem_map.mp hv
  by_cases hj : j ∈ hitBlocks B x
  · right
    intro i hi
    by_contra hy
    exact Finset.disjoint_left.mp hxy hj ((mem_hitBlocks hdisj y j).mpr
      ⟨i, support_placeAt_subset hi, hy⟩)
  · left
    intro i hi
    by_contra hx
    exact hj ((mem_hitBlocks hdisj x j).mpr ⟨i, support_placeAt_subset hi, hx⟩)

lemma covered_by_blocks_of_le {B : ℕ → Finset ℕ+} {x y : ℕ+ →₀ ℕ}
    (hxy : x ≤ y) (hy : ∀ pos, y pos ≠ 0 → ∃ j, pos ∈ B j) :
    ∀ pos, x pos ≠ 0 → ∃ j, pos ∈ B j := by
  intro pos hx
  apply hy pos
  have hp := Finsupp.le_def.mp hxy pos
  omega

lemma hitBlocks_power_le_supported {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type*} [CommRing K] {B : ℕ → Finset ℕ+}
    (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
    (A : DigitCoefficients p K) {r : ℕ}
    (hA : ∀ v : {d : DigitSeries // d.IsP p}, A v ≠ 0 →
      (∀ pos, v.1 pos ≠ 0 → ∃ j, pos ∈ B j) →
      (hitBlocks B (v.1)).card ≤ r)
    (n : ℕ) (u : {d : DigitSeries // d.IsP p})
    (hcover : ∀ pos, u.1 pos ≠ 0 → ∃ j, pos ∈ B j)
    (hu : DigitCoefficients.power A n u ≠ 0) :
    (hitBlocks B (u.1)).card ≤ n * r := by
  apply hitBlocks_power_le hdisj A (u.1) _ n u le_rfl hu
  intro v hv hne
  exact hA v hne (covered_by_blocks_of_le hv hcover)

end PAdicOrderType
