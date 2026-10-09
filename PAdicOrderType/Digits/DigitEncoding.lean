/-
Copyright (c) 2025 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shanwen Wang, Yijun Yuan
-/
module

public import PAdicOrderType.Digits.DigitSeries
public import PAdicOrderType.Digits.QTR
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Finite.List

/-!
# Digit words, zero gaps, and index changes

A finite digit sequence is encoded by its nonzero digits in increasing position order
and by the lengths of the zero gaps preceding those digits. These two lists determine
the sequence. Inserting zeros preserves the word and increases the corresponding gap.
These are the coordinates used in Definition 3.5 and in the proof of Lemma 3.6.

## Main definitions

* `PAdicOrderType.Sabc_m`: the rational slice with fixed integer part and bounded digit sum,
  the slice `S_{a,b,c,m}` of Section 2.2.
* `PAdicOrderType.word`: the ordered list of nonzero digit values.
* `PAdicOrderType.gapVector`: the leading zero count and the gaps between nonzero digits,
  the zero gaps of Definition 3.5.
* `PAdicOrderType.DigitSeries.ofFinsupp`: conversion from zero-based to positive digit indices.
* `PAdicOrderType.DigitSeries.shiftBy`: translation of digit positions to the right.

## Main statements

* `PAdicOrderType.DigitEncoding.finsupp_eq_of_word_gapVector_eq`: a word and its gaps determine the
  digits.
* `PAdicOrderType.DigitEncoding.gapOfList_map_insertZeros`: inserting zeros changes exactly one gap.
* `PAdicOrderType.DigitSeries.norm_shiftBy`: shifting by `m` scales the value by `p ^ (-m)`.
-/

@[expose] public section

namespace PAdicOrderType

open TrustworthyKedlaya QTR


/-- The rational slice with integer part `m`, scale `a`, and digit-sum bound `c`:
the values `(m - ∑ i, d i * p ^ (-(i + 1))) / a` for finite digit sequences with digits
below `p` and total digit sum at most `c`. This is the slice `S_{a,b,c,m}` of Section 2.2.
When `m ≥ -b`, it lies in `TrustworthyKedlaya.Sabc p a b c`. -/
noncomputable def Sabc_m (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ+) (c : ℕ) (m : ℤ) : Set ℚ :=
  { s : ℚ | ∃ (d : ℕ →₀ ℕ),
      (∀ i, d i < p) ∧ (d.sum fun _ v => v) ≤ c ∧
      s = (1 / (a : ℚ)) *
        ((m : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) }

/-- The nonzero digits of a finitely supported sequence, read in increasing order
of position. This is the sequence of nonzero digits recorded in the proof of Lemma 3.6. -/
noncomputable def word (d : ℕ →₀ ℕ) : List ℕ :=
  (d.support.sort (· ≤ ·)).map (fun i => d i)

/-- The zero gaps preceding the nonzero digits of a finitely supported sequence, as in
Definition 3.5. The first entry counts leading zeros; each later entry counts zeros between
consecutive nonzero digits. There is one gap per nonzero digit, and no entry for the final
zero tail. -/
noncomputable def gapVector (d : ℕ →₀ ℕ) : List ℕ :=
  let pos := d.support.sort (· ≤ ·)
  match pos with
  | [] => []
  | hd :: tl =>
    -- Leading zeros before the first nonzero digit
    hd :: (List.zipWith (fun a b => b - a - 1) (hd :: tl).dropLast tl)

namespace DigitEncoding

/-- The digit-insertion reindexing `fun j => if j < s then j else j + N` is strictly monotone. -/
theorem strictMono_insertZeros (s N : ℕ) :
    StrictMono (fun j => if j < s then j else j + N) := by
  intro i j hij
  by_cases hi : i < s
  · by_cases hj : j < s
    · simp only [hi, hj, if_true]; exact hij
    · simp only [hi, hj, if_true, if_false]; omega
  · have hj : ¬ j < s := by omega
    simp only [hi, hj, if_false]; omega

/-- A strictly monotone reindexing preserves the word (sorted list of nonzero digit values). -/
theorem word_mapDomain_strictMono (d : ℕ →₀ ℕ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    word (Finsupp.mapDomain φ d) = word d := by
  have hinj : Function.Injective φ := hφ.injective
  have he : (Finsupp.mapDomain φ d).support = Finset.map ⟨φ, hinj⟩ d.support := by
    rw [Finsupp.mapDomain_support_of_injective hinj d]
    exact (Finset.map_eq_image ⟨φ, hinj⟩ d.support).symm
  unfold word
  rw [he, ← StrictMonoOn.map_finsetSort ⟨φ, hinj⟩ d.support (hφ.strictMonoOn _), List.map_map]
  apply List.map_congr_left
  intro i _
  change (Finsupp.mapDomain φ d) (φ i) = d i
  exact Finsupp.mapDomain_apply hinj d i

/-- The leading position followed by the gaps between consecutive positions.
For a strictly increasing list, this records the number of zeros preceding each occupied
position. Applied to a sorted support, it gives `PAdicOrderType.gapVector`. -/
def gapOfList (pos : List ℕ) : List ℕ :=
  match pos with
  | [] => []
  | hd :: tl => hd :: (List.zipWith (fun a b => b - a - 1) (hd :: tl).dropLast tl)

/-- `gapVector d = gapOfList (sorted support of d)`. -/
theorem gapVector_eq_gapOfList (d : ℕ →₀ ℕ) :
    gapVector d = gapOfList (d.support.sort (· ≤ ·)) := rfl

/-- `gapOfList` preserves length. -/
theorem gapOfList_length (pos : List ℕ) : (gapOfList pos).length = pos.length := by
  cases pos with
  | nil => rfl
  | cons hd tl =>
    simp only [gapOfList, List.length_cons, List.length_zipWith, List.length_dropLast]; simp

/-- The `j`-th entry of `gapOfList pos`: `pos.getI 0` for `j = 0`, and `pos.getI j - pos.getI (j-1)
- 1` for `j ≥ 1`. -/
theorem gapOfList_getI (pos : List ℕ) (j : ℕ) (hj : j < pos.length) :
    (gapOfList pos).getI j =
      pos.getI j - (if j = 0 then 0 else pos.getI (j-1) + 1) := by
  cases pos with
  | nil => simp at hj
  | cons hd tl =>
    cases j with
    | zero => simp [gapOfList]
    | succ i =>
      simp only [gapOfList, Nat.succ_ne_zero, if_false, List.getI_cons_succ, Nat.add_sub_cancel]
      have hilt : i < tl.length := by simp at hj; omega
      rw [List.getI_eq_getElem (l := List.zipWith (fun a b => b - a - 1) (hd :: tl).dropLast tl)
            (by simp [List.length_zipWith, List.length_dropLast]; omega),
          List.getElem_zipWith, List.getElem_dropLast,
          List.getI_eq_getElem (l := tl) hilt,
          List.getI_eq_getElem (l := hd :: tl) (by simp; omega)]
      omega

/-- `gapVector d` has one entry per nonzero digit of `d`. -/
theorem gapVector_length (d : ℕ →₀ ℕ) : (gapVector d).length = d.support.card := by
  rw [gapVector_eq_gapOfList, gapOfList_length, Finset.length_sort]

/-- The `j`-th entry of `gapVector d` (via `getI`, total) in terms of the sorted support
positions: `pos.getI 0` for `j = 0`, and `pos.getI j - pos.getI (j-1) - 1` for `j ≥ 1`. -/
theorem gapVector_getI (d : ℕ →₀ ℕ) (j : ℕ) (hj : j < (gapVector d).length) :
    (gapVector d).getI j =
      (d.support.sort (· ≤ ·)).getI j
        - (if j = 0 then 0 else (d.support.sort (· ≤ ·)).getI (j-1) + 1) := by
  rw [gapVector_eq_gapOfList]
  apply gapOfList_getI
  rw [Finset.length_sort, ← gapVector_length]; exact hj

/-- `getI` commutes with `List.map` on in-range indices. -/
theorem map_getI (l : List ℕ) (f : ℕ → ℕ) (j : ℕ) (hj : j < l.length) :
    (l.map f).getI j = f (l.getI j) := by
  rw [List.getI_eq_getElem (l := l.map f) (by simpa using hj), List.getElem_map,
      List.getI_eq_getElem (l := l) hj]

/-- `getI` of a `List.set` on in-range indices. -/
theorem set_getI (l : List ℕ) (i : ℕ) (v : ℕ) (j : ℕ) (hj : j < l.length) :
    (l.set i v).getI j = if i = j then v else l.getI j := by
  rw [List.getI_eq_getElem (l := l.set i v) (by simpa using hj), List.getElem_set,
      List.getI_eq_getElem (l := l) hj]

/-- `getI` of a `List.set` at the set index. -/
theorem set_getI_self (l : List ℕ) (i v : ℕ) (hi : i < l.length) :
    (l.set i v).getI i = v := by
  rw [List.getI_eq_getElem (l := l.set i v) (by simpa using hi), List.getElem_set_self]

/-- Inserting `N` zeros before the `i`-th occupied position increases exactly the
`i`-th gap by `N`. All other gaps in a strictly increasing position list are unchanged. -/
theorem gapOfList_map_insertZeros (pos : List ℕ)
    (hmono : ∀ j₁ j₂, j₁ < j₂ → j₂ < pos.length → pos.getI j₁ < pos.getI j₂)
    (i N : ℕ) (hi : i < pos.length) :
    gapOfList (pos.map (fun x => if x < pos.getI i then x else x + N))
      = (gapOfList pos).set i ((gapOfList pos).getI i + N) := by
  set φ : ℕ → ℕ := fun x => if x < pos.getI i then x else x + N with hφ
  have hlen : (pos.map φ).length = pos.length := by rw [List.length_map]
  have hφval : ∀ l, l < pos.length →
      φ (pos.getI l) = if l < i then pos.getI l else pos.getI l + N := by
    intro l hl
    simp only [hφ]
    by_cases hli : l < i
    · have : pos.getI l < pos.getI i := hmono l i hli hi
      simp [hli, this]
    · have hge : ¬ pos.getI l < pos.getI i := by
        rcases Nat.lt_or_ge i l with h | h
        · have := hmono i l h hl; omega
        · have : l = i := by omega
          subst this; omega
      simp [hli, hge]
  apply List.ext_getElem
  · rw [gapOfList_length, List.length_set, gapOfList_length, List.length_map]
  · intro j h1 h2
    have jlen : j < pos.length := by rw [gapOfList_length, hlen] at h1; exact h1
    rw [← List.getI_eq_getElem (l := gapOfList (pos.map φ)),
        ← List.getI_eq_getElem (l := (gapOfList pos).set i _)]
    rw [gapOfList_getI _ _ (by rw [hlen]; exact jlen)]
    rw [map_getI _ _ _ jlen, hφval j jlen]
    rw [set_getI _ _ _ _ (by rw [gapOfList_length]; exact jlen)]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, gapOfList_getI _ _ hi]
      by_cases hi0 : i = 0
      · subst hi0; simp
      · have hjm1 : i - 1 < pos.length := by omega
        rw [map_getI _ _ _ hjm1, hφval (i-1) hjm1]
        have hm := hmono (i-1) i (by omega) hi
        simp only [if_neg hi0, if_neg (show ¬ i < i by omega), if_pos (show i - 1 < i by omega)]
        omega
    · rw [if_neg hij, gapOfList_getI _ _ jlen]
      by_cases hj0 : j = 0
      · subst hj0
        have hpos : 0 < i := by omega
        simp only [if_true, if_pos hpos]
      · have hjm1 : j - 1 < pos.length := by omega
        rw [map_getI _ _ _ hjm1, hφval (j-1) hjm1]
        simp only [if_neg hj0]
        rcases Nat.lt_or_ge j i with hlt | hge
        · simp only [if_pos (show j < i by omega), if_pos (show j - 1 < i by omega)]
        · have hgt : i < j := by omega
          have hm := hmono (j-1) j (by omega) jlen
          simp only [if_neg (show ¬ j < i by omega), if_neg (show ¬ j - 1 < i by omega)]
          omega

/-- The sorted support of `mapDomain φ d` (for `φ` strictly monotone) is the sorted support of `d`
mapped through `φ`. -/
theorem support_sort_mapDomain (d : ℕ →₀ ℕ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    (Finsupp.mapDomain φ d).support.sort (· ≤ ·) = (d.support.sort (· ≤ ·)).map φ := by
  have hinj : Function.Injective φ := hφ.injective
  have he : (Finsupp.mapDomain φ d).support = Finset.map ⟨φ, hinj⟩ d.support := by
    rw [Finsupp.mapDomain_support_of_injective hinj d]
    exact (Finset.map_eq_image ⟨φ, hinj⟩ d.support).symm
  rw [he, ← StrictMonoOn.map_finsetSort ⟨φ, hinj⟩ d.support (hφ.strictMonoOn _)]
  rfl

/-- The sorted support of `d` is strictly increasing (in `getI` form). -/
theorem support_sort_strictMono (d : ℕ →₀ ℕ) (l₁ l₂ : ℕ)
    (h12 : l₁ < l₂) (h2 : l₂ < (d.support.sort (· ≤ ·)).length) :
    (d.support.sort (· ≤ ·)).getI l₁ < (d.support.sort (· ≤ ·)).getI l₂ := by
  have h1 : l₁ < (d.support.sort (· ≤ ·)).length := by omega
  rw [List.getI_eq_getElem (l := d.support.sort (· ≤ ·)) h1,
      List.getI_eq_getElem (l := d.support.sort (· ≤ ·)) h2]
  exact (d.support.sortedLT_sort.getElem_lt_getElem_iff).mpr h12

/-- Every element of `d.support` is some entry of the sorted support. -/
theorem mem_support_eq_getI (d : ℕ →₀ ℕ) (x : ℕ) (hx : x ∈ d.support) :
    ∃ l, l < (d.support.sort (· ≤ ·)).length ∧ (d.support.sort (· ≤ ·)).getI l = x := by
  have hx2 : x ∈ d.support.sort (· ≤ ·) := by rwa [Finset.mem_sort]
  rw [List.mem_iff_getElem] at hx2
  obtain ⟨l, hl, hlx⟩ := hx2
  exact ⟨l, hl, by rw [List.getI_eq_getElem (l := d.support.sort (· ≤ ·)) hl]; exact hlx⟩

/-- The set of `List ℕ` of length `≤ c` with all entries `< M` is finite (it embeds into the
length-`≤ c` lists over the finite type `Fin M`). -/
theorem finite_bounded_lists (c M : ℕ) :
    {l : List ℕ | l.length ≤ c ∧ ∀ x ∈ l, x < M}.Finite := by
  have hfin : {l : List (Fin M) | l.length ≤ c}.Finite := List.finite_length_le (Fin M) c
  apply Set.Finite.subset (hfin.image (fun l => l.map Fin.val))
  rintro l ⟨hlen, hbd⟩
  refine ⟨l.attachWith (fun x => x < M) hbd |>.map (fun x => (⟨x.1, x.2⟩ : Fin M)), ?_, ?_⟩
  · simp [List.length_map, hlen]
  · simp [List.map_map, List.map_attachWith]

/-- The sum of the word equals the digit sum. -/
theorem word_sum (d : ℕ →₀ ℕ) : (word d).sum = d.sum (fun _ v => v) := by
  unfold word
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
  rfl

/-- Membership in the word: `v` occurs iff some support position carries digit value `v`. -/
theorem mem_word (d : ℕ →₀ ℕ) (v : ℕ) : v ∈ word d ↔ ∃ i ∈ d.support, d i = v := by
  unfold word
  rw [List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by rwa [Finset.mem_sort] at hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, by rwa [Finset.mem_sort], rfl⟩

/-- If two finsupps have the same word and one has all digits `< p`, so does the other. -/
theorem digit_lt_of_word_eq {p : ℕ} (hp : 0 < p) (d' d_word : ℕ →₀ ℕ)
    (hw : word d' = word d_word) (hbd : ∀ i, d_word i < p) : ∀ i, d' i < p := by
  intro i
  by_cases hi : i ∈ d'.support
  · have : d' i ∈ word d' := by rw [mem_word]; exact ⟨i, hi, rfl⟩
    rw [hw, mem_word] at this
    obtain ⟨j, _, hj⟩ := this
    rw [← hj]; exact hbd j
  · rw [Finsupp.notMem_support_iff.mp hi]; exact hp

/-- Equal words have equal digit sums. -/
theorem sum_eq_of_word_eq (d' d_word : ℕ →₀ ℕ) (hw : word d' = word d_word) :
    d'.sum (fun _ v => v) = d_word.sum (fun _ v => v) := by
  rw [← word_sum d', ← word_sum d_word, hw]

/-- A strictly increasing list of positions is determined by its gap list.
The position at index `j` is `j` plus the sum of the first `j + 1` gaps. -/
theorem sortedSupportList_inj {pos₁ pos₂ : List ℕ}
    (hmono₁ : ∀ j₁ j₂, j₁ < j₂ → j₂ < pos₁.length → pos₁.getI j₁ < pos₁.getI j₂)
    (hmono₂ : ∀ j₁ j₂, j₁ < j₂ → j₂ < pos₂.length → pos₂.getI j₁ < pos₂.getI j₂)
    (h : gapOfList pos₁ = gapOfList pos₂) : pos₁ = pos₂ := by
  have hlen : pos₁.length = pos₂.length := by
    rw [← gapOfList_length pos₁, ← gapOfList_length pos₂, h]
  have hgetI : ∀ j, j < pos₁.length → pos₁.getI j = pos₂.getI j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j IH =>
      intro hj1
      have hj2 : j < pos₂.length := hlen ▸ hj1
      have e : (gapOfList pos₁).getI j = (gapOfList pos₂).getI j := by rw [h]
      rw [gapOfList_getI pos₁ j hj1, gapOfList_getI pos₂ j hj2] at e
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0; simpa using e
      · have hjne : j ≠ 0 := by omega
        rw [if_neg hjne, if_neg hjne] at e
        have hprev : pos₁.getI (j - 1) = pos₂.getI (j - 1) :=
          IH (j - 1) (by omega) (by omega)
        have hs1 : pos₁.getI (j - 1) < pos₁.getI j := hmono₁ (j - 1) j (by omega) hj1
        have hs2 : pos₂.getI (j - 1) < pos₂.getI j := hmono₂ (j - 1) j (by omega) hj2
        omega
  apply List.ext_getElem hlen
  intro i h1 h2
  rw [← List.getI_eq_getElem pos₁ h1, ← List.getI_eq_getElem pos₂ h2]
  exact hgetI i h1

/-- A finitely supported digit sequence is determined by its word and gap vector.
The gaps determine the occupied positions, and the word determines the digit at each position. -/
theorem finsupp_eq_of_word_gapVector_eq {d₁ d₂ : ℕ →₀ ℕ}
    (hw : word d₁ = word d₂) (hgv : gapVector d₁ = gapVector d₂) : d₁ = d₂ := by
  classical
  have hpos : d₁.support.sort (· ≤ ·) = d₂.support.sort (· ≤ ·) := by
    apply sortedSupportList_inj (support_sort_strictMono d₁) (support_sort_strictMono d₂)
    rw [← gapVector_eq_gapOfList, ← gapVector_eq_gapOfList]; exact hgv
  have hsupp : d₁.support = d₂.support := by
    have h := congrArg List.toFinset hpos
    rwa [Finset.sort_toFinset, Finset.sort_toFinset] at h
  apply Finsupp.ext
  intro x
  by_cases hx : x ∈ d₁.support
  · obtain ⟨l, hl, hlx⟩ := mem_support_eq_getI d₁ x hx
    have hl2 : l < (d₂.support.sort (· ≤ ·)).length := by rw [← hpos]; exact hl
    have e1 : (word d₁).getI l = d₁ x := by
      rw [word, map_getI _ _ _ hl, hlx]
    have e2 : (word d₂).getI l = d₂ x := by
      rw [word, map_getI _ _ _ hl2]
      rw [← hpos, hlx]
    rw [← e1, hw, e2]
  · have hx2 : x ∉ d₂.support := by rwa [hsupp] at hx
    rw [Finsupp.notMem_support_iff.mp hx, Finsupp.notMem_support_iff.mp hx2]

end DigitEncoding

open DigitEncoding

namespace DigitSeries

/-- Add a `ℕ` offset to a `ℕ+` index. -/
def pAdd (i : ℕ+) (m : ℕ) : ℕ+ := ⟨(i : ℕ) + m, by have h := i.pos; omega⟩

@[simp] lemma pAdd_coe (i : ℕ+) (m : ℕ) : ((pAdd i m : ℕ+) : ℕ) = (i : ℕ) + m := rfl

lemma pAdd_inj (m : ℕ) : Function.Injective (fun i => pAdd i m) := by
  intro a b h
  have h2 : ((pAdd a m : ℕ+) : ℕ) = ((pAdd b m : ℕ+) : ℕ) := congrArg (fun x : ℕ+ => (x : ℕ)) h
  rw [pAdd_coe, pAdd_coe] at h2
  exact PNat.coe_injective (by omega)

/-- Build a `DigitSeries` from the zero-indexed digit model `d : ℕ →₀ ℕ`
(`d j` = digit at position `j+1`, i.e. coefficient of `p^{-(j+1)}`). -/
noncomputable def ofFinsupp (d : ℕ →₀ ℕ) : DigitSeries :=
  Finsupp.ofSupportFinite (fun q => d q.natPred) (by
    apply Set.Finite.subset (d.support.finite_toSet.image (fun j => Nat.succPNat j))
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    exact ⟨q.natPred, by simpa [Finsupp.mem_support_iff] using hq, PNat.succPNat_natPred q⟩
  )

@[simp] lemma ofFinsupp_apply (d : ℕ →₀ ℕ) (q : ℕ+) : (ofFinsupp d) q = d q.natPred := rfl

lemma ofFinsupp_isP (p : ℕ) [Fact (Nat.Prime p)] (d : ℕ →₀ ℕ) (hd : ∀ j, d j < p) :
    (ofFinsupp d).IsP p := fun _q => hd _

/-- Reindex a sum over `(ofFinsupp d)`'s support (`ℕ+`-indexed) as a `Finsupp.sum`
over `d` (`ℕ`-indexed), via the bijection `q ↦ q.natPred`. The caller supplies only
the per-point value identity; the structural bijection is shared. -/
private lemma ofFinsupp_sum_reindex {M : Type*} [AddCommMonoid M] (d : ℕ →₀ ℕ)
    (F : ℕ+ → M) (H : ℕ → ℕ → M)
    (hFH : ∀ q ∈ (ofFinsupp d).support, F q = H q.natPred (d q.natPred)) :
    ∑ q ∈ (ofFinsupp d).support, F q = d.sum H := by
  classical
  rw [Finsupp.sum]
  refine Finset.sum_bij (fun (q : ℕ+) _ => q.natPred) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finsupp.mem_support_iff, ne_eq] at hq
    simpa [Finsupp.mem_support_iff] using hq
  · intro a _ b _ hab
    have : Nat.succPNat a.natPred = Nat.succPNat b.natPred := by rw [hab]
    rwa [PNat.succPNat_natPred, PNat.succPNat_natPred] at this
  · intro j hj
    refine ⟨Nat.succPNat j, ?_, ?_⟩
    · simp only [Finsupp.mem_support_iff, ne_eq]
      simpa [Finsupp.mem_support_iff] using hj
    · simp [Nat.natPred_succPNat]
  · intro q hq
    exact hFH q hq

/-- `ofFinsupp` recovers the zero-indexed digit value via `norm`. -/
lemma ofFinsupp_norm (p : ℕ) [Fact (Nat.Prime p)] (d : ℕ →₀ ℕ) :
    (ofFinsupp d).norm p = d.sum (fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))) := by
  classical
  change ∑ q ∈ (ofFinsupp d).support, ((ofFinsupp d) q : ℚ) * (p : ℚ) ^ (-(q : ℤ))
       = d.sum (fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)))
  apply ofFinsupp_sum_reindex
  intro q hq
  simp only [ofFinsupp_apply]
  congr 2
  have hq' : (q : ℕ) = q.natPred + 1 := (PNat.natPred_add_one q).symm
  rw [show ((q : ℕ) : ℤ) = ((q.natPred : ℕ) : ℤ) + 1 by rw [hq']; push_cast; ring]

/-- Shift a digit series right by `m` positions (multiply value by `p^{-m}`). -/
noncomputable def shiftBy (f : DigitSeries) (m : ℕ) : DigitSeries :=
  Finsupp.ofSupportFinite (fun q => if h : m < (q : ℕ) then f ⟨(q : ℕ) - m, by omega⟩ else 0) (by
    apply Set.Finite.subset (f.hasFiniteSupport.image (fun i => pAdd i m))
    intro q hq
    simp only [Function.mem_support, ne_eq] at hq
    split_ifs at hq with h
    · refine ⟨⟨(q : ℕ) - m, by omega⟩, ?_, ?_⟩
      · exact Function.mem_support.mpr hq
      · apply Subtype.ext; change ((q : ℕ) - m) + m = (q : ℕ); omega
    · exact absurd rfl hq
  )

lemma shiftBy_apply_pAdd (f : DigitSeries) (m : ℕ) (i : ℕ+) :
    (shiftBy f m) (pAdd i m) = f i := by
  change (if h : m < ((pAdd i m : ℕ+) : ℕ) then f ⟨((pAdd i m : ℕ+) : ℕ) - m, by omega⟩ else 0)
    = f i
  have hp := i.pos
  rw [dif_pos (by rw [pAdd_coe]; omega)]
  congr 1
  apply Subtype.ext
  change ((pAdd i m : ℕ+) : ℕ) - m = (i : ℕ)
  rw [pAdd_coe]; omega

/-- Where `shiftBy f m` is nonzero: exactly the `m`-translates of `f`'s support. -/
lemma shiftBy_ne_zero_iff (f : DigitSeries) (m : ℕ) (q : ℕ+) :
    (shiftBy f m) q ≠ 0 ↔ ∃ i : ℕ+, f i ≠ 0 ∧ q = pAdd i m := by
  constructor
  · intro hq
    have hmq : m < (q : ℕ) := by
      by_contra hle
      push Not at hle
      apply hq
      change (if h : m < (q : ℕ) then f ⟨(q : ℕ) - m, by omega⟩ else 0) = 0
      rw [dif_neg (by omega)]
    refine ⟨⟨(q : ℕ) - m, by omega⟩, ?_, ?_⟩
    · have hval : (shiftBy f m) q = f ⟨(q : ℕ) - m, by omega⟩ := by
        change (if h : m < (q : ℕ) then f ⟨(q : ℕ) - m, by omega⟩ else 0) = _
        rw [dif_pos hmq]
      rwa [hval] at hq
    · apply PNat.coe_injective
      change (q : ℕ) = (q : ℕ) - m + m; omega
  · rintro ⟨i, hi, rfl⟩
    rw [shiftBy_apply_pAdd]; exact hi

/-- Membership in the support `Finset` of `shiftBy f m`, as a translate. -/
lemma mem_shiftBy_support_iff (f : DigitSeries) (m : ℕ) (q : ℕ+) :
    q ∈ (shiftBy f m).support ↔ ∃ i : ℕ+, f i ≠ 0 ∧ q = pAdd i m := by
  rw [Finsupp.mem_support_iff]
  exact shiftBy_ne_zero_iff f m q

/-- `pAdd i m` lands in the support `Finset` of `shiftBy f m` whenever `i` is in `f`'s support. -/
lemma pAdd_mem_shiftBy_support (f : DigitSeries) (m : ℕ) (i : ℕ+) (hi : f i ≠ 0) :
    pAdd i m ∈ (shiftBy f m).support :=
  (mem_shiftBy_support_iff f m _).mpr ⟨i, hi, rfl⟩

/-- Reindex a sum over `shiftBy f m`'s support back onto `f`'s support, via the
forward bijection `i ↦ pAdd i m`. Oriented to match the post-`symm` goal
(`∑ over f.support = ∑ over (shiftBy f m).support`); the caller supplies only the
per-point value identity, the structural bijection is shared. -/
private lemma shiftBy_sum_reindex {M : Type*} [AddCommMonoid M] (f : DigitSeries) (m : ℕ)
    (F : ℕ+ → M) (G : ℕ+ → M)
    (hFG : ∀ i ∈ f.support, F i = G (pAdd i m)) :
    ∑ i ∈ f.support, F i = ∑ q ∈ (shiftBy f m).support, G q := by
  classical
  refine Finset.sum_bij (fun (i : ℕ+) _ => pAdd i m) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finsupp.mem_support_iff] at hi
    exact pAdd_mem_shiftBy_support f m i hi
  · intro a _ b _ hab; exact pAdd_inj m hab
  · intro q hq
    rw [mem_shiftBy_support_iff] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact ⟨i, by rw [Finsupp.mem_support_iff]; exact hi, rfl⟩
  · intro i hi
    exact hFG i hi

/-- `norm` of a shifted series scales by `p^{-m}`. -/
lemma norm_shiftBy (p : ℕ) [Fact (Nat.Prime p)] (f : DigitSeries) (m : ℕ) :
    (shiftBy f m).norm p = f.norm p * (p : ℚ) ^ (-(m : ℤ)) := by
  classical
  have hpne : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  change ∑ q ∈ (shiftBy f m).support, ((shiftBy f m) q : ℚ) * (p : ℚ) ^ (-(q : ℤ))
       = (∑ i ∈ f.support, (f i : ℚ) * (p : ℚ) ^ (-(i : ℤ))) * (p : ℚ) ^ (-(m : ℤ))
  rw [Finset.sum_mul]
  symm
  apply shiftBy_sum_reindex
  intro i _
  rw [shiftBy_apply_pAdd, pAdd_coe, mul_assoc]
  congr 1
  rw [← zpow_add₀ hpne]
  congr 1; push_cast; ring

end DigitSeries

end PAdicOrderType
