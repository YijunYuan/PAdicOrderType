/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Digits.DigitEncoding
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.List.ToFinsupp

/-!
# Digit coordinates, long-gap pumping, and lexicographic order

This file develops word/gap coordinates and the order embedding obtained by independently
inserting zeros into chosen gaps. Finite patterns of short and long gaps then give
upper bounds on the order type of bounded digit sets. Together these constitute the proof of
Lemma 3.6.

An element `q = (1/a)(m − 0.q₁q₂⋯)` of the slice `S_{a,b,c,m}` is encoded by a
digit finsupp `d : ℕ →₀ ℕ` (with `d i` the digit `q_{i+1}`); its **word** and
**gap vector** are
`PAdicOrderType.word d` and `PAdicOrderType.gapVector d`. The pair
`(word, gap vector)` determines `d`
(`PAdicOrderType.DigitEncoding.finsupp_eq_of_word_gapVector_eq`), so the coding
`(𝐝, g) ↦ q_m(𝐝, g)` is realized by `d ↦ qval p a m d` below.

## Main definitions

- `PAdicOrderType.qval`: the value `q_m(𝐝, g) = (1/a)(m − 0.[𝐝; g])`.
- `PAdicOrderType.gapSet`: the gap set `U_{𝐝,m}` of gap vectors of elements
  of `U` in the `m`-slice with word `𝐝`.

## Main statements

- `PAdicOrderType.gapSet_pump_single` / `PAdicOrderType.gapSet_pump`: for `U` the support
  of a QTR function and `g ∈ U_{𝐝,m}`, inserting `N` zeros at any collection of gap indices `i` with
  `g_i ≥ M` (each any number of times) stays inside `U_{𝐝,m}`.
- `PAdicOrderType.card_active_lt`: a point of QTR support of order type `< ω ^ k`
  has fewer than `k` long gaps (the first direction of Lemma 3.6).
- `PAdicOrderType.typeLT_ray`: a ray of dimension `r` has order type `ω ^ r`.
- `PAdicOrderType.pow_mul_norm_eq_pih_add_norm_tailh`: the head-tail norm identity from the
  proof of Lemma 3.8.
-/

namespace PAdicOrderType

open PAdicOrderType PAdicOrderType.DigitEncoding

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- **`q_m(𝐝, g)`**: the value
`(1/a)(m − 0.[𝐝; g])` of the slice element encoded by the digit finsupp `d`
(whose word is `𝐝` and whose gap vector is `g`). This is the expression `q = (m - ‖d‖)/a`
following Definition 3.5. -/
noncomputable def qval (p : ℕ) (a : ℕ+) (m : ℤ) (d : ℕ →₀ ℕ) : ℚ :=
  (1 / (a : ℚ)) * ((m : ℚ) - d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))

/-- **The gap set `U_{𝐝,m}`**: the set of gap
vectors `g` such that the element with word `word dw`, gap vector `g` and
integer part `m` belongs to `U`. -/
def gapSet (p : ℕ) (a : ℕ+) (U : Set ℚ) (m : ℤ) (dw : ℕ →₀ ℕ) : Set (List ℕ) :=
  { g | ∃ d : ℕ →₀ ℕ, word d = word dw ∧ gapVector d = g ∧ qval p a m d ∈ U }

omit [Fact (Nat.Prime p)] in
/-- Every member of the gap set `U_{𝐝,m}` has length the length of the word
`𝐝`. -/
lemma length_of_mem_gapSet {a : ℕ+} {U : Set ℚ} {m : ℤ} {dw : ℕ →₀ ℕ}
    {g : List ℕ} (hg : g ∈ gapSet p a U m dw) : g.length = (word dw).length := by
  obtain ⟨d, hword, hgap, -⟩ := hg
  rw [← hgap, gapVector_length, ← hword]
  unfold word
  rw [List.length_map, Finset.length_sort]

/-- In the support of a QTR function, inserting one period of zeros into a gap of
length at least the recurrence threshold preserves membership in the same gap set. -/
theorem gapSet_pump_single {a : ℕ+} {b c : ℕ} {M N : ℕ+} {x : ℚ → 𝔽ᵃ_[p]}
    (hx : IsQTR x a b c M N) {m : ℤ} (hm : -(b : ℤ) ≤ m)
    {dw : ℕ →₀ ℕ} (hdw : ∀ i, dw i < p) (hdw_sum : (dw.sum fun _ v => v) ≤ c)
    {g : List ℕ} (hg : g ∈ gapSet p a (Function.support x) m dw)
    {i : ℕ} (hi : (M : ℕ) ≤ g.getI i) :
    g.set i (g.getI i + (N : ℕ)) ∈ gapSet p a (Function.support x) m dw := by
  classical
  obtain ⟨d, hword, hgap, hq⟩ := hg
  subst hgap
  have hd_digit : ∀ j, d j < p :=
    DigitEncoding.digit_lt_of_word_eq (Fact.out : Nat.Prime p).pos d dw hword hdw
  have hd_sum : (d.sum fun _ v => v) ≤ c := by
    rw [DigitEncoding.sum_eq_of_word_eq d dw hword]; exact hdw_sum
  set pos := d.support.sort (· ≤ ·) with hpos
  clear_value pos
  -- `i` is a valid gap index: otherwise `getI i = 0 < M`, contradicting `hi`.
  have hi_lt : i < (gapVector d).length := by
    by_contra hcon
    rw [not_lt] at hcon
    rw [List.getI_eq_default _ hcon] at hi
    simp only [Nat.default_eq_zero] at hi
    have hMpos : 0 < (M : ℕ) := M.pos
    omega
  have hi_pos : i < pos.length := by
    rw [hpos, Finset.length_sort, ← gapVector_length]; exact hi_lt
  -- `pos`-stated forms of the support-sort helpers.
  have hmono_pos : ∀ l₁ l₂, l₁ < l₂ → l₂ < pos.length → pos.getI l₁ < pos.getI l₂ := by
    intro l₁ l₂ h12 h2; rw [hpos] at h2 ⊢; exact support_sort_strictMono d l₁ l₂ h12 h2
  have hmem_pos : ∀ y, y ∈ d.support → ∃ l, l < pos.length ∧ pos.getI l = y := by
    intro y hy; rw [hpos]; exact mem_support_eq_getI d y hy
  -- The gap before position `i` in terms of the sorted support positions.
  have hgapi : (gapVector d).getI i
      = pos.getI i - (if i = 0 then 0 else pos.getI (i-1) + 1) := by
    rw [gapVector_getI _ _ hi_lt, ← hpos]
  -- `M ≤ pos.getI i`, and the recurrence start index `k` with `k + M = pos.getI i`.
  have hM_le : (M : ℕ) ≤ pos.getI i := by
    have h := hi; rw [hgapi] at h; exact le_trans h (Nat.sub_le _ _)
  set k : ℕ := pos.getI i - (M : ℕ) with hk
  have hkM : k + (M : ℕ) = pos.getI i := by rw [hk]; omega
  -- Build `d'` via the digit-insertion reindexing `ψ` with threshold `pos.getI i`.
  set ψ : ℕ → ℕ := fun y => if y < pos.getI i then y else y + (N : ℕ) with hψ
  have hψmono : StrictMono ψ := by rw [hψ]; exact strictMono_insertZeros _ _
  refine ⟨Finsupp.mapDomain ψ d, ?_, ?_, ?_⟩
  · -- word preserved
    exact (word_mapDomain_strictMono d hψmono).trans hword
  · -- gap vector: `+N` at coordinate `i`
    rw [gapVector_eq_gapOfList, gapVector_eq_gapOfList,
      support_sort_mapDomain d hψmono, ← hpos, hψ]
    exact gapOfList_map_insertZeros pos hmono_pos i (N : ℕ) hi_pos
  · -- membership: the QTR recurrence applied at the run of `M` zeros starting at `k`.
    have hrun : ∀ y, k ≤ y → y < k + (M : ℕ) → d y = 0 := by
      intro y hy1 hy2
      by_contra hne
      obtain ⟨l, hl, hly⟩ := hmem_pos y (Finsupp.mem_support_iff.mpr hne)
      have hylt : pos.getI l < pos.getI i := by rw [hly]; omega
      have hli : l < i := by
        rcases lt_trichotomy l i with h | h | h
        · exact h
        · subst h; exact absurd hylt (lt_irrefl _)
        · exact absurd (hmono_pos i l h hl) (by omega)
      have hi0 : i ≠ 0 := by rintro rfl; exact absurd hli (Nat.not_lt_zero _)
      have hle : pos.getI l ≤ pos.getI (i-1) := by
        rcases eq_or_lt_of_le (show l ≤ i - 1 by omega) with heq | hlt
        · rw [heq]
        · exact le_of_lt (hmono_pos l (i-1) hlt (by omega))
      have hgap_lb : pos.getI (i-1) + 1 ≤ k := by
        have h := hi; rw [hgapi, if_neg hi0] at h; omega
      omega
    have heq := hx.2.2 m hm d hd_digit hd_sum k hrun
    rw [Function.mem_support]
    unfold qval
    rw [hψ, ← hkM, ← heq]
    exact hq

/-- The length of an iteratively pumped gap vector. -/
lemma foldl_pump_length (g : List ℕ) (steps : List ℕ) (N' : ℕ) :
    (steps.foldl (fun h i => h.set i (h.getI i + N')) g).length = g.length := by
  induction steps generalizing g with
  | nil => rfl
  | cons i rest ih => rw [List.foldl_cons, ih, List.length_set]

/-- Iterated pumping realizes the vector `g + N'·∑ᵢ nᵢ e⁽ⁱ⁾`: coordinate `j` of the pumped vector is
`g_j + N'·(count of j
among the steps)`. -/
lemma foldl_pump_getI (g : List ℕ) (steps : List ℕ) (N' : ℕ)
    (hsteps : ∀ i ∈ steps, i < g.length) (j : ℕ) (hj : j < g.length) :
    (steps.foldl (fun h i => h.set i (h.getI i + N')) g).getI j
      = g.getI j + N' * steps.count j := by
  induction steps generalizing g with
  | nil => simp
  | cons i rest ih =>
    have hi_lt : i < g.length := hsteps i (List.mem_cons_self ..)
    rw [List.foldl_cons, ih _ (fun l hl => by
        rw [List.length_set]; exact hsteps l (List.mem_cons_of_mem _ hl))
      (by rw [List.length_set]; exact hj)]
    rcases eq_or_ne i j with rfl | hne
    · rw [set_getI_self g i _ hi_lt, List.count_cons_self]
      ring
    · rw [set_getI g i _ j hj, if_neg hne, List.count_cons_of_ne hne]

/-- **The pumping lemma**: let `U` be the support
of a QTR function with respect to `(a,b,c,M,N)`, let `m ≥ -b`, let the word
`𝐝` have digits `< p` and digit sum `≤ c`, and let `g ∈ U_{𝐝,m}`. Then for
any finite sequence of insertion steps at gap indices `i` with `g_i ≥ M`
(repetitions allowed), the iteratively pumped gap vector stays in `U_{𝐝,m}`. These are the
zero insertions in the proof of Lemma 3.6. These are the
zero insertions in the proof of Lemma 3.6.
By `foldl_pump_getI`, the result of the steps is exactly
`g + N·∑_{i ∈ J} n_i e⁽ⁱ⁾` where `n_i` is the number of occurrences of `i`
among the steps. -/
theorem gapSet_pump {a : ℕ+} {b c : ℕ} {M N : ℕ+} {x : ℚ → 𝔽ᵃ_[p]}
    (hx : IsQTR x a b c M N) {m : ℤ} (hm : -(b : ℤ) ≤ m)
    {dw : ℕ →₀ ℕ} (hdw : ∀ i, dw i < p) (hdw_sum : (dw.sum fun _ v => v) ≤ c)
    {g : List ℕ} (hg : g ∈ gapSet p a (Function.support x) m dw)
    (steps : List ℕ) (hsteps : ∀ i ∈ steps, (M : ℕ) ≤ g.getI i) :
    steps.foldl (fun h i => h.set i (h.getI i + (N : ℕ))) g
      ∈ gapSet p a (Function.support x) m dw := by
  induction steps generalizing g with
  | nil => exact hg
  | cons i rest ih =>
    have hi : (M : ℕ) ≤ g.getI i := hsteps i (List.mem_cons_self ..)
    have hi_lt : i < g.length := by
      by_contra hcon
      rw [not_lt] at hcon
      rw [List.getI_eq_default _ hcon] at hi
      simp only [Nat.default_eq_zero] at hi
      have := M.pos
      omega
    rw [List.foldl_cons]
    refine ih (gapSet_pump_single hx hm hdw hdw_sum hg hi) ?_
    intro j hj
    have hj_orig : (M : ℕ) ≤ g.getI j := hsteps j (List.mem_cons_of_mem _ hj)
    have hj_lt : j < g.length := by
      by_contra hcon
      rw [not_lt] at hcon
      rw [List.getI_eq_default _ hcon] at hj_orig
      simp only [Nat.default_eq_zero] at hj_orig
      have := M.pos
      omega
    rcases eq_or_ne i j with rfl | hne
    · rw [set_getI_self g i _ hi_lt]
      omega
    · rw [set_getI g i _ j hj_lt, if_neg hne]
      exact hj_orig

/-!
### Realizing a word/gap pair as a digit finsupp

A word/gap pair `(𝐝, g)` encodes the same data as a finitely supported digit sequence. The injective
direction is
`PAdicOrderType.DigitEncoding.finsupp_eq_of_word_gapVector_eq`; here we provide the
constructor direction: `ofWordGap w g` is the digit finsupp whose `j`-th
nonzero digit is `w_j`, placed after `g_j` additional zeros. If all entries of `w` are
nonzero and the two lists have equal lengths, then `word (ofWordGap w g) = w` and
`gapVector (ofWordGap w g) = g`.
-/

/-- The position `pos_j = j + (g_0 + ⋯ + g_j)` of the `j`-th nonzero digit
determined by the gap list `g`, with indices starting at zero.
Beyond `g.length` the function keeps increasing by unit steps, so it is
strictly monotone everywhere. -/
def gapPos (g : List ℕ) (j : ℕ) : ℕ := j + (g.take (j + 1)).sum

/-- Prefix sums step by `getI`: `∑ take (j+1) = ∑ take j + g_j` in range. -/
lemma sum_take_succ_getI (g : List ℕ) (j : ℕ) (hj : j < g.length) :
    (g.take (j + 1)).sum = (g.take j).sum + g.getI j := by
  rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem hj]
  simp [List.getI_eq_getElem _ hj]

lemma strictMono_gapPos (g : List ℕ) : StrictMono (gapPos g) := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold gapPos
  rcases lt_or_ge (j + 1) g.length with h | h
  · rw [sum_take_succ_getI g (j + 1) h]; omega
  · rw [List.take_of_length_le h, List.take_of_length_le (by omega)]; omega

/-- **Realization of a word/gap pair**:
the digit finsupp placing digit `w_j` at position `gapPos g j`. -/
noncomputable def ofWordGap (w g : List ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapDomain (gapPos g) w.toFinsupp

/-- If all entries of `w` are nonzero, the support of `w.toFinsupp` is an
initial range. -/
lemma toFinsupp_support_of_forall_ne_zero (w : List ℕ)
    [DecidablePred (w.getD · 0 ≠ 0)] (hw : ∀ v ∈ w, v ≠ 0) :
    w.toFinsupp.support = Finset.range w.length := by
  rw [List.toFinsupp_support]
  apply Finset.filter_true_of_mem
  intro i hi
  rw [Finset.mem_range] at hi
  rw [List.getD_eq_getElem _ _ hi]
  exact hw _ (List.getElem_mem hi)

/-- The sorted support of `ofWordGap w g` is the list of positions
`gapPos g 0 < gapPos g 1 < ⋯`. -/
lemma support_sort_ofWordGap (w g : List ℕ) (hw : ∀ v ∈ w, v ≠ 0) :
    (ofWordGap w g).support.sort (· ≤ ·)
      = (List.range w.length).map (gapPos g) := by
  unfold ofWordGap
  rw [support_sort_mapDomain _ (strictMono_gapPos g),
    toFinsupp_support_of_forall_ne_zero w hw, Finset.sort_range]

/-- `ofWordGap` realizes the word. -/
theorem word_ofWordGap (w g : List ℕ) (hw : ∀ v ∈ w, v ≠ 0) :
    word (ofWordGap w g) = w := by
  unfold ofWordGap word
  rw [support_sort_mapDomain _ (strictMono_gapPos g),
    toFinsupp_support_of_forall_ne_zero w hw, Finset.sort_range, List.map_map]
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  rw [Finsupp.mapDomain_apply (strictMono_gapPos g).injective]
  exact List.toFinsupp_apply_lt w j h2

/-- `ofWordGap` realizes the gap vector. -/
theorem gapVector_ofWordGap (w g : List ℕ) (hw : ∀ v ∈ w, v ≠ 0)
    (hlen : w.length = g.length) : gapVector (ofWordGap w g) = g := by
  rw [gapVector_eq_gapOfList, support_sort_ofWordGap w g hw, hlen]
  apply List.ext_getElem
  · rw [gapOfList_length, List.length_map, List.length_range]
  · intro j h1 h2
    rw [gapOfList_length, List.length_map, List.length_range] at h1
    rw [← List.getI_eq_getElem _ (by
        rwa [gapOfList_length, List.length_map, List.length_range]),
      ← List.getI_eq_getElem _ h2,
      gapOfList_getI _ j (by rwa [List.length_map, List.length_range]),
      map_getI _ _ _ (by rwa [List.length_range])]
    have hrange : (List.range g.length).getI j = j := by
      rw [List.getI_eq_getElem _ (by rwa [List.length_range]),
        List.getElem_range]
    rw [hrange]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · unfold gapPos
      rw [sum_take_succ_getI g 0 h2]
      simp
    · rw [if_neg (by omega),
        map_getI _ _ _ (by rw [List.length_range]; omega)]
      have hrange' : (List.range g.length).getI (j - 1) = j - 1 := by
        rw [List.getI_eq_getElem _ (by rw [List.length_range]; omega),
          List.getElem_range]
      rw [hrange']
      unfold gapPos
      have hstep : (g.take (j - 1 + 1)).sum + g.getI j = (g.take (j + 1)).sum := by
        rw [show j - 1 + 1 = j by omega] at *
        rw [sum_take_succ_getI g j h2]
      omega

/-- Digits of `ofWordGap w g` are bounded by any bound on the (nonzero)
letters of `w`. -/
lemma ofWordGap_digit_lt (w g : List ℕ) {n : ℕ} (hn : 0 < n)
    (hw : ∀ v ∈ w, v ≠ 0) (hlt : ∀ v ∈ w, v < n) : ∀ i, ofWordGap w g i < n := by
  intro i
  by_cases hi : ofWordGap w g i = 0
  · rw [hi]; exact hn
  · refine hlt _ ?_
    have hmem : ofWordGap w g i ∈ word (ofWordGap w g) :=
      (mem_word _ _).mpr ⟨i, Finsupp.mem_support_iff.mpr hi, rfl⟩
    rwa [word_ofWordGap w g hw] at hmem

/-- Letters of a word are nonzero. -/
lemma word_ne_zero (d : ℕ →₀ ℕ) : ∀ v ∈ word d, v ≠ 0 := by
  intro v hv
  rw [mem_word] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  exact Finsupp.mem_support_iff.mp hi

/-- The word has one letter per nonzero digit. -/
lemma word_length_eq_gapVector_length (d : ℕ →₀ ℕ) :
    (word d).length = (gapVector d).length := by
  rw [gapVector_length]
  unfold word
  rw [List.length_map, Finset.length_sort]

/-- **The coding is a bijection**:
every digit finsupp is the realization of its word/gap pair. -/
theorem ofWordGap_word_gapVector (d : ℕ →₀ ℕ) :
    ofWordGap (word d) (gapVector d) = d :=
  finsupp_eq_of_word_gapVector_eq
    (word_ofWordGap _ _ (word_ne_zero d))
    (gapVector_ofWordGap _ _ (word_ne_zero d) (word_length_eq_gapVector_length d))

omit [Fact (Nat.Prime p)] in
/-- Membership in a gap set, in terms of the canonical realization. -/
theorem mem_gapSet_iff {a : ℕ+} {U : Set ℚ} {m : ℤ} {dw : ℕ →₀ ℕ}
    {g : List ℕ} :
    g ∈ gapSet p a U m dw ↔
      g.length = (word dw).length ∧ qval p a m (ofWordGap (word dw) g) ∈ U := by
  constructor
  · intro hg
    refine ⟨length_of_mem_gapSet hg, ?_⟩
    obtain ⟨d, hword, hgap, hq⟩ := hg
    rw [← hword, ← hgap, ofWordGap_word_gapVector]
    exact hq
  · rintro ⟨hlen, hq⟩
    exact ⟨ofWordGap (word dw) g,
      word_ofWordGap _ _ (word_ne_zero dw),
      gapVector_ofWordGap _ _ (word_ne_zero dw) hlen.symm, hq⟩

/-!
### The coding is injective

Uniqueness of terminating base-`p` expansions, transported from
`PAdicOrderType.DigitSeries` through the bridge
`DigitSeries.ofFinsupp`.
-/

/-- The digit value `0.[𝐝;g] = ∑ᵢ dᵢ p^{-(i+1)}` of a digit finsupp with
digits `< p` lies in `[0,1)`. -/
theorem digitVal_mem_Ico {d : ℕ →₀ ℕ} (hd : ∀ i, d i < p) :
    (d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) ∈ Set.Ico (0 : ℚ) 1 := by
  rw [← DigitSeries.ofFinsupp_norm]
  exact DigitSeries.norm_mem_Ico p _ (DigitSeries.ofFinsupp_isP p d hd)

/-- Terminating base-`p` expansions are unique (digit finsupp form). -/
theorem digitVal_injective {d₁ d₂ : ℕ →₀ ℕ}
    (h₁ : ∀ i, d₁ i < p) (h₂ : ∀ i, d₂ i < p)
    (h : (d₁.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
       = d₂.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) : d₁ = d₂ := by
  exact TrustworthyKedlaya.UP.eq_of_fracVal_eq p (Fact.out : p.Prime).one_lt h₁ h₂ h

/-- **The coding is injective**:
the value `q_m(𝐝, g)` determines the integer part `m` and the digit
finsupp encoding `(𝐝, g)`. -/
theorem eq_of_qval_eq {a : ℕ+} {m₁ m₂ : ℤ} {d₁ d₂ : ℕ →₀ ℕ}
    (h₁ : ∀ i, d₁ i < p) (h₂ : ∀ i, d₂ i < p)
    (h : qval p a m₁ d₁ = qval p a m₂ d₂) : m₁ = m₂ ∧ d₁ = d₂ := by
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast a.ne_zero
  unfold qval at h
  have h' : (m₁ : ℚ) - (d₁.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      = (m₂ : ℚ) - (d₂.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ))) :=
    mul_left_cancel₀ (one_div_ne_zero ha) h
  obtain ⟨hv₁0, hv₁1⟩ := digitVal_mem_Ico h₁
  obtain ⟨hv₂0, hv₂1⟩ := digitVal_mem_Ico h₂
  have hm : m₁ = m₂ := by
    have hcast : ((m₁ - m₂ : ℤ) : ℚ)
        = (d₁.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
          - d₂.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
      push_cast
      linarith
    have hlt : ((m₁ - m₂ : ℤ) : ℚ) < 1 := by rw [hcast]; linarith
    have hgt : (-1 : ℚ) < ((m₁ - m₂ : ℤ) : ℚ) := by rw [hcast]; linarith
    have hlt' : m₁ - m₂ < 1 := by exact_mod_cast hlt
    have hgt' : (-1 : ℤ) < m₁ - m₂ := by exact_mod_cast hgt
    omega
  subst hm
  refine ⟨rfl, digitVal_injective h₁ h₂ ?_⟩
  linarith

/-!
### Comparing digit values at the first differing position

If two digit strings agree strictly below a position `s` and the first has the
larger digit at `s`, its value is strictly larger — regardless of all later
digits (the tail of a proper expansion is `< p^{-(s+1)}`). This is the digit
comparison driving the order-type computation of rays.
-/

omit [Fact (Nat.Prime p)] in
/-- Split a digit value at position `s`: head (positions `< s`), the digit at
`s`, and the tail (positions `> s`). -/
lemma digitVal_split_at (d : ℕ →₀ ℕ) (s : ℕ) :
    (d.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      = (∑ i ∈ d.support.filter (fun i => i < s),
            (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
        + (d s : ℚ) * (p : ℚ) ^ (-(s + 1 : ℤ))
        + ∑ i ∈ d.support.filter (fun i => s < i),
            (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
  classical
  rw [Finsupp.sum, ← Finset.sum_filter_add_sum_filter_not d.support (fun i => i < s),
    add_assoc]
  congr 1
  by_cases hs : s ∈ d.support
  · have hins : d.support.filter (fun i => ¬ i < s)
        = insert s (d.support.filter (fun i => s < i)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert, not_lt]
      constructor
      · rintro ⟨hi, hle⟩
        rcases eq_or_lt_of_le hle with rfl | h
        · exact Or.inl rfl
        · exact Or.inr ⟨hi, h⟩
      · rintro (rfl | ⟨hi, h⟩)
        · exact ⟨hs, le_refl _⟩
        · exact ⟨hi, le_of_lt h⟩
    rw [hins, Finset.sum_insert (by simp)]
  · have hd0 : d s = 0 := Finsupp.notMem_support_iff.mp hs
    have heq : d.support.filter (fun i => ¬ i < s)
        = d.support.filter (fun i => s < i) := by
      ext i
      simp only [Finset.mem_filter, not_lt]
      constructor
      · rintro ⟨hi, hle⟩
        refine ⟨hi, lt_of_le_of_ne hle ?_⟩
        rintro rfl
        exact hs hi
      · rintro ⟨hi, h⟩
        exact ⟨hi, le_of_lt h⟩
    rw [heq, hd0]
    simp

/-- The tail of a proper base-`p` expansion beyond position `s` is
`< p^{-(s+1)}`. -/
lemma digitVal_tail_lt {d : ℕ →₀ ℕ} (hd : ∀ i, d i < p) (s : ℕ) :
    (∑ i ∈ d.support.filter (fun i => s < i),
        (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      < (p : ℚ) ^ (-(s + 1 : ℤ)) := by
  classical
  have hp_pos : (0 : ℚ) < (p : ℚ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hp_ne : (p : ℚ) ≠ 0 := ne_of_gt hp_pos
  set e : ℕ →₀ ℕ :=
    Finsupp.comapDomain (fun j => j + (s + 1)) d ((add_left_injective (s + 1)).injOn)
    with he_def
  have he_apply : ∀ j, e j = d (j + (s + 1)) := fun j =>
    Finsupp.comapDomain_apply _ d _ j
  have he_lt : ∀ j, e j < p := fun j => by rw [he_apply]; exact hd _
  have hval := (digitVal_mem_Ico he_lt).2
  have hkey : (∑ i ∈ d.support.filter (fun i => s < i),
        (d i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      = (p : ℚ) ^ (-(s + 1 : ℤ))
        * (e.sum fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ))) := by
    rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_nbij' (fun i => i - (s + 1)) (fun j => j + (s + 1))
      ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finsupp.mem_support_iff, he_apply,
        Nat.sub_add_cancel (by omega : s + 1 ≤ i)]
      exact Finsupp.mem_support_iff.mp hi.1
    · intro j hj
      rw [Finsupp.mem_support_iff, he_apply] at hj
      rw [Finset.mem_filter]
      exact ⟨Finsupp.mem_support_iff.mpr hj, by omega⟩
    · intro i hi
      rw [Finset.mem_filter] at hi
      omega
    · intro j _
      omega
    · intro i hi
      rw [Finset.mem_filter] at hi
      have hi' : s + 1 ≤ i := by omega
      rw [he_apply, Nat.sub_add_cancel hi', ← mul_assoc,
        mul_comm ((p : ℚ) ^ (-(s + 1 : ℤ))) ((d i : ℚ)), mul_assoc,
        ← zpow_add₀ hp_ne]
      congr 2
      omega
  rw [hkey]
  calc
    (p : ℚ) ^ (-(s + 1 : ℤ))
        * (e.sum fun j v => (v : ℚ) * (p : ℚ) ^ (-(j + 1 : ℤ)))
      < (p : ℚ) ^ (-(s + 1 : ℤ)) * 1 :=
        mul_lt_mul_of_pos_left hval (zpow_pos hp_pos _)
    _ = (p : ℚ) ^ (-(s + 1 : ℤ)) := mul_one _

/-- **First-difference comparison**: if `d₁` and `d₂` agree strictly below `s`
and `d₂ s < d₁ s`, then the value of `d₂` is strictly below the value of `d₁`
(only `d₂` needs proper digits). -/
theorem digitVal_lt_of_eq_below {d₁ d₂ : ℕ →₀ ℕ} {s : ℕ}
    (hd₂ : ∀ i, d₂ i < p) (hagree : ∀ x, x < s → d₁ x = d₂ x)
    (hs : d₂ s < d₁ s) :
    (d₂.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      < d₁.sum fun i v => (v : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
  classical
  have hp_pos : (0 : ℚ) < (p : ℚ) := by
    exact_mod_cast (Fact.out : Nat.Prime p).pos
  rw [digitVal_split_at d₁ s, digitVal_split_at d₂ s]
  have hhead : (∑ i ∈ d₁.support.filter (fun i => i < s),
        (d₁ i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)))
      = ∑ i ∈ d₂.support.filter (fun i => i < s),
          (d₂ i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) := by
    have hsupp : d₁.support.filter (fun i => i < s)
        = d₂.support.filter (fun i => i < s) := by
      ext i
      simp only [Finset.mem_filter, Finsupp.mem_support_iff]
      constructor
      · rintro ⟨hne, hlt⟩
        exact ⟨by rw [← hagree i hlt]; exact hne, hlt⟩
      · rintro ⟨hne, hlt⟩
        exact ⟨by rw [hagree i hlt]; exact hne, hlt⟩
    rw [hsupp]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [hagree i hi.2]
  have htail₂ := digitVal_tail_lt hd₂ s
  have htail₁ : (0 : ℚ) ≤ ∑ i ∈ d₁.support.filter (fun i => s < i),
      (d₁ i : ℚ) * (p : ℚ) ^ (-(i + 1 : ℤ)) :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt (zpow_pos hp_pos _))
  have hmid : ((d₂ s : ℚ) + 1) * (p : ℚ) ^ (-(s + 1 : ℤ))
      ≤ (d₁ s : ℚ) * (p : ℚ) ^ (-(s + 1 : ℤ)) := by
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos hp_pos _))
    exact_mod_cast Nat.succ_le_of_lt hs
  have hexpand : ((d₂ s : ℚ) + 1) * (p : ℚ) ^ (-(s + 1 : ℤ))
      = (d₂ s : ℚ) * (p : ℚ) ^ (-(s + 1 : ℤ)) + (p : ℚ) ^ (-(s + 1 : ℤ)) := by
    ring
  rw [hhead]
  linarith

/-!
### Rays

A ray of dimension `r` is the family of values
`q_m(𝐝, v + N·∑ₕ n_h e^{(i_h)})` over parameters `n ∈ ℕ^r`, for a base gap
vector `v` and active indices `i_1 < ⋯ < i_r` (encoded by a strictly monotone
`idx : Fin r → ℕ`).
-/

/-- The pumped gap vector `v + N·∑ₕ n_h e^{(idx h)}`. -/
def rayGap (v : List ℕ) (N : ℕ) {r : ℕ} (idx : Fin r → ℕ) (n : Fin r → ℕ) :
    List ℕ :=
  v.mapIdx fun j gj => gj + N * ∑ h, if idx h = j then n h else 0

lemma rayGap_length (v : List ℕ) (N : ℕ) {r : ℕ} (idx n : Fin r → ℕ) :
    (rayGap v N idx n).length = v.length :=
  List.length_mapIdx

lemma rayGap_getI (v : List ℕ) (N : ℕ) {r : ℕ} (idx n : Fin r → ℕ)
    {j : ℕ} (hj : j < v.length) :
    (rayGap v N idx n).getI j
      = v.getI j + N * ∑ h, if idx h = j then n h else 0 := by
  rw [List.getI_eq_getElem _ (by rw [rayGap_length]; exact hj),
    List.getI_eq_getElem _ hj]
  exact List.getElem_mapIdx

/-- The pumped gap vector at an active index. -/
lemma rayGap_getI_idx (v : List ℕ) (N : ℕ) {r : ℕ} {idx : Fin r → ℕ}
    (hidx : Function.Injective idx) (n : Fin r → ℕ) (h : Fin r)
    (hj : idx h < v.length) :
    (rayGap v N idx n).getI (idx h) = v.getI (idx h) + N * n h := by
  rw [rayGap_getI v N idx n hj]
  congr 1
  have hcond : ∀ h' : Fin r,
      (if idx h' = idx h then n h' else 0) = if h' = h then n h' else 0 := by
    intro h'
    by_cases hc : h' = h
    · subst hc; simp
    · rw [if_neg (fun hcc => hc (hidx hcc)), if_neg hc]
  rw [Finset.sum_congr rfl fun h' _ => hcond h']
  simp

/-- The pumped gap vector away from the active indices. -/
lemma rayGap_getI_of_ne (v : List ℕ) (N : ℕ) {r : ℕ} {idx : Fin r → ℕ}
    (n : Fin r → ℕ) {j : ℕ} (hj : j < v.length) (hne : ∀ h, idx h ≠ j) :
    (rayGap v N idx n).getI j = v.getI j := by
  rw [rayGap_getI v N idx n hj,
    Finset.sum_eq_zero fun h _ => if_neg (hne h)]
  simp

/-- Prefixes of pumped gap vectors below the first differing active index
agree. -/
lemma rayGap_take_eq (v : List ℕ) (N : ℕ) {r : ℕ} {idx : Fin r → ℕ}
    (hidx : StrictMono idx) {n n' : Fin r → ℕ} {h : Fin r}
    (hagree : ∀ h', h' < h → n h' = n' h') {t : ℕ} (ht : t ≤ idx h) :
    (rayGap v N idx n).take t = (rayGap v N idx n').take t := by
  apply List.ext_getElem (by simp [rayGap_length])
  intro j h1 h2
  have hjt : j < t := by
    rw [List.length_take, rayGap_length] at h1
    omega
  have hjv : j < v.length := by
    rw [List.length_take, rayGap_length] at h1
    omega
  rw [List.getElem_take, List.getElem_take,
    ← List.getI_eq_getElem _ (by rw [rayGap_length]; exact hjv),
    ← List.getI_eq_getElem _ (by rw [rayGap_length]; exact hjv),
    rayGap_getI v N idx n hjv, rayGap_getI v N idx n' hjv]
  congr 2
  refine Finset.sum_congr rfl fun h'' _ => ?_
  by_cases hc : idx h'' = j
  · rw [if_pos hc, if_pos hc, hagree h'' (hidx.lt_iff_lt.mp (by omega))]
  · rw [if_neg hc, if_neg hc]

/-- Equal `take (j+1)` prefixes give equal digit positions. -/
lemma gapPos_congr {g₁ g₂ : List ℕ} {j : ℕ}
    (hj : g₁.take (j + 1) = g₂.take (j + 1)) : gapPos g₁ j = gapPos g₂ j := by
  unfold gapPos
  rw [hj]

/-- Digit positions compare strictly at the first strictly larger gap. -/
lemma gapPos_lt_gapPos {g₁ g₂ : List ℕ} {j : ℕ}
    (hj₁ : j < g₁.length) (hj₂ : j < g₂.length)
    (htake : g₁.take j = g₂.take j) (hlt : g₁.getI j < g₂.getI j) :
    gapPos g₁ j < gapPos g₂ j := by
  unfold gapPos
  rw [sum_take_succ_getI g₁ j hj₁, sum_take_succ_getI g₂ j hj₂, htake]
  omega

/-- `ofWordGap` at a digit position. -/
lemma ofWordGap_apply_gapPos (w g : List ℕ) (j : ℕ) :
    ofWordGap w g (gapPos g j) = w.getD j 0 := by
  unfold ofWordGap
  rw [Finsupp.mapDomain_apply (strictMono_gapPos g).injective]
  rfl

/-- The support of `ofWordGap w g` is the set of digit positions. -/
lemma support_ofWordGap (w g : List ℕ) (hw : ∀ v ∈ w, v ≠ 0) :
    (ofWordGap w g).support = (Finset.range w.length).image (gapPos g) := by
  unfold ofWordGap
  rw [Finsupp.mapDomain_support_of_injective (strictMono_gapPos g).injective,
    toFinsupp_support_of_forall_ne_zero w hw]

/-- `ofWordGap` vanishes away from the digit positions. -/
lemma ofWordGap_apply_eq_zero (w g : List ℕ) (hw : ∀ v ∈ w, v ≠ 0) {x : ℕ}
    (hx : ∀ j, j < w.length → gapPos g j ≠ x) : ofWordGap w g x = 0 := by
  rw [← Finsupp.notMem_support_iff, support_ofWordGap w g hw]
  intro hmem
  obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hmem
  exact hx j (Finset.mem_range.mp hj) hje

/-- **Rays**: the set of values
`q_m(𝐝, v + N·∑ₕ n_h e^{(i_h)})` over all parameters `n ∈ ℕ^r`. -/
def ray (p : ℕ) (a : ℕ+) (m : ℤ) (w v : List ℕ) (N : ℕ) {r : ℕ}
    (idx : Fin r → ℕ) : Set ℚ :=
  Set.range fun n : Fin r → ℕ => qval p a m (ofWordGap w (rayGap v N idx n))

/-- **Strict comparison of ray elements**: a lexicographically smaller
parameter yields a strictly smaller ray element. -/
theorem qval_rayGap_lt {a : ℕ+} {m : ℤ} {w v : List ℕ} {N : ℕ} {r : ℕ}
    {idx : Fin r → ℕ}
    (hw0 : ∀ x ∈ w, x ≠ 0) (hwp : ∀ x ∈ w, x < p) (hlen : w.length = v.length)
    (hidx : StrictMono idx) (hbound : ∀ h, idx h < v.length) (hN : 0 < N)
    {n n' : Fin r → ℕ} {h : Fin r}
    (hagree : ∀ h', h' < h → n h' = n' h') (hh : n h < n' h) :
    qval p a m (ofWordGap w (rayGap v N idx n))
      < qval p a m (ofWordGap w (rayGap v N idx n')) := by
  set g₁ := rayGap v N idx n with hg₁
  set g₂ := rayGap v N idx n' with hg₂
  have hg₁len : g₁.length = v.length := rayGap_length v N idx n
  have hg₂len : g₂.length = v.length := rayGap_length v N idx n'
  set j₀ := idx h with hj₀
  have hj₀v : j₀ < v.length := hbound h
  have hj₀w : j₀ < w.length := by omega
  -- gap prefixes agree strictly below `j₀`, and the `j₀`-th gap grows
  have htake : g₁.take j₀ = g₂.take j₀ := rayGap_take_eq v N hidx hagree le_rfl
  have hentry : g₁.getI j₀ < g₂.getI j₀ := by
    rw [hg₁, hg₂, hj₀, rayGap_getI_idx v N hidx.injective n h (hbound h),
      rayGap_getI_idx v N hidx.injective n' h (hbound h)]
    have := (Nat.mul_lt_mul_left hN).mpr hh
    omega
  set s := gapPos g₁ j₀ with hs_def
  have hs₂ : s < gapPos g₂ j₀ :=
    gapPos_lt_gapPos (by omega) (by omega) htake hentry
  -- digit positions strictly below `j₀` coincide
  have hposeq : ∀ j, j < j₀ → gapPos g₁ j = gapPos g₂ j := by
    intro j hj
    apply gapPos_congr
    have h₁ : g₁.take (j + 1) = (g₁.take j₀).take (j + 1) := by
      rw [List.take_take, min_eq_left (by omega)]
    rw [h₁, htake, List.take_take, min_eq_left (by omega)]
  -- the second string has a zero at position `s`
  have hd₂s : ofWordGap w g₂ s = 0 := by
    apply ofWordGap_apply_eq_zero w g₂ hw0
    intro j hj hje
    rcases lt_or_ge j j₀ with hlt | hge
    · rw [← hposeq j hlt] at hje
      exact absurd ((strictMono_gapPos g₁).injective hje) (by omega)
    · have := (strictMono_gapPos g₂).monotone hge
      omega
  -- the first string has the nonzero digit `w_{j₀}` at position `s`
  have hd₁s : 0 < ofWordGap w g₁ s := by
    rw [hs_def, ofWordGap_apply_gapPos w g₁ j₀]
    refine Nat.pos_of_ne_zero (hw0 _ ?_)
    rw [List.getD_eq_getElem _ _ hj₀w]
    exact List.getElem_mem _
  -- the two strings agree strictly below `s`
  have hagree_digits : ∀ x, x < s → ofWordGap w g₁ x = ofWordGap w g₂ x := by
    intro x hx
    by_cases hx₁ : ofWordGap w g₁ x = 0
    · by_cases hx₂ : ofWordGap w g₂ x = 0
      · rw [hx₁, hx₂]
      · exfalso
        have hmem := Finsupp.mem_support_iff.mpr hx₂
        rw [support_ofWordGap w g₂ hw0] at hmem
        obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hmem
        rw [Finset.mem_range] at hj
        rcases lt_or_ge j j₀ with hlt | hge
        · refine hw0 (w.getD j 0) ?_ ?_
          · rw [List.getD_eq_getElem _ _ hj]
            exact List.getElem_mem _
          · calc
              w.getD j 0
                = ofWordGap w g₁ (gapPos g₁ j) :=
                  (ofWordGap_apply_gapPos w g₁ j).symm
              _ = ofWordGap w g₁ x := by rw [hposeq j hlt, hje]
              _ = 0 := hx₁
        · have := (strictMono_gapPos g₂).monotone hge
          omega
    · have hmem := Finsupp.mem_support_iff.mpr hx₁
      rw [support_ofWordGap w g₁ hw0] at hmem
      obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hmem
      have hjlt : j < j₀ := by
        by_contra hcon
        rw [not_lt] at hcon
        have := (strictMono_gapPos g₁).monotone hcon
        omega
      rw [← hje, ofWordGap_apply_gapPos, hposeq j hjlt, ofWordGap_apply_gapPos]
  -- conclude by the first-difference comparison
  have hd₂p : ∀ i, ofWordGap w g₂ i < p :=
    ofWordGap_digit_lt w g₂ (Fact.out : Nat.Prime p).pos hw0 hwp
  have hcomp := digitVal_lt_of_eq_below (d₁ := ofWordGap w g₁)
    hd₂p hagree_digits (by rw [hd₂s]; exact hd₁s)
  unfold qval
  have ha_pos : (0 : ℚ) < 1 / ((a : ℕ) : ℚ) := by positivity
  apply mul_lt_mul_of_pos_left _ ha_pos
  linarith

/-- **The parameter map of a ray is strictly monotone** from lexicographic
`ℕ^r` (first coordinate most significant) to `ℚ`. This is the order embedding in the proof of
Lemma 3.6. -/
theorem strictMono_rayParam {a : ℕ+} {m : ℤ} {w v : List ℕ} {N : ℕ} {r : ℕ}
    {idx : Fin r → ℕ}
    (hw0 : ∀ x ∈ w, x ≠ 0) (hwp : ∀ x ∈ w, x < p) (hlen : w.length = v.length)
    (hidx : StrictMono idx) (hbound : ∀ h, idx h < v.length) (hN : 0 < N) :
    StrictMono fun n : Lex (Fin r → ℕ) =>
      qval p a m (ofWordGap w (rayGap v N idx (ofLex n))) := by
  intro n n' hlt
  obtain ⟨h, hagree, hh⟩ := hlt
  exact qval_rayGap_lt hw0 hwp hlen hidx hbound hN hagree hh

/-!
### The order type of lexicographic `ℕ^r` is `ω^r`
-/

open Ordinal in
/-- Lexicographic `ℕ^r` (first coordinate most significant) has order type
`ω^r`, as used in the proof of Lemma 3.6. -/
theorem typeLT_lex_pi_fin (r : ℕ) :
    typeLT (Lex (Fin r → ℕ)) = omega0 ^ r := by
  induction r with
  | zero =>
    rw [pow_zero]
    have : Unique (Lex (Fin 0 → ℕ)) := Equiv.unique (toLex (α := Fin 0 → ℕ)).symm
    exact type_eq_one_of_unique _
  | succ r ih =>
    have hwo : IsWellOrder (Fin r → ℕ)
        (Pi.Lex ((· < ·) : Fin r → Fin r → Prop) fun {_} => ((· < ·) : ℕ → ℕ → Prop)) :=
      inferInstanceAs (IsWellOrder (Lex (Fin r → ℕ)) (· < ·))
    have ih' : type (Pi.Lex ((· < ·) : Fin r → Fin r → Prop)
        fun {_} => ((· < ·) : ℕ → ℕ → Prop)) = omega0 ^ r := ih
    have key : typeLT (Lex (Fin (r + 1) → ℕ))
        = type (Prod.Lex ((· < ·) : ℕ → ℕ → Prop)
            (Pi.Lex ((· < ·) : Fin r → Fin r → Prop)
              fun {_} => ((· < ·) : ℕ → ℕ → Prop))) := by
      apply RelIso.ordinalType_congr
      refine ⟨(Fin.consEquiv fun _ => ℕ).symm, ?_⟩
      intro x y
      change Prod.Lex _ _ (x 0, Fin.tail x) (y 0, Fin.tail y)
        ↔ Pi.Lex (· < ·) (fun {_} => (· < ·)) x y
      conv_rhs => rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y]
      rw [Prod.lex_iff, Fin.pi_lex_lt_cons_cons]
    rw [key, type_prod_lex, ih', type_nat_lt, pow_succ]

section
variable {a : ℕ+} {m : ℤ} {w v : List ℕ} {N : ℕ} {r : ℕ} {idx : Fin r → ℕ}

/-- **Order type of a ray**: the
parameter map is an order isomorphism from lexicographic `ℕ^r` onto the
ray. -/
noncomputable def rayOrderIso
    (hw0 : ∀ x ∈ w, x ≠ 0) (hwp : ∀ x ∈ w, x < p) (hlen : w.length = v.length)
    (hidx : StrictMono idx) (hbound : ∀ h, idx h < v.length) (hN : 0 < N) :
    Lex (Fin r → ℕ) ≃o ↥(ray p a m w v N idx) :=
  (strictMono_rayParam hw0 hwp hlen hidx hbound hN).orderIso _

open Ordinal in
/-- **Order type of a ray**: a ray of dimension `r`
has order type `ω^r`. -/
theorem typeLT_ray [WellFoundedLT ↥(ray p a m w v N idx)]
    (hw0 : ∀ x ∈ w, x ≠ 0) (hwp : ∀ x ∈ w, x < p) (hlen : w.length = v.length)
    (hidx : StrictMono idx) (hbound : ∀ h, idx h < v.length) (hN : 0 < N) :
    typeLT ↥(ray p a m w v N idx) = omega0 ^ r :=
  ((rayOrderIso hw0 hwp hlen hidx hbound hN).symm.ordinalType_congr).trans
    (typeLT_lex_pi_fin r)

open Ordinal in
/-- The ordinal lower bound extracted from a ray inside a well-ordered set: if all ray elements lie
in `U`,
then `ω^r ≤ typeLT U`. -/
theorem omega0_pow_le_typeLT_of_ray_subset {U : Set ℚ} [WellFoundedLT ↥U]
    (hw0 : ∀ x ∈ w, x ≠ 0) (hwp : ∀ x ∈ w, x < p) (hlen : w.length = v.length)
    (hidx : StrictMono idx) (hbound : ∀ h, idx h < v.length) (hN : 0 < N)
    (hsub : ray p a m w v N idx ⊆ U) :
    omega0 ^ r ≤ typeLT ↥U := by
  rw [← typeLT_lex_pi_fin r]
  have hmono := strictMono_rayParam (a := a) (m := m) hw0 hwp hlen hidx hbound hN
  refine RelEmbedding.ordinal_type_le
    ⟨⟨fun n => ⟨qval p a m (ofWordGap w (rayGap v N idx (ofLex n))),
      hsub (Set.mem_range_self _)⟩, ?_⟩, ?_⟩
  · intro n n' he
    exact hmono.injective (Subtype.ext_iff.mp he)
  · intro n n'
    exact ⟨fun hlt => hmono.lt_iff_lt.mp hlt, fun hlt => hmono hlt⟩

end

/-!
### Bound on active indices
-/

/-- A pumped gap vector is an iterated single-coordinate pump: `rayGap` is the
`foldl` of `gapSet_pump` over the steps list repeating each active index `idx h`
exactly `n h` times. -/
lemma rayGap_eq_foldl_pump {r : ℕ} (g : List ℕ) (N : ℕ) {idx : Fin r → ℕ}
    (hbound : ∀ h, idx h < g.length) (n : Fin r → ℕ) :
    rayGap g N idx n
      = ((List.ofFn fun h => List.replicate (n h) (idx h)).flatten).foldl
          (fun h i => h.set i (h.getI i + N)) g := by
  set steps := (List.ofFn fun h => List.replicate (n h) (idx h)).flatten
    with hsteps_def
  have hsteps_mem : ∀ i ∈ steps, i < g.length := by
    intro i hi
    rw [hsteps_def, List.mem_flatten] at hi
    obtain ⟨l, hl, hil⟩ := hi
    rw [List.mem_ofFn] at hl
    obtain ⟨h, rfl⟩ := hl
    rw [List.eq_of_mem_replicate hil]
    exact hbound h
  have hcount : ∀ j, steps.count j = ∑ h, if idx h = j then n h else 0 := by
    intro j
    rw [hsteps_def, List.count_flatten, List.map_ofFn, List.sum_ofFn]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Function.comp_apply, List.count_replicate]
    by_cases hc : idx h = j
    · simp [hc]
    · simp [hc]
  apply List.ext_getElem
  · rw [rayGap_length, foldl_pump_length]
  · intro j h1 h2
    have hjg : j < g.length := by rwa [rayGap_length] at h1
    rw [← List.getI_eq_getElem _ h1, ← List.getI_eq_getElem _ h2,
      rayGap_getI g N idx n hjg, foldl_pump_getI g steps N hsteps_mem j hjg,
      hcount j]

open Ordinal in
/-- **Bound on active indices** (the first direction of Lemma 3.6): if the support of a
QTR function has order type `< ω^k`, then every member of a gap set has fewer
than `k` coordinates `≥ M`, that is, fewer than `k` long gaps. -/
theorem card_active_lt {a : ℕ+} {b c : ℕ} {M N : ℕ+} {x : ℚ → 𝔽ᵃ_[p]}
    (hx : IsQTR x a b c M N) [WellFoundedLT ↥(Function.support x)]
    {k : ℕ} (hk : typeLT ↥(Function.support x) < omega0 ^ k)
    {m : ℤ} (hm : -(b : ℤ) ≤ m)
    {dw : ℕ →₀ ℕ} (hdw : ∀ i, dw i < p) (hdw_sum : (dw.sum fun _ v => v) ≤ c)
    {g : List ℕ} (hg : g ∈ gapSet p a (Function.support x) m dw) :
    ((Finset.range g.length).filter fun i => (M : ℕ) ≤ g.getI i).card < k := by
  classical
  set J := (Finset.range g.length).filter fun i => (M : ℕ) ≤ g.getI i with hJ
  set r := J.card with hr
  set e := J.orderIsoOfFin rfl with he
  set idx : Fin r → ℕ := fun h => (e h : ℕ) with hidx_def
  have hidx_mem : ∀ h, idx h ∈ J := fun h => (e h).2
  have hidx_lt : ∀ h, idx h < g.length := fun h => by
    have := hidx_mem h
    rw [hJ, Finset.mem_filter, Finset.mem_range] at this
    exact this.1
  have hidx_M : ∀ h, (M : ℕ) ≤ g.getI (idx h) := fun h => by
    have := hidx_mem h
    rw [hJ, Finset.mem_filter] at this
    exact this.2
  have hidx_mono : StrictMono idx := fun h h' hlt => e.strictMono hlt
  -- word data
  have hw0 : ∀ v ∈ word dw, v ≠ 0 := word_ne_zero dw
  have hwp : ∀ v ∈ word dw, v < p := by
    intro v hv
    rw [mem_word] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact hdw i
  have hlen_g : g.length = (word dw).length := length_of_mem_gapSet hg
  -- the ray through `g` with these active indices lies in the support
  have hsub : ray p a m (word dw) g (N : ℕ) idx ⊆ Function.support x := by
    rintro q ⟨n, rfl⟩
    have hsteps_M : ∀ i ∈ (List.ofFn fun h => List.replicate (n h) (idx h)).flatten,
        (M : ℕ) ≤ g.getI i := by
      intro i hi
      rw [List.mem_flatten] at hi
      obtain ⟨l, hl, hil⟩ := hi
      rw [List.mem_ofFn] at hl
      obtain ⟨h, rfl⟩ := hl
      rw [List.eq_of_mem_replicate hil]
      exact hidx_M h
    have hpump := gapSet_pump hx hm hdw hdw_sum hg _ hsteps_M
    rw [← rayGap_eq_foldl_pump g (N : ℕ) hidx_lt n] at hpump
    exact (mem_gapSet_iff.mp hpump).2
  -- ordinal comparison
  have hray := omega0_pow_le_typeLT_of_ray_subset hw0 hwp hlen_g.symm
    hidx_mono hidx_lt N.pos hsub
  have hlt : omega0 ^ r < omega0 ^ k := lt_of_le_of_lt hray hk
  rw [← opow_natCast, ← opow_natCast] at hlt
  exact_mod_cast (opow_lt_opow_iff_right one_lt_omega0).mp hlt

/-! ### Finite patterns of short and long gaps -/

/-- A gap pattern records each short gap exactly and replaces each long gap by `M`.
There are finitely many patterns of any bounded length. Together with the integer part and
the word, it determines the classes in the proof of Lemma 3.6. -/
def gapPattern (M : ℕ) (g : List ℕ) : List ℕ := g.map (min M)

lemma gapPattern_length (M : ℕ) (g : List ℕ) :
    (gapPattern M g).length = g.length := by simp [gapPattern]

lemma gapPattern_getI (M : ℕ) {g : List ℕ} {i : ℕ} (hi : i < g.length) :
    (gapPattern M g).getI i = min M (g.getI i) := by
  rw [List.getI_eq_getElem _ (by rw [gapPattern_length]; exact hi),
    List.getI_eq_getElem _ hi]
  simp [gapPattern]

lemma gapPattern_entry_lt (M : ℕ) (g : List ℕ) :
    ∀ y ∈ gapPattern M g, y < M + 1 := by
  intro y hy
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy
  exact Nat.lt_succ_of_le (min_le_left _ _)

/-- The **active positions** (entries `≥ M`) of a gap list: the long gaps of
Definition 3.5. -/
def activeFinset (M : ℕ) (v : List ℕ) : Finset ℕ :=
  (Finset.range v.length).filter fun i => M ≤ v.getI i

lemma mem_activeFinset_iff {M : ℕ} {v : List ℕ} {i : ℕ} :
    i ∈ activeFinset M v ↔ i < v.length ∧ M ≤ v.getI i := by
  simp [activeFinset]

/-- **`v + N·ℕ^s`**: the
gap lists obtained from the base list `v` by adding an arbitrary multiple of
`N` at each position in `s` and keeping every other entry. -/
def pumpSet (N : ℕ) (v : List ℕ) (s : Finset ℕ) : Set (List ℕ) :=
  { g | g.length = v.length ∧ (∀ i ∈ s, ∃ n : ℕ, g.getI i = v.getI i + N * n) ∧
      ∀ i < v.length, i ∉ s → g.getI i = v.getI i }

/-- A digit expansion belongs to the class obtained by varying only its long gaps. -/
lemma mem_pumpSet_gapPattern (M : ℕ) (g : List ℕ) :
    g ∈ pumpSet 1 (gapPattern M g) (activeFinset M (gapPattern M g)) := by
  refine ⟨(gapPattern_length M g).symm, ?_, ?_⟩
  · intro i hi
    obtain ⟨hi, hM⟩ := mem_activeFinset_iff.mp hi
    rw [gapPattern_length] at hi
    rw [gapPattern_getI M hi] at hM ⊢
    refine ⟨g.getI i - M, ?_⟩
    omega
  · intro i hi hinactive
    rw [gapPattern_length] at hi
    rw [gapPattern_getI M hi]
    have hM : ¬ M ≤ (gapPattern M g).getI i := by
      intro hM
      exact hinactive (mem_activeFinset_iff.mpr ⟨by rwa [gapPattern_length], hM⟩)
    rw [gapPattern_getI M hi] at hM
    omega

/-- `pumpSet` in ray form: for `s` a set of positions of `v`, the pump set is
the image of the ray parametrization `n ↦ v + N·∑ₕ n_h e^{(s(h))}` over the
increasing enumeration of `s`. -/
theorem pumpSet_eq_range_rayGap {N : ℕ} {v : List ℕ} {s : Finset ℕ}
    (hs : ∀ i ∈ s, i < v.length) :
    pumpSet N v s
      = Set.range fun n : Fin s.card → ℕ =>
          rayGap v N (fun h => (s.orderIsoOfFin rfl h : ℕ)) n := by
  set idx : Fin s.card → ℕ := fun h => (s.orderIsoOfFin rfl h : ℕ) with hidx_def
  have hidx_mem : ∀ h, idx h ∈ s := fun h => (s.orderIsoOfFin rfl h).2
  have hidx_lt : ∀ h, idx h < v.length := fun h => hs _ (hidx_mem h)
  have hidx_inj : Function.Injective idx := fun h h' he => by
    have := (s.orderIsoOfFin rfl).injective (Subtype.ext he)
    exact this
  have hidx_surj : ∀ i ∈ s, ∃ h, idx h = i := fun i hi =>
    ⟨(s.orderIsoOfFin rfl).symm ⟨i, hi⟩,
      congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)⟩
  ext g
  constructor
  · rintro ⟨hlen, hact, hinact⟩
    choose f hf using hact
    refine ⟨fun h => f (idx h) (hidx_mem h), ?_⟩
    apply List.ext_getElem (by rw [rayGap_length]; omega)
    intro j h1 h2
    have hjv : j < v.length := by rwa [rayGap_length] at h1
    rw [← List.getI_eq_getElem _ h1, ← List.getI_eq_getElem _ h2]
    by_cases hj : j ∈ s
    · obtain ⟨h, rfl⟩ := hidx_surj j hj
      rw [rayGap_getI_idx v N hidx_inj _ h (hidx_lt h)]
      exact (hf (idx h) (hidx_mem h)).symm
    · rw [rayGap_getI_of_ne v N _ hjv (fun h he => hj (he ▸ hidx_mem h))]
      exact (hinact j hjv hj).symm
  · rintro ⟨n, rfl⟩
    refine ⟨rayGap_length v N idx n, ?_, ?_⟩
    · intro i hi
      obtain ⟨h, rfl⟩ := hidx_surj i hi
      exact ⟨n h, rayGap_getI_idx v N hidx_inj n h (hidx_lt h)⟩
    · intro i hilen hi
      exact rayGap_getI_of_ne v N n hilen (fun h he => hi (he ▸ hidx_mem h))

/-- Truncating the gaps at `M` preserves exactly the long-gap positions. -/
lemma activeFinset_gapPattern (M : ℕ) (g : List ℕ) :
    activeFinset M (gapPattern M g) = activeFinset M g := by
  ext i
  simp only [mem_activeFinset_iff, gapPattern_length]
  constructor <;> rintro ⟨hi, hM⟩ <;> refine ⟨hi, ?_⟩
  · rw [gapPattern_getI M hi] at hM
    omega
  · rw [gapPattern_getI M hi]
    omega

omit [Fact (Nat.Prime p)] in
/-- A gap-pattern class is parametrized by a ray: the image of a pump set under
`g ↦ q_m(𝐝, g)` is the ray over the increasing enumeration of the pumped
positions. -/
lemma image_qval_pumpSet {a : ℕ+} {m : ℤ} {w : List ℕ} {N : ℕ} {v : List ℕ}
    {s : Finset ℕ} (hs : ∀ i ∈ s, i < v.length) :
    (fun g => qval p a m (ofWordGap w g)) '' pumpSet N v s
      = ray p a m w v N fun h : Fin s.card => (s.orderIsoOfFin rfl h : ℕ) := by
  rw [pumpSet_eq_range_rayGap hs, ← Set.range_comp]
  rfl

/-! ### Tails of digit vectors -/

section Tails

open DigitSeries

/-- The `h`-**tail** of a digit series:
`tail_h(b) = (b_{h+1}, b_{h+2}, …)`, i.e. `tail_h(b)ᵢ = b_{i+h}`. It deletes the first `h`
digits, as in the proof of Lemma 3.8. -/
noncomputable def tailh (b : DigitSeries) (h : ℕ) : DigitSeries :=
  Finsupp.ofSupportFinite (fun i => b (pAdd i h))
    (b.hasFiniteSupport.preimage (pAdd_inj h).injOn)

@[simp] lemma tailh_apply (b : DigitSeries) (h : ℕ) (i : ℕ+) :
    tailh b h i = b (pAdd i h) := rfl

/-- The tail of a proper digit series is proper. -/
lemma tailh_isP {p : ℕ} [Fact (Nat.Prime p)] {b : DigitSeries} (hb : b.IsP p)
    (h : ℕ) : (tailh b h).IsP p := fun i => hb (pAdd i h)

/-- The `h`-head of a digit series: keep the digits at positions `≤ h`. -/
noncomputable def headh (b : DigitSeries) (h : ℕ) : DigitSeries :=
  Finsupp.ofSupportFinite (fun i => if (i : ℕ) ≤ h then b i else 0)
    (b.hasFiniteSupport.subset fun i hi => by
    simp only [Function.mem_support] at hi ⊢
    by_cases hle : (i : ℕ) ≤ h
    · simpa [hle] using hi
    · simp [hle] at hi)

@[simp] lemma headh_apply (b : DigitSeries) (h : ℕ) (i : ℕ+) :
    headh b h i = if (i : ℕ) ≤ h then b i else 0 := rfl

/-- A digit series splits as its `h`-head plus its `h`-tail shifted right by
`h` positions. -/
lemma headh_add_shiftBy_tailh (b : DigitSeries) (h : ℕ) :
    headh b h + shiftBy (tailh b h) h = b := by
  ext q
  change headh b h q + shiftBy (tailh b h) h q = b q
  by_cases hq : (q : ℕ) ≤ h
  · have hz : shiftBy (tailh b h) h q = 0 := by
      by_contra hne
      obtain ⟨i, -, rfl⟩ := (shiftBy_ne_zero_iff _ _ _).mp hne
      rw [pAdd_coe] at hq
      have := i.pos
      omega
    rw [hz, add_zero, headh_apply, if_pos hq]
  · have hqpos : h < (q : ℕ) := Nat.lt_of_not_le hq
    obtain ⟨i, hqi⟩ : ∃ i : ℕ+, pAdd i h = q := by
      refine ⟨⟨(q : ℕ) - h, by omega⟩, ?_⟩
      apply PNat.coe_injective
      change (q : ℕ) - h + h = (q : ℕ)
      omega
    rw [headh_apply, if_neg hq, zero_add, ← hqi, shiftBy_apply_pAdd,
      tailh_apply]

/-- `π_h(b) = ∑_{i=1}^{h} b_i p^{h-i}`. -/
def pih (p : ℕ) (b : DigitSeries) (h : ℕ) : ℕ :=
  ∑ i ∈ indices h, b i * p ^ (h - (i : ℕ))

/-- The head has largest nonzero position at most `h`. -/
lemma maxIndex_headh_le (b : DigitSeries) (h : ℕ) :
    (headh b h).maxIndex ≤ h := by
  refine Finset.sup_le fun i hi => ?_
  rw [Finsupp.mem_support_iff] at hi
  by_contra hgt
  apply hi
  simp only [headh_apply]
  rw [if_neg hgt]

/-- **The tail identity** from the proof of Lemma 3.8:
`p^h · ‖b‖ = π_h(b) + ‖tail_h(b)‖`. -/
theorem pow_mul_norm_eq_pih_add_norm_tailh (p : ℕ) [Fact (Nat.Prime p)]
    (b : DigitSeries) (h : ℕ) :
    (p : ℚ) ^ h * b.norm p = (pih p b h : ℚ) + (tailh b h).norm p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  -- split off the shifted tail
  have hsplit : b.norm p
      = (headh b h).norm p + (tailh b h).norm p * (p : ℚ) ^ (-(h : ℤ)) := by
    conv_lhs => rw [← headh_add_shiftBy_tailh b h]
    rw [map_add, norm_shiftBy]
  -- the head contributes exactly `π_h(b)` after scaling by `p^h`
  have hhead : (p : ℚ) ^ h * (headh b h).norm p = (pih p b h : ℚ) := by
    have hmax : (headh b h).maxIndex < h + 1 :=
      Nat.lt_succ_of_le (maxIndex_headh_le b h)
    rw [norm_eq_sum_indices _ p hmax, indices_succ, Finset.sum_insert (by simp),
      headh_apply, if_neg (by simp), Nat.cast_zero, zero_mul, zero_add,
      Finset.mul_sum, pih, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < h ∧ Nat.succPNat k = i := by
      simpa [indices, eq_comm] using hi
    have hile : ((Nat.succPNat k : ℕ+) : ℕ) ≤ h := by
      simp [Nat.succPNat]
      omega
    rw [headh_apply, if_pos hile, Nat.cast_mul, Nat.cast_pow]
    rw [show ((p : ℚ) ^ h) = (p : ℚ) ^ (h : ℤ) from (zpow_natCast _ h).symm,
      ← mul_assoc, mul_comm ((p : ℚ) ^ (h : ℤ)) _, mul_assoc,
      ← zpow_add₀ hp0]
    congr 1
    rw [show (h : ℤ) + -((Nat.succPNat k : ℕ+) : ℕ) = ((h - (Nat.succPNat k : ℕ+) : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hile]
      ring]
    exact (zpow_natCast _ _).symm
  -- the shifted tail contributes its norm after scaling by `p^h`
  have htail : (p : ℚ) ^ h * ((tailh b h).norm p * (p : ℚ) ^ (-(h : ℤ)))
      = (tailh b h).norm p := by
    rw [mul_comm ((tailh b h).norm p) _, ← mul_assoc,
      show ((p : ℚ) ^ h) = (p : ℚ) ^ (h : ℤ) from (zpow_natCast _ h).symm,
      ← zpow_add₀ hp0]
    simp
  rw [hsplit, mul_add, hhead, htail]

end Tails

/-! ### Coordinates of digit tails -/

section TailBound

open DigitSeries

/-- The `h`-tail of `ofFinsupp dv` at position `q` is the entry of `dv` at the
(0-based) position `q.natPred + h`. -/
lemma tailh_ofFinsupp_apply (dv : ℕ →₀ ℕ) (h : ℕ) (q : ℕ+) :
    tailh (ofFinsupp dv) h q = dv (q.natPred + h) := by
  rw [tailh_apply, ofFinsupp_apply]
  congr 1
  have e1 : (pAdd q h).natPred + 1 = (q : ℕ) + h := by
    rw [PNat.natPred_add_one]
    exact pAdd_coe q h
  have e2 : q.natPred + 1 = (q : ℕ) := PNat.natPred_add_one q
  omega

end TailBound

end PAdicOrderType
