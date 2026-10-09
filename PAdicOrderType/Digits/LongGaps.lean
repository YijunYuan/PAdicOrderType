/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.OrderType.FiniteUnion

/-!
# Long zero gaps and order type

This file proves the long-gap criterion, Lemma 3.6. The upper order bound only needs finitely
many patterns: record the integer slice, the nonzero digit word, and each gap truncated at `M`.
A pattern with `d` long gaps embeds into lexicographic `ℕ^d`; these are the classes in the
proof of Lemma 3.6. No decomposition of QTR sets into disjoint rays is needed. The opposite
bound follows by inserting zeros independently into long gaps.
-/

namespace PAdicOrderType

open PAdicOrderType.DigitEncoding Ordinal

lemma word_length_le_digit_sum (d : ℕ →₀ ℕ) :
    (word d).length ≤ d.sum fun _ v => v := by
  unfold word
  rw [List.length_map, Finset.length_sort, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun i hi =>
    Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

/-- A bounded digit set with fewer than `k` long gaps at every point has order
type below `ω^k`. The set need not satisfy any recurrence. This is the converse direction
in the proof of Lemma 3.6. -/
theorem typeLT_lt_omega0_pow_of_longGaps {p : ℕ} [Fact (Nat.Prime p)]
    {a : ℕ+} {c M k : ℕ} {U : Set ℚ} [WellFoundedLT ↥U] {m₁ m₂ : ℤ}
    (hsub : U ⊆ ⋃ m ∈ Set.Icc m₁ m₂, Sabc_m p a c m)
    (hgaps : ∀ (m : ℤ) (d : ℕ →₀ ℕ), (∀ i, d i < p) →
      (d.sum fun _ v => v) ≤ c → qval p a m d ∈ U →
      (activeFinset M (gapVector d)).card < k) :
    typeLT ↥U < omega0 ^ k := by
  classical
  have hchoice : ∀ q ∈ U, ∃ md : ℤ × (ℕ →₀ ℕ),
      md.1 ∈ Set.Icc m₁ m₂ ∧ (∀ i, md.2 i < p) ∧
      (md.2.sum fun _ v => v) ≤ c ∧ q = qval p a md.1 md.2 := by
    intro q hq
    obtain ⟨m, hm, d, hd, hsum, heq⟩ := Set.mem_iUnion₂.mp (hsub hq)
    exact ⟨(m, d), hm, hd, hsum, heq⟩
  choose! md hm hd hsum hq using hchoice
  let code : ℚ → ℤ × List ℕ × List ℕ := fun q =>
    ((md q).1, word (md q).2, gapPattern M (gapVector (md q).2))
  let D := code '' U
  have hDfin : D.Finite := by
    refine ((Set.finite_Icc m₁ m₂).prod
      ((finite_bounded_lists c p).prod (finite_bounded_lists c (M + 1)))).subset ?_
    rintro _ ⟨q, hqU, rfl⟩
    refine ⟨hm q hqU, ⟨(word_length_le_digit_sum _).trans (hsum q hqU), ?_⟩, ?_,
      gapPattern_entry_lt M _⟩
    · intro y hy
      obtain ⟨i, _, rfl⟩ := (mem_word _ _).mp hy
      exact hd q hqU i
    · rw [gapPattern_length, ← word_length_eq_gapVector_length]
      exact (word_length_le_digit_sum _).trans (hsum q hqU)
  have hD : ∀ z ∈ D, (∀ y ∈ z.2.1, y ≠ 0 ∧ y < p) ∧
      z.2.1.length = z.2.2.length ∧ (activeFinset M z.2.2).card < k := by
    rintro _ ⟨q, hqU, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro y hy
      refine ⟨word_ne_zero _ y hy, ?_⟩
      obtain ⟨i, _, rfl⟩ := (mem_word _ _).mp hy
      exact hd q hqU i
    · exact (word_length_eq_gapVector_length _).trans (gapPattern_length _ _).symm
    · change (activeFinset M (gapPattern M (gapVector (md q).2))).card < k
      rw [activeFinset_gapPattern]
      exact hgaps _ _ (hd q hqU) (hsum q hqU) ((hq q hqU) ▸ hqU)
  let piece : (ℤ × List ℕ × List ℕ) → Set ℚ := fun z =>
    (fun g => qval p a z.1 (ofWordGap z.2.1 g)) ''
      pumpSet 1 z.2.2 (activeFinset M z.2.2)
  have hcover : ∀ q ∈ U, q ∈ piece (code q) := by
    intro q hqU
    refine ⟨gapVector (md q).2, ?_, ?_⟩
    · exact mem_pumpSet_gapPattern M _
    · simpa only [code, ofWordGap_word_gapVector] using (hq q hqU).symm
  have : Finite ↥D := hDfin.to_subtype
  let P : ↥D → Set ℚ := fun z => U ∩ piece z
  have hU : U = ⋃ z, P z := by
    ext q
    constructor
    · intro hqU
      exact Set.mem_iUnion.mpr ⟨⟨code q, Set.mem_image_of_mem _ hqU⟩, hqU, hcover q hqU⟩
    · intro h
      obtain ⟨z, hz⟩ := Set.mem_iUnion.mp h
      exact hz.1
  have : ∀ z, WellFoundedLT ↥(P z) := fun _ => wellFoundedLT_of_subset Set.inter_subset_left
  apply typeLT_lt_omega0_pow_of_iUnion hU
  intro z
  obtain ⟨hw, hlen, hcard⟩ := hD z z.2
  let s := activeFinset M z.1.2.2
  let idx : Fin s.card → ℕ := fun i => (s.orderIsoOfFin rfl i : ℕ)
  have hs : ∀ i ∈ s, i < z.1.2.2.length := fun i hi => (mem_activeFinset_iff.mp hi).1
  have hmono : StrictMono idx := (s.orderIsoOfFin rfl).strictMono
  have hbound : ∀ i, idx i < z.1.2.2.length := fun i => hs _ (s.orderIsoOfFin rfl i).2
  have heq : piece z = ray p a z.1.1 z.1.2.1 z.1.2.2 1 idx := image_qval_pumpSet hs
  have : WellFoundedLT ↥(ray p a z.1.1 z.1.2.1 z.1.2.2 1 idx) :=
    (rayOrderIso (fun y hy => (hw y hy).1) (fun y hy => (hw y hy).2)
      hlen hmono hbound (by omega)).symm.strictMono.wellFoundedLT
  have hle : typeLT ↥(P z) ≤ omega0 ^ s.card := by
    rw [← typeLT_ray (a := a) (m := z.1.1) (N := 1) (idx := idx)
      (fun y hy => (hw y hy).1) (fun y hy => (hw y hy).2)
      hlen hmono hbound (by omega)]
    apply typeLT_le_of_subset
    rw [← heq]
    exact Set.inter_subset_right
  apply hle.trans_lt
  rw [← opow_natCast, ← opow_natCast]
  exact (opow_lt_opow_iff_right one_lt_omega0).mpr (by exact_mod_cast hcard)

/-- **Long-gap criterion** (Lemma 3.6): for bounded QTR support, the order type is below
`ω ^ k` if and only if every support point has fewer than `k` zero gaps of length at least
`M`. -/
theorem typeLT_support_lt_iff_longGaps {p : ℕ} [Fact (Nat.Prime p)]
    {a : ℕ+} {b c : ℕ} {M N : ℕ+} {x : ℚ → 𝔽ᵃ_[p]}
    (hx : IsQTR x a b c M N) [WellFoundedLT ↥(Function.support x)]
    {m₁ m₂ : ℤ} (hm₁ : -(b : ℤ) ≤ m₁)
    (hsub : Function.support x ⊆ ⋃ m ∈ Set.Icc m₁ m₂, Sabc_m p a c m) {k : ℕ} :
    typeLT ↥(Function.support x) < omega0 ^ k ↔
      ∀ (m : ℤ) (d : ℕ →₀ ℕ), (∀ i, d i < p) → (d.sum fun _ v => v) ≤ c →
        qval p a m d ∈ Function.support x → (activeFinset M (gapVector d)).card < k := by
  constructor
  · intro hk m d hd hsum hmem
    obtain ⟨m', hm', d', hd', _, heq⟩ := Set.mem_iUnion₂.mp (hsub hmem)
    have hmm := (eq_of_qval_eq hd hd' heq).1
    exact card_active_lt hx hk (hmm ▸ hm₁.trans hm'.1) hd hsum
      (show gapVector d ∈ gapSet p a (Function.support x) m d from
        ⟨d, rfl, rfl, hmem⟩)
  · exact typeLT_lt_omega0_pow_of_longGaps hsub

/-- A truncation of order type at least `ω^r` contains a point with exactly `r`
long gaps when the whole QTR support has order type below `ω^(r+1)`. This is the consequence
stated in Lemma 3.6, applied as in the proof of Lemma 3.9. -/
theorem exists_point_card_longGaps_eq {p : ℕ} [Fact (Nat.Prime p)]
    {a : ℕ+} {b c : ℕ} {M N : ℕ+} {x : ℚ → 𝔽ᵃ_[p]}
    (hx : IsQTR x a b c M N) [WellFoundedLT ↥(Function.support x)]
    {m₁ m₂ : ℤ} (hm₁ : -(b : ℤ) ≤ m₁)
    (hsub : Function.support x ⊆ ⋃ m ∈ Set.Icc m₁ m₂, Sabc_m p a c m)
    {r : ℕ} (hV : typeLT ↥(Function.support x) < omega0 ^ (r + 1))
    {U : Set ℚ} [WellFoundedLT ↥U] (hUV : U ⊆ Function.support x)
    (hU : omega0 ^ r ≤ typeLT ↥U) :
    ∃ (m : ℤ) (d : ℕ →₀ ℕ), -(b : ℤ) ≤ m ∧ (∀ i, d i < p) ∧
      (d.sum fun _ v => v) ≤ c ∧ qval p a m d ∈ U ∧
      (activeFinset M (gapVector d)).card = r := by
  classical
  by_contra hcon
  apply not_lt_of_ge hU
  apply typeLT_lt_omega0_pow_of_longGaps (M := (M : ℕ)) (hUV.trans hsub)
  intro m d hd hsum hmem
  obtain ⟨m', hm', d', hd', _, heq⟩ := Set.mem_iUnion₂.mp (hsub (hUV hmem))
  have hmm := (eq_of_qval_eq hd hd' heq).1
  have hm : -(b : ℤ) ≤ m := hmm ▸ hm₁.trans hm'.1
  have hcard := (typeLT_support_lt_iff_longGaps hx hm₁ hsub).mp hV m d hd hsum (hUV hmem)
  have hne : (activeFinset M (gapVector d)).card ≠ r :=
    fun he => hcon ⟨m, d, hm, hd, hsum, hmem, he⟩
  omega

end PAdicOrderType
