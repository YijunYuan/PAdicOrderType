/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Digits.WordGapGeometry

/-!
# QTR invariance on separated digit blocks

The insertion rule first extends to all proper digit vectors: outside the
slice or digit-sum bounds, both coefficients vanish. Iterating the rule then
moves any finite word of patterns from consecutive arithmetic blocks to any
increasing selection of blocks, while preserving an arbitrary earlier prefix.

`PAdicOrderType.qtr_arithmeticPlacement` gives the resulting invariance on arithmetic blocks.
These are the successive zero insertions in the proof of Lemma 3.12.
-/

namespace PAdicOrderType

open TrustworthyKedlaya

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The support conditions of QTR apply to every nonzero digit coefficient. -/
lemma qtr_bounds_of_coeff_ne_zero {a : ℕ+} {b c : ℕ} {M N : ℕ+}
    {x : ℚ → 𝔽ᵃ_[p]} (hx : IsQTR x a b c M N) (m : ℤ)
    (d : ℕ →₀ ℕ) (hd : ∀ i, d i < p) (hne : x (qval p a m d) ≠ 0) :
    -(b : ℤ) ≤ m ∧ d.sum (fun _ v => v) ≤ c := by
  obtain ⟨m', e, hm', he, hsum, hq⟩ := hx.2.1 hne
  obtain ⟨rfl, rfl⟩ := eq_of_qval_eq hd he hq
  exact ⟨hm', hsum⟩

/-- Insert `t` zero digits at position `k`, shifting all positions at least `k`
to the right by `t`, as in Definition 2.5 (2). -/
noncomputable def digitShift (k t : ℕ) (d : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapDomain (fun i => if i < k then i else i + t) d

lemma digitShift_zero (k : ℕ) (d : ℕ →₀ ℕ) : digitShift k 0 d = d := by
  unfold digitShift
  simp only [Nat.add_zero, ite_self]
  exact Finsupp.mapDomain_id

lemma digitShift_lt {k t : ℕ} {d : ℕ →₀ ℕ} (hd : ∀ i, d i < p) :
    ∀ i, digitShift k t d i < p :=
  QTR.shift_mapDomain_lt (Fact.out : Nat.Prime p).pos k t d hd

lemma digitShift_apply_lt {k t i : ℕ} (hi : i < k) (d : ℕ →₀ ℕ) :
    digitShift k t d i = d i := by
  have heq : (if i < k then i else i + t) = i := if_pos hi
  conv_lhs => rw [← heq]
  exact Finsupp.mapDomain_apply (QTR.shift_injective k t) _ _

lemma digitShift_add (k t u : ℕ) (d : ℕ →₀ ℕ) :
    digitShift k u (digitShift k t d) = digitShift k (t + u) d := by
  unfold digitShift
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro i _
  by_cases hi : i < k
  · simp [hi]
  · simp [hi, show ¬i + t < k by omega, Nat.add_assoc]

/-- QTR insertion preserves coefficients even outside the prescribed digit-sum bound, where
both coefficients vanish. This covers the case `Ψ(e*) > c` in the proof of Lemma 3.12. -/
lemma qtr_coeff_digitShift {a : ℕ+} {b c : ℕ} {M N : ℕ+}
    {x : ℚ → 𝔽ᵃ_[p]} (hx : IsQTR x a b c M N) (m : ℤ)
    (d : ℕ →₀ ℕ) (hd : ∀ i, d i < p) {k : ℕ} (hk : (M : ℕ) ≤ k)
    (hgap : ∀ i, k - (M : ℕ) ≤ i → i < k → d i = 0) :
    x (qval p a m d) = x (qval p a m (digitShift k N d)) := by
  classical
  have hsum : (digitShift k N d).sum (fun _ v => v) = d.sum (fun _ v => v) :=
    QTR.shift_mapDomain_sum k N d
  by_cases hgood : -(b : ℤ) ≤ m ∧ d.sum (fun _ v => v) ≤ c
  · have h := hx.2.2 m hgood.1 d hd hgood.2 (k - M) (by
      intro i hi hik
      exact hgap i hi (by omega))
    simpa only [Nat.sub_add_cancel hk, qval, digitShift] using h
  · have h0 : x (qval p a m d) = 0 := by
      by_contra hn
      exact hgood (qtr_bounds_of_coeff_ne_zero hx m d hd hn)
    have h1 : x (qval p a m (digitShift k N d)) = 0 := by
      by_contra hn
      have hb := qtr_bounds_of_coeff_ne_zero hx m _ (digitShift_lt hd) hn
      rw [hsum] at hb
      exact hgood hb
    rw [h0, h1]

/-- Any multiple of the QTR period may be inserted into a long zero gap. -/
lemma qtr_coeff_digitShift_mul {a : ℕ+} {b c : ℕ} {M N : ℕ+}
    {x : ℚ → 𝔽ᵃ_[p]} (hx : IsQTR x a b c M N) (m : ℤ)
    (d : ℕ →₀ ℕ) (hd : ∀ i, d i < p) {k : ℕ} (hk : (M : ℕ) ≤ k)
    (hgap : ∀ i, k - (M : ℕ) ≤ i → i < k → d i = 0) (t : ℕ) :
    x (qval p a m d) = x (qval p a m (digitShift k ((N : ℕ) * t) d)) := by
  induction t with
  | zero => simp [digitShift_zero]
  | succ t ih =>
      have h := qtr_coeff_digitShift hx m (digitShift k ((N : ℕ) * t) d)
        (digitShift_lt hd) hk (by
          intro i hi hik
          rw [digitShift_apply_lt hik]
          exact hgap i hi hik)
      rw [digitShift_add, ← Nat.mul_succ] at h
      exact ih.trans h

/-- A finite digit pattern beginning at a zero-based digit position. -/
noncomputable def patternAt {s : ℕ} (start : ℕ) (a : Fin s → ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapDomain (fun i : Fin s => start + i) (Finsupp.equivFunOnFinite.symm a)

lemma patternAt_apply {s : ℕ} (start : ℕ) (a : Fin s → ℕ) (i : Fin s) :
    patternAt start a (start + i) = a i := by
  exact Finsupp.mapDomain_apply (fun i j hij => Fin.ext (by omega)) _ _

lemma patternAt_eq_zero {s start i : ℕ} (a : Fin s → ℕ)
    (hi : i < start ∨ start + s ≤ i) : patternAt start a i = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨j, rfl⟩
  have := j.isLt
  dsimp at hi
  omega

lemma patternAt_lt {s : ℕ} (start : ℕ) (a : Fin s → ℕ) (ha : ∀ i, a i < p) :
    ∀ i, patternAt start a i < p := by
  intro i
  by_cases hi : start ≤ i ∧ i < start + s
  · have he : i = start + (⟨i - start, by omega⟩ : Fin s) := by simp; omega
    rw [he, patternAt_apply]
    exact ha _
  · rw [patternAt_eq_zero a (by omega)]
    exact (Fact.out : Nat.Prime p).pos

lemma digitShift_patternAt {s k t start : ℕ} (hstart : k ≤ start) (a : Fin s → ℕ) :
    digitShift k t (patternAt start a) = patternAt (start + t) a := by
  unfold digitShift patternAt
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro i _
  simp only [Function.comp_apply, if_neg (by omega : ¬start + (i : ℕ) < k)]
  omega

lemma digitShift_prefix {k t : ℕ} (d : ℕ →₀ ℕ) (hd : ∀ i, k ≤ i → d i = 0) :
    digitShift k t d = d := by
  unfold digitShift
  have h : Finsupp.mapDomain (fun i => if i < k then i else i + t) d =
      Finsupp.mapDomain id d := by
    apply Finsupp.mapDomain_congr
    intro i hi
    have : i < k := by
      by_contra hik
      exact (Finsupp.mem_support_iff.mp hi) (hd i (by omega))
    simp [this]
  rw [h, Finsupp.mapDomain_id]

/-- Place successive patterns at positions `lo + Δ * j` for the indices `j` in
the second list. If the lists differ in length, only their common prefix contributes. -/
noncomputable def arithmeticPlacement {s : ℕ} (lo Δ : ℕ) :
    List (Fin s → ℕ) → List ℕ → (ℕ →₀ ℕ)
  | a :: w, j :: l => patternAt (lo + Δ * j) a + arithmeticPlacement lo Δ w l
  | _, _ => 0

lemma arithmeticPlacement_nil {s : ℕ} (lo Δ : ℕ) (l : List ℕ) :
    arithmeticPlacement lo Δ ([] : List (Fin s → ℕ)) l = 0 := by cases l <;> rfl

lemma arithmeticPlacement_eq_zero {s : ℕ} (lo Δ : ℕ) (w : List (Fin s → ℕ))
    (l : List ℕ) {i : ℕ} (hi : i < lo) : arithmeticPlacement lo Δ w l i = 0 := by
  induction w generalizing l with
  | nil => rw [arithmeticPlacement_nil]; rfl
  | cons a w ih =>
      cases l with
      | nil => rfl
      | cons j l =>
          change patternAt (lo + Δ * j) a i + arithmeticPlacement lo Δ w l i = 0
          rw [patternAt_eq_zero a (Or.inl (by omega)), ih l]

lemma digitShift_arithmeticPlacement {s : ℕ} {k lo Δ t : ℕ} (hk : k ≤ lo)
    (w : List (Fin s → ℕ)) (l : List ℕ) :
    digitShift k t (arithmeticPlacement lo Δ w l) =
      arithmeticPlacement (lo + t) Δ w l := by
  induction w generalizing l with
  | nil => simp [arithmeticPlacement_nil, digitShift]
  | cons a w ih =>
      cases l with
      | nil => simp [arithmeticPlacement, digitShift]
      | cons j l =>
          change digitShift k t (patternAt (lo + Δ * j) a + arithmeticPlacement lo Δ w l) = _
          rw [digitShift, Finsupp.mapDomain_add]
          change digitShift k t (patternAt (lo + Δ * j) a) +
            digitShift k t (arithmeticPlacement lo Δ w l) = _
          rw [digitShift_patternAt (by omega), ih]
          change patternAt (lo + Δ * j + t) a + arithmeticPlacement (lo + t) Δ w l =
            patternAt (lo + t+Δ * j) a + arithmeticPlacement (lo + t) Δ w l
          rw [show lo + Δ * j + t = lo + t + Δ * j by omega]

/-- Translating all digit positions translates the start of the arithmetic blocks. -/
lemma arithmeticPlacement_shift {s : ℕ} (lo Δ h : ℕ)
    (w : List (Fin s → ℕ)) (l : List ℕ) :
    Finsupp.mapDomain (fun i => i + h) (arithmeticPlacement lo Δ w l) =
      arithmeticPlacement (lo + h) Δ w l := by
  simpa only [digitShift, Nat.not_lt_zero, ite_false] using
    digitShift_arithmeticPlacement (k := 0) (t := h) (Nat.zero_le lo) w l

lemma arithmeticPlacement_map_add {s : ℕ} (lo Δ k : ℕ) (w : List (Fin s → ℕ))
    (l : List ℕ) : arithmeticPlacement lo Δ w (l.map (fun j => j + k)) =
      arithmeticPlacement (lo + Δ * k) Δ w l := by
  induction w generalizing l with
  | nil => simp [arithmeticPlacement_nil]
  | cons a w ih =>
      cases l with
      | nil => rfl
      | cons j l =>
          simp only [List.map_cons, arithmeticPlacement, ih]
          congr 2
          ring

lemma arithmeticPlacement_eq_zero_of_forall {s : ℕ} (lo Δ : ℕ)
    (w : List (Fin s → ℕ)) (l : List ℕ) {i : ℕ}
    (hi : ∀ j ∈ l, i < lo + Δ * j) : arithmeticPlacement lo Δ w l i = 0 := by
  induction w generalizing l with
  | nil => simp [arithmeticPlacement_nil]
  | cons a w ih =>
      cases l with
      | nil => rfl
      | cons j l =>
          change patternAt (lo + Δ * j) a i + arithmeticPlacement lo Δ w l i = 0
          rw [patternAt_eq_zero a (Or.inl (hi j (by simp))),
            ih l (fun k hk => hi k (by simp [hk]))]

lemma arithmeticPlacement_lt {s lo Δ : ℕ} (hΔ : s ≤ Δ)
    (w : List (Fin s → ℕ)) (hw : ∀ a ∈ w, ∀ i, a i < p)
    (l : List ℕ) (hl : l.Pairwise (· < ·)) :
    ∀ i, arithmeticPlacement lo Δ w l i < p := by
  induction w generalizing l with
  | nil => simp only [arithmeticPlacement_nil, Finsupp.zero_apply]; exact fun _ =>
      (Fact.out : Nat.Prime p).pos
  | cons a w ih =>
      cases l with
      | nil => exact fun _ => (Fact.out : Nat.Prime p).pos
      | cons j l =>
          obtain ⟨hjl, hl⟩ := List.pairwise_cons.mp hl
          intro i
          change patternAt (lo + Δ * j) a i + arithmeticPlacement lo Δ w l i < p
          by_cases hi : i < lo + Δ * (j + 1)
          · rw [arithmeticPlacement_eq_zero_of_forall lo Δ w l (by
              intro k hk
              exact hi.trans_le (Nat.add_le_add_left
                (Nat.mul_le_mul_left Δ (hjl k hk)) lo)), Nat.add_zero]
            exact patternAt_lt _ _ (hw a (by simp)) i
          · rw [patternAt_eq_zero a (Or.inr (by
              rw [Nat.mul_add, Nat.mul_one] at hi
              omega)), Nat.zero_add]
            exact ih (fun e he => hw e (by simp [he])) l hl i

lemma prefix_arithmeticPlacement_lt {s lo Δ : ℕ} (hΔ : s ≤ Δ)
    (head : ℕ →₀ ℕ) (hpref : ∀ i, head i < p)
    (hz : ∀ i, lo ≤ i → head i = 0)
    (w : List (Fin s → ℕ)) (hw : ∀ a ∈ w, ∀ i, a i < p)
    (l : List ℕ) (hl : l.Pairwise (· < ·)) :
    ∀ i, (head + arithmeticPlacement lo Δ w l) i < p := by
  intro i
  rw [Finsupp.add_apply]
  by_cases hi : i < lo
  · rw [arithmeticPlacement_eq_zero lo Δ w l hi, Nat.add_zero]
    exact hpref i
  · rw [hz i (by omega), Nat.zero_add]
    exact arithmeticPlacement_lt hΔ w hw l hl i

/-- QTR coefficients of separated patterns depend only on their ordered patterns. This is
the QTR step in the proof of Lemma 3.12. -/
theorem qtr_arithmeticPlacement {a : ℕ+} {b c : ℕ} {M N : ℕ+}
    {x : ℚ → 𝔽ᵃ_[p]} (hx : IsQTR x a b c M N) (m : ℤ)
    {s lo Δ : ℕ} (hlo : (M : ℕ) ≤ lo) (hΔ : s + (M : ℕ) ≤ Δ)
    (hdiv : (N : ℕ) ∣ Δ) (head : ℕ →₀ ℕ) (hhead : ∀ i, head i < p)
    (hzero : ∀ i, lo - (M : ℕ) ≤ i → head i = 0)
    (w : List (Fin s → ℕ)) (hw : ∀ a ∈ w, ∀ i, a i < p)
    (l : List ℕ) (hl : l.Pairwise (· < ·)) (hlen : l.length = w.length) :
    x (qval p a m (head + arithmeticPlacement lo Δ w (List.range w.length))) =
      x (qval p a m (head + arithmeticPlacement lo Δ w l)) := by
  classical
  induction w generalizing head lo l with
  | nil => simp [arithmeticPlacement_nil]
  | cons e w ih =>
      cases l with
      | nil => simp at hlen
      | cons j l =>
          obtain ⟨hjl, hl⟩ := List.pairwise_cons.mp hl
          have hlen' : l.length = w.length := by simpa using hlen
          have he : ∀ i, e i < p := hw e (by simp)
          have hw' : ∀ e ∈ w, ∀ i, e i < p := fun e he => hw e (by simp [he])
          have hbase : ∀ i,
              (head + arithmeticPlacement lo Δ (e :: w) (List.range (e :: w).length)) i < p :=
            prefix_arithmeticPlacement_lt (by omega) head hhead
              (fun i hi => hzero i (by omega)) (e :: w) hw _ List.pairwise_lt_range
          obtain ⟨Q, hQ⟩ := hdiv
          have hshift := qtr_coeff_digitShift_mul hx m _ hbase hlo (by
            intro i hi hik
            rw [Finsupp.add_apply, hzero i hi,
              arithmeticPlacement_eq_zero lo Δ (e :: w) _ hik]) (Q * j)
          have hperiod : (N : ℕ) * (Q * j) = Δ * j := by rw [hQ]; ring
          rw [hperiod, digitShift, Finsupp.mapDomain_add] at hshift
          change x (qval p a m _) = x (qval p a m
            (digitShift lo (Δ * j) head +
              digitShift lo (Δ * j) (arithmeticPlacement lo Δ (e :: w) _))) at hshift
          rw [digitShift_prefix head (fun i hi => hzero i (by omega)),
            digitShift_arithmeticPlacement le_rfl] at hshift
          have hstd : arithmeticPlacement (lo + Δ * j) Δ (e :: w) (List.range (e :: w).length) =
              patternAt (lo + Δ * j) e +
                arithmeticPlacement (lo + Δ * (j + 1)) Δ w (List.range w.length) := by
            rw [List.length_cons, List.range_succ_eq_map]
            simp only [arithmeticPlacement, Nat.mul_zero, Nat.add_zero]
            rw [show Nat.succ = (fun z : ℕ => z + 1) from rfl,
              arithmeticPlacement_map_add]
            congr 2
            ring
          rw [hstd, ← add_assoc] at hshift
          let head' := head + patternAt (lo + Δ * j) e
          let l' := l.map (fun k => k - (j + 1))
          have hnewlo : (M : ℕ) ≤ lo + Δ * (j + 1) := by omega
          have hhead' : ∀ i, head' i < p := by
            intro i
            change head i + patternAt (lo + Δ * j) e i < p
            by_cases hi : i < lo
            · rw [patternAt_eq_zero e (Or.inl (by omega)), Nat.add_zero]
              exact hhead i
            · rw [hzero i (by omega), Nat.zero_add]
              exact patternAt_lt _ _ he i
          have hzero' : ∀ i, lo + Δ * (j + 1)-(M : ℕ) ≤ i → head' i = 0 := by
            intro i hi
            change head i + patternAt (lo + Δ * j) e i = 0
            have hj : lo + Δ * j+s ≤ i := by
              rw [Nat.mul_add, Nat.mul_one] at hi
              omega
            rw [hzero i (by omega), patternAt_eq_zero e (Or.inr hj)]
          have hl' : l'.Pairwise (· < ·) := by
            rw [List.pairwise_map]
            exact (List.pairwise_iff_getElem.mp hl |> fun h =>
              List.pairwise_iff_getElem.mpr (by
                intro u v hu hv huv
                have hku := hjl _ (List.getElem_mem hu)
                have hkv := hjl _ (List.getElem_mem hv)
                have hlt := h u v hu hv huv
                omega))
          have hlen'' : l'.length = w.length := by simp [l', hlen']
          have hi := ih hnewlo head' hhead' hzero' hw' l' hl' hlen''
          have htarget : arithmeticPlacement (lo + Δ * (j + 1)) Δ w l' =
              arithmeticPlacement lo Δ w l := by
            rw [← arithmeticPlacement_map_add]
            congr 1
            apply List.ext_getElem
            · simp [l']
            · intro i hi1 hi2
              simp only [l', List.getElem_map]
              have := hjl _ (List.getElem_mem hi2)
              omega
          rw [htarget] at hi
          exact hshift.trans (by simpa only [head', arithmeticPlacement, add_assoc] using hi)

end PAdicOrderType
