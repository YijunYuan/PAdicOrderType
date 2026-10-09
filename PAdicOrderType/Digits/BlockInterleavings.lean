/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
import PAdicOrderType.Coefficients.CarryFreeCoefficients
import PAdicOrderType.Interleaving.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.PiLex

/-!
# Digit patterns placed in finite blocks

This file defines finite pattern placements (Definition 3.7) and the carry-free coefficient
families used in the polynomial estimate (Proposition 3.1). Interleaving products record
ordered partitions of the occupied blocks.
-/

namespace PAdicOrderType

section Place
variable {s : ℕ}

/-- The rank of a position inside a coordinate block: the number of strictly
smaller elements of the block. -/
def rankIn (S : Finset ℕ+) (pos : ℕ+) : ℕ := (S.filter (· < pos)).card

lemma rankIn_lt_card {S : Finset ℕ+} {pos : ℕ+} (h : pos ∈ S) :
    rankIn S pos < S.card :=
  Finset.card_lt_card ((Finset.filter_subset _ S).ssubset_of_ne fun heq => by
    have := heq ▸ h
    exact absurd (Finset.mem_filter.mp this).2 (lt_irrefl pos))

lemma rankIn_lt_rankIn {S : Finset ℕ+} {pos pos' : ℕ+} (h : pos ∈ S)
    (hlt : pos < pos') : rankIn S pos < rankIn S pos' := by
  refine Finset.card_lt_card ?_
  have hsub : S.filter (· < pos) ⊆ S.filter (· < pos') := fun x hx => by
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, lt_trans hx.2 hlt⟩
  refine (Finset.ssubset_iff_of_subset hsub).mpr
    ⟨pos, Finset.mem_filter.mpr ⟨h, hlt⟩, fun hmem => ?_⟩
  exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl pos)

lemma eq_of_rankIn_eq {S : Finset ℕ+} {pos pos' : ℕ+} (h : pos ∈ S) (h' : pos' ∈ S)
    (heq : rankIn S pos = rankIn S pos') : pos = pos' := by
  rcases lt_trichotomy pos pos' with hlt | hlt | hlt
  · exact absurd heq (rankIn_lt_rankIn h hlt).ne
  · exact hlt
  · exact absurd heq.symm (rankIn_lt_rankIn h' hlt).ne

/-- Ranks are surjective onto `[0, S.card)`. -/
lemma exists_rankIn_eq {S : Finset ℕ+} {t : ℕ} (ht : t < S.card) :
    ∃ pos ∈ S, rankIn S pos = t := by
  classical
  have himage : S.image (rankIn S) = Finset.range S.card := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      obtain ⟨pos, hpos, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (rankIn_lt_card hpos)
    · rw [Finset.card_range, Finset.card_image_of_injOn fun a ha b hb =>
        eq_of_rankIn_eq ha hb]
  obtain ⟨pos, hpos, hrank⟩ := Finset.mem_image.mp
    (himage ▸ Finset.mem_range.mpr ht)
  exact ⟨pos, hpos, hrank⟩

/-- Place a letter, a digit pattern of length `s` in the sense of Definition 3.7 (1), along a
finite coordinate block in increasing order of position, as in Definition 3.7 (3).
The intended case is `S.card = s`; if the sizes differ, only positions whose rank is below
`s` receive a digit, and unused letter entries are ignored. -/
noncomputable def placeAt (S : Finset ℕ+) (c : Fin s → ℕ) : ℕ+ →₀ ℕ :=
  Finsupp.onFinset S
    (fun pos => if h : pos ∈ S ∧ rankIn S pos < s then c ⟨rankIn S pos, h.2⟩ else 0)
    (fun pos h => by
      by_contra hpos
      exact h (dif_neg fun hc => hpos hc.1))

lemma placeAt_apply (S : Finset ℕ+) (c : Fin s → ℕ) (pos : ℕ+) :
    placeAt S c pos =
      if h : pos ∈ S ∧ rankIn S pos < s then c ⟨rankIn S pos, h.2⟩ else 0 :=
  Finsupp.onFinset_apply

lemma placeAt_apply_of_mem {S : Finset ℕ+} {pos : ℕ+} (h : pos ∈ S)
    (hr : rankIn S pos < s) (c : Fin s → ℕ) :
    placeAt S c pos = c ⟨rankIn S pos, hr⟩ := by
  rw [placeAt_apply, dif_pos ⟨h, hr⟩]

@[simp] lemma placeAt_apply_of_notMem {S : Finset ℕ+} {pos : ℕ+} (h : pos ∉ S)
    (c : Fin s → ℕ) : placeAt S c pos = 0 := by
  rw [placeAt_apply, dif_neg fun hc => h hc.1]

lemma support_placeAt_subset {S : Finset ℕ+} {c : Fin s → ℕ} :
    (placeAt S c).support ⊆ S := Finsupp.support_onFinset_subset

/-- Digits of a placement are digits of the letter (or zero). -/
lemma placeAt_lt {c : Fin s → ℕ} {P : ℕ} (hP : 0 < P) (hc : ∀ t, c t < P)
    (S : Finset ℕ+) (pos : ℕ+) : placeAt S c pos < P := by
  rw [placeAt_apply]
  by_cases h : pos ∈ S ∧ rankIn S pos < s
  · rw [dif_pos h]
    exact hc _
  · rw [dif_neg h]
    exact hP

/-- The placement of a nonzero letter at a block of the right size is
nonzero. -/
lemma placeAt_ne_zero {S : Finset ℕ+} (hS : S.card = s) {c : Fin s → ℕ}
    (hc : c ≠ 0) : placeAt S c ≠ 0 := by
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hc
  have htcard : (t : ℕ) < S.card := by rw [hS]; exact t.2
  obtain ⟨pos, hpos, hrank⟩ := exists_rankIn_eq htcard
  have hr : rankIn S pos < s := by rw [hrank]; exact t.2
  intro heq
  have h := placeAt_apply_of_mem hpos hr c
  rw [heq, Finsupp.coe_zero, Pi.zero_apply] at h
  refine ht ?_
  have hft : (⟨rankIn S pos, hr⟩ : Fin s) = t := Fin.ext hrank
  rw [← hft]
  exact h.symm

end Place

section Blocks
variable {s : ℕ} (B : ℕ → Finset ℕ+)

/-- Place successive letters at the blocks indexed by `l` and add the digit vectors.
If the lists have different lengths, only their common prefix contributes. For a word `z` on
the first `|z|` blocks, this is the digit vector `u_z` defined before Lemma 3.14. -/
noncomputable def placeList : List (Fin s → ℕ) → List ℕ → (ℕ+ →₀ ℕ)
  | [], _ => 0
  | _ :: _, [] => 0
  | c :: w, i :: l => placeAt (B i) c + placeList w l

@[simp] lemma placeList_nil (l : List ℕ) :
    placeList B ([] : List (Fin s → ℕ)) l = 0 := by
  cases l <;> rfl

@[simp] lemma placeList_cons_cons (c : Fin s → ℕ) (w : List (Fin s → ℕ))
    (i : ℕ) (l : List ℕ) :
    placeList B (c :: w) (i :: l) = placeAt (B i) c + placeList B w l := rfl

/-- Positions outside all the indexed blocks carry no digit. -/
lemma placeList_apply_eq_zero : ∀ (w : List (Fin s → ℕ)) (l : List ℕ) {pos : ℕ+},
    (∀ j ∈ l, pos ∉ B j) → placeList B w l pos = 0 := by
  intro w
  induction w with
  | nil => intro l pos _; rw [placeList_nil]; rfl
  | cons c w ih =>
    intro l pos hpos
    cases l with
    | nil => rfl
    | cons i l =>
      rw [placeList_cons_cons, Finsupp.add_apply,
        placeAt_apply_of_notMem (hpos i (List.mem_cons_self ..)) c,
        ih l fun j hj => hpos j (List.mem_cons_of_mem i hj)]

variable {B}
variable (hdisj : ∀ ⦃i j : ℕ⦄, i ≠ j → Disjoint (B i) (B j))
  (hcard : ∀ i, (B i).card = s)

include hcard in
/-- Every index of a placement list contributes to the support: at a block
of a nonzero letter, the placed word has a nonzero digit. -/
lemma exists_apply_ne_zero_of_mem :
    ∀ (w : List (Fin s → ℕ)) (l : List ℕ), (∀ e ∈ w, e ≠ 0) →
      l.length = w.length → ∀ j ∈ l, ∃ pos ∈ B j, placeList B w l pos ≠ 0 := by
  intro w
  induction w with
  | nil => intro l _ hlen j hj; rw [List.length_nil, List.length_eq_zero_iff] at hlen
           subst hlen; exact absurd hj (List.not_mem_nil)
  | cons c w ih =>
    intro l hw hlen j hj
    cases l with
    | nil => simp at hlen
    | cons i l =>
      rw [List.length_cons, List.length_cons, Nat.add_right_cancel_iff] at hlen
      rcases List.mem_cons.mp hj with rfl | hj'
      · -- the head block: the head letter is placed there.
        have hc : c ≠ 0 := hw c (List.mem_cons_self ..)
        obtain ⟨pos, hpos⟩ := Finsupp.ne_iff.mp (placeAt_ne_zero (hcard j) hc)
        refine ⟨pos, support_placeAt_subset (Finsupp.mem_support_iff.mpr hpos), ?_⟩
        rw [placeList_cons_cons, Finsupp.add_apply]
        exact fun h => hpos (Nat.eq_zero_of_add_eq_zero_right h)
      · -- a tail block: use the inductive hypothesis.
        obtain ⟨pos, hpos, hval⟩ :=
          ih l (fun e he => hw e (List.mem_cons_of_mem c he)) hlen j hj'
        refine ⟨pos, hpos, ?_⟩
        rw [placeList_cons_cons, Finsupp.add_apply]
        exact fun h => hval (Nat.eq_zero_of_add_eq_zero_left h)

include hdisj in
/-- Placements of words with digits `< P` along pairwise increasing block
indices have all digits `< P`: the blocks are disjoint, so no position
receives more than one letter digit. -/
lemma placeList_lt {P : ℕ} (hP : 0 < P) :
    ∀ (w : List (Fin s → ℕ)) (l : List ℕ), (∀ c ∈ w, ∀ t, c t < P) →
      l.Pairwise (· < ·) → ∀ pos, placeList B w l pos < P := by
  intro w
  induction w with
  | nil =>
    intro l _ _ pos
    rw [placeList_nil]
    exact hP
  | cons c w ih =>
    intro l hw hl pos
    cases l with
    | nil => exact hP
    | cons i l' =>
      rw [placeList_cons_cons, Finsupp.add_apply]
      by_cases hpos : pos ∈ B i
      · have htail : placeList B w l' pos = 0 :=
          placeList_apply_eq_zero B w l' fun j hj =>
            Finset.disjoint_left.mp
              (hdisj (Nat.ne_of_lt ((List.pairwise_cons.mp hl).1 j hj))) hpos
        rw [htail, Nat.add_zero]
        exact placeAt_lt hP (hw c (List.mem_cons_self ..)) (B i) pos
      · rw [placeAt_apply_of_notMem hpos, Nat.zero_add]
        exact ih l' (fun c' hc' => hw c' (List.mem_cons_of_mem c hc'))
          (List.pairwise_cons.mp hl).2 pos

/-- Placement along re-indexed blocks is placement along the mapped index
list. -/
lemma placeList_comp (B : ℕ → Finset ℕ+) (y : ℕ → ℕ) :
    ∀ (w : List (Fin s → ℕ)) (l : List ℕ),
      placeList (fun j => B (y j)) w l = placeList B w (l.map y) := by
  intro w
  induction w with
  | nil =>
    intro l
    rw [placeList_nil, placeList_nil]
  | cons e w ih =>
    intro l
    cases l with
    | nil => rfl
    | cons i l' =>
      rw [List.map_cons, placeList_cons_cons, placeList_cons_cons, ih]

end Blocks

section ProperDigits
variable {p : ℕ} [Fact (Nat.Prime p)]

/-- A digit vector dominated by a proper one is proper. -/
lemma isP_of_le {v : DigitSeries} (hv : v.IsP p) {x : ℕ+ →₀ ℕ}
    (hx : x ≤ v) : DigitSeries.IsP (x) p := fun i =>
  lt_of_le_of_lt (Finsupp.le_def.mp hx i) (hv i)

end ProperDigits

/-- Lexicographic order on finite digit patterns. -/
local instance letterLinearOrder {s : ℕ} : LinearOrder (Fin s → ℕ) :=
  LinearOrder.lift' (fun c => List.ofFn c) fun _ _ h => List.ofFn_inj.mp h

section InterleavingSupport
variable (K : Type*) [CommRing K] {s : ℕ}

lemma interleavingPower_support_letters {P : (Fin s → ℕ) → Prop}
    {f : (List (Fin s → ℕ)) →₀ K} (hf : ∀ w ∈ f.support, ∀ e ∈ w, P e) :
    ∀ n, ∀ w ∈ (interleavingPower K f n).support, ∀ e ∈ w, P e := by
  intro n
  induction n with
  | zero =>
    intro w hw
    rw [interleavingPower] at hw
    have h1 := Finsupp.support_single_subset hw
    rw [Finset.mem_singleton] at h1
    subst h1
    intro e he
    exact absurd he (List.not_mem_nil)
  | succ n ih =>
    intro w hw
    rw [interleavingPower] at hw
    obtain ⟨u, hu, v, hv, hmem⟩ := exists_mem_shuffles_of_mem_support_interleavingProduct K hw
    intro e he
    rcases mem_of_mem_of_mem_shuffles u v w hmem e he with h | h
    · exact ih u hu e h
    · exact hf v hv e h

end InterleavingSupport

section HDDef

variable (p : ℕ) [Fact (Nat.Prime p)] {K : Type*} [CommRing K]

open Classical in
/-- The coefficient family attached to
a set `D` of digit vectors and a coefficient function `A`:
the coefficient at a proper `u` is `A u` if `u ∈ D` and `0` otherwise. For the coefficients
`A_d` of (3.2), its `n`-th carry-free power has coefficient `S_n(u)` from (3.4) at `u`. -/
noncomputable def coefficientFamily (D : Set DigitSeries) (A : DigitSeries → K) :
    DigitCoefficients p K :=
  fun u => if u.1 ∈ D then A u.1 else 0

open Classical in
lemma coefficientFamily_apply (D : Set DigitSeries) (A : DigitSeries → K)
    (u : {d : DigitSeries // d.IsP p}) :
    coefficientFamily p D A u = if u.1 ∈ D then A u.1 else 0 := rfl

end HDDef

section Words

variable {s : ℕ}

/-- All words of length `r` over a list `L` of letters. -/
def wordsOfLen (L : List (Fin s → ℕ)) : ℕ → List (List (Fin s → ℕ))
  | 0 => [[]]
  | r + 1 => L.flatMap fun e => (wordsOfLen L r).map (e :: ·)

lemma mem_wordsOfLen {L : List (Fin s → ℕ)} :
    ∀ {r : ℕ} {w : List (Fin s → ℕ)}, w.length = r → (∀ e ∈ w, e ∈ L) →
      w ∈ wordsOfLen L r := by
  intro r
  induction r with
  | zero =>
    intro w hlen _
    rw [List.length_eq_zero_iff] at hlen
    subst hlen
    exact List.mem_singleton.mpr rfl
  | succ r ih =>
    intro w hlen hmem
    cases w with
    | nil => simp at hlen
    | cons e w' =>
      rw [wordsOfLen, List.mem_flatMap]
      refine ⟨e, hmem e (List.mem_cons_self ..), List.mem_map.mpr ⟨w', ?_, rfl⟩⟩
      refine ih ?_ fun e' he' => hmem e' (List.mem_cons_of_mem e he')
      rw [List.length_cons] at hlen
      omega

end Words

end PAdicOrderType
