/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Interleaving.Basic

/-!
# Nonvanishing of interleaving powers in characteristic zero

Replacing a word by a lexicographically larger word of the same length strictly
increases the output with the same interleaving positions. Hence a maximal
interleaving of the largest input words receives contributions only from those
words. Its coefficient is their product times a positive integer. This is the lexicographic
argument in the proof of Lemma 3.15.
-/

namespace PAdicOrderType

/-- Interleaving powers preserve the prescribed total length. -/
theorem length_eq_of_mem_support_pow {K L : Type*} [CommRing K] [DecidableEq L]
    {G : List L →₀ K} {r : ℕ}
    (hlen : ∀ w ∈ G.support, w.length = r) (n : ℕ) :
    ∀ w ∈ (interleavingPower K G n).support, w.length = n * r := by
  induction n with
  | zero =>
    intro w hw
    rw [interleavingPower] at hw
    have hw' : w = [] := Finset.mem_singleton.mp (Finsupp.support_single_subset hw)
    rw [hw', List.length_nil, zero_mul]
  | succ n ih =>
    intro w hw
    rw [interleavingPower] at hw
    obtain ⟨u, hu, v, hv, hmem⟩ := exists_mem_shuffles_of_mem_support_interleavingProduct K hw
    rw [length_of_mem_shuffles u v w hmem, ih u hu, hlen v hv]
    simp [Nat.add_mul]

section Words

variable {L : Type*}

lemma append_mem_shuffles (u v : List L) : u ++ v ∈ shuffles u v := by
  induction u with
  | nil => simp
  | cons a u ih =>
    cases v with
    | nil => simp
    | cons b v =>
      rw [shuffles_cons_cons, Multiset.mem_add]
      exact Or.inl (Multiset.mem_map.mpr ⟨u ++ b :: v, ih, rfl⟩)

lemma shuffles_comm (u v : List L) : shuffles u v = shuffles v u := by
  induction u, v using shuffles.induct with
  | case1 v => simp
  | case2 a u => simp
  | case3 a u b v ih₁ ih₂ =>
    rw [shuffles_cons_cons, shuffles_cons_cons, ih₁, ih₂, add_comm]

variable [LinearOrder L]

/-- Increasing one factor strictly increases every interleaving when the same
positions are used for the replacement. -/
lemma exists_larger_shuffle_left (u v : List L) :
    ∀ {u' : List L}, u.length = u'.length → u < u' →
      ∀ z ∈ shuffles u v, ∃ z' ∈ shuffles u' v, z < z' := by
  induction u, v using shuffles.induct with
  | case1 v =>
    intro u' hlen hlt
    have : u' = [] := List.length_eq_zero_iff.mp hlen.symm
    subst u'
    exact (lt_irrefl _ hlt).elim
  | case2 a u =>
    intro u' _ hlt z hz
    rw [shuffles_nil_right, Multiset.mem_singleton] at hz
    exact ⟨u', by simp, hz ▸ hlt⟩
  | case3 a u b v ih₁ ih₂ =>
    intro u' hlen hlt z hz
    cases u' with
    | nil => simp at hlen
    | cons a' u' =>
      rw [shuffles_cons_cons, Multiset.mem_add] at hz
      rcases hz with hz | hz
      · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hz
        cases hlt with
        | rel haa' =>
          refine ⟨a' :: (u' ++ b :: v), ?_, List.Lex.rel haa'⟩
          rw [shuffles_cons_cons, Multiset.mem_add]
          exact Or.inl (Multiset.mem_map.mpr ⟨_, append_mem_shuffles _ _, rfl⟩)
        | cons huu' =>
          obtain ⟨z', hz', hzz'⟩ := ih₁ (by simpa using hlen) huu' t ht
          refine ⟨a :: z', ?_, List.Lex.cons hzz'⟩
          rw [shuffles_cons_cons, Multiset.mem_add]
          exact Or.inl (Multiset.mem_map.mpr ⟨z', hz', rfl⟩)
      · obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hz
        obtain ⟨z', hz', hzz'⟩ := ih₂ hlen hlt t ht
        refine ⟨b :: z', ?_, List.Lex.cons hzz'⟩
        rw [shuffles_cons_cons, Multiset.mem_add]
        exact Or.inr (Multiset.mem_map.mpr ⟨z', hz', rfl⟩)

lemma exists_larger_shuffle_right {u v v' z : List L}
    (hlen : v.length = v'.length) (hlt : v < v') (hz : z ∈ shuffles u v) :
    ∃ z' ∈ shuffles u v', z < z' := by
  rw [shuffles_comm] at hz ⊢
  exact exists_larger_shuffle_left v u hlen hlt z hz

lemma exists_ge_shuffle_right {u v v' z : List L}
    (hlen : v.length = v'.length) (hle : v ≤ v') (hz : z ∈ shuffles u v) :
    ∃ z' ∈ shuffles u v', z ≤ z' := by
  rcases hle.eq_or_lt with rfl | hlt
  · exact ⟨z, hz, le_rfl⟩
  · obtain ⟨z', hz', hzz'⟩ := exists_larger_shuffle_right hlen hlt hz
    exact ⟨z', hz', hzz'.le⟩

end Words

section Coefficients

variable {K L : Type*} [Field K] [CharZero K] [LinearOrder L] [DecidableEq L]

/-- Homogeneous nonzero word families have a nonzero interleaving product. -/
theorem interleavingProduct_ne_zero {f g : List L →₀ K} {r s : ℕ}
    (hf_len : ∀ w ∈ f.support, w.length = r)
    (hg_len : ∀ w ∈ g.support, w.length = s) (hf : f ≠ 0) (hg : g ≠ 0) :
    interleavingProduct K f g ≠ 0 := by
  classical
  obtain ⟨u₀, hu₀, humax⟩ := f.support.exists_max_image id (Finsupp.support_nonempty_iff.mpr hf)
  obtain ⟨v₀, hv₀, hvmax⟩ := g.support.exists_max_image id (Finsupp.support_nonempty_iff.mpr hg)
  have hsh : (shuffles u₀ v₀).toFinset.Nonempty :=
    ⟨u₀ ++ v₀, Multiset.mem_toFinset.mpr (append_mem_shuffles _ _)⟩
  obtain ⟨z, hz, hzmax⟩ := (shuffles u₀ v₀).toFinset.exists_max_image id hsh
  have hzmem : z ∈ shuffles u₀ v₀ := Multiset.mem_toFinset.mp hz
  have honly : ∀ u ∈ f.support, ∀ v ∈ g.support, z ∈ shuffles u v → u = u₀ ∧ v = v₀ := by
    intro u hu v hv hzuv
    have huu : u ≤ u₀ := humax u hu
    have hvv : v ≤ v₀ := hvmax v hv
    have hulen : u.length = u₀.length := (hf_len u hu).trans (hf_len u₀ hu₀).symm
    have hvlen : v.length = v₀.length := (hg_len v hv).trans (hg_len v₀ hv₀).symm
    have hueq : u = u₀ := by
      by_contra hne
      obtain ⟨z', hz', hzz'⟩ := exists_larger_shuffle_left u v hulen (lt_of_le_of_ne huu hne) z hzuv
      obtain ⟨z'', hz'', hzz''⟩ := exists_ge_shuffle_right hvlen hvv hz'
      exact not_lt_of_ge (hzmax z'' (Multiset.mem_toFinset.mpr hz'')) (hzz'.trans_le hzz'')
    subst u
    refine ⟨rfl, ?_⟩
    by_contra hne
    obtain ⟨z', hz', hzz'⟩ := exists_larger_shuffle_right hvlen (lt_of_le_of_ne hvv hne) hzuv
    exact not_lt_of_ge (hzmax z' (Multiset.mem_toFinset.mpr hz')) hzz'
  have hcoeff : interleavingProduct K f g z =
      f u₀ * g v₀ * ((shuffles u₀ v₀).count z : K) := by
    rw [interleavingProduct_apply, Finset.sum_eq_single_of_mem u₀ hu₀]
    · apply Finset.sum_eq_single_of_mem v₀ hv₀
      intro v hv hne
      have hzv : z ∉ shuffles u₀ v := fun h => hne (honly u₀ hu₀ v hv h).2
      simp [Multiset.count_eq_zero.mpr hzv]
    · intro u hu hne
      apply Finset.sum_eq_zero
      intro v hv
      have hzu : z ∉ shuffles u v := fun h => hne (honly u hu v hv h).1
      simp [Multiset.count_eq_zero.mpr hzu]
  intro hzero
  have hnonzero : f u₀ * g v₀ * ((shuffles u₀ v₀).count z : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Finsupp.mem_support_iff.mp hu₀) (Finsupp.mem_support_iff.mp hv₀))
      (Nat.cast_ne_zero.mpr (Multiset.count_ne_zero.mpr hzmem))
  apply hnonzero
  rw [← hcoeff, hzero, Finsupp.zero_apply]

end Coefficients

section Powers

variable {K L : Type*} [Field K] [DecidableEq L]

/-- A nonzero homogeneous family remains nonzero under every interleaving power. This is the
lexicographic argument in the proof of Lemma 3.15. -/
theorem interleavingPower_ne_zero [CharZero K] [LinearOrder L]
    {f : List L →₀ K} {r : ℕ} (hlen : ∀ w ∈ f.support, w.length = r)
    (hf : f ≠ 0) (n : ℕ) : interleavingPower K f n ≠ 0 := by
  induction n with
  | zero => simp [interleavingPower]
  | succ n ih =>
    change interleavingProduct K (interleavingPower K f n) f ≠ 0
    exact interleavingProduct_ne_zero (length_eq_of_mem_support_pow hlen n) hlen ih hf

end Powers

end PAdicOrderType
