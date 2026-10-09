/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Interleaving.Basic

/-!
# Ordered partitions of word positions

The interleaving coefficient is the sum over ordered partitions of a word's
positions into its two input subsequences, with multiplicities preserved. These are the
ordered partitions realizing interleavings in Definition 3.13.
-/

namespace PAdicOrderType

/-- Ordered partitions of the positions of a word into two subsequences. -/
def unshuffles {L : Type*} : List L → Multiset (List L × List L)
  | [] => {([], [])}
  | a :: w => (unshuffles w).map (fun uv => (a :: uv.1, uv.2)) +
      (unshuffles w).map (fun uv => (uv.1, a :: uv.2))

lemma unshuffles_lengths {L : Type*} {w u v : List L} (h : (u, v) ∈ unshuffles w) :
    u.length + v.length = w.length := by
  induction w generalizing u v with
  | nil => simpa [unshuffles] using h
  | cons a w ih =>
    simp only [unshuffles, Multiset.mem_add, Multiset.mem_map] at h
    rcases h with ⟨⟨u', v'⟩, h, heq⟩ | ⟨⟨u', v'⟩, h, heq⟩
    · cases heq
      simp only [List.length_cons]
      have := ih h
      omega
    · cases heq
      simp only [List.length_cons]
      have := ih h
      omega

private lemma count_map_left_cons {L : Type*} [DecidableEq L]
    (S : Multiset (List L × List L)) (a : L) (u v : List L) :
    ((S.map fun uv => (a :: uv.1, uv.2)).count (u, v)) =
      match u with
      | [] => 0
      | b :: u => if b = a then S.count (u, v) else 0 := by
  cases u with
  | nil => simp
  | cons b u =>
    by_cases h : b = a
    · subst b
      simpa using Multiset.count_map_eq_count' (fun uv : List L × List L => (a :: uv.1, uv.2))
        S (by
          intro x y h
          simpa only [Prod.mk.injEq, List.cons.injEq, true_and, Prod.ext_iff] using h)
        (u, v)
    · simp [Multiset.count_map, h]

private lemma count_map_right_cons {L : Type*} [DecidableEq L]
    (S : Multiset (List L × List L)) (a : L) (u v : List L) :
    ((S.map fun uv => (uv.1, a :: uv.2)).count (u, v)) =
      match v with
      | [] => 0
      | b :: v => if b = a then S.count (u, v) else 0 := by
  cases v with
  | nil => simp
  | cons b v =>
    by_cases h : b = a
    · subst b
      simpa using Multiset.count_map_eq_count' (fun uv : List L × List L => (uv.1, a :: uv.2))
        S (by
          intro x y h
          simpa only [Prod.mk.injEq, List.cons.injEq, true_and, Prod.ext_iff] using h)
        (u, v)
    · simp [Multiset.count_map, h]

private lemma count_map_cons {L : Type*} [DecidableEq L]
    (S : Multiset (List L)) (a b : L) (w : List L) :
    ((S.map (List.cons a)).count (b :: w)) = if b = a then S.count w else 0 := by
  by_cases h : b = a
  · subst b
    simpa using Multiset.count_map_eq_count' (List.cons a) S List.cons_injective w
  · simp [Multiset.count_map, h]

/-- Partitioning a fixed word and interleaving two fixed subwords count the same
ways to assign its positions. -/
lemma unshuffles_count {L : Type*} [DecidableEq L] (w u v : List L) :
    (unshuffles w).count (u, v) = (shuffles u v).count w := by
  induction w generalizing u v with
  | nil => cases u <;> cases v <;> simp [unshuffles]
  | cons a w ih =>
    cases u with
    | nil =>
      cases v with
      | nil => simp [unshuffles]
      | cons b v =>
        rw [unshuffles, Multiset.count_add, count_map_left_cons, count_map_right_cons]
        by_cases h : b = a
        · subst b
          simpa [ih] using (Multiset.count_map_eq_count' (List.cons a)
            (shuffles [] v) List.cons_injective w).symm
        · simp [h, Ne.symm h]
    | cons b u =>
      cases v with
      | nil =>
        rw [unshuffles, Multiset.count_add, count_map_left_cons, count_map_right_cons]
        by_cases h : b = a
        · subst b
          simpa [ih] using (Multiset.count_map_eq_count' (List.cons a)
            (shuffles u []) List.cons_injective w).symm
        · simp [h, Ne.symm h]
      | cons c v =>
        rw [unshuffles, Multiset.count_add, count_map_left_cons, count_map_right_cons,
          shuffles_cons_cons, Multiset.count_add, count_map_cons, count_map_cons]
        simp only [ih, eq_comm]

/-- Interleaving coefficients are finite sums over ordered partitions of the
positions of the output word. -/
theorem interleavingProduct_eq_unshuffles {L K : Type*} [DecidableEq L] [Semiring K]
    (f g : (List L) →₀ K) (w : List L) :
    interleavingProduct K f g w =
      ((unshuffles w).map (fun uv => f uv.1 * g uv.2)).sum := by
  classical
  rw [interleavingProduct_apply]
  simp only [← unshuffles_count]
  rw [← Finset.sum_product f.support g.support
    (fun uv : List L × List L => f uv.1 * g uv.2 * ((unshuffles w).count uv : K))]
  rw [Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]
  let F : List L × List L → K := fun uv =>
    f uv.1 * g uv.2 * ((unshuffles w).count uv : K)
  change (∑ uv ∈ f.support ×ˢ g.support, F uv) = _
  calc
    _ = ∑ uv ∈ (unshuffles w).toFinset ∪ (f.support ×ˢ g.support), F uv := by
      apply Finset.sum_subset Finset.subset_union_right
      intro uv _ huv
      have hmissing : uv.1 ∉ f.support ∨ uv.2 ∉ g.support := by
        simpa only [Finset.mem_product, not_and_or] using huv
      rcases hmissing with hf | hg
      · simp [F, Finsupp.notMem_support_iff.mp hf]
      · simp [F, Finsupp.notMem_support_iff.mp hg]
    _ = ∑ uv ∈ (unshuffles w).toFinset, F uv := by
      symm
      apply Finset.sum_subset Finset.subset_union_left
      intro uv _ huv
      have hcount : (unshuffles w).count uv = 0 :=
        Multiset.count_eq_zero.mpr (by simpa using huv)
      simp [F, hcount]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro uv _
      exact (Nat.cast_commute ((unshuffles w).count uv) (f uv.1 * g uv.2)).eq.symm

/-- Mapping the letters commutes with partitioning their positions. -/
lemma unshuffles_map {L L' : Type*} (f : L → L') (w : List L) :
    unshuffles (w.map f) =
      (unshuffles w).map (fun uv => (uv.1.map f, uv.2.map f)) := by
  induction w with
  | nil => simp [unshuffles]
  | cons a w ih =>
    simp only [List.map_cons, unshuffles, ih, Multiset.map_add, Multiset.map_map,
      Function.comp_def]

/-- Each part of an ordered position partition is a sublist of the whole word. -/
lemma unshuffles_sublists {L : Type*} {w u v : List L} (h : (u, v) ∈ unshuffles w) :
    u.Sublist w ∧ v.Sublist w := by
  induction w generalizing u v with
  | nil =>
    simp only [unshuffles, Multiset.mem_singleton, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp
  | cons a w ih =>
    simp only [unshuffles, Multiset.mem_add, Multiset.mem_map] at h
    rcases h with ⟨⟨u', v'⟩, h, heq⟩ | ⟨⟨u', v'⟩, h, heq⟩
    · cases heq
      exact ⟨(ih h).1.cons_cons a, (ih h).2.cons a⟩
    · cases heq
      exact ⟨(ih h).1.cons a, (ih h).2.cons_cons a⟩

end PAdicOrderType
