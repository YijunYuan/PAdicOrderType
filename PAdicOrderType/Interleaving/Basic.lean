/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.Data.List.Lex
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Order.MinMax
import Mathlib.Tactic.Abel

/-!
# Finite interleaving sums

Interleavings (Definition 3.13) merge two words while preserving the order of the letters in
each word. Different choices of positions may yield the same output, so outputs are counted
with multiplicity. Extending this operation to finitely supported coefficient families gives
finite interleaving products and their iterated powers, whose coefficients are the sums `σ_z`
of Lemma 3.15.

## Main definitions

* `PAdicOrderType.shuffles`: interleavings of two words, counted with multiplicity.
* `PAdicOrderType.wordShuffle`: the coefficient family counting these interleavings.
* `PAdicOrderType.interleavingProduct`: the bilinear product of two coefficient families.
* `PAdicOrderType.interleavingPower`: the iterated product, with the empty word as unit.
-/

namespace PAdicOrderType

variable {L : Type*}

/-- The multiset of **shuffles** (interleavings) of two words, with
multiplicity: `shuffles u v` lists, for each of the `(|u|+|v| choose |u|)`
interleaving patterns, the resulting word. Each pattern is an ordered partition of the
positions realizing the output as an interleaving of `u` and `v` (Definition 3.13). -/
def shuffles : List L → List L → Multiset (List L)
  | [], v => {v}
  | u :: us, [] => {u :: us}
  | a :: us, b :: vs =>
      ((shuffles us (b :: vs)).map (a :: ·)) + ((shuffles (a :: us) vs).map (b :: ·))
  termination_by u v => u.length + v.length
  decreasing_by all_goals (simp only [List.length_cons]; omega)

@[simp] lemma shuffles_nil_left (v : List L) : shuffles [] v = {v} := by
  simp [shuffles]

@[simp] lemma shuffles_nil_right (u : List L) : shuffles u [] = {u} := by
  cases u <;> simp [shuffles]

@[simp] lemma shuffles_cons_cons (a b : L) (us vs : List L) :
    shuffles (a :: us) (b :: vs) =
      ((shuffles us (b :: vs)).map (a :: ·)) + ((shuffles (a :: us) vs).map (b :: ·)) := by
  simp [shuffles]

/-- Every interleaving of `u` and `v` has length `|u| + |v|`. -/
lemma length_of_mem_shuffles :
    ∀ (u v : List L), ∀ w ∈ shuffles u v, w.length = u.length + v.length := by
  intro u v
  induction u, v using shuffles.induct with
  | case1 v =>
    intro w hw
    rw [shuffles_nil_left, Multiset.mem_singleton] at hw
    simp [hw]
  | case2 u us =>
    intro w hw
    rw [shuffles_nil_right, Multiset.mem_singleton] at hw
    simp [hw]
  | case3 a us b vs ih₁ ih₂ =>
    intro w hw
    rw [shuffles_cons_cons, Multiset.mem_add] at hw
    rcases hw with hw | hw <;> rw [Multiset.mem_map] at hw <;>
      obtain ⟨w', hw', rfl⟩ := hw
    · rw [List.length_cons, ih₁ w' hw']
      simp [Nat.add_right_comm]
    · rw [List.length_cons, ih₂ w' hw']
      simp [Nat.add_assoc]

/-- Letters of an interleaving are letters of the factors. -/
lemma mem_of_mem_of_mem_shuffles :
    ∀ (u v : List L), ∀ w ∈ shuffles u v, ∀ e ∈ w, e ∈ u ∨ e ∈ v := by
  intro u v
  induction u, v using shuffles.induct with
  | case1 v =>
    intro w hw
    rw [shuffles_nil_left, Multiset.mem_singleton] at hw
    exact hw ▸ fun e he => Or.inr he
  | case2 u us =>
    intro w hw
    rw [shuffles_nil_right, Multiset.mem_singleton] at hw
    exact hw ▸ fun e he => Or.inl he
  | case3 a us b vs ih₁ ih₂ =>
    intro w hw
    rw [shuffles_cons_cons, Multiset.mem_add] at hw
    rcases hw with hw | hw <;> rw [Multiset.mem_map] at hw <;>
      obtain ⟨w', hw', rfl⟩ := hw <;> intro e he <;>
      rcases List.mem_cons.mp he with rfl | he'
    · exact Or.inl (List.mem_cons_self ..)
    · rcases ih₁ w' hw' e he' with h | h
      · exact Or.inl (List.mem_cons_of_mem a h)
      · exact Or.inr h
    · exact Or.inr (List.mem_cons_self ..)
    · rcases ih₂ w' hw' e he' with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem b h)

variable (K : Type*)

section Defs

variable [DecidableEq L] [Semiring K]

/-- The interleaving sum of two basis words, as an element of the free
`K`-module on words: the word `w` occurs with coefficient the number of
interleaving patterns of `u` and `v` producing `w`. -/
noncomputable def wordShuffle (u v : List L) : (List L) →₀ K :=
  ((shuffles u v).toFinsupp).mapRange Nat.cast Nat.cast_zero

@[simp] lemma wordShuffle_apply (u v w : List L) :
    wordShuffle K u v w = ((shuffles u v).count w : K) := by
  simp [wordShuffle]

/-- The **interleaving sum** on the free `K`-module on words, as a bilinear
operation: `interleavingProduct K f g = ∑_{u, v} f(u) g(v) (u shuffle v)`. -/
noncomputable def interleavingProduct (f g : (List L) →₀ K) : (List L) →₀ K :=
  f.sum fun u a => g.sum fun v b => (a * b) • wordShuffle K u v

lemma interleavingProduct_apply (f g : (List L) →₀ K) (w : List L) :
    interleavingProduct K f g w =
      ∑ u ∈ f.support, ∑ v ∈ g.support, f u * g v * ((shuffles u v).count w : K) := by
  simp [interleavingProduct, Finsupp.sum, mul_assoc]

/-- A word in the support of an interleaving sum is an interleaving of words
from the supports of the factors. -/
lemma exists_mem_shuffles_of_mem_support_interleavingProduct {f g : (List L) →₀ K}
    {w : List L} (hw : w ∈ (interleavingProduct K f g).support) :
    ∃ u ∈ f.support, ∃ v ∈ g.support, w ∈ shuffles u v := by
  classical
  have hne := Finsupp.mem_support_iff.mp hw
  rw [interleavingProduct_apply] at hne
  obtain ⟨u, hu, hune⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨v, hv, hvne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hune
  refine ⟨u, hu, v, hv, ?_⟩
  by_contra hmem
  rw [Multiset.count_eq_zero.mpr hmem] at hvne
  simp at hvne

@[simp] lemma interleavingProduct_zero_left (g : (List L) →₀ K) :
    interleavingProduct K 0 g = 0 := by
  simp [interleavingProduct]

@[simp] lemma interleavingProduct_zero_right (f : (List L) →₀ K) :
    interleavingProduct K f 0 = 0 := by
  simp [interleavingProduct]

lemma interleavingProduct_add_left (f f' g : (List L) →₀ K) :
    interleavingProduct K (f + f') g = interleavingProduct K f g + interleavingProduct K f' g := by
  unfold interleavingProduct
  exact Finsupp.sum_add_index' (fun u => by simp)
    (fun u a₁ a₂ => by simp [add_mul, add_smul, Finsupp.sum_add])

lemma interleavingProduct_add_right (f g g' : (List L) →₀ K) :
    interleavingProduct K f (g + g') = interleavingProduct K f g + interleavingProduct K f g' := by
  unfold interleavingProduct
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun u _ => ?_
  exact Finsupp.sum_add_index' (fun v => by simp)
    (fun v b₁ b₂ => by simp [mul_add, add_smul])

@[simp] lemma interleavingProduct_single_single (u v : List L) (a b : K) :
    interleavingProduct K (Finsupp.single u a) (Finsupp.single v b) =
      (a * b) • wordShuffle K u v := by
  unfold interleavingProduct
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

end Defs

section Powers

variable [DecidableEq L] [CommRing K]

/-- The `n`-fold interleaving product of a finite coefficient family.
The zeroth power has coefficient `1` at the empty word and vanishes elsewhere. For a family
`λ` supported on words of length `r`, the coefficient at `z` is the sum `σ_z` of Lemma 3.15
over ordered partitions of the positions of `z` into `n` sets of cardinality `r`. -/
noncomputable def interleavingPower (f : (List L) →₀ K) : ℕ → (List L) →₀ K
  | 0 => Finsupp.single [] 1
  | n + 1 => interleavingProduct K (interleavingPower f n) f

end Powers

end PAdicOrderType
