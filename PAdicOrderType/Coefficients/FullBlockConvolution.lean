/-
Copyright (c) 2026 Shanwen Wang, Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/

import PAdicOrderType.Coefficients.CarryFreeCoefficients

/-!
# Convolution over partitions of digit blocks

When a nonzero convolution term assigns each whole block to one input,
the coefficient sum reduces to the finite ordered partitions of those blocks.
Disjoint, nonzero blocks make the resulting digit-vector decompositions unique.
The resulting identity converts carry-free convolution into an interleaving sum, as in the
proof of Lemma 3.14.
-/

namespace PAdicOrderType

/-- All ordered decompositions obtained by assigning each vector in a list wholly
to one of two sums. Multiplicities record distinct assignments with equal resulting sums. -/
noncomputable def splitSums {ι : Type*} : List (ι →₀ ℕ) → Multiset ((ι →₀ ℕ) × (ι →₀ ℕ))
  | [] => {(0, 0)}
  | a :: xs => (splitSums xs).map (fun xy => (a + xy.1, xy.2)) +
      (splitSums xs).map (fun xy => (xy.1, a + xy.2))

lemma splitSums_add {ι : Type*} {xs : List (ι →₀ ℕ)} {x y : ι →₀ ℕ}
    (h : (x, y) ∈ splitSums xs) : x + y = xs.sum := by
  induction xs generalizing x y with
  | nil => simpa [splitSums] using h
  | cons a xs ih =>
    simp only [splitSums, Multiset.mem_add, Multiset.mem_map] at h
    rcases h with ⟨⟨x',y'⟩, h, heq⟩ | ⟨⟨x',y'⟩, h, heq⟩
    · cases heq
      simp only [List.sum_cons, add_assoc, ih h]
    · cases heq
      rw [List.sum_cons, ← ih h]
      abel

lemma splitSums_nodup {ι : Type*} (xs : List (ι →₀ ℕ))
    (hnz : ∀ a ∈ xs, a ≠ 0)
    (hd : xs.Pairwise fun a b => Disjoint a.support b.support) : (splitSums xs).Nodup := by
  classical
  induction xs with
  | nil => simp [splitSums]
  | cons a xs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hd
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr (hnz a List.mem_cons_self)
    have hsumi : xs.sum i = 0 := by
      change (Finsupp.applyAddHom i) xs.sum = 0
      rw [map_list_sum]
      apply List.sum_eq_zero
      intro z hz
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hz
      exact Finsupp.notMem_support_iff.mp (fun hbi => Finset.disjoint_left.mp (hhead b hb) hi hbi)
    have hzero : ∀ x y : ι →₀ ℕ, (x, y) ∈ splitSums xs → x i = 0 ∧ y i = 0 := by
      intro x y h
      have hsum := congrArg (fun z : ι →₀ ℕ => z i) (splitSums_add h)
      simpa only [Finsupp.add_apply, hsumi, Nat.add_eq_zero_iff] using hsum
    rw [splitSums, Multiset.nodup_add]
    have hnd := ih (fun b hb => hnz b (List.mem_cons_of_mem _ hb)) htail
    refine ⟨hnd.map ?_, hnd.map ?_, ?_⟩
    · intro x y h
      simpa only [Prod.mk.injEq, add_right_inj, Prod.ext_iff] using h
    · intro x y h
      simpa only [Prod.mk.injEq, add_right_inj, Prod.ext_iff] using h
    · rw [Multiset.disjoint_left]
      intro z hleft hright
      obtain ⟨⟨x,y⟩, hxy, hx⟩ := Multiset.mem_map.mp hleft
      obtain ⟨⟨x',y'⟩, hxy', hy⟩ := Multiset.mem_map.mp hright
      have heq := congrArg (fun z : (ι →₀ ℕ) × (ι →₀ ℕ) => z.1 i) (hx.trans hy.symm)
      simp only [Finsupp.add_apply, (hzero x y hxy).1, (hzero x' y' hxy').1, add_zero] at heq
      exact Finsupp.mem_support_iff.mp hi heq

/-- A decomposition that does not split any component comes from a partition
of the list of components. -/
lemma mem_splitSums_of_whole {ι : Type*} (xs : List (ι →₀ ℕ)) (x y : ι →₀ ℕ)
    (hsum : x + y = xs.sum)
    (hwhole : ∀ a ∈ xs, (∀ i ∈ a.support, x i = 0) ∨ (∀ i ∈ a.support, y i = 0)) :
    (x, y) ∈ splitSums xs := by
  classical
  induction xs generalizing x y with
  | nil =>
    have hx : x = 0 := by
      ext i
      have hi := congrArg (fun z : ι →₀ ℕ => z i) hsum
      simpa using (Nat.eq_zero_of_add_eq_zero_right (by simpa using hi))
    have hy : y = 0 := by simpa [hx] using hsum
    simp [splitSums, hx, hy]
  | cons a xs ih =>
    simp only [List.sum_cons] at hsum
    have hle {z t : ι →₀ ℕ} (hz : ∀ i ∈ a.support, z i = 0)
        (heq : z + t = a + xs.sum) : a ≤ t := by
      intro i
      by_cases hai : a i = 0
      · simp [hai]
      · have hz := hz i (Finsupp.mem_support_iff.mpr hai)
        have hi := congrArg (fun z : ι →₀ ℕ => z i) heq
        simp only [Finsupp.add_apply, hz, zero_add] at hi
        omega
    rcases hwhole a List.mem_cons_self with hx | hy
    · have hay := hle hx hsum
      have hysum : a + (y - a) = y := add_tsub_cancel_of_le hay
      have hsum' : x + (y - a) = xs.sum := by
        apply add_left_cancel (a := a)
        calc
          a + (x + (y - a)) = x + (a + (y - a)) := add_left_comm ..
          _ = a + xs.sum := by rw [hysum, hsum]
      have hpart := ih x (y - a) hsum' (by
        intro b hb
        rcases hwhole b (List.mem_cons_of_mem _ hb) with hb | hb
        · exact Or.inl hb
        · right
          intro i hi
          simp [Finsupp.tsub_apply, hb i hi])
      apply Multiset.mem_add.mpr
      right
      exact Multiset.mem_map.mpr ⟨(x, y - a), hpart, by simp only [hysum]⟩
    · have hax := hle (z := y) (t := x) hy (by rw [add_comm]; exact hsum)
      have hxsum : a + (x - a) = x := add_tsub_cancel_of_le hax
      have hsum' : (x - a) + y = xs.sum := by
        apply add_left_cancel (a := a)
        rw [← add_assoc, hxsum, hsum]
      have hpart := ih (x - a) y hsum' (by
        intro b hb
        rcases hwhole b (List.mem_cons_of_mem _ hb) with hb | hb
        · left
          intro i hi
          simp [Finsupp.tsub_apply, hb i hi]
        · exact Or.inr hb)
      apply Multiset.mem_add.mpr
      left
      exact Multiset.mem_map.mpr ⟨(x - a, y), hpart, by simp only [hxsum]⟩

/-- If every nonzero convolution term assigns whole blocks to its inputs,
convolution is the finite sum over the ordered partitions of those blocks. -/
lemma convolve_eq_splitSums {p : ℕ} [Fact (Nat.Prime p)] {K : Type*} [CommRing K]
    (A C : DigitCoefficients p K) (u : {d : PAdicOrderType.DigitSeries // d.IsP p})
    (xs : List (ℕ+ →₀ ℕ)) (hsum : xs.sum = u.1)
    (hnz : ∀ a ∈ xs, a ≠ 0)
    (hd : xs.Pairwise fun a b => Disjoint a.support b.support)
    (hwhole : ∀ x y : ℕ+ →₀ ℕ, x + y = u.1 →
      DigitCoefficients.extendMv A x * DigitCoefficients.extendMv C y ≠ 0 →
      ∀ a ∈ xs, (∀ i ∈ a.support, x i = 0) ∨ (∀ i ∈ a.support, y i = 0)) :
    DigitCoefficients.convolve A C u =
      ((splitSums xs).map fun xy =>
        DigitCoefficients.extendMv A xy.1 * DigitCoefficients.extendMv C xy.2).sum := by
  classical
  rw [DigitCoefficients.convolve_apply]
  let S : Finset ((ℕ+ →₀ ℕ) × (ℕ+ →₀ ℕ)) := ⟨splitSums xs, splitSums_nodup xs hnz hd⟩
  have hsub : S ⊆ Finset.antidiagonal (u.1) := by
    intro xy hxy
    exact Finset.mem_antidiagonal.mpr ((splitSums_add hxy).trans hsum)
  rw [← Finset.sum_mk _ (splitSums_nodup xs hnz hd)]
  symm
  apply Finset.sum_subset hsub
  rintro ⟨x,y⟩ hxy hnot
  by_contra hne
  apply hnot
  exact mem_splitSums_of_whole xs x y
    ((Finset.mem_antidiagonal.mp hxy).trans hsum.symm)
    (hwhole x y (Finset.mem_antidiagonal.mp hxy) hne)

end PAdicOrderType
